import ATK.Discovery.Truncamento
import Mathlib.Basic.Complex.Basic

/-!
# ATK-Discovery — Habitante de truncamento, certificado de comparação e objeto estruturado

**Habitante** (`Habitante α`): um valor junto com uma decomposição exata `valor = cabeça + cauda` e a
precisão em que o corte foi feito, num grupo aditivo linearmente ordenado `α`. O habitante carrega a
**prova** da reconstrução, não só os números.

**Certificado de comparação** (`Comparacao a b`): a evidência `cabeça(a) − cabeça(b) < cauda(b) − cauda(a)`.

* `lt_of_comparacao`, `comparacao_iff`: o certificado existe **se e só se** `a.valor < b.valor`;
* `lt_iff_de_cabecas_iguais`: com cabeças iguais, decide a ordem das caudas;
* `sem_comparacao_consigo`: nenhum habitante tem certificado contra si mesmo;
* `deTruncamento`: o habitante canônico de `x : ℝ` na precisão `N` (cabeça `P_N x`, cauda `T_N x`);
* `p01_sem_certificado`: o par `combustível = 1`, `tamanho = 1` do lema P01 refutado, em qualquer
  precisão, **não** admite certificado (`1 < 1` é falso; as caudas são `0`).

**Objeto estruturado** (`Estruturado`): componentes real, imaginária, fracionária e cauda, com valor
complexo `V = (R + F + T) + I·i` e observação `R`.

* `observacao_nao_injetiva`: dois objetos com a mesma observação e valores distintos;
* `observa_zero_valor_nao`: observação `0` com valor `2i`, `1/2` ou `10⁻ᴺ/2` — nenhum é zero;
* `equivObs`: a equivalência observacional é uma relação de equivalência, e **não** implica igualdade
  de valor (`equivObs_nao_implica_valor`).

Isto não acrescenta cauda alguma a contagens exatas: um `ℕ` não tem parte fracionária oculta
(`ATK.Discovery.Truncamento.natural_sem_cauda`).
-/

namespace ATK.Discovery.Cauda

open ATK.Discovery.Truncamento

section Grupo

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- Um valor com a sua decomposição exata em cabeça e cauda. -/
structure Habitante (α : Type*) [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] where
  valor : α
  precisao : ℕ
  cabeca : α
  cauda : α
  reconstrucao : valor = cabeca + cauda

/-- Certificado de comparação estrita entre dois habitantes. -/
structure Comparacao (a b : Habitante α) : Prop where
  balanco : a.cabeca - b.cabeca < b.cauda - a.cauda

theorem lt_of_comparacao {a b : Habitante α} (h : Comparacao a b) : a.valor < b.valor := by
  rw [a.reconstrucao, b.reconstrucao]
  have := h.balanco
  rw [sub_lt_sub_iff] at this
  rwa [add_comm b.cauda] at this

/-- O certificado existe **se e só se** a desigualdade estrita vale. -/
theorem comparacao_iff (a b : Habitante α) : Comparacao a b ↔ a.valor < b.valor := by
  refine ⟨lt_of_comparacao, fun h => ⟨?_⟩⟩
  rw [a.reconstrucao, b.reconstrucao] at h
  rw [sub_lt_sub_iff, add_comm b.cauda]
  exact h

/-- Com cabeças iguais, a ordem dos valores é a ordem das caudas. -/
theorem lt_iff_de_cabecas_iguais {a b : Habitante α} (h : a.cabeca = b.cabeca) :
    a.valor < b.valor ↔ a.cauda < b.cauda := by
  rw [a.reconstrucao, b.reconstrucao, h]
  exact add_lt_add_iff_left _

/-- Nenhum habitante tem certificado de comparação contra si mesmo. -/
theorem sem_comparacao_consigo (a : Habitante α) : ¬ Comparacao a a := by
  rw [comparacao_iff]
  exact lt_irrefl _

/-- Toda escolha de cabeça dá um habitante (a cauda é o que sobra). -/
def deCabeca (x cabeca : α) (n : ℕ) : Habitante α where
  valor := x
  precisao := n
  cabeca := cabeca
  cauda := x - cabeca
  reconstrucao := by abel

end Grupo

/-- O habitante canônico de `x : ℝ` na precisão `N`: cabeça `P_N x`, cauda `T_N x`. -/
noncomputable def deTruncamento (N : ℕ) (x : ℝ) : Habitante ℝ where
  valor := x
  precisao := N
  cabeca := P N x
  cauda := T N x
  reconstrucao := reconstrucao N x

theorem cauda_deTruncamento_nonneg (N : ℕ) (x : ℝ) : 0 ≤ (deTruncamento N x).cauda :=
  cauda_nonneg N x

/-- O par do lema P01 refutado (`combustível = 1`, `tamanho = 1`) não admite certificado em
nenhuma precisão: as cabeças são `1`, as caudas são `0`, e `0 < 0` é falso. -/
theorem p01_sem_certificado (N : ℕ) :
    (deTruncamento N 1).cauda = 0 ∧ ¬ Comparacao (deTruncamento N 1) (deTruncamento N 1) := by
  refine ⟨?_, sem_comparacao_consigo _⟩
  have := (natural_sem_cauda N 1).2
  push_cast at this
  exact this

/-! ## Objeto estruturado e observação -/

/-- Objeto com componentes real, imaginária, fracionária e cauda. -/
structure Estruturado where
  real : ℝ
  imag : ℝ
  frac : ℝ
  cauda : ℝ

/-- Valor complexo associado: `(R + F + T) + I·i`. -/
def Estruturado.valor (X : Estruturado) : ℂ := ⟨X.real + X.frac + X.cauda, X.imag⟩

/-- A observação: só a componente real. -/
def Estruturado.observa (X : Estruturado) : ℝ := X.real

/-- Dois objetos com a mesma observação e valores distintos: a observação não é injetiva. -/
theorem observacao_nao_injetiva :
    ∃ X Y : Estruturado, X.observa = Y.observa ∧ X.valor ≠ Y.valor := by
  refine ⟨⟨0, 0, 0, 0⟩, ⟨0, 2, 0, 0⟩, rfl, ?_⟩
  intro h
  have := congrArg Complex.im h
  simp [Estruturado.valor] at this

/-- Observação `0` sem valor `0`: parte imaginária `2`, fração `1/2`, cauda `10⁻ᴺ/2`. -/
theorem observa_zero_valor_nao (N : ℕ) :
    let A : Estruturado := ⟨0, 2, 0, 0⟩
    let B : Estruturado := ⟨0, 0, 1 / 2, 0⟩
    let C : Estruturado := ⟨0, 0, 0, 1 / (2 * (10 : ℝ) ^ N)⟩
    A.observa = 0 ∧ B.observa = 0 ∧ C.observa = 0 ∧ A.valor ≠ 0 ∧ B.valor ≠ 0 ∧ C.valor ≠ 0 := by
  intro A B C
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro h; have := congrArg Complex.im h; simp [A, Estruturado.valor] at this
  · intro h; have := congrArg Complex.re h; simp [B, Estruturado.valor] at this
  · intro h
    have := congrArg Complex.re h
    simp only [C, Estruturado.valor, Complex.zero_re] at this
    have h10 : (0 : ℝ) < (10 : ℝ) ^ N := by positivity
    have : (0 : ℝ) < 0 + 0 + 1 / (2 * (10 : ℝ) ^ N) := by positivity
    linarith

/-- Equivalência observacional: mesma componente real. -/
def equivObs : Setoid Estruturado where
  r X Y := X.observa = Y.observa
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- A equivalência observacional não implica igualdade de valor. -/
theorem equivObs_nao_implica_valor :
    ¬ ∀ X Y : Estruturado, equivObs.r X Y → X.valor = Y.valor := by
  intro h
  obtain ⟨X, Y, hobs, hval⟩ := observacao_nao_injetiva
  exact hval (h X Y hobs)

end ATK.Discovery.Cauda

#print axioms ATK.Discovery.Cauda.lt_of_comparacao
#print axioms ATK.Discovery.Cauda.comparacao_iff
#print axioms ATK.Discovery.Cauda.lt_iff_de_cabecas_iguais
#print axioms ATK.Discovery.Cauda.sem_comparacao_consigo
#print axioms ATK.Discovery.Cauda.cauda_deTruncamento_nonneg
#print axioms ATK.Discovery.Cauda.p01_sem_certificado
#print axioms ATK.Discovery.Cauda.observacao_nao_injetiva
#print axioms ATK.Discovery.Cauda.observa_zero_valor_nao
#print axioms ATK.Discovery.Cauda.equivObs_nao_implica_valor
