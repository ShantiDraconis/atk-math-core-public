import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# ATK — O operador `_` (objeto de duas faces)

`(a_b)` é um único objeto formado por duas faces, `a` e `b`, que podem ter tipos diferentes. Aqui
ele é `ligar a b : Linha A B` (em Lean `_` é reservado, por isso o construtor tem nome).

Provado neste arquivo, sem hipóteses e só com os axiomas padrão:

* `igualdade_estrutural`: `(a_b) = (c_d) ⟺ a = c ∧ b = d`; `linhaEquivProd`: `Linha A B ≃ A × B`;
* `residuo_zero_iff`: para faces reais, o resíduo `(a−c)_(b−d)` é `(0_0)` exatamente quando os dois
  objetos são iguais; `residuo_proprio`: o resíduo de um objeto consigo mesmo é `(0_0)`;
* `preserva_residuo`: uma transformação linear injetiva preserva "resíduo zero" nos dois sentidos;
* `singular_anula`: uma transformação **não** injetiva anula resíduos não nulos — por isso só
  transformações injetivas servem para transportar enunciados;
* `transporte`: se `T` preserva a propriedade `P` e `P (T x)` vale, então `P x` vale;
* `absorcao`: `X ≤ (c_B + c_T) X + C` com `c_B + c_T < 1` dá `X ≤ C / (1 − c_B − c_T)`;
* `telescopagem`: `∑_{n<N} (D n − D (n+1)) = D 0 − D N`;
* `decaimento`: `0 ≤ D n ≤ C/(n+1)` dá `D n → 0`;
* `estrutura_nao_basta`: existe uma sequência `≥ 0` e não crescente que **não** tende a zero (o
  defeito constante) — as leis estruturais sozinhas não dão `D_∞ = 0`;
* `fechamento_condicional`: produtores e pontes para os sete núcleos dão a conjunção dos sete.

O que este arquivo **não** faz: nenhuma conjectura é provada. `fechamento_condicional` recebe os sete
produtores como hipóteses; `estrutura_nao_basta` mostra que a álgebra do `_` não os fornece.
`OPEN_MATH = true`, `CLOSED_MATH = false`.
-/

open Filter Topology

namespace ATK.DuasFaces

universe u v

/-- O objeto de duas faces `(a_b)`. -/
structure Linha (A : Type u) (B : Type v) where
  esquerda : A
  direita : B

/-- `ligar a b` é `(a_b)`. -/
def ligar {A : Type u} {B : Type v} (a : A) (b : B) : Linha A B := ⟨a, b⟩

/-- **Igualdade estrutural**: `(a_b) = (c_d) ⟺ a = c ∧ b = d`. -/
theorem igualdade_estrutural {A : Type u} {B : Type v} (a c : A) (b d : B) :
    ligar a b = ligar c d ↔ a = c ∧ b = d := by
  simp [ligar]

/-- `Linha A B` é o produto `A × B`. -/
def linhaEquivProd (A : Type u) (B : Type v) : Linha A B ≃ A × B where
  toFun x := (x.esquerda, x.direita)
  invFun p := ⟨p.1, p.2⟩
  left_inv x := by cases x; rfl
  right_inv p := by cases p; rfl

theorem linhaEquivProd_ligar {A : Type u} {B : Type v} (a : A) (b : B) :
    linhaEquivProd A B (ligar a b) = (a, b) := rfl

/-! ### Faces reais: o espaço `ℝ × ℝ` -/

/-- Faces reais. -/
abbrev LinhaR := ℝ × ℝ

/-- Resíduo entre dois objetos de faces reais: `(a_b) − (c_d) = ((a−c)_(b−d))`. -/
def residuo (x y : LinhaR) : LinhaR := x - y

theorem residuo_apply (a b c d : ℝ) : residuo (a, b) (c, d) = (a - c, b - d) := rfl

/-- **Resíduo zero ⟺ igualdade.** -/
theorem residuo_zero_iff (x y : LinhaR) : residuo x y = 0 ↔ x = y := by
  simp [residuo, sub_eq_zero]

/-- O resíduo de um objeto consigo mesmo é `(0_0)`. -/
theorem residuo_proprio (x : LinhaR) : residuo x x = 0 := by
  simp [residuo]

/-- `(a_b) = (0_0) ⟺ a = 0 ∧ b = 0`. -/
theorem linha_zero_iff (a b : ℝ) : ((a, b) : LinhaR) = 0 ↔ a = 0 ∧ b = 0 := by
  simp [Prod.ext_iff]

/-- **Transformações lineares injetivas preservam o resíduo zero**, nos dois sentidos. -/
theorem preserva_residuo (T : LinhaR →ₗ[ℝ] LinhaR) (hT : Function.Injective T) (x y : LinhaR) :
    residuo (T x) (T y) = 0 ↔ residuo x y = 0 := by
  rw [residuo_zero_iff, residuo_zero_iff]
  exact hT.eq_iff

/-- **Uma transformação não injetiva anula um resíduo não nulo**: a transformação nula leva
`(3_1) − (0_0) ≠ (0_0)` a `(0_0)`. -/
theorem singular_anula :
    ∃ (T : LinhaR →ₗ[ℝ] LinhaR) (x y : LinhaR),
      residuo x y ≠ 0 ∧ residuo (T x) (T y) = 0 := by
  refine ⟨0, (3, 1), 0, ?_, ?_⟩
  · rw [Ne, residuo_zero_iff]
    simp [Prod.ext_iff]
  · simp [residuo]

/-- **Transporte**: se `T` preserva `P` e `P (T x)` vale, então `P x` vale. -/
theorem transporte {A : Type u} (P : A → Prop) (T : A → A) (x : A)
    (preserva : ∀ y, P y ↔ P (T y)) (h : P (T x)) : P x :=
  (preserva x).mpr h

/-! ### Leis de fechamento sobre parâmetros reais -/

/-- **Absorção**: `X ≤ (c_B + c_T) X + C` com `c_B + c_T < 1` dá `X ≤ C / (1 − c_B − c_T)`. -/
theorem absorcao (X C cB cT : ℝ) (h : X ≤ (cB + cT) * X + C) (hd : cB + cT < 1) :
    X ≤ C / (1 - cB - cT) := by
  have hp : 0 < 1 - cB - cT := by linarith
  rw [le_div_iff₀ hp]
  nlinarith

/-- **Telescopagem**: `∑_{n<N} (D n − D (n+1)) = D 0 − D N`. -/
theorem telescopagem (D : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (D n - D (n + 1))) = D 0 - D N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- **Decaimento**: `0 ≤ D n ≤ C/(n+1)` dá `D n → 0`. -/
theorem decaimento (D : ℕ → ℝ) (C : ℝ) (h0 : ∀ n, 0 ≤ D n)
    (h : ∀ n, D n ≤ C / ((n : ℝ) + 1)) : Tendsto D atTop (𝓝 0) :=
  squeeze_zero h0 h (tendsto_const_div_atTop_nhds_zero_nat C |>.comp (tendsto_add_atTop_nat 1)
    |>.congr fun n => by simp)

/-- **As leis estruturais não bastam**: o defeito constante `D n = 1` é `≥ 0`, não crescente, tem
todos os decréscimos nulos e **não** tende a zero. -/
theorem estrutura_nao_basta :
    ∃ D : ℕ → ℝ, (∀ n, 0 ≤ D n) ∧ Antitone D ∧ (∀ n, D n - D (n + 1) = 0) ∧
      ¬ Tendsto D atTop (𝓝 0) := by
  refine ⟨fun _ => 1, fun _ => zero_le_one, fun _ _ _ => le_rfl, fun _ => sub_self 1, ?_⟩
  intro h
  have := tendsto_nhds_unique h tendsto_const_nhds
  norm_num at this

/-! ### Composição dos sete núcleos -/

/-- **Fechamento condicional**: com os sete produtores e as sete pontes, a conjunção dos sete
enunciados vale. Os produtores são hipóteses: este teorema não os fornece. -/
theorem fechamento_condicional (P K : Fin 7 → Prop) (produtores : ∀ i, K i)
    (pontes : ∀ i, K i → P i) : ∀ i, P i :=
  fun i => pontes i (produtores i)

end ATK.DuasFaces

#print axioms ATK.DuasFaces.igualdade_estrutural
#print axioms ATK.DuasFaces.linhaEquivProd_ligar
#print axioms ATK.DuasFaces.residuo_apply
#print axioms ATK.DuasFaces.residuo_zero_iff
#print axioms ATK.DuasFaces.residuo_proprio
#print axioms ATK.DuasFaces.linha_zero_iff
#print axioms ATK.DuasFaces.preserva_residuo
#print axioms ATK.DuasFaces.singular_anula
#print axioms ATK.DuasFaces.transporte
#print axioms ATK.DuasFaces.absorcao
#print axioms ATK.DuasFaces.telescopagem
#print axioms ATK.DuasFaces.decaimento
#print axioms ATK.DuasFaces.estrutura_nao_basta
#print axioms ATK.DuasFaces.fechamento_condicional
