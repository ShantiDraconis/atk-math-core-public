import ATK.Indeterminacy
import Mathlib.Algebra.Ring.Pointwise.Set
import Mathlib.Analysis.Real.Hyperreal

/-!
# ATK — A álgebra de `I`: o que é consistente, o que é inconsistente, e os modelos

O acervo propõe várias álgebras para `I` (= `0/0`). Aqui o kernel decide, de uma vez por todas:

**Teoremas de impossibilidade** (refutam conjuntos de axiomas do acervo, que tornariam um arquivo
capaz de provar `False`):
* `absorvente_unico`, `absorvente_zero_trivial`: o absorvente é único; se for o neutro, a estrutura
  é trivial;
* `idempotente_inverso`: `I + I = I` e `I − I = 0` (inverso aditivo) ⇒ `I = 0` (refuta os 15
  postulados PAX P1–P15 e `K_I`);
* `absorvente_inverso_trivial`: absorvente com inverso ⇒ estrutura trivial;
* `mul_absorvente_zero`: `x·I = I` para todo `x` ⇒ `I = 0` sempre que `0·y = 0`;
* `triangulo`: `I + x = I`, `0·I = 0`, `I·1 = I` e distributividade ⇒ `I = 0`;
* `idempotente_unidade`, `idempotente_dominio`: `I² = I` num corpo força `I ∈ {0, 1}`;
* `propagacao_universal_falsa`, `invariancia_falsa`: os axiomas "toda transformação fixa `I`"
  (P1) e "quem fixa `I` é a identidade" são falsos.

**Modelos consistentes** (onde as leis verdadeiras moram):
* `RI = Option ℝ` com `I` absorvente (o "meadow comum"): monoides comutativos para `+` e `·`, as
  **duas leis distributivas para todos os elementos**, mas `0·I = I` e `I` sem inverso;
* modelo de conjuntos `I := ℝ` inteiro (multiestado): `{x} + I = I`, `{x}·I = I` (`x ≠ 0`),
  `{0}·I = {0}`, `I + I = I·I = I − I = I`, só **subdistributividade** — e a distributividade
  falha (`distributiva_falha`), o que explica o triângulo;
* testemunha `(1, 0) ∈ ℝ × ℝ`: idempotente, `≠ 0`, `≠ 1`, não invertível, `·0 = 0` — consistente;
* `Δ` infinitesimal: existe nos hiper-reais (`delta_hiperreal`), não existe em `ℝ`
  (`delta_real_nao_existe`) — a única leitura consistente de "Δ = 0.∞19".
-/

open Set

namespace ATK.IAlgebra

/-! ## Impossibilidades abstratas -/

/-- Elemento absorvente (dos dois lados) para `+`. -/
def Absorvente {α : Type*} [Add α] (a : α) : Prop := ∀ x, a + x = a ∧ x + a = a

theorem absorvente_unico {α : Type*} [Add α] {a b : α} (ha : Absorvente a) (hb : Absorvente b) :
    a = b :=
  ((ha b).1).symm.trans (hb a).2

theorem absorvente_zero_trivial {α : Type*} [AddMonoid α] {I : α} (h : ∀ x, I + x = I)
    (h0 : I = 0) (x : α) : x = 0 := by
  have := h x
  rw [h0, zero_add] at this
  exact this

/-- **`I + I = I` e `I + J = 0` ⇒ `I = 0`** (associatividade basta). -/
theorem idempotente_inverso {α : Type*} [AddMonoid α] {I J : α} (hI : I + I = I) (hJ : I + J = 0) :
    I = 0 :=
  calc I = I + (I + J) := by rw [hJ, add_zero]
    _ = I + I + J := (add_assoc I I J).symm
    _ = 0 := by rw [hI, hJ]

/-- **Os postulados PAX (`I + I = I`, `I − I = 0`, `I ≠ 0`) não têm modelo.** -/
theorem pax_inconsistente {α : Type*} [AddGroup α] (I : α) : ¬ (I + I = I ∧ I ≠ 0) := by
  rintro ⟨hI, hne⟩
  exact hne (idempotente_inverso hI (add_neg_cancel I))

theorem absorvente_inverso_trivial {α : Type*} [AddMonoid α] {I J : α} (h : ∀ x, I + x = I)
    (hJ : I + J = 0) (x : α) : x = 0 :=
  absorvente_zero_trivial h ((h J).symm.trans hJ) x

/-- **`x·I = I` para todo `x` força `I = 0`** em qualquer estrutura com `0·y = 0`. -/
theorem mul_absorvente_zero {α : Type*} [MulZeroClass α] {I : α} (h : ∀ x, x * I = I) : I = 0 :=
  (h 0).symm.trans (zero_mul I)

/-- **Triângulo de incompatibilidade**: `I + x = I`, `0·I = 0` (na forma `I·0 = 0`), `I·1 = I` e
distributividade à esquerda ⇒ `I = 0`. -/
theorem triangulo {α : Type*} [Add α] [Mul α] [Zero α] [One α] [Neg α] {I : α}
    (hd : ∀ a b c : α, a * (b + c) = a * b + a * c) (hinv : (1 : α) + -1 = 0)
    (h0 : I * 0 = 0) (h1 : I * 1 = I) (habs : ∀ x, I + x = I) : I = 0 :=
  calc I = I + I * (-1) := (habs _).symm
    _ = I * 1 + I * (-1) := by rw [h1]
    _ = I * (1 + -1) := (hd _ _ _).symm
    _ = I * 0 := by rw [hinv]
    _ = 0 := h0

/-- Idempotente invertível é `1`. -/
theorem idempotente_unidade {M : Type*} [Monoid M] {e : M} (he : e * e = e) (hu : IsUnit e) :
    e = 1 := by
  obtain ⟨u, rfl⟩ := hu
  have h := congrArg (fun x => x * ((u⁻¹ : Mˣ) : M)) he
  simpa [mul_assoc] using h

/-- Num domínio, `I² = I` força `I = 0 ∨ I = 1`. -/
theorem idempotente_dominio {R : Type*} [Ring R] [NoZeroDivisors R] {e : R} (he : e * e = e) :
    e = 0 ∨ e = 1 := by
  have h : e * (e - 1) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- Num anel, todo idempotente `e` satisfaz `e·(1 − e) = 0`. -/
theorem idempotente_divisor {R : Type*} [Ring R] {e : R} (he : e * e = e) : e * (1 - e) = 0 := by
  rw [mul_sub, mul_one, he, sub_self]

/-- **Consistência** de `{I² = I, I ≠ 0, I ≠ 1, I não invertível, I·0 = 0}`: testemunha `(1, 0)`. -/
theorem testemunha_idempotente :
    let I : ℝ × ℝ := (1, 0)
    I * I = I ∧ I ≠ 0 ∧ I ≠ 1 ∧ ¬ IsUnit I ∧ I * 0 = 0 := by
  intro I
  refine ⟨by simp [I], by simp [I, Prod.ext_iff], by simp [I, Prod.ext_iff], ?_, by simp⟩
  rw [Prod.isUnit_iff]
  rintro ⟨_, h⟩
  exact not_isUnit_zero h

/-- Translação injetiva + idempotente aditivo ⇒ o idempotente é `0` (sem ordem compatível). -/
theorem idempotente_cancelativo {α : Type*} [Add α] [Zero α] {I : α}
    (hinj : Function.Injective (· + I)) (hz : ∀ x : α, 0 + x = x) (hI : I + I = I) : I = 0 :=
  hinj (show I + I = 0 + I by rw [hI, hz])

/-- **P1 é falso**: nem toda transformação fixa `I` (quando o alvo não é vazio). -/
theorem propagacao_universal_falsa {α β : Type*} (b : β) :
    ¬ ∀ T : Option α → Option β, T none = none := fun h => by
  have := h (fun _ => some b)
  simp at this

/-- **"Quem fixa `I` é a identidade" é falso** quando há outro elemento. -/
theorem invariancia_falsa {α : Type*} {i j : α} (hij : j ≠ i) :
    ¬ ∀ f : α → α, f i = i → f = id := fun h => by
  have := congrFun (h (fun _ => i) rfl) j
  exact hij this.symm

/-- **Caracterização das transformações estáveis**: preservam `I` e levam determinados em
determinados ⟺ são levantamentos `Option.map f`. -/
theorem estavel_iff_map {α β : Type*} (T : Option α → Option β) :
    (T none = none ∧ ∀ a, ∃ b, T (some a) = some b) ↔ ∃ f : α → β, T = Option.map f := by
  constructor
  · rintro ⟨h0, h1⟩
    choose f hf using h1
    refine ⟨f, funext fun x => ?_⟩
    cases x with
    | none => simpa using h0
    | some a => simpa using hf a
  · rintro ⟨f, rfl⟩
    exact ⟨rfl, fun a => ⟨f a, rfl⟩⟩

/-! ## O modelo `RI = Option ℝ` com `I` absorvente (meadow comum) -/

open ATK.Indeterminacy

theorem addI_comm (x y : RI) : addI x y = addI y x := by
  cases x <;> cases y <;> simp [addI, add_comm]

theorem addI_assoc (x y z : RI) : addI (addI x y) z = addI x (addI y z) := by
  cases x <;> cases y <;> cases z <;> simp [addI, add_assoc]

theorem addI_zero (x : RI) : addI x (ι 0) = x := by cases x <;> simp [addI, ι]

theorem mulI_comm (x y : RI) : mulI x y = mulI y x := by
  cases x <;> cases y <;> simp [mulI, mul_comm]

theorem mulI_assoc (x y z : RI) : mulI (mulI x y) z = mulI x (mulI y z) := by
  cases x <;> cases y <;> cases z <;> simp [mulI, mul_assoc]

theorem mulI_one (x : RI) : mulI x (ι 1) = x := by cases x <;> simp [mulI, ι]

/-- **Distributividade total** no modelo absorvente. -/
theorem mulI_addI (x y z : RI) : mulI x (addI y z) = addI (mulI x y) (mulI x z) := by
  cases x <;> cases y <;> cases z <;> simp [mulI, addI, mul_add]

/-- `I` não tem inverso aditivo no modelo. -/
theorem I_sem_inverso (x : RI) : addI I x ≠ ι 0 := by
  rw [addI_I]; exact I_ne_ι 0

/-- `0·I = I`: o modelo **não** é um semianel. -/
theorem zero_mulI_I : mulI (ι 0) I = I := by simp [mulI, ι, I]

/-! ## O modelo de conjuntos (multiestado): `I := ℝ` inteiro -/

open Pointwise

/-- `I` como o conjunto de todos os valores. -/
def Iset : Set ℝ := univ

theorem singleton_add_Iset (x : ℝ) : {x} + Iset = Iset := by
  refine eq_univ_of_forall fun y => ?_
  exact Set.mem_add.mpr ⟨x, rfl, y - x, mem_univ _, by ring⟩

theorem singleton_mul_Iset {x : ℝ} (hx : x ≠ 0) : {x} * Iset = Iset := by
  refine eq_univ_of_forall fun y => ?_
  exact Set.mem_mul.mpr ⟨x, rfl, y / x, mem_univ _, by field_simp⟩

theorem zero_mul_Iset : ({0} : Set ℝ) * Iset = {0} := by
  ext y
  simp only [Set.mem_mul, mem_singleton_iff, Iset, mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl, b, rfl⟩; ring
  · rintro rfl; exact ⟨0, rfl, 0, by ring⟩

theorem Iset_add_Iset : Iset + Iset = Iset :=
  eq_univ_of_forall fun y => Set.mem_add.mpr ⟨y, mem_univ _, 0, mem_univ _, add_zero y⟩

theorem Iset_mul_Iset : Iset * Iset = Iset :=
  eq_univ_of_forall fun y => Set.mem_mul.mpr ⟨y, mem_univ _, 1, mem_univ _, mul_one y⟩

theorem Iset_sub_Iset : Iset - Iset = Iset :=
  eq_univ_of_forall fun y => Set.mem_sub.mpr ⟨y, mem_univ _, 0, mem_univ _, sub_zero y⟩

/-- Só subdistributividade vale em geral. -/
theorem subdistributiva (s t u : Set ℝ) : s * (t + u) ⊆ s * t + s * u := Set.mul_add_subset _ _ _

/-- **A distributividade falha**: `I·(1 + (−1)) = {0}` mas `I·1 + I·(−1) = ℝ`. -/
theorem distributiva_falha :
    Iset * ({1} + {-1}) = {0} ∧ Iset * {1} + Iset * {-1} = Iset := by
  constructor
  · rw [Set.singleton_add_singleton, show (1 : ℝ) + -1 = 0 by norm_num, mul_comm]
    exact zero_mul_Iset
  · rw [mul_comm Iset {1}, mul_comm Iset {-1}, singleton_mul_Iset one_ne_zero,
      singleton_mul_Iset (by norm_num), Iset_add_Iset]

/-! ## `Δ` infinitesimal: hiper-reais sim, reais não -/

/-- Nos hiper-reais existe `Δ > 0` menor que todo `1/(n+1)`. -/
theorem delta_hiperreal : ∃ Δ : Hyperreal, 0 < Δ ∧ ∀ n : ℕ, Δ < ((1 / ((n : ℝ) + 1) : ℝ) : Hyperreal) :=
  ⟨Hyperreal.epsilon, Hyperreal.epsilon_pos, fun n => Hyperreal.epsilon_lt_of_pos (by positivity)⟩

/-- Em `ℝ` não existe tal `Δ` (arquimedianidade). -/
theorem delta_real_nao_existe : ¬ ∃ Δ : ℝ, 0 < Δ ∧ ∀ n : ℕ, Δ < 1 / ((n : ℝ) + 1) := by
  rintro ⟨Δ, hΔ, h⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hΔ
  exact lt_asymm (h n) hn

end ATK.IAlgebra

#print axioms ATK.IAlgebra.absorvente_unico
#print axioms ATK.IAlgebra.absorvente_zero_trivial
#print axioms ATK.IAlgebra.idempotente_inverso
#print axioms ATK.IAlgebra.pax_inconsistente
#print axioms ATK.IAlgebra.absorvente_inverso_trivial
#print axioms ATK.IAlgebra.mul_absorvente_zero
#print axioms ATK.IAlgebra.triangulo
#print axioms ATK.IAlgebra.idempotente_unidade
#print axioms ATK.IAlgebra.idempotente_dominio
#print axioms ATK.IAlgebra.idempotente_divisor
#print axioms ATK.IAlgebra.testemunha_idempotente
#print axioms ATK.IAlgebra.idempotente_cancelativo
#print axioms ATK.IAlgebra.propagacao_universal_falsa
#print axioms ATK.IAlgebra.invariancia_falsa
#print axioms ATK.IAlgebra.estavel_iff_map
#print axioms ATK.IAlgebra.addI_comm
#print axioms ATK.IAlgebra.addI_assoc
#print axioms ATK.IAlgebra.addI_zero
#print axioms ATK.IAlgebra.mulI_comm
#print axioms ATK.IAlgebra.mulI_assoc
#print axioms ATK.IAlgebra.mulI_one
#print axioms ATK.IAlgebra.mulI_addI
#print axioms ATK.IAlgebra.I_sem_inverso
#print axioms ATK.IAlgebra.zero_mulI_I
#print axioms ATK.IAlgebra.singleton_add_Iset
#print axioms ATK.IAlgebra.singleton_mul_Iset
#print axioms ATK.IAlgebra.zero_mul_Iset
#print axioms ATK.IAlgebra.Iset_add_Iset
#print axioms ATK.IAlgebra.Iset_mul_Iset
#print axioms ATK.IAlgebra.Iset_sub_Iset
#print axioms ATK.IAlgebra.subdistributiva
#print axioms ATK.IAlgebra.distributiva_falha
#print axioms ATK.IAlgebra.delta_hiperreal
#print axioms ATK.IAlgebra.delta_real_nao_existe
