import ATK.LinhasNovas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Linhas novas II: unificação, pontos fixos, colapso `∞ = 0` e densidade de `ℤ[1/10]`

Continua `ATK.LinhasNovas`, organizado por linha em namespaces próprios.

* **Meio**: `half_fixed_point`, o ponto fixo de `x ↦ a − x` é `a/2` em qualquer corpo de
  característica 0; `half_normalized`, `a − x − c = (a − 2c) − (x − c)`; `half_center_invariant`,
  o centro não se move ao mudar a coordenada para `t = x − c`.
* **Truncamento** (linguagens sobre qualquer alfabeto): monótono, a união é a linguagem, e
  `trunc_injective`, os truncamentos determinam a linguagem. O mapa não perde nem acrescenta
  informação, logo não pode separar classes de complexidade.
* **Reta projetiva** (`ℝ ∪ {∞}`): pontos fixos de `inv` = `{1, −1}`, de `neg` = `{0, ∞}`;
  `neg`, `inv` e `neg ∘ inv` são involuções: o grupo `{id, inv, neg, neg ∘ inv} ≅ (ℤ/2)²`;
  `inv_some` concorda com o inverso de `ℝ` fora de `0`.
* **Colapso `∞ = 0`**: `colapso : ℝ ∪ {∞} → ℝ` cola só `∞` e `0` (`colapso_fiber`) e comuta com a
  inversão (`colapso_inv`), levando a da reta projetiva na convenção `0⁻¹ = 0` da Mathlib. Em `ℝ`
  os fixos da inversão são `{−1, 0, 1}` (`inv_real_fixed`); a inversão continua bijetiva.
* **Cauda**: as frações com cauda decimal finita formam o subanel `ℤ[1/10]` de `ℝ`, **enumerável**
  e **denso**; `1/3 ∉` mostra que não é corpo.
* **Involução com fixos** (`InvolucaoComFixos`): estrutura que carrega uma involução e o seu
  conjunto de pontos fixos, com instâncias `x ↦ a − x` (fixos `{a/2}`), `inv` e `neg` na reta
  projetiva. É `structure`, não `class`: em `ℝ` há uma involução `x ↦ a − x` por `a`, e instâncias
  automáticas entrariam em conflito. `ofAffineCenter` generaliza `x ↦ a − x` para qualquer
  `ℚ`-módulo, com fixos `{(1/2) • a}`.
* **Extras**: `no_fixpoint_of_cancelative` (com cancelamento, `x + a = x` força `a = 0`; o
  natural final exige perdê-lo), `enat_nao_cancelativo`, `rat_sem_maior_negativo`,
  `caudaFinita_iff` (`10ⁿ · x ∈ ℤ`), `trunc_tabela` (cada truncamento é uma tabela finita).
-/

open ATK.LinhasNovas

namespace ATK.LinhasNovas

/-! ## Meio -/

namespace Meio

theorem half_fixed_point {α : Type*} [Field α] [CharZero α] (a x : α) :
    a - x = x ↔ x = a / 2 := by
  constructor
  · intro h
    rw [eq_div_iff two_ne_zero]
    linear_combination -h
  · intro h
    rw [h]
    ring

theorem half_normalized {α : Type*} [CommRing α] (a c x : α) :
    a - x - c = (a - 2 * c) - (x - c) := by ring

/-- O centro não se move: na coordenada `t = x − c`, a simetria `x ↦ a − x` vira
`t ↦ (a − 2c) − t`, com os mesmos pontos fixos. -/
theorem half_center_invariant {α : Type*} [CommRing α] (a c x : α) :
    a - x = x ↔ (a - 2 * c) - (x - c) = x - c := by
  constructor <;> intro h <;> linear_combination h

end Meio

/-! ## Truncamento -/

namespace Truncamento

variable {α : Type*}

/-- O truncamento de uma linguagem em comprimento `≤ k`. -/
def trunc (L : Set (List α)) (k : ℕ) : Set (List α) := {w ∈ L | w.length ≤ k}

theorem trunc_monotone (L : Set (List α)) : Monotone (trunc L) :=
  fun _ _ hkl _ hw => ⟨hw.1, le_trans hw.2 hkl⟩

@[simp] theorem trunc_iUnion (L : Set (List α)) : (⋃ k, trunc L k) = L := by
  ext w
  simp only [Set.mem_iUnion, trunc, Set.mem_ofPred_eq]
  exact ⟨fun ⟨_, hw, _⟩ => hw, fun hw => ⟨_, hw, le_refl _⟩⟩

/-- **Os truncamentos determinam a linguagem.** -/
theorem trunc_injective (L L' : Set (List α)) :
    (∀ k, trunc L k = trunc L' k) ↔ L = L' := by
  constructor
  · intro h
    rw [← trunc_iUnion L, ← trunc_iUnion L']
    exact Set.iUnion_congr h
  · rintro rfl _
    rfl

/-- **Cada truncamento é uma tabela finita** (alfabeto `Bool`): existe `S : Finset` com
`trunc L k = S`, seja qual for `L`. Um algoritmo de busca na tabela decide `trunc L k`; essa
decidibilidade vale para linguagens indecidíveis também, então não mede complexidade. -/
theorem trunc_tabela (L : Set (List Bool)) (k : ℕ) : ∃ S : Finset (List Bool), (S : Set _) = trunc L k :=
  ⟨(truncamento_finito L k).toFinset, by simp [truncamento, trunc]⟩

end Truncamento

/-! ## Reta projetiva -/

namespace RetaProjetiva

/-- Fora de `0`, `inv` concorda com o inverso de `ℝ`. -/
theorem inv_some {x : ℝ} (hx : x ≠ 0) : ATK.LinhasNovas.inv (some x) = some x⁻¹ := by
  simp [ATK.LinhasNovas.inv, hx]

/-- **Os pontos fixos de `inv` são `1` e `−1`**; `0` e `∞` são trocados. -/
theorem inv_fixed (x : RetaProj) :
    ATK.LinhasNovas.inv x = x ↔ x = some 1 ∨ x = some (-1) := by
  rcases x with _ | r
  · simp [ATK.LinhasNovas.inv]
  · by_cases hr : r = 0
    · subst hr; simp [ATK.LinhasNovas.inv]
    · rw [inv_some hr]
      simp only [Option.some.injEq]
      constructor
      · intro h
        have h1 : r * r = 1 := by
          calc r * r = r * r⁻¹ := by rw [h]
            _ = 1 := mul_inv_cancel₀ hr
        exact mul_self_eq_one_iff.mp h1
      · rintro (rfl | rfl) <;> norm_num

/-- **Os pontos fixos de `neg` são `0` e `∞`.** -/
theorem neg_fixed (x : RetaProj) :
    ATK.LinhasNovas.neg x = x ↔ x = some 0 ∨ x = infinito := by
  rcases x with _ | r
  · simp [ATK.LinhasNovas.neg, infinito]
  · simp only [ATK.LinhasNovas.neg, Option.some.injEq, infinito, reduceCtorEq, or_false]
    constructor <;> intro h <;> linarith

theorem neg_involutive : Function.Involutive ATK.LinhasNovas.neg := by
  intro x; rcases x with _ | r <;> simp [ATK.LinhasNovas.neg]

theorem inv_involutive : Function.Involutive ATK.LinhasNovas.inv := ATK.LinhasNovas.inv_inv

/-- **`neg ∘ inv` é involução**: fecha o grupo `{id, inv, neg, neg ∘ inv} ≅ (ℤ/2)²`. -/
theorem neg_inv_involutive : Function.Involutive (ATK.LinhasNovas.neg ∘ ATK.LinhasNovas.inv) := by
  intro x
  simp only [Function.comp_apply]
  rw [ATK.LinhasNovas.inv_neg, neg_involutive (ATK.LinhasNovas.inv (ATK.LinhasNovas.inv x)),
    ATK.LinhasNovas.inv_inv]

end RetaProjetiva

/-! ## Colapso `∞ = 0` -/

namespace Colapso

/-- O quociente `ℝ ∪ {∞} → ℝ` que identifica `∞` com `0`. -/
def colapso : RetaProj → ℝ
  | none => 0
  | some x => x

@[simp] theorem colapso_inf : colapso infinito = 0 := rfl

@[simp] theorem colapso_some (x : ℝ) : colapso (some x) = x := rfl

/-- **Só `∞` e `0` são colados.** -/
theorem colapso_fiber (x y : RetaProj) :
    colapso x = colapso y ↔
      x = y ∨ (x = infinito ∧ y = some 0) ∨ (x = some 0 ∧ y = infinito) := by
  rcases x with _ | a <;> rcases y with _ | b <;> simp [colapso, infinito, eq_comm]

/-- **O colapso comuta com a inversão**: leva a da reta projetiva na convenção `0⁻¹ = 0`. -/
theorem colapso_inv (x : RetaProj) : colapso (ATK.LinhasNovas.inv x) = (colapso x)⁻¹ := by
  rcases x with _ | r
  · simp [colapso, ATK.LinhasNovas.inv]
  · by_cases hr : r = 0
    · subst hr; simp [colapso, ATK.LinhasNovas.inv]
    · simp [colapso, ATK.LinhasNovas.inv, hr]

/-- Em `ℝ` (convenção `0⁻¹ = 0`), os fixos da inversão são `{−1, 0, 1}`: o `0` ganha o papel. -/
theorem inv_real_fixed (x : ℝ) : x⁻¹ = x ↔ x = 1 ∨ x = -1 ∨ x = 0 := by
  by_cases hx : x = 0
  · subst hx; simp
  · constructor
    · intro h
      have h1 : x * x = 1 := by
        calc x * x = x * x⁻¹ := by rw [h]
          _ = 1 := mul_inv_cancel₀ hx
      rcases mul_self_eq_one_iff.mp h1 with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rintro (rfl | rfl | rfl) <;> norm_num

/-- A inversão de `ℝ` continua bijetiva (é involutiva). -/
theorem inv_real_bijective : Function.Bijective (fun x : ℝ => x⁻¹) :=
  _root_.inv_involutive.bijective

end Colapso

/-! ## Cauda: `ℤ[1/10]` -/

namespace Cauda

/-- As frações com cauda decimal finita, como conjunto. -/
def conjunto : Set ℝ := {x | CaudaFinita x}

/-- **`ℤ[1/10]` é um subanel de `ℝ`.** -/
def subanel : Subring ℝ where
  carrier := conjunto
  zero_mem' := show CaudaFinita 0 from ⟨0, 0, by norm_num⟩
  one_mem' := show CaudaFinita 1 from ⟨1, 0, by norm_num⟩
  add_mem' := by
    rintro x y ⟨k₁, n₁, rfl⟩ ⟨k₂, n₂, rfl⟩
    refine ⟨k₁ * 10 ^ n₂ + k₂ * 10 ^ n₁, n₁ + n₂, ?_⟩
    push_cast
    rw [pow_add]
    field_simp
  mul_mem' := by
    rintro x y ⟨k₁, n₁, rfl⟩ ⟨k₂, n₂, rfl⟩
    refine ⟨k₁ * k₂, n₁ + n₂, ?_⟩
    push_cast
    rw [pow_add]
    field_simp
  neg_mem' := by
    rintro x ⟨k, n, rfl⟩
    exact ⟨-k, n, by push_cast; ring⟩

/-- **Enumerável.** -/
theorem conjunto_countable : conjunto.Countable :=
  (Set.countable_range fun p : ℤ × ℕ => (p.1 : ℝ) / 10 ^ p.2).mono
    fun x (hx : CaudaFinita x) => by
      obtain ⟨k, n, h⟩ := hx
      exact ⟨(k, n), h.symm⟩

/-- **Denso em `ℝ`**: dado `x` e `ε > 0`, `⌊x·10ⁿ⌋/10ⁿ` fica a menos de `ε` de `x` com `10⁻ⁿ < ε`. -/
theorem conjunto_dense : Dense conjunto := by
  rw [Metric.dense_iff]
  intro x ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 10 : ℝ) < 1)
  set P : ℝ := 10 ^ n with hP
  have hP0 : 0 < P := by positivity
  have hεP : 1 < ε * P := by
    rw [one_div_pow, ← hP, div_lt_iff₀ hP0] at hn
    linarith
  set f : ℝ := (⌊x * P⌋ : ℝ) with hf
  have h1 : f ≤ x * P := Int.floor_le _
  have h2 : x * P < f + 1 := Int.lt_floor_add_one _
  refine ⟨f / P, ?_, ⟨⌊x * P⌋, n, rfl⟩⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  have e : f / P - x = (f - x * P) / P := by field_simp
  rw [e]
  constructor
  · rw [lt_div_iff₀ hP0]; nlinarith
  · rw [div_lt_iff₀ hP0]; nlinarith

/-- **Não é corpo**: `3 ∈`, mas `1/3 ∉`. -/
theorem nao_corpo : (3 : ℝ) ∈ subanel ∧ (1 / 3 : ℝ) ∉ subanel :=
  ⟨⟨3, 0, by norm_num⟩, um_terco_cauda_infinita⟩

end Cauda

/-! ## Involução com pontos fixos -/

/-- Uma involução com o seu conjunto de pontos fixos. -/
structure InvolucaoComFixos (α : Type*) where
  σ : α → α
  involutiva : Function.Involutive σ
  fixos : Set α
  mem_fixos : ∀ x, x ∈ fixos ↔ σ x = x

namespace InvolucaoComFixos

/-- Construtor canônico: os fixos de uma involução, por definição. -/
def deInvolutiva {α : Type*} (σ : α → α) (h : Function.Involutive σ) : InvolucaoComFixos α :=
  ⟨σ, h, {x | σ x = x}, fun _ => Iff.rfl⟩

/-- A simetria `x ↦ a − x`. -/
def centro {α : Type*} [Field α] (a : α) : InvolucaoComFixos α :=
  deInvolutiva (fun x => a - x) fun x => by ring

/-- **Os fixos de `x ↦ a − x` são `{a/2}`.** -/
theorem centro_fixos {α : Type*} [Field α] [CharZero α] (a : α) : (centro a).fixos = {a / 2} := by
  ext x
  simp only [centro, deInvolutiva, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact Meio.half_fixed_point a x

/-- `inv` na reta projetiva. -/
noncomputable def invProj : InvolucaoComFixos RetaProj :=
  deInvolutiva ATK.LinhasNovas.inv RetaProjetiva.inv_involutive

/-- `neg` na reta projetiva. -/
def negProj : InvolucaoComFixos RetaProj :=
  deInvolutiva ATK.LinhasNovas.neg RetaProjetiva.neg_involutive

theorem invProj_fixos : invProj.fixos = {some 1, some (-1)} := by
  ext x
  simp only [invProj, deInvolutiva, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact RetaProjetiva.inv_fixed x

theorem negProj_fixos : negProj.fixos = {some 0, infinito} := by
  ext x
  simp only [negProj, deInvolutiva, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact RetaProjetiva.neg_fixed x

end InvolucaoComFixos

/-! ## Cancelamento, `ℚ`, cauda finita e centro afim -/

namespace Extras

/-- **Num monoide cancelativo, `x + a = x` só com `a = 0`**: por isso o "natural final" exige
perder o cancelamento (`enat_sem_cancelamento`). -/
theorem no_fixpoint_of_cancelative {M : Type*} [AddLeftCancelMonoid M] {a : M} (ha : a ≠ 0)
    (x : M) : x + a ≠ x := fun h => ha (add_eq_left.mp h)

/-- `ℕ∞` não é cancelativo. -/
theorem enat_nao_cancelativo : ¬ ∀ a b c : ℕ∞, a + b = a + c → b = c := fun h =>
  one_ne_zero (h ⊤ 1 0 (by simp))

/-- **Em `ℚ` também não há maior negativo** (`r/2` fica entre `r` e `0`): a linha só é
consistente em `ℤ`, não por densidade. -/
theorem rat_sem_maior_negativo : ¬ ∃ r : ℚ, r < 0 ∧ ∀ x : ℚ, x < 0 → x ≤ r := by
  rintro ⟨r, hr, h⟩
  have := h (r / 2) (by linarith)
  linarith

/-- **Cauda finita ⟺ algum `10ⁿ · x` é inteiro.** -/
theorem caudaFinita_iff (x : ℝ) : CaudaFinita x ↔ ∃ (n : ℕ) (k : ℤ), x * 10 ^ n = k := by
  constructor
  · rintro ⟨k, n, rfl⟩
    exact ⟨n, k, by field_simp⟩
  · rintro ⟨n, k, h⟩
    exact ⟨k, n, by rw [← h]; field_simp⟩

/-- O centro de `x ↦ a − x` num `ℚ`-módulo qualquer: o único fixo é `(1/2) • a`. -/
theorem centro_afim {M : Type*} [AddCommGroup M] [Module ℚ M] (a x : M) :
    a - x = x ↔ x = (1 / 2 : ℚ) • a := by
  constructor
  · intro h
    have ha : a = (2 : ℚ) • x := by rw [two_smul]; nth_rw 1 [← h]; abel
    rw [ha, smul_smul]; norm_num
  · rintro rfl
    module

end Extras

namespace InvolucaoComFixos

/-- **A simetria `x ↦ a − x` num `ℚ`-módulo**, com fixos `{(1/2) • a}`: generaliza `centro`
de corpos para vetores (por exemplo `ℂ`, `ℝⁿ`). -/
def ofAffineCenter {M : Type*} [AddCommGroup M] [Module ℚ M] (a : M) : InvolucaoComFixos M :=
  ⟨fun x => a - x, fun x => sub_sub_cancel a x, {(1 / 2 : ℚ) • a}, fun x => by
    rw [Set.mem_singleton_iff]; exact (Extras.centro_afim a x).symm⟩

theorem ofAffineCenter_fixos {M : Type*} [AddCommGroup M] [Module ℚ M] (a : M) :
    (ofAffineCenter a).fixos = {(1 / 2 : ℚ) • a} := rfl

end InvolucaoComFixos

end ATK.LinhasNovas

#print axioms ATK.LinhasNovas.Meio.half_fixed_point
#print axioms ATK.LinhasNovas.Meio.half_normalized
#print axioms ATK.LinhasNovas.Meio.half_center_invariant
#print axioms ATK.LinhasNovas.Truncamento.trunc_monotone
#print axioms ATK.LinhasNovas.Truncamento.trunc_iUnion
#print axioms ATK.LinhasNovas.Truncamento.trunc_injective
#print axioms ATK.LinhasNovas.RetaProjetiva.inv_some
#print axioms ATK.LinhasNovas.RetaProjetiva.inv_fixed
#print axioms ATK.LinhasNovas.RetaProjetiva.neg_fixed
#print axioms ATK.LinhasNovas.RetaProjetiva.neg_involutive
#print axioms ATK.LinhasNovas.RetaProjetiva.inv_involutive
#print axioms ATK.LinhasNovas.RetaProjetiva.neg_inv_involutive
#print axioms ATK.LinhasNovas.Colapso.colapso_inf
#print axioms ATK.LinhasNovas.Colapso.colapso_some
#print axioms ATK.LinhasNovas.Colapso.colapso_fiber
#print axioms ATK.LinhasNovas.Colapso.colapso_inv
#print axioms ATK.LinhasNovas.Colapso.inv_real_fixed
#print axioms ATK.LinhasNovas.Colapso.inv_real_bijective
#print axioms ATK.LinhasNovas.Cauda.conjunto_countable
#print axioms ATK.LinhasNovas.Cauda.conjunto_dense
#print axioms ATK.LinhasNovas.Cauda.nao_corpo
#print axioms ATK.LinhasNovas.InvolucaoComFixos.centro_fixos
#print axioms ATK.LinhasNovas.InvolucaoComFixos.invProj_fixos
#print axioms ATK.LinhasNovas.InvolucaoComFixos.negProj_fixos
#print axioms ATK.LinhasNovas.Truncamento.trunc_tabela
#print axioms ATK.LinhasNovas.Extras.no_fixpoint_of_cancelative
#print axioms ATK.LinhasNovas.Extras.enat_nao_cancelativo
#print axioms ATK.LinhasNovas.Extras.rat_sem_maior_negativo
#print axioms ATK.LinhasNovas.Extras.caudaFinita_iff
#print axioms ATK.LinhasNovas.Extras.centro_afim
#print axioms ATK.LinhasNovas.InvolucaoComFixos.ofAffineCenter_fixos
