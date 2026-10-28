/-
ATK.Base (Y3, forma abstrata) — Positividade por reflexão.

Lema central de Osterwalder–Seiler.  O espaço de configurações é `Ω = X × X` (metade negativa ×
metade positiva da rede), com a medida produto `μ ⊗ μ` (para a teoria de calibre: a medida de Haar
produto de `ATK.BaseWilsonMedida`) e a reflexão `θ(a, b) = (b, a)`.  Se a ação se decompõe como

  `−S(a, b) = B(a) + B(b) + Σᵢ Cᵢ(a) Cᵢ(b)`

(parte de cada metade + termos de cruzamento com coeficientes positivos), então para toda
observável `F` da metade positiva

  `⟨Θ(F) · F⟩ = ∫ F(a) F(b) e^{−S(a,b)} d(μ ⊗ μ) ≥ 0`.

* **`cruz_pow`**: `(Σᵢ Cᵢ(a)Cᵢ(b))ⁿ = Σ_{σ : Fin n → ι} (∏ₖ C_{σk}(a)) (∏ₖ C_{σk}(b))`;
* **`momento_nonneg`**: `∫ f(a) f(b) d(μ⊗μ) = (∫ f)² ≥ 0`;
* **`termo_nonneg`**: cada termo da série de `e^{cruz}` tem integral `≥ 0`;
* **`positividade_reflexao`**: a desigualdade acima, por troca de série e integral
  (convergência dominada, funções limitadas, `μ` finita);
* **`positividade_reflexao_coef`**: a mesma coisa com coeficientes `cᵢ ≥ 0` explícitos.

A decomposição concreta da ação de Wilson (`Re tr` de plaquetas que cruzam o plano) nessa forma,
o gap em acoplamento forte e o limite contínuo continuam em aberto como bases (Y3'–Y5).
-/
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

open MeasureTheory Finset
open scoped Nat

namespace ATK.BasePositividadeReflexao

variable {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]

/-- Termo de cruzamento `E(a, b) = Σᵢ Cᵢ(a) Cᵢ(b)`. -/
def cruz (C : ι → X → ℝ) (a b : X) : ℝ := ∑ i, C i a * C i b

/-- Produto ao longo de uma palavra `σ`. -/
def prodP (C : ι → X → ℝ) {n : ℕ} (σ : Fin n → ι) (a : X) : ℝ := ∏ k, C (σ k) a

/-- **Expansão tensorial** de `Eⁿ`. -/
theorem cruz_pow (C : ι → X → ℝ) (n : ℕ) (a b : X) :
    cruz C a b ^ n = ∑ σ : Fin n → ι, prodP C σ a * prodP C σ b := by
  classical
  rw [cruz, ← Fin.prod_const n, Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ, prodP, Finset.prod_mul_distrib]

variable (μ : Measure X) [IsFiniteMeasure μ]

/-- `∫ f(a) f(b) d(μ ⊗ μ) = (∫ f)² ≥ 0`. -/
theorem momento_nonneg (f : X → ℝ) : 0 ≤ ∫ z, f z.1 * f z.2 ∂(μ.prod μ) := by
  rw [integral_prod_mul]
  exact mul_self_nonneg _

/-- Funções mensuráveis limitadas são integráveis contra uma medida finita. -/
theorem integrable_lim {Y : Type*} [MeasurableSpace Y] (ρ : Measure Y) [IsFiniteMeasure ρ]
    {f : Y → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ y, |f y| ≤ M) : Integrable f ρ :=
  Integrable.of_bound hf.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM y)

theorem measurable_prodP {C : ι → X → ℝ} (hC : ∀ i, Measurable (C i)) {n : ℕ} (σ : Fin n → ι) :
    Measurable (prodP C σ) :=
  Finset.measurable_prod _ fun k _ => hC (σ k)

theorem abs_prodP_le {C : ι → X → ℝ} {MC : ℝ} (hCb : ∀ i a, |C i a| ≤ MC) {n : ℕ}
    (σ : Fin n → ι) (a : X) : |prodP C σ a| ≤ MC ^ n := by
  rw [prodP, Finset.abs_prod]
  calc ∏ k, |C (σ k) a| ≤ ∏ _k : Fin n, MC :=
        Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) (fun k _ => hCb (σ k) a)
    _ = MC ^ n := by rw [Fin.prod_const]

theorem abs_cruz_le {C : ι → X → ℝ} {MC : ℝ} (hCb : ∀ i a, |C i a| ≤ MC) (a b : X) :
    |cruz C a b| ≤ Fintype.card ι * MC ^ 2 := by
  unfold cruz
  calc |∑ i, C i a * C i b| ≤ ∑ i, |C i a * C i b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, MC ^ 2 := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, sq]
        exact mul_le_mul (hCb i a) (hCb i b) (abs_nonneg _) (le_trans (abs_nonneg _) (hCb i a))
    _ = Fintype.card ι * MC ^ 2 := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Termo `n` da série: `G(a) G(b) Eⁿ/n!`. -/
noncomputable def termo (G : X → ℝ) (C : ι → X → ℝ) (n : ℕ) (z : X × X) : ℝ :=
  G z.1 * G z.2 * (cruz C z.1 z.2 ^ n / n !)

theorem termo_eq (G : X → ℝ) (C : ι → X → ℝ) (n : ℕ) (z : X × X) :
    termo G C n z = ∑ σ : Fin n → ι,
      (1 / (n ! : ℝ)) * ((G z.1 * prodP C σ z.1) * (G z.2 * prodP C σ z.2)) := by
  rw [termo, cruz_pow, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

/-- **Cada termo da série tem integral não negativa.** -/
theorem termo_nonneg {G : X → ℝ} {C : ι → X → ℝ} (hG : Measurable G) (hC : ∀ i, Measurable (C i))
    {MG MC : ℝ} (hGb : ∀ a, |G a| ≤ MG) (hCb : ∀ i a, |C i a| ≤ MC) (n : ℕ) :
    0 ≤ ∫ z, termo G C n z ∂(μ.prod μ) := by
  have hg : ∀ σ : Fin n → ι, Integrable (fun a => G a * prodP C σ a) μ := by
    intro σ
    refine integrable_lim μ (hG.mul (measurable_prodP hC σ)) (M := MG * MC ^ n) fun a => ?_
    rw [abs_mul]
    exact mul_le_mul (hGb a) (abs_prodP_le hCb σ a) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hGb a))
  simp_rw [termo_eq]
  rw [integral_finsetSum _ fun σ _ => ((hg σ).mul_prod (hg σ)).const_mul _]
  refine Finset.sum_nonneg fun σ _ => ?_
  rw [integral_const_mul]
  exact mul_nonneg (by positivity) (momento_nonneg μ fun a => G a * prodP C σ a)

/-- Série exponencial real. -/
theorem hasSum_exp (x : ℝ) : HasSum (fun n => x ^ n / n !) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp x

/-- **Positividade por reflexão** (forma abstrata de Osterwalder–Seiler). -/
theorem positividade_reflexao {F B : X → ℝ} {C : ι → X → ℝ}
    (hF : Measurable F) (hB : Measurable B) (hC : ∀ i, Measurable (C i))
    {MF MB MC : ℝ} (hFb : ∀ a, |F a| ≤ MF) (hBb : ∀ a, |B a| ≤ MB) (hCb : ∀ i a, |C i a| ≤ MC) :
    0 ≤ ∫ z, F z.1 * F z.2 * Real.exp (B z.1 + B z.2 + cruz C z.1 z.2) ∂(μ.prod μ) := by
  set G : X → ℝ := fun a => F a * Real.exp (B a) with hGdef
  set MG : ℝ := MF * Real.exp MB
  have hG : Measurable G := hF.mul (Real.measurable_exp.comp hB)
  have hGb : ∀ a, |G a| ≤ MG := by
    intro a
    rw [hGdef, abs_mul, Real.abs_exp]
    exact mul_le_mul (hFb a) (Real.exp_le_exp.mpr (le_trans (le_abs_self _) (hBb a)))
      (Real.exp_pos _).le (le_trans (abs_nonneg _) (hFb a))
  set ME : ℝ := Fintype.card ι * MC ^ 2
  -- série pontual
  have hsum : ∀ z : X × X, HasSum (fun n => termo G C n z)
      (F z.1 * F z.2 * Real.exp (B z.1 + B z.2 + cruz C z.1 z.2)) := by
    intro z
    have h := (hasSum_exp (cruz C z.1 z.2)).mul_left (G z.1 * G z.2)
    have e : F z.1 * F z.2 * Real.exp (B z.1 + B z.2 + cruz C z.1 z.2) =
        G z.1 * G z.2 * Real.exp (cruz C z.1 z.2) := by
      simp only [hGdef, Real.exp_add]
      ring
    rw [e]
    exact h
  -- cotas
  have hbound : ∀ n (z : X × X), |termo G C n z| ≤ MG ^ 2 * |ME| ^ n / n ! := by
    intro n z
    have hE : |cruz C z.1 z.2| ≤ |ME| := le_trans (abs_cruz_le hCb z.1 z.2) (le_abs_self _)
    have hMG : 0 ≤ MG := le_trans (abs_nonneg _) (hGb z.1)
    rw [termo, abs_mul, abs_mul, abs_div, abs_pow, Nat.abs_cast]
    have h1 : |G z.1| * |G z.2| ≤ MG ^ 2 := by
      rw [sq]; exact mul_le_mul (hGb _) (hGb _) (abs_nonneg _) hMG
    have h2 : |cruz C z.1 z.2| ^ n / n ! ≤ |ME| ^ n / n ! :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hE n) (Nat.cast_nonneg _)
    calc |G z.1| * |G z.2| * (|cruz C z.1 z.2| ^ n / n !)
        ≤ MG ^ 2 * (|ME| ^ n / n !) :=
          mul_le_mul h1 h2 (div_nonneg (pow_nonneg (abs_nonneg _) _) (Nat.cast_nonneg _))
            (sq_nonneg _)
      _ = MG ^ 2 * |ME| ^ n / n ! := by ring
  have hmeas : ∀ n, Measurable (termo G C n) := by
    intro n
    unfold termo cruz
    exact ((hG.comp measurable_fst).mul (hG.comp measurable_snd)).mul
      ((Finset.measurable_sum _ fun i _ =>
        ((hC i).comp measurable_fst).mul ((hC i).comp measurable_snd)).pow_const n |>.div_const _)
  have hint : ∀ n, Integrable (termo G C n) (μ.prod μ) :=
    fun n => integrable_lim (μ.prod μ) (hmeas n) (hbound n)
  have hsummable : Summable fun n => ∫ z, ‖termo G C n z‖ ∂(μ.prod μ) := by
    set K : ℝ := ∫ _z : X × X, (1 : ℝ) ∂(μ.prod μ)
    have hb : Summable fun n : ℕ => MG ^ 2 * |ME| ^ n / n ! * K := by
      have := ((Real.summable_pow_div_factorial |ME|).mul_left (MG ^ 2)).mul_right K
      refine this.congr fun n => ?_
      ring
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun z => norm_nonneg _)
      (fun n => ?_) hb
    calc ∫ z, ‖termo G C n z‖ ∂(μ.prod μ)
        ≤ ∫ _z, MG ^ 2 * |ME| ^ n / n ! * 1 ∂(μ.prod μ) := by
          refine integral_mono (hint n).norm (integrable_const _) fun z => ?_
          simp only [mul_one, Real.norm_eq_abs]
          exact hbound n z
      _ = MG ^ 2 * |ME| ^ n / n ! * K := integral_const_mul _ _
  have heq : (fun z : X × X => F z.1 * F z.2 * Real.exp (B z.1 + B z.2 + cruz C z.1 z.2)) =
      fun z => ∑' n, termo G C n z := funext fun z => ((hsum z).tsum_eq).symm
  rw [heq, ← integral_tsum_of_summable_integral_norm hint hsummable]
  exact tsum_nonneg fun n => termo_nonneg μ hG hC hGb hCb n

/-- Versão com coeficientes de cruzamento `cᵢ ≥ 0` explícitos. -/
theorem positividade_reflexao_coef {F B : X → ℝ} {C : ι → X → ℝ} {c : ι → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hF : Measurable F) (hB : Measurable B) (hC : ∀ i, Measurable (C i))
    {MF MB MC : ℝ} (hFb : ∀ a, |F a| ≤ MF) (hBb : ∀ a, |B a| ≤ MB) (hCb : ∀ i a, |C i a| ≤ MC) :
    0 ≤ ∫ z, F z.1 * F z.2 *
      Real.exp (B z.1 + B z.2 + ∑ i, c i * C i z.1 * C i z.2) ∂(μ.prod μ) := by
  set C' : ι → X → ℝ := fun i a => Real.sqrt (c i) * C i a
  have hC' : ∀ i, Measurable (C' i) := fun i => (hC i).const_mul _
  have hC'b : ∀ i a, |C' i a| ≤ (⨆ j, Real.sqrt (c j)) * MC := by
    intro i a
    have hMC : 0 ≤ MC := le_trans (abs_nonneg _) (hCb i a)
    simp only [C', abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs : Real.sqrt (c i) ≤ ⨆ j, Real.sqrt (c j) :=
      le_ciSup (f := fun j => Real.sqrt (c j)) (Set.finite_range _).bddAbove i
    exact mul_le_mul hs (hCb i a) (abs_nonneg _) (le_trans (Real.sqrt_nonneg _) hs)
  have e : ∀ a b, ∑ i, c i * C i a * C i b = cruz C' a b := by
    intro a b
    unfold cruz
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [C']
    have := Real.mul_self_sqrt (hc i)
    calc c i * C i a * C i b = (Real.sqrt (c i) * Real.sqrt (c i)) * C i a * C i b := by rw [this]
      _ = Real.sqrt (c i) * C i a * (Real.sqrt (c i) * C i b) := by ring
  simp_rw [e]
  exact positividade_reflexao μ hF hB hC' hFb hBb hC'b

/-- Reflexão `θ(a, b) = (b, a)` de `Ω = X × X`. -/
def θ (z : X × X) : X × X := (z.2, z.1)

/-- **Forma de reflexão**: para `F₊(z) = F(z.2)` (observável da metade positiva) e
`Θ(F₊) = F₊ ∘ θ`, `⟨Θ(F₊) · F₊⟩_{e^{−S}} ≥ 0`. -/
theorem positividade_reflexao_θ {F B : X → ℝ} {C : ι → X → ℝ}
    (hF : Measurable F) (hB : Measurable B) (hC : ∀ i, Measurable (C i))
    {MF MB MC : ℝ} (hFb : ∀ a, |F a| ≤ MF) (hBb : ∀ a, |B a| ≤ MB) (hCb : ∀ i a, |C i a| ≤ MC) :
    0 ≤ ∫ z, F (θ z).2 * F z.2 * Real.exp (B z.1 + B z.2 + cruz C z.1 z.2) ∂(μ.prod μ) :=
  positividade_reflexao μ hF hB hC hFb hBb hCb

end ATK.BasePositividadeReflexao

#print axioms ATK.BasePositividadeReflexao.cruz_pow
#print axioms ATK.BasePositividadeReflexao.momento_nonneg
#print axioms ATK.BasePositividadeReflexao.integrable_lim
#print axioms ATK.BasePositividadeReflexao.measurable_prodP
#print axioms ATK.BasePositividadeReflexao.abs_prodP_le
#print axioms ATK.BasePositividadeReflexao.abs_cruz_le
#print axioms ATK.BasePositividadeReflexao.termo_eq
#print axioms ATK.BasePositividadeReflexao.termo_nonneg
#print axioms ATK.BasePositividadeReflexao.hasSum_exp
#print axioms ATK.BasePositividadeReflexao.positividade_reflexao
#print axioms ATK.BasePositividadeReflexao.positividade_reflexao_coef
#print axioms ATK.BasePositividadeReflexao.positividade_reflexao_θ
