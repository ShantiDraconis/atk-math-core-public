import ATK.LigacaoNS
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# ATK — Navier–Stokes no lado de Fourier, marco NS1: álgebra e núcleos

Primeiro marco da ponte B3 (`EnstrophyBlowupCriterion modeloNS`). A solução será construída no
lado de Fourier, `v(ξ, t) = û(ξ, t) ∈ ℂ³`, pela fórmula de Duhamel

  `v(ξ, t) = e^{−c|ξ|²t} v₀(ξ) + ∫₀ᵗ e^{−c|ξ|²(t−s)} 𝐏(ξ) B(v, v)(ξ, s) ds`,   `c = 4π²ν`,

com `𝐏(ξ)` o projetor de Leray e `B` a convolução não linear. Este arquivo reúne os ingredientes
elementares:

* `C3`, `cx`, `ip` (o produto `ξ · a` com `ξ ∈ ℝ³`, `a ∈ ℂ³`), `cj` (conjugação);
* **`leray ξ`**: o projetor de Leray `a ↦ a − (ξ·a/|ξ|²) ξ` como aplicação `ℂ`-linear contínua, com
  `ip_leray` (imagem de divergência nula), `leray_of_ip_eq_zero`, **`norm_leray_le`** (norma `≤ 1`),
  `leray_neg`, `leray_cj`;
* pesos: `one_add_norm_pow_le` (desigualdade de Peetre), `integrable_inv_pow` (`(1+|ξ|)^{−m}`
  integrável em `ℝ³` para `m ≥ 4`), `Kp`;
* **`conv_bound`**: a estimativa mansa da convolução com pesos
  `(1+|ξ|)^m ∫ f(ξ−η) g(η) dη ≤ 2^m K₄ (A_m B₄ + A₄ B_m)`;
* núcleo do calor: **`kernel_bound`** `|ξ| ∫₀ᵗ e^{−c|ξ|²(t−s)} ds ≤ √(t/c)` e
  **`norm_mul_heat_le`** `|ξ| e^{−c|ξ|²τ} ≤ 1/√(cτ)`.

Só `propext`, `Classical.choice`, `Quot.sound`. Nada aqui é sobre a ponte em si: **B3 continua
aberta** e **CLOSED_MATH continua false**.
-/

set_option autoImplicit false

open MeasureTheory Real
open ATK.LigacaoNS (E3)

namespace ATK.NSFourierBase

/-! ### Vetores complexos -/

/-- `ℂ³` com a norma euclidiana. -/
abbrev C3 := EuclideanSpace ℂ (Fin 3)

/-- Complexificação de um vetor real. -/
noncomputable def cx (ξ : E3) : C3 := WithLp.toLp 2 (fun j => ((ξ j : ℝ) : ℂ))

@[simp] theorem cx_apply (ξ : E3) (j : Fin 3) : cx ξ j = ((ξ j : ℝ) : ℂ) := rfl

theorem norm_cx (ξ : E3) : ‖cx ξ‖ = ‖ξ‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [cx]

theorem cx_neg (ξ : E3) : cx (-ξ) = -cx ξ := by
  ext j
  simp

/-- O produto `ξ · a = Σ_j ξ_j a_j`. -/
noncomputable def ip (ξ : E3) (a : C3) : ℂ := ∑ j, ((ξ j : ℝ) : ℂ) * a j

theorem ip_eq_inner (ξ : E3) (a : C3) : ip ξ a = inner ℂ (cx ξ) a := by
  simp [ip, PiLp.inner_apply, mul_comm]

theorem norm_ip_le (ξ : E3) (a : C3) : ‖ip ξ a‖ ≤ ‖ξ‖ * ‖a‖ := by
  rw [ip_eq_inner, ← norm_cx]
  exact norm_inner_le_norm _ _

theorem ip_add (ξ : E3) (a b : C3) : ip ξ (a + b) = ip ξ a + ip ξ b := by
  simp [ip, mul_add, Finset.sum_add_distrib]

theorem ip_sub (ξ : E3) (a b : C3) : ip ξ (a - b) = ip ξ a - ip ξ b := by
  simp [ip, mul_sub, Finset.sum_sub_distrib]

theorem ip_smul (ξ : E3) (c : ℂ) (a : C3) : ip ξ (c • a) = c * ip ξ a := by
  simp [ip, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem ip_zero (ξ : E3) : ip ξ 0 = 0 := by simp [ip]

theorem ip_zero_left (a : C3) : ip 0 a = 0 := by simp [ip]

theorem ip_neg_left (ξ : E3) (a : C3) : ip (-ξ) a = -ip ξ a := by
  simp [ip, Finset.sum_neg_distrib]

theorem ip_cx (ξ : E3) : ip ξ (cx ξ) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [ip, sq]

/-- Linearidade de `ip ξ` como aplicação contínua. -/
noncomputable def ipL (ξ : E3) : C3 →L[ℂ] ℂ := innerSL ℂ (cx ξ)

theorem ipL_apply (ξ : E3) (a : C3) : ipL ξ a = ip ξ a := by
  rw [ip_eq_inner]
  rfl

/-! ### Conjugação -/

/-- Conjugação complexa coordenada a coordenada. -/
noncomputable def cj (a : C3) : C3 := WithLp.toLp 2 (fun j => (starRingEnd ℂ) (a j))

@[simp] theorem cj_apply (a : C3) (j : Fin 3) : cj a j = (starRingEnd ℂ) (a j) := rfl

theorem cj_cj (a : C3) : cj (cj a) = a := by
  ext j
  simp

theorem norm_cj (a : C3) : ‖cj a‖ = ‖a‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp

theorem cj_add (a b : C3) : cj (a + b) = cj a + cj b := by
  ext j
  simp

theorem cj_sub (a b : C3) : cj (a - b) = cj a - cj b := by
  ext j
  simp

theorem cj_smul (c : ℂ) (a : C3) : cj (c • a) = (starRingEnd ℂ) c • cj a := by
  ext j
  simp

theorem cj_cx (ξ : E3) : cj (cx ξ) = cx ξ := by
  ext j
  simp

theorem cj_zero : cj 0 = 0 := by
  ext j
  simp

theorem ip_cj (ξ : E3) (a : C3) : ip ξ (cj a) = (starRingEnd ℂ) (ip ξ a) := by
  simp [ip, map_sum]

/-- A conjugação como aplicação `ℝ`-linear contínua (para comutar com integrais). -/
noncomputable def cjL : C3 →L[ℝ] C3 :=
  LinearMap.toContinuousLinearMap
    { toFun := cj
      map_add' := cj_add
      map_smul' := fun r a => by
        ext j
        simp only [cj_apply, PiLp.smul_apply, RingHom.id_apply]
        rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal] }

theorem cjL_apply (a : C3) : cjL a = cj a := rfl

/-! ### O projetor de Leray -/

/-- **Projetor de Leray** `𝐏(ξ) a = a − (ξ·a / |ξ|²) ξ` (em `ξ = 0`, a identidade). -/
noncomputable def leray (ξ : E3) : C3 →L[ℂ] C3 :=
  ContinuousLinearMap.id ℂ C3 - ((((‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹) • (ipL ξ).smulRight (cx ξ)

theorem leray_apply (ξ : E3) (a : C3) :
    leray ξ a = a - ((((‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹ * ip ξ a) • cx ξ := by
  simp [leray, ipL_apply, mul_smul]

theorem leray_zero_left (a : C3) : leray 0 a = a := by
  simp [leray_apply]

/-- A imagem de `𝐏(ξ)` tem divergência nula: `ξ · 𝐏(ξ) a = 0`. -/
theorem ip_leray (ξ : E3) (a : C3) : ip ξ (leray ξ a) = 0 := by
  rw [leray_apply, ip_sub, ip_smul, ip_cx]
  by_cases hξ : ξ = 0
  · subst hξ
    simp [ip_zero_left]
  · have h : ((‖ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
      exact_mod_cast pow_ne_zero 2 this
    field_simp
    ring

/-- `𝐏(ξ)` fixa os vetores de divergência nula. -/
theorem leray_of_ip_eq_zero {ξ : E3} {a : C3} (h : ip ξ a = 0) : leray ξ a = a := by
  simp [leray_apply, h]

theorem leray_leray (ξ : E3) (a : C3) : leray ξ (leray ξ a) = leray ξ a :=
  leray_of_ip_eq_zero (ip_leray ξ a)

/-- **`‖𝐏(ξ) a‖ ≤ ‖a‖`** (projeção ortogonal). -/
theorem norm_leray_le (ξ : E3) (a : C3) : ‖leray ξ a‖ ≤ ‖a‖ := by
  set c : ℂ := (((‖ξ‖ ^ 2 : ℝ) : ℂ))⁻¹ * ip ξ a
  have hdec : a = leray ξ a + c • cx ξ := by
    rw [leray_apply]
    abel
  have horth : inner ℂ (leray ξ a) (c • cx ξ) = 0 := by
    rw [inner_smul_right, ← inner_conj_symm, ← ip_eq_inner, ip_leray]
    simp
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [← hdec] at hp
  have h0 : 0 ≤ ‖c • cx ξ‖ * ‖c • cx ξ‖ := mul_self_nonneg _
  have : ‖leray ξ a‖ * ‖leray ξ a‖ ≤ ‖a‖ * ‖a‖ := by linarith
  exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).mpr this

theorem leray_neg (ξ : E3) : leray (-ξ) = leray ξ := by
  ext1 a
  rw [leray_apply, leray_apply, ip_neg_left, cx_neg, norm_neg]
  simp [smul_neg, neg_smul, mul_neg]

theorem leray_cj (ξ : E3) (a : C3) : leray ξ (cj a) = cj (leray ξ a) := by
  rw [leray_apply, leray_apply, cj_sub, cj_smul, ip_cj, cj_cx]
  congr 2
  simp [map_mul, map_inv₀]

theorem norm_leray_smul_le (ξ : E3) (c : ℂ) (a : C3) : ‖leray ξ (c • a)‖ ≤ ‖c‖ * ‖a‖ := by
  rw [map_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_leray_le ξ a) (norm_nonneg _)

/-! ### Pesos -/

theorem one_add_norm_pos (ξ : E3) : 0 < 1 + ‖ξ‖ := by positivity

/-- Peetre: `1 + |ξ| ≤ (1 + |ξ − η|) + (1 + |η|)`. -/
theorem one_add_norm_le_add (ξ η : E3) : 1 + ‖ξ‖ ≤ (1 + ‖ξ - η‖) + (1 + ‖η‖) := by
  have h2 : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by
    calc ‖ξ‖ = ‖(ξ - η) + η‖ := by rw [sub_add_cancel]
      _ ≤ ‖ξ - η‖ + ‖η‖ := norm_add_le _ _
  linarith

/-- **Peetre com potência**: `(1+|ξ|)^m ≤ 2^m ((1+|ξ−η|)^m + (1+|η|)^m)`. -/
theorem one_add_norm_pow_le (ξ η : E3) (m : ℕ) :
    (1 + ‖ξ‖) ^ m ≤ 2 ^ m * ((1 + ‖ξ - η‖) ^ m + (1 + ‖η‖) ^ m) := by
  set a := 1 + ‖ξ - η‖
  set b := 1 + ‖η‖
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have h1 : 1 + ‖ξ‖ ≤ 2 * max a b := by
    have := one_add_norm_le_add ξ η
    have := le_max_left a b
    have := le_max_right a b
    linarith
  have h2 : (1 + ‖ξ‖) ^ m ≤ (2 * max a b) ^ m :=
    pow_le_pow_left₀ (by positivity) h1 m
  have h3 : (max a b) ^ m ≤ a ^ m + b ^ m := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]
      have := pow_nonneg ha m
      linarith
    · rw [max_eq_left h]
      have := pow_nonneg hb m
      linarith
  calc (1 + ‖ξ‖) ^ m ≤ (2 * max a b) ^ m := h2
    _ = 2 ^ m * (max a b) ^ m := mul_pow _ _ _
    _ ≤ 2 ^ m * (a ^ m + b ^ m) := mul_le_mul_of_nonneg_left h3 (by positivity)

theorem finrank_E3 : Module.finrank ℝ E3 = 3 := by simp

/-- `(1+|ξ|)^{−m}` é integrável em `ℝ³` para `m ≥ 4`. -/
theorem integrable_inv_pow {m : ℕ} (hm : 4 ≤ m) :
    Integrable (fun ξ : E3 => ((1 + ‖ξ‖) ^ m)⁻¹) := by
  have h := integrable_one_add_norm (E := E3) (μ := volume) (r := (m : ℝ))
    (by rw [finrank_E3]; exact_mod_cast (by omega : 3 < m))
  refine h.congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- `K_m = ∫ (1+|ξ|)^{−m} dξ`. -/
noncomputable def Kp (m : ℕ) : ℝ := ∫ ξ : E3, ((1 + ‖ξ‖) ^ m)⁻¹

theorem Kp_nonneg (m : ℕ) : 0 ≤ Kp m :=
  integral_nonneg fun ξ => by positivity

theorem integral_inv_pow_sub (m : ℕ) (ξ : E3) :
    ∫ η : E3, ((1 + ‖ξ - η‖) ^ m)⁻¹ = Kp m :=
  integral_sub_left_eq_self (fun ζ : E3 => ((1 + ‖ζ‖) ^ m)⁻¹) volume ξ

theorem integrable_inv_pow_sub {m : ℕ} (hm : 4 ≤ m) (ξ : E3) :
    Integrable (fun η : E3 => ((1 + ‖ξ - η‖) ^ m)⁻¹) :=
  (integrable_inv_pow hm).comp_sub_left ξ

/-- Cota com peso ⇒ cota pela função peso. -/
theorem le_of_mul_le {f : E3 → ℝ} {m : ℕ} {A : ℝ} (hA : ∀ ζ, f ζ * (1 + ‖ζ‖) ^ m ≤ A)
    (ζ : E3) : f ζ ≤ A * ((1 + ‖ζ‖) ^ m)⁻¹ := by
  have hp : 0 < (1 + ‖ζ‖) ^ m := by positivity
  rw [le_mul_inv_iff₀ hp]
  exact hA ζ

/-! ### A convolução com pesos -/

/-- Integrabilidade do integrando da convolução. -/
theorem integrable_conv {f g : E3 → ℝ} (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g)
    (hf0 : ∀ ζ, 0 ≤ f ζ) (hg0 : ∀ ζ, 0 ≤ g ζ) {A B : ℝ}
    (hA : ∀ ζ, f ζ * (1 + ‖ζ‖) ^ 4 ≤ A) (hB : ∀ ζ, g ζ * (1 + ‖ζ‖) ^ 4 ≤ B) (ξ : E3) :
    Integrable (fun η => f (ξ - η) * g η) := by
  have hm : AEStronglyMeasurable (fun η => f (ξ - η) * g η) := by
    have h1 : AEStronglyMeasurable (fun η => f (ξ - η)) :=
      hf.comp_measurePreserving (Measure.measurePreserving_sub_left volume ξ)
    exact h1.mul hg
  have hA0 : 0 ≤ A := le_trans (mul_nonneg (hf0 0) (by positivity)) (hA 0)
  refine Integrable.mono' ((integrable_inv_pow le_rfl).const_mul (A * B)) hm
    (Filter.Eventually.of_forall fun η => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 _) (hg0 _))]
  have h1 : f (ξ - η) ≤ A := by
    have := hA (ξ - η)
    have hp : 1 ≤ (1 + ‖ξ - η‖) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg (ξ - η)])
    nlinarith [hf0 (ξ - η)]
  have h2 := le_of_mul_le hB η
  calc f (ξ - η) * g η ≤ A * (B * ((1 + ‖η‖) ^ 4)⁻¹) :=
        mul_le_mul h1 h2 (hg0 η) hA0
    _ = A * B * ((1 + ‖η‖) ^ 4)⁻¹ := by ring

/-- **Estimativa mansa da convolução com pesos.** Se `f, g ≥ 0` têm cotas `A₄, A_m` e `B₄, B_m`
com os pesos `(1+|·|)^4` e `(1+|·|)^m`, então
`(1+|ξ|)^m ∫ f(ξ−η) g(η) dη ≤ 2^m K₄ (A_m B₄ + A₄ B_m)`. -/
theorem conv_bound {f g : E3 → ℝ} (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g)
    (hf0 : ∀ ζ, 0 ≤ f ζ) (hg0 : ∀ ζ, 0 ≤ g ζ) (m : ℕ) {A₄ Am B₄ Bm : ℝ}
    (hA₄ : ∀ ζ, f ζ * (1 + ‖ζ‖) ^ 4 ≤ A₄) (hAm : ∀ ζ, f ζ * (1 + ‖ζ‖) ^ m ≤ Am)
    (hB₄ : ∀ ζ, g ζ * (1 + ‖ζ‖) ^ 4 ≤ B₄) (hBm : ∀ ζ, g ζ * (1 + ‖ζ‖) ^ m ≤ Bm) (ξ : E3) :
    (∫ η, f (ξ - η) * g η) * (1 + ‖ξ‖) ^ m ≤ 2 ^ m * Kp 4 * (Am * B₄ + A₄ * Bm) := by
  have hint := integrable_conv hf hg hf0 hg0 hA₄ hB₄ ξ
  have hAm0 : 0 ≤ Am := le_trans (mul_nonneg (hf0 0) (by positivity)) (hAm 0)
  have hBm0 : 0 ≤ Bm := le_trans (mul_nonneg (hg0 0) (by positivity)) (hBm 0)
  -- cota pontual do integrando com o peso
  have hpt : ∀ η, f (ξ - η) * g η * (1 + ‖ξ‖) ^ m ≤
      2 ^ m * (Am * B₄ * ((1 + ‖η‖) ^ 4)⁻¹ + A₄ * Bm * ((1 + ‖ξ - η‖) ^ 4)⁻¹) := by
    intro η
    have hP := one_add_norm_pow_le ξ η m
    have hfg : 0 ≤ f (ξ - η) * g η := mul_nonneg (hf0 _) (hg0 _)
    have e1 : f (ξ - η) * (1 + ‖ξ - η‖) ^ m * g η ≤ Am * (B₄ * ((1 + ‖η‖) ^ 4)⁻¹) :=
      mul_le_mul (hAm _) (le_of_mul_le hB₄ η) (hg0 _) hAm0
    have e2 : f (ξ - η) * (g η * (1 + ‖η‖) ^ m) ≤ (A₄ * ((1 + ‖ξ - η‖) ^ 4)⁻¹) * Bm :=
      mul_le_mul (le_of_mul_le hA₄ _) (hBm _) (by positivity [hg0 η])
        (by have := le_of_mul_le hA₄ (ξ - η); nlinarith [hf0 (ξ - η)])
    calc f (ξ - η) * g η * (1 + ‖ξ‖) ^ m
        ≤ f (ξ - η) * g η * (2 ^ m * ((1 + ‖ξ - η‖) ^ m + (1 + ‖η‖) ^ m)) :=
          mul_le_mul_of_nonneg_left hP hfg
      _ = 2 ^ m * (f (ξ - η) * (1 + ‖ξ - η‖) ^ m * g η + f (ξ - η) * (g η * (1 + ‖η‖) ^ m)) := by
          ring
      _ ≤ 2 ^ m * (Am * (B₄ * ((1 + ‖η‖) ^ 4)⁻¹) + (A₄ * ((1 + ‖ξ - η‖) ^ 4)⁻¹) * Bm) := by
          gcongr
      _ = 2 ^ m * (Am * B₄ * ((1 + ‖η‖) ^ 4)⁻¹ + A₄ * Bm * ((1 + ‖ξ - η‖) ^ 4)⁻¹) := by ring
  have hI1 := integrable_inv_pow le_rfl
  have hI2 := integrable_inv_pow_sub le_rfl ξ
  have hR : Integrable (fun η : E3 =>
      2 ^ m * (Am * B₄ * ((1 + ‖η‖) ^ 4)⁻¹ + A₄ * Bm * ((1 + ‖ξ - η‖) ^ 4)⁻¹)) :=
    ((hI1.const_mul _).add (hI2.const_mul _)).const_mul _
  rw [← integral_mul_const]
  calc ∫ η, f (ξ - η) * g η * (1 + ‖ξ‖) ^ m
      ≤ ∫ η : E3, 2 ^ m * (Am * B₄ * ((1 + ‖η‖) ^ 4)⁻¹ + A₄ * Bm * ((1 + ‖ξ - η‖) ^ 4)⁻¹) :=
        integral_mono (hint.mul_const _) hR hpt
    _ = 2 ^ m * Kp 4 * (Am * B₄ + A₄ * Bm) := by
        rw [integral_const_mul, integral_add (hI1.const_mul _) (hI2.const_mul _),
          integral_const_mul, integral_const_mul, integral_inv_pow_sub]
        unfold Kp
        ring

/-- A integral de `f` com cota de peso 4: `∫ f ≤ A₄ K₄`. -/
theorem integral_le_of_bound {f : E3 → ℝ} (hf : AEStronglyMeasurable f) (hf0 : ∀ ζ, 0 ≤ f ζ)
    {A : ℝ} (hA : ∀ ζ, f ζ * (1 + ‖ζ‖) ^ 4 ≤ A) : Integrable f ∧ ∫ ζ, f ζ ≤ A * Kp 4 := by
  have hI := (integrable_inv_pow le_rfl).const_mul A
  have hint : Integrable f := hI.mono' hf (Filter.Eventually.of_forall fun ζ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ζ)]
    exact le_of_mul_le hA ζ)
  refine ⟨hint, ?_⟩
  calc ∫ ζ, f ζ ≤ ∫ ζ : E3, A * ((1 + ‖ζ‖) ^ 4)⁻¹ := integral_mono hint hI (le_of_mul_le hA)
    _ = A * Kp 4 := by rw [integral_const_mul]; rfl

/-! ### O núcleo do calor -/

theorem integral_heat {A : ℝ} (hA : 0 < A) (t : ℝ) :
    ∫ s in (0 : ℝ)..t, exp (-(A * (t - s))) = (1 - exp (-(A * t))) / A := by
  have hd : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s => exp (-(A * (t - s))) / A) (exp (-(A * (t - s)))) s := by
    intro s _
    have h1 : HasDerivAt (fun s => -(A * (t - s))) A s := by
      have h0 : HasDerivAt (fun s => A * s - A * t) A s := by
        simpa using ((hasDerivAt_id s).const_mul A).sub_const (A * t)
      convert h0 using 1
      funext s
      ring
    have h2 := (h1.exp).div_const A
    convert h2 using 1
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_exp.comp (by fun_prop)).intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, neg_zero, exp_zero, sub_zero]
  ring

theorem one_sub_exp_neg_le_sqrt {x : ℝ} (hx : 0 ≤ x) : 1 - exp (-x) ≤ sqrt x := by
  rcases le_total x 1 with h | h
  · have h1 : 1 - exp (-x) ≤ x := by
      have := Real.add_one_le_exp (-x)
      linarith
    have h2 : x ≤ sqrt x := by
      rw [Real.le_sqrt hx hx]
      nlinarith
    linarith
  · have h1 : 1 - exp (-x) ≤ 1 := by
      have := exp_pos (-x)
      linarith
    have h2 : 1 ≤ sqrt x := by
      rw [Real.le_sqrt zero_le_one hx]
      simpa using h
    linarith

/-- **`|ξ| ∫₀ᵗ e^{−c|ξ|²(t−s)} ds ≤ √(t/c)`.** -/
theorem kernel_bound {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (ξ : E3) :
    ‖ξ‖ * ∫ s in (0 : ℝ)..t, exp (-(c * ‖ξ‖ ^ 2 * (t - s))) ≤ sqrt (t / c) := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [norm_zero, zero_mul]
    exact sqrt_nonneg _
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hA : 0 < c * ‖ξ‖ ^ 2 := by positivity
  rw [integral_heat hA]
  have hx : 0 ≤ c * ‖ξ‖ ^ 2 * t := by positivity
  have h1 := one_sub_exp_neg_le_sqrt hx
  have hs : sqrt (c * ‖ξ‖ ^ 2 * t) = ‖ξ‖ * sqrt (c * t) := by
    rw [show c * ‖ξ‖ ^ 2 * t = ‖ξ‖ ^ 2 * (c * t) by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hn.le]
  have key : 1 - exp (-(c * ‖ξ‖ ^ 2 * t)) ≤ ‖ξ‖ * sqrt (c * t) := hs ▸ h1
  calc ‖ξ‖ * ((1 - exp (-(c * ‖ξ‖ ^ 2 * t))) / (c * ‖ξ‖ ^ 2))
      = (1 - exp (-(c * ‖ξ‖ ^ 2 * t))) / (c * ‖ξ‖) := by
        field_simp
    _ ≤ (‖ξ‖ * sqrt (c * t)) / (c * ‖ξ‖) := div_le_div_of_nonneg_right key (by positivity)
    _ = sqrt (c * t) / c := by
        field_simp
    _ = sqrt (t / c) := by
        rw [show t / c = c * t / c ^ 2 by field_simp, Real.sqrt_div (by positivity),
          Real.sqrt_sq hc.le]

/-- `x e^{−a x²} ≤ 1/√a`. -/
theorem mul_exp_neg_sq_le {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    x * exp (-(a * x ^ 2)) ≤ 1 / sqrt a := by
  set y := sqrt a * x
  have hy : 0 ≤ y := by positivity
  have hsa : 0 < sqrt a := Real.sqrt_pos.mpr ha
  have hyy : y ^ 2 = a * x ^ 2 := by
    simp only [y, mul_pow, Real.sq_sqrt ha.le]
  have hexp : y ≤ exp (y ^ 2) := by
    have := Real.add_one_le_exp (y ^ 2)
    nlinarith [sq_nonneg (y - 1)]
  have h1 : y * exp (-(y ^ 2)) ≤ 1 := by
    rw [Real.exp_neg]
    rw [mul_inv_le_iff₀ (exp_pos _)]
    simpa using hexp
  rw [← hyy, le_div_iff₀ hsa]
  calc x * exp (-y ^ 2) * sqrt a = y * exp (-(y ^ 2)) := by
        simp only [y]
        ring
    _ ≤ 1 := h1

/-- **`|ξ| e^{−c|ξ|²τ} ≤ 1/√(cτ)`** para `τ > 0`. -/
theorem norm_mul_heat_le {c τ : ℝ} (hc : 0 < c) (hτ : 0 < τ) (ξ : E3) :
    ‖ξ‖ * exp (-(c * ‖ξ‖ ^ 2 * τ)) ≤ 1 / sqrt (c * τ) := by
  have := mul_exp_neg_sq_le (mul_pos hc hτ) (norm_nonneg ξ)
  convert this using 3
  ring

theorem heat_le_one {c τ : ℝ} (hc : 0 ≤ c) (hτ : 0 ≤ τ) (ξ : E3) :
    exp (-(c * ‖ξ‖ ^ 2 * τ)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have : 0 ≤ c * ‖ξ‖ ^ 2 * τ := by positivity
  linarith

end ATK.NSFourierBase

#print axioms ATK.NSFourierBase.C3
#print axioms ATK.NSFourierBase.cx
#print axioms ATK.NSFourierBase.cx_apply
#print axioms ATK.NSFourierBase.norm_cx
#print axioms ATK.NSFourierBase.cx_neg
#print axioms ATK.NSFourierBase.ip
#print axioms ATK.NSFourierBase.ip_eq_inner
#print axioms ATK.NSFourierBase.norm_ip_le
#print axioms ATK.NSFourierBase.ip_add
#print axioms ATK.NSFourierBase.ip_sub
#print axioms ATK.NSFourierBase.ip_smul
#print axioms ATK.NSFourierBase.ip_zero
#print axioms ATK.NSFourierBase.ip_zero_left
#print axioms ATK.NSFourierBase.ip_neg_left
#print axioms ATK.NSFourierBase.ip_cx
#print axioms ATK.NSFourierBase.ipL
#print axioms ATK.NSFourierBase.ipL_apply
#print axioms ATK.NSFourierBase.cj
#print axioms ATK.NSFourierBase.cj_apply
#print axioms ATK.NSFourierBase.cj_cj
#print axioms ATK.NSFourierBase.norm_cj
#print axioms ATK.NSFourierBase.cj_add
#print axioms ATK.NSFourierBase.cj_sub
#print axioms ATK.NSFourierBase.cj_smul
#print axioms ATK.NSFourierBase.cj_cx
#print axioms ATK.NSFourierBase.cj_zero
#print axioms ATK.NSFourierBase.ip_cj
#print axioms ATK.NSFourierBase.cjL
#print axioms ATK.NSFourierBase.cjL_apply
#print axioms ATK.NSFourierBase.leray
#print axioms ATK.NSFourierBase.leray_apply
#print axioms ATK.NSFourierBase.leray_zero_left
#print axioms ATK.NSFourierBase.ip_leray
#print axioms ATK.NSFourierBase.leray_of_ip_eq_zero
#print axioms ATK.NSFourierBase.leray_leray
#print axioms ATK.NSFourierBase.norm_leray_le
#print axioms ATK.NSFourierBase.leray_neg
#print axioms ATK.NSFourierBase.leray_cj
#print axioms ATK.NSFourierBase.norm_leray_smul_le
#print axioms ATK.NSFourierBase.one_add_norm_pos
#print axioms ATK.NSFourierBase.one_add_norm_le_add
#print axioms ATK.NSFourierBase.one_add_norm_pow_le
#print axioms ATK.NSFourierBase.finrank_E3
#print axioms ATK.NSFourierBase.integrable_inv_pow
#print axioms ATK.NSFourierBase.Kp
#print axioms ATK.NSFourierBase.Kp_nonneg
#print axioms ATK.NSFourierBase.integral_inv_pow_sub
#print axioms ATK.NSFourierBase.integrable_inv_pow_sub
#print axioms ATK.NSFourierBase.le_of_mul_le
#print axioms ATK.NSFourierBase.integrable_conv
#print axioms ATK.NSFourierBase.conv_bound
#print axioms ATK.NSFourierBase.integral_le_of_bound
#print axioms ATK.NSFourierBase.integral_heat
#print axioms ATK.NSFourierBase.one_sub_exp_neg_le_sqrt
#print axioms ATK.NSFourierBase.kernel_bound
#print axioms ATK.NSFourierBase.mul_exp_neg_sq_le
#print axioms ATK.NSFourierBase.norm_mul_heat_le
#print axioms ATK.NSFourierBase.heat_le_one
