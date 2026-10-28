import ATK.XiCrescimento

/-!
# ATK — Momentos de `Φ` e os coeficientes de `Ξ` (camadas M1–M2 dos "produtores")

* `Phi_pos`: **`Φ(u) > 0` para `u ≥ 0`** (cada termo `(4w² − 6w)e^{u/2−w}`, `w = πn²e^{2u} > 3/2`, é positivo).
* `mom n = 2∫₀^∞Φ(u)u^{2n}du` (`mom`), integrável e **`> 0`** (`mom_pos`).
* **M1** (`aXi_eq_mom`): **`aₙ = 2∫₀^∞Φ(u)u^{2n}du/(2n)!`** — os coeficientes de `B(w) = Σaₙwⁿ`, `B(−z²) = ξ(1/2 + iz)`,
  são momentos de uma medida positiva. Prova: `HPhi(z) = 2∫Φcos(zu)` (rodada 11) e a série do cosseno trocada com a
  integral (`hasSum_HPhi`, dominação `|Φ|(|z|u)^{2n}/(2n)! ≤ |Φ|e^{2|z|u}/4ⁿ`), mais unicidade dos coeficientes.
  Daí **`aₙ > 0` para todo `n`** (`aXi_pos`), sem hipóteses.
* **M2** (`hankel`, `mom_logconvexo`): `Σ_{i,j} cᵢcⱼm_{s+i+j} = 2∫Φu^{2s}(Σcᵢu^{2i})² ≥ 0` (Hankel positiva) e
  `m_{n+1}² ≤ mₙm_{n+2}` (Cauchy–Schwarz); para os `aₙ` (`aXi_cota_superior`):
  `a_{n+1}²((2n+2)!)² ≤ aₙ(2n)!·a_{n+2}(2n+4)!`.

**O que isto não dá.** Positividade de cada `aₙ` e de Hankel **não** implica positividade total de Toeplitz: a
log-convexidade dos momentos é uma cota *superior* para `a_{n+1}²`; a desigualdade de Turán (necessária para PF∞) é
uma cota *inferior*. A positividade total dos `aₙ` continua `OPEN_MATH` (é HR).
-/

open Complex Filter Topology Metric Set MeasureTheory
open scoped Nat

namespace ATK.XiMom

open ATK.Edrei ATK.XiTP ATK.XiCresc ATK.BaseRiemannXi
open ATK.XiPhi (Phi phiT cN hT)

/-! ## 1. `Φ > 0` -/

theorem cN_gt (n : ℕ) : 3 / 2 < cN n := by
  unfold cN
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
    nlinarith
  nlinarith [Real.pi_gt_three]

theorem phiT_pos {c u : ℝ} (hc : 3 / 2 < c) (hu : 0 ≤ u) : 0 < phiT c u := by
  unfold phiT
  have hE : 1 ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hw : 3 / 2 < c * Real.exp (2 * u) := by nlinarith
  apply mul_pos _ (ATK.XiPhi.hT_pos c u)
  nlinarith

theorem summable_phiT {u : ℝ} (hu : 0 ≤ u) : Summable fun n => phiT (cN n) u :=
  Summable.of_nonneg_of_le (fun n => (phiT_pos (cN_gt n) hu).le)
    (fun n => (le_abs_self _).trans (ATK.XiPhi.cota_phiT _ u (ATK.XiPhi.cN_ge n) hu))
    ((ATK.XiPhi.summable_exp_cN.mul_left 80).mul_right _)

/-- **`Φ(u) > 0` para `u ≥ 0`.** -/
theorem Phi_pos {u : ℝ} (hu : 0 ≤ u) : 0 < Phi u :=
  (summable_phiT hu).tsum_pos (fun n => (phiT_pos (cN_gt n) hu).le) 0 (phiT_pos (cN_gt 0) hu)

/-! ## 2. Momentos -/

/-- `mₙ = 2∫₀^∞Φ(u)u^{2n}du`. -/
noncomputable def mom (n : ℕ) : ℝ := 2 * ∫ u in Ioi (0 : ℝ), Phi u * u ^ (2 * n)

/-- `(yu)^{2n}/(2n)! ≤ e^{2yu}/4ⁿ`. -/
theorem pow_div_le {y u : ℝ} (hy : 0 ≤ y) (hu : 0 ≤ u) (n : ℕ) :
    (y * u) ^ (2 * n) / ((2 * n)! : ℝ) ≤ (1 / 4) ^ n * Real.exp ((2 * y) * u) := by
  have h := Real.pow_div_factorial_le_exp ((2 * y) * u) (by positivity) (2 * n)
  have e : ((2 * y) * u) ^ (2 * n) = 4 ^ n * (y * u) ^ (2 * n) := by
    rw [show (2 * y) * u = 2 * (y * u) by ring, mul_pow, pow_mul]
    norm_num
  rw [e, mul_div_assoc] at h
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have : (y * u) ^ (2 * n) / ((2 * n)! : ℝ) ≤ Real.exp ((2 * y) * u) / 4 ^ n := by
    rw [le_div_iff₀ h4]
    linarith
  calc _ ≤ Real.exp ((2 * y) * u) / 4 ^ n := this
    _ = (1 / 4) ^ n * Real.exp ((2 * y) * u) := by rw [div_pow, one_pow]; ring

/-- Cota pontual: `|Φ(u)|(yu)^{2n}/(2n)! ≤ (1/4)ⁿ·160e^{2y√(2y)}e^{−u}`. -/
theorem pt_le {y u : ℝ} (hy : 0 ≤ y) (hu : 0 ≤ u) (n : ℕ) :
    |Phi u| * ((y * u) ^ (2 * n) / ((2 * n)! : ℝ)) ≤
      (1 / 4) ^ n * (160 * Real.exp ((2 * y) * Real.sqrt (2 * y))) * Real.exp (-u) := by
  have h1 := pow_div_le hy hu n
  have h2 := Phi_exp_cota (y := 2 * y) (by positivity) hu
  calc |Phi u| * ((y * u) ^ (2 * n) / ((2 * n)! : ℝ))
      ≤ |Phi u| * ((1 / 4) ^ n * Real.exp ((2 * y) * u)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = (1 / 4) ^ n * (|Phi u| * Real.exp ((2 * y) * u)) := by ring
    _ ≤ (1 / 4) ^ n * (160 * Real.exp ((2 * y) * Real.sqrt (2 * y)) * Real.exp (-u)) := by gcongr
    _ = _ := by ring

theorem aesm_mom (n : ℕ) : AEStronglyMeasurable (fun u : ℝ => Phi u * u ^ (2 * n))
    (volume.restrict (Ioi 0)) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  exact (continuousOn_Phi.mono Ioi_subset_Ici_self).mul (continuous_pow _).continuousOn

theorem integrable_mom (n : ℕ) : IntegrableOn (fun u : ℝ => Phi u * u ^ (2 * n)) (Ioi 0) := by
  refine Integrable.mono' (ATK.XiPhi.integrableOn_exp_neg_mul
    ((2 * n)! * (160 * Real.exp ((2 * 1) * Real.sqrt (2 * 1))))) (aesm_mom n) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
  have hu0 : 0 ≤ u := le_of_lt hu
  have h := pt_le (y := 1) (by norm_num) hu0 n
  rw [one_mul] at h
  have hf : (0 : ℝ) < (2 * n)! := by exact_mod_cast Nat.factorial_pos _
  have h1 : (1 / 4 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hu0 _)]
  have h3 : |Phi u| * u ^ (2 * n) = (2 * n)! * (|Phi u| * (u ^ (2 * n) / (2 * n)!)) := by
    field_simp
  rw [h3]
  have hK : 0 ≤ 160 * Real.exp ((2 * 1) * Real.sqrt (2 * 1)) * Real.exp (-u) := by positivity
  calc (2 * n)! * (|Phi u| * (u ^ (2 * n) / (2 * n)!))
      ≤ (2 * n)! * ((1 / 4) ^ n * (160 * Real.exp ((2 * 1) * Real.sqrt (2 * 1))) * Real.exp (-u)) :=
        mul_le_mul_of_nonneg_left h hf.le
    _ ≤ (2 * n)! * (160 * Real.exp ((2 * 1) * Real.sqrt (2 * 1)) * Real.exp (-u)) := by
        apply mul_le_mul_of_nonneg_left _ hf.le
        calc (1 / 4 : ℝ) ^ n * (160 * Real.exp ((2 * 1) * Real.sqrt (2 * 1))) * Real.exp (-u)
            = (1 / 4 : ℝ) ^ n * (160 * Real.exp ((2 * 1) * Real.sqrt (2 * 1)) * Real.exp (-u)) := by ring
          _ ≤ 1 * (160 * Real.exp ((2 * 1) * Real.sqrt (2 * 1)) * Real.exp (-u)) :=
            mul_le_mul_of_nonneg_right h1 hK
          _ = _ := one_mul _
    _ = _ := by ring

/-- **`mₙ > 0`.** -/
theorem mom_pos (n : ℕ) : 0 < mom n := by
  unfold mom
  apply mul_pos two_pos
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ (integrable_mom n)]
  · have hsub : Ioi (0 : ℝ) ⊆ Function.support (fun u : ℝ => Phi u * u ^ (2 * n)) ∩ Ioi 0 := by
      intro u hu
      refine ⟨?_, hu⟩
      exact (mul_pos (Phi_pos (le_of_lt hu)) (pow_pos hu _)).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    simp
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
    exact (mul_pos (Phi_pos (le_of_lt hu)) (pow_pos hu _)).le

/-! ## 3. M1: `aₙ = mₙ/(2n)!` -/

/-- Os coeficientes-momento `cₙ = mₙ/(2n)!`. -/
noncomputable def cMom (n : ℕ) : ℝ := mom n / (2 * n)!

theorem int_abs_le (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ∫ u in Ioi (0 : ℝ), |Phi u| * ((y * u) ^ (2 * n) / ((2 * n)! : ℝ)) ≤
      (1 / 4) ^ n * (160 * Real.exp ((2 * y) * Real.sqrt (2 * y))) := by
  have hint := ATK.XiPhi.integrableOn_exp_neg_mul
    ((1 / 4) ^ n * (160 * Real.exp ((2 * y) * Real.sqrt (2 * y))))
  calc ∫ u in Ioi (0 : ℝ), |Phi u| * ((y * u) ^ (2 * n) / ((2 * n)! : ℝ))
      ≤ ∫ u in Ioi (0 : ℝ), (1 / 4) ^ n * (160 * Real.exp ((2 * y) * Real.sqrt (2 * y))) *
          Real.exp (-u) := by
        refine integral_mono_of_nonneg ?_ hint ?_
        · exact Eventually.of_forall fun u => mul_nonneg (abs_nonneg _) (by
            rcases le_total 0 u with h | h
            · positivity
            · have : (y * u) ^ (2 * n) = ((y * u) ^ 2) ^ n := by rw [pow_mul]
              rw [this]; positivity)
        · exact ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => pt_le hy (le_of_lt hu) n
    _ = _ := by rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

/-- **`HPhi(z) = Σₙ (mₙ/(2n)!)(−z²)ⁿ`** (série do cosseno sob a integral). -/
theorem hasSum_HPhi (z : ℂ) :
    HasSum (fun n => ((cMom n : ℝ) : ℂ) * (-z ^ 2) ^ n) (HPhi z) := by
  set F : ℕ → ℝ → ℂ := fun n u =>
    (Phi u : ℂ) * ((-1) ^ n * (z * u) ^ (2 * n) / ((2 * n)! : ℂ)) with hF
  have hFn : ∀ n u, F n u =
      ((-1) ^ n * z ^ (2 * n) / ((2 * n)! : ℂ)) * ((Phi u * u ^ (2 * n) : ℝ) : ℂ) := by
    intro n u
    simp only [hF]
    push_cast
    ring
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi 0)) := by
    intro n
    have h := (Integrable.ofReal (𝕜 := ℂ) (integrable_mom n)).const_mul
      ((-1) ^ n * z ^ (2 * n) / ((2 * n)! : ℂ))
    exact h.congr (Eventually.of_forall fun u => (hFn n u).symm)
  have hnorm : ∀ n, ∀ u, 0 ≤ u → ‖F n u‖ = |Phi u| * ((‖z‖ * u) ^ (2 * n) / ((2 * n)! : ℝ)) := by
    intro n u hu
    simp only [hF, norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast, abs_of_nonneg hu]
  have hsum : Summable fun n => ∫ u in Ioi (0 : ℝ), ‖F n u‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun u => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num) :
        Summable fun n : ℕ => (1 / 4 : ℝ) ^ n).mul_right
        (160 * Real.exp ((2 * ‖z‖) * Real.sqrt (2 * ‖z‖))))
    calc ∫ u in Ioi (0 : ℝ), ‖F n u‖
        = ∫ u in Ioi (0 : ℝ), |Phi u| * ((‖z‖ * u) ^ (2 * n) / ((2 * n)! : ℝ)) :=
          setIntegral_congr_fun measurableSet_Ioi fun u hu => hnorm n u (le_of_lt hu)
      _ ≤ _ := int_abs_le n (norm_nonneg z)
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have htsum : ∀ u, ∑' n, F n u = (Phi u : ℂ) * Complex.cos (z * u) := fun u =>
    ((Complex.hasSum_cos (z * u)).mul_left (Phi u : ℂ)).tsum_eq
  simp only [htsum] at h
  have h2 := h.mul_left 2
  show HasSum _ (2 * ∫ u in Ioi (0 : ℝ), (Phi u : ℂ) * Complex.cos (z * u))
  convert h2 using 1
  funext n
  have hI : (∫ u in Ioi (0 : ℝ), F n u) = ((-1) ^ n * z ^ (2 * n) / ((2 * n)! : ℂ)) *
      ((∫ u in Ioi (0 : ℝ), Phi u * u ^ (2 * n) : ℝ) : ℂ) := by
    simp only [hFn]
    rw [integral_const_mul, integral_complex_ofReal]
  rw [hI]
  simp only [cMom, mom]
  push_cast
  rw [neg_pow, pow_mul]
  ring

theorem summ_of_inteira {c : ℕ → ℝ} (hc : Inteira c) (t : ℝ) : Summable fun k => c k * t ^ k :=
  Summable.of_norm_bounded (hc |t| (abs_nonneg t)) fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow]

theorem inteira_sub {a b : ℕ → ℝ} (ha : Inteira a) (hb : Inteira b) :
    Inteira fun n => a n - b n := by
  intro R hR
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg hR n))
    (fun n => ?_) ((ha R hR).add (hb R hR))
  have h := abs_sub_le (a n) 0 (b n)
  simp only [sub_zero, zero_sub, abs_neg] at h
  have hp := pow_nonneg hR n
  nlinarith

theorem cMom_pos (n : ℕ) : 0 < cMom n := div_pos (mom_pos n) (by positivity)

theorem inteira_cMom : Inteira cMom := by
  intro R hR
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (pow_nonneg hR n))
    (fun n => ?_) ((summable_geometric_of_lt_one (by norm_num) (by norm_num) :
      Summable fun n : ℕ => (1 / 4 : ℝ) ^ n).mul_right
      (2 * (160 * Real.exp ((2 * Real.sqrt R) * Real.sqrt (2 * Real.sqrt R)))))
  rw [abs_of_pos (cMom_pos n)]
  have e : cMom n * R ^ n =
      2 * ∫ u in Ioi (0 : ℝ), |Phi u| * ((Real.sqrt R * u) ^ (2 * n) / ((2 * n)! : ℝ)) := by
    have hpt : ∀ u ∈ Ioi (0 : ℝ), |Phi u| * ((Real.sqrt R * u) ^ (2 * n) / ((2 * n)! : ℝ)) =
        Phi u * u ^ (2 * n) * (R ^ n / (2 * n)!) := by
      intro u hu
      rw [abs_of_pos (Phi_pos (le_of_lt hu)), mul_pow, pow_mul, Real.sq_sqrt hR]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_mul_const]
    unfold cMom mom
    ring
  rw [e]
  have := int_abs_le n (Real.sqrt_nonneg R)
  linarith

/-- **M1: `aₙ = 2∫₀^∞Φ(u)u^{2n}du/(2n)!`.** -/
theorem aXi_eq_mom (n : ℕ) : aXi n = mom n / (2 * n)! := by
  have he := inteira_sub inteira_cMom inteira_aXi
  have hev : ∀ w, ev cMom w = ev aXi w := by
    intro w
    obtain ⟨z, rfl⟩ := existe_raiz w
    rw [ev_aXi, gXi_eq_HPhi]
    exact (hasSum_HPhi z).tsum_eq
  have h : ∀ t : ℝ, HasSum (fun k => (cMom k - aXi k) * t ^ k) 0 := by
    intro t
    have hs1 := summ_of_inteira inteira_cMom t
    have hs2 := summ_of_inteira inteira_aXi t
    have e1 := ATK.Hadamard.ev_ofReal cMom hs1
    have e2 := ATK.Hadamard.ev_ofReal aXi hs2
    have heq : ∑' j, cMom j * t ^ j = ∑' j, aXi j * t ^ j := by
      have := hev t
      rw [e1, e2] at this
      exact_mod_cast this
    have h3 := hs1.hasSum.sub hs2.hasSum
    rw [heq, sub_self] at h3
    convert h3 using 1
    funext k
    ring
  have := coef_zero_of_hasSum_zero he h n
  unfold cMom at this
  linarith

/-- **`aₙ > 0` para todo `n`** (sem hipóteses). -/
theorem aXi_pos (n : ℕ) : 0 < aXi n := by
  rw [aXi_eq_mom]
  exact div_pos (mom_pos n) (by positivity)

/-! ## 4. M2: Hankel e Cauchy–Schwarz -/

/-- **Hankel**: `Σ_{i,j<N} cᵢcⱼm_{s+i+j} = 2∫Φu^{2s}(Σcᵢu^{2i})² ≥ 0`. -/
theorem hankel (s N : ℕ) (c : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i * c j * mom (s + i + j) := by
  have hint : ∀ k, Integrable (fun u => Phi u * u ^ (2 * k)) (volume.restrict (Ioi 0)) :=
    integrable_mom
  have key : ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i * c j * mom (s + i + j) =
      2 * ∫ u in Ioi (0 : ℝ), Phi u * u ^ (2 * s) * (∑ i ∈ Finset.range N, c i * u ^ (2 * i)) ^ 2 := by
    have hpt : ∀ u : ℝ, Phi u * u ^ (2 * s) * (∑ i ∈ Finset.range N, c i * u ^ (2 * i)) ^ 2 =
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, (c i * c j) * (Phi u * u ^ (2 * (s + i + j))) := by
      intro u
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show 2 * (s + i + j) = 2 * s + 2 * i + 2 * j by ring, pow_add, pow_add]
      ring
    simp_rw [hpt]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun j _ => (hint _).const_mul _),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun j _ => (hint _).const_mul _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, mom]
    ring
  rw [key]
  apply mul_nonneg (by norm_num)
  refine setIntegral_nonneg measurableSet_Ioi fun u hu => ?_
  exact mul_nonneg (mul_nonneg (Phi_pos (le_of_lt hu)).le (pow_nonneg (le_of_lt hu) _)) (sq_nonneg _)

/-- **Cauchy–Schwarz para os momentos**: `m_{n+1}² ≤ mₙm_{n+2}`. -/
theorem mom_logconvexo (n : ℕ) : mom (n + 1) ^ 2 ≤ mom n * mom (n + 2) := by
  have h := hankel n 2 (fun i => if i = 0 then mom (n + 1) else -mom n)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, if_true, one_ne_zero,
    if_false, add_zero] at h
  have hp := mom_pos n
  have e : n + 1 + 1 = n + 2 := rfl
  rw [e] at h
  nlinarith [h, hp]

/-- A cota de Cauchy–Schwarz nos `aₙ`: `a_{n+1}²((2n+2)!)² ≤ aₙ(2n)!·a_{n+2}(2n+4)!` (cota **superior**). -/
theorem aXi_cota_superior (n : ℕ) :
    aXi (n + 1) ^ 2 * ((2 * (n + 1))! : ℝ) ^ 2 ≤
      (aXi n * (2 * n)!) * (aXi (n + 2) * (2 * (n + 2))!) := by
  have e : ∀ k, aXi k * ((2 * k)! : ℝ) = mom k := fun k => by
    rw [aXi_eq_mom, div_mul_cancel₀]
    positivity
  rw [e n, e (n + 2), show aXi (n + 1) ^ 2 * ((2 * (n + 1))! : ℝ) ^ 2 =
    (aXi (n + 1) * (2 * (n + 1))!) ^ 2 by ring, e (n + 1)]
  exact mom_logconvexo n

end ATK.XiMom

#print axioms ATK.XiMom.cN_gt
#print axioms ATK.XiMom.phiT_pos
#print axioms ATK.XiMom.summable_phiT
#print axioms ATK.XiMom.Phi_pos
#print axioms ATK.XiMom.pow_div_le
#print axioms ATK.XiMom.pt_le
#print axioms ATK.XiMom.aesm_mom
#print axioms ATK.XiMom.integrable_mom
#print axioms ATK.XiMom.mom_pos
#print axioms ATK.XiMom.int_abs_le
#print axioms ATK.XiMom.hasSum_HPhi
#print axioms ATK.XiMom.summ_of_inteira
#print axioms ATK.XiMom.inteira_sub
#print axioms ATK.XiMom.cMom_pos
#print axioms ATK.XiMom.inteira_cMom
#print axioms ATK.XiMom.aXi_eq_mom
#print axioms ATK.XiMom.aXi_pos
#print axioms ATK.XiMom.hankel
#print axioms ATK.XiMom.mom_logconvexo
#print axioms ATK.XiMom.aXi_cota_superior
