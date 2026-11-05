import ATK.ErrosAnaliticos

/-!
# ATK — `Ξ(t) = 2∫₀^∞ Φ(u) cos(tu) du`, sem hipóteses

Fecha o item que ficou condicional em `ATK/ErrosAnaliticos.lean` (`Xi_forma_Phi`): com
`Φ(u) = Σ_{n ≥ 1} (4π²n⁴e^{9u/2} − 6πn²e^{5u/2}) e^{−πn²e^{2u}}`,

**`Ξ(t) = 2 ∫₀^∞ Φ(u) cos(tu) du`** (`Xi_eq_dois_int_Phi`), para todo `t` real.

Roteiro (tudo no kernel):

* termos `h_c(u) = exp(u/2 − c e^{2u})`, `c = πn²`; `ψ(e^{2u})e^{u/2} = Σ h_c(u)` (`hasSum_g`);
  derivadas exatas `h_c′`, `h_c″` e `h_c″ − h_c/4 = (4c²e^{4u} − 6ce^{2u})h_c` (= o termo de `Φ`);
* **cota-chave** `(ce^{2u})^k h_c(u) ≤ 8e^{−c/2}e^{−u}` (`u ≥ 0`, `k ≤ 2`): integrabilidade, limites e somas;
* integração por partes termo a termo (`ErrosAnaliticos.ibp_cos`) e troca soma/integral
  (`integral_tsum_of_summable_integral_norm`) dão `Ξ(t) = (½ + 2Σh_c′(0)) + 2∫₀^∞Φ cos(tu)`;
* **a constante é zero**: derivando a equação funcional `θ(x) = x^{−1/2}θ(1/x)` (Mathlib,
  `evenKernel_functional_equation`) em `x = 1`, com `ψ′(1) = −Σ c e^{−c}` termo a termo, sai
  `4Σc e^{−c} = ψ(1) + ½` (`quatro_T`), isto é `½ + 2Σh_c′(0) = 0` (`constante_zero`).
-/

open Real Filter Topology Set MeasureTheory

namespace ATK.XiPhi

open ATK.BaseRiemannTeta (psi)

/-! ## 1. Os termos e suas derivadas -/

/-- `h_c(u) = exp(u/2 − c·e^{2u})`. -/
noncomputable def hT (c u : ℝ) : ℝ := Real.exp (u / 2 - c * Real.exp (2 * u))

/-- `h_c′(u) = (½ − 2ce^{2u}) h_c(u)`. -/
noncomputable def hT1 (c u : ℝ) : ℝ := (1 / 2 - 2 * c * Real.exp (2 * u)) * hT c u

/-- `h_c″(u) = (¼ − 6ce^{2u} + 4(ce^{2u})²) h_c(u)`. -/
noncomputable def hT2 (c u : ℝ) : ℝ :=
  (1 / 4 - 6 * (c * Real.exp (2 * u)) + 4 * (c * Real.exp (2 * u)) ^ 2) * hT c u

/-- `h_c″ − h_c/4 = (4(ce^{2u})² − 6ce^{2u}) h_c` (o termo de `Φ`). -/
noncomputable def phiT (c u : ℝ) : ℝ :=
  (4 * (c * Real.exp (2 * u)) ^ 2 - 6 * (c * Real.exp (2 * u))) * hT c u

theorem hT_pos (c u : ℝ) : 0 < hT c u := Real.exp_pos _

theorem hasDerivAt_hT (c u : ℝ) : HasDerivAt (hT c) (hT1 c u) u := by
  have h1 : HasDerivAt (fun x : ℝ => x / 2 - c * Real.exp (2 * x))
      (1 / 2 - c * (Real.exp (2 * u) * (2 * 1))) u :=
    ((hasDerivAt_id' u).div_const 2).sub (((hasDerivAt_id' u).const_mul 2).exp.const_mul c)
  exact h1.exp.congr_deriv (by unfold hT1 hT; ring)

theorem hasDerivAt_hT1 (c u : ℝ) : HasDerivAt (hT1 c) (hT2 c u) u := by
  have hl : HasDerivAt (fun x : ℝ => 1 / 2 - 2 * c * Real.exp (2 * x))
      (-(2 * c * (Real.exp (2 * u) * (2 * 1)))) u :=
    (((hasDerivAt_id' u).const_mul 2).exp.const_mul (2 * c)).const_sub (1 / 2)
  exact (hl.mul (hasDerivAt_hT c u)).congr_deriv (by unfold hT2 hT1; ring)

theorem hT2_eq (c u : ℝ) : hT2 c u = phiT c u + hT c u / 4 := by
  unfold hT2 phiT; ring

theorem continuous_hT (c : ℝ) : Continuous (hT c) := by unfold hT; fun_prop
theorem continuous_hT1 (c : ℝ) : Continuous (hT1 c) := by
  unfold hT1; exact (by fun_prop : Continuous fun u : ℝ => 1 / 2 - 2 * c * Real.exp (2 * u)).mul
    (continuous_hT c)
theorem continuous_hT2 (c : ℝ) : Continuous (hT2 c) := by
  unfold hT2
  exact (by fun_prop : Continuous fun u : ℝ =>
    1 / 4 - 6 * (c * Real.exp (2 * u)) + 4 * (c * Real.exp (2 * u)) ^ 2).mul (continuous_hT c)
theorem continuous_phiT (c : ℝ) : Continuous (phiT c) := by
  unfold phiT
  exact (by fun_prop : Continuous fun u : ℝ =>
    4 * (c * Real.exp (2 * u)) ^ 2 - 6 * (c * Real.exp (2 * u))).mul (continuous_hT c)

/-! ## 2. A cota-chave -/

theorem pow_le_exp_half {w : ℝ} (hw : 0 ≤ w) {k : ℕ} (hk : k ≤ 2) : w ^ k ≤ 8 * Real.exp (w / 2) := by
  have h := Real.pow_div_factorial_le_exp (w / 2) (by linarith) k
  have e : (w / 2) ^ k = w ^ k / 2 ^ k := div_pow w 2 k
  rw [e, div_div, div_le_iff₀ (by positivity)] at h
  have hc : (2 : ℝ) ^ k * (k.factorial : ℝ) ≤ 8 := by
    interval_cases k <;> norm_num [Nat.factorial]
  have hE := Real.exp_pos (w / 2)
  nlinarith [mul_le_mul_of_nonneg_left hc hE.le]

/-- **`(ce^{2u})^k · h_c(u) ≤ 8 e^{−c/2} e^{−u}`** para `u ≥ 0`, `c ≥ 3/2`, `k ≤ 2`. -/
theorem cota (c u : ℝ) (hc : 3 / 2 ≤ c) (hu : 0 ≤ u) {k : ℕ} (hk : k ≤ 2) :
    (c * Real.exp (2 * u)) ^ k * hT c u ≤ 8 * Real.exp (-(c / 2)) * Real.exp (-u) := by
  obtain ⟨w, hw⟩ : ∃ w, w = c * Real.exp (2 * u) := ⟨_, rfl⟩
  have he : 2 * u + 1 ≤ Real.exp (2 * u) := Real.add_one_le_exp _
  have hc0 : 0 ≤ c := by linarith
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hwc : c + 3 * u ≤ w := by
    rw [hw]; nlinarith [mul_le_mul_of_nonneg_left he hc0, mul_nonneg (by linarith : 0 ≤ c - 3 / 2) hu]
  have h1 := pow_le_exp_half hw0 hk
  have e1 : hT c u = Real.exp (-(w / 2)) * Real.exp (u / 2 - w / 2) := by
    unfold hT; rw [← Real.exp_add, hw]; congr 1; ring
  have h2 : Real.exp (u / 2 - w / 2) ≤ Real.exp (-(c / 2)) * Real.exp (-u) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have h3 : w ^ k * Real.exp (-(w / 2)) ≤ 8 := by
    have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(w / 2))).le
    calc w ^ k * Real.exp (-(w / 2)) ≤ 8 * Real.exp (w / 2) * Real.exp (-(w / 2)) := this
      _ = 8 := by rw [mul_assoc, ← Real.exp_add]; simp
  rw [← hw, e1, ← mul_assoc]
  calc w ^ k * Real.exp (-(w / 2)) * Real.exp (u / 2 - w / 2) ≤ 8 * Real.exp (u / 2 - w / 2) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ ≤ 8 * (Real.exp (-(c / 2)) * Real.exp (-u)) := by gcongr
    _ = 8 * Real.exp (-(c / 2)) * Real.exp (-u) := by ring

/-- Polinômio de grau `≤ 2` em `w = ce^{2u}` vezes `h_c`. -/
theorem cota_quad (c u a b d : ℝ) (hc : 3 / 2 ≤ c) (hu : 0 ≤ u) :
    |(a + b * (c * Real.exp (2 * u)) + d * (c * Real.exp (2 * u)) ^ 2) * hT c u| ≤
      (|a| + |b| + |d|) * (8 * Real.exp (-(c / 2)) * Real.exp (-u)) := by
  obtain ⟨w, hw⟩ : ∃ w, w = c * Real.exp (2 * u) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by linarith
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have k0 := cota c u hc hu (k := 0) (by norm_num)
  have k1 := cota c u hc hu (k := 1) (by norm_num)
  have k2 := cota c u hc hu (k := 2) (by norm_num)
  rw [← hw] at k0 k1 k2 ⊢
  simp only [pow_zero, one_mul, pow_one] at k0 k1
  have hh := hT_pos c u
  set B := 8 * Real.exp (-(c / 2)) * Real.exp (-u)
  rw [abs_mul, abs_of_pos hh]
  have ht : |a + b * w + d * w ^ 2| ≤ |a| + |b| * w + |d| * w ^ 2 := by
    calc |a + b * w + d * w ^ 2| ≤ |a| + |b * w| + |d * w ^ 2| := abs_add_three _ _ _
      _ = |a| + |b| * w + |d| * w ^ 2 := by
          rw [abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg (by positivity : 0 ≤ w ^ 2)]
  calc |a + b * w + d * w ^ 2| * hT c u ≤ (|a| + |b| * w + |d| * w ^ 2) * hT c u :=
        mul_le_mul_of_nonneg_right ht hh.le
    _ = |a| * hT c u + |b| * (w * hT c u) + |d| * (w ^ 2 * hT c u) := by ring
    _ ≤ |a| * B + |b| * B + |d| * B := by
        gcongr
    _ = (|a| + |b| + |d|) * B := by ring

theorem cota_hT (c u : ℝ) (hc : 3 / 2 ≤ c) (hu : 0 ≤ u) :
    |hT c u| ≤ 8 * Real.exp (-(c / 2)) * Real.exp (-u) := by
  have := cota_quad c u 1 0 0 hc hu
  simp only [zero_mul, add_zero, one_mul, abs_one, abs_zero] at this
  simpa using this

theorem cota_hT1 (c u : ℝ) (hc : 3 / 2 ≤ c) (hu : 0 ≤ u) :
    |hT1 c u| ≤ 20 * Real.exp (-(c / 2)) * Real.exp (-u) := by
  have := cota_quad c u (1 / 2) (-2) 0 hc hu
  have e : hT1 c u = (1 / 2 + -2 * (c * Real.exp (2 * u)) + 0 * (c * Real.exp (2 * u)) ^ 2) * hT c u := by
    unfold hT1; ring
  rw [e]
  calc _ ≤ _ := this
    _ = 20 * Real.exp (-(c / 2)) * Real.exp (-u) := by norm_num; ring

theorem cota_hT2 (c u : ℝ) (hc : 3 / 2 ≤ c) (hu : 0 ≤ u) :
    |hT2 c u| ≤ 82 * Real.exp (-(c / 2)) * Real.exp (-u) := by
  have := cota_quad c u (1 / 4) (-6) 4 hc hu
  have e : hT2 c u = (1 / 4 + -6 * (c * Real.exp (2 * u)) + 4 * (c * Real.exp (2 * u)) ^ 2) * hT c u := by
    unfold hT2; ring
  rw [e]
  calc _ ≤ _ := this
    _ = 82 * Real.exp (-(c / 2)) * Real.exp (-u) := by norm_num; ring

theorem cota_phiT (c u : ℝ) (hc : 3 / 2 ≤ c) (hu : 0 ≤ u) :
    |phiT c u| ≤ 80 * Real.exp (-(c / 2)) * Real.exp (-u) := by
  have := cota_quad c u 0 (-6) 4 hc hu
  have e : phiT c u = (0 + -6 * (c * Real.exp (2 * u)) + 4 * (c * Real.exp (2 * u)) ^ 2) * hT c u := by
    unfold phiT; ring
  rw [e]
  calc _ ≤ _ := this
    _ = 80 * Real.exp (-(c / 2)) * Real.exp (-u) := by norm_num; ring

/-! ## 3. Integrabilidade, integrais e limites -/

theorem integrableOn_exp_neg_mul (K : ℝ) : IntegrableOn (fun u => K * Real.exp (-u)) (Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ => K * Real.exp (-1 * x)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 one_pos).const_mul K
  exact h.congr_fun (fun x _ => by simp) measurableSet_Ioi

theorem integrableOn_of_cota {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ}
    (hb : ∀ u, 0 ≤ u → |f u| ≤ K * Real.exp (-u)) : IntegrableOn f (Ioi 0) :=
  Integrable.mono' (integrableOn_exp_neg_mul K) hf.aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => by
      rw [Real.norm_eq_abs]; exact hb u (le_of_lt hu))

theorem integral_abs_le_of_cota {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ}
    (hb : ∀ u, 0 ≤ u → |f u| ≤ K * Real.exp (-u)) : ∫ u in Ioi (0 : ℝ), |f u| ≤ K := by
  have h := setIntegral_mono_on (integrableOn_of_cota hf hb).abs (integrableOn_exp_neg_mul K)
    measurableSet_Ioi (fun u hu => hb u (le_of_lt hu))
  rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one] at h
  exact h

theorem tendsto_of_cota {f : ℝ → ℝ} {K : ℝ} (hb : ∀ u, 0 ≤ u → |f u| ≤ K * Real.exp (-u)) :
    Tendsto f atTop (𝓝 0) := by
  have hK : Tendsto (fun u => K * Real.exp (-u)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul K
  refine squeeze_zero_norm' ?_ hK
  filter_upwards [eventually_ge_atTop 0] with u hu
  rw [Real.norm_eq_abs]; exact hb u hu

theorem cos_cota {f : ℝ → ℝ} {K : ℝ} (hb : ∀ u, 0 ≤ u → |f u| ≤ K * Real.exp (-u)) (t : ℝ) :
    ∀ u, 0 ≤ u → |f u * Real.cos (t * u)| ≤ K * Real.exp (-u) := by
  intro u hu
  rw [abs_mul]
  calc |f u| * |Real.cos (t * u)| ≤ |f u| * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
    _ ≤ K * Real.exp (-u) := by rw [mul_one]; exact hb u hu

/-! ## 4. Integração por partes termo a termo -/

/-- **Por termo**: `(t² + ¼)∫₀^∞ h_c cos(tu) = −h_c′(0) − ∫₀^∞ (h_c″ − h_c/4) cos(tu)`. -/
theorem ibp_termo (c t : ℝ) (hc : 3 / 2 ≤ c) :
    (t ^ 2 + 1 / 4) * ∫ u in Ioi (0 : ℝ), hT c u * Real.cos (t * u) =
      -hT1 c 0 - ∫ u in Ioi (0 : ℝ), phiT c u * Real.cos (t * u) := by
  have b0 : ∀ u, 0 ≤ u → |hT c u| ≤ 8 * Real.exp (-(c / 2)) * Real.exp (-u) :=
    fun u hu => cota_hT c u hc hu
  have b1 : ∀ u, 0 ≤ u → |hT1 c u| ≤ 20 * Real.exp (-(c / 2)) * Real.exp (-u) :=
    fun u hu => cota_hT1 c u hc hu
  have b2 : ∀ u, 0 ≤ u → |hT2 c u| ≤ 82 * Real.exp (-(c / 2)) * Real.exp (-u) :=
    fun u hu => cota_hT2 c u hc hu
  have bp : ∀ u, 0 ≤ u → |phiT c u| ≤ 80 * Real.exp (-(c / 2)) * Real.exp (-u) :=
    fun u hu => cota_phiT c u hc hu
  have h := ATK.ErrosAnaliticos.ibp_cos t (fun u _ => hasDerivAt_hT c u) (fun u _ => hasDerivAt_hT1 c u)
    (integrableOn_of_cota (continuous_hT c) b0) (integrableOn_of_cota (continuous_hT1 c) b1)
    (integrableOn_of_cota (continuous_hT2 c) b2) (tendsto_of_cota b0) (tendsto_of_cota b1)
  have ip : IntegrableOn (fun u => phiT c u * Real.cos (t * u)) (Ioi 0) :=
    integrableOn_of_cota ((continuous_phiT c).mul (by fun_prop)) (cos_cota bp t)
  have ih : IntegrableOn (fun u => 1 / 4 * (hT c u * Real.cos (t * u))) (Ioi 0) :=
    (integrableOn_of_cota ((continuous_hT c).mul (by fun_prop)) (cos_cota b0 t)).const_mul _
  have e2 : ∫ u in Ioi (0 : ℝ), hT2 c u * Real.cos (t * u) =
      (∫ u in Ioi (0 : ℝ), phiT c u * Real.cos (t * u)) +
        1 / 4 * ∫ u in Ioi (0 : ℝ), hT c u * Real.cos (t * u) := by
    rw [← integral_const_mul, ← integral_add ip ih]
    congr 1; funext u; rw [hT2_eq]; ring
  rw [e2] at h
  linear_combination h

/-! ## 5. Soma sobre `n`: `c_n = π(n+1)²` -/

/-- `c_n = π(n+1)²`. -/
noncomputable def cN (n : ℕ) : ℝ := π * ((n : ℝ) + 1) ^ 2

theorem cN_ge (n : ℕ) : 3 / 2 ≤ cN n := by
  unfold cN
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
    nlinarith
  nlinarith [Real.pi_gt_three]

theorem summable_exp_cN : Summable fun n : ℕ => Real.exp (-(cN n / 2)) := by
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
    (summable_geometric_of_lt_one (Real.exp_pos (-1)).le (Real.exp_lt_one_iff.mpr (by norm_num)))
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  unfold cN
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  nlinarith [Real.pi_gt_three]

/-- `ψ(e^{2u})e^{u/2} = Σ_n h_{c_n}(u)`. -/
theorem hasSum_g (u : ℝ) :
    HasSum (fun n => hT (cN n) u) (psi (Real.exp (2 * u)) * Real.exp (u / 2)) := by
  have h := (ATK.BaseRiemannTeta.hasSum_psi (Real.exp_pos (2 * u))).mul_right (Real.exp (u / 2))
  refine h.congr_fun fun n => ?_
  unfold hT cN
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

theorem summable_int_hT (t : ℝ) :
    Summable fun n : ℕ => ∫ u in Ioi (0 : ℝ), ‖hT (cN n) u * Real.cos (t * u)‖ := by
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
    (summable_exp_cN.mul_left 8)
  simp only [Real.norm_eq_abs]
  exact integral_abs_le_of_cota ((continuous_hT _).mul (by fun_prop))
    (cos_cota (fun u hu => cota_hT (cN n) u (cN_ge n) hu) t)

theorem summable_int_phiT (t : ℝ) :
    Summable fun n : ℕ => ∫ u in Ioi (0 : ℝ), ‖phiT (cN n) u * Real.cos (t * u)‖ := by
  refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_)
    (summable_exp_cN.mul_left 80)
  simp only [Real.norm_eq_abs]
  exact integral_abs_le_of_cota ((continuous_phiT _).mul (by fun_prop))
    (cos_cota (fun u hu => cota_phiT (cN n) u (cN_ge n) hu) t)

theorem integrable_hT_cos (n : ℕ) (t : ℝ) :
    Integrable (fun u => hT (cN n) u * Real.cos (t * u)) (volume.restrict (Ioi 0)) :=
  integrableOn_of_cota ((continuous_hT _).mul (by fun_prop))
    (cos_cota (fun u hu => cota_hT (cN n) u (cN_ge n) hu) t)

theorem integrable_phiT_cos (n : ℕ) (t : ℝ) :
    Integrable (fun u => phiT (cN n) u * Real.cos (t * u)) (volume.restrict (Ioi 0)) :=
  integrableOn_of_cota ((continuous_phiT _).mul (by fun_prop))
    (cos_cota (fun u hu => cota_phiT (cN n) u (cN_ge n) hu) t)

/-- `∫₀^∞ ψ(e^{2u})e^{u/2}cos(tu) = Σ_n ∫₀^∞ h_{c_n} cos(tu)`. -/
theorem K_tsum (t : ℝ) :
    ∫ u in Ioi (0 : ℝ), psi (Real.exp (2 * u)) * Real.exp (u / 2) * Real.cos (t * u) =
      ∑' n : ℕ, ∫ u in Ioi (0 : ℝ), hT (cN n) u * Real.cos (t * u) := by
  rw [integral_tsum_of_summable_integral_norm (fun n => integrable_hT_cos n t) (summable_int_hT t)]
  congr 1
  funext u
  rw [tsum_mul_right, (hasSum_g u).tsum_eq]

/-- `Φ(u) = Σ_n (h_{c_n}″ − h_{c_n}/4)(u)`. -/
noncomputable def Phi (u : ℝ) : ℝ := ∑' n : ℕ, phiT (cN n) u

theorem Phi_tsum (t : ℝ) :
    ∫ u in Ioi (0 : ℝ), Phi u * Real.cos (t * u) =
      ∑' n : ℕ, ∫ u in Ioi (0 : ℝ), phiT (cN n) u * Real.cos (t * u) := by
  rw [integral_tsum_of_summable_integral_norm (fun n => integrable_phiT_cos n t) (summable_int_phiT t)]
  congr 1
  funext u
  rw [Phi, tsum_mul_right]

theorem summable_hT1_zero : Summable fun n : ℕ => hT1 (cN n) 0 := by
  refine Summable.of_norm_bounded (summable_exp_cN.mul_left 20) fun n => ?_
  have := cota_hT1 (cN n) 0 (cN_ge n) le_rfl
  rw [Real.norm_eq_abs]
  simpa using this

/-- **`Ξ(t) = (½ + 2Σ h_{c_n}′(0)) + 2∫₀^∞ Φ(u)cos(tu)du`**, sem hipóteses. -/
theorem Xi_forma_constante (t : ℝ) :
    ATK.BaseRiemannXi.Xi t = (1 / 2 + 2 * ∑' n : ℕ, hT1 (cN n) 0) +
      2 * ∫ u in Ioi (0 : ℝ), Phi u * Real.cos (t * u) := by
  rw [ATK.ErrosAnaliticos.Xi_forma_u, K_tsum, Phi_tsum]
  have hP : Summable fun n : ℕ => ∫ u in Ioi (0 : ℝ), phiT (cN n) u * Real.cos (t * u) :=
    Summable.of_norm_bounded (summable_int_phiT t) fun n => norm_integral_le_integral_norm _
  have hK : Summable fun n : ℕ => ∫ u in Ioi (0 : ℝ), hT (cN n) u * Real.cos (t * u) :=
    Summable.of_norm_bounded (summable_int_hT t) fun n => norm_integral_le_integral_norm _
  have e : ∀ n : ℕ, (t ^ 2 + 1 / 4) * ∫ u in Ioi (0 : ℝ), hT (cN n) u * Real.cos (t * u) =
      -hT1 (cN n) 0 - ∫ u in Ioi (0 : ℝ), phiT (cN n) u * Real.cos (t * u) :=
    fun n => ibp_termo (cN n) t (cN_ge n)
  have hsum : (t ^ 2 + 1 / 4) * ∑' n : ℕ, ∫ u in Ioi (0 : ℝ), hT (cN n) u * Real.cos (t * u) =
      -(∑' n : ℕ, hT1 (cN n) 0) - ∑' n : ℕ, ∫ u in Ioi (0 : ℝ), phiT (cN n) u * Real.cos (t * u) := by
    rw [← tsum_mul_left, ← tsum_neg, ← Summable.tsum_sub summable_hT1_zero.neg hP]
    exact tsum_congr e
  linear_combination (-2 : ℝ) * hsum

/-! ## 6. A constante é zero (equação funcional de `θ`) -/

/-- `T = Σ c_n e^{−c_n}`. -/
noncomputable def T : ℝ := ∑' n : ℕ, cN n * Real.exp (-cN n)

theorem psi_tsum {x : ℝ} (hx : 0 < x) : psi x = ∑' n : ℕ, Real.exp (-cN n * x) := by
  rw [← (ATK.BaseRiemannTeta.hasSum_psi hx).tsum_eq]
  congr 1; funext n; unfold cN; push_cast; ring_nf

theorem cN_exp_le (n : ℕ) : cN n * Real.exp (-(cN n / 2)) ≤ 4 * Real.exp (-1) ^ n := by
  have hc : 0 ≤ cN n := by linarith [cN_ge n]
  have h1 : cN n / 4 + 1 ≤ Real.exp (cN n / 4) := Real.add_one_le_exp _
  have h2 : cN n ≤ 4 * Real.exp (cN n / 4) := by linarith
  have h3 : cN n * Real.exp (-(cN n / 2)) ≤ 4 * Real.exp (-(cN n / 4)) := by
    calc cN n * Real.exp (-(cN n / 2)) ≤ 4 * Real.exp (cN n / 4) * Real.exp (-(cN n / 2)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = 4 * Real.exp (-(cN n / 4)) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
  have h4 : Real.exp (-(cN n / 4)) ≤ Real.exp (-1) ^ n := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    unfold cN
    have hn : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith [Real.pi_gt_three]
  linarith

theorem summable_cN_exp : Summable fun n : ℕ => cN n * Real.exp (-(cN n / 2)) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (by linarith [cN_ge n]) (Real.exp_pos _).le) cN_exp_le
    ((summable_geometric_of_lt_one (Real.exp_pos (-1)).le
      (Real.exp_lt_one_iff.mpr (by norm_num))).mul_left 4)

/-- **`ψ′(1) = −T`** (derivação termo a termo em `(½, ∞)`). -/
theorem hasDerivAt_psi_um : HasDerivAt psi (-T) 1 := by
  have hd := hasDerivAt_tsum_of_isPreconnected (t := Ioi (1 / 2 : ℝ)) (y₀ := 1) (y := 1)
    (g := fun n x => Real.exp (-cN n * x)) (g' := fun n x => Real.exp (-cN n * x) * (-cN n))
    summable_cN_exp isOpen_Ioi isPreconnected_Ioi
    (fun n y _ => (((hasDerivAt_id' y).const_mul (-cN n)).exp).congr_deriv (by ring))
    (fun n y hy => by
      have hc : 0 ≤ cN n := by linarith [cN_ge n]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_neg, abs_of_nonneg hc,
        mul_comm]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc
      have : (1 / 2 : ℝ) < y := hy
      nlinarith)
    (by norm_num : (1 : ℝ) ∈ Ioi (1 / 2 : ℝ))
    ((ATK.BaseRiemannTeta.hasSum_psi one_pos).summable.congr fun n => by unfold cN; push_cast; ring_nf)
    (by norm_num : (1 : ℝ) ∈ Ioi (1 / 2 : ℝ))
  have hT' : ∑' n : ℕ, Real.exp (-cN n * 1) * (-cN n) = -T := by
    unfold T
    rw [← tsum_neg]
    congr 1; funext n; ring_nf
  rw [hT'] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds one_pos] with x hx
  exact psi_tsum hx

/-- **Equação funcional**: `ψ(x) = x^{−1/2}ψ(1/x) + (x^{−1/2} − 1)/2` para `x > 0`. -/
theorem psi_feq {x : ℝ} (_hx : 0 < x) :
    psi x = (x ^ (1 / 2 : ℝ))⁻¹ * psi x⁻¹ + ((x ^ (1 / 2 : ℝ))⁻¹ - 1) / 2 := by
  have h := HurwitzZeta.evenKernel_functional_equation 0 x
  rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero, one_div (x ^ (1 / 2 : ℝ)), one_div x] at h
  unfold psi
  rw [h]
  ring

/-- **`4T = ψ(1) + ½`.** -/
theorem quatro_T : 4 * T = psi 1 + 1 / 2 := by
  have hp := hasDerivAt_psi_um
  have hs : HasDerivAt (fun x : ℝ => x ^ (1 / 2 : ℝ)) (1 / 2 * (1 : ℝ) ^ (1 / 2 - 1 : ℝ)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
  have hsi := hs.inv (by norm_num : (1 : ℝ) ^ (1 / 2 : ℝ) ≠ 0)
  have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-((1 : ℝ) ^ 2)⁻¹) 1 := hasDerivAt_inv one_ne_zero
  have hp' : HasDerivAt psi (-T) ((fun x : ℝ => x⁻¹) 1) := by simpa using hp
  have hcomp := hp'.comp (1 : ℝ) hinv
  have hr := (hsi.mul hcomp).add ((hsi.sub_const 1).div_const 2)
  have hr' : HasDerivAt psi _ 1 := hr.congr_of_eventuallyEq (by
    filter_upwards [Ioi_mem_nhds one_pos] with x hx
    simp only [Pi.add_apply, Pi.mul_apply, Pi.inv_apply, Function.comp_apply]
    exact psi_feq hx)
  have hu := hp.unique hr'
  simp only [Real.one_rpow, inv_one, one_pow, Function.comp_apply, mul_one, Pi.inv_apply,
    div_one] at hu
  linarith

/-- **`½ + 2Σ h_{c_n}′(0) = 0`.** -/
theorem constante_zero : 1 / 2 + 2 * ∑' n : ℕ, hT1 (cN n) 0 = 0 := by
  have e : ∀ n : ℕ, hT1 (cN n) 0 = 1 / 2 * Real.exp (-cN n * 1) - 2 * (cN n * Real.exp (-cN n)) := by
    intro n; unfold hT1 hT; simp; ring
  have h1 : Summable fun n : ℕ => Real.exp (-cN n * 1) :=
    (ATK.BaseRiemannTeta.hasSum_psi one_pos).summable.congr fun n => by unfold cN; push_cast; ring_nf
  have h2 : Summable fun n : ℕ => cN n * Real.exp (-cN n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (by linarith [cN_ge n]) (Real.exp_pos _).le)
      (fun n => mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [cN_ge n]))
        (by linarith [cN_ge n])) summable_cN_exp
  have hs : ∑' n : ℕ, hT1 (cN n) 0 = 1 / 2 * psi 1 - 2 * T := by
    rw [tsum_congr e, Summable.tsum_sub (h1.mul_left _) (h2.mul_left _), tsum_mul_left, tsum_mul_left,
      psi_tsum one_pos]
    rfl
  rw [hs]
  linarith [quatro_T]

/-! ## 7. O teorema -/

/-- **`Ξ(t) = 2∫₀^∞ Φ(u)cos(tu)du`** com `Φ = Σ_n (h_{c_n}″ − h_{c_n}/4)`. -/
theorem Xi_dois_Phi (t : ℝ) :
    ATK.BaseRiemannXi.Xi t = 2 * ∫ u in Ioi (0 : ℝ), Phi u * Real.cos (t * u) := by
  rw [Xi_forma_constante, constante_zero, zero_add]

/-- O termo de `Φ` na forma do texto: `(4π²n⁴e^{9u/2} − 6πn²e^{5u/2})e^{−πn²e^{2u}}`. -/
theorem phiT_texto (n : ℕ) (u : ℝ) :
    phiT (cN n) u = (4 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u / 2) -
      6 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u / 2)) *
        Real.exp (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)) := by
  unfold phiT hT cN
  have e1 : Real.exp (u / 2 - π * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)) =
      Real.exp (u / 2) * Real.exp (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (2 * u) ^ 2 * Real.exp (u / 2) = Real.exp (9 * u / 2) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (2 * u) * Real.exp (u / 2) = Real.exp (5 * u / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1, ← e2, ← e3]
  ring

/-- **O enunciado do texto, com o fator 2**: `Ξ(t) = 2∫₀^∞ Φ(u)cos(tu)du`,
`Φ(u) = Σ_{n≥1}(4π²n⁴e^{9u/2} − 6πn²e^{5u/2})e^{−πn²e^{2u}}`. -/
theorem Xi_eq_dois_int_Phi (t : ℝ) :
    ATK.BaseRiemannXi.Xi t = 2 * ∫ u in Ioi (0 : ℝ),
      (∑' n : ℕ, (4 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u / 2) -
        6 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u / 2)) *
          Real.exp (-π * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u))) * Real.cos (t * u) := by
  rw [Xi_dois_Phi]
  congr 1
  congr 1
  funext u
  congr 1
  unfold Phi
  exact tsum_congr fun n => phiT_texto n u

/-- E a versão do texto (sem o 2) é falsa: daria `Ξ = Ξ/2`, logo `Ξ(0) = 0`, mas `Ξ(0) > 0`. -/
theorem sem_fator_dois_falso :
    ¬ ∀ t : ℝ, ATK.BaseRiemannXi.Xi t = ∫ u in Ioi (0 : ℝ), Phi u * Real.cos (t * u) := by
  intro h
  have a := h 0
  have b := Xi_dois_Phi 0
  have h0 := ATK.BaseRiemannXiSinal.Xi_zero_pos
  linarith

/-- `2∫₀^∞Φ = ξ(½)` (`t = 0`). -/
theorem dois_int_Phi_meio :
    2 * ∫ u in Ioi (0 : ℝ), Phi u = ATK.BaseRiemannXi.Xi 0 := by
  rw [Xi_dois_Phi]; simp

end ATK.XiPhi

-- Auditoria de axiomas (kernel)
#print axioms ATK.XiPhi.hT_pos
#print axioms ATK.XiPhi.hasDerivAt_hT
#print axioms ATK.XiPhi.hasDerivAt_hT1
#print axioms ATK.XiPhi.hT2_eq
#print axioms ATK.XiPhi.continuous_hT
#print axioms ATK.XiPhi.continuous_hT1
#print axioms ATK.XiPhi.continuous_hT2
#print axioms ATK.XiPhi.continuous_phiT
#print axioms ATK.XiPhi.pow_le_exp_half
#print axioms ATK.XiPhi.cota
#print axioms ATK.XiPhi.cota_quad
#print axioms ATK.XiPhi.cota_hT
#print axioms ATK.XiPhi.cota_hT1
#print axioms ATK.XiPhi.cota_hT2
#print axioms ATK.XiPhi.cota_phiT
#print axioms ATK.XiPhi.integrableOn_exp_neg_mul
#print axioms ATK.XiPhi.integrableOn_of_cota
#print axioms ATK.XiPhi.integral_abs_le_of_cota
#print axioms ATK.XiPhi.tendsto_of_cota
#print axioms ATK.XiPhi.cos_cota
#print axioms ATK.XiPhi.ibp_termo
#print axioms ATK.XiPhi.cN_ge
#print axioms ATK.XiPhi.summable_exp_cN
#print axioms ATK.XiPhi.hasSum_g
#print axioms ATK.XiPhi.summable_int_hT
#print axioms ATK.XiPhi.summable_int_phiT
#print axioms ATK.XiPhi.integrable_hT_cos
#print axioms ATK.XiPhi.integrable_phiT_cos
#print axioms ATK.XiPhi.K_tsum
#print axioms ATK.XiPhi.Phi_tsum
#print axioms ATK.XiPhi.summable_hT1_zero
#print axioms ATK.XiPhi.Xi_forma_constante
#print axioms ATK.XiPhi.psi_tsum
#print axioms ATK.XiPhi.cN_exp_le
#print axioms ATK.XiPhi.summable_cN_exp
#print axioms ATK.XiPhi.hasDerivAt_psi_um
#print axioms ATK.XiPhi.psi_feq
#print axioms ATK.XiPhi.quatro_T
#print axioms ATK.XiPhi.constante_zero
#print axioms ATK.XiPhi.Xi_dois_Phi
#print axioms ATK.XiPhi.phiT_texto
#print axioms ATK.XiPhi.Xi_eq_dois_int_Phi
#print axioms ATK.XiPhi.sem_fator_dois_falso
#print axioms ATK.XiPhi.dois_int_Phi_meio
