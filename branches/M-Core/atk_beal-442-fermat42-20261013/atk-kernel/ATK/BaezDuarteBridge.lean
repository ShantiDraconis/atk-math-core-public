import ATK.MellinRho
import ATK.RiemannStates
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# ATK — Ponte B1 provada: `D_N → 0 ⇒ Hipótese de Riemann` (Nyman–Beurling–Báez-Duarte)

Este arquivo **descarrega a ponte B1** (`ATK.Conditional.Riemann.BaezDuarteCriterion`), que até
aqui era hipótese ("publicada, não formalizada"). Prova-se no kernel, sem hipóteses:

  `baezDuarteCriterion : Tendsto DN atTop (𝓝 0) → RiemannHypothesis`

com `RiemannHypothesis` **da Mathlib** e `D_N` a família concreta `ρ_k(t) = {1/(k t)}`.

Argumento (direção "fácil" de Nyman–Beurling, versão de Báez-Duarte):

1. Se `ζ(s) = 0` com `1/2 < Re s < 1`, então `∫_0^∞ ρ_k(t) t^{s−1} dt = 0` para todo `k ≥ 1`
   (`ATK.MellinRho.mellin_rho_eq_zero`), enquanto `∫_0^∞ χ(t) t^{s−1} dt = 1/s`.
2. Logo, para qualquer resíduo `f = χ − Σ c_k ρ_{k+1}`: `∫_0^∞ f(t) t^{s−1} dt = 1/s`.
3. Mas `|∫ f t^{s−1}| ≤ (λ‖f‖² + 1/(λ(2σ−1)))/2 + ‖f‖/(1−σ)` (Cauchy–Schwarz elementar em
   `(0,1]`; em `(1,∞)`, `f = −S/t` e `S² ≤ ‖f‖²`). Com `D_N → 0` o lado direito fica `< 1/|s|`:
   contradição. Portanto `ζ ≠ 0` em `1/2 < Re s < 1`.
4. `ζ ≠ 0` em `Re s ≥ 1` (Mathlib) e a equação funcional (Mathlib) cobrem `Re s < 1/2`.

Depois deste arquivo, a rota de Riemann depende **apenas** da obrigação O1 (`D_N → 0`,
equivalentemente `inf_N D_N = 0`), que continua aberta.
-/

open Complex Set MeasureTheory Filter Topology

namespace ATK.BaezDuarteBridge

open ATK.Conditional.Riemann ATK.RiemannConcrete ATK.RiemannFaithful ATK.MellinRho ATK.ZetaStrip

/-! ## Transformada de Mellin de `χ` -/

theorem chi_complex (t : ℝ) :
    ((chi t : ℝ) : ℂ) = Set.indicator (Ioc (0 : ℝ) 1) (fun _ => (1 : ℂ)) t := by
  unfold chi
  by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [ht]

theorem hasMellin_chi {s : ℂ} (hs : 0 < s.re) :
    HasMellin (fun t => ((chi t : ℝ) : ℂ)) s (1 / s) := by
  have hfun : (fun t => ((chi t : ℝ) : ℂ)) = Set.indicator (Ioc (0 : ℝ) 1) (fun _ => (1 : ℂ)) :=
    funext chi_complex
  rw [hfun]
  exact hasMellin_one_Ioc hs

/-! ## O resíduo -/

/-- O resíduo real `χ − Σ_k c_k ρ_{k+1}`. -/
noncomputable def res {N : ℕ} (c : Fin N → ℝ) (t : ℝ) : ℝ :=
  chi t - ∑ k : Fin N, c k * rho (k.val + 1) t

/-- A constante da cauda: `S = Σ_k c_k/(k+1)`. -/
noncomputable def tailS {N : ℕ} (c : Fin N → ℝ) : ℝ := ∑ k : Fin N, c k / ((k.val : ℝ) + 1)

theorem residualSq_eq_res {N : ℕ} (c : Fin N → ℝ) :
    residualSq N c = ∫ t in Ioi (0 : ℝ), res c t ^ 2 := rfl

theorem integrable_res_sq {N : ℕ} (c : Fin N → ℝ) :
    IntegrableOn (fun t => res c t ^ 2) (Ioi 0) := integrable_residual N c

/-- **Passo 2**: se `ζ(s) = 0` com `0 < Re s < 1`, então `∫_0^∞ res(t) t^{s−1} dt = 1/s`. -/
theorem mellin_res {N : ℕ} (c : Fin N → ℝ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) :
    MellinConvergent (fun t => ((res c t : ℝ) : ℂ)) s ∧
      mellin (fun t => ((res c t : ℝ) : ℂ)) s = 1 / s := by
  have hχ := hasMellin_chi hs0
  have hρ : ∀ k : Fin N, MellinConvergent (fun t => ((rho (k.val + 1) t : ℝ) : ℂ)) s :=
    fun k => mellinConvergent_rho (Nat.succ_pos _) hs0 hs1
  have hρ0 : ∀ k : Fin N,
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • ((rho (k.val + 1) t : ℝ) : ℂ) = 0 :=
    fun k => mellin_rho_eq_zero (Nat.succ_pos _) hs0 hs1 hz
  have hpt : ∀ t : ℝ, (t : ℂ) ^ (s - 1) • ((res c t : ℝ) : ℂ) =
      (t : ℂ) ^ (s - 1) • ((chi t : ℝ) : ℂ) -
        ∑ k : Fin N, (c k : ℂ) * ((t : ℂ) ^ (s - 1) • ((rho (k.val + 1) t : ℝ) : ℂ)) := by
    intro t
    simp only [res, smul_eq_mul]
    push_cast
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  have hint : ∀ k : Fin N, Integrable
      (fun t : ℝ => (c k : ℂ) * ((t : ℂ) ^ (s - 1) • ((rho (k.val + 1) t : ℝ) : ℂ)))
      (volume.restrict (Ioi 0)) :=
    fun k => Integrable.const_mul (hρ k) _
  have hsum : Integrable
      (fun t : ℝ => ∑ k : Fin N, (c k : ℂ) * ((t : ℂ) ^ (s - 1) • ((rho (k.val + 1) t : ℝ) : ℂ)))
      (volume.restrict (Ioi 0)) :=
    integrable_finsetSum _ fun k _ => hint k
  have hdiff : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • ((chi t : ℝ) : ℂ) -
      ∑ k : Fin N, (c k : ℂ) * ((t : ℂ) ^ (s - 1) • ((rho (k.val + 1) t : ℝ) : ℂ))) (Ioi 0) :=
    Integrable.sub hχ.1 hsum
  refine ⟨hdiff.congr_fun (fun t _ => (hpt t).symm) measurableSet_Ioi, ?_⟩
  have hχ2 : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • ((chi t : ℝ) : ℂ) = 1 / s := hχ.2
  unfold mellin
  simp_rw [hpt]
  rw [integral_sub hχ.1 hsum, integral_finsetSum _ (fun k _ => hint k), hχ2]
  simp_rw [integral_const_mul, hρ0, mul_zero, Finset.sum_const_zero, sub_zero]

/-- `‖∫_0^∞ f(t) t^{s−1} dt‖ ≤ ∫_0^∞ t^{σ−1} |f(t)| dt`. -/
theorem norm_mellin_le (f : ℝ → ℝ) (s : ℂ) :
    ‖mellin (fun t => ((f t : ℝ) : ℂ)) s‖ ≤ ∫ t in Ioi (0 : ℝ), t ^ (s.re - 1) * |f t| := by
  unfold mellin
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only
  rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re, Complex.norm_real,
    Real.norm_eq_abs]

/-! ## A cauda `(1, ∞)` -/

theorem rho_of_gt_one {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 1 < t) : rho k t = 1 / ((k : ℝ) * t) := by
  unfold rho
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < (k : ℝ) * t := mul_pos (by linarith) (by linarith)
  rw [Int.fract_eq_self]
  constructor
  · exact le_of_lt (one_div_pos.mpr hpos)
  · rw [div_lt_one hpos]; nlinarith

theorem res_of_gt_one {N : ℕ} (c : Fin N → ℝ) {t : ℝ} (ht : 1 < t) :
    res c t = -tailS c / t := by
  have ht0 : (0 : ℝ) < t := by linarith
  unfold res tailS
  rw [chi_of_gt_one ht, zero_sub]
  have hk : ∀ k : Fin N, c k * rho (k.val + 1) t = c k / ((k.val : ℝ) + 1) / t := by
    intro k
    rw [rho_of_gt_one (Nat.succ_pos _) ht]
    have hk1 : ((k.val : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [Finset.sum_congr rfl fun k _ => hk k, ← Finset.sum_div, neg_div]

/-- `∫_1^∞ res² = S²`. -/
theorem integral_tail_sq {N : ℕ} (c : Fin N → ℝ) :
    ∫ t in Ioi (1 : ℝ), res c t ^ 2 = tailS c ^ 2 := by
  have hpt : ∀ t ∈ Ioi (1 : ℝ), res c t ^ 2 = tailS c ^ 2 * t ^ (-2 : ℝ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    rw [res_of_gt_one c ht, Real.rpow_neg ht0.le, Real.rpow_two]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
  norm_num

/-- `S² ≤ ‖res‖²`. -/
theorem tailS_sq_le {N : ℕ} (c : Fin N → ℝ) : tailS c ^ 2 ≤ residualSq N c := by
  rw [← integral_tail_sq, residualSq_eq_res]
  exact setIntegral_mono_set (integrable_res_sq c)
    (Eventually.of_forall fun t => sq_nonneg _) (Ioi_subset_Ioi zero_le_one).eventuallyLE

/-- `∫_1^∞ t^{σ−1} |res| = |S|/(1−σ)` para `σ < 1`. -/
theorem integral_tail_weighted {N : ℕ} (c : Fin N → ℝ) {σ : ℝ} (hσ : σ < 1) :
    ∫ t in Ioi (1 : ℝ), t ^ (σ - 1) * |res c t| = |tailS c| / (1 - σ) := by
  have hpt : ∀ t ∈ Ioi (1 : ℝ), t ^ (σ - 1) * |res c t| = |tailS c| * t ^ (σ - 2) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have e : t ^ (σ - 2) = t ^ (σ - 1) / t := by
      rw [show σ - 2 = (σ - 1) - 1 by ring]
      exact Real.rpow_sub_one ht0.ne' _
    rw [res_of_gt_one c ht, abs_div, abs_neg, abs_of_pos ht0, e]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
  have h1 : σ - 2 + 1 ≠ 0 := by intro h; linarith
  have h2 : 1 - σ ≠ 0 := by intro h; linarith
  field_simp
  ring

/-! ## A parte `(0, 1]` -/

theorem amgm {a b l : ℝ} (hl : 0 < l) : b * a ≤ (l * a ^ 2 + b ^ 2 / l) / 2 := by
  have h2 : 0 ≤ (l * a - b) ^ 2 / l := div_nonneg (sq_nonneg _) hl.le
  have h3 : (l * a - b) ^ 2 / l = l * a ^ 2 - 2 * a * b + b ^ 2 / l := by
    field_simp
    ring
  nlinarith [h2, h3]

theorem integral_rpow_Ioc {r : ℝ} (hr : -1 < r) : ∫ t in Ioc (0 : ℝ) 1, t ^ r = 1 / (r + 1) := by
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_rpow (Or.inl hr), Real.one_rpow,
    Real.zero_rpow (by linarith : r + 1 ≠ 0), sub_zero]

theorem integrableOn_rpow_Ioc {r : ℝ} (hr : -1 < r) : IntegrableOn (fun t : ℝ => t ^ r) (Ioc 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    (intervalIntegral.intervalIntegrable_rpow' hr)

/-- Em `(0,1]`: `∫ t^{σ−1}|res| ≤ (λ‖res‖² + 1/(λ(2σ−1)))/2`. -/
theorem integral_head_le {N : ℕ} (c : Fin N → ℝ) {σ : ℝ} (hσ : 1 / 2 < σ) {l : ℝ} (hl : 0 < l)
    (hint : IntegrableOn (fun t => t ^ (σ - 1) * |res c t|) (Ioc 0 1)) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ (σ - 1) * |res c t| ≤
      (l * residualSq N c + 1 / (l * (2 * σ - 1))) / 2 := by
  have hr2 : IntegrableOn (fun t => res c t ^ 2) (Ioc 0 1) :=
    (integrable_res_sq c).mono_set Ioc_subset_Ioi_self
  have hpow : IntegrableOn (fun t : ℝ => t ^ (2 * σ - 2)) (Ioc 0 1) :=
    integrableOn_rpow_Ioc (by linarith)
  have hg : IntegrableOn (fun t => (l * res c t ^ 2 + t ^ (2 * σ - 2) / l) / 2) (Ioc 0 1) :=
    Integrable.div_const (Integrable.add (Integrable.const_mul hr2 l) (Integrable.div_const hpow l)) 2
  have hle : ∫ t in Ioc (0 : ℝ) 1, t ^ (σ - 1) * |res c t| ≤
      ∫ t in Ioc (0 : ℝ) 1, (l * res c t ^ 2 + t ^ (2 * σ - 2) / l) / 2 := by
    refine setIntegral_mono_on hint hg measurableSet_Ioc fun t ht => ?_
    have hsq : t ^ (2 * σ - 2) = (t ^ (σ - 1)) ^ 2 := by
      rw [show 2 * σ - 2 = (σ - 1) * 2 by ring, Real.rpow_mul ht.1.le, Real.rpow_two]
    rw [hsq, ← sq_abs (res c t)]
    exact amgm hl
  have hval : ∫ t in Ioc (0 : ℝ) 1, (l * res c t ^ 2 + t ^ (2 * σ - 2) / l) / 2 =
      (l * ∫ t in Ioc (0 : ℝ) 1, res c t ^ 2) / 2 + (1 / (2 * σ - 1)) / l / 2 := by
    rw [integral_div, integral_add (Integrable.const_mul hr2 l) (Integrable.div_const hpow l),
      integral_const_mul, integral_div, integral_rpow_Ioc (by linarith)]
    ring_nf
  have hR : ∫ t in Ioc (0 : ℝ) 1, res c t ^ 2 ≤ residualSq N c := by
    rw [residualSq_eq_res]
    exact setIntegral_mono_set (integrable_res_sq c)
      (Eventually.of_forall fun t => sq_nonneg _) Ioc_subset_Ioi_self.eventuallyLE
  have h2σ : 0 < 2 * σ - 1 := by linarith
  calc ∫ t in Ioc (0 : ℝ) 1, t ^ (σ - 1) * |res c t| ≤ _ := hle
    _ = (l * ∫ t in Ioc (0 : ℝ) 1, res c t ^ 2) / 2 + (1 / (2 * σ - 1)) / l / 2 := hval
    _ ≤ (l * residualSq N c) / 2 + (1 / (2 * σ - 1)) / l / 2 := by
        have := mul_le_mul_of_nonneg_left hR hl.le
        linarith
    _ = (l * residualSq N c + 1 / (l * (2 * σ - 1))) / 2 := by
        field_simp

/-! ## A desigualdade-chave e a não anulação na faixa -/

/-- **Desigualdade-chave**: se `ζ(s) = 0`, `1/2 < σ < 1`, então para todo resíduo e todo `λ > 0`,
`1/|s| ≤ (λ‖res‖² + 1/(λ(2σ−1)))/2 + √‖res‖²/(1−σ)`. -/
theorem key_ineq {N : ℕ} (c : Fin N → ℝ) {s : ℂ} (hs0 : 1 / 2 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) {l : ℝ} (hl : 0 < l) :
    1 / ‖s‖ ≤ (l * residualSq N c + 1 / (l * (2 * s.re - 1))) / 2 +
      Real.sqrt (residualSq N c) / (1 - s.re) := by
  obtain ⟨hconv, hval⟩ := mellin_res c (by linarith) hs1 hz
  have hnorm := norm_mellin_le (res c) s
  rw [hval, norm_div, norm_one] at hnorm
  -- integrabilidade do peso
  have hw : IntegrableOn (fun t => t ^ (s.re - 1) * |res c t|) (Ioi 0) := by
    refine IntegrableOn.congr_fun (Integrable.norm hconv) (fun t ht => ?_) measurableSet_Ioi
    simp only
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re, Complex.norm_real,
      Real.norm_eq_abs]
  have hsplit : ∫ t in Ioi (0 : ℝ), t ^ (s.re - 1) * |res c t| =
      (∫ t in Ioc (0 : ℝ) 1, t ^ (s.re - 1) * |res c t|) +
        ∫ t in Ioi (1 : ℝ), t ^ (s.re - 1) * |res c t| := by
    have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) :=
      Set.disjoint_left.mpr fun x hx1 hx2 => absurd hx2 (not_lt.mpr hx1.2)
    have hu := setIntegral_union hdisj measurableSet_Ioi (hw.mono_set Ioc_subset_Ioi_self)
      (hw.mono_set (Ioi_subset_Ioi zero_le_one))
    rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hu
    exact hu
  have hhead := integral_head_le c hs0 hl (hw.mono_set Ioc_subset_Ioi_self)
  have htail := integral_tail_weighted c hs1
  have hS : |tailS c| ≤ Real.sqrt (residualSq N c) := Real.abs_le_sqrt (tailS_sq_le c)
  have h1σ : 0 < 1 - s.re := by linarith
  have hS' : |tailS c| / (1 - s.re) ≤ Real.sqrt (residualSq N c) / (1 - s.re) :=
    div_le_div_of_nonneg_right hS h1σ.le
  calc 1 / ‖s‖ ≤ ∫ t in Ioi (0 : ℝ), t ^ (s.re - 1) * |res c t| := hnorm
    _ = (∫ t in Ioc (0 : ℝ) 1, t ^ (s.re - 1) * |res c t|) +
          ∫ t in Ioi (1 : ℝ), t ^ (s.re - 1) * |res c t| := hsplit
    _ ≤ (l * residualSq N c + 1 / (l * (2 * s.re - 1))) / 2 + |tailS c| / (1 - s.re) :=
        add_le_add hhead (le_of_eq htail)
    _ ≤ _ := by gcongr

/-- **`D_N → 0` ⇒ `ζ(s) ≠ 0` na faixa `1/2 < Re s < 1`.** -/
theorem zeta_ne_zero_strip (hD : Tendsto DN atTop (𝓝 0)) {s : ℂ} (hs0 : 1 / 2 < s.re)
    (hs1 : s.re < 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hsne : s ≠ 0 := by intro h; rw [h, zero_re] at hs0; linarith
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hsne
  set σ := s.re with hσ
  set A : ℝ := 1 / ‖s‖ with hA
  have hA0 : 0 < A := one_div_pos.mpr hsn
  have h2σ : 0 < 2 * σ - 1 := by linarith
  have h1σ : 0 < 1 - σ := by linarith
  set l : ℝ := 1 / (A * (2 * σ - 1)) with hl
  have hl0 : 0 < l := one_div_pos.mpr (mul_pos hA0 h2σ)
  have hlA : 1 / (l * (2 * σ - 1)) = A := by
    rw [hl]; field_simp
  set δ : ℝ := A * (1 - σ) / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  set ε : ℝ := min (A / (2 * l)) (δ ^ 2) with hε
  have hε0 : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨N, hN⟩ := (hD.eventually (gt_mem_nhds hε0)).exists
  obtain ⟨c, hc⟩ := exists_lt_of_ciInf_lt (show (⨅ c : Fin N → ℝ, residualSq N c) < ε from hN)
  have hR0 : 0 ≤ residualSq N c := integral_nonneg fun _ => sq_nonneg _
  have hkey := key_ineq c hs0 hs1 hz hl0
  rw [← hσ, ← hA, hlA] at hkey
  have hc1 : residualSq N c < A / (2 * l) := lt_of_lt_of_le hc (min_le_left _ _)
  have hc2 : residualSq N c < δ ^ 2 := lt_of_lt_of_le hc (min_le_right _ _)
  have hlR : l * residualSq N c < A / 2 := by
    have := mul_lt_mul_of_pos_left hc1 hl0
    have heq : l * (A / (2 * l)) = A / 2 := by field_simp
    linarith
  have hsq : Real.sqrt (residualSq N c) < δ := by
    rw [show δ = Real.sqrt (δ ^ 2) from (Real.sqrt_sq hδ0.le).symm]
    exact Real.sqrt_lt_sqrt hR0 hc2
  have hsqd : Real.sqrt (residualSq N c) / (1 - σ) < A / 4 := by
    rw [div_lt_iff₀ h1σ]
    have : δ = A / 4 * (1 - σ) := by rw [hδ]; ring
    linarith
  linarith

/-! ## Da faixa à Hipótese de Riemann (equação funcional da Mathlib) -/

/-- Se `ζ ≠ 0` em `1/2 < Re s < 1`, vale a Hipótese de Riemann (enunciado da Mathlib). -/
theorem riemannHypothesis_of_strip (h : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0) :
    RiemannHypothesis := by
  intro s hz htriv _
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `Re s < 1/2`: refletir por `w = 1 − s`
    set w : ℂ := 1 - s with hw
    have hwre : 1 / 2 < w.re := by rw [hw, sub_re, one_re]; linarith
    have hw0 : ∀ n : ℕ, w ≠ -n := by
      intro n hn
      have := congrArg Complex.re hn
      rw [neg_re, natCast_re] at this
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hζw : riemannZeta w ≠ 0 := by
      rcases le_or_gt 1 w.re with h1 | h1
      · exact riemannZeta_ne_zero_of_one_le_re h1
      · exact h w hwre h1
    by_cases hw1 : w = 1
    · have hs0 : s = 0 := by linear_combination -hw1 + hw
      rw [hs0, riemannZeta_zero] at hz
      norm_num at hz
    · have hfe := riemannZeta_one_sub hw0 hw1
      rw [show (1 : ℂ) - w = s by rw [hw]; ring, hz] at hfe
      have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      have h2π : (2 : ℂ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero hπ
      have hpow : ((2 : ℂ) * Real.pi) ^ (-w) ≠ 0 := by
        intro hp
        rw [cpow_eq_zero_iff] at hp
        exact h2π hp.1
      have hΓ : Gamma w ≠ 0 := Complex.Gamma_ne_zero hw0
      have hcos : Complex.cos (Real.pi * w / 2) ≠ 0 := by
        intro hc
        obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
        have h2 : w * Real.pi = (2 * k + 1) * Real.pi := by linear_combination 2 * hk
        have hwk : w = 2 * k + 1 := mul_right_cancel₀ hπ h2
        have hre : w.re = 2 * (k : ℝ) + 1 := by
          rw [hwk]; simp
        have hk0 : (0 : ℤ) ≤ k := by
          by_contra hneg
          have : k ≤ -1 := by omega
          have : (k : ℝ) ≤ -1 := by exact_mod_cast this
          linarith
        have hk1 : k ≠ 0 := by
          intro hk0'
          apply hw1
          rw [hwk, hk0']
          simp
        apply htriv
        refine ⟨(k - 1).toNat, ?_⟩
        have hcast : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
          have : (((k - 1).toNat : ℕ) : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
          exact_mod_cast this
        rw [hcast]
        linear_combination hw - hwk
      exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hΓ) hcos) hζw)
        hfe.symm
  · rcases le_or_gt 1 s.re with h1 | h1
    · exact riemannZeta_ne_zero_of_one_le_re h1 hz
    · exact h s hgt h1 hz

/-! ## Resultados finais -/

/-- **A ponte B1, provada**: `D_N → 0 ⇒ RH`. Isto é exatamente `BaezDuarteCriterion`. -/
theorem baezDuarteCriterion : BaezDuarteCriterion :=
  fun hD => riemannHypothesis_of_strip fun _ hs0 hs1 => zeta_ne_zero_strip hD hs0 hs1

/-- RH a partir de `inf_N D_N = 0` — **sem nenhuma ponte**. -/
theorem riemann_of_iInf_zero (h : ⨅ N, DN N = 0) : RiemannHypothesis :=
  baezDuarteCriterion (O1_iff_iInf_zero.mpr h)

/-- RH a partir da exclusão do estado `finito` para `D_N` — sem pontes. -/
theorem riemann_of_not_finito
    (h : ¬ ATK.IndeterminacyStates.Comporta atTop DN ATK.IndeterminacyStates.Estado7.finito) :
    RiemannHypothesis :=
  baezDuarteCriterion (ATK.RiemannStates.O1_iff_nao_finito.mpr h)

/-- O condicional original, agora com **uma** hipótese só (a obrigação aberta O1). -/
theorem riemann_of_uniformLogBound (h : UniformLogBound) : RiemannHypothesis :=
  riemann_conditional baezDuarteCriterion h

end ATK.BaezDuarteBridge

#print axioms ATK.BaezDuarteBridge.chi_complex
#print axioms ATK.BaezDuarteBridge.hasMellin_chi
#print axioms ATK.BaezDuarteBridge.residualSq_eq_res
#print axioms ATK.BaezDuarteBridge.integrable_res_sq
#print axioms ATK.BaezDuarteBridge.mellin_res
#print axioms ATK.BaezDuarteBridge.norm_mellin_le
#print axioms ATK.BaezDuarteBridge.rho_of_gt_one
#print axioms ATK.BaezDuarteBridge.res_of_gt_one
#print axioms ATK.BaezDuarteBridge.integral_tail_sq
#print axioms ATK.BaezDuarteBridge.tailS_sq_le
#print axioms ATK.BaezDuarteBridge.integral_tail_weighted
#print axioms ATK.BaezDuarteBridge.amgm
#print axioms ATK.BaezDuarteBridge.integral_rpow_Ioc
#print axioms ATK.BaezDuarteBridge.integrableOn_rpow_Ioc
#print axioms ATK.BaezDuarteBridge.integral_head_le
#print axioms ATK.BaezDuarteBridge.key_ineq
#print axioms ATK.BaezDuarteBridge.zeta_ne_zero_strip
#print axioms ATK.BaezDuarteBridge.riemannHypothesis_of_strip
#print axioms ATK.BaezDuarteBridge.baezDuarteCriterion
#print axioms ATK.BaezDuarteBridge.riemann_of_iInf_zero
#print axioms ATK.BaezDuarteBridge.riemann_of_not_finito
#print axioms ATK.BaezDuarteBridge.riemann_of_uniformLogBound
