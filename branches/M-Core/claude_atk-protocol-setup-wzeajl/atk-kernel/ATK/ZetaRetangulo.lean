import ATK.ZetaSimetria

/-!
# ATK — Uma região sem zeros que alcança o meio: RH verificada até a altura `√3/2`

Movendo o "fim fechado" para dentro da faixa, incondicionalmente:

1. `norm_H_le`, `Hr_le`: `|∫_1^∞ {t} t^{-s-1} dt| ≤ ∫_1^∞ {t} t^{-σ-1} dt ≤ 1/(2σ)` (`σ = Re s > 0`).
   A segunda desigualdade vem de `∫_m^{m+1} ({t} − 1/2) t^{-σ-1} dt ≤ 0` em cada intervalo unitário
   (`{t} − 1/2` cresce e `t^{-σ-1}` decresce), somada e passada ao limite.
2. `zeta_ne_zero_disco`: **`ζ(s) ≠ 0` sempre que `|s − 1| < 2·Re s`** (com `Re s > 0`). A região
   contém o segmento real `(1/3, ∞)` e, na reta crítica, `|Im s| < √3/2`.
3. `zeta_ne_zero_baixo` (com a tensão `s ↦ 1 − s`): **nenhum zero na faixa com `(Im s)² < 3/4`**;
   `riemannAte_raiz`: **RH vale até a altura `√3/2`** (`RiemannAte`).

Na linguagem da geometria de `I`: abaixo da altura `√3/2`, o início fechado e o fim fechado já
chegam ao meio. O primeiro zero conhecido está na altura ≈ 14,13; empurrar a altura com fórmulas de
Euler–Maclaurin de ordem maior é rotina, e uniformizar em toda altura é RH (O1).
-/

open Complex Set MeasureTheory Filter Topology

namespace ATK.ZetaRetangulo

open ATK.ZetaStrip ATK.ZetaSimetria

/-- `∫_1^∞ {t} t^{-σ-1} dt`. -/
noncomputable def Hr (σ : ℝ) : ℝ := ∫ t in Ioi (1 : ℝ), t ^ (-σ - 1) * Int.fract t

/-- `({t} − 1/2) t^{-σ-1}`. -/
noncomputable def g (σ t : ℝ) : ℝ := (Int.fract t - 1 / 2) * t ^ (-σ - 1)

theorem norm_H_le {s : ℂ} : ‖H s‖ ≤ Hr s.re := by
  rw [H_eq_integral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  unfold Hr
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Int.fract_nonneg t), show (-s - 1).re = -s.re - 1 by simp]

theorem integrableOn_rpow {σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun t : ℝ => t ^ (-σ - 1)) (Ioi 1) :=
  integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one

theorem integrableOn_g {σ : ℝ} (hσ : 0 < σ) : IntegrableOn (g σ) (Ioi 1) := by
  refine Integrable.mono' ((integrableOn_rpow hσ).const_mul (1 / 2)) ?_ ?_
  · exact ((measurable_fract.sub_const _).mul (measurable_id.pow_const _)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0 : ℝ) ≤ t := le_of_lt (lt_trans zero_lt_one ht)
    unfold g
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0 _)]
    have h1 : |Int.fract t - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [Int.fract_nonneg t, Int.fract_lt_one t]
    exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht0 _)

theorem integral_rpow {σ : ℝ} (hσ : 0 < σ) : ∫ t in Ioi (1 : ℝ), t ^ (-σ - 1) = 1 / σ := by
  rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow,
    show -σ - 1 + 1 = -σ by ring]
  field_simp

theorem Hr_eq {σ : ℝ} (hσ : 0 < σ) : Hr σ = (∫ t in Ioi (1 : ℝ), g σ t) + 1 / (2 * σ) := by
  have e : (fun t : ℝ => t ^ (-σ - 1) * Int.fract t) =
      fun t => g σ t + 1 / 2 * t ^ (-σ - 1) := by
    funext t; unfold g; ring
  unfold Hr
  rw [e, integral_add (integrableOn_g hσ) ((integrableOn_rpow hσ).const_mul _),
    integral_const_mul, integral_rpow hσ]
  field_simp

theorem fract_on {m : ℕ} {t : ℝ} (h1 : (m : ℝ) ≤ t) (h2 : t < m + 1) : Int.fract t = t - m := by
  have hf : ⌊t⌋ = (m : ℤ) := Int.floor_eq_iff.mpr ⟨by exact_mod_cast h1, by push_cast; exact h2⟩
  unfold Int.fract
  rw [hf]
  push_cast
  ring

theorem intervalIntegrable_g {σ : ℝ} (hσ : 0 < σ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (g σ) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (integrableOn_g hσ).mono_set fun t ht => lt_of_le_of_lt ha ht.1

/-- Em cada intervalo unitário `[m, m+1]`, `m ≥ 1`: `∫ ({t} − 1/2) t^{-σ-1} ≤ 0`. -/
theorem peca_nonpos {σ : ℝ} (hσ : 0 < σ) {m : ℕ} (hm : 1 ≤ m) :
    ∫ t in (m : ℝ)..(m + 1), g σ t ≤ 0 := by
  set c : ℝ := ((m : ℝ) + 1 / 2) ^ (-σ - 1) with hc
  have hm0 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hint := intervalIntegrable_g hσ hm0 (by linarith : (m : ℝ) ≤ m + 1)
  have hint2 : IntervalIntegrable (fun t : ℝ => (t - (m + 1 / 2)) * c) volume (m : ℝ) (m + 1) :=
    ((continuous_id.sub continuous_const).mul continuous_const).intervalIntegrable _ _
  have hpt : ∀ t ∈ Ioo (m : ℝ) (m + 1), g σ t ≤ (t - (m + 1 / 2)) * c := by
    rintro t ⟨h1, h2⟩
    have ht0 : 0 < t := by linarith
    unfold g
    rw [fract_on h1.le h2, show t - m - 1 / 2 = t - (m + 1 / 2) by ring]
    rcases le_total t ((m : ℝ) + 1 / 2) with h | h
    · have hpow : c ≤ t ^ (-σ - 1) := Real.rpow_le_rpow_of_nonpos ht0 h (by linarith)
      exact mul_le_mul_of_nonpos_left hpow (by linarith)
    · have hpow : t ^ (-σ - 1) ≤ c := Real.rpow_le_rpow_of_nonpos (by positivity) h (by linarith)
      exact mul_le_mul_of_nonneg_left hpow (by linarith)
  have hle := intervalIntegral.integral_mono_on_of_le_Ioo (by linarith) hint hint2 hpt
  refine hle.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_mul_const]
  have h0 : ∫ t in (m : ℝ)..(m + 1), (t - (m + 1 / 2)) = 0 := by
    rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x), integral_id]
    ring
  rw [h0, zero_mul]

/-- `∫_1^∞ ({t} − 1/2) t^{-σ-1} dt ≤ 0`. -/
theorem integral_g_nonpos {σ : ℝ} (hσ : 0 < σ) : ∫ t in Ioi (1 : ℝ), g σ t ≤ 0 := by
  have hlim := intervalIntegral_tendsto_integral_Ioi (μ := volume) (l := atTop)
    (b := fun n : ℕ => (n : ℝ) + 1) 1 (integrableOn_g hσ)
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine le_of_tendsto' hlim fun n => ?_
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := g σ) (μ := volume)
    (a := fun k : ℕ => (k : ℝ) + 1) (n := n) fun k _ =>
      intervalIntegrable_g hσ (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
        (by push_cast; linarith)
  simp only [Nat.cast_zero, zero_add] at hsum
  rw [← hsum]
  refine Finset.sum_nonpos fun k _ => ?_
  have := peca_nonpos hσ (m := k + 1) (by omega)
  convert this using 2
  push_cast
  ring

/-- **`∫_1^∞ {t} t^{-σ-1} dt ≤ 1/(2σ)`.** -/
theorem Hr_le {σ : ℝ} (hσ : 0 < σ) : Hr σ ≤ 1 / (2 * σ) := by
  rw [Hr_eq hσ]; linarith [integral_g_nonpos hσ]

/-- **Região sem zeros: `ζ(s) ≠ 0` se `Re s > 0` e `|s − 1| < 2·Re s`.** -/
theorem zeta_ne_zero_disco {s : ℂ} (hs : 0 < s.re) (h1 : ‖s - 1‖ < 2 * s.re) :
    riemannZeta s ≠ 0 := by
  intro hz
  rcases le_or_gt 1 s.re with hre | hre
  · exact riemannZeta_ne_zero_of_one_le_re hre hz
  have hs1 : s ≠ 1 := by intro h; rw [h, one_re] at hre; exact lt_irrefl _ hre
  have hH := H_eq_zeta hs hs1
  rw [hz, zero_div, sub_zero] at hH
  have hn : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
  have h2 : ‖H s‖ = 1 / ‖s - 1‖ := by rw [hH, norm_div, norm_one]
  have h3 := (norm_H_le (s := s)).trans (Hr_le hs)
  rw [h2] at h3
  have := (one_div_le_one_div hn (by positivity)).mp h3
  linarith

/-- **Nenhum zero na faixa com `(Im s)² < 3/4`.** -/
theorem zeta_ne_zero_baixo {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (ht : s.im ^ 2 < 3 / 4) :
    riemannZeta s ≠ 0 := by
  have key : ∀ w : ℂ, 1 / 2 ≤ w.re → w.im ^ 2 < 3 / 4 → riemannZeta w ≠ 0 := by
    intro w hw0 hwt
    apply zeta_ne_zero_disco (by linarith)
    have hsq : ‖w - 1‖ ^ 2 = (w.re - 1) ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have hlt : ‖w - 1‖ ^ 2 < (2 * w.re) ^ 2 := by
      rw [hsq]
      nlinarith [mul_nonneg (sub_nonneg.mpr hw0) (by linarith : (0 : ℝ) ≤ 3 * w.re + 7 / 2)]
    exact (sq_lt_sq₀ (norm_nonneg _) (by linarith)).mp hlt
  rcases le_or_gt (1 / 2) s.re with h | h
  · exact key s h ht
  · intro hz
    have h2 := tensao_mem_Z (⟨hz, h0, h1⟩ : s ∈ Z)
    have him : (tensao s).im ^ 2 = s.im ^ 2 := by
      unfold tensao; simp only [sub_im, one_im, zero_sub, neg_sq]
    exact key (tensao s) (by rw [re_tensao]; linarith) (by rw [him]; exact ht) h2.1

/-- Todo zero não trivial tem `(Im s)² ≥ 3/4`. -/
theorem sem_zeros_ate_altura : ∀ s ∈ Z, 3 / 4 ≤ s.im ^ 2 := by
  rintro s ⟨hz, h0, h1⟩
  by_contra h
  exact zeta_ne_zero_baixo h0 h1 (not_le.mp h) hz

/-- RH até a altura `T`. -/
def RiemannAte (T : ℝ) : Prop := ∀ s ∈ Z, |s.im| < T → s.re = 1 / 2

theorem riemannAte_mono {T T' : ℝ} (h : T' ≤ T) (hT : RiemannAte T) : RiemannAte T' :=
  fun s hs ht => hT s hs (lt_of_lt_of_le ht h)

/-- **RH vale até a altura `√3/2`** (vacuamente: não há zeros abaixo dela). -/
theorem riemannAte_raiz : RiemannAte (Real.sqrt 3 / 2) := by
  intro s hs ht
  exfalso
  have h34 := sem_zeros_ate_altura s hs
  have hlt : |s.im| ^ 2 < (Real.sqrt 3 / 2) ^ 2 := pow_lt_pow_left₀ ht (abs_nonneg _) two_ne_zero
  rw [sq_abs, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hlt
  linarith

/-- RH é RH em toda altura. -/
theorem riemann_iff_ate : RiemannHypothesis ↔ ∀ T, RiemannAte T := by
  rw [riemann_iff_torcao]
  constructor
  · intro h T s hs _
    exact (torcao_fixo_iff s).mp (h s hs)
  · intro h s hs
    exact (torcao_fixo_iff s).mpr (h (|s.im| + 1) s hs (by linarith))

end ATK.ZetaRetangulo

#print axioms ATK.ZetaRetangulo.norm_H_le
#print axioms ATK.ZetaRetangulo.integrableOn_rpow
#print axioms ATK.ZetaRetangulo.integrableOn_g
#print axioms ATK.ZetaRetangulo.integral_rpow
#print axioms ATK.ZetaRetangulo.Hr_eq
#print axioms ATK.ZetaRetangulo.fract_on
#print axioms ATK.ZetaRetangulo.intervalIntegrable_g
#print axioms ATK.ZetaRetangulo.peca_nonpos
#print axioms ATK.ZetaRetangulo.integral_g_nonpos
#print axioms ATK.ZetaRetangulo.Hr_le
#print axioms ATK.ZetaRetangulo.zeta_ne_zero_disco
#print axioms ATK.ZetaRetangulo.zeta_ne_zero_baixo
#print axioms ATK.ZetaRetangulo.sem_zeros_ate_altura
#print axioms ATK.ZetaRetangulo.riemannAte_mono
#print axioms ATK.ZetaRetangulo.riemannAte_raiz
#print axioms ATK.ZetaRetangulo.riemann_iff_ate
