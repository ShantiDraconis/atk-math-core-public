import ATK.BaezDuarteBridge
import ATK.ZeroClasses.OmegaPsi

/-!
# Báez-Duarte ponderado: `D_N(σ) → 0` ⟹ `ζ ≠ 0` em `Re s > σ` (rodada 59)

Para `0 < σ < 1`, com o peso `t^{2σ−1}`:

  `D_N(σ) = inf_c ∫_0^∞ (χ(t) − Σ_{k ≤ N} c_k ρ_k(t))² t^{2σ−1} dt`,   `ρ_k(t) = {1/(kt)}`

(`DNσ`; `DNσ_meio`: `D_N(½) = D_N`, o `D_N` de Báez-Duarte). É a questão Q2(i) de `fronteira/RH_frontier.md`.

* **`semZeros_of_DNσ`**: `inf_N D_N(σ) = 0` ⟹ `ζ ≠ 0` em `Re s > σ` (`SemZeros σ`, rodada 57);
* `psi_of_DNσ`, `mertens_of_DNσ` (`½ ≤ σ < 1`): daí `ψ(x) = x + O(x^{σ+ε})` e `M(x) = O(x^{σ+ε})`;
* **`piso_DNσ`**: para `0 < σ < ½`, `inf_N D_N(σ) > 0` — incondicional (Hardy, rodada 50: há zeros em `Re s = ½`).

A prova é a da ponte B1 (`ATK.BaezDuarteBridge`) com o peso: se `ζ(s) = 0`, `σ < Re s < 1`, então
`∫_0^∞ res(t) t^{s−1} dt = 1/s` (`mellin_res`); em `(0, 1]`, `t^{Re s − 1}|res| = (|res| t^{σ−½}) t^{Re s − σ − ½}` e
AM-GM dão `≤ (λ‖res‖²_σ + 1/(2λ(Re s − σ)))/2` (`head_le`); em `(1, ∞)`, `res = −S/t` e `S² ≤ (2 − 2σ)‖res‖²_σ`
(`tail_sq_le`). Logo `1/|s| ≤ (λW + 1/(2λ(Re s − σ)))/2 + √((2 − 2σ)W)/(1 − Re s)` (`key_ineq`), absurdo se `W` é
pequeno.

Classificação (rodada 59): **reformulação** (metade suficiente de um critério de Nyman–Beurling para semiplanos;
Beurling 1955 fez a versão `L^p`). A necessidade com taxa, Q2(ii), segue BUILD_PENDING; RH continua OPEN_MATH.
-/

open Complex Set MeasureTheory Filter Topology

namespace ATK.ZeroClasses.BDPonderado

open ATK.Conditional.Riemann ATK.RiemannFaithful
open ATK.BaezDuarteBridge (res tailS res_of_gt_one mellin_res norm_mellin_le amgm integral_rpow_Ioc
  integrableOn_rpow_Ioc integral_tail_weighted residualSq_eq_res)
open ATK.ZeroClasses.QuasiRH (SemZeros semZeros_iff_psi semZeros_iff_mertens)

/-! ## 1. A norma ponderada -/

/-- `‖res‖²_σ = ∫_0^∞ res(t)² t^{2σ−1} dt`. -/
noncomputable def Wσ (σ : ℝ) {N : ℕ} (c : Fin N → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), res c t ^ 2 * t ^ (2 * σ - 1)

/-- `D_N(σ) = inf_c ‖χ − Σ c_k ρ_{k+1}‖²_σ`. -/
noncomputable def DNσ (σ : ℝ) (N : ℕ) : ℝ := ⨅ c : Fin N → ℝ, Wσ σ c

theorem Wσ_nonneg (σ : ℝ) {N : ℕ} (c : Fin N → ℝ) : 0 ≤ Wσ σ c :=
  setIntegral_nonneg measurableSet_Ioi fun _ ht => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt ht) _)

theorem DNσ_nonneg (σ : ℝ) (N : ℕ) : 0 ≤ DNσ σ N := Real.iInf_nonneg fun c => Wσ_nonneg σ c

/-- `D_N(½) = D_N` (o peso `t⁰ = 1`). -/
theorem DNσ_meio (N : ℕ) : DNσ (1 / 2) N = DN N := by
  unfold DNσ DN
  congr 1
  funext c
  rw [residualSq_eq_res]
  unfold Wσ
  refine setIntegral_congr_fun measurableSet_Ioi fun _ _ => ?_
  simp

theorem measurable_res {N : ℕ} (c : Fin N → ℝ) : Measurable (res c) :=
  measurable_chi.sub (Finset.measurable_sum _ fun _ _ => measurable_const.mul (measurable_rho _))

theorem abs_res_le {N : ℕ} (c : Fin N → ℝ) (t : ℝ) : |res c t| ≤ 1 + ∑ k : Fin N, |c k| := by
  have hS := abs_sum_le c t 1 fun _ => by
    rw [abs_of_nonneg (rho_nonneg _ _)]; exact rho_le_one _ _
  obtain ⟨h3, h4⟩ := abs_le.mp hS
  have h1 := chi_nonneg t
  have h2 := chi_le_one t
  unfold res
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem res_sq_w_gt_one {N : ℕ} (c : Fin N → ℝ) (σ : ℝ) {t : ℝ} (ht : 1 < t) :
    res c t ^ 2 * t ^ (2 * σ - 1) = tailS c ^ 2 * t ^ (2 * σ - 3) := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have e : t ^ (2 * σ - 3) = t ^ (2 * σ - 1) / t ^ 2 := by
    rw [show 2 * σ - 3 = (2 * σ - 1) - 2 by ring, Real.rpow_sub ht0, Real.rpow_two]
  rw [res_of_gt_one c ht, e]
  field_simp

theorem integrable_w {N : ℕ} (c : Fin N → ℝ) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    IntegrableOn (fun t => res c t ^ 2 * t ^ (2 * σ - 1)) (Ioi 0) := by
  set B : ℝ := 1 + ∑ k : Fin N, |c k| with hB
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hpow : IntegrableOn (fun t : ℝ => B ^ 2 * t ^ (2 * σ - 1)) (Ioc 0 1) :=
      (integrableOn_rpow_Ioc (by linarith)).const_mul _
    refine Integrable.mono' hpow
      (((measurable_res c).pow_const 2).mul (measurable_id.pow_const _)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have hw : 0 ≤ t ^ (2 * σ - 1) := Real.rpow_nonneg ht.1.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) hw)]
    have h1 : res c t ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_res_le c t) 2
    exact mul_le_mul_of_nonneg_right h1 hw
  · have hg : IntegrableOn (fun t : ℝ => tailS c ^ 2 * t ^ (2 * σ - 3)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
    exact hg.congr_fun (fun t ht => (res_sq_w_gt_one c σ ht).symm) measurableSet_Ioi

/-- `S² ≤ (2 − 2σ)‖res‖²_σ`. -/
theorem tail_sq_le {N : ℕ} (c : Fin N → ℝ) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    tailS c ^ 2 ≤ (2 - 2 * σ) * Wσ σ c := by
  have hval : ∫ t in Ioi (1 : ℝ), res c t ^ 2 * t ^ (2 * σ - 1) = tailS c ^ 2 / (2 - 2 * σ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun t ht => res_sq_w_gt_one c σ ht, integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
    have h1 : 2 * σ - 3 + 1 ≠ 0 := by intro h; linarith
    have h2 : 2 - 2 * σ ≠ 0 := by intro h; linarith
    have h3 : (1 : ℝ) - σ ≠ 0 := by intro h; linarith
    have e : 2 * σ - 3 + 1 = -(2 - 2 * σ) := by ring
    rw [e]
    field_simp
  have hle : ∫ t in Ioi (1 : ℝ), res c t ^ 2 * t ^ (2 * σ - 1) ≤ Wσ σ c := by
    unfold Wσ
    exact setIntegral_mono_set (integrable_w c hσ0 hσ1)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt ht) _)))
      (Ioi_subset_Ioi zero_le_one).eventuallyLE
  rw [hval, div_le_iff₀ (by linarith)] at hle
  linarith

/-! ## 2. A desigualdade-chave -/

/-- Em `(0, 1]`: `∫ t^{s′−1}|res| ≤ (λ‖res‖²_σ + 1/(2λ(s′ − σ)))/2` para `σ < s′`. -/
theorem head_le {N : ℕ} (c : Fin N → ℝ) {σ s' : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hs : σ < s') {l : ℝ}
    (hl : 0 < l) (hint : IntegrableOn (fun t => t ^ (s' - 1) * |res c t|) (Ioc 0 1)) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ (s' - 1) * |res c t| ≤ (l * Wσ σ c + 1 / (l * (2 * (s' - σ)))) / 2 := by
  have hr2 : IntegrableOn (fun t => res c t ^ 2 * t ^ (2 * σ - 1)) (Ioc 0 1) :=
    (integrable_w c hσ0 hσ1).mono_set Ioc_subset_Ioi_self
  have hpow : IntegrableOn (fun t : ℝ => t ^ (2 * (s' - σ) - 1)) (Ioc 0 1) :=
    integrableOn_rpow_Ioc (by linarith)
  have hg : IntegrableOn (fun t => (l * (res c t ^ 2 * t ^ (2 * σ - 1)) + t ^ (2 * (s' - σ) - 1) / l) / 2)
      (Ioc 0 1) :=
    Integrable.div_const (Integrable.add (Integrable.const_mul hr2 l) (Integrable.div_const hpow l)) 2
  have hle : ∫ t in Ioc (0 : ℝ) 1, t ^ (s' - 1) * |res c t| ≤
      ∫ t in Ioc (0 : ℝ) 1, (l * (res c t ^ 2 * t ^ (2 * σ - 1)) + t ^ (2 * (s' - σ) - 1) / l) / 2 := by
    refine setIntegral_mono_on hint hg measurableSet_Ioc fun t ht => ?_
    have ht0 := ht.1
    have ha : (|res c t| * t ^ (σ - 1 / 2)) ^ 2 = res c t ^ 2 * t ^ (2 * σ - 1) := by
      rw [mul_pow, sq_abs]
      congr 1
      rw [← Real.rpow_natCast (t ^ (σ - 1 / 2)) 2, ← Real.rpow_mul ht0.le]
      congr 1
      push_cast
      ring
    have hb : (t ^ (s' - σ - 1 / 2)) ^ 2 = t ^ (2 * (s' - σ) - 1) := by
      rw [← Real.rpow_natCast (t ^ (s' - σ - 1 / 2)) 2, ← Real.rpow_mul ht0.le]
      congr 1
      push_cast
      ring
    have hab : t ^ (s' - σ - 1 / 2) * (|res c t| * t ^ (σ - 1 / 2)) = t ^ (s' - 1) * |res c t| := by
      rw [mul_left_comm, ← Real.rpow_add ht0]
      ring_nf
    have := amgm (a := |res c t| * t ^ (σ - 1 / 2)) (b := t ^ (s' - σ - 1 / 2)) hl
    rw [ha, hb, hab] at this
    exact this
  have hval : ∫ t in Ioc (0 : ℝ) 1, (l * (res c t ^ 2 * t ^ (2 * σ - 1)) + t ^ (2 * (s' - σ) - 1) / l) / 2 =
      (l * ∫ t in Ioc (0 : ℝ) 1, res c t ^ 2 * t ^ (2 * σ - 1)) / 2 + (1 / (2 * (s' - σ))) / l / 2 := by
    rw [integral_div, integral_add (Integrable.const_mul hr2 l) (Integrable.div_const hpow l),
      integral_const_mul, integral_div, integral_rpow_Ioc (by linarith)]
    ring_nf
  have hR : ∫ t in Ioc (0 : ℝ) 1, res c t ^ 2 * t ^ (2 * σ - 1) ≤ Wσ σ c := by
    unfold Wσ
    exact setIntegral_mono_set (integrable_w c hσ0 hσ1)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt ht) _)))
      Ioc_subset_Ioi_self.eventuallyLE
  have h2 : 0 < 2 * (s' - σ) := by linarith
  calc ∫ t in Ioc (0 : ℝ) 1, t ^ (s' - 1) * |res c t| ≤ _ := hle
    _ = (l * ∫ t in Ioc (0 : ℝ) 1, res c t ^ 2 * t ^ (2 * σ - 1)) / 2 + (1 / (2 * (s' - σ))) / l / 2 := hval
    _ ≤ (l * Wσ σ c) / 2 + (1 / (2 * (s' - σ))) / l / 2 := by
        have := mul_le_mul_of_nonneg_left hR hl.le
        linarith
    _ = (l * Wσ σ c + 1 / (l * (2 * (s' - σ)))) / 2 := by
        field_simp

/-- **Desigualdade-chave ponderada**: se `ζ(s) = 0`, `σ < Re s < 1`, então para todo resíduo e todo `λ > 0`,
`1/|s| ≤ (λW + 1/(2λ(Re s − σ)))/2 + √((2 − 2σ)W)/(1 − Re s)`, `W = ‖res‖²_σ`. -/
theorem key_ineq {N : ℕ} (c : Fin N → ℝ) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {s : ℂ} (hs0 : σ < s.re)
    (hs1 : s.re < 1) (hz : riemannZeta s = 0) {l : ℝ} (hl : 0 < l) :
    1 / ‖s‖ ≤ (l * Wσ σ c + 1 / (l * (2 * (s.re - σ)))) / 2 +
      Real.sqrt ((2 - 2 * σ) * Wσ σ c) / (1 - s.re) := by
  obtain ⟨hconv, hval⟩ := mellin_res c (by linarith) hs1 hz
  have hnorm := norm_mellin_le (res c) s
  rw [hval, norm_div, norm_one] at hnorm
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
  have hhead := head_le c hσ0 hσ1 hs0 hl (hw.mono_set Ioc_subset_Ioi_self)
  have htail := integral_tail_weighted c hs1
  have hS : |tailS c| ≤ Real.sqrt ((2 - 2 * σ) * Wσ σ c) := Real.abs_le_sqrt (tail_sq_le c hσ0 hσ1)
  have h1σ : 0 < 1 - s.re := by linarith
  have hS' : |tailS c| / (1 - s.re) ≤ Real.sqrt ((2 - 2 * σ) * Wσ σ c) / (1 - s.re) :=
    div_le_div_of_nonneg_right hS h1σ.le
  calc 1 / ‖s‖ ≤ ∫ t in Ioi (0 : ℝ), t ^ (s.re - 1) * |res c t| := hnorm
    _ = (∫ t in Ioc (0 : ℝ) 1, t ^ (s.re - 1) * |res c t|) +
          ∫ t in Ioi (1 : ℝ), t ^ (s.re - 1) * |res c t| := hsplit
    _ ≤ (l * Wσ σ c + 1 / (l * (2 * (s.re - σ)))) / 2 + |tailS c| / (1 - s.re) :=
        add_le_add hhead (le_of_eq htail)
    _ ≤ _ := by gcongr

/-! ## 3. Os teoremas -/

/-- **`D_N(σ)` pequeno ⟹ `ζ(s) ≠ 0` em `σ < Re s < 1`.** -/
theorem zeta_ne_zero_of_DNσ {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hD : ∀ ε > 0, ∃ N, DNσ σ N < ε) {s : ℂ}
    (hs0 : σ < s.re) (hs1 : s.re < 1) : riemannZeta s ≠ 0 := by
  intro hz
  have hsne : s ≠ 0 := by intro h; rw [h, zero_re] at hs0; linarith
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hsne
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 1 / ‖s‖ := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; exact one_div_pos.mpr hsn
  have h2 : 0 < 2 * (s.re - σ) := by linarith
  have h1s : 0 < 1 - s.re := by linarith
  have h2σ : 0 < 2 - 2 * σ := by linarith
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = 1 / (A * (2 * (s.re - σ))) := ⟨_, rfl⟩
  have hl0 : 0 < l := by rw [hl]; exact one_div_pos.mpr (mul_pos hA0 h2)
  have hsσ : s.re - σ ≠ 0 := (by linarith : (0 : ℝ) < s.re - σ).ne'
  have hA' : A ≠ 0 := hA0.ne'
  have hlx : l * (2 * (s.re - σ)) = 1 / A := by rw [hl]; field_simp
  have hlA : 1 / (l * (2 * (s.re - σ))) = A := by rw [hlx, one_div_one_div]
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = A * (1 - s.re) / 4 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (A / (2 * l)) (δ ^ 2 / (2 - 2 * σ)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by positivity)
  obtain ⟨N, hN⟩ := hD ε hε0
  obtain ⟨c, hc⟩ := exists_lt_of_ciInf_lt (show (⨅ c : Fin N → ℝ, Wσ σ c) < ε from hN)
  have hW0 := Wσ_nonneg σ c
  have hkey := key_ineq c hσ0 hσ1 hs0 hs1 hz hl0
  rw [← hA, hlA] at hkey
  have hc1 : Wσ σ c < A / (2 * l) := lt_of_lt_of_le hc (by rw [hε]; exact min_le_left _ _)
  have hc2 : Wσ σ c < δ ^ 2 / (2 - 2 * σ) := lt_of_lt_of_le hc (by rw [hε]; exact min_le_right _ _)
  have hlR : l * Wσ σ c < A / 2 := by
    have := mul_lt_mul_of_pos_left hc1 hl0
    have heq : l * (A / (2 * l)) = A / 2 := by field_simp
    linarith
  have hc2' : (2 - 2 * σ) * Wσ σ c < δ ^ 2 := by
    rw [lt_div_iff₀ h2σ] at hc2; linarith
  have hsq : Real.sqrt ((2 - 2 * σ) * Wσ σ c) < δ := by
    rw [show δ = Real.sqrt (δ ^ 2) from (Real.sqrt_sq hδ0.le).symm]
    exact Real.sqrt_lt_sqrt (mul_nonneg h2σ.le hW0) hc2'
  have hsqd : Real.sqrt ((2 - 2 * σ) * Wσ σ c) / (1 - s.re) < A / 4 := by
    rw [div_lt_iff₀ h1s]
    have : δ = A / 4 * (1 - s.re) := by rw [hδ]; ring
    linarith
  linarith

/-- `inf_N D_N(σ) = 0` dá `D_N(σ) < ε` para algum `N`. -/
theorem pequeno_of_iInf {σ : ℝ} (hD : ⨅ N, DNσ σ N = 0) : ∀ ε > 0, ∃ N, DNσ σ N < ε := by
  intro ε hε
  exact exists_lt_of_ciInf_lt (by rw [hD]; exact hε)

/-- **`inf_N D_N(σ) = 0` ⟹ `ζ ≠ 0` em `Re s > σ`** (`0 < σ < 1`). -/
theorem semZeros_of_DNσ {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hD : ⨅ N, DNσ σ N = 0) : SemZeros σ := by
  intro s hs
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · exact zeta_ne_zero_of_DNσ hσ0 hσ1 (pequeno_of_iInf hD) hs h1

/-- `inf_N D_N(σ) = 0` ⟹ `ψ(x) = x + O(x^{σ+ε})` (`½ ≤ σ < 1`). -/
theorem psi_of_DNσ {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (hD : ⨅ N, DNσ σ N = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |Chebyshev.psi N - N| ≤ C * ((N : ℝ) + 1) ^ (σ + ε) :=
  (semZeros_iff_psi hσ hσ1).mp (semZeros_of_DNσ (by linarith) hσ1 hD)

/-- `inf_N D_N(σ) = 0` ⟹ `M(x) = O(x^{σ+ε})` (`½ ≤ σ < 1`). -/
theorem mertens_of_DNσ {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (hD : ⨅ N, DNσ σ N = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ,
      |ATK.ZeroClasses.Mertens.M N| ≤ C * ((N : ℝ) + 1) ^ (σ + ε) :=
  (semZeros_iff_mertens hσ hσ1).mp (semZeros_of_DNσ (by linarith) hσ1 hD)

/-- **Piso incondicional**: para `0 < σ < ½`, `inf_N D_N(σ) > 0` (há zeros em `Re s = ½`, Hardy). -/
theorem piso_DNσ {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ < 1 / 2) : 0 < ⨅ N, DNσ σ N := by
  have hge : 0 ≤ ⨅ N, DNσ σ N := Real.iInf_nonneg fun N => DNσ_nonneg σ N
  rcases hge.lt_or_eq with h | h
  · exact h
  · exfalso
    obtain ⟨γ, -, hγ⟩ := ATK.ZeroClasses.Hardy.existe_zero_acima 0
    have hZ := semZeros_of_DNσ hσ0 (by linarith) h.symm
    exact hZ _ (by rw [ATK.ZeroClasses.Omega.re_zero_reta]; exact hσ) hγ

/-- Com `σ = ½`: `inf_N D_N = 0` ⟹ RH (a ponte B1 de novo, agora como caso do ponderado). -/
theorem rh_of_DN_iInf (hD : ⨅ N, DN N = 0) : RiemannHypothesis := by
  have hD' : ⨅ N, DNσ (1 / 2) N = 0 := by simp only [DNσ_meio]; exact hD
  exact ATK.ZeroClasses.QuasiRH.semZeros_meio_iff.mp (semZeros_of_DNσ (by norm_num) (by norm_num) hD')

end ATK.ZeroClasses.BDPonderado

#print axioms ATK.ZeroClasses.BDPonderado.Wσ_nonneg
#print axioms ATK.ZeroClasses.BDPonderado.DNσ_nonneg
#print axioms ATK.ZeroClasses.BDPonderado.DNσ_meio
#print axioms ATK.ZeroClasses.BDPonderado.measurable_res
#print axioms ATK.ZeroClasses.BDPonderado.abs_res_le
#print axioms ATK.ZeroClasses.BDPonderado.res_sq_w_gt_one
#print axioms ATK.ZeroClasses.BDPonderado.integrable_w
#print axioms ATK.ZeroClasses.BDPonderado.tail_sq_le
#print axioms ATK.ZeroClasses.BDPonderado.head_le
#print axioms ATK.ZeroClasses.BDPonderado.key_ineq
#print axioms ATK.ZeroClasses.BDPonderado.zeta_ne_zero_of_DNσ
#print axioms ATK.ZeroClasses.BDPonderado.pequeno_of_iInf
#print axioms ATK.ZeroClasses.BDPonderado.semZeros_of_DNσ
#print axioms ATK.ZeroClasses.BDPonderado.psi_of_DNσ
#print axioms ATK.ZeroClasses.BDPonderado.mertens_of_DNσ
#print axioms ATK.ZeroClasses.BDPonderado.piso_DNσ
#print axioms ATK.ZeroClasses.BDPonderado.rh_of_DN_iInf
