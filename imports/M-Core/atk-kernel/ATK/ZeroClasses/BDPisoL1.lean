import ATK.ZeroClasses.BDTheta

/-!
# Pisos `ℓ¹` para Báez-Duarte ponderado: `κ_A(σ) ≤ 2A(σ − Θ)/Θ` (rodada 79)

A questão Q2(iii) de `fronteira/RH_frontier.md` pede o piso `κ(σ) ≤ 2(σ − Θ)` para a taxa de `D_N(σ)` sobre
**todos** os coeficientes. Aqui ela fica resolvida na classe restrita `‖c‖₁ ≤ N^A`, por um argumento elementar.

Se `ζ(ρ) = 0` com `0 < β = Re ρ < σ < 1`, a transformada de Mellin do resíduo vale `1/ρ` em `ρ` (ponte B1). Partimos
`∫_0^∞ |res| t^{β−1}` em três pedaços:
* em `(0, ε]`, `|res| ≤ 1 + ‖c‖₁` (`head0_le`);
* em `(ε, 1]`, AM-GM contra `‖res‖²_σ` (`mid_le`, `J_le`);
* em `(1, ∞)`, a cauda `−S/t` (rodada 59).

Escolhendo `ε^β ≍ 1/(1 + ‖c‖₁)` sai o piso (`piso_L1`):

  **`‖res‖²_σ ≥ C_ρ (1 + ‖c‖₁)^{−2(σ−β)/β}`**.

Consequências:
* `DNσL σ L N` é `D_N(σ)` restrito a `‖c‖₁ ≤ L`. `TaxaL σ A κ` é a taxa `N^{−κ}` nessa classe com `L = N^A`.
* `taxaL_le_zero`: `κ ≤ 2A(σ − β)/β` para cada zero `ρ`.
* `taxaL_Teta`: `Θ (κ + 2A) ≤ 2Aσ`, isto é, `κ ≤ 2A(σ − Θ)/Θ`.
* `taxaL_mol`: o molificador de Riesz tem `‖c‖₁ ≤ N`, logo `TaxaL σ 1 (2(σ − Θ))`.

Na classe `A = 1`, portanto, `2(σ − Θ) ≤ κ₁(σ) ≤ 2(σ − Θ)/Θ` (`taxaL_sanduiche`). Sob RH, `2σ − 1 ≤ κ₁(σ) ≤ 4σ − 2`.

Classificação (rodada 79): **parcial** (Q2(iii) na classe `‖c‖₁ ≤ N^A`; o caso de `c` arbitrário segue OPEN_MATH).
RH continua OPEN_MATH.
-/

open Complex Set MeasureTheory Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.BDPisoL1

open ATK.BaezDuarteBridge (res tailS mellin_res norm_mellin_le amgm integral_tail_weighted)
open ATK.ZeroClasses.BDPonderado (Wσ DNσ Wσ_nonneg integrable_w tail_sq_le abs_res_le measurable_res)
open ATK.ZeroClasses.QuasiRH (SemZeros)
open ATK.ZeroClasses.BDTheta (Teta meio_le_Teta Teta_le_um semZeros_Teta re_le_Teta existe_zero)

/-! ## 1. O piso `ℓ¹` -/

/-- Em `(0, ε]`: `∫ t^{β−1}|res| ≤ (1 + ‖c‖₁) ε^β/β`. -/
theorem head0_le {N : ℕ} (c : Fin N → ℝ) {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) :
    ∫ t in Ioc (0 : ℝ) ε, t ^ (β - 1) * |res c t| ≤ (1 + ∑ k : Fin N, |c k|) * (ε ^ β / β) := by
  set L : ℝ := 1 + ∑ k : Fin N, |c k| with hL
  have hpow : IntegrableOn (fun t : ℝ => t ^ (β - 1)) (Ioc 0 ε) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hε.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  have hval : ∫ t in Ioc (0 : ℝ) ε, t ^ (β - 1) = ε ^ β / β := by
    rw [← intervalIntegral.integral_of_le hε.le, integral_rpow (Or.inl (by linarith))]
    rw [show β - 1 + 1 = β by ring, Real.zero_rpow hβ.ne', sub_zero]
  have hpt : ∀ t ∈ Ioc (0 : ℝ) ε, t ^ (β - 1) * |res c t| ≤ L * t ^ (β - 1) := by
    intro t ht
    rw [mul_comm L]
    exact mul_le_mul_of_nonneg_left (abs_res_le c t) (Real.rpow_nonneg ht.1.le _)
  have hint : IntegrableOn (fun t => t ^ (β - 1) * |res c t|) (Ioc 0 ε) := by
    refine Integrable.mono' (hpow.const_mul L) ?_ ?_
    · exact ((measurable_id.pow_const _).mul (continuous_abs.measurable.comp (measurable_res c))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (abs_nonneg _))]
      exact hpt t ht
  calc ∫ t in Ioc (0 : ℝ) ε, t ^ (β - 1) * |res c t| ≤ ∫ t in Ioc (0 : ℝ) ε, L * t ^ (β - 1) :=
        setIntegral_mono_on hint (hpow.const_mul L) measurableSet_Ioc hpt
    _ = L * (ε ^ β / β) := by rw [integral_const_mul, hval]

/-- Em `(ε, 1]`: `∫ t^{β−1}|res| ≤ (λ‖res‖²_σ + J/λ)/2`, `J = ∫_ε^1 t^{2(β−σ)−1}`. -/
theorem mid_le {N : ℕ} (c : Fin N → ℝ) {σ β ε : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {l : ℝ} (hl : 0 < l) (hint : IntegrableOn (fun t => t ^ (β - 1) * |res c t|) (Ioc ε 1)) :
    ∫ t in Ioc ε 1, t ^ (β - 1) * |res c t| ≤
      (l * Wσ σ c + (∫ t in Ioc ε 1, t ^ (2 * (β - σ) - 1)) / l) / 2 := by
  have hr2 : IntegrableOn (fun t => res c t ^ 2 * t ^ (2 * σ - 1)) (Ioc ε 1) :=
    (integrable_w c hσ0 hσ1).mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hε.le))
  have hpow : IntegrableOn (fun t : ℝ => t ^ (2 * (β - σ) - 1)) (Ioc ε 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hε1).mp
      (intervalIntegral.intervalIntegrable_rpow (Or.inr (notMem_uIcc_of_lt hε zero_lt_one)))
  have hg : IntegrableOn (fun t => (l * (res c t ^ 2 * t ^ (2 * σ - 1)) + t ^ (2 * (β - σ) - 1) / l) / 2)
      (Ioc ε 1) :=
    Integrable.div_const (Integrable.add (Integrable.const_mul hr2 l) (Integrable.div_const hpow l)) 2
  have hle : ∫ t in Ioc ε 1, t ^ (β - 1) * |res c t| ≤
      ∫ t in Ioc ε 1, (l * (res c t ^ 2 * t ^ (2 * σ - 1)) + t ^ (2 * (β - σ) - 1) / l) / 2 := by
    refine setIntegral_mono_on hint hg measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := lt_of_lt_of_le hε ht.1.le
    have ha : (|res c t| * t ^ (σ - 1 / 2)) ^ 2 = res c t ^ 2 * t ^ (2 * σ - 1) := by
      rw [mul_pow, sq_abs]
      congr 1
      rw [← Real.rpow_natCast (t ^ (σ - 1 / 2)) 2, ← Real.rpow_mul ht0.le]
      congr 1
      push_cast
      ring
    have hb : (t ^ (β - σ - 1 / 2)) ^ 2 = t ^ (2 * (β - σ) - 1) := by
      rw [← Real.rpow_natCast (t ^ (β - σ - 1 / 2)) 2, ← Real.rpow_mul ht0.le]
      congr 1
      push_cast
      ring
    have hab : t ^ (β - σ - 1 / 2) * (|res c t| * t ^ (σ - 1 / 2)) = t ^ (β - 1) * |res c t| := by
      rw [mul_left_comm, ← Real.rpow_add ht0]
      ring_nf
    have := amgm (a := |res c t| * t ^ (σ - 1 / 2)) (b := t ^ (β - σ - 1 / 2)) hl
    rw [ha, hb, hab] at this
    exact this
  have hval : ∫ t in Ioc ε 1, (l * (res c t ^ 2 * t ^ (2 * σ - 1)) + t ^ (2 * (β - σ) - 1) / l) / 2 =
      (l * ∫ t in Ioc ε 1, res c t ^ 2 * t ^ (2 * σ - 1)) / 2 +
        (∫ t in Ioc ε 1, t ^ (2 * (β - σ) - 1)) / l / 2 := by
    rw [integral_div, integral_add (Integrable.const_mul hr2 l) (Integrable.div_const hpow l),
      integral_const_mul, integral_div]
    ring
  have hR : ∫ t in Ioc ε 1, res c t ^ 2 * t ^ (2 * σ - 1) ≤ Wσ σ c := by
    unfold Wσ
    exact setIntegral_mono_set (integrable_w c hσ0 hσ1)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht =>
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt ht) _)))
      (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hε.le)).eventuallyLE
  calc ∫ t in Ioc ε 1, t ^ (β - 1) * |res c t| ≤ _ := hle
    _ = _ := hval
    _ ≤ (l * Wσ σ c) / 2 + (∫ t in Ioc ε 1, t ^ (2 * (β - σ) - 1)) / l / 2 := by
        have := mul_le_mul_of_nonneg_left hR hl.le
        linarith
    _ = _ := by ring

/-- `J = ∫_ε^1 t^{2(β−σ)−1} dt ≤ ε^{2(β−σ)}/(2(σ − β))` para `β < σ`. -/
theorem J_le {β σ ε : ℝ} (hβσ : β < σ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ t in Ioc ε 1, t ^ (2 * (β - σ) - 1) ≤ ε ^ (2 * (β - σ)) / (2 * (σ - β)) := by
  have hr : 2 * (β - σ) - 1 ≠ -1 := by intro h; linarith
  rw [← intervalIntegral.integral_of_le hε1,
    integral_rpow (Or.inr ⟨hr, notMem_uIcc_of_lt hε zero_lt_one⟩)]
  rw [show 2 * (β - σ) - 1 + 1 = 2 * (β - σ) by ring, Real.one_rpow]
  have h1 : (2 * (β - σ)) ≠ 0 := by intro h; linarith
  have h2 : (2 * (σ - β)) ≠ 0 := by intro h; linarith
  have e : (1 - ε ^ (2 * (β - σ))) / (2 * (β - σ)) = (ε ^ (2 * (β - σ)) - 1) / (2 * (σ - β)) := by
    rw [div_eq_div_iff h1 h2]
    ring
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- **A desigualdade-chave `ℓ¹`**: se `ζ(s) = 0` com `0 < Re s < σ < 1`, então para `0 < ε ≤ 1` e `λ > 0`,
`1/|s| ≤ (1 + ‖c‖₁) ε^β/β + (λW + ε^{2(β−σ)}/(2(σ−β))/λ)/2 + √((2 − 2σ)W)/(1 − β)`. -/
theorem key_L1 {N : ℕ} (c : Fin N → ℝ) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {s : ℂ} (hs0 : 0 < s.re)
    (hsσ : s.re < σ) (hz : riemannZeta s = 0) {ε l : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hl : 0 < l) :
    1 / ‖s‖ ≤ (1 + ∑ k : Fin N, |c k|) * (ε ^ s.re / s.re) +
      (l * Wσ σ c + ε ^ (2 * (s.re - σ)) / (2 * (σ - s.re)) / l) / 2 +
      Real.sqrt ((2 - 2 * σ) * Wσ σ c) / (1 - s.re) := by
  have hs1 : s.re < 1 := by linarith
  obtain ⟨hconv, hval⟩ := mellin_res c hs0 hs1 hz
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
  have hsplit2 : ∫ t in Ioc (0 : ℝ) 1, t ^ (s.re - 1) * |res c t| =
      (∫ t in Ioc (0 : ℝ) ε, t ^ (s.re - 1) * |res c t|) +
        ∫ t in Ioc ε 1, t ^ (s.re - 1) * |res c t| := by
    have hdisj : Disjoint (Ioc (0 : ℝ) ε) (Ioc ε 1) :=
      Set.disjoint_left.mpr fun x hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)
    have h01 : Ioc (0 : ℝ) ε ⊆ Ioi 0 := Ioc_subset_Ioi_self
    have h02 : Ioc ε 1 ⊆ Ioi 0 := Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hε.le)
    have hu := setIntegral_union hdisj measurableSet_Ioc (hw.mono_set h01) (hw.mono_set h02)
    rw [Ioc_union_Ioc_eq_Ioc hε.le hε1] at hu
    exact hu
  have hhead := head0_le c hs0 hε
  have hmid := mid_le c hσ0 hσ1 hε hε1 hl
    (hw.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi hε.le)))
  have hJ := J_le hsσ hε hε1
  have hmid' : ∫ t in Ioc ε 1, t ^ (s.re - 1) * |res c t| ≤
      (l * Wσ σ c + ε ^ (2 * (s.re - σ)) / (2 * (σ - s.re)) / l) / 2 := by
    refine hmid.trans ?_
    have := div_le_div_of_nonneg_right hJ hl.le
    linarith
  have htail := integral_tail_weighted c hs1
  have hS : |tailS c| ≤ Real.sqrt ((2 - 2 * σ) * Wσ σ c) := Real.abs_le_sqrt (tail_sq_le c hσ0 hσ1)
  have h1σ : 0 < 1 - s.re := by linarith
  have hS' : |tailS c| / (1 - s.re) ≤ Real.sqrt ((2 - 2 * σ) * Wσ σ c) / (1 - s.re) :=
    div_le_div_of_nonneg_right hS h1σ.le
  calc 1 / ‖s‖ ≤ ∫ t in Ioi (0 : ℝ), t ^ (s.re - 1) * |res c t| := hnorm
    _ = _ := by rw [hsplit, hsplit2]
    _ ≤ _ := by
        rw [htail]
        linarith

/-- **O piso `ℓ¹`**: se `ζ(ρ) = 0` com `0 < β = Re ρ < σ < 1`, há `C > 0` com
`‖res‖²_σ ≥ C (1 + ‖c‖₁)^{−2(σ−β)/β}` para todo `N` e todo `c`. -/
theorem piso_L1 {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {s : ℂ} (hs0 : 0 < s.re) (hsσ : s.re < σ)
    (hz : riemannZeta s = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ} (c : Fin N → ℝ),
      C * (1 + ∑ k : Fin N, |c k|) ^ (-(2 * (σ - s.re) / s.re)) ≤ Wσ σ c := by
  have hsne : s ≠ 0 := fun h => by rw [h, zero_re] at hs0; exact lt_irrefl 0 hs0
  have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hsne
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = s.re := ⟨_, rfl⟩
  rw [← hβ] at hs0 hsσ ⊢
  have hβ1 : β < 1 := by linarith
  set r : ℝ := 1 / (2 * ‖s‖) with hr
  have hr0 : 0 < r := by positivity
  set a : ℝ := 2 * (σ - β) / β with ha
  have ha0 : 0 ≤ a := by rw [ha]; exact div_nonneg (by linarith) hs0.le
  set m0 : ℝ := min 1 (r * β) with hm0
  have hm00 : 0 < m0 := lt_min one_pos (mul_pos hr0 hs0)
  have h2σ : 0 < 2 - 2 * σ := by linarith
  set C₀ : ℝ := min (3 * r ^ 2 * (σ - β) / 4) ((3 * r * (1 - β) / 8) ^ 2 / (2 - 2 * σ)) with hC₀
  have hσβ' : 0 < σ - β := by linarith
  have h1β' : 0 < 1 - β := by linarith
  have hC₀0 : 0 < C₀ := lt_min (by positivity) (div_pos (by positivity) h2σ)
  refine ⟨C₀ * m0 ^ a, mul_pos hC₀0 (Real.rpow_pos_of_pos hm00 a), fun {N} c => ?_⟩
  set L : ℝ := 1 + ∑ k : Fin N, |c k| with hL
  have hL1 : 1 ≤ L := by
    have : 0 ≤ ∑ k : Fin N, |c k| := Finset.sum_nonneg fun k _ => abs_nonneg _
    linarith
  have hL0 : 0 < L := by linarith
  set W : ℝ := Wσ σ c with hW
  have hW0 : 0 ≤ W := Wσ_nonneg σ c
  set m : ℝ := min 1 (r * β / L) with hm
  have hm0' : 0 < m := lt_min one_pos (by positivity)
  have hm1 : m ≤ 1 := min_le_left _ _
  set ε : ℝ := m ^ β⁻¹ with hε
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hm0' _
  have hε1 : ε ≤ 1 := Real.rpow_le_one hm0'.le hm1 (inv_nonneg.mpr hs0.le)
  have hεβ : ε ^ β = m := Real.rpow_inv_rpow hm0'.le hs0.ne'
  set J₁ : ℝ := ε ^ (2 * (β - σ)) / (2 * (σ - β)) with hJ₁
  have hσβ : 0 < σ - β := by linarith
  have hJ0 : 0 < J₁ := div_pos (Real.rpow_pos_of_pos hε0 _) (by linarith)
  set l : ℝ := 2 * J₁ / r with hl
  have hl0 : 0 < l := by positivity
  have hkey := key_L1 c hσ0 hσ1 (s := s) (by rw [← hβ]; exact hs0) (by rw [← hβ]; exact hsσ) hz hε0 hε1 hl0
  rw [← hβ, ← hJ₁, ← hW, ← hL] at hkey
  -- os três termos
  have hhead : L * (ε ^ β / β) ≤ r := by
    rw [hεβ]
    have : m ≤ r * β / L := min_le_right _ _
    rw [mul_div_assoc', div_le_iff₀ hs0]
    rw [le_div_iff₀ hL0] at this
    linarith
  have hJl : J₁ / l = r / 2 := by
    rw [hl]
    field_simp
  have hlW : l * W / 2 = J₁ / r * W := by
    rw [hl]
    field_simp
  have h2r : 1 / ‖s‖ = 2 * r := by
    rw [hr]
    field_simp
  set Q : ℝ := Real.sqrt ((2 - 2 * σ) * W) / (1 - β) with hQ
  have hmain : 3 * r / 4 ≤ J₁ / r * W + Q := by
    have e : (l * W + J₁ / l) / 2 = J₁ / r * W + r / 4 := by
      rw [hJl, add_div, hlW]
      ring
    rw [e, h2r] at hkey
    linarith
  -- `ε^{2(σ−β)}` e `1/J₁`
  have hpow1 : ε ^ (2 * (β - σ)) * ε ^ (2 * (σ - β)) = 1 := by
    rw [← Real.rpow_add hε0, show 2 * (β - σ) + 2 * (σ - β) = 0 by ring, Real.rpow_zero]
  have hE1 : ε ^ (2 * (σ - β)) ≤ 1 := Real.rpow_le_one hε0.le hε1 (by linarith)
  have hE0 : 0 ≤ ε ^ (2 * (σ - β)) := (Real.rpow_pos_of_pos hε0 _).le
  have hWge : C₀ * ε ^ (2 * (σ - β)) ≤ W := by
    rcases le_or_gt (3 * r / 8) (J₁ / r * W) with hA | hA
    · -- caso A: `W ≥ 3r²/(8J₁) = (3r²(σ−β)/4) ε^{2(σ−β)}`
      have hW1 : 3 * r ^ 2 / (8 * J₁) ≤ W := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_mul_eq_mul_div, le_div_iff₀ hr0] at hA
        nlinarith
      have e : 3 * r ^ 2 / (8 * J₁) = 3 * r ^ 2 * (σ - β) / 4 * ε ^ (2 * (σ - β)) := by
        have hinv : (ε ^ (2 * (β - σ)))⁻¹ = ε ^ (2 * (σ - β)) := by
          rw [← Real.rpow_neg hε0.le]
          congr 1
          ring
        have hp : ε ^ (2 * (β - σ)) ≠ 0 := (Real.rpow_pos_of_pos hε0 _).ne'
        rw [hJ₁, ← hinv]
        field_simp
        ring
      calc C₀ * ε ^ (2 * (σ - β)) ≤ 3 * r ^ 2 * (σ - β) / 4 * ε ^ (2 * (σ - β)) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hE0
        _ = _ := e.symm
        _ ≤ W := hW1
    · -- caso B: `√((2 − 2σ)W) ≥ 3r(1 − β)/8`
      have hQ' : 3 * r / 8 ≤ Q := by linarith
      have h1β : 0 < 1 - β := by linarith
      rw [hQ, le_div_iff₀ h1β] at hQ'
      have hsq : (3 * r / 8 * (1 - β)) ^ 2 ≤ (2 - 2 * σ) * W := by
        have h0 : 0 ≤ 3 * r / 8 * (1 - β) := by positivity
        calc (3 * r / 8 * (1 - β)) ^ 2 ≤ Real.sqrt ((2 - 2 * σ) * W) ^ 2 := pow_le_pow_left₀ h0 hQ' 2
          _ = (2 - 2 * σ) * W := Real.sq_sqrt (mul_nonneg h2σ.le hW0)
      have hW1 : (3 * r * (1 - β) / 8) ^ 2 / (2 - 2 * σ) ≤ W := by
        rw [div_le_iff₀ h2σ]
        have e : (3 * r * (1 - β) / 8) = 3 * r / 8 * (1 - β) := by ring
        rw [e]
        linarith
      calc C₀ * ε ^ (2 * (σ - β)) ≤ C₀ := by
            have := mul_le_mul_of_nonneg_left hE1 hC₀0.le
            linarith
        _ ≤ _ := min_le_right _ _
        _ ≤ W := hW1
  -- `ε^{2(σ−β)} = m^a ≥ m0^a L^{−a}`
  have hεa : ε ^ (2 * (σ - β)) = m ^ a := by
    rw [hε, ← Real.rpow_mul hm0'.le, ha]
    congr 1
    field_simp
  have hmm : m0 / L ≤ m := by
    apply le_min
    · rw [div_le_one hL0]
      exact (min_le_left _ _).trans hL1
    · exact div_le_div_of_nonneg_right (min_le_right _ _) hL0.le
  have hma : m0 ^ a * L ^ (-a) ≤ m ^ a := by
    rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv, ← Real.div_rpow hm00.le hL0.le]
    exact Real.rpow_le_rpow (div_nonneg hm00.le hL0.le) hmm ha0
  calc C₀ * m0 ^ a * L ^ (-a) = C₀ * (m0 ^ a * L ^ (-a)) := by ring
    _ ≤ C₀ * m ^ a := mul_le_mul_of_nonneg_left hma hC₀0.le
    _ = C₀ * ε ^ (2 * (σ - β)) := by rw [hεa]
    _ ≤ W := hWge

/-! ## 2. O molificador de Riesz tem `‖c‖₁ ≤ N` -/

open ATK.ZeroClasses.BDEspectral (aN cN espectroσ Wσ_espectral soma_cN wR wR_nonneg)
open ATK.ZeroClasses.BDDesloc (molif_cota)
open ATK.ZeroClasses.BDTaxa (norm_zeta_linha)
open ATK.RHLogZeta (F F_eq)

theorem wR_le_one {u : ℝ} (hu : 0 ≤ u) : wR u ≤ 1 := by
  unfold wR
  have h0 : 0 ≤ max (1 - u) 0 := le_max_right _ _
  have h1 : max (1 - u) 0 ≤ 1 := max_le (by linarith) zero_le_one
  nlinarith

/-- **`‖c‖₁ ≤ N`** para os coeficientes do molificador de Riesz. -/
theorem norm_cN_le (N : ℕ) : ∑ k : Fin N, |cN N k| ≤ N := by
  have hk : ∀ k : Fin N, |cN N k| ≤ 1 := by
    intro k
    unfold cN
    rw [abs_mul, abs_neg, abs_of_nonneg (wR_nonneg _)]
    have h1 : |((ArithmeticFunction.moebius (k.val + 1) : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have h2 : wR (((k.val + 1 : ℕ) : ℝ) / N) ≤ 1 := wR_le_one (by positivity)
    calc |((ArithmeticFunction.moebius (k.val + 1) : ℤ) : ℝ)| * wR (((k.val + 1 : ℕ) : ℝ) / N)
        ≤ 1 * 1 := mul_le_mul h1 h2 (wR_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  calc ∑ k : Fin N, |cN N k| ≤ ∑ _k : Fin N, (1 : ℝ) := Finset.sum_le_sum fun k _ => hk k
    _ = N := by simp

/-- `‖res‖²_σ` do molificador: `(1/2π) ∫ |1 − ζ(s)A_N(s)|²/|s|² dτ`. -/
theorem Wσ_molif {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {N : ℕ} (hN : 1 ≤ N) :
    Wσ σ (cN N) = (2 * π)⁻¹ * ∫ τ : ℝ, ‖(1 - riemannZeta ((σ : ℂ) + (τ : ℂ) * I) *
      LSeries (aN N) ((σ : ℂ) + (τ : ℂ) * I)) / ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2 := by
  rw [Wσ_espectral hσ0 hσ1 (cN N)]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  simp only [espectroσ]
  rw [soma_cN hN]
  ring_nf

/-- **O molificador sob `SemZeros θ`**: `‖res_{c_N}‖²_σ ≤ K N^{−2δ}` para `θ + δ < σ < 1` (a prova de
`BDTaxa.DNσ_taxa`, rodada 75, para o vetor `c_N` em vez do ínfimo). -/
theorem Wσ_taxa {θ σ δ : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (hσ1 : σ < 1)
    (hδ0 : 0 < δ) (hδ : θ + δ < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → Wσ σ (cN N) ≤ K * (N : ℝ) ^ (-(2 * δ)) := by
  have hσ0 : 0 < σ := by linarith
  have hδ1 : δ < 1 := by linarith
  obtain ⟨K₁, hK₁0, hK₁⟩ := molif_cota hZ hθ hθ1 hδ0 hδ1 hδ hσ1 (η := 1 / 8) (by norm_num) (by norm_num)
  obtain ⟨C, hC0, hC⟩ := norm_zeta_linha hZ hθ hθ1 (by linarith) hσ1 (η := 1 / 8) (by norm_num)
  have hI : Integrable (fun τ : ℝ => (1 + ‖τ‖) ^ (-(3 / 2 : ℝ))) := integrable_one_add_norm (by simp; norm_num)
  set I₀ : ℝ := ∫ τ : ℝ, (1 + ‖τ‖) ^ (-(3 / 2 : ℝ)) with hI₀
  have hI0 : 0 ≤ I₀ := integral_nonneg fun τ => by positivity
  set B : ℝ := (2 * C * K₁ / σ) ^ 2 with hB
  refine ⟨(2 * π)⁻¹ * (B * I₀), by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Wσ_molif hσ0 hσ1 hN]
  -- a cota pontual
  have hpt : ∀ τ : ℝ, ‖(1 - riemannZeta ((σ : ℂ) + (τ : ℂ) * I) * LSeries (aN N) ((σ : ℂ) + (τ : ℂ) * I)) /
      ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤ (B * (N : ℝ) ^ (-(2 * δ))) * (1 + ‖τ‖) ^ (-(3 / 2 : ℝ)) := by
    intro τ
    set s : ℂ := (σ : ℂ) + (τ : ℂ) * I with hsdef
    have hsre : s.re = σ := by simp [hsdef]
    have hsim : s.im = τ := by simp [hsdef]
    have hs1 : s ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      rw [hsre, one_re] at this
      linarith
    have hζ : riemannZeta s ≠ 0 := hZ s (by rw [hsre]; linarith)
    have hζF : riemannZeta s * F s = 1 := by rw [F_eq hs1, mul_inv_cancel₀ hζ]
    have e1 : 1 - riemannZeta s * LSeries (aN N) s = -(riemannZeta s * (LSeries (aN N) s - F s)) := by
      linear_combination -hζF
    have hy : (0 : ℝ) < 1 + |τ| := by positivity
    have hs : σ * (1 + |τ|) / 2 ≤ ‖s‖ := by
      have a1 := abs_re_le_norm s
      have a2 := abs_im_le_norm s
      rw [hsre, abs_of_pos hσ0] at a1
      rw [hsim] at a2
      nlinarith [abs_nonneg τ]
    have hnum : ‖1 - riemannZeta s * LSeries (aN N) s‖ ≤
        C * K₁ * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ (1 / 4 : ℝ) := by
      rw [e1, norm_neg, norm_mul]
      have h1 := hC τ
      have h2 := hK₁ N hN τ
      have hp : (1 + |τ|) ^ (1 / 8 : ℝ) * (1 + |τ|) ^ (1 / 8 : ℝ) = (1 + |τ|) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_add hy]
        norm_num
      calc ‖riemannZeta s‖ * ‖LSeries (aN N) s - F s‖
          ≤ (C * (1 + |τ|) ^ (1 / 8 : ℝ)) * (K₁ * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ (1 / 8 : ℝ)) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = C * K₁ * (N : ℝ) ^ (-δ) * ((1 + |τ|) ^ (1 / 8 : ℝ) * (1 + |τ|) ^ (1 / 8 : ℝ)) := by ring
        _ = C * K₁ * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ (1 / 4 : ℝ) := by rw [hp]
    have hq : ‖(1 - riemannZeta s * LSeries (aN N) s) / s‖ ≤
        2 * C * K₁ / σ * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ (-(3 / 4 : ℝ)) := by
      rw [norm_div]
      have hsp : 0 < σ * (1 + |τ|) / 2 := by positivity
      have hp : (1 + |τ|) ^ (1 / 4 : ℝ) / (σ * (1 + |τ|) / 2) = 2 / σ * (1 + |τ|) ^ (-(3 / 4 : ℝ)) := by
        have e : (1 + |τ|) ^ (-(3 / 4 : ℝ)) = (1 + |τ|) ^ (1 / 4 : ℝ) * (1 + |τ|) ^ (-1 : ℝ) := by
          rw [← Real.rpow_add hy]
          norm_num
        rw [e, Real.rpow_neg_one]
        field_simp
      calc ‖1 - riemannZeta s * LSeries (aN N) s‖ / ‖s‖
          ≤ C * K₁ * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ (1 / 4 : ℝ) / (σ * (1 + |τ|) / 2) :=
            div_le_div₀ (by positivity) hnum hsp hs
        _ = C * K₁ * (N : ℝ) ^ (-δ) * ((1 + |τ|) ^ (1 / 4 : ℝ) / (σ * (1 + |τ|) / 2)) := by ring
        _ = 2 * C * K₁ / σ * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ (-(3 / 4 : ℝ)) := by rw [hp]; ring
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hq 2
    have hN2 : ((N : ℝ) ^ (-δ)) ^ 2 = (N : ℝ) ^ (-(2 * δ)) := by
      rw [← Real.rpow_mul_natCast hN0.le]
      congr 1
      push_cast
      ring
    have hy2 : ((1 + |τ|) ^ (-(3 / 4 : ℝ))) ^ 2 = (1 + ‖τ‖) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.norm_eq_abs, ← Real.rpow_mul_natCast hy.le]
      congr 1
      push_cast
      ring
    calc ‖(1 - riemannZeta s * LSeries (aN N) s) / s‖ ^ 2
        ≤ (2 * C * K₁ / σ * (N : ℝ) ^ (-δ) * (1 + |τ|) ^ (-(3 / 4 : ℝ))) ^ 2 := hsq
      _ = (2 * C * K₁ / σ) ^ 2 * ((N : ℝ) ^ (-δ)) ^ 2 * ((1 + |τ|) ^ (-(3 / 4 : ℝ))) ^ 2 := by ring
      _ = (B * (N : ℝ) ^ (-(2 * δ))) * (1 + ‖τ‖) ^ (-(3 / 2 : ℝ)) := by rw [hN2, hy2, hB]
  have hint : ∫ τ : ℝ, ‖(1 - riemannZeta ((σ : ℂ) + (τ : ℂ) * I) * LSeries (aN N) ((σ : ℂ) + (τ : ℂ) * I)) /
      ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤ (B * (N : ℝ) ^ (-(2 * δ))) * I₀ := by
    rw [hI₀, ← integral_const_mul]
    exact integral_mono_of_nonneg (ae_of_all _ fun τ => by positivity) (hI.const_mul _) (ae_of_all _ hpt)
  calc (2 * π)⁻¹ * ∫ τ : ℝ, ‖(1 - riemannZeta ((σ : ℂ) + (τ : ℂ) * I) *
        LSeries (aN N) ((σ : ℂ) + (τ : ℂ) * I)) / ((σ : ℂ) + (τ : ℂ) * I)‖ ^ 2
      ≤ (2 * π)⁻¹ * ((B * (N : ℝ) ^ (-(2 * δ))) * I₀) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = (2 * π)⁻¹ * (B * I₀) * (N : ℝ) ^ (-(2 * δ)) := by ring

/-! ## 3. A classe `‖c‖₁ ≤ L` e a taxa `κ_A(σ)` -/

/-- `D_N(σ)` restrito a `‖c‖₁ ≤ L`. -/
noncomputable def DNσL (σ L : ℝ) (N : ℕ) : ℝ := ⨅ c : {c : Fin N → ℝ // ∑ k, |c k| ≤ L}, Wσ σ c.1

theorem DNσL_le {σ L : ℝ} {N : ℕ} (c : Fin N → ℝ) (hc : ∑ k, |c k| ≤ L) : DNσL σ L N ≤ Wσ σ c := by
  have hb : BddBelow (Set.range fun c : {c : Fin N → ℝ // ∑ k, |c k| ≤ L} => Wσ σ c.1) :=
    ⟨0, fun _ ⟨c', hc'⟩ => hc' ▸ Wσ_nonneg σ c'.1⟩
  exact ciInf_le hb (⟨c, hc⟩ : {c : Fin N → ℝ // ∑ k, |c k| ≤ L})

/-- `D_N(σ) ≤ D_N^{(L)}(σ)`: o ínfimo restrito é maior. -/
theorem DNσ_le_DNσL {σ L : ℝ} (hL : 0 ≤ L) (N : ℕ) : DNσ σ N ≤ DNσL σ L N := by
  have : Nonempty {c : Fin N → ℝ // ∑ k, |c k| ≤ L} := ⟨⟨0, by simpa using hL⟩⟩
  have hb : BddBelow (Set.range fun c : Fin N → ℝ => Wσ σ c) :=
    ⟨0, fun _ ⟨c', hc'⟩ => hc' ▸ Wσ_nonneg σ c'⟩
  exact le_ciInf fun c => ciInf_le hb c.1

/-- **O piso na classe restrita**: para um zero `ρ` com `0 < β = Re ρ < σ < 1`,
`D_N^{(L)}(σ) ≥ C (1 + L)^{−2(σ−β)/β}`. -/
theorem piso_DNσL {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) {s : ℂ} (hs0 : 0 < s.re) (hsσ : s.re < σ)
    (hz : riemannZeta s = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) (N : ℕ), 0 ≤ L →
      C * (1 + L) ^ (-(2 * (σ - s.re) / s.re)) ≤ DNσL σ L N := by
  obtain ⟨C, hC0, hC⟩ := piso_L1 hσ0 hσ1 hs0 hsσ hz
  refine ⟨C, hC0, fun L N hL => ?_⟩
  have : Nonempty {c : Fin N → ℝ // ∑ k, |c k| ≤ L} := ⟨⟨0, by simpa using hL⟩⟩
  refine le_ciInf fun c => le_trans ?_ (hC c.1)
  apply mul_le_mul_of_nonneg_left _ hC0.le
  have h0 : 0 ≤ ∑ k, |c.1 k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have ha : 0 ≤ 2 * (σ - s.re) / s.re := div_nonneg (by linarith) hs0.le
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith [c.2]) (by linarith)

/-- A taxa na classe `‖c‖₁ ≤ N^A`: `D_N^{(N^A)}(σ) ≪ N^{−δ}` para todo `δ < κ`. -/
def TaxaL (σ A κ : ℝ) : Prop :=
  ∀ δ : ℝ, δ < κ → ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N → DNσL σ ((N : ℝ) ^ A) N ≤ K * (N : ℝ) ^ (-δ)

/-- **Um zero limita a taxa**: se `ζ(ρ) = 0`, `0 < β = Re ρ < σ < 1`, então `κ_A(σ) ≤ 2A(σ − β)/β`. -/
theorem taxaL_le_zero {σ A κ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hA : 0 ≤ A) {s : ℂ} (hs0 : 0 < s.re)
    (hsσ : s.re < σ) (hz : riemannZeta s = 0) (hT : TaxaL σ A κ) : κ ≤ A * (2 * (σ - s.re) / s.re) := by
  set a : ℝ := 2 * (σ - s.re) / s.re with ha
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hs0.le
  by_contra h
  push Not at h
  set δ : ℝ := (A * a + κ) / 2 with hδ
  obtain ⟨K, hK⟩ := hT δ (by rw [hδ]; linarith)
  obtain ⟨C, hC0, hC⟩ := piso_DNσL hσ0 hσ1 hs0 hsσ hz
  have hp : 0 < δ - A * a := by rw [hδ]; linarith
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (δ - A * a)) atTop atTop :=
    (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hNbig, hN1⟩ :=
    ((hlim.eventually_gt_atTop (K * (2 : ℝ) ^ a / C)).and (eventually_ge_atTop 1)).exists
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := by linarith
  have hD := hK N hN1
  have hF := hC ((N : ℝ) ^ A) N (Real.rpow_nonneg hN0.le _)
  have hNA : 1 ≤ (N : ℝ) ^ A := Real.one_le_rpow hNr hA
  have h2 : (1 + (N : ℝ) ^ A) ≤ 2 * (N : ℝ) ^ A := by linarith
  have h3 : (2 * (N : ℝ) ^ A) ^ (-a) ≤ (1 + (N : ℝ) ^ A) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) h2 (by linarith)
  have h4 : (2 * (N : ℝ) ^ A) ^ (-a) = (2 : ℝ) ^ (-a) * (N : ℝ) ^ (-(A * a)) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hN0.le _), ← Real.rpow_mul hN0.le]
    congr 2
    ring
  have h5 : (N : ℝ) ^ (-(A * a)) = (N : ℝ) ^ (δ - A * a) * (N : ℝ) ^ (-δ) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  set P : ℝ := (N : ℝ) ^ (δ - A * a) with hP
  have hNd : 0 < (N : ℝ) ^ (-δ) := Real.rpow_pos_of_pos hN0 _
  have h2a : 0 < (2 : ℝ) ^ (-a) := Real.rpow_pos_of_pos (by norm_num) _
  have hchain : C * (2 : ℝ) ^ (-a) * P * (N : ℝ) ^ (-δ) ≤ K * (N : ℝ) ^ (-δ) := by
    calc C * (2 : ℝ) ^ (-a) * P * (N : ℝ) ^ (-δ) = C * (2 * (N : ℝ) ^ A) ^ (-a) := by
          rw [h4, h5]; ring
      _ ≤ C * (1 + (N : ℝ) ^ A) ^ (-a) := mul_le_mul_of_nonneg_left h3 hC0.le
      _ ≤ _ := hF
      _ ≤ _ := hD
  have hPK : C * (2 : ℝ) ^ (-a) * P ≤ K := le_of_mul_le_mul_right hchain hNd
  have h2inv : (2 : ℝ) ^ (-a) = ((2 : ℝ) ^ a)⁻¹ := Real.rpow_neg (by norm_num) a
  have h2p : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  rw [h2inv] at hPK
  have : P ≤ K * (2 : ℝ) ^ a / C := by
    rw [le_div_iff₀ hC0]
    have e : C * ((2 : ℝ) ^ a)⁻¹ * P * (2 : ℝ) ^ a = P * C := by field_simp
    nlinarith
  linarith

/-- **O piso `ℓ¹` em termos de `Θ`**: para `Θ < σ < 1` e `A ≥ 0`, `TaxaL σ A κ ⟹ Θ (κ + 2A) ≤ 2Aσ`,
isto é, `κ_A(σ) ≤ 2A(σ − Θ)/Θ`. -/
theorem taxaL_Teta {σ A κ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) (hA : 0 ≤ A) (hT : TaxaL σ A κ) :
    Teta * (κ + 2 * A) ≤ 2 * A * σ := by
  have hT12 := meio_le_Teta
  have hσ0 : 0 < σ := by linarith
  have hz : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re * (κ + 2 * A) ≤ 2 * A * σ := by
    intro ρ hρ h0
    have hρσ : ρ.re < σ := lt_of_le_of_lt (re_le_Teta hρ) hσ
    have h := taxaL_le_zero hσ0 hσ1 hA h0 hρσ hρ hT
    rw [mul_div_assoc', le_div_iff₀ h0] at h
    nlinarith
  by_contra hc
  push Not at hc
  have hT0 : 0 < Teta := by linarith
  have hk : 0 < κ + 2 * A := by
    by_contra hk
    push Not at hk
    have : Teta * (κ + 2 * A) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hT0.le hk
    nlinarith
  set θ : ℝ := 2 * A * σ / (κ + 2 * A) with hθ
  have hθk : θ * (κ + 2 * A) = 2 * A * σ := by rw [hθ]; field_simp
  have hθT : θ < Teta := by
    by_contra h
    push Not at h
    nlinarith
  obtain ⟨ρ, hρ, hρθ, hρ0⟩ : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ θ < ρ.re ∧ 0 < ρ.re := by
    rcases lt_or_ge θ (1 / 2) with h | h
    · obtain ⟨γ, -, hγ⟩ := ATK.ZeroClasses.Hardy.existe_zero_acima 0
      refine ⟨_, hγ, ?_, ?_⟩ <;> rw [ATK.ZeroClasses.Omega.re_zero_reta] <;> linarith
    · obtain ⟨ρ, hρ, hρθ⟩ := existe_zero h hθT
      exact ⟨ρ, hρ, hρθ, by linarith⟩
  have h1 := hz ρ hρ hρ0
  have h2 := mul_lt_mul_of_pos_right hρθ hk
  linarith

/-- **O molificador está na classe `A = 1`**: `TaxaL σ 1 (2(σ − Θ))` para `Θ < σ < 1`. -/
theorem taxaL_mol {σ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) : TaxaL σ 1 (2 * (σ - Teta)) := by
  intro δ hδ
  have hm0 := le_max_right δ 0
  have hmδ := le_max_left δ 0
  have hmax : max δ 0 < 2 * (σ - Teta) := max_lt hδ (by linarith)
  set δ' : ℝ := (max δ 0 / 2 + (σ - Teta)) / 2 with hδ'
  obtain ⟨K, hK0, hK⟩ := Wσ_taxa semZeros_Teta meio_le_Teta (by linarith) hσ1 (δ := δ')
    (by rw [hδ']; linarith) (by rw [hδ']; linarith)
  refine ⟨K, fun N hN => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hexp : -(2 * δ') ≤ -δ := by
    rcases le_total δ 0 with h | h
    · rw [hδ']; linarith
    · have hm : max δ 0 = δ := max_eq_left h
      rw [hδ', hm]
      linarith
  have hc : ∑ k, |cN N k| ≤ (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]; exact norm_cN_le N
  exact (DNσL_le _ hc).trans ((hK N hN).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 hexp) hK0))

/-- **O sanduíche na classe `‖c‖₁ ≤ N`**: para `Θ < σ < 1`, a taxa `2(σ − Θ)` é atingida e nenhuma taxa passa
de `2(σ − Θ)/Θ`. -/
theorem taxaL_sanduiche {σ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) :
    TaxaL σ 1 (2 * (σ - Teta)) ∧ ∀ κ : ℝ, TaxaL σ 1 κ → κ ≤ 2 * (σ - Teta) / Teta := by
  refine ⟨taxaL_mol hσ hσ1, fun κ hκ => ?_⟩
  have h := taxaL_Teta hσ hσ1 zero_le_one hκ
  have hT0 : 0 < Teta := by linarith [meio_le_Teta]
  rw [le_div_iff₀ hT0]
  linarith

/-- **Sob RH**, na classe `‖c‖₁ ≤ N`: `2σ − 1 ≤ κ₁(σ) ≤ 4σ − 2` para `σ ∈ (½, 1)`. -/
theorem taxaL_RH (hRH : RiemannHypothesis) {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    TaxaL σ 1 (2 * σ - 1) ∧ ∀ κ : ℝ, TaxaL σ 1 κ → κ ≤ 4 * σ - 2 := by
  have hT := ATK.ZeroClasses.BDTheta.rh_iff_Teta.mp hRH
  have h := taxaL_sanduiche (σ := σ) (by rw [hT]; exact hσ) hσ1
  rw [hT] at h
  refine ⟨?_, fun κ hκ => ?_⟩
  · have e : 2 * (σ - 1 / 2) = 2 * σ - 1 := by ring
    rw [← e]
    exact h.1
  · have := h.2 κ hκ
    have e : 2 * (σ - 1 / 2) / (1 / 2) = 4 * σ - 2 := by ring
    rw [e] at this
    exact this

end ATK.ZeroClasses.BDPisoL1

#print axioms ATK.ZeroClasses.BDPisoL1.head0_le
#print axioms ATK.ZeroClasses.BDPisoL1.mid_le
#print axioms ATK.ZeroClasses.BDPisoL1.J_le
#print axioms ATK.ZeroClasses.BDPisoL1.key_L1
#print axioms ATK.ZeroClasses.BDPisoL1.piso_L1
#print axioms ATK.ZeroClasses.BDPisoL1.wR_le_one
#print axioms ATK.ZeroClasses.BDPisoL1.norm_cN_le
#print axioms ATK.ZeroClasses.BDPisoL1.Wσ_molif
#print axioms ATK.ZeroClasses.BDPisoL1.Wσ_taxa
#print axioms ATK.ZeroClasses.BDPisoL1.DNσL_le
#print axioms ATK.ZeroClasses.BDPisoL1.DNσ_le_DNσL
#print axioms ATK.ZeroClasses.BDPisoL1.piso_DNσL
#print axioms ATK.ZeroClasses.BDPisoL1.taxaL_le_zero
#print axioms ATK.ZeroClasses.BDPisoL1.taxaL_Teta
#print axioms ATK.ZeroClasses.BDPisoL1.taxaL_mol
#print axioms ATK.ZeroClasses.BDPisoL1.taxaL_sanduiche
#print axioms ATK.ZeroClasses.BDPisoL1.taxaL_RH
