import ATK.ZetaStrip
import ATK.RiemannFaithful

/-!
# ATK — Transformada de Mellin dos geradores de Báez-Duarte (passo 2 da ponte)

Para `0 < Re s < 1` e `k ≥ 1`, prova-se no kernel

  `∫_0^∞ {1/(k t)} t^{s-1} dt = − k^{-s} ζ(s) / s`,

com `ζ` a função zeta da Mathlib. Ingredientes: `∫_0^∞ {u} u^{-s-1} du = 1/(1−s) + H(s)`
(decomposição de `{u}` em `(0,1]` e `(1,∞)`), `H(s) = 1/(s−1) − ζ(s)/s` (`ATK.ZetaStrip`),
e as regras de mudança de variável de Mellin da Mathlib (`mellin_comp_mul_left`,
`mellin_comp_inv`).

Consequência: se `ζ(s) = 0` na faixa, todos os `ρ_k` têm transformada de Mellin nula em `s`.
-/

open Complex Set MeasureTheory Filter Topology

namespace ATK.MellinRho

open ATK.ZetaStrip ATK.Conditional.Riemann

/-- `{t}` como função complexa. -/
noncomputable def fr (t : ℝ) : ℂ := ((Int.fract t : ℝ) : ℂ)

/-- A parte `(0,1]` de `{t}`: `t·𝟙_{(0,1]}`. -/
noncomputable def low (t : ℝ) : ℂ := Set.indicator (Ioc (0 : ℝ) 1) (fun u : ℝ => (u : ℂ) ^ (1 : ℂ)) t

theorem fr_decomp {t : ℝ} (ht : 0 < t) (h1 : t ≠ 1) : low t + fracTail t = fr t := by
  rcases lt_or_gt_of_ne h1 with h | h
  · have hl : low t = (t : ℂ) := by
      have hm : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, h.le⟩
      simp [low, hm]
    rw [hl, fracTail_of_lt_one h, add_zero]
    unfold fr
    rw [Int.fract_eq_self.mpr ⟨ht.le, h⟩]
  · have hl : low t = 0 := by
      have hm : t ∉ Ioc (0 : ℝ) 1 := fun hm => absurd hm.2 (not_le.mpr h)
      simp [low, hm]
    have hf : fracTail t = fr t := by
      have hm : t ∈ Ioi (1 : ℝ) := h
      simp [fracTail, fr, hm]
    rw [hl, hf, zero_add]

theorem ae_ne_one : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 1 := by
  have h := measure_eq_zero_iff_ae_notMem.mp (Real.volume_singleton (a := (1 : ℝ)))
  filter_upwards [h] with t ht
  simpa using ht

theorem mellin_congr_ne_one {f g : ℝ → ℂ} {s : ℂ} (h : ∀ t, 0 < t → t ≠ 1 → f t = g t) :
    mellin f s = mellin g s := by
  unfold mellin
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards [ae_ne_one] with t h1 ht0
  rw [h t ht0 h1]

theorem mellinConvergent_congr_ne_one {f g : ℝ → ℂ} {s : ℂ}
    (h : ∀ t, 0 < t → t ≠ 1 → f t = g t) (hf : MellinConvergent f s) : MellinConvergent g s := by
  unfold MellinConvergent at *
  refine Integrable.congr hf ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr ?_
  filter_upwards [ae_ne_one] with t h1 ht0
  simp only [h t ht0 h1]

/-- `∫_0^∞ {u} u^{-s-1} du = 1/(1−s) + H(s)` para `0 < Re s < 1`. -/
theorem mellin_fr_neg {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent fr (-s) ∧ mellin fr (-s) = 1 / (1 - s) + H s := by
  have hlow : HasMellin low (-s) (1 / (-s + 1)) :=
    hasMellin_cpow_Ioc 1 (by rw [neg_re, one_re]; linarith)
  have htail : MellinConvergent fracTail (-s) := mellinConvergent_fracTail (by rw [neg_re]; linarith)
  have hsum := hasMellin_add hlow.1 htail
  have hdec : ∀ t, 0 < t → t ≠ 1 → low t + fracTail t = fr t := fun t ht h1 => fr_decomp ht h1
  refine ⟨mellinConvergent_congr_ne_one hdec hsum.1, ?_⟩
  rw [← mellin_congr_ne_one hdec, hsum.2, hlow.2]
  unfold H
  rw [show -s + 1 = 1 - s by ring]

theorem rho_eq_comp (k : ℕ) :
    (fun t => ((rho k t : ℝ) : ℂ)) = fun t => (fun u : ℝ => fr u⁻¹) ((k : ℝ) * t) := by
  funext t
  unfold rho fr
  rw [one_div]

/-- Convergência e valor da transformada de Mellin de `ρ_k` na faixa `0 < Re s < 1`. -/
theorem mellin_rho_aux {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (fun t => ((rho k t : ℝ) : ℂ)) s ∧
      mellin (fun t => ((rho k t : ℝ) : ℂ)) s = (k : ℂ) ^ (-s) * (1 / (1 - s) + H s) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  obtain ⟨hc, hm⟩ := mellin_fr_neg hs0 hs1
  have hinv : (fun u : ℝ => fr u⁻¹) = fun u => fr (u ^ (-1 : ℝ)) := by
    funext u; rw [Real.rpow_neg_one]
  constructor
  · rw [rho_eq_comp]
    refine (MellinConvergent.comp_mul_left (f := fun u : ℝ => fr u⁻¹) hk0).mpr ?_
    rw [hinv]
    refine (MellinConvergent.comp_rpow (f := fr) (by norm_num : (-1 : ℝ) ≠ 0)).mpr ?_
    have hs' : s / (((-1 : ℝ)) : ℂ) = -s := by push_cast; ring
    rw [hs']
    exact hc
  · calc mellin (fun t => ((rho k t : ℝ) : ℂ)) s
        = mellin (fun t => (fun u : ℝ => fr u⁻¹) ((k : ℝ) * t)) s := by rw [rho_eq_comp]
      _ = (k : ℂ) ^ (-s) • mellin (fun u : ℝ => fr u⁻¹) s :=
          mellin_comp_mul_left (fun u : ℝ => fr u⁻¹) s hk0
      _ = (k : ℂ) ^ (-s) * mellin fr (-s) := by rw [mellin_comp_inv, smul_eq_mul]
      _ = (k : ℂ) ^ (-s) * (1 / (1 - s) + H s) := by rw [hm]

/-- **`∫_0^∞ {1/(k t)} t^{s−1} dt = −k^{−s} ζ(s)/s`** para `0 < Re s < 1`, `k ≥ 1`. -/
theorem mellin_rho {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    mellin (fun t => ((rho k t : ℝ) : ℂ)) s = -((k : ℂ) ^ (-s) * riemannZeta s / s) := by
  have hsne : s ≠ 1 := by intro h; rw [h, one_re] at hs1; exact lt_irrefl 1 hs1
  have hs0' : s ≠ 0 := by intro h; rw [h, zero_re] at hs0; exact lt_irrefl 0 hs0
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hsne)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hsne
  rw [(mellin_rho_aux hk hs0 hs1).2, H_eq_zeta hs0 hsne]
  field_simp
  ring

theorem mellinConvergent_rho {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (fun t => ((rho k t : ℝ) : ℂ)) s :=
  (mellin_rho_aux hk hs0 hs1).1

/-- Se `ζ(s) = 0` com `0 < Re s < 1`, então `∫_0^∞ ρ_k(t) t^{s−1} dt = 0` para todo `k ≥ 1`. -/
theorem mellin_rho_eq_zero {k : ℕ} (hk : 1 ≤ k) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) : mellin (fun t => ((rho k t : ℝ) : ℂ)) s = 0 := by
  rw [mellin_rho hk hs0 hs1, hz]
  simp

end ATK.MellinRho

#print axioms ATK.MellinRho.fr_decomp
#print axioms ATK.MellinRho.ae_ne_one
#print axioms ATK.MellinRho.mellin_congr_ne_one
#print axioms ATK.MellinRho.mellinConvergent_congr_ne_one
#print axioms ATK.MellinRho.mellin_fr_neg
#print axioms ATK.MellinRho.rho_eq_comp
#print axioms ATK.MellinRho.mellin_rho_aux
#print axioms ATK.MellinRho.mellin_rho
#print axioms ATK.MellinRho.mellinConvergent_rho
#print axioms ATK.MellinRho.mellin_rho_eq_zero
