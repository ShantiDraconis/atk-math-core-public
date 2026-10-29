import ATK.MellinPlancherel
import ATK.BaezDuarteBridge

/-!
# ATK — Fórmula espectral de `D_N` na linha crítica

Com `𝓜χ(s) = 1/s` e `𝓜ρ_k(s) = −k^{−s} ζ(s)/s` (`0 < Re s < 1`, `ATK.MellinRho`), a transformada
de Mellin do resíduo `χ − Σ c_k ρ_{k+1}` é

  `𝓜(res)(s) = (1 + ζ(s) · Σ_k c_k (k+1)^{−s}) / s`   (`mellin_res_geral`),

e o Plancherel de Mellin (`ATK.MellinPlancherel`) dá a **fórmula espectral**

  `‖χ − Σ c_k ρ_{k+1}‖² = (1/2π) ∫_ℝ |1 + ζ(½+iτ) Σ_k c_k (k+1)^{−½−iτ}|² / |½+iτ|² dτ`

(`residualSq_espectral`) e `D_N = inf_c (1/2π) ∫ …` (`DN_espectral`). Com isso, a direção de
necessidade de Báez-Duarte (RH ⇒ `D_N → 0`) fica equivalente a um enunciado só sobre `ζ` na
linha crítica (`necessidade_iff_espectral`). Ela continua não provada aqui.
-/

open MeasureTheory Set Real Filter Topology
open ATK.Conditional.Riemann ATK.BaezDuarteBridge ATK.MellinRho

namespace ATK.EspectralDN

/-- Integrando espectral em `s = 1/2 + iτ`. -/
noncomputable def espectro {N : ℕ} (c : Fin N → ℝ) (τ : ℝ) : ℝ :=
  ‖(1 + riemannZeta (1 / 2 + (τ : ℂ) * Complex.I) *
      ∑ k : Fin N, (c k : ℂ) * ((k.val + 1 : ℕ) : ℂ) ^ (-(1 / 2 + (τ : ℂ) * Complex.I))) /
    (1 / 2 + (τ : ℂ) * Complex.I)‖ ^ 2

/-- **Mellin do resíduo** para `0 < Re s < 1`. -/
theorem mellin_res_geral {N : ℕ} (c : Fin N → ℝ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (fun t => ((res c t : ℝ) : ℂ)) s ∧
      mellin (fun t => ((res c t : ℝ) : ℂ)) s =
        (1 + riemannZeta s * ∑ k : Fin N, (c k : ℂ) * ((k.val + 1 : ℕ) : ℂ) ^ (-s)) / s := by
  have hs0' : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have hχ := hasMellin_chi hs0
  have hρ : ∀ k : Fin N, MellinConvergent (fun t => ((rho (k.val + 1) t : ℝ) : ℂ)) s :=
    fun k => mellinConvergent_rho (Nat.succ_pos _) hs0 hs1
  have hρv : ∀ k : Fin N,
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • ((rho (k.val + 1) t : ℝ) : ℂ) =
        -(((k.val + 1 : ℕ) : ℂ) ^ (-s) * riemannZeta s / s) :=
    fun k => mellin_rho (Nat.succ_pos _) hs0 hs1
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
  simp_rw [integral_const_mul, hρv]
  rw [Finset.mul_sum, add_div, Finset.sum_div, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp

/-- **Fórmula espectral do resíduo.** -/
theorem residualSq_espectral {N : ℕ} (c : Fin N → ℝ) :
    residualSq N c = (2 * π)⁻¹ * ∫ τ : ℝ, espectro c τ := by
  have hhalf0 : 0 < (((1 / 2 : ℝ) : ℂ)).re := by simp
  have hhalf1 : (((1 / 2 : ℝ) : ℂ)).re < 1 := by norm_num
  have h1 : MellinConvergent (fun t => ((res c t : ℝ) : ℂ)) ((1 / 2 : ℝ) : ℂ) :=
    (mellin_res_geral c hhalf0 hhalf1).1
  have h2 : IntegrableOn (fun t => ‖((res c t : ℝ) : ℂ)‖ ^ 2) (Ioi 0) := by
    refine (integrable_res_sq c).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [Complex.norm_real, sq_abs]
  have h := ATK.MellinPlancherel.integral_norm_sq_eq_mellin h1 h2
  have hL : ∫ t in Ioi (0 : ℝ), ‖((res c t : ℝ) : ℂ)‖ ^ 2 = residualSq N c := by
    rw [residualSq_eq_res]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp [Complex.norm_real, sq_abs]
  have hR : ∀ τ : ℝ, ‖mellin (fun t => ((res c t : ℝ) : ℂ)) (1 / 2 + (τ : ℂ) * Complex.I)‖ ^ 2 =
      espectro c τ := by
    intro τ
    have hre : (1 / 2 + (τ : ℂ) * Complex.I).re = 1 / 2 := by simp
    rw [(mellin_res_geral c (by rw [hre]; norm_num) (by rw [hre]; norm_num)).2]
    rfl
  rw [← hL, h]
  congr 2
  funext τ
  exact hR τ

/-- **`D_N` na linha crítica**: `D_N = inf_c (1/2π) ∫ espectro`. -/
theorem DN_espectral (N : ℕ) :
    DN N = ⨅ c : Fin N → ℝ, (2 * π)⁻¹ * ∫ τ : ℝ, espectro c τ := by
  unfold DN
  congr 1
  funext c
  exact residualSq_espectral c

/-- A sequência espectral. -/
noncomputable def DNespectral (N : ℕ) : ℝ := ⨅ c : Fin N → ℝ, (2 * π)⁻¹ * ∫ τ : ℝ, espectro c τ

theorem DN_eq_DNespectral : DN = DNespectral := funext DN_espectral

/-- **A necessidade de Báez-Duarte equivale a um enunciado só sobre `ζ` na linha crítica.** -/
theorem necessidade_iff_espectral :
    (RiemannHypothesis → Tendsto DN atTop (𝓝 0)) ↔
      (RiemannHypothesis → Tendsto DNespectral atTop (𝓝 0)) := by
  rw [DN_eq_DNespectral]

/-- Com B1: `DNespectral → 0` implica RH. -/
theorem rh_of_espectral (h : Tendsto DNespectral atTop (𝓝 0)) : RiemannHypothesis :=
  baezDuarteCriterion (DN_eq_DNespectral ▸ h)

end ATK.EspectralDN

#print axioms ATK.EspectralDN.mellin_res_geral
#print axioms ATK.EspectralDN.residualSq_espectral
#print axioms ATK.EspectralDN.DN_espectral
#print axioms ATK.EspectralDN.DN_eq_DNespectral
#print axioms ATK.EspectralDN.necessidade_iff_espectral
#print axioms ATK.EspectralDN.rh_of_espectral
