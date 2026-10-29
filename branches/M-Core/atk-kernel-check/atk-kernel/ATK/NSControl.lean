import Mathlib

/-!
# ATK — Navier–Stokes, item NS3 da agenda: controle de energia ponderado

Lei de controle com RESTO EXPLÍCITO (a versão sem resto é falsa para soluções reais):
se E' + (1 − θ) D ≤ C E em [0, T], com D contínua, então
  e^{−CT} E(T) + (1 − θ) ∫₀ᵀ e^{−Cs} D(s) ds ≤ E(0).

É o Teorema 4 da sessão anterior, agora provado no kernel. Aplicá-lo a Navier–Stokes exige provar
a desigualdade de entrada para as soluções reais — isso continua ABERTO.
-/

namespace ATK.NSControl

open Set

theorem weighted_energy_control {E E' D : ℝ → ℝ} {C θ T : ℝ} (hT : 0 ≤ T)
    (hE : ∀ t, HasDerivAt E (E' t) t) (hD : Continuous D)
    (hineq : ∀ t ∈ Icc 0 T, E' t + (1 - θ) * D t ≤ C * E t) :
    Real.exp (-C * T) * E T + (1 - θ) * ∫ s in (0 : ℝ)..T, Real.exp (-C * s) * D s ≤ E 0 := by
  have hg : Continuous (fun s : ℝ => Real.exp (-C * s) * D s) := by fun_prop
  have hderiv : ∀ t, HasDerivAt
      (fun u => Real.exp (-C * u) * E u + (1 - θ) * ∫ s in (0 : ℝ)..u, Real.exp (-C * s) * D s)
      (Real.exp (-C * t) * (-C) * E t + Real.exp (-C * t) * E' t
        + (1 - θ) * (Real.exp (-C * t) * D t)) t := by
    intro t
    have h1 : HasDerivAt (fun u => Real.exp (-C * u)) (Real.exp (-C * t) * (-C)) t := by
      have := ((hasDerivAt_id t).const_mul (-C)).exp
      simpa using this
    have h2 := h1.mul (hE t)
    have h3 := (hg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_mul (1 - θ)
    exact h2.add h3
  have hanti : AntitoneOn
      (fun u => Real.exp (-C * u) * E u + (1 - θ) * ∫ s in (0 : ℝ)..u, Real.exp (-C * s) * D s)
      (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact HasDerivAt.continuousOn (fun t _ => hderiv t)
    · intro t _
      exact (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t).deriv]
      have hin := hineq t (Ioo_subset_Icc_self ht)
      have hexp := Real.exp_pos (-C * t)
      have hkey : Real.exp (-C * t) * (-C) * E t + Real.exp (-C * t) * E' t
          + (1 - θ) * (Real.exp (-C * t) * D t)
          = Real.exp (-C * t) * (E' t + (1 - θ) * D t - C * E t) := by ring
      rw [hkey]
      exact mul_nonpos_of_nonneg_of_nonpos hexp.le (by linarith)
  have h := hanti ⟨le_refl 0, hT⟩ ⟨hT, le_refl T⟩ hT
  simpa using h

end ATK.NSControl

#print axioms ATK.NSControl.weighted_energy_control
