import ATK.IndeterminacyStates
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# ATK — Navier–Stokes: o núcleo analítico da regularidade global para dados pequenos

Na 3D com viscosidade `ν` (toro, média nula), a enstrofia `y(t) = ‖∇u(t)‖²` satisfaz — pela equação,
desigualdade de Poincaré e interpolação de Sobolev — a desigualdade diferencial

  `y' ≤ −a·y + b·y³`   (`a = νλ₁ > 0`, `b = C/ν³ ≥ 0`).

Derivar essa desigualdade exige o modelo de Navier–Stokes (lacuna L1, ausente da Mathlib). Dada a
desigualdade, este arquivo prova o resto **sem hipóteses adicionais**:

* `barreira_exponencial`: se `0 < M`, `y(0) < M` e `b·M² < a`, então
  `y(t) ≤ M·e^{−κt}` para todo `t ≥ 0`, com `κ = (a − bM²)/2 > 0` (princípio de comparação da
  Mathlib);
* `enstrofia_limitada`: `y(t) ≤ M` para todo `t ≥ 0` — **o estado `+∞` está excluído** (sem explosão,
  isto é, regularidade global);
* `enstrofia_estado_zero`: se além disso `y ≥ 0`, então `y(t) → 0` — **estado `zero`**.

A lacuna O3 (cota a priori de enstrofia para **todo** dado) é exatamente remover a hipótese
`b·M² < a`: para dados grandes, a mesma desigualdade só dá a cota local de Riccati
(`ATK.NavierStokes.riccati_upper_bound`), que pode explodir em tempo finito.
-/

open Set Filter Topology Real

namespace ATK.NSPequeno

open ATK.IndeterminacyStates

/-- **Barreira exponencial (dados pequenos).** -/
theorem barreira_exponencial {y y' : ℝ → ℝ} {a b M : ℝ} (hb : 0 ≤ b) (hM0 : 0 < M)
    (hy0 : y 0 < M) (hMa : b * M ^ 2 < a) (hderiv : ∀ t, HasDerivAt y (y' t) t)
    (hineq : ∀ t, 0 ≤ t → y' t ≤ -a * y t + b * y t ^ 3) :
    ∀ t, 0 ≤ t → y t ≤ M * rexp (-((a - b * M ^ 2) / 2) * t) := by
  set κ := (a - b * M ^ 2) / 2 with hκ
  have hκpos : 0 < κ := by rw [hκ]; linarith
  intro T hT
  have hB : ∀ t, HasDerivAt (fun s => M * rexp (-κ * s)) (M * (rexp (-κ * t) * -κ)) t := by
    intro t
    have h1 : HasDerivAt (fun s => -κ * s) (-κ) t := by
      simpa using (hasDerivAt_id t).const_mul (-κ)
    exact (h1.exp).const_mul M
  refine image_le_of_deriv_right_lt_deriv_boundary' (a := 0) (b := T)
    (f := y) (f' := y') (B := fun s => M * rexp (-κ * s)) (B' := fun t => M * (rexp (-κ * t) * -κ))
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
    (fun t _ => (hderiv t).hasDerivWithinAt)
    (by simp; linarith)
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt)
    ?_ ⟨hT, le_rfl⟩
  intro t ht hyt
  have hE : 0 < rexp (-κ * t) := exp_pos _
  have hBpos : 0 < M * rexp (-κ * t) := mul_pos hM0 hE
  have hE1 : rexp (-κ * t) ≤ 1 := by
    rw [exp_le_one_iff]; nlinarith [ht.1]
  have hyle : y t ≤ M := by rw [hyt]; nlinarith
  have hypos : 0 < y t := by rw [hyt]; exact hBpos
  have hsq : y t ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hypos.le hyle 2
  have h1 := hineq t ht.1
  have h2 : -a * y t + b * y t ^ 3 ≤ -(2 * κ) * y t := by
    have : b * y t ^ 2 ≤ b * M ^ 2 := mul_le_mul_of_nonneg_left hsq hb
    nlinarith
  have h3 : -(2 * κ) * y t < M * (rexp (-κ * t) * -κ) := by
    have e : M * (rexp (-κ * t) * -κ) = -κ * y t := by rw [hyt]; ring
    rw [e]; nlinarith
  show y' t < M * (rexp (-κ * t) * -κ)
  linarith

/-- **Sem explosão**: a enstrofia fica abaixo de `M` para todo tempo. -/
theorem enstrofia_limitada {y y' : ℝ → ℝ} {a b M : ℝ} (hb : 0 ≤ b) (hM0 : 0 < M)
    (hy0 : y 0 < M) (hMa : b * M ^ 2 < a) (hderiv : ∀ t, HasDerivAt y (y' t) t)
    (hineq : ∀ t, 0 ≤ t → y' t ≤ -a * y t + b * y t ^ 3) :
    ∀ t, 0 ≤ t → y t ≤ M := by
  intro t ht
  have h := barreira_exponencial hb hM0 hy0 hMa hderiv hineq t ht
  have hκ : 0 ≤ (a - b * M ^ 2) / 2 := by linarith
  have hE1 : rexp (-((a - b * M ^ 2) / 2) * t) ≤ 1 := by
    rw [exp_le_one_iff]; nlinarith
  nlinarith

/-- **Estado `zero`**: com `y ≥ 0` (enstrofia), `y(t) → 0`. -/
theorem enstrofia_estado_zero {y y' : ℝ → ℝ} {a b M : ℝ} (hb : 0 ≤ b) (hM0 : 0 < M)
    (hy0 : y 0 < M) (hMa : b * M ^ 2 < a) (hderiv : ∀ t, HasDerivAt y (y' t) t)
    (hineq : ∀ t, 0 ≤ t → y' t ≤ -a * y t + b * y t ^ 3) (hnn : ∀ t, 0 ≤ y t) :
    Comporta atTop y Estado7.zero := by
  set κ := (a - b * M ^ 2) / 2 with hκ
  have hκpos : 0 < κ := by rw [hκ]; linarith
  have hlim : Tendsto (fun t => M * rexp (-κ * t)) atTop (𝓝 (M * 0)) := by
    refine tendsto_const_nhds.mul ?_
    have : Tendsto (fun t : ℝ => -κ * t) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    exact tendsto_exp_atBot.comp this
  rw [mul_zero] at hlim
  show Tendsto y atTop (𝓝 0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall hnn) ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact barreira_exponencial hb hM0 hy0 hMa hderiv hineq t ht

end ATK.NSPequeno

#print axioms ATK.NSPequeno.barreira_exponencial
#print axioms ATK.NSPequeno.enstrofia_limitada
#print axioms ATK.NSPequeno.enstrofia_estado_zero
