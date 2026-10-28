import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# ATK — Navier–Stokes: a taxa de Leray e a explosão da comparação de Riccati

Dois fatos sobre a desigualdade cúbica da enstrofia `y' ≤ −a·y + b·y³` (`ATK.NSPequeno`), que
delimitam o que a desigualdade sozinha pode dar:

* **Ponte B3 (critério de Leray), parte quantitativa** — `taxa_leray`: se `y > 0`, `y' ≤ b·y³` em
  `[t₀, T)` e `y → +∞` quando `t → T⁻`, então `y(t)² ≥ 1 / (2b(T − t))`. Com `y = ‖∇u‖²₂` é a
  taxa mínima de explosão de Leray (1934): se a solução suave explode em `T`, a enstrofia cresce
  pelo menos como `(T − t)^{−1/2}`.
* **Obrigação O3, obstrução** — `explosao_comparacao`: para `a, b > 0` e `b·y₀² > a`, a equação de
  comparação `y' = −a·y + b·y³` com `y(0) = y₀` **explode em tempo finito** `T`. Logo a hipótese
  `b·M² < a` de `ATK.NSPequeno.enstrofia_limitada` não pode ser removida usando só a desigualdade
  diferencial: a cota a priori (O3) precisa de informação estrutural de Navier–Stokes além dela.

B3 continua `PUBLICADA_NAO_FORMALIZADA` (a existência local e a continuação das soluções suaves não
estão na Mathlib) e O3 continua `OPEN_MATH`.
-/

open Set Filter Topology Real

namespace ATK.NSExplosao

/-- **Taxa de Leray**: `y > 0`, `y' ≤ b·y³` em `[t₀, T)` e `y → +∞` em `T⁻` ⇒
`1 ≤ 2b(T − t)·y(t)²` para `t ∈ [t₀, T)`. -/
theorem taxa_leray {y y' : ℝ → ℝ} {b t₀ T : ℝ}
    (hderiv : ∀ s ∈ Ico t₀ T, HasDerivAt y (y' s) s) (hpos : ∀ s ∈ Ico t₀ T, 0 < y s)
    (hineq : ∀ s ∈ Ico t₀ T, y' s ≤ b * y s ^ 3) (hlim : Tendsto y (𝓝[<] T) atTop)
    {t : ℝ} (ht : t ∈ Ico t₀ T) : 1 ≤ 2 * b * (T - t) * y t ^ 2 := by
  -- `g(s) = y(s)⁻² + 2bs` é crescente em `[t, T)`
  set g : ℝ → ℝ := fun s => ((y s)⁻¹) ^ 2 + 2 * b * s with hg
  have hsub : Ico t T ⊆ Ico t₀ T := fun s hs => ⟨ht.1.trans hs.1, hs.2⟩
  have hgd : ∀ s ∈ Ico t₀ T, HasDerivAt g (2 * (y s)⁻¹ * (-(y' s) / y s ^ 2) + 2 * b) s := by
    intro s hs
    have h1 : HasDerivAt (fun s => ((y s)⁻¹) ^ 2) (2 * (y s)⁻¹ * (-(y' s) / y s ^ 2)) s := by
      convert ((hderiv s hs).inv (hpos s hs).ne').pow 2 using 1
      simp
    have h2 : HasDerivAt (fun s => 2 * b * s) (2 * b) s := by
      simpa using (hasDerivAt_id s).const_mul (2 * b)
    exact h1.add h2
  have hmono : MonotoneOn g (Ico t T) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico t T)
      (f' := fun s => 2 * (y s)⁻¹ * (-(y' s) / y s ^ 2) + 2 * b) ?_ ?_ ?_
    · exact fun s hs => (hgd s (hsub hs)).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      exact (hgd s (hsub (Ioo_subset_Ico_self hs))).hasDerivWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      have hs' := hsub (Ioo_subset_Ico_self hs)
      have hy := hpos s hs'
      have hi := hineq s hs'
      have e : 2 * (y s)⁻¹ * (-(y' s) / y s ^ 2) + 2 * b = 2 * (b * y s ^ 3 - y' s) / y s ^ 3 := by
        field_simp
        ring
      rw [e]
      exact div_nonneg (by linarith) (by positivity)
  -- `g(s) → 2bT`
  have hw : Tendsto (fun s => ((y s)⁻¹) ^ 2) (𝓝[<] T) (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp hlim).pow 2
    simpa using this
  have hgT : Tendsto g (𝓝[<] T) (𝓝 (0 + 2 * b * T)) :=
    hw.add ((continuous_const.mul continuous_id).tendsto T |>.mono_left nhdsWithin_le_nhds)
  have hle : g t ≤ 0 + 2 * b * T := by
    refine ge_of_tendsto hgT ?_
    filter_upwards [Ioo_mem_nhdsLT ht.2] with s hs
    exact hmono ⟨le_rfl, ht.2⟩ ⟨hs.1.le, hs.2⟩ hs.1.le
  have hy := hpos t ht
  simp only [hg] at hle
  have e : ((y t)⁻¹) ^ 2 * y t ^ 2 = 1 := by field_simp
  nlinarith [sq_nonneg (y t), e]

/-- **Explosão da comparação** (`b·y₀² > a`): `y' = −a·y + b·y³`, `y(0) = y₀`, explode em tempo finito. -/
theorem explosao_comparacao {a b y₀ : ℝ} (ha : 0 < a) (hb : 0 < b) (hy₀ : 0 < y₀)
    (hbig : a < b * y₀ ^ 2) :
    ∃ T : ℝ, 0 < T ∧ ∃ y : ℝ → ℝ, y 0 = y₀ ∧
      (∀ t, t < T → HasDerivAt y (-a * y t + b * y t ^ 3) t) ∧ Tendsto y (𝓝[<] T) atTop := by
  set c := b / a with hc
  set u₀ := (y₀ ^ 2)⁻¹ with hu₀
  have hu₀pos : 0 < u₀ := by positivity
  have hu₀c : u₀ < c := by
    rw [hu₀, hc, inv_lt_iff_one_lt_mul₀ (by positivity), div_mul_eq_mul_div, one_lt_div ha]
    linarith
  set κ := c - u₀ with hκ
  have hκpos : 0 < κ := by linarith
  have hcpos : 0 < c := by positivity
  set u : ℝ → ℝ := fun t => c - κ * rexp (2 * a * t) with hu
  set T := Real.log (c / κ) / (2 * a) with hT
  have hcκ : 1 < c / κ := by rw [one_lt_div hκpos]; linarith
  have hTpos : 0 < T := div_pos (Real.log_pos hcκ) (by positivity)
  have huT : ∀ t, t < T → 0 < u t := by
    intro t ht
    have h1 : 2 * a * t < Real.log (c / κ) := by
      rw [hT, lt_div_iff₀ (by positivity)] at ht; linarith
    have h2 : rexp (2 * a * t) < c / κ := by
      rw [← Real.exp_log (by positivity : 0 < c / κ)]; exact Real.exp_lt_exp.mpr h1
    have h3 : κ * rexp (2 * a * t) < c := by rwa [lt_div_iff₀ hκpos, mul_comm] at h2
    simp only [hu]; linarith
  have huTeq : u T = 0 := by
    simp only [hu, hT]
    rw [show 2 * a * (Real.log (c / κ) / (2 * a)) = Real.log (c / κ) by field_simp,
      Real.exp_log (by positivity)]
    field_simp; ring
  have hud : ∀ t, HasDerivAt u (2 * a * (u t - c)) t := by
    intro t
    have h1 : HasDerivAt (fun s => 2 * a * s) (2 * a) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * a)
    have h2 := ((h1.exp).const_mul κ).const_sub c
    convert h2 using 1
    simp only [hu]; ring
  refine ⟨T, hTpos, fun t => (Real.sqrt (u t))⁻¹, ?_, ?_, ?_⟩
  · -- `y(0) = y₀`
    simp only [hu, mul_zero, Real.exp_zero, mul_one, hκ, sub_sub_cancel, hu₀]
    rw [Real.sqrt_inv, Real.sqrt_sq hy₀.le, inv_inv]
  · intro t ht
    have hut := huT t ht
    have hsq : Real.sqrt (u t) ^ 2 = u t := Real.sq_sqrt hut.le
    have hspos : 0 < Real.sqrt (u t) := Real.sqrt_pos.mpr hut
    have h := ((hud t).sqrt hut.ne').inv hspos.ne'
    convert h using 1
    have hac : a * c = b := by rw [hc]; field_simp
    field_simp
    rw [hsq, ← hac]
    ring
  · -- `√u → 0⁺`, logo `y → +∞`
    have hcont : Continuous fun t => Real.sqrt (u t) := by
      simp only [hu]; fun_prop
    have h0 : Tendsto (fun t => Real.sqrt (u t)) (𝓝[<] T) (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have := hcont.tendsto T
        rw [huTeq, Real.sqrt_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact Real.sqrt_pos.mpr (huT t ht)
    exact tendsto_inv_nhdsGT_zero.comp h0

end ATK.NSExplosao

#print axioms ATK.NSExplosao.taxa_leray
#print axioms ATK.NSExplosao.explosao_comparacao
