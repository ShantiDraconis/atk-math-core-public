import ATK.JensenTuran
import ATK.RHTerminal
import ATK.BaseRiemannXi
import ATK.BSDCoefLider

/-!
# ATK-RH — `ξ` analítica: ordens, derivada logarítmica, paridade, Jensen no disco, critério de sinal

`xiE(s) = s(s−1)/2 · Λ₀(s) + ½` (inteira; `ATK.ClosedMath.Jensen.xiE`).

* **Básico**: `xiE` inteira, `ξ(s̄) = conj ξ(s)`, ordem finita em todo ponto (`xiE_order_ne_top`),
  `log|ξ|` harmônica fora dos zeros (`log_norm_xiE_harmonica`).
* **Ponte de multiplicidade**: na faixa `Re s > 0`, `s ≠ 1`: `ord_s ξ = ord_s ζ` (`ordem_xiE_eq_zeta`).
* **Zeros triviais simples**: `ζ′(−2k) = (π/2)·sin(π(2k+1)/2)·2(2π)^{−(2k+1)}Γ(2k+1)ζ(2k+1) ≠ 0` e
  `ord_{−2k} ζ = 1` para `k ≥ 1` (`zeros_triviais_simples`).
* **`ξ′/ξ` com digama**: `ξ′/ξ(s) = 1/s + 1/(s−1) − ½ log π + ½ ψ(s/2) + ζ′/ζ(s)` (`logDeriv_xiE`).
* **Paridade** de `F(z) = ξ(½ + z)`: `F^{(n)}(−z) = (−1)ⁿ F^{(n)}(z)`, `F(it) ∈ ℝ`, `F′(it) ∈ iℝ`,
  `A(−d,t) = A(d,t)`, `B(−d,t) = −B(d,t)`; **integração horizontal**
  `F(d+it) − F(it) = d ∫₀¹ F′(vd+it) dv`, logo `B = d ∫₀¹ Im F′(vd+it) dv` (`B_integral`) — com
  **`Im`**, não `Re`: o contraexemplo `F = z²` (`contraexemplo_Re`) mostra que a versão com `Re` é
  falsa. Num zero `F(d+it) = 0`: `F(it)² ≤ d² ∫₀¹ (Re F′)²` (`zero_cota`).
* **Teste do disco (Jensen)**: `f` analítica em `B̄(c,R)`, `f(c) ≠ 0`: há zero em `B(c,R)` ⟺
  `log|f(c)| < média de log|f|` no círculo (`disco_jensen`); para `ξ`: HR ⟺ igualdade em todo disco
  da metade direita (`rh_iff_disco`).
* **Critério de sinal (direção suficiente)**: se `Re(F′/F) > 0` fora dos zeros num aberto, `F` não
  tem zeros lá (`sem_zeros_de_sinal`); para `ξ`: `Re ξ′/ξ > 0` em `Re s > ½` ⇒ HR (`rh_de_sinal`).
  A recíproca precisa do produto de Hadamard (fora da Mathlib) e **não** está aqui.
* **Energia finita** (parte (d) da identidade de Green): `H = 24 Σ m_ρ (Re ρ − ½)² ≥ 0`, `= 0` ⟺ todos
  na linha; cada zero tem `|Re ρ − ½| ≤ √(H/(24 m_ρ))` (`energia_*`).
* **Fator Γ em `K_n`**: `∃ A > 0, ∀ s ∈ K_n, A|ζ(s)| ≤ |ξ(s)|` (`fator_gamma_Kn`).

Nada aqui prova HR.
-/

open Complex ComplexConjugate Filter Topology Set Metric MeasureTheory
open scoped Real

namespace ATK.XiAnalitica

open ATK.ClosedMath.Jensen (xiE xiE_par xiE_zero_iff xiE_zero_val)
open ATK.ZetaSimetria

/-! ## 1. Básico -/

theorem xiE_eq_riemannXi : xiE = ATK.BaseRiemannXi.riemannXi := rfl

theorem differentiable_xiE : Differentiable ℂ xiE := ATK.BaseRiemannXi.differentiable_riemannXi

theorem analyticAt_xiE (s : ℂ) : AnalyticAt ℂ xiE s := differentiable_xiE.analyticAt s

theorem xiE_conj (s : ℂ) : xiE (conj s) = conj (xiE s) := ATK.BaseRiemannXi.riemannXi_conj s

/-- A ordem de `ξ` é finita em todo ponto (`ξ(0) = ½`). -/
theorem xiE_order_ne_top (s : ℂ) : analyticOrderAt xiE s ≠ ⊤ := by
  intro h
  have hev : xiE =ᶠ[𝓝 s] 0 := analyticOrderAt_eq_top.mp h
  have han : AnalyticOnNhd ℂ xiE univ := fun z _ => analyticAt_xiE z
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ s) hev
  have h0 := this (mem_univ 0)
  rw [xiE_zero_val] at h0
  norm_num at h0

/-- **`log|ξ|` é harmônica fora dos zeros.** -/
theorem log_norm_xiE_harmonica {s : ℂ} (hs : xiE s ≠ 0) :
    InnerProductSpace.HarmonicAt (fun z => Real.log ‖xiE z‖) s :=
  (analyticAt_xiE s).harmonicAt_log_norm hs

/-- HR ⟺ `ξ` não se anula em `Re s > ½`. -/
theorem rh_iff_xiE_direita : RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → xiE s ≠ 0 := by
  rw [ATK.ClosedMath.Terminal.T25]
  constructor
  · intro h s hs hx
    have hZ := (xiE_zero_iff s).mp hx
    exact h s ⟨hs, hZ.2.2⟩ hZ.1
  · intro h s hs hz
    exact h s hs.1 ((xiE_zero_iff s).mpr ⟨hz, by linarith [hs.1], hs.2⟩)

/-! ## 2. Ponte de multiplicidade `ord ξ = ord ζ` na faixa -/

theorem xiE_eq_fator {z : ℂ} (hz : 0 < z.re) (hz1 : z ≠ 1) :
    xiE z = z * (z - 1) / 2 * Gammaℝ z * riemannZeta z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  rw [xiE_eq_riemannXi]
  exact ATK.BaseRiemannXi.riemannXi_eq_zeta hz0 hz1 (Gammaℝ_ne_zero_of_re_pos hz)

theorem hasDerivAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt Gammaℝ (Gammaℝ s * (-(Real.log π : ℂ) / 2 + digamma (s / 2) / 2)) s := by
  have hs2 : 0 < (s / 2).re := by simp; linarith
  have hG0 : Gamma (s / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hs2
  have hnm : ∀ m : ℕ, s / 2 ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  have hGd : HasDerivAt Gamma (deriv Gamma (s / 2)) (s / 2) :=
    (differentiableAt_Gamma _ hnm).hasDerivAt
  have hlin : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) s := by
    simpa using (hasDerivAt_id s).div_const 2
  have hneg : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) s := by
    simpa using (hasDerivAt_id s).neg.div_const 2
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 := hneg.const_cpow (c := (π : ℂ)) (Or.inl hpi)
  have h2 := hGd.comp s hlin
  have h := h1.mul h2
  have hlog : Complex.log (π : ℂ) = (Real.log π : ℂ) := (Complex.ofReal_log Real.pi_pos.le).symm
  have hdig : digamma (s / 2) = deriv Gamma (s / 2) / Gamma (s / 2) := by
    rw [digamma_def, logDeriv_apply]
  have e : Gammaℝ = (fun x : ℂ => (π : ℂ) ^ (-x / 2)) * (Gamma ∘ fun z : ℂ => z / 2) := by
    funext z; rw [Gammaℝ_def]; rfl
  rw [e]
  convert h using 1
  rw [hdig, hlog]
  simp only [Function.comp, Pi.mul_apply]
  field_simp

theorem analyticAt_fator {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ (fun z => z * (z - 1) / 2 * Gammaℝ z) s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hd : DifferentiableOn ℂ (fun z => z * (z - 1) / 2 * Gammaℝ z) {z : ℂ | 0 < z.re} := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).div_const 2).mul
      (hasDerivAt_Gammaℝ hz).differentiableAt)
  exact hd.analyticAt (hU.mem_nhds hs)

/-- **`ord_s ξ = ord_s ζ`** para `Re s > 0`, `s ≠ 1`. -/
theorem ordem_xiE_eq_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    analyticOrderAt xiE s = analyticOrderAt riemannZeta s := by
  have hU : IsOpen {z : ℂ | 0 < z.re ∧ z ≠ 1} :=
    (isOpen_lt continuous_const continuous_re).inter isOpen_ne
  have hev : xiE =ᶠ[𝓝 s] fun z => (z * (z - 1) / 2 * Gammaℝ z) * riemannZeta z := by
    filter_upwards [hU.mem_nhds ⟨hs, hs1⟩] with z hz
    exact xiE_eq_fator hz.1 hz.2
  rw [analyticOrderAt_congr hev]
  have hz : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hu0 : s * (s - 1) / 2 * Gammaℝ s ≠ 0 :=
    mul_ne_zero (div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) two_ne_zero)
      (Gammaℝ_ne_zero_of_re_pos hs)
  exact ATK.ClosedMath.ordem_preservada (u := fun z => z * (z - 1) / 2 * Gammaℝ z) hz
    (analyticAt_fator hs) hu0

/-! ## 3. Os zeros triviais são simples -/

/-- `2(2π)^{−s}Γ(s)`. -/
noncomputable def Afun (s : ℂ) : ℂ := 2 * (2 * π) ^ (-s) * Gamma s

/-- **`ζ′(−2k) = (π/2)·sin(π(2k+1)/2)·A(2k+1)·ζ(2k+1)`.** -/
theorem deriv_zeta_trivial (k : ℕ) (hk : 1 ≤ k) :
    HasDerivAt riemannZeta
      ((π : ℂ) / 2 * Complex.sin (π * (2 * k + 1) / 2) * Afun (2 * k + 1) * riemannZeta (2 * k + 1))
      (-2 * k) := by
  set s₀ : ℂ := 2 * k + 1 with hs₀
  have hre : s₀.re = 2 * k + 1 := by simp [hs₀]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have hmem : s₀ ∈ {s : ℂ | 1 < s.re} := by simp only [mem_ofPred_eq, hre]; linarith
  -- a equação funcional perto de `s₀`
  have hev : (fun s => riemannZeta (1 - s)) =ᶠ[𝓝 s₀]
      fun s => (Afun s * Complex.cos (π * s / 2)) * riemannZeta s := by
    filter_upwards [hU.mem_nhds hmem] with s hs
    have hs' : ∀ n : ℕ, s ≠ -n := by
      intro n h
      have := congrArg Complex.re h
      simp only [neg_re, natCast_re] at this
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    have hs1 : s ≠ 1 := by
      rintro rfl; simp at hs
    rw [riemannZeta_one_sub hs' hs1, Afun]
  -- derivadas
  have hnm : ∀ m : ℕ, s₀ ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    rw [hre] at this
    simp at this
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  have h2pi : (2 * (π : ℂ)) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hA : HasDerivAt Afun (deriv Afun s₀) s₀ := by
    refine DifferentiableAt.hasDerivAt ?_
    unfold Afun
    refine (DifferentiableAt.const_mul ?_ 2).mul (differentiableAt_Gamma _ hnm)
    exact (differentiableAt_id.neg).const_cpow (Or.inl h2pi)
  have hc : HasDerivAt (fun s : ℂ => Complex.cos (π * s / 2))
      (-Complex.sin (π * s₀ / 2) * (π / 2)) s₀ := by
    have hl : HasDerivAt (fun s : ℂ => π * s / 2) (π / 2) s₀ := by
      simpa using ((hasDerivAt_id s₀).const_mul (π : ℂ)).div_const 2
    exact hl.ccos
  have hcos0 : Complex.cos (π * s₀ / 2) = 0 := by
    rw [Complex.cos_eq_zero_iff]
    exact ⟨k, by rw [hs₀]; push_cast; ring⟩
  have h1 : (1 : ℂ) - s₀ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp [hs₀] at this
    linarith
  have hzd : HasDerivAt riemannZeta (deriv riemannZeta (1 - s₀)) (1 - s₀) :=
    (differentiableAt_riemannZeta h1).hasDerivAt
  have hs0ne : s₀ ≠ 1 := by intro h; rw [h] at hmem; simp at hmem
  have hzs : HasDerivAt riemannZeta (deriv riemannZeta s₀) s₀ :=
    (differentiableAt_riemannZeta hs0ne).hasDerivAt
  have hL : HasDerivAt (fun s => riemannZeta (1 - s)) (deriv riemannZeta (1 - s₀) * (-1)) s₀ := by
    have hl : HasDerivAt (fun s : ℂ => 1 - s) (-1) s₀ := by
      simpa using (hasDerivAt_id s₀).const_sub (1 : ℂ)
    exact hzd.comp s₀ hl
  have hR := (hA.mul hc).mul hzs
  have hR' := hR.congr_of_eventuallyEq hev
  have huniq := hL.unique hR'
  simp only [Pi.mul_apply] at huniq
  rw [hcos0] at huniq
  have hpt : (1 : ℂ) - s₀ = -2 * k := by rw [hs₀]; ring
  rw [hpt] at huniq hzd
  have hval : deriv riemannZeta (-2 * k) =
      (π : ℂ) / 2 * Complex.sin (π * (2 * k + 1) / 2) * Afun (2 * k + 1) * riemannZeta (2 * k + 1) := by
    rw [← hs₀]
    linear_combination (-1 : ℂ) * huniq
  rw [← hval]
  exact hzd

/-- **Os zeros triviais `−2k` (`k ≥ 1`) são simples**: `ζ′(−2k) ≠ 0` e `ord_{−2k} ζ = 1`. -/
theorem zeros_triviais_simples (k : ℕ) (hk : 1 ≤ k) :
    deriv riemannZeta (-2 * k) ≠ 0 ∧ analyticOrderAt riemannZeta (-2 * k) = 1 := by
  have hd := deriv_zeta_trivial k hk
  set s₀ : ℂ := 2 * k + 1 with hs₀
  have hre : s₀.re = 2 * k + 1 := by simp [hs₀]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnm : ∀ m : ℕ, s₀ ≠ -m := by
    intro m h
    have := congrArg Complex.re h
    rw [hre] at this
    simp at this
    have : (0 : ℝ) ≤ m := m.cast_nonneg
    linarith
  have hcos0 : Complex.cos (π * s₀ / 2) = 0 := by
    rw [Complex.cos_eq_zero_iff]
    exact ⟨k, by rw [hs₀]; push_cast; ring⟩
  have hsin : Complex.sin (π * s₀ / 2) ≠ 0 := by
    intro h
    have := Complex.sin_sq_add_cos_sq (π * s₀ / 2)
    rw [h, hcos0] at this
    norm_num at this
  have hA : Afun s₀ ≠ 0 := by
    unfold Afun
    have h2pi : (2 * (π : ℂ)) ≠ 0 := by
      have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero two_ne_zero this
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero hnm)
    exact (cpow_ne_zero_iff_of_exponent_ne_zero (by
      intro h; have := congrArg Complex.re h; simp [hre] at this; linarith)).mpr h2pi
  have hz : riemannZeta s₀ ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hre]; linarith)
  have hpi : (π : ℂ) / 2 ≠ 0 := div_ne_zero (by exact_mod_cast Real.pi_ne_zero) two_ne_zero
  have hne : deriv riemannZeta (-2 * k) ≠ 0 := by
    rw [hd.deriv]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hpi hsin) hA) hz
  refine ⟨hne, ?_⟩
  have hm1 : (-2 * k : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have han : AnalyticAt ℂ riemannZeta (-2 * k) := analyticOn_riemannZeta _ hm1
  have hzero : riemannZeta (-2 * k) = 0 := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have := riemannZeta_neg_two_mul_nat_add_one n
    push_cast at this ⊢
    exact this
  have := (ATK.BSDCoefLider.ordem_iff_derivadas han 1).mpr ⟨fun j hj => by
    have : j = 0 := by omega
    subst this
    simpa using hzero, by simpa using hne⟩
  exact_mod_cast this

/-! ## 4. `ξ′/ξ` com a digama -/

/-- **`ξ′/ξ(s) = 1/s + 1/(s−1) − ½ log π + ½ ψ(s/2) + ζ′/ζ(s)`** (`Re s > 0`, `s ≠ 1`, `ζ(s) ≠ 0`). -/
theorem logDeriv_xiE {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    logDeriv xiE s = 1 / s + 1 / (s - 1) - (Real.log π : ℂ) / 2 + digamma (s / 2) / 2 +
      logDeriv riemannZeta s := by
  have hU : IsOpen {z : ℂ | 0 < z.re ∧ z ≠ 1} :=
    (isOpen_lt continuous_const continuous_re).inter isOpen_ne
  have hev : xiE =ᶠ[𝓝 s] fun z => (z * (z - 1) / 2 * Gammaℝ z) * riemannZeta z := by
    filter_upwards [hU.mem_nhds ⟨hs, hs1⟩] with z hz
    exact xiE_eq_fator hz.1 hz.2
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hG0 : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hP : HasDerivAt (fun z : ℂ => z * (z - 1) / 2) ((2 * s - 1) / 2) s := by
    have := ((hasDerivAt_id' s).mul ((hasDerivAt_id' s).sub_const 1)).div_const 2
    convert this using 1
    ring
  have hzd : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs1).hasDerivAt
  have hprod := (hP.mul (hasDerivAt_Gammaℝ hs)).mul hzd
  have hprod2 : HasDerivAt (fun z => (z * (z - 1) / 2 * Gammaℝ z) * riemannZeta z)
      (((2 * s - 1) / 2 * Gammaℝ s + s * (s - 1) / 2 *
        (Gammaℝ s * (-(Real.log π : ℂ) / 2 + digamma (s / 2) / 2))) * riemannZeta s +
        s * (s - 1) / 2 * Gammaℝ s * deriv riemannZeta s) s := hprod
  have hderiv := hev.deriv_eq.trans hprod2.deriv
  rw [logDeriv_apply, hderiv, xiE_eq_fator hs hs1, logDeriv_apply]
  field_simp
  ring

/-! ## 5. Paridade e integração horizontal de `F(z) = ξ(½ + z)` -/

/-- `F(z) = ξ(½ + z)`. -/
noncomputable def F (z : ℂ) : ℂ := xiE (1 / 2 + z)

theorem differentiable_F : Differentiable ℂ F :=
  differentiable_xiE.comp ((differentiable_const _).add differentiable_id)

theorem F_par (z : ℂ) : F (-z) = F z := by
  unfold F; rw [← sub_eq_add_neg, xiE_par]

theorem F_conj (z : ℂ) : F (conj z) = conj (F z) := by
  unfold F
  rw [← xiE_conj]
  congr 1
  simp [map_add, map_ofNat]

/-- **`F^{(n)}(−z) = (−1)ⁿ F^{(n)}(z)`.** -/
theorem iteratedDeriv_F_par (n : ℕ) : ∀ z, iteratedDeriv n F (-z) = (-1) ^ n * iteratedDeriv n F z := by
  induction n with
  | zero => intro z; simp [F_par]
  | succ n ih =>
    intro z
    have hfun : (fun x => iteratedDeriv n F (-x)) = fun x => (-1) ^ n * iteratedDeriv n F x := funext ih
    have h1 : deriv (fun x => iteratedDeriv n F (-x)) z = -deriv (iteratedDeriv n F) (-z) :=
      deriv_comp_neg (iteratedDeriv n F) z
    rw [hfun, deriv_const_mul_field] at h1
    rw [iteratedDeriv_succ]
    linear_combination h1

theorem deriv_F_impar (z : ℂ) : deriv F (-z) = -deriv F z := by
  have := iteratedDeriv_F_par 1 z
  simpa [iteratedDeriv_one] using this

theorem deriv_F_conj (z : ℂ) : deriv F (conj z) = conj (deriv F z) := by
  have hd : HasDerivAt F (deriv F z) z := (differentiable_F z).hasDerivAt
  have h := hd.conj_conj
  have e : (conj ∘ F ∘ conj) = F := by
    funext w
    simp only [Function.comp, F_conj, Complex.conj_conj]
  rw [e] at h
  exact h.deriv

theorem conj_I_mul (t : ℝ) : conj ((t : ℂ) * I) = -((t : ℂ) * I) := by
  simp [map_mul, Complex.conj_ofReal, Complex.conj_I]

/-- **`F(it)` é real.** -/
theorem F_real (t : ℝ) : (F (t * I)).im = 0 := by
  have h : conj (F (t * I)) = F (t * I) := by
    rw [← F_conj, conj_I_mul, F_par]
  exact Complex.conj_eq_iff_im.mp h

/-- **`F′(it)` é imaginário puro.** -/
theorem deriv_F_imag (t : ℝ) : (deriv F (t * I)).re = 0 := by
  have h : conj (deriv F (t * I)) = -deriv F (t * I) := by
    rw [← deriv_F_conj, conj_I_mul, deriv_F_impar]
  have := congrArg Complex.re h
  simp only [Complex.conj_re, Complex.neg_re] at this
  linarith

/-- **`A(−d,t) = A(d,t)`, `B(−d,t) = −B(d,t)`.** -/
theorem simetria_AB (d t : ℝ) :
    (F (-d + t * I)).re = (F (d + t * I)).re ∧ (F (-d + t * I)).im = -(F (d + t * I)).im := by
  have e : (-(d : ℂ) + t * I) = -(conj ((d : ℂ) + t * I)) := by
    simp [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [e, F_par, F_conj]
  simp

theorem hasDerivAt_horizontal (d t v : ℝ) :
    HasDerivAt (fun v : ℝ => F (v * d + t * I)) (deriv F (v * d + t * I) * d) v := by
  have hl : HasDerivAt (fun v : ℝ => ((v : ℂ) * d + t * I)) (d : ℂ) v := by
    have := ((hasDerivAt_id (v : ℂ)).mul_const (d : ℂ)).add_const ((t : ℂ) * I)
    simpa using this.comp_ofReal
  exact (differentiable_F _).hasDerivAt.comp v hl

theorem continuous_deriv_F : Continuous (deriv F) :=
  (differentiableOn_univ.mp (differentiable_F.differentiableOn.deriv isOpen_univ)).continuous

/-- **Integração horizontal**: `F(d+it) − F(it) = d ∫₀¹ F′(vd+it) dv`. -/
theorem horizontal (d t : ℝ) :
    F (d + t * I) - F (t * I) = d * ∫ v in (0 : ℝ)..1, deriv F (v * d + t * I) := by
  have hcont : Continuous fun v : ℝ => deriv F (v * d + t * I) * d :=
    (continuous_deriv_F.comp (by fun_prop)).mul continuous_const
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun v _ => hasDerivAt_horizontal d t v) (hcont.intervalIntegrable 0 1)
  simp only [ofReal_one, one_mul, ofReal_zero, zero_mul, zero_add] at this
  rw [← this, intervalIntegral.integral_mul_const]
  ring

theorem integrable_comp {g : ℂ → ℂ} (hg : Continuous g) (d t : ℝ) :
    IntervalIntegrable (fun v : ℝ => g (v * d + t * I)) volume 0 1 :=
  (hg.comp (by fun_prop)).intervalIntegrable 0 1

/-- **`B(d,t) = d ∫₀¹ Im F′(vd+it) dv`.** -/
theorem B_integral (d t : ℝ) :
    (F (d + t * I)).im = d * ∫ v in (0 : ℝ)..1, (deriv F (v * d + t * I)).im := by
  have h := congrArg Complex.im (horizontal d t)
  rw [Complex.sub_im, F_real, sub_zero] at h
  rw [h]
  have := Complex.imCLM.intervalIntegral_comp_comm (integrable_comp continuous_deriv_F d t)
  simp only [Complex.imCLM_apply] at this
  rw [this]
  simp [Complex.mul_im]

/-- **`A(d,t) = F(it) + d ∫₀¹ Re F′(vd+it) dv`.** -/
theorem A_integral (d t : ℝ) :
    (F (d + t * I)).re = (F (t * I)).re + d * ∫ v in (0 : ℝ)..1, (deriv F (v * d + t * I)).re := by
  have h := congrArg Complex.re (horizontal d t)
  rw [Complex.sub_re] at h
  have := Complex.reCLM.intervalIntegral_comp_comm (integrable_comp continuous_deriv_F d t)
  simp only [Complex.reCLM_apply] at this
  rw [this]
  have e : (F (d + t * I)).re = (F (t * I)).re + ((d : ℂ) * ∫ v in (0 : ℝ)..1, deriv F (v * d + t * I)).re := by
    linarith
  rw [e]
  simp [Complex.mul_re]

/-- **A versão com `Re` é falsa**: para `F = z²`, `d = t = 1`, `Im F(1+i) = 2` mas
`∫₀¹ Re F′(v+i) dv = 1`. -/
theorem contraexemplo_Re :
    (((1 : ℂ) + I) ^ 2).im = 2 ∧ ∫ v in (0 : ℝ)..1, (2 * ((v : ℂ) + I)).re = 1 ∧
      ∫ v in (0 : ℝ)..1, (2 * ((v : ℂ) + I)).im = 2 := by
  refine ⟨by norm_num [sq, Complex.mul_im], ?_, ?_⟩
  · have e : (fun v : ℝ => (2 * ((v : ℂ) + I)).re) = fun v => 2 * v := by
      funext v; simp
    rw [e, intervalIntegral.integral_const_mul, integral_id]; norm_num
  · have e : (fun v : ℝ => (2 * ((v : ℂ) + I)).im) = fun _ => 2 := by
      funext v; simp
    rw [e]; simp

/-- `(∫₀¹ g)² ≤ ∫₀¹ g²` para `g` contínua. -/
theorem sq_integral_le {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ v in (0 : ℝ)..1, g v) ^ 2 ≤ ∫ v in (0 : ℝ)..1, g v ^ 2 := by
  have key : ∀ m : ℝ, ∫ v in (0 : ℝ)..1, (g v - m) ^ 2 =
      (∫ v in (0 : ℝ)..1, g v ^ 2) - 2 * m * (∫ v in (0 : ℝ)..1, g v) + m ^ 2 := by
    intro m
    have hi1 : IntervalIntegrable (fun v => g v ^ 2) volume 0 1 := (hg.pow 2).intervalIntegrable 0 1
    have hi2 : IntervalIntegrable (fun v => -(2 * m) * g v) volume 0 1 :=
      (continuous_const.mul hg).intervalIntegrable 0 1
    have hi3 : IntervalIntegrable (fun _ : ℝ => m ^ 2) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have e1 : (fun v => (g v - m) ^ 2) = fun v => (g v ^ 2 + -(2 * m) * g v) + m ^ 2 := by
      funext v; ring
    rw [e1, intervalIntegral.integral_add (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul, one_mul]
    ring
  have h0 : 0 ≤ ∫ v in (0 : ℝ)..1, (g v - ∫ v in (0 : ℝ)..1, g v) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun v _ => sq_nonneg _
  rw [key] at h0
  nlinarith

/-- **Num zero `F(d+it) = 0`: `F(it)² ≤ d² ∫₀¹ (Re F′(vd+it))² dv`.** -/
theorem zero_cota {d t : ℝ} (h : F (d + t * I) = 0) :
    (F (t * I)).re ^ 2 ≤ d ^ 2 * ∫ v in (0 : ℝ)..1, (deriv F (v * d + t * I)).re ^ 2 := by
  have hA := A_integral d t
  rw [h, Complex.zero_re] at hA
  have hg : Continuous fun v : ℝ => (deriv F (v * d + t * I)).re :=
    Complex.continuous_re.comp (continuous_deriv_F.comp (by fun_prop))
  have hcs := sq_integral_le hg
  have e : (F (t * I)).re = -(d * ∫ v in (0 : ℝ)..1, (deriv F (v * d + t * I)).re) := by linarith
  rw [e, neg_sq, mul_pow]
  exact mul_le_mul_of_nonneg_left hcs (sq_nonneg d)

/-! ## 6. O teste do disco na forma de Jensen -/

open MeromorphicOn in
/-- **Teste do disco**: para `f` analítica em `B̄(c,R)` com `f(c) ≠ 0`, há um zero em `B(c,R)` ⟺
`log|f(c)| <` média de `log|f|` no círculo `|z − c| = R`. -/
theorem disco_jensen {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) :
    (∃ u ∈ ball c R, f u = 0) ↔ Real.log ‖f c‖ < Real.circleAverage (fun z => Real.log ‖f z‖) c R := by
  have habs : |R| = R := abs_of_pos hR
  have hf' : AnalyticOnNhd ℂ f (closedBall c |R|) := by rw [habs]; exact hf
  have jensen := hf'.circleAverage_log_norm hR.ne' hc
  rw [habs] at jensen
  rw [jensen]
  set T : ℂ → ℝ := fun u => (divisor f (closedBall c R) u : ℝ) * Real.log (R * ‖c - u‖⁻¹) with hT
  have hsupp : (Function.support T).Finite :=
    ((divisor f (closedBall c R)).finiteSupport (isCompact_closedBall ..)).subset fun u h => by
      simp only [Function.mem_support, ne_eq, hT] at h ⊢
      intro h'; exact h (by rw [h']; simp)
  have hfin : ∀ u ∈ closedBall c R, analyticOrderAt f u ≠ ⊤ := by
    intro u hu htop
    have hev := analyticOrderAt_eq_top.mp htop
    have := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_closedBall c R).isPreconnected
      hu hev
    exact hc (this (mem_closedBall_self hR.le))
  have hnn : ∀ u, 0 ≤ T u := by
    intro u
    simp only [hT]
    by_cases hu : u ∈ closedBall c R
    · refine mul_nonneg (by exact_mod_cast hf.divisor_nonneg u) ?_
      by_cases huc : u = c
      · rw [huc, sub_self, norm_zero, inv_zero, mul_zero, Real.log_zero]
      · have hpos : 0 < ‖c - u‖ := by rw [norm_pos_iff, sub_ne_zero]; exact fun h => huc h.symm
        have hle : ‖c - u‖ ≤ R := by
          have := mem_closedBall.mp hu
          rwa [dist_eq_norm, norm_sub_rev] at this
        rw [show R * ‖c - u‖⁻¹ = R / ‖c - u‖ by ring]
        exact Real.log_nonneg (by rw [le_div_iff₀ hpos, one_mul]; exact hle)
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]; simp
  constructor
  · rintro ⟨u, hu, hfu⟩
    have hub : u ∈ closedBall c R := ball_subset_closedBall hu
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hfin u hub)
    have hne : analyticOrderAt f u ≠ 0 := (hf u hub).analyticOrderAt_ne_zero.mpr hfu
    have hn0 : n ≠ 0 := by intro h; apply hne; rw [← hn, h]; rfl
    have hd : (1 : ℝ) ≤ (divisor f (closedBall c R) u : ℝ) := by
      rw [hf.divisor_apply hub, ← hn]
      simp only [ENat.map_natCast, WithTop.untop₀_coe]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    have huc : u ≠ c := by rintro rfl; exact hc hfu
    have hpos : 0 < ‖c - u‖ := by rw [norm_pos_iff, sub_ne_zero]; exact fun h => huc h.symm
    have hlt : ‖c - u‖ < R := by
      have := mem_ball.mp hu
      rwa [dist_eq_norm, norm_sub_rev] at this
    have hlog : 0 < Real.log (R * ‖c - u‖⁻¹) := by
      rw [show R * ‖c - u‖⁻¹ = R / ‖c - u‖ by ring]
      exact Real.log_pos (by rw [lt_div_iff₀ hpos, one_mul]; exact hlt)
    have hTu : 0 < T u := by
      simp only [hT]
      nlinarith
    have := single_le_finsum u hsupp hnn
    linarith
  · intro hlt
    by_contra hno
    push Not at hno
    have hzero : ∀ u, T u = 0 := by
      intro u
      simp only [hT]
      by_cases hu : u ∈ closedBall c R
      · by_cases hb : u ∈ ball c R
        · rw [hf.divisor_apply hu, (hf u hu).analyticOrderAt_eq_zero.mpr (hno u hb)]
          simp
        · have hd : ‖c - u‖ = R := by
            have h1 := mem_closedBall.mp hu
            have h2 : ¬ dist u c < R := fun h => hb (mem_ball.mpr h)
            rw [dist_eq_norm, norm_sub_rev] at h1 h2
            linarith [not_lt.mp h2]
          rw [hd, mul_inv_cancel₀ hR.ne', Real.log_one, mul_zero]
      · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]; simp
    have : ∑ᶠ u, T u = 0 := by simp [hzero]
    linarith

/-- **HR ⟺ igualdade de Jensen em todo disco da metade direita** onde `ξ(c) ≠ 0`. -/
theorem rh_iff_disco :
    RiemannHypothesis ↔ ∀ c : ℂ, ∀ R : ℝ, 0 < R → ball c R ⊆ {s : ℂ | 1 / 2 < s.re} → xiE c ≠ 0 →
      Real.circleAverage (fun z => Real.log ‖xiE z‖) c R ≤ Real.log ‖xiE c‖ := by
  have han : ∀ c R, AnalyticOnNhd ℂ xiE (closedBall c R) := fun _ _ z _ => analyticAt_xiE z
  rw [rh_iff_xiE_direita]
  constructor
  · intro h c R hR hsub hc
    by_contra hlt
    push Not at hlt
    obtain ⟨u, hu, hzu⟩ := (disco_jensen hR (han c R) hc).mpr hlt
    exact h u (hsub hu) hzu
  · intro h ρ hρ hzρ
    set δ : ℝ := (ρ.re - 1 / 2) / 3 with hδ
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    have hfreq : ∃ᶠ z in 𝓝 ρ, xiE z ≠ 0 := by
      refine Filter.not_eventually.mp fun hev => xiE_order_ne_top ρ ?_
      rw [analyticOrderAt_eq_top]
      filter_upwards [hev] with z hz
      simpa using hz
    obtain ⟨c, hc0, hcb⟩ := (hfreq.and_eventually (ball_mem_nhds ρ hδ0)).exists
    have hρc : ρ ∈ ball c (2 * δ) := by
      rw [mem_ball, dist_comm]
      have := mem_ball.mp hcb
      linarith
    have hsub : ball c (2 * δ) ⊆ {s : ℂ | 1 / 2 < s.re} := by
      intro w hw
      have h1 := mem_ball.mp hw
      have h2 := mem_ball.mp hcb
      have h3 : dist w ρ < 3 * δ := by
        calc dist w ρ ≤ dist w c + dist c ρ := dist_triangle w c ρ
          _ < 2 * δ + δ := add_lt_add h1 h2
          _ = 3 * δ := by ring
      have h4 : |w.re - ρ.re| < 3 * δ := by
        have := Complex.abs_re_le_norm (w - ρ)
        rw [Complex.sub_re] at this
        rw [dist_eq_norm] at h3
        linarith
      simp only [mem_ofPred_eq]
      have := (abs_lt.mp h4).1
      rw [hδ] at this
      linarith
    have hle := h c (2 * δ) (by linarith) hsub hc0
    have hlt := (disco_jensen (by linarith) (han c (2 * δ)) hc0).mp ⟨ρ, hρc, hzρ⟩
    linarith

/-! ## 7. Critério de sinal (direção suficiente) -/

/-- **Critério de sinal**: num aberto `U` onde `f` é analítica de ordem finita, se `Re(f′/f) > 0` em todo
ponto de `U` fora dos zeros, então `f` não tem zeros em `U` (num zero de ordem `m`,
`Re(f′/f)(z₀ − ε) = −m/ε + O(1) < 0`). -/
theorem sem_zeros_de_sinal {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hfin : ∀ z ∈ U, analyticOrderAt f z ≠ ⊤)
    (hpos : ∀ z ∈ U, f z ≠ 0 → 0 < (logDeriv f z).re) : ∀ z ∈ U, f z ≠ 0 := by
  intro z₀ hz₀ hzero
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hfin z₀ hz₀)
  have hne : analyticOrderAt f z₀ ≠ 0 := (hf z₀ hz₀).analyticOrderAt_ne_zero.mpr hzero
  have hm0 : m ≠ 0 := by intro h; apply hne; rw [← hm, h]; rfl
  obtain ⟨g, hg, hg0, hev⟩ := (hf z₀ hz₀).analyticOrderAt_eq_natCast.mp hm.symm
  have hgan := hg.eventually_analyticAt
  have hgne := hg.continuousAt.eventually_ne hg0
  have hall : ∀ᶠ z in 𝓝 z₀, z ∈ U ∧ (f z = (z - z₀) ^ m • g z) ∧ AnalyticAt ℂ g z ∧ g z ≠ 0 :=
    (show ∀ᶠ z in 𝓝 z₀, z ∈ U from hU.mem_nhds hz₀).and (hev.and (hgan.and hgne))
  obtain ⟨V, hVsub, hVo, hz₀V⟩ := _root_.eventually_nhds_iff.mp hall
  -- `f′/f = m/(z − z₀) + g′/g` em `V \ {z₀}`
  have hld : ∀ z ∈ V, z ≠ z₀ → logDeriv f z = (m : ℂ) / (z - z₀) + logDeriv g z ∧ f z ≠ 0 := by
    intro z hz hzz
    obtain ⟨-, -, hga, hgz⟩ := hVsub z hz
    have hfe : f =ᶠ[𝓝 z] fun w => (w - z₀) ^ m * g w := by
      filter_upwards [hVo.mem_nhds hz] with w hw
      rw [(hVsub w hw).2.1, smul_eq_mul]
    have hd := ATK.ClosedMath.logDeriv_ordem m hga.differentiableAt.hasDerivAt hzz hgz
    have hfz : f z = (z - z₀) ^ m * g z := by rw [(hVsub z hz).2.1, smul_eq_mul]
    have hzz' : z - z₀ ≠ 0 := sub_ne_zero.mpr hzz
    have hfz0 : f z ≠ 0 := by rw [hfz]; exact mul_ne_zero (pow_ne_zero _ hzz') hgz
    refine ⟨?_, hfz0⟩
    rw [logDeriv_apply, hfe.deriv_eq, hd.deriv, hfz, logDeriv_apply]
    field_simp
  -- o limite `ε → 0⁺` ao longo de `z₀ − ε`
  have hmov : Tendsto (fun ε : ℝ => z₀ - (ε : ℂ)) (𝓝[>] 0) (𝓝 z₀) := by
    have : Continuous fun ε : ℝ => z₀ - (ε : ℂ) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hlg : ContinuousAt (fun z => (logDeriv g z).re) z₀ := by
    have h1 : ContinuousAt (deriv g) z₀ := hg.deriv.continuousAt
    have h2 : ContinuousAt (fun z => deriv g z / g z) z₀ := h1.div hg.continuousAt hg0
    exact Complex.continuous_re.continuousAt.comp h2
  have hT1 : Tendsto (fun ε : ℝ => (logDeriv g (z₀ - ε)).re) (𝓝[>] 0) (𝓝 (logDeriv g z₀).re) :=
    hlg.tendsto.comp hmov
  have hT2 : Tendsto (fun ε : ℝ => -(m : ℝ) / ε) (𝓝[>] 0) atBot := by
    have hm1 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    have := (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hm1
    have h2 := Filter.tendsto_neg_atTop_atBot.comp this
    refine h2.congr fun ε => ?_
    simp only [Function.comp]
    ring
  have hT := hT2.atBot_add hT1
  have hev1 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), -(m : ℝ) / ε + (logDeriv g (z₀ - (ε : ℂ))).re < 0 :=
    hT.eventually (eventually_lt_atBot 0)
  have hev2 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), z₀ - (ε : ℂ) ∈ V := hmov.eventually (hVo.mem_nhds hz₀V)
  have hev3 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, h1, h2, h3⟩ := (hev1.and (hev2.and hev3)).exists
  have hzz : z₀ - (ε : ℂ) ≠ z₀ := by
    intro h
    have : (ε : ℂ) = 0 := by linear_combination -h
    exact h3.ne' (by exact_mod_cast this)
  obtain ⟨hl, hf0⟩ := hld _ h2 hzz
  have hp := hpos _ (hVsub _ h2).1 hf0
  rw [hl, Complex.add_re] at hp
  have e : ((m : ℂ) / (z₀ - (ε : ℂ) - z₀)).re = -(m : ℝ) / ε := by
    rw [show z₀ - (ε : ℂ) - z₀ = ((-ε : ℝ) : ℂ) by push_cast; ring]
    rw [show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_div, Complex.ofReal_re]
    ring
  rw [e] at hp
  linarith

/-- **`Re ξ′/ξ > 0` em `Re s > ½` (fora dos zeros) ⇒ HR.** -/
theorem rh_de_sinal (h : ∀ s : ℂ, 1 / 2 < s.re → xiE s ≠ 0 → 0 < (logDeriv xiE s).re) :
    RiemannHypothesis := by
  rw [rh_iff_xiE_direita]
  exact sem_zeros_de_sinal (isOpen_lt continuous_const continuous_re)
    (fun z _ => analyticAt_xiE z) (fun z _ => xiE_order_ne_top z) h

/-! ## 8. Energia finita (parte (d) da identidade de Green) -/

/-- `H = 24 Σ m_ρ (Re ρ − ½)²` para uma lista finita de zeros com multiplicidades. -/
noncomputable def energia (S : Finset ℂ) (m : ℂ → ℕ) : ℝ :=
  24 * ∑ ρ ∈ S, (m ρ : ℝ) * (ρ.re - 1 / 2) ^ 2

theorem energia_nonneg (S : Finset ℂ) (m : ℂ → ℕ) : 0 ≤ energia S m := by
  unfold energia
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun ρ _ => by positivity)

theorem energia_eq_zero_iff (S : Finset ℂ) (m : ℂ → ℕ) (hm : ∀ ρ ∈ S, 1 ≤ m ρ) :
    energia S m = 0 ↔ ∀ ρ ∈ S, ρ.re = 1 / 2 := by
  unfold energia
  rw [mul_eq_zero, or_iff_right (by norm_num : (24 : ℝ) ≠ 0),
    Finset.sum_eq_zero_iff_of_nonneg (fun ρ _ => by positivity)]
  refine forall₂_congr fun ρ hρ => ?_
  have hm1 : (0 : ℝ) < m ρ := by exact_mod_cast hm ρ hρ
  rw [mul_eq_zero, or_iff_right hm1.ne', pow_eq_zero_iff two_ne_zero, sub_eq_zero]

theorem energia_termo (S : Finset ℂ) (m : ℂ → ℕ) {ρ : ℂ} (hρ : ρ ∈ S) :
    24 * ((m ρ : ℝ) * (ρ.re - 1 / 2) ^ 2) ≤ energia S m := by
  unfold energia
  have := Finset.single_le_sum (f := fun ρ => (m ρ : ℝ) * (ρ.re - 1 / 2) ^ 2)
    (fun ρ _ => by positivity) hρ
  linarith

/-- **Cada zero tem `|Re ρ − ½| ≤ √(H/(24 m_ρ))`.** -/
theorem energia_cota (S : Finset ℂ) (m : ℂ → ℕ) (hm : ∀ ρ ∈ S, 1 ≤ m ρ) {ρ : ℂ} (hρ : ρ ∈ S) :
    |ρ.re - 1 / 2| ≤ Real.sqrt (energia S m / (24 * m ρ)) := by
  have hm1 : (0 : ℝ) < m ρ := by exact_mod_cast hm ρ hρ
  have ht := energia_termo S m hρ
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs, le_div_iff₀ (by positivity)]
  linarith

/-- **Se `H < 24δ²`, nenhum zero tem `|Re ρ − ½| ≥ δ`.** -/
theorem energia_exclui (S : Finset ℂ) (m : ℂ → ℕ) (hm : ∀ ρ ∈ S, 1 ≤ m ρ) {δ : ℝ} (hδ : 0 < δ)
    (hH : energia S m < 24 * δ ^ 2) : ∀ ρ ∈ S, |ρ.re - 1 / 2| < δ := by
  intro ρ hρ
  have hm1 : (1 : ℝ) ≤ m ρ := by exact_mod_cast hm ρ hρ
  have ht := energia_termo S m hρ
  have h2 : (ρ.re - 1 / 2) ^ 2 < δ ^ 2 := by nlinarith [sq_nonneg (ρ.re - 1 / 2)]
  exact abs_lt_of_sq_lt_sq h2 hδ.le

/-! ## 9. O fator Γ em `K_n` -/

/-- **`∃ A > 0, ∀ s ∈ K_n, A |ζ(s)| ≤ |ξ(s)|`** (`n ≥ 5`). -/
theorem fator_gamma_Kn (n : ℕ) (hn : 5 ≤ n) :
    ∃ A > 0, ∀ s ∈ ATK.ClosedMath.Terminal.Kn n, A * ‖riemannZeta s‖ ≤ ‖ATK.ClosedMath.xi s‖ := by
  set u : ℂ → ℂ := fun z => z * (z - 1) / 2 * Gammaℝ z with hu
  have hK := ATK.ClosedMath.Terminal.Kn_compacto n
  have hsub := ATK.ClosedMath.Terminal.Kn_sub hn
  have hre : ∀ z ∈ ATK.ClosedMath.Terminal.Kn n, 0 < z.re ∧ z ≠ 1 := by
    intro z hz
    have := hsub hz
    refine ⟨by linarith [this.1], ?_⟩
    rintro rfl
    simp [ATK.ClosedMath.Terminal.Splus] at this
  have hcont : ContinuousOn (fun z => ‖u z‖) (ATK.ClosedMath.Terminal.Kn n) := by
    intro z hz
    have h1 : ContinuousAt u z := (analyticAt_fator (hre z hz).1).continuousAt
    exact h1.norm.continuousWithinAt
  have hpos : ∀ z ∈ ATK.ClosedMath.Terminal.Kn n, 0 < ‖u z‖ := by
    intro z hz
    obtain ⟨h0, h1⟩ := hre z hz
    have hz0 : z ≠ 0 := by rintro rfl; simp at h0
    rw [norm_pos_iff]
    exact mul_ne_zero (div_ne_zero (mul_ne_zero hz0 (sub_ne_zero.mpr h1)) two_ne_zero)
      (Gammaℝ_ne_zero_of_re_pos h0)
  rcases (ATK.ClosedMath.Terminal.Kn n).eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun s hs => by rw [he] at hs; exact absurd hs (Set.notMem_empty s)⟩
  · obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne hcont
    refine ⟨‖u z₀‖, hpos z₀ hz₀, fun s hs => ?_⟩
    obtain ⟨h0, h1⟩ := hre s hs
    have hs0 : s ≠ 0 := by rintro rfl; simp at h0
    have hxi : ATK.ClosedMath.xi s = u s * riemannZeta s := by
      rw [← ATK.ClosedMath.Jensen.xiE_eq_xi hs0 h1, xiE_eq_fator h0 h1]
    have hm : ‖u z₀‖ ≤ ‖u s‖ := hmin hs
    rw [hxi]
    calc ‖u z₀‖ * ‖riemannZeta s‖ ≤ ‖u s‖ * ‖riemannZeta s‖ :=
          mul_le_mul_of_nonneg_right hm (norm_nonneg _)
      _ = ‖u s * riemannZeta s‖ := (norm_mul _ _).symm

end ATK.XiAnalitica

-- Auditoria de axiomas (kernel)
#print axioms ATK.XiAnalitica.xiE_eq_riemannXi
#print axioms ATK.XiAnalitica.differentiable_xiE
#print axioms ATK.XiAnalitica.analyticAt_xiE
#print axioms ATK.XiAnalitica.xiE_conj
#print axioms ATK.XiAnalitica.xiE_order_ne_top
#print axioms ATK.XiAnalitica.log_norm_xiE_harmonica
#print axioms ATK.XiAnalitica.rh_iff_xiE_direita
#print axioms ATK.XiAnalitica.xiE_eq_fator
#print axioms ATK.XiAnalitica.hasDerivAt_Gammaℝ
#print axioms ATK.XiAnalitica.analyticAt_fator
#print axioms ATK.XiAnalitica.ordem_xiE_eq_zeta
#print axioms ATK.XiAnalitica.deriv_zeta_trivial
#print axioms ATK.XiAnalitica.zeros_triviais_simples
#print axioms ATK.XiAnalitica.logDeriv_xiE
#print axioms ATK.XiAnalitica.differentiable_F
#print axioms ATK.XiAnalitica.F_par
#print axioms ATK.XiAnalitica.F_conj
#print axioms ATK.XiAnalitica.iteratedDeriv_F_par
#print axioms ATK.XiAnalitica.deriv_F_impar
#print axioms ATK.XiAnalitica.deriv_F_conj
#print axioms ATK.XiAnalitica.conj_I_mul
#print axioms ATK.XiAnalitica.F_real
#print axioms ATK.XiAnalitica.deriv_F_imag
#print axioms ATK.XiAnalitica.simetria_AB
#print axioms ATK.XiAnalitica.hasDerivAt_horizontal
#print axioms ATK.XiAnalitica.continuous_deriv_F
#print axioms ATK.XiAnalitica.horizontal
#print axioms ATK.XiAnalitica.integrable_comp
#print axioms ATK.XiAnalitica.B_integral
#print axioms ATK.XiAnalitica.A_integral
#print axioms ATK.XiAnalitica.contraexemplo_Re
#print axioms ATK.XiAnalitica.sq_integral_le
#print axioms ATK.XiAnalitica.zero_cota
#print axioms ATK.XiAnalitica.disco_jensen
#print axioms ATK.XiAnalitica.rh_iff_disco
#print axioms ATK.XiAnalitica.sem_zeros_de_sinal
#print axioms ATK.XiAnalitica.rh_de_sinal
#print axioms ATK.XiAnalitica.energia_nonneg
#print axioms ATK.XiAnalitica.energia_eq_zero_iff
#print axioms ATK.XiAnalitica.energia_termo
#print axioms ATK.XiAnalitica.energia_cota
#print axioms ATK.XiAnalitica.energia_exclui
#print axioms ATK.XiAnalitica.fator_gamma_Kn
