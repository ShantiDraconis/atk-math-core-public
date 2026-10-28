import ATK.ZeroClasses.Unilateral

/-!
# `Ω±(√x)` para `ψ(x) − x` e `M(x)`, e zeros simples sob a cota de Mertens fraca (rodada 88)

A rodada 58 (`OmegaPsi`) provou `ψ(x) − x ≠ o(√x)` e `M(x) ≠ o(√x)`; a rodada 87 (`Unilateral`) deu `Ω±(x^θ)` para
`θ < Θ`. Aqui, na escala `√x`, com constante e **dos dois lados** (Schmidt 1903; Landau; Ingham):

* **`psi_omega_mais_raiz`**, **`psi_omega_menos_raiz`**: existe `c > 0` com `ψ(N) − N > c√(N + 1) + K` e
  `ψ(N) − N < −c√(N + 1) − K` infinitas vezes, para todo `K` (`c = 1/(8|ρ₀|)`, `ρ₀` um zero de Hardy);
* **`mertens_omega_mais_raiz`**, **`mertens_omega_menos_raiz`**: o mesmo para `M(x)`;
* **`simples_of_mertens_le`**, **`simples_of_mertens_ge`**, **`rh_e_simples_of_mertens_le`**: a cota de Mertens
  fraca **de um lado só**, `M(N) ≤ A√(N + 1) + K`, implica RH e que todo zero `½ + iγ` é simples
  (`analyticOrderAt ζ₁ ρ = 1`).

O instrumento é **`cota_polo`**. Suponha `a(N) ≤ c(N + 1)^{1/2} + K` e que `GA a = H` tenha o polo
`(σ − ½)|H(σ + iγ)| ≥ L`. Então `L ≤ |½ + iγ| · c√2`. A prova:
* a extensão `Gext` da rodada 87 coincide com `H` em `Re s > ½` (`Gext_eq_H`);
* para `f ≥ 0`, `|Ik f 0 (σ + iγ)| ≤ Ik f 0 σ` (`norm_Ik_le`);
* `(σ − ½) Ik f 0 σ → c√2`, porque `H` é holomorfa em `½` (`ζ(½) ≠ 0`).

Os polos vêm da rodada 58 (`cota_inf_H`, `cota_inf_F`). Para multiplicidade `≥ 2`, `(σ − ½)|1/ζ| → ∞`
(`cota_inf_F_dupla`).

Classificação (rodada 88): **consequência** (incondicional: `Ω±(√x)`) e **reformulação parcial** (a cota de Mertens
fraca de um lado só ⟹ RH + zeros simples; a recíproca não é conhecida). `ψ(x) − x = Ω±(√x log log log x)`
(Littlewood) continua BUILD_PENDING; RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric MeasureTheory
open scoped Real

namespace ATK.ZeroClasses.OmegaRaiz

open ATK.ZeroClasses.Unilateral (Ik IntAcima fUni Al Al_nonneg pos_uni intAcima_uni Gext Gext_eq
  measurable_fUni differentiableAt_Ik Ik_real norm_integrando re_gt_of_mem_ball abs_E_le abs_M_le GA_E_eq
  GA_M_eq GA_neg zeta₁_ne_zero_bola differentiableOn_Hf differentiableOn_F semZeros_of_psi_le
  semZeros_of_psi_ge semZeros_of_mertens_le semZeros_of_mertens_ge)
open ATK.ZeroClasses.VonKoch (GA E)
open ATK.ZeroClasses.VonKochRH (Hf)
open ATK.ZeroClasses.QuasiRH (SemZeros differentiableAt_Hf differentiableAt_F)
open ATK.ZeroClasses.Mertens (M)
open ATK.RHLogZeta (F zeta₁_eq)
open ATK.ZeroClasses.Omega (cota_inf_H cota_inf_F fatora caminho sub_caminho)

/-! ## 1. A extensão explícita é holomorfa e coincide com `H` em `Re s > θ` -/

theorem differentiableAt_Gext {a : ℕ → ℝ} {C A K θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hC : ∀ N : ℕ, |a N| ≤ C * ((N : ℝ) + 1)) (hA : ∀ N : ℕ, a N ≤ A * ((N : ℝ) + 1) ^ θ + K)
    {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H (ball (2 : ℂ) (2 - θ)))
    (hHG : ∀ s : ℂ, 1 < s.re → GA a s = H s) {s : ℂ} (hs : θ < s.re) :
    DifferentiableAt ℂ (Gext a A K θ) s := by
  have hIθ := intAcima_uni hθ hθ1 hC hA hH hHG
  have hf := measurable_fUni a (Al A θ) K θ
  have hsθ : s - θ ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp only [sub_re, ofReal_re, zero_re] at this
    linarith
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  have d1 : DifferentiableAt ℂ (fun w : ℂ => (Al A θ : ℂ) / (w - θ)) s :=
    (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) hsθ
  have d2 : DifferentiableAt ℂ (fun w : ℂ => (K : ℂ) / w) s :=
    (differentiableAt_const _).div differentiableAt_id hs0
  exact differentiableAt_id.mul ((d1.add d2).sub (differentiableAt_Ik hf hIθ hs))

theorem Gext_eq_H {a : ℕ → ℝ} {C A K θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hC : ∀ N : ℕ, |a N| ≤ C * ((N : ℝ) + 1)) (hA : ∀ N : ℕ, a N ≤ A * ((N : ℝ) + 1) ^ θ + K)
    {H : ℂ → ℂ} (hHa : ∀ s : ℂ, θ < s.re → DifferentiableAt ℂ H s)
    (hHG : ∀ s : ℂ, 1 < s.re → GA a s = H s) {s : ℂ} (hs : θ < s.re) : Gext a A K θ s = H s := by
  have hH : DifferentiableOn ℂ H (ball (2 : ℂ) (2 - θ)) := fun w hw =>
    (hHa w (re_gt_of_mem_ball hw)).differentiableWithinAt
  have hV : IsOpen {w : ℂ | θ < w.re} := isOpen_lt continuous_const continuous_re
  have hA1 : AnalyticOnNhd ℂ (Gext a A K θ) {w : ℂ | θ < w.re} :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (differentiableAt_Gext hθ hθ1 hC hA hH hHG hw).differentiableWithinAt) hV
  have hA2 : AnalyticOnNhd ℂ H {w : ℂ | θ < w.re} :=
    DifferentiableOn.analyticOnNhd (fun w hw => (hHa w hw).differentiableWithinAt) hV
  have hev : Gext a A K θ =ᶠ[𝓝 (2 : ℂ)] H := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with w hw
    exact (Gext_eq hθ1.le hC hw).trans (hHG w hw)
  have h2V : (2 : ℂ) ∈ {w : ℂ | θ < w.re} := by
    show θ < (2 : ℂ).re
    norm_num; linarith
  exact hA1.eqOn_of_preconnected_of_eventuallyEq hA2 (convex_halfSpace_re_gt θ).isPreconnected h2V hev hs

/-! ## 2. `|Ik f 0 s| ≤ Ik f 0 (Re s)` para `f ≥ 0` -/

theorem norm_Ik_le {f : ℝ → ℝ} {θ : ℝ} (hpos : ∀ x : ℝ, 1 < x → 0 ≤ f x) (h : IntAcima f θ)
    {s : ℂ} (hs : θ < s.re) : ‖Ik f 0 s‖ ≤ ∫ x in Ioi 1, x ^ (-s.re - 1) * f x := by
  unfold Ik
  refine norm_integral_le_of_norm_le ?_ ?_
  · refine (h s.re hs).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [abs_of_nonneg (hpos x hx)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_integrando 0 hx, pow_zero, one_mul, abs_of_nonneg (hpos x hx)]

theorem Ik_real0 (f : ℝ → ℝ) (σ : ℝ) : Ik f 0 σ = ((∫ x in Ioi 1, x ^ (-σ - 1) * f x : ℝ) : ℂ) := by
  rw [Ik_real]
  simp only [pow_zero, one_mul]

/-! ## 3. A cota no polo -/

/-- **A cota no polo**: se `a(N) ≤ c(N + 1)^{1/2} + K`, `GA a = H` com `H` holomorfa em `Re s > ½` e em `½`, e
`(σ − ½)|H(σ + iγ)| ≥ L` perto de `½⁺` (`γ ≠ 0`), então `L ≤ |½ + iγ| · A′`, `A′ = max(c, 0)√2`. A prova:
`H = Gext` em `Re s > ½`, `|Ik f 0 (σ + iγ)| ≤ Ik f 0 σ` (`f ≥ 0`), e `(σ − ½) Ik f 0 σ → A′`. -/
theorem cota_polo {a : ℕ → ℝ} {C c K : ℝ} (hC : ∀ N : ℕ, |a N| ≤ C * ((N : ℝ) + 1))
    (hA : ∀ N : ℕ, a N ≤ c * ((N : ℝ) + 1) ^ (1 / 2 : ℝ) + K) {H : ℂ → ℂ}
    (hHa : ∀ s : ℂ, 1 / 2 < s.re → DifferentiableAt ℂ H s) (hH0 : DifferentiableAt ℂ H ((1 / 2 : ℝ) : ℂ))
    (hHG : ∀ s : ℂ, 1 < s.re → GA a s = H s) {γ L : ℝ} (hγ : γ ≠ 0)
    (hL : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), L ≤ (σ - 1 / 2) * ‖H ((σ : ℂ) + γ * I)‖) :
    L ≤ ‖(1 / 2 : ℂ) + γ * I‖ * Al c (1 / 2) := by
  set A' := Al c (1 / 2) with hA'
  set f := fUni a A' K (1 / 2) with hfdef
  have hθ : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hθ1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hH : DifferentiableOn ℂ H (ball (2 : ℂ) (2 - 1 / 2)) := fun w hw =>
    (hHa w (re_gt_of_mem_ball hw)).differentiableWithinAt
  have hIθ : IntAcima f (1 / 2) := intAcima_uni hθ hθ1 hC hA hH hHG
  have hpos : ∀ x : ℝ, 1 < x → 0 ≤ f x := fun x hx => pos_uni hθ hA hx
  have hA0 : 0 ≤ A' := Al_nonneg c (1 / 2)
  have hγ0 : 0 < |γ| := abs_pos.mpr hγ
  set φ : ℝ → ℝ := fun σ => (σ - 1 / 2) * ‖(σ : ℂ) + γ * I‖ * (A' / |γ|) + (σ - 1 / 2) * |K| +
    ‖(σ : ℂ) + γ * I‖ * (A' + (σ - 1 / 2) * (K / σ - (H σ).re / σ)) with hφ
  have hbd : ∀ σ : ℝ, 1 / 2 < σ → (σ - 1 / 2) * ‖H ((σ : ℂ) + γ * I)‖ ≤ φ σ := by
    intro σ hσ
    set s : ℂ := (σ : ℂ) + γ * I with hsdef
    have hsre : s.re = σ := by simp [hsdef]
    have hsim : s.im = γ := by simp [hsdef]
    have hs : 1 / 2 < s.re := by rw [hsre]; exact hσ
    have hσ' : 1 / 2 < (σ : ℂ).re := by simpa using hσ
    have hGs : H s = Gext a c K (1 / 2) s := (Gext_eq_H hθ hθ1 hC hA hHa hHG hs).symm
    have hGσ : H σ = Gext a c K (1 / 2) σ := (Gext_eq_H hθ hθ1 hC hA hHa hHG hσ').symm
    have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (show σ ≠ 0 by linarith)
    have hσh : (σ : ℂ) - ((1 / 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (show σ - 1 / 2 ≠ 0 by linarith)
    have hIσ : Ik f 0 σ = ((A' / (σ - 1 / 2) + K / σ : ℝ) : ℂ) - ((1 / σ : ℝ) : ℂ) * H σ := by
      rw [hGσ]
      unfold Gext
      rw [← hA', ← hfdef]
      push_cast
      field_simp
      ring
    have hJ : (∫ x in Ioi 1, x ^ (-σ - 1) * f x) = A' / (σ - 1 / 2) + K / σ - (1 / σ) * (H σ).re := by
      have := congrArg Complex.re hIσ
      rw [Ik_real0, ofReal_re, sub_re, ofReal_re, re_ofReal_mul] at this
      exact this
    have hIk : ‖Ik f 0 s‖ ≤ ∫ x in Ioi 1, x ^ (-σ - 1) * f x := by
      have := norm_Ik_le hpos hIθ hs
      rwa [hsre] at this
    have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
    have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
    have hsh : |γ| ≤ ‖s - ((1 / 2 : ℝ) : ℂ)‖ := by
      have := abs_im_le_norm (s - ((1 / 2 : ℝ) : ℂ))
      rwa [sub_im, ofReal_im, sub_zero, hsim] at this
    have h1 : ‖(A' : ℂ) / (s - ((1 / 2 : ℝ) : ℂ))‖ ≤ A' / |γ| := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0]
      exact div_le_div_of_nonneg_left hA0 hγ0 hsh
    have h2 : ‖s‖ * ‖(K : ℂ) / s‖ = |K| := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
      field_simp
    have hHs : ‖H s‖ ≤ ‖s‖ * (A' / |γ|) + |K| + ‖s‖ * ∫ x in Ioi 1, x ^ (-σ - 1) * f x := by
      rw [hGs]
      unfold Gext
      rw [← hA', ← hfdef, norm_mul]
      calc ‖s‖ * ‖(A' : ℂ) / (s - ((1 / 2 : ℝ) : ℂ)) + (K : ℂ) / s - Ik f 0 s‖
          ≤ ‖s‖ * (‖(A' : ℂ) / (s - ((1 / 2 : ℝ) : ℂ))‖ + ‖(K : ℂ) / s‖ + ‖Ik f 0 s‖) := by
            gcongr
            exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
        _ = ‖s‖ * ‖(A' : ℂ) / (s - ((1 / 2 : ℝ) : ℂ))‖ + ‖s‖ * ‖(K : ℂ) / s‖ + ‖s‖ * ‖Ik f 0 s‖ := by ring
        _ ≤ ‖s‖ * (A' / |γ|) + |K| + ‖s‖ * ∫ x in Ioi 1, x ^ (-σ - 1) * f x := by
            rw [h2]
            gcongr
    have hpos' : 0 < σ - 1 / 2 := by linarith
    calc (σ - 1 / 2) * ‖H s‖
        ≤ (σ - 1 / 2) * (‖s‖ * (A' / |γ|) + |K| + ‖s‖ * ∫ x in Ioi 1, x ^ (-σ - 1) * f x) :=
          mul_le_mul_of_nonneg_left hHs hpos'.le
      _ = φ σ := by
          have hk : (σ - 1 / 2) * (A' / (σ - 1 / 2)) = A' := mul_div_cancel₀ A' hpos'.ne'
          rw [hJ, hφ]
          simp only
          rw [← hsdef]
          linear_combination ‖s‖ * hk
  have hHc : ContinuousAt (fun σ : ℝ => (H σ).re) (1 / 2) :=
    Complex.continuous_re.continuousAt.comp (hH0.continuousAt.comp continuous_ofReal.continuousAt)
  have hn : Continuous fun σ : ℝ => ‖(σ : ℂ) + γ * I‖ := by fun_prop
  have hφc : ContinuousAt φ (1 / 2) := by
    have e1 : ContinuousAt (fun σ : ℝ => σ - 1 / 2) (1 / 2) := continuousAt_id.sub continuousAt_const
    have e2 : ContinuousAt (fun σ : ℝ => K / σ - (H σ).re / σ) (1 / 2) :=
      (continuousAt_const.div continuousAt_id (by norm_num)).sub (hHc.div continuousAt_id (by norm_num))
    exact (((e1.mul hn.continuousAt).mul continuousAt_const).add (e1.mul continuousAt_const)).add
      (hn.continuousAt.mul (continuousAt_const.add (e1.mul e2)))
  have hlim : Tendsto φ (𝓝[>] (1 / 2)) (𝓝 (φ (1 / 2))) := hφc.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), L ≤ φ σ := by
    filter_upwards [hL, self_mem_nhdsWithin] with σ h1 h2
    exact h1.trans (hbd σ h2)
  have hge := ge_of_tendsto hlim hev
  have hφ0 : φ (1 / 2) = ‖(1 / 2 : ℂ) + γ * I‖ * A' := by
    rw [hφ]
    simp only [sub_self, zero_mul, zero_add, add_zero]
    push_cast
    ring
  rw [hφ0] at hge
  exact hge

/-! ## 4. `Ω±(√x)` com constante -/

theorem differentiableAt_Hf_meio : DifferentiableAt ℂ Hf ((1 / 2 : ℝ) : ℂ) := by
  have h : ((1 / 2 : ℝ) : ℂ) ∈ ball (2 : ℂ) (2 - 0) := by
    rw [mem_ball, dist_eq]
    norm_num
  exact (differentiableOn_Hf (le_refl 0)).differentiableAt (isOpen_ball.mem_nhds h)

theorem differentiableAt_F_meio : DifferentiableAt ℂ F ((1 / 2 : ℝ) : ℂ) := by
  have h : ((1 / 2 : ℝ) : ℂ) ∈ ball (2 : ℂ) (2 - 0) := by
    rw [mem_ball, dist_eq]
    norm_num
  exact (differentiableOn_F (le_refl 0)).differentiableAt (isOpen_ball.mem_nhds h)

theorem existe_zero : ∃ γ : ℝ, 0 < γ ∧ riemannZeta ((1 / 2 : ℂ) + γ * I) = 0 := by
  obtain ⟨t, ht, hz⟩ := ATK.ZeroClasses.Hardy.existe_zero_acima 0
  exact ⟨t, ht, hz⟩

theorem norm_rho_pos (γ : ℝ) : 0 < ‖(1 / 2 : ℂ) + γ * I‖ :=
  norm_pos_iff.mpr fun h => by
    have := congrArg Complex.re h
    norm_num at this

theorem Al_meio {c : ℝ} (hc : 0 ≤ c) : Al c (1 / 2) = c * √2 := by
  unfold Al
  rw [max_eq_left hc, Real.sqrt_eq_rpow]

theorem sqrt_dois_lt : √2 < 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

theorem contra_raiz {L c ρn : ℝ} (hL : 0 < L) (hρ : 0 < ρn) (hc : c = L / (4 * ρn))
    (key : L ≤ ρn * (c * √2)) : False := by
  rw [hc] at key
  have e : ρn * (L / (4 * ρn) * √2) = L * √2 / 4 := by field_simp
  rw [e] at key
  nlinarith [sqrt_dois_lt]

/-- **`ψ(x) − x = Ω₊(√x)`**: existe `c > 0` tal que `ψ(N) − N > c√(N + 1) + K` infinitas vezes, para todo `K`
(Schmidt 1903). Com `ρ₀ = ½ + iγ₀` um zero de Hardy, serve `c = 1/(8|ρ₀|)`. -/
theorem psi_omega_mais_raiz : ∃ c : ℝ, 0 < c ∧ ∀ K : ℝ, ∃ N : ℕ,
    c * √((N : ℝ) + 1) + K < Chebyshev.psi N - N := by
  obtain ⟨γ, hγ, hz⟩ := existe_zero
  have hρ := norm_rho_pos γ
  set c : ℝ := (1 / 2) / (4 * ‖(1 / 2 : ℂ) + γ * I‖) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c, hc0, fun K => ?_⟩
  by_contra hne
  push Not at hne
  have hA : ∀ N : ℕ, E N ≤ c * ((N : ℝ) + 1) ^ (1 / 2 : ℝ) + K := fun N => by
    rw [← Real.sqrt_eq_rpow]; exact hne N
  have hZ : SemZeros (1 / 2) := semZeros_of_psi_le (by norm_num) (by norm_num) hA
  have key := cota_polo abs_E_le hA (fun s hs => differentiableAt_Hf hZ hs) differentiableAt_Hf_meio
    (fun s hs => GA_E_eq hs) hγ.ne' (cota_inf_H hz)
  rw [Al_meio hc0.le] at key
  exact contra_raiz (by norm_num) hρ hc key

/-- **`ψ(x) − x = Ω₋(√x)`**. -/
theorem psi_omega_menos_raiz : ∃ c : ℝ, 0 < c ∧ ∀ K : ℝ, ∃ N : ℕ,
    Chebyshev.psi N - N < -(c * √((N : ℝ) + 1)) - K := by
  obtain ⟨γ, hγ, hz⟩ := existe_zero
  have hρ := norm_rho_pos γ
  set c : ℝ := (1 / 2) / (4 * ‖(1 / 2 : ℂ) + γ * I‖) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c, hc0, fun K => ?_⟩
  by_contra hne
  push Not at hne
  have hA : ∀ N : ℕ, (fun N => -E N) N ≤ c * ((N : ℝ) + 1) ^ (1 / 2 : ℝ) + K := fun N => by
    show -E N ≤ _
    rw [← Real.sqrt_eq_rpow]
    have := hne N
    unfold E
    linarith
  have hZ : SemZeros (1 / 2) := semZeros_of_psi_ge (A := c) (K := K) (by norm_num) (by norm_num)
    (fun N => by rw [← Real.sqrt_eq_rpow]; exact hne N)
  have key := cota_polo (a := fun N => -E N) (H := fun s => -Hf s)
    (fun N => by rw [abs_neg]; exact abs_E_le N) hA (fun s hs => (differentiableAt_Hf hZ hs).neg)
    differentiableAt_Hf_meio.neg (fun s hs => by rw [GA_neg, GA_E_eq hs]) hγ.ne'
    (by simpa only [norm_neg] using cota_inf_H hz)
  rw [Al_meio hc0.le] at key
  exact contra_raiz (by norm_num) hρ hc key

/-- **`M(x) = Ω₊(√x)`**. -/
theorem mertens_omega_mais_raiz : ∃ c : ℝ, 0 < c ∧ ∀ K : ℝ, ∃ N : ℕ, c * √((N : ℝ) + 1) + K < M N := by
  obtain ⟨γ, hγ, hz⟩ := existe_zero
  obtain ⟨c', hc', hL⟩ := cota_inf_F hz
  have hρ := norm_rho_pos γ
  set c : ℝ := c' / (4 * ‖(1 / 2 : ℂ) + γ * I‖) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c, hc0, fun K => ?_⟩
  by_contra hne
  push Not at hne
  have hA : ∀ N : ℕ, M N ≤ c * ((N : ℝ) + 1) ^ (1 / 2 : ℝ) + K := fun N => by
    rw [← Real.sqrt_eq_rpow]; exact hne N
  have hZ : SemZeros (1 / 2) := semZeros_of_mertens_le (by norm_num) (by norm_num) hA
  have key := cota_polo abs_M_le hA (fun s hs => differentiableAt_F hZ hs) differentiableAt_F_meio
    (fun s hs => GA_M_eq hs) hγ.ne' hL
  rw [Al_meio hc0.le] at key
  exact contra_raiz hc' hρ hc key

/-- **`M(x) = Ω₋(√x)`**. -/
theorem mertens_omega_menos_raiz : ∃ c : ℝ, 0 < c ∧ ∀ K : ℝ, ∃ N : ℕ, M N < -(c * √((N : ℝ) + 1)) - K := by
  obtain ⟨γ, hγ, hz⟩ := existe_zero
  obtain ⟨c', hc', hL⟩ := cota_inf_F hz
  have hρ := norm_rho_pos γ
  set c : ℝ := c' / (4 * ‖(1 / 2 : ℂ) + γ * I‖) with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c, hc0, fun K => ?_⟩
  by_contra hne
  push Not at hne
  have hA : ∀ N : ℕ, (fun N => -M N) N ≤ c * ((N : ℝ) + 1) ^ (1 / 2 : ℝ) + K := fun N => by
    show -M N ≤ _
    rw [← Real.sqrt_eq_rpow]
    linarith [hne N]
  have hZ : SemZeros (1 / 2) := semZeros_of_mertens_ge (A := c) (K := K) (by norm_num) (by norm_num)
    (fun N => by rw [← Real.sqrt_eq_rpow]; exact hne N)
  have key := cota_polo (a := fun N => -M N) (H := fun s => -F s)
    (fun N => by rw [abs_neg]; exact abs_M_le N) hA (fun s hs => (differentiableAt_F hZ hs).neg)
    differentiableAt_F_meio.neg (fun s hs => by rw [GA_neg, GA_M_eq hs]) hγ.ne'
    (by simpa only [norm_neg] using hL)
  rw [Al_meio hc0.le] at key
  exact contra_raiz hc' hρ hc key

/-! ## 5. A cota de Mertens fraca de um lado só força zeros simples -/

/-- Num zero `ρ = ½ + iγ` de multiplicidade `≥ 2`, `(σ − ½)|1/ζ(σ + iγ)| → ∞` quando `σ → ½⁺`. -/
theorem cota_inf_F_dupla {γ : ℝ} {m : ℕ} {g : ℂ → ℂ} (hm : 1 ≤ m)
    (hg : AnalyticAt ℂ g ((1 / 2 : ℂ) + γ * I)) (hgρ : g ((1 / 2 : ℂ) + γ * I) ≠ 0)
    (hfg : ∀ᶠ s in 𝓝 ((1 / 2 : ℂ) + γ * I),
      riemannZeta₁ s = (s - ((1 / 2 : ℂ) + γ * I)) ^ (m + 1) * g s) (L : ℝ) :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), L ≤ (σ - 1 / 2) * ‖F ((σ : ℂ) + γ * I)‖ := by
  set ρ : ℂ := (1 / 2 : ℂ) + γ * I with hρdef
  have hρ1 : ρ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [hρdef] at this
  have hd1 : 0 < ‖ρ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hρ1)
  set c₁ : ℝ := ‖ρ - 1‖ / 2 / (‖g ρ‖ + 1) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  have hgne : ∀ᶠ s in 𝓝 ρ, g s ≠ 0 := hg.continuousAt.eventually_ne hgρ
  have hgn : Tendsto (fun s => ‖g s‖) (𝓝 ρ) (𝓝 ‖g ρ‖) := hg.continuousAt.norm
  have hgev : ∀ᶠ s in 𝓝 ρ, ‖g s‖ < ‖g ρ‖ + 1 :=
    hgn.eventually (Iio_mem_nhds (show ‖g ρ‖ < ‖g ρ‖ + 1 by linarith))
  have h1ev : ∀ᶠ s in 𝓝 ρ, ‖ρ - 1‖ / 2 < ‖s - 1‖ := by
    have hc : Tendsto (fun s : ℂ => ‖s - 1‖) (𝓝 ρ) (𝓝 ‖ρ - 1‖) :=
      ((continuousAt_id.sub continuousAt_const).norm : ContinuousAt (fun s : ℂ => ‖s - 1‖) ρ)
    exact hc.eventually (Ioi_mem_nhds (show ‖ρ - 1‖ / 2 < ‖ρ - 1‖ by linarith))
  have hrev : ∀ᶠ s in 𝓝 ρ, ‖s - ρ‖ < 1 := by
    have hc : Tendsto (fun s : ℂ => ‖s - ρ‖) (𝓝 ρ) (𝓝 ‖ρ - ρ‖) :=
      ((continuousAt_id.sub continuousAt_const).norm : ContinuousAt (fun s : ℂ => ‖s - ρ‖) ρ)
    exact hc.eventually (Iio_mem_nhds (show ‖ρ - ρ‖ < 1 by simp))
  have ev := (caminho γ).eventually (hfg.and (hgne.and (hgev.and (h1ev.and hrev))))
  have hsmall : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), σ - 1 / 2 < c₁ / (|L| + 1) := by
    exact ATK.ZeroClasses.Omega.tendsto_sub_meio.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [ev, self_mem_nhdsWithin, hsmall] with σ ⟨hf1, hg0, hg1, hs1, hr1⟩ hσ hsm
  simp only [mem_Ioi] at hσ
  have hpos : 0 < σ - 1 / 2 := by linarith
  have hd : ((σ : ℂ) + γ * I) - ρ = ((σ - 1 / 2 : ℝ) : ℂ) := by rw [hρdef]; exact sub_caminho σ γ
  have hdn : ‖((σ : ℂ) + γ * I) - ρ‖ = σ - 1 / 2 := by
    rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  rw [hdn] at hr1
  unfold F
  rw [hf1, norm_div, norm_mul, norm_pow, hdn]
  have hgn' : 0 < ‖g ((σ : ℂ) + γ * I)‖ := norm_pos_iff.mpr hg0
  have hpow : (σ - 1 / 2) ^ (m + 1) ≤ (σ - 1 / 2) ^ 2 :=
    pow_le_pow_of_le_one hpos.le hr1.le (by omega)
  have hD : 0 < (σ - 1 / 2) ^ (m + 1) * ‖g ((σ : ℂ) + γ * I)‖ := by positivity
  have hL1 : (|L| + 1) * (σ - 1 / 2) < c₁ := by
    rw [lt_div_iff₀ (by positivity)] at hsm
    linarith
  have hkey : (|L| + 1) * ((σ - 1 / 2) ^ (m + 1) * ‖g ((σ : ℂ) + γ * I)‖) ≤
      (σ - 1 / 2) * ‖(σ : ℂ) + γ * I - 1‖ := by
    have hgρ1 : 0 < ‖g ρ‖ + 1 := by positivity
    have e1 : c₁ * (‖g ρ‖ + 1) = ‖ρ - 1‖ / 2 := by rw [hc₁]; field_simp
    calc (|L| + 1) * ((σ - 1 / 2) ^ (m + 1) * ‖g ((σ : ℂ) + γ * I)‖)
        ≤ (|L| + 1) * ((σ - 1 / 2) ^ 2 * (‖g ρ‖ + 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hpow hg1.le hgn'.le (by positivity)
      _ = (σ - 1 / 2) * (((|L| + 1) * (σ - 1 / 2)) * (‖g ρ‖ + 1)) := by ring
      _ ≤ (σ - 1 / 2) * (c₁ * (‖g ρ‖ + 1)) := by
          apply mul_le_mul_of_nonneg_left _ hpos.le
          exact mul_le_mul_of_nonneg_right hL1.le hgρ1.le
      _ = (σ - 1 / 2) * (‖ρ - 1‖ / 2) := by rw [e1]
      _ ≤ (σ - 1 / 2) * ‖(σ : ℂ) + γ * I - 1‖ := mul_le_mul_of_nonneg_left hs1.le hpos.le
  rw [mul_div_assoc', le_div_iff₀ hD]
  have : L * ((σ - 1 / 2) ^ (m + 1) * ‖g ((σ : ℂ) + γ * I)‖) ≤
      (|L| + 1) * ((σ - 1 / 2) ^ (m + 1) * ‖g ((σ : ℂ) + γ * I)‖) :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self L]) hD.le
  linarith

/-- **`M(N) ≤ A√(N + 1) + K` ⟹ todo zero `½ + iγ` de `ζ` é simples** (`ζ₁` tem ordem `1` nele). -/
theorem simples_of_mertens_le {A K : ℝ} (h : ∀ N : ℕ, M N ≤ A * √((N : ℝ) + 1) + K) {γ : ℝ}
    (hz : riemannZeta ((1 / 2 : ℂ) + γ * I) = 0) :
    analyticOrderAt riemannZeta₁ ((1 / 2 : ℂ) + γ * I) = 1 := by
  set ρ : ℂ := (1 / 2 : ℂ) + γ * I with hρdef
  have hρ1 : ρ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [hρdef] at this
  have hγ : γ ≠ 0 := by
    rintro rfl
    refine ATK.ZeroClasses.Faixa.faixa_sem_zeros (s := ρ) ?_ ?_ ?_ hz <;> norm_num [hρdef]
  have hA : ∀ N : ℕ, M N ≤ A * ((N : ℝ) + 1) ^ (1 / 2 : ℝ) + K := fun N => by
    rw [← Real.sqrt_eq_rpow]; exact h N
  have hZ : SemZeros (1 / 2) := semZeros_of_mertens_le (by norm_num) (by norm_num) hA
  obtain ⟨m, g, hg, hgρ, hfg⟩ := fatora hz hρ1
  have hm : m = 0 := by
    by_contra hm
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have key := cota_polo abs_M_le hA (fun s hs => differentiableAt_F hZ hs) differentiableAt_F_meio
      (fun s hs => GA_M_eq hs) hγ (cota_inf_F_dupla hm1 hg hgρ hfg (‖ρ‖ * Al A (1 / 2) + 1))
    linarith
  subst hm
  have := ((differentiable_riemannZeta₁.analyticAt ρ).analyticOrderAt_eq_natCast (n := 1)).mpr
    ⟨g, hg, hgρ, by simpa [smul_eq_mul] using hfg⟩
  simpa using this

/-- **O mesmo por baixo**: `M(N) ≥ −A√(N + 1) − K` ⟹ todo zero `½ + iγ` é simples. -/
theorem simples_of_mertens_ge {A K : ℝ} (h : ∀ N : ℕ, -(A * √((N : ℝ) + 1)) - K ≤ M N) {γ : ℝ}
    (hz : riemannZeta ((1 / 2 : ℂ) + γ * I) = 0) :
    analyticOrderAt riemannZeta₁ ((1 / 2 : ℂ) + γ * I) = 1 := by
  set ρ : ℂ := (1 / 2 : ℂ) + γ * I with hρdef
  have hρ1 : ρ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [hρdef] at this
  have hγ : γ ≠ 0 := by
    rintro rfl
    refine ATK.ZeroClasses.Faixa.faixa_sem_zeros (s := ρ) ?_ ?_ ?_ hz <;> norm_num [hρdef]
  have hA : ∀ N : ℕ, (fun N => -M N) N ≤ A * ((N : ℝ) + 1) ^ (1 / 2 : ℝ) + K := fun N => by
    show -M N ≤ _
    rw [← Real.sqrt_eq_rpow]
    linarith [h N]
  have hZ : SemZeros (1 / 2) := semZeros_of_mertens_ge (A := A) (K := K) (by norm_num) (by norm_num)
    (fun N => by rw [← Real.sqrt_eq_rpow]; exact h N)
  obtain ⟨m, g, hg, hgρ, hfg⟩ := fatora hz hρ1
  have hm : m = 0 := by
    by_contra hm
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have key := cota_polo (a := fun N => -M N) (H := fun s => -F s)
      (fun N => by rw [abs_neg]; exact abs_M_le N) hA (fun s hs => (differentiableAt_F hZ hs).neg)
      differentiableAt_F_meio.neg (fun s hs => by rw [GA_neg, GA_M_eq hs]) hγ
      (by simpa only [norm_neg] using cota_inf_F_dupla hm1 hg hgρ hfg (‖ρ‖ * Al A (1 / 2) + 1))
    linarith
  subst hm
  have := ((differentiable_riemannZeta₁.analyticAt ρ).analyticOrderAt_eq_natCast (n := 1)).mpr
    ⟨g, hg, hgρ, by simpa [smul_eq_mul] using hfg⟩
  simpa using this

/-- **RH e zeros simples a partir de uma cota de Mertens fraca de um lado só.** -/
theorem rh_e_simples_of_mertens_le {A K : ℝ} (h : ∀ N : ℕ, M N ≤ A * √((N : ℝ) + 1) + K) :
    RiemannHypothesis ∧ ∀ γ : ℝ, riemannZeta ((1 / 2 : ℂ) + γ * I) = 0 →
      analyticOrderAt riemannZeta₁ ((1 / 2 : ℂ) + γ * I) = 1 :=
  ⟨ATK.ZeroClasses.Unilateral.rh_of_mertens_le h, fun _ hz => simples_of_mertens_le h hz⟩

end ATK.ZeroClasses.OmegaRaiz

#print axioms ATK.ZeroClasses.OmegaRaiz.differentiableAt_Gext
#print axioms ATK.ZeroClasses.OmegaRaiz.Gext_eq_H
#print axioms ATK.ZeroClasses.OmegaRaiz.norm_Ik_le
#print axioms ATK.ZeroClasses.OmegaRaiz.Ik_real0
#print axioms ATK.ZeroClasses.OmegaRaiz.cota_polo
#print axioms ATK.ZeroClasses.OmegaRaiz.differentiableAt_Hf_meio
#print axioms ATK.ZeroClasses.OmegaRaiz.differentiableAt_F_meio
#print axioms ATK.ZeroClasses.OmegaRaiz.existe_zero
#print axioms ATK.ZeroClasses.OmegaRaiz.norm_rho_pos
#print axioms ATK.ZeroClasses.OmegaRaiz.Al_meio
#print axioms ATK.ZeroClasses.OmegaRaiz.sqrt_dois_lt
#print axioms ATK.ZeroClasses.OmegaRaiz.contra_raiz
#print axioms ATK.ZeroClasses.OmegaRaiz.psi_omega_mais_raiz
#print axioms ATK.ZeroClasses.OmegaRaiz.psi_omega_menos_raiz
#print axioms ATK.ZeroClasses.OmegaRaiz.mertens_omega_mais_raiz
#print axioms ATK.ZeroClasses.OmegaRaiz.mertens_omega_menos_raiz
#print axioms ATK.ZeroClasses.OmegaRaiz.cota_inf_F_dupla
#print axioms ATK.ZeroClasses.OmegaRaiz.simples_of_mertens_le
#print axioms ATK.ZeroClasses.OmegaRaiz.simples_of_mertens_ge
#print axioms ATK.ZeroClasses.OmegaRaiz.rh_e_simples_of_mertens_le
