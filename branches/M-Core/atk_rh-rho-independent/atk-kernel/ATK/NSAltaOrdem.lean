import ATK.NSEstimativas
import ATK.NSClasse

/-!
# ATK — Navier–Stokes: estimativas de energia de ordem alta (para a continuação)

Camada 13 do ataque a B3. Normas de Sobolev com peso no lado de Fourier
`J_k(f) = ∫ (1 + ‖ξ‖)^{2k} ‖f(ξ)‖²` ao longo da solução branda:

* `J_sub_eq`: `J_k(â(t)) − J_k(â(0)) = ∫₀ᵗ D_k`, `D_k = ∫ w_k² · 2 Re ⟪â, ∂ₜâ⟫` (Fubini);
* `continuous_D`, `hasDerivAt_J`: `D_k` é contínua e é a derivada de `J_k(â(t))`;
* `gronwall`: `φ' = D ≤ g φ` (com `g ≥ 0` contínua) ⇒ `φ(t) ≤ φ(0) e^{∫₀ᵗ g}`.

**CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped Real

namespace ATK.NSAltaOrdem

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSPicard ATK.NSMild ATK.NSSuave ATK.NSTempo
  ATK.NSSimetria ATK.NSFisico ATK.NSEnergia ATK.NSEstimativas

/-! ### Pesos -/

theorem w_sq (k : ℕ) (ξ : E3) : w k ξ ^ 2 = w (2 * k) ξ := by
  unfold w; rw [← pow_mul, mul_comm]

theorem w_inv_mul_w_sq (k m : ℕ) (ξ : E3) :
    w k ξ ^ 2 * (w (2 * k + m) ξ)⁻¹ = (w m ξ)⁻¹ := by
  rw [w_sq, w_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (w_pos _ ξ).ne', one_mul]

/-- `‖F‖ ≤ C w_{2k+4}⁻¹ ⇒ w_k² ‖F‖ ≤ C w₄⁻¹`. -/
theorem wsq_mul_le {k : ℕ} {x C : ℝ} {ξ : E3} (h : x ≤ C * (w (2 * k + 4) ξ)⁻¹) :
    w k ξ ^ 2 * x ≤ C * (w 4 ξ)⁻¹ := by
  have hw := (w_pos k ξ)
  calc w k ξ ^ 2 * x ≤ w k ξ ^ 2 * (C * (w (2 * k + 4) ξ)⁻¹) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = C * (w k ξ ^ 2 * (w (2 * k + 4) ξ)⁻¹) := by ring
    _ = C * (w 4 ξ)⁻¹ := by rw [w_inv_mul_w_sq]

/-! ### A norma `J_k` -/

/-- `J_k(f) = ∫ w_k² ‖f‖²`. -/
noncomputable def J (k : ℕ) (f : E3 → C3) : ℝ := ∫ ξ, w k ξ ^ 2 * ‖f ξ‖ ^ 2

theorem J_nonneg (k : ℕ) (f : E3 → C3) : 0 ≤ J k f :=
  integral_nonneg fun ξ => by positivity

theorem BoaW.integrable_J {f : ℝ → E3 → C3} (hf : BoaW f) (k : ℕ) (s : ℝ) :
    Integrable fun ξ => w k ξ ^ 2 * ‖f s ξ‖ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := hf.bound (2 * k + 4)
  obtain ⟨C', hC'0, hC'⟩ := hf.bound 0
  have hw0 : ∀ ξ, (w 0 ξ)⁻¹ = 1 := fun ξ => by simp [w]
  refine integrable_of_le_w4 (A := C' * C) (fun ξ => by positivity) (fun ξ => ?_) ?_
  · have h1 : ‖f s ξ‖ ≤ C' := by simpa [hw0] using hC' s ξ
    have h2 : ‖f s ξ‖ ^ 2 ≤ C' * (C * (w (2 * k + 4) ξ)⁻¹) := by
      rw [sq]; exact mul_le_mul h1 (hC s ξ) (norm_nonneg _) hC'0
    have := wsq_mul_le (k := k) (C := C' * C) (x := ‖f s ξ‖ ^ 2) (ξ := ξ) (by linarith)
    exact this
  · exact ((continuous_w k).pow 2 |>.mul ((hf.cont_s s).norm.pow 2)).aestronglyMeasurable

/-- O integrando `w_k² · 2 Re ⟪f, g⟫`. -/
theorem BoaW.wsq_re_inner_bound {f g : ℝ → E3 → C3} (hf : BoaW f) (hg : BoaW g) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ s ξ, ‖w k ξ ^ 2 * (2 * (inner ℂ (f s ξ) (g s ξ)).re)‖ ≤ C * (w 4 ξ)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := hf.bound (2 * k + 4)
  obtain ⟨C', hC'0, hC'⟩ := hg.bound 0
  have hw0 : ∀ ξ, (w 0 ξ)⁻¹ = 1 := fun ξ => by simp [w]
  refine ⟨2 * C * C', by positivity, fun s ξ => ?_⟩
  have h1 : ‖g s ξ‖ ≤ C' := by simpa [hw0] using hC' s ξ
  have h2 : ‖2 * (inner ℂ (f s ξ) (g s ξ)).re‖ ≤ 2 * C * C' * (w (2 * k + 4) ξ)⁻¹ := by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
    have h3 := (Complex.abs_re_le_norm (inner ℂ (f s ξ) (g s ξ))).trans (norm_inner_le_norm _ _)
    have h4 : ‖f s ξ‖ * ‖g s ξ‖ ≤ C * (w (2 * k + 4) ξ)⁻¹ * C' :=
      mul_le_mul (hC s ξ) h1 (norm_nonneg _) (by have := w_pos (2 * k + 4) ξ; positivity)
    nlinarith
  rw [norm_mul, Real.norm_of_nonneg (by positivity)]
  exact wsq_mul_le h2

theorem BoaW.continuous_wsq_re_inner {f g : ℝ → E3 → C3} (hf : BoaW f) (hg : BoaW g) (k : ℕ) :
    Continuous fun p : ℝ × E3 => w k p.2 ^ 2 * (2 * (inner ℂ (f p.1 p.2) (g p.1 p.2)).re) := by
  have c1 := hf.cont
  have c2 := hg.cont
  have c3 := continuous_w k
  fun_prop

/-- `D_k(s) = ∫ w_k² · 2 Re ⟪â(s), ∂ₜâ(s)⟫`. -/
noncomputable def D (ν : ℝ) (a : ℝ → E3 → C3) (k : ℕ) (s : ℝ) : ℝ :=
  ∫ ξ, w k ξ ^ 2 * (2 * (inner ℂ (a s ξ) (ader ν a 1 s ξ)).re)

theorem continuous_D {ν : ℝ} {a : ℝ → E3 → C3} (ha : BoaW a) (k : ℕ) : Continuous (D ν a k) := by
  obtain ⟨C, -, hC⟩ := BoaW.wsq_re_inner_bound ha (boaW_ader (ν := ν) ha 1) k
  have hc := BoaW.continuous_wsq_re_inner ha (boaW_ader (ν := ν) ha 1) k
  refine continuous_of_dominated (bound := fun ξ => C * (w 4 ξ)⁻¹) (fun s => ?_)
    (fun s => Eventually.of_forall fun ξ => hC s ξ) (integrable_w_inv.const_mul C)
    (Eventually.of_forall fun ξ => ?_)
  · have c1 := ha.cont_s s
    have c2 := (boaW_ader (ν := ν) ha 1).cont_s s
    have c3 := continuous_w k
    exact (by fun_prop : Continuous fun ξ =>
      w k ξ ^ 2 * (2 * (inner ℂ (a s ξ) (ader ν a 1 s ξ)).re)).aestronglyMeasurable
  · have c1 := ha.cont_t ξ
    have c2 := (boaW_ader (ν := ν) ha 1).cont_t ξ
    fun_prop

theorem continuous_J {a : ℝ → E3 → C3} (ha : BoaW a) (k : ℕ) :
    Continuous fun s => J k (a s) := by
  obtain ⟨C, hC0, hC⟩ := ha.bound (2 * k + 4)
  obtain ⟨C', hC'0, hC'⟩ := ha.bound 0
  have hw0 : ∀ ξ, (w 0 ξ)⁻¹ = 1 := fun ξ => by simp [w]
  have hc : Continuous fun p : ℝ × E3 => w k p.2 ^ 2 * ‖a p.1 p.2‖ ^ 2 := by
    have c1 := ha.cont
    have c3 := continuous_w k
    fun_prop
  refine continuous_of_dominated (bound := fun ξ => (C' * C) * (w 4 ξ)⁻¹) (fun s => ?_)
    (fun s => Eventually.of_forall fun ξ => ?_) (integrable_w_inv.const_mul _)
    (Eventually.of_forall fun ξ => ?_)
  · have c1 := ha.cont_s s
    have c3 := continuous_w k
    exact (by fun_prop : Continuous fun ξ => w k ξ ^ 2 * ‖a s ξ‖ ^ 2).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (by positivity)]
    have h1 : ‖a s ξ‖ ≤ C' := by simpa [hw0] using hC' s ξ
    have h2 : ‖a s ξ‖ ^ 2 ≤ C' * C * (w (2 * k + 4) ξ)⁻¹ := by
      rw [sq, mul_assoc]; exact mul_le_mul h1 (hC s ξ) (norm_nonneg _) hC'0
    exact wsq_mul_le h2
  · have c1 := ha.cont_t ξ
    fun_prop

section

variable {ν T : ℝ} {a₀ : E3 → C3} {a : ℝ → E3 → C3}

/-- **Identidade de energia com peso**: `J_k(â(t)) − J_k(â(0)) = ∫₀ᵗ D_k`. -/
theorem J_sub_eq (ha : BoaW a)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a₀ ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    J k (a t) - J k (a 0) = ∫ s in (0 : ℝ)..t, D ν a k s := by
  set h : ℝ → E3 → ℝ := fun s ξ => w k ξ ^ 2 * (2 * (inner ℂ (a s ξ) (ader ν a 1 s ξ)).re)
    with hh
  obtain ⟨C, hC0, hC⟩ := BoaW.wsq_re_inner_bound ha (boaW_ader (ν := ν) ha 1) k
  have hint : Integrable (Function.uncurry h) ((volume.restrict (uIoc 0 t)).prod volume) := by
    have h1 : Integrable (fun _ : ℝ => C) (volume.restrict (uIoc 0 t)) :=
      integrableOn_const (by simp [uIoc])
    have hdom : Integrable (fun p : ℝ × E3 => C * (w 4 p.2)⁻¹)
        ((volume.restrict (uIoc 0 t)).prod volume) := h1.mul_prod integrable_w_inv
    exact hdom.mono' (BoaW.continuous_wsq_re_inner ha (boaW_ader (ν := ν) ha 1) k).aestronglyMeasurable
      (Eventually.of_forall fun p => hC p.1 p.2)
  unfold J
  rw [← integral_sub (BoaW.integrable_J ha k t) (BoaW.integrable_J ha k 0)]
  unfold D
  rw [intervalIntegral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [hh]
  rw [← mul_sub, norm_sq_sub_eq ha hmild ξ ht]
  simp only [intervalIntegral.integral_const_mul]

/-- `J_k(â(t))` tem derivada `D_k(t)` no interior. -/
theorem hasDerivAt_J (ha : BoaW a)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a₀ ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    (k : ℕ) {s : ℝ} (hs : s ∈ Ioo 0 T) :
    HasDerivAt (fun r => J k (a r)) (D ν a k s) s := by
  have hD := continuous_D (ν := ν) ha k
  have h1 : HasDerivAt (fun r => J k (a 0) + ∫ u in (0 : ℝ)..r, D ν a k u) (D ν a k s) s := by
    have := intervalIntegral.integral_hasDerivAt_right (hD.intervalIntegrable 0 s)
      (hD.stronglyMeasurableAtFilter _ _) hD.continuousAt
    simpa using this.const_add (J k (a 0))
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
  have := J_sub_eq ha hmild k hr
  linarith

end

/-! ### Gronwall -/

/-- **Gronwall**: se `φ(t) = φ(0) + ∫₀ᵗ D`, `D` contínua e `D ≤ g φ` com `g ≥ 0` contínua, então
`φ(t) ≤ φ(0) e^{∫₀ᵗ g}`. -/
theorem gronwall {φ Dφ g : ℝ → ℝ} {T : ℝ}
    (hφ : ∀ t ∈ Icc 0 T, φ t = φ 0 + ∫ s in (0 : ℝ)..t, Dφ s) (hD : Continuous Dφ)
    (hg : Continuous g) (hDg : ∀ s ∈ Icc 0 T, Dφ s ≤ g s * φ s) {t : ℝ} (ht : t ∈ Icc 0 T) :
    φ t ≤ φ 0 * Real.exp (∫ s in (0 : ℝ)..t, g s) := by
  set G : ℝ → ℝ := fun r => ∫ s in (0 : ℝ)..r, g s with hG
  set Ψ : ℝ → ℝ := fun r => φ r * Real.exp (-G r) with hΨ
  have hGd : ∀ r, HasDerivAt G (g r) r := fun r =>
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 r)
      (hg.stronglyMeasurableAtFilter _ _) hg.continuousAt
  have hφd : ∀ r ∈ Ioo 0 T, HasDerivAt φ (Dφ r) r := by
    intro r hr
    have h1 : HasDerivAt (fun r => φ 0 + ∫ u in (0 : ℝ)..r, Dφ u) (Dφ r) r := by
      have := intervalIntegral.integral_hasDerivAt_right (hD.intervalIntegrable 0 r)
        (hD.stronglyMeasurableAtFilter _ _) hD.continuousAt
      simpa using this.const_add (φ 0)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds hr.1 hr.2] with u hu
    exact hφ u hu
  have hφc : ContinuousOn φ (Icc 0 T) := by
    have hc : Continuous fun r => φ 0 + ∫ u in (0 : ℝ)..r, Dφ u := by
      exact continuous_const.add (intervalIntegral.continuous_primitive (fun a b => hD.intervalIntegrable a b) 0)
    exact hc.continuousOn.congr fun r hr => hφ r hr
  have hGc : Continuous G := intervalIntegral.continuous_primitive (fun a b => hg.intervalIntegrable a b) 0
  have hΨc : ContinuousOn Ψ (Icc 0 t) :=
    (hφc.mono (Icc_subset_Icc_right ht.2)).mul (hGc.neg.rexp.continuousOn)
  have hΨd : ∀ r ∈ Ioo 0 t, HasDerivAt Ψ (Dφ r * Real.exp (-G r) +
      φ r * (Real.exp (-G r) * -g r)) r := by
    intro r hr
    have hr' : r ∈ Ioo 0 T := ⟨hr.1, hr.2.trans_le ht.2⟩
    exact (hφd r hr').mul ((hGd r).neg.exp)
  have hanti : AntitoneOn Ψ (Icc 0 t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t) hΨc ?_ ?_
    · rw [interior_Icc]
      exact fun r hr => (hΨd r hr).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro r hr
      rw [(hΨd r hr).deriv]
      have hr' : r ∈ Icc 0 T := ⟨hr.1.le, hr.2.le.trans ht.2⟩
      have := hDg r hr'
      have he := Real.exp_pos (-G r)
      nlinarith
  have h0 : (0 : ℝ) ∈ Icc 0 t := ⟨le_rfl, ht.1⟩
  have htt : t ∈ Icc 0 t := ⟨ht.1, le_rfl⟩
  have hle := hanti h0 htt ht.1
  simp only [hΨ, hG, intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one] at hle
  have he := Real.exp_pos (∫ s in (0 : ℝ)..t, g s)
  calc φ t = φ t * Real.exp (-∫ s in (0 : ℝ)..t, g s) * Real.exp (∫ s in (0 : ℝ)..t, g s) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ φ 0 * Real.exp (∫ s in (0 : ℝ)..t, g s) := mul_le_mul_of_nonneg_right hle he.le


/-! ### Funções de decaimento rápido e convolução -/

/-- Função real contínua, não negativa, de decaimento rápido. -/
structure Rapida (X : E3 → ℝ) : Prop where
  cont : Continuous X
  nonneg : ∀ ξ, 0 ≤ X ξ
  bound : ∀ m : ℕ, ∃ C, ∀ ξ, X ξ ≤ C * (w m ξ)⁻¹

theorem Rapida.mansa {X : E3 → ℝ} (h : Rapida X) : Mansa X := ⟨h.cont, h.nonneg, h.bound 4⟩

theorem Rapida.integrable {X : E3 → ℝ} (h : Rapida X) : Integrable X := h.mansa.integrable

theorem Rapida.C_nonneg {X : E3 → ℝ} (h : Rapida X) {m : ℕ} {C : ℝ}
    (hC : ∀ ξ, X ξ ≤ C * (w m ξ)⁻¹) : 0 ≤ C :=
  nonneg_of_mul_nonneg_left ((h.nonneg 0).trans (hC 0)) (inv_pos.mpr (w_pos m 0))

theorem Rapida.mul_w {X : E3 → ℝ} (h : Rapida X) (j : ℕ) : Rapida fun ξ => w j ξ * X ξ where
  cont := (continuous_w j).mul h.cont
  nonneg ξ := mul_nonneg (w_pos j ξ).le (h.nonneg ξ)
  bound m := by
    obtain ⟨C, hC⟩ := h.bound (m + j)
    refine ⟨C, fun ξ => ?_⟩
    have hw := w_pos j ξ
    calc w j ξ * X ξ ≤ w j ξ * (C * (w (m + j) ξ)⁻¹) := mul_le_mul_of_nonneg_left (hC ξ) hw.le
      _ = C * (w m ξ)⁻¹ := by rw [w_add, mul_inv]; field_simp

theorem Rapida.norm_mul {X : E3 → ℝ} (h : Rapida X) : Rapida fun ξ => ‖ξ‖ * X ξ where
  cont := continuous_norm.mul h.cont
  nonneg ξ := mul_nonneg (norm_nonneg _) (h.nonneg ξ)
  bound m := by
    obtain ⟨C, hC⟩ := (h.mul_w 1).bound m
    exact ⟨C, fun ξ => (mul_le_mul_of_nonneg_right (norm_le_w1 ξ) (h.nonneg ξ)).trans (hC ξ)⟩

theorem Rapida.of_norm {f : E3 → C3} (hc : Continuous f) (hb : ∀ m : ℕ, ∃ C, ∀ ξ, ‖f ξ‖ ≤ C * (w m ξ)⁻¹) :
    Rapida fun ξ => ‖f ξ‖ := ⟨hc.norm, fun ξ => norm_nonneg _, hb⟩

theorem BoaW.rapida {f : ℝ → E3 → C3} (hf : BoaW f) (s : ℝ) : Rapida fun ξ => ‖f s ξ‖ :=
  Rapida.of_norm (hf.cont_s s) fun m => by
    obtain ⟨C, -, hC⟩ := hf.bound m; exact ⟨C, hC s⟩

/-- Convolução `(Y ⋆ Z)(ξ) = ∫ Y(η) Z(ξ − η) dη`. -/
noncomputable def cv (Y Z : E3 → ℝ) (ξ : E3) : ℝ := ∫ η, Y η * Z (ξ - η)

theorem cv_eq_convolution (Y Z : E3 → ℝ) :
    cv Y Z = convolution Y Z (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext ξ; simp [cv, convolution]

theorem Rapida.integrable_cv_integrand {Y Z : E3 → ℝ} (hY : Rapida Y) (hZ : Rapida Z) (ξ : E3) :
    Integrable fun η => Y η * Z (ξ - η) := by
  obtain ⟨C, hC0, hC⟩ := hZ.mansa.le_const
  refine (hY.integrable.mul_const C).mono'
    (hY.cont.mul (hZ.cont.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    (Eventually.of_forall fun η => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (hY.nonneg _) (hZ.nonneg _))]
  exact mul_le_mul_of_nonneg_left (hC _) (hY.nonneg _)

theorem Rapida.cv {Y Z : E3 → ℝ} (hY : Rapida Y) (hZ : Rapida Z) : Rapida (cv Y Z) where
  cont := by
    rw [cv_eq_convolution]
    obtain ⟨C, hC0, hC⟩ := hZ.mansa.le_const
    refine BddAbove.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℝ ℝ)
      ⟨C, ?_⟩ hY.integrable hZ.cont
    rintro _ ⟨x, rfl⟩
    simp only [Real.norm_of_nonneg (hZ.nonneg x)]
    exact hC x
  nonneg ξ := integral_nonneg fun η => mul_nonneg (hY.nonneg _) (hZ.nonneg _)
  bound m := by
    obtain ⟨A, hA⟩ := hY.bound 4
    obtain ⟨A', hA'⟩ := hY.bound m
    obtain ⟨B, hB⟩ := hZ.bound 4
    obtain ⟨B', hB'⟩ := hZ.bound m
    refine ⟨2 ^ m * I4 * (A' * B + A * B'), fun ξ => ?_⟩
    have h := conv_peso m hY.cont hZ.cont hY.nonneg hZ.nonneg hA hA' hB hB' ξ
    rw [← div_eq_mul_inv, le_div_iff₀ (w_pos m ξ), mul_comm]
    exact h

/-- `∫ X · (Y ⋆ Z) = ∫∫ X(ξ) Y(η) Z(ξ − η)`. -/
theorem integral_mul_cv (X Y Z : E3 → ℝ) :
    ∫ ξ, X ξ * cv Y Z ξ = ∫ ξ, ∫ η, X ξ * Y η * Z (ξ - η) := by
  congr 1 with ξ
  rw [cv, ← integral_const_mul]
  congr 1 with η
  ring

/-- Divisão de peso na convolução: `w_j(ξ) (Y ⋆ Z)(ξ) ≤ 2^j ((w_j Y) ⋆ Z + Y ⋆ (w_j Z))(ξ)`. -/
theorem w_mul_cv_le {Y Z : E3 → ℝ} (hY : Rapida Y) (hZ : Rapida Z) (j : ℕ) (ξ : E3) :
    w j ξ * cv Y Z ξ ≤
      2 ^ j * (cv (fun η => w j η * Y η) Z ξ + cv Y (fun ζ => w j ζ * Z ζ) ξ) := by
  have i1 := (hY.mul_w j).integrable_cv_integrand hZ ξ
  have i2 := hY.integrable_cv_integrand (hZ.mul_w j) ξ
  have i0 := hY.integrable_cv_integrand hZ ξ
  unfold cv
  rw [← integral_add i1 i2, ← integral_const_mul, ← integral_const_mul]
  refine integral_mono (i0.const_mul _) ((i1.add i2).const_mul _) fun η => ?_
  have hw := w_le_add j ξ η
  have hYZ : 0 ≤ Y η * Z (ξ - η) := mul_nonneg (hY.nonneg _) (hZ.nonneg _)
  calc w j ξ * (Y η * Z (ξ - η)) ≤ 2 ^ j * (w j η + w j (ξ - η)) * (Y η * Z (ξ - η)) :=
        mul_le_mul_of_nonneg_right hw hYZ
    _ = 2 ^ j * (w j η * Y η * Z (ξ - η) + Y η * (w j (ξ - η) * Z (ξ - η))) := by ring

/-! ### O termo não linear com divergência nula -/

/-- Com `⟪η, f(η)⟫ = 0`: `‖N(f, f)(ξ)‖ ≤ 2π ∫ ‖f(η)‖ ‖ξ − η‖ ‖f(ξ − η)‖ dη`. -/
theorem norm_Nl_le_cv {f : E3 → C3} (hd : ∀ ξ, inner ℂ (cpx ξ) (f ξ) = 0)
    (hR : Rapida fun ξ => ‖f ξ‖) (ξ : E3) :
    ‖Nl f f ξ‖ ≤ 2 * π * cv (fun η => ‖f η‖) (fun ζ => ‖ζ‖ * ‖f ζ‖) ξ := by
  unfold Nl cv
  rw [norm_smul]
  have hI : ‖((2 * π : ℝ) * Complex.I : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hI]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine norm_integral_le_of_norm_le (hR.integrable_cv_integrand hR.norm_mul ξ)
    (Eventually.of_forall fun η => ?_)
  have e : inner ℂ (cpx ξ) (f η) = inner ℂ (cpx (ξ - η)) (f η) := by
    rw [NSEnergia.cpx_sub, inner_sub_left, hd η, sub_zero]
  rw [norm_smul, e]
  calc ‖inner ℂ (cpx (ξ - η)) (f η)‖ * ‖f (ξ - η)‖ ≤ (‖ξ - η‖ * ‖f η‖) * ‖f (ξ - η)‖ :=
        mul_le_mul_of_nonneg_right (norm_inner_cpx_le _ _) (norm_nonneg _)
    _ = ‖f η‖ * (‖ξ - η‖ * ‖f (ξ - η)‖) := by ring


/-! ### A cota de `D_k` -/

/-- `T_k(f) = ∫ w_k² ‖f‖ ‖N(f, f)‖`. -/
noncomputable def Tn (f : E3 → C3) (k : ℕ) : ℝ := ∫ ξ, w k ξ ^ 2 * (‖f ξ‖ * ‖Nl f f ξ‖)

theorem Tn_nonneg (f : E3 → C3) (k : ℕ) : 0 ≤ Tn f k :=
  integral_nonneg fun ξ => by positivity

theorem BoaW.integrable_wsq_mul_norm {f g : ℝ → E3 → C3} (hf : BoaW f) (hg : BoaW g) (k : ℕ)
    (s : ℝ) : Integrable fun ξ => w k ξ ^ 2 * (‖f s ξ‖ * ‖g s ξ‖) := by
  obtain ⟨C, hC0, hC⟩ := hf.bound (2 * k + 4)
  obtain ⟨C', hC'0, hC'⟩ := hg.bound 0
  have hw0 : ∀ ξ, (w 0 ξ)⁻¹ = 1 := fun ξ => by simp [w]
  refine integrable_of_le_w4 (A := C * C') (fun ξ => by positivity) (fun ξ => ?_) ?_
  · have h1 : ‖g s ξ‖ ≤ C' := by simpa [hw0] using hC' s ξ
    have h2 : ‖f s ξ‖ * ‖g s ξ‖ ≤ C * C' * (w (2 * k + 4) ξ)⁻¹ := by
      have := mul_le_mul (hC s ξ) h1 (norm_nonneg _) (by have := w_pos (2 * k + 4) ξ; positivity)
      linarith
    exact wsq_mul_le h2
  · have c1 := hf.cont_s s
    have c2 := hg.cont_s s
    have c3 := continuous_w k
    exact (by fun_prop : Continuous fun ξ => w k ξ ^ 2 * (‖f s ξ‖ * ‖g s ξ‖)).aestronglyMeasurable

theorem dissip_le (ν : ℝ) (hν : 0 ≤ ν) (k : ℕ) (ξ : E3) (x : ℝ) (hx : 0 ≤ x) :
    -2 * (w k ξ ^ 2 * (kappa ν ξ * x)) ≤
      -(4 * π ^ 2 * ν) * (w (k + 1) ξ ^ 2 * x) + 8 * π ^ 2 * ν * (w k ξ ^ 2 * x) := by
  rw [w_succ]
  unfold kappa
  have hr := norm_nonneg ξ
  have h1 : (1 + ‖ξ‖) ^ 2 ≤ 2 * (1 + ‖ξ‖ ^ 2) := by nlinarith [sq_nonneg (1 - ‖ξ‖)]
  have hW : 0 ≤ w k ξ ^ 2 * x := by positivity
  have hp : 0 ≤ 4 * π ^ 2 * ν := by positivity
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hW) hp
  nlinarith

/-- **Cota de `D_k`**: `D_k ≤ −4π²ν J_{k+1} + 8π²ν J_k + 2 T_k`. -/
theorem D_le {ν : ℝ} {a : ℝ → E3 → C3} (hν : 0 ≤ ν) (ha : BoaW a)
    (hdivF : ∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0) (k : ℕ) (s : ℝ) :
    D ν a k s ≤ -(4 * π ^ 2 * ν) * J (k + 1) (a s) + 8 * π ^ 2 * ν * J k (a s) +
      2 * Tn (a s) k := by
  have hN := ha.nl ha
  have i1 := BoaW.integrable_J ha (k + 1) s
  have i2 := BoaW.integrable_J ha k s
  have i3 := BoaW.integrable_wsq_mul_norm ha hN k s
  have iD : Integrable fun ξ => w k ξ ^ 2 * (2 * (inner ℂ (a s ξ) (ader ν a 1 s ξ)).re) := by
    obtain ⟨C, -, hC⟩ := BoaW.wsq_re_inner_bound ha (boaW_ader (ν := ν) ha 1) k
    exact (integrable_w_inv.const_mul C).mono'
      ((BoaW.continuous_wsq_re_inner ha (boaW_ader (ν := ν) ha 1) k).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun ξ => hC s ξ)
  have hpt : ∀ ξ, w k ξ ^ 2 * (2 * (inner ℂ (a s ξ) (ader ν a 1 s ξ)).re) ≤
      -(4 * π ^ 2 * ν) * (w (k + 1) ξ ^ 2 * ‖a s ξ‖ ^ 2) +
        8 * π ^ 2 * ν * (w k ξ ^ 2 * ‖a s ξ‖ ^ 2) +
        2 * (w k ξ ^ 2 * (‖a s ξ‖ * ‖Nl (a s) (a s) ξ‖)) := by
    intro ξ
    have e : (inner ℂ (a s ξ) (ader ν a 1 s ξ)).re =
        -(kappa ν ξ * ‖a s ξ‖ ^ 2) - (inner ℂ (a s ξ) (Nl (a s) (a s) ξ)).re := by
      rw [ader_one, inner_sub_right, inner_lp_of_div (hdivF s ξ), inner_smul_right]
      have h0 : (inner ℂ (a s ξ) (a s ξ)).re = ‖a s ξ‖ ^ 2 := by
        have := inner_self_eq_norm_sq (𝕜 := ℂ) (a s ξ)
        simpa [RCLike.re_to_complex] using this
      simp only [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re, Complex.ofReal_im, h0]
      ring
    have hre : -(inner ℂ (a s ξ) (Nl (a s) (a s) ξ)).re ≤ ‖a s ξ‖ * ‖Nl (a s) (a s) ξ‖ := by
      have := (Complex.abs_re_le_norm (inner ℂ (a s ξ) (Nl (a s) (a s) ξ))).trans
        (norm_inner_le_norm _ _)
      have := neg_abs_le (inner ℂ (a s ξ) (Nl (a s) (a s) ξ)).re
      linarith
    have hd := dissip_le ν hν k ξ (‖a s ξ‖ ^ 2) (sq_nonneg _)
    rw [e]
    have hw : 0 ≤ w k ξ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hre hw]
  have i1' : Integrable fun ξ => -(4 * π ^ 2 * ν) * (w (k + 1) ξ ^ 2 * ‖a s ξ‖ ^ 2) :=
    i1.const_mul _
  have i2' : Integrable fun ξ => 8 * π ^ 2 * ν * (w k ξ ^ 2 * ‖a s ξ‖ ^ 2) := i2.const_mul _
  have i3' : Integrable fun ξ => 2 * (w k ξ ^ 2 * (‖a s ξ‖ * ‖Nl (a s) (a s) ξ‖)) :=
    i3.const_mul _
  have i12 : Integrable fun ξ => -(4 * π ^ 2 * ν) * (w (k + 1) ξ ^ 2 * ‖a s ξ‖ ^ 2) +
      8 * π ^ 2 * ν * (w k ξ ^ 2 * ‖a s ξ‖ ^ 2) := i1'.add i2'
  unfold D J Tn
  calc ∫ ξ, w k ξ ^ 2 * (2 * (inner ℂ (a s ξ) (ader ν a 1 s ξ)).re)
      ≤ ∫ ξ, (-(4 * π ^ 2 * ν) * (w (k + 1) ξ ^ 2 * ‖a s ξ‖ ^ 2) +
        8 * π ^ 2 * ν * (w k ξ ^ 2 * ‖a s ξ‖ ^ 2) +
        2 * (w k ξ ^ 2 * (‖a s ξ‖ * ‖Nl (a s) (a s) ξ‖))) :=
        integral_mono iD (i12.add i3') hpt
    _ = _ := by
        rw [integral_add i12 i3', integral_add i1' i2', integral_const_mul, integral_const_mul,
          integral_const_mul]

/-! ### A cota trilinear de `T_k` -/

/-- `S(X, Y, Z) = ∫∫ X(ξ) Y(η) Z(ξ − η)`. -/
noncomputable def S3 (X Y Z : E3 → ℝ) : ℝ := ∫ ξ, ∫ η, X ξ * Y η * Z (ξ - η)

theorem S3_nonneg {X Y Z : E3 → ℝ} (hX : ∀ ξ, 0 ≤ X ξ) (hY : ∀ ξ, 0 ≤ Y ξ)
    (hZ : ∀ ξ, 0 ≤ Z ξ) : 0 ≤ S3 X Y Z :=
  integral_nonneg fun ξ => integral_nonneg fun η => mul_nonneg (mul_nonneg (hX _) (hY _)) (hZ _)

theorem Rapida.mul {X Y : E3 → ℝ} (hX : Rapida X) (hY : Rapida Y) :
    Rapida fun ξ => X ξ * Y ξ where
  cont := hX.cont.mul hY.cont
  nonneg ξ := mul_nonneg (hX.nonneg ξ) (hY.nonneg ξ)
  bound m := by
    obtain ⟨C, hC⟩ := hX.bound m
    obtain ⟨C', hC'0, hC'⟩ := hY.mansa.le_const
    refine ⟨C * C', fun ξ => ?_⟩
    have hC0 := hX.C_nonneg hC
    have hw := w_pos m ξ
    have := mul_le_mul (hC ξ) (hC' ξ) (hY.nonneg ξ) (by positivity)
    calc X ξ * Y ξ ≤ C * (w m ξ)⁻¹ * C' := this
      _ = C * C' * (w m ξ)⁻¹ := by ring

/-- **Divisão de `T_{j+1}`**: com `A = ‖f‖`, `P(ζ) = ‖ζ‖ A(ζ)`, `X = w_{j+2} A`:
`T_{j+1} ≤ 2π 2^j (S(X, w_j A, P) + S(X, A, w_j P))`. -/
theorem Tn_le {f : E3 → C3} (hd : ∀ ξ, inner ℂ (cpx ξ) (f ξ) = 0)
    (hR : Rapida fun ξ => ‖f ξ‖) (j : ℕ) :
    Tn f (j + 1) ≤ 2 * π * 2 ^ j *
      (S3 (fun ξ => w (j + 2) ξ * ‖f ξ‖) (fun η => w j η * ‖f η‖) (fun ζ => ‖ζ‖ * ‖f ζ‖) +
       S3 (fun ξ => w (j + 2) ξ * ‖f ξ‖) (fun η => ‖f η‖) (fun ζ => w j ζ * (‖ζ‖ * ‖f ζ‖))) := by
  have hRP : Rapida fun ζ => ‖ζ‖ * ‖f ζ‖ := hR.norm_mul
  have hX : Rapida fun ξ => w (j + 2) ξ * ‖f ξ‖ := hR.mul_w (j + 2)
  have h1 := hX.mul ((hR.mul_w j).cv hRP)
  have h2 := hX.mul (hR.cv (hRP.mul_w j))
  have hpt : ∀ ξ, w (j + 1) ξ ^ 2 * (‖f ξ‖ * ‖Nl f f ξ‖) ≤ 2 * π * 2 ^ j *
      (w (j + 2) ξ * ‖f ξ‖ * cv (fun η => w j η * ‖f η‖) (fun ζ => ‖ζ‖ * ‖f ζ‖) ξ +
       w (j + 2) ξ * ‖f ξ‖ * cv (fun η => ‖f η‖) (fun ζ => w j ζ * (‖ζ‖ * ‖f ζ‖)) ξ) := by
    intro ξ
    have e : w (j + 1) ξ ^ 2 = w (j + 2) ξ * w j ξ := by
      rw [w_sq, show 2 * (j + 1) = (j + 2) + j by ring, w_add]
    have hN := norm_Nl_le_cv hd hR ξ
    have hW := w_mul_cv_le hR hRP j ξ
    have hXn : 0 ≤ w (j + 2) ξ * ‖f ξ‖ := hX.nonneg ξ
    have hwj := (w_pos j ξ).le
    calc w (j + 1) ξ ^ 2 * (‖f ξ‖ * ‖Nl f f ξ‖)
        = (w (j + 2) ξ * ‖f ξ‖) * (w j ξ * ‖Nl f f ξ‖) := by rw [e]; ring
      _ ≤ (w (j + 2) ξ * ‖f ξ‖) * (w j ξ * (2 * π *
            cv (fun η => ‖f η‖) (fun ζ => ‖ζ‖ * ‖f ζ‖) ξ)) := by gcongr
      _ = (w (j + 2) ξ * ‖f ξ‖) * (2 * π *
            (w j ξ * cv (fun η => ‖f η‖) (fun ζ => ‖ζ‖ * ‖f ζ‖) ξ)) := by ring
      _ ≤ (w (j + 2) ξ * ‖f ξ‖) * (2 * π * (2 ^ j *
            (cv (fun η => w j η * ‖f η‖) (fun ζ => ‖ζ‖ * ‖f ζ‖) ξ +
             cv (fun η => ‖f η‖) (fun ζ => w j ζ * (‖ζ‖ * ‖f ζ‖)) ξ))) := by gcongr
      _ = _ := by ring
  have hg := (h1.integrable.add h2.integrable).const_mul (2 * π * 2 ^ j)
  calc Tn f (j + 1) = ∫ ξ, w (j + 1) ξ ^ 2 * (‖f ξ‖ * ‖Nl f f ξ‖) := rfl
    _ ≤ ∫ ξ, 2 * π * 2 ^ j *
          (w (j + 2) ξ * ‖f ξ‖ * cv (fun η => w j η * ‖f η‖) (fun ζ => ‖ζ‖ * ‖f ζ‖) ξ +
           w (j + 2) ξ * ‖f ξ‖ * cv (fun η => ‖f η‖) (fun ζ => w j ζ * (‖ζ‖ * ‖f ζ‖)) ξ) :=
        integral_mono_of_nonneg (Eventually.of_forall fun ξ => by positivity) hg
          (Eventually.of_forall hpt)
    _ = _ := by
        rw [integral_const_mul, integral_add h1.integrable h2.integrable]
        unfold S3
        rw [← integral_mul_cv (fun ξ => w (j + 2) ξ * ‖f ξ‖) (fun η => w j η * ‖f η‖)
          (fun ζ => ‖ζ‖ * ‖f ζ‖), ← integral_mul_cv (fun ξ => w (j + 2) ξ * ‖f ξ‖)
          (fun η => ‖f η‖) (fun ζ => w j ζ * (‖ζ‖ * ‖f ζ‖))]


/-! ### As quantidades `L²` e `L¹` -/

theorem w_zero (ξ : E3) : w 0 ξ = 1 := by simp [w]

theorem integral_wA_sq (f : E3 → C3) (j : ℕ) :
    ∫ ξ, (w j ξ * ‖f ξ‖) ^ 2 = J j f := by
  unfold J; congr 1 with ξ; rw [mul_pow]

theorem integral_wP_sq_le {f : E3 → C3} (hR : Rapida fun ξ => ‖f ξ‖) (j : ℕ) :
    ∫ ζ, (w j ζ * (‖ζ‖ * ‖f ζ‖)) ^ 2 ≤ J (j + 1) f := by
  rw [← integral_wA_sq]
  refine integral_mono ((hR.norm_mul.mul_w j).mansa.integrable_sq)
    ((hR.mul_w (j + 1)).mansa.integrable_sq) fun ζ => ?_
  have h : w j ζ * (‖ζ‖ * ‖f ζ‖) ≤ w (j + 1) ζ * ‖f ζ‖ := by
    rw [w_succ]
    have := w_pos j ζ
    have := norm_nonneg (f ζ)
    have : ‖ζ‖ ≤ 1 + ‖ζ‖ := by linarith
    nlinarith
  exact pow_le_pow_left₀ (mul_nonneg (w_pos j ζ).le (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    h 2

theorem integral_P_sq_le {f : E3 → C3} (hR : Rapida fun ξ => ‖f ξ‖) :
    ∫ ζ, (‖ζ‖ * ‖f ζ‖) ^ 2 ≤ J 1 f := by
  have := integral_wP_sq_le hR 0
  simpa [w_zero] using this

/-- `(∫ B)² ≤ I₄ ∫ w₂² B²`. -/
theorem integral_sq_le_I4 {B : E3 → ℝ} (hB : Rapida B) :
    (∫ ξ, B ξ) ^ 2 ≤ I4 * ∫ ξ, (w 2 ξ * B ξ) ^ 2 := by
  have hc : Continuous fun ξ : E3 => (w 2 ξ)⁻¹ :=
    (continuous_w 2).inv₀ fun ξ => (w_pos 2 ξ).ne'
  have h := cs_sq (μ := volume) (f := fun ξ => w 2 ξ * B ξ) (g := fun ξ => (w 2 ξ)⁻¹)
    (fun ξ => (hB.mul_w 2).nonneg ξ) (fun ξ => (inv_pos.mpr (w_pos 2 ξ)).le)
    (hB.mul_w 2).cont.aestronglyMeasurable hc.aestronglyMeasurable
    (hB.mul_w 2).mansa.integrable_sq ?_
  · have e1 : ∀ ξ, w 2 ξ * B ξ * (w 2 ξ)⁻¹ = B ξ := fun ξ => by
      have := w_pos 2 ξ; field_simp
    have e2 : ∀ ξ, ((w 2 ξ)⁻¹) ^ 2 = (w 4 ξ)⁻¹ := fun ξ => by
      rw [inv_pow, w_sq]
    simp_rw [e1, e2] at h
    rw [← I4] at h
    linarith
  · have e2 : ∀ ξ, ((w 2 ξ)⁻¹) ^ 2 = (w 4 ξ)⁻¹ := fun ξ => by
      rw [inv_pow, w_sq]
    simp_rw [e2]; exact integrable_w_inv

theorem L0_sq_le {f : E3 → C3} (hR : Rapida fun ξ => ‖f ξ‖) :
    (∫ ξ, ‖f ξ‖) ^ 2 ≤ I4 * J 2 f := by
  rw [← integral_wA_sq]; exact integral_sq_le_I4 hR

theorem L1_sq_le {f : E3 → C3} (hR : Rapida fun ξ => ‖f ξ‖) :
    (∫ ξ, ‖ξ‖ * ‖f ξ‖) ^ 2 ≤ I4 * J 3 f := by
  have h := integral_sq_le_I4 hR.norm_mul
  refine h.trans (mul_le_mul_of_nonneg_left ?_ I4_nonneg)
  have := integral_wP_sq_le hR 2
  exact this

theorem L0_pow8_le {f : E3 → C3} (hR : Rapida fun ξ => ‖f ξ‖) :
    (∫ ξ, ‖f ξ‖) ^ 8 ≤ c72 ^ 4 * J 1 f * J 2 f ^ 3 := by
  obtain ⟨C, hC⟩ := hR.bound 8
  have h := interp_L1 hR.cont hR.nonneg hC
  have e1 : ∫ ξ, (1 + ‖ξ‖) ^ 2 * ‖f ξ‖ ^ 2 = J 1 f := by
    unfold J; congr 1 with ξ; unfold w; ring
  have e2 : ∫ ξ, (1 + ‖ξ‖) ^ 4 * ‖f ξ‖ ^ 2 = J 2 f := by
    unfold J; congr 1 with ξ; unfold w; ring
  rw [e1, e2] at h
  exact h

theorem L1w_pow8_le {f : E3 → C3} (hR : Rapida fun ξ => ‖f ξ‖) :
    (∫ ξ, w 1 ξ * ‖f ξ‖) ^ 8 ≤ c72 ^ 4 * J 2 f * J 3 f ^ 3 := by
  obtain ⟨C, hC⟩ := (hR.mul_w 1).bound 8
  have h := interp_L1 (hR.mul_w 1).cont (hR.mul_w 1).nonneg hC
  have e1 : ∫ ξ, (1 + ‖ξ‖) ^ 2 * (w 1 ξ * ‖f ξ‖) ^ 2 = J 2 f := by
    unfold J; congr 1 with ξ; unfold w; ring
  have e2 : ∫ ξ, (1 + ‖ξ‖) ^ 4 * (w 1 ξ * ‖f ξ‖) ^ 2 = J 3 f := by
    unfold J; congr 1 with ξ; unfold w; ring
  rw [e1, e2] at h
  exact h


/-! ### As cotas de `T₁`, `T₂`, `T₃` -/

/-- Constantes. -/
noncomputable def ep (ν : ℝ) : ℝ := π * ν / 4

noncomputable def K1 (ν : ℝ) : ℝ := 8 * π * c72 ^ 4 / ep ν ^ 7

noncomputable def K2 (ν : ℝ) : ℝ := 8 * π * c72 ^ 4 / ep ν ^ 7

noncomputable def K2b (ν : ℝ) : ℝ := 8 * π * I4 / ep ν

noncomputable def K3 (ν : ℝ) : ℝ := 32 * π * I4 / (ep ν / 2)

theorem ep_pos {ν : ℝ} (hν : 0 < ν) : 0 < ep ν := by unfold ep; positivity

theorem K1_nonneg {ν : ℝ} (hν : 0 < ν) : 0 ≤ K1 ν := by
  have := ep_pos hν; have := c72_nonneg; unfold K1; positivity

theorem K2_nonneg {ν : ℝ} (hν : 0 < ν) : 0 ≤ K2 ν := by
  have := ep_pos hν; have := c72_nonneg; unfold K2; positivity

theorem K2b_nonneg {ν : ℝ} (hν : 0 < ν) : 0 ≤ K2b ν := by
  have := ep_pos hν; have := I4_nonneg; unfold K2b; positivity

theorem K3_nonneg {ν : ℝ} (hν : 0 < ν) : 0 ≤ K3 ν := by
  have := ep_pos hν; have := I4_nonneg; unfold K3; positivity

section

variable {f : E3 → C3} (hd : ∀ ξ, inner ℂ (cpx ξ) (f ξ) = 0) (hR : Rapida fun ξ => ‖f ξ‖)
include hd hR

/-- **`T₁`**: `2 T₁ ≤ 2π²ν J₂ + K₁ J₁⁵`. -/
theorem T1_le {ν : ℝ} (hν : 0 < ν) : 2 * Tn f 1 ≤ 2 * π ^ 2 * ν * J 2 f + K1 ν * J 1 f ^ 5 := by
  have h := Tn_le hd hR 0
  simp only [pow_zero, mul_one, w_zero, one_mul, zero_add] at h
  set S := S3 (fun ξ => w 2 ξ * ‖f ξ‖) (fun η => ‖f η‖) (fun ζ => ‖ζ‖ * ‖f ζ‖) with hS
  have hX := (hR.mul_w 2).mansa
  have hP := hR.norm_mul.mansa
  have hS0 : 0 ≤ S := S3_nonneg (hR.mul_w 2).nonneg hR.nonneg hR.norm_mul.nonneg
  have ht := tri_le hX hR.mansa hP
  rw [integral_wA_sq] at ht
  have hJ1 := J_nonneg 1 f
  have hJ2 := J_nonneg 2 f
  have hL := L0_pow8_le hR
  have hP2 := integral_P_sq_le hR
  have hS2 : S ^ 2 ≤ J 2 f * (∫ ξ, ‖f ξ‖) ^ 2 * J 1 f :=
    ht.trans (mul_le_mul_of_nonneg_left hP2 (by positivity))
  have hS8 : S ^ (7 + 1) ≤ c72 ^ 4 * J 2 f ^ 7 * J 1 f ^ 5 := by
    have h4 := pow_le_pow_left₀ (sq_nonneg S) hS2 4
    rw [← pow_mul] at h4
    calc S ^ (7 + 1) = S ^ (2 * 4) := by norm_num
      _ ≤ (J 2 f * (∫ ξ, ‖f ξ‖) ^ 2 * J 1 f) ^ 4 := h4
      _ = J 2 f ^ 4 * (∫ ξ, ‖f ξ‖) ^ 8 * J 1 f ^ 4 := by ring
      _ ≤ J 2 f ^ 4 * (c72 ^ 4 * J 1 f * J 2 f ^ 3) * J 1 f ^ 4 := by gcongr
      _ = c72 ^ 4 * J 2 f ^ 7 * J 1 f ^ 5 := by ring
  have hε := ep_pos hν
  have habs := absorve 7 hS0 hJ2 (pow_nonneg hJ1 5) (pow_nonneg c72_nonneg 4) hε hS8
  have e : 8 * π * ep ν = 2 * π ^ 2 * ν := by unfold ep; ring
  have hTS : Tn f 1 ≤ 2 * π * (S + S) := by simpa [hS] using h
  have : 2 * Tn f 1 ≤ 8 * π * S := by nlinarith [Real.pi_pos]
  calc 2 * Tn f 1 ≤ 8 * π * S := this
    _ ≤ 8 * π * (ep ν * J 2 f + c72 ^ 4 * J 1 f ^ 5 / ep ν ^ 7) := by
        have := Real.pi_pos; gcongr
    _ = 2 * π ^ 2 * ν * J 2 f + K1 ν * J 1 f ^ 5 := by
        rw [mul_add, ← mul_assoc, e]; unfold K1; ring

/-- **`T₂`**: `2 T₂ ≤ 4π²ν J₃ + (K₂ J₁⁴ + K₂' J₂) J₂`. -/
theorem T2_le {ν : ℝ} (hν : 0 < ν) :
    2 * Tn f 2 ≤ 4 * π ^ 2 * ν * J 3 f + (K2 ν * J 1 f ^ 4 + K2b ν * J 2 f) * J 2 f := by
  have h := Tn_le hd hR 1
  simp only [pow_one] at h
  set S1 := S3 (fun ξ => w (1 + 2) ξ * ‖f ξ‖) (fun η => w 1 η * ‖f η‖) (fun ζ => ‖ζ‖ * ‖f ζ‖)
    with hS1
  set S2 := S3 (fun ξ => w (1 + 2) ξ * ‖f ξ‖) (fun η => ‖f η‖)
    (fun ζ => w 1 ζ * (‖ζ‖ * ‖f ζ‖)) with hS2
  have hX := (hR.mul_w (1 + 2)).mansa
  have hS10 : 0 ≤ S1 := S3_nonneg (hR.mul_w _).nonneg (hR.mul_w 1).nonneg hR.norm_mul.nonneg
  have hS20 : 0 ≤ S2 := S3_nonneg (hR.mul_w _).nonneg hR.nonneg (hR.norm_mul.mul_w 1).nonneg
  have hJ1 := J_nonneg 1 f
  have hJ2 := J_nonneg 2 f
  have hJ3 := J_nonneg 3 f
  have hε := ep_pos hν
  -- S₁
  have t1 := tri_le hX (hR.mul_w 1).mansa hR.norm_mul.mansa
  rw [integral_wA_sq] at t1
  have hP2 := integral_P_sq_le hR
  have hL1 := L1w_pow8_le hR
  have hS1sq : S1 ^ 2 ≤ J 3 f * (∫ ξ, w 1 ξ * ‖f ξ‖) ^ 2 * J 1 f :=
    t1.trans (mul_le_mul_of_nonneg_left hP2 (by positivity))
  have hS18 : S1 ^ (7 + 1) ≤ c72 ^ 4 * J 3 f ^ 7 * (J 1 f ^ 4 * J 2 f) := by
    have h4 := pow_le_pow_left₀ (sq_nonneg S1) hS1sq 4
    rw [← pow_mul] at h4
    calc S1 ^ (7 + 1) = S1 ^ (2 * 4) := by norm_num
      _ ≤ (J 3 f * (∫ ξ, w 1 ξ * ‖f ξ‖) ^ 2 * J 1 f) ^ 4 := h4
      _ = J 3 f ^ 4 * (∫ ξ, w 1 ξ * ‖f ξ‖) ^ 8 * J 1 f ^ 4 := by ring
      _ ≤ J 3 f ^ 4 * (c72 ^ 4 * J 2 f * J 3 f ^ 3) * J 1 f ^ 4 := by gcongr
      _ = c72 ^ 4 * J 3 f ^ 7 * (J 1 f ^ 4 * J 2 f) := by ring
  have a1 := absorve 7 hS10 hJ3 (by positivity) (pow_nonneg c72_nonneg 4) hε hS18
  -- S₂
  have t2 := tri_le hX hR.mansa (hR.norm_mul.mul_w 1).mansa
  rw [integral_wA_sq] at t2
  have hwP := integral_wP_sq_le hR 1
  have hL0 := L0_sq_le hR
  have hS2sq : S2 ^ (1 + 1) ≤ I4 * J 3 f ^ 1 * (J 2 f * J 2 f) := by
    calc S2 ^ (1 + 1) = S2 ^ 2 := rfl
      _ ≤ J 3 f * (∫ ξ, ‖f ξ‖) ^ 2 * ∫ ζ, (w 1 ζ * (‖ζ‖ * ‖f ζ‖)) ^ 2 := t2
      _ ≤ J 3 f * (I4 * J 2 f) * J 2 f :=
          mul_le_mul (mul_le_mul_of_nonneg_left hL0 hJ3) hwP
            (integral_nonneg fun _ => sq_nonneg _) (mul_nonneg hJ3 (mul_nonneg I4_nonneg hJ2))
      _ = I4 * J 3 f ^ 1 * (J 2 f * J 2 f) := by ring
  have a2 := absorve 1 hS20 hJ3 (by positivity) I4_nonneg hε hS2sq
  have e : 16 * π * ep ν = 4 * π ^ 2 * ν := by unfold ep; ring
  have hT : 2 * Tn f 2 ≤ 8 * π * (S1 + S2) := by
    have : Tn f (1 + 1) ≤ 2 * π * 2 * (S1 + S2) := h
    norm_num at this
    nlinarith [Real.pi_pos]
  calc 2 * Tn f 2 ≤ 8 * π * (S1 + S2) := hT
    _ ≤ 8 * π * ((ep ν * J 3 f + c72 ^ 4 * (J 1 f ^ 4 * J 2 f) / ep ν ^ 7) +
          (ep ν * J 3 f + I4 * (J 2 f * J 2 f) / ep ν ^ 1)) := by
        have := Real.pi_pos; gcongr
    _ = 4 * π ^ 2 * ν * J 3 f + (K2 ν * J 1 f ^ 4 + K2b ν * J 2 f) * J 2 f := by
        rw [← e]; unfold K2 K2b; ring

/-- **`T₃`**: `2 T₃ ≤ 4π²ν J₄ + K₃ J₂ J₃`. -/
theorem T3_le {ν : ℝ} (hν : 0 < ν) :
    2 * Tn f 3 ≤ 4 * π ^ 2 * ν * J 4 f + K3 ν * J 2 f * J 3 f := by
  have h := Tn_le hd hR 2
  set S1 := S3 (fun ξ => w (2 + 2) ξ * ‖f ξ‖) (fun η => w 2 η * ‖f η‖) (fun ζ => ‖ζ‖ * ‖f ζ‖)
    with hS1
  set S2 := S3 (fun ξ => w (2 + 2) ξ * ‖f ξ‖) (fun η => ‖f η‖)
    (fun ζ => w 2 ζ * (‖ζ‖ * ‖f ζ‖)) with hS2
  have hX := (hR.mul_w (2 + 2)).mansa
  have hS10 : 0 ≤ S1 := S3_nonneg (hR.mul_w _).nonneg (hR.mul_w 2).nonneg hR.norm_mul.nonneg
  have hS20 : 0 ≤ S2 := S3_nonneg (hR.mul_w _).nonneg hR.nonneg (hR.norm_mul.mul_w 2).nonneg
  have hJ2 := J_nonneg 2 f
  have hJ3 := J_nonneg 3 f
  have hJ4 := J_nonneg 4 f
  have hε : 0 < ep ν / 2 := by have := ep_pos hν; positivity
  -- S₁ (P em L¹)
  have t1 := tri_leZ hX (hR.mul_w 2).mansa hR.norm_mul.mansa
  rw [integral_wA_sq, integral_wA_sq] at t1
  have hL1 := L1_sq_le hR
  have hS1sq : S1 ^ (1 + 1) ≤ I4 * J 4 f ^ 1 * (J 2 f * J 3 f) := by
    calc S1 ^ (1 + 1) = S1 ^ 2 := rfl
      _ ≤ J (2 + 2) f * J 2 f * (∫ ζ, ‖ζ‖ * ‖f ζ‖) ^ 2 := t1
      _ ≤ J 4 f * J 2 f * (I4 * J 3 f) := mul_le_mul_of_nonneg_left hL1 (mul_nonneg hJ4 hJ2)
      _ = I4 * J 4 f ^ 1 * (J 2 f * J 3 f) := by ring
  have a1 := absorve 1 hS10 hJ4 (by positivity) I4_nonneg hε hS1sq
  -- S₂
  have t2 := tri_le hX hR.mansa (hR.norm_mul.mul_w 2).mansa
  rw [integral_wA_sq] at t2
  have hwP := integral_wP_sq_le hR 2
  have hL0 := L0_sq_le hR
  have hS2sq : S2 ^ (1 + 1) ≤ I4 * J 4 f ^ 1 * (J 2 f * J 3 f) := by
    calc S2 ^ (1 + 1) = S2 ^ 2 := rfl
      _ ≤ J (2 + 2) f * (∫ ξ, ‖f ξ‖) ^ 2 * ∫ ζ, (w 2 ζ * (‖ζ‖ * ‖f ζ‖)) ^ 2 := t2
      _ ≤ J 4 f * (I4 * J 2 f) * J 3 f :=
          mul_le_mul (mul_le_mul_of_nonneg_left hL0 hJ4) hwP
            (integral_nonneg fun _ => sq_nonneg _) (mul_nonneg hJ4 (mul_nonneg I4_nonneg hJ2))
      _ = I4 * J 4 f ^ 1 * (J 2 f * J 3 f) := by ring
  have a2 := absorve 1 hS20 hJ4 (by positivity) I4_nonneg hε hS2sq
  have e : 32 * π * (ep ν / 2) = 4 * π ^ 2 * ν := by unfold ep; ring
  have hT : 2 * Tn f 3 ≤ 16 * π * (S1 + S2) := by
    have : Tn f (2 + 1) ≤ 2 * π * 2 ^ 2 * (S1 + S2) := h
    norm_num at this
    nlinarith [Real.pi_pos]
  calc 2 * Tn f 3 ≤ 16 * π * (S1 + S2) := hT
    _ ≤ 16 * π * ((ep ν / 2 * J 4 f + I4 * (J 2 f * J 3 f) / (ep ν / 2) ^ 1) +
          (ep ν / 2 * J 4 f + I4 * (J 2 f * J 3 f) / (ep ν / 2) ^ 1)) := by
        have := Real.pi_pos; gcongr
    _ = 4 * π ^ 2 * ν * J 4 f + K3 ν * J 2 f * J 3 f := by
        rw [← e]; unfold K3; ring

end

end ATK.NSAltaOrdem

#print axioms ATK.NSAltaOrdem.w_sq
#print axioms ATK.NSAltaOrdem.w_inv_mul_w_sq
#print axioms ATK.NSAltaOrdem.wsq_mul_le
#print axioms ATK.NSAltaOrdem.J_nonneg
#print axioms ATK.NSAltaOrdem.BoaW.integrable_J
#print axioms ATK.NSAltaOrdem.BoaW.wsq_re_inner_bound
#print axioms ATK.NSAltaOrdem.BoaW.continuous_wsq_re_inner
#print axioms ATK.NSAltaOrdem.continuous_D
#print axioms ATK.NSAltaOrdem.continuous_J
#print axioms ATK.NSAltaOrdem.J_sub_eq
#print axioms ATK.NSAltaOrdem.hasDerivAt_J
#print axioms ATK.NSAltaOrdem.gronwall
#print axioms ATK.NSAltaOrdem.Rapida.mansa
#print axioms ATK.NSAltaOrdem.Rapida.integrable
#print axioms ATK.NSAltaOrdem.Rapida.C_nonneg
#print axioms ATK.NSAltaOrdem.Rapida.mul_w
#print axioms ATK.NSAltaOrdem.Rapida.norm_mul
#print axioms ATK.NSAltaOrdem.Rapida.of_norm
#print axioms ATK.NSAltaOrdem.BoaW.rapida
#print axioms ATK.NSAltaOrdem.cv_eq_convolution
#print axioms ATK.NSAltaOrdem.Rapida.integrable_cv_integrand
#print axioms ATK.NSAltaOrdem.Rapida.cv
#print axioms ATK.NSAltaOrdem.integral_mul_cv
#print axioms ATK.NSAltaOrdem.w_mul_cv_le
#print axioms ATK.NSAltaOrdem.norm_Nl_le_cv
#print axioms ATK.NSAltaOrdem.Tn_nonneg
#print axioms ATK.NSAltaOrdem.BoaW.integrable_wsq_mul_norm
#print axioms ATK.NSAltaOrdem.dissip_le
#print axioms ATK.NSAltaOrdem.D_le
#print axioms ATK.NSAltaOrdem.S3_nonneg
#print axioms ATK.NSAltaOrdem.Rapida.mul
#print axioms ATK.NSAltaOrdem.Tn_le
#print axioms ATK.NSAltaOrdem.w_zero
#print axioms ATK.NSAltaOrdem.integral_wA_sq
#print axioms ATK.NSAltaOrdem.integral_wP_sq_le
#print axioms ATK.NSAltaOrdem.integral_P_sq_le
#print axioms ATK.NSAltaOrdem.integral_sq_le_I4
#print axioms ATK.NSAltaOrdem.L0_sq_le
#print axioms ATK.NSAltaOrdem.L1_sq_le
#print axioms ATK.NSAltaOrdem.L0_pow8_le
#print axioms ATK.NSAltaOrdem.L1w_pow8_le
#print axioms ATK.NSAltaOrdem.ep_pos
#print axioms ATK.NSAltaOrdem.K1_nonneg
#print axioms ATK.NSAltaOrdem.K2_nonneg
#print axioms ATK.NSAltaOrdem.K2b_nonneg
#print axioms ATK.NSAltaOrdem.K3_nonneg
#print axioms ATK.NSAltaOrdem.T1_le
#print axioms ATK.NSAltaOrdem.T2_le
#print axioms ATK.NSAltaOrdem.T3_le
