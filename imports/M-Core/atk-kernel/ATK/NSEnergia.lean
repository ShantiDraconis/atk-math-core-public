import ATK.NSMaximal

/-!
# ATK — Navier–Stokes, marco NS7a: energia, cancelamento e a estimativa de enstrofia

Ponte B3, marco NS7 (primeira parte), no lado de Fourier. Para uma fatia `f : ℝ³ → ℂ³`:

* `Q k f = ∫ |ξ|^{2k} |f(ξ)|²` (energia `Q 0`, enstrofia `Q 1` a menos de `4π²`), `L1 f = ∫ |f|`;
* **`L1_sq_le`** (interpolação por escala): `(L1 f)² ≤ (I₁+1) r⁻³ (Q 0 f + r⁴ Q 2 f)`;
* **`integral_inner_Bq`** (cancelamento de energia): `∫ ⟨f(ξ), 𝐏(ξ)(−2πi N(f,f))(ξ)⟩ dξ = 0` para
  `f` de divergência nula e hermitiana — a versão de Fourier de `∫ (u·∇)u·u = 0`;
* **`termo_enstrofia_le`**: `∫ |ξ|² |f| |B(f)| ≤ 2π L1(f) (μ Q 2 f + Q 1 f / μ)` para todo `μ > 0`.

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta**; **CLOSED_MATH continua
false**.
-/

set_option autoImplicit false

open MeasureTheory Real Set Filter Topology
open ATK.LigacaoNS (E3)
open ATK.NSFourierBase ATK.NSPicard ATK.NSRegular ATK.NSEquacao

namespace ATK.NSEnergia

/-! ### Ferramentas elementares -/

/-- Média aritmética–geométrica com parâmetro. -/
theorem amgm (a b : ℝ) {μ : ℝ} (hμ : 0 < μ) : a * b ≤ (μ * a ^ 2 + b ^ 2 / μ) / 2 := by
  have h : 0 ≤ (μ * a - b) ^ 2 / μ := by positivity
  have e : (μ * a ^ 2 + b ^ 2 / μ) / 2 - a * b = (μ * a - b) ^ 2 / μ / 2 := by
    field_simp
    ring
  linarith

/-- `x ≤ (μ / w + w x² / μ) / 2`. -/
theorem amgm_w (x : ℝ) {w μ : ℝ} (hw : 0 < w) (hμ : 0 < μ) :
    x ≤ (μ * w⁻¹ + w * x ^ 2 / μ) / 2 := by
  have h : 0 ≤ (μ - w * x) ^ 2 / (w * μ) := by positivity
  have e : (μ * w⁻¹ + w * x ^ 2 / μ) / 2 - x = (μ - w * x) ^ 2 / (w * μ) / 2 := by
    field_simp
    ring
  linarith

/-- Se `x ≤ (μ A + B/μ)/2` para todo `μ > 0`, então `x² ≤ A B`. -/
theorem sq_le_of_forall {x A B : ℝ} (hx : 0 ≤ x) (hA : 0 < A) (hB : 0 ≤ B)
    (h : ∀ μ > 0, x ≤ (μ * A + B / μ) / 2) : x ^ 2 ≤ A * B := by
  rcases hB.eq_or_lt with hB0 | hBp
  · rw [← hB0, mul_zero]
    rcases hx.eq_or_lt with h0 | h0
    · rw [← h0]
      norm_num
    · have := h (x / A) (by positivity)
      rw [← hB0, zero_div, add_zero, div_mul_cancel₀ _ hA.ne'] at this
      linarith
  · set s := sqrt (A * B)
    have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
    have hs2 : s ^ 2 = A * B := Real.sq_sqrt (by positivity)
    have := h (s / A) (by positivity)
    have e1 : s / A * A = s := div_mul_cancel₀ _ hA.ne'
    have e2 : B / (s / A) = s := by
      rw [div_div_eq_mul_div, div_eq_iff hs.ne']
      nlinarith [hs2]
    rw [e1, e2] at this
    have hxs : x ≤ s := by linarith
    calc x ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hx hxs 2
      _ = A * B := hs2

/-- Derivada de uma integral com parâmetro (valores num espaço de Banach qualquer). -/
theorem hasDerivWithinAt_integral_gen {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {F F' : ℝ → E3 → V} {s : Set ℝ} (hs : Convex ℝ s) {t₀ : ℝ}
    (ht₀ : t₀ ∈ s) (hmeas : ∀ t ∈ s, AEStronglyMeasurable (F t)) (hint : Integrable (F t₀))
    {b : E3 → ℝ} (hb : Integrable b)
    (hderiv : ∀ η, ∀ t ∈ s, HasDerivWithinAt (fun t => F t η) (F' t η) s t)
    (hbound : ∀ η, ∀ t ∈ s, ‖F' t η‖ ≤ b η) :
    HasDerivWithinAt (fun t => ∫ η, F t η) (∫ η, F' t₀ η) s t₀ := by
  have hmvt : ∀ η, ∀ t ∈ s, ‖F t η - F t₀ η‖ ≤ b η * ‖t - t₀‖ := fun η t ht =>
    hs.norm_image_sub_le_of_norm_hasDerivWithin_le (hderiv η) (hbound η) ht₀ ht
  have hintt : ∀ t ∈ s, Integrable (F t) := by
    intro t ht
    have h1 : Integrable (fun η => F t η - F t₀ η) :=
      (hb.mul_const ‖t - t₀‖).mono' ((hmeas t ht).sub hint.aestronglyMeasurable)
        (Eventually.of_forall fun η => hmvt η t ht)
    have := h1.add hint
    refine this.congr (Eventually.of_forall fun η => ?_)
    simp
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hev : ∀ᶠ t in 𝓝[s \ {t₀}] t₀, t ∈ s \ {t₀} := self_mem_nhdsWithin
  have hslope : ∀ᶠ t in 𝓝[s \ {t₀}] t₀,
      slope (fun t => ∫ η, F t η) t₀ t = ∫ η, slope (fun t => F t η) t₀ t := by
    filter_upwards [hev] with t ht
    simp only [slope_def_module]
    rw [integral_smul, integral_sub (hintt t ht.1) hint]
  refine Tendsto.congr' (EventuallyEq.symm hslope) ?_
  refine tendsto_integral_filter_of_dominated_convergence b ?_ ?_ hb ?_
  · filter_upwards [hev] with t ht
    simp only [slope_def_module]
    exact (((hmeas t ht.1).sub hint.aestronglyMeasurable).const_smul (t - t₀)⁻¹)
  · filter_upwards [hev] with t ht
    refine Eventually.of_forall fun η => ?_
    simp only [slope_def_module]
    have hne : t - t₀ ≠ 0 := sub_ne_zero.mpr ht.2
    rw [norm_smul, norm_inv]
    have := hmvt η t ht.1
    rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hne)]
    linarith [mul_comm (b η) ‖t - t₀‖]
  · exact Eventually.of_forall fun η =>
      (hasDerivWithinAt_iff_tendsto_slope.mp (hderiv η t₀ ht₀))

/-! ### Os momentos `Q k` e a norma `L1` -/

/-- `Q k f = ∫ |ξ|^{2k} |f(ξ)|²`. -/
noncomputable def Q (k : ℕ) (f : E3 → C3) : ℝ := ∫ ξ, ‖ξ‖ ^ (2 * k) * ‖f ξ‖ ^ 2

/-- `L1 f = ∫ |f|` (a norma de Wiener). -/
noncomputable def L1 (f : E3 → C3) : ℝ := ∫ ξ, ‖f ξ‖

theorem Q_nonneg (k : ℕ) (f : E3 → C3) : 0 ≤ Q k f :=
  integral_nonneg fun ξ => by positivity

theorem L1_nonneg (f : E3 → C3) : 0 ≤ L1 f :=
  integral_nonneg fun _ => norm_nonneg _

theorem bound_Q {m k : ℕ} (hmk : k + 2 ≤ m) {C : ℝ} {f : E3 → C3} (h : Cota m C f) (ξ : E3) :
    ‖ξ‖ ^ (2 * k) * ‖f ξ‖ ^ 2 ≤ C ^ 2 * ((1 + ‖ξ‖) ^ 4)⁻¹ := by
  have hw : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
  have h1 := h ξ
  have h2 : (‖f ξ‖ * (1 + ‖ξ‖) ^ m) ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have h3 : ‖ξ‖ ^ (2 * k) ≤ (1 + ‖ξ‖) ^ (2 * k) :=
    pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
  have h4 : (1 + ‖ξ‖) ^ (2 * k) * (1 + ‖ξ‖) ^ 4 ≤ ((1 + ‖ξ‖) ^ m) ^ 2 := by
    rw [← pow_add, ← pow_mul]
    exact pow_le_pow_right₀ hw (by omega)
  rw [le_mul_inv_iff₀ (by positivity)]
  calc ‖ξ‖ ^ (2 * k) * ‖f ξ‖ ^ 2 * (1 + ‖ξ‖) ^ 4
      ≤ (1 + ‖ξ‖) ^ (2 * k) * ‖f ξ‖ ^ 2 * (1 + ‖ξ‖) ^ 4 := by gcongr
    _ = ‖f ξ‖ ^ 2 * ((1 + ‖ξ‖) ^ (2 * k) * (1 + ‖ξ‖) ^ 4) := by ring
    _ ≤ ‖f ξ‖ ^ 2 * ((1 + ‖ξ‖) ^ m) ^ 2 := by gcongr
    _ = (‖f ξ‖ * (1 + ‖ξ‖) ^ m) ^ 2 := by ring
    _ ≤ C ^ 2 := h2

theorem integrable_Q {m k : ℕ} (hmk : k + 2 ≤ m) {C : ℝ} {f : E3 → C3} (hf : Continuous f)
    (h : Cota m C f) : Integrable (fun ξ => ‖ξ‖ ^ (2 * k) * ‖f ξ‖ ^ 2) := by
  have hc : Continuous fun ξ : E3 => ‖ξ‖ ^ (2 * k) * ‖f ξ‖ ^ 2 := by fun_prop
  refine ((integrable_inv_pow (le_refl 4)).const_mul (C ^ 2)).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact bound_Q hmk h ξ

theorem integrable_norm_of_cota {C : ℝ} {f : E3 → C3} (hf : Continuous f) (h : Cota 4 C f) :
    Integrable (fun ξ => ‖f ξ‖) := by
  refine ((integrable_inv_pow (le_refl 4)).const_mul C).mono' hf.norm.aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [norm_norm]
  exact h.le_inv ξ

/-! ### Interpolação por escala -/

/-- `I₁ = ∫ (1 + |ξ|⁴)⁻¹`. -/
noncomputable def I₁ : ℝ := ∫ ξ : E3, (1 + ‖ξ‖ ^ 4)⁻¹

theorem one_add_pow_four_le {x : ℝ} (hx : 0 ≤ x) : (1 + x) ^ 4 ≤ 8 * (1 + x ^ 4) := by
  have h : 0 ≤ (x - 1) ^ 2 * (7 * x ^ 2 + 10 * x + 7) := by positivity
  nlinarith [h]

theorem integrable_w : Integrable (fun ξ : E3 => (1 + ‖ξ‖ ^ 4)⁻¹) := by
  have hc : Continuous fun ξ : E3 => (1 + ‖ξ‖ ^ 4)⁻¹ :=
    (continuous_const.add (continuous_norm.pow 4)).inv₀ fun ξ =>
      (by positivity : (0 : ℝ) < 1 + ‖ξ‖ ^ 4).ne'
  refine ((integrable_inv_pow (le_refl 4)).const_mul 8).mono' hc.aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 := one_add_pow_four_le (norm_nonneg ξ)
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  calc (1 : ℝ) = 8 * ((1 + ‖ξ‖) ^ 4)⁻¹ * ((1 + ‖ξ‖) ^ 4 / 8) := by field_simp
    _ ≤ 8 * ((1 + ‖ξ‖) ^ 4)⁻¹ * (1 + ‖ξ‖ ^ 4) := by gcongr; linarith

theorem integral_w_scale {r : ℝ} (hr : 0 < r) :
    ∫ ξ : E3, (1 + r ^ 4 * ‖ξ‖ ^ 4)⁻¹ = (r ^ 3)⁻¹ * I₁ := by
  have h := Measure.integral_comp_smul (volume : Measure E3) (fun ξ : E3 => (1 + ‖ξ‖ ^ 4)⁻¹) r
  rw [finrank_E3] at h
  have e : (fun ξ : E3 => (1 + ‖r • ξ‖ ^ 4)⁻¹) = fun ξ => (1 + r ^ 4 * ‖ξ‖ ^ 4)⁻¹ := by
    funext ξ
    rw [norm_smul, Real.norm_of_nonneg hr.le, mul_pow]
  rw [e] at h
  rw [h, abs_of_pos (by positivity), smul_eq_mul]
  rfl

theorem integrable_w_scale {r : ℝ} (hr : 0 < r) :
    Integrable (fun ξ : E3 => (1 + r ^ 4 * ‖ξ‖ ^ 4)⁻¹) := by
  have h := integrable_w.comp_smul hr.ne'
  refine h.congr (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [norm_smul, Real.norm_of_nonneg hr.le, mul_pow]

/-- **Interpolação**: `(L1 f)² ≤ (I₁+1) r⁻³ (Q 0 f + r⁴ Q 2 f)` para todo `r > 0`. -/
theorem L1_sq_le {C : ℝ} {f : E3 → C3} (hf : Continuous f) (h : Cota 4 C f) {r : ℝ}
    (hr : 0 < r) : L1 f ^ 2 ≤ (r ^ 3)⁻¹ * (I₁ + 1) * (Q 0 f + r ^ 4 * Q 2 f) := by
  have hI0 : 0 ≤ I₁ := integral_nonneg fun ξ => by positivity
  have hQ0 := integrable_Q (k := 0) (by norm_num) hf h
  have hQ2 := integrable_Q (k := 2) (by norm_num) hf h
  have hL := integrable_norm_of_cota hf h
  refine sq_le_of_forall (L1_nonneg f) (by positivity)
    (by have := Q_nonneg 0 f; have := Q_nonneg 2 f; positivity) fun μ hμ => ?_
  set w : E3 → ℝ := fun ξ => 1 + r ^ 4 * ‖ξ‖ ^ 4
  have hw : ∀ ξ, 0 < w ξ := fun ξ => by positivity
  have hpt : ∀ ξ, ‖f ξ‖ ≤ (μ * (w ξ)⁻¹ + w ξ * ‖f ξ‖ ^ 2 / μ) / 2 :=
    fun ξ => amgm_w _ (hw ξ) hμ
  have hi1 : Integrable fun ξ => μ * (w ξ)⁻¹ := (integrable_w_scale hr).const_mul μ
  have hi2 : Integrable fun ξ => w ξ * ‖f ξ‖ ^ 2 / μ := by
    have : (fun ξ => w ξ * ‖f ξ‖ ^ 2 / μ) =
        fun ξ => (‖ξ‖ ^ (2 * 0) * ‖f ξ‖ ^ 2 + r ^ 4 * (‖ξ‖ ^ (2 * 2) * ‖f ξ‖ ^ 2)) / μ := by
      funext ξ
      simp only [w]
      ring
    rw [this]
    exact (hQ0.add (hQ2.const_mul _)).div_const μ
  have hmono : ∫ ξ, ‖f ξ‖ ≤ ∫ ξ, (μ * (w ξ)⁻¹ + w ξ * ‖f ξ‖ ^ 2 / μ) / 2 :=
    integral_mono hL ((hi1.add hi2).div_const 2) hpt
  have e : ∫ ξ, (μ * (w ξ)⁻¹ + w ξ * ‖f ξ‖ ^ 2 / μ) / 2 =
      (μ * ((r ^ 3)⁻¹ * (I₁ + 1)) + (Q 0 f + r ^ 4 * Q 2 f) / μ) / 2 - μ * (r ^ 3)⁻¹ / 2 := by
    rw [integral_div, integral_add hi1 hi2, integral_const_mul, integral_div]
    have e1 : ∫ ξ, (w ξ)⁻¹ = (r ^ 3)⁻¹ * I₁ := integral_w_scale hr
    have e2 : ∫ ξ, w ξ * ‖f ξ‖ ^ 2 = Q 0 f + r ^ 4 * Q 2 f := by
      have : (fun ξ => w ξ * ‖f ξ‖ ^ 2) =
          fun ξ => ‖ξ‖ ^ (2 * 0) * ‖f ξ‖ ^ 2 + r ^ 4 * (‖ξ‖ ^ (2 * 2) * ‖f ξ‖ ^ 2) := by
        funext ξ
        simp only [w]
        ring
      rw [this, integral_add hQ0 (hQ2.const_mul _), integral_const_mul]
      rfl
    rw [e1, e2]
    ring
  have hμr : 0 ≤ μ * (r ^ 3)⁻¹ / 2 := by positivity
  unfold L1
  linarith


/-! ### O cancelamento de energia -/

theorem inner_leray_of_ip {ξ : E3} {a : C3} (h : ip ξ a = 0) (b : C3) :
    inner ℂ a (leray ξ b) = inner ℂ a b := by
  rw [leray_apply, inner_sub_right, inner_smul_right]
  have : inner ℂ a (cx ξ) = 0 := by
    rw [← inner_conj_symm, ← ip_eq_inner, h, map_zero]
  rw [this, mul_zero, sub_zero]

theorem inner_cj (a b : C3) : inner ℂ (cj a) (cj b) = inner ℂ b a := by
  simp [PiLp.inner_apply, mul_comm]

theorem ip_sub_eq {f : E3 → C3} (hd : ∀ ξ, ip ξ (f ξ) = 0) (ξ η : E3) :
    ip η (f (ξ - η)) = ip ξ (f (ξ - η)) := by
  have h := ip_sub_left ξ η (f (ξ - η))
  rw [hd] at h
  linear_combination h

/-- **Cancelamento de energia** (`∫ (u·∇)u·u = 0` no lado de Fourier). -/
theorem integral_inner_Bq {f : E3 → C3} (hf : Continuous f) (hC : ∀ m, ∃ C, Cota m C f)
    (hd : ∀ ξ, ip ξ (f ξ) = 0) (hh : ∀ ξ, f (-ξ) = cj (f ξ)) :
    ∫ ξ, inner ℂ (f ξ) (Bq f ξ) = 0 := by
  obtain ⟨C0, h0⟩ := hC 0
  obtain ⟨C4, h4⟩ := hC 4
  obtain ⟨C5, h5⟩ := hC 5
  set K : E3 → E3 → ℂ := fun ξ η => ip ξ (f (ξ - η)) * inner ℂ (f ξ) (f η) with hK
  have hpt : ∀ ξ, inner ℂ (f ξ) (Bq f ξ) = cI * ∫ η, K ξ η := by
    intro ξ
    unfold Bq
    rw [inner_leray_of_ip (hd ξ), inner_smul_right, nl,
      ← integral_inner (integrable_nl hf hf h4 h4 ξ)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun η => ?_)
    simp only [hK]
    rw [inner_smul_right]
  -- integrabilidade no produto
  have hKc : Continuous (Function.uncurry K) := by
    have h1 : Continuous fun z : E3 × E3 => ip z.1 (f (z.1 - z.2)) :=
      continuous_ip.comp (continuous_fst.prodMk (hf.comp (continuous_fst.sub continuous_snd)))
    have h2 : Continuous fun z : E3 × E3 => inner ℂ (f z.1) (f z.2) :=
      (hf.comp continuous_fst).inner (hf.comp continuous_snd)
    exact h1.mul h2
  have hKint : Integrable (Function.uncurry K) (volume.prod volume) := by
    have hb := ((integrable_inv_pow (le_refl 4)).const_mul (C0 * C5)).mul_prod
      ((integrable_inv_pow (le_refl 4)).const_mul C4)
    refine hb.mono' hKc.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    obtain ⟨ξ, η⟩ := z
    simp only [Function.uncurry_apply_pair, hK, norm_mul]
    have e1 := norm_ip_le ξ (f (ξ - η))
    have e2 := norm_inner_le_norm (𝕜 := ℂ) (f ξ) (f η)
    have e3 : ‖f (ξ - η)‖ ≤ C0 := h0.le _
    have e4 : ‖ξ‖ * ‖f ξ‖ ≤ C5 * ((1 + ‖ξ‖) ^ 4)⁻¹ := by
      have := h5.le_inv ξ
      have hw : 0 < 1 + ‖ξ‖ := by positivity
      have e : C5 * ((1 + ‖ξ‖) ^ 5)⁻¹ * (1 + ‖ξ‖) = C5 * ((1 + ‖ξ‖) ^ 4)⁻¹ := by
        field_simp
      calc ‖ξ‖ * ‖f ξ‖ ≤ (1 + ‖ξ‖) * ‖f ξ‖ := by gcongr; linarith
        _ ≤ (1 + ‖ξ‖) * (C5 * ((1 + ‖ξ‖) ^ 5)⁻¹) := by gcongr
        _ = C5 * ((1 + ‖ξ‖) ^ 4)⁻¹ := by rw [mul_comm, e]
    have e5 : ‖f η‖ ≤ C4 * ((1 + ‖η‖) ^ 4)⁻¹ := h4.le_inv η
    have hC0 : 0 ≤ C0 := h0.nonneg
    have hC5 : 0 ≤ C5 := h5.nonneg
    calc ‖ip ξ (f (ξ - η))‖ * ‖inner ℂ (f ξ) (f η)‖
        ≤ (‖ξ‖ * ‖f (ξ - η)‖) * (‖f ξ‖ * ‖f η‖) := by gcongr
      _ = ‖f (ξ - η)‖ * (‖ξ‖ * ‖f ξ‖) * ‖f η‖ := by ring
      _ ≤ C0 * (C5 * ((1 + ‖ξ‖) ^ 4)⁻¹) * (C4 * ((1 + ‖η‖) ^ 4)⁻¹) := by gcongr
      _ = C0 * C5 * ((1 + ‖ξ‖) ^ 4)⁻¹ * (C4 * ((1 + ‖η‖) ^ 4)⁻¹) := by ring
  -- antissimetria
  have hsym : ∀ ξ η, K (-η) (-ξ) = -K ξ η := by
    intro ξ η
    simp only [hK]
    rw [neg_sub_neg, ip_neg_left, hh, hh, inner_cj, ip_sub_eq hd]
    ring
  have hS : ∫ ξ, ∫ η, K ξ η = 0 := by
    have h1 : ∫ ξ, ∫ η, K ξ η = -∫ ξ, ∫ η, K (-η) (-ξ) := by
      rw [← integral_neg]
      congr 1
      funext ξ
      rw [← integral_neg]
      congr 1
      funext η
      rw [hsym, neg_neg]
    have hint2 : Integrable (Function.uncurry fun ξ η => K (-η) (-ξ)) (volume.prod volume) := by
      refine hKint.neg.congr (Eventually.of_forall fun z => ?_)
      obtain ⟨ξ, η⟩ := z
      simp only [Function.uncurry_apply_pair, Pi.neg_apply]
      rw [hsym]
    have h2 : ∫ ξ, ∫ η, K (-η) (-ξ) = ∫ η, ∫ ξ, K (-η) (-ξ) := integral_integral_swap hint2
    have h3 : ∫ η, ∫ ξ, K (-η) (-ξ) = ∫ ξ, ∫ η, K ξ η := by
      have : (fun η => ∫ ξ, K (-η) (-ξ)) = fun η => ∫ ξ, K (-η) ξ := by
        funext η
        exact integral_neg_eq_self (fun ξ => K (-η) ξ) volume
      rw [this]
      exact integral_neg_eq_self (fun η => ∫ ξ, K η ξ) volume
    rw [h2, h3] at h1
    have h4 : (2 : ℂ) * ∫ ξ, ∫ η, K ξ η = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h4 with h | h
    · norm_num at h
    · exact h
  calc ∫ ξ, inner ℂ (f ξ) (Bq f ξ) = ∫ ξ, cI * ∫ η, K ξ η :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = cI * ∫ ξ, ∫ η, K ξ η := integral_const_mul _ _
    _ = 0 := by rw [hS, mul_zero]


/-! ### O termo não linear da enstrofia -/

/-- **Estimativa do termo não linear da enstrofia**:
`∫ |ξ|² |f| |B(f)| ≤ 2π L1(f) (μ Q 2 f + Q 1 f / μ)` para todo `μ > 0`. -/
theorem termo_enstrofia_le {f : E3 → C3} (hf : Continuous f) (hC : ∀ m, ∃ C, Cota m C f)
    {μ : ℝ} (hμ : 0 < μ) :
    ∫ ξ, ‖ξ‖ ^ 2 * (‖f ξ‖ * ‖Bq f ξ‖) ≤ 2 * π * (L1 f * (μ * Q 2 f + Q 1 f / μ)) := by
  obtain ⟨C0, h0⟩ := hC 0
  obtain ⟨C4, h4⟩ := hC 4
  have hC0 : 0 ≤ C0 := h0.nonneg
  set a : E3 → ℝ := fun ζ => ‖f ζ‖ with ha_def
  set g : E3 → ℝ := fun ζ => ‖ζ‖ ^ (2 * 1) * ‖f ζ‖ ^ 2 with hg_def
  set X2 : E3 → ℝ := fun ζ => ‖ζ‖ ^ (2 * 2) * ‖f ζ‖ ^ 2 with hX2_def
  have hac : Continuous a := hf.norm
  have hgc : Continuous g := by simp only [hg_def]; fun_prop
  have ha : Integrable a := integrable_norm_of_cota hf h4
  have hg : Integrable g := integrable_Q (k := 1) (by norm_num) hf h4
  have hX2 : Integrable X2 := integrable_Q (k := 2) (by norm_num) hf h4
  have hgC : ∀ ζ, g ζ ≤ C4 ^ 2 := by
    intro ζ
    have h1 := bound_Q (k := 1) (by norm_num) h4 ζ
    have h2 : ((1 + ‖ζ‖) ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg ζ]))
    have h3 : C4 ^ 2 * ((1 + ‖ζ‖) ^ 4)⁻¹ ≤ C4 ^ 2 := by
      calc C4 ^ 2 * ((1 + ‖ζ‖) ^ 4)⁻¹ ≤ C4 ^ 2 * 1 := by gcongr
        _ = C4 ^ 2 := mul_one _
    exact h1.trans h3
  have hg0 : ∀ ζ, 0 ≤ g ζ := fun ζ => by positivity
  have haC : ∀ ζ, a ζ ≤ C0 := h0.le
  set A : E3 → ℝ := fun ξ => ∫ η, g (ξ - η) * a η with hA_def
  set B : E3 → ℝ := fun ξ => ∫ η, a (ξ - η) * g η with hB_def
  have hAconv : A = convolution a g (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext ξ
    simp only [hA_def, convolution_def, ContinuousLinearMap.mul_apply']
    congr 1
    funext η
    ring
  have hBconv : B = convolution g a (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext ξ
    simp only [hB_def, convolution_def, ContinuousLinearMap.mul_apply']
    congr 1
    funext η
    ring
  have hAint : Integrable A := by
    rw [hAconv]
    exact ha.integrable_convolution _ hg
  have hBint : Integrable B := by
    rw [hBconv]
    exact hg.integrable_convolution _ ha
  have hAI : ∫ ξ, A ξ = L1 f * Q 1 f := by
    rw [hAconv, integral_convolution _ ha hg]
    rfl
  have hBI : ∫ ξ, B ξ = Q 1 f * L1 f := by
    rw [hBconv, integral_convolution _ hg ha]
    rfl
  set R : E3 → ℝ := fun ξ => 2 * π * (μ * L1 f * X2 ξ + (A ξ + B ξ) / (2 * μ)) with hR_def
  have hR : Integrable R :=
    ((hX2.const_mul (μ * L1 f)).add ((hAint.add hBint).div_const (2 * μ))).const_mul (2 * π)
  have hpt : ∀ ξ, ‖ξ‖ ^ 2 * (‖f ξ‖ * ‖Bq f ξ‖) ≤ R ξ := by
    intro ξ
    have hconv : Integrable fun η => a (ξ - η) * a η :=
      integrable_conv hac.aestronglyMeasurable hac.aestronglyMeasurable (fun _ => norm_nonneg _)
        (fun _ => norm_nonneg _) h4 h4 ξ
    have hB1 : ‖Bq f ξ‖ ≤ 2 * π * (‖ξ‖ * ∫ η, a (ξ - η) * a η) :=
      (norm_Bq_le_nl f ξ).trans (by gcongr; exact norm_nl_le_conv hf hf h4 h4 ξ)
    set Bd : E3 → ℝ := fun η => μ / 2 * X2 ξ * (a η + a (ξ - η)) +
      (g (ξ - η) * a η + a (ξ - η) * g η) / (2 * μ) with hBd_def
    have hi1 : Integrable fun η => a (ξ - η) := ha.comp_sub_left ξ
    have hi2 : Integrable fun η => g (ξ - η) * a η := by
      refine (ha.const_mul (C4 ^ 2)).mono'
        ((hgc.comp (continuous_const.sub continuous_id)).mul hac).aestronglyMeasurable
        (Eventually.of_forall fun η => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (hg0 _) (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hgC _) (norm_nonneg _)
    have hi3 : Integrable fun η => a (ξ - η) * g η := by
      refine (hg.const_mul C0).mono'
        ((hac.comp (continuous_const.sub continuous_id)).mul hgc).aestronglyMeasurable
        (Eventually.of_forall fun η => ?_)
      rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (hg0 _))]
      exact mul_le_mul_of_nonneg_right (haC _) (hg0 _)
    have hBdi : Integrable Bd :=
      ((ha.add hi1).const_mul (μ / 2 * X2 ξ)).add ((hi2.add hi3).div_const (2 * μ))
    have hPB : ∀ η, ‖ξ‖ ^ 3 * a ξ * (a (ξ - η) * a η) ≤ Bd η := by
      intro η
      have hn : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by
        calc ‖ξ‖ = ‖(ξ - η) + η‖ := by rw [sub_add_cancel]
          _ ≤ ‖ξ - η‖ + ‖η‖ := norm_add_le _ _
      set X := ‖ξ‖ ^ 2 * a ξ
      set u := ‖ξ - η‖ * a (ξ - η)
      set w := ‖η‖ * a η
      have hX2e : X2 ξ = X ^ 2 := by simp only [hX2_def, X, ha_def]; ring
      have hgu : g (ξ - η) = u ^ 2 := by simp only [hg_def, u, ha_def]; ring
      have hgw : g η = w ^ 2 := by simp only [hg_def, w, ha_def]; ring
      have m1 := amgm X u hμ
      have m2 := amgm X w hμ
      have ha1 : 0 ≤ a ξ := norm_nonneg _
      have ha2 : 0 ≤ a (ξ - η) := norm_nonneg _
      have ha3 : 0 ≤ a η := norm_nonneg _
      calc ‖ξ‖ ^ 3 * a ξ * (a (ξ - η) * a η) = ‖ξ‖ * (X * (a (ξ - η) * a η)) := by
            simp only [X]; ring
        _ ≤ (‖ξ - η‖ + ‖η‖) * (X * (a (ξ - η) * a η)) := by gcongr
        _ = X * u * a η + X * w * a (ξ - η) := by simp only [u, w]; ring
        _ ≤ (μ * X ^ 2 + u ^ 2 / μ) / 2 * a η + (μ * X ^ 2 + w ^ 2 / μ) / 2 * a (ξ - η) := by
            gcongr
        _ = Bd η := by
            simp only [hBd_def, hX2e, hgu, hgw]
            field_simp
            ring
    have hint_le : ∫ η, ‖ξ‖ ^ 3 * a ξ * (a (ξ - η) * a η) ≤ ∫ η, Bd η :=
      integral_mono (hconv.const_mul _) hBdi hPB
    have hBdI : ∫ η, Bd η = μ * L1 f * X2 ξ + (A ξ + B ξ) / (2 * μ) := by
      have j1 : Integrable (fun η => μ / 2 * X2 ξ * (a η + a (ξ - η))) := (ha.add hi1).const_mul _
      have j2 : Integrable (fun η => (g (ξ - η) * a η + a (ξ - η) * g η) / (2 * μ)) :=
        (hi2.add hi3).div_const _
      have j3 : Integrable (fun η => a η + a (ξ - η)) := ha.add hi1
      have j4 : Integrable (fun η => g (ξ - η) * a η + a (ξ - η) * g η) := hi2.add hi3
      simp only [hBd_def]
      rw [integral_add j1 j2, integral_const_mul, integral_add ha hi1, integral_div,
        integral_add hi2 hi3]
      have e1 : ∫ η, a (ξ - η) = L1 f := integral_sub_left_eq_self a volume ξ
      have e2 : ∫ η, a η = L1 f := rfl
      rw [e1, e2]
      simp only [hA_def, hB_def]
      ring
    calc ‖ξ‖ ^ 2 * (‖f ξ‖ * ‖Bq f ξ‖) ≤ ‖ξ‖ ^ 2 * (a ξ * (2 * π * (‖ξ‖ * ∫ η, a (ξ - η) * a η))) := by
          gcongr
      _ = 2 * π * ∫ η, ‖ξ‖ ^ 3 * a ξ * (a (ξ - η) * a η) := by
          rw [integral_const_mul]
          ring
      _ ≤ 2 * π * ∫ η, Bd η := by gcongr
      _ = R ξ := by rw [hBdI]
  calc ∫ ξ, ‖ξ‖ ^ 2 * (‖f ξ‖ * ‖Bq f ξ‖) ≤ ∫ ξ, R ξ :=
        integral_mono_of_nonneg (Eventually.of_forall fun ξ => by positivity) hR
          (Eventually.of_forall hpt)
    _ = 2 * π * (μ * L1 f * Q 2 f + (L1 f * Q 1 f + Q 1 f * L1 f) / (2 * μ)) := by
        have k1 : Integrable (fun ξ => μ * L1 f * X2 ξ) := hX2.const_mul _
        have k2 : Integrable (fun ξ => (A ξ + B ξ) / (2 * μ)) := (hAint.add hBint).div_const _
        simp only [hR_def]
        rw [integral_const_mul, integral_add k1 k2, integral_const_mul, integral_div,
          integral_add hAint hBint, hAI, hBI]
        rfl
    _ = 2 * π * (L1 f * (μ * Q 2 f + Q 1 f / μ)) := by
        field_simp
        ring

end ATK.NSEnergia

#print axioms ATK.NSEnergia.amgm
#print axioms ATK.NSEnergia.amgm_w
#print axioms ATK.NSEnergia.sq_le_of_forall
#print axioms ATK.NSEnergia.hasDerivWithinAt_integral_gen
#print axioms ATK.NSEnergia.Q
#print axioms ATK.NSEnergia.L1
#print axioms ATK.NSEnergia.Q_nonneg
#print axioms ATK.NSEnergia.L1_nonneg
#print axioms ATK.NSEnergia.bound_Q
#print axioms ATK.NSEnergia.integrable_Q
#print axioms ATK.NSEnergia.integrable_norm_of_cota
#print axioms ATK.NSEnergia.I₁
#print axioms ATK.NSEnergia.one_add_pow_four_le
#print axioms ATK.NSEnergia.integrable_w
#print axioms ATK.NSEnergia.integral_w_scale
#print axioms ATK.NSEnergia.integrable_w_scale
#print axioms ATK.NSEnergia.L1_sq_le
#print axioms ATK.NSEnergia.inner_leray_of_ip
#print axioms ATK.NSEnergia.inner_cj
#print axioms ATK.NSEnergia.ip_sub_eq
#print axioms ATK.NSEnergia.integral_inner_Bq
#print axioms ATK.NSEnergia.termo_enstrofia_le
