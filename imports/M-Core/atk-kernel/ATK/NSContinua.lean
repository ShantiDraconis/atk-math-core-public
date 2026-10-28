import ATK.NSEnergia

/-!
# ATK — Navier–Stokes, marco NS7b: desigualdade de energia e critério de continuação

Ponte B3, marco NS7 (segunda parte), no lado de Fourier. Para uma solução `v` (classe `SolF`):

* **`energia_decresce`**: `Q 0 (v(·,t)) ≤ Q 0 (v(·,0))` (desigualdade de energia, via o
  cancelamento `integral_inner_Bq`);
* **`enstrofia_deriv_le`**: `d/dt Q 1 ≤ −2c Q 2 + 4π L1 (μ Q 2 + Q 1 / μ)`;
* **`cota_continua`**: se a enstrofia `Q 1` fica `≤ E` em `[0, T]`, a cota de peso 4 em
  `t = T` é controlada por uma constante que só depende de `c`, do dado, de `E` e de `T̄ ≥ T`
  (Gronwall com peso exponencial na fórmula de Duhamel).

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta**; **CLOSED_MATH continua
false**.
-/

set_option autoImplicit false

open MeasureTheory Real Set Filter Topology
open ATK.LigacaoNS (E3)
open ATK.NSFourierBase ATK.NSPicard ATK.NSRegular ATK.NSEquacao ATK.NSEnergia

namespace ATK.NSEquacao

/-! ### Fatias -/

theorem SolF.cont_slice {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Continuous fun ξ => v (ξ, t) := h.reg0.1 t ht

theorem SolF.pesos {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) (m : ℕ) :
    ∃ C, ∀ t ∈ Icc 0 T, Cota m C (fun ξ => v (ξ, t)) := h.reg0.2 m

theorem SolF.pesos_slice {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∀ m, ∃ C, Cota m C (fun ξ => v (ξ, t)) := fun m => by
  obtain ⟨C, hC⟩ := h.pesos m
  exact ⟨C, hC t ht⟩

theorem SolF.contOn {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) (ξ : E3) :
    ContinuousOn (fun s => v (ξ, s)) (Icc 0 T) :=
  fun s hs => (h.deq ξ s hs).continuousWithinAt

end ATK.NSEquacao

namespace ATK.NSContinua

variable {c T : ℝ} {v : E3 × ℝ → C3}


/-! ### A classe `SolF` a partir de `Sol` -/

theorem solF_of_sol_gen {D : Dado} {T : ℝ} (hT : 0 < T) {v : E3 × ℝ → C3} (hv : Sol D T v)
    (hw : ∀ m, ∃ M, Cota m M D.v₀) (hd : ∀ p : E3 × ℝ, ip p.1 (v p) = 0)
    (hh : ∀ ξ t, v (-ξ, t) = cj (v (ξ, t))) : SolF D.c T v :=
  ⟨D.hc, hT, sol_suave hT.le hv hw, fun ξ _ ht => sol_hasDerivWithinAt hv ξ ht, hd, hh⟩

theorem Bil_eq_Bq (v : E3 × ℝ → C3) (ξ : E3) (t : ℝ) :
    Bil v v (ξ, t) = Bq (fun η => v (η, t)) ξ := rfl

theorem dv_apply (c : ℝ) (v : E3 × ℝ → C3) (ξ : E3) (t : ℝ) :
    dv c v (ξ, t) = phiC c ξ • v (ξ, t) + Bil v v (ξ, t) := rfl

theorem inner_dv (c : ℝ) (v : E3 × ℝ → C3) (ξ : E3) (t : ℝ) :
    inner ℝ (v (ξ, t)) (dv c v (ξ, t)) =
      -(c * ‖ξ‖ ^ 2) * ‖v (ξ, t)‖ ^ 2 + (inner ℂ (v (ξ, t)) (Bil v v (ξ, t))).re := by
  have e2 : inner ℝ (v (ξ, t)) (Bil v v (ξ, t)) = (inner ℂ (v (ξ, t)) (Bil v v (ξ, t))).re :=
    real_inner_eq_re_inner ℂ _ _
  rw [dv_apply, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, e2]
  rfl

/-! ### Derivada dos momentos -/

theorem hasDerivWithinAt_Q (h : SolF c T v) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => Q k (fun ξ => v (ξ, s)))
      (∫ ξ, ‖ξ‖ ^ (2 * k) * (2 * inner ℝ (v (ξ, t)) (dv c v (ξ, t)))) (Icc 0 T) t := by
  obtain ⟨Cv, hCv⟩ := h.pesos (2 * k + 4)
  obtain ⟨Cd, hCd⟩ := (Suave.reg0 (h.suave_dv 0)).2 0
  have hb := (integrable_inv_pow (le_refl 4)).const_mul (2 * Cv * Cd)
  show HasDerivWithinAt (fun s => ∫ ξ, ‖ξ‖ ^ (2 * k) * ‖v (ξ, s)‖ ^ 2) _ _ _
  refine hasDerivWithinAt_integral_gen (V := ℝ) (F := fun s ξ => ‖ξ‖ ^ (2 * k) * ‖v (ξ, s)‖ ^ 2)
    (F' := fun s ξ => ‖ξ‖ ^ (2 * k) * (2 * inner ℝ (v (ξ, s)) (dv c v (ξ, s))))
    (convex_Icc 0 T) ht (fun s hs => ?_) ?_ hb
    (fun ξ s hs => ?_) (fun ξ s hs => ?_)
  · exact ((continuous_norm.pow _).mul ((h.cont_slice hs).norm.pow 2)).aestronglyMeasurable
  · exact integrable_Q (m := 2 * k + 4) (by omega) (h.cont_slice ht) (hCv t ht)
  · exact ((h.deq ξ s hs).norm_sq).const_mul _
  · have hw : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
    have e1 := (hCv s hs).le_inv ξ
    have e2 := (hCd s hs).le ξ
    have hCv0 := (hCv s hs).nonneg
    have hi := abs_real_inner_le_norm (v (ξ, s)) (dv c v (ξ, s))
    rw [norm_mul, norm_mul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h3 : ‖ξ‖ ^ (2 * k) ≤ (1 + ‖ξ‖) ^ (2 * k) :=
      pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
    have h4 : (1 + ‖ξ‖) ^ (2 * k) * ((1 + ‖ξ‖) ^ (2 * k + 4))⁻¹ = ((1 + ‖ξ‖) ^ 4)⁻¹ := by
      rw [pow_add]
      field_simp
    calc ‖ξ‖ ^ (2 * k) * (2 * |inner ℝ (v (ξ, s)) (dv c v (ξ, s))|)
        ≤ (1 + ‖ξ‖) ^ (2 * k) * (2 * (‖v (ξ, s)‖ * ‖dv c v (ξ, s)‖)) := by gcongr
      _ ≤ (1 + ‖ξ‖) ^ (2 * k) * (2 * (Cv * ((1 + ‖ξ‖) ^ (2 * k + 4))⁻¹ * Cd)) := by gcongr
      _ = 2 * Cv * Cd * ((1 + ‖ξ‖) ^ (2 * k) * ((1 + ‖ξ‖) ^ (2 * k + 4))⁻¹) := by ring
      _ = 2 * Cv * Cd * ((1 + ‖ξ‖) ^ 4)⁻¹ := by rw [h4]

theorem integrable_inner_Bil (h : SolF c T v) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable fun ξ => ‖ξ‖ ^ (2 * k) * (inner ℂ (v (ξ, t)) (Bil v v (ξ, t))).re := by
  obtain ⟨Cv, hCv⟩ := h.pesos (2 * k + 4)
  obtain ⟨Cb, hCb⟩ := (Suave.reg0 (h.suave_Bil 0)).2 0
  have hc1 := h.cont_slice ht
  have hc2 : Continuous fun ξ => Bil v v (ξ, t) := (Suave.reg0 (h.suave_Bil 0)).1 t ht
  have hm : Continuous fun ξ => ‖ξ‖ ^ (2 * k) * (inner ℂ (v (ξ, t)) (Bil v v (ξ, t))).re :=
    (continuous_norm.pow _).mul (Complex.continuous_re.comp (hc1.inner hc2))
  refine ((integrable_inv_pow (le_refl 4)).const_mul (Cv * Cb)).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  have hw : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
  have e1 := (hCv t ht).le_inv ξ
  have e2 := (hCb t ht).le ξ
  have hCv0 := (hCv t ht).nonneg
  have hi : |(inner ℂ (v (ξ, t)) (Bil v v (ξ, t))).re| ≤ ‖v (ξ, t)‖ * ‖Bil v v (ξ, t)‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  rw [norm_mul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
  have h3 : ‖ξ‖ ^ (2 * k) ≤ (1 + ‖ξ‖) ^ (2 * k) :=
    pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
  have h4 : (1 + ‖ξ‖) ^ (2 * k) * ((1 + ‖ξ‖) ^ (2 * k + 4))⁻¹ = ((1 + ‖ξ‖) ^ 4)⁻¹ := by
    rw [pow_add]
    field_simp
  calc ‖ξ‖ ^ (2 * k) * |(inner ℂ (v (ξ, t)) (Bil v v (ξ, t))).re|
      ≤ (1 + ‖ξ‖) ^ (2 * k) * (‖v (ξ, t)‖ * ‖Bil v v (ξ, t)‖) := by gcongr
    _ ≤ (1 + ‖ξ‖) ^ (2 * k) * (Cv * ((1 + ‖ξ‖) ^ (2 * k + 4))⁻¹ * Cb) := by gcongr
    _ = Cv * Cb * ((1 + ‖ξ‖) ^ (2 * k) * ((1 + ‖ξ‖) ^ (2 * k + 4))⁻¹) := by ring
    _ = Cv * Cb * ((1 + ‖ξ‖) ^ 4)⁻¹ := by rw [h4]

theorem integrable_norm_Bil (h : SolF c T v) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable fun ξ => ‖ξ‖ ^ (2 * k) * (‖v (ξ, t)‖ * ‖Bil v v (ξ, t)‖) := by
  obtain ⟨Cv, hCv⟩ := h.pesos (2 * k + 4)
  obtain ⟨Cb, hCb⟩ := (Suave.reg0 (h.suave_Bil 0)).2 0
  have hc1 := h.cont_slice ht
  have hc2 : Continuous fun ξ => Bil v v (ξ, t) := (Suave.reg0 (h.suave_Bil 0)).1 t ht
  have hm : Continuous fun ξ => ‖ξ‖ ^ (2 * k) * (‖v (ξ, t)‖ * ‖Bil v v (ξ, t)‖) :=
    (continuous_norm.pow _).mul (hc1.norm.mul hc2.norm)
  refine ((integrable_inv_pow (le_refl 4)).const_mul (Cv * Cb)).mono' hm.aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  have hw : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
  have e1 := (hCv t ht).le_inv ξ
  have e2 := (hCb t ht).le ξ
  have hCv0 := (hCv t ht).nonneg
  rw [Real.norm_of_nonneg (by positivity)]
  have h3 : ‖ξ‖ ^ (2 * k) ≤ (1 + ‖ξ‖) ^ (2 * k) :=
    pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
  have h4 : (1 + ‖ξ‖) ^ (2 * k) * ((1 + ‖ξ‖) ^ (2 * k + 4))⁻¹ = ((1 + ‖ξ‖) ^ 4)⁻¹ := by
    rw [pow_add]
    field_simp
  calc ‖ξ‖ ^ (2 * k) * (‖v (ξ, t)‖ * ‖Bil v v (ξ, t)‖)
      ≤ (1 + ‖ξ‖) ^ (2 * k) * (Cv * ((1 + ‖ξ‖) ^ (2 * k + 4))⁻¹ * Cb) := by gcongr
    _ = Cv * Cb * ((1 + ‖ξ‖) ^ (2 * k) * ((1 + ‖ξ‖) ^ (2 * k + 4))⁻¹) := by ring
    _ = Cv * Cb * ((1 + ‖ξ‖) ^ 4)⁻¹ := by rw [h4]

/-- O valor da derivada: `−2c Q(k+1) + 2 ∫ |ξ|^{2k} Re⟨v, B(v)⟩`. -/
theorem deriv_Q_eq (h : SolF c T v) (k : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫ ξ, ‖ξ‖ ^ (2 * k) * (2 * inner ℝ (v (ξ, t)) (dv c v (ξ, t))) =
      -(2 * c) * Q (k + 1) (fun ξ => v (ξ, t)) +
        2 * ∫ ξ, ‖ξ‖ ^ (2 * k) * (inner ℂ (v (ξ, t)) (Bil v v (ξ, t))).re := by
  obtain ⟨Cv, hCv⟩ := h.pesos (k + 1 + 2)
  have hQ := integrable_Q (k := k + 1) le_rfl (h.cont_slice ht) (hCv t ht)
  have hB := integrable_inner_Bil h k ht
  have e : (fun ξ => ‖ξ‖ ^ (2 * k) * (2 * inner ℝ (v (ξ, t)) (dv c v (ξ, t)))) =
      fun ξ => -(2 * c) * (‖ξ‖ ^ (2 * (k + 1)) * ‖v (ξ, t)‖ ^ 2) +
        2 * (‖ξ‖ ^ (2 * k) * (inner ℂ (v (ξ, t)) (Bil v v (ξ, t))).re) := by
    funext ξ
    rw [inner_dv]
    ring
  rw [e, integral_add (hQ.const_mul _) (hB.const_mul _), integral_const_mul, integral_const_mul]
  rfl

/-! ### A desigualdade de energia -/

theorem antitoneOn_of_deriv {f f' : ℝ → ℝ} {T : ℝ}
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (f' t) (Icc 0 T) t) (hn : ∀ t ∈ Icc 0 T, f' t ≤ 0) :
    AntitoneOn f (Icc 0 T) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
    (fun t ht => (hd t ht).continuousWithinAt) (fun t ht => ?_) (fun t ht => hn t
      (interior_subset ht))
  exact (hd t (interior_subset ht)).mono interior_subset

theorem monotoneOn_of_deriv {f f' : ℝ → ℝ} {T : ℝ}
    (hd : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (f' t) (Icc 0 T) t) (hn : ∀ t ∈ Icc 0 T, 0 ≤ f' t) :
    MonotoneOn f (Icc 0 T) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
    (fun t ht => (hd t ht).continuousWithinAt) (fun t ht => ?_) (fun t ht => hn t
      (interior_subset ht))
  exact (hd t (interior_subset ht)).mono interior_subset

/-- **Desigualdade de energia**: `Q 0 (v(·, t)) ≤ Q 0 (v(·, 0))`. -/
theorem energia_decresce (h : SolF c T v) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Q 0 (fun ξ => v (ξ, t)) ≤ Q 0 (fun ξ => v (ξ, 0)) := by
  have hT : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, h.pos.le⟩
  refine antitoneOn_of_deriv (fun s hs => hasDerivWithinAt_Q h 0 hs) (fun s hs => ?_) hT ht ht.1
  rw [deriv_Q_eq h 0 hs]
  have hz : ∫ ξ, ‖ξ‖ ^ (2 * 0) * (inner ℂ (v (ξ, s)) (Bil v v (ξ, s))).re = 0 := by
    have e : (fun ξ => ‖ξ‖ ^ (2 * 0) * (inner ℂ (v (ξ, s)) (Bil v v (ξ, s))).re) =
        fun ξ => RCLike.re (inner ℂ (v (ξ, s)) (Bq (fun η => v (η, s)) ξ)) := by
      funext ξ
      simp [Bil_eq_Bq]
    have hint : Integrable fun ξ => inner ℂ (v (ξ, s)) (Bq (fun η => v (η, s)) ξ) := by
      obtain ⟨C0, hC0⟩ := h.pesos 0
      obtain ⟨Cb, hCb⟩ := (Suave.reg0 (h.suave_Bil 0)).2 4
      have hc1 := h.cont_slice hs
      have hc2 : Continuous fun ξ => Bil v v (ξ, s) := (Suave.reg0 (h.suave_Bil 0)).1 s hs
      refine ((integrable_inv_pow (le_refl 4)).const_mul (C0 * Cb)).mono'
        (hc1.inner hc2).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
      have e1 := (hC0 s hs).le ξ
      have e2 := (hCb s hs).le_inv ξ
      have hC00 := (hC0 s hs).nonneg
      calc ‖inner ℂ (v (ξ, s)) (Bq (fun η => v (η, s)) ξ)‖
          ≤ ‖v (ξ, s)‖ * ‖Bil v v (ξ, s)‖ := norm_inner_le_norm _ _
        _ ≤ C0 * (Cb * ((1 + ‖ξ‖) ^ 4)⁻¹) := by gcongr
        _ = C0 * Cb * ((1 + ‖ξ‖) ^ 4)⁻¹ := by ring
    rw [e, integral_re hint, integral_inner_Bq (h.cont_slice hs) (h.pesos_slice hs)
      (fun ξ => h.div (ξ, s)) (fun ξ => h.herm ξ s)]
    simp
  rw [hz]
  have := Q_nonneg (0 + 1) (fun ξ => v (ξ, s))
  have := h.hc
  nlinarith

/-! ### A desigualdade diferencial da enstrofia -/

theorem enstrofia_deriv_le (h : SolF c T v) {t : ℝ} (ht : t ∈ Icc 0 T) {μ : ℝ} (hμ : 0 < μ) :
    ∫ ξ, ‖ξ‖ ^ (2 * 1) * (2 * inner ℝ (v (ξ, t)) (dv c v (ξ, t))) ≤
      -(2 * c) * Q 2 (fun ξ => v (ξ, t)) +
        4 * π * (L1 (fun ξ => v (ξ, t)) *
          (μ * Q 2 (fun ξ => v (ξ, t)) + Q 1 (fun ξ => v (ξ, t)) / μ)) := by
  rw [deriv_Q_eq h 1 ht]
  have hB := integrable_inner_Bil h 1 ht
  have hR := integrable_norm_Bil h 1 ht
  have hle : ∫ ξ, ‖ξ‖ ^ (2 * 1) * (inner ℂ (v (ξ, t)) (Bil v v (ξ, t))).re ≤
      ∫ ξ, ‖ξ‖ ^ 2 * (‖v (ξ, t)‖ * ‖Bq (fun η => v (η, t)) ξ‖) := by
    refine integral_mono hB hR fun ξ => ?_
    have hi : (inner ℂ (v (ξ, t)) (Bil v v (ξ, t))).re ≤ ‖v (ξ, t)‖ * ‖Bil v v (ξ, t)‖ :=
      (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
    show ‖ξ‖ ^ (2 * 1) * _ ≤ ‖ξ‖ ^ 2 * (‖v (ξ, t)‖ * ‖Bil v v (ξ, t)‖)
    have : ‖ξ‖ ^ (2 * 1) = ‖ξ‖ ^ 2 := rfl
    rw [this]
    exact mul_le_mul_of_nonneg_left hi (by positivity)
  have hT := termo_enstrofia_le (h.cont_slice ht) (h.pesos_slice ht) hμ
  show -(2 * c) * Q 2 (fun ξ => v (ξ, t)) + _ ≤ _
  linarith


/-! ### Continuidade em `t` -/

theorem continuousOn_L1 (h : SolF c T v) :
    ContinuousOn (fun s => L1 (fun ξ => v (ξ, s))) (Icc 0 T) := by
  obtain ⟨C, hC⟩ := h.pesos 4
  refine continuousOn_of_dominated (bound := fun ξ => C * ((1 + ‖ξ‖) ^ 4)⁻¹)
    (fun s hs => (h.cont_slice hs).norm.aestronglyMeasurable)
    (fun s hs => Eventually.of_forall fun ξ => ?_)
    ((integrable_inv_pow (le_refl 4)).const_mul C)
    (Eventually.of_forall fun ξ => (h.contOn ξ).norm)
  rw [norm_norm]
  exact (hC s hs).le_inv ξ

theorem continuousOn_Q (h : SolF c T v) (k : ℕ) :
    ContinuousOn (fun s => Q k (fun ξ => v (ξ, s))) (Icc 0 T) :=
  fun _ hs => (hasDerivWithinAt_Q h k hs).continuousWithinAt

/-! ### A desigualdade diferencial absorvida -/

/-- O parâmetro de escala da interpolação. -/
noncomputable def rr (c E : ℝ) : ℝ := c ^ 2 / (64 * π ^ 2 * (E + 1) * (I₁ + 1))

/-- A constante da desigualdade da enstrofia. -/
noncomputable def K₁ (c A E : ℝ) : ℝ := 32 * π ^ 2 * E * ((rr c E ^ 3)⁻¹ * (I₁ + 1) * A + 1) / c

theorem I₁_nonneg : 0 ≤ I₁ := integral_nonneg fun ξ => by positivity

theorem rr_pos {c E : ℝ} (hc : 0 < c) (hE : 0 ≤ E) : 0 < rr c E := by
  have := I₁_nonneg
  unfold rr
  positivity

theorem K₁_nonneg {c A E : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hE : 0 ≤ E) : 0 ≤ K₁ c A E := by
  have := I₁_nonneg
  have := rr_pos hc hE
  unfold K₁
  positivity

/-- `D₁(t) ≤ −(c/2) Q 2 + K₁` sob `Q 1 ≤ E` e `Q 0 ≤ A`. -/
theorem enstrofia_deriv_abs (h : SolF c T v) {E A : ℝ} (hE0 : 0 ≤ E)
    {t : ℝ} (ht : t ∈ Icc 0 T) (hE : Q 1 (fun ξ => v (ξ, t)) ≤ E)
    (hA : Q 0 (fun ξ => v (ξ, t)) ≤ A) :
    ∫ ξ, ‖ξ‖ ^ (2 * 1) * (2 * inner ℝ (v (ξ, t)) (dv c v (ξ, t))) ≤
      -(c / 2) * Q 2 (fun ξ => v (ξ, t)) + K₁ c A E := by
  have hc := h.hc
  set L := L1 (fun ξ => v (ξ, t))
  set q0 := Q 0 (fun ξ => v (ξ, t))
  set q1 := Q 1 (fun ξ => v (ξ, t))
  set q2 := Q 2 (fun ξ => v (ξ, t))
  have hL : 0 ≤ L := L1_nonneg _
  have hq1 : 0 ≤ q1 := Q_nonneg _ _
  have hq2 : 0 ≤ q2 := Q_nonneg _ _
  have hI := I₁_nonneg
  set r := rr c E
  have hr : 0 < r := rr_pos hc hE0
  set μ := c / (4 * π * (L + 1))
  have hμ : 0 < μ := by positivity
  have hd := enstrofia_deriv_le h ht hμ
  obtain ⟨C4, hC4⟩ := h.pesos 4
  have hL2 : L ^ 2 ≤ (r ^ 3)⁻¹ * (I₁ + 1) * (q0 + r ^ 4 * q2) :=
    L1_sq_le (h.cont_slice ht) (hC4 t ht) hr
  -- (a) o termo em `μ`
  have f1 : 4 * π * (L * (μ * q2)) ≤ c * q2 := by
    have e : 4 * π * (L * μ) = c * (L / (L + 1)) := by
      simp only [μ]
      field_simp
    have hle : L / (L + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    calc 4 * π * (L * (μ * q2)) = 4 * π * (L * μ) * q2 := by ring
      _ = c * (L / (L + 1)) * q2 := by rw [e]
      _ ≤ c * 1 * q2 := by gcongr
      _ = c * q2 := by ring
  -- (b) o termo em `1/μ`
  have f2 : 4 * π * (L * (q1 / μ)) = 16 * π ^ 2 * (L * (L + 1)) * q1 / c := by
    simp only [μ]
    field_simp
    ring
  have f3 : 16 * π ^ 2 * (L * (L + 1)) * q1 / c ≤ 32 * π ^ 2 * (L ^ 2 + 1) * E / c := by
    have h1 : L * (L + 1) ≤ 2 * (L ^ 2 + 1) := by nlinarith [sq_nonneg (L - 1)]
    have h2 : L * (L + 1) * q1 ≤ 2 * (L ^ 2 + 1) * E := by
      calc L * (L + 1) * q1 ≤ 2 * (L ^ 2 + 1) * q1 := by gcongr
        _ ≤ 2 * (L ^ 2 + 1) * E := by gcongr
    rw [div_le_div_iff_of_pos_right hc]
    nlinarith [pi_pos]
  have f4 : 32 * π ^ 2 * (L ^ 2 + 1) * E / c ≤ c / 2 * q2 + K₁ c A E := by
    have hrc : 32 * π ^ 2 * E * (r * (I₁ + 1)) / c ≤ c / 2 := by
      have e : 32 * π ^ 2 * E * (r * (I₁ + 1)) / c = c * E / (2 * (E + 1)) := by
        simp only [r, rr]
        field_simp
        ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hq0 : q0 ≤ A := hA
    have hL2' : L ^ 2 ≤ (r ^ 3)⁻¹ * (I₁ + 1) * A + r * (I₁ + 1) * q2 := by
      have e : (r ^ 3)⁻¹ * (I₁ + 1) * (q0 + r ^ 4 * q2) =
          (r ^ 3)⁻¹ * (I₁ + 1) * q0 + r * (I₁ + 1) * q2 := by
        field_simp
      have : (r ^ 3)⁻¹ * (I₁ + 1) * q0 ≤ (r ^ 3)⁻¹ * (I₁ + 1) * A := by gcongr
      linarith
    have hk : 32 * π ^ 2 * (L ^ 2 + 1) * E / c ≤
        32 * π ^ 2 * E * (r * (I₁ + 1)) / c * q2 + K₁ c A E := by
      have e : K₁ c A E = 32 * π ^ 2 * E * ((r ^ 3)⁻¹ * (I₁ + 1) * A + 1) / c := rfl
      rw [e, div_mul_eq_mul_div, ← add_div, div_le_div_iff_of_pos_right hc]
      have : 0 ≤ 32 * π ^ 2 * E := by positivity
      nlinarith
    calc 32 * π ^ 2 * (L ^ 2 + 1) * E / c
        ≤ 32 * π ^ 2 * E * (r * (I₁ + 1)) / c * q2 + K₁ c A E := hk
      _ ≤ c / 2 * q2 + K₁ c A E := by gcongr
  have hsplit : 4 * π * (L * (μ * q2 + q1 / μ)) =
      4 * π * (L * (μ * q2)) + 4 * π * (L * (q1 / μ)) := by ring
  rw [hsplit, f2] at hd
  linarith


/-! ### A função de Gronwall `Ψ` -/

/-- A derivada da enstrofia. -/
noncomputable def D1 (c : ℝ) (v : E3 × ℝ → C3) (t : ℝ) : ℝ :=
  ∫ ξ, ‖ξ‖ ^ (2 * 1) * (2 * inner ℝ (v (ξ, t)) (dv c v (ξ, t)))

/-- `Ψ(t) = (2(I₁+1)/c)(K₁ t + Q₁(0) − Q₁(t)) + (I₁+1) A t`. -/
noncomputable def Psi (c A E : ℝ) (v : E3 × ℝ → C3) (t : ℝ) : ℝ :=
  2 * (I₁ + 1) / c * (K₁ c A E * t + Q 1 (fun ξ => v (ξ, 0)) - Q 1 (fun ξ => v (ξ, t))) +
    (I₁ + 1) * A * t

/-- O majorante de `Ψ` em `[0, T̄]`. -/
noncomputable def Psimax (c A E T : ℝ) : ℝ :=
  2 * (I₁ + 1) / c * (K₁ c A E * T + E) + (I₁ + 1) * A * T

theorem hasDerivWithinAt_Psi (h : SolF c T v) (A E : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (Psi c A E v)
      (2 * (I₁ + 1) / c * (K₁ c A E - D1 c v t) + (I₁ + 1) * A) (Icc 0 T) t := by
  have h1 := ((((hasDerivWithinAt_id t (Icc 0 T)).const_mul (K₁ c A E)).add_const
    (Q 1 (fun ξ => v (ξ, 0)))).sub (hasDerivWithinAt_Q h 1 ht)).const_mul (2 * (I₁ + 1) / c)
  have h2 := h1.add ((hasDerivWithinAt_id t (Icc 0 T)).const_mul ((I₁ + 1) * A))
  refine h2.congr_deriv ?_
  simp only [D1, mul_one]

theorem Psi_zero (c A E : ℝ) (v : E3 × ℝ → C3) : Psi c A E v 0 = 0 := by
  simp [Psi]

theorem continuousOn_Psi (h : SolF c T v) (A E : ℝ) : ContinuousOn (Psi c A E v) (Icc 0 T) :=
  fun _ ht => (hasDerivWithinAt_Psi h A E ht).continuousWithinAt

section Gronwall

variable (h : SolF c T v) {E A : ℝ} (hE0 : 0 ≤ E) (hE : ∀ t ∈ Icc 0 T, Q 1 (fun ξ => v (ξ, t)) ≤ E)
  (hA : ∀ t ∈ Icc 0 T, Q 0 (fun ξ => v (ξ, t)) ≤ A)
include h hE0 hE hA

/-- `L1² ≤ Ψ'`. -/
theorem L1_sq_le_dPsi {t : ℝ} (ht : t ∈ Icc 0 T) :
    L1 (fun ξ => v (ξ, t)) ^ 2 ≤ 2 * (I₁ + 1) / c * (K₁ c A E - D1 c v t) + (I₁ + 1) * A := by
  have hc := h.hc
  have hI := I₁_nonneg
  have hd := enstrofia_deriv_abs h hE0 ht (hE t ht) (hA t ht)
  obtain ⟨C4, hC4⟩ := h.pesos 4
  have hL2 := L1_sq_le (h.cont_slice ht) (hC4 t ht) one_pos
  simp only [one_pow, inv_one, one_mul] at hL2
  have hq0 := hA t ht
  have hq2 := Q_nonneg 2 (fun ξ => v (ξ, t))
  have h1 : (I₁ + 1) * Q 2 (fun ξ => v (ξ, t)) ≤ 2 * (I₁ + 1) / c * (K₁ c A E - D1 c v t) := by
    have : c / 2 * Q 2 (fun ξ => v (ξ, t)) ≤ K₁ c A E - D1 c v t := by
      simp only [D1]
      linarith
    calc (I₁ + 1) * Q 2 (fun ξ => v (ξ, t))
        = 2 * (I₁ + 1) / c * (c / 2 * Q 2 (fun ξ => v (ξ, t))) := by field_simp
      _ ≤ 2 * (I₁ + 1) / c * (K₁ c A E - D1 c v t) := by gcongr
  have h2 : (I₁ + 1) * Q 0 (fun ξ => v (ξ, t)) ≤ (I₁ + 1) * A := by gcongr
  nlinarith

theorem Psi_nonneg {t : ℝ} (ht : t ∈ Icc 0 T) : 0 ≤ Psi c A E v t := by
  have hmono := monotoneOn_of_deriv (fun s hs => hasDerivWithinAt_Psi h A E hs)
    (fun s hs => (sq_nonneg _).trans (L1_sq_le_dPsi h hE0 hE hA hs))
  have := hmono ⟨le_rfl, h.pos.le⟩ ht ht.1
  rwa [Psi_zero] at this

theorem Psi_le {t : ℝ} (ht : t ∈ Icc 0 T) {T' : ℝ} (hT' : T ≤ T') :
    Psi c A E v t ≤ Psimax c A E T' := by
  have hc := h.hc
  have hI := I₁_nonneg
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, h.pos.le⟩
  have hA0 : 0 ≤ A := (Q_nonneg 0 _).trans (hA 0 h0)
  have hK := K₁_nonneg hc hA0 hE0
  have hq0 := hE 0 h0
  have hqt := Q_nonneg 1 (fun ξ => v (ξ, t))
  have htT : t ≤ T' := ht.2.trans hT'
  unfold Psi Psimax
  have e1 : K₁ c A E * t + Q 1 (fun ξ => v (ξ, 0)) - Q 1 (fun ξ => v (ξ, t)) ≤
      K₁ c A E * T' + E := by nlinarith
  have e2 : (I₁ + 1) * A * t ≤ (I₁ + 1) * A * T' := by gcongr
  have e3 : 2 * (I₁ + 1) / c * (K₁ c A E * t + Q 1 (fun ξ => v (ξ, 0)) - Q 1 (fun ξ => v (ξ, t)))
      ≤ 2 * (I₁ + 1) / c * (K₁ c A E * T' + E) := by gcongr
  linarith

/-- **Gronwall integral**: `∫₀ᵗ L1² e^{λΨ} ≤ (e^{λΨ(t)} − 1)/λ`. -/
theorem integral_L1_exp_le {lam : ℝ} (hl : 0 < lam) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫ s in (0 : ℝ)..t, L1 (fun ξ => v (ξ, s)) ^ 2 * exp (lam * Psi c A E v s) ≤
      (exp (lam * Psi c A E v t) - 1) / lam := by
  have hT0 : 0 ≤ T := h.pos.le
  set g : ℝ → ℝ := fun s => L1 (fun ξ => v (ξ, s)) ^ 2 * exp (lam * Psi c A E v s) with hg_def
  have hgc : ContinuousOn g (Icc 0 T) :=
    ((continuousOn_L1 h).pow 2).mul ((continuousOn_Psi h A E).const_smul lam |>.rexp)
  set H : ℝ → ℝ := fun u => (∫ s in (0 : ℝ)..u, g s) - (exp (lam * Psi c A E v u) - 1) / lam
  have hHc : ContinuousOn H (Icc 0 T) := by
    have h1 : ContinuousOn (fun u => ∫ s in (0 : ℝ)..u, g s) (Icc 0 T) := by
      have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := T)
        (f := g) (by rw [uIcc_of_le hT0]; exact hgc.integrableOn_Icc)
      rwa [uIcc_of_le hT0] at this
    have h2 : ContinuousOn (fun u => (exp (lam * Psi c A E v u) - 1) / lam) (Icc 0 T) :=
      (((continuousOn_Psi h A E).const_smul lam).rexp.sub continuousOn_const).div_const _
    exact h1.sub h2
  have hHd : ∀ u ∈ interior (Icc 0 T), HasDerivWithinAt H
      (g u - exp (lam * Psi c A E v u) * (lam * (2 * (I₁ + 1) / c * (K₁ c A E - D1 c v u) +
        (I₁ + 1) * A)) / lam) (interior (Icc 0 T)) u := by
    intro u hu
    rw [interior_Icc] at hu
    have hnhds : Icc 0 T ∈ 𝓝 u := Icc_mem_nhds hu.1 hu.2
    have hi : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, g s) (g u) u := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ (hgc.continuousAt hnhds)
      · refine (hgc.mono ?_).intervalIntegrable
        rw [uIcc_of_le hu.1.le]
        exact Icc_subset_Icc le_rfl hu.2.le
      · exact (hgc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo u hu
    have hP := (hasDerivWithinAt_Psi h A E (Ioo_subset_Icc_self hu)).hasDerivAt hnhds
    have he := ((hP.const_mul lam).exp.sub_const 1).div_const lam
    exact (hi.sub he).hasDerivWithinAt
  have hHn : ∀ u ∈ interior (Icc 0 T),
      g u - exp (lam * Psi c A E v u) * (lam * (2 * (I₁ + 1) / c * (K₁ c A E - D1 c v u) +
        (I₁ + 1) * A)) / lam ≤ 0 := by
    intro u hu
    rw [interior_Icc] at hu
    have hL := L1_sq_le_dPsi h hE0 hE hA (Ioo_subset_Icc_self hu)
    have hex := exp_pos (lam * Psi c A E v u)
    have e : exp (lam * Psi c A E v u) * (lam * (2 * (I₁ + 1) / c * (K₁ c A E - D1 c v u) +
        (I₁ + 1) * A)) / lam = exp (lam * Psi c A E v u) * (2 * (I₁ + 1) / c *
          (K₁ c A E - D1 c v u) + (I₁ + 1) * A) := by
      field_simp
    rw [e]
    simp only [hg_def]
    nlinarith
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hHc hHd hHn
  have := hanti ⟨le_rfl, hT0⟩ ht ht.1
  simp only [H, intervalIntegral.integral_same, Psi_zero, mul_zero, exp_zero, sub_self,
    zero_div] at this
  linarith

end Gronwall


/-! ### Ferramentas para a fórmula de Duhamel -/

/-- `|B(f)(ξ)| (1+|ξ|)⁴ ≤ 64π |ξ| Y L1(f)` quando `Cota 4 Y f`. -/
theorem norm_Bq_peso {f : E3 → C3} (hf : Continuous f) {Y : ℝ} (hY : Cota 4 Y f) (ξ : E3) :
    ‖Bq f ξ‖ * (1 + ‖ξ‖) ^ 4 ≤ ‖ξ‖ * (64 * π * Y * L1 f) := by
  have hY0 : 0 ≤ Y := hY.nonneg
  have ha := integrable_norm_of_cota hf hY
  have hconv : Integrable fun η => ‖f (ξ - η)‖ * ‖f η‖ :=
    integrable_conv hf.norm.aestronglyMeasurable hf.norm.aestronglyMeasurable
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hY hY ξ
  have hi1 : Integrable fun η => ‖f (ξ - η)‖ := ha.comp_sub_left ξ
  have hpt : ∀ η, ‖f (ξ - η)‖ * ‖f η‖ * (1 + ‖ξ‖) ^ 4 ≤ 16 * Y * (‖f η‖ + ‖f (ξ - η)‖) := by
    intro η
    have hp := one_add_norm_pow_le ξ η 4
    have e1 := hY (ξ - η)
    have e2 := hY η
    have hn1 := norm_nonneg (f (ξ - η))
    have hn2 := norm_nonneg (f η)
    calc ‖f (ξ - η)‖ * ‖f η‖ * (1 + ‖ξ‖) ^ 4
        ≤ ‖f (ξ - η)‖ * ‖f η‖ * (2 ^ 4 * ((1 + ‖ξ - η‖) ^ 4 + (1 + ‖η‖) ^ 4)) := by gcongr
      _ = 16 * ((‖f (ξ - η)‖ * (1 + ‖ξ - η‖) ^ 4) * ‖f η‖ +
            ‖f (ξ - η)‖ * (‖f η‖ * (1 + ‖η‖) ^ 4)) := by ring
      _ ≤ 16 * (Y * ‖f η‖ + ‖f (ξ - η)‖ * Y) := by gcongr
      _ = 16 * Y * (‖f η‖ + ‖f (ξ - η)‖) := by ring
  have hint : (∫ η, ‖f (ξ - η)‖ * ‖f η‖) * (1 + ‖ξ‖) ^ 4 ≤ 32 * Y * L1 f := by
    rw [← integral_mul_const]
    have : ∫ η, ‖f (ξ - η)‖ * ‖f η‖ * (1 + ‖ξ‖) ^ 4 ≤ ∫ η, 16 * Y * (‖f η‖ + ‖f (ξ - η)‖) :=
      integral_mono (hconv.mul_const _) ((ha.add hi1).const_mul (16 * Y)) hpt
    have e : ∫ η, 16 * Y * (‖f η‖ + ‖f (ξ - η)‖) = 32 * Y * L1 f := by
      rw [integral_const_mul, integral_add ha hi1, integral_sub_left_eq_self
        (fun ζ => ‖f ζ‖) volume ξ]
      unfold L1
      ring
    linarith
  have hB := norm_Bq_le_nl f ξ
  have hN := norm_nl_le_conv hf hf hY hY ξ
  calc ‖Bq f ξ‖ * (1 + ‖ξ‖) ^ 4 ≤ 2 * π * (‖ξ‖ * ∫ η, ‖f (ξ - η)‖ * ‖f η‖) * (1 + ‖ξ‖) ^ 4 := by
        gcongr
        exact hB.trans (by gcongr)
    _ = 2 * π * ‖ξ‖ * ((∫ η, ‖f (ξ - η)‖ * ‖f η‖) * (1 + ‖ξ‖) ^ 4) := by ring
    _ ≤ 2 * π * ‖ξ‖ * (32 * Y * L1 f) := by gcongr
    _ = ‖ξ‖ * (64 * π * Y * L1 f) := by ring

theorem norm_Iduh_le_int (c : ℝ) {G : E3 × ℝ → C3} (ξ : E3) {t : ℝ} (ht : 0 ≤ t) :
    ‖Iduh c G ξ t‖ ≤ ∫ s in (0 : ℝ)..t, hk c ξ (t - s) * ‖G (ξ, s)‖ := by
  unfold Iduh
  refine (intervalIntegral.norm_integral_le_integral_norm ht).trans_eq ?_
  congr 1
  funext s
  rw [norm_smul, Real.norm_of_nonneg (hk_pos c ξ _).le]

theorem kernel_sq_le {c : ℝ} (hc : 0 < c) (ξ : E3) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, (hk c ξ (t - s) * ‖ξ‖) ^ 2 ≤ 1 / (2 * c) := by
  rcases eq_or_ne ξ 0 with hξ | hξ
  · subst hξ
    simp
    positivity
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  set A := 2 * c * ‖ξ‖ ^ 2
  have hA : 0 < A := by positivity
  have e : (fun s => (hk c ξ (t - s) * ‖ξ‖) ^ 2) = fun s => ‖ξ‖ ^ 2 * exp (-(A * (t - s))) := by
    funext s
    unfold hk
    rw [mul_pow, ← exp_nat_mul]
    simp only [A]
    push_cast
    ring_nf
  rw [e, intervalIntegral.integral_const_mul, integral_heat hA]
  have h1 : 1 - exp (-(A * t)) ≤ 1 := by linarith [exp_pos (-(A * t))]
  have h0 : 0 ≤ 1 - exp (-(A * t)) := by
    rw [sub_nonneg, exp_le_one_iff]
    have := mul_nonneg hA.le ht
    linarith
  calc ‖ξ‖ ^ 2 * ((1 - exp (-(A * t))) / A) ≤ ‖ξ‖ ^ 2 * (1 / A) := by gcongr
    _ = 1 / (2 * c) := by simp only [A]; field_simp

theorem amgm_integral {a b : ℝ → ℝ} {t μ : ℝ} (ht : 0 ≤ t) (hμ : 0 < μ)
    (ha : ContinuousOn a (Icc 0 t)) (hb : ContinuousOn b (Icc 0 t)) :
    ∫ s in (0 : ℝ)..t, a s * b s ≤
      (μ * (∫ s in (0 : ℝ)..t, a s ^ 2) + (∫ s in (0 : ℝ)..t, b s ^ 2) / μ) / 2 := by
  have hi : ∀ {g : ℝ → ℝ}, ContinuousOn g (Icc 0 t) → IntervalIntegrable g volume 0 t :=
    fun hg => (hg.mono (by rw [uIcc_of_le ht])).intervalIntegrable
  have h1 := hi (ha.mul hb)
  have h2 := hi (ha.pow 2)
  have h3 := hi (hb.pow 2)
  have hle := intervalIntegral.integral_mono_on ht h1
    ((((h2.const_mul μ).add (h3.div_const μ))).div_const 2) (fun s _ => amgm (a s) (b s) hμ)
  refine hle.trans_eq ?_
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (h2.const_mul μ)
    (h3.div_const μ), intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
  rfl


/-! ### O critério de continuação -/

/-- `λ = (128π)²/(2c)`. -/
noncomputable def lamG (c : ℝ) : ℝ := (128 * π) ^ 2 / (2 * c)

/-- A cota de peso 4 que só depende de `c`, `M₀`, `A`, `E` e `T̄`. -/
noncomputable def Bnd (c M A E T : ℝ) : ℝ := 2 * M * exp (lamG c * Psimax c A E T / 2)

/-- **Critério de continuação (forma quantitativa)**: se a enstrofia de Fourier `Q 1` fica `≤ E`
em `[0, T]`, então a cota de peso 4 em `[0, T]` é `Bnd c M₀ A E T̄` (`A` = energia do dado,
`T̄ ≥ T`), independente de `T`. -/
theorem cota_continua {D : Dado} {T : ℝ} (hT : 0 < T) {v : E3 × ℝ → C3} (hv : Sol D T v)
    (hw : ∀ m, ∃ M, Cota m M D.v₀) (hd : ∀ p : E3 × ℝ, ip p.1 (v p) = 0)
    (hh : ∀ ξ t, v (-ξ, t) = cj (v (ξ, t))) {E : ℝ}
    (hE : ∀ t ∈ Icc 0 T, Q 1 (fun ξ => v (ξ, t)) ≤ E) {T' : ℝ} (hT' : T ≤ T') :
    ∀ t ∈ Icc 0 T, Cota 4 (Bnd D.c D.M₀ (Q 0 D.v₀) E T') (fun ξ => v (ξ, t)) := by
  have h := solF_of_sol_gen hT hv hw hd hh
  have hc := D.hc
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hE0 : 0 ≤ E := (Q_nonneg 1 _).trans (hE 0 h0)
  set A := Q 0 D.v₀ with hA_def
  have hsl0 : (fun ξ => v (ξ, 0)) = D.v₀ := funext fun ξ => sol_zero hT.le hv ξ
  have hA : ∀ t ∈ Icc 0 T, Q 0 (fun ξ => v (ξ, t)) ≤ A := by
    intro t ht
    have := energia_decresce h ht
    rwa [hsl0] at this
  set lam := lamG D.c with hlam_def
  have hl : 0 < lam := by
    rw [hlam_def]
    unfold lamG
    positivity
  set Ψ := Psi D.c A E v with hΨ_def
  have hΨ0 : ∀ t ∈ Icc 0 T, 0 ≤ Ψ t := fun t ht => Psi_nonneg h hE0 hE hA ht
  obtain ⟨R, hR⟩ := hv.cota
  have hM₀ : 0 ≤ D.M₀ := D.cota.nonneg
  set S : Set ℝ :=
    {z | ∃ ξ, ∃ t ∈ Icc 0 T, z = exp (-(lam * Ψ t / 2)) * (‖v (ξ, t)‖ * (1 + ‖ξ‖) ^ 4)}
  have hexle : ∀ t ∈ Icc 0 T, exp (-(lam * Ψ t / 2)) ≤ 1 := by
    intro t ht
    rw [exp_le_one_iff]
    have := mul_nonneg hl.le (hΨ0 t ht)
    linarith
  have hbdd : BddAbove S := by
    refine ⟨R, ?_⟩
    rintro z ⟨ξ, t, ht, rfl⟩
    have e2 := hR t ξ
    calc exp (-(lam * Ψ t / 2)) * (‖v (ξ, t)‖ * (1 + ‖ξ‖) ^ 4) ≤ 1 * R := by
          gcongr
          exact hexle t ht
      _ = R := one_mul R
  have hne : S.Nonempty := ⟨_, 0, 0, h0, rfl⟩
  set Z := sSup S
  have hZ : ∀ ξ, ∀ t ∈ Icc 0 T, exp (-(lam * Ψ t / 2)) * (‖v (ξ, t)‖ * (1 + ‖ξ‖) ^ 4) ≤ Z :=
    fun ξ t ht => le_csSup hbdd ⟨ξ, t, ht, rfl⟩
  have hZ0 : 0 ≤ Z := le_trans (by positivity) (hZ 0 0 h0)
  have hslice : ∀ s ∈ Icc 0 T, Cota 4 (Z * exp (lam * Ψ s / 2)) (fun η => v (η, s)) := by
    intro s hs ζ
    have := hZ ζ s hs
    rw [exp_neg, inv_mul_le_iff₀ (exp_pos _)] at this
    linarith
  -- a estimativa central
  have hkey : ∀ ξ, ∀ t ∈ Icc 0 T,
      ‖v (ξ, t)‖ * (1 + ‖ξ‖) ^ 4 ≤ D.M₀ + Z * exp (lam * Ψ t / 2) / 2 := by
    intro ξ t ht
    have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    have hG : Continuous (Gv v) := continuous_Bq_param hv.cont hR
    set L : ℝ → ℝ := fun s => L1 (fun η => v (η, s)) with hL_def
    have hLc : ContinuousOn L (Icc 0 t) := (continuousOn_L1 h).mono hsub
    have hΨc : ContinuousOn Ψ (Icc 0 t) := (continuousOn_Psi h A E).mono hsub
    have hv1 : ‖v (ξ, t)‖ * (1 + ‖ξ‖) ^ 4 ≤ D.M₀ + ‖Iduh D.c (Gv v) ξ t‖ * (1 + ‖ξ‖) ^ 4 := by
      rw [hv.eq_of_mem ht]
      have e1 : ‖hk D.c ξ t • D.v₀ ξ‖ * (1 + ‖ξ‖) ^ 4 ≤ D.M₀ := by
        rw [norm_smul, Real.norm_of_nonneg (hk_pos _ _ _).le]
        have hk1 := hk_le_one hc.le ht.1 ξ
        calc hk D.c ξ t * ‖D.v₀ ξ‖ * (1 + ‖ξ‖) ^ 4 ≤ 1 * ‖D.v₀ ξ‖ * (1 + ‖ξ‖) ^ 4 := by gcongr
          _ = ‖D.v₀ ξ‖ * (1 + ‖ξ‖) ^ 4 := by ring
          _ ≤ D.M₀ := D.cota ξ
      calc ‖hk D.c ξ t • D.v₀ ξ + Iduh D.c (Gv v) ξ t‖ * (1 + ‖ξ‖) ^ 4
          ≤ (‖hk D.c ξ t • D.v₀ ξ‖ + ‖Iduh D.c (Gv v) ξ t‖) * (1 + ‖ξ‖) ^ 4 := by
            gcongr
            exact norm_add_le _ _
        _ = ‖hk D.c ξ t • D.v₀ ξ‖ * (1 + ‖ξ‖) ^ 4 + ‖Iduh D.c (Gv v) ξ t‖ * (1 + ‖ξ‖) ^ 4 := by
            ring
        _ ≤ D.M₀ + ‖Iduh D.c (Gv v) ξ t‖ * (1 + ‖ξ‖) ^ 4 := by gcongr
    set a : ℝ → ℝ := fun s => hk D.c ξ (t - s) * ‖ξ‖ with ha_def
    set b : ℝ → ℝ := fun s => exp (lam * Ψ s / 2) * L s with hb_def
    have hac : ContinuousOn a (Icc 0 t) := by
      refine Continuous.continuousOn ?_
      simp only [ha_def]
      unfold hk
      fun_prop
    have hbc : ContinuousOn b (Icc 0 t) := by
      have : ContinuousOn (fun s => lam * Ψ s / 2) (Icc 0 t) :=
        (continuousOn_const.mul hΨc).div_const 2
      exact this.rexp.mul hLc
    have hI1 : ‖Iduh D.c (Gv v) ξ t‖ * (1 + ‖ξ‖) ^ 4 ≤
        64 * π * Z * ∫ s in (0 : ℝ)..t, a s * b s := by
      have h1 := norm_Iduh_le_int D.c (G := Gv v) ξ ht.1
      have hk1 : Continuous fun s => hk D.c ξ (t - s) := by unfold hk; fun_prop
      have hint1 : IntervalIntegrable (fun s => hk D.c ξ (t - s) * ‖Gv v (ξ, s)‖) volume 0 t :=
        (hk1.mul (hG.comp (continuous_const.prodMk continuous_id)).norm).intervalIntegrable _ _
      have hint2 : IntervalIntegrable (fun s => a s * b s) volume 0 t :=
        ((hac.mul hbc).mono (by rw [uIcc_of_le ht.1])).intervalIntegrable
      have h2 : ∫ s in (0 : ℝ)..t, hk D.c ξ (t - s) * ‖Gv v (ξ, s)‖ * (1 + ‖ξ‖) ^ 4 ≤
          ∫ s in (0 : ℝ)..t, 64 * π * Z * (a s * b s) := by
        refine intervalIntegral.integral_mono_on ht.1 (hint1.mul_const _) (hint2.const_mul _)
          fun s hs => ?_
        have hsT : s ∈ Icc 0 T := hsub hs
        have hb := norm_Bq_peso (h.cont_slice hsT) (hslice s hsT) ξ
        have e : Gv v (ξ, s) = Bq (fun η => v (η, s)) ξ := rfl
        rw [e]
        have hk0 := (hk_pos D.c ξ (t - s)).le
        calc hk D.c ξ (t - s) * ‖Bq (fun η => v (η, s)) ξ‖ * (1 + ‖ξ‖) ^ 4
            = hk D.c ξ (t - s) * (‖Bq (fun η => v (η, s)) ξ‖ * (1 + ‖ξ‖) ^ 4) := by ring
          _ ≤ hk D.c ξ (t - s) * (‖ξ‖ * (64 * π * (Z * exp (lam * Ψ s / 2)) * L s)) := by
              gcongr
          _ = 64 * π * Z * (a s * b s) := by simp only [ha_def, hb_def]; ring
      calc ‖Iduh D.c (Gv v) ξ t‖ * (1 + ‖ξ‖) ^ 4
          ≤ (∫ s in (0 : ℝ)..t, hk D.c ξ (t - s) * ‖Gv v (ξ, s)‖) * (1 + ‖ξ‖) ^ 4 := by gcongr
        _ = ∫ s in (0 : ℝ)..t, hk D.c ξ (t - s) * ‖Gv v (ξ, s)‖ * (1 + ‖ξ‖) ^ 4 :=
            (intervalIntegral.integral_mul_const _ _).symm
        _ ≤ ∫ s in (0 : ℝ)..t, 64 * π * Z * (a s * b s) := h2
        _ = 64 * π * Z * ∫ s in (0 : ℝ)..t, a s * b s := intervalIntegral.integral_const_mul _ _
    set β : ℝ := 128 * π with hβ_def
    have hβ : 0 < β := by positivity
    set μ' := 2 * D.c / β * exp (lam * Ψ t / 2) with hμ'_def
    have hμ' : 0 < μ' := by positivity
    have hab := amgm_integral ht.1 hμ' hac hbc
    have ha2 : ∫ s in (0 : ℝ)..t, a s ^ 2 ≤ 1 / (2 * D.c) := kernel_sq_le hc ξ ht.1
    have hb2 : ∫ s in (0 : ℝ)..t, b s ^ 2 ≤ exp (lam * Ψ t) / lam := by
      have e : (fun s => b s ^ 2) = fun s => L s ^ 2 * exp (lam * Ψ s) := by
        funext s
        simp only [hb_def]
        rw [mul_pow, ← exp_nat_mul]
        push_cast
        ring_nf
      rw [e]
      have h1 := integral_L1_exp_le h hE0 hE hA hl ht
      have h2 : (exp (lam * Ψ t) - 1) / lam ≤ exp (lam * Ψ t) / lam := by
        gcongr
        linarith
      exact h1.trans h2
    have hsq : exp (lam * Ψ t) = exp (lam * Ψ t / 2) ^ 2 := by
      rw [← exp_nat_mul]
      push_cast
      ring_nf
    have h3 : (μ' * (1 / (2 * D.c)) + exp (lam * Ψ t) / lam / μ') / 2 =
        exp (lam * Ψ t / 2) / β := by
      have hlam' : lam = β ^ 2 / (2 * D.c) := by rw [hlam_def, hβ_def]; rfl
      rw [hsq, hμ'_def, hlam']
      have := exp_pos (lam * Ψ t / 2)
      field_simp
      ring
    have h4 : ∫ s in (0 : ℝ)..t, a s * b s ≤ exp (lam * Ψ t / 2) / β := by
      rw [← h3]
      calc ∫ s in (0 : ℝ)..t, a s * b s
          ≤ (μ' * (∫ s in (0 : ℝ)..t, a s ^ 2) + (∫ s in (0 : ℝ)..t, b s ^ 2) / μ') / 2 := hab
        _ ≤ (μ' * (1 / (2 * D.c)) + exp (lam * Ψ t) / lam / μ') / 2 := by gcongr
    have h5 : 64 * π * Z * ∫ s in (0 : ℝ)..t, a s * b s ≤ Z * exp (lam * Ψ t / 2) / 2 := by
      calc 64 * π * Z * ∫ s in (0 : ℝ)..t, a s * b s
          ≤ 64 * π * Z * (exp (lam * Ψ t / 2) / β) := by gcongr
        _ = Z * exp (lam * Ψ t / 2) / 2 := by
            rw [hβ_def]
            field_simp
            ring
    linarith
  have hZle : Z ≤ D.M₀ + Z / 2 := by
    refine csSup_le hne ?_
    rintro z ⟨ξ, t, ht, rfl⟩
    have hk := hkey ξ t ht
    have hex : exp (-(lam * Ψ t / 2)) * exp (lam * Ψ t / 2) = 1 := by
      rw [← exp_add]
      simp
    have hle1 := hexle t ht
    have hpos := exp_pos (-(lam * Ψ t / 2))
    calc exp (-(lam * Ψ t / 2)) * (‖v (ξ, t)‖ * (1 + ‖ξ‖) ^ 4)
        ≤ exp (-(lam * Ψ t / 2)) * (D.M₀ + Z * exp (lam * Ψ t / 2) / 2) := by gcongr
      _ = exp (-(lam * Ψ t / 2)) * D.M₀ +
            Z * (exp (-(lam * Ψ t / 2)) * exp (lam * Ψ t / 2)) / 2 := by ring
      _ = exp (-(lam * Ψ t / 2)) * D.M₀ + Z / 2 := by rw [hex, mul_one]
      _ ≤ 1 * D.M₀ + Z / 2 := by gcongr
      _ = D.M₀ + Z / 2 := by ring
  have hZ2 : Z ≤ 2 * D.M₀ := by linarith
  intro t ht ξ
  have h1 := hZ ξ t ht
  rw [exp_neg, inv_mul_le_iff₀ (exp_pos _)] at h1
  have hΨ := Psi_le h hE0 hE hA ht hT'
  calc ‖v (ξ, t)‖ * (1 + ‖ξ‖) ^ 4 ≤ exp (lam * Ψ t / 2) * Z := h1
    _ ≤ exp (lam * Psimax D.c A E T' / 2) * (2 * D.M₀) := by
        gcongr
    _ = Bnd D.c D.M₀ A E T' := by
        unfold Bnd
        ring

end ATK.NSContinua

#print axioms ATK.NSEquacao.SolF.cont_slice
#print axioms ATK.NSEquacao.SolF.pesos
#print axioms ATK.NSEquacao.SolF.pesos_slice
#print axioms ATK.NSEquacao.SolF.contOn
#print axioms ATK.NSContinua.solF_of_sol_gen
#print axioms ATK.NSContinua.Bil_eq_Bq
#print axioms ATK.NSContinua.dv_apply
#print axioms ATK.NSContinua.inner_dv
#print axioms ATK.NSContinua.hasDerivWithinAt_Q
#print axioms ATK.NSContinua.integrable_inner_Bil
#print axioms ATK.NSContinua.integrable_norm_Bil
#print axioms ATK.NSContinua.deriv_Q_eq
#print axioms ATK.NSContinua.antitoneOn_of_deriv
#print axioms ATK.NSContinua.monotoneOn_of_deriv
#print axioms ATK.NSContinua.energia_decresce
#print axioms ATK.NSContinua.enstrofia_deriv_le
#print axioms ATK.NSContinua.continuousOn_L1
#print axioms ATK.NSContinua.continuousOn_Q
#print axioms ATK.NSContinua.rr
#print axioms ATK.NSContinua.K₁
#print axioms ATK.NSContinua.I₁_nonneg
#print axioms ATK.NSContinua.rr_pos
#print axioms ATK.NSContinua.K₁_nonneg
#print axioms ATK.NSContinua.enstrofia_deriv_abs
#print axioms ATK.NSContinua.D1
#print axioms ATK.NSContinua.Psi
#print axioms ATK.NSContinua.Psimax
#print axioms ATK.NSContinua.hasDerivWithinAt_Psi
#print axioms ATK.NSContinua.Psi_zero
#print axioms ATK.NSContinua.continuousOn_Psi
#print axioms ATK.NSContinua.L1_sq_le_dPsi
#print axioms ATK.NSContinua.Psi_nonneg
#print axioms ATK.NSContinua.Psi_le
#print axioms ATK.NSContinua.integral_L1_exp_le
#print axioms ATK.NSContinua.norm_Bq_peso
#print axioms ATK.NSContinua.norm_Iduh_le_int
#print axioms ATK.NSContinua.kernel_sq_le
#print axioms ATK.NSContinua.amgm_integral
#print axioms ATK.NSContinua.lamG
#print axioms ATK.NSContinua.Bnd
#print axioms ATK.NSContinua.cota_continua
