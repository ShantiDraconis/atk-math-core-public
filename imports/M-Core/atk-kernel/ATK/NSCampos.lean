import ATK.NSFisico
import Mathlib.Analysis.Fourier.Convolution

/-!
# ATK — Navier–Stokes, marco NS4b: os campos físicos e a equação ponto a ponto

Ponte B3, marco NS4b. A partir de `Φ L V` (NS4a):

* derivadas parciais em `x` e derivada em `t` (nos tempos interiores) como novas integrais de
  Fourier (`dX_Φ`, `hasDerivAt_Φ_t`);
* a transformada inversa `Fi V (x, t) = ∫ e^{2πi⟨ξ,x⟩} V(ξ, t) dξ` e a regra do produto
  (`mul_Fi`: produto de transformadas = transformada da convolução);
* a forma não linear sem projeção `Nl` e o fechamento da classe `Suave` por ela.

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta**; **CLOSED_MATH continua
false**.
-/

set_option autoImplicit false

open MeasureTheory Real Filter Topology Set
open scoped ContDiff Convolution
open FourierTransform
open ATK.LigacaoNS (E3)
open ATK.NSFourierBase ATK.NSPicard ATK.NSRegular ATK.NSFisico

namespace ATK.NSCampos

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-! ### Integrabilidade e fatias -/

theorem integrable_integrand {T : ℝ} {L : E3 → (C3 →L[ℝ] W)} (hL : AEStronglyMeasurable L)
    {K : ℝ} {p : ℕ} (hLb : ∀ ξ, ‖L ξ‖ * ‖ξ‖ ≤ K * (1 + ‖ξ‖) ^ p) {V : E3 × ℝ → C3}
    (hV : Reg0 T V) (x : E3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Integrable fun ξ => L ξ (ex ξ x • V (ξ, t)) := by
  obtain ⟨C, hC⟩ := hV.2 (p + 4)
  refine integrable_sing (K := K) (C := C) |>.mono'
    (aesm_apply hL (continuous_exV hV x ht).aestronglyMeasurable) ?_
  filter_upwards [Measure.ae_ne volume 0] with ξ hξ
  have h1 := (L ξ).le_opNorm (ex ξ x • V (ξ, t))
  rw [norm_smul, norm_ex, one_mul] at h1
  exact h1.trans (norm_L_mul_le hLb hξ (norm_nonneg _) ((hC t ht).le_inv ξ))

/-- Derivada em `x` da fatia `y ↦ Φ L V (y, t)`. -/
theorem hasFDerivAt_Φ_x [CompleteSpace W] {T : ℝ} {L : E3 → (C3 →L[ℝ] W)}
    (hL : AEStronglyMeasurable L) {K : ℝ} {p : ℕ} (hK : 0 ≤ K)
    (hLb : ∀ ξ, ‖L ξ‖ * ‖ξ‖ ≤ K * (1 + ‖ξ‖) ^ p) {V V' : E3 × ℝ → C3} (hV : Reg0 T V)
    (hV' : Reg0 T V')
    (hdV : ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => V (ξ, s)) (V' (ξ, t)) (Icc 0 T) t)
    (x : E3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasFDerivAt (fun y => Φ L V (y, t)) (Φ (LA L) V (x, t)) x := by
  have hz : (x, t) ∈ Dom T := ⟨mem_univ _, ht⟩
  have h := hasFDerivWithinAt_Φ hL hK hLb hV hV' hdV hz
  have hi : HasFDerivAt (fun y : E3 => ((y, t) : E3 × ℝ)) (ContinuousLinearMap.inl ℝ E3 ℝ) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  have h2 := h.comp x (hi.hasFDerivWithinAt (s := univ))
    (fun y _ => (⟨mem_univ _, ht⟩ : ((y, t) : E3 × ℝ) ∈ Dom T))
  rw [hasFDerivWithinAt_univ] at h2
  have h3 : HasFDerivAt (fun y => NSFisico.Φ L V (y, t)) _ x := h2
  refine h3.congr_fderiv ?_
  refine ContinuousLinearMap.ext fun h => ?_
  simp

/-- Derivada em `t` nos tempos interiores. -/
theorem hasDerivAt_Φ_t [CompleteSpace W] {T : ℝ} {L : E3 → (C3 →L[ℝ] W)}
    (hL : AEStronglyMeasurable L) {K : ℝ} {p : ℕ} (hK : 0 ≤ K)
    (hLb : ∀ ξ, ‖L ξ‖ * ‖ξ‖ ≤ K * (1 + ‖ξ‖) ^ p) {V V' : E3 × ℝ → C3} (hV : Reg0 T V)
    (hV' : Reg0 T V')
    (hdV : ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => V (ξ, s)) (V' (ξ, t)) (Icc 0 T) t)
    (x : E3) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => Φ L V (x, s)) (Φ L V' (x, t)) t := by
  have hz : (x, t) ∈ Dom T := ⟨mem_univ _, Ioo_subset_Icc_self ht⟩
  have h := (hasFDerivWithinAt_Φ hL hK hLb hV hV' hdV hz).hasFDerivAt
    (prod_mem_nhds univ_mem (Icc_mem_nhds ht.1 ht.2))
  have hi : HasDerivAt (fun s : ℝ => ((x, s) : E3 × ℝ)) ((0 : E3), (1 : ℝ)) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have h2 := h.comp_hasDerivAt t hi
  have h3 : HasDerivAt (fun s => NSFisico.Φ L V (x, s)) _ t := h2
  refine h3.congr_deriv ?_
  rw [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', map_zero, zero_add]
  have hint : Integrable fun ξ => LB L ξ (ex ξ x • V' (ξ, t)) :=
    integrable_integrand (aesm_LB hL) (LB_bound hLb) hV' x (Ioo_subset_Icc_self ht)
  unfold NSFisico.Φ
  rw [ContinuousLinearMap.integral_apply hint]
  simp [LB_apply]

/-! ### A transformada inversa `Fi` -/

/-- A identidade como aplicação `ℝ`-linear de `ℂ³`. -/
noncomputable abbrev idL : C3 →L[ℝ] C3 := ContinuousLinearMap.id ℝ C3

/-- **A transformada inversa** `Fi V (x, t) = ∫ e^{2πi⟨ξ,x⟩} V(ξ, t) dξ`. -/
noncomputable def Fi (V : E3 × ℝ → C3) : E3 × ℝ → C3 := NSFisico.Φ (fun _ => idL) V

theorem Fi_apply (V : E3 × ℝ → C3) (z : E3 × ℝ) : Fi V z = ∫ ξ, ex ξ z.1 • V (ξ, z.2) := rfl

theorem aesm_idL : AEStronglyMeasurable (fun _ : E3 => idL) := aestronglyMeasurable_const

theorem idL_bound (ξ : E3) : ‖idL‖ * ‖ξ‖ ≤ 1 * (1 + ‖ξ‖) ^ 1 := by
  have h1 : ‖idL‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have := norm_nonneg ξ
  calc ‖idL‖ * ‖ξ‖ ≤ 1 * ‖ξ‖ := by gcongr
    _ ≤ 1 * (1 + ‖ξ‖) ^ 1 := by simp

/-- O multiplicador `2πi ξ_j`. -/
noncomputable def mj (j : Fin 3) (ξ : E3) : ℂ := 2 * π * Complex.I * ((ξ j : ℝ) : ℂ)

theorem continuous_mj (j : Fin 3) : Continuous (mj j) := by
  unfold mj
  have : Continuous fun ξ : E3 => ξ j := (EuclideanSpace.proj (𝕜 := ℝ) j).continuous
  fun_prop

theorem norm_mj_le (j : Fin 3) (ξ : E3) : ‖mj j ξ‖ ≤ 2 * π * (1 + ‖ξ‖) ^ 1 := by
  have e : mj j ξ = ((2 * π * ξ j : ℝ) : ℂ) * Complex.I := by
    unfold mj
    push_cast
    ring
  have h1 : |ξ j| ≤ ‖ξ‖ := by
    have := EuclideanSpace.norm_eq ξ
    rw [this]
    refine Real.le_sqrt_of_sq_le ?_
    have := Finset.single_le_sum (f := fun i => ‖ξ i‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
    simpa [Real.norm_eq_abs, sq_abs] using this
  rw [e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π), pow_one]
  have := pi_pos
  nlinarith

theorem inner_e (ξ : E3) (j : Fin 3) : inner ℝ ξ (ATK.LigacaoNS.e j) = ξ j := by
  simp [ATK.LigacaoNS.e, EuclideanSpace.inner_single_right]

/-- **Derivada parcial de `Fi V`**: `∂_j Fi V = Fi (2πi ξ_j V)`. -/
theorem dX_Fi {T : ℝ} {V V' : E3 × ℝ → C3} (hV : Reg0 T V) (hV' : Reg0 T V')
    (hdV : ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => V (ξ, s)) (V' (ξ, t)) (Icc 0 T) t)
    (j : Fin 3) (x : E3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ATK.LigacaoNS.dX j (fun y => Fi V (y, t)) x = Fi (fun q => mj j q.1 • V q) (x, t) := by
  have h := hasFDerivAt_Φ_x aesm_idL zero_le_one idL_bound hV hV' hdV x ht
  unfold ATK.LigacaoNS.dX
  rw [show (fun y => Fi V (y, t)) = fun y => NSFisico.Φ (fun _ => idL) V (y, t) from rfl,
    h.fderiv]
  have hint : Integrable fun ξ => LA (fun _ => idL) ξ (ex ξ x • V (ξ, t)) :=
    integrable_integrand (aesm_LA aesm_idL) (LA_bound idL_bound) hV x ht
  unfold NSFisico.Φ
  rw [ContinuousLinearMap.integral_apply hint, Fi_apply]
  congr 1
  funext ξ
  rw [LA_apply, inner_e]
  simp only [ContinuousLinearMap.id_apply, mj]
  rw [smul_comm (ex ξ x), ← Complex.coe_smul, smul_smul]
  congr 1
  push_cast
  ring

/-- **Derivada temporal de `Fi V`** nos tempos interiores. -/
theorem hasDerivAt_Fi_t {T : ℝ} {V V' : E3 × ℝ → C3} (hV : Reg0 T V) (hV' : Reg0 T V')
    (hdV : ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => V (ξ, s)) (V' (ξ, t)) (Icc 0 T) t)
    (x : E3) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => Fi V (x, s)) (Fi V' (x, t)) t :=
  hasDerivAt_Φ_t aesm_idL zero_le_one idL_bound hV hV' hdV x ht

/-! ### Multiplicadores complexos -/

theorem Reg0.smulC {T : ℝ} {φ : E3 → ℂ} (hφ : Continuous φ) {K : ℝ} {p : ℕ}
    (hK : ∀ ξ, ‖φ ξ‖ ≤ K * (1 + ‖ξ‖) ^ p) {g : E3 × ℝ → C3} (hg : Reg0 T g) :
    Reg0 T (fun q => φ q.1 • g q) := by
  refine ⟨fun t ht => hφ.smul (hg.1 t ht), fun m => ?_⟩
  obtain ⟨C, hC⟩ := hg.2 (m + p)
  refine ⟨K * C, fun t ht ζ => ?_⟩
  have h1 := hC t ht ζ
  have h2 := hK ζ
  simp only
  rw [norm_smul]
  have hK0 : 0 ≤ K := by
    have := hK 0
    have h0 : (0 : ℝ) < (1 + ‖(0 : E3)‖) ^ p := by positivity
    nlinarith [norm_nonneg (φ 0)]
  calc ‖φ ζ‖ * ‖g (ζ, t)‖ * (1 + ‖ζ‖) ^ m
      ≤ (K * (1 + ‖ζ‖) ^ p) * ‖g (ζ, t)‖ * (1 + ‖ζ‖) ^ m := by gcongr
    _ = K * (‖g (ζ, t)‖ * (1 + ‖ζ‖) ^ (m + p)) := by ring
    _ ≤ K * C := by gcongr

theorem Suave.smulC {T : ℝ} {φ : E3 → ℂ} (hφ : Continuous φ) {K : ℝ} {p : ℕ}
    (hK : ∀ ξ, ‖φ ξ‖ ≤ K * (1 + ‖ξ‖) ^ p) :
    ∀ {k : ℕ} {g : E3 × ℝ → C3}, Suave T k g → Suave T k (fun q => φ q.1 • g q)
  | 0, _, hg => Reg0.smulC hφ hK hg
  | _ + 1, _, hg => by
    obtain ⟨hg0, g', hg', hd⟩ := hg
    exact ⟨Reg0.smulC hφ hK hg0, fun q => φ q.1 • g' q, Suave.smulC hφ hK hg',
      fun ξ t ht => (hd ξ t ht).const_smul (φ ξ)⟩

theorem Reg0.neg {T : ℝ} {g : E3 × ℝ → C3} (hg : Reg0 T g) : Reg0 T (-g) := by
  refine ⟨fun t ht => (hg.1 t ht).neg, fun m => ?_⟩
  obtain ⟨C, hC⟩ := hg.2 m
  exact ⟨C, fun t ht ζ => by simpa using hC t ht ζ⟩

theorem Suave.neg {T : ℝ} : ∀ {k : ℕ} {g : E3 × ℝ → C3}, Suave T k g → Suave T k (-g)
  | 0, _, hg => Reg0.neg hg
  | _ + 1, _, hg => by
    obtain ⟨hg0, g', hg', hd⟩ := hg
    exact ⟨Reg0.neg hg0, -g', Suave.neg hg', fun ξ t ht => (hd ξ t ht).neg⟩

theorem Suave.sub {T : ℝ} {k : ℕ} {f g : E3 × ℝ → C3} (hf : Suave T k f) (hg : Suave T k g) :
    Suave T k (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add (Suave.neg hg)

/-! ### A forma não linear sem projeção -/

/-- `Ñ(f, g)(ξ, t) = −2πi N(f(·,t), g(·,t))(ξ)` (sem o projetor de Leray). -/
noncomputable def Nl (f g : E3 × ℝ → C3) (q : E3 × ℝ) : C3 :=
  cI • nl (fun η => f (η, q.2)) (fun η => g (η, q.2)) q.1

theorem Bil_eq_leray_Nl (f g : E3 × ℝ → C3) (q : E3 × ℝ) : Bil f g q = leray q.1 (Nl f g q) := rfl

theorem Reg0.nls {T : ℝ} {f g : E3 × ℝ → C3} (hf : Reg0 T f) (hg : Reg0 T g) :
    Reg0 T (Nl f g) := by
  obtain ⟨A, hA⟩ := hf.2 4
  obtain ⟨B, hB⟩ := hg.2 4
  refine ⟨fun t ht => ?_, fun m => ?_⟩
  · exact (continuous_nl (hf.1 t ht) (hg.1 t ht) (hA t ht) (hB t ht)).const_smul cI
  · obtain ⟨Am, hAm⟩ := hf.2 (m + 1)
    obtain ⟨Bm, hBm⟩ := hg.2 (m + 1)
    refine ⟨2 * π * (2 ^ (m + 1) * Kp 4 * (Am * B + A * Bm)), fun t ht ξ => ?_⟩
    have h1 := norm_nl_le (hf.1 t ht) (hg.1 t ht) (m + 1) (hA t ht) (hAm t ht) (hB t ht)
      (hBm t ht) ξ
    have hw : 0 < 1 + ‖ξ‖ := by positivity
    have h2 : ‖nl (fun η => f (η, t)) (fun η => g (η, t)) ξ‖ * (1 + ‖ξ‖) ^ m ≤
        2 ^ (m + 1) * Kp 4 * (Am * B + A * Bm) := by
      have hQ0 : 0 ≤ 2 ^ (m + 1) * Kp 4 * (Am * B + A * Bm) := by
        have := (hAm t ht).nonneg
        have := (hBm t ht).nonneg
        have := (hA t ht).nonneg
        have := (hB t ht).nonneg
        have := Kp_nonneg 4
        positivity
      rw [pow_succ] at h1
      have h3 : ‖ξ‖ * (2 ^ (m + 1) * Kp 4 * (Am * B + A * Bm)) ≤
          (1 + ‖ξ‖) * (2 ^ (m + 1) * Kp 4 * (Am * B + A * Bm)) := by
        gcongr
        linarith
      have h4 : ‖nl (fun η => f (η, t)) (fun η => g (η, t)) ξ‖ * (1 + ‖ξ‖) ^ m * (1 + ‖ξ‖) ≤
          (2 ^ (m + 1) * Kp 4 * (Am * B + A * Bm)) * (1 + ‖ξ‖) := by
        rw [← mul_assoc] at h1
        linarith
      exact le_of_mul_le_mul_right h4 hw
    simp only [Nl]
    rw [norm_smul, norm_cI, mul_assoc]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- Derivada temporal de `N(f(·,t), g(·,t))(ξ)` (regra do produto sob a integral). -/
theorem hasDerivWithinAt_nl {T : ℝ} {f g f' g' : E3 × ℝ → C3} (hf : Reg0 T f) (hg : Reg0 T g)
    (hf' : Reg0 T f') (hg' : Reg0 T g')
    (hdf : ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => f (ξ, s)) (f' (ξ, t)) (Icc 0 T) t)
    (hdg : ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => g (ξ, s)) (g' (ξ, t)) (Icc 0 T) t)
    (ξ : E3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => nl (fun η => f (η, s)) (fun η => g (η, s)) ξ)
      (nl (fun η => f' (η, t)) (fun η => g (η, t)) ξ +
        nl (fun η => f (η, t)) (fun η => g' (η, t)) ξ) (Icc 0 T) t := by
  obtain ⟨A, hA⟩ := hf.2 4
  obtain ⟨B, hB⟩ := hg.2 4
  obtain ⟨A', hA'⟩ := hf'.2 4
  obtain ⟨B', hB'⟩ := hg'.2 4
  have hA0 : 0 ≤ A := (hA t ht).nonneg
  have hB0 : 0 ≤ B := (hB t ht).nonneg
  have hA'0 : 0 ≤ A' := (hA' t ht).nonneg
  have hB'0 : 0 ≤ B' := (hB' t ht).nonneg
  set F : ℝ → E3 → C3 := fun s η => ip ξ (f (ξ - η, s)) • g (η, s)
  set F' : ℝ → E3 → C3 := fun s η =>
    ip ξ (f' (ξ - η, s)) • g (η, s) + ip ξ (f (ξ - η, s)) • g' (η, s)
  have hderiv : ∀ η, ∀ s ∈ Icc 0 T, HasDerivWithinAt (fun s => F s η) (F' s η) (Icc 0 T) s := by
    intro η s hs
    have h1 : HasDerivWithinAt (fun s => ip ξ (f (ξ - η, s))) (ip ξ (f' (ξ - η, s)))
        (Icc 0 T) s := by
      have := ((ipL ξ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt s (hdf (ξ - η) s hs)
      simpa [Function.comp_def, ipL_apply] using this
    have h2 := h1.smul (hdg η s hs)
    convert h2 using 1
    simp only [F']
    abel
  have hb : Integrable fun η : E3 => ‖ξ‖ * ((A' * B + A * B') * ((1 + ‖η‖) ^ 4)⁻¹) :=
    ((integrable_inv_pow (m := 4) le_rfl).const_mul _).const_mul _
  have hbound : ∀ η, ∀ s ∈ Icc 0 T, ‖F' s η‖ ≤ ‖ξ‖ * ((A' * B + A * B') * ((1 + ‖η‖) ^ 4)⁻¹) := by
    intro η s hs
    simp only [F']
    have e1 := norm_ip_le ξ (f' (ξ - η, s))
    have e2 := norm_ip_le ξ (f (ξ - η, s))
    have e3 := (hA' s hs).le (ξ - η)
    have e4 := (hA s hs).le (ξ - η)
    have e5 := (hB s hs).le_inv η
    have e6 := (hB' s hs).le_inv η
    have hinv : 0 ≤ ((1 + ‖η‖) ^ 4)⁻¹ := by positivity
    calc ‖ip ξ (f' (ξ - η, s)) • g (η, s) + ip ξ (f (ξ - η, s)) • g' (η, s)‖
        ≤ ‖ip ξ (f' (ξ - η, s))‖ * ‖g (η, s)‖ + ‖ip ξ (f (ξ - η, s))‖ * ‖g' (η, s)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul]
      _ ≤ (‖ξ‖ * A') * (B * ((1 + ‖η‖) ^ 4)⁻¹) + (‖ξ‖ * A) * (B' * ((1 + ‖η‖) ^ 4)⁻¹) := by
          gcongr
          · exact e1.trans (by gcongr)
          · exact e2.trans (by gcongr)
      _ = ‖ξ‖ * ((A' * B + A * B') * ((1 + ‖η‖) ^ 4)⁻¹) := by ring
  have hmeas : ∀ s ∈ Icc 0 T, AEStronglyMeasurable (F s) := fun s hs =>
    ((continuous_ip_comp (hf.1 s hs) ξ).smul (hg.1 s hs)).aestronglyMeasurable
  have hint := integrable_nl (hf.1 t ht) (hg.1 t ht) (hA t ht) (hB t ht) ξ
  have hI := hasDerivWithinAt_integral (convex_Icc 0 T) ht hmeas hint hb hderiv hbound
  have hI1 := integrable_nl (hf'.1 t ht) (hg.1 t ht) (hA' t ht) (hB t ht) ξ
  have hI2 := integrable_nl (hf.1 t ht) (hg'.1 t ht) (hA t ht) (hB' t ht) ξ
  have hsum : ∫ η, F' t η = nl (fun η => f' (η, t)) (fun η => g (η, t)) ξ +
      nl (fun η => f (η, t)) (fun η => g' (η, t)) ξ := by
    simp only [F', nl]
    exact integral_add hI1 hI2
  rw [hsum] at hI
  exact hI

theorem Suave.nls {T : ℝ} : ∀ {k : ℕ} {f g : E3 × ℝ → C3}, Suave T k f → Suave T k g →
    Suave T k (Nl f g)
  | 0, _, _, hf, hg => Reg0.nls hf hg
  | _ + 1, f, g, hf, hg => by
    obtain ⟨hf0, f', hf', hdf⟩ := hf
    obtain ⟨hg0, g', hg', hdg⟩ := hg
    refine ⟨Reg0.nls hf0 hg0, Nl f' g + Nl f g', ?_, ?_⟩
    · exact (Suave.nls hf' (Suave.mono ⟨hg0, g', hg', hdg⟩)).add
        (Suave.nls (Suave.mono ⟨hf0, f', hf', hdf⟩) hg')
    · intro ξ t ht
      have h : HasDerivWithinAt
          (fun s => cI • nl (fun η => f (η, s)) (fun η => g (η, s)) ξ)
          (cI • (nl (fun η => f' (η, t)) (fun η => g (η, t)) ξ +
            nl (fun η => f (η, t)) (fun η => g' (η, t)) ξ)) (Icc 0 T) t :=
        (hasDerivWithinAt_nl hf0 hg0 hf'.reg0 hg'.reg0 hdf hdg ξ ht).const_smul cI
      refine h.congr_deriv ?_
      rw [Pi.add_apply, smul_add]
      rfl

/-! ### `Fi` como transformada inversa; produto e convolução -/

theorem ex_eq (ξ x : E3) : ex ξ x = Complex.exp (↑(2 * π * inner ℝ ξ x) * Complex.I) := by
  unfold ex
  congr 1
  push_cast
  ring

theorem Fi_eq_fourierInv (V : E3 × ℝ → C3) (z : E3 × ℝ) :
    Fi V z = 𝓕⁻ (fun ξ => V (ξ, z.2)) z.1 := by
  rw [Fi_apply, Real.fourierInv_eq']
  congr 1
  funext ξ
  rw [ex_eq]

theorem fourierInv_scalar_eq (f : E3 → ℂ) (x : E3) :
    𝓕⁻ f x = ∫ ξ, ex ξ x * f ξ := by
  rw [Real.fourierInv_eq']
  congr 1
  funext ξ
  rw [ex_eq, smul_eq_mul]

/-- **Produto de transformadas inversas = transformada inversa da convolução.** -/
theorem mul_fourierInv {f : E3 → ℂ} {g : E3 → C3} (hf : Integrable f) (hg : Integrable g)
    (x : E3) : 𝓕⁻ f x • 𝓕⁻ g x = 𝓕⁻ (f ⋆[ContinuousLinearMap.lsmul ℂ ℂ] g) x := by
  rw [Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg,
    Real.fourierInv_eq_fourier_neg, Real.fourier_smul_convolution_eq hf hg]

/-! ### Realidade -/

/-- Parte real coordenada a coordenada, `ℂ³ → ℝ³`. -/
noncomputable def reV : C3 →L[ℝ] E3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun a => WithLp.toLp 2 (fun j => (a j).re)
      map_add' := fun a b => by ext j; simp
      map_smul' := fun r a => by ext j; simp [Complex.real_smul] }

@[simp] theorem reV_apply (a : C3) (j : Fin 3) : reV a j = (a j).re := rfl

theorem cx_reV {a : C3} (h : cj a = a) : cx (reV a) = a := by
  ext j
  have hj : (starRingEnd ℂ) (a j) = a j := by
    have := congrArg (fun b : C3 => b j) h
    simpa using this
  simp only [cx_apply, reV_apply]
  exact Complex.conj_eq_iff_re.mp hj

theorem conj_ex (ξ x : E3) : (starRingEnd ℂ) (ex ξ x) = ex (-ξ) x := by
  unfold ex
  rw [← Complex.exp_conj]
  congr 1
  simp [inner_neg_left, Complex.conj_ofReal, map_mul, Complex.conj_I, map_ofNat]

/-- **A transformada inversa de um campo hermitiano é real.** -/
theorem cj_Fi {V : E3 × ℝ → C3} (hV : ∀ ξ t, V (-ξ, t) = cj (V (ξ, t))) (z : E3 × ℝ) :
    cj (Fi V z) = Fi V z := by
  rw [Fi_apply, ← cj_integral, ← integral_neg_eq_self]
  congr 1
  funext ξ
  rw [cj_smul, conj_ex, hV, cj_cj, neg_neg]

end ATK.NSCampos

#print axioms ATK.NSCampos.integrable_integrand
#print axioms ATK.NSCampos.hasFDerivAt_Φ_x
#print axioms ATK.NSCampos.hasDerivAt_Φ_t
#print axioms ATK.NSCampos.idL
#print axioms ATK.NSCampos.Fi
#print axioms ATK.NSCampos.Fi_apply
#print axioms ATK.NSCampos.aesm_idL
#print axioms ATK.NSCampos.idL_bound
#print axioms ATK.NSCampos.mj
#print axioms ATK.NSCampos.continuous_mj
#print axioms ATK.NSCampos.norm_mj_le
#print axioms ATK.NSCampos.inner_e
#print axioms ATK.NSCampos.dX_Fi
#print axioms ATK.NSCampos.hasDerivAt_Fi_t
#print axioms ATK.NSCampos.Reg0.smulC
#print axioms ATK.NSCampos.Suave.smulC
#print axioms ATK.NSCampos.Reg0.neg
#print axioms ATK.NSCampos.Suave.neg
#print axioms ATK.NSCampos.Suave.sub
#print axioms ATK.NSCampos.Nl
#print axioms ATK.NSCampos.Bil_eq_leray_Nl
#print axioms ATK.NSCampos.Reg0.nls
#print axioms ATK.NSCampos.hasDerivWithinAt_nl
#print axioms ATK.NSCampos.Suave.nls
#print axioms ATK.NSCampos.ex_eq
#print axioms ATK.NSCampos.Fi_eq_fourierInv
#print axioms ATK.NSCampos.fourierInv_scalar_eq
#print axioms ATK.NSCampos.mul_fourierInv
#print axioms ATK.NSCampos.reV
#print axioms ATK.NSCampos.reV_apply
#print axioms ATK.NSCampos.cx_reV
#print axioms ATK.NSCampos.conj_ex
#print axioms ATK.NSCampos.cj_Fi
