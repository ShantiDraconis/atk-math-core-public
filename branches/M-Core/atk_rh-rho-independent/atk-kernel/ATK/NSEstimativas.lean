import ATK.NSEnergia

/-!
# ATK — Estimativas elementares em `ℝ³` (para as estimativas de energia de ordem alta)

Camada 12 do ataque a B3 (ferramentas para a continuação):

* `cs_sq`: Cauchy–Schwarz `(∫ f g)² ≤ ∫ f² · ∫ g²` (funções reais não negativas);
* `tri_le`, `tri_leZ`: **estimativa trilinear** `(∫∫ X(ξ) Y(η) Z(ξ − η))² ≤ ‖X‖₂² ‖Y‖₁² ‖Z‖₂²`
  (e a versão com `Z ∈ L¹`) — Cauchy–Schwarz em `ℝ³ × ℝ³` e invariância por translação;
* `interp_L1`: **interpolação** `(∫ B)⁸ ≤ c⁴ (∫ (1+‖ξ‖)² B²) (∫ (1+‖ξ‖)⁴ B²)³` com
  `c = ∫ (1+‖ξ‖)^{−7/2}` (três Cauchy–Schwarz com pesos semi-inteiros);
* `absorve`: `T^{n+1} ≤ K Yⁿ Z ⇒ T ≤ ε Y + K Z / εⁿ` (Young por casos, sem potências reais).

**CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology
open scoped Real

namespace ATK.NSEstimativas

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSSuave

/-! ### Cauchy–Schwarz -/

theorem cs_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hf2 : Integrable (fun x => f x ^ 2) μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
  have hmf : MemLp f (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq hf).mpr hf2
  have hmg : MemLp g (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq hg).mpr hg2
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall hf0) (Eventually.of_forall hg0) hmf hmg
  have e1 : ∀ (u : α → ℝ), (∫ x, u x ^ (2 : ℝ) ∂μ) = ∫ x, u x ^ 2 ∂μ := fun u => by
    congr 1 with x; exact Real.rpow_two _
  rw [e1 f, e1 g] at h
  have hF : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hG : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hfg : 0 ≤ ∫ x, f x * g x ∂μ := integral_nonneg fun x => mul_nonneg (hf0 x) (hg0 x)
  calc (∫ x, f x * g x ∂μ) ^ 2
      ≤ ((∫ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hfg h 2
    _ = (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) := by
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast ((∫ x, g x ^ 2 ∂μ) ^ _),
          ← Real.rpow_mul hF, ← Real.rpow_mul hG]
        norm_num

/-! ### Estimativa trilinear -/

/-- Funções contínuas, não negativas, com decaimento `w₄⁻¹`. -/
structure Mansa (X : E3 → ℝ) : Prop where
  cont : Continuous X
  nonneg : ∀ ξ, 0 ≤ X ξ
  bound : ∃ C, ∀ ξ, X ξ ≤ C * (w 4 ξ)⁻¹

theorem Mansa.integrable {X : E3 → ℝ} (h : Mansa X) : Integrable X := by
  obtain ⟨C, hC⟩ := h.bound
  exact integrable_of_le_w4 h.nonneg hC h.cont.aestronglyMeasurable

theorem Mansa.le_const {X : E3 → ℝ} (h : Mansa X) : ∃ C, 0 ≤ C ∧ ∀ ξ, X ξ ≤ C := by
  obtain ⟨C, hC⟩ := h.bound
  have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((h.nonneg 0).trans (hC 0))
    (inv_pos.mpr (w_pos 4 0))
  exact ⟨C, hC0, fun ξ => (hC ξ).trans (mul_le_of_le_one_right hC0
    (inv_le_one_of_one_le₀ (one_le_w 4 ξ)))⟩

theorem Mansa.integrable_sq {X : E3 → ℝ} (h : Mansa X) : Integrable fun ξ => X ξ ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := h.le_const
  refine (h.integrable.const_mul C).mono' (h.cont.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), sq]
  exact mul_le_mul_of_nonneg_right (hC ξ) (h.nonneg ξ) |>.trans_eq (mul_comm _ _) |>.trans
    (by rw [mul_comm])

theorem Mansa.sqrt {X : E3 → ℝ} (h : Mansa X) : Continuous fun ξ => Real.sqrt (X ξ) :=
  Real.continuous_sqrt.comp h.cont

/-- **Estimativa trilinear** (`Y ∈ L¹`): `(∫∫ X(ξ) Y(η) Z(ξ − η))² ≤ ‖X‖₂² ‖Y‖₁² ‖Z‖₂²`. -/
theorem tri_le {X Y Z : E3 → ℝ} (hX : Mansa X) (hY : Mansa Y) (hZ : Mansa Z) :
    (∫ ξ, ∫ η, X ξ * Y η * Z (ξ - η)) ^ 2 ≤
      (∫ ξ, X ξ ^ 2) * (∫ η, Y η) ^ 2 * (∫ ζ, Z ζ ^ 2) := by
  set μ : Measure (E3 × E3) := (volume : Measure E3).prod volume
  set F : E3 × E3 → ℝ := fun p => X p.1 * Real.sqrt (Y p.2) with hF
  set G : E3 × E3 → ℝ := fun p => Real.sqrt (Y p.2) * Z (p.1 - p.2) with hG
  have hY0 := hY.nonneg
  have hsq : ∀ η, Real.sqrt (Y η) ^ 2 = Y η := fun η => Real.sq_sqrt (hY0 η)
  have hFG : ∀ p, F p * G p = X p.1 * Y p.2 * Z (p.1 - p.2) := by
    intro p
    simp only [hF, hG]
    have := Real.mul_self_sqrt (hY0 p.2)
    calc X p.1 * Real.sqrt (Y p.2) * (Real.sqrt (Y p.2) * Z (p.1 - p.2))
        = X p.1 * (Real.sqrt (Y p.2) * Real.sqrt (Y p.2)) * Z (p.1 - p.2) := by ring
      _ = X p.1 * Y p.2 * Z (p.1 - p.2) := by rw [this]
  have hF2 : ∀ p, F p ^ 2 = X p.1 ^ 2 * Y p.2 := by
    intro p; simp only [hF, mul_pow, hsq]
  have hG2 : ∀ p, G p ^ 2 = Y p.2 * Z (p.1 - p.2) ^ 2 := by
    intro p; simp only [hG, mul_pow, hsq]
  -- integrabilidades no produto
  have iF2 : Integrable (fun p => F p ^ 2) μ := by
    simp_rw [hF2]
    exact hX.integrable_sq.mul_prod hY.integrable
  have iG2 : Integrable (fun p => G p ^ 2) μ := by
    simp_rw [hG2]
    have := (hY.integrable).convolution_integrand (μ := volume) (ν := volume)
      (ContinuousLinearMap.mul ℝ ℝ) hZ.integrable_sq
    simpa [mul_comm] using this
  have cF : Continuous F := by
    simp only [hF]; exact (hX.cont.comp continuous_fst).mul (hY.sqrt.comp continuous_snd)
  have cG : Continuous G := by
    simp only [hG]
    exact (hY.sqrt.comp continuous_snd).mul (hZ.cont.comp (continuous_fst.sub continuous_snd))
  have iXYZ : Integrable (fun p : E3 × E3 => X p.1 * Y p.2 * Z (p.1 - p.2)) μ := by
    obtain ⟨CZ, hCZ0, hCZ⟩ := hZ.le_const
    refine ((hX.integrable.mul_prod hY.integrable).const_mul CZ).mono'
      (((hX.cont.comp continuous_fst).mul (hY.cont.comp continuous_snd)).mul
        (hZ.cont.comp (continuous_fst.sub continuous_snd))).aestronglyMeasurable
      (Eventually.of_forall fun p => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (hX.nonneg _) (hY0 _)) (hZ.nonneg _))]
    calc X p.1 * Y p.2 * Z (p.1 - p.2) ≤ X p.1 * Y p.2 * CZ :=
          mul_le_mul_of_nonneg_left (hCZ _) (mul_nonneg (hX.nonneg _) (hY0 _))
      _ = CZ * (X p.1 * Y p.2) := by ring
  have hcs := cs_sq (μ := μ) (fun p => mul_nonneg (hX.nonneg _) (Real.sqrt_nonneg _))
    (fun p => mul_nonneg (Real.sqrt_nonneg _) (hZ.nonneg _)) cF.aestronglyMeasurable
    cG.aestronglyMeasurable iF2 iG2
  -- reescrever as três integrais no produto
  have e1 : ∫ ξ, ∫ η, X ξ * Y η * Z (ξ - η) = ∫ p, F p * G p ∂μ := by
    simp_rw [hFG]
    exact (integral_prod _ iXYZ).symm
  have e2 : ∫ p, F p ^ 2 ∂μ = (∫ ξ, X ξ ^ 2) * ∫ η, Y η := by
    simp_rw [hF2]
    exact integral_prod_mul (fun ξ => X ξ ^ 2) Y
  have e3 : ∫ p, G p ^ 2 ∂μ = (∫ η, Y η) * ∫ ζ, Z ζ ^ 2 := by
    simp_rw [hG2]
    rw [integral_prod_symm _ (by simpa [hG2] using iG2)]
    simp only
    have : ∀ η, ∫ ξ, Y η * Z (ξ - η) ^ 2 = Y η * ∫ ζ, Z ζ ^ 2 := fun η => by
      rw [integral_const_mul, integral_sub_right_eq_self (fun ζ => Z ζ ^ 2) η]
    simp_rw [this]
    rw [integral_mul_const]
  rw [e1]
  calc (∫ p, F p * G p ∂μ) ^ 2 ≤ (∫ p, F p ^ 2 ∂μ) * ∫ p, G p ^ 2 ∂μ := hcs
    _ = (∫ ξ, X ξ ^ 2) * (∫ η, Y η) ^ 2 * (∫ ζ, Z ζ ^ 2) := by rw [e2, e3]; ring

/-- **Estimativa trilinear** (`Z ∈ L¹`): `(∫∫ X(ξ) Y(η) Z(ξ − η))² ≤ ‖X‖₂² ‖Y‖₂² ‖Z‖₁²`. -/
theorem tri_leZ {X Y Z : E3 → ℝ} (hX : Mansa X) (hY : Mansa Y) (hZ : Mansa Z) :
    (∫ ξ, ∫ η, X ξ * Y η * Z (ξ - η)) ^ 2 ≤
      (∫ ξ, X ξ ^ 2) * (∫ η, Y η ^ 2) * (∫ ζ, Z ζ) ^ 2 := by
  have e : ∀ ξ, ∫ η, X ξ * Y η * Z (ξ - η) = ∫ η, X ξ * Z η * Y (ξ - η) := fun ξ => by
    rw [← integral_sub_left_eq_self (fun η => X ξ * Y η * Z (ξ - η)) volume ξ]
    congr 1 with η
    simp only [sub_sub_cancel]
    ring
  simp_rw [e]
  have := tri_le hX hZ hY
  linarith

/-! ### Interpolação `L¹` -/

theorem one_add_norm_pos (ξ : E3) : 0 < 1 + ‖ξ‖ := by positivity

theorem rpow_mul_rpow {u : ℝ} (hu : 0 < u) (a b : ℝ) : u ^ a * u ^ b = u ^ (a + b) :=
  (Real.rpow_add hu a b).symm

theorem rpow_sq {u : ℝ} (hu : 0 < u) (a : ℝ) : (u ^ a) ^ 2 = u ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]; norm_num; ring_nf

theorem rpow_natc {u : ℝ} (hu : 0 < u) (n : ℕ) : u ^ (n : ℝ) = u ^ n := Real.rpow_natCast u n

/-- Funções com decaimento `w₈⁻¹`: `B² (1+‖ξ‖)^p ≤ C² w₄⁻¹` para `p ≤ 4`. -/
theorem sq_mul_rpow_le {B : E3 → ℝ} (hB0 : ∀ ξ, 0 ≤ B ξ) {C : ℝ} (hB : ∀ ξ, B ξ ≤ C * (w 8 ξ)⁻¹)
    {p : ℝ} (hp : p ≤ 4) (ξ : E3) : B ξ ^ 2 * (1 + ‖ξ‖) ^ p ≤ C ^ 2 * (w 4 ξ)⁻¹ := by
  have hu := one_add_norm_pos ξ
  have hu1 : 1 ≤ 1 + ‖ξ‖ := by have := norm_nonneg ξ; linarith
  have hC0 : 0 ≤ C := nonneg_of_mul_nonneg_left ((hB0 0).trans (hB 0)) (inv_pos.mpr (w_pos 8 0))
  have h1 : (1 + ‖ξ‖) ^ p ≤ w 4 ξ := by
    unfold w
    rw [← rpow_natc hu 4]
    exact Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num; linarith)
  have h8 : w 8 ξ = w 4 ξ * w 4 ξ := w_add 4 4 ξ
  have hw4 := w_pos 4 ξ
  have h2 : B ξ ^ 2 ≤ C ^ 2 * ((w 8 ξ)⁻¹) ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (hB0 ξ) (hB ξ) 2
  have h3 : ((w 8 ξ)⁻¹) ^ 2 * w 4 ξ ≤ (w 4 ξ)⁻¹ := by
    rw [h8, mul_inv, sq]
    have : (w 4 ξ)⁻¹ * (w 4 ξ)⁻¹ * ((w 4 ξ)⁻¹ * (w 4 ξ)⁻¹) * w 4 ξ =
        (w 4 ξ)⁻¹ * ((w 4 ξ)⁻¹ * (w 4 ξ)⁻¹) := by field_simp
    rw [this]
    have hle : (w 4 ξ)⁻¹ * (w 4 ξ)⁻¹ ≤ 1 := by
      have := inv_le_one_of_one_le₀ (one_le_w 4 ξ)
      nlinarith [inv_pos.mpr hw4]
    nlinarith [inv_pos.mpr hw4]
  calc B ξ ^ 2 * (1 + ‖ξ‖) ^ p ≤ C ^ 2 * ((w 8 ξ)⁻¹) ^ 2 * w 4 ξ :=
        mul_le_mul h2 h1 (Real.rpow_nonneg hu.le _) (by positivity)
    _ = C ^ 2 * (((w 8 ξ)⁻¹) ^ 2 * w 4 ξ) := by ring
    _ ≤ C ^ 2 * (w 4 ξ)⁻¹ := mul_le_mul_of_nonneg_left h3 (by positivity)

theorem integrable_sq_mul_rpow {B : E3 → ℝ} (hBc : Continuous B) (hB0 : ∀ ξ, 0 ≤ B ξ) {C : ℝ}
    (hB : ∀ ξ, B ξ ≤ C * (w 8 ξ)⁻¹) {p : ℝ} (hp : p ≤ 4) :
    Integrable fun ξ => B ξ ^ 2 * (1 + ‖ξ‖) ^ p := by
  refine integrable_of_le_w4 (fun ξ => mul_nonneg (sq_nonneg _)
    (Real.rpow_nonneg (one_add_norm_pos ξ).le _)) (sq_mul_rpow_le hB0 hB hp) ?_
  exact (Continuous.mul (hBc.pow 2) (Continuous.rpow_const (by fun_prop)
    (fun ξ => Or.inl (one_add_norm_pos ξ).ne'))).aestronglyMeasurable

/-- A constante `c = ∫ (1 + ‖ξ‖)^{−7/2}`. -/
noncomputable def c72 : ℝ := ∫ ξ : E3, (1 + ‖ξ‖) ^ (-(7 / 2 : ℝ))

theorem integrable_72 : Integrable fun ξ : E3 => (1 + ‖ξ‖) ^ (-(7 / 2 : ℝ)) := by
  refine integrable_one_add_norm ?_
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  norm_num

theorem c72_nonneg : 0 ≤ c72 :=
  integral_nonneg fun ξ => Real.rpow_nonneg (one_add_norm_pos ξ).le _

/-- **Interpolação `L¹`**: `(∫ B)⁸ ≤ c⁴ (∫ (1+‖ξ‖)² B²)(∫ (1+‖ξ‖)⁴ B²)³`. -/
theorem interp_L1 {B : E3 → ℝ} (hBc : Continuous B) (hB0 : ∀ ξ, 0 ≤ B ξ) {C : ℝ}
    (hB : ∀ ξ, B ξ ≤ C * (w 8 ξ)⁻¹) :
    (∫ ξ, B ξ) ^ 8 ≤ c72 ^ 4 * (∫ ξ, (1 + ‖ξ‖) ^ 2 * B ξ ^ 2) *
      (∫ ξ, (1 + ‖ξ‖) ^ 4 * B ξ ^ 2) ^ 3 := by
  have hu := one_add_norm_pos
  have cu : Continuous fun ξ : E3 => 1 + ‖ξ‖ := by fun_prop
  have cr : ∀ a : ℝ, Continuous fun ξ : E3 => (1 + ‖ξ‖) ^ a := fun a =>
    cu.rpow_const (fun ξ => Or.inl (hu ξ).ne')
  set I : ℝ → ℝ := fun p => ∫ ξ, B ξ ^ 2 * (1 + ‖ξ‖) ^ p with hI
  have hI0 : ∀ p, 0 ≤ I p := fun p => integral_nonneg fun ξ =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hu ξ).le _)
  have iI : ∀ p : ℝ, p ≤ 4 → Integrable fun ξ => B ξ ^ 2 * (1 + ‖ξ‖) ^ p :=
    fun p hp => integrable_sq_mul_rpow hBc hB0 hB hp
  -- passo 1: `(∫ B)² ≤ I(7/2) · c`
  have s1 : (∫ ξ, B ξ) ^ 2 ≤ I (7 / 2) * c72 := by
    have h := cs_sq (μ := volume) (f := fun ξ => B ξ * (1 + ‖ξ‖) ^ (7 / 4 : ℝ))
      (g := fun ξ => (1 + ‖ξ‖) ^ (-(7 / 4) : ℝ))
      (fun ξ => mul_nonneg (hB0 ξ) (Real.rpow_nonneg (hu ξ).le _))
      (fun ξ => Real.rpow_nonneg (hu ξ).le _) (hBc.mul (cr _)).aestronglyMeasurable
      (cr _).aestronglyMeasurable ?_ ?_
    · have e1 : ∀ ξ, B ξ * (1 + ‖ξ‖) ^ (7 / 4 : ℝ) * (1 + ‖ξ‖) ^ (-(7 / 4) : ℝ) = B ξ := by
        intro ξ; rw [mul_assoc, rpow_mul_rpow (hu ξ)]; norm_num
      have e2 : ∀ ξ, (B ξ * (1 + ‖ξ‖) ^ (7 / 4 : ℝ)) ^ 2 = B ξ ^ 2 * (1 + ‖ξ‖) ^ (7 / 2 : ℝ) := by
        intro ξ; rw [mul_pow, rpow_sq (hu ξ)]; norm_num
      have e3 : ∀ ξ : E3, ((1 + ‖ξ‖) ^ (-(7 / 4) : ℝ)) ^ 2 = (1 + ‖ξ‖) ^ (-(7 / 2 : ℝ)) := by
        intro ξ; rw [rpow_sq (hu ξ)]; norm_num
      simp_rw [e1, e2, e3] at h
      exact h
    · have e2 : ∀ ξ, (B ξ * (1 + ‖ξ‖) ^ (7 / 4 : ℝ)) ^ 2 = B ξ ^ 2 * (1 + ‖ξ‖) ^ (7 / 2 : ℝ) := by
        intro ξ; rw [mul_pow, rpow_sq (hu ξ)]; norm_num
      simp_rw [e2]; exact iI _ (by norm_num)
    · have e3 : ∀ ξ : E3, ((1 + ‖ξ‖) ^ (-(7 / 4) : ℝ)) ^ 2 = (1 + ‖ξ‖) ^ (-(7 / 2 : ℝ)) := by
        intro ξ; rw [rpow_sq (hu ξ)]; norm_num
      simp_rw [e3]; exact integrable_72
  -- passo 2: `I(7/2)² ≤ I 3 · I 4`
  have s2 : I (7 / 2) ^ 2 ≤ I 3 * I 4 := by
    have h := cs_sq (μ := volume) (f := fun ξ => B ξ * (1 + ‖ξ‖) ^ (3 / 2 : ℝ))
      (g := fun ξ => B ξ * (1 + ‖ξ‖) ^ (2 : ℝ))
      (fun ξ => mul_nonneg (hB0 ξ) (Real.rpow_nonneg (hu ξ).le _))
      (fun ξ => mul_nonneg (hB0 ξ) (Real.rpow_nonneg (hu ξ).le _))
      (hBc.mul (cr _)).aestronglyMeasurable (hBc.mul (cr _)).aestronglyMeasurable ?_ ?_
    · have e1 : ∀ ξ, B ξ * (1 + ‖ξ‖) ^ (3 / 2 : ℝ) * (B ξ * (1 + ‖ξ‖) ^ (2 : ℝ)) =
          B ξ ^ 2 * (1 + ‖ξ‖) ^ (7 / 2 : ℝ) := by
        intro ξ
        rw [show B ξ * (1 + ‖ξ‖) ^ (3 / 2 : ℝ) * (B ξ * (1 + ‖ξ‖) ^ (2 : ℝ)) =
          B ξ ^ 2 * ((1 + ‖ξ‖) ^ (3 / 2 : ℝ) * (1 + ‖ξ‖) ^ (2 : ℝ)) by ring,
          rpow_mul_rpow (hu ξ)]
        norm_num
      have e2 : ∀ ξ, (B ξ * (1 + ‖ξ‖) ^ (3 / 2 : ℝ)) ^ 2 = B ξ ^ 2 * (1 + ‖ξ‖) ^ (3 : ℝ) := by
        intro ξ; rw [mul_pow, rpow_sq (hu ξ)]; norm_num
      have e3 : ∀ ξ, (B ξ * (1 + ‖ξ‖) ^ (2 : ℝ)) ^ 2 = B ξ ^ 2 * (1 + ‖ξ‖) ^ (4 : ℝ) := by
        intro ξ; rw [mul_pow, rpow_sq (hu ξ)]; norm_num
      simp_rw [e1, e2, e3] at h
      exact h
    · have e2 : ∀ ξ, (B ξ * (1 + ‖ξ‖) ^ (3 / 2 : ℝ)) ^ 2 = B ξ ^ 2 * (1 + ‖ξ‖) ^ (3 : ℝ) := by
        intro ξ; rw [mul_pow, rpow_sq (hu ξ)]; norm_num
      simp_rw [e2]; exact iI _ (by norm_num)
    · have e3 : ∀ ξ, (B ξ * (1 + ‖ξ‖) ^ (2 : ℝ)) ^ 2 = B ξ ^ 2 * (1 + ‖ξ‖) ^ (4 : ℝ) := by
        intro ξ; rw [mul_pow, rpow_sq (hu ξ)]; norm_num
      simp_rw [e3]; exact iI _ (by norm_num)
  -- passo 3: `I 3² ≤ I 2 · I 4`
  have s3 : I 3 ^ 2 ≤ I 2 * I 4 := by
    have h := cs_sq (μ := volume) (f := fun ξ => B ξ * (1 + ‖ξ‖) ^ (1 : ℝ))
      (g := fun ξ => B ξ * (1 + ‖ξ‖) ^ (2 : ℝ))
      (fun ξ => mul_nonneg (hB0 ξ) (Real.rpow_nonneg (hu ξ).le _))
      (fun ξ => mul_nonneg (hB0 ξ) (Real.rpow_nonneg (hu ξ).le _))
      (hBc.mul (cr _)).aestronglyMeasurable (hBc.mul (cr _)).aestronglyMeasurable ?_ ?_
    · have e1 : ∀ ξ, B ξ * (1 + ‖ξ‖) ^ (1 : ℝ) * (B ξ * (1 + ‖ξ‖) ^ (2 : ℝ)) =
          B ξ ^ 2 * (1 + ‖ξ‖) ^ (3 : ℝ) := by
        intro ξ
        rw [show B ξ * (1 + ‖ξ‖) ^ (1 : ℝ) * (B ξ * (1 + ‖ξ‖) ^ (2 : ℝ)) =
          B ξ ^ 2 * ((1 + ‖ξ‖) ^ (1 : ℝ) * (1 + ‖ξ‖) ^ (2 : ℝ)) by ring,
          rpow_mul_rpow (hu ξ)]
        norm_num
      have e2 : ∀ ξ, (B ξ * (1 + ‖ξ‖) ^ (1 : ℝ)) ^ 2 = B ξ ^ 2 * (1 + ‖ξ‖) ^ (2 : ℝ) := by
        intro ξ; rw [mul_pow, rpow_sq (hu ξ)]; norm_num
      have e3 : ∀ ξ, (B ξ * (1 + ‖ξ‖) ^ (2 : ℝ)) ^ 2 = B ξ ^ 2 * (1 + ‖ξ‖) ^ (4 : ℝ) := by
        intro ξ; rw [mul_pow, rpow_sq (hu ξ)]; norm_num
      simp_rw [e1, e2, e3] at h
      exact h
    · have e2 : ∀ ξ, (B ξ * (1 + ‖ξ‖) ^ (1 : ℝ)) ^ 2 = B ξ ^ 2 * (1 + ‖ξ‖) ^ (2 : ℝ) := by
        intro ξ; rw [mul_pow, rpow_sq (hu ξ)]; norm_num
      simp_rw [e2]; exact iI _ (by norm_num)
    · have e3 : ∀ ξ, (B ξ * (1 + ‖ξ‖) ^ (2 : ℝ)) ^ 2 = B ξ ^ 2 * (1 + ‖ξ‖) ^ (4 : ℝ) := by
        intro ξ; rw [mul_pow, rpow_sq (hu ξ)]; norm_num
      simp_rw [e3]; exact iI _ (by norm_num)
  -- combinação
  have eI2 : I 2 = ∫ ξ, (1 + ‖ξ‖) ^ 2 * B ξ ^ 2 := by
    simp only [hI]; congr 1 with ξ; rw [mul_comm]; norm_cast
  have eI4 : I 4 = ∫ ξ, (1 + ‖ξ‖) ^ 4 * B ξ ^ 2 := by
    simp only [hI]; congr 1 with ξ; rw [mul_comm]; norm_cast
  rw [← eI2, ← eI4]
  have hc := c72_nonneg
  have h72 := hI0 (7 / 2)
  have h3 := hI0 3
  have h4 := hI0 4
  have h2 := hI0 2
  have t1 : (∫ ξ, B ξ) ^ 8 ≤ (I (7 / 2) * c72) ^ 4 := by
    have := pow_le_pow_left₀ (sq_nonneg _) s1 4
    rw [← pow_mul] at this
    exact this
  have t2 : I (7 / 2) ^ 4 ≤ (I 3 * I 4) ^ 2 := by
    have := pow_le_pow_left₀ (sq_nonneg _) s2 2
    rw [← pow_mul] at this
    exact this
  have t3 : (I 3 * I 4) ^ 2 ≤ I 2 * I 4 * I 4 ^ 2 := by
    rw [mul_pow]
    have := mul_le_mul_of_nonneg_right s3 (sq_nonneg (I 4))
    linarith
  calc (∫ ξ, B ξ) ^ 8 ≤ (I (7 / 2) * c72) ^ 4 := t1
    _ = I (7 / 2) ^ 4 * c72 ^ 4 := by ring
    _ ≤ (I 2 * I 4 * I 4 ^ 2) * c72 ^ 4 :=
        mul_le_mul_of_nonneg_right (t2.trans t3) (by positivity)
    _ = c72 ^ 4 * I 2 * I 4 ^ 3 := by ring

/-! ### Absorção (Young por casos) -/

/-- `T^{n+1} ≤ K Yⁿ Z ⇒ T ≤ ε Y + K Z / εⁿ`. -/
theorem absorve {T Y Z K ε : ℝ} (n : ℕ) (hT : 0 ≤ T) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hK : 0 ≤ K)
    (hε : 0 < ε) (h : T ^ (n + 1) ≤ K * Y ^ n * Z) : T ≤ ε * Y + K * Z / ε ^ n := by
  by_cases hc : T ≤ ε * Y
  · have : 0 ≤ K * Z / ε ^ n := by positivity
    linarith
  push_neg at hc
  have hTpos : 0 < T := lt_of_le_of_lt (by positivity) hc
  have hYle : Y ≤ T / ε := by rw [le_div_iff₀ hε]; linarith
  have h1 : T ^ (n + 1) ≤ K * (T / ε) ^ n * Z := by
    calc T ^ (n + 1) ≤ K * Y ^ n * Z := h
      _ ≤ K * (T / ε) ^ n * Z := by gcongr
  have h2 : T ^ n * T ≤ T ^ n * (K * Z / ε ^ n) := by
    rw [← pow_succ]
    calc T ^ (n + 1) ≤ K * (T / ε) ^ n * Z := h1
      _ = T ^ n * (K * Z / ε ^ n) := by rw [div_pow]; field_simp
  have := le_of_mul_le_mul_left h2 (pow_pos hTpos n)
  have : 0 ≤ ε * Y := by positivity
  linarith

end ATK.NSEstimativas

#print axioms ATK.NSEstimativas.cs_sq
#print axioms ATK.NSEstimativas.Mansa.integrable
#print axioms ATK.NSEstimativas.Mansa.le_const
#print axioms ATK.NSEstimativas.Mansa.integrable_sq
#print axioms ATK.NSEstimativas.Mansa.sqrt
#print axioms ATK.NSEstimativas.tri_le
#print axioms ATK.NSEstimativas.tri_leZ
#print axioms ATK.NSEstimativas.one_add_norm_pos
#print axioms ATK.NSEstimativas.rpow_mul_rpow
#print axioms ATK.NSEstimativas.rpow_sq
#print axioms ATK.NSEstimativas.rpow_natc
#print axioms ATK.NSEstimativas.sq_mul_rpow_le
#print axioms ATK.NSEstimativas.integrable_sq_mul_rpow
#print axioms ATK.NSEstimativas.integrable_72
#print axioms ATK.NSEstimativas.c72_nonneg
#print axioms ATK.NSEstimativas.interp_L1
#print axioms ATK.NSEstimativas.absorve
