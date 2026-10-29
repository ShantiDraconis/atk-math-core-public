import ATK.NSAltaOrdem

/-!
# ATK — Navier–Stokes: cota uniforme a partir da enstrofia (para a continuação)

Camada 14 do ataque a B3. Ao longo da solução branda `â` em `[0, T]`, se `J₁(â(s)) ≤ M₁`
(energia + enstrofia limitadas), então, com constantes que só dependem de `ν`, de uma cota
superior `T_b ≥ T`, de `M₁` e do dado `â(0)`:

* `int_J2_le`: `2π²ν ∫₀ᵗ J₂ ≤ J₁(0) + t C₁` (estimativa `H¹`, com `T₁ ≤ ε J₂ + C J₁⁵`);
* `J2_le`: `J₂(t) ≤ M₂` (Gronwall com coeficiente integrável `C + K₂' J₂`);
* `J3_le`: `J₃(t) ≤ M₃` (Gronwall linear);
* **`cota_uniforme`**: `‖â(t, ξ)‖ ≤ M w₄(ξ)⁻¹` em `[0, T]` (Duhamel com o ganho de duas derivadas
  do calor e `w₂ ‖N‖ ≤ 16π J₃`).

**CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology
open scoped Real

namespace ATK.NSCotaUniforme

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSPicard ATK.NSMild ATK.NSSuave ATK.NSTempo
  ATK.NSSimetria ATK.NSFisico ATK.NSEnergia ATK.NSEstimativas ATK.NSAltaOrdem

/-! ### Monotonia e Cauchy–Schwarz para convoluções -/

theorem J_mono {f : E3 → C3} (hR : Rapida fun ξ => ‖f ξ‖) (k : ℕ) : J k f ≤ J (k + 1) f := by
  rw [← integral_wA_sq, ← integral_wA_sq]
  refine integral_mono (hR.mul_w k).mansa.integrable_sq (hR.mul_w (k + 1)).mansa.integrable_sq
    fun ξ => ?_
  exact pow_le_pow_left₀ ((hR.mul_w k).nonneg ξ)
    (mul_le_mul_of_nonneg_right (w_mono (Nat.le_succ k) ξ) (norm_nonneg _)) 2

theorem J_mono_le {f : E3 → C3} (hR : Rapida fun ξ => ‖f ξ‖) {k n : ℕ} (h : k ≤ n) :
    J k f ≤ J n f := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (J_mono hR _)

/-- `(Y ⋆ Z)(ξ) ≤ (‖Y‖₂² + ‖Z‖₂²)/2`. -/
theorem cv_le_half {Y Z : E3 → ℝ} (hY : Rapida Y) (hZ : Rapida Z) (ξ : E3) :
    cv Y Z ξ ≤ ((∫ η, Y η ^ 2) + ∫ ζ, Z ζ ^ 2) / 2 := by
  have hZ2 : Integrable fun η => Z (ξ - η) ^ 2 := hZ.mansa.integrable_sq.comp_sub_left ξ
  have h := cs_sq (μ := volume) (f := Y) (g := fun η => Z (ξ - η)) hY.nonneg
    (fun η => hZ.nonneg _) hY.cont.aestronglyMeasurable
    (hZ.cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    hY.mansa.integrable_sq hZ2
  have e : ∫ η, Z (ξ - η) ^ 2 = ∫ ζ, Z ζ ^ 2 :=
    integral_sub_left_eq_self (fun ζ => Z ζ ^ 2) volume ξ
  rw [e] at h
  have hcv0 : 0 ≤ cv Y Z ξ := (hY.cv hZ).nonneg ξ
  have hX : 0 ≤ ∫ η, Y η ^ 2 := integral_nonneg fun η => sq_nonneg (Y η)
  have hW : 0 ≤ ∫ ζ, Z ζ ^ 2 := integral_nonneg fun ζ => sq_nonneg (Z ζ)
  have h2 : cv Y Z ξ ^ 2 ≤ (((∫ η, Y η ^ 2) + ∫ ζ, Z ζ ^ 2) / 2) ^ 2 := by
    refine (show cv Y Z ξ ^ 2 ≤ (∫ η, Y η ^ 2) * ∫ ζ, Z ζ ^ 2 from h).trans ?_
    nlinarith [sq_nonneg ((∫ η, Y η ^ 2) - ∫ ζ, Z ζ ^ 2)]
  exact (pow_le_pow_iff_left₀ hcv0 (by positivity) two_ne_zero).mp h2

/-- `w₂(ξ) ‖N(f, f)(ξ)‖ ≤ 16π J₃(f)`. -/
theorem w2_norm_Nl_le {f : E3 → C3} (hd : ∀ ξ, inner ℂ (cpx ξ) (f ξ) = 0)
    (hR : Rapida fun ξ => ‖f ξ‖) (ξ : E3) : w 2 ξ * ‖Nl f f ξ‖ ≤ 16 * π * J 3 f := by
  have hRP : Rapida fun ζ => ‖ζ‖ * ‖f ζ‖ := hR.norm_mul
  have hN := norm_Nl_le_cv hd hR ξ
  have hW := w_mul_cv_le hR hRP 2 ξ
  have c1 := cv_le_half (hR.mul_w 2) hRP ξ
  have c2 := cv_le_half hR (hRP.mul_w 2) ξ
  rw [integral_wA_sq] at c1
  have hP1 := integral_P_sq_le hR
  have hP3 := integral_wP_sq_le hR 2
  have hA0 : ∫ η, ‖f η‖ ^ 2 = J 0 f := by
    rw [← integral_wA_sq]; congr 1 with η; rw [w_zero, one_mul]
  rw [hA0] at c2
  have m01 := J_mono_le hR (show 0 ≤ 3 by norm_num)
  have m11 := J_mono_le hR (show 1 ≤ 3 by norm_num)
  have m21 := J_mono_le hR (show 2 ≤ 3 by norm_num)
  have hw := w_pos 2 ξ
  calc w 2 ξ * ‖Nl f f ξ‖ ≤ w 2 ξ * (2 * π * cv (fun η => ‖f η‖) (fun ζ => ‖ζ‖ * ‖f ζ‖) ξ) :=
        mul_le_mul_of_nonneg_left hN hw.le
    _ = 2 * π * (w 2 ξ * cv (fun η => ‖f η‖) (fun ζ => ‖ζ‖ * ‖f ζ‖) ξ) := by ring
    _ ≤ 2 * π * (2 ^ 2 * (cv (fun η => w 2 η * ‖f η‖) (fun ζ => ‖ζ‖ * ‖f ζ‖) ξ +
          cv (fun η => ‖f η‖) (fun ζ => w 2 ζ * (‖ζ‖ * ‖f ζ‖)) ξ)) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
    _ ≤ 2 * π * (2 ^ 2 * (J 3 f + J 3 f)) := by
        have h1 : cv (fun η => w 2 η * ‖f η‖) (fun ζ => ‖ζ‖ * ‖f ζ‖) ξ ≤ J 3 f := by
          refine c1.trans ?_; linarith
        have h2 : cv (fun η => ‖f η‖) (fun ζ => w 2 ζ * (‖ζ‖ * ‖f ζ‖)) ξ ≤ J 3 f := by
          refine c2.trans ?_; linarith
        have := Real.pi_pos
        gcongr
    _ = 16 * π * J 3 f := by ring

/-! ### O calor -/

/-- `w₂(ξ) ∫₀ᵗ e^{−4π²ν‖ξ‖²(t−s)} ds ≤ 2t + 1/(2π²ν)`. -/
theorem w2_int_heat_le {ν : ℝ} (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) (ξ : E3) :
    w 2 ξ * ∫ s in (0 : ℝ)..t, heat ν (t - s) ξ ≤ 2 * t + 1 / (2 * π ^ 2 * ν) := by
  have hc : Continuous fun s => heat ν (t - s) ξ := by
    have := continuous_heat ν
    unfold heat; fun_prop
  set I := ∫ s in (0 : ℝ)..t, heat ν (t - s) ξ with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg ht fun s _ => (heat_pos _ _ _).le
  have hIt : I ≤ t := by
    have : I ≤ ∫ s in (0 : ℝ)..t, (1 : ℝ) :=
      intervalIntegral.integral_mono_on ht (hc.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _) fun s hs =>
          heat_le_one hν.le (by linarith [hs.2]) ξ
    simpa using this
  -- `κ I = 1 − e^{−κ t} ≤ 1`
  have hkI : kappa ν ξ * I ≤ 1 := by
    have hd : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => heat ν (t - r) ξ)
        (kappa ν ξ * heat ν (t - s) ξ) s := by
      intro s _
      have h : HasDerivAt (fun r => heat ν (t - r) ξ) (-kappa ν ξ * heat ν (t - s) ξ * -1) s :=
        (hasDerivAt_heat ν ξ (t - s)).comp s ((hasDerivAt_id s).const_sub t)
      convert h using 1
      ring
    have hfun := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hc.continuousOn hd
      ((continuous_const.mul hc).intervalIntegrable _ _)
    rw [intervalIntegral.integral_const_mul] at hfun
    beta_reduce at hfun
    have h0 : heat ν (t - t) ξ = 1 := by rw [sub_self, heat_zero]
    have := heat_pos ν (t - 0) ξ
    rw [h0] at hfun
    rw [hI, hfun]
    linarith
  have hk : kappa ν ξ = 4 * π ^ 2 * ν * ‖ξ‖ ^ 2 := rfl
  have hw2 : w 2 ξ ≤ 2 + 2 * ‖ξ‖ ^ 2 := by
    unfold w; nlinarith [sq_nonneg (1 - ‖ξ‖), norm_nonneg ξ]
  have hpi : 0 < π ^ 2 * ν := by positivity
  have hr : ‖ξ‖ ^ 2 * I ≤ 1 / (4 * π ^ 2 * ν) := by
    rw [le_div_iff₀ (by positivity)]
    rw [hk] at hkI
    linarith
  calc w 2 ξ * I ≤ (2 + 2 * ‖ξ‖ ^ 2) * I := mul_le_mul_of_nonneg_right hw2 hI0
    _ = 2 * I + 2 * (‖ξ‖ ^ 2 * I) := by ring
    _ ≤ 2 * t + 2 * (1 / (4 * π ^ 2 * ν)) := by gcongr
    _ = 2 * t + 1 / (2 * π ^ 2 * ν) := by field_simp; ring

/-! ### Evolução das normas -/

section

variable {ν T : ℝ} {a : ℝ → E3 → C3}

/-- Constante da estimativa `H¹`. -/
noncomputable def C1 (ν M1 : ℝ) : ℝ := 8 * π ^ 2 * ν * M1 + K1 ν * M1 ^ 5

/-- **Estimativa `H¹`**: `2π²ν ∫₀ᵗ J₂ ≤ J₁(0) + t C₁`. -/
theorem int_J2_le (hν : 0 < ν) (ha : BoaW a) (hdivF : ∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a 0 ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    {M1 : ℝ} (hM1 : ∀ s ∈ Icc 0 T, J 1 (a s) ≤ M1) {t : ℝ} (ht : t ∈ Icc 0 T) :
    2 * π ^ 2 * ν * ∫ s in (0 : ℝ)..t, J 2 (a s) ≤ J 1 (a 0) + t * C1 ν M1 := by
  have hJ := J_sub_eq ha hmild 1 ht
  have hDb : ∀ s ∈ Icc 0 t, D ν a 1 s ≤ -(2 * π ^ 2 * ν) * J 2 (a s) + C1 ν M1 := by
    intro s hs
    have hs' : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    have h1 := D_le hν.le ha hdivF 1 s
    have h2 := T1_le (hdivF s) (BoaW.rapida ha s) hν
    have hJ1 := J_nonneg 1 (a s)
    have hM := hM1 s hs'
    have h5 : J 1 (a s) ^ 5 ≤ M1 ^ 5 := pow_le_pow_left₀ hJ1 hM 5
    have hK := K1_nonneg hν
    unfold C1
    have : K1 ν * J 1 (a s) ^ 5 ≤ K1 ν * M1 ^ 5 := mul_le_mul_of_nonneg_left h5 hK
    have : 8 * π ^ 2 * ν * J 1 (a s) ≤ 8 * π ^ 2 * ν * M1 :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    show D ν a 1 s ≤ _
    simp only [show (1 : ℕ) + 1 = 2 from rfl] at h1
    linarith
  have hcD := continuous_D (ν := ν) ha 1
  have hcJ := continuous_J ha 2
  have hint : ∫ s in (0 : ℝ)..t, D ν a 1 s ≤
      ∫ s in (0 : ℝ)..t, (-(2 * π ^ 2 * ν) * J 2 (a s) + C1 ν M1) :=
    intervalIntegral.integral_mono_on ht.1 (hcD.intervalIntegrable _ _)
      ((continuous_const.mul hcJ).add continuous_const |>.intervalIntegrable _ _) hDb
  rw [intervalIntegral.integral_add (f := fun s => -(2 * π ^ 2 * ν) * J 2 (a s))
    (g := fun _ => C1 ν M1) ((continuous_const.mul hcJ).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hint
  have hJt := J_nonneg 1 (a t)
  simp only [sub_zero, smul_eq_mul] at hint
  linarith

/-- O expoente de `M₂`. -/
noncomputable def E2 (ν Tb M1 j10 : ℝ) : ℝ :=
  Tb * (8 * π ^ 2 * ν + K2 ν * M1 ^ 4) + K2b ν * ((j10 + Tb * C1 ν M1) / (2 * π ^ 2 * ν))

/-- **`J₂` limitado**. -/
theorem J2_le (hν : 0 < ν) (ha : BoaW a) (hdivF : ∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a 0 ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    {M1 : ℝ} (hM10 : 0 ≤ M1) (hM1 : ∀ s ∈ Icc 0 T, J 1 (a s) ≤ M1) {Tb : ℝ} (hTb : T ≤ Tb)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    J 2 (a t) ≤ J 2 (a 0) * Real.exp (E2 ν Tb M1 (J 1 (a 0))) := by
  set g : ℝ → ℝ := fun s => 8 * π ^ 2 * ν + K2 ν * M1 ^ 4 + K2b ν * J 2 (a s) with hg
  have hcJ := continuous_J ha 2
  have hgc : Continuous g := continuous_const.add (continuous_const.mul hcJ)
  have hφ : ∀ r ∈ Icc 0 T, J 2 (a r) = J 2 (a 0) + ∫ s in (0 : ℝ)..r, D ν a 2 s := by
    intro r hr; have := J_sub_eq ha hmild 2 hr; linarith
  have hDg : ∀ s ∈ Icc 0 T, D ν a 2 s ≤ g s * J 2 (a s) := by
    intro s hs
    have h1 := D_le hν.le ha hdivF 2 s
    have h2 := T2_le (hdivF s) (BoaW.rapida ha s) hν
    have hJ1 := J_nonneg 1 (a s)
    have hJ2 := J_nonneg 2 (a s)
    have h4 : J 1 (a s) ^ 4 ≤ M1 ^ 4 := pow_le_pow_left₀ hJ1 (hM1 s hs) 4
    have hK := K2_nonneg hν
    have : K2 ν * J 1 (a s) ^ 4 * J 2 (a s) ≤ K2 ν * M1 ^ 4 * J 2 (a s) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hK) hJ2
    simp only [hg]
    simp only [show (2 : ℕ) + 1 = 3 from rfl] at h1
    nlinarith
  have hgr := gronwall hφ (continuous_D (ν := ν) ha 2) hgc hDg ht
  refine hgr.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (J_nonneg 2 (a 0)))
  -- `∫₀ᵗ g ≤ E₂`
  have hint := int_J2_le hν ha hdivF hmild hM1 ht
  rw [hg]
  beta_reduce
  rw [intervalIntegral.integral_add (f := fun _ => 8 * π ^ 2 * ν + K2 ν * M1 ^ 4)
    (g := fun s => K2b ν * J 2 (a s)) (continuous_const.intervalIntegrable _ _)
    ((continuous_const.mul hcJ).intervalIntegrable _ _), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul]
  simp only [sub_zero, smul_eq_mul]
  have hK2 := K2_nonneg hν
  have hK2' := K2b_nonneg hν
  have hpi : 0 < 2 * π ^ 2 * ν := by positivity
  have hC1 : 0 ≤ C1 ν M1 := by have := K1_nonneg hν; unfold C1; positivity
  have hJ2int : ∫ s in (0 : ℝ)..t, J 2 (a s) ≤ (J 1 (a 0) + Tb * C1 ν M1) / (2 * π ^ 2 * ν) := by
    rw [le_div_iff₀ hpi]
    have : t * C1 ν M1 ≤ Tb * C1 ν M1 :=
      mul_le_mul_of_nonneg_right (ht.2.trans hTb) hC1
    linarith
  unfold E2
  have h1 : t * (8 * π ^ 2 * ν + K2 ν * M1 ^ 4) ≤ Tb * (8 * π ^ 2 * ν + K2 ν * M1 ^ 4) :=
    mul_le_mul_of_nonneg_right (ht.2.trans hTb) (by positivity)
  have h2 := mul_le_mul_of_nonneg_left hJ2int hK2'
  linarith

/-- **`J₃` limitado**. -/
theorem J3_le (hν : 0 < ν) (ha : BoaW a) (hdivF : ∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a 0 ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    {M2 : ℝ} (hM20 : 0 ≤ M2) (hM2 : ∀ s ∈ Icc 0 T, J 2 (a s) ≤ M2) {Tb : ℝ} (hTb : T ≤ Tb)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    J 3 (a t) ≤ J 3 (a 0) * Real.exp (Tb * (8 * π ^ 2 * ν + K3 ν * M2)) := by
  have hφ : ∀ r ∈ Icc 0 T, J 3 (a r) = J 3 (a 0) + ∫ s in (0 : ℝ)..r, D ν a 3 s := by
    intro r hr; have := J_sub_eq ha hmild 3 hr; linarith
  have hDg : ∀ s ∈ Icc 0 T, D ν a 3 s ≤ (8 * π ^ 2 * ν + K3 ν * M2) * J 3 (a s) := by
    intro s hs
    have h1 := D_le hν.le ha hdivF 3 s
    have h2 := T3_le (hdivF s) (BoaW.rapida ha s) hν
    have hJ3 := J_nonneg 3 (a s)
    have hK := K3_nonneg hν
    have : K3 ν * J 2 (a s) * J 3 (a s) ≤ K3 ν * M2 * J 3 (a s) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM2 s hs) hK) hJ3
    simp only [show (3 : ℕ) + 1 = 4 from rfl] at h1
    nlinarith
  have hgr := gronwall hφ (continuous_D (ν := ν) ha 3) continuous_const hDg ht
  refine hgr.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (J_nonneg 3 (a 0)))
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  have := K3_nonneg hν
  exact mul_le_mul_of_nonneg_right (ht.2.trans hTb) (by positivity)

/-- `‖â(t, ξ)‖ ≤ ‖â(0, ξ)‖ + ∫₀ᵗ e^{−κ(t−s)} ‖N(â(s), â(s))(ξ)‖ ds`. -/
theorem norm_le_duhamel (hν : 0 < ν) (ha : BoaW a)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a 0 ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    {t : ℝ} (ht : t ∈ Icc 0 T) (ξ : E3) :
    ‖a t ξ‖ ≤ ‖a 0 ξ‖ + ∫ s in (0 : ℝ)..t, heat ν (t - s) ξ * ‖Nl (a s) (a s) ξ‖ := by
  have hN := ha.nl ha
  have hcN : Continuous fun s => ‖Nl (a s) (a s) ξ‖ := (hN.cont_t ξ).norm
  have hch : Continuous fun s => heat ν (t - s) ξ := by
    have := continuous_heat ν
    unfold heat; fun_prop
  have hcd : Continuous fun s => duhI ν a a t s ξ := by
    unfold duhI
    have := (ha.lpNl ha).cont_t ξ
    exact hch.smul this
  rw [hmild t ht ξ]
  calc ‖heat ν t ξ • a 0 ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ‖
      ≤ ‖heat ν t ξ • a 0 ξ‖ + ‖∫ s in (0 : ℝ)..t, duhI ν a a t s ξ‖ := norm_sub_le _ _
    _ ≤ ‖a 0 ξ‖ + ∫ s in (0 : ℝ)..t, ‖duhI ν a a t s ξ‖ := by
        gcongr
        · rw [norm_smul, Real.norm_of_nonneg (heat_pos _ _ _).le]
          exact mul_le_of_le_one_left (norm_nonneg _) (heat_le_one hν.le ht.1 ξ)
        · exact intervalIntegral.norm_integral_le_integral_norm ht.1
    _ ≤ ‖a 0 ξ‖ + ∫ s in (0 : ℝ)..t, heat ν (t - s) ξ * ‖Nl (a s) (a s) ξ‖ := by
        gcongr
        refine intervalIntegral.integral_mono_on ht.1 (hcd.norm.intervalIntegrable _ _)
          ((hch.mul hcN).intervalIntegrable _ _) fun s _ => ?_
        unfold duhI
        rw [norm_smul, Real.norm_of_nonneg (heat_pos _ _ _).le]
        exact mul_le_mul_of_nonneg_left (norm_lp_le _ _) (heat_pos _ _ _).le

/-- A constante final. -/
noncomputable def Mfin (ν Tb M0 M3 : ℝ) : ℝ := M0 + 16 * π * M3 * (2 * Tb + 1 / (2 * π ^ 2 * ν))

/-- **Cota uniforme**: se `J₃ ≤ M₃` em `[0, T]` e `‖â(0)‖ ≤ M₀ w₄⁻¹`, então
`‖â(t, ξ)‖ ≤ (M₀ + 16π M₃ (2T_b + 1/(2π²ν))) w₄(ξ)⁻¹` em `[0, T]`. -/
theorem cota_de_J3 (hν : 0 < ν) (ha : BoaW a) (hdivF : ∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a 0 ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    {M0 M3 : ℝ} (hM0 : ∀ ξ, ‖a 0 ξ‖ ≤ M0 * (w 4 ξ)⁻¹) (hM30 : 0 ≤ M3)
    (hM3 : ∀ s ∈ Icc 0 T, J 3 (a s) ≤ M3) {Tb : ℝ} (hTb : T ≤ Tb)
    {t : ℝ} (ht : t ∈ Icc 0 T) (ξ : E3) :
    ‖a t ξ‖ ≤ Mfin ν Tb M0 M3 * (w 4 ξ)⁻¹ := by
  have hd := norm_le_duhamel hν ha hmild ht ξ
  have hw2 := w_pos 2 ξ
  have hpt : ∀ s ∈ Icc 0 t, heat ν (t - s) ξ * ‖Nl (a s) (a s) ξ‖ ≤
      heat ν (t - s) ξ * (16 * π * M3 * (w 2 ξ)⁻¹) := by
    intro s hs
    have hs' : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    have h := w2_norm_Nl_le (hdivF s) (BoaW.rapida ha s) ξ
    have h' : ‖Nl (a s) (a s) ξ‖ ≤ 16 * π * M3 * (w 2 ξ)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hw2]
      have := hM3 s hs'
      have : 16 * π * J 3 (a s) ≤ 16 * π * M3 := by
        have := Real.pi_pos; gcongr
      linarith
    exact mul_le_mul_of_nonneg_left h' (heat_pos _ _ _).le
  have hch : Continuous fun s => heat ν (t - s) ξ := by
    have := continuous_heat ν
    unfold heat; fun_prop
  have hcN : Continuous fun s => ‖Nl (a s) (a s) ξ‖ := ((ha.nl ha).cont_t ξ).norm
  have hint : ∫ s in (0 : ℝ)..t, heat ν (t - s) ξ * ‖Nl (a s) (a s) ξ‖ ≤
      ∫ s in (0 : ℝ)..t, heat ν (t - s) ξ * (16 * π * M3 * (w 2 ξ)⁻¹) :=
    intervalIntegral.integral_mono_on ht.1
    ((hch.mul hcN).intervalIntegrable (μ := volume) _ _)
    ((hch.mul (continuous_const : Continuous fun _ : ℝ => 16 * π * M3 * (w 2 ξ)⁻¹)).intervalIntegrable
      (μ := volume) _ _) hpt
  rw [intervalIntegral.integral_mul_const] at hint
  have hheat := w2_int_heat_le hν ht.1 ξ
  set I := ∫ s in (0 : ℝ)..t, heat ν (t - s) ξ with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg ht.1 fun s _ => (heat_pos _ _ _).le
  have hIle : I ≤ (2 * Tb + 1 / (2 * π ^ 2 * ν)) * (w 2 ξ)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hw2]
    have : 2 * t + 1 / (2 * π ^ 2 * ν) ≤ 2 * Tb + 1 / (2 * π ^ 2 * ν) := by
      have := ht.2.trans hTb; linarith
    linarith
  have hw4 : (w 2 ξ)⁻¹ * (w 2 ξ)⁻¹ = (w 4 ξ)⁻¹ := by
    rw [← mul_inv, ← w_add]
  unfold Mfin
  have hpi := Real.pi_pos
  calc ‖a t ξ‖ ≤ ‖a 0 ξ‖ + I * (16 * π * M3 * (w 2 ξ)⁻¹) := hd.trans (by linarith)
    _ ≤ M0 * (w 4 ξ)⁻¹ + (2 * Tb + 1 / (2 * π ^ 2 * ν)) * (w 2 ξ)⁻¹ *
          (16 * π * M3 * (w 2 ξ)⁻¹) := by
        gcongr
        · exact hM0 ξ
    _ = (M0 + 16 * π * M3 * (2 * Tb + 1 / (2 * π ^ 2 * ν))) * (w 4 ξ)⁻¹ := by
        rw [← hw4]; ring

end

end ATK.NSCotaUniforme

#print axioms ATK.NSCotaUniforme.J_mono
#print axioms ATK.NSCotaUniforme.J_mono_le
#print axioms ATK.NSCotaUniforme.cv_le_half
#print axioms ATK.NSCotaUniforme.w2_norm_Nl_le
#print axioms ATK.NSCotaUniforme.w2_int_heat_le
#print axioms ATK.NSCotaUniforme.int_J2_le
#print axioms ATK.NSCotaUniforme.J2_le
#print axioms ATK.NSCotaUniforme.J3_le
#print axioms ATK.NSCotaUniforme.norm_le_duhamel
#print axioms ATK.NSCotaUniforme.cota_de_J3
