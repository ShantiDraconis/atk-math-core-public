import ATK.NSFraca

/-!
# ATK — Navier–Stokes, marco NS8b: campos teste de Fourier e a função de corte

Ponte B3, marco NS8 (segunda parte). Ferramentas para a unicidade:

* `F0 g x = ∫ e^{2πi⟨ξ,x⟩} g(ξ) dξ` para `g` contínua com todos os pesos (`Pesos g`): é `C^∞`,
  `∂_j F0 g = F0 (2πi ξ_j g)`, `|F0 g| ≤ ∫ |g|` e `∫ |F0 g|² = ∫ |g|²` (Plancherel);
* `R0 g = Re F0 g` (campo real; igual a `F0 g` se `g` é hermitiana);
* o corte `κ_R(x) = κ(x/R)`: suave, de suporte compacto, `κ_R → 1`, `∂κ_R, ∂²κ_R → 0`.

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta**; **CLOSED_MATH continua
false**.
-/

set_option autoImplicit false

open MeasureTheory Real Set Filter Topology
open scoped ContDiff
open ATK.LigacaoNS (E3 dX e div)
open ATK.NSFourierBase ATK.NSPicard ATK.NSRegular ATK.NSFisico ATK.NSCampos ATK.NSEquacao
  ATK.NSPlancherel ATK.NSFraca

namespace ATK.NSTeste

/-! ### Funções com todos os pesos -/

/-- `g` contínua com todas as cotas `|g(ξ)|(1+|ξ|)^m ≤ C_m`. -/
def Pesos (g : E3 → C3) : Prop := Continuous g ∧ ∀ m : ℕ, ∃ C, Cota m C g

theorem pesos_of_compact {g : E3 → C3} (hg : Continuous g) (hs : HasCompactSupport g) :
    Pesos g := by
  refine ⟨hg, fun m => ?_⟩
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuous hg
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  refine ⟨max B 0 * (1 + max R 0) ^ m, fun ξ => ?_⟩
  by_cases hξ : ξ ∈ tsupport g
  · have h1 : ‖ξ‖ ≤ max R 0 := by
      have := hR hξ
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    have h2 : ‖g ξ‖ ≤ max B 0 := (hB ξ).trans (le_max_left _ _)
    gcongr
  · rw [image_eq_zero_of_notMem_tsupport hξ, norm_zero, zero_mul]
    positivity

/-- O campo constante no tempo. -/
def Vt (g : E3 → C3) : E3 × ℝ → C3 := fun q => g q.1

theorem reg0_Vt {g : E3 → C3} (hg : Pesos g) (T : ℝ) : Reg0 T (Vt g) :=
  ⟨fun _ _ => hg.1, fun m => by
    obtain ⟨C, hC⟩ := hg.2 m
    exact ⟨C, fun _ _ => hC⟩⟩

theorem reg0_zero (T : ℝ) : Reg0 T (fun _ : E3 × ℝ => (0 : C3)) :=
  ⟨fun _ _ => continuous_const, fun _ => ⟨0, fun _ _ ζ => by simp⟩⟩

theorem suave_zero (T : ℝ) : ∀ k, Suave T k (fun _ : E3 × ℝ => (0 : C3))
  | 0 => reg0_zero T
  | k + 1 => ⟨reg0_zero T, fun _ => 0, suave_zero T k, fun _ _ _ => hasDerivWithinAt_const _ _ _⟩

theorem suave_Vt {g : E3 → C3} (hg : Pesos g) (T : ℝ) : ∀ k, Suave T k (Vt g)
  | 0 => reg0_Vt hg T
  | k + 1 => ⟨reg0_Vt hg T, fun _ => 0, suave_zero T k, fun ξ t _ => by
      show HasDerivWithinAt (fun _ => g ξ) 0 _ _
      exact hasDerivWithinAt_const _ _ _⟩

/-! ### A integral de Fourier sem tempo -/

/-- `F0 g x = ∫ e^{2πi⟨ξ,x⟩} g(ξ) dξ`. -/
noncomputable def F0 (g : E3 → C3) (x : E3) : C3 := ∫ ξ, ex ξ x • g ξ

theorem F0_eq_Fi (g : E3 → C3) (x : E3) (t : ℝ) : F0 g x = Fi (Vt g) (x, t) := rfl

theorem contDiff_F0 {g : E3 → C3} (hg : Pesos g) : ContDiff ℝ ∞ (F0 g) := by
  have h := contDiffOn_Φ_top (T := 1) one_pos aesm_idL zero_le_one idL_bound (suave_Vt hg 1)
  have h2 := h.comp_contDiff (contDiff_id.prodMk contDiff_const) (f := fun x : E3 => (x, (0 : ℝ)))
    (fun x => ⟨mem_univ _, le_rfl, zero_le_one⟩)
  exact h2

theorem pesos_mj {g : E3 → C3} (hg : Pesos g) (j : Fin 3) :
    Pesos (fun ξ => mj j ξ • g ξ) := by
  refine ⟨(continuous_mj j).smul hg.1, fun m => ?_⟩
  obtain ⟨C, hC⟩ := hg.2 (m + 1)
  refine ⟨2 * π * C, fun ξ => ?_⟩
  have h1 := norm_mj_le j ξ
  have h2 := hC ξ
  rw [norm_smul]
  calc ‖mj j ξ‖ * ‖g ξ‖ * (1 + ‖ξ‖) ^ m ≤ 2 * π * (1 + ‖ξ‖) ^ 1 * ‖g ξ‖ * (1 + ‖ξ‖) ^ m := by
        gcongr
    _ = 2 * π * (‖g ξ‖ * (1 + ‖ξ‖) ^ (m + 1)) := by ring
    _ ≤ 2 * π * C := by gcongr

theorem dX_F0 {g : E3 → C3} (hg : Pesos g) (j : Fin 3) (x : E3) :
    dX j (F0 g) x = F0 (fun ξ => mj j ξ • g ξ) x := by
  have h := dX_Fi (T := 1) (reg0_Vt hg 1) (reg0_zero 1)
    (fun ξ _ _ => by
      show HasDerivWithinAt (fun _ => g ξ) 0 _ _
      exact hasDerivWithinAt_const _ _ _) j x ⟨le_rfl, zero_le_one⟩
  exact h

theorem integrable_pesos {g : E3 → C3} (hg : Pesos g) : Integrable g := by
  obtain ⟨C, hC⟩ := hg.2 4
  refine ((integrable_inv_pow (le_refl 4)).const_mul C).mono' hg.1.aestronglyMeasurable
    (Eventually.of_forall fun ξ => hC.le_inv ξ)

theorem norm_F0_le (g : E3 → C3) (x : E3) : ‖F0 g x‖ ≤ ∫ ξ, ‖g ξ‖ := by
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  congr 1
  funext ξ
  rw [norm_smul, norm_ex, one_mul]

theorem plancherel_F0 {g : E3 → C3} (hg : Pesos g) :
    Integrable (fun x => ‖F0 g x‖ ^ 2) ∧ ∫ x, ‖F0 g x‖ ^ 2 = ∫ ξ, ‖g ξ‖ ^ 2 :=
  energia_Fi (T := 1) (reg0_Vt hg 1) (t := 0) ⟨le_rfl, zero_le_one⟩

theorem cj_F0 {g : E3 → C3} (hh : ∀ ξ, g (-ξ) = cj (g ξ)) (x : E3) : cj (F0 g x) = F0 g x :=
  cj_Fi (V := Vt g) (fun ξ _ => hh ξ) (x, 0)

theorem herm_mj {g : E3 → C3} (hh : ∀ ξ, g (-ξ) = cj (g ξ)) (j : Fin 3) :
    ∀ ξ, mj j (-ξ) • g (-ξ) = cj (mj j ξ • g ξ) := by
  intro ξ
  rw [hh, cj_smul]
  congr 1
  unfold mj
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  have : ((-ξ) j : ℝ) = -(ξ j) := rfl
  rw [this]
  push_cast
  ring

/-! ### O campo real -/

/-- `R0 g = Re F0 g`. -/
noncomputable def R0 (g : E3 → C3) (x : E3) : E3 := reV (F0 g x)

theorem contDiff_R0 {g : E3 → C3} (hg : Pesos g) : ContDiff ℝ ∞ (R0 g) :=
  reV.contDiff.comp (contDiff_F0 hg)

theorem dX_R0 {g : E3 → C3} (hg : Pesos g) (j : Fin 3) (x : E3) :
    dX j (R0 g) x = R0 (fun ξ => mj j ξ • g ξ) x := by
  have hd : HasFDerivAt (F0 g) (fderiv ℝ (F0 g) x) x :=
    ((contDiff_F0 hg).differentiable (by simp) x).hasFDerivAt
  have h := reV.hasFDerivAt.comp x hd
  unfold dX R0
  rw [show (fun x => reV (F0 g x)) = reV ∘ F0 g from rfl, h.fderiv]
  show reV (fderiv ℝ (F0 g) x (e j)) = _
  rw [show fderiv ℝ (F0 g) x (e j) = dX j (F0 g) x from rfl, dX_F0 hg]

theorem cx_R0 {g : E3 → C3} (hh : ∀ ξ, g (-ξ) = cj (g ξ)) (x : E3) : cx (R0 g x) = F0 g x :=
  cx_reV (cj_F0 hh x)

theorem norm_R0 {g : E3 → C3} (hh : ∀ ξ, g (-ξ) = cj (g ξ)) (x : E3) : ‖R0 g x‖ = ‖F0 g x‖ := by
  rw [← cx_R0 hh x, norm_cx]

theorem norm_R0_le (g : E3 → C3) (x : E3) : ‖R0 g x‖ ≤ ‖F0 g x‖ := by
  unfold R0
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => ?_)
  have : |(F0 g x j).re| ≤ ‖F0 g x j‖ := Complex.abs_re_le_norm _
  simp only [reV, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

/-! ### A função de corte -/

theorem dX_comp_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : E3 → V}
    (hf : Differentiable ℝ f) (R : ℝ) (j : Fin 3) (x : E3) :
    dX j (fun y => f (R • y)) x = R • dX j f (R • x) := by
  have h := (hf (R • x)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul R)
  unfold dX
  rw [show (fun y => f (R • y)) = f ∘ fun y => R • y from rfl, h.fderiv]
  simp

theorem dX_const_mul {f : E3 → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (j : Fin 3) (x : E3) :
    dX j (fun y => c * f y) x = c * dX j f x := by
  unfold dX
  rw [fderiv_const_mul (hf x)]
  simp

/-- O "bump" base: `1` em `B̄(0, 1)`, suporte em `B(0, 2)`. -/
noncomputable def bump0 : ContDiffBump (0 : E3) := ⟨1, 2, one_pos, one_lt_two⟩

noncomputable def kap0 (x : E3) : ℝ := bump0 x

theorem contDiff_kap0 : ContDiff ℝ ∞ kap0 := bump0.contDiff

theorem kap0_le_one (x : E3) : kap0 x ≤ 1 := bump0.le_one

theorem kap0_nonneg (x : E3) : 0 ≤ kap0 x := bump0.nonneg

theorem hasCompactSupport_kap0 : HasCompactSupport kap0 := bump0.hasCompactSupport

theorem kap0_one {x : E3} (hx : ‖x‖ ≤ 1) : kap0 x = 1 :=
  bump0.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_zero_right]; exact hx)

/-- `κ_R(x) = κ(x/R)`. -/
noncomputable def kR (R : ℝ) (x : E3) : ℝ := kap0 (R⁻¹ • x)

theorem contDiff_kR (R : ℝ) : ContDiff ℝ ∞ (kR R) :=
  contDiff_kap0.comp (contDiff_const_smul _)

theorem hasCompactSupport_kR {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (kR R) := by
  have h := hasCompactSupport_kap0.comp_homeomorph (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR))
  exact h

theorem kR_bound (R : ℝ) (x : E3) : |kR R x| ≤ 1 := by
  unfold kR
  rw [abs_of_nonneg (kap0_nonneg _)]
  exact kap0_le_one _

theorem dX_kap0_cont (j : Fin 3) : ContDiff ℝ ∞ (dX j kap0) := contDiff_dX_top contDiff_kap0 j

theorem dX_kR (R : ℝ) (j : Fin 3) (x : E3) : dX j (kR R) x = R⁻¹ * dX j kap0 (R⁻¹ • x) :=
  dX_comp_smul (contDiff_kap0.differentiable (by simp)) R⁻¹ j x

theorem dX_dX_kR (R : ℝ) (i j : Fin 3) (x : E3) :
    dX i (dX j (kR R)) x = R⁻¹ * (R⁻¹ * dX i (dX j kap0) (R⁻¹ • x)) := by
  have e : dX j (kR R) = fun y => R⁻¹ * dX j kap0 (R⁻¹ • y) := funext (dX_kR R j)
  have hd : Differentiable ℝ fun y => dX j kap0 (R⁻¹ • y) :=
    ((dX_kap0_cont j).differentiable (by simp)).comp (differentiable_id.const_smul R⁻¹)
  rw [e, dX_const_mul hd _ i x]
  rw [dX_comp_smul ((dX_kap0_cont j).differentiable (by simp)) R⁻¹ i x, smul_eq_mul]

theorem exists_bound_dX_kap0 : ∃ C, 0 ≤ C ∧ ∀ j y, |dX j kap0 y| ≤ C := by
  have h : ∀ j, ∃ C, ∀ y, ‖dX j kap0 y‖ ≤ C := fun j =>
    (hasCompactSupport_dX hasCompactSupport_kap0 j).exists_bound_of_continuous
      (dX_kap0_cont j).continuous
  choose C hC using h
  refine ⟨∑ j, |C j|, by positivity, fun j y => ?_⟩
  have := hC j y
  rw [Real.norm_eq_abs] at this
  exact this.trans ((le_abs_self _).trans (Finset.single_le_sum (fun i _ => abs_nonneg (C i))
    (Finset.mem_univ j)))

theorem exists_bound_dX_dX_kap0 : ∃ C, 0 ≤ C ∧ ∀ i j y, |dX i (dX j kap0) y| ≤ C := by
  have h : ∀ p : Fin 3 × Fin 3, ∃ C, ∀ y, ‖dX p.1 (dX p.2 kap0) y‖ ≤ C := fun p =>
    (hasCompactSupport_dX (hasCompactSupport_dX hasCompactSupport_kap0 p.2) p.1).exists_bound_of_continuous
      (continuous_dX_gen ((dX_kap0_cont p.2).of_le (by simp)) p.1)
  choose C hC using h
  refine ⟨∑ p, |C p|, by positivity, fun i j y => ?_⟩
  have := hC (i, j) y
  rw [Real.norm_eq_abs] at this
  exact this.trans ((le_abs_self _).trans (Finset.single_le_sum (fun p _ => abs_nonneg (C p))
    (Finset.mem_univ (i, j))))

theorem kR_eventually_one (x : E3) : ∀ᶠ n : ℕ in atTop, kR (n + 1) x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  apply kap0_one
  rw [norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
  rw [inv_mul_le_one₀ (by positivity)]
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem tendsto_kR (x : E3) : Tendsto (fun n : ℕ => kR (n + 1) x) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' (by filter_upwards [kR_eventually_one x] with n hn; rw [hn])

theorem inv_succ_le_one (n : ℕ) : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by have := n.cast_nonneg (α := ℝ); linarith)

theorem tendsto_C_inv (C : ℝ) : Tendsto (fun n : ℕ => C * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C
  simpa using h

theorem dX_kR_bound {C : ℝ} (hC : ∀ j y, |dX j kap0 y| ≤ C) (n : ℕ) (j : Fin 3)
    (x : E3) : |dX j (kR (n + 1)) x| ≤ C * ((n : ℝ) + 1)⁻¹ := by
  rw [dX_kR, abs_mul, abs_of_pos (by positivity), mul_comm]
  gcongr
  exact hC j _

theorem dX_dX_kR_bound {C : ℝ} (hC : ∀ i j y, |dX i (dX j kap0) y| ≤ C) (n : ℕ)
    (i j : Fin 3) (x : E3) : |dX i (dX j (kR (n + 1))) x| ≤ C * ((n : ℝ) + 1)⁻¹ := by
  rw [dX_dX_kR, abs_mul, abs_mul, abs_of_pos (by positivity)]
  have h1 := inv_succ_le_one n
  have h2 := hC i j ((((n : ℝ) + 1))⁻¹ • x)
  have h3 : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
  calc ((n : ℝ) + 1)⁻¹ * (((n : ℝ) + 1)⁻¹ * |dX i (dX j kap0) (((n : ℝ) + 1)⁻¹ • x)|)
      ≤ ((n : ℝ) + 1)⁻¹ * (1 * C) := by gcongr
    _ = C * ((n : ℝ) + 1)⁻¹ := by ring

theorem tendsto_dX_kR (j : Fin 3) (x : E3) :
    Tendsto (fun n : ℕ => dX j (kR (n + 1)) x) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_dX_kap0
  refine squeeze_zero_norm (fun n => ?_) (tendsto_C_inv C)
  rw [Real.norm_eq_abs]
  exact dX_kR_bound hC n j x

theorem tendsto_dX_dX_kR (i j : Fin 3) (x : E3) :
    Tendsto (fun n : ℕ => dX i (dX j (kR (n + 1))) x) atTop (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_dX_dX_kap0
  refine squeeze_zero_norm (fun n => ?_) (tendsto_C_inv C)
  rw [Real.norm_eq_abs]
  exact dX_dX_kR_bound hC n i j x


/-! ### Linearidade de `F0` e `R0` -/

theorem continuous_ex_left (x : E3) : Continuous fun ξ => ex ξ x :=
  continuous_ex.comp (continuous_id.prodMk continuous_const)

theorem integrable_ex_smul {g : E3 → C3} (hg : Integrable g) (x : E3) :
    Integrable fun ξ => ex ξ x • g ξ :=
  hg.norm.mono' ((continuous_ex_left x).aestronglyMeasurable.smul hg.aestronglyMeasurable)
    (Eventually.of_forall fun ξ => by rw [norm_smul, norm_ex, one_mul])

theorem F0_add {f g : E3 → C3} (hf : Integrable f) (hg : Integrable g) (x : E3) :
    F0 (fun ξ => f ξ + g ξ) x = F0 f x + F0 g x := by
  unfold F0
  simp_rw [smul_add]
  exact integral_add (integrable_ex_smul hf x) (integrable_ex_smul hg x)

theorem F0_sum {g : Fin 3 → E3 → C3} (hg : ∀ k, Integrable (g k)) (x : E3) :
    F0 (fun ξ => ∑ k, g k ξ) x = ∑ k, F0 (g k) x := by
  unfold F0
  simp_rw [Finset.smul_sum]
  exact integral_finsetSum _ fun k _ => integrable_ex_smul (hg k) x

theorem R0_sum {g : Fin 3 → E3 → C3} (hg : ∀ k, Integrable (g k)) (x : E3) :
    R0 (fun ξ => ∑ k, g k ξ) x = ∑ k, R0 (g k) x := by
  unfold R0
  rw [F0_sum hg, map_sum]

theorem F0_coord (g : E3 → C3) (hg : Integrable g) (x : E3) (i : Fin 3) :
    F0 g x i = ∫ ξ, ex ξ x * g ξ i := by
  unfold F0
  have h := (EuclideanSpace.proj (𝕜 := ℂ) i).integral_comp_comm (integrable_ex_smul hg x)
  show (EuclideanSpace.proj (𝕜 := ℂ) i) (∫ ξ, ex ξ x • g ξ) = _
  rw [← h]
  rfl

theorem R0_coord (g : E3 → C3) (hg : Integrable g) (x : E3) (i : Fin 3) :
    R0 g x i = (∫ ξ, ex ξ x * g ξ i).re := by
  rw [← F0_coord g hg x i]
  rfl

/-! ### Os dados teste e o potencial antissimétrico -/

/-- Dados teste no lado de Fourier: contínuos, de suporte compacto, nulos perto de `0`, de
divergência nula e hermitianos. -/
structure Teste (h : E3 → C3) : Prop where
  cont : Continuous h
  supp : HasCompactSupport h
  zero : ∃ a > 0, ∀ η : E3, ‖η‖ < a → h η = 0
  div : ∀ η, ip η (h η) = 0
  herm : ∀ η, h (-η) = cj (h η)

theorem Teste.pesos {h : E3 → C3} (hh : Teste h) : Pesos h := pesos_of_compact hh.cont hh.supp

/-- `Ĝ_k(η) = (2πi|η|²)⁻¹ (η_k h(η) − h_k(η) η)`: `Σ_k 2πiη_k Ĝ_k = h` e `(Ĝ_k)_i = −(Ĝ_i)_k`. -/
noncomputable def Gk (h : E3 → C3) (k : Fin 3) (η : E3) : C3 :=
  ((2 * π * Complex.I * ((‖η‖ ^ 2 : ℝ) : ℂ))⁻¹) • (((η k : ℝ) : ℂ) • h η - (h η k) • cx η)

theorem Gk_zero {h : E3 → C3} {η : E3} (h0 : h η = 0) (k : Fin 3) : Gk h k η = 0 := by
  simp [Gk, h0]

theorem continuous_Gk {h : E3 → C3} (hh : Teste h) (k : Fin 3) : Continuous (Gk h k) := by
  obtain ⟨a, ha, hz⟩ := hh.zero
  rw [continuous_iff_continuousAt]
  intro η₀
  by_cases hη : ‖η₀‖ < a
  · have hev : Gk h k =ᶠ[𝓝 η₀] fun _ => 0 := by
      have : {η : E3 | ‖η‖ < a} ∈ 𝓝 η₀ :=
        (isOpen_lt continuous_norm continuous_const).mem_nhds hη
      filter_upwards [this] with η hη'
      exact Gk_zero (hz η hη') k
    exact (continuousAt_const).congr hev.symm
  · have hne : η₀ ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hη
      exact hη ha
    have hn : (2 * π * Complex.I * ((‖η₀‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
      have : (‖η₀‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
      have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
      simp [hpi, Complex.I_ne_zero, hne]
    have h1 : ContinuousAt (fun η : E3 => (2 * π * Complex.I * ((‖η‖ ^ 2 : ℝ) : ℂ))⁻¹) η₀ :=
      ContinuousAt.inv₀ (by fun_prop) hn
    have hk : Continuous fun η : E3 => ((η k : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp (EuclideanSpace.proj (𝕜 := ℝ) k).continuous
    have hhk : Continuous fun η => h η k := (EuclideanSpace.proj (𝕜 := ℂ) k).continuous.comp hh.cont
    exact h1.smul ((hk.smul hh.cont).sub (hhk.smul continuous_cx)).continuousAt

theorem hasCompactSupport_Gk {h : E3 → C3} (hh : Teste h) (k : Fin 3) :
    HasCompactSupport (Gk h k) :=
  hcs_of_zero hh.supp fun _ hη => Gk_zero hη k

theorem pesos_Gk {h : E3 → C3} (hh : Teste h) (k : Fin 3) : Pesos (Gk h k) :=
  pesos_of_compact (continuous_Gk hh k) (hasCompactSupport_Gk hh k)

theorem Gk_antisymm (h : E3 → C3) (k i : Fin 3) (η : E3) : Gk h k η i = -(Gk h i η k) := by
  simp only [Gk, PiLp.smul_apply, PiLp.sub_apply, cx_apply, smul_eq_mul]
  ring

theorem sum_mj_Gk {h : E3 → C3} (hh : Teste h) (η : E3) : ∑ k, mj k η • Gk h k η = h η := by
  obtain ⟨a, ha, hz⟩ := hh.zero
  by_cases hη : η = 0
  · have h0 : h η = 0 := hz η (by rw [hη, norm_zero]; exact ha)
    simp [Gk_zero h0, h0]
  have hn2 : ((‖η‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (‖η‖ ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hη)
    exact_mod_cast this
  have hpi : (2 * π * Complex.I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr pi_ne_zero
    simp [this, Complex.I_ne_zero]
  have e1 : ∀ k, mj k η • Gk h k η =
      ((((‖η‖ ^ 2 : ℝ) : ℂ))⁻¹) • (((η k : ℝ) : ℂ) • (((η k : ℝ) : ℂ) • h η - (h η k) • cx η)) := by
    intro k
    unfold Gk mj
    rw [smul_smul, smul_smul, mul_inv]
    congr 1
    field_simp
  simp_rw [e1, ← Finset.smul_sum, smul_sub, smul_smul, Finset.sum_sub_distrib, ← Finset.sum_smul]
  have e2 : ∑ k, ((η k : ℝ) : ℂ) * ((η k : ℝ) : ℂ) = ((‖η‖ ^ 2 : ℝ) : ℂ) := by
    rw [← ip_cx η]
    rfl
  have e3 : ∑ k, ((η k : ℝ) : ℂ) * h η k = 0 := hh.div η
  rw [e2, e3, zero_smul, sub_zero, smul_smul, inv_mul_cancel₀ hn2, one_smul]

theorem herm_Gk {h : E3 → C3} (hh : Teste h) (k : Fin 3) (η : E3) :
    Gk h k (-η) = cj (Gk h k η) := by
  unfold Gk
  rw [hh.herm, cj_smul, cj_sub, cj_smul, cj_smul, cj_cx, norm_neg]
  have e1 : cx (-η) = -cx η := by ext j; simp
  have e2 : ((((-η) k : ℝ)) : ℂ) = -(((η k : ℝ)) : ℂ) := by simp
  have e3 : (cj (h η)) k = (starRingEnd ℂ) (h η k) := rfl
  rw [e1, e2, e3]
  simp only [map_inv₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  have e4 : (2 * (π : ℂ) * -Complex.I * ((‖η‖ ^ 2 : ℝ) : ℂ))⁻¹ =
      -(2 * (π : ℂ) * Complex.I * ((‖η‖ ^ 2 : ℝ) : ℂ))⁻¹ := by
    rw [← inv_neg]
    ring_nf
  rw [e4, neg_smul, neg_smul, smul_neg, smul_sub, smul_sub]
  simp only [smul_neg]
  abel


/-! ### O campo teste como rotacional generalizado -/

theorem R0_eq_sum_dX {h : E3 → C3} (hh : Teste h) (x : E3) :
    R0 h x = ∑ k, dX k (R0 (Gk h k)) x := by
  have hi : ∀ k, Integrable fun ξ => mj k ξ • Gk h k ξ := fun k =>
    integrable_pesos (pesos_mj (pesos_Gk hh k) k)
  simp_rw [dX_R0 (pesos_Gk hh _)]
  rw [← R0_sum hi]
  congr 1
  funext ξ
  exact (sum_mj_Gk hh ξ).symm

theorem R0_Gk_antisymm {h : E3 → C3} (hh : Teste h) (k i : Fin 3) (x : E3) :
    R0 (Gk h k) x i = -(R0 (Gk h i) x k) := by
  rw [R0_coord _ (integrable_pesos (pesos_Gk hh k)), R0_coord _ (integrable_pesos (pesos_Gk hh i))]
  have e : (fun ξ => ex ξ x * Gk h k ξ i) = fun ξ => -(ex ξ x * Gk h i ξ k) := by
    funext ξ
    rw [Gk_antisymm, mul_neg]
  rw [e, integral_neg, Complex.neg_re]

/-! ### Derivadas de ordem 2 -/

theorem hcs_dX_gen {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : E3 → V}
    (hF : HasCompactSupport F) (j : Fin 3) : HasCompactSupport (dX j F) := by
  have h := hF.fderiv (𝕜 := ℝ)
  have : dX j F = (fun L : E3 →L[ℝ] V => L (e j)) ∘ fderiv ℝ F := rfl
  rw [this]
  exact h.comp_left (by simp)

theorem dX_fun_sum {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : Fin 3 → E3 → V}
    {x : E3} (hf : ∀ k, DifferentiableAt ℝ (f k) x)
    (i : Fin 3) : dX i (fun y => ∑ k, f k y) x = ∑ k, dX i (f k) x := by
  unfold dX
  rw [fderiv_fun_sum fun k _ => hf k]
  simp

theorem dX_fun_neg {f : E3 → ℝ} (i : Fin 3) (x : E3) : dX i (fun y => -f y) x = -dX i f x := by
  unfold dX
  rw [fderiv_fun_neg]
  rfl

theorem dX_dX_eq {f : E3 → ℝ} (hf : ContDiff ℝ 2 f) (i k : Fin 3) (x : E3) :
    dX i (dX k f) x = fderiv ℝ (fderiv ℝ f) x (e i) (e k) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)) x
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (e k) x)
  unfold dX
  rw [show (fun y => fderiv ℝ f y (e k)) = fun y => (fderiv ℝ f y) ((fun _ => e k) y) from rfl,
    h.fderiv]
  simp

theorem dX_dX_comm {f : E3 → ℝ} (hf : ContDiff ℝ 2 f) (i k : Fin 3) (x : E3) :
    dX i (dX k f) x = dX k (dX i f) x := by
  rw [dX_dX_eq hf, dX_dX_eq hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq (e i) (e k)

/-! ### O teste truncado -/

/-- O potencial `G_k = Re F0 Ĝ_k`. -/
noncomputable def Gr (h : E3 → C3) (k : Fin 3) : E3 → E3 := R0 (Gk h k)

/-- **O teste truncado** `φ_n = Σ_k ∂_k(κ_{n+1} G_k)`: suporte compacto, divergência nula. -/
noncomputable def phiN (h : E3 → C3) (n : ℕ) (x : E3) : E3 :=
  ∑ k, dX k (fun y => kR (n + 1) y • Gr h k y) x

theorem contDiff_Gr {h : E3 → C3} (hh : Teste h) (k : Fin 3) : ContDiff ℝ ∞ (Gr h k) :=
  contDiff_R0 (pesos_Gk hh k)

theorem contDiff_kG {h : E3 → C3} (hh : Teste h) (n : ℕ) (k : Fin 3) :
    ContDiff ℝ ∞ (fun y => kR (n + 1) y • Gr h k y) :=
  (contDiff_kR _).smul (contDiff_Gr hh k)

theorem contDiff_phiN {h : E3 → C3} (hh : Teste h) (n : ℕ) : ContDiff ℝ ∞ (phiN h n) := by
  unfold phiN
  exact ContDiff.sum fun k _ => contDiff_dX_top (contDiff_kG hh n k) k

theorem hasCompactSupport_phiN {h : E3 → C3} (_hh : Teste h) (n : ℕ) :
    HasCompactSupport (phiN h n) := by
  have hc : ∀ k, HasCompactSupport (dX k (fun y => kR (n + 1) y • Gr h k y)) := fun k =>
    hcs_dX_gen ((hasCompactSupport_kR (by positivity)).smul_right) k
  unfold phiN
  have h1 : HasCompactSupport (fun x => ∑ k ∈ (Finset.univ : Finset (Fin 3)),
      dX k (fun y => kR (n + 1) y • Gr h k y) x) := by
    refine HasCompactSupport.intro (((hc 0).isCompact.union (hc 1).isCompact).union
      (hc 2).isCompact) fun x hx => ?_
    simp only [mem_union, not_or] at hx
    rw [Fin.sum_univ_three, image_eq_zero_of_notMem_tsupport hx.1.1,
      image_eq_zero_of_notMem_tsupport hx.1.2, image_eq_zero_of_notMem_tsupport hx.2]
    simp
  exact h1

theorem div_phiN {h : E3 → C3} (hh : Teste h) (n : ℕ) (x : E3) :
    div (phiN h n) x = 0 := by
  set F : Fin 3 → Fin 3 → E3 → ℝ := fun k i y => kR (n + 1) y * Gr h k y i with hF_def
  have hF2 : ∀ k i, ContDiff ℝ ∞ (F k i) := fun k i =>
    (contDiff_kR _).mul ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp (contDiff_Gr hh k))
  have hanti : ∀ k i, F k i = fun y => -(F i k y) := by
    intro k i
    funext y
    simp only [hF_def, Gr]
    rw [R0_Gk_antisymm hh k i y]
    ring
  have hcoord : ∀ i, (fun y => phiN h n y i) = fun y => ∑ k, dX k (F k i) y := by
    intro i
    funext y
    unfold phiN
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dX_coord ((contDiff_kG hh n k).differentiable (by simp) y)]
    rfl
  have hdiff : ∀ k i, Differentiable ℝ (dX k (F k i)) := fun k i =>
    (contDiff_dX_top (hF2 k i) k).differentiable (by simp)
  have hstep : ∀ i, dX i (fun y => phiN h n y i) x = ∑ k, dX i (dX k (F k i)) x := by
    intro i
    rw [hcoord i, dX_fun_sum fun k => hdiff k i x]
  unfold div
  have e1 : ∑ i, dX i (phiN h n) x i = ∑ i, ∑ k, dX i (dX k (F k i)) x := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dX_coord ((contDiff_phiN hh n).differentiable (by simp) x), hstep]
  rw [e1]
  have e2 : ∑ i, ∑ k, dX i (dX k (F k i)) x = -∑ i, ∑ k, dX i (dX k (F k i)) x := by
    conv_rhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dX_dX_comm ((hF2 i k).of_le (by simp)), hanti i k]
    have : dX k (fun y => -F k i y) = fun y => -dX k (F k i) y := by
      funext y
      exact dX_fun_neg k y
    rw [this, dX_fun_neg, neg_neg]
  linarith


theorem dX_fun_add {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f g : E3 → V} {x : E3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin 3) :
    dX i (fun y => f y + g y) x = dX i f x + dX i g x := by
  unfold dX
  rw [fderiv_fun_add hf hg]
  rfl

/-- `φ_n = Σ_k (∂_k κ) G_k + κ θ`. -/
theorem phiN_eq {h : E3 → C3} (hh : Teste h) (n : ℕ) (x : E3) :
    phiN h n x = ∑ k, dX k (kR (n + 1)) x • Gr h k x + kR (n + 1) x • R0 h x := by
  unfold phiN
  have hk := (contDiff_kR (n + 1)).differentiable (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  simp_rw [dX_smul_scalar (hk x) ((contDiff_Gr hh _).differentiable (by simp) x)]
  rw [Finset.sum_add_distrib, R0_eq_sum_dX hh x, Finset.smul_sum]
  rfl

/-- A derivada do teste truncado. -/
theorem dX_phiN {h : E3 → C3} (hh : Teste h) (n : ℕ) (j : Fin 3) (x : E3) :
    dX j (phiN h n) x = ∑ k, (dX j (dX k (kR (n + 1))) x • Gr h k x +
      dX k (kR (n + 1)) x • dX j (Gr h k) x) +
      (dX j (kR (n + 1)) x • R0 h x + kR (n + 1) x • dX j (R0 h) x) := by
  have hk : ContDiff ℝ ∞ (kR (n + 1)) := contDiff_kR _
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hdk : ∀ k, Differentiable ℝ (dX k (kR (n + 1))) := fun k =>
    (contDiff_dX_top hk k).differentiable hne
  have hG : ∀ k, Differentiable ℝ (Gr h k) := fun k => (contDiff_Gr hh k).differentiable hne
  have hR : Differentiable ℝ (R0 h) := (contDiff_R0 hh.pesos).differentiable hne
  have e : phiN h n = fun x => ∑ k, dX k (kR (n + 1)) x • Gr h k x + kR (n + 1) x • R0 h x :=
    funext (phiN_eq hh n)
  have d0 : ∀ k, DifferentiableAt ℝ (fun y => dX k (kR (n + 1)) y • Gr h k y) x := fun k =>
    (hdk k x).smul (hG k x)
  have d1 : DifferentiableAt ℝ (fun y => ∑ k, dX k (kR (n + 1)) y • Gr h k y) x :=
    DifferentiableAt.fun_sum fun k _ => d0 k
  have d2 : DifferentiableAt ℝ (fun y => kR (n + 1) y • R0 h y) x :=
    (hk.differentiable hne x).smul (hR x)
  rw [e, dX_fun_add d1 d2, dX_fun_sum (f := fun k y => dX k (kR (n + 1)) y • Gr h k y) d0]
  simp_rw [dX_smul_scalar (hdk _ x) (hG _ x)]
  rw [dX_smul_scalar (hk.differentiable hne x) (hR x)]

theorem tendsto_phiN {h : E3 → C3} (hh : Teste h) (x : E3) :
    Tendsto (fun n => phiN h n x) atTop (𝓝 (R0 h x)) := by
  simp_rw [phiN_eq hh]
  have h1 : Tendsto (fun n : ℕ => ∑ k, dX k (kR (n + 1)) x • Gr h k x) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun k _ =>
      (tendsto_dX_kR k x).smul_const (Gr h k x)
    simpa using this
  have h2 : Tendsto (fun n : ℕ => kR (n + 1) x • R0 h x) atTop (𝓝 (R0 h x)) := by
    have := (tendsto_kR x).smul_const (R0 h x)
    simpa using this
  simpa using h1.add h2

theorem tendsto_dX_phiN {h : E3 → C3} (hh : Teste h) (j : Fin 3) (x : E3) :
    Tendsto (fun n => dX j (phiN h n) x) atTop (𝓝 (dX j (R0 h) x)) := by
  simp_rw [dX_phiN hh]
  have h1 : Tendsto (fun n : ℕ => ∑ k, (dX j (dX k (kR (n + 1))) x • Gr h k x +
      dX k (kR (n + 1)) x • dX j (Gr h k) x)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun k _ =>
      ((tendsto_dX_dX_kR j k x).smul_const (Gr h k x)).add
        ((tendsto_dX_kR k x).smul_const (dX j (Gr h k) x))
    simpa using this
  have h2 : Tendsto (fun n : ℕ => dX j (kR (n + 1)) x • R0 h x + kR (n + 1) x • dX j (R0 h) x)
      atTop (𝓝 (dX j (R0 h) x)) := by
    have := ((tendsto_dX_kR j x).smul_const (R0 h x)).add
      ((tendsto_kR x).smul_const (dX j (R0 h) x))
    simpa using this
  simpa using h1.add h2

/-- Majorante de `|φ_n|`. -/
noncomputable def Dphi (h : E3 → C3) (C1 : ℝ) (x : E3) : ℝ :=
  C1 * ∑ k, ‖Gr h k x‖ + ‖R0 h x‖

/-- Majorante de `|∂_j φ_n|`. -/
noncomputable def DdPhi (h : E3 → C3) (C1 C2 : ℝ) (j : Fin 3) (x : E3) : ℝ :=
  ∑ k, (C2 * ‖Gr h k x‖ + C1 * ‖dX j (Gr h k) x‖) + (C1 * ‖R0 h x‖ + ‖dX j (R0 h) x‖)

theorem norm_phiN_le {h : E3 → C3} (hh : Teste h) {C1 : ℝ}
    (hC1 : ∀ j y, |dX j kap0 y| ≤ C1) (n : ℕ) (x : E3) : ‖phiN h n x‖ ≤ Dphi h C1 x := by
  rw [phiN_eq hh]
  have hk1 : ∀ k, |dX k (kR (n + 1)) x| ≤ C1 := fun k =>
    (dX_kR_bound hC1 n k x).trans (by
      have := inv_succ_le_one n
      have h0 : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0 0)
      nlinarith)
  unfold Dphi
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [norm_smul, Real.norm_eq_abs]
    gcongr
    exact hk1 k
  · rw [norm_smul, Real.norm_eq_abs]
    calc |kR (n + 1) x| * ‖R0 h x‖ ≤ 1 * ‖R0 h x‖ := by gcongr; exact kR_bound _ _
      _ = ‖R0 h x‖ := one_mul _

theorem norm_dX_phiN_le {h : E3 → C3} (hh : Teste h) {C1 C2 : ℝ}
    (hC1 : ∀ j y, |dX j kap0 y| ≤ C1) (hC2 : ∀ i j y, |dX i (dX j kap0) y| ≤ C2) (n : ℕ)
    (j : Fin 3) (x : E3) : ‖dX j (phiN h n) x‖ ≤ DdPhi h C1 C2 j x := by
  rw [dX_phiN hh]
  have h1 := inv_succ_le_one n
  have hC10 : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0 0)
  have hC20 : 0 ≤ C2 := (abs_nonneg _).trans (hC2 0 0 0)
  have hk1 : ∀ k, |dX k (kR (n + 1)) x| ≤ C1 := fun k =>
    (dX_kR_bound hC1 n k x).trans (by nlinarith)
  have hk2 : ∀ k, |dX j (dX k (kR (n + 1))) x| ≤ C2 := fun k =>
    (dX_dX_kR_bound hC2 n j k x).trans (by nlinarith)
  unfold DdPhi
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]; gcongr; exact hk2 k
    · rw [norm_smul, Real.norm_eq_abs]; gcongr; exact hk1 k
  · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs]; gcongr; exact hk1 j
    · rw [norm_smul, Real.norm_eq_abs]
      calc |kR (n + 1) x| * ‖dX j (R0 h) x‖ ≤ 1 * ‖dX j (R0 h) x‖ := by
            gcongr; exact kR_bound _ _
        _ = ‖dX j (R0 h) x‖ := one_mul _


/-! ### Funções contínuas, limitadas e de quadrado integrável -/

/-- `f` contínua, limitada e com `f²` integrável. -/
def L2B (f : E3 → ℝ) : Prop :=
  Continuous f ∧ (∃ B, ∀ x, |f x| ≤ B) ∧ Integrable fun x => f x ^ 2

theorem L2B.add {f g : E3 → ℝ} (hf : L2B f) (hg : L2B g) : L2B fun x => f x + g x := by
  obtain ⟨hfc, ⟨Bf, hBf⟩, hfi⟩ := hf
  obtain ⟨hgc, ⟨Bg, hBg⟩, hgi⟩ := hg
  refine ⟨hfc.add hgc, ⟨Bf + Bg, fun x => (abs_add_le _ _).trans (add_le_add (hBf x) (hBg x))⟩, ?_⟩
  refine ((hfi.add hgi).const_mul 2).mono' ((hfc.add hgc).pow 2).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  show (f x + g x) ^ 2 ≤ 2 * (f x ^ 2 + g x ^ 2)
  nlinarith [sq_nonneg (f x - g x)]

theorem L2B.const_mul {f : E3 → ℝ} (hf : L2B f) (c : ℝ) : L2B fun x => c * f x := by
  obtain ⟨hfc, ⟨B, hB⟩, hfi⟩ := hf
  refine ⟨continuous_const.mul hfc, ⟨|c| * B, fun x => by rw [abs_mul]; gcongr; exact hB x⟩, ?_⟩
  have : (fun x => (c * f x) ^ 2) = fun x => c ^ 2 * f x ^ 2 := by funext x; ring
  rw [this]
  exact hfi.const_mul _

theorem L2B.sum {f : Fin 3 → E3 → ℝ} (hf : ∀ k, L2B (f k)) : L2B fun x => ∑ k, f k x := by
  have e : (fun x => ∑ k, f k x) = fun x => f 0 x + f 1 x + f 2 x := by
    funext x
    rw [Fin.sum_univ_three]
  rw [e]
  exact ((hf 0).add (hf 1)).add (hf 2)

theorem L2B_R0 {g : E3 → C3} (hg : Pesos g) : L2B fun x => ‖R0 g x‖ := by
  refine ⟨(contDiff_R0 hg).continuous.norm, ⟨∫ ξ, ‖g ξ‖, fun x => ?_⟩, ?_⟩
  · rw [abs_of_nonneg (norm_nonneg _)]
    exact (norm_R0_le g x).trans (norm_F0_le g x)
  · refine (plancherel_F0 hg).1.mono' ((contDiff_R0 hg).continuous.norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_R0_le g x) 2

theorem L2B_dX_R0 {g : E3 → C3} (hg : Pesos g) (j : Fin 3) : L2B fun x => ‖dX j (R0 g) x‖ := by
  have e : (fun x => ‖dX j (R0 g) x‖) = fun x => ‖R0 (fun ξ => mj j ξ • g ξ) x‖ := by
    funext x
    rw [dX_R0 hg]
  rw [e]
  exact L2B_R0 (pesos_mj hg j)

theorem L2B_Dphi {h : E3 → C3} (hh : Teste h) (C1 : ℝ) : L2B (Dphi h C1) :=
  ((L2B.sum fun k => L2B_R0 (pesos_Gk hh k)).const_mul C1).add (L2B_R0 hh.pesos)

theorem L2B_DdPhi {h : E3 → C3} (hh : Teste h) (C1 C2 : ℝ) (j : Fin 3) : L2B (DdPhi h C1 C2 j) :=
  (L2B.sum fun k => ((L2B_R0 (pesos_Gk hh k)).const_mul C2).add
    ((L2B_dX_R0 (pesos_Gk hh k) j).const_mul C1)).add
    (((L2B_R0 hh.pesos).const_mul C1).add (L2B_dX_R0 hh.pesos j))

end ATK.NSTeste

#print axioms ATK.NSTeste.Pesos
#print axioms ATK.NSTeste.pesos_of_compact
#print axioms ATK.NSTeste.Vt
#print axioms ATK.NSTeste.reg0_Vt
#print axioms ATK.NSTeste.reg0_zero
#print axioms ATK.NSTeste.suave_zero
#print axioms ATK.NSTeste.suave_Vt
#print axioms ATK.NSTeste.F0
#print axioms ATK.NSTeste.F0_eq_Fi
#print axioms ATK.NSTeste.contDiff_F0
#print axioms ATK.NSTeste.pesos_mj
#print axioms ATK.NSTeste.dX_F0
#print axioms ATK.NSTeste.integrable_pesos
#print axioms ATK.NSTeste.norm_F0_le
#print axioms ATK.NSTeste.plancherel_F0
#print axioms ATK.NSTeste.cj_F0
#print axioms ATK.NSTeste.herm_mj
#print axioms ATK.NSTeste.R0
#print axioms ATK.NSTeste.contDiff_R0
#print axioms ATK.NSTeste.dX_R0
#print axioms ATK.NSTeste.cx_R0
#print axioms ATK.NSTeste.norm_R0
#print axioms ATK.NSTeste.norm_R0_le
#print axioms ATK.NSTeste.dX_comp_smul
#print axioms ATK.NSTeste.dX_const_mul
#print axioms ATK.NSTeste.bump0
#print axioms ATK.NSTeste.kap0
#print axioms ATK.NSTeste.contDiff_kap0
#print axioms ATK.NSTeste.kap0_le_one
#print axioms ATK.NSTeste.kap0_nonneg
#print axioms ATK.NSTeste.hasCompactSupport_kap0
#print axioms ATK.NSTeste.kap0_one
#print axioms ATK.NSTeste.kR
#print axioms ATK.NSTeste.contDiff_kR
#print axioms ATK.NSTeste.hasCompactSupport_kR
#print axioms ATK.NSTeste.kR_bound
#print axioms ATK.NSTeste.dX_kap0_cont
#print axioms ATK.NSTeste.dX_kR
#print axioms ATK.NSTeste.dX_dX_kR
#print axioms ATK.NSTeste.exists_bound_dX_kap0
#print axioms ATK.NSTeste.exists_bound_dX_dX_kap0
#print axioms ATK.NSTeste.kR_eventually_one
#print axioms ATK.NSTeste.tendsto_kR
#print axioms ATK.NSTeste.inv_succ_le_one
#print axioms ATK.NSTeste.tendsto_C_inv
#print axioms ATK.NSTeste.dX_kR_bound
#print axioms ATK.NSTeste.dX_dX_kR_bound
#print axioms ATK.NSTeste.tendsto_dX_kR
#print axioms ATK.NSTeste.tendsto_dX_dX_kR
#print axioms ATK.NSTeste.continuous_ex_left
#print axioms ATK.NSTeste.integrable_ex_smul
#print axioms ATK.NSTeste.F0_add
#print axioms ATK.NSTeste.F0_sum
#print axioms ATK.NSTeste.R0_sum
#print axioms ATK.NSTeste.F0_coord
#print axioms ATK.NSTeste.R0_coord
#print axioms ATK.NSTeste.Teste
#print axioms ATK.NSTeste.Teste.pesos
#print axioms ATK.NSTeste.Gk
#print axioms ATK.NSTeste.Gk_zero
#print axioms ATK.NSTeste.continuous_Gk
#print axioms ATK.NSTeste.hasCompactSupport_Gk
#print axioms ATK.NSTeste.pesos_Gk
#print axioms ATK.NSTeste.Gk_antisymm
#print axioms ATK.NSTeste.sum_mj_Gk
#print axioms ATK.NSTeste.herm_Gk
#print axioms ATK.NSTeste.R0_eq_sum_dX
#print axioms ATK.NSTeste.R0_Gk_antisymm
#print axioms ATK.NSTeste.hcs_dX_gen
#print axioms ATK.NSTeste.dX_fun_sum
#print axioms ATK.NSTeste.dX_fun_neg
#print axioms ATK.NSTeste.dX_dX_eq
#print axioms ATK.NSTeste.dX_dX_comm
#print axioms ATK.NSTeste.Gr
#print axioms ATK.NSTeste.phiN
#print axioms ATK.NSTeste.contDiff_Gr
#print axioms ATK.NSTeste.contDiff_kG
#print axioms ATK.NSTeste.contDiff_phiN
#print axioms ATK.NSTeste.hasCompactSupport_phiN
#print axioms ATK.NSTeste.div_phiN
#print axioms ATK.NSTeste.dX_fun_add
#print axioms ATK.NSTeste.phiN_eq
#print axioms ATK.NSTeste.dX_phiN
#print axioms ATK.NSTeste.tendsto_phiN
#print axioms ATK.NSTeste.tendsto_dX_phiN
#print axioms ATK.NSTeste.Dphi
#print axioms ATK.NSTeste.DdPhi
#print axioms ATK.NSTeste.norm_phiN_le
#print axioms ATK.NSTeste.norm_dX_phiN_le
#print axioms ATK.NSTeste.L2B
#print axioms ATK.NSTeste.L2B.add
#print axioms ATK.NSTeste.L2B.const_mul
#print axioms ATK.NSTeste.L2B.sum
#print axioms ATK.NSTeste.L2B_R0
#print axioms ATK.NSTeste.L2B_dX_R0
#print axioms ATK.NSTeste.L2B_Dphi
#print axioms ATK.NSTeste.L2B_DdPhi
