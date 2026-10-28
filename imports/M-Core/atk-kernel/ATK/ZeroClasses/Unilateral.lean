import ATK.ZeroClasses.OmegaPsi
import ATK.ZeroClasses.BDTheta

/-!
# Cotas de um lado só: o teorema de Landau e `Θ` lido por cima ou por baixo (rodada 87)

As rodadas 55–57 e 76 leram `Θ = sup Re ρ` em cotas **bilaterais**: `|ψ(x) − x| ≪ x^{θ+ε}` ou
`|M(x)| ≪ x^{θ+ε}` (`QuasiRH.semZeros_iff_psi`, `BDTheta.Teta_le_iff_psi`). Aqui basta **um lado**:

* **`landau`** (Landau 1905, forma de Pringsheim): se `f ≥ 0` em `(1, ∞)` e a transformada
  `Ik f 0 s = ∫_{x>1} x^{−s−1} f(x) dx` coincide, onde converge, com uma `Φ` holomorfa no disco `|s − c| < r`,
  então a integral converge em todo `σ ∈ (c − r, c]` e vale `Φ(σ)`. A prova: série de Taylor de `Φ` em `c`
  (`Complex.hasSum_taylorSeries_on_ball`), derivadas `Ik f k` por derivação sob o sinal de integral
  (`hasDerivAt_Ik`, `iteratedDeriv_Ik`), todos os termos `≥ 0`, e convergência monótona (`lintegral_tsum`);
* **a série de Abel como transformada** (`integral_escada`): `∫_{x>1} x^{−s−1} a(⌊x⌋) dx = GA a(s)/s`;
* **`extensao`**: `a(N) ≤ A(N + 1)^θ + K` (`0 ≤ θ < 1`) e `|a(N)| ≪ N` dão
  `f = A′x^θ + K − a(⌊x⌋) ≥ 0`, e Landau no disco `|s − 2| < 2 − θ` (sem zeros de `ζ`: `zeta₁_ne_zero_bola`)
  estende `GA a` a `Re s > θ`;
* **`semZeros_of_psi_le`, `semZeros_of_psi_ge`, `semZeros_of_mertens_le`, `semZeros_of_mertens_ge`**: uma cota
  **de um lado só** `ψ(N) − N ≤ A(N + 1)^θ + K` (ou `≥ −…`, ou o mesmo para `M`) já implica `ζ ≠ 0` em `Re s > θ`;
* **`Teta_le_iff_psi_le`** (e `_psi_ge`, `_mertens_le`, `_mertens_ge`): `Θ ≤ θ` ⟺ a cota de um lado com
  expoente `θ + ε`;
* **`psi_omega_mais`, `psi_omega_menos`, `mertens_omega_mais`, `mertens_omega_menos`**: para `0 ≤ θ < Θ`,
  `ψ(x) − x` e `M(x)` ultrapassam `±(A x^θ + K)` dos dois lados (`Ω±(x^θ)`; incondicional para `θ < ½`);
* **`rh_iff_psi_le`, `rh_iff_psi_ge`**: RH ⟺ von Koch de um lado só; **`rh_of_mertens_le`**,
  **`rh_of_mertens_ge`**: `M(N) ≤ A√(N + 1) + K` (ou `≥ −…`) ⟹ RH.

Classificação (rodada 87): **ferramenta** (o teorema de Landau para transformadas de Mellin de `f ≥ 0`) e
**reformulação** (`Θ` e RH por cotas unilaterais), mais **consequência** (as oscilações `Ω±(x^θ)`, `θ < Θ`).
A forma `Ω±(√x)` com constante (pelo polo num zero de Hardy) e a simplicidade dos zeros sob a cota de Mertens
fraca ficam para a rodada seguinte. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric MeasureTheory
open scoped Real ENNReal Nat

namespace ATK.ZeroClasses.Unilateral

/-! ## 1. A transformada `∫_{x > 1} (−log x)^k x^{−s−1} f(x) dx` -/

/-- `Ik f k s = ∫_{x > 1} (−log x)^k x^{−s−1} f(x) dx`. -/
noncomputable def Ik (f : ℝ → ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), (((-Real.log x) ^ k : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) * (f x : ℂ)

/-- `x^{−σ−1}|f(x)|` integrável em `(1, ∞)` para todo `σ > σ₀`. -/
def IntAcima (f : ℝ → ℝ) (σ₀ : ℝ) : Prop :=
  ∀ σ : ℝ, σ₀ < σ → IntegrableOn (fun x => x ^ (-σ - 1) * |f x|) (Ioi 1)

/-- `(log x)^k ≤ (k/ε)^k x^ε` para `x ≥ 1`. -/
theorem log_pow_le {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 < ε) (k : ℕ) :
    Real.log x ^ k ≤ ((k : ℝ) / ε) ^ k * x ^ ε := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, one_mul]
    exact Real.one_le_rpow hx hε.le
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hl := Real.log_le_rpow_div (x := x) (by linarith) (show 0 < ε / k by positivity)
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  calc Real.log x ^ k ≤ (x ^ (ε / k) / (ε / k)) ^ k := pow_le_pow_left₀ hl0 hl k
    _ = (x ^ (ε / k)) ^ k / (ε / k) ^ k := div_pow _ _ _
    _ = x ^ ε / (ε / k) ^ k := by
        rw [← Real.rpow_natCast (x ^ (ε / k)), ← Real.rpow_mul (by linarith), div_mul_cancel₀ _ hk'.ne']
    _ = ((k : ℝ) / ε) ^ k * x ^ ε := by
        rw [div_pow, div_pow]
        field_simp

theorem integrable_log_pow {f : ℝ → ℝ} {σ₀ : ℝ} (hf : Measurable f) (h : IntAcima f σ₀) (k : ℕ)
    {σ : ℝ} (hσ : σ₀ < σ) :
    IntegrableOn (fun x => Real.log x ^ k * x ^ (-σ - 1) * |f x|) (Ioi 1) := by
  set ε := (σ - σ₀) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hi := (h (σ - ε) (by rw [hε]; linarith)).const_mul (((k : ℝ) / ε) ^ k)
  refine hi.mono' ?_ ?_
  · exact (by fun_prop : Measurable fun x => Real.log x ^ k * x ^ (-σ - 1) * |f x|).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : 1 ≤ x := le_of_lt hx
    have hx0 : 0 < x := by linarith
    have hpos : 0 ≤ Real.log x ^ k * x ^ (-σ - 1) * |f x| :=
      mul_nonneg (mul_nonneg (pow_nonneg (Real.log_nonneg hx1) k) (Real.rpow_nonneg hx0.le _)) (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hpos]
    have h1 := log_pow_le hx1 hε0 k
    have h2 : x ^ ε * x ^ (-σ - 1) = x ^ (-(σ - ε) - 1) := by
      rw [← Real.rpow_add hx0]; ring_nf
    calc Real.log x ^ k * x ^ (-σ - 1) * |f x|
        ≤ (((k : ℝ) / ε) ^ k * x ^ ε) * x ^ (-σ - 1) * |f x| := by gcongr
      _ = ((k : ℝ) / ε) ^ k * (x ^ (-(σ - ε) - 1) * |f x|) := by rw [← h2]; ring

theorem norm_integrando {f : ℝ → ℝ} (k : ℕ) {x : ℝ} (hx : 1 < x) (z : ℂ) :
    ‖(((-Real.log x) ^ k : ℝ) : ℂ) * (x : ℂ) ^ (-z - 1) * (f x : ℂ)‖ =
      Real.log x ^ k * x ^ (-z.re - 1) * |f x| := by
  have hx0 : 0 < x := by linarith
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0, abs_pow, abs_neg, abs_of_nonneg (Real.log_nonneg hx.le)]
  simp

theorem aesm_integrando (f : ℝ → ℝ) (hf : Measurable f) (k : ℕ) (z : ℂ) :
    AEStronglyMeasurable (fun x : ℝ => (((-Real.log x) ^ k : ℝ) : ℂ) * (x : ℂ) ^ (-z - 1) * (f x : ℂ))
      (volume.restrict (Ioi (1 : ℝ))) := by
  refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ ?_) ?_
  · exact (Complex.measurable_ofReal.comp (by fun_prop : Measurable fun x : ℝ => (-Real.log x) ^ k)).aestronglyMeasurable
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt fun x hx => ?_
    exact continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt (lt_trans zero_lt_one hx)))
  · exact (Complex.measurable_ofReal.comp hf).aestronglyMeasurable

theorem integrable_integrando {f : ℝ → ℝ} {σ₀ : ℝ} (hf : Measurable f) (h : IntAcima f σ₀) (k : ℕ)
    {z : ℂ} (hz : σ₀ < z.re) :
    Integrable (fun x : ℝ => (((-Real.log x) ^ k : ℝ) : ℂ) * (x : ℂ) ^ (-z - 1) * (f x : ℂ))
      (volume.restrict (Ioi (1 : ℝ))) := by
  refine (integrable_log_pow hf h k hz).mono' (aesm_integrando f hf k z) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [norm_integrando k hx]

/-- **A derivada de `Ik`**: `d/ds Ik f k = Ik f (k + 1)` em `Re s > σ₀` (derivação sob o sinal de integral). -/
theorem hasDerivAt_Ik {f : ℝ → ℝ} {σ₀ : ℝ} (hf : Measurable f) (h : IntAcima f σ₀) (k : ℕ) {s : ℂ}
    (hs : σ₀ < s.re) : HasDerivAt (Ik f k) (Ik f (k + 1) s) s := by
  set ε := (s.re - σ₀) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (1 : ℝ)))
    (F := fun (z : ℂ) (x : ℝ) => (((-Real.log x) ^ k : ℝ) : ℂ) * (x : ℂ) ^ (-z - 1) * (f x : ℂ))
    (F' := fun (z : ℂ) (x : ℝ) => (((-Real.log x) ^ (k + 1) : ℝ) : ℂ) * (x : ℂ) ^ (-z - 1) * (f x : ℂ))
    (x₀ := s) (bound := fun x => Real.log x ^ (k + 1) * x ^ (-(s.re - ε) - 1) * |f x|) (ball_mem_nhds s hε0)
    (Eventually.of_forall fun z => aesm_integrando f hf k z) (integrable_integrando hf h k hs)
    (aesm_integrando f hf (k + 1) s) ?_ (integrable_log_pow hf h (k + 1) (by rw [hε]; linarith)) ?_
  · exact key.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z hz
    rw [norm_integrando (k + 1) hx]
    have hx1 : 1 ≤ x := le_of_lt hx
    have hre : s.re - ε < z.re := by
      have h1 : |z.re - s.re| < ε := by
        calc |z.re - s.re| = |(z - s).re| := by rw [sub_re]
          _ ≤ ‖z - s‖ := abs_re_le_norm _
          _ < ε := by rw [← dist_eq]; exact hz
      linarith [(abs_lt.mp h1).1]
    have hp : x ^ (-z.re - 1) ≤ x ^ (-(s.re - ε) - 1) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h0 : 0 ≤ Real.log x ^ (k + 1) := pow_nonneg (Real.log_nonneg hx1) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp h0) (abs_nonneg _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx z _
    have hx0 : (x : ℂ) ≠ 0 := by
      have : (0 : ℝ) < x := by linarith [show (1 : ℝ) < x from hx]
      exact_mod_cast this.ne'
    have hd : HasDerivAt (fun z : ℂ => (x : ℂ) ^ (-z - 1))
        ((x : ℂ) ^ (-z - 1) * Complex.log x * (-1)) z :=
      ((hasDerivAt_id z).neg.sub_const 1).const_cpow (Or.inl hx0)
    have hlog : Complex.log (x : ℂ) = (Real.log x : ℂ) :=
      (Complex.ofReal_log (le_of_lt (lt_trans zero_lt_one hx))).symm
    have h2 := (hd.const_mul ((((-Real.log x) ^ k : ℝ) : ℂ))).mul_const (f x : ℂ)
    convert h2 using 1
    rw [hlog]
    push_cast
    ring

/-- As derivadas iteradas: `iteratedDeriv k (Ik f 0) = Ik f k` em `Re s > σ₀`. -/
theorem iteratedDeriv_Ik {f : ℝ → ℝ} {σ₀ : ℝ} (hf : Measurable f) (h : IntAcima f σ₀) (k : ℕ) :
    EqOn (iteratedDeriv k (Ik f 0)) (Ik f k) {s : ℂ | σ₀ < s.re} := by
  have hU : IsOpen {s : ℂ | σ₀ < s.re} := isOpen_lt continuous_const continuous_re
  induction k with
  | zero => intro s _; simp
  | succ k ih =>
    intro s hs
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (Ik f 0) =ᶠ[𝓝 s] Ik f k := by
      filter_upwards [hU.mem_nhds hs] with w hw using ih hw
    rw [hev.deriv_eq]
    exact (hasDerivAt_Ik hf h k hs).deriv

/-! ## 2. O teorema de Landau (Pringsheim) para `f ≥ 0` -/

theorem integrable_log_pow' {f : ℝ → ℝ} {σ₀ : ℝ} (hf : Measurable f) (hpos : ∀ x : ℝ, 1 < x → 0 ≤ f x)
    (h : IntAcima f σ₀) (k : ℕ) {σ : ℝ} (hσ : σ₀ < σ) :
    IntegrableOn (fun x => Real.log x ^ k * (x ^ (-σ - 1) * f x)) (Ioi 1) := by
  refine (integrable_log_pow hf h k hσ).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [abs_of_nonneg (hpos x hx)]; ring

/-- O termo `k` da série de Taylor em `c`, avaliado em `σ`: `((c − σ) log x)^k/k! · x^{−c−1} f(x)`. -/
noncomputable def termo (f : ℝ → ℝ) (c σ : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ((c - σ) * Real.log x) ^ k / (k ! : ℝ) * (x ^ (-c - 1) * f x)

theorem termo_nonneg {f : ℝ → ℝ} (hpos : ∀ x : ℝ, 1 < x → 0 ≤ f x) {c σ : ℝ} (hσ : σ ≤ c) (k : ℕ)
    {x : ℝ} (hx : 1 < x) : 0 ≤ termo f c σ k x := by
  unfold termo
  have h1 : 0 ≤ (c - σ) * Real.log x := mul_nonneg (by linarith) (Real.log_nonneg hx.le)
  have hx0 : 0 < x := by linarith
  exact mul_nonneg (div_nonneg (pow_nonneg h1 k) (Nat.cast_nonneg _))
    (mul_nonneg (Real.rpow_nonneg hx0.le _) (hpos x hx))

theorem measurable_termo {f : ℝ → ℝ} (hf : Measurable f) (c σ : ℝ) (k : ℕ) :
    Measurable (termo f c σ k) := by
  unfold termo; fun_prop

theorem integrable_termo {f : ℝ → ℝ} {σ₀ : ℝ} (hf : Measurable f) (hpos : ∀ x : ℝ, 1 < x → 0 ≤ f x)
    (h : IntAcima f σ₀) {c σ : ℝ} (hc : σ₀ < c) (k : ℕ) : IntegrableOn (termo f c σ k) (Ioi 1) := by
  have := (integrable_log_pow' hf hpos h k hc).const_mul ((c - σ) ^ k / (k ! : ℝ))
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [termo]
  rw [mul_pow]; ring

theorem hasSum_termo (f : ℝ → ℝ) (c σ : ℝ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun k => termo f c σ k x) (x ^ (-σ - 1) * f x) := by
  have he := NormedSpace.expSeries_div_hasSum_exp ((c - σ) * Real.log x)
  have hexp : Real.exp ((c - σ) * Real.log x) = NormedSpace.exp ((c - σ) * Real.log x) := by
    rw [Real.exp_eq_exp_ℝ]
  rw [← hexp] at he
  have h2 : x ^ (-σ - 1) = Real.exp ((c - σ) * Real.log x) * x ^ (-c - 1) := by
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx, ← Real.exp_add]
    congr 1; ring
  rw [h2, mul_assoc]
  exact he.mul_right _

theorem Ik_real {f : ℝ → ℝ} (k : ℕ) (c : ℝ) :
    Ik f k c = ((∫ x in Ioi 1, (-Real.log x) ^ k * (x ^ (-c - 1) * f x) : ℝ) : ℂ) := by
  rw [Ik, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) ≤ x := by
    have : (1 : ℝ) < x := hx
    linarith
  have e : (x : ℂ) ^ (-(c : ℂ) - 1) = ((x ^ (-c - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hx0]; push_cast; ring_nf
  rw [e]; push_cast; ring

theorem taylor_termo {f : ℝ → ℝ} (k : ℕ) (c σ : ℝ) :
    (k ! : ℂ)⁻¹ • ((σ : ℂ) - c) ^ k • Ik f k c = ((∫ x in Ioi 1, termo f c σ k x : ℝ) : ℂ) := by
  have h1 : (∫ x in Ioi 1, termo f c σ k x) =
      ((σ - c) ^ k / (k ! : ℝ)) * ∫ x in Ioi 1, (-Real.log x) ^ k * (x ^ (-c - 1) * f x) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    simp only [termo]
    rw [show (c - σ) * Real.log x = (σ - c) * (-Real.log x) by ring, mul_pow]
    ring
  rw [Ik_real, h1, smul_eq_mul, smul_eq_mul]
  push_cast
  ring

/-- **O teorema de Landau** (forma de Pringsheim, para transformadas de Mellin de `f ≥ 0`). Se `Φ` é holomorfa
no disco `|s − c| < r` e coincide com `Ik f 0` onde a integral converge, então `∫_{x>1} x^{−σ−1} f(x) dx`
converge para todo `σ ∈ (c − r, c]` e vale `Φ(σ)`: a integral de uma função positiva não pode parar antes
de uma singularidade no eixo real. -/
theorem landau {f : ℝ → ℝ} {σ₀ c r : ℝ} (hf : Measurable f) (hpos : ∀ x : ℝ, 1 < x → 0 ≤ f x)
    (h : IntAcima f σ₀) (hc : σ₀ < c) {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (ball (c : ℂ) r))
    (hEq : ∀ s : ℂ, s ∈ ball (c : ℂ) r → σ₀ < s.re → Φ s = Ik f 0 s) {σ : ℝ} (hσ1 : c - r < σ)
    (hσ2 : σ ≤ c) :
    IntegrableOn (fun x => x ^ (-σ - 1) * f x) (Ioi 1) ∧
      ((∫ x in Ioi 1, x ^ (-σ - 1) * f x : ℝ) : ℂ) = Φ σ := by
  have hσb : (σ : ℂ) ∈ ball (c : ℂ) r := by
    rw [mem_ball, dist_eq, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg (by linarith)]
    linarith
  have hT := Complex.hasSum_taylorSeries_on_ball hΦ hσb
  have hV : IsOpen (ball (c : ℂ) r ∩ {s : ℂ | σ₀ < s.re}) :=
    isOpen_ball.inter (isOpen_lt continuous_const continuous_re)
  have hcV : (c : ℂ) ∈ ball (c : ℂ) r ∩ {s : ℂ | σ₀ < s.re} :=
    ⟨mem_ball_self (by linarith), by show σ₀ < (c : ℂ).re; simpa using hc⟩
  have hEqV : EqOn Φ (Ik f 0) (ball (c : ℂ) r ∩ {s : ℂ | σ₀ < s.re}) := fun s hs => hEq s hs.1 hs.2
  have hder : ∀ k, iteratedDeriv k Φ c = Ik f k c := fun k => by
    rw [hEqV.iteratedDeriv_of_isOpen hV k hcV]
    exact iteratedDeriv_Ik hf h k (show σ₀ < (c : ℂ).re by simpa using hc)
  set a : ℕ → ℝ := fun k => ∫ x in Ioi 1, termo f c σ k x with ha
  have hfun : (fun k : ℕ => (k ! : ℂ)⁻¹ • ((σ : ℂ) - c) ^ k • iteratedDeriv k Φ c) =
      fun k => (a k : ℂ) := funext fun k => by rw [hder k]; exact taylor_termo k c σ
  rw [hfun] at hT
  have ha0 : ∀ k, 0 ≤ a k := fun k =>
    setIntegral_nonneg measurableSet_Ioi fun x hx => termo_nonneg hpos hσ2 k hx
  have hre : HasSum a (Φ σ).re := by
    have := Complex.reCLM.hasSum hT
    simpa using this
  have hΦr : ((Φ σ).re : ℂ) = Φ σ := ((Complex.hasSum_ofReal).mpr hre).unique hT
  have hmeas : ∀ k, AEMeasurable (fun x => ENNReal.ofReal (termo f c σ k x)) (volume.restrict (Ioi 1)) :=
    fun k => (measurable_termo hf c σ k).ennreal_ofReal.aemeasurable
  have hlin : ∫⁻ x in Ioi 1, ENNReal.ofReal (x ^ (-σ - 1) * f x) = ENNReal.ofReal ((Φ σ).re) := by
    calc ∫⁻ x in Ioi 1, ENNReal.ofReal (x ^ (-σ - 1) * f x)
        = ∫⁻ x in Ioi 1, ∑' k, ENNReal.ofReal (termo f c σ k x) := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
          have hx' : (1 : ℝ) < x := hx
          have hs := hasSum_termo f c σ (lt_trans zero_lt_one hx')
          rw [← hs.tsum_eq]
          exact ENNReal.ofReal_tsum_of_nonneg (fun k => termo_nonneg hpos hσ2 k hx') hs.summable
      _ = ∑' k, ∫⁻ x in Ioi 1, ENNReal.ofReal (termo f c σ k x) := lintegral_tsum hmeas
      _ = ∑' k, ENNReal.ofReal (a k) := by
          congr 1; funext k
          refine (ofReal_integral_eq_lintegral_ofReal (integrable_termo hf hpos h hc k) ?_).symm
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using termo_nonneg hpos hσ2 k hx
      _ = ENNReal.ofReal ((Φ σ).re) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg ha0 hre.summable, hre.tsum_eq]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 1)] fun x => x ^ (-σ - 1) * f x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : (1 : ℝ) < x := hx
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (hpos x hx')
  have hint : IntegrableOn (fun x => x ^ (-σ - 1) * f x) (Ioi 1) := by
    refine ⟨(by fun_prop : Measurable fun x => x ^ (-σ - 1) * f x).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn, hlin]
    exact ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hint.aestronglyMeasurable, hlin,
    ENNReal.toReal_ofReal (hre.nonneg ha0)]
  exact hΦr

/-- Onde as integrais `x^{−σ−1}f` convergem para todo `σ > θ`, `Ik f 0` é holomorfa em `Re s > θ`. -/
theorem differentiableAt_Ik {f : ℝ → ℝ} {θ : ℝ} (hf : Measurable f) (h : IntAcima f θ) {s : ℂ}
    (hs : θ < s.re) : DifferentiableAt ℂ (Ik f 0) s :=
  (hasDerivAt_Ik hf h 0 hs).differentiableAt

/-! ## 3. A função escada `a(⌊x⌋)` e a série de Abel -/

open ATK.ZeroClasses.VonKoch (gA GA summable_gA C_nonneg)

theorem floor_eq_of_mem {n : ℕ} {x : ℝ} (hx : x ∈ Ico ((n : ℝ) + 1) ((n : ℝ) + 2)) : ⌊x⌋₊ = n + 1 := by
  have h0 : (0 : ℝ) ≤ x := by linarith [hx.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [Nat.floor_eq_iff h0]
  push_cast
  exact ⟨hx.1, by linarith [hx.2]⟩

theorem iUnion_Ico : (⋃ n : ℕ, Ico ((n : ℝ) + 1) ((n : ℝ) + 2)) = Ici 1 := by
  ext x
  simp only [mem_iUnion, mem_Ico, mem_Ici]
  constructor
  · rintro ⟨n, h1, _⟩
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · intro hx
    have h0 : (0 : ℝ) ≤ x := by linarith
    have h1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    refine ⟨⌊x⌋₊ - 1, ?_, ?_⟩
    · rw [Nat.cast_sub h1]; push_cast
      linarith [Nat.floor_le h0]
    · rw [Nat.cast_sub h1]; push_cast
      linarith [Nat.lt_floor_add_one x]

theorem disjoint_Ico :
    Pairwise (Function.onFun Disjoint fun n : ℕ => Ico ((n : ℝ) + 1) ((n : ℝ) + 2)) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  intro x hm hn
  have := (floor_eq_of_mem hm).symm.trans (floor_eq_of_mem hn)
  exact hmn (by omega)

theorem integral_Ico_cpow (n : ℕ) {s : ℂ} (hs : s ≠ 0) :
    ∫ x in Ico ((n : ℝ) + 1) ((n : ℝ) + 2), (x : ℂ) ^ (-s - 1) =
      (((n : ℂ) + 1) ^ (-s) - ((n : ℂ) + 2) ^ (-s)) / s := by
  have hle : (n : ℝ) + 1 ≤ (n : ℝ) + 2 := by linarith
  rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle]
  have hr : -s - 1 ≠ -1 := by
    intro h; apply hs; linear_combination -h
  have h0 : (0 : ℝ) ∉ uIcc ((n : ℝ) + 1) ((n : ℝ) + 2) := by
    rw [Set.uIcc_of_le hle]
    intro h
    linarith [h.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [integral_cpow (Or.inr ⟨hr, h0⟩)]
  rw [show -s - 1 + 1 = -s by ring]
  push_cast
  field_simp
  ring

theorem aesm_escada (a : ℕ → ℝ) (s : ℂ) (t : Set ℝ) (ht : MeasurableSet t) (ht1 : t ⊆ Ici 1) :
    AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ (-s - 1) * (a ⌊x⌋₊ : ℂ)) (volume.restrict t) := by
  refine AEStronglyMeasurable.mul ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ ht
    refine continuousOn_of_forall_continuousAt fun x hx => ?_
    have : (1 : ℝ) ≤ x := ht1 hx
    exact continuousAt_ofReal_cpow_const _ _ (Or.inr (by linarith))
  · exact (Complex.measurable_ofReal.comp ((measurable_from_nat (f := a)).comp
      Nat.measurable_floor)).aestronglyMeasurable

theorem integrable_escada {a : ℕ → ℝ} {C : ℝ} (hC : ∀ N : ℕ, |a N| ≤ C * ((N : ℝ) + 1)) {s : ℂ}
    (hs : 1 < s.re) : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * (a ⌊x⌋₊ : ℂ)) (Ici 1) := by
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [Nat.cast_zero, zero_add, mul_one] at this
    exact le_trans (abs_nonneg _) this
  have hb := (integrableOn_Ioi_rpow_of_lt (show -s.re < -1 by linarith) zero_lt_one).const_mul (2 * C)
  have hb' : IntegrableOn (fun x : ℝ => 2 * C * x ^ (-s.re)) (Ici 1) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hb
  refine hb'.mono' (aesm_escada a s _ measurableSet_Ici subset_rfl) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  have hx1 : (1 : ℝ) ≤ x := hx
  have hx0 : 0 < x := by linarith
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs]
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have h1 := hC ⌊x⌋₊
  have h2 : |a ⌊x⌋₊| ≤ 2 * C * x := by nlinarith
  have hre : (-s - 1).re = -s.re - 1 := by simp
  rw [hre]
  calc x ^ (-s.re - 1) * |a ⌊x⌋₊| ≤ x ^ (-s.re - 1) * (2 * C * x) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hx0.le _)
    _ = 2 * C * x ^ (-s.re) := by
        rw [Real.rpow_sub_one hx0.ne']
        field_simp

/-- **A série de Abel como transformada de Mellin**: `∫_{x>1} x^{−s−1} a(⌊x⌋) dx = GA a(s)/s` em `Re s > 1`. -/
theorem integral_escada {a : ℕ → ℝ} {C : ℝ} (hC : ∀ N : ℕ, |a N| ≤ C * ((N : ℝ) + 1)) {s : ℂ}
    (hs : 1 < s.re) : ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (-s - 1) * (a ⌊x⌋₊ : ℂ) = GA a s / s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  rw [← integral_Ici_eq_integral_Ioi, ← iUnion_Ico]
  have hsum := hasSum_integral_iUnion (fun n => measurableSet_Ico) disjoint_Ico
    (by rw [iUnion_Ico]; exact integrable_escada hC hs)
  have hpiece : ∀ n : ℕ, ∫ x in Ico ((n : ℝ) + 1) ((n : ℝ) + 2), (x : ℂ) ^ (-s - 1) * (a ⌊x⌋₊ : ℂ) =
      gA a n s / s := fun n => by
    rw [setIntegral_congr_fun measurableSet_Ico (fun x hx => by rw [floor_eq_of_mem hx]),
      integral_mul_const, integral_Ico_cpow n hs0]
    unfold gA
    ring
  simp only [hpiece] at hsum
  rw [GA, ← tsum_div_const, hsum.tsum_eq]

/-- Abel com `|A(N)| ≤ C(N + 1)^θ` e `θ < Re z` (sem exigir `θ < 1`). -/
theorem GA_eq_LSeries' {c : ℕ → ℂ} {A : ℕ → ℝ} {C θ : ℝ} (hθ : 0 ≤ θ)
    (hC : ∀ N : ℕ, |A N| ≤ C * ((N : ℝ) + 1) ^ θ)
    (hA : ∀ n : ℕ, ((A (n + 1) : ℝ) : ℂ) = ∑ k ∈ Finset.range (n + 1), c (k + 1))
    {z : ℂ} (hz : θ < z.re) (hL : LSeriesSummable c z) : GA A z = LSeries c z := by
  have hsum := summable_gA hθ hC hz
  have hP : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), c (n + 1) * ((n : ℂ) + 1) ^ (-z)) atTop
      (𝓝 (LSeries c z)) := by
    have h := hL.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)
    refine h.congr fun N => ?_
    simp only [Function.comp_apply]
    rw [show N + 2 = (N + 1) + 1 by ring, Finset.sum_range_succ']
    simp only [LSeries.term_zero, add_zero]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), cpow_neg, div_eq_mul_inv]
    push_cast
    ring
  have hab : ∀ N : ℕ, ∑ n ∈ Finset.range (N + 1), c (n + 1) * ((n : ℂ) + 1) ^ (-z) =
      ((A (N + 1) : ℝ) : ℂ) * ((N : ℂ) + 1) ^ (-z) + ∑ n ∈ Finset.range N, gA A n z := by
    intro N
    rw [ATK.ZeroClasses.Mertens.abel (fun n => c (n + 1)) (fun n => ((n : ℂ) + 1) ^ (-z)) N, ← hA]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold gA
    rw [← hA]
    push_cast
    ring_nf
  have hbd : Tendsto (fun N : ℕ => ((A (N + 1) : ℝ) : ℂ) * ((N : ℂ) + 1) ^ (-z)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Tendsto (fun N : ℕ => C * 2 ^ θ * ((N : ℝ) + 1) ^ (-(z.re - θ))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      have := ((tendsto_rpow_neg_atTop (show 0 < z.re - θ by linarith)).comp h1).const_mul (C * 2 ^ θ)
      simpa using this
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hlim
    have hn1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
    have hC0 := C_nonneg hC
    have hM := hC (N + 1)
    have h2 : ((N + 1 : ℕ) : ℝ) + 1 ≤ 2 * ((N : ℝ) + 1) := by push_cast; linarith
    have hpow : (((N + 1 : ℕ) : ℝ) + 1) ^ θ ≤ 2 ^ θ * ((N : ℝ) + 1) ^ θ := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)]
      exact Real.rpow_le_rpow (by positivity) h2 hθ
    have e : ((N : ℂ) + 1) = (((N : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, e, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith),
      neg_re]
    have hsplit : ((N : ℝ) + 1) ^ θ * ((N : ℝ) + 1) ^ (-z.re) = ((N : ℝ) + 1) ^ (-(z.re - θ)) := by
      rw [← Real.rpow_add (by linarith)]; ring_nf
    calc |A (N + 1)| * ((N : ℝ) + 1) ^ (-z.re)
        ≤ (C * (2 ^ θ * ((N : ℝ) + 1) ^ θ)) * ((N : ℝ) + 1) ^ (-z.re) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact hM.trans (mul_le_mul_of_nonneg_left hpow hC0)
      _ = C * 2 ^ θ * (((N : ℝ) + 1) ^ θ * ((N : ℝ) + 1) ^ (-z.re)) := by ring
      _ = C * 2 ^ θ * ((N : ℝ) + 1) ^ (-(z.re - θ)) := by rw [hsplit]
  have hG : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, gA A n z) atTop (𝓝 (GA A z)) :=
    hsum.hasSum.tendsto_sum_nat
  have hlim2 := hbd.add hG
  rw [zero_add] at hlim2
  exact tendsto_nhds_unique (hlim2.congr fun N => (hab N).symm) hP

/-! ## 4. Uma cota de um lado só estende a série de Abel até `Re s > θ` -/

/-- `f(x) = A x^θ + K − a(⌊x⌋)`: positiva quando `a(N) ≤ A(N + 1)^θ + K`. -/
noncomputable def fUni (a : ℕ → ℝ) (A K θ : ℝ) (x : ℝ) : ℝ := A * x ^ θ + K - a ⌊x⌋₊

theorem measurable_fUni (a : ℕ → ℝ) (A K θ : ℝ) : Measurable (fUni a A K θ) := by
  have hfl : Measurable fun x : ℝ => a ⌊x⌋₊ := (measurable_from_nat (f := a)).comp Nat.measurable_floor
  exact ((measurable_const.mul (measurable_id.pow_const θ)).add measurable_const).sub hfl

theorem fUni_nonneg {a : ℕ → ℝ} {A K θ : ℝ} (hθ : 0 ≤ θ) (hA : 0 ≤ A)
    (h : ∀ N : ℕ, a N ≤ A * ((N : ℝ) + 1) ^ θ + K) {x : ℝ} (hx : 1 < x) :
    0 ≤ fUni a (A * 2 ^ θ) K θ x := by
  unfold fUni
  have hx0 : 0 < x := by linarith
  have hfl : (⌊x⌋₊ : ℝ) + 1 ≤ 2 * x := by linarith [Nat.floor_le hx0.le]
  have h1 := h ⌊x⌋₊
  have h2 : ((⌊x⌋₊ : ℝ) + 1) ^ θ ≤ (2 * x) ^ θ := Real.rpow_le_rpow (by positivity) hfl hθ
  rw [Real.mul_rpow (by norm_num) hx0.le] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 hA
  linarith

theorem intAcima_fUni {a : ℕ → ℝ} {C A K θ : ℝ} (hθ1 : θ ≤ 1)
    (hC : ∀ N : ℕ, |a N| ≤ C * ((N : ℝ) + 1)) : IntAcima (fUni a A K θ) 1 := by
  intro σ hσ
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [Nat.cast_zero, zero_add, mul_one] at this
    exact le_trans (abs_nonneg _) this
  have hb := (integrableOn_Ioi_rpow_of_lt (show -σ < -1 by linarith) zero_lt_one).const_mul
    (|A| + |K| + 2 * C)
  refine hb.mono' ((measurable_id.pow_const _).mul
    (measurable_fUni a A K θ).abs).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx1 : (1 : ℝ) < x := hx
  have hx0 : 0 < x := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (abs_nonneg _))]
  have hxθ : x ^ θ ≤ x := by simpa using Real.rpow_le_rpow_of_exponent_le hx1.le hθ1
  have hxθ0 : 0 ≤ x ^ θ := Real.rpow_nonneg hx0.le _
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have h1 := hC ⌊x⌋₊
  have hf : |fUni a A K θ x| ≤ (|A| + |K| + 2 * C) * x := by
    unfold fUni
    have e1 : |A * x ^ θ| = |A| * x ^ θ := by rw [abs_mul, abs_of_nonneg hxθ0]
    have t1 := abs_sub (A * x ^ θ + K) (a ⌊x⌋₊)
    have t2 := abs_add_le (A * x ^ θ) K
    have t3 : |A| * x ^ θ ≤ |A| * x := mul_le_mul_of_nonneg_left hxθ (abs_nonneg _)
    have t4 : |K| ≤ |K| * x := le_mul_of_one_le_right (abs_nonneg _) hx1.le
    have t5 : C * ((⌊x⌋₊ : ℝ) + 1) ≤ 2 * C * x := by nlinarith
    nlinarith
  calc x ^ (-σ - 1) * |fUni a A K θ x| ≤ x ^ (-σ - 1) * ((|A| + |K| + 2 * C) * x) :=
        mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg hx0.le _)
    _ = (|A| + |K| + 2 * C) * x ^ (-σ) := by
        rw [Real.rpow_sub_one hx0.ne']
        field_simp

/-- Em `Re s > 1`: `Ik f 0 s = A/(s − θ) + K/s − GA a(s)/s`. -/
theorem Ik_fUni {a : ℕ → ℝ} {C A K θ : ℝ} (hθ1 : θ ≤ 1) (hC : ∀ N : ℕ, |a N| ≤ C * ((N : ℝ) + 1))
    {s : ℂ} (hs : 1 < s.re) : Ik (fUni a A K θ) 0 s = A / (s - θ) + K / s - GA a s / s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  have hsθ : s - θ ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp only [sub_re, ofReal_re, zero_re] at this
    linarith
  have hcongr : ∀ x ∈ Ioi (1 : ℝ), (((-Real.log x) ^ 0 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) *
      ((fUni a A K θ x : ℝ) : ℂ) = (A : ℂ) * (x : ℂ) ^ (-s - 1 + θ) + (K : ℂ) * (x : ℂ) ^ (-s - 1) -
        (x : ℂ) ^ (-s - 1) * (a ⌊x⌋₊ : ℂ) := by
    intro x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [cpow_add _ _ (ofReal_ne_zero.mpr hx0.ne'), ← Complex.ofReal_cpow hx0.le θ]
    unfold fUni
    push_cast
    ring
  have h1 : (-s - 1 + θ).re < -1 := by simp; linarith
  have h2 : (-s - 1).re < -1 := by simp; linarith
  have i1 : IntegrableOn (fun x : ℝ => (A : ℂ) * (x : ℂ) ^ (-s - 1 + θ)) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt h1 zero_lt_one).const_mul _
  have i2 : IntegrableOn (fun x : ℝ => (K : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt h2 zero_lt_one).const_mul _
  have i3 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) * (a ⌊x⌋₊ : ℂ)) (Ioi 1) :=
    (integrable_escada hC hs).mono_set Ioi_subset_Ici_self
  have i12 : IntegrableOn (fun x : ℝ => (A : ℂ) * (x : ℂ) ^ (-s - 1 + θ) + (K : ℂ) * (x : ℂ) ^ (-s - 1))
      (Ioi 1) := i1.add i2
  unfold Ik
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_sub i12 i3, integral_add i1 i2,
    integral_const_mul, integral_const_mul, integral_Ioi_cpow_of_lt h1 zero_lt_one,
    integral_Ioi_cpow_of_lt h2 zero_lt_one, integral_escada hC hs]
  simp only [ofReal_one, one_cpow]
  rw [show -s - 1 + θ + 1 = -(s - θ) by ring, show -s - 1 + 1 = -s by ring]
  field_simp


/-- O coeficiente `A′ = max(A, 0)·2^θ`. -/
noncomputable def Al (A θ : ℝ) : ℝ := max A 0 * 2 ^ θ

theorem Al_nonneg (A θ : ℝ) : 0 ≤ Al A θ := mul_nonneg (le_max_right A 0) (by positivity)

theorem pos_uni {a : ℕ → ℝ} {A K θ : ℝ} (hθ : 0 ≤ θ) (hA : ∀ N : ℕ, a N ≤ A * ((N : ℝ) + 1) ^ θ + K)
    {x : ℝ} (hx : 1 < x) : 0 ≤ fUni a (Al A θ) K θ x := by
  have hA0 : ∀ N : ℕ, a N ≤ max A 0 * ((N : ℝ) + 1) ^ θ + K := fun N => by
    have h1 := hA N
    have h2 : A * ((N : ℝ) + 1) ^ θ ≤ max A 0 * ((N : ℝ) + 1) ^ θ :=
      mul_le_mul_of_nonneg_right (le_max_left A 0) (Real.rpow_nonneg (by positivity) _)
    linarith
  exact fUni_nonneg hθ (le_max_right A 0) hA0 hx

theorem re_gt_of_mem_ball {θ : ℝ} {s : ℂ} (hs : s ∈ ball (2 : ℂ) (2 - θ)) : θ < s.re := by
  rw [mem_ball, dist_eq] at hs
  have := abs_re_le_norm (s - 2)
  rw [sub_re, show (2 : ℂ).re = 2 by norm_num] at this
  linarith [(abs_lt.mp (lt_of_le_of_lt this hs)).1]

/-- **O passo de Landau**: com `|a(N)| ≤ C(N + 1)`, `a(N) ≤ A(N + 1)^θ + K` (`0 ≤ θ < 1`) e `GA a = H` em
`Re s > 1` com `H` holomorfa no disco `|s − 2| < 2 − θ`, as integrais `∫_{x>1} x^{−σ−1} f(x) dx` de
`f = A′x^θ + K − a(⌊x⌋) ≥ 0` convergem para todo `σ > θ`. -/
theorem intAcima_uni {a : ℕ → ℝ} {C A K θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hC : ∀ N : ℕ, |a N| ≤ C * ((N : ℝ) + 1)) (hA : ∀ N : ℕ, a N ≤ A * ((N : ℝ) + 1) ^ θ + K)
    {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H (ball (2 : ℂ) (2 - θ)))
    (hHG : ∀ s : ℂ, 1 < s.re → GA a s = H s) : IntAcima (fUni a (Al A θ) K θ) θ := by
  set A' := Al A θ with hA'
  set f := fUni a A' K θ with hfdef
  have hf : Measurable f := measurable_fUni a A' K θ
  have hpos : ∀ x : ℝ, 1 < x → 0 ≤ f x := fun x hx => pos_uni hθ hA hx
  have h1 : IntAcima f 1 := intAcima_fUni hθ1.le hC
  have e2 : ((2 : ℝ) : ℂ) = 2 := by norm_num
  set Φ : ℂ → ℂ := fun s => A' / (s - θ) + K / s - H s / s with hΦdef
  have hΦ : DifferentiableOn ℂ Φ (ball (2 : ℂ) (2 - θ)) := by
    intro s hs
    have hre := re_gt_of_mem_ball hs
    have hsθ : s - θ ≠ 0 := fun h => by
      have := congrArg Complex.re h
      simp only [sub_re, ofReal_re, zero_re] at this
      linarith
    have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hre; linarith
    have d1 : DifferentiableAt ℂ (fun w : ℂ => (A' : ℂ) / (w - θ)) s :=
      (differentiableAt_const _).div (differentiableAt_id.sub (differentiableAt_const _)) hsθ
    have d2 : DifferentiableAt ℂ (fun w : ℂ => (K : ℂ) / w) s :=
      (differentiableAt_const _).div differentiableAt_id hs0
    have d3 : DifferentiableAt ℂ (fun w : ℂ => H w / w) s :=
      (hH.differentiableAt (isOpen_ball.mem_nhds hs)).div differentiableAt_id hs0
    exact ((d1.add d2).sub d3).differentiableWithinAt
  have hEq : ∀ s : ℂ, s ∈ ball ((2 : ℝ) : ℂ) (2 - θ) → 1 < s.re → Φ s = Ik f 0 s := fun s _ h1s => by
    rw [hfdef, Ik_fUni hθ1.le hC h1s, hHG s h1s]
  have hL : ∀ σ : ℝ, θ < σ → σ ≤ 2 → IntegrableOn (fun x => x ^ (-σ - 1) * f x) (Ioi 1) :=
    fun σ hσ1 hσ2 => (landau hf hpos h1 (by norm_num : (1 : ℝ) < 2) (by rw [e2]; exact hΦ) hEq
      (by linarith) hσ2).1
  intro σ hσ
  rcases le_or_gt σ 2 with h2 | h2
  · refine (hL σ hσ h2).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [abs_of_nonneg (hpos x hx)]
  · exact h1 σ (by linarith)

/-- A extensão explícita: `G(s) = s (A′/(s − θ) + K/s − Ik f 0 s)`. -/
noncomputable def Gext (a : ℕ → ℝ) (A K θ : ℝ) (s : ℂ) : ℂ :=
  s * ((Al A θ : ℂ) / (s - θ) + K / s - Ik (fUni a (Al A θ) K θ) 0 s)

theorem Gext_eq {a : ℕ → ℝ} {C A K θ : ℝ} (hθ1 : θ ≤ 1) (hC : ∀ N : ℕ, |a N| ≤ C * ((N : ℝ) + 1))
    {s : ℂ} (hs : 1 < s.re) : Gext a A K θ s = GA a s := by
  have hs0 : s ≠ 0 := fun h => by rw [h, zero_re] at hs; linarith
  unfold Gext
  rw [Ik_fUni hθ1 hC hs]
  field_simp
  ring

/-- **A extensão**: nas hipóteses de `intAcima_uni`, `GA a` tem extensão holomorfa `Gext` a `Re s > θ`. -/
theorem extensao {a : ℕ → ℝ} {C A K θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hC : ∀ N : ℕ, |a N| ≤ C * ((N : ℝ) + 1)) (hA : ∀ N : ℕ, a N ≤ A * ((N : ℝ) + 1) ^ θ + K)
    {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H (ball (2 : ℂ) (2 - θ)))
    (hHG : ∀ s : ℂ, 1 < s.re → GA a s = H s) :
    ∃ G : ℂ → ℂ, (∀ s : ℂ, θ < s.re → DifferentiableAt ℂ G s) ∧ ∀ s : ℂ, 1 < s.re → G s = GA a s := by
  have hIθ := intAcima_uni hθ hθ1 hC hA hH hHG
  have hf := measurable_fUni a (Al A θ) K θ
  refine ⟨Gext a A K θ, fun s hs => ?_, fun s hs => Gext_eq hθ1.le hC hs⟩
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

/-! ## 5. `ψ` e `M`: cotas de um lado só dão semiplanos sem zeros -/

open ATK.ZeroClasses.VonKoch (cL E E_succ LSeries_cL LSeriesSummable_cL zero_de_edo)
open ATK.ZeroClasses.VonKochRH (Hf Hf_eq)
open ATK.ZeroClasses.QuasiRH (SemZeros)
open ATK.ZeroClasses.Mertens (M M_succ_eq)
open ATK.ZeroClasses.LittlewoodMu (mu norm_mu_le LSeries_mu)
open ATK.RHLogZeta (F zeta₁_eq)

theorem abs_E_le (N : ℕ) : |E N| ≤ (Real.log 4 + 4) * ((N : ℝ) + 1) := by
  unfold E
  have h0 : 0 ≤ Chebyshev.psi N := Chebyshev.psi_nonneg _
  have h1 : Chebyshev.psi N ≤ (Real.log 4 + 4) * N := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg N)
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_M_le (N : ℕ) : |M N| ≤ 1 * ((N : ℝ) + 1) := by
  unfold M
  calc |∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.moebius n : ℝ)|
      ≤ ∑ n ∈ Finset.range (N + 1), |(ArithmeticFunction.moebius n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range (N + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = 1 * ((N : ℝ) + 1) := by simp

/-- `ζ₁ ≠ 0` no disco `|s − 2| < 2` (`Re s > 0`, `|Im s| < 2`; os zeros não triviais têm `|Im ρ| > 13`). -/
theorem zeta₁_ne_zero_bola {s : ℂ} (hs : s ∈ ball (2 : ℂ) 2) : riemannZeta₁ s ≠ 0 := by
  rw [mem_ball, dist_eq] at hs
  have hre : 0 < s.re := by
    have := abs_re_le_norm (s - 2)
    rw [sub_re, show (2 : ℂ).re = 2 by norm_num] at this
    linarith [(abs_lt.mp (lt_of_le_of_lt this hs)).1]
  have him : |s.im| ≤ 13 := by
    have := abs_im_le_norm (s - 2)
    rw [sub_im, show (2 : ℂ).im = 0 by norm_num, sub_zero] at this
    linarith
  by_cases hs1 : s = 1
  · subst hs1; rw [riemannZeta₁_one]; exact one_ne_zero
  rw [zeta₁_eq hs1]
  refine mul_ne_zero (sub_ne_zero.mpr hs1) ?_
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · exact ATK.ZeroClasses.Faixa.faixa_sem_zeros hre h1 him

theorem differentiableOn_Hf {θ : ℝ} (hθ : 0 ≤ θ) : DifferentiableOn ℂ Hf (ball (2 : ℂ) (2 - θ)) := by
  intro s hs
  have h1 := zeta₁_ne_zero_bola (ball_subset_ball (by linarith) hs)
  have hd : DifferentiableAt ℂ (deriv riemannZeta₁) s :=
    (differentiable_riemannZeta₁.analyticAt s).deriv.differentiableAt
  exact ((hd.neg.div (differentiable_riemannZeta₁ s) h1).sub
    (differentiable_riemannZeta₀ s)).differentiableWithinAt

theorem differentiableOn_F {θ : ℝ} (hθ : 0 ≤ θ) : DifferentiableOn ℂ F (ball (2 : ℂ) (2 - θ)) :=
  fun s hs => ((differentiableAt_id.sub (differentiableAt_const _)).div (differentiable_riemannZeta₁ s)
    (zeta₁_ne_zero_bola (ball_subset_ball (by linarith) hs))).differentiableWithinAt

theorem GA_E_eq {s : ℂ} (hs : 1 < s.re) : GA E s = Hf s := by
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; exact lt_irrefl 1 hs
  rw [GA_eq_LSeries' (θ := 1) (C := Real.log 4 + 4) zero_le_one
    (fun N => by rw [Real.rpow_one]; exact abs_E_le N) E_succ hs (LSeriesSummable_cL hs), LSeries_cL hs,
    Hf_eq hs1 (riemannZeta_ne_zero_of_one_lt_re hs)]

theorem GA_M_eq {s : ℂ} (hs : 1 < s.re) : GA M s = F s := by
  have hL : LSeriesSummable mu s := LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_mu_le n) hs
  rw [GA_eq_LSeries' (θ := 1) (C := 1) zero_le_one (fun N => by rw [Real.rpow_one]; exact abs_M_le N)
    M_succ_eq hs hL, LSeries_mu hs]

theorem GA_neg (a : ℕ → ℝ) (s : ℂ) : GA (fun N => -a N) s = -GA a s := by
  unfold GA gA
  rw [← tsum_neg]
  congr 1
  funext n
  push_cast
  ring

/-- Se `−ζ′/ζ − ζ` tem extensão holomorfa a `Re s > θ`, não há zeros em `Re s > θ` (o argumento da rodada 55,
`VonKoch.zeroFree_of_psi`, com a extensão no lugar da série). -/
theorem semZeros_of_ext_psi {θ : ℝ} {G : ℂ → ℂ} (hG : ∀ s : ℂ, θ < s.re → DifferentiableAt ℂ G s)
    (hGE : ∀ s : ℂ, 1 < s.re → G s = Hf s) : SemZeros θ := by
  intro s hs
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  intro hz
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at h1; exact lt_irrefl 1 h1
  have hV : IsOpen {w : ℂ | θ < w.re} := isOpen_lt continuous_const continuous_re
  have hVc : IsPreconnected {w : ℂ | θ < w.re} := (convex_halfSpace_re_gt θ).isPreconnected
  have hZ : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hL : AnalyticOnNhd ℂ (fun w => (w - 1) * deriv riemannZeta₁ w) {w : ℂ | θ < w.re} := by
    refine DifferentiableOn.analyticOnNhd (fun w _ => ?_) hV
    exact ((differentiableAt_id.sub (differentiableAt_const 1)).mul
      (hZ.analyticAt w).deriv.differentiableAt).differentiableWithinAt
  have hR : AnalyticOnNhd ℂ (fun w => riemannZeta₁ w * (1 - riemannZeta₁ w - (w - 1) * G w))
      {w : ℂ | θ < w.re} := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hV
    exact ((hZ w).mul (((differentiableAt_const 1).sub (hZ w)).sub
      ((differentiableAt_id.sub (differentiableAt_const 1)).mul (hG w hw)))).differentiableWithinAt
  have hev : (fun w => (w - 1) * deriv riemannZeta₁ w) =ᶠ[𝓝 (2 : ℂ)]
      fun w => riemannZeta₁ w * (1 - riemannZeta₁ w - (w - 1) * G w) := by
    have hmem : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by show (1 : ℝ) < (2 : ℂ).re; norm_num)
    filter_upwards [hmem] with w hw
    have hw' : 1 < w.re := hw
    have hw1 : w ≠ 1 := fun h => by rw [h, one_re] at hw'; exact lt_irrefl 1 hw'
    have hz1 : riemannZeta₁ w ≠ 0 := by
      rw [zeta₁_eq hw1]
      exact mul_ne_zero (sub_ne_zero.mpr hw1) (riemannZeta_ne_zero_of_one_lt_re hw')
    rw [hGE w hw']
    unfold Hf
    have e1 : riemannZeta₁ w * (deriv riemannZeta₁ w / riemannZeta₁ w) = deriv riemannZeta₁ w :=
      mul_div_cancel₀ _ hz1
    have e2 : riemannZeta₁ w = 1 + (w - 1) * riemannZeta₀ w := rfl
    linear_combination (-(w - 1)) * e1 + riemannZeta₁ w * e2
  have h2V : (2 : ℂ) ∈ {w : ℂ | θ < w.re} := by
    show θ < (2 : ℂ).re
    norm_num; linarith
  have hid := hL.eqOn_of_preconnected_of_eventuallyEq hR hVc h2V hev
  have hsV : s ∈ {w : ℂ | θ < w.re} := hs
  have hz1 : riemannZeta₁ s = 0 := by rw [zeta₁_eq hs1, hz, mul_zero]
  have hloc : ∀ᶠ w in 𝓝 s, riemannZeta₁ w = 0 := by
    refine zero_de_edo (q := fun w => w - 1) (P := fun w => 1 - riemannZeta₁ w - (w - 1) * G w)
      (hZ.analyticAt s) ?_ (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hs1) hz1 ?_
    · exact (((differentiableAt_const 1).sub (hZ s)).sub ((differentiableAt_id.sub
        (differentiableAt_const 1)).mul (hG s hs))).continuousAt
    · filter_upwards [hV.mem_nhds hsV] with w hw
      exact hid hw
  have hAu : AnalyticOnNhd ℂ riemannZeta₁ univ := fun z _ => hZ.analyticAt z
  have hall := hAu.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ s) hloc
  have h2 := hall (mem_univ (2 : ℂ))
  simp only [Pi.zero_apply] at h2
  rw [zeta₁_eq (by norm_num)] at h2
  have h21 : (2 : ℂ) - 1 ≠ 0 := by norm_num
  exact riemannZeta_ne_zero_of_one_lt_re (s := 2) (by norm_num) ((mul_eq_zero.mp h2).resolve_left h21)

/-- Se `1/ζ` tem extensão holomorfa a `Re s > θ`, não há zeros em `Re s > θ`. -/
theorem semZeros_of_ext_mertens {θ : ℝ} {G : ℂ → ℂ} (hG : ∀ s : ℂ, θ < s.re → DifferentiableAt ℂ G s)
    (hGF : ∀ s : ℂ, 1 < s.re → G s = F s) : SemZeros θ := by
  intro s hs
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  intro hz
  have hV : IsOpen {w : ℂ | θ < w.re} := isOpen_lt continuous_const continuous_re
  have hA : AnalyticOnNhd ℂ (fun w => riemannZeta₁ w * G w - (w - 1)) {w : ℂ | θ < w.re} := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hV
    exact (((differentiable_riemannZeta₁ w).mul (hG w hw)).sub
      (differentiableAt_id.sub (differentiableAt_const 1))).differentiableWithinAt
  have hev : (fun w => riemannZeta₁ w * G w - (w - 1)) =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hmem : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by show (1 : ℝ) < (2 : ℂ).re; norm_num)
    filter_upwards [hmem] with w hw
    have hw' : 1 < w.re := hw
    have hw1 : w ≠ 1 := fun h => by rw [h, one_re] at hw'; exact lt_irrefl 1 hw'
    have hz1 : riemannZeta₁ w ≠ 0 := by
      rw [zeta₁_eq hw1]
      exact mul_ne_zero (sub_ne_zero.mpr hw1) (riemannZeta_ne_zero_of_one_lt_re hw')
    rw [hGF w hw']
    simp only [Pi.zero_apply, F]
    rw [mul_div_cancel₀ _ hz1, sub_self]
  have h2V : (2 : ℂ) ∈ {w : ℂ | θ < w.re} := by
    show θ < (2 : ℂ).re
    norm_num; linarith
  have hzero := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_halfSpace_re_gt θ).isPreconnected h2V hev
  have h0 := hzero (show s ∈ {w : ℂ | θ < w.re} from hs)
  simp only [Pi.zero_apply] at h0
  have hs1' : s ≠ 1 := fun h => by rw [h, one_re] at h1; exact lt_irrefl 1 h1
  rw [zeta₁_eq hs1', hz, mul_zero, zero_mul, zero_sub, neg_eq_zero, sub_eq_zero] at h0
  exact hs1' h0

/-- **`ψ(N) − N ≤ A(N + 1)^θ + K` ⟹ `ζ ≠ 0` em `Re s > θ`** (`0 ≤ θ < 1`): basta a cota de cima. -/
theorem semZeros_of_psi_le {θ A K : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ N : ℕ, Chebyshev.psi N - N ≤ A * ((N : ℝ) + 1) ^ θ + K) : SemZeros θ := by
  obtain ⟨G, hG, hGA⟩ := extensao (a := E) (C := Real.log 4 + 4) hθ hθ1 abs_E_le h (differentiableOn_Hf hθ)
    (fun s hs => GA_E_eq hs)
  exact semZeros_of_ext_psi hG (fun s hs => (hGA s hs).trans (GA_E_eq hs))

/-- **`ψ(N) − N ≥ −A(N + 1)^θ − K` ⟹ `ζ ≠ 0` em `Re s > θ`**: basta a cota de baixo. -/
theorem semZeros_of_psi_ge {θ A K : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ N : ℕ, -(A * ((N : ℝ) + 1) ^ θ) - K ≤ Chebyshev.psi N - N) : SemZeros θ := by
  obtain ⟨G, hG, hGA⟩ := extensao (a := fun N => -E N) (C := Real.log 4 + 4) (A := A) (K := K) hθ hθ1
    (fun N => by rw [abs_neg]; exact abs_E_le N) (fun N => by have := h N; unfold E; linarith)
    (H := fun s => -Hf s) (differentiableOn_Hf hθ).neg (fun s hs => by rw [GA_neg, GA_E_eq hs])
  refine semZeros_of_ext_psi (G := fun s => -G s) (fun s hs => (hG s hs).neg) (fun s hs => ?_)
  show -G s = Hf s
  rw [hGA s hs, GA_neg, GA_E_eq hs, neg_neg]

/-- **`M(N) ≤ A(N + 1)^θ + K` ⟹ `ζ ≠ 0` em `Re s > θ`**. -/
theorem semZeros_of_mertens_le {θ A K : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ N : ℕ, M N ≤ A * ((N : ℝ) + 1) ^ θ + K) : SemZeros θ := by
  obtain ⟨G, hG, hGA⟩ := extensao (a := M) (C := 1) hθ hθ1 abs_M_le h (differentiableOn_F hθ)
    (fun s hs => GA_M_eq hs)
  exact semZeros_of_ext_mertens hG (fun s hs => (hGA s hs).trans (GA_M_eq hs))

/-- **`M(N) ≥ −A(N + 1)^θ − K` ⟹ `ζ ≠ 0` em `Re s > θ`**. -/
theorem semZeros_of_mertens_ge {θ A K : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ N : ℕ, -(A * ((N : ℝ) + 1) ^ θ) - K ≤ M N) : SemZeros θ := by
  obtain ⟨G, hG, hGA⟩ := extensao (a := fun N => -M N) (C := 1) (A := A) (K := K) hθ hθ1
    (fun N => by rw [abs_neg]; exact abs_M_le N) (fun N => by have := h N; linarith)
    (H := fun s => -F s) (differentiableOn_F hθ).neg (fun s hs => by rw [GA_neg, GA_M_eq hs])
  refine semZeros_of_ext_mertens (G := fun s => -G s) (fun s hs => (hG s hs).neg) (fun s hs => ?_)
  show -G s = F s
  rw [hGA s hs, GA_neg, GA_M_eq hs, neg_neg]

/-! ## 6. `Θ` lido por um lado só; oscilação `Ω±`; RH por cotas unilaterais -/

open ATK.ZeroClasses.BDTheta (Teta Teta_le_iff Teta_le_um meio_le_Teta rh_iff_Teta)

theorem Teta_le_of_unilateral {θ : ℝ} (hθ : 1 / 2 ≤ θ)
    (h : ∀ ε : ℝ, 0 < ε → θ + ε < 1 → SemZeros (θ + ε)) : Teta ≤ θ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rcases lt_or_ge (θ + ε) 1 with h1 | h1
  · exact (Teta_le_iff (by linarith)).mpr (h ε hε h1)
  · exact Teta_le_um.trans h1

/-- **`Θ` pela cota de cima de `ψ`**: `Θ ≤ θ ⟺ ψ(N) − N ≤ A(N + 1)^{θ+ε} + K` para todo `ε > 0`. -/
theorem Teta_le_iff_psi_le {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    Teta ≤ θ ↔ ∀ ε : ℝ, 0 < ε → ∃ A K : ℝ, ∀ N : ℕ,
      Chebyshev.psi N - N ≤ A * ((N : ℝ) + 1) ^ (θ + ε) + K := by
  constructor
  · intro hT ε hε
    obtain ⟨C, hC⟩ := (ATK.ZeroClasses.QuasiRH.semZeros_iff_psi hθ hθ1).mp ((Teta_le_iff hθ).mp hT) ε hε
    exact ⟨C, 0, fun N => by rw [add_zero]; exact (le_abs_self _).trans (hC N)⟩
  · intro h
    refine Teta_le_of_unilateral hθ fun ε hε h1 => ?_
    obtain ⟨A, K, hAK⟩ := h ε hε
    exact semZeros_of_psi_le (by linarith) h1 hAK

/-- **`Θ` pela cota de baixo de `ψ`**. -/
theorem Teta_le_iff_psi_ge {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    Teta ≤ θ ↔ ∀ ε : ℝ, 0 < ε → ∃ A K : ℝ, ∀ N : ℕ,
      -(A * ((N : ℝ) + 1) ^ (θ + ε)) - K ≤ Chebyshev.psi N - N := by
  constructor
  · intro hT ε hε
    obtain ⟨C, hC⟩ := (ATK.ZeroClasses.QuasiRH.semZeros_iff_psi hθ hθ1).mp ((Teta_le_iff hθ).mp hT) ε hε
    exact ⟨C, 0, fun N => by rw [sub_zero]; exact neg_le_of_abs_le (hC N)⟩
  · intro h
    refine Teta_le_of_unilateral hθ fun ε hε h1 => ?_
    obtain ⟨A, K, hAK⟩ := h ε hε
    exact semZeros_of_psi_ge (by linarith) h1 hAK

/-- **`Θ` pela cota de cima de `M`**. -/
theorem Teta_le_iff_mertens_le {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    Teta ≤ θ ↔ ∀ ε : ℝ, 0 < ε → ∃ A K : ℝ, ∀ N : ℕ, M N ≤ A * ((N : ℝ) + 1) ^ (θ + ε) + K := by
  constructor
  · intro hT ε hε
    obtain ⟨C, hC⟩ :=
      (ATK.ZeroClasses.QuasiRH.semZeros_iff_mertens hθ hθ1).mp ((Teta_le_iff hθ).mp hT) ε hε
    exact ⟨C, 0, fun N => by rw [add_zero]; exact (le_abs_self _).trans (hC N)⟩
  · intro h
    refine Teta_le_of_unilateral hθ fun ε hε h1 => ?_
    obtain ⟨A, K, hAK⟩ := h ε hε
    exact semZeros_of_mertens_le (by linarith) h1 hAK

/-- **`Θ` pela cota de baixo de `M`**. -/
theorem Teta_le_iff_mertens_ge {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    Teta ≤ θ ↔ ∀ ε : ℝ, 0 < ε → ∃ A K : ℝ, ∀ N : ℕ, -(A * ((N : ℝ) + 1) ^ (θ + ε)) - K ≤ M N := by
  constructor
  · intro hT ε hε
    obtain ⟨C, hC⟩ :=
      (ATK.ZeroClasses.QuasiRH.semZeros_iff_mertens hθ hθ1).mp ((Teta_le_iff hθ).mp hT) ε hε
    exact ⟨C, 0, fun N => by rw [sub_zero]; exact neg_le_of_abs_le (hC N)⟩
  · intro h
    refine Teta_le_of_unilateral hθ fun ε hε h1 => ?_
    obtain ⟨A, K, hAK⟩ := h ε hε
    exact semZeros_of_mertens_ge (by linarith) h1 hAK

theorem existe_zero_reta : ∃ γ : ℝ, riemannZeta (1 / 2 + γ * I) = 0 := by
  obtain ⟨t, -, ht⟩ := ATK.ZeroClasses.Hardy.existe_zero_acima 0
  exact ⟨t, ht⟩

/-- Para `0 ≤ θ < Θ` há um zero com `Re ρ > θ` (para `θ < ½`, um zero de Hardy na reta). -/
theorem nao_semZeros {θ : ℝ} (hlt : θ < Teta) : ¬ SemZeros θ := by
  intro hZ
  rcases lt_or_ge θ (1 / 2) with h | h
  · obtain ⟨γ, hγ⟩ := existe_zero_reta
    exact hZ _ (by simpa using h) hγ
  · exact absurd ((Teta_le_iff h).mpr hZ) (not_le.mpr hlt)

/-- **`ψ(x) − x = Ω₊(x^θ)` para todo `0 ≤ θ < Θ`**: nenhuma cota `A(N + 1)^θ + K` vale por cima. -/
theorem psi_omega_mais {θ : ℝ} (hθ : 0 ≤ θ) (hlt : θ < Teta) (A K : ℝ) :
    ∃ N : ℕ, A * ((N : ℝ) + 1) ^ θ + K < Chebyshev.psi N - N := by
  by_contra hne
  push Not at hne
  exact nao_semZeros hlt (semZeros_of_psi_le hθ (hlt.trans_le Teta_le_um) hne)

/-- **`ψ(x) − x = Ω₋(x^θ)` para todo `0 ≤ θ < Θ`**. -/
theorem psi_omega_menos {θ : ℝ} (hθ : 0 ≤ θ) (hlt : θ < Teta) (A K : ℝ) :
    ∃ N : ℕ, Chebyshev.psi N - N < -(A * ((N : ℝ) + 1) ^ θ) - K := by
  by_contra hne
  push Not at hne
  exact nao_semZeros hlt (semZeros_of_psi_ge hθ (hlt.trans_le Teta_le_um) hne)

/-- **`M(x) = Ω₊(x^θ)` para todo `0 ≤ θ < Θ`**. -/
theorem mertens_omega_mais {θ : ℝ} (hθ : 0 ≤ θ) (hlt : θ < Teta) (A K : ℝ) :
    ∃ N : ℕ, A * ((N : ℝ) + 1) ^ θ + K < M N := by
  by_contra hne
  push Not at hne
  exact nao_semZeros hlt (semZeros_of_mertens_le hθ (hlt.trans_le Teta_le_um) hne)

/-- **`M(x) = Ω₋(x^θ)` para todo `0 ≤ θ < Θ`**. -/
theorem mertens_omega_menos {θ : ℝ} (hθ : 0 ≤ θ) (hlt : θ < Teta) (A K : ℝ) :
    ∃ N : ℕ, M N < -(A * ((N : ℝ) + 1) ^ θ) - K := by
  by_contra hne
  push Not at hne
  exact nao_semZeros hlt (semZeros_of_mertens_ge hθ (hlt.trans_le Teta_le_um) hne)

/-- **RH ⟺ `ψ(N) − N ≤ A(N + 1)^{½+ε} + K` para todo `ε > 0`** (von Koch por cima). -/
theorem rh_iff_psi_le : RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ A K : ℝ, ∀ N : ℕ,
    Chebyshev.psi N - N ≤ A * ((N : ℝ) + 1) ^ (1 / 2 + ε) + K := by
  rw [rh_iff_Teta]
  constructor
  · intro h
    exact (Teta_le_iff_psi_le (le_refl _) (by norm_num)).mp h.le
  · intro h
    exact le_antisymm ((Teta_le_iff_psi_le (le_refl _) (by norm_num)).mpr h) meio_le_Teta

/-- **RH ⟺ `ψ(N) − N ≥ −A(N + 1)^{½+ε} − K` para todo `ε > 0`** (von Koch por baixo). -/
theorem rh_iff_psi_ge : RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ A K : ℝ, ∀ N : ℕ,
    -(A * ((N : ℝ) + 1) ^ (1 / 2 + ε)) - K ≤ Chebyshev.psi N - N := by
  rw [rh_iff_Teta]
  constructor
  · intro h
    exact (Teta_le_iff_psi_ge (le_refl _) (by norm_num)).mp h.le
  · intro h
    exact le_antisymm ((Teta_le_iff_psi_ge (le_refl _) (by norm_num)).mpr h) meio_le_Teta

/-- **A cota de Mertens fraca de um lado só implica RH**: `M(N) ≤ A√(N + 1) + K` ⟹ RH. -/
theorem rh_of_mertens_le {A K : ℝ} (h : ∀ N : ℕ, M N ≤ A * √((N : ℝ) + 1) + K) : RiemannHypothesis := by
  refine ATK.ZeroClasses.QuasiRH.semZeros_meio_iff.mp (semZeros_of_mertens_le (A := A) (K := K)
    (by norm_num) (by norm_num) fun N => ?_)
  rw [← Real.sqrt_eq_rpow]
  exact h N

/-- **O mesmo por baixo**: `M(N) ≥ −A√(N + 1) − K` ⟹ RH. -/
theorem rh_of_mertens_ge {A K : ℝ} (h : ∀ N : ℕ, -(A * √((N : ℝ) + 1)) - K ≤ M N) : RiemannHypothesis := by
  refine ATK.ZeroClasses.QuasiRH.semZeros_meio_iff.mp (semZeros_of_mertens_ge (A := A) (K := K)
    (by norm_num) (by norm_num) fun N => ?_)
  rw [← Real.sqrt_eq_rpow]
  exact h N

end ATK.ZeroClasses.Unilateral

#print axioms ATK.ZeroClasses.Unilateral.log_pow_le
#print axioms ATK.ZeroClasses.Unilateral.integrable_log_pow
#print axioms ATK.ZeroClasses.Unilateral.norm_integrando
#print axioms ATK.ZeroClasses.Unilateral.aesm_integrando
#print axioms ATK.ZeroClasses.Unilateral.integrable_integrando
#print axioms ATK.ZeroClasses.Unilateral.hasDerivAt_Ik
#print axioms ATK.ZeroClasses.Unilateral.iteratedDeriv_Ik
#print axioms ATK.ZeroClasses.Unilateral.integrable_log_pow'
#print axioms ATK.ZeroClasses.Unilateral.termo_nonneg
#print axioms ATK.ZeroClasses.Unilateral.measurable_termo
#print axioms ATK.ZeroClasses.Unilateral.integrable_termo
#print axioms ATK.ZeroClasses.Unilateral.hasSum_termo
#print axioms ATK.ZeroClasses.Unilateral.Ik_real
#print axioms ATK.ZeroClasses.Unilateral.taylor_termo
#print axioms ATK.ZeroClasses.Unilateral.landau
#print axioms ATK.ZeroClasses.Unilateral.differentiableAt_Ik
#print axioms ATK.ZeroClasses.Unilateral.floor_eq_of_mem
#print axioms ATK.ZeroClasses.Unilateral.iUnion_Ico
#print axioms ATK.ZeroClasses.Unilateral.disjoint_Ico
#print axioms ATK.ZeroClasses.Unilateral.integral_Ico_cpow
#print axioms ATK.ZeroClasses.Unilateral.aesm_escada
#print axioms ATK.ZeroClasses.Unilateral.integrable_escada
#print axioms ATK.ZeroClasses.Unilateral.integral_escada
#print axioms ATK.ZeroClasses.Unilateral.GA_eq_LSeries'
#print axioms ATK.ZeroClasses.Unilateral.measurable_fUni
#print axioms ATK.ZeroClasses.Unilateral.fUni_nonneg
#print axioms ATK.ZeroClasses.Unilateral.intAcima_fUni
#print axioms ATK.ZeroClasses.Unilateral.Ik_fUni
#print axioms ATK.ZeroClasses.Unilateral.Al_nonneg
#print axioms ATK.ZeroClasses.Unilateral.pos_uni
#print axioms ATK.ZeroClasses.Unilateral.re_gt_of_mem_ball
#print axioms ATK.ZeroClasses.Unilateral.intAcima_uni
#print axioms ATK.ZeroClasses.Unilateral.Gext_eq
#print axioms ATK.ZeroClasses.Unilateral.extensao
#print axioms ATK.ZeroClasses.Unilateral.abs_E_le
#print axioms ATK.ZeroClasses.Unilateral.abs_M_le
#print axioms ATK.ZeroClasses.Unilateral.zeta₁_ne_zero_bola
#print axioms ATK.ZeroClasses.Unilateral.differentiableOn_Hf
#print axioms ATK.ZeroClasses.Unilateral.differentiableOn_F
#print axioms ATK.ZeroClasses.Unilateral.GA_E_eq
#print axioms ATK.ZeroClasses.Unilateral.GA_M_eq
#print axioms ATK.ZeroClasses.Unilateral.GA_neg
#print axioms ATK.ZeroClasses.Unilateral.semZeros_of_ext_psi
#print axioms ATK.ZeroClasses.Unilateral.semZeros_of_ext_mertens
#print axioms ATK.ZeroClasses.Unilateral.semZeros_of_psi_le
#print axioms ATK.ZeroClasses.Unilateral.semZeros_of_psi_ge
#print axioms ATK.ZeroClasses.Unilateral.semZeros_of_mertens_le
#print axioms ATK.ZeroClasses.Unilateral.semZeros_of_mertens_ge
#print axioms ATK.ZeroClasses.Unilateral.Teta_le_of_unilateral
#print axioms ATK.ZeroClasses.Unilateral.Teta_le_iff_psi_le
#print axioms ATK.ZeroClasses.Unilateral.Teta_le_iff_psi_ge
#print axioms ATK.ZeroClasses.Unilateral.Teta_le_iff_mertens_le
#print axioms ATK.ZeroClasses.Unilateral.Teta_le_iff_mertens_ge
#print axioms ATK.ZeroClasses.Unilateral.existe_zero_reta
#print axioms ATK.ZeroClasses.Unilateral.nao_semZeros
#print axioms ATK.ZeroClasses.Unilateral.psi_omega_mais
#print axioms ATK.ZeroClasses.Unilateral.psi_omega_menos
#print axioms ATK.ZeroClasses.Unilateral.mertens_omega_mais
#print axioms ATK.ZeroClasses.Unilateral.mertens_omega_menos
#print axioms ATK.ZeroClasses.Unilateral.rh_iff_psi_le
#print axioms ATK.ZeroClasses.Unilateral.rh_iff_psi_ge
#print axioms ATK.ZeroClasses.Unilateral.rh_of_mertens_le
#print axioms ATK.ZeroClasses.Unilateral.rh_of_mertens_ge
