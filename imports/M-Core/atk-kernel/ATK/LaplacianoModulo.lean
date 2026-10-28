import Mathlib

/-!
# ATK — `|F|²` para `F` holomorfa: gradiente e laplaciano; cálculo elementar (18f9cbdc)

Para `F` holomorfa e `z = σ + it`:

* **gradiente**: `∂_σ|F|² = 2 Re(F′ F̄)` e `∂_t|F|² = −2 Im(F′ F̄)` (`grad_sigma`, `grad_t`);
* **laplaciano**: `∂_σ(2 Re F′F̄) = 2 Re(F″F̄) + 2|F′|²`, `∂_t(−2 Im F′F̄) = −2 Re(F″F̄) + 2|F′|²`, logo
  **`Δ|F|² = 4|F′|² ≥ 0`** (`laplaciano`); `F = z` dá `Δ|z|² = 4` com zero em `0`: subharmonicidade não
  exclui zeros (`exemplo_z`).

Cálculo elementar: `θ(R) = arctan(h/(R+½))` tem `θ′ = −h/((R+½)² + h²)` e `θ → 0`;
`w(s) = 1/(s−½)`: `w(−2n) = −2/(4n+1)`, `w(½+it) = −i/t`; `d = √(4/(4n+1)² + 1/t²)`:
`∂_n d = −16/((4n+1)³d)`, `∂_t d = −1/(t³d)`, `∫_T^∞ (d² − 4/(4n+1)²) dt = 1/T`.
-/

open Complex ComplexConjugate Filter Topology Set MeasureTheory

namespace ATK.LaplacianoModulo

/-! ## 1. Derivadas de partes real e imaginária -/

theorem hasDerivAt_re {g : ℝ → ℂ} {g' : ℂ} {x : ℝ} (h : HasDerivAt g g' x) :
    HasDerivAt (fun x => (g x).re) g'.re x := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h

theorem hasDerivAt_im {g : ℝ → ℂ} {g' : ℂ} {x : ℝ} (h : HasDerivAt g g' x) :
    HasDerivAt (fun x => (g x).im) g'.im x := by
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h

theorem hasDerivAt_re_mul_conj {A B : ℝ → ℂ} {A' B' : ℂ} {x : ℝ} (hA : HasDerivAt A A' x)
    (hB : HasDerivAt B B' x) :
    HasDerivAt (fun x => (A x * conj (B x)).re) (A' * conj (B x) + A x * conj B').re x := by
  have := ((hasDerivAt_re hA).mul (hasDerivAt_re hB)).add ((hasDerivAt_im hA).mul (hasDerivAt_im hB))
  convert this using 1
  · funext y; simp [Complex.mul_re]
  · simp [Complex.mul_re, Complex.add_re]; ring

theorem hasDerivAt_im_mul_conj {A B : ℝ → ℂ} {A' B' : ℂ} {x : ℝ} (hA : HasDerivAt A A' x)
    (hB : HasDerivAt B B' x) :
    HasDerivAt (fun x => (A x * conj (B x)).im) (A' * conj (B x) + A x * conj B').im x := by
  have := ((hasDerivAt_im hA).mul (hasDerivAt_re hB)).sub ((hasDerivAt_re hA).mul (hasDerivAt_im hB))
  convert this using 1
  · funext y; simp [Complex.mul_im]; ring
  · simp [Complex.mul_im, Complex.add_im]; ring

theorem normSq_eq_re (w : ℂ) : Complex.normSq w = (w * conj w).re := by
  rw [Complex.mul_conj]; simp

/-! ## 2. As direções `σ` e `t` -/

theorem hasDerivAt_sigma {f : ℂ → ℂ} {f' : ℂ} {σ t : ℝ} (hf : HasDerivAt f f' ((σ : ℂ) + t * I)) :
    HasDerivAt (fun x : ℝ => f ((x : ℂ) + t * I)) f' σ := by
  have hl : HasDerivAt (fun x : ℝ => ((x : ℂ) + t * I)) 1 σ := by
    simpa using ((hasDerivAt_id (σ : ℂ)).add_const ((t : ℂ) * I)).comp_ofReal
  exact (hf.comp σ hl).congr_deriv (mul_one f')

theorem hasDerivAt_t {f : ℂ → ℂ} {f' : ℂ} {σ t : ℝ} (hf : HasDerivAt f f' ((σ : ℂ) + t * I)) :
    HasDerivAt (fun y : ℝ => f ((σ : ℂ) + y * I)) (f' * I) t := by
  have hl : HasDerivAt (fun y : ℝ => ((σ : ℂ) + (y : ℂ) * I)) I t := by
    have := ((hasDerivAt_id (t : ℂ)).mul_const I).const_add (σ : ℂ)
    simpa using this.comp_ofReal
  exact hf.comp t hl

/-! ## 3. Gradiente -/

/-- **`∂_σ|F|² = 2 Re(F′F̄)`.** -/
theorem grad_sigma {f : ℂ → ℂ} {σ t : ℝ} (hf : DifferentiableAt ℂ f ((σ : ℂ) + t * I)) :
    HasDerivAt (fun x : ℝ => Complex.normSq (f ((x : ℂ) + t * I)))
      (2 * (deriv f ((σ : ℂ) + t * I) * conj (f ((σ : ℂ) + t * I))).re) σ := by
  have hg := hasDerivAt_sigma hf.hasDerivAt
  have := hasDerivAt_re_mul_conj hg hg
  simp_rw [← normSq_eq_re] at this
  convert this using 1
  simp [Complex.mul_re]; ring

/-- **`∂_t|F|² = −2 Im(F′F̄)`.** -/
theorem grad_t {f : ℂ → ℂ} {σ t : ℝ} (hf : DifferentiableAt ℂ f ((σ : ℂ) + t * I)) :
    HasDerivAt (fun y : ℝ => Complex.normSq (f ((σ : ℂ) + y * I)))
      (-2 * (deriv f ((σ : ℂ) + t * I) * conj (f ((σ : ℂ) + t * I))).im) t := by
  have hg := hasDerivAt_t hf.hasDerivAt
  have := hasDerivAt_re_mul_conj hg hg
  simp_rw [← normSq_eq_re] at this
  convert this using 1
  simp [Complex.mul_re, Complex.mul_im]; ring

/-! ## 4. Laplaciano -/

theorem lap_sigma {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf' : Differentiable ℂ (deriv f)) (σ t : ℝ) :
    HasDerivAt (fun x : ℝ => 2 * (deriv f ((x : ℂ) + t * I) * conj (f ((x : ℂ) + t * I))).re)
      (2 * (deriv (deriv f) ((σ : ℂ) + t * I) * conj (f ((σ : ℂ) + t * I))).re +
        2 * Complex.normSq (deriv f ((σ : ℂ) + t * I))) σ := by
  have hA := hasDerivAt_sigma (hf' ((σ : ℂ) + t * I)).hasDerivAt
  have hB := hasDerivAt_sigma (hf ((σ : ℂ) + t * I)).hasDerivAt
  have := (hasDerivAt_re_mul_conj hA hB).const_mul 2
  convert this using 1
  rw [Complex.add_re, normSq_eq_re]; ring

theorem lap_t {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf' : Differentiable ℂ (deriv f)) (σ t : ℝ) :
    HasDerivAt (fun y : ℝ => -2 * (deriv f ((σ : ℂ) + y * I) * conj (f ((σ : ℂ) + y * I))).im)
      (-2 * (deriv (deriv f) ((σ : ℂ) + t * I) * conj (f ((σ : ℂ) + t * I))).re +
        2 * Complex.normSq (deriv f ((σ : ℂ) + t * I))) t := by
  have hA := hasDerivAt_t (hf' ((σ : ℂ) + t * I)).hasDerivAt
  have hB := hasDerivAt_t (hf ((σ : ℂ) + t * I)).hasDerivAt
  have := (hasDerivAt_im_mul_conj hA hB).const_mul (-2)
  convert this using 1
  rw [normSq_eq_re]
  simp [Complex.mul_re, Complex.mul_im, Complex.add_im]
  ring

/-- **`Δ|F|² = 4|F′|²`**: a soma das duas segundas derivadas. -/
theorem laplaciano {f : ℂ → ℂ} (σ t : ℝ) :
    (2 * (deriv (deriv f) ((σ : ℂ) + t * I) * conj (f ((σ : ℂ) + t * I))).re +
        2 * Complex.normSq (deriv f ((σ : ℂ) + t * I))) +
      (-2 * (deriv (deriv f) ((σ : ℂ) + t * I) * conj (f ((σ : ℂ) + t * I))).re +
        2 * Complex.normSq (deriv f ((σ : ℂ) + t * I))) =
      4 * Complex.normSq (deriv f ((σ : ℂ) + t * I)) := by ring

theorem laplaciano_nonneg {f : ℂ → ℂ} (σ t : ℝ) :
    0 ≤ 4 * Complex.normSq (deriv f ((σ : ℂ) + t * I)) :=
  mul_nonneg (by norm_num) (Complex.normSq_nonneg _)

/-- `F(z) = z`: `Δ|z|² = 4 > 0` e `F(0) = 0` — subharmonicidade não exclui zeros. -/
theorem exemplo_z : (4 * Complex.normSq (deriv (fun z : ℂ => z) 0) = 4) ∧ (fun z : ℂ => z) 0 = 0 := by
  simp

/-! ## 5. Cálculo elementar (18f9cbdc) -/

theorem deriv_theta (h : ℝ) {R : ℝ} (hR : R + 1 / 2 ≠ 0) :
    HasDerivAt (fun R => Real.arctan (h / (R + 1 / 2))) (-h / ((R + 1 / 2) ^ 2 + h ^ 2)) R := by
  have hq : HasDerivAt (fun R : ℝ => h / (R + 1 / 2)) (-h / (R + 1 / 2) ^ 2) R := by
    have := (hasDerivAt_const R h).div ((hasDerivAt_id' R).add_const (1 / 2 : ℝ)) hR
    exact this.congr_deriv (by ring)
  have := (Real.hasDerivAt_arctan (h / (R + 1 / 2))).comp R hq
  refine this.congr_deriv ?_
  have key : ∀ a : ℝ, a ≠ 0 → 1 / (1 + (h / a) ^ 2) * (-h / a ^ 2) = -h / (a ^ 2 + h ^ 2) := by
    intro a ha
    have h4 : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha))
    have h5 : a ^ 2 + h ^ 2 ≠ 0 := ne_of_gt (by nlinarith [sq_nonneg h])
    field_simp
  exact key _ hR

theorem theta_tende_zero (h : ℝ) : Tendsto (fun R : ℝ => Real.arctan (h / (R + 1 / 2))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ => h / (R + 1 / 2)) atTop (𝓝 0) :=
    (tendsto_atTop_add_const_right _ (1 / 2) tendsto_id).const_div_atTop h
  have := (Real.continuous_arctan.tendsto 0).comp h1
  rw [Real.arctan_zero] at this
  exact this

/-- `w(s) = 1/(s − ½)`. -/
noncomputable def w (s : ℂ) : ℂ := 1 / (s - 1 / 2)

theorem w_trivial (n : ℕ) : w (-2 * n) = -2 / (4 * n + 1) := by
  unfold w
  have h2 : (4 * (n : ℂ) + 1) ≠ 0 := by
    have : (0 : ℝ) < 4 * n + 1 := by positivity
    exact_mod_cast this.ne'
  have h1 : (-2 * (n : ℂ) - 1 / 2) ≠ 0 := by
    intro h; apply h2; linear_combination (-2 : ℂ) * h
  rw [div_eq_div_iff h1 h2]
  ring

theorem w_linha {t : ℝ} (ht : t ≠ 0) : w ((1 / 2 : ℂ) + t * I) = -I / t := by
  unfold w
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  rw [show (1 / 2 : ℂ) + t * I - 1 / 2 = t * I by ring]
  field_simp
  rw [I_sq]; ring

/-- `d(n,t) = √(4/(4n+1)² + 1/t²)`. -/
noncomputable def dd (n t : ℝ) : ℝ := Real.sqrt (4 / (4 * n + 1) ^ 2 + 1 / t ^ 2)

theorem deriv_dd_n {n t : ℝ} (hn : 0 ≤ n) (ht : t ≠ 0) :
    HasDerivAt (fun n => dd n t) (-16 / ((4 * n + 1) ^ 3 * dd n t)) n := by
  have hq : (4 * n + 1) ≠ 0 := by linarith
  have hpos : 0 < 4 / (4 * n + 1) ^ 2 + 1 / t ^ 2 := by positivity
  have hlin : HasDerivAt (fun n : ℝ => 4 * n + 1) 4 n := by
    simpa using ((hasDerivAt_id' n).const_mul (4 : ℝ)).add_const (1 : ℝ)
  have hp := hasDerivAt_pow 2 (4 * n + 1)
  have hc := hp.comp n hlin
  have h1 : HasDerivAt (fun n : ℝ => (4 * n + 1) ^ 2) (2 * (4 * n + 1) * 4) n :=
    hc.congr_deriv (by norm_num)
  have hin : HasDerivAt (fun n : ℝ => 4 / (4 * n + 1) ^ 2 + 1 / t ^ 2) (-32 / (4 * n + 1) ^ 3) n := by
    have := ((hasDerivAt_const n (4 : ℝ)).div h1 (pow_ne_zero 2 hq)).add_const (1 / t ^ 2)
    refine this.congr_deriv ?_
    field_simp
    ring
  have := (Real.hasDerivAt_sqrt hpos.ne').comp n hin
  unfold dd
  refine this.congr_deriv ?_
  have hs : 0 < Real.sqrt (4 / (4 * n + 1) ^ 2 + 1 / t ^ 2) := Real.sqrt_pos.mpr hpos
  field_simp
  try ring

theorem deriv_dd_t {n t : ℝ} (hn : 0 ≤ n) (ht : t ≠ 0) :
    HasDerivAt (fun t => dd n t) (-1 / (t ^ 3 * dd n t)) t := by
  have hq : (4 * n + 1) ≠ 0 := by linarith
  have hpos : 0 < 4 / (4 * n + 1) ^ 2 + 1 / t ^ 2 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
  have hin : HasDerivAt (fun t : ℝ => 4 / (4 * n + 1) ^ 2 + 1 / t ^ 2) (-2 / t ^ 3) t := by
    have := ((hasDerivAt_const t (1 : ℝ)).div h1 (pow_ne_zero 2 ht)).const_add (4 / (4 * n + 1) ^ 2)
    refine this.congr_deriv ?_
    field_simp
    ring
  have := (Real.hasDerivAt_sqrt hpos.ne').comp t hin
  unfold dd
  refine this.congr_deriv ?_
  have hs : 0 < Real.sqrt (4 / (4 * n + 1) ^ 2 + 1 / t ^ 2) := Real.sqrt_pos.mpr hpos
  field_simp
  try ring

/-- `∫_T^∞ (d² − 4/(4n+1)²) dt = 1/T`. -/
theorem integral_dd {n T : ℝ} (hn : 0 ≤ n) (hT : 0 < T) :
    ∫ t in Ioi T, (dd n t ^ 2 - 4 / (4 * n + 1) ^ 2) = 1 / T := by
  have hpt : ∀ t ∈ Ioi T, dd n t ^ 2 - 4 / (4 * n + 1) ^ 2 = t ^ (-2 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hT ht
    unfold dd
    rw [Real.sq_sqrt (by positivity), Real.rpow_neg ht0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_Ioi_rpow_of_lt (by norm_num) hT]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

end ATK.LaplacianoModulo

-- Auditoria de axiomas (kernel)
#print axioms ATK.LaplacianoModulo.hasDerivAt_re
#print axioms ATK.LaplacianoModulo.hasDerivAt_im
#print axioms ATK.LaplacianoModulo.hasDerivAt_re_mul_conj
#print axioms ATK.LaplacianoModulo.hasDerivAt_im_mul_conj
#print axioms ATK.LaplacianoModulo.normSq_eq_re
#print axioms ATK.LaplacianoModulo.hasDerivAt_sigma
#print axioms ATK.LaplacianoModulo.hasDerivAt_t
#print axioms ATK.LaplacianoModulo.grad_sigma
#print axioms ATK.LaplacianoModulo.grad_t
#print axioms ATK.LaplacianoModulo.lap_sigma
#print axioms ATK.LaplacianoModulo.lap_t
#print axioms ATK.LaplacianoModulo.laplaciano
#print axioms ATK.LaplacianoModulo.laplaciano_nonneg
#print axioms ATK.LaplacianoModulo.exemplo_z
#print axioms ATK.LaplacianoModulo.deriv_theta
#print axioms ATK.LaplacianoModulo.theta_tende_zero
#print axioms ATK.LaplacianoModulo.w_trivial
#print axioms ATK.LaplacianoModulo.w_linha
#print axioms ATK.LaplacianoModulo.deriv_dd_n
#print axioms ATK.LaplacianoModulo.deriv_dd_t
#print axioms ATK.LaplacianoModulo.integral_dd
