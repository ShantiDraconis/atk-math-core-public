import ATK.ZeroClasses.ArgRetangulo

/-!
# A fórmula de Perron truncada: o núcleo (rodada 44)

Para `c > 0`, `T > 0` e `L ≠ 0`,

  `perron L c T = (1/2π) ∫_{−T}^{T} e^{(c + it)L}/(c + it) dt = (1/2πi) ∫_{c−iT}^{c+iT} y^z/z dz`, `y = e^L`,

aproxima o degrau `1_{y > 1}`:

* **`perron_pos`**: para `L > 0`, `‖perron L c T − 1‖ ≤ e^{cL}/(πTL)`;
* **`perron_neg`**: para `L < 0`, `‖perron L c T‖ ≤ e^{cL}/(πT|L|)`.

A prova desloca o segmento vertical num retângulo (`ArgRetangulo`, rodada 40): para a esquerda até `Re z = −U`
quando `y > 1` (o resíduo em `z = 0` é `1`: `e^{zL}/z = dslope(e^{·L}) 0 + 1/z` e `bordo_inv`), para a direita até
`Re z = U` quando `y < 1` (sem polos: `bordo_cauchy`). Os lados horizontais custam `≤ e^{cL}/(|L|T)` cada
(`horiz`), o vertical deslocado `≤ 2T/U` (`vert`), e `U → ∞`.

A Mathlib não tem a fórmula de Perron. É a primeira peça da entrada de Littlewood
(`ATK.NecessidadeBD.EntradaLittlewood`), a única parte de `NecessidadeRH` que segue BUILD_PENDING.

Classificação (rodada 44): **ferramenta**. Não é RH.
-/

open Complex Set Filter Topology
open scoped Real Interval

namespace ATK.ZeroClasses.Perron

open ATK.ZeroClasses.ArgRetangulo (bordo Bordo Ret bordo_congr bordo_add bordo_cauchy bordo_inv)

/-- O núcleo de Perron: `(1/2π) ∫_{−T}^{T} e^{(c + it)L}/(c + it) dt`. -/
noncomputable def perron (L c T : ℝ) : ℂ :=
  (2 * π : ℂ)⁻¹ * ∫ t in (-T)..T, cexp (((c : ℂ) + t * I) * L) / ((c : ℂ) + t * I)

theorem norm_nucleo (L : ℝ) (s : ℂ) : ‖cexp (s * L) / s‖ = Real.exp (s.re * L) / ‖s‖ := by
  simp only [norm_div, Complex.norm_exp, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]

theorem nucleo_cont (L : ℝ) : ContinuousOn (fun s : ℂ => cexp (s * L) / s) {s | s ≠ 0} := fun _ hs =>
  ((by fun_prop : Continuous fun s : ℂ => cexp (s * L)).continuousAt.div continuousAt_id
    hs).continuousWithinAt

/-- **Lado horizontal**: `‖∫_a^b e^{(x + ih)L}/(x + ih) dx‖ ≤ (e^{bL} − e^{aL})/(L|h|)`. -/
theorem horiz {L h a b : ℝ} (hL : L ≠ 0) (hh : h ≠ 0) (hab : a ≤ b) :
    ‖∫ x in a..b, cexp (((x : ℂ) + h * I) * L) / ((x : ℂ) + h * I)‖ ≤
      (Real.exp (b * L) - Real.exp (a * L)) / (L * |h|) := by
  have hhp : 0 < |h| := abs_pos.mpr hh
  have hh' : |h| ≠ 0 := hhp.ne'
  have hF : ∀ x : ℝ, HasDerivAt (fun x => Real.exp (x * L) / (L * |h|)) (Real.exp (x * L) / |h|) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => x * L) L x := by simpa using (hasDerivAt_id x).mul_const L
    have h3 := h1.exp.div_const (L * |h|)
    exact h3.congr_deriv (by field_simp)
  have hgc : Continuous fun x : ℝ => Real.exp (x * L) / |h| := by fun_prop
  have hint : ∫ x in a..b, Real.exp (x * L) / |h| = (Real.exp (b * L) - Real.exp (a * L)) / (L * |h|) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x) (hgc.intervalIntegrable _ _)]
    ring
  rw [← hint]
  refine intervalIntegral.norm_integral_le_of_norm_le hab (MeasureTheory.ae_of_all _ fun x _ => ?_)
    (hgc.intervalIntegrable _ _)
  rw [norm_nucleo]
  have hre : ((x : ℂ) + h * I).re = x := by simp
  have him : |h| ≤ ‖(x : ℂ) + h * I‖ := by
    have := Complex.abs_im_le_norm ((x : ℂ) + h * I)
    simpa using this
  rw [hre]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hhp him

/-- **Lado vertical**: `‖∫_{−T}^{T} e^{(u + iy)L}/(u + iy) dy‖ ≤ 2T e^{uL}/|u|`. -/
theorem vert {L u T : ℝ} (hu : u ≠ 0) (hT : 0 ≤ T) :
    ‖∫ y in (-T)..T, cexp (((u : ℂ) + y * I) * L) / ((u : ℂ) + y * I)‖ ≤
      2 * T * (Real.exp (u * L) / |u|) := by
  have hup : 0 < |u| := abs_pos.mpr hu
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
    (f := fun y : ℝ => cexp (((u : ℂ) + y * I) * L) / ((u : ℂ) + y * I))
    (C := Real.exp (u * L) / |u|) (fun y _ => by
      rw [norm_nucleo]
      have hre : ((u : ℂ) + y * I).re = u := by simp
      have : |u| ≤ ‖(u : ℂ) + y * I‖ := by
        have := Complex.abs_re_le_norm ((u : ℂ) + y * I)
        simpa using this
      rw [hre]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hup this)
  rw [show |T - -T| = 2 * T by rw [abs_of_nonneg (by linarith)]; ring] at this
  exact this.trans_eq (by ring)

/-- Álgebra do deslocamento para a esquerda. -/
theorem alg_esq {A B V D : ℂ} (h : A - B + I * V - I * D = 2 * π * I) :
    ‖(2 * π : ℂ)⁻¹ * V - 1‖ ≤ (‖A‖ + ‖B‖ + ‖D‖) / (2 * π) := by
  have hπ : (2 * π : ℂ) ≠ 0 := by
    have : (2 * π : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have h2 : (2 * π : ℂ)⁻¹ * (2 * π) = 1 := inv_mul_cancel₀ hπ
  have hden : (2 * π * I : ℂ) ≠ 0 := mul_ne_zero hπ I_ne_zero
  have e : (2 * π : ℂ)⁻¹ * V - 1 = (B - A + I * D) / (2 * π * I) := by
    rw [eq_div_iff hden]
    calc ((2 * π : ℂ)⁻¹ * V - 1) * (2 * π * I) = I * V * ((2 * π : ℂ)⁻¹ * (2 * π)) - 2 * π * I := by ring
      _ = I * V - 2 * π * I := by rw [h2, mul_one]
      _ = B - A + I * D := by linear_combination h
  have hn : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    rw [norm_mul, norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [e, norm_div, hn]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc ‖B - A + I * D‖ ≤ ‖B - A‖ + ‖I * D‖ := norm_add_le _ _
    _ ≤ (‖B‖ + ‖A‖) + ‖D‖ := by
        rw [norm_mul, norm_I, one_mul]
        linarith [norm_sub_le B A]
    _ = ‖A‖ + ‖B‖ + ‖D‖ := by ring

/-- Álgebra do deslocamento para a direita. -/
theorem alg_dir {A B V D : ℂ} (h : A - B + I * D - I * V = 0) :
    ‖(2 * π : ℂ)⁻¹ * V‖ ≤ (‖A‖ + ‖B‖ + ‖D‖) / (2 * π) := by
  have hπ : (2 * π : ℂ) ≠ 0 := by
    have : (2 * π : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have hden : (2 * π * I : ℂ) ≠ 0 := mul_ne_zero hπ I_ne_zero
  have h2 : (2 * π : ℂ)⁻¹ * (2 * π) = 1 := inv_mul_cancel₀ hπ
  have e : (2 * π : ℂ)⁻¹ * V = (A - B + I * D) / (2 * π * I) := by
    rw [eq_div_iff hden]
    calc (2 * π : ℂ)⁻¹ * V * (2 * π * I) = I * V * ((2 * π : ℂ)⁻¹ * (2 * π)) := by ring
      _ = I * V := by rw [h2, mul_one]
      _ = A - B + I * D := by linear_combination (-1 : ℂ) * h
  have hn : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    rw [norm_mul, norm_I, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [e, norm_div, hn]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc ‖A - B + I * D‖ ≤ ‖A - B‖ + ‖I * D‖ := norm_add_le _ _
    _ ≤ (‖A‖ + ‖B‖) + ‖D‖ := by
        rw [norm_mul, norm_I, one_mul]
        linarith [norm_sub_le A B]

/-- O limite `U → ∞`. -/
theorem limite {a b T : ℝ} (h : ∀ U : ℝ, 1 ≤ U → a ≤ b + T / (π * U)) : a ≤ b := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  set M := max 1 (T / (π * η)) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := by linarith
  have hle : T / (π * M) ≤ η := by
    rw [div_le_iff₀ (mul_pos Real.pi_pos hM0)]
    have : T / (π * η) ≤ M := le_max_right _ _
    rw [div_le_iff₀ (mul_pos Real.pi_pos hη)] at this
    calc T ≤ M * (π * η) := this
      _ = η * (π * M) := by ring
  linarith [h M hM1]

/-- **Perron, `y > 1`**: `‖perron L c T − 1‖ ≤ e^{cL}/(πTL)` para `L > 0`. -/
theorem perron_pos {L c T : ℝ} (hL : 0 < L) (hc : 0 < c) (hT : 0 < T) :
    ‖perron L c T - 1‖ ≤ Real.exp (c * L) / (π * T * L) := by
  refine limite (T := T) fun U hU1 => ?_
  have hU0 : 0 < U := by linarith
  have hne : ∀ p ∈ Bordo ⟨-U, -T⟩ ⟨c, T⟩, p ≠ 0 := by
    rintro p ⟨_, h⟩ hp
    change p.re = -U ∨ p.re = c ∨ p.im = -T ∨ p.im = T at h
    have h1 : p.re = 0 := by rw [hp, zero_re]
    have h2 : p.im = 0 := by rw [hp, zero_im]
    rcases h with h | h | h | h <;> linarith
  have hD : Differentiable ℂ (dslope (fun s : ℂ => cexp (s * L)) 0) :=
    differentiableOn_univ.mp ((differentiableOn_dslope univ_mem).mpr
      (by fun_prop : Differentiable ℂ fun s : ℂ => cexp (s * L)).differentiableOn)
  have heq : EqOn (fun s : ℂ => cexp (s * L) / s)
      (fun s => dslope (fun s : ℂ => cexp (s * L)) 0 s + (s - 0)⁻¹) (Bordo ⟨-U, -T⟩ ⟨c, T⟩) := by
    intro s hs
    have hs0 := hne s hs
    simp only [dslope_of_ne _ hs0, slope_def_field, sub_zero, zero_mul, Complex.exp_zero]
    rw [sub_div]
    ring
  have hIc : ContinuousOn (fun s : ℂ => (s - 0)⁻¹) (Bordo ⟨-U, -T⟩ ⟨c, T⟩) := fun s hs =>
    ((continuousAt_id.sub continuousAt_const).inv₀ (by simpa using hne s hs)).continuousWithinAt
  have hB : bordo (fun s : ℂ => cexp (s * L) / s) ⟨-U, -T⟩ ⟨c, T⟩ = 2 * π * I := by
    rw [bordo_congr heq, bordo_add hD.continuous.continuousOn hIc, bordo_cauchy hD.differentiableOn,
      bordo_inv (z := ⟨-U, -T⟩) (w := ⟨c, T⟩) (u := 0) (by simp; linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith),
      zero_add]
  have hB' : (∫ x in (-U)..c, cexp (((x : ℂ) + ((-T : ℝ) : ℂ) * I) * L) / ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) -
      (∫ x in (-U)..c, cexp (((x : ℂ) + (T : ℂ) * I) * L) / ((x : ℂ) + (T : ℂ) * I)) +
      I * (∫ y in (-T)..T, cexp (((c : ℂ) + y * I) * L) / ((c : ℂ) + y * I)) -
      I * (∫ y in (-T)..T, cexp ((((-U : ℝ) : ℂ) + y * I) * L) / (((-U : ℝ) : ℂ) + y * I)) =
      2 * π * I := by
    have := hB
    simp only [bordo, smul_eq_mul] at this
    exact this
  have hal := alg_esq hB'
  have hA := horiz (L := L) (h := -T) (a := -U) (b := c) hL.ne' (neg_ne_zero.mpr hT.ne') (by linarith)
  have hB2 := horiz (L := L) (h := T) (a := -U) (b := c) hL.ne' hT.ne' (by linarith)
  have hV := vert (L := L) (u := -U) (T := T) (neg_ne_zero.mpr hU0.ne') hT.le
  rw [abs_neg, abs_of_pos hT] at hA
  rw [abs_of_pos hT] at hB2
  rw [abs_neg, abs_of_pos hU0] at hV
  have he : Real.exp (-U * L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hep := Real.exp_pos (-U * L)
  have hA' : (Real.exp (c * L) - Real.exp (-U * L)) / (L * T) ≤ Real.exp (c * L) / (L * T) :=
    div_le_div_of_nonneg_right (by linarith) (mul_pos hL hT).le
  have hV' : 2 * T * (Real.exp (-U * L) / U) ≤ 2 * T * (1 / U) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he hU0.le) (by linarith)
  have h1 := hL.ne'
  have h2 := hT.ne'
  have h3 := hU0.ne'
  have h4 := Real.pi_ne_zero
  calc ‖perron L c T - 1‖ ≤ (Real.exp (c * L) / (L * T) + Real.exp (c * L) / (L * T) + 2 * T * (1 / U)) /
        (2 * π) := hal.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))
    _ = Real.exp (c * L) / (π * T * L) + T / (π * U) := by
        field_simp
        ring

/-- **Perron, `0 < y < 1`**: `‖perron L c T‖ ≤ e^{cL}/(πT|L|)` para `L < 0`. -/
theorem perron_neg {L c T : ℝ} (hL : L < 0) (hc : 0 < c) (hT : 0 < T) :
    ‖perron L c T‖ ≤ Real.exp (c * L) / (π * T * (-L)) := by
  refine limite (T := T) fun U' hU1 => ?_
  set U := U' + c with hUdef
  have hU0 : 0 < U := by linarith
  have hcU : c < U := by linarith
  have hne : ∀ p ∈ Ret ⟨c, -T⟩ ⟨U, T⟩, p ≠ 0 := by
    intro p hp hp0
    have h1 := (mem_reProdIm.mp hp).1
    change p.re ∈ [[c, U]] at h1
    rw [uIcc_of_le hcU.le, hp0, zero_re] at h1
    linarith [h1.1]
  have hf : DifferentiableOn ℂ (fun s : ℂ => cexp (s * L) / s) (Ret ⟨c, -T⟩ ⟨U, T⟩) := fun s hs =>
    ((by fun_prop : Differentiable ℂ fun s : ℂ => cexp (s * L)) s).div differentiableAt_id
      (hne s hs) |>.differentiableWithinAt
  have hB := bordo_cauchy hf
  have hB' : (∫ x in c..U, cexp (((x : ℂ) + ((-T : ℝ) : ℂ) * I) * L) / ((x : ℂ) + ((-T : ℝ) : ℂ) * I)) -
      (∫ x in c..U, cexp (((x : ℂ) + (T : ℂ) * I) * L) / ((x : ℂ) + (T : ℂ) * I)) +
      I * (∫ y in (-T)..T, cexp (((U : ℂ) + y * I) * L) / ((U : ℂ) + y * I)) -
      I * (∫ y in (-T)..T, cexp (((c : ℂ) + y * I) * L) / ((c : ℂ) + y * I)) = 0 := by
    have := hB
    simp only [bordo, smul_eq_mul] at this
    exact this
  have hal := alg_dir hB'
  have hA := horiz (L := L) (h := -T) (a := c) (b := U) hL.ne (neg_ne_zero.mpr hT.ne') hcU.le
  have hB2 := horiz (L := L) (h := T) (a := c) (b := U) hL.ne hT.ne' hcU.le
  have hV := vert (L := L) (u := U) (T := T) hU0.ne' hT.le
  rw [abs_neg, abs_of_pos hT] at hA
  rw [abs_of_pos hT] at hB2
  rw [abs_of_pos hU0] at hV
  have he : Real.exp (U * L) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hep := Real.exp_pos (U * L)
  have hLT : L * T < 0 := by nlinarith
  have hLT' : 0 < (-L) * T := by nlinarith
  have hA' : (Real.exp (U * L) - Real.exp (c * L)) / (L * T) ≤ Real.exp (c * L) / ((-L) * T) := by
    have e : (Real.exp (U * L) - Real.exp (c * L)) / (L * T) =
        (Real.exp (c * L) - Real.exp (U * L)) / ((-L) * T) := by
      rw [div_eq_div_iff hLT.ne hLT'.ne']
      ring
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith) hLT'.le
  have hU'U : U' ≤ U := by linarith
  have hV' : 2 * T * (Real.exp (U * L) / U) ≤ 2 * T * (1 / U') := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    calc Real.exp (U * L) / U ≤ 1 / U := div_le_div_of_nonneg_right he hU0.le
      _ ≤ 1 / U' := one_div_le_one_div_of_le (by linarith) hU'U
  have h1 : -L ≠ 0 := by linarith
  have h2 := hT.ne'
  have h3 : U' ≠ 0 := by linarith
  have h4 := Real.pi_ne_zero
  calc ‖perron L c T‖ ≤ (Real.exp (c * L) / ((-L) * T) + Real.exp (c * L) / ((-L) * T) + 2 * T * (1 / U')) /
        (2 * π) := hal.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))
    _ = Real.exp (c * L) / (π * T * (-L)) + T / (π * U') := by
        field_simp
        ring

/-- **O degrau**: `‖perron L c T − 1_{L > 0}‖ ≤ e^{cL}/(πT|L|)` para `L ≠ 0`. -/
theorem perron_degrau {L c T : ℝ} (hL : L ≠ 0) (hc : 0 < c) (hT : 0 < T) :
    ‖perron L c T - (if 0 < L then 1 else 0)‖ ≤ Real.exp (c * L) / (π * T * |L|) := by
  rcases lt_or_gt_of_ne hL with h | h
  · have h' : ¬ (0 < L) := not_lt.mpr h.le
    simp only [h', ↓reduceIte, sub_zero, abs_of_neg h]
    exact perron_neg h hc hT
  · simp only [h, ↓reduceIte, abs_of_pos h]
    exact perron_pos h hc hT

end ATK.ZeroClasses.Perron

#print axioms ATK.ZeroClasses.Perron.norm_nucleo
#print axioms ATK.ZeroClasses.Perron.nucleo_cont
#print axioms ATK.ZeroClasses.Perron.horiz
#print axioms ATK.ZeroClasses.Perron.vert
#print axioms ATK.ZeroClasses.Perron.alg_esq
#print axioms ATK.ZeroClasses.Perron.alg_dir
#print axioms ATK.ZeroClasses.Perron.limite
#print axioms ATK.ZeroClasses.Perron.perron_pos
#print axioms ATK.ZeroClasses.Perron.perron_neg
#print axioms ATK.ZeroClasses.Perron.perron_degrau
