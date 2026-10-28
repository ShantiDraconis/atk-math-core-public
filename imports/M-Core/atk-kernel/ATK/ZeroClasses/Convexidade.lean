import ATK.ZeroClasses.BDTaxaTeta
import ATK.ZetaTroca

/-!
# A cota de convexidade `ζ(σ + it) ≪ |t|^{(1−σ)/2+ε}` (rodada 86)

**Teorema (Phragmén–Lindelöf, convexidade).** Para `0 < δ ≤ ½` há `C` com

  **`|ζ(σ + it)| ≤ C |t|^{(1−σ+δ)/2}`** para `0 ≤ σ ≤ 1`, `|t| ≥ 1`   (`convexidade`),

e em particular `ζ(½ + it) = O((1 + |t|)^{1/4+ε})` (`convexidade_meio`). Até aqui o ATK tinha a cota sob RH
(`LindelofRH`, rodada 61); esta é incondicional.

A prova aplica Phragmén–Lindelöf (Mathlib) na faixa `−δ ≤ Re s ≤ 1 + δ` à função
`g(s) = ζ₁(s) · w(s)^{−ℓ(s)}`, com:
* `ζ₁ = (s − 1)ζ` inteira (Mathlib);
* `w(s) = −i(s + 2)`, que tem `Im w < 0` na faixa e portanto fica no plano cortado;
* `ℓ(s) = (3 + δ − s)/2`, que tem parte real `1` em `Re s = 1 + δ` e `3/2 + δ` em `Re s = −δ`.

O fator `e^{−arg w · Im(−ℓ)} = e^{−arg w · t/2}` fica entre `1` e `e^{π(Re s + 2)/4}` para `t ≥ 0`
(`arg_mul_re_le`, Jordan; ver `norm_peso`).

As retas:
* em `Re s = 1 + δ`, `|ζ| ≤ 2 + 1/δ` (`norm_zeta_dir`, via `ZetaTroca.norm_zeta_sub_one_le`);
* em `Re s = −δ`, a equação funcional dá `|ζ(1 − u)| ≤ 2C_Γ|u|^{½+δ}|ζ(u)|` (`GammaVertical.norm_zeta_one_sub_le`);
* dentro, o crescimento é polinomial (`RegiaoLivre.cota_zeta_faixa` e a equação funcional).

Para `t ≤ −1`, usa-se `ζ(s̄) = conj ζ(s)`.

Classificação (rodada 86): **ferramenta** (a cota de convexidade, BUILD_PENDING desde a rodada 61). A hipótese de
Lindelöf (`|t|^ε`) segue OPEN_MATH; RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Asymptotics
open scoped Real

namespace ATK.ZeroClasses.Convexidade

open ATK.GammaVertical (CΓ CΓ_pos norm_zeta_one_sub_le)

/-! ## 1. O peso -/

/-- `w(s) = −i(s + 2)`. -/
noncomputable def w (s : ℂ) : ℂ := -I * (s + 2)

/-- `ℓ(s) = (3 + δ − s)/2`. -/
noncomputable def ell (δ : ℝ) (s : ℂ) : ℂ := (3 + δ - s) / 2

theorem w_re (s : ℂ) : (w s).re = s.im := by simp [w]

theorem w_im (s : ℂ) : (w s).im = -(s.re + 2) := by simp [w]

theorem norm_w (s : ℂ) : ‖w s‖ = ‖s + 2‖ := by simp [w]

theorem w_slit {s : ℂ} (hs : -2 < s.re) : w s ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inr (by rw [w_im]; linarith))

theorem w_ne_zero {s : ℂ} (hs : -2 < s.re) : w s ≠ 0 := slitPlane_ne_zero (w_slit hs)

theorem ell_re (δ : ℝ) (s : ℂ) : (ell δ s).re = (3 + δ - s.re) / 2 := by simp [ell]

theorem ell_im (δ : ℝ) (s : ℂ) : (ell δ s).im = -s.im / 2 := by simp [ell]

/-- **Jordan**: `|arg z| · Re z ≤ (π/2) |Im z|` para `Re z > 0`. -/
theorem arg_mul_re_le {z : ℂ} (hz : 0 < z.re) : |arg z| * z.re ≤ π / 2 * |z.im| := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr (fun h => by rw [h, zero_re] at hz; exact lt_irrefl 0 hz)
  rw [Complex.arg_of_re_nonneg hz.le]
  set x : ℝ := z.im / ‖z‖ with hx
  have hx1 : |x| ≤ 1 := by
    rw [hx, abs_div, abs_of_pos hn, div_le_one hn]
    exact Complex.abs_im_le_norm z
  have habs : |Real.arcsin x| = Real.arcsin |x| := by
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg (Real.arcsin_nonneg.mpr h)]
    · rw [abs_of_nonpos h, abs_of_nonpos (Real.arcsin_nonpos.mpr h), Real.arcsin_neg]
  have ha0 : 0 ≤ Real.arcsin |x| := Real.arcsin_nonneg.mpr (abs_nonneg x)
  have ha1 : Real.arcsin |x| ≤ π / 2 := Real.arcsin_le_pi_div_two _
  have hj := Real.mul_le_sin ha0 ha1
  rw [Real.sin_arcsin (by linarith [abs_nonneg x]) hx1] at hj
  have hle : Real.arcsin |x| ≤ π / 2 * |x| := by
    have hp : 0 < π := Real.pi_pos
    have := mul_le_mul_of_nonneg_left hj (by positivity : (0 : ℝ) ≤ π / 2)
    calc Real.arcsin |x| = π / 2 * (2 / π * Real.arcsin |x|) := by field_simp
      _ ≤ π / 2 * |x| := this
  rw [habs]
  have hxre : |x| * z.re ≤ |z.im| := by
    rw [hx, abs_div, abs_of_pos hn, div_mul_eq_mul_div, div_le_iff₀ hn]
    exact mul_le_mul_of_nonneg_left (Complex.re_le_norm z) (abs_nonneg _)
  calc Real.arcsin |x| * z.re ≤ π / 2 * |x| * z.re := mul_le_mul_of_nonneg_right hle hz.le
    _ = π / 2 * (|x| * z.re) := by ring
    _ ≤ π / 2 * |z.im| := mul_le_mul_of_nonneg_left hxre (by positivity)

/-- O fator angular: `0 ≤ −arg w(s) · Im s/2 ≤ π(Re s + 2)/4` para `Im s ≥ 0`, e `≤ 0` para `Im s < 0`. -/
theorem fator_arg {s : ℂ} (hs : -2 < s.re) :
    -(arg (w s) * (s.im / 2)) ≤ π * (s.re + 2) / 4 := by
  have harg : arg (w s) < 0 := Complex.arg_neg_iff.mpr (by rw [w_im]; linarith)
  rcases le_or_gt s.im 0 with ht | ht
  · have : 0 ≤ arg (w s) * (s.im / 2) := mul_nonneg_of_nonpos_of_nonpos harg.le (by linarith)
    have : 0 ≤ π * (s.re + 2) / 4 := by
      have := Real.pi_pos
      have : 0 < s.re + 2 := by linarith
      positivity
    linarith
  · have hre : 0 < (w s).re := by rw [w_re]; exact ht
    have hj := arg_mul_re_le hre
    rw [w_re, w_im, abs_neg, abs_of_pos (by linarith : 0 < s.re + 2), abs_of_neg harg] at hj
    nlinarith

theorem fator_arg_nonneg {s : ℂ} (hs : -2 < s.re) (ht : 0 ≤ s.im) : 0 ≤ -(arg (w s) * (s.im / 2)) := by
  have harg : arg (w s) < 0 := Complex.arg_neg_iff.mpr (by rw [w_im]; linarith)
  have : arg (w s) * (s.im / 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg harg.le (by linarith)
  linarith

/-- `‖w^{−ℓ}‖ = ‖s + 2‖^{−(3+δ−σ)/2} · e^{−arg w · Im(−ℓ)}`. -/
theorem norm_peso (δ : ℝ) {s : ℂ} (hs : -2 < s.re) :
    ‖(w s) ^ (-(ell δ s))‖ = ‖s + 2‖ ^ (-((3 + δ - s.re) / 2)) * Real.exp (-(arg (w s) * (s.im / 2))) := by
  rw [Complex.norm_cpow_of_ne_zero (w_ne_zero hs), norm_w, neg_re, ell_re, neg_im, ell_im,
    Real.exp_neg, div_eq_mul_inv]
  congr 2
  ring_nf

/-! ## 2. A função `g` e as retas -/

/-- `g(s) = ζ₁(s) · w(s)^{−ℓ(s)}`. -/
noncomputable def g (δ : ℝ) (s : ℂ) : ℂ := riemannZeta₁ s * (w s) ^ (-(ell δ s))

theorem differentiableAt_g (δ : ℝ) {s : ℂ} (hs : -2 < s.re) : DifferentiableAt ℂ (g δ) s := by
  unfold g
  refine (differentiable_riemannZeta₁ s).mul ?_
  exact DifferentiableAt.cpow (by unfold w; fun_prop) (by unfold ell; fun_prop) (w_slit hs)

theorem norm_g (δ : ℝ) {s : ℂ} (hs : -2 < s.re) :
    ‖g δ s‖ = ‖riemannZeta₁ s‖ * (‖s + 2‖ ^ (-((3 + δ - s.re) / 2)) *
      Real.exp (-(arg (w s) * (s.im / 2)))) := by
  rw [g, norm_mul, norm_peso δ hs]

theorem one_le_norm_s2 {s : ℂ} (hs : -1 ≤ s.re) : 1 ≤ ‖s + 2‖ := by
  have h := Complex.abs_re_le_norm (s + 2)
  rw [add_re, re_ofNat, abs_of_nonneg (by linarith)] at h
  linarith

theorem norm_s1_le {s : ℂ} (hs : -1 / 2 ≤ s.re) : ‖s - 1‖ ≤ ‖s + 2‖ := by
  have h : ‖s - 1‖ ^ 2 ≤ ‖s + 2‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [sub_re, add_re, sub_im, add_im, one_re, one_im, re_ofNat, im_ofNat, sub_zero, add_zero]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- `|ζ(s)| ≤ 2 + 1/δ` em `Re s = 1 + δ`. -/
theorem norm_zeta_dir {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hs : s.re = 1 + δ) : ‖riemannZeta s‖ ≤ 2 + 1 / δ := by
  have h := ATK.ZetaTroca.norm_zeta_sub_one_le (s := s) (by rw [hs]; linarith)
  rw [hs] at h
  have h1 : (2 : ℝ) ^ (-(1 + δ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ (1 - (1 + δ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (1 - (1 + δ)) / (1 + δ - 1) ≤ 1 / δ := by
    rw [show 1 + δ - 1 = δ by ring]
    exact div_le_div_of_nonneg_right h2 hδ.le
  have h4 : ‖riemannZeta s‖ ≤ ‖riemannZeta s - 1‖ + 1 := by
    have := norm_sub_norm_le (riemannZeta s) 1
    rw [norm_one] at this
    linarith
  linarith

/-- O fator angular é `≤ e⁴` em `−1 ≤ Re s ≤ 2`. -/
theorem fator_le_exp4 {s : ℂ} (h1 : -1 ≤ s.re) (h2 : s.re ≤ 2) :
    Real.exp (-(arg (w s) * (s.im / 2))) ≤ Real.exp 4 := by
  apply Real.exp_le_exp.mpr
  have hF := fator_arg (s := s) (by linarith)
  have : π * (s.re + 2) / 4 ≤ 4 := by nlinarith [Real.pi_le_four, Real.pi_pos]
  linarith

/-- **A reta direita** `Re s = 1 + δ`: `‖g‖ ≤ (2 + 1/δ) e⁴`. -/
theorem g_dir {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) {s : ℂ} (hs : s.re = 1 + δ) :
    ‖g δ s‖ ≤ (2 + 1 / δ) * Real.exp 4 := by
  have hs2 : -2 < s.re := by rw [hs]; linarith
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; linarith
  rw [norm_g δ hs2, ATK.RHLogZeta.zeta₁_eq hs1, norm_mul]
  have hn1 := one_le_norm_s2 (s := s) (by rw [hs]; linarith)
  have hn0 : 0 < ‖s + 2‖ := by linarith
  have hsm := norm_s1_le (s := s) (by rw [hs]; linarith)
  have hz := norm_zeta_dir hδ hs
  have hE := fator_le_exp4 (s := s) (by rw [hs]; linarith) (by rw [hs]; linarith)
  have hexp : ‖s + 2‖ ^ (-((3 + δ - s.re) / 2)) = ‖s + 2‖⁻¹ := by
    rw [hs, show -((3 + δ - (1 + δ)) / 2) = (-1 : ℝ) by ring, Real.rpow_neg_one]
  rw [hexp]
  have hE0 : 0 ≤ Real.exp (-(arg (w s) * (s.im / 2))) := (Real.exp_pos _).le
  calc ‖s - 1‖ * ‖riemannZeta s‖ * (‖s + 2‖⁻¹ * Real.exp (-(arg (w s) * (s.im / 2))))
      ≤ ‖s + 2‖ * (2 + 1 / δ) * (‖s + 2‖⁻¹ * Real.exp 4) := by
        apply mul_le_mul (mul_le_mul hsm hz (norm_nonneg _) hn0.le)
          (mul_le_mul_of_nonneg_left hE (by positivity)) (by positivity) (by positivity)
    _ = (2 + 1 / δ) * Real.exp 4 := by field_simp

/-- **A reta esquerda** `Re s = −δ` (equação funcional): `‖g‖ ≤ 2C_Γ 4^{½+δ} (2 + 1/δ) e⁴`. -/
theorem g_esq {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) {s : ℂ} (hs : s.re = -δ) :
    ‖g δ s‖ ≤ 2 * CΓ * 4 ^ (1 / 2 + δ) * (2 + 1 / δ) * Real.exp 4 := by
  have hs2 : -2 < s.re := by rw [hs]; linarith
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; linarith
  rw [norm_g δ hs2, ATK.RHLogZeta.zeta₁_eq hs1, norm_mul]
  set u : ℂ := 1 - s with hu
  have hure : u.re = 1 + δ := by rw [hu, sub_re, one_re, hs]; ring
  have hu1 : u ≠ 1 := fun h => by rw [h, one_re] at hure; linarith
  have hfe := norm_zeta_one_sub_le (w := u) (by linarith) (by linarith) hu1
  rw [show (1 : ℂ) - u = s by rw [hu]; ring, hure, show 1 + δ - 1 / 2 = 1 / 2 + δ by ring] at hfe
  have hzu := norm_zeta_dir hδ hure
  have hn1 := one_le_norm_s2 (s := s) (by rw [hs]; linarith)
  have hn0 : 0 < ‖s + 2‖ := by linarith
  have hun : ‖u‖ ≤ 4 * ‖s + 2‖ := by
    calc ‖u‖ = ‖3 - (s + 2)‖ := by rw [hu]; ring_nf
      _ ≤ ‖(3 : ℂ)‖ + ‖s + 2‖ := norm_sub_le _ _
      _ ≤ 4 * ‖s + 2‖ := by rw [norm_ofNat]; linarith
  have hupow : ‖u‖ ^ (1 / 2 + δ) ≤ 4 ^ (1 / 2 + δ) * ‖s + 2‖ ^ (1 / 2 + δ) := by
    rw [← Real.mul_rpow (by norm_num) (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) hun (by linarith)
  have hsm := norm_s1_le (s := s) (by rw [hs]; linarith)
  have hE := fator_le_exp4 (s := s) (by rw [hs]; linarith) (by rw [hs]; linarith)
  have hexp : ‖s + 2‖ ^ (-((3 + δ - s.re) / 2)) = ‖s + 2‖ ^ (-(3 / 2 + δ)) := by
    rw [hs]; congr 1; ring
  rw [hexp]
  have hcanc : ‖s + 2‖ * ‖s + 2‖ ^ (1 / 2 + δ) * ‖s + 2‖ ^ (-(3 / 2 + δ)) = 1 := by
    have h1 : ‖s + 2‖ ^ (1 / 2 + δ) * ‖s + 2‖ ^ (-(3 / 2 + δ)) = ‖s + 2‖ ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    rw [mul_assoc, h1, Real.rpow_neg_one, mul_inv_cancel₀ hn0.ne']
  have hC := CΓ_pos
  have hζs : ‖riemannZeta s‖ ≤ 2 * CΓ * (4 ^ (1 / 2 + δ) * ‖s + 2‖ ^ (1 / 2 + δ)) * (2 + 1 / δ) := by
    calc ‖riemannZeta s‖ ≤ 2 * CΓ * ‖u‖ ^ (1 / 2 + δ) * ‖riemannZeta u‖ := hfe
      _ ≤ 2 * CΓ * (4 ^ (1 / 2 + δ) * ‖s + 2‖ ^ (1 / 2 + δ)) * (2 + 1 / δ) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hupow (by positivity)) hzu (norm_nonneg _)
            (by positivity)
  have hE0 : 0 ≤ Real.exp (-(arg (w s) * (s.im / 2))) := (Real.exp_pos _).le
  have hP : 0 ≤ ‖s + 2‖ ^ (-(3 / 2 + δ)) := by positivity
  calc ‖s - 1‖ * ‖riemannZeta s‖ * (‖s + 2‖ ^ (-(3 / 2 + δ)) * Real.exp (-(arg (w s) * (s.im / 2))))
      ≤ ‖s + 2‖ * (2 * CΓ * (4 ^ (1 / 2 + δ) * ‖s + 2‖ ^ (1 / 2 + δ)) * (2 + 1 / δ)) *
          (‖s + 2‖ ^ (-(3 / 2 + δ)) * Real.exp 4) := by
        apply mul_le_mul (mul_le_mul hsm hζs (norm_nonneg _) hn0.le)
          (mul_le_mul_of_nonneg_left hE hP) (by positivity) (by positivity)
    _ = 2 * CΓ * 4 ^ (1 / 2 + δ) * (2 + 1 / δ) * Real.exp 4 *
          (‖s + 2‖ * ‖s + 2‖ ^ (1 / 2 + δ) * ‖s + 2‖ ^ (-(3 / 2 + δ))) := by ring
    _ = 2 * CΓ * 4 ^ (1 / 2 + δ) * (2 + 1 / δ) * Real.exp 4 := by rw [hcanc, mul_one]

/-! ## 3. Crescimento na faixa e Phragmén–Lindelöf -/

/-- **Crescimento polinomial**: para `−½ ≤ Re s ≤ 3/2`, `|Im s| ≥ 1`, `‖ζ₁(s)‖ ≤ 6(1 + 2C_Γ)(2 + |Im s|)³`. -/
theorem norm_zeta₁_faixa {s : ℂ} (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3 / 2) (him : 1 ≤ |s.im|) :
    ‖riemannZeta₁ s‖ ≤ 6 * (1 + 2 * CΓ) * (2 + |s.im|) ^ 3 := by
  have hs1 : s ≠ 1 := fun h => by rw [h, one_im, abs_zero] at him; linarith
  rw [ATK.RHLogZeta.zeta₁_eq hs1, norm_mul]
  set t : ℝ := |s.im| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  have hC := CΓ_pos
  have hs1n : ‖s - 1‖ ≤ 2 + t := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    simp only [sub_re, one_re, sub_im, one_im, sub_zero] at h
    have : |s.re - 1| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  have hζ : ‖riemannZeta s‖ ≤ (1 + 2 * CΓ) * (2 + t) * (3 * t + 12) := by
    rcases le_or_gt (1 / 2) s.re with hr | hr
    · have h := ATK.ZeroClasses.RegiaoLivre.cota_zeta_faixa hr (by linarith) him
      have h1' : 1 ≤ (1 + 2 * CΓ) * (2 + t) := by nlinarith
      have h3 : 0 ≤ 3 * t + 12 := by linarith
      calc ‖riemannZeta s‖ ≤ 3 * t + 12 := h
        _ = 1 * (3 * t + 12) := (one_mul _).symm
        _ ≤ (1 + 2 * CΓ) * (2 + t) * (3 * t + 12) := mul_le_mul_of_nonneg_right h1' h3
    · set u : ℂ := 1 - s with hu
      have hure : u.re = 1 - s.re := by rw [hu, sub_re, one_re]
      have huim : |u.im| = t := by rw [hu, sub_im, one_im, zero_sub, abs_neg]
      have hu1 : u ≠ 1 := fun h => by rw [h, one_im, abs_zero] at huim; linarith
      have hfe := norm_zeta_one_sub_le (w := u) (by rw [hure]; linarith) (by rw [hure]; linarith) hu1
      rw [show (1 : ℂ) - u = s by rw [hu]; ring] at hfe
      have hzu := ATK.ZeroClasses.RegiaoLivre.cota_zeta_faixa (s := u) (by rw [hure]; linarith)
        (by rw [hure]; linarith) (by rw [huim]; exact him)
      rw [huim] at hzu
      have hun1 : 1 ≤ ‖u‖ := le_trans (by rw [huim]; exact him) (Complex.abs_im_le_norm u)
      have hun : ‖u‖ ≤ 2 + t := by
        have h := Complex.norm_le_abs_re_add_abs_im u
        rw [huim, hure] at h
        have : |1 - s.re| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
        linarith
      have hpow : ‖u‖ ^ (u.re - 1 / 2) ≤ ‖u‖ := by
        conv_rhs => rw [← Real.rpow_one ‖u‖]
        exact Real.rpow_le_rpow_of_exponent_le hun1 (by rw [hure]; linarith)
      calc ‖riemannZeta s‖ ≤ 2 * CΓ * ‖u‖ ^ (u.re - 1 / 2) * ‖riemannZeta u‖ := hfe
        _ ≤ 2 * CΓ * (2 + t) * (3 * t + 12) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left (hpow.trans hun) (by positivity)) hzu
              (norm_nonneg _) (by positivity)
        _ ≤ (1 + 2 * CΓ) * (2 + t) * (3 * t + 12) := by
            have : 0 ≤ (2 + t) * (3 * t + 12) := by positivity
            nlinarith
  calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ (2 + t) * ((1 + 2 * CΓ) * (2 + t) * (3 * t + 12)) :=
        mul_le_mul hs1n hζ (norm_nonneg _) (by positivity)
    _ ≤ 6 * (1 + 2 * CΓ) * (2 + t) ^ 3 := by
        have h6 : 3 * t + 12 ≤ 6 * (2 + t) := by linarith
        have h0 : 0 ≤ (1 + 2 * CΓ) * (2 + t) ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_left h6 h0
        nlinarith

/-- `(2 + x)³ ≤ 6e² · exp(exp x)` para `x ≥ 0`. -/
theorem cubo_le {x : ℝ} (hx : 0 ≤ x) : (2 + x) ^ 3 ≤ 6 * Real.exp 2 * Real.exp (Real.exp x) := by
  have h1 := Real.pow_div_factorial_le_exp (2 + x) (by linarith) 3
  have hf : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hf, div_le_iff₀ (by norm_num)] at h1
  have h6 : (2 + x) ^ 3 ≤ 6 * Real.exp (2 + x) := by linarith
  have h2 : Real.exp (2 + x) ≤ Real.exp 2 * Real.exp (Real.exp x) := by
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [Real.add_one_le_exp x]))
      (Real.exp_pos _).le
  nlinarith

/-- **Phragmén–Lindelöf**: `‖g(s)‖ ≤ C_g` em `−δ ≤ Re s ≤ 1 + δ`. -/
theorem g_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (z : ℂ) (hza : -δ ≤ z.re) (hzb : z.re ≤ 1 + δ) :
    ‖g δ z‖ ≤ max (2 * CΓ * 4 ^ (1 / 2 + δ) * (2 + 1 / δ) * Real.exp 4) ((2 + 1 / δ) * Real.exp 4) := by
  have hsub : closure (re ⁻¹' Ioo (-δ) (1 + δ)) ⊆ re ⁻¹' Icc (-δ) (1 + δ) :=
    closure_minimal (fun w hw => ⟨le_of_lt hw.1, le_of_lt hw.2⟩)
      (isClosed_Icc.preimage Complex.continuous_re)
  refine PhragmenLindelof.vertical_strip (a := -δ) (b := 1 + δ) ?_ ?_ ?_ ?_ hza hzb
  · refine ⟨fun w (hw : w ∈ re ⁻¹' Ioo (-δ) (1 + δ)) =>
      (differentiableAt_g δ (by have := hw.1; linarith)).differentiableWithinAt, fun w hw => ?_⟩
    have hw' := hsub hw
    exact (differentiableAt_g δ (by have := hw'.1; linarith)).continuousAt.continuousWithinAt
  · refine ⟨1, by
      have := Real.pi_gt_three
      rw [show 1 + δ - -δ = 1 + 2 * δ by ring, lt_div_iff₀ (by linarith)]
      nlinarith, 1, ?_⟩
    have hC := CΓ_pos
    refine Asymptotics.IsBigO.of_bound (6 * (1 + 2 * CΓ) * Real.exp 4 * (6 * Real.exp 2)) ?_
    refine Filter.eventually_inf_principal.mpr ?_
    filter_upwards [(eventually_ge_atTop (1 : ℝ)).comap (_root_.abs ∘ im)] with z hz hzs
    simp only [Function.comp_apply] at hz
    have hz1 : -1 / 2 ≤ z.re := by have := hzs.1; linarith
    have hz2 : z.re ≤ 3 / 2 := by have := hzs.2; linarith
    rw [norm_g δ (by linarith)]
    have hn1 := one_le_norm_s2 (s := z) (by linarith)
    have hX : ‖z + 2‖ ^ (-((3 + δ - z.re) / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
    have hE := fator_le_exp4 (s := z) (by linarith) (by linarith)
    have hζ := norm_zeta₁_faixa hz1 hz2 hz
    have hcubo := cubo_le (abs_nonneg z.im)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul, one_mul]
    have hP : 0 ≤ ‖z + 2‖ ^ (-((3 + δ - z.re) / 2)) := by positivity
    calc ‖riemannZeta₁ z‖ * (‖z + 2‖ ^ (-((3 + δ - z.re) / 2)) * Real.exp (-(arg (w z) * (z.im / 2))))
        ≤ (6 * (1 + 2 * CΓ) * (2 + |z.im|) ^ 3) * (1 * Real.exp 4) :=
          mul_le_mul hζ (mul_le_mul hX hE (Real.exp_pos _).le zero_le_one) (by positivity) (by positivity)
      _ = 6 * (1 + 2 * CΓ) * Real.exp 4 * (2 + |z.im|) ^ 3 := by ring
      _ ≤ 6 * (1 + 2 * CΓ) * Real.exp 4 * (6 * Real.exp 2 * Real.exp (Real.exp |z.im|)) :=
          mul_le_mul_of_nonneg_left hcubo (by positivity)
      _ = _ := by ring
  · intro z hz
    exact (g_esq hδ hδ1 hz).trans (le_max_left _ _)
  · intro z hz
    exact (g_dir hδ hδ1 hz).trans (le_max_right _ _)

/-! ## 4. A cota de convexidade -/

/-- O caso `t ≥ 1`: `‖ζ(σ + it)‖ ≤ 16 C_g t^{(1−σ+δ)/2}`. -/
theorem convexidade_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 1 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      16 * max (2 * CΓ * 4 ^ (1 / 2 + δ) * (2 + 1 / δ) * Real.exp 4) ((2 + 1 / δ) * Real.exp 4) *
        t ^ ((1 - σ + δ) / 2) := by
  set Cg : ℝ := max (2 * CΓ * 4 ^ (1 / 2 + δ) * (2 + 1 / δ) * Real.exp 4) ((2 + 1 / δ) * Real.exp 4)
    with hCg
  have hCg0 : 0 ≤ Cg := le_trans (by positivity) (le_max_right _ _)
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have h := g_le hδ hδ1 s (by rw [hsre]; linarith) (by rw [hsre]; linarith)
  rw [norm_g δ (by rw [hsre]; linarith), hsre] at h
  have hF0 := fator_arg_nonneg (s := s) (by rw [hsre]; linarith) (by rw [hsim]; linarith)
  have hE1 : 1 ≤ Real.exp (-(arg (w s) * (s.im / 2))) := Real.one_le_exp hF0
  have hn1 := one_le_norm_s2 (s := s) (by rw [hsre]; linarith)
  have hn0 : 0 < ‖s + 2‖ := by linarith
  set e : ℝ := (3 + δ - σ) / 2 with he
  have hp : 0 < ‖s + 2‖ ^ (-e) := Real.rpow_pos_of_pos hn0 _
  have h' : ‖riemannZeta₁ s‖ * ‖s + 2‖ ^ (-e) ≤ Cg := by
    have := mul_le_mul_of_nonneg_left hE1 (mul_nonneg (norm_nonneg (riemannZeta₁ s)) hp.le)
    calc ‖riemannZeta₁ s‖ * ‖s + 2‖ ^ (-e) = ‖riemannZeta₁ s‖ * ‖s + 2‖ ^ (-e) * 1 := (mul_one _).symm
      _ ≤ ‖riemannZeta₁ s‖ * ‖s + 2‖ ^ (-e) * Real.exp (-(arg (w s) * (s.im / 2))) := this
      _ = ‖riemannZeta₁ s‖ * (‖s + 2‖ ^ (-e) * Real.exp (-(arg (w s) * (s.im / 2)))) := by ring
      _ ≤ Cg := h
  have hz1 : ‖riemannZeta₁ s‖ ≤ Cg * ‖s + 2‖ ^ e := by
    have hpe : ‖s + 2‖ ^ (-e) * ‖s + 2‖ ^ e = 1 := by
      rw [← Real.rpow_add hn0, neg_add_cancel, Real.rpow_zero]
    calc ‖riemannZeta₁ s‖ = ‖riemannZeta₁ s‖ * ‖s + 2‖ ^ (-e) * ‖s + 2‖ ^ e := by
          rw [mul_assoc, hpe, mul_one]
      _ ≤ Cg * ‖s + 2‖ ^ e := mul_le_mul_of_nonneg_right h' (by positivity)
  have hs1 : s ≠ 1 := fun h1 => by rw [h1, one_im] at hsim; linarith
  rw [ATK.RHLogZeta.zeta₁_eq hs1, norm_mul] at hz1
  have hsm : t ≤ ‖s - 1‖ := by
    have h2 := Complex.abs_im_le_norm (s - 1)
    rw [sub_im, one_im, sub_zero, hsim, abs_of_pos (by linarith)] at h2
    exact h2
  have hX : ‖s + 2‖ ≤ 4 * t := by
    have h2 := Complex.norm_le_abs_re_add_abs_im (s + 2)
    rw [add_re, add_im, hsre, hsim, re_ofNat, im_ofNat, add_zero, abs_of_nonneg (by linarith),
      abs_of_pos (by linarith)] at h2
    linarith
  have he0 : 0 ≤ e := by rw [he]; linarith
  have he2 : e ≤ 2 := by rw [he]; linarith
  have hXe : ‖s + 2‖ ^ e ≤ 16 * t ^ e := by
    calc ‖s + 2‖ ^ e ≤ (4 * t) ^ e := Real.rpow_le_rpow (norm_nonneg _) hX he0
      _ = 4 ^ e * t ^ e := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 16 * t ^ e := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc (4 : ℝ) ^ e ≤ 4 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) he2
            _ = 16 := by norm_num
  have ht0 : 0 < t := by linarith
  have hte : t ^ e = t * t ^ ((1 - σ + δ) / 2) := by
    rw [show e = 1 + (1 - σ + δ) / 2 by rw [he]; ring, Real.rpow_add ht0, Real.rpow_one]
  have hζ0 : 0 ≤ ‖riemannZeta s‖ := norm_nonneg _
  have hmain : t * ‖riemannZeta s‖ ≤ t * (16 * Cg * t ^ ((1 - σ + δ) / 2)) := by
    calc t * ‖riemannZeta s‖ ≤ ‖s - 1‖ * ‖riemannZeta s‖ := mul_le_mul_of_nonneg_right hsm hζ0
      _ ≤ Cg * ‖s + 2‖ ^ e := hz1
      _ ≤ Cg * (16 * t ^ e) := mul_le_mul_of_nonneg_left hXe hCg0
      _ = t * (16 * Cg * t ^ ((1 - σ + δ) / 2)) := by rw [hte]; ring
  exact le_of_mul_le_mul_left hmain ht0

/-- **A cota de convexidade**: para `0 < δ ≤ ½` há `C` com `‖ζ(σ + it)‖ ≤ C |t|^{(1−σ+δ)/2}` em `0 ≤ σ ≤ 1`,
`|t| ≥ 1`. -/
theorem convexidade {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 → 1 ≤ |t| →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * |t| ^ ((1 - σ + δ) / 2) := by
  refine ⟨16 * max (2 * CΓ * 4 ^ (1 / 2 + δ) * (2 + 1 / δ) * Real.exp 4) ((2 + 1 / δ) * Real.exp 4),
    by have := CΓ_pos; positivity, fun σ t hσ0 hσ1 ht => ?_⟩
  rcases le_or_gt 0 t with h0 | h0
  · rw [abs_of_nonneg h0] at ht ⊢
    exact convexidade_pos hδ hδ1 hσ0 hσ1 ht
  · rw [abs_of_neg h0] at ht ⊢
    have e : (σ : ℂ) + (t : ℂ) * I = (starRingEnd ℂ) ((σ : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      apply Complex.ext <;> simp
    rw [e, riemannZeta_conj, Complex.norm_conj]
    exact convexidade_pos hδ hδ1 hσ0 hσ1 ht

/-- **`ζ(½ + it) = O((1 + |t|)^{1/4+ε})`**. -/
theorem convexidade_meio {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t : ℝ, ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ (1 / 4 + ε) := by
  set δ : ℝ := min (2 * ε) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ ≤ 1 / 2 := min_le_right _ _
  have hδ2 : δ ≤ 2 * ε := min_le_left _ _
  obtain ⟨C, hC0, hC⟩ := convexidade hδ0 hδ1
  refine ⟨max C 12, fun t => ?_⟩
  have h1t : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hpow1 : 1 ≤ (1 + |t|) ^ (1 / 4 + ε) := Real.one_le_rpow h1t (by linarith)
  rcases le_or_gt 1 |t| with ht | ht
  · have h := hC (1 / 2) t (by norm_num) (by norm_num) ht
    push_cast at h
    have hexp : |t| ^ ((1 - 1 / 2 + δ) / 2) ≤ (1 + |t|) ^ (1 / 4 + ε) := by
      calc |t| ^ ((1 - 1 / 2 + δ) / 2) ≤ (1 + |t|) ^ ((1 - 1 / 2 + δ) / 2) :=
            Real.rpow_le_rpow (abs_nonneg t) (by linarith) (by linarith)
        _ ≤ (1 + |t|) ^ (1 / 4 + ε) := Real.rpow_le_rpow_of_exponent_le h1t (by linarith)
    calc ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ C * |t| ^ ((1 - 1 / 2 + δ) / 2) := h
      _ ≤ C * (1 + |t|) ^ (1 / 4 + ε) := mul_le_mul_of_nonneg_left hexp hC0
      _ ≤ max C 12 * (1 + |t|) ^ (1 / 4 + ε) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · set s : ℂ := 1 / 2 + (t : ℂ) * I with hs
    have hsre : s.re = 1 / 2 := by simp [hs]
    have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hsre; norm_num at hsre
    have hq := ATK.ZeroClasses.VariacaoArg.cota_zeta_quarto (s := s) (by rw [hsre]; norm_num) hs1
    have hm : 1 / 2 ≤ ‖s - 1‖ := by
      have h := Complex.abs_re_le_norm (s - 1)
      rw [sub_re, one_re, hsre] at h
      norm_num at h ⊢
      linarith
    have hsn : ‖s‖ ≤ 3 / 2 := by
      have h := Complex.norm_le_abs_re_add_abs_im s
      have him : s.im = t := by simp [hs]
      rw [hsre, him] at h
      norm_num at h
      linarith
    have hinv : 1 / ‖s - 1‖ ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have h12 : ‖riemannZeta s‖ ≤ 12 := by linarith
    calc ‖riemannZeta s‖ ≤ 12 := h12
      _ ≤ max C 12 := le_max_right _ _
      _ = max C 12 * 1 := (mul_one _).symm
      _ ≤ max C 12 * (1 + |t|) ^ (1 / 4 + ε) :=
          mul_le_mul_of_nonneg_left hpow1 (le_trans (by norm_num) (le_max_right _ _))

end ATK.ZeroClasses.Convexidade

#print axioms ATK.ZeroClasses.Convexidade.w_re
#print axioms ATK.ZeroClasses.Convexidade.w_im
#print axioms ATK.ZeroClasses.Convexidade.norm_w
#print axioms ATK.ZeroClasses.Convexidade.w_slit
#print axioms ATK.ZeroClasses.Convexidade.w_ne_zero
#print axioms ATK.ZeroClasses.Convexidade.ell_re
#print axioms ATK.ZeroClasses.Convexidade.ell_im
#print axioms ATK.ZeroClasses.Convexidade.arg_mul_re_le
#print axioms ATK.ZeroClasses.Convexidade.fator_arg
#print axioms ATK.ZeroClasses.Convexidade.fator_arg_nonneg
#print axioms ATK.ZeroClasses.Convexidade.norm_peso
#print axioms ATK.ZeroClasses.Convexidade.differentiableAt_g
#print axioms ATK.ZeroClasses.Convexidade.norm_g
#print axioms ATK.ZeroClasses.Convexidade.one_le_norm_s2
#print axioms ATK.ZeroClasses.Convexidade.norm_s1_le
#print axioms ATK.ZeroClasses.Convexidade.norm_zeta_dir
#print axioms ATK.ZeroClasses.Convexidade.fator_le_exp4
#print axioms ATK.ZeroClasses.Convexidade.g_dir
#print axioms ATK.ZeroClasses.Convexidade.g_esq
#print axioms ATK.ZeroClasses.Convexidade.norm_zeta₁_faixa
#print axioms ATK.ZeroClasses.Convexidade.cubo_le
#print axioms ATK.ZeroClasses.Convexidade.g_le
#print axioms ATK.ZeroClasses.Convexidade.convexidade_pos
#print axioms ATK.ZeroClasses.Convexidade.convexidade
#print axioms ATK.ZeroClasses.Convexidade.convexidade_meio
