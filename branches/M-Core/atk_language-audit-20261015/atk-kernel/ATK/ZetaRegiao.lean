import ATK.ZetaRetangulo
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# ATK — Região sem zeros em **toda** altura: o fim fechado entra na faixa

Com a desigualdade `3–4–1` da Mathlib (`|ζ(1+x)³ ζ(1+x+it)⁴ ζ(1+x+2it)| ≥ 1`, via
`DirichletCharacter.norm_LFunction_product_ge_one`) e cotas explícitas tiradas da representação
`ζ(s) = s/(s−1) − s·∫_1^∞ {u} u^{−s−1} du` (`ATK.ZetaStrip`), o kernel prova:

* `norm_zeta_real_le`: `|ζ(σ)| ≤ σ/(σ−1)` para `σ > 1`;
* `norm_zeta_le`: `|ζ(s)| ≤ |s|/|s−1| + |s|/(2 Re s)` para `Re s > 0`;
* `norm_H_sub_le`: `|H(σ+it) − H(β+it)| ≤ 1/β − 1/σ` (sem derivadas);
* `norm_zeta_le_de_zero`: se `ζ(β+it) = 0`, então `|ζ(σ+it)| ≤ (σ−β)(9 + 4|t|)`;
* **`regiao_sem_zeros`**: para `|t| ≥ 1/2`, todo zero `β + it` tem
  `β < 1 − 1/(256·(9+4|t|)⁴·(3+3|t|))`;
* **`faixa_estreitada`**: todo zero não trivial `s` satisfaz
  `c(t) < Re s < 1 − c(t)` com `c(t) = 1/(256·(9+4|t|)⁴·(3+3|t|)) > 0`, `t = Im s`.

Na geometria de `I`: o início fechado e o fim fechado **entram na faixa em toda altura** (antes só
`Re s ≥ 1` e `Re s ≤ 0` eram conhecidos no kernel). A largura ganha decai como `|t|⁻⁵`; a região
clássica de de la Vallée Poussin (`c/log|t|`) é mais forte, e o meio (`c = 1/2`) é RH (O1).
-/

open Complex Set MeasureTheory Filter Topology

namespace ATK.ZetaRegiao

open ATK.ZetaStrip ATK.ZetaSimetria ATK.ZetaRetangulo

/-- **Desigualdade 3–4–1** para ζ (Mathlib). -/
theorem tres_quatro_um {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖riemannZeta (1 + x)‖ ^ 3 * ‖riemannZeta (1 + x + I * y)‖ ^ 4 *
      ‖riemannZeta (1 + x + 2 * I * y)‖ := by
  have h := DirichletCharacter.norm_LFunction_product_ge_one (N := 1) (χ := 1) hx y
  have h' : ‖riemannZeta (1 + x) ^ 3 * riemannZeta (1 + x + I * y) ^ 4 *
      riemannZeta (1 + x + 2 * I * y)‖ ≥ 1 := by
    simpa [DirichletCharacter.LFunctionTrivChar] using h
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at h'
  exact h'

theorem zeta_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s * H s := by
  have h := H_eq_zeta hs hs1
  have hs0 : s ≠ 0 := by intro h0; rw [h0, zero_re] at hs; exact lt_irrefl 0 hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [h]
  field_simp
  ring

/-- `|ζ(σ)| ≤ σ/(σ−1)` para `σ > 1`. -/
theorem norm_zeta_real_le {σ : ℝ} (hσ : 1 < σ) : ‖riemannZeta σ‖ ≤ σ / (σ - 1) := by
  have h0 : (0 : ℝ) < (σ : ℂ).re := by simp; linarith
  have h1 : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hσ0 : 0 < σ := by linarith
  rw [zeta_eq h0 h1, H_real]
  have hHr : (∫ t in Ioi (1 : ℝ), t ^ (-σ - 1) * Int.fract t) = Hr σ := rfl
  rw [hHr]
  have hle := Hr_le hσ0
  have hge : 0 ≤ Hr σ := H_real_nonneg σ
  have h2 : σ * Hr σ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hle hσ0.le
    rwa [show σ * (1 / (2 * σ)) = 1 / 2 by field_simp] at this
  have h3 : 1 ≤ σ / (σ - 1) := by rw [le_div_iff₀ (by linarith)]; linarith
  have e : (σ : ℂ) / (σ - 1) - σ * (Hr σ : ℂ) = ((σ / (σ - 1) - σ * Hr σ : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- `|ζ(s)| ≤ |s|/|s−1| + |s|/(2 Re s)`. -/
theorem norm_zeta_le {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ / (2 * s.re) := by
  rw [zeta_eq hs hs1]
  calc ‖s / (s - 1) - s * H s‖ ≤ ‖s / (s - 1)‖ + ‖s * H s‖ := norm_sub_le _ _
    _ ≤ ‖s‖ / ‖s - 1‖ + ‖s‖ * (1 / (2 * s.re)) := by
        rw [norm_div, norm_mul]
        gcongr
        exact (norm_H_le (s := s)).trans (Hr_le hs)
    _ = _ := by ring

/-- `|H(σ+it) − H(β+it)| ≤ 1/β − 1/σ` para `0 < β ≤ σ`. -/
theorem norm_H_sub_le {β σ t : ℝ} (hβ : 0 < β) (hβσ : β ≤ σ) :
    ‖H (σ + t * I) - H (β + t * I)‖ ≤ 1 / β - 1 / σ := by
  have hσ : 0 < σ := lt_of_lt_of_le hβ hβσ
  rw [H_eq_integral, H_eq_integral, ← integral_sub (integrableOn_cpow_mul_fract (by simp; linarith))
    (integrableOn_cpow_mul_fract (by simp; linarith))]
  have hb : IntegrableOn (fun u : ℝ => u ^ (-β - 1) - u ^ (-σ - 1)) (Ioi 1) :=
    (integrableOn_rpow hβ).sub (integrableOn_rpow hσ)
  refine (norm_integral_le_of_norm_le hb ?_).trans (le_of_eq ?_)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
    have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one hu
    have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
    have hc : ∀ a : ℝ, (u : ℂ) ^ (-((a : ℂ) + t * I) - 1) =
        ((u ^ (-a - 1) : ℝ) : ℂ) * (u : ℂ) ^ (((-t : ℝ) : ℂ) * I) := by
      intro a
      rw [show -((a : ℂ) + t * I) - 1 = ((-a - 1 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I by push_cast; ring,
        Complex.cpow_add _ _ (by exact_mod_cast hu0.ne'), ofReal_cpow hu0.le]
    rw [hc σ, hc β]
    have hP : ‖(u : ℂ) ^ (((-t : ℝ) : ℂ) * I)‖ = 1 := by
      rw [norm_cpow_eq_rpow_re_of_pos hu0]; simp
    have hF : ‖((Int.fract u : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact (Int.fract_lt_one _).le
    have hmono : u ^ (-σ - 1) ≤ u ^ (-β - 1) := Real.rpow_le_rpow_of_exponent_le hu1 (by linarith)
    have e : ((u ^ (-σ - 1) : ℝ) : ℂ) * (u : ℂ) ^ (((-t : ℝ) : ℂ) * I) * ((Int.fract u : ℝ) : ℂ) -
        ((u ^ (-β - 1) : ℝ) : ℂ) * (u : ℂ) ^ (((-t : ℝ) : ℂ) * I) * ((Int.fract u : ℝ) : ℂ) =
        ((u ^ (-σ - 1) - u ^ (-β - 1) : ℝ) : ℂ) * ((u : ℂ) ^ (((-t : ℝ) : ℂ) * I) *
          ((Int.fract u : ℝ) : ℂ)) := by push_cast; ring
    rw [e, norm_mul, norm_mul, hP, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg (by linarith), one_mul]
    calc (u ^ (-β - 1) - u ^ (-σ - 1)) * ‖((Int.fract u : ℝ) : ℂ)‖
        ≤ (u ^ (-β - 1) - u ^ (-σ - 1)) * 1 := mul_le_mul_of_nonneg_left hF (by linarith)
      _ = u ^ (-β - 1) - u ^ (-σ - 1) := mul_one _
  · rw [integral_sub (integrableOn_rpow hβ) (integrableOn_rpow hσ), integral_rpow hβ,
      integral_rpow hσ]

/-- **Perto de um zero, ζ é pequena**: se `ζ(β+it) = 0`, `1/2 ≤ β ≤ 1`, `β ≤ σ`, `|t| ≥ 1/2`, então
`|ζ(σ+it)| ≤ (σ−β)(9 + 4|t|)`. -/
theorem norm_zeta_le_de_zero {β σ t : ℝ} (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1) (hβσ : β ≤ σ)
    (ht : 1 / 2 ≤ |t|) (hz : riemannZeta (β + t * I) = 0) :
    ‖riemannZeta (σ + t * I)‖ ≤ (σ - β) * (9 + 4 * |t|) := by
  set s1 : ℂ := σ + t * I with hs1def
  set s0 : ℂ := β + t * I with hs0def
  have hre1 : s1.re = σ := by simp [s1]
  have hre0 : s0.re = β := by simp [s0]
  have him1 : s1.im = t := by simp [s1]
  have him0 : s0.im = t := by simp [s0]
  have ht0 : t ≠ 0 := by intro h; rw [h, abs_zero] at ht; linarith
  have hs1 : s1 ≠ 1 := fun h => ht0 (by rw [← him1, h, one_im])
  have hs0 : s0 ≠ 1 := fun h => ht0 (by rw [← him0, h, one_im])
  have hσ : 1 / 2 ≤ σ := le_trans hβ hβσ
  have hz1 := zeta_eq (s := s1) (by rw [hre1]; linarith) hs1
  have hz0 := zeta_eq (s := s0) (by rw [hre0]; linarith) hs0
  rw [hz] at hz0
  have hs1' : s1 - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hs0' : s0 - 1 ≠ 0 := sub_ne_zero.mpr hs0
  have key : riemannZeta s1 =
      (s0 - s1) / ((s1 - 1) * (s0 - 1)) - ((s1 - s0) * H s1 + s0 * (H s1 - H s0)) := by
    rw [hz1]
    have e : s1 / (s1 - 1) - s0 / (s0 - 1) = (s0 - s1) / ((s1 - 1) * (s0 - 1)) := by
      field_simp; ring
    linear_combination e - hz0
  have hd : s0 - s1 = ((β - σ : ℝ) : ℂ) := by simp [s0, s1]
  have hd' : s1 - s0 = ((σ - β : ℝ) : ℂ) := by simp [s0, s1]
  have hn1 : |t| ≤ ‖s1 - 1‖ := by
    have := Complex.abs_im_le_norm (s1 - 1); simpa [s1] using this
  have hn0 : |t| ≤ ‖s0 - 1‖ := by
    have := Complex.abs_im_le_norm (s0 - 1); simpa [s0] using this
  have hns0 : ‖s0‖ ≤ 1 + |t| := by
    have := Complex.norm_le_abs_re_add_abs_im s0
    rw [hre0, him0, abs_of_nonneg (by linarith)] at this; linarith
  have hH1 : ‖H s1‖ ≤ 1 := by
    have := (norm_H_le (s := s1)).trans (Hr_le (by rw [hre1]; linarith))
    rw [hre1] at this
    have : 1 / (2 * σ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hσβ : 0 ≤ σ - β := by linarith
  have hHd : ‖H s1 - H s0‖ ≤ 4 * (σ - β) := by
    have h := norm_H_sub_le (t := t) (by linarith : 0 < β) hβσ
    have hbs : 1 / 4 ≤ β * σ := by nlinarith
    have : 1 / β - 1 / σ ≤ 4 * (σ - β) := by
      rw [div_sub_div _ _ (by linarith) (by linarith), div_le_iff₀ (by nlinarith)]
      nlinarith [mul_le_mul_of_nonneg_left hbs hσβ]
    linarith
  have hT : 1 / 4 ≤ |t| * |t| := by nlinarith
  have hA : ‖(s0 - s1) / ((s1 - 1) * (s0 - 1))‖ ≤ 4 * (σ - β) := by
    rw [norm_div, norm_mul, hd, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg hσβ, div_le_iff₀ (by nlinarith)]
    have : |t| * |t| ≤ ‖s1 - 1‖ * ‖s0 - 1‖ := mul_le_mul hn1 hn0 (abs_nonneg _) (norm_nonneg _)
    nlinarith
  have hB : ‖(s1 - s0) * H s1‖ ≤ σ - β := by
    rw [norm_mul, hd', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσβ]
    calc (σ - β) * ‖H s1‖ ≤ (σ - β) * 1 := mul_le_mul_of_nonneg_left hH1 hσβ
      _ = σ - β := mul_one _
  have hC : ‖s0 * (H s1 - H s0)‖ ≤ (1 + |t|) * (4 * (σ - β)) := by
    rw [norm_mul]; exact mul_le_mul hns0 hHd (norm_nonneg _) (by positivity)
  rw [key]
  calc ‖(s0 - s1) / ((s1 - 1) * (s0 - 1)) - ((s1 - s0) * H s1 + s0 * (H s1 - H s0))‖
      ≤ ‖(s0 - s1) / ((s1 - 1) * (s0 - 1))‖ + (‖(s1 - s0) * H s1‖ + ‖s0 * (H s1 - H s0)‖) :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ 4 * (σ - β) + ((σ - β) + (1 + |t|) * (4 * (σ - β))) := by gcongr
    _ = (σ - β) * (9 + 4 * |t|) := by ring

/-- Constante da região. -/
noncomputable def A (t : ℝ) : ℝ := (9 + 4 * |t|) ^ 4 * (3 + 3 * |t|)

theorem A_ge (t : ℝ) : 1 ≤ A t := by
  unfold A
  have h1 : (1 : ℝ) ≤ (9 + 4 * |t|) ^ 4 := one_le_pow₀ (by linarith [abs_nonneg t])
  have h2 : (1 : ℝ) ≤ 3 + 3 * |t| := by linarith [abs_nonneg t]
  nlinarith

theorem A_neg (t : ℝ) : A (-t) = A t := by unfold A; rw [abs_neg]

/-- **Região sem zeros em toda altura `|t| ≥ 1/2`.** -/
theorem regiao_sem_zeros {β t : ℝ} (ht : 1 / 2 ≤ |t|) (hz : riemannZeta (β + t * I) = 0) :
    β < 1 - 1 / (256 * A t) := by
  set x := 1 / (256 * A t) with hxdef
  have hA := A_ge t
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 256 := by
    rw [hxdef, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  by_contra hcon
  have hβx : 1 - x ≤ β := not_lt.mp hcon
  have hβ1 : β < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (by simpa using not_lt.mp h) hz
  have hβ : 1 / 2 ≤ β := by linarith
  have h341 := tres_quatro_um hx0 t
  have b1 : ‖riemannZeta (1 + x)‖ ≤ 2 / x := by
    have h := norm_zeta_real_le (σ := 1 + x) (by linarith)
    push_cast at h
    refine h.trans ?_
    rw [show 1 + x - 1 = x by ring, div_le_div_iff_of_pos_right hx0]; linarith
  have b2 : ‖riemannZeta (1 + x + I * t)‖ ≤ (1 + x - β) * (9 + 4 * |t|) := by
    have h := norm_zeta_le_de_zero (σ := 1 + x) hβ hβ1.le (by linarith) ht hz
    have e : ((1 + x : ℝ) : ℂ) + t * I = 1 + x + I * t := by push_cast; ring
    rw [e] at h
    exact h
  have b3 : ‖riemannZeta (1 + x + 2 * I * t)‖ ≤ 3 + 3 * |t| := by
    set s : ℂ := 1 + x + 2 * I * t with hsdef
    have hre : s.re = 1 + x := by simp [s]
    have him : s.im = 2 * t := by simp [s]
    have hs1 : s ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      rw [him, one_im] at this
      have : t = 0 := by linarith
      rw [this, abs_zero] at ht; linarith
    have h := norm_zeta_le (s := s) (by rw [hre]; linarith) hs1
    have hn : ‖s‖ ≤ 2 + 2 * |t| := by
      have := Complex.norm_le_abs_re_add_abs_im s
      rw [hre, him, abs_of_pos (by linarith), abs_mul, abs_two] at this; linarith
    have hm : 1 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      rw [sub_im, him, one_im, sub_zero, abs_mul, abs_two] at this; linarith
    have h1 : ‖s‖ / ‖s - 1‖ ≤ ‖s‖ := div_le_self (norm_nonneg _) hm
    have h2 : ‖s‖ / (2 * s.re) ≤ ‖s‖ / 2 := by
      rw [hre]; exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (by linarith)
    linarith
  have hδ : 0 ≤ 1 + x - β := by linarith
  have hδx : 1 + x - β ≤ 2 * x := by linarith
  have hK : 0 ≤ 9 + 4 * |t| := by linarith [abs_nonneg t]
  have key : ‖riemannZeta (1 + x)‖ ^ 3 * ‖riemannZeta (1 + x + I * t)‖ ^ 4 *
      ‖riemannZeta (1 + x + 2 * I * t)‖ ≤ (2 / x) ^ 3 * (2 * x * (9 + 4 * |t|)) ^ 4 *
        (3 + 3 * |t|) := by
    have c2 : ‖riemannZeta (1 + x + I * t)‖ ≤ 2 * x * (9 + 4 * |t|) :=
      b2.trans (mul_le_mul_of_nonneg_right hδx hK)
    gcongr
  have hval : (2 / x) ^ 3 * (2 * x * (9 + 4 * |t|)) ^ 4 * (3 + 3 * |t|) = 1 / 2 := by
    have : (2 / x) ^ 3 * (2 * x * (9 + 4 * |t|)) ^ 4 * (3 + 3 * |t|) = 128 * x * A t := by
      unfold A; field_simp; ring
    rw [this, hxdef]; field_simp; norm_num
  linarith

/-- **A faixa se estreita em toda altura**: todo zero não trivial `s` satisfaz
`c(Im s) < Re s < 1 − c(Im s)` com `c(t) = 1/(256·(9+4|t|)⁴·(3+3|t|))`. -/
theorem faixa_estreitada : ∀ s ∈ Z,
    1 / (256 * A s.im) < s.re ∧ s.re < 1 - 1 / (256 * A s.im) := by
  intro s hs
  have h34 := sem_zeros_ate_altura s hs
  have ht : 1 / 2 ≤ |s.im| := by
    by_contra h
    have h' : |s.im| < 1 / 2 := not_le.mp h
    have : s.im ^ 2 < 1 / 4 := by
      rw [← sq_abs]; nlinarith [abs_nonneg s.im]
    linarith
  have hsplit : s = (s.re : ℂ) + (s.im : ℂ) * I := (Complex.re_add_im s).symm
  have hzs : riemannZeta ((s.re : ℂ) + (s.im : ℂ) * I) = 0 := by rw [← hsplit]; exact hs.1
  constructor
  · have h2 := tensao_mem_Z hs
    have him2 : (tensao s).im = -s.im := by unfold tensao; simp
    have hre2 : (tensao s).re = 1 - s.re := re_tensao s
    have hsplit2 : tensao s = ((tensao s).re : ℂ) + ((tensao s).im : ℂ) * I :=
      (Complex.re_add_im _).symm
    have hz2 : riemannZeta (((tensao s).re : ℂ) + ((tensao s).im : ℂ) * I) = 0 := by
      rw [← hsplit2]; exact h2.1
    have ht2 : 1 / 2 ≤ |(tensao s).im| := by rw [him2, abs_neg]; exact ht
    have := regiao_sem_zeros ht2 hz2
    rw [hre2, him2, A_neg] at this
    linarith
  · exact regiao_sem_zeros ht hzs

end ATK.ZetaRegiao

#print axioms ATK.ZetaRegiao.tres_quatro_um
#print axioms ATK.ZetaRegiao.zeta_eq
#print axioms ATK.ZetaRegiao.norm_zeta_real_le
#print axioms ATK.ZetaRegiao.norm_zeta_le
#print axioms ATK.ZetaRegiao.norm_H_sub_le
#print axioms ATK.ZetaRegiao.norm_zeta_le_de_zero
#print axioms ATK.ZetaRegiao.A_ge
#print axioms ATK.ZetaRegiao.A_neg
#print axioms ATK.ZetaRegiao.regiao_sem_zeros
#print axioms ATK.ZetaRegiao.faixa_estreitada
