import ATK.ZeroClasses.VonKoch
import ATK.ZeroClasses.LittlewoodMu

/-!
# RH ⟹ `ψ(x) = x + O(x^{1/2+ε})`: o critério de von Koch completo (rodada 56)

**Teorema** (von Koch, 1901). `RH ⟺ ψ(x) = x + O(x^{1/2+ε})` para todo `ε > 0` (`rh_iff_psi`). A direção ⇐ é a
rodada 55 (`ATK.ZeroClasses.VonKoch.RH_of_psi`); aqui entra a direção ⇒ (`psi_of_RH`).

A prova segue a de `mertens_of_RH` (rodada 51), trocando `μ` por `Λ − 1`:

1. **Littlewood geral** (`cota_gen`): a estimativa da rodada 46 (Perron truncado com `T = x²`, deslocamento até
   `Re z = −ε/2`, os três lados) para quaisquer coeficientes `|f(n)| ≤ 1` cuja série `L` se estende a uma `Φ`
   holomorfa em `Re u > ½` com `|Φ(u)| ≤ C (1 + |Im u|)^{ε/16}` em `Re u ≥ ½ + ε/2`;
2. **`H = −ζ′/ζ − ζ` sob RH** (`Hf`, `Hf_eq`, `differentiableAt_Hf`, **`norm_H_le`**): `H = −ζ₁′/ζ₁ − ζ₀` é
   holomorfa em `Re s > ½` (o polo em `s = 1` cancela) e `|H(s)| ≤ C (1 + |Im s|)^η` em `Re s ≥ ½ + δ` — Cauchy no
   ramo de `log ζ` da rodada 45 (`ATK.RHLogZeta.norm_L_le`, três círculos + Borel–Carathéodory) e Young;
3. **normalização** (`fco`, `norm_fco_le`, `LSeries_fco`): `|Λ(n) − 1| ≤ (1/δ + 1) n^δ`, e
   `f(n) = (Λ(n) − 1)/((1/δ + 1)n^δ)` tem série `H(u + δ)/(1/δ + 1)`;
4. **por partes** (`abel_cota`, `E_eq_sum`): somas parciais limitadas de `(Λ(n) − 1)n^{−σ}` dão
   `|ψ(N) − N| ≤ 2B N^σ`.

Classificação (rodada 56): **reformulação** (o critério de von Koch, as duas direções). RH continua OPEN_MATH.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real Interval

namespace ATK.ZeroClasses.VonKochRH

open ATK.ZeroClasses.ArgRetangulo (bordo Bordo Ret bordo_congr bordo_add bordo_cauchy bordo_inv bordo_const_mul)
open ATK.ZeroClasses.PerronD (xN xN_pos perron_LSeries)
open ATK.ZeroClasses.LittlewoodMu (alg_res um_add_abs_le integrable_peso rpow_mul_le um_add_sq_rpow_le
  rpow_div_le xN_ge_um)
open ATK.ZeroClasses.Mertens (abel)
open ATK.ZeroClasses.VonKoch (cL E E_succ LSeries_cL VonKochFraco RH_of_psi)
open ATK.RHLogZeta (zeta₁_eq zeta₁_ne_zero_of_RH zeta_ne_zero_of_RH existe_log_zeta norm_L_le θ₂ θ₂_bounds young
  c₀ norm_zeta_sub_one_le)

/-! ## 1. Littlewood geral: o deslocamento -/

/-- `G(z) = x^z Φ(w + z)`. -/
noncomputable def Gf (Φ : ℂ → ℂ) (x : ℝ) (w z : ℂ) : ℂ := (x : ℂ) ^ z * Φ (w + z)

/-- O integrando `g(z) = x^z Φ(w + z)/z`. -/
noncomputable def g (Φ : ℂ → ℂ) (x : ℝ) (w z : ℂ) : ℂ := Gf Φ x w z / z

theorem norm_g (Φ : ℂ → ℂ) {x : ℝ} (hx : 0 < x) (w z : ℂ) :
    ‖g Φ x w z‖ = x ^ z.re * ‖Φ (w + z)‖ / ‖z‖ := by
  rw [g, Gf, norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]

/-- **O resíduo**: `∮ x^z Φ(w + z)/z dz = 2πi Φ(w)` no retângulo `[−b, c] × [−T, T]`, se `Φ` é holomorfa em
`Re > ½`. -/
theorem bordo_g {Φ : ℂ → ℂ} (hΦ : ∀ u : ℂ, 1 / 2 < u.re → DifferentiableAt ℂ Φ u) {w : ℂ} {x b c T : ℝ} (hx : 0 < x) (hb : 0 < b) (hc : 0 < c)
    (hT : 0 < T) (hwb : 1 / 2 < w.re - b) :
    bordo (g Φ x w) ⟨-b, -T⟩ ⟨c, T⟩ = 2 * π * I * Φ w := by
  set U : Set ℂ := {z | 1 / 2 < w.re + z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const (continuous_const.add continuous_re)
  have h0U : (0 : ℂ) ∈ U := by
    show 1 / 2 < w.re + (0 : ℂ).re
    rw [zero_re, add_zero]
    linarith
  have hGd : DifferentiableOn ℂ (Gf Φ x w) U := fun z hz => by
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ z) z :=
      differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
    have hre : 1 / 2 < (w + z).re := by rw [add_re]; exact hz
    have h2 : DifferentiableAt ℂ (fun z : ℂ => Φ (w + z)) z :=
      (hΦ _ hre).comp z (differentiableAt_id.const_add w)
    exact (h1.mul h2).differentiableWithinAt
  have hDd : DifferentiableOn ℂ (dslope (Gf Φ x w) 0) U :=
    (differentiableOn_dslope (hUo.mem_nhds h0U)).mpr hGd
  have hsub : Ret ⟨-b, -T⟩ ⟨c, T⟩ ⊆ U := by
    intro p hp
    have h1 := (mem_reProdIm.mp hp).1
    change p.re ∈ [[-b, c]] at h1
    rw [uIcc_of_le (by linarith)] at h1
    show 1 / 2 < w.re + p.re
    linarith [h1.1]
  have hne : ∀ p ∈ Bordo ⟨-b, -T⟩ ⟨c, T⟩, p ≠ 0 := by
    rintro p ⟨_, h⟩ hp
    change p.re = -b ∨ p.re = c ∨ p.im = -T ∨ p.im = T at h
    have h1 : p.re = 0 := by rw [hp, zero_re]
    have h2 : p.im = 0 := by rw [hp, zero_im]
    rcases h with h | h | h | h <;> linarith
  have hBR : Bordo ⟨-b, -T⟩ ⟨c, T⟩ ⊆ Ret ⟨-b, -T⟩ ⟨c, T⟩ := fun p hp => hp.1
  have heq : EqOn (g Φ x w) (fun s => dslope (Gf Φ x w) 0 s + Gf Φ x w 0 * (s - 0)⁻¹)
      (Bordo ⟨-b, -T⟩ ⟨c, T⟩) := by
    intro s hs
    have hs0 := hne s hs
    simp only [g, dslope_of_ne _ hs0, slope_def_field, sub_zero]
    rw [sub_div]
    ring
  have hc1 : ContinuousOn (dslope (Gf Φ x w) 0) (Bordo ⟨-b, -T⟩ ⟨c, T⟩) :=
    (hDd.mono (hBR.trans hsub)).continuousOn
  have hc2 : ContinuousOn (fun s : ℂ => Gf Φ x w 0 * (s - 0)⁻¹) (Bordo ⟨-b, -T⟩ ⟨c, T⟩) := fun s hs =>
    (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀
      (by simpa using hne s hs))).continuousWithinAt
  rw [bordo_congr heq, bordo_add hc1 hc2, bordo_cauchy (hDd.mono hsub), bordo_const_mul,
    bordo_inv (z := ⟨-b, -T⟩) (w := ⟨c, T⟩) (u := 0) (by simp; linarith) (by simp; linarith)
      (by simp; linarith) (by simp; linarith)]
  simp only [Gf, cpow_zero, one_mul, add_zero, zero_add]
  ring

/-- **O deslocamento**: `|(1/2π) ∫_{−T}^{T} g(c + iy) dy − Φ(w)| ≤ (|A| + |B| + |D|)/(2π)`. -/
theorem desloca {Φ : ℂ → ℂ} (hΦ : ∀ u : ℂ, 1 / 2 < u.re → DifferentiableAt ℂ Φ u) {w : ℂ} {x b c T : ℝ} (hx : 0 < x) (hb : 0 < b) (hc : 0 < c)
    (hT : 0 < T) (hwb : 1 / 2 < w.re - b) :
    ‖(2 * π : ℂ)⁻¹ * (∫ y in (-T)..T, g Φ x w ((c : ℂ) + y * I)) - Φ w‖ ≤
      (‖∫ t in (-b)..c, g Φ x w ((t : ℂ) + ((-T : ℝ) : ℂ) * I)‖ +
        ‖∫ t in (-b)..c, g Φ x w ((t : ℂ) + (T : ℂ) * I)‖ +
        ‖∫ y in (-T)..T, g Φ x w (((-b : ℝ) : ℂ) + y * I)‖) / (2 * π) := by
  have hB := bordo_g hΦ hx hb hc hT hwb
  simp only [bordo, smul_eq_mul] at hB
  exact alg_res hB

/-! ## 2. As cotas dos três lados -/

/-- **Lados horizontais**. -/
theorem horiz_g {Φ : ℂ → ℂ} {w : ℂ} {x b c T δ η CF h : ℝ} (hx : 1 ≤ x) (hb : 0 ≤ b) (hc : 0 ≤ c) (hcb : c + b ≤ 1)
    (hT : 0 < T) (hh : |h| = T) (hη : 0 ≤ η) (hCF : 0 ≤ CF)
    (hF : ∀ u : ℂ, 1 / 2 + δ ≤ u.re → ‖Φ u‖ ≤ CF * (1 + |u.im|) ^ η) (hwb : 1 / 2 + δ ≤ w.re - b) :
    ‖∫ t in (-b)..c, g Φ x w ((t : ℂ) + (h : ℂ) * I)‖ ≤
      x ^ c * CF * (1 + |w.im|) ^ η * (1 + T) ^ η / T := by
  have hx0 : 0 < x := by linarith
  have hK : 0 ≤ x ^ c * CF * (1 + |w.im|) ^ η * (1 + T) ^ η / T := by positivity
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -b) (b := c)
    (f := fun t : ℝ => g Φ x w ((t : ℂ) + (h : ℂ) * I))
    (C := x ^ c * CF * (1 + |w.im|) ^ η * (1 + T) ^ η / T) (fun t ht => by
      rw [uIoc_of_le (by linarith)] at ht
      rw [norm_g Φ hx0]
      have hre : ((t : ℂ) + (h : ℂ) * I).re = t := by simp
      have him : ((t : ℂ) + (h : ℂ) * I).im = h := by simp
      rw [hre]
      have hz : T ≤ ‖(t : ℂ) + (h : ℂ) * I‖ := by
        have := Complex.abs_im_le_norm ((t : ℂ) + (h : ℂ) * I)
        rw [him, hh] at this
        exact this
      have hxt : x ^ t ≤ x ^ c := Real.rpow_le_rpow_of_exponent_le hx ht.2
      have hwre : 1 / 2 + δ ≤ (w + ((t : ℂ) + (h : ℂ) * I)).re := by
        rw [add_re, hre]; linarith [ht.1]
      have hFb := hF _ hwre
      rw [add_im, him] at hFb
      have hFb2 : ‖Φ (w + ((t : ℂ) + (h : ℂ) * I))‖ ≤ CF * ((1 + |w.im|) ^ η * (1 + T) ^ η) := by
        refine hFb.trans (mul_le_mul_of_nonneg_left ?_ hCF)
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        apply Real.rpow_le_rpow (by positivity) _ hη
        have := um_add_abs_le w.im h
        rw [hh] at this
        exact this
      calc x ^ t * ‖Φ (w + ((t : ℂ) + (h : ℂ) * I))‖ / ‖(t : ℂ) + (h : ℂ) * I‖
          ≤ x ^ c * (CF * ((1 + |w.im|) ^ η * (1 + T) ^ η)) / T := by
            apply div_le_div₀ (by positivity) (mul_le_mul hxt hFb2 (norm_nonneg _) (by positivity)) hT hz
        _ = x ^ c * CF * (1 + |w.im|) ^ η * (1 + T) ^ η / T := by ring)
  refine this.trans ?_
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ c - -b)]
  calc x ^ c * CF * (1 + |w.im|) ^ η * (1 + T) ^ η / T * (c - -b)
      ≤ x ^ c * CF * (1 + |w.im|) ^ η * (1 + T) ^ η / T * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) hK
    _ = _ := mul_one _

/-- **Lado vertical** em `Re z = −b`. -/
theorem vert_g {Φ : ℂ → ℂ} {w : ℂ} {x b T δ η CF : ℝ} (hx : 0 < x) (hb : 0 < b) (hT : 0 ≤ T) (hη : 0 < η)
    (hCF : 0 ≤ CF) (hF : ∀ u : ℂ, 1 / 2 + δ ≤ u.re → ‖Φ u‖ ≤ CF * (1 + |u.im|) ^ η)
    (hwb : 1 / 2 + δ ≤ w.re - b) :
    ‖∫ y in (-T)..T, g Φ x w (((-b : ℝ) : ℂ) + y * I)‖ ≤
      x ^ (-b) * CF * (1 + |w.im|) ^ η * (1 + 1 / b) * (1 + T) ^ (2 * η) *
        ∫ y : ℝ, (1 + |y|) ^ (-(1 + η)) := by
  set M := x ^ (-b) * CF * (1 + |w.im|) ^ η * (1 + 1 / b) * (1 + T) ^ (2 * η) with hM
  have hM0 : 0 ≤ M := by positivity
  have hint := integrable_peso hη
  have hpt : ∀ y ∈ Ioc (-T) T, ‖g Φ x w (((-b : ℝ) : ℂ) + y * I)‖ ≤ M * (1 + |y|) ^ (-(1 + η)) := by
    intro y hy
    have hyT : |y| ≤ T := abs_le.mpr ⟨hy.1.le, hy.2⟩
    have hp1 : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
    have hp0 : 0 < 1 + |y| := by linarith
    rw [norm_g Φ hx]
    have hre : (((-b : ℝ) : ℂ) + y * I).re = -b := by simp
    have him : (((-b : ℝ) : ℂ) + y * I).im = y := by simp
    rw [hre]
    have hwre : 1 / 2 + δ ≤ (w + (((-b : ℝ) : ℂ) + y * I)).re := by rw [add_re, hre]; linarith
    have hFb := hF _ hwre
    rw [add_im, him] at hFb
    have hFb2 : ‖Φ (w + (((-b : ℝ) : ℂ) + y * I))‖ ≤ CF * ((1 + |w.im|) ^ η * (1 + |y|) ^ η) := by
      refine hFb.trans (mul_le_mul_of_nonneg_left ?_ hCF)
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (um_add_abs_le w.im y) hη.le
    have hz : (1 + |y|) ≤ (1 + 1 / b) * ‖((-b : ℝ) : ℂ) + y * I‖ := by
      have h1 := Complex.abs_im_le_norm (((-b : ℝ) : ℂ) + y * I)
      have h2 := Complex.abs_re_le_norm (((-b : ℝ) : ℂ) + y * I)
      rw [him] at h1
      rw [hre, abs_neg, abs_of_pos hb] at h2
      have : 1 ≤ ‖((-b : ℝ) : ℂ) + y * I‖ / b := by rw [le_div_iff₀ hb]; linarith
      calc 1 + |y| ≤ ‖((-b : ℝ) : ℂ) + y * I‖ / b + ‖((-b : ℝ) : ℂ) + y * I‖ := by linarith
        _ = (1 + 1 / b) * ‖((-b : ℝ) : ℂ) + y * I‖ := by ring
    have hzpos : 0 < ‖((-b : ℝ) : ℂ) + y * I‖ := by
      have h2 := Complex.abs_re_le_norm (((-b : ℝ) : ℂ) + y * I)
      rw [hre, abs_neg, abs_of_pos hb] at h2
      linarith
    -- p^η/p = p^{2η} p^{−(1+η)} ≤ (1+T)^{2η} p^{−(1+η)}
    have hpow : (1 + |y|) ^ η = (1 + |y|) ^ (2 * η) * (1 + |y|) ^ (-(1 + η)) * (1 + |y|) := by
      symm
      calc (1 + |y|) ^ (2 * η) * (1 + |y|) ^ (-(1 + η)) * (1 + |y|)
          = (1 + |y|) ^ (2 * η + -(1 + η)) * (1 + |y|) ^ (1 : ℝ) := by
            rw [Real.rpow_add hp0, Real.rpow_one]
        _ = (1 + |y|) ^ (2 * η + -(1 + η) + 1) := by rw [← Real.rpow_add hp0]
        _ = (1 + |y|) ^ η := by ring_nf
    have hmono : (1 + |y|) ^ (2 * η) ≤ (1 + T) ^ (2 * η) :=
      Real.rpow_le_rpow hp0.le (by linarith) (by linarith)
    have hq0 : 0 ≤ (1 + |y|) ^ (-(1 + η)) := by positivity
    calc x ^ (-b) * ‖Φ (w + (((-b : ℝ) : ℂ) + y * I))‖ / ‖((-b : ℝ) : ℂ) + y * I‖
        ≤ x ^ (-b) * (CF * ((1 + |w.im|) ^ η * (1 + |y|) ^ η)) / ‖((-b : ℝ) : ℂ) + y * I‖ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hFb2 (by positivity)) hzpos.le
      _ = x ^ (-b) * CF * (1 + |w.im|) ^ η * ((1 + |y|) ^ (2 * η) * (1 + |y|) ^ (-(1 + η))) *
            ((1 + |y|) / ‖((-b : ℝ) : ℂ) + y * I‖) := by
          rw [hpow]; ring
      _ ≤ x ^ (-b) * CF * (1 + |w.im|) ^ η * ((1 + T) ^ (2 * η) * (1 + |y|) ^ (-(1 + η))) *
            (1 + 1 / b) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmono hq0) (by positivity))
            ((div_le_iff₀ hzpos).mpr hz) (by positivity) (by positivity)
      _ = M * (1 + |y|) ^ (-(1 + η)) := by rw [hM]; ring
  have hle := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ T)
    (ae_of_all _ hpt) ((hint.const_mul M).intervalIntegrable)
  refine hle.trans ?_
  rw [intervalIntegral.integral_of_le (by linarith), integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ hM0
  exact setIntegral_le_integral hint (ae_of_all _ fun y => by positivity)

/-! ## 3. A estimativa de Littlewood geral -/

/-- **Littlewood geral, com taxa**: se `|f(n)| ≤ 1`, `L(f, u) = Φ(u)` em `Re u > 1`, `Φ` é holomorfa em `Re u > ½`
e `|Φ(u)| ≤ C_F (1 + |Im u|)^{ε/16}` em `Re u ≥ ½ + ε/2`, então para `Re w = ½ + ε` (`0 < ε ≤ 1`) e `N ≥ 1`,
`|Σ_{n ≤ N} f(n) n^{−w} − Φ(w)| ≤ K (1 + |Im w|)^{ε/16} (N + ½)^{−ε/4}`. -/
theorem cota_gen {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {Φ : ℂ → ℂ}
    (hΦd : ∀ u : ℂ, 1 / 2 < u.re → DifferentiableAt ℂ Φ u) (hΦL : ∀ u : ℂ, 1 < u.re → LSeries f u = Φ u)
    {ε CF : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hCF0 : 0 ≤ CF)
    (hCF : ∀ u : ℂ, 1 / 2 + ε / 2 ≤ u.re → ‖Φ u‖ ≤ CF * (1 + |u.im|) ^ (ε / 16)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, w.re = 1 / 2 + ε → ∀ N : ℕ, 1 ≤ N →
      ‖∑ n ∈ Finset.range (N + 1), LSeries.term f w n - Φ w‖ ≤
        K * ((1 + |w.im|) ^ (ε / 16) * xN N ^ (-(ε / 4))) := by
  obtain ⟨Zt, hZt⟩ : ∃ Zt : ℝ,
      Zt = ∑' n : ℕ, ‖LSeries.term (fun _ => (1 : ℂ)) ((1 / 2 + ε + 1 / 2 : ℝ) : ℂ) n‖ := ⟨_, rfl⟩
  have hZ0 : 0 ≤ Zt := by rw [hZt]; exact tsum_nonneg fun _ => norm_nonneg _
  obtain ⟨Ie, hIe⟩ : ∃ Ie : ℝ, Ie = ∫ y : ℝ, (1 + |y|) ^ (-(1 + ε / 16)) := ⟨_, rfl⟩
  have hI0 : 0 ≤ Ie := by rw [hIe]; exact integral_nonneg fun y => by positivity
  refine ⟨6 * Zt / π + (4 * CF + 2 * CF * (1 + 1 / (ε / 2)) * Ie) / (2 * π), by positivity, ?_⟩
  intro w hw N hN
  have hx1 := xN_ge_um hN
  have hx0 : 0 < xN N := by linarith
  have hT1 : 1 ≤ xN N ^ (2 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hT0 : 0 < xN N ^ (2 : ℝ) := by linarith
  have ha1 : 1 ≤ (1 + |w.im|) ^ (ε / 16) := Real.one_le_rpow (by linarith [abs_nonneg w.im]) (by positivity)
  have hθ0 : 0 < xN N ^ (-(ε / 4)) := Real.rpow_pos_of_pos hx0 _
  -- Perron
  have hP := perron_LSeries hf N (s := w) (c := 1 / 2) (T := xN N ^ (2 : ℝ)) (by norm_num)
    (by rw [hw]; linarith) hT0
  rw [hw, ← hZt] at hP
  have hV : (∫ t in (-(xN N ^ (2 : ℝ)))..(xN N ^ (2 : ℝ)), LSeries f (w + (((1 / 2 : ℝ) : ℂ) + t * I)) *
      (xN N : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I)) =
      ∫ t in (-(xN N ^ (2 : ℝ)))..(xN N ^ (2 : ℝ)), g Φ (xN N) w (((1 / 2 : ℝ) : ℂ) + t * I) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hre : 1 < (w + (((1 / 2 : ℝ) : ℂ) + t * I)).re := by simp [hw]; linarith
    simp only [g, Gf]
    rw [hΦL _ hre]
    ring
  rw [hV] at hP
  -- o deslocamento e os três lados
  have hR := desloca hΦd (w := w) (x := xN N) (b := ε / 2) (c := 1 / 2) (T := xN N ^ (2 : ℝ)) hx0
    (by positivity) (by norm_num) hT0 (by rw [hw]; linarith)
  have hA := horiz_g (w := w) (x := xN N) (b := ε / 2) (c := 1 / 2) (T := xN N ^ (2 : ℝ)) (δ := ε / 2)
    (η := ε / 16) (CF := CF) (h := -(xN N ^ (2 : ℝ))) hx1 (by positivity) (by norm_num) (by linarith) hT0
    (by rw [abs_neg, abs_of_pos hT0]) (by positivity) hCF0 hCF (by rw [hw]; linarith)
  have hB := horiz_g (w := w) (x := xN N) (b := ε / 2) (c := 1 / 2) (T := xN N ^ (2 : ℝ)) (δ := ε / 2)
    (η := ε / 16) (CF := CF) (h := xN N ^ (2 : ℝ)) hx1 (by positivity) (by norm_num) (by linarith) hT0
    (abs_of_pos hT0) (by positivity) hCF0 hCF (by rw [hw]; linarith)
  have hD := vert_g (w := w) (x := xN N) (b := ε / 2) (T := xN N ^ (2 : ℝ)) (δ := ε / 2) (η := ε / 16)
    hx0 (by positivity) hT0.le (by positivity) hCF0 hCF (by rw [hw]; linarith)
  rw [← hIe] at hD
  -- as potências de x
  have q1 : xN N ^ (1 / 2 : ℝ) * (4 * xN N + 2) / xN N ^ (2 : ℝ) ≤ 6 * xN N ^ (-(ε / 4)) := by
    calc xN N ^ (1 / 2 : ℝ) * (4 * xN N + 2) / xN N ^ (2 : ℝ)
        ≤ xN N ^ (1 / 2 : ℝ) * (6 * xN N ^ (1 : ℝ)) / xN N ^ (2 : ℝ) := by
          apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left _ (by positivity)) hT0.le
          rw [Real.rpow_one]
          linarith
      _ = 6 * (xN N ^ (1 / 2 : ℝ) * xN N ^ (1 : ℝ) / xN N ^ (2 : ℝ)) := by ring
      _ ≤ 6 * xN N ^ (-(ε / 4)) := mul_le_mul_of_nonneg_left (rpow_div_le hx1 (by linarith)) (by norm_num)
  have q2 : xN N ^ (1 / 2 : ℝ) * (1 + xN N ^ (2 : ℝ)) ^ (ε / 16) / xN N ^ (2 : ℝ) ≤ 2 * xN N ^ (-(ε / 4)) := by
    calc xN N ^ (1 / 2 : ℝ) * (1 + xN N ^ (2 : ℝ)) ^ (ε / 16) / xN N ^ (2 : ℝ)
        ≤ xN N ^ (1 / 2 : ℝ) * (2 * xN N ^ (2 * (ε / 16))) / xN N ^ (2 : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
            (um_add_sq_rpow_le hx1 (by positivity) (by linarith)) (by positivity)) hT0.le
      _ = 2 * (xN N ^ (1 / 2 : ℝ) * xN N ^ (2 * (ε / 16)) / xN N ^ (2 : ℝ)) := by ring
      _ ≤ 2 * xN N ^ (-(ε / 4)) := mul_le_mul_of_nonneg_left (rpow_div_le hx1 (by linarith)) (by norm_num)
  have q3 : xN N ^ (-(ε / 2)) * (1 + xN N ^ (2 : ℝ)) ^ (2 * (ε / 16)) ≤ 2 * xN N ^ (-(ε / 4)) := by
    calc xN N ^ (-(ε / 2)) * (1 + xN N ^ (2 : ℝ)) ^ (2 * (ε / 16))
        ≤ xN N ^ (-(ε / 2)) * (2 * xN N ^ (2 * (2 * (ε / 16)))) :=
          mul_le_mul_of_nonneg_left (um_add_sq_rpow_le hx1 (by positivity) (by linarith)) (by positivity)
      _ = 2 * (xN N ^ (-(ε / 2)) * xN N ^ (2 * (2 * (ε / 16)))) := by ring
      _ ≤ 2 * xN N ^ (-(ε / 4)) := mul_le_mul_of_nonneg_left (rpow_mul_le hx1 (by linarith)) (by norm_num)
  -- os três lados em termos de a·x^{−ε/4}
  have hA' := hA.trans (le_of_eq_of_le (by ring) (mul_le_mul_of_nonneg_left q2
    (by positivity : 0 ≤ CF * (1 + |w.im|) ^ (ε / 16))))
  have hB' := hB.trans (le_of_eq_of_le (by ring) (mul_le_mul_of_nonneg_left q2
    (by positivity : 0 ≤ CF * (1 + |w.im|) ^ (ε / 16))))
  have hD' := hD.trans (le_of_eq_of_le (by ring) (mul_le_mul_of_nonneg_left q3
    (by positivity : 0 ≤ CF * (1 + |w.im|) ^ (ε / 16) * (1 + 1 / (ε / 2)) * Ie)))
  have hR' := hR.trans (div_le_div_of_nonneg_right (add_le_add (add_le_add hA' hB') hD') (by positivity))
  have hP' := hP.trans (le_of_eq_of_le (by ring) (mul_le_mul_of_nonneg_left q1
    (div_nonneg hZ0 Real.pi_pos.le)))
  calc ‖∑ n ∈ Finset.range (N + 1), LSeries.term f w n - Φ w‖
      ≤ ‖∑ n ∈ Finset.range (N + 1), LSeries.term f w n - (2 * π : ℂ)⁻¹ *
          ∫ t in (-(xN N ^ (2 : ℝ)))..(xN N ^ (2 : ℝ)), g Φ (xN N) w (((1 / 2 : ℝ) : ℂ) + t * I)‖ +
        ‖(2 * π : ℂ)⁻¹ * (∫ t in (-(xN N ^ (2 : ℝ)))..(xN N ^ (2 : ℝ)), g Φ (xN N) w (((1 / 2 : ℝ) : ℂ) + t * I)) -
          Φ w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add hP' hR'
    _ ≤ 6 * Zt / π * ((1 + |w.im|) ^ (ε / 16) * xN N ^ (-(ε / 4))) +
          (4 * CF + 2 * CF * (1 + 1 / (ε / 2)) * Ie) / (2 * π) *
            ((1 + |w.im|) ^ (ε / 16) * xN N ^ (-(ε / 4))) := by
        have hθa : xN N ^ (-(ε / 4)) ≤ (1 + |w.im|) ^ (ε / 16) * xN N ^ (-(ε / 4)) :=
          le_mul_of_one_le_left hθ0.le ha1
        have key := mul_le_mul_of_nonneg_left hθa (by positivity : (0 : ℝ) ≤ 6 * Zt / π)
        exact add_le_add (le_of_eq_of_le (by ring) key) (le_of_eq (by ring))
    _ = _ := by ring

/-! ## 4. `H = −ζ′/ζ − ζ` sob RH -/

/-- `H(s) = −ζ₁′(s)/ζ₁(s) − ζ₀(s)`; fora de `s = 1` e dos zeros, `H = −ζ′/ζ − ζ` (`Hf_eq`). -/
noncomputable def Hf (s : ℂ) : ℂ := -deriv riemannZeta₁ s / riemannZeta₁ s - riemannZeta₀ s

theorem deriv_zeta₁ {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta₁ s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
  have heq : riemannZeta₁ =ᶠ[𝓝 s] fun u => (u - 1) * riemannZeta u := by
    filter_upwards [eventually_ne_nhds hs] with u hu
    exact zeta₁_eq hu
  rw [heq.deriv_eq]
  have := ((hasDerivAt_id' s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt
  have h := this.deriv
  rw [one_mul] at h
  exact h

theorem Hf_eq {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    Hf s = -logDeriv riemannZeta s - riemannZeta s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have h0 : riemannZeta₀ s = riemannZeta s - (s - 1)⁻¹ := by
    rw [riemannZeta_eq_inv_sub_add hs]; ring
  unfold Hf
  rw [deriv_zeta₁ hs, zeta₁_eq hs, h0, logDeriv_apply]
  field_simp
  ring

theorem differentiableAt_Hf (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ Hf s := by
  have h1 := zeta₁_ne_zero_of_RH hRH hs
  have hd : DifferentiableAt ℂ (deriv riemannZeta₁) s :=
    (differentiable_riemannZeta₁.analyticAt s).deriv.differentiableAt
  exact ((hd.neg.div (differentiable_riemannZeta₁ s) h1).sub (differentiable_riemannZeta₀ s))

/-- `|ζ′/ζ(s)| ≤ A` em `Re s ≥ 2` (série de von Mangoldt). -/
theorem norm_logDeriv_le_dois : ∃ A : ℝ, ∀ s : ℂ, 2 ≤ s.re → ‖logDeriv riemannZeta s‖ ≤ A := by
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have hS : LSeriesSummable ATK.ZeroClasses.PNT.vM 2 := ArithmeticFunction.LSeriesSummable_vonMangoldt h2
  refine ⟨∑' n, ‖LSeries.term ATK.ZeroClasses.PNT.vM 2 n‖, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by linarith
  have hS' : LSeriesSummable ATK.ZeroClasses.PNT.vM s := ArithmeticFunction.LSeriesSummable_vonMangoldt hs1
  have e : logDeriv riemannZeta s = -LSeries ATK.ZeroClasses.PNT.vM s := by
    rw [ATK.ZeroClasses.PNT.LSeries_vM hs1, neg_neg]
  rw [e, norm_neg]
  calc ‖LSeries ATK.ZeroClasses.PNT.vM s‖ ≤ ∑' n, ‖LSeries.term ATK.ZeroClasses.PNT.vM s n‖ :=
        norm_tsum_le_tsum_norm (summable_norm_iff.mpr hS')
    _ ≤ ∑' n, ‖LSeries.term ATK.ZeroClasses.PNT.vM 2 n‖ :=
        Summable.tsum_le_tsum (fun n => LSeries.norm_term_le_of_re_le_re _ (by simpa using hs) n)
          (summable_norm_iff.mpr hS') (summable_norm_iff.mpr hS)

/-- **Sob RH**: para `δ ∈ (0, 1]` e `η > 0` existe `C > 0` com `|H(s)| ≤ C (1 + |Im s|)^η` em `Re s ≥ ½ + δ`. -/
theorem norm_H_le (hRH : RiemannHypothesis) {δ η : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hη : 0 < η) :
    ∃ C, 0 < C ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → ‖Hf s‖ ≤ C * (1 + |s.im|) ^ η := by
  have hδ2 : 0 < δ / 2 := by linarith
  have hθ := θ₂_bounds hδ2 (by linarith : δ / 2 ≤ 1)
  obtain ⟨K, hK⟩ := young (A := (10 / (δ / 2)) ^ θ₂ (δ / 2)) (θ := θ₂ (δ / 2)) (η := η)
    (Real.rpow_nonneg (by positivity) _) hθ.1 hθ.2 hη
  obtain ⟨A, hA⟩ := norm_logDeriv_le_dois
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = (2 / δ + 1) * (Real.exp (η + K) * 12 ^ η) := ⟨_, rfl⟩
  have hC₁0 : 0 < C₁ := by rw [hC₁]; positivity
  set Kc : Set ℂ := {s : ℂ | 1 / 2 + δ ≤ s.re} ∩ {s : ℂ | s.re ≤ 5 / 2} ∩ {s : ℂ | |s.im| ≤ 4}
    with hKcdef
  have hKc : IsCompact Kc := by
    refine (isCompact_closedBall (0 : ℂ) 10).of_isClosed_subset ?_ ?_
    · exact ((isClosed_le continuous_const Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const)).inter
        (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
    · rintro s ⟨⟨h1, h2⟩, h3⟩
      simp only [mem_ofPred_eq] at h1 h2 h3
      rw [mem_closedBall, dist_zero_right]
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 3 + 4 := by
            gcongr
            rw [abs_le]; constructor <;> linarith
        _ ≤ 10 := by norm_num
  have hHc : ContinuousOn Hf Kc := fun s hs =>
    (differentiableAt_Hf hRH (by have := hs.1.1; simp only [mem_ofPred_eq] at this; linarith)
      ).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := hKc.exists_bound_of_continuousOn hHc
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (max (A + 3 / 2) C₀) C₁ + 1 := ⟨_, rfl⟩
  have hCA : A + 3 / 2 ≤ C := by
    have := le_max_left (max (A + 3 / 2) C₀) C₁; have := le_max_left (A + 3 / 2) C₀; linarith
  have hCC₀ : C₀ ≤ C := by
    have := le_max_left (max (A + 3 / 2) C₀) C₁; have := le_max_right (A + 3 / 2) C₀; linarith
  have hCC₁ : C₁ ≤ C := by have := le_max_right (max (A + 3 / 2) C₀) C₁; linarith
  have hCpos : 0 < C := by linarith
  refine ⟨C, hCpos, fun s hs => ?_⟩
  have h1 : 1 ≤ (1 + |s.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hη.le
  have hCle : ∀ x, x ≤ C → x ≤ C * (1 + |s.im|) ^ η := fun x hx =>
    hx.trans (le_mul_of_one_le_right hCpos.le h1)
  rcases le_or_gt (5 / 2) s.re with h52 | h52
  · have hs1 : s ≠ 1 := by intro h; rw [h, one_re] at h52; norm_num at h52
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by linarith)
    rw [Hf_eq hs1 hz]
    have hζ : ‖riemannZeta s‖ ≤ 3 / 2 := by
      have := norm_zeta_sub_one_le h52
      calc ‖riemannZeta s‖ = ‖(riemannZeta s - 1) + 1‖ := by ring_nf
        _ ≤ ‖riemannZeta s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ 3 / 2 := by rw [norm_one]; linarith
    refine hCle _ ((norm_sub_le _ _).trans ?_)
    rw [norm_neg]
    have := hA s (by linarith)
    linarith
  rcases le_or_gt |s.im| 4 with h4 | h4
  · exact hCle _ ((hC₀ s ⟨⟨hs, h52.le⟩, h4⟩).trans hCC₀)
  · set t := s.im with htdef
    have ht : 4 ≤ |t| := h4.le
    obtain ⟨L, hL0, hLe, hLd⟩ := existe_log_zeta hRH ht
    have hsc : s - c₀ t = ((s.re - 3 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c₀, htdef]
    have hz : ‖s - c₀ t‖ ≤ 5 / 2 - δ := by
      rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith
    have hsmem : s ∈ ball (c₀ t) (5 / 2) := by
      rw [mem_ball, dist_eq_norm]; linarith
    obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Real.log (2 * (|t| + 6)) := ⟨_, rfl⟩
    obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = (10 * (M + 1) / (δ / 2)) ^ θ₂ (δ / 2) := ⟨_, rfl⟩
    have hLb : ∀ z, ‖z - c₀ t‖ ≤ 5 / 2 - δ / 2 → ‖L z‖ ≤ Λ := fun z hz' => by
      rw [hΛ, hM]
      exact norm_L_le hRH ht hδ2 (by linarith) hL0 hLe hLd hz'
    have hdiffL : DifferentiableOn ℂ L (ball (c₀ t) (5 / 2)) :=
      fun z hz' => (hLd z hz').differentiableAt.differentiableWithinAt
    have hcl : closedBall s (δ / 2) ⊆ ball (c₀ t) (5 / 2) := by
      intro z hz'
      rw [mem_closedBall, dist_eq_norm] at hz'
      rw [mem_ball, dist_eq_norm]
      calc ‖z - c₀ t‖ = ‖(z - s) + (s - c₀ t)‖ := by ring_nf
        _ ≤ ‖z - s‖ + ‖s - c₀ t‖ := norm_add_le _ _
        _ < 5 / 2 := by linarith
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ2 (hdiffL.diffContOnCl_ball hcl)
      (C := Λ) (fun z hz' => hLb z (by
        rw [mem_sphere, dist_eq_norm] at hz'
        calc ‖z - c₀ t‖ = ‖(z - s) + (s - c₀ t)‖ := by ring_nf
          _ ≤ ‖z - s‖ + ‖s - c₀ t‖ := norm_add_le _ _
          _ ≤ 5 / 2 - δ / 2 := by linarith))
    have hderiv : deriv L s = logDeriv riemannZeta s := by
      rw [(hLd s hsmem).deriv, logDeriv_apply]
    rw [hderiv] at hcauchy
    have hs1 : s ≠ 1 := by
      intro h
      have h0 : t = 0 := by rw [htdef, h, one_im]
      rw [h0, abs_zero] at h4
      norm_num at h4
    have hzs : riemannZeta s ≠ 0 := zeta_ne_zero_of_RH hRH (by linarith)
    have hLs : ‖L s‖ ≤ Λ := hLb s (by linarith)
    have hζ : ‖riemannZeta s‖ ≤ Real.exp Λ := by
      rw [← hLe s hsmem, Complex.norm_exp]
      exact Real.exp_le_exp.mpr ((Complex.re_le_norm (L s)).trans hLs)
    have hΛe : Λ ≤ Real.exp Λ := by linarith [Real.add_one_le_exp Λ]
    have hld : ‖logDeriv riemannZeta s‖ ≤ 2 / δ * Real.exp Λ := by
      refine hcauchy.trans ?_
      rw [div_le_iff₀ hδ2]
      have e : 2 / δ * Real.exp Λ * (δ / 2) = Real.exp Λ := by field_simp
      linarith
    have hH : ‖Hf s‖ ≤ (2 / δ + 1) * Real.exp Λ := by
      rw [Hf_eq hs1 hzs]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_neg]
      linarith
    have hM0 : 0 ≤ M := by rw [hM]; exact (Real.log_pos (by linarith [abs_nonneg t])).le
    have hsplit : (10 * (M + 1) / (δ / 2)) ^ θ₂ (δ / 2) =
        (10 / (δ / 2)) ^ θ₂ (δ / 2) * (M + 1) ^ θ₂ (δ / 2) := by
      rw [show 10 * (M + 1) / (δ / 2) = (10 / (δ / 2)) * (M + 1) by ring,
        Real.mul_rpow (by positivity) (by linarith)]
    have hY := hK (M + 1) (by linarith)
    have hexpM : Real.exp (η * M) = (2 * (|t| + 6)) ^ η := by
      rw [Real.rpow_def_of_pos (by positivity), hM, mul_comm]
    have hpow : (2 * (|t| + 6)) ^ η ≤ 12 ^ η * (1 + |t|) ^ η := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg t]) hη.le
    have hexp : Real.exp Λ ≤ Real.exp (η + K) * (12 ^ η * (1 + |t|) ^ η) := by
      calc Real.exp Λ ≤ Real.exp (η * (M + 1) + K) := by
            rw [hΛ, hsplit]; exact Real.exp_le_exp.mpr hY
        _ = Real.exp (η + K) * Real.exp (η * M) := by rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (η + K) * (12 ^ η * (1 + |t|) ^ η) := by rw [hexpM]; gcongr
    calc ‖Hf s‖ ≤ (2 / δ + 1) * Real.exp Λ := hH
      _ ≤ (2 / δ + 1) * (Real.exp (η + K) * (12 ^ η * (1 + |t|) ^ η)) := by gcongr
      _ = C₁ * (1 + |t|) ^ η := by rw [hC₁]; ring
      _ ≤ C * (1 + |t|) ^ η := by gcongr

/-! ## 5. Os coeficientes `Λ(n) − 1` normalizados -/

theorem norm_cL_le {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : n ≠ 0) :
    ‖cL n‖ ≤ (1 / δ + 1) * (n : ℝ) ^ δ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hΛl : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hp1 : 1 ≤ (n : ℝ) ^ δ := Real.one_le_rpow hn1 hδ.le
  have hlog : δ * Real.log n ≤ (n : ℝ) ^ δ := by
    have h := Real.add_one_le_exp (δ * Real.log n)
    have e : Real.exp (δ * Real.log n) = (n : ℝ) ^ δ := by
      rw [Real.rpow_def_of_pos hn0, mul_comm]
    linarith
  have hlog' : Real.log n ≤ (n : ℝ) ^ δ / δ := by rw [le_div_iff₀ hδ]; linarith
  have e : cL n = ((ArithmeticFunction.vonMangoldt n - 1 : ℝ) : ℂ) := by
    unfold cL; push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  calc |ArithmeticFunction.vonMangoldt n - 1| ≤ Real.log n + 1 := by
        rw [abs_le]; constructor <;> linarith
    _ ≤ (n : ℝ) ^ δ / δ + (n : ℝ) ^ δ := by linarith
    _ = (1 / δ + 1) * (n : ℝ) ^ δ := by ring

/-- `f(n) = (Λ(n) − 1)/((1/δ + 1) n^δ)` (e `f(0) = 0`). -/
noncomputable def fco (δ : ℝ) (n : ℕ) : ℂ := cL n / (((1 / δ + 1) * (n : ℝ) ^ δ : ℝ) : ℂ)

theorem norm_fco_le {δ : ℝ} (hδ : 0 < δ) (n : ℕ) : ‖fco δ n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [fco, Real.zero_rpow hδ.ne']
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hp : 0 < (1 / δ + 1) * (n : ℝ) ^ δ := by positivity
    unfold fco
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, div_le_one hp]
    exact norm_cL_le hδ hn

theorem term_fco {δ : ℝ} (hδ : 0 < δ) (u : ℂ) (n : ℕ) :
    LSeries.term (fco δ) u n = ((1 / δ + 1 : ℝ) : ℂ)⁻¹ * LSeries.term cL (u + δ) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, cpow_add _ _ hnc]
    have hB : ((1 / δ + 1 : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 1 / δ + 1 := by positivity
      exact_mod_cast this.ne'
    have e : ((((1 / δ + 1) * (n : ℝ) ^ δ : ℝ)) : ℂ) = ((1 / δ + 1 : ℝ) : ℂ) * (n : ℂ) ^ (δ : ℂ) := by
      rw [ofReal_mul, ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      ring
    have h1 : (n : ℂ) ^ (δ : ℂ) ≠ 0 := fun h => hnc ((cpow_eq_zero_iff _ _).mp h).1
    have h2 : (n : ℂ) ^ u ≠ 0 := fun h => hnc ((cpow_eq_zero_iff _ _).mp h).1
    unfold fco
    rw [e]
    field_simp

theorem LSeries_fco {δ : ℝ} (hδ : 0 < δ) {u : ℂ} (hu : 1 < u.re) :
    LSeries (fco δ) u = ((1 / δ + 1 : ℝ) : ℂ)⁻¹ * Hf (u + δ) := by
  have hu' : 1 < (u + δ).re := by simp; linarith
  have hu1 : u + δ ≠ 1 := fun h => by rw [h, one_re] at hu'; exact lt_irrefl 1 hu'
  rw [Hf_eq hu1 (riemannZeta_ne_zero_of_one_lt_re hu'), ← LSeries_cL hu']
  unfold LSeries
  simp_rw [term_fco hδ]
  exact tsum_mul_left

/-- **Sob RH**: as somas parciais de `Σ (Λ(n) − 1) n^{−σ}`, `σ = ½ + ε + δ`, são limitadas. -/
theorem somas_limitadas (hRH : RiemannHypothesis) {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) :
    ∃ B₂ : ℝ, ∀ N : ℕ,
      ‖∑ n ∈ Finset.range (N + 1), LSeries.term cL ((1 / 2 + ε + δ : ℝ) : ℂ) n‖ ≤ B₂ := by
  have hB0 : (0 : ℝ) < 1 / δ + 1 := by positivity
  obtain ⟨CH, hCH0, hCH⟩ := norm_H_le hRH (δ := ε / 2) (η := ε / 16) (by linarith) (by linarith)
    (by linarith)
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : ℂ → ℂ, Φ = fun u => ((1 / δ + 1 : ℝ) : ℂ)⁻¹ * Hf (u + δ) := ⟨_, rfl⟩
  have hΦd : ∀ u : ℂ, 1 / 2 < u.re → DifferentiableAt ℂ Φ u := by
    intro u hu
    have hre : 1 / 2 < (u + (δ : ℂ)).re := by simp; linarith
    rw [hΦdef]
    exact (differentiableAt_const _).mul ((differentiableAt_Hf hRH hre).comp u
      (differentiableAt_id.add_const _))
  have hΦL : ∀ u : ℂ, 1 < u.re → LSeries (fco δ) u = Φ u := fun u hu => by
    rw [hΦdef]; exact LSeries_fco hδ hu
  have hΦb : ∀ u : ℂ, 1 / 2 + ε / 2 ≤ u.re → ‖Φ u‖ ≤ CH / (1 / δ + 1) * (1 + |u.im|) ^ (ε / 16) := by
    intro u hu
    have hre : 1 / 2 + ε / 2 ≤ (u + (δ : ℂ)).re := by simp; linarith
    have h := hCH _ hre
    have him : (u + (δ : ℂ)).im = u.im := by simp
    rw [him] at h
    rw [hΦdef]
    simp only
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB0]
    calc (1 / δ + 1)⁻¹ * ‖Hf (u + (δ : ℂ))‖ ≤ (1 / δ + 1)⁻¹ * (CH * (1 + |u.im|) ^ (ε / 16)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = CH / (1 / δ + 1) * (1 + |u.im|) ^ (ε / 16) := by ring
  obtain ⟨K, hK0, hK⟩ := cota_gen (norm_fco_le hδ) hΦd hΦL hε hε1 (by positivity) hΦb
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = ((1 / 2 + ε : ℝ) : ℂ) := ⟨_, rfl⟩
  have hwre : w.re = 1 / 2 + ε := by rw [hw, ofReal_re]
  have hwim : w.im = 0 := by rw [hw, ofReal_im]
  have hbd : ∀ N : ℕ, ‖∑ n ∈ Finset.range (N + 1), LSeries.term (fco δ) w n‖ ≤ ‖Φ w‖ + K := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [zero_add, Finset.range_one, Finset.sum_singleton, LSeries.term_zero, norm_zero]
      positivity
    · have h := hK w hwre N hN
      have hx1 := xN_ge_um hN
      have hxle : xN N ^ (-(ε / 4)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
      rw [hwim, abs_zero, add_zero, Real.one_rpow, one_mul] at h
      have h' : ‖∑ n ∈ Finset.range (N + 1), LSeries.term (fco δ) w n - Φ w‖ ≤ K :=
        h.trans (by nlinarith)
      calc ‖∑ n ∈ Finset.range (N + 1), LSeries.term (fco δ) w n‖
          = ‖(∑ n ∈ Finset.range (N + 1), LSeries.term (fco δ) w n - Φ w) + Φ w‖ := by ring_nf
        _ ≤ ‖∑ n ∈ Finset.range (N + 1), LSeries.term (fco δ) w n - Φ w‖ + ‖Φ w‖ := norm_add_le _ _
        _ ≤ ‖Φ w‖ + K := by linarith
  refine ⟨(1 / δ + 1) * (‖Φ w‖ + K), fun N => ?_⟩
  have e : ∑ n ∈ Finset.range (N + 1), LSeries.term cL ((1 / 2 + ε + δ : ℝ) : ℂ) n =
      ((1 / δ + 1 : ℝ) : ℂ) * ∑ n ∈ Finset.range (N + 1), LSeries.term (fco δ) w n := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hB : ((1 / δ + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hB0.ne'
    rw [term_fco hδ, ← mul_assoc, mul_inv_cancel₀ hB, one_mul, hw]
    congr 1
    push_cast
    ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB0]
  exact mul_le_mul_of_nonneg_left (hbd N) hB0.le

/-! ## 6. Por partes, e o critério de von Koch -/

theorem term_mul_rpow (a : ℕ → ℂ) (σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term a (σ : ℂ) n * (((n : ℝ) ^ σ : ℝ) : ℂ) = a n := by
  rw [LSeries.term_of_ne_zero hn, ofReal_cpow (Nat.cast_nonneg n)]
  have h : ((n : ℝ) : ℂ) ^ (σ : ℂ) ≠ 0 := by
    rw [← ofReal_cpow (Nat.cast_nonneg n)]
    exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) σ).ne'
  push_cast at h ⊢
  field_simp

/-- **Por partes**: se `|Σ_{n ≤ N} a(n)n^{−σ}| ≤ B` para todo `N`, então `|Σ_{1 ≤ n ≤ N} a(n)| ≤ 2B N^σ`. -/
theorem abel_cota {a : ℕ → ℂ} {σ B : ℝ} (hσ : 0 < σ)
    (hB : ∀ N : ℕ, ‖∑ n ∈ Finset.range (N + 1), LSeries.term a (σ : ℂ) n‖ ≤ B) (N : ℕ) :
    ‖∑ n ∈ Finset.range (N + 1), LSeries.term a (σ : ℂ) n * (((n : ℝ) ^ σ : ℝ) : ℂ)‖ ≤
      2 * B * (N : ℝ) ^ σ := by
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℂ, b = fun n : ℕ => (((n : ℝ) ^ σ : ℝ) : ℂ) := ⟨_, rfl⟩
  have hab := abel (fun n => LSeries.term a (σ : ℂ) n) b N
  have hS : ∑ n ∈ Finset.range (N + 1), LSeries.term a (σ : ℂ) n * (((n : ℝ) ^ σ : ℝ) : ℂ) =
      ∑ n ∈ Finset.range (N + 1), LSeries.term a (σ : ℂ) n * b n := by rw [hb]
  rw [hS, hab]
  have hmono : ∀ n : ℕ, (n : ℝ) ^ σ ≤ ((n : ℝ) + 1) ^ σ := fun n =>
    Real.rpow_le_rpow (Nat.cast_nonneg n) (by linarith) hσ.le
  have hbsub : ∀ n : ℕ, ‖b (n + 1) - b n‖ = ((n : ℝ) + 1) ^ σ - (n : ℝ) ^ σ := by
    intro n
    rw [hb]
    simp only
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Nat.cast_succ,
      abs_of_nonneg (sub_nonneg.mpr (hmono n))]
  have htel : ∑ n ∈ Finset.range N, (((n : ℝ) + 1) ^ σ - (n : ℝ) ^ σ) = (N : ℝ) ^ σ := by
    have := Finset.sum_range_sub (fun n : ℕ => (n : ℝ) ^ σ) N
    simp only [Nat.cast_succ, Nat.cast_zero, Real.zero_rpow hσ.ne', sub_zero] at this
    exact this
  have h1 : ‖∑ n ∈ Finset.range N, (∑ k ∈ Finset.range (n + 1), LSeries.term a (σ : ℂ) k) *
      (b (n + 1) - b n)‖ ≤ B * (N : ℝ) ^ σ := by
    refine (norm_sum_le _ _).trans ?_
    rw [← htel, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul, hbsub n]
    exact mul_le_mul_of_nonneg_right (hB n) (sub_nonneg.mpr (hmono n))
  have h2 : ‖(∑ n ∈ Finset.range (N + 1), LSeries.term a (σ : ℂ) n) * b N‖ ≤ B * (N : ℝ) ^ σ := by
    have hbN : ‖b N‖ = (N : ℝ) ^ σ := by
      rw [hb]
      simp only
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) σ)]
    rw [norm_mul, hbN]
    exact mul_le_mul_of_nonneg_right (hB N) (Real.rpow_nonneg (Nat.cast_nonneg N) σ)
  refine (norm_sub_le _ _).trans ?_
  linarith

theorem E_eq_sum (σ : ℝ) (N : ℕ) :
    ((E N : ℝ) : ℂ) = ∑ n ∈ Finset.range (N + 1), LSeries.term cL (σ : ℂ) n * (((n : ℝ) ^ σ : ℝ) : ℂ) := by
  rcases N with _ | n
  · simp [E, Chebyshev.psi_zero]
  · rw [E_succ, Finset.sum_range_succ' (fun k => LSeries.term cL (σ : ℂ) k * (((k : ℝ) ^ σ : ℝ) : ℂ))]
    simp only [LSeries.term_zero, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [term_mul_rpow cL σ (Nat.succ_ne_zero k)]

/-- **RH ⟹ `ψ(x) = x + O(x^{1/2 + ε})`** (von Koch 1901, direção ⇒). -/
theorem psi_of_RH (hRH : RiemannHypothesis) : VonKochFraco := by
  suffices h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C : ℝ, ∀ N : ℕ,
      |Chebyshev.psi N - N| ≤ C * ((N : ℝ) + 1) ^ (1 / 2 + ε) by
    intro ε hε
    rcases le_or_gt ε 1 with h1 | h1
    · exact h ε hε h1
    · obtain ⟨C, hC⟩ := h 1 one_pos le_rfl
      have hC0 : 0 ≤ C := by
        have := hC 0
        simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one] at this
        exact le_trans (abs_nonneg _) this
      refine ⟨C, fun N => (hC N).trans ?_⟩
      have hN : (1 : ℝ) ≤ (N : ℝ) + 1 := by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) hC0
  intro ε hε hε1
  obtain ⟨B₂, hB₂⟩ := somas_limitadas hRH (ε := ε / 2) (δ := ε / 4) (by linarith) (by linarith) (by linarith)
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = 1 / 2 + ε / 2 + ε / 4 := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  have hB : ∀ N : ℕ, ‖∑ n ∈ Finset.range (N + 1), LSeries.term cL (σ : ℂ) n‖ ≤ B₂ := by
    intro N; rw [hσ]; exact hB₂ N
  have hB0 : 0 ≤ B₂ := le_trans (norm_nonneg _) (hB 0)
  refine ⟨2 * B₂, fun N => ?_⟩
  have hn := congrArg norm (E_eq_sum σ N)
  rw [Complex.norm_real, Real.norm_eq_abs] at hn
  have h1 : |E N| ≤ 2 * B₂ * (N : ℝ) ^ σ := by rw [hn]; exact abel_cota hσ0 hB N
  have hEN : |Chebyshev.psi N - N| = |E N| := rfl
  rw [hEN]
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hN0 := (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  calc (N : ℝ) ^ σ ≤ ((N : ℝ) + 1) ^ σ := Real.rpow_le_rpow hN0 (by linarith) hσ0.le
    _ ≤ ((N : ℝ) + 1) ^ (1 / 2 + ε) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hσ]; linarith)

/-- **O critério de von Koch** (1901): `RH ⟺ ψ(x) = x + O(x^{1/2 + ε})` para todo `ε > 0`. -/
theorem rh_iff_psi : RiemannHypothesis ↔ VonKochFraco :=
  ⟨psi_of_RH, RH_of_psi⟩

/-- As duas hipóteses fracas, de von Koch e de Littlewood, são equivalentes (ambas equivalem a RH). -/
theorem vonKoch_iff_mertens : VonKochFraco ↔ ATK.ZeroClasses.Mertens.MertensFraco :=
  rh_iff_psi.symm.trans ATK.ZeroClasses.Mertens.rh_iff_mertens

end ATK.ZeroClasses.VonKochRH

#print axioms ATK.ZeroClasses.VonKochRH.norm_g
#print axioms ATK.ZeroClasses.VonKochRH.bordo_g
#print axioms ATK.ZeroClasses.VonKochRH.desloca
#print axioms ATK.ZeroClasses.VonKochRH.horiz_g
#print axioms ATK.ZeroClasses.VonKochRH.vert_g
#print axioms ATK.ZeroClasses.VonKochRH.cota_gen
#print axioms ATK.ZeroClasses.VonKochRH.deriv_zeta₁
#print axioms ATK.ZeroClasses.VonKochRH.Hf_eq
#print axioms ATK.ZeroClasses.VonKochRH.differentiableAt_Hf
#print axioms ATK.ZeroClasses.VonKochRH.norm_logDeriv_le_dois
#print axioms ATK.ZeroClasses.VonKochRH.norm_H_le
#print axioms ATK.ZeroClasses.VonKochRH.norm_cL_le
#print axioms ATK.ZeroClasses.VonKochRH.norm_fco_le
#print axioms ATK.ZeroClasses.VonKochRH.term_fco
#print axioms ATK.ZeroClasses.VonKochRH.LSeries_fco
#print axioms ATK.ZeroClasses.VonKochRH.somas_limitadas
#print axioms ATK.ZeroClasses.VonKochRH.term_mul_rpow
#print axioms ATK.ZeroClasses.VonKochRH.abel_cota
#print axioms ATK.ZeroClasses.VonKochRH.E_eq_sum
#print axioms ATK.ZeroClasses.VonKochRH.psi_of_RH
#print axioms ATK.ZeroClasses.VonKochRH.rh_iff_psi
#print axioms ATK.ZeroClasses.VonKochRH.vonKoch_iff_mertens
