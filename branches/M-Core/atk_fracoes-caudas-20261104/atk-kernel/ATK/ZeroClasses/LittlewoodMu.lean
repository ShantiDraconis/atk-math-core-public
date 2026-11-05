import ATK.ZeroClasses.PerronDirichlet
import ATK.ZeroClasses.JSobRH
import ATK.RHLogZeta

/-!
# O teorema de Littlewood para `Σ μ(n) n^{−s}` sob RH (rodada 46)

**Teorema** (Littlewood, 1912). Sob RH, para `½ < Re w ≤ 3/2`, as somas parciais de corte abrupto
`P_N(w) = Σ_{n ≤ N} μ(n) n^{−w}` satisfazem

  `|P_N(w) − F(w)| ≤ K (1 + |Im w|)^η (N + ½)^{−ε/4}`,   `ε = Re w − ½`, `η = ε/16`

(`cota_PN`), com `F(w) = (w − 1)/ζ₁(w) = 1/ζ(w)` (`ATK.RHLogZeta.F`). Em particular `P_N(w) → 1/ζ(w)`
(`littlewood`).

A prova é a fórmula de Perron truncada (rodadas 44 e 45) com `c = ½` e `T = x²`, `x = N + ½`, seguida do
deslocamento do segmento vertical até `Re z = −ε/2` num retângulo (`bordo_g`): o resíduo em `z = 0` é `F(w)`, e
os três lados novos são estimados com a cota `|F(s)| ≤ C (1 + |Im s|)^η` em `Re s ≥ ½ + ε/2`
(`ATK.RHLogZeta.norm_F_le`, Titchmarsh 14.2).

Consequência: **`entradaLittlewood`** (`ATK.NecessidadeBD.EntradaLittlewood ε` para `0 < ε ≤ ¼`, com a dominação
vinda da razão `ζ(s)/ζ(s + ε)` da rodada 43 e de Lindelöf à direita da reta) e **`necessidadeRH`**: a estrutura
nomeada `ATK.FechamentoO1.NecessidadeRH` (mollificador de corte abrupto) é um teorema. O critério
`RH ⟺ D_N → 0` já estava certificado (`ATK.NecessidadeRH.rh_iff_DN`, mollificador suavizado); aqui ele sai também
pelo caminho clássico (`rh_iff_DN_classico`).

Classificação (rodada 46): **consequência** de RH (Littlewood) e fechamento de `NecessidadeRH`. Não é RH.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

namespace ATK.ZeroClasses.LittlewoodMu

open ATK.ZeroClasses.ArgRetangulo (bordo Bordo Ret bordo_congr bordo_add bordo_cauchy bordo_inv bordo_const_mul)
open ATK.ZeroClasses.PerronD (xN xN_pos perron_LSeries summable_um)
open ATK.RHLogZeta (F F_eq differentiableAt_F norm_F_le)

/-! ## 1. Möbius -/

/-- `μ` como coeficiente complexo. -/
noncomputable abbrev mu : ℕ → ℂ := fun n => (ArithmeticFunction.moebius n : ℂ)

theorem norm_mu_le (n : ℕ) : ‖mu n‖ ≤ 1 := by
  have := ArithmeticFunction.abs_moebius_le_one (n := n)
  simp only [mu, Complex.norm_intCast]
  exact_mod_cast this

theorem LSeries_mu {u : ℂ} (hu : 1 < u.re) : LSeries mu u = F u := by
  have := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hu
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hu] at this
  have hu1 : u ≠ 1 := fun h => by rw [h, one_re] at hu; exact lt_irrefl 1 hu
  rw [F_eq hu1]
  exact eq_inv_of_mul_eq_one_right this

/-! ## 2. O deslocamento -/

/-- `G(z) = x^z F(w + z)`. -/
noncomputable def Gf (x : ℝ) (w z : ℂ) : ℂ := (x : ℂ) ^ z * F (w + z)

/-- O integrando `g(z) = x^z F(w + z)/z`. -/
noncomputable def g (x : ℝ) (w z : ℂ) : ℂ := Gf x w z / z

theorem norm_g {x : ℝ} (hx : 0 < x) (w z : ℂ) : ‖g x w z‖ = x ^ z.re * ‖F (w + z)‖ / ‖z‖ := by
  rw [g, Gf, norm_div, norm_mul, norm_cpow_eq_rpow_re_of_pos hx]

/-- Álgebra das quatro integrais com resíduo `R`. -/
theorem alg_res {A B V D R : ℂ} (h : A - B + I * V - I * D = 2 * π * I * R) :
    ‖(2 * π : ℂ)⁻¹ * V - R‖ ≤ (‖A‖ + ‖B‖ + ‖D‖) / (2 * π) := by
  have hπ : (2 * π : ℂ) ≠ 0 := by
    have : (2 * π : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have h2 : (2 * π : ℂ)⁻¹ * (2 * π) = 1 := inv_mul_cancel₀ hπ
  have hden : (2 * π * I : ℂ) ≠ 0 := mul_ne_zero hπ I_ne_zero
  have e : (2 * π : ℂ)⁻¹ * V - R = (B - A + I * D) / (2 * π * I) := by
    rw [eq_div_iff hden]
    calc ((2 * π : ℂ)⁻¹ * V - R) * (2 * π * I) =
          I * V * ((2 * π : ℂ)⁻¹ * (2 * π)) - 2 * π * I * R := by ring
      _ = I * V - 2 * π * I * R := by rw [h2, mul_one]
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

/-- **O resíduo**: `∮ x^z F(w + z)/z dz = 2πi F(w)` no retângulo `[−b, c] × [−T, T]`, sob RH. -/
theorem bordo_g (hRH : RiemannHypothesis) {w : ℂ} {x b c T : ℝ} (hx : 0 < x) (hb : 0 < b) (hc : 0 < c)
    (hT : 0 < T) (hwb : 1 / 2 < w.re - b) :
    bordo (g x w) ⟨-b, -T⟩ ⟨c, T⟩ = 2 * π * I * F w := by
  set U : Set ℂ := {z | 1 / 2 < w.re + z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const (continuous_const.add continuous_re)
  have h0U : (0 : ℂ) ∈ U := by
    show 1 / 2 < w.re + (0 : ℂ).re
    rw [zero_re, add_zero]
    linarith
  have hGd : DifferentiableOn ℂ (Gf x w) U := fun z hz => by
    have h1 : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ z) z :=
      differentiableAt_id.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))
    have hre : 1 / 2 < (w + z).re := by rw [add_re]; exact hz
    have h2 : DifferentiableAt ℂ (fun z : ℂ => F (w + z)) z :=
      (differentiableAt_F hRH hre).comp z (differentiableAt_id.const_add w)
    exact (h1.mul h2).differentiableWithinAt
  have hDd : DifferentiableOn ℂ (dslope (Gf x w) 0) U :=
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
  have heq : EqOn (g x w) (fun s => dslope (Gf x w) 0 s + Gf x w 0 * (s - 0)⁻¹) (Bordo ⟨-b, -T⟩ ⟨c, T⟩) := by
    intro s hs
    have hs0 := hne s hs
    simp only [g, dslope_of_ne _ hs0, slope_def_field, sub_zero]
    rw [sub_div]
    ring
  have hc1 : ContinuousOn (dslope (Gf x w) 0) (Bordo ⟨-b, -T⟩ ⟨c, T⟩) :=
    (hDd.mono (hBR.trans hsub)).continuousOn
  have hc2 : ContinuousOn (fun s : ℂ => Gf x w 0 * (s - 0)⁻¹) (Bordo ⟨-b, -T⟩ ⟨c, T⟩) := fun s hs =>
    (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀
      (by simpa using hne s hs))).continuousWithinAt
  rw [bordo_congr heq, bordo_add hc1 hc2, bordo_cauchy (hDd.mono hsub), bordo_const_mul,
    bordo_inv (z := ⟨-b, -T⟩) (w := ⟨c, T⟩) (u := 0) (by simp; linarith) (by simp; linarith)
      (by simp; linarith) (by simp; linarith)]
  simp only [Gf, cpow_zero, one_mul, add_zero, zero_add]
  ring

/-- **O deslocamento**: `|(1/2π) ∫_{−T}^{T} g(c + iy) dy − F(w)| ≤ (|A| + |B| + |D|)/(2π)`. -/
theorem desloca_mu (hRH : RiemannHypothesis) {w : ℂ} {x b c T : ℝ} (hx : 0 < x) (hb : 0 < b) (hc : 0 < c)
    (hT : 0 < T) (hwb : 1 / 2 < w.re - b) :
    ‖(2 * π : ℂ)⁻¹ * (∫ y in (-T)..T, g x w ((c : ℂ) + y * I)) - F w‖ ≤
      (‖∫ t in (-b)..c, g x w ((t : ℂ) + ((-T : ℝ) : ℂ) * I)‖ +
        ‖∫ t in (-b)..c, g x w ((t : ℂ) + (T : ℂ) * I)‖ +
        ‖∫ y in (-T)..T, g x w (((-b : ℝ) : ℂ) + y * I)‖) / (2 * π) := by
  have hB := bordo_g hRH hx hb hc hT hwb
  simp only [bordo, smul_eq_mul] at hB
  exact alg_res hB

/-! ## 3. As cotas dos três lados -/

theorem um_add_abs_le (a y : ℝ) : 1 + |a + y| ≤ (1 + |a|) * (1 + |y|) := by
  have := abs_add_le a y
  nlinarith [abs_nonneg a, abs_nonneg y, mul_nonneg (abs_nonneg a) (abs_nonneg y)]

/-- **Lados horizontais**. -/
theorem horiz_g {w : ℂ} {x b c T δ η CF h : ℝ} (hx : 1 ≤ x) (hb : 0 ≤ b) (hc : 0 ≤ c) (hcb : c + b ≤ 1)
    (hT : 0 < T) (hh : |h| = T) (hη : 0 ≤ η) (hCF : 0 ≤ CF)
    (hF : ∀ u : ℂ, 1 / 2 + δ ≤ u.re → ‖F u‖ ≤ CF * (1 + |u.im|) ^ η) (hwb : 1 / 2 + δ ≤ w.re - b) :
    ‖∫ t in (-b)..c, g x w ((t : ℂ) + (h : ℂ) * I)‖ ≤
      x ^ c * CF * (1 + |w.im|) ^ η * (1 + T) ^ η / T := by
  have hx0 : 0 < x := by linarith
  have hK : 0 ≤ x ^ c * CF * (1 + |w.im|) ^ η * (1 + T) ^ η / T := by positivity
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -b) (b := c)
    (f := fun t : ℝ => g x w ((t : ℂ) + (h : ℂ) * I))
    (C := x ^ c * CF * (1 + |w.im|) ^ η * (1 + T) ^ η / T) (fun t ht => by
      rw [uIoc_of_le (by linarith)] at ht
      rw [norm_g hx0]
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
      have hFb2 : ‖F (w + ((t : ℂ) + (h : ℂ) * I))‖ ≤ CF * ((1 + |w.im|) ^ η * (1 + T) ^ η) := by
        refine hFb.trans (mul_le_mul_of_nonneg_left ?_ hCF)
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        apply Real.rpow_le_rpow (by positivity) _ hη
        have := um_add_abs_le w.im h
        rw [hh] at this
        exact this
      calc x ^ t * ‖F (w + ((t : ℂ) + (h : ℂ) * I))‖ / ‖(t : ℂ) + (h : ℂ) * I‖
          ≤ x ^ c * (CF * ((1 + |w.im|) ^ η * (1 + T) ^ η)) / T := by
            apply div_le_div₀ (by positivity) (mul_le_mul hxt hFb2 (norm_nonneg _) (by positivity)) hT hz
        _ = x ^ c * CF * (1 + |w.im|) ^ η * (1 + T) ^ η / T := by ring)
  refine this.trans ?_
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ c - -b)]
  calc x ^ c * CF * (1 + |w.im|) ^ η * (1 + T) ^ η / T * (c - -b)
      ≤ x ^ c * CF * (1 + |w.im|) ^ η * (1 + T) ^ η / T * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) hK
    _ = _ := mul_one _

/-- `I_η = ∫ (1 + |y|)^{−(1+η)}`. -/
theorem integrable_peso {η : ℝ} (hη : 0 < η) : Integrable (fun y : ℝ => (1 + |y|) ^ (-(1 + η))) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 1 + η) (by simp; linarith)
  simpa [Real.norm_eq_abs] using this

/-- **Lado vertical** em `Re z = −b`. -/
theorem vert_g {w : ℂ} {x b T δ η CF : ℝ} (hx : 0 < x) (hb : 0 < b) (hT : 0 ≤ T) (hη : 0 < η)
    (hCF : 0 ≤ CF) (hF : ∀ u : ℂ, 1 / 2 + δ ≤ u.re → ‖F u‖ ≤ CF * (1 + |u.im|) ^ η)
    (hwb : 1 / 2 + δ ≤ w.re - b) :
    ‖∫ y in (-T)..T, g x w (((-b : ℝ) : ℂ) + y * I)‖ ≤
      x ^ (-b) * CF * (1 + |w.im|) ^ η * (1 + 1 / b) * (1 + T) ^ (2 * η) *
        ∫ y : ℝ, (1 + |y|) ^ (-(1 + η)) := by
  set M := x ^ (-b) * CF * (1 + |w.im|) ^ η * (1 + 1 / b) * (1 + T) ^ (2 * η) with hM
  have hM0 : 0 ≤ M := by positivity
  have hint := integrable_peso hη
  have hpt : ∀ y ∈ Ioc (-T) T, ‖g x w (((-b : ℝ) : ℂ) + y * I)‖ ≤ M * (1 + |y|) ^ (-(1 + η)) := by
    intro y hy
    have hyT : |y| ≤ T := abs_le.mpr ⟨hy.1.le, hy.2⟩
    have hp1 : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
    have hp0 : 0 < 1 + |y| := by linarith
    rw [norm_g hx]
    have hre : (((-b : ℝ) : ℂ) + y * I).re = -b := by simp
    have him : (((-b : ℝ) : ℂ) + y * I).im = y := by simp
    rw [hre]
    have hwre : 1 / 2 + δ ≤ (w + (((-b : ℝ) : ℂ) + y * I)).re := by rw [add_re, hre]; linarith
    have hFb := hF _ hwre
    rw [add_im, him] at hFb
    have hFb2 : ‖F (w + (((-b : ℝ) : ℂ) + y * I))‖ ≤ CF * ((1 + |w.im|) ^ η * (1 + |y|) ^ η) := by
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
    calc x ^ (-b) * ‖F (w + (((-b : ℝ) : ℂ) + y * I))‖ / ‖((-b : ℝ) : ℂ) + y * I‖
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

/-! ## 4. A estimativa de Littlewood -/

/-- Potências: `x^a x^b ≤ x^c` para `x ≥ 1`, `a + b ≤ c`. -/
theorem rpow_mul_le {x a b c : ℝ} (hx : 1 ≤ x) (h : a + b ≤ c) : x ^ a * x ^ b ≤ x ^ c := by
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hx h

/-- `(1 + x²)^θ ≤ 2 x^{2θ}` para `x ≥ 1`, `0 ≤ θ ≤ 1`. -/
theorem um_add_sq_rpow_le {x θ : ℝ} (hx : 1 ≤ x) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 + x ^ (2 : ℝ)) ^ θ ≤ 2 * x ^ (2 * θ) := by
  have hx0 : 0 < x := by linarith
  have h1 : 1 ≤ x ^ (2 : ℝ) := Real.one_le_rpow hx (by norm_num)
  calc (1 + x ^ (2 : ℝ)) ^ θ ≤ (2 * x ^ (2 : ℝ)) ^ θ := Real.rpow_le_rpow (by positivity) (by linarith) hθ
    _ = 2 ^ θ * x ^ (2 * θ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hx0.le]
    _ ≤ 2 * x ^ (2 * θ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        calc (2 : ℝ) ^ θ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
          _ = 2 := Real.rpow_one 2

/-- `y^a y^b / y² ≤ y^c` para `y ≥ 1`, `a + b ≤ c + 2`. -/
theorem rpow_div_le {y a b c : ℝ} (hy : 1 ≤ y) (h : a + b ≤ c + 2) : y ^ a * y ^ b / y ^ (2 : ℝ) ≤ y ^ c := by
  have hy0 : 0 < y := by linarith
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hy0 _), ← Real.rpow_add hy0, ← Real.rpow_add hy0]
  exact Real.rpow_le_rpow_of_exponent_le hy h

theorem xN_ge_um {N : ℕ} (hN : 1 ≤ N) : 1 ≤ xN N := by
  unfold xN
  have : (1 : ℝ) ≤ N := by exact_mod_cast hN
  linarith

/-- **Littlewood com taxa**: sob RH, para `Re w = ½ + ε` (`0 < ε ≤ 1`) e `N ≥ 1`,
`|Σ_{n ≤ N} μ(n) n^{−w} − F(w)| ≤ K (1 + |Im w|)^{ε/16} (N + ½)^{−ε/4}`. -/
theorem cota_PN (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, w.re = 1 / 2 + ε → ∀ N : ℕ, 1 ≤ N →
      ‖∑ n ∈ Finset.range (N + 1), LSeries.term mu w n - F w‖ ≤
        K * ((1 + |w.im|) ^ (ε / 16) * xN N ^ (-(ε / 4))) := by
  obtain ⟨CF, hCF0, hCF⟩ := norm_F_le hRH (δ := ε / 2) (η := ε / 16) (by positivity) (by linarith)
    (by positivity)
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
  have hP := perron_LSeries norm_mu_le N (s := w) (c := 1 / 2) (T := xN N ^ (2 : ℝ)) (by norm_num)
    (by rw [hw]; linarith) hT0
  rw [hw, ← hZt] at hP
  have hV : (∫ t in (-(xN N ^ (2 : ℝ)))..(xN N ^ (2 : ℝ)), LSeries mu (w + (((1 / 2 : ℝ) : ℂ) + t * I)) *
      (xN N : ℂ) ^ (((1 / 2 : ℝ) : ℂ) + t * I) / (((1 / 2 : ℝ) : ℂ) + t * I)) =
      ∫ t in (-(xN N ^ (2 : ℝ)))..(xN N ^ (2 : ℝ)), g (xN N) w (((1 / 2 : ℝ) : ℂ) + t * I) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hre : 1 < (w + (((1 / 2 : ℝ) : ℂ) + t * I)).re := by simp [hw]; linarith
    simp only [g, Gf]
    rw [LSeries_mu hre]
    ring
  rw [hV] at hP
  -- o deslocamento e os três lados
  have hR := desloca_mu hRH (w := w) (x := xN N) (b := ε / 2) (c := 1 / 2) (T := xN N ^ (2 : ℝ)) hx0
    (by positivity) (by norm_num) hT0 (by rw [hw]; linarith)
  have hA := horiz_g (w := w) (x := xN N) (b := ε / 2) (c := 1 / 2) (T := xN N ^ (2 : ℝ)) (δ := ε / 2)
    (η := ε / 16) (CF := CF) (h := -(xN N ^ (2 : ℝ))) hx1 (by positivity) (by norm_num) (by linarith) hT0
    (by rw [abs_neg, abs_of_pos hT0]) (by positivity) hCF0.le hCF (by rw [hw]; linarith)
  have hB := horiz_g (w := w) (x := xN N) (b := ε / 2) (c := 1 / 2) (T := xN N ^ (2 : ℝ)) (δ := ε / 2)
    (η := ε / 16) (CF := CF) (h := xN N ^ (2 : ℝ)) hx1 (by positivity) (by norm_num) (by linarith) hT0
    (abs_of_pos hT0) (by positivity) hCF0.le hCF (by rw [hw]; linarith)
  have hD := vert_g (w := w) (x := xN N) (b := ε / 2) (T := xN N ^ (2 : ℝ)) (δ := ε / 2) (η := ε / 16)
    hx0 (by positivity) hT0.le (by positivity) hCF0.le hCF (by rw [hw]; linarith)
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
  calc ‖∑ n ∈ Finset.range (N + 1), LSeries.term mu w n - F w‖
      ≤ ‖∑ n ∈ Finset.range (N + 1), LSeries.term mu w n - (2 * π : ℂ)⁻¹ *
          ∫ t in (-(xN N ^ (2 : ℝ)))..(xN N ^ (2 : ℝ)), g (xN N) w (((1 / 2 : ℝ) : ℂ) + t * I)‖ +
        ‖(2 * π : ℂ)⁻¹ * (∫ t in (-(xN N ^ (2 : ℝ)))..(xN N ^ (2 : ℝ)), g (xN N) w (((1 / 2 : ℝ) : ℂ) + t * I)) -
          F w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add hP' hR'
    _ ≤ 6 * Zt / π * ((1 + |w.im|) ^ (ε / 16) * xN N ^ (-(ε / 4))) +
          (4 * CF + 2 * CF * (1 + 1 / (ε / 2)) * Ie) / (2 * π) *
            ((1 + |w.im|) ^ (ε / 16) * xN N ^ (-(ε / 4))) := by
        have hθa : xN N ^ (-(ε / 4)) ≤ (1 + |w.im|) ^ (ε / 16) * xN N ^ (-(ε / 4)) :=
          le_mul_of_one_le_left hθ0.le ha1
        have key := mul_le_mul_of_nonneg_left hθa (by positivity : (0 : ℝ) ≤ 6 * Zt / π)
        exact add_le_add (le_of_eq_of_le (by ring) key) (le_of_eq (by ring))
    _ = _ := by ring

/-- **O teorema de Littlewood** (1912): sob RH, `Σ_{n ≤ N} μ(n) n^{−w} → F(w) = 1/ζ(w)` para `½ < Re w ≤ 3/2`. -/
theorem littlewood (hRH : RiemannHypothesis) {w : ℂ} (hw : 1 / 2 < w.re) (hw1 : w.re ≤ 3 / 2) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), LSeries.term mu w n) atTop (𝓝 (F w)) := by
  obtain ⟨K, hK0, hK⟩ := cota_PN hRH (ε := w.re - 1 / 2) (by linarith) (by linarith)
  have hx : Tendsto (fun N : ℕ => xN N) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hθ : Tendsto (fun N : ℕ => xN N ^ (-((w.re - 1 / 2) / 4))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp hx
  have hlim : Tendsto (fun N : ℕ => K * ((1 + |w.im|) ^ ((w.re - 1 / 2) / 16) * xN N ^ (-((w.re - 1 / 2) / 4))))
      atTop (𝓝 0) := by
    simpa using (hθ.const_mul ((1 + |w.im|) ^ ((w.re - 1 / 2) / 16))).const_mul K
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact hK w (by ring) N hN

/-! ## 5. A entrada de Littlewood e `NecessidadeRH` -/

theorem polD_eq (ε : ℝ) (N : ℕ) (s : ℂ) :
    ATK.NecessidadeBD.polD (ATK.NecessidadeBD.moll ε) N s =
      ∑ n ∈ Finset.range (N + 1), LSeries.term mu (s + ε) n := by
  rw [ATK.NecessidadeBD.polD_moll_eq_term, Fin.sum_univ_eq_sum_range
    (fun i => LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) (s + ε) (i + 1)) N,
    Finset.sum_range_succ' (fun n => LSeries.term mu (s + ε) n)]
  simp

/-- **A entrada de Littlewood** (`ATK.NecessidadeBD.EntradaLittlewood ε`) sob RH, para `0 < ε ≤ ¼`. -/
theorem entradaLittlewood (hRH : RiemannHypothesis) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1 / 4) :
    ATK.NecessidadeBD.EntradaLittlewood ε := by
  obtain ⟨K, hK0, hK⟩ := cota_PN hRH h0 (by linarith)
  obtain ⟨CF, hCF0, hCF⟩ := norm_F_le hRH (δ := ε) (η := ε / 16) h0 (by linarith) (by positivity)
  obtain ⟨Kr, hKr0, hKr⟩ := ATK.ZeroClasses.JRH.razao_zeta hRH
  obtain ⟨CZ, hCZ0, hCZ⟩ := ATK.RHLogZeta.norm_zeta_le_RH hRH (δ := ε) (η := ε / 16) h0 (by linarith)
    (by positivity)
  have hwre : ∀ τ : ℝ, (ATK.NecessidadeBD.lc τ + ε).re = 1 / 2 + ε := fun τ => by
    simp [ATK.NecessidadeBD.lc]
  have hwim : ∀ τ : ℝ, (ATK.NecessidadeBD.lc τ + ε).im = τ := fun τ => by
    simp [ATK.NecessidadeBD.lc]
  -- `|P_N| ≤ (K + CF)(1 + |τ|)^{ε/16}`
  have hPN : ∀ (N : ℕ) (τ : ℝ),
      ‖ATK.NecessidadeBD.polD (ATK.NecessidadeBD.moll ε) N (ATK.NecessidadeBD.lc τ)‖ ≤
        (K + CF) * (1 + |τ|) ^ (ε / 16) := by
    intro N τ
    rw [polD_eq]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [zero_add, Finset.range_one, Finset.sum_singleton, LSeries.term_zero, norm_zero]
      positivity
    · have h := hK _ (hwre τ) N hN
      rw [hwim τ] at h
      have hF := hCF _ (le_of_eq (hwre τ).symm)
      rw [hwim τ] at hF
      have hx : xN N ^ (-(ε / 4)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (xN_ge_um hN) (by linarith)
      have ha : 0 ≤ (1 + |τ|) ^ (ε / 16) := by positivity
      have htri := norm_add_le (∑ n ∈ Finset.range (N + 1), LSeries.term mu (ATK.NecessidadeBD.lc τ + ε) n -
        F (ATK.NecessidadeBD.lc τ + ε)) (F (ATK.NecessidadeBD.lc τ + ε))
      rw [sub_add_cancel] at htri
      have hKa : K * ((1 + |τ|) ^ (ε / 16) * xN N ^ (-(ε / 4))) ≤ K * (1 + |τ|) ^ (ε / 16) :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_right ha hx) hK0
      linarith
  -- `|ζ(½ + iτ)| ≤ Kr CZ (1 + |τ|)^{1/4 + ε/16}`
  have hZs : ∀ τ : ℝ, ‖riemannZeta (ATK.NecessidadeBD.lc τ)‖ ≤
      Kr * CZ * ((1 + |τ|) ^ (1 / 4 : ℝ) * (1 + |τ|) ^ (ε / 16)) := by
    intro τ
    have h1 := hKr τ ε h0 (by linarith)
    have h2 := hCZ _ (le_of_eq (hwre τ).symm) (by rw [hwre τ]; linarith)
    rw [hwim τ] at h2
    calc ‖riemannZeta (ATK.NecessidadeBD.lc τ)‖
        ≤ Kr * (1 + |τ|) ^ (1 / 4 : ℝ) * ‖riemannZeta (ATK.NecessidadeBD.lc τ + ε)‖ := h1
      _ ≤ Kr * (1 + |τ|) ^ (1 / 4 : ℝ) * (CZ * (1 + |τ|) ^ (ε / 16)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Kr * CZ * ((1 + |τ|) ^ (1 / 4 : ℝ) * (1 + |τ|) ^ (ε / 16)) := by ring
  set M := Kr * CZ * (K + CF) with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨⟨fun τ => 16 * (1 + M ^ 2) * (1 + |τ|) ^ (-(5 / 4 : ℝ)), ?_, fun N => ae_of_all _ fun τ => ?_⟩,
    ae_of_all _ fun τ => ?_⟩
  · have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 5 / 4) (by norm_num)
    exact (by simpa [Real.norm_eq_abs] using this : Integrable fun τ : ℝ => (1 + |τ|) ^ (-(5 / 4 : ℝ))).const_mul _
  · -- dominação
    set a := 1 + |τ| with ha
    have ha1 : 1 ≤ a := by linarith [abs_nonneg τ]
    have ha0 : 0 < a := by linarith
    set q := a ^ (3 / 8 : ℝ) with hq
    have hq1 : 1 ≤ q := Real.one_le_rpow ha1 (by norm_num)
    have hprod : ‖riemannZeta (ATK.NecessidadeBD.lc τ) *
        ATK.NecessidadeBD.polD (ATK.NecessidadeBD.moll ε) N (ATK.NecessidadeBD.lc τ)‖ ≤ M * q := by
      rw [norm_mul]
      have h1 := hZs τ
      have h2 := hPN N τ
      have hexp : a ^ (1 / 4 : ℝ) * a ^ (ε / 16) * a ^ (ε / 16) ≤ q := by
        rw [← Real.rpow_add ha0, ← Real.rpow_add ha0, hq]
        exact Real.rpow_le_rpow_of_exponent_le ha1 (by linarith)
      calc ‖riemannZeta (ATK.NecessidadeBD.lc τ)‖ *
            ‖ATK.NecessidadeBD.polD (ATK.NecessidadeBD.moll ε) N (ATK.NecessidadeBD.lc τ)‖
          ≤ (Kr * CZ * (a ^ (1 / 4 : ℝ) * a ^ (ε / 16))) * ((K + CF) * a ^ (ε / 16)) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = M * (a ^ (1 / 4 : ℝ) * a ^ (ε / 16) * a ^ (ε / 16)) := by rw [hM]; ring
        _ ≤ M * q := mul_le_mul_of_nonneg_left hexp hM0
    have h1' : ‖1 - riemannZeta (ATK.NecessidadeBD.lc τ) *
        ATK.NecessidadeBD.polD (ATK.NecessidadeBD.moll ε) N (ATK.NecessidadeBD.lc τ)‖ ≤ 1 + M * q :=
      (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
    have hs2 : a ^ 2 ≤ 8 * ‖ATK.NecessidadeBD.lc τ‖ ^ 2 := by
      rw [ATK.ZeroClasses.JRH.norm_lc_sq, ha]
      nlinarith [sq_abs τ, abs_nonneg τ, sq_nonneg (|τ| - 1)]
    have hL : 0 < ‖ATK.NecessidadeBD.lc τ‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr (ATK.NecessidadeBD.lc_ne_zero τ)) 2
    have hq2 : q ^ 2 = a ^ (3 / 4 : ℝ) := by
      rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
      norm_num
    have e3 : a ^ (3 / 4 : ℝ) = a ^ (-(5 / 4) : ℝ) * a ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add ha0]
      norm_num
    have hp : 0 ≤ a ^ (-(5 / 4) : ℝ) := by positivity
    have hqq : 1 ≤ q ^ 2 := by nlinarith
    show ATK.NecessidadeBD.erro _ τ ≤ 16 * (1 + M ^ 2) * a ^ (-(5 / 4 : ℝ))
    unfold ATK.NecessidadeBD.erro
    rw [norm_div, div_pow, div_le_iff₀ hL]
    calc ‖1 - riemannZeta (ATK.NecessidadeBD.lc τ) *
          ATK.NecessidadeBD.polD (ATK.NecessidadeBD.moll ε) N (ATK.NecessidadeBD.lc τ)‖ ^ 2
        ≤ (1 + M * q) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1' 2
      _ ≤ 2 * (1 + M ^ 2) * q ^ 2 := by nlinarith [sq_nonneg (1 - M * q), sq_nonneg M]
      _ = 2 * (1 + M ^ 2) * (a ^ (-(5 / 4) : ℝ) * a ^ 2) := by rw [hq2, e3]
      _ ≤ 2 * (1 + M ^ 2) * (a ^ (-(5 / 4) : ℝ) * (8 * ‖ATK.NecessidadeBD.lc τ‖ ^ 2)) := by gcongr
      _ = 16 * (1 + M ^ 2) * a ^ (-(5 / 4 : ℝ)) * ‖ATK.NecessidadeBD.lc τ‖ ^ 2 := by ring
  · -- convergência
    have hfun : (fun N => ATK.NecessidadeBD.polD (ATK.NecessidadeBD.moll ε) N (ATK.NecessidadeBD.lc τ)) =
        fun N => ∑ n ∈ Finset.range (N + 1), LSeries.term mu (ATK.NecessidadeBD.lc τ + ε) n :=
      funext fun N => polD_eq ε N _
    have hne : ATK.NecessidadeBD.lc τ + ε ≠ 1 := fun h => by
      have := hwre τ
      rw [h, one_re] at this
      linarith
    rw [hfun, ← F_eq hne]
    exact littlewood hRH (by rw [hwre τ]; linarith) (by rw [hwre τ]; linarith)

/-- **As entradas da necessidade** sob RH (`ATK.NecessidadeBD.EntradasNecessidade`). -/
theorem entradas (hRH : RiemannHypothesis) : ATK.NecessidadeBD.EntradasNecessidade := by
  refine ⟨?_, ATK.ZeroClasses.JRH.tendsto_J hRH⟩
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with ε hε
  exact entradaLittlewood hRH hε.1 hε.2.le

/-- **`NecessidadeRH` é um teorema** (a estrutura nomeada de `ATK.FechamentoO1`, mollificador de corte abrupto). -/
theorem necessidadeRH : ATK.FechamentoO1.NecessidadeRH :=
  ATK.ZeroClasses.JRH.necessidade_iff_entrada.mpr fun hRH => (entradas hRH).1

/-- **O critério de Báez-Duarte pelo caminho clássico**: `RH ⟺ D_N → 0` (a primeira prova é
`ATK.NecessidadeRH.rh_iff_DN`, com o mollificador suavizado). -/
theorem rh_iff_DN_classico : RiemannHypothesis ↔ Tendsto ATK.Conditional.Riemann.DN atTop (𝓝 0) :=
  ATK.FechamentoO1.rh_iff_DN necessidadeRH

end ATK.ZeroClasses.LittlewoodMu

#print axioms ATK.ZeroClasses.LittlewoodMu.norm_mu_le
#print axioms ATK.ZeroClasses.LittlewoodMu.LSeries_mu
#print axioms ATK.ZeroClasses.LittlewoodMu.norm_g
#print axioms ATK.ZeroClasses.LittlewoodMu.alg_res
#print axioms ATK.ZeroClasses.LittlewoodMu.bordo_g
#print axioms ATK.ZeroClasses.LittlewoodMu.desloca_mu
#print axioms ATK.ZeroClasses.LittlewoodMu.um_add_abs_le
#print axioms ATK.ZeroClasses.LittlewoodMu.horiz_g
#print axioms ATK.ZeroClasses.LittlewoodMu.integrable_peso
#print axioms ATK.ZeroClasses.LittlewoodMu.vert_g
#print axioms ATK.ZeroClasses.LittlewoodMu.rpow_mul_le
#print axioms ATK.ZeroClasses.LittlewoodMu.um_add_sq_rpow_le
#print axioms ATK.ZeroClasses.LittlewoodMu.rpow_div_le
#print axioms ATK.ZeroClasses.LittlewoodMu.xN_ge_um
#print axioms ATK.ZeroClasses.LittlewoodMu.cota_PN
#print axioms ATK.ZeroClasses.LittlewoodMu.littlewood
#print axioms ATK.ZeroClasses.LittlewoodMu.polD_eq
#print axioms ATK.ZeroClasses.LittlewoodMu.entradaLittlewood
#print axioms ATK.ZeroClasses.LittlewoodMu.entradas
#print axioms ATK.ZeroClasses.LittlewoodMu.necessidadeRH
#print axioms ATK.ZeroClasses.LittlewoodMu.rh_iff_DN_classico
