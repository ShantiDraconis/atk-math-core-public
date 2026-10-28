import ATK.ZeroClasses.ExplicitaPecas
import ATK.ZeroClasses.PiLiRH

/-!
# RH ⟺ `ψ(x) = x + O(√x log² x)` ⟺ `π(x) = Li(x) + O(√x log x)` (rodada 67)

**Teorema** (von Koch, 1901). Sob RH,

  `|ψ(x) − x| ≤ K √x log² x` (`psi_RH_log2`)   e   `|π(x) − Li(x)| ≤ K √x log x` (`pi_RH_log`),

e as recíprocas valem (rodadas 64–65): **`rh_iff_psiLog2`**, **`rh_iff_piLog`**. É a forma clássica do critério de
von Koch. A prova passa o contorno de Perron **através** dos zeros (rodada 66):

1. Perron (`perron_psi`, rodada 64) com `η = 1/log x`, `c = 1 + 2η` e uma **altura boa** `T ∈ [x², x² + 1]`
   (`altura_boa`): `|ψ(N) − (1/2π) ∫_{−T}^{T} F(c + it) dt| ≤ 48e² log² x/π`, `x = N + ½`;
2. **o resíduo explícito** (`bordo_explicita`) no retângulo `[¼, c] × [−T, T]`:
   `(1/2π) ∫ F(c + it) dt = x − Σ_{|γ| < T} m_ρ x^ρ/ρ + (lados)/2π`;
3. sob RH `|x^ρ| = √x`, logo `|Σ m_ρ x^ρ/ρ| ≤ √x Σ_{|γ| ≤ T} m_ρ/|ρ| ≤ C √x log² x` (`soma_ordem_norm`); os lados
   horizontais custam `O(log² x)` (alturas boas) e o lado `Re s = ¼` custa `O(x^{1/4} log² x)`
   (`logDeriv_quarto_RH`);
4. para `π`: `|θ(x) − x| = O(√x log² x)` e a fórmula de partes da rodada 65 (`pi_sub_Li`): o termo de fronteira dá
   `√x log x` e a integral `∫_2^x t^{−1/2} dt ≤ 2√x`.

Classificação (rodada 67): **reformulação** — o critério de von Koch na forma clássica, com as recíprocas. RH continua
OPEN_MATH.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real Interval

namespace ATK.ZeroClasses.Koch

open ATK.ZeroClasses.PerronD (xN xN_pos)
open ATK.ZeroClasses.ArgRetangulo (bordo Bordo Ret)
open ATK.ZeroClasses.PsiRH (Fx px norm_Fx perron_psi integral_um_abs continuous_um_abs psi_le_sq)
open ATK.ZeroClasses.Explicita (altura_boa bordo_explicita soma_ordem_norm logDeriv_quarto_RH)
open ATK.ZeroClasses.PiLi (Li log_pos_of_ge integral_rpow_le)
open ATK.ZeroClasses.PiLiRH (pi_sub_Li log_dois_gt)

/-! ## 1. `ψ` -/

/-- **Sob RH, `|ψ(N) − (N + ½)| ≤ K √(N + ½) log²(N + ½)`** quando `log(N + ½) ≥ 4`. -/
theorem psi_RH_meio (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 4 ≤ Real.log (xN N) →
    |Chebyshev.psi N - xN N| ≤ K * Real.sqrt (xN N) * Real.log (xN N) ^ 2 := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := altura_boa
  obtain ⟨C₂, hC₂0, hC₂⟩ := logDeriv_quarto_RH hRH
  obtain ⟨C₃, hC₃0, hC₃⟩ := soma_ordem_norm
  refine ⟨128 + 16 * C₃ + 48 * C₁ + 24 * C₂, by positivity, fun N hL4 => ?_⟩
  set x := xN N with hxdef
  set L := Real.log x with hLdef
  have hx0 : 0 < x := xN_pos N
  have hL0 : 0 < L := by linarith
  have hx5 : 5 ≤ x := by
    have := Real.add_one_le_exp L
    rw [hLdef, Real.exp_log hx0] at this
    linarith
  have hx1 : 1 ≤ x := by linarith
  set η : ℝ := 1 / L with hηdef
  have hη0 : 0 < η := by positivity
  have hηL : η * L = 1 := by rw [hηdef]; field_simp
  have hη4 : η ≤ 1 / 4 := by
    rw [hηdef]
    exact one_div_le_one_div_of_le (by norm_num) hL4
  set c : ℝ := 1 + 2 * η with hcdef
  have hc1 : 1 < c := by linarith
  have hc2 : c ≤ 2 := by linarith
  have hx2 : 6 ≤ x ^ 2 := by
    have h := mul_le_mul hx5 hx5 (by norm_num) (by linarith)
    rw [sq]
    linarith
  -- a altura boa
  obtain ⟨T, hT1, hT2, hgood⟩ := hC₁ (x ^ 2) hx2
  have hT0 : 0 < T := by linarith
  have hT6 : 6 ≤ T := by linarith
  -- as potências
  have hxpow : ∀ u : ℝ, x ^ (u * η) = Real.exp u := by
    intro u
    rw [Real.rpow_def_of_pos hx0, ← hLdef]
    congr 1
    rw [hηdef]
    field_simp
  have hxc : x ^ c = Real.exp 2 * x := by
    rw [hcdef, Real.rpow_add hx0, Real.rpow_one, hxpow 2]
    ring
  have hsqx : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
  have hsq1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr hx1
  have hlog3 : Real.log 3 ≤ L := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith
  have hlog2 : Real.log 2 ≤ L := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogT : Real.log (2 + T) ≤ 3 * L := by
    have h1 : 2 + T ≤ 2 * x ^ 2 := by linarith
    have h2 : Real.log (2 * x ^ 2) = Real.log 2 + 2 * L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    have := Real.log_le_log (by positivity) h1
    linarith
  have hlogT' : Real.log T ≤ 3 * L :=
    (Real.log_le_log hT0 (by linarith)).trans hlogT
  have hlogT1 : Real.log (1 + T) ≤ 3 * L :=
    (Real.log_le_log (by positivity) (by linarith)).trans hlogT
  have he1 : Real.exp 1 ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have he2 : Real.exp 2 ≤ 8 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]
    have h0 := (Real.exp_pos 1).le
    have h' : Real.exp 1 ≤ 2.72 := by linarith
    have := mul_le_mul h' h' h0 (by norm_num)
    norm_num at this
    linarith
  have hpi := Real.pi_gt_three
  -- (1) Perron
  set Vc : ℂ := ∫ t in (-T)..T, (x : ℂ) ^ ((c : ℂ) + t * I) *
      (-logDeriv riemannZeta ((c : ℂ) + t * I)) / ((c : ℂ) + t * I) with hVc
  have hP := perron_psi N (η := η) (c := c) (T := T) hη0 (by linarith) (by linarith) hT0
  rw [← hxdef, ← hVc] at hP
  have hPerron : ‖(Chebyshev.psi N : ℂ) - (2 * π : ℂ)⁻¹ * Vc‖ ≤ 48 * Real.exp 2 * L ^ 2 / π := by
    have e8 : 8 / (c - η - 1) = 8 * L := by
      rw [hcdef, show 1 + 2 * η - η - 1 = η by ring, hηdef]
      field_simp
    rw [e8, hxc] at hP
    have hA : x * (4 * x + 2) / T ≤ 6 := by
      rw [div_le_iff₀ hT0]
      have hxx : x ≤ x ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hx0.le hx1
      have hTx : x ^ 2 ≤ T := hT1
      nlinarith
    have hbound : Real.exp 2 * x * (4 * x + 2) / (π * T) * (8 * L) ≤ 48 * Real.exp 2 * L / π := by
      have e : Real.exp 2 * x * (4 * x + 2) / (π * T) * (8 * L) =
          (x * (4 * x + 2) / T) * (8 * Real.exp 2 * L / π) := by ring
      rw [e]
      have hB : 0 ≤ 8 * Real.exp 2 * L / π := by positivity
      calc (x * (4 * x + 2) / T) * (8 * Real.exp 2 * L / π) ≤ 6 * (8 * Real.exp 2 * L / π) :=
            mul_le_mul_of_nonneg_right hA hB
        _ = 48 * Real.exp 2 * L / π := by ring
    have h1 := hP.trans hbound
    calc ‖(Chebyshev.psi N : ℂ) - (2 * π : ℂ)⁻¹ * Vc‖
        = η * ‖(Chebyshev.psi N : ℂ) - (2 * π : ℂ)⁻¹ * Vc‖ * L := by rw [mul_right_comm, hηL, one_mul]
      _ ≤ 48 * Real.exp 2 * L / π * L := mul_le_mul_of_nonneg_right h1 hL0.le
      _ = 48 * Real.exp 2 * L ^ 2 / π := by ring
  -- (2) o retângulo `[¼, c] × [−T, T]`
  have hbd : ∀ p ∈ Bordo ⟨1 / 4, -T⟩ ⟨c, T⟩, riemannZeta p ≠ 0 := by
    rintro p ⟨hpR, hside⟩
    have hre := (mem_reProdIm.mp hpR).1
    change p.re ∈ [[1 / 4, c]] at hre
    rw [uIcc_of_le (by linarith)] at hre
    change p.re = 1 / 4 ∨ p.re = c ∨ p.im = -T ∨ p.im = T at hside
    rcases hside with h | h | h | h
    · intro hz
      have hZ : p ∈ ATK.ZetaSimetria.Z := ⟨hz, by rw [h]; norm_num, by rw [h]; norm_num⟩
      have := ATK.ZeroClasses.LagariasHadamard.re_de_RH hRH hZ
      rw [h] at this
      norm_num at this
    · exact riemannZeta_ne_zero_of_one_le_re (by rw [h]; linarith)
    · have hp : p = (p.re : ℂ) + (-T : ℝ) * I := by
        rw [← h]
        exact (Complex.re_add_im p).symm
      rw [hp]
      exact (hgood p.re (by linarith [hre.1]) (by linarith [hre.2]) (-T) (Or.inr rfl)).1
    · have hp : p = (p.re : ℂ) + (T : ℝ) * I := by
        rw [← h]
        exact (Complex.re_add_im p).symm
      rw [hp]
      exact (hgood p.re (by linarith [hre.1]) (by linarith [hre.2]) T (Or.inl rfl)).1
  obtain ⟨S, hS, hbordo⟩ := bordo_explicita hx0 (b := 1 / 4) (c := c) (T := T) (by norm_num) (by norm_num)
    hc1 hT0 hbd
  set R : ℂ := ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) * px x u with hR
  set B : ℂ := ∫ u in (1 / 4 : ℝ)..c, Fx x ((u : ℂ) + ((-T : ℝ) : ℂ) * I) with hB
  set Tp : ℂ := ∫ u in (1 / 4 : ℝ)..c, Fx x ((u : ℂ) + (T : ℂ) * I) with hTp
  set Vb : ℂ := ∫ y in (-T)..T, Fx x (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I) with hVb
  have hunf : bordo (Fx x) ⟨1 / 4, -T⟩ ⟨c, T⟩ = B - Tp + I • Vc - I • Vb := rfl
  rw [hunf, smul_eq_mul, smul_eq_mul] at hbordo
  have h2 : I * (Vc - 2 * π * x + 2 * π * R) = Tp - B + I * Vb := by linear_combination hbordo
  have h3 : ‖Vc - 2 * π * x + 2 * π * R‖ ≤ ‖B‖ + ‖Tp‖ + ‖Vb‖ := by
    have h := congrArg norm h2
    rw [norm_mul, Complex.norm_I, one_mul] at h
    rw [h]
    have a1 := norm_add_le (Tp - B) (I * Vb)
    have a2 := norm_sub_le Tp B
    rw [norm_mul, Complex.norm_I, one_mul] at a1
    linarith
  have hπ : (2 * (π : ℂ)) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hcont : ‖(2 * π : ℂ)⁻¹ * Vc - x‖ ≤ ‖R‖ + (‖B‖ + ‖Tp‖ + ‖Vb‖) / (2 * π) := by
    have e : (2 * π : ℂ)⁻¹ * Vc - x = (2 * π : ℂ)⁻¹ * (Vc - 2 * π * x + 2 * π * R) - R := by
      field_simp
      ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_inv, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, inv_mul_eq_div]
    have := div_le_div_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith
  -- (3) a soma sobre os zeros
  have hRb : ‖R‖ ≤ 16 * C₃ * Real.sqrt x * L ^ 2 := by
    have hSZ : ∀ u ∈ S, u ∈ ATK.ZetaSimetria.Z ∧ |u.im| ≤ T := by
      intro u hu
      obtain ⟨huR, hz⟩ := (hS u).mp hu
      have hre := (mem_reProdIm.mp huR).1
      have him := (mem_reProdIm.mp huR).2
      change u.re ∈ [[1 / 4, c]] at hre
      change u.im ∈ [[-T, T]] at him
      rw [uIcc_of_le (by linarith)] at hre
      rw [uIcc_of_le (by linarith)] at him
      have hu1 : u.re < 1 := by
        by_contra h
        exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
      exact ⟨⟨hz, by linarith [hre.1], hu1⟩, abs_le.mpr ⟨him.1, him.2⟩⟩
    have hsum := hC₃ T (by linarith) S hSZ
    have hterm : ∀ u ∈ S, ‖(analyticOrderNatAt riemannZeta u : ℂ) * px x u‖ =
        Real.sqrt x * ((analyticOrderNatAt riemannZeta u : ℝ) / ‖u‖) := by
      intro u hu
      have hρ := ATK.ZeroClasses.LagariasHadamard.re_de_RH hRH (hSZ u hu).1
      unfold px
      rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hρ, hsqx, Complex.norm_natCast]
      ring
    have hlogT2 : (1 + Real.log T) ^ 2 ≤ 16 * L ^ 2 := by
      have h0 : 0 ≤ 1 + Real.log T := by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T); linarith
      have h1 : 1 + Real.log T ≤ 4 * L := by linarith
      calc (1 + Real.log T) ^ 2 ≤ (4 * L) ^ 2 := pow_le_pow_left₀ h0 h1 2
        _ = 16 * L ^ 2 := by ring
    calc ‖R‖ ≤ ∑ u ∈ S, ‖(analyticOrderNatAt riemannZeta u : ℂ) * px x u‖ := norm_sum_le _ _
      _ = Real.sqrt x * ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℝ) / ‖u‖ := by
          rw [Finset.sum_congr rfl hterm, Finset.mul_sum]
      _ ≤ Real.sqrt x * (C₃ * (1 + Real.log T) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt x * (C₃ * (16 * L ^ 2)) := by gcongr
      _ = 16 * C₃ * Real.sqrt x * L ^ 2 := by ring
  -- (4) os lados horizontais
  have hhor : ∀ t : ℝ, (t = T ∨ t = -T) → ‖∫ u in (1 / 4 : ℝ)..c, Fx x ((u : ℂ) + (t : ℂ) * I)‖ ≤
      18 * Real.exp 2 * C₁ * L ^ 2 := by
    intro t ht
    have htabs : |t| = T := by
      rcases ht with h | h <;> rw [h]
      · exact abs_of_pos hT0
      · rw [abs_neg]; exact abs_of_pos hT0
    have hbound : ∀ u ∈ Ι (1 / 4 : ℝ) c, ‖Fx x ((u : ℂ) + (t : ℂ) * I)‖ ≤
        Real.exp 2 * x * (C₁ * (3 * L) ^ 2) / T := by
      intro u hu
      rw [uIoc_of_le (by linarith)] at hu
      obtain ⟨hu1, hu2⟩ := hu
      rw [norm_Fx hx0]
      have hre : ((u : ℂ) + (t : ℂ) * I).re = u := by simp
      rw [hre]
      have h1 : x ^ u ≤ Real.exp 2 * x := by
        rw [← hxc]
        exact Real.rpow_le_rpow_of_exponent_le hx1 hu2
      have h2 := (hgood u (by linarith) (by linarith) t ht).2
      have h3 : C₁ * Real.log (2 + T) ^ 2 ≤ C₁ * (3 * L) ^ 2 := by
        have h0 : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hlogT 2) hC₁0
      have h23 := h2.trans h3
      have h4 : T ≤ ‖(u : ℂ) + (t : ℂ) * I‖ := by
        rw [← htabs]
        have := abs_im_le_norm ((u : ℂ) + (t : ℂ) * I)
        simpa using this
      have hlz := norm_nonneg (logDeriv riemannZeta ((u : ℂ) + (t : ℂ) * I))
      have hE0 : 0 ≤ Real.exp 2 * x := by positivity
      exact div_le_div₀ (mul_nonneg hE0 (hlz.trans h23)) (mul_le_mul h1 h23 hlz hE0) hT0 h4
    calc ‖∫ u in (1 / 4 : ℝ)..c, Fx x ((u : ℂ) + (t : ℂ) * I)‖
        ≤ Real.exp 2 * x * (C₁ * (3 * L) ^ 2) / T * |c - 1 / 4| :=
          intervalIntegral.norm_integral_le_of_norm_le_const hbound
      _ ≤ Real.exp 2 * x * (C₁ * (3 * L) ^ 2) / T * 2 := by
          gcongr
          rw [abs_of_pos (by linarith)]
          linarith
      _ ≤ Real.exp 2 * x * (C₁ * (3 * L) ^ 2) / x ^ 2 * 2 := by
          gcongr
      _ = 18 * Real.exp 2 * C₁ * L ^ 2 / x := by
          field_simp
          ring
      _ ≤ 18 * Real.exp 2 * C₁ * L ^ 2 := by
          apply div_le_self _ hx1
          positivity
  have hBb : ‖B‖ ≤ 18 * Real.exp 2 * C₁ * L ^ 2 := hhor (-T) (Or.inr rfl)
  have hTpb : ‖Tp‖ ≤ 18 * Real.exp 2 * C₁ * L ^ 2 := hhor T (Or.inl rfl)
  -- (5) o lado `Re s = ¼`
  have hvert : ‖Vb‖ ≤ 144 * C₂ * Real.sqrt x * L ^ 2 := by
    set K₀ : ℝ := Real.sqrt x * (C₂ * (3 * L)) * 8 with hK₀
    have hK₀0 : 0 ≤ K₀ := by positivity
    have hbound : ∀ y ∈ Ioc (-T) T, ‖Fx x (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        K₀ * (1 / (1 + |y|)) := by
      intro y hy
      have hyT : |y| ≤ T := abs_le.mpr ⟨hy.1.le, hy.2⟩
      rw [norm_Fx hx0]
      have hre : (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I).re = 1 / 4 := by simp
      rw [hre]
      have h1 : x ^ (1 / 4 : ℝ) ≤ Real.sqrt x := by
        rw [← hsqx]
        exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      have h2 := hC₂ y
      have h3 : C₂ * Real.log (2 + |y|) ≤ C₂ * (3 * L) := by
        have hly : Real.log (2 + |y|) ≤ 3 * L :=
          (Real.log_le_log (by positivity) (by linarith)).trans hlogT
        exact mul_le_mul_of_nonneg_left hly hC₂0
      have h23 := h2.trans h3
      have h4 : (1 + |y|) / 8 ≤ ‖((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I‖ := by
        have hr := abs_re_le_norm (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I)
        have hi := abs_im_le_norm (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I)
        have hre' : (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I).re = 1 / 4 := by simp
        have him' : (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I).im = y := by simp
        rw [hre', abs_of_pos (by norm_num)] at hr
        rw [him'] at hi
        linarith
      have h4p : 0 < (1 + |y|) / 8 := by positivity
      have hlz := norm_nonneg (logDeriv riemannZeta (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I))
      have hx14 : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx0.le _
      calc x ^ (1 / 4 : ℝ) * ‖logDeriv riemannZeta (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I)‖ /
            ‖((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I‖
          ≤ Real.sqrt x * (C₂ * (3 * L)) / ((1 + |y|) / 8) :=
            div_le_div₀ (mul_nonneg (Real.sqrt_nonneg _) (hlz.trans h23))
              (mul_le_mul h1 h23 hlz (Real.sqrt_nonneg _)) h4p h4
        _ = K₀ * (1 / (1 + |y|)) := by
            rw [hK₀]
            field_simp
    have hgi : IntervalIntegrable (fun y : ℝ => K₀ * (1 / (1 + |y|))) volume (-T) T :=
      (continuous_const.mul continuous_um_abs).intervalIntegrable _ _
    have hint := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ T)
      (ae_of_all _ hbound) hgi
    rw [intervalIntegral.integral_const_mul, integral_um_abs hT0.le] at hint
    calc ‖Vb‖ ≤ K₀ * (2 * Real.log (1 + T)) := hint
      _ ≤ K₀ * (2 * (3 * L)) := by gcongr
      _ = 144 * C₂ * Real.sqrt x * L ^ 2 := by rw [hK₀]; ring
  -- (6) a soma
  have htri : |Chebyshev.psi N - x| ≤ ‖(Chebyshev.psi N : ℂ) - (2 * π : ℂ)⁻¹ * Vc‖ +
      ‖(2 * π : ℂ)⁻¹ * Vc - x‖ := by
    have e : |Chebyshev.psi N - x| = ‖(Chebyshev.psi N : ℂ) - (x : ℂ)‖ := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [e]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hL2 : 0 ≤ L ^ 2 := by positivity
  have p1 : 48 * Real.exp 2 * L ^ 2 / π ≤ 128 * L ^ 2 := by
    rw [div_le_iff₀ Real.pi_pos]
    have a1 := mul_le_mul_of_nonneg_right he2 hL2
    have a2 := mul_le_mul_of_nonneg_left hpi.le hL2
    linarith
  have p2 : (‖B‖ + ‖Tp‖ + ‖Vb‖) / (2 * π) ≤ 48 * C₁ * L ^ 2 + 24 * C₂ * Real.sqrt x * L ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hq1 : 0 ≤ C₁ * L ^ 2 := by positivity
    have hq2 : 0 ≤ C₂ * Real.sqrt x * L ^ 2 := by positivity
    have a1 := mul_le_mul_of_nonneg_right he2 hq1
    have a2 := mul_le_mul_of_nonneg_left hpi.le hq1
    have a4 := mul_le_mul_of_nonneg_left hpi.le hq2
    linarith
  have p4 : L ^ 2 ≤ Real.sqrt x * L ^ 2 := by
    have := mul_le_mul_of_nonneg_right hsq1 hL2
    linarith
  have hq : (128 + 48 * C₁) * L ^ 2 ≤ (128 + 48 * C₁) * (Real.sqrt x * L ^ 2) :=
    mul_le_mul_of_nonneg_left p4 (by positivity)
  have hfin : |Chebyshev.psi N - x| ≤
      128 * L ^ 2 + (16 * C₃ * Real.sqrt x * L ^ 2 + (48 * C₁ * L ^ 2 + 24 * C₂ * Real.sqrt x * L ^ 2)) := by
    linarith
  calc |Chebyshev.psi N - x|
      ≤ 128 * L ^ 2 + (16 * C₃ * Real.sqrt x * L ^ 2 + (48 * C₁ * L ^ 2 + 24 * C₂ * Real.sqrt x * L ^ 2)) :=
        hfin
    _ ≤ (128 + 16 * C₃ + 48 * C₁ + 24 * C₂) * Real.sqrt x * L ^ 2 := by linarith

/-- **`ψ(x) = x + O(√x log² x)`**. -/
def PsiLog2 : Prop :=
  ∃ K x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → |Chebyshev.psi x - x| ≤ K * Real.sqrt x * Real.log x ^ 2

/-- **RH ⟹ `|ψ(x) − x| ≤ K √x log² x`** para `x ≥ 100`. -/
theorem psi_RH_log2 (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 100 ≤ x →
    |Chebyshev.psi x - x| ≤ K * Real.sqrt x * Real.log x ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := psi_RH_meio hRH
  refine ⟨8 * K + 1, by positivity, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  set N := ⌊x⌋₊ with hN
  have hN1 : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hN2 : x < N + 1 := Nat.lt_floor_add_one x
  have hxN : xN N = (N : ℝ) + 1 / 2 := rfl
  have hxN0 : 0 < xN N := xN_pos N
  have he4 : Real.exp 4 ≤ 99 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have h1 : Real.exp 1 ≤ 2.72 := by linarith
    calc Real.exp 1 ^ 4 ≤ 2.72 ^ 4 := by gcongr
      _ ≤ 99 := by norm_num
  have hL4 : 4 ≤ Real.log (xN N) := by
    rw [Real.le_log_iff_exp_le hxN0, hxN]
    linarith
  have h := hK N hL4
  have hlogx : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hxNx : xN N ≤ 2 * x := by rw [hxN]; linarith
  have hsq : Real.sqrt (xN N) ≤ 2 * Real.sqrt x := by
    have h1 : Real.sqrt (xN N) ≤ Real.sqrt (4 * x) := Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)] at h1
    exact h1
  have hlog : Real.log (xN N) ≤ 2 * Real.log x := by
    have h1 : Real.log (xN N) ≤ Real.log (2 * x) := Real.log_le_log hxN0 hxNx
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hlog0 : 0 ≤ Real.log (xN N) := by linarith
  have hlog2 : Real.log (xN N) ^ 2 ≤ 4 * Real.log x ^ 2 := by
    calc Real.log (xN N) ^ 2 ≤ (2 * Real.log x) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
      _ = 4 * Real.log x ^ 2 := by ring
  have hsx : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr (by linarith)
  have hl2 : 1 ≤ Real.log x ^ 2 := one_le_pow₀ hlogx
  rw [Chebyshev.psi_eq_psi_coe_floor x, ← hN]
  have hdist : |xN N - x| ≤ 1 / 2 := by
    rw [hxN, abs_le]
    constructor <;> linarith
  have htri : |Chebyshev.psi N - x| ≤ |Chebyshev.psi N - xN N| + |xN N - x| := by
    have := abs_sub_le (Chebyshev.psi N) (xN N) x
    linarith
  have hmain : K * Real.sqrt (xN N) * Real.log (xN N) ^ 2 ≤ 8 * K * Real.sqrt x * Real.log x ^ 2 := by
    have hs0 : 0 ≤ Real.sqrt (xN N) := Real.sqrt_nonneg _
    have hl0 : 0 ≤ Real.log (xN N) ^ 2 := by positivity
    calc K * Real.sqrt (xN N) * Real.log (xN N) ^ 2 ≤ K * (2 * Real.sqrt x) * (4 * Real.log x ^ 2) := by
          gcongr
      _ = 8 * K * Real.sqrt x * Real.log x ^ 2 := by ring
  have hone : (1 : ℝ) * 1 ≤ Real.sqrt x * Real.log x ^ 2 :=
    mul_le_mul hsx hl2 (by norm_num) (Real.sqrt_nonneg _)
  linarith

theorem psiLog3_of_psiLog2 (h : PsiLog2) : ATK.ZeroClasses.PsiRH.PsiLog3 := by
  obtain ⟨K, x₀, hK⟩ := h
  refine ⟨|K|, max x₀ 3, fun x hx => ?_⟩
  have hx3 : 3 ≤ x := (le_max_right _ _).trans hx
  have hlog : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hs := Real.sqrt_nonneg x
  have h23 : Real.log x ^ 2 ≤ Real.log x ^ 3 := by
    have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ Real.log x ^ 2)
    nlinarith
  calc |Chebyshev.psi x - x| ≤ K * Real.sqrt x * Real.log x ^ 2 := hK x ((le_max_left _ _).trans hx)
    _ ≤ |K| * Real.sqrt x * Real.log x ^ 2 := by
        gcongr
        exact le_abs_self K
    _ ≤ |K| * Real.sqrt x * Real.log x ^ 3 := by gcongr

/-- **RH ⟺ `ψ(x) = x + O(√x log² x)`** (von Koch). -/
theorem rh_iff_psiLog2 : RiemannHypothesis ↔ PsiLog2 := by
  constructor
  · intro hRH
    obtain ⟨K, _, hK⟩ := psi_RH_log2 hRH
    exact ⟨K, 100, hK⟩
  · intro h
    exact ATK.ZeroClasses.PsiRH.rh_iff_psiLog3.mpr (psiLog3_of_psiLog2 h)

/-! ## 2. `θ` e `π` -/

/-- Sob RH, `|θ(x) − x| ≤ K √x log² x` para `x ≥ 2`. -/
theorem theta_RH_log2 (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 2 ≤ x →
    |Chebyshev.theta x - x| ≤ K * Real.sqrt x * Real.log x ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := psi_RH_log2 hRH
  refine ⟨K + 2 + 40000, by positivity, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hl2 := log_dois_gt
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hs1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr (by linarith)
  have hge : (1 / 3 : ℝ) ≤ Real.sqrt x * Real.log x ^ 2 := by
    have h3 : (0.69 : ℝ) ^ 2 ≤ Real.log x ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have := mul_le_mul hs1 h3 (by norm_num) (Real.sqrt_nonneg x)
    norm_num at this
    linarith
  have hq0 : 0 ≤ Real.sqrt x * Real.log x ^ 2 := by linarith
  have h1 := Chebyshev.theta_le_psi x
  have hθ0 := Chebyshev.theta_nonneg x
  rcases le_or_gt 100 x with h100 | h100
  · have hψ := hK x h100
    have h2 := Chebyshev.psi_sub_theta_le (by linarith : (1 : ℝ) ≤ x)
    have hl1 : 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hx0]
      have := Real.exp_one_lt_d9
      linarith
    have h3 : 2 * Real.sqrt x * Real.log x ≤ 2 * (Real.sqrt x * Real.log x ^ 2) := by
      have : Real.log x ≤ Real.log x ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg x)
      linarith
    have e : K * Real.sqrt x * Real.log x ^ 2 = K * (Real.sqrt x * Real.log x ^ 2) := by ring
    rw [e] at hψ
    have e2 : (K + 2 + 40000) * Real.sqrt x * Real.log x ^ 2 =
        K * (Real.sqrt x * Real.log x ^ 2) + 2 * (Real.sqrt x * Real.log x ^ 2) +
          40000 * (Real.sqrt x * Real.log x ^ 2) := by ring
    rw [e2, abs_le]
    rw [abs_le] at hψ
    have : 0 ≤ 40000 * (Real.sqrt x * Real.log x ^ 2) := by positivity
    constructor <;> linarith
  · have hψ100 : Chebyshev.psi x ≤ 10000 := by
      have := Chebyshev.psi_mono h100.le
      have h2 := psi_le_sq 100
      norm_num at h2
      linarith
    have habs : |Chebyshev.theta x - x| ≤ 10100 := by
      rw [abs_le]
      constructor <;> linarith
    have e2 : (K + 2 + 40000) * Real.sqrt x * Real.log x ^ 2 =
        (K + 2) * (Real.sqrt x * Real.log x ^ 2) + 40000 * (Real.sqrt x * Real.log x ^ 2) := by ring
    have hB : 0 ≤ (K + 2) * (Real.sqrt x * Real.log x ^ 2) := mul_nonneg (by linarith) hq0
    rw [e2]
    linarith

/-- **`π(x) = Li(x) + O(√x log x)`**. -/
def PiLog : Prop :=
  ∃ K : ℝ, ∀ x : ℝ, 2 ≤ x → |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x| ≤ K * Real.sqrt x * Real.log x

/-- **Sob RH, `|π(x) − Li(x)| ≤ K √x log x`** para `x ≥ 2`. -/
theorem pi_RH_log (hRH : RiemannHypothesis) : PiLog := by
  obtain ⟨K, hK0, hK⟩ := theta_RH_log2 hRH
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h69 := log_dois_gt
  refine ⟨K + 3 * K + 5, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlx0 : 0 < Real.log x := by linarith
  have hs1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.mpr (by linarith)
  set L := Real.log x with hL
  have hb1 : |(Chebyshev.theta x - x) / L| ≤ K * Real.sqrt x * L := by
    rw [abs_div, abs_of_pos hlx0, div_le_iff₀ hlx0]
    calc |Chebyshev.theta x - x| ≤ K * Real.sqrt x * L ^ 2 := hK x hx
      _ = K * Real.sqrt x * L * L := by ring
  have hb2 : |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
      2 * K * Real.sqrt x := by
    have hle : ∀ t ∈ Ioc (2 : ℝ) x, ‖(Chebyshev.theta t - t) / (t * Real.log t ^ 2)‖ ≤
        K * t ^ ((1 / 2 : ℝ) - 1) := by
      intro t ht
      have ht2 : 2 ≤ t := ht.1.le
      have ht0 : (0 : ℝ) < t := by linarith
      have hlt0 : 0 < Real.log t := log_pos_of_ge ht2
      have hden : 0 < t * Real.log t ^ 2 := mul_pos ht0 (pow_pos hlt0 2)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hden, div_le_iff₀ hden]
      have hst' : t ^ ((1 / 2 : ℝ) - 1) * t = Real.sqrt t := by
        rw [← Real.rpow_add_one ht0.ne', Real.sqrt_eq_rpow]
        norm_num
      calc |Chebyshev.theta t - t| ≤ K * Real.sqrt t * Real.log t ^ 2 := hK t ht2
        _ = K * (t ^ ((1 / 2 : ℝ) - 1) * t) * Real.log t ^ 2 := by rw [hst']
        _ = K * t ^ ((1 / 2 : ℝ) - 1) * (t * Real.log t ^ 2) := by ring
    have hn := intervalIntegral.norm_integral_le_of_norm_le hx (Eventually.of_forall hle)
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < 1 / 2 - 1)).const_mul _)
    rw [Real.norm_eq_abs] at hn
    refine hn.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have hi := integral_rpow_le hx (by norm_num : (0 : ℝ) < 1 / 2)
    have hs : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
    rw [hs] at hi
    calc K * ∫ t in (2 : ℝ)..x, t ^ ((1 / 2 : ℝ) - 1) ≤ K * (Real.sqrt x / (1 / 2)) :=
          mul_le_mul_of_nonneg_left hi hK0
      _ = 2 * K * Real.sqrt x := by ring
  have hb3 : |2 / Real.log 2| ≤ 3 := by
    rw [abs_of_pos (by positivity), div_le_iff₀ hl2]
    linarith
  have hsum : |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x| ≤ K * Real.sqrt x * L + 2 * K * Real.sqrt x + 3 := by
    rw [pi_sub_Li hx]
    have a1 := abs_add_le ((Chebyshev.theta x - x) / L +
      ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) (2 / Real.log 2)
    have a2 := abs_add_le ((Chebyshev.theta x - x) / L)
      (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
    linarith
  have hL69 : (0.69 : ℝ) ≤ L := by linarith
  have hsL : (0.69 : ℝ) ≤ Real.sqrt x * L := by
    have := mul_le_mul hs1 hL69 (by norm_num) (Real.sqrt_nonneg x)
    linarith
  have hq : 0 ≤ K * Real.sqrt x := by positivity
  have h2 : 2 * K * Real.sqrt x ≤ 3 * K * Real.sqrt x * L := by
    have := mul_le_mul_of_nonneg_left hL69 hq
    nlinarith
  have h3 : (3 : ℝ) ≤ 5 * (Real.sqrt x * L) := by linarith
  calc |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x| ≤ K * Real.sqrt x * L + 2 * K * Real.sqrt x + 3 := hsum
    _ ≤ K * Real.sqrt x * L + 3 * K * Real.sqrt x * L + 5 * (Real.sqrt x * L) := by linarith
    _ = (K + 3 * K + 5) * Real.sqrt x * L := by ring

theorem piLog2_of_piLog (h : PiLog) : ATK.ZeroClasses.PiLiRH.PiLog2 := by
  obtain ⟨K, hK⟩ := h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨|K| / Real.log 2, fun x hx => ?_⟩
  have hlx : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlx0 : 0 < Real.log x := by linarith
  have hs := Real.sqrt_nonneg x
  have hLL : Real.log x ≤ Real.log x ^ 2 / Real.log 2 := by
    rw [le_div_iff₀ hl2]
    nlinarith
  calc |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x| ≤ K * Real.sqrt x * Real.log x := hK x hx
    _ ≤ |K| * Real.sqrt x * Real.log x := by
        gcongr
        exact le_abs_self K
    _ ≤ |K| * Real.sqrt x * (Real.log x ^ 2 / Real.log 2) := by gcongr
    _ = |K| / Real.log 2 * Real.sqrt x * Real.log x ^ 2 := by ring

/-- **RH ⟺ `π(x) = Li(x) + O(√x log x)`** (von Koch). -/
theorem rh_iff_piLog : RiemannHypothesis ↔ PiLog :=
  ⟨pi_RH_log, fun h => ATK.ZeroClasses.PiLiRH.rh_iff_piLog2.mpr (piLog2_of_piLog h)⟩

end ATK.ZeroClasses.Koch

#print axioms ATK.ZeroClasses.Koch.psi_RH_meio
#print axioms ATK.ZeroClasses.Koch.psi_RH_log2
#print axioms ATK.ZeroClasses.Koch.psiLog3_of_psiLog2
#print axioms ATK.ZeroClasses.Koch.rh_iff_psiLog2
#print axioms ATK.ZeroClasses.Koch.theta_RH_log2
#print axioms ATK.ZeroClasses.Koch.pi_RH_log
#print axioms ATK.ZeroClasses.Koch.piLog2_of_piLog
#print axioms ATK.ZeroClasses.Koch.rh_iff_piLog
