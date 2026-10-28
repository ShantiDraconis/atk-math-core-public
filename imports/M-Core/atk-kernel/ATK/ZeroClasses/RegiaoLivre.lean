import ATK.ZeroClasses.Landau

/-!
# A região livre de zeros de de la Vallée Poussin (rodada 37)

**Teorema (de la Vallée Poussin, 1899).** Existe `c > 0` tal que todo zero não trivial `ρ = β + iγ` de `ζ` com
`|γ| ≥ 2` satisfaz

  `β ≤ 1 − c / log |γ|`

(`regiao_livre`); equivalentemente, `ζ(s) ≠ 0` em `Re s > 1 − c/log|Im s|`, `|Im s| ≥ 2` (`zeta_ne_zero_regiao`).
A Mathlib tem só a não anulação em `Re s ≥ 1`. A prova é a clássica (Montgomery–Vaughan, Teorema 6.6), com o lema
de Landau da rodada 36 no lugar da fórmula de Hadamard:

1. **cotas de ζ perto de `Re s = 1`** (`cota_zeta_faixa`, `cota_zeta_real`) a partir da cota de Euler–Maclaurin
   da rodada 30, e **a cota inferior** `|ζ(σ + it)|⁴ ≥ (σ − 1)³/(512(6|t| + 12))` (`zeta_lb`) pelo produto
   `|ζ(σ)³ ζ(σ + it)⁴ ζ(σ + 2it)| ≥ 1` da Mathlib (`prod341`);
2. **o lema de Landau aplicado a ζ** no disco `‖z − (σ + it)‖ ≤ ½` (`zeta_local`): todos os termos
   `Re m_ρ/(s − ρ)` são `≥ 0`, logo `−Re ζ′/ζ(σ + it) ≤ 32(2 log|t| + log(1/(σ − 1)) + 7)`
   (`re_logDeriv_local`), e com um zero `ρ = β + it` a `1/8` do centro, `≤ −1/(σ − β) + …`
   (`re_logDeriv_local_zero`);
3. **o polo** (`polo`): `−Re ζ′/ζ(σ) ≤ 1/(σ − 1) + C` em `1 < σ ≤ 2`, por `G(s) = 2ξ(s)/(sΓℝ(s)) = (s − 1)ζ(s)`
   e compacidade;
4. **a desigualdade 3-4-1** (`tres_quatro_um`): `3 Re(−ζ′/ζ)(σ) + 4 Re(−ζ′/ζ)(σ + it) + Re(−ζ′/ζ)(σ + 2it) ≥ 0`,
   termo a termo na série de von Mangoldt (`3 + 4 cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0`, `termo341`);
5. **a montagem** com `σ = 1 + 1/(962 log|γ|)` (`regiao_livre_grande`, `c = 1/6734` para `|γ|` grande) e a
   finitude dos zeros num compacto para o resto (`regiao_livre`).

Classificação (rodada 37): **parcial** — a primeira região livre de zeros à esquerda de `Re s = 1` no kernel.
Ela não chega perto de `Re s = ½`: RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.RegiaoLivre

open ATK.ZeroClasses.Landau (landau)

/-! ## 1. Cotas de ζ perto da reta `Re s = 1` -/

/-- `‖ζ(s)‖ ≤ 3|Im s| + 12` para `½ ≤ Re s ≤ 3` e `|Im s| ≥ 1`. -/
theorem cota_zeta_faixa {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h3 : s.re ≤ 3) (him : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 3 * |s.im| + 12 := by
  have hs1 : s ≠ 1 := by
    rintro rfl
    norm_num at him
  have hn1 : |s.im| ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    simpa using h
  have hpos : 0 < ‖s - 1‖ := by linarith
  have hsn : ‖s‖ ≤ 3 + |s.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos (by linarith : 0 < s.re)] at h
    linarith
  have hc := ATK.ZeroClasses.Jensen.cota_zeta h1 hs1
  rw [norm_mul] at hc
  have hz : ‖riemannZeta s‖ ≤ 1 / ‖s - 1‖ + (1 / 2 + 3 * ‖s‖) := by
    rw [div_add' _ _ _ hpos.ne', le_div_iff₀ hpos]
    nlinarith
  have h1' : 1 / ‖s - 1‖ ≤ 1 := by rw [div_le_one hpos]; linarith
  linarith

/-- `‖ζ(σ)‖ ≤ 8/(σ − 1)` em `1 < σ ≤ 2`. -/
theorem cota_zeta_real {σ : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) : ‖riemannZeta σ‖ ≤ 8 / (σ - 1) := by
  have hs1 : (σ : ℂ) ≠ 1 := by exact_mod_cast h1.ne'
  have hc := ATK.ZeroClasses.Jensen.cota_zeta (s := σ) (by rw [Complex.ofReal_re]; linarith) hs1
  rw [norm_mul] at hc
  have hn : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have hsn : ‖(σ : ℂ)‖ = σ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [hn, hsn] at hc
  rw [le_div_iff₀ (by linarith)]
  have : (σ - 1) * (1 / 2 + 3 * σ) ≤ 1 * (13 / 2) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by norm_num)
  nlinarith

/-- **O produto 3-4-1** (Mathlib, `norm_LFunction_product_ge_one` com o caráter trivial módulo 1):
`‖ζ(1 + x)‖³ ‖ζ(1 + x + iy)‖⁴ ‖ζ(1 + x + 2iy)‖ ≥ 1` para `x > 0`. -/
theorem prod341 {x : ℝ} (hx : 0 < x) (y : ℝ) :
    1 ≤ ‖riemannZeta (1 + x)‖ ^ 3 * ‖riemannZeta (1 + x + I * y)‖ ^ 4 *
      ‖riemannZeta (1 + x + 2 * I * y)‖ := by
  have h := DirichletCharacter.norm_LFunction_product_ge_one (1 : DirichletCharacter ℂ 1) hx y
  simp only [DirichletCharacter.LFunctionTrivChar, DirichletCharacter.LFunction_modOne_eq, norm_mul,
    norm_pow] at h
  exact h

/-- **Cota inferior perto de `Re s = 1`**: `‖ζ(σ + it)‖⁴ ≥ (σ − 1)³/(512(6|t| + 12))` em `1 < σ ≤ 2`, `|t| ≥ 1`. -/
theorem zeta_lb {σ t : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) (ht : 1 ≤ |t|) :
    (σ - 1) ^ 3 / (512 * (6 * |t| + 12)) ≤ ‖riemannZeta (σ + t * I)‖ ^ 4 := by
  have hp := prod341 (x := σ - 1) (by linarith) t
  have e0 : (1 + ((σ - 1 : ℝ) : ℂ)) = (σ : ℂ) := by push_cast; ring
  have e1 : (1 + ((σ - 1 : ℝ) : ℂ) + I * t) = σ + t * I := by push_cast; ring
  have e2 : (1 + ((σ - 1 : ℝ) : ℂ) + 2 * I * t) = σ + ((2 * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [e1, e2, e0] at hp
  have hA := cota_zeta_real h1 h2
  have hB : ‖riemannZeta (σ + ((2 * t : ℝ) : ℂ) * I)‖ ≤ 6 * |t| + 12 := by
    have him : ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I).im = 2 * t := by simp
    have hre : ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I).re = σ := by simp
    have h2t : |2 * t| = 2 * |t| := by rw [abs_mul, abs_two]
    have := cota_zeta_faixa (s := σ + ((2 * t : ℝ) : ℂ) * I) (by rw [hre]; linarith)
      (by rw [hre]; linarith) (by rw [him, h2t]; linarith)
    rw [him, h2t] at this
    linarith
  set a := ‖riemannZeta σ‖
  set b := ‖riemannZeta (σ + t * I)‖
  set c := ‖riemannZeta (σ + ((2 * t : ℝ) : ℂ) * I)‖
  have ha0 : 0 ≤ a := norm_nonneg _
  have hc0 : 0 ≤ c := norm_nonneg _
  have hs : 0 < σ - 1 := by linarith
  have hs' : σ - 1 ≠ 0 := hs.ne'
  have hpos : 0 < 512 * (6 * |t| + 12) := by positivity
  have key : 1 ≤ (8 / (σ - 1)) ^ 3 * b ^ 4 * (6 * |t| + 12) := by
    calc 1 ≤ a ^ 3 * b ^ 4 * c := hp
      _ ≤ (8 / (σ - 1)) ^ 3 * b ^ 4 * (6 * |t| + 12) := by gcongr
  have e : (8 / (σ - 1)) ^ 3 * b ^ 4 * (6 * |t| + 12) =
      b ^ 4 * (512 * (6 * |t| + 12)) / (σ - 1) ^ 3 := by
    field_simp
    ring
  rw [e, le_div_iff₀ (by positivity)] at key
  rw [div_le_iff₀ hpos]
  linarith

/-! ## 2. O lema de Landau aplicado a ζ -/

/-- **Landau para ζ**: no disco `‖z − (σ + it)‖ ≤ ½` (`1 < σ ≤ 2`, `|t| ≥ 2`), `ζ′/ζ(σ + it)` é a soma sobre os
zeros a distância `≤ 1/8` mais um erro `≤ 32(2 log|t| + log(1/(σ − 1)) + 7)`. -/
theorem zeta_local {σ t : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ∃ S : Finset ℂ, (∀ u ∈ S, u ∈ closedBall ((σ : ℂ) + t * I) (1 / 8) ∧ riemannZeta u = 0) ∧
      (∀ u ∈ closedBall ((σ : ℂ) + t * I) (1 / 8), riemannZeta u = 0 → u ∈ S) ∧
      ‖logDeriv riemannZeta (σ + t * I) -
          ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (σ + t * I - u)‖ ≤
        32 * (2 * Real.log |t| + Real.log (1 / (σ - 1)) + 7) := by
  set z₀ : ℂ := σ + t * I with hz₀
  have hre0 : z₀.re = σ := by simp [hz₀]
  have him0 : z₀.im = t := by simp [hz₀]
  have coord : ∀ z ∈ closedBall z₀ (1 / 2), |z.re - σ| ≤ 1 / 2 ∧ |z.im - t| ≤ 1 / 2 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    refine ⟨?_, ?_⟩
    · have := Complex.abs_re_le_norm (z - z₀)
      rw [sub_re, hre0] at this
      linarith
    · have := Complex.abs_im_le_norm (z - z₀)
      rw [sub_im, him0] at this
      linarith
  have hbound : ∀ z ∈ closedBall z₀ (1 / 2), ‖riemannZeta z‖ ≤ 3 * |t| + 14 := by
    intro z hz
    obtain ⟨hr, hi⟩ := coord z hz
    have hi1 : |t| - 1 / 2 ≤ |z.im| := by
      have := abs_sub_abs_le_abs_sub t z.im
      rw [abs_sub_comm] at this
      linarith
    have hi2 : |z.im| ≤ |t| + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub z.im t
      linarith
    have := cota_zeta_faixa (s := z) (by linarith [(abs_le.mp hr).1]) (by linarith [(abs_le.mp hr).2])
      (by linarith)
    linarith
  have hana : AnalyticOnNhd ℂ riemannZeta (closedBall z₀ (1 / 2)) := by
    refine analyticOn_riemannZeta.mono fun z hz => ?_
    rw [Set.mem_compl_singleton_iff]
    rintro rfl
    obtain ⟨_, hi⟩ := coord 1 hz
    rw [one_im, zero_sub, abs_neg] at hi
    linarith
  have hz0 : riemannZeta z₀ ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hre0]; linarith)
  set a := ‖riemannZeta z₀‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr hz0
  have haU : a ≤ 3 * |t| + 12 := by
    have := cota_zeta_faixa (s := z₀) (by rw [hre0]; linarith) (by rw [hre0]; linarith)
      (by rw [him0]; linarith)
    rwa [him0] at this
  set M := (3 * |t| + 14) / a with hM
  have hM1 : 1 ≤ M := by rw [hM, le_div_iff₀ ha0]; linarith
  have hb : ∀ z ∈ closedBall z₀ (1 / 2), ‖riemannZeta z‖ ≤ M * a := by
    intro z hz
    rw [hM, div_mul_cancel₀ _ ha0.ne']
    exact hbound z hz
  obtain ⟨S, hS1, hS2, hS3⟩ := landau (f := riemannZeta) (z₀ := z₀) (R := 1 / 2) (M := M) (by norm_num)
    hM1 hana hz0 hb
  have h8 : (1 / 2 : ℝ) / 4 = 1 / 8 := by norm_num
  rw [h8] at hS1 hS2
  refine ⟨S, hS1, hS2, hS3.trans ?_⟩
  have hlogM : Real.log M + 1 ≤ 2 * Real.log |t| + Real.log (1 / (σ - 1)) + 7 := by
    have ht0 : 0 < |t| := by linarith
    have hs : 0 < σ - 1 := by linarith
    have hL : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
    have hl1 : 0 ≤ Real.log (1 / (σ - 1)) := Real.log_nonneg (by rw [le_div_iff₀ hs]; linarith)
    have hlinv : Real.log (1 / (σ - 1)) = -Real.log (σ - 1) := by rw [one_div, Real.log_inv]
    have hl2 := Real.log_two_lt_d9
    have hlog16 : Real.log (16 * |t|) = 4 * Real.log 2 + Real.log |t| := by
      rw [Real.log_mul (by norm_num) ht0.ne', show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      push_cast
      ring
    have hA : Real.log (3 * |t| + 14) ≤ 4 * Real.log 2 + Real.log |t| := by
      rw [← hlog16]
      exact Real.log_le_log (by positivity) (by linarith)
    have hB : Real.log (6 * |t| + 12) ≤ 4 * Real.log 2 + Real.log |t| := by
      rw [← hlog16]
      exact Real.log_le_log (by positivity) (by linarith)
    have hlb' : (σ - 1) ^ 3 / (512 * (6 * |t| + 12)) ≤ a ^ 4 := zeta_lb h1 h2 (by linarith)
    have hpos : 0 < (σ - 1) ^ 3 / (512 * (6 * |t| + 12)) := by positivity
    have hlog := Real.log_le_log hpos hlb'
    rw [Real.log_pow, Real.log_div (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by norm_num) (by positivity), show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow] at hlog
    push_cast at hlog
    have hMdef : Real.log M = Real.log (3 * |t| + 14) - Real.log a := by
      rw [hM, Real.log_div (by positivity) ha0.ne']
    rw [hMdef]
    linarith
  have : 16 * (Real.log M + 1) / (1 / 2) = 32 * (Real.log M + 1) := by ring
  rw [this]
  linarith

/-- Os termos da soma de Landau têm parte real `≥ 0` à direita dos zeros. -/
theorem re_termo_nonneg {z u : ℂ} (m : ℕ) (h : u.re < z.re) : 0 ≤ ((m : ℂ) / (z - u)).re := by
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero, Complex.sub_re]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg m) (by linarith)) (Complex.normSq_nonneg _)

/-- Um zero de ζ tem `Re < 1`. -/
theorem re_lt_um {u : ℂ} (hz : riemannZeta u = 0) : u.re < 1 := by
  by_contra hc
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hc) hz

/-- **A cota local**: `−Re ζ′/ζ(σ + it) ≤ 32(2 log|t| + log(1/(σ − 1)) + 7)` em `1 < σ ≤ 2`, `|t| ≥ 2`. -/
theorem re_logDeriv_local {σ t : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    -(logDeriv riemannZeta (σ + t * I)).re ≤ 32 * (2 * Real.log |t| + Real.log (1 / (σ - 1)) + 7) := by
  obtain ⟨S, hS1, _, hS3⟩ := zeta_local h1 h2 ht
  have hre0 : ((σ : ℂ) + t * I).re = σ := by simp
  have hsum : 0 ≤ (∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (σ + t * I - u)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun u hu => re_termo_nonneg _ ?_
    have := re_lt_um (hS1 u hu).2
    rw [hre0]
    linarith
  have hD := Complex.abs_re_le_norm (logDeriv riemannZeta (σ + t * I) -
    ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (σ + t * I - u))
  rw [Complex.sub_re] at hD
  linarith [(abs_le.mp hD).1]

/-- **A cota local com um zero**: se `ρ = β + iγ ∈ Z`, `|γ| ≥ 2` e `σ − β ≤ 1/8`, então
`−Re ζ′/ζ(σ + iγ) ≤ −1/(σ − β) + 32(2 log|γ| + log(1/(σ − 1)) + 7)`. -/
theorem re_logDeriv_local_zero {σ : ℝ} {ρ : ℂ} (hρ : ρ ∈ ATK.ZetaSimetria.Z) (h1 : 1 < σ) (h2 : σ ≤ 2)
    (ht : 2 ≤ |ρ.im|) (hd : σ - ρ.re ≤ 1 / 8) :
    -(logDeriv riemannZeta (σ + ρ.im * I)).re ≤
      -(1 / (σ - ρ.re)) + 32 * (2 * Real.log |ρ.im| + Real.log (1 / (σ - 1)) + 7) := by
  obtain ⟨S, hS1, hS2, hS3⟩ := zeta_local h1 h2 ht
  have hre0 : ((σ : ℂ) + ρ.im * I).re = σ := by simp
  have hβ : ρ.re < 1 := hρ.2.2
  have hdpos : 0 < σ - ρ.re := by linarith
  have hdiff : (σ : ℂ) + ρ.im * I - ρ = ((σ - ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  have hρS : ρ ∈ S := by
    refine hS2 ρ ?_ hρ.1
    rw [mem_closedBall, dist_comm, dist_eq_norm, hdiff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hdpos]
    exact hd
  have hnn : ∀ u ∈ S, 0 ≤ ((analyticOrderNatAt riemannZeta u : ℂ) / (σ + ρ.im * I - u)).re := by
    intro u hu
    refine re_termo_nonneg _ ?_
    have := re_lt_um (hS1 u hu).2
    rw [hre0]
    linarith
  have hterm : 1 / (σ - ρ.re) ≤ ((analyticOrderNatAt riemannZeta ρ : ℂ) / (σ + ρ.im * I - ρ)).re := by
    rw [hdiff, show (analyticOrderNatAt riemannZeta ρ : ℂ) = ((analyticOrderNatAt riemannZeta ρ : ℝ) : ℂ) by
      push_cast; rfl, ← Complex.ofReal_div, Complex.ofReal_re]
    have hm : (1 : ℝ) ≤ analyticOrderNatAt riemannZeta ρ := by
      exact_mod_cast ATK.ZeroClasses.Expoente.ordem_pos hρ
    exact div_le_div_of_nonneg_right hm hdpos.le
  have hsum : 1 / (σ - ρ.re) ≤
      (∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (σ + ρ.im * I - u)).re := by
    rw [Complex.re_sum]
    exact hterm.trans (Finset.single_le_sum hnn hρS)
  have hD := Complex.abs_re_le_norm (logDeriv riemannZeta (σ + ρ.im * I) -
    ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (σ + ρ.im * I - u))
  rw [Complex.sub_re] at hD
  linarith [(abs_le.mp hD).1]

/-! ## 3. O polo em `s = 1` -/

/-- `G(s) = 2ξ(s)/(s Γℝ(s))`: holomorfa em `Re s > 0`, igual a `(s − 1)ζ(s)` fora de `s = 1`, `G(1) = 1`. -/
noncomputable def Gp (s : ℂ) : ℂ := 2 * ATK.BaseRiemannXi.riemannXi s * (Gammaℝ s)⁻¹ / s

theorem Gp_diff {s : ℂ} (hs : s ≠ 0) : DifferentiableAt ℂ Gp s :=
  (((differentiableAt_const 2).mul (ATK.BaseRiemannXi.differentiable_riemannXi s)).mul
    (differentiable_Gammaℝ_inv s)).div differentiableAt_id hs

theorem Gp_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) : Gp s = (s - 1) * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  unfold Gp
  rw [ATK.BaseRiemannXi.riemannXi_eq_zeta hs0 hs1 hG]
  field_simp

theorem Gp_ne_zero {σ : ℝ} (h : 1 ≤ σ) : Gp σ ≠ 0 := by
  have hre : 1 ≤ (σ : ℂ).re := by simpa using h
  have h0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : σ ≠ 0)
  unfold Gp
  exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
    (ATK.BaseRiemannXi.riemannXi_ne_zero_of_one_le_re hre))
    (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos (by linarith)))) h0

/-- `ζ′/ζ(s) = G′/G(s) − 1/(s − 1)` em `Re s > 1`. -/
theorem logDeriv_zeta_Gp {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannZeta s = logDeriv Gp s - 1 / (s - 1) := by
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have hU : IsOpen {z : ℂ | 0 < z.re ∧ z ≠ 1} :=
    (isOpen_lt continuous_const continuous_re).inter isOpen_ne
  have hev : Gp =ᶠ[𝓝 s] fun z => (z - 1) * riemannZeta z := by
    filter_upwards [hU.mem_nhds ⟨by linarith, hs1⟩] with z hz
    exact Gp_eq hz.1 hz.2
  rw [(logDeriv_congr_nhds hev).self_of_nhds]
  change logDeriv riemannZeta s = logDeriv ((fun z : ℂ => z - 1) * riemannZeta) s - 1 / (s - 1)
  rw [logDeriv_mul (f := fun z : ℂ => z - 1) (g := riemannZeta) s (sub_ne_zero.mpr hs1)
      (riemannZeta_ne_zero_of_one_le_re hs.le) (differentiableAt_id.sub_const 1)
      (differentiableAt_riemannZeta hs1)]
  have : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
    rw [logDeriv_apply, deriv_sub_const, deriv_id'']
  rw [this]
  ring

/-- **O polo**: existe `C ≥ 0` com `−Re ζ′/ζ(σ) ≤ 1/(σ − 1) + C` em `1 < σ ≤ 2`. -/
theorem polo : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
    (-(logDeriv riemannZeta σ)).re ≤ 1 / (σ - 1) + C := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hGd : DifferentiableOn ℂ Gp {z : ℂ | 0 < z.re} := fun z hz =>
    (Gp_diff (by rintro rfl; simp at hz)).differentiableWithinAt
  have hdd : DifferentiableOn ℂ (deriv Gp) {z : ℂ | 0 < z.re} := hGd.deriv hU
  have hmaps : MapsTo (fun σ : ℝ => (σ : ℂ)) (Icc 1 2) {z : ℂ | 0 < z.re} := fun σ hσ => by
    simp only [Set.mem_ofPred_eq, ofReal_re]
    linarith [hσ.1]
  have hcont : ContinuousOn (fun σ : ℝ => deriv Gp σ / Gp σ) (Icc 1 2) :=
    ContinuousOn.div (hdd.continuousOn.comp Complex.continuous_ofReal.continuousOn hmaps)
      (hGd.continuousOn.comp Complex.continuous_ofReal.continuousOn hmaps)
      (fun σ hσ => Gp_ne_zero hσ.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun σ h1 h2 => ?_⟩
  have hs : 1 < (σ : ℂ).re := by simpa using h1
  rw [logDeriv_zeta_Gp hs]
  have hb : ‖logDeriv Gp σ‖ ≤ C := by
    rw [logDeriv_apply]
    exact hC σ ⟨h1.le, h2⟩
  have hre : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
    rw [show (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_one,
      ← Complex.ofReal_div, Complex.ofReal_re]
  rw [neg_sub, Complex.sub_re, hre]
  have h3 := (abs_le.mp (Complex.abs_re_le_norm (logDeriv Gp σ))).1
  linarith [le_max_left C 0]

/-! ## 4. A desigualdade 3-4-1 -/

/-- **Termo a termo**: `3 Re a_n(σ) + 4 Re a_n(σ + it) + Re a_n(σ + 2it) ≥ 0` para `a_n(s) = Λ(n)/n^s`. -/
theorem termo341 (n : ℕ) (σ t : ℝ) :
    0 ≤ 3 * (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) σ n).re +
      4 * (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ + t * I) n).re +
      (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ + ((2 * t : ℝ) : ℂ) * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  set w : ℂ := (n : ℂ) ^ ((t : ℂ) * I) with hwdef
  have hw : ‖w‖ = 1 := by
    rw [hwdef, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
    simp
  have e1 : (n : ℂ) ^ ((σ : ℂ) + t * I) = (n : ℂ) ^ (σ : ℂ) * w := Complex.cpow_add _ _ hn0
  have e2 : (n : ℂ) ^ ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I) = (n : ℂ) ^ (σ : ℂ) * w ^ 2 := by
    rw [Complex.cpow_add _ _ hn0]
    congr 1
    rw [show ((2 * t : ℝ) : ℂ) * I = (2 : ℕ) * ((t : ℂ) * I) by push_cast; ring, Complex.cpow_nat_mul]
  set c : ℝ := ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ with hcdef
  have hc : 0 ≤ c := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  have ec : (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ (σ : ℂ) = (c : ℂ) := by
    rw [hcdef, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg (α := ℝ) n),
      Complex.ofReal_natCast]
  rw [e1, e2, ← div_div, ← div_div, ec]
  set v : ℂ := w⁻¹ with hvdef
  have hv : v.re ^ 2 + v.im ^ 2 = 1 := by
    have hvn : ‖v‖ = 1 := by rw [hvdef, norm_inv, hw, inv_one]
    have h := Complex.sq_norm v
    rw [hvn, Complex.normSq_apply] at h
    nlinarith
  have q1 : ((c : ℂ) / w).re = c * v.re := by
    rw [div_eq_mul_inv, ← hvdef, Complex.re_ofReal_mul]
  have q2 : ((c : ℂ) / w ^ 2).re = c * (v.re * v.re - v.im * v.im) := by
    rw [div_eq_mul_inv, ← inv_pow, ← hvdef, Complex.re_ofReal_mul, pow_two, Complex.mul_re]
  rw [q1, q2, Complex.ofReal_re]
  have key : 3 * c + 4 * (c * v.re) + c * (v.re * v.re - v.im * v.im) = 2 * c * (1 + v.re) ^ 2 := by
    linear_combination (-c) * hv
  rw [key]
  positivity

/-- **A desigualdade 3-4-1** para a derivada logarítmica: em `σ > 1`,
`3 Re(−ζ′/ζ)(σ) + 4 Re(−ζ′/ζ)(σ + it) + Re(−ζ′/ζ)(σ + 2it) ≥ 0`. -/
theorem tres_quatro_um {σ : ℝ} (h1 : 1 < σ) (t : ℝ) :
    0 ≤ 3 * (-(logDeriv riemannZeta σ)).re + 4 * (-(logDeriv riemannZeta (σ + t * I))).re +
      (-(logDeriv riemannZeta (σ + ((2 * t : ℝ) : ℂ) * I))).re := by
  have hre : ∀ s : ℂ, 1 < s.re → (-(logDeriv riemannZeta s)).re =
      ∑' n, (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n).re := by
    intro s hs
    rw [logDeriv_apply, ← neg_div, ← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
      LSeries, Complex.re_tsum (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)]
  have hs0 : 1 < (σ : ℂ).re := by simpa using h1
  have hs1 : 1 < ((σ : ℂ) + t * I).re := by simpa using h1
  have hs2 : 1 < ((σ : ℂ) + ((2 * t : ℝ) : ℂ) * I).re := by simpa using h1
  have S0 := (Complex.hasSum_re (ArithmeticFunction.LSeriesSummable_vonMangoldt hs0).hasSum).summable
  have S1 := (Complex.hasSum_re (ArithmeticFunction.LSeriesSummable_vonMangoldt hs1).hasSum).summable
  have S2 := (Complex.hasSum_re (ArithmeticFunction.LSeriesSummable_vonMangoldt hs2).hasSum).summable
  rw [hre _ hs0, hre _ hs1, hre _ hs2, ← tsum_mul_left, ← tsum_mul_left,
    ← (S0.mul_left 3).tsum_add (S1.mul_left 4), ← ((S0.mul_left 3).add (S1.mul_left 4)).tsum_add S2]
  exact tsum_nonneg fun n => termo341 n σ t

/-! ## 5. A montagem -/

/-- **A região livre de zeros para `|γ|` grande**: com `c = 1/6734`, existe `T₀ ≥ 2` tal que todo zero não trivial
com `|γ| ≥ T₀` tem `β ≤ 1 − c/log|γ|`. -/
theorem regiao_livre_grande : ∃ c > 0, ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ ρ ∈ ATK.ZetaSimetria.Z, T₀ ≤ |ρ.im| →
    ρ.re ≤ 1 - c / Real.log |ρ.im| := by
  obtain ⟨C, hC0, hC⟩ := polo
  set L₀ : ℝ := 3 * C + 32 * (5 * Real.log 962 + 37) with hL₀
  have hl962 : 0 ≤ Real.log 962 := Real.log_nonneg (by norm_num)
  have hL₀1 : 1 ≤ L₀ := by rw [hL₀]; nlinarith
  refine ⟨1 / 6734, by norm_num, Real.exp L₀, ?_, fun ρ hρ hT => ?_⟩
  · linarith [Real.add_one_le_exp L₀]
  set γ := ρ.im with hγ
  set β := ρ.re with hβdef
  have hT2 : 2 ≤ |γ| := by linarith [Real.add_one_le_exp L₀]
  have hγ0 : 0 < |γ| := by linarith
  set L := Real.log |γ| with hLdef
  have hLL₀ : L₀ ≤ L := by
    rw [hLdef, ← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos _) hT
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hβ1 : β < 1 := hρ.2.2
  have hgoal : (1 / 6734 : ℝ) ≤ (1 - β) * L → β ≤ 1 - 1 / 6734 / L := by
    intro h
    have : 1 / 6734 / L ≤ 1 - β := by rw [div_le_iff₀ hLpos]; linarith
    linarith
  apply hgoal
  by_cases hβ : β ≤ 15 / 16
  · nlinarith
  replace hβ := not_le.mp hβ
  set σ : ℝ := 1 + 1 / (962 * L) with hσdef
  have hinv : 0 < 1 / (962 * L) := by positivity
  have hinv1 : 1 / (962 * L) ≤ 1 / 962 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 2 := by linarith
  have hd : σ - β ≤ 1 / 8 := by linarith
  have hdpos : 0 < σ - β := by linarith
  have A1 := hC σ hσ1 hσ2
  have A2 := re_logDeriv_local_zero hρ hσ1 hσ2 hT2 hd
  rw [← hγ, ← hβdef, ← hLdef] at A2
  have h2γ : 2 ≤ |2 * γ| := by rw [abs_mul, abs_two]; linarith
  have A3 := re_logDeriv_local hσ1 hσ2 h2γ
  have P := tres_quatro_um hσ1 γ
  have e1 : 1 / (σ - 1) = 962 * L := by
    rw [hσdef, add_sub_cancel_left, one_div_one_div]
  have e2 : Real.log (1 / (σ - 1)) ≤ L + Real.log 962 := by
    rw [e1, Real.log_mul (by norm_num) hLpos.ne']
    linarith [Real.log_le_sub_one_of_pos hLpos]
  have e3 : Real.log |2 * γ| = Real.log 2 + L := by
    rw [abs_mul, abs_two, Real.log_mul (by norm_num) hγ0.ne']
  have hl2 := Real.log_two_lt_d9
  rw [e1] at A1
  rw [e3] at A3
  simp only [Complex.neg_re] at A1 P
  set X := 1 / (σ - β) with hX
  have h4 : 4 * X ≤ 3367 * L := by linarith
  have hXd : X * (σ - β) = 1 := by rw [hX]; field_simp
  have key : 4 ≤ 3367 * L * (σ - β) := by
    have := mul_le_mul_of_nonneg_right h4 hdpos.le
    linarith
  have hexp : 3367 * L * (σ - β) = 3367 / 962 + 3367 * ((1 - β) * L) := by
    rw [hσdef]
    field_simp
    ring
  rw [hexp] at key
  linarith

/-- **A região livre de zeros de de la Vallée Poussin**: existe `c > 0` tal que todo zero não trivial `ρ` com
`|Im ρ| ≥ 2` satisfaz `Re ρ ≤ 1 − c/log|Im ρ|`. -/
theorem regiao_livre : ∃ c > 0, ∀ ρ ∈ ATK.ZetaSimetria.Z, 2 ≤ |ρ.im| →
    ρ.re ≤ 1 - c / Real.log |ρ.im| := by
  obtain ⟨c₁, hc₁, T₀, hT₀, h₁⟩ := regiao_livre_grande
  set F : Set ℂ := closedBall (0 : ℂ) (T₀ + 1) ∩ riemannZetaZeros ∩ ATK.ZetaSimetria.Z with hF
  have hfin : F.Finite :=
    ((isCompact_closedBall (0 : ℂ) (T₀ + 1)).inter_riemannZetaZeros_finite).subset inter_subset_left
  obtain ⟨η, hη, hηb⟩ : ∃ η > 0, ∀ ρ ∈ F, ρ.re ≤ 1 - η := by
    rcases F.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun ρ hρ => by rw [he] at hρ; exact absurd hρ (Set.notMem_empty ρ)⟩
    · obtain ⟨ρ₀, hρ₀, hmax⟩ := Set.exists_max_image F (fun ρ => ρ.re) hfin hne
      refine ⟨1 - ρ₀.re, by linarith [hρ₀.2.2.2], fun ρ hρ => ?_⟩
      have := hmax ρ hρ
      linarith
  refine ⟨min c₁ (η * Real.log 2), lt_min hc₁ (mul_pos hη (Real.log_pos (by norm_num))),
    fun ρ hρ h2 => ?_⟩
  have hL : Real.log 2 ≤ Real.log |ρ.im| := Real.log_le_log (by norm_num) h2
  have hLpos : 0 < Real.log |ρ.im| := lt_of_lt_of_le (Real.log_pos (by norm_num)) hL
  rcases le_or_gt T₀ |ρ.im| with hT | hT
  · have h := h₁ ρ hρ hT
    have : min c₁ (η * Real.log 2) / Real.log |ρ.im| ≤ c₁ / Real.log |ρ.im| :=
      div_le_div_of_nonneg_right (min_le_left _ _) hLpos.le
    linarith
  · have hmem : ρ ∈ F := by
      refine ⟨⟨?_, hρ.1⟩, hρ⟩
      rw [mem_closedBall, dist_zero_right]
      have h := Complex.norm_le_abs_re_add_abs_im ρ
      rw [abs_of_pos hρ.2.1] at h
      linarith [hρ.2.2]
    have h := hηb ρ hmem
    have : min c₁ (η * Real.log 2) / Real.log |ρ.im| ≤ η := by
      rw [div_le_iff₀ hLpos]
      calc min c₁ (η * Real.log 2) ≤ η * Real.log 2 := min_le_right _ _
        _ ≤ η * Real.log |ρ.im| := by gcongr
    linarith

/-- **Forma de não anulação**: existe `c > 0` com `ζ(s) ≠ 0` sempre que `|Im s| ≥ 2` e
`Re s > 1 − c/log|Im s|`. -/
theorem zeta_ne_zero_regiao : ∃ c > 0, ∀ s : ℂ, 2 ≤ |s.im| → 1 - c / Real.log |s.im| < s.re →
    riemannZeta s ≠ 0 := by
  obtain ⟨c, hc, h⟩ := regiao_livre
  refine ⟨c, hc, fun s h2 hre hz => ?_⟩
  rcases le_or_gt s.re 0 with h0 | h0
  · obtain ⟨n, hn⟩ := ATK.ZetaSimetria.zero_trivial_de_re_nao_pos hz h0
    have : s.im = 0 := by rw [hn]; simp
    rw [this, abs_zero] at h2
    linarith
  · have h1 : s.re < 1 := re_lt_um hz
    have := h s ⟨hz, h0, h1⟩ h2
    linarith

end ATK.ZeroClasses.RegiaoLivre

#print axioms ATK.ZeroClasses.RegiaoLivre.cota_zeta_faixa
#print axioms ATK.ZeroClasses.RegiaoLivre.cota_zeta_real
#print axioms ATK.ZeroClasses.RegiaoLivre.prod341
#print axioms ATK.ZeroClasses.RegiaoLivre.zeta_lb
#print axioms ATK.ZeroClasses.RegiaoLivre.zeta_local
#print axioms ATK.ZeroClasses.RegiaoLivre.re_termo_nonneg
#print axioms ATK.ZeroClasses.RegiaoLivre.re_lt_um
#print axioms ATK.ZeroClasses.RegiaoLivre.re_logDeriv_local
#print axioms ATK.ZeroClasses.RegiaoLivre.re_logDeriv_local_zero
#print axioms ATK.ZeroClasses.RegiaoLivre.Gp_diff
#print axioms ATK.ZeroClasses.RegiaoLivre.Gp_eq
#print axioms ATK.ZeroClasses.RegiaoLivre.Gp_ne_zero
#print axioms ATK.ZeroClasses.RegiaoLivre.logDeriv_zeta_Gp
#print axioms ATK.ZeroClasses.RegiaoLivre.polo
#print axioms ATK.ZeroClasses.RegiaoLivre.termo341
#print axioms ATK.ZeroClasses.RegiaoLivre.tres_quatro_um
#print axioms ATK.ZeroClasses.RegiaoLivre.regiao_livre_grande
#print axioms ATK.ZeroClasses.RegiaoLivre.regiao_livre
#print axioms ATK.ZeroClasses.RegiaoLivre.zeta_ne_zero_regiao
