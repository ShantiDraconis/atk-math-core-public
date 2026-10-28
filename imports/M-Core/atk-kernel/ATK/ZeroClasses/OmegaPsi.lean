import ATK.ZeroClasses.QuasiRH
import ATK.ZeroClasses.HardyTeorema

/-!
# Teoremas Ω: `ψ(x) − x` e `M(x)` não são `o(√x)` (rodada 58)

* **`psi_nao_o`**: não vale `|ψ(N) − N| ≤ ε√(N + 1) + C_ε` para todo `ε > 0` — isto é, `ψ(x) − x ≠ o(√x)`
  (Schmidt 1903, na forma Ω; `psi_nao_littleO` na linguagem `=o[atTop]` da Mathlib);
* **`mertens_nao_o`**: o mesmo para `M(x) = Σ_{n ≤ x} μ(n)` (`mertens_nao_littleO`);
* `psi_nao_O_rpow`, `mertens_nao_O_rpow`: para `θ < ½`, nem `ψ(x) − x` nem `M(x)` são `O(x^θ)`.

Ingredientes: o teorema de Hardy (rodada 50) dá um zero `ρ₀ = ½ + iγ₀` de `ζ`. Se `ψ(x) − x = o(√x)`, a série por partes
`G(s) = Σ E(n + 1)((n + 1)^{−s} − (n + 2)^{−s})` da rodada 55 satisfaz `(σ − ½)|G(σ + iγ₀)| → 0` quando `σ → ½⁺`
(`o_GA`, com `(σ − ½)ζ(σ + ½) → 1` da Mathlib), e `G = −ζ′/ζ − ζ` em `Re s > ½` (`GA_E_eq_Hf`, princípio da
identidade). Mas `−ζ′/ζ` tem polo de resíduo `−m` em `ρ₀`, logo `(σ − ½)|G(σ + iγ₀)| ≥ ½` perto de `½`
(`cota_inf_H`). Para `M`, `G = 1/ζ` (`GA_M_eq_F`) e o polo de `1/ζ` dá a mesma contradição (`cota_inf_F`).

Classificação (rodada 58): **consequência** (incondicional) de Hardy + rodada 55. Não é RH, nem Ω±.
-/

open Complex Set Filter Topology Metric Asymptotics
open scoped Real

namespace ATK.ZeroClasses.Omega

open ATK.ZeroClasses.VonKoch (gA GA differentiableAt_GA GA_eq_LSeries cL E E_succ LSeries_cL LSeriesSummable_cL
  zeroFree_of_psi zeroFree_of_mertens)
open ATK.ZeroClasses.VonKochRH (Hf Hf_eq)
open ATK.ZeroClasses.QuasiRH (SemZeros differentiableAt_Hf differentiableAt_F)
open ATK.ZeroClasses.Mertens (M M_succ_eq norm_cpow_sub_le summable_shift)
open ATK.ZeroClasses.LittlewoodMu (mu norm_mu_le LSeries_mu)
open ATK.RHLogZeta (F F_eq zeta₁_eq)

/-! ## 1. `(σ − ½) Z(σ + ½) → 1` -/

/-- `Z(p) = Σ_{n ≥ 0} (n + 1)^{−p}`. -/
noncomputable def Z (p : ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) ^ (-p)

theorem summable_Z {p : ℝ} (hp : 1 < p) : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-p) :=
  summable_shift (by linarith)

theorem Z_eq {p : ℝ} (hp : 1 < p) : Z p = ∑' n : ℕ, 1 / (n : ℝ) ^ p := by
  have hs : Summable fun n : ℕ => 1 / (n : ℝ) ^ p := Real.summable_one_div_nat_rpow.mpr hp
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, Real.zero_rpow (by linarith : p ≠ 0), div_zero, zero_add]
  unfold Z
  refine tsum_congr fun n => ?_
  rw [Real.rpow_neg (by positivity), one_div, Nat.cast_succ]

theorem tendsto_Z : Tendsto (fun σ : ℝ => (σ - 1 / 2) * Z (σ + 1 / 2)) (𝓝[>] (1 / 2)) (𝓝 1) := by
  have hmap : Tendsto (fun σ : ℝ => σ + 1 / 2) (𝓝[>] (1 / 2)) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous (fun σ : ℝ => σ + 1 / 2) := by fun_prop
      exact (hc.tendsto' (1 / 2) 1 (by norm_num)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      simp only [mem_Ioi] at hσ ⊢
      linarith
  refine (tendsto_sub_mul_tsum_nat_rpow.comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  simp only [mem_Ioi] at hσ
  simp only [Function.comp_apply]
  rw [Z_eq (by linarith)]
  ring_nf

/-! ## 2. `ψ − x = o(√x)` ⟹ `(σ − ½)|G(σ + iγ)| → 0` -/

theorem norm_gA_le_o {A : ℕ → ℝ} {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hA : ∀ N : ℕ, |A N| ≤ ε * √((N : ℝ) + 1) + C) (n : ℕ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖gA A n s‖ ≤ ‖s‖ * (ε * √2 * ((n : ℝ) + 1) ^ (-(s.re + 1 / 2)) + C * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hsub := norm_cpow_sub_le hn1 (z := s) (by linarith)
  have e1 : (((n : ℝ) + 1 : ℝ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
  have e2 : (((n : ℝ) + 1 + 1 : ℝ) : ℂ) = (n : ℂ) + 2 := by push_cast; ring
  rw [e1, e2] at hsub
  have hAn := hA (n + 1)
  have hsq : √(((n + 1 : ℕ) : ℝ) + 1) ≤ √2 * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by push_cast; linarith)
  have hA' : |A (n + 1)| ≤ ε * √2 * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) + C := by
    calc |A (n + 1)| ≤ ε * √(((n + 1 : ℕ) : ℝ) + 1) + C := hAn
      _ ≤ ε * (√2 * ((n : ℝ) + 1) ^ (1 / 2 : ℝ)) + C := by gcongr
      _ = ε * √2 * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) + C := by ring
  have hp1 : ((n : ℝ) + 1) ^ (1 / 2 : ℝ) * ((n : ℝ) + 1) ^ (-s.re - 1) = ((n : ℝ) + 1) ^ (-(s.re + 1 / 2)) := by
    rw [← Real.rpow_add hn0]; ring_nf
  have hp2 : ((n : ℝ) + 1) ^ (-s.re - 1) ≤ ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  unfold gA
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |A (n + 1)| * ‖((n : ℂ) + 1) ^ (-s) - ((n : ℂ) + 2) ^ (-s)‖
      ≤ (ε * √2 * ((n : ℝ) + 1) ^ (1 / 2 : ℝ) + C) * (‖s‖ * ((n : ℝ) + 1) ^ (-s.re - 1)) :=
        mul_le_mul hA' hsub (norm_nonneg _) (by positivity)
    _ = ‖s‖ * (ε * √2 * (((n : ℝ) + 1) ^ (1 / 2 : ℝ) * ((n : ℝ) + 1) ^ (-s.re - 1)) +
          C * ((n : ℝ) + 1) ^ (-s.re - 1)) := by ring
    _ ≤ ‖s‖ * (ε * √2 * ((n : ℝ) + 1) ^ (-(s.re + 1 / 2)) + C * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
        rw [hp1]; gcongr

theorem norm_GA_le_o {A : ℕ → ℝ} {ε C : ℝ} (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hA : ∀ N : ℕ, |A N| ≤ ε * √((N : ℝ) + 1) + C) {s : ℂ} (hs : 1 / 2 < s.re) :
    ‖GA A s‖ ≤ ‖s‖ * (ε * √2 * Z (s.re + 1 / 2) + C * Z (3 / 2)) := by
  have h1 := summable_Z (p := s.re + 1 / 2) (by linarith)
  have h2 := summable_Z (p := 3 / 2) (by norm_num)
  have hmaj : Summable fun n : ℕ => ‖s‖ * (ε * √2 * ((n : ℝ) + 1) ^ (-(s.re + 1 / 2)) +
      C * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))) :=
    ((h1.mul_left (ε * √2)).add (h2.mul_left C)).mul_left ‖s‖
  have hb : ∀ n, ‖gA A n s‖ ≤ ‖s‖ * (ε * √2 * ((n : ℝ) + 1) ^ (-(s.re + 1 / 2)) +
      C * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := fun n => norm_gA_le_o hε hC hA n hs.le
  have hsn : Summable fun n => ‖gA A n s‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hmaj
  unfold GA
  refine (norm_tsum_le_tsum_norm hsn).trans ((Summable.tsum_le_tsum hb hsn hmaj).trans (le_of_eq ?_))
  rw [tsum_mul_left, (h1.mul_left (ε * √2)).tsum_add (h2.mul_left C), tsum_mul_left, tsum_mul_left]
  rfl

/-- **`A(N) = o(√N)` ⟹ `(σ − ½)|G(σ + iγ)| → 0` quando `σ → ½⁺`.** -/
theorem o_GA {A : ℕ → ℝ} (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |A N| ≤ ε * √((N : ℝ) + 1) + C) (γ : ℝ) :
    Tendsto (fun σ : ℝ => (σ - 1 / 2) * ‖GA A ((σ : ℂ) + γ * I)‖) (𝓝[>] (1 / 2)) (𝓝 0) := by
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ‖(1 / 2 : ℂ) + γ * I‖ + 1 := ⟨_, rfl⟩
  have hR0 : 0 < R := by rw [hR]; positivity
  have hpath : Tendsto (fun σ : ℝ => ‖(σ : ℂ) + γ * I‖) (𝓝[>] (1 / 2)) (𝓝 ‖(1 / 2 : ℂ) + γ * I‖) := by
    have hc : Continuous (fun σ : ℝ => (σ : ℂ) + γ * I) := by fun_prop
    exact ((hc.tendsto' (1 / 2) ((1 / 2 : ℂ) + γ * I) (by push_cast; ring)).mono_left nhdsWithin_le_nhds).norm
  have hσ0 : Tendsto (fun σ : ℝ => σ - 1 / 2) (𝓝[>] (1 / 2)) (𝓝 0) := by
    have hc : Continuous (fun σ : ℝ => σ - 1 / 2) := by fun_prop
    exact (hc.tendsto' (1 / 2) 0 (by norm_num)).mono_left nhdsWithin_le_nhds
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = δ / (2 * R * (2 * √2 + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  obtain ⟨C, hC⟩ := h ε hε0
  have hC' : ∀ N : ℕ, |A N| ≤ ε * √((N : ℝ) + 1) + max C 0 := fun N =>
    (hC N).trans (by linarith [le_max_left C 0])
  have hZ32 : 0 ≤ Z (3 / 2) := tsum_nonneg fun n => by positivity
  have ev1 : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), (σ - 1 / 2) * Z (σ + 1 / 2) < 2 :=
    tendsto_Z.eventually (Iio_mem_nhds (by norm_num))
  have ev2 : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), (σ - 1 / 2) * (max C 0 * Z (3 / 2)) < ε := by
    have := (hσ0.mul_const (max C 0 * Z (3 / 2)))
    rw [zero_mul] at this
    exact this.eventually (Iio_mem_nhds hε0)
  have ev3 : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), ‖(σ : ℂ) + γ * I‖ < R :=
    hpath.eventually (Iio_mem_nhds (show ‖(1 / 2 : ℂ) + γ * I‖ < R by rw [hR]; linarith))
  filter_upwards [ev1, ev2, ev3, self_mem_nhdsWithin] with σ h1 h2 h3 h4
  simp only [mem_Ioi] at h4
  have hre : ((σ : ℂ) + γ * I).re = σ := by simp
  have hb := norm_GA_le_o hε0.le (le_max_right C 0) hC' (s := (σ : ℂ) + γ * I) (by rw [hre]; exact h4)
  rw [hre] at hb
  have hpos : 0 ≤ (σ - 1 / 2) * ‖GA A ((σ : ℂ) + γ * I)‖ := mul_nonneg (by linarith) (norm_nonneg _)
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hpos]
  have hZ0 : 0 ≤ Z (σ + 1 / 2) := tsum_nonneg fun n => by positivity
  have hs2 : (σ - 1 / 2) * (ε * √2 * Z (σ + 1 / 2) + max C 0 * Z (3 / 2)) ≤ ε * (2 * √2 + 1) := by
    have e : (σ - 1 / 2) * (ε * √2 * Z (σ + 1 / 2) + max C 0 * Z (3 / 2)) =
        ε * √2 * ((σ - 1 / 2) * Z (σ + 1 / 2)) + (σ - 1 / 2) * (max C 0 * Z (3 / 2)) := by ring
    rw [e]
    have : ε * √2 * ((σ - 1 / 2) * Z (σ + 1 / 2)) ≤ ε * √2 * 2 :=
      mul_le_mul_of_nonneg_left h1.le (by positivity)
    nlinarith
  calc (σ - 1 / 2) * ‖GA A ((σ : ℂ) + γ * I)‖
      ≤ (σ - 1 / 2) * (‖(σ : ℂ) + γ * I‖ * (ε * √2 * Z (σ + 1 / 2) + max C 0 * Z (3 / 2))) :=
        mul_le_mul_of_nonneg_left hb (by linarith)
    _ = ‖(σ : ℂ) + γ * I‖ * ((σ - 1 / 2) * (ε * √2 * Z (σ + 1 / 2) + max C 0 * Z (3 / 2))) := by ring
    _ ≤ R * (ε * (2 * √2 + 1)) := mul_le_mul h3.le hs2 (by
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ σ - 1 / 2)
          (by positivity : (0 : ℝ) ≤ ε * √2 * Z (σ + 1 / 2) + max C 0 * Z (3 / 2))
        exact this) hR0.le
    _ = δ / 2 := by rw [hε]; field_simp
    _ < δ := by linarith

/-! ## 3. O polo em um zero de `ζ` -/

/-- Num zero `ρ ≠ 1` de `ζ`, `ζ₁ = (s − ρ)^{m+1} g` perto de `ρ`, com `g(ρ) ≠ 0`. -/
theorem fatora {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) :
    ∃ m : ℕ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      ∀ᶠ s in 𝓝 ρ, riemannZeta₁ s = (s - ρ) ^ (m + 1) * g s := by
  have hZ : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hne : ¬∀ᶠ s in 𝓝 ρ, riemannZeta₁ s = 0 := by
    intro hloc
    have hAu : AnalyticOnNhd ℂ riemannZeta₁ univ := fun z _ => hZ.analyticAt z
    have hall := hAu.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ ρ) hloc
    have h2 := hall (mem_univ (2 : ℂ))
    simp only [Pi.zero_apply] at h2
    rw [zeta₁_eq (by norm_num)] at h2
    have h21 : (2 : ℂ) - 1 ≠ 0 := by norm_num
    exact riemannZeta_ne_zero_of_one_lt_re (s := 2) (by norm_num) ((mul_eq_zero.mp h2).resolve_left h21)
  obtain ⟨n, g, hg, hgρ, hfg⟩ := (hZ.analyticAt ρ).exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  simp only [smul_eq_mul] at hfg
  have hz1 : riemannZeta₁ ρ = 0 := by rw [zeta₁_eq hρ1, hρ, mul_zero]
  rcases n with _ | m
  · exfalso
    have h0 := hfg.self_of_nhds
    rw [sub_self, pow_zero, one_mul] at h0
    exact hgρ (h0.symm.trans hz1)
  · exact ⟨m, g, hg, hgρ, hfg⟩

/-- O caminho `σ ↦ σ + iγ` tende a `½ + iγ` quando `σ → ½⁺`. -/
theorem caminho (γ : ℝ) :
    Tendsto (fun σ : ℝ => (σ : ℂ) + γ * I) (𝓝[>] (1 / 2)) (𝓝 ((1 / 2 : ℂ) + γ * I)) := by
  have hc : Continuous (fun σ : ℝ => (σ : ℂ) + γ * I) := by fun_prop
  exact (hc.tendsto' (1 / 2) ((1 / 2 : ℂ) + γ * I) (by push_cast; ring)).mono_left nhdsWithin_le_nhds

theorem sub_caminho (σ γ : ℝ) : ((σ : ℂ) + γ * I) - ((1 / 2 : ℂ) + γ * I) = ((σ - 1 / 2 : ℝ) : ℂ) := by
  push_cast; ring

theorem tendsto_sub_meio : Tendsto (fun σ : ℝ => σ - 1 / 2) (𝓝[>] (1 / 2)) (𝓝 0) := by
  have hc : Continuous (fun σ : ℝ => σ - 1 / 2) := by fun_prop
  exact (hc.tendsto' (1 / 2) 0 (by norm_num)).mono_left nhdsWithin_le_nhds

/-- **`−ζ′/ζ − ζ` explode em um zero da reta**: `(σ − ½)|H(σ + iγ)| ≥ ½` perto de `½`. -/
theorem cota_inf_H {γ : ℝ} (hz : riemannZeta ((1 / 2 : ℂ) + γ * I) = 0) :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), 1 / 2 ≤ (σ - 1 / 2) * ‖Hf ((σ : ℂ) + γ * I)‖ := by
  set ρ : ℂ := (1 / 2 : ℂ) + γ * I with hρdef
  have hρ1 : ρ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [hρdef] at this
  obtain ⟨m, g, hg, hgρ, hfg⟩ := fatora hz hρ1
  have hgev : ∀ᶠ s in 𝓝 ρ, AnalyticAt ℂ g s := hg.eventually_analyticAt
  have hgne : ∀ᶠ s in 𝓝 ρ, g s ≠ 0 := hg.continuousAt.eventually_ne hgρ
  have hder : ∀ᶠ s in 𝓝 ρ, deriv riemannZeta₁ s =
      ((m + 1 : ℕ) : ℂ) * (s - ρ) ^ m * g s + (s - ρ) ^ (m + 1) * deriv g s := by
    have hfg' : riemannZeta₁ =ᶠ[𝓝 ρ] fun s => (s - ρ) ^ (m + 1) * g s := hfg
    filter_upwards [hfg'.eventuallyEq_nhds, hgev] with s hs hgs
    rw [hs.deriv_eq]
    have h1 : HasDerivAt (fun s : ℂ => (s - ρ) ^ (m + 1)) (((m + 1 : ℕ) : ℂ) * (s - ρ) ^ m) s := by
      have := ((hasDerivAt_id' s).sub_const ρ).pow (m + 1)
      convert this using 1
      simp
    exact (h1.mul hgs.differentiableAt.hasDerivAt).deriv
  -- o resto `g′/g + ζ₀` é limitado perto de `ρ`
  set K : ℂ → ℂ := fun s => deriv g s / g s + riemannZeta₀ s with hKdef
  have hKc : ContinuousAt K ρ :=
    (hg.deriv.continuousAt.div hg.continuousAt hgρ).add (differentiable_riemannZeta₀ ρ).continuousAt
  have hKn : Tendsto (fun s => ‖K s‖) (𝓝 ρ) (𝓝 ‖K ρ‖) := hKc.norm
  have hKev : ∀ᶠ s in 𝓝 ρ, ‖K s‖ < ‖K ρ‖ + 1 :=
    hKn.eventually (Iio_mem_nhds (show ‖K ρ‖ < ‖K ρ‖ + 1 by linarith))
  -- a identidade `H = −(m + 1)/(s − ρ) − K` fora de `ρ`
  have hH : ∀ᶠ s in 𝓝 ρ, s ≠ ρ → Hf s = -(((m + 1 : ℕ) : ℂ) / (s - ρ)) - K s := by
    filter_upwards [hfg, hder, hgne] with s h1 h2 h3 hsρ
    have hsρ' : s - ρ ≠ 0 := sub_ne_zero.mpr hsρ
    unfold Hf
    rw [h1, h2, hKdef]
    field_simp
    ring
  have ev := (caminho γ).eventually (hH.and hKev)
  have evr : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), (σ - 1 / 2) * (‖K ρ‖ + 1) < 1 / 2 := by
    have := tendsto_sub_meio.mul_const (‖K ρ‖ + 1)
    rw [zero_mul] at this
    exact this.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [ev, evr, self_mem_nhdsWithin] with σ ⟨hH1, hK1⟩ hr hσ
  simp only [mem_Ioi] at hσ
  have hd : ((σ : ℂ) + γ * I) - ρ = ((σ - 1 / 2 : ℝ) : ℂ) := by rw [hρdef]; exact sub_caminho σ γ
  have hne : (σ : ℂ) + γ * I ≠ ρ := by
    intro h
    have : ((σ - 1 / 2 : ℝ) : ℂ) = 0 := by rw [← hd, h, sub_self]
    have : σ - 1 / 2 = 0 := by exact_mod_cast this
    linarith
  rw [hH1 hne, hd]
  have hpos : 0 < σ - 1 / 2 := by linarith
  have hnorm : ‖-(((m + 1 : ℕ) : ℂ) / ((σ - 1 / 2 : ℝ) : ℂ)) - K ((σ : ℂ) + γ * I)‖ ≥
      ((m : ℝ) + 1) / (σ - 1 / 2) - ‖K ((σ : ℂ) + γ * I)‖ := by
    have e : ‖-(((m + 1 : ℕ) : ℂ) / ((σ - 1 / 2 : ℝ) : ℂ))‖ = ((m : ℝ) + 1) / (σ - 1 / 2) := by
      rw [norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      push_cast
      rw [show ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    have := norm_sub_norm_le (-(((m + 1 : ℕ) : ℂ) / ((σ - 1 / 2 : ℝ) : ℂ))) (K ((σ : ℂ) + γ * I))
    rw [e] at this
    linarith
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith
  calc 1 / 2 ≤ ((m : ℝ) + 1) - (σ - 1 / 2) * (‖K ρ‖ + 1) := by linarith
    _ ≤ (σ - 1 / 2) * (((m : ℝ) + 1) / (σ - 1 / 2) - ‖K ((σ : ℂ) + γ * I)‖) := by
        have e : (σ - 1 / 2) * (((m : ℝ) + 1) / (σ - 1 / 2)) = (m : ℝ) + 1 := by
          rw [mul_comm]; exact div_mul_cancel₀ _ hpos.ne'
        nlinarith
    _ ≤ (σ - 1 / 2) * ‖-(((m + 1 : ℕ) : ℂ) / ((σ - 1 / 2 : ℝ) : ℂ)) - K ((σ : ℂ) + γ * I)‖ :=
        mul_le_mul_of_nonneg_left hnorm hpos.le

/-- **`1/ζ` explode em um zero da reta**: existe `c > 0` com `(σ − ½)|1/ζ(σ + iγ)| ≥ c` perto de `½`. -/
theorem cota_inf_F {γ : ℝ} (hz : riemannZeta ((1 / 2 : ℂ) + γ * I) = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), c ≤ (σ - 1 / 2) * ‖F ((σ : ℂ) + γ * I)‖ := by
  set ρ : ℂ := (1 / 2 : ℂ) + γ * I with hρdef
  have hρ1 : ρ ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [hρdef] at this
  obtain ⟨m, g, hg, hgρ, hfg⟩ := fatora hz hρ1
  have hd1 : 0 < ‖ρ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hρ1)
  refine ⟨‖ρ - 1‖ / 2 / (‖g ρ‖ + 1), by positivity, ?_⟩
  have hgne : ∀ᶠ s in 𝓝 ρ, g s ≠ 0 := hg.continuousAt.eventually_ne hgρ
  have hgn : Tendsto (fun s => ‖g s‖) (𝓝 ρ) (𝓝 ‖g ρ‖) := hg.continuousAt.norm
  have hgev : ∀ᶠ s in 𝓝 ρ, ‖g s‖ < ‖g ρ‖ + 1 :=
    hgn.eventually (Iio_mem_nhds (show ‖g ρ‖ < ‖g ρ‖ + 1 by linarith))
  have h1ev : ∀ᶠ s in 𝓝 ρ, ‖ρ - 1‖ / 2 < ‖s - 1‖ := by
    have hc : Tendsto (fun s : ℂ => ‖s - 1‖) (𝓝 ρ) (𝓝 ‖ρ - 1‖) :=
      ((continuousAt_id.sub continuousAt_const).norm : ContinuousAt (fun s : ℂ => ‖s - 1‖) ρ)
    exact hc.eventually (Ioi_mem_nhds (show ‖ρ - 1‖ / 2 < ‖ρ - 1‖ by linarith))
  have hrev : ∀ᶠ s in 𝓝 ρ, ‖s - ρ‖ < 1 := by
    have hc : Tendsto (fun s : ℂ => ‖s - ρ‖) (𝓝 ρ) (𝓝 ‖ρ - ρ‖) :=
      ((continuousAt_id.sub continuousAt_const).norm : ContinuousAt (fun s : ℂ => ‖s - ρ‖) ρ)
    exact hc.eventually (Iio_mem_nhds (show ‖ρ - ρ‖ < 1 by simp))
  have ev := (caminho γ).eventually (hfg.and (hgne.and (hgev.and (h1ev.and hrev))))
  filter_upwards [ev, self_mem_nhdsWithin] with σ ⟨hf1, hg0, hg1, hs1, hr1⟩ hσ
  simp only [mem_Ioi] at hσ
  have hpos : 0 < σ - 1 / 2 := by linarith
  have hd : ((σ : ℂ) + γ * I) - ρ = ((σ - 1 / 2 : ℝ) : ℂ) := by rw [hρdef]; exact sub_caminho σ γ
  have hdn : ‖((σ : ℂ) + γ * I) - ρ‖ = σ - 1 / 2 := by
    rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  rw [hdn] at hr1
  unfold F
  rw [hf1, norm_div, norm_mul, norm_pow, hdn]
  have hgn : 0 < ‖g ((σ : ℂ) + γ * I)‖ := norm_pos_iff.mpr hg0
  have hpow : (σ - 1 / 2) ^ (m + 1) ≤ σ - 1 / 2 := by
    calc (σ - 1 / 2) ^ (m + 1) = (σ - 1 / 2) ^ m * (σ - 1 / 2) := pow_succ _ _
      _ ≤ 1 * (σ - 1 / 2) := mul_le_mul_of_nonneg_right (pow_le_one₀ hpos.le hr1.le) hpos.le
      _ = σ - 1 / 2 := one_mul _
  have hden : 0 < (σ - 1 / 2) ^ (m + 1) * ‖g ((σ : ℂ) + γ * I)‖ := by positivity
  rw [mul_div_assoc', le_div_iff₀ hden]
  calc ‖ρ - 1‖ / 2 / (‖g ρ‖ + 1) * ((σ - 1 / 2) ^ (m + 1) * ‖g ((σ : ℂ) + γ * I)‖)
      ≤ ‖ρ - 1‖ / 2 / (‖g ρ‖ + 1) * ((σ - 1 / 2) * (‖g ρ‖ + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hpow hg1.le hgn.le hpos.le
    _ = (σ - 1 / 2) * (‖ρ - 1‖ / 2) := by field_simp
    _ ≤ (σ - 1 / 2) * ‖(σ : ℂ) + γ * I - 1‖ := mul_le_mul_of_nonneg_left hs1.le hpos.le

/-! ## 4. `G = −ζ′/ζ − ζ` e `G = 1/ζ` em `Re s > ½` -/

theorem GA_E_eq_Hf {C : ℝ} (hC : ∀ N : ℕ, |E N| ≤ C * ((N : ℝ) + 1) ^ (1 / 2 : ℝ))
    (hZ : SemZeros (1 / 2)) {s : ℂ} (hs : 1 / 2 < s.re) : GA E s = Hf s := by
  have hV : IsOpen {w : ℂ | (1 / 2 : ℝ) < w.re} := isOpen_lt continuous_const continuous_re
  have hA1 : AnalyticOnNhd ℂ (GA E) {w : ℂ | (1 / 2 : ℝ) < w.re} :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (differentiableAt_GA (by norm_num) hC hw).differentiableWithinAt) hV
  have hA2 : AnalyticOnNhd ℂ Hf {w : ℂ | (1 / 2 : ℝ) < w.re} :=
    DifferentiableOn.analyticOnNhd (fun w hw => (differentiableAt_Hf hZ hw).differentiableWithinAt) hV
  have hev : GA E =ᶠ[𝓝 (2 : ℂ)] Hf := by
    have hmem : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by show (1 : ℝ) < (2 : ℂ).re; norm_num)
    filter_upwards [hmem] with w hw
    have hw' : 1 < w.re := hw
    have hw1 : w ≠ 1 := fun h => by rw [h, one_re] at hw'; exact lt_irrefl 1 hw'
    rw [GA_eq_LSeries (by norm_num) (by norm_num) hC E_succ hw' (LSeriesSummable_cL hw'), LSeries_cL hw',
      Hf_eq hw1 (riemannZeta_ne_zero_of_one_lt_re hw')]
  have h2V : (2 : ℂ) ∈ {w : ℂ | (1 / 2 : ℝ) < w.re} := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
  exact hA1.eqOn_of_preconnected_of_eventuallyEq hA2 (convex_halfSpace_re_gt (1 / 2)).isPreconnected h2V hev hs

theorem GA_M_eq_F {C : ℝ} (hC : ∀ N : ℕ, |M N| ≤ C * ((N : ℝ) + 1) ^ (1 / 2 : ℝ))
    (hZ : SemZeros (1 / 2)) {s : ℂ} (hs : 1 / 2 < s.re) : GA M s = F s := by
  have hV : IsOpen {w : ℂ | (1 / 2 : ℝ) < w.re} := isOpen_lt continuous_const continuous_re
  have hA1 : AnalyticOnNhd ℂ (GA M) {w : ℂ | (1 / 2 : ℝ) < w.re} :=
    DifferentiableOn.analyticOnNhd (fun w hw =>
      (differentiableAt_GA (by norm_num) hC hw).differentiableWithinAt) hV
  have hA2 : AnalyticOnNhd ℂ F {w : ℂ | (1 / 2 : ℝ) < w.re} :=
    DifferentiableOn.analyticOnNhd (fun w hw => (differentiableAt_F hZ hw).differentiableWithinAt) hV
  have hev : GA M =ᶠ[𝓝 (2 : ℂ)] F := by
    have hmem : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by show (1 : ℝ) < (2 : ℂ).re; norm_num)
    filter_upwards [hmem] with w hw
    have hw' : 1 < w.re := hw
    have hL : LSeriesSummable mu w := LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_mu_le n) hw'
    rw [GA_eq_LSeries (by norm_num) (by norm_num) hC M_succ_eq hw' hL, LSeries_mu hw']
  have h2V : (2 : ℂ) ∈ {w : ℂ | (1 / 2 : ℝ) < w.re} := by show (1 / 2 : ℝ) < (2 : ℂ).re; norm_num
  exact hA1.eqOn_of_preconnected_of_eventuallyEq hA2 (convex_halfSpace_re_gt (1 / 2)).isPreconnected h2V hev hs

/-! ## 5. Os teoremas Ω -/

theorem O_meio {A : ℕ → ℝ} {C : ℝ} (hA : ∀ N : ℕ, |A N| ≤ 1 * √((N : ℝ) + 1) + C) :
    ∀ N : ℕ, |A N| ≤ (1 + max C 0) * ((N : ℝ) + 1) ^ (1 / 2 : ℝ) := by
  intro N
  have hN : (1 : ℝ) ≤ (N : ℝ) + 1 := by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
  have h1 : (1 : ℝ) ≤ √((N : ℝ) + 1) := by rw [Real.one_le_sqrt]; exact hN
  rw [← Real.sqrt_eq_rpow]
  have := hA N
  nlinarith [le_max_left C 0, le_max_right C 0, mul_nonneg (sub_nonneg.mpr h1) (le_max_right C 0)]

/-- **`ψ(x) − x` não é `o(√x)`**: não existem, para todo `ε > 0`, constantes com `|ψ(N) − N| ≤ ε√(N + 1) + C`. -/
theorem psi_nao_o :
    ¬ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |Chebyshev.psi N - N| ≤ ε * √((N : ℝ) + 1) + C := by
  intro h
  have h' : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |E N| ≤ ε * √((N : ℝ) + 1) + C := h
  obtain ⟨C₁, hC₁⟩ := h' 1 one_pos
  have hO := O_meio hC₁
  have hZ : SemZeros (1 / 2) := fun s hs =>
    zeroFree_of_psi (θ := 1 / 2) (by norm_num) (by norm_num) hO hs
  obtain ⟨γ, -, hγ⟩ := ATK.ZeroClasses.Hardy.existe_zero_acima 0
  have hlow := cota_inf_H hγ
  have hsmall : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), (σ - 1 / 2) * ‖GA E ((σ : ℂ) + γ * I)‖ < 1 / 2 :=
    (o_GA h' γ).eventually (Iio_mem_nhds (by norm_num))
  have hcontra : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), False := by
    filter_upwards [hlow, hsmall, self_mem_nhdsWithin] with σ h1 h2 h3
    simp only [mem_Ioi] at h3
    have hre : 1 / 2 < ((σ : ℂ) + γ * I).re := by simpa using h3
    rw [GA_E_eq_Hf hO hZ hre] at h2
    linarith
  obtain ⟨σ, hσ⟩ := hcontra.exists
  exact hσ

/-- **`M(x)` não é `o(√x)`**. -/
theorem mertens_nao_o :
    ¬ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |M N| ≤ ε * √((N : ℝ) + 1) + C := by
  intro h
  obtain ⟨C₁, hC₁⟩ := h 1 one_pos
  have hO := O_meio hC₁
  have hZ : SemZeros (1 / 2) := fun s hs =>
    zeroFree_of_mertens (θ := 1 / 2) (by norm_num) (by norm_num) hO hs
  obtain ⟨γ, -, hγ⟩ := ATK.ZeroClasses.Hardy.existe_zero_acima 0
  obtain ⟨c, hc, hlow⟩ := cota_inf_F hγ
  have hsmall : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), (σ - 1 / 2) * ‖GA M ((σ : ℂ) + γ * I)‖ < c :=
    (o_GA h γ).eventually (Iio_mem_nhds hc)
  have hcontra : ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2), False := by
    filter_upwards [hlow, hsmall, self_mem_nhdsWithin] with σ h1 h2 h3
    simp only [mem_Ioi] at h3
    have hre : 1 / 2 < ((σ : ℂ) + γ * I).re := by simpa using h3
    rw [GA_M_eq_F hO hZ hre] at h2
    linarith
  obtain ⟨σ, hσ⟩ := hcontra.exists
  exact hσ

theorem o_de_littleO {A : ℕ → ℝ} (h : A =o[atTop] (fun N : ℕ => √(N : ℝ))) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |A N| ≤ ε * √((N : ℝ) + 1) + C := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (h.bound hε)
  refine ⟨∑ n ∈ Finset.range N₀, |A n|, fun N => ?_⟩
  have hS0 : 0 ≤ ∑ n ∈ Finset.range N₀, |A n| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsq : 0 ≤ ε * √((N : ℝ) + 1) := by positivity
  rcases lt_or_ge N N₀ with hN | hN
  · have := Finset.single_le_sum (f := fun n => |A n|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hN)
    linarith
  · have h1 := hN₀ N hN
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h1
    have h2 : √(N : ℝ) ≤ √((N : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h2 hε.le]

/-- `ψ(x) − x ≠ o(√x)` (na linguagem `IsLittleO` da Mathlib). -/
theorem psi_nao_littleO : ¬ (fun N : ℕ => Chebyshev.psi N - N) =o[atTop] (fun N : ℕ => √(N : ℝ)) :=
  fun h => psi_nao_o (o_de_littleO h)

/-- `M(x) ≠ o(√x)` (na linguagem `IsLittleO` da Mathlib). -/
theorem mertens_nao_littleO : ¬ (fun N : ℕ => M N) =o[atTop] (fun N : ℕ => √(N : ℝ)) :=
  fun h => mertens_nao_o (o_de_littleO h)

theorem re_zero_reta (γ : ℝ) : ((1 / 2 : ℂ) + γ * I).re = 1 / 2 := by simp

/-- Para `θ < ½`, `ψ(x) − x` não é `O(x^θ)` (Hardy + rodada 55). -/
theorem psi_nao_O_rpow {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ C : ℝ, ∀ N : ℕ, |Chebyshev.psi N - N| ≤ C * ((N : ℝ) + 1) ^ θ := by
  rintro ⟨C, hC⟩
  obtain ⟨γ, -, hγ⟩ := ATK.ZeroClasses.Hardy.existe_zero_acima 0
  have hC' : ∀ N : ℕ, |Chebyshev.psi N - N| ≤ max C 0 * ((N : ℝ) + 1) ^ (max θ 0) := by
    intro N
    have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
    calc |Chebyshev.psi N - N| ≤ C * ((N : ℝ) + 1) ^ θ := hC N
      _ ≤ max C 0 * ((N : ℝ) + 1) ^ θ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((N : ℝ) + 1) ^ (max θ 0) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)) (le_max_right _ _)
  have hm : max θ 0 < 1 / 2 := max_lt hθ (by norm_num)
  exact zeroFree_of_psi (le_max_right θ 0) (by linarith) hC' (by rw [re_zero_reta]; exact hm) hγ

/-- Para `θ < ½`, `M(x)` não é `O(x^θ)`. -/
theorem mertens_nao_O_rpow {θ : ℝ} (hθ : θ < 1 / 2) :
    ¬ ∃ C : ℝ, ∀ N : ℕ, |M N| ≤ C * ((N : ℝ) + 1) ^ θ := by
  rintro ⟨C, hC⟩
  obtain ⟨γ, -, hγ⟩ := ATK.ZeroClasses.Hardy.existe_zero_acima 0
  have hC' : ∀ N : ℕ, |M N| ≤ max C 0 * ((N : ℝ) + 1) ^ (max θ 0) := by
    intro N
    have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
    calc |M N| ≤ C * ((N : ℝ) + 1) ^ θ := hC N
      _ ≤ max C 0 * ((N : ℝ) + 1) ^ θ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((N : ℝ) + 1) ^ (max θ 0) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)) (le_max_right _ _)
  have hm : max θ 0 < 1 / 2 := max_lt hθ (by norm_num)
  exact zeroFree_of_mertens (le_max_right θ 0) (by linarith) hC' (by rw [re_zero_reta]; exact hm) hγ

end ATK.ZeroClasses.Omega

#print axioms ATK.ZeroClasses.Omega.summable_Z
#print axioms ATK.ZeroClasses.Omega.Z_eq
#print axioms ATK.ZeroClasses.Omega.tendsto_Z
#print axioms ATK.ZeroClasses.Omega.norm_gA_le_o
#print axioms ATK.ZeroClasses.Omega.norm_GA_le_o
#print axioms ATK.ZeroClasses.Omega.o_GA
#print axioms ATK.ZeroClasses.Omega.fatora
#print axioms ATK.ZeroClasses.Omega.caminho
#print axioms ATK.ZeroClasses.Omega.sub_caminho
#print axioms ATK.ZeroClasses.Omega.tendsto_sub_meio
#print axioms ATK.ZeroClasses.Omega.cota_inf_H
#print axioms ATK.ZeroClasses.Omega.cota_inf_F
#print axioms ATK.ZeroClasses.Omega.GA_E_eq_Hf
#print axioms ATK.ZeroClasses.Omega.GA_M_eq_F
#print axioms ATK.ZeroClasses.Omega.O_meio
#print axioms ATK.ZeroClasses.Omega.psi_nao_o
#print axioms ATK.ZeroClasses.Omega.mertens_nao_o
#print axioms ATK.ZeroClasses.Omega.o_de_littleO
#print axioms ATK.ZeroClasses.Omega.psi_nao_littleO
#print axioms ATK.ZeroClasses.Omega.mertens_nao_littleO
#print axioms ATK.ZeroClasses.Omega.re_zero_reta
#print axioms ATK.ZeroClasses.Omega.psi_nao_O_rpow
#print axioms ATK.ZeroClasses.Omega.mertens_nao_O_rpow
