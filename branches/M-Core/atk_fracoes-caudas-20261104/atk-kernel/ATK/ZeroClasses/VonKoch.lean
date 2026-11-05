import ATK.ZeroClasses.MertensRH
import ATK.ZeroClasses.TNP

/-!
# Termos de erro e semiplanos sem zeros: `ψ(x) = x + O(x^θ)` e `M(x) = O(x^θ)` ⟹ `ζ ≠ 0` em `Re s > θ` (rodada 55)

A metade "aritmética ⟹ analítica" dos critérios de von Koch e de Littlewood, **com expoente arbitrário**:

* **`zeroFree_of_psi`**: se `|ψ(N) − N| ≤ C(N + 1)^θ` para todo `N` (`0 ≤ θ < 1`), então `ζ(s) ≠ 0` em `Re s > θ`;
* **`zeroFree_of_mertens`**: o mesmo com `|M(N)| ≤ C(N + 1)^θ` (generaliza `RH_of_mertens`, rodada 51);
* **`RH_of_psi`**: `ψ(x) = x + O(x^{1/2+ε})` para todo `ε > 0` ⟹ RH (metade do critério de von Koch).

A prova para `ψ`: por partes, `−ζ′/ζ(s) − ζ(s) = G(s) = Σ_{n≥1} (ψ(n) − n)(n^{−s} − (n + 1)^{−s})` em `Re s > 1`
(`G_eq_LSeries`), e `G` é holomorfa em `Re s > θ` (`differentiableAt_GA`). Com `ζ₁(s) = (s − 1)ζ(s)` inteira, o
princípio da identidade dá `(s − 1)ζ₁′ = ζ₁·(1 − ζ₁ − (s − 1)G)` em `Re s > θ` (`identidade`), e uma solução de
`q f′ = f P` com `q(ρ) ≠ 0` que se anula em `ρ` é identicamente nula perto de `ρ` (`zero_de_edo`, pela ordem do
zero). Como `ζ₁(2) ≠ 0`, `ζ₁` não tem zeros em `Re s > θ`.

Classificação (rodada 55): **reformulação** (metades suficientes dos critérios clássicos, com `θ` livre). RH continua
OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.VonKoch

open ATK.ZeroClasses.Mertens (abel norm_cpow_sub_le summable_shift)
open ATK.ZeroClasses.LittlewoodMu (LSeries_mu)
open ATK.RHLogZeta (F_eq zeta₁_eq)

/-! ## 1. Séries de Abel com coeficientes `O(n^θ)` -/

/-- `gA a n z = a(n + 1)((n + 1)^{−z} − (n + 2)^{−z})`. -/
noncomputable def gA (a : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  (a (n + 1) : ℂ) * (((n : ℂ) + 1) ^ (-z) - ((n : ℂ) + 2) ^ (-z))

/-- `GA a z = Σ_{n ≥ 0} a(n + 1)((n + 1)^{−z} − (n + 2)^{−z})`. -/
noncomputable def GA (a : ℕ → ℝ) (z : ℂ) : ℂ := ∑' n, gA a n z

theorem C_nonneg {a : ℕ → ℝ} {C θ : ℝ} (hC : ∀ N : ℕ, |a N| ≤ C * ((N : ℝ) + 1) ^ θ) : 0 ≤ C := by
  have := hC 0
  simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one] at this
  exact le_trans (abs_nonneg _) this

theorem norm_gA_le {a : ℕ → ℝ} {C θ : ℝ} (hθ : 0 ≤ θ) (hC : ∀ N : ℕ, |a N| ≤ C * ((N : ℝ) + 1) ^ θ)
    (n : ℕ) {z : ℂ} (hz : -1 ≤ z.re) :
    ‖gA a n z‖ ≤ C * 2 ^ θ * ‖z‖ * ((n : ℝ) + 1) ^ (θ - z.re - 1) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hs := norm_cpow_sub_le hn1 hz
  have e1 : (((n : ℝ) + 1 : ℝ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
  have e2 : (((n : ℝ) + 1 + 1 : ℝ) : ℂ) = (n : ℂ) + 2 := by push_cast; ring
  rw [e1, e2] at hs
  have hM := hC (n + 1)
  have hC0 := C_nonneg hC
  have h2 : ((n + 1 : ℕ) : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by push_cast; linarith
  have hpow : (((n + 1 : ℕ) : ℝ) + 1) ^ θ ≤ 2 ^ θ * ((n : ℝ) + 1) ^ θ := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by positivity) h2 hθ
  have hsplit : ((n : ℝ) + 1) ^ θ * ((n : ℝ) + 1) ^ (-z.re - 1) = ((n : ℝ) + 1) ^ (θ - z.re - 1) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  unfold gA
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |a (n + 1)| * ‖((n : ℂ) + 1) ^ (-z) - ((n : ℂ) + 2) ^ (-z)‖
      ≤ (C * (2 ^ θ * ((n : ℝ) + 1) ^ θ)) * (‖z‖ * ((n : ℝ) + 1) ^ (-z.re - 1)) := by
        apply mul_le_mul _ hs (norm_nonneg _) (by positivity)
        exact hM.trans (mul_le_mul_of_nonneg_left hpow hC0)
    _ = C * 2 ^ θ * ‖z‖ * (((n : ℝ) + 1) ^ θ * ((n : ℝ) + 1) ^ (-z.re - 1)) := by ring
    _ = C * 2 ^ θ * ‖z‖ * ((n : ℝ) + 1) ^ (θ - z.re - 1) := by rw [hsplit]

theorem summable_gA {a : ℕ → ℝ} {C θ : ℝ} (hθ : 0 ≤ θ) (hC : ∀ N : ℕ, |a N| ≤ C * ((N : ℝ) + 1) ^ θ)
    {z : ℂ} (hz : θ < z.re) : Summable fun n => gA a n z := by
  have hs := (summable_shift (p := θ - z.re - 1) (by linarith)).mul_left (C * 2 ^ θ * ‖z‖)
  refine Summable.of_norm_bounded hs fun n => ?_
  exact norm_gA_le hθ hC n (by linarith)

theorem differentiableAt_GA {a : ℕ → ℝ} {C θ : ℝ} (hθ : 0 ≤ θ)
    (hC : ∀ N : ℕ, |a N| ≤ C * ((N : ℝ) + 1) ^ θ) {z : ℂ} (hz : θ < z.re) :
    DifferentiableAt ℂ (GA a) z := by
  obtain ⟨θ', hθ'⟩ : ∃ θ' : ℝ, θ' = (θ + z.re) / 2 := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ‖z‖ + 1 := ⟨_, rfl⟩
  have hU : IsOpen ({w : ℂ | θ' < w.re} ∩ ball 0 R) :=
    (isOpen_lt continuous_const continuous_re).inter isOpen_ball
  have hzU : z ∈ {w : ℂ | θ' < w.re} ∩ ball 0 R := by
    refine ⟨?_, ?_⟩
    · show θ' < z.re
      rw [hθ']; linarith
    · rw [mem_ball, dist_zero_right, hR]; linarith
  have hC0 := C_nonneg hC
  have hsum := (summable_shift (p := θ - θ' - 1) (by rw [hθ']; linarith)).mul_left (C * 2 ^ θ * R)
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ (gA a n) ({w : ℂ | θ' < w.re} ∩ ball 0 R) := by
    intro n w _
    have h1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have h2 : ((n : ℂ) + 2) ≠ 0 := by
      have : ((n : ℂ) + 2) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
      rw [this]; exact_mod_cast (by omega : n + 2 ≠ 0)
    unfold gA
    exact ((differentiableAt_const _).mul ((differentiableAt_id.neg.const_cpow (Or.inl h1)).sub
      (differentiableAt_id.neg.const_cpow (Or.inl h2)))).differentiableWithinAt
  have hle : ∀ (n : ℕ) (w : ℂ), w ∈ {w : ℂ | θ' < w.re} ∩ ball 0 R →
      ‖gA a n w‖ ≤ C * 2 ^ θ * R * ((n : ℝ) + 1) ^ (θ - θ' - 1) := by
    intro n w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hw1' : θ' < w.re := hw1
    rw [mem_ball, dist_zero_right] at hw2
    have hθ'0 : 0 ≤ θ' := by rw [hθ']; linarith
    refine (norm_gA_le hθ hC n (by linarith)).trans ?_
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
    have hp : ((n : ℝ) + 1) ^ (θ - w.re - 1) ≤ ((n : ℝ) + 1) ^ (θ - θ' - 1) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have h2θ : 0 ≤ C * 2 ^ θ := by positivity
    have hR0 : 0 ≤ R := by rw [hR]; positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hw2.le h2θ) hp (by positivity) (by positivity)
  have hD := differentiableOn_tsum_of_summable_norm hsum hdiff hU hle
  exact hD.differentiableAt (hU.mem_nhds hzU)

/-- **Abel para séries de Dirichlet**: se `A(n) = Σ_{k ≤ n} c(k + 1)` e `|A(N)| ≤ C(N + 1)^θ` com `θ < 1`, então
`Σ c(n)n^{−z} = GA A z` em `Re z > 1` (as somas de `c` sobre `n ≥ 1`). -/
theorem GA_eq_LSeries {c : ℕ → ℂ} {A : ℕ → ℝ} {C θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hC : ∀ N : ℕ, |A N| ≤ C * ((N : ℝ) + 1) ^ θ)
    (hA : ∀ n : ℕ, ((A (n + 1) : ℝ) : ℂ) = ∑ k ∈ Finset.range (n + 1), c (k + 1))
    {z : ℂ} (hz : 1 < z.re) (hL : LSeriesSummable c z) : GA A z = LSeries c z := by
  have hsum := summable_gA hθ hC (show θ < z.re by linarith)
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
    rw [abel (fun n => c (n + 1)) (fun n => ((n : ℂ) + 1) ^ (-z)) N, ← hA]
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

/-! ## 2. Uma EDO linear que se anula num ponto -/

/-- Se `q f′ = f P` perto de `ρ`, com `f` analítica em `ρ`, `P, q` contínuas em `ρ`, `q(ρ) ≠ 0` e `f(ρ) = 0`,
então `f ≡ 0` perto de `ρ` (pela ordem do zero: `f = (s − ρ)^{m+1} g` daria `q(ρ)(m + 1)g(ρ) = 0`). -/
theorem zero_de_edo {f P q : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ) (hP : ContinuousAt P ρ)
    (hq : ContinuousAt q ρ) (hqρ : q ρ ≠ 0) (hfρ : f ρ = 0)
    (hedo : ∀ᶠ s in 𝓝 ρ, q s * deriv f s = f s * P s) : ∀ᶠ s in 𝓝 ρ, f s = 0 := by
  by_contra hne
  obtain ⟨n, g, hg, hgρ, hfg⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hne
  simp only [smul_eq_mul] at hfg
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exfalso
      have h0 := hfg.self_of_nhds
      rw [sub_self, pow_zero, one_mul] at h0
      exact hgρ (h0.symm.trans hfρ)
    · exact ⟨m, rfl⟩
  have hgev : ∀ᶠ s in 𝓝 ρ, AnalyticAt ℂ g s := hg.eventually_analyticAt
  have hder : ∀ᶠ s in 𝓝 ρ, deriv f s =
      ((m + 1 : ℕ) : ℂ) * (s - ρ) ^ m * g s + (s - ρ) ^ (m + 1) * deriv g s := by
    have hfg' : f =ᶠ[𝓝 ρ] fun s => (s - ρ) ^ (m + 1) * g s := hfg
    filter_upwards [hfg'.eventuallyEq_nhds, hgev] with s hs hgs
    rw [hs.deriv_eq]
    have h1 : HasDerivAt (fun s : ℂ => (s - ρ) ^ (m + 1)) (((m + 1 : ℕ) : ℂ) * (s - ρ) ^ m) s := by
      have := ((hasDerivAt_id' s).sub_const ρ).pow (m + 1)
      convert this using 1
      simp
    exact (h1.mul hgs.differentiableAt.hasDerivAt).deriv
  have hev : ∀ᶠ s in 𝓝[≠] ρ, q s * (((m + 1 : ℕ) : ℂ) * g s + (s - ρ) * deriv g s) =
      (s - ρ) * g s * P s := by
    filter_upwards [nhdsWithin_le_nhds (hedo.and (hder.and hfg)), self_mem_nhdsWithin] with s hs hs'
    obtain ⟨h1, h2, h3⟩ := hs
    have hsρ : s ≠ ρ := hs'
    have hne' : (s - ρ) ^ m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hsρ)
    apply mul_right_cancel₀ hne'
    calc q s * (((m + 1 : ℕ) : ℂ) * g s + (s - ρ) * deriv g s) * (s - ρ) ^ m
        = q s * deriv f s := by rw [h2]; ring
      _ = f s * P s := h1
      _ = (s - ρ) * g s * P s * (s - ρ) ^ m := by rw [h3]; ring
  have hcL : ContinuousAt (fun s => q s * (((m + 1 : ℕ) : ℂ) * g s + (s - ρ) * deriv g s)) ρ :=
    hq.mul ((continuousAt_const.mul hg.continuousAt).add
      ((continuousAt_id.sub continuousAt_const).mul hg.deriv.continuousAt))
  have hcR : ContinuousAt (fun s => (s - ρ) * g s * P s) ρ :=
    ((continuousAt_id.sub continuousAt_const).mul hg.continuousAt).mul hP
  have hlim := tendsto_nhds_unique (hcL.tendsto.mono_left nhdsWithin_le_nhds)
    ((hcR.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun s hs => hs.symm))
  simp only [sub_self, zero_mul, add_zero] at hlim
  exact mul_ne_zero hqρ (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)) hgρ) hlim

/-! ## 3. `ψ(N) = N + O(N^θ)` ⟹ `ζ ≠ 0` em `Re s > θ` -/

/-- Os coeficientes `Λ(n) − 1` (série `−ζ′/ζ − ζ`). -/
noncomputable def cL (n : ℕ) : ℂ := ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) - 1

/-- O erro do TNP nos inteiros: `E(N) = ψ(N) − N`. -/
noncomputable def E (N : ℕ) : ℝ := Chebyshev.psi N - N

theorem E_succ (n : ℕ) : ((E (n + 1) : ℝ) : ℂ) = ∑ k ∈ Finset.range (n + 1), cL (k + 1) := by
  have hψ : Chebyshev.psi ((n + 1 : ℕ) : ℝ) =
      ∑ k ∈ Finset.range (n + 1 + 1), (ArithmeticFunction.vonMangoldt k : ℝ) :=
    ATK.ZeroClasses.PNT.psi_eq_range _ (by rw [Nat.floor_natCast])
  unfold E cL
  rw [hψ, Finset.sum_range_succ' (fun k => (ArithmeticFunction.vonMangoldt k : ℝ)),
    Finset.sum_sub_distrib]
  simp

theorem LSeriesSummable_cL {s : ℂ} (hs : 1 < s.re) : LSeriesSummable cL s := by
  have h1 : LSeriesSummable ATK.ZeroClasses.PNT.vM s := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have h2 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  have : cL = ATK.ZeroClasses.PNT.vM - 1 := by ext n; simp [cL, ATK.ZeroClasses.PNT.vM]
  rw [this]
  exact h1.sub h2

/-- Em `Re s > 1`: `Σ (Λ(n) − 1) n^{−s} = −ζ′/ζ(s) − ζ(s)`. -/
theorem LSeries_cL {s : ℂ} (hs : 1 < s.re) :
    LSeries cL s = -logDeriv riemannZeta s - riemannZeta s := by
  have h1 : LSeriesSummable ATK.ZeroClasses.PNT.vM s := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have h2 : LSeriesSummable 1 s := LSeriesSummable_one_iff.mpr hs
  have : cL = ATK.ZeroClasses.PNT.vM - 1 := by ext n; simp [cL, ATK.ZeroClasses.PNT.vM]
  rw [this, LSeries_sub h1 h2, ATK.ZeroClasses.PNT.LSeries_vM hs, LSeries_one_eq_riemannZeta hs]

/-- **`ψ(N) = N + O(N^θ)` ⟹ `ζ(s) ≠ 0` em `Re s > θ`** (`0 ≤ θ < 1`). -/
theorem zeroFree_of_psi {C θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hψ : ∀ N : ℕ, |Chebyshev.psi N - N| ≤ C * ((N : ℝ) + 1) ^ θ) {s : ℂ} (hs : θ < s.re) :
    riemannZeta s ≠ 0 := by
  have hC : ∀ N : ℕ, |E N| ≤ C * ((N : ℝ) + 1) ^ θ := hψ
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
  have hR : AnalyticOnNhd ℂ (fun w => riemannZeta₁ w * (1 - riemannZeta₁ w - (w - 1) * GA E w))
      {w : ℂ | θ < w.re} := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hV
    exact ((hZ w).mul (((differentiableAt_const 1).sub (hZ w)).sub
      ((differentiableAt_id.sub (differentiableAt_const 1)).mul
        (differentiableAt_GA hθ hC hw)))).differentiableWithinAt
  have hev : (fun w => (w - 1) * deriv riemannZeta₁ w) =ᶠ[𝓝 (2 : ℂ)]
      fun w => riemannZeta₁ w * (1 - riemannZeta₁ w - (w - 1) * GA E w) := by
    have hmem : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by show (1 : ℝ) < (2 : ℂ).re; norm_num)
    filter_upwards [hmem] with w hw
    have hw' : 1 < w.re := hw
    have hw1 : w ≠ 1 := fun h => by rw [h, one_re] at hw'; exact lt_irrefl 1 hw'
    have hz0 : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hw'
    have hd : deriv riemannZeta₁ w = riemannZeta w + (w - 1) * deriv riemannZeta w := by
      have heq : riemannZeta₁ =ᶠ[𝓝 w] fun u => (u - 1) * riemannZeta u := by
        filter_upwards [eventually_ne_nhds hw1] with u hu
        exact zeta₁_eq hu
      rw [heq.deriv_eq]
      have := ((hasDerivAt_id' w).sub_const 1).mul (differentiableAt_riemannZeta hw1).hasDerivAt
      have h := this.deriv
      rw [one_mul] at h
      exact h
    rw [GA_eq_LSeries hθ hθ1 hC E_succ hw' (LSeriesSummable_cL hw'), LSeries_cL hw', hd,
      zeta₁_eq hw1, logDeriv_apply]
    field_simp
    ring
  have h2V : (2 : ℂ) ∈ {w : ℂ | θ < w.re} := by
    show θ < (2 : ℂ).re
    norm_num; linarith
  have hid := hL.eqOn_of_preconnected_of_eventuallyEq hR hVc h2V hev
  have hsV : s ∈ {w : ℂ | θ < w.re} := hs
  have hz1 : riemannZeta₁ s = 0 := by rw [zeta₁_eq hs1, hz, mul_zero]
  have hloc : ∀ᶠ w in 𝓝 s, riemannZeta₁ w = 0 := by
    refine zero_de_edo (q := fun w => w - 1) (P := fun w => 1 - riemannZeta₁ w - (w - 1) * GA E w)
      (hZ.analyticAt s) ?_ (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr hs1) hz1 ?_
    · exact (((differentiableAt_const 1).sub (hZ s)).sub ((differentiableAt_id.sub
        (differentiableAt_const 1)).mul (differentiableAt_GA hθ hC hs))).continuousAt
    · filter_upwards [hV.mem_nhds hsV] with w hw
      exact hid hw
  have hAu : AnalyticOnNhd ℂ riemannZeta₁ univ := fun z _ => hZ.analyticAt z
  have hall := hAu.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (mem_univ s) hloc
  have h2 := hall (mem_univ (2 : ℂ))
  simp only [Pi.zero_apply] at h2
  rw [zeta₁_eq (by norm_num)] at h2
  have h21 : (2 : ℂ) - 1 ≠ 0 := by norm_num
  exact riemannZeta_ne_zero_of_one_lt_re (s := 2) (by norm_num) ((mul_eq_zero.mp h2).resolve_left h21)

/-- A hipótese de von Koch: `ψ(N) = N + O(N^{1/2 + ε})` para todo `ε > 0`. -/
def VonKochFraco : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |Chebyshev.psi N - N| ≤ C * ((N : ℝ) + 1) ^ (1 / 2 + ε)

/-- **`ψ(x) = x + O(x^{1/2 + ε})` ⟹ RH** (metade do critério de von Koch). -/
theorem RH_of_psi (h : VonKochFraco) : RiemannHypothesis := by
  refine ATK.BaezDuarteBridge.riemannHypothesis_of_strip fun s hs1 hs2 => ?_
  obtain ⟨C, hC⟩ := h ((s.re - 1 / 2) / 2) (by linarith)
  exact zeroFree_of_psi (θ := 1 / 2 + (s.re - 1 / 2) / 2) (by linarith) (by linarith) hC (by linarith)

/-! ## 4. `M(N) = O(N^θ)` ⟹ `ζ ≠ 0` em `Re s > θ` -/

/-- **`M(N) = O(N^θ)` ⟹ `ζ(s) ≠ 0` em `Re s > θ`** (`0 ≤ θ < 1`); generaliza `RH_of_mertens`. -/
theorem zeroFree_of_mertens {C θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hC : ∀ N : ℕ, |Mertens.M N| ≤ C * ((N : ℝ) + 1) ^ θ) {s : ℂ} (hs : θ < s.re) :
    riemannZeta s ≠ 0 := by
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  intro hz
  have hV : IsOpen {w : ℂ | θ < w.re} := isOpen_lt continuous_const continuous_re
  have hA : AnalyticOnNhd ℂ (fun w => riemannZeta₁ w * Mertens.G w - (w - 1)) {w : ℂ | θ < w.re} := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hV
    exact (((differentiable_riemannZeta₁ w).mul (Mertens.differentiableAt_G hθ hC hw)).sub
      (differentiableAt_id.sub (differentiableAt_const 1))).differentiableWithinAt
  have hev : (fun w => riemannZeta₁ w * Mertens.G w - (w - 1)) =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hmem : {w : ℂ | 1 < w.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by show (1 : ℝ) < (2 : ℂ).re; norm_num)
    filter_upwards [hmem] with w hw
    have hw' : 1 < w.re := hw
    have hw1 : w ≠ 1 := fun h => by rw [h, one_re] at hw'; exact lt_irrefl 1 hw'
    have hz0 : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hw'
    rw [Mertens.G_eq_LSeries hθ hθ1 hC hw', LSeries_mu hw', F_eq hw1, zeta₁_eq hw1]
    simp only [Pi.zero_apply]
    field_simp
    ring
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

/-- `ψ(x) = x + O(x^{1/2 + ε})` ⟹ `M(x) = O(x^{1/2 + ε})` (via RH: as duas hipóteses fracas, a de von Koch e a de
Littlewood, ligadas pelo núcleo). -/
theorem mertens_of_vonKoch (h : VonKochFraco) : Mertens.MertensFraco :=
  Mertens.mertens_of_RH (RH_of_psi h)

end ATK.ZeroClasses.VonKoch

#print axioms ATK.ZeroClasses.VonKoch.C_nonneg
#print axioms ATK.ZeroClasses.VonKoch.norm_gA_le
#print axioms ATK.ZeroClasses.VonKoch.summable_gA
#print axioms ATK.ZeroClasses.VonKoch.differentiableAt_GA
#print axioms ATK.ZeroClasses.VonKoch.GA_eq_LSeries
#print axioms ATK.ZeroClasses.VonKoch.zero_de_edo
#print axioms ATK.ZeroClasses.VonKoch.E_succ
#print axioms ATK.ZeroClasses.VonKoch.LSeriesSummable_cL
#print axioms ATK.ZeroClasses.VonKoch.LSeries_cL
#print axioms ATK.ZeroClasses.VonKoch.zeroFree_of_psi
#print axioms ATK.ZeroClasses.VonKoch.RH_of_psi
#print axioms ATK.ZeroClasses.VonKoch.zeroFree_of_mertens
#print axioms ATK.ZeroClasses.VonKoch.mertens_of_vonKoch
