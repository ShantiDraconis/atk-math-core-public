import ATK.ZeroClasses.QuasiRH

/-!
# A abscissa de convergência de `Σ μ(n)n^{−s}` e de `Σ (Λ(n) − 1)n^{−s}` é `Θ = sup Re ρ` (rodada 62)

Para `½ ≤ θ < 1`, com `SemZeros θ` (`ζ ≠ 0` em `Re s > θ`, rodada 57):

* **`semZeros_iff_mu`**: `SemZeros θ ⟺ Σ μ(n)n^{−s}` converge em todo `Re s > θ`; e então converge para `1/ζ(s)`
  (`tendsto_mu`);
* **`semZeros_iff_cL`**: o mesmo para `Σ (Λ(n) − 1)n^{−s}`, que converge para `−ζ′/ζ(s) − ζ(s)` (`tendsto_cL`);
* **`rh_iff_mu`**, **`rh_iff_cL`**: **RH ⟺ `Σ μ(n)n^{−s}` converge em `Re s > ½`** (Littlewood) ⟺ o mesmo para
  `Λ − 1`.

Ou seja: a abscissa de convergência de `Σ μ(n)n^{−s}` (e de `Σ (Λ(n) − 1)n^{−s}`) é `max(½, Θ)`.

A ida usa o Littlewood geral da rodada 56 (`cota_gen`, aqui `tendsto_gen`) para os coeficientes deslocados
`μ(n)n^{−d}` (`escala`) e `(Λ(n) − 1)/((1/d + 1)n^d)` (`fco`), com as cotas `|1/ζ|, |ζ′/ζ + ζ| ≪ |t|^η` da rodada 57.
A volta: convergência num real `σ` dá somas parciais limitadas, e a somação por partes (`abel_cota`) dá
`M(N), ψ(N) − N = O(N^σ)`, logo `ζ ≠ 0` em `Re s > σ` (rodada 55).

Classificação (rodada 62): **reformulação**. RH continua OPEN_MATH.
-/

open Complex Filter Topology

namespace ATK.ZeroClasses.Abscissa

open ATK.ZeroClasses.QuasiRH (SemZeros escala norm_escala_le term_escala LSeries_escala norm_F_le norm_H_le
  differentiableAt_F differentiableAt_Hf semZeros_meio_iff M_eq_sum)
open ATK.ZeroClasses.VonKochRH (cota_gen abel_cota fco norm_fco_le term_fco LSeries_fco Hf Hf_eq E_eq_sum)
open ATK.ZeroClasses.LittlewoodMu (mu norm_mu_le LSeries_mu)
open ATK.ZeroClasses.PerronD (xN)
open ATK.RHLogZeta (F F_eq)
open ATK.ZeroClasses.VonKoch (cL E zeroFree_of_mertens zeroFree_of_psi)

/-- A série `Σ a(n)n^{−s}` converge (somas parciais `Σ_{n ≤ N}`). -/
def Converge (a : ℕ → ℂ) (s : ℂ) : Prop :=
  ∃ L : ℂ, Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), LSeries.term a s n) atTop (𝓝 L)

/-! ## 1. Littlewood geral ⟹ convergência -/

theorem tendsto_gen {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {Φ : ℂ → ℂ}
    (hΦd : ∀ u : ℂ, 1 / 2 < u.re → DifferentiableAt ℂ Φ u) (hΦL : ∀ u : ℂ, 1 < u.re → LSeries f u = Φ u)
    {ε CF : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hCF0 : 0 ≤ CF)
    (hCF : ∀ u : ℂ, 1 / 2 + ε / 2 ≤ u.re → ‖Φ u‖ ≤ CF * (1 + |u.im|) ^ (ε / 16)) {w : ℂ}
    (hw : w.re = 1 / 2 + ε) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), LSeries.term f w n) atTop (𝓝 (Φ w)) := by
  obtain ⟨K, -, hK⟩ := cota_gen hf hΦd hΦL hε hε1 hCF0 hCF
  have hx : Tendsto (fun N : ℕ => xN N) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hθ : Tendsto (fun N : ℕ => xN N ^ (-(ε / 4))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp hx
  have hlim : Tendsto (fun N : ℕ => K * ((1 + |w.im|) ^ (ε / 16) * xN N ^ (-(ε / 4)))) atTop (𝓝 0) := by
    simpa using (hθ.const_mul ((1 + |w.im|) ^ (ε / 16))).const_mul K
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact hK w hw N hN

/-- Os parâmetros: para `θ < Re s`, `ε = min((Re s − θ)/2, 1)` e `d = Re s − ½ − ε > 0`. -/
theorem parametros {θ : ℝ} (hθ : 1 / 2 ≤ θ) {s : ℂ} (hs : θ < s.re) :
    ∃ ε d : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 < d ∧ θ + ε / 2 ≤ 1 / 2 + ε / 2 + d ∧ θ < 1 / 2 + d ∧
      (s - d).re = 1 / 2 + ε := by
  refine ⟨min ((s.re - θ) / 2) 1, s.re - 1 / 2 - min ((s.re - θ) / 2) 1, lt_min (by linarith) one_pos,
    min_le_right _ _, ?_, ?_, ?_, ?_⟩
  · have := min_le_left ((s.re - θ) / 2) 1; linarith
  · have := min_le_left ((s.re - θ) / 2) 1; linarith
  · have := min_le_left ((s.re - θ) / 2) 1; linarith
  · simp; ring

/-- **Sob `SemZeros θ`, `Σ μ(n)n^{−s} → 1/ζ(s)` em `Re s > θ`** (`F = (s − 1)/ζ₁ = 1/ζ`). -/
theorem tendsto_mu {θ : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) {s : ℂ} (hs : θ < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), LSeries.term mu s n) atTop (𝓝 (F s)) := by
  obtain ⟨ε, d, hε, hε1, hd, hεd, hθd, hw⟩ := parametros hθ hs
  obtain ⟨CF, hCF0, hCF⟩ := norm_F_le hZ hθ hθ1 (δ := ε / 2) (η := ε / 16) (by linarith) (by linarith)
    (by linarith)
  have hΦd : ∀ u : ℂ, 1 / 2 < u.re → DifferentiableAt ℂ (fun u => F (u + d)) u := by
    intro u hu
    have hre : θ < (u + (d : ℂ)).re := by simp; linarith
    exact (differentiableAt_F hZ hre).comp u (differentiableAt_id.add_const _)
  have hΦL : ∀ u : ℂ, 1 < u.re → LSeries (escala mu d) u = (fun u => F (u + d)) u := by
    intro u hu
    have hre : 1 < (u + (d : ℂ)).re := by simp; linarith
    rw [LSeries_escala, LSeries_mu hre]
  have hCF' : ∀ u : ℂ, 1 / 2 + ε / 2 ≤ u.re →
      ‖(fun u => F (u + d)) u‖ ≤ CF * (1 + |u.im|) ^ (ε / 16) := by
    intro u hu
    have hre : θ + ε / 2 ≤ (u + (d : ℂ)).re := by simp; linarith
    have h := hCF _ hre
    simpa using h
  have h := tendsto_gen (norm_escala_le norm_mu_le hd) hΦd hΦL hε hε1 hCF0.le hCF' hw
  simp only [term_escala, sub_add_cancel] at h
  exact h

/-- **Sob `SemZeros θ`, `Σ (Λ(n) − 1)n^{−s} → −ζ′/ζ(s) − ζ(s)` em `Re s > θ`**. -/
theorem tendsto_cL {θ : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) {s : ℂ} (hs : θ < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), LSeries.term cL s n) atTop (𝓝 (Hf s)) := by
  obtain ⟨ε, d, hε, hε1, hd, hεd, hθd, hw⟩ := parametros hθ hs
  have hB0 : (0 : ℝ) < 1 / d + 1 := by positivity
  have hBc : ((1 / d + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hB0.ne'
  obtain ⟨CH, hCH0, hCH⟩ := norm_H_le hZ hθ hθ1 (δ := ε / 2) (η := ε / 16) (by linarith) (by linarith)
    (by linarith)
  have hΦd : ∀ u : ℂ, 1 / 2 < u.re →
      DifferentiableAt ℂ (fun u => ((1 / d + 1 : ℝ) : ℂ)⁻¹ * Hf (u + d)) u := by
    intro u hu
    have hre : θ < (u + (d : ℂ)).re := by simp; linarith
    exact (differentiableAt_const _).mul ((differentiableAt_Hf hZ hre).comp u (differentiableAt_id.add_const _))
  have hΦL : ∀ u : ℂ, 1 < u.re →
      LSeries (fco d) u = (fun u => ((1 / d + 1 : ℝ) : ℂ)⁻¹ * Hf (u + d)) u :=
    fun u hu => LSeries_fco hd hu
  have hCF' : ∀ u : ℂ, 1 / 2 + ε / 2 ≤ u.re →
      ‖(fun u => ((1 / d + 1 : ℝ) : ℂ)⁻¹ * Hf (u + d)) u‖ ≤ CH / (1 / d + 1) * (1 + |u.im|) ^ (ε / 16) := by
    intro u hu
    have hre : θ + ε / 2 ≤ (u + (d : ℂ)).re := by simp; linarith
    have h := hCH _ hre
    have him : (u + (d : ℂ)).im = u.im := by simp
    rw [him] at h
    simp only
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB0]
    calc (1 / d + 1)⁻¹ * ‖Hf (u + (d : ℂ))‖ ≤ (1 / d + 1)⁻¹ * (CH * (1 + |u.im|) ^ (ε / 16)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = CH / (1 / d + 1) * (1 + |u.im|) ^ (ε / 16) := by ring
  have h := tendsto_gen (norm_fco_le hd) hΦd hΦL hε hε1 (by positivity) hCF' hw
  have h2 := h.const_mul ((1 / d + 1 : ℝ) : ℂ)
  simp only [sub_add_cancel] at h2
  rw [← mul_assoc, mul_inv_cancel₀ hBc, one_mul] at h2
  refine h2.congr fun N => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [term_fco hd, ← mul_assoc, mul_inv_cancel₀ hBc, one_mul, sub_add_cancel]

/-! ## 2. Convergência num real ⟹ cota de `M` e de `ψ` -/

theorem limitada_of_converge {a : ℕ → ℂ} {s : ℂ} (h : Converge a s) :
    ∃ B : ℝ, ∀ N : ℕ, ‖∑ n ∈ Finset.range (N + 1), LSeries.term a s n‖ ≤ B := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto _ hL)
  exact ⟨B, fun N => hB _ ⟨N, rfl⟩⟩

theorem mertens_of_converge {σ : ℝ} (hσ : 0 < σ) (h : Converge mu (σ : ℂ)) :
    ∃ C : ℝ, ∀ N : ℕ, |ATK.ZeroClasses.Mertens.M N| ≤ C * ((N : ℝ) + 1) ^ σ := by
  obtain ⟨B, hB⟩ := limitada_of_converge h
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  refine ⟨2 * B, fun N => ?_⟩
  have hn := congrArg norm (M_eq_sum σ N)
  rw [Complex.norm_real, Real.norm_eq_abs] at hn
  rw [hn]
  refine (abel_cota hσ hB N).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Real.rpow_le_rpow (Nat.cast_nonneg N) (by linarith) hσ.le

theorem psi_of_converge {σ : ℝ} (hσ : 0 < σ) (h : Converge cL (σ : ℂ)) :
    ∃ C : ℝ, ∀ N : ℕ, |Chebyshev.psi N - N| ≤ C * ((N : ℝ) + 1) ^ σ := by
  obtain ⟨B, hB⟩ := limitada_of_converge h
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  refine ⟨2 * B, fun N => ?_⟩
  have hn := congrArg norm (E_eq_sum σ N)
  rw [Complex.norm_real, Real.norm_eq_abs] at hn
  show |E N| ≤ _
  rw [hn]
  refine (abel_cota hσ hB N).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Real.rpow_le_rpow (Nat.cast_nonneg N) (by linarith) hσ.le

/-! ## 3. As equivalências -/

/-- **`ζ ≠ 0` em `Re s > θ` ⟺ `Σ μ(n)n^{−s}` converge em `Re s > θ`** (`½ ≤ θ < 1`). -/
theorem semZeros_iff_mu {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    SemZeros θ ↔ ∀ s : ℂ, θ < s.re → Converge mu s := by
  refine ⟨fun hZ s hs => ⟨F s, tendsto_mu hZ hθ hθ1 hs⟩, fun h s hs => ?_⟩
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  obtain ⟨C, hC⟩ := mertens_of_converge (σ := (θ + s.re) / 2) (by linarith)
    (h _ (by simp; linarith))
  exact zeroFree_of_mertens (θ := (θ + s.re) / 2) (by linarith) (by linarith) hC (by linarith)

/-- **`ζ ≠ 0` em `Re s > θ` ⟺ `Σ (Λ(n) − 1)n^{−s}` converge em `Re s > θ`** (`½ ≤ θ < 1`). -/
theorem semZeros_iff_cL {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    SemZeros θ ↔ ∀ s : ℂ, θ < s.re → Converge cL s := by
  refine ⟨fun hZ s hs => ⟨Hf s, tendsto_cL hZ hθ hθ1 hs⟩, fun h s hs => ?_⟩
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  obtain ⟨C, hC⟩ := psi_of_converge (σ := (θ + s.re) / 2) (by linarith) (h _ (by simp; linarith))
  exact zeroFree_of_psi (θ := (θ + s.re) / 2) (by linarith) (by linarith) hC (by linarith)

/-- **RH ⟺ `Σ μ(n)n^{−s}` converge em `Re s > ½`** (Littlewood). -/
theorem rh_iff_mu : RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → Converge mu s :=
  semZeros_meio_iff.symm.trans (semZeros_iff_mu (by norm_num) (by norm_num))

/-- **RH ⟺ `Σ (Λ(n) − 1)n^{−s}` converge em `Re s > ½`**. -/
theorem rh_iff_cL : RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → Converge cL s :=
  semZeros_meio_iff.symm.trans (semZeros_iff_cL (by norm_num) (by norm_num))

/-- Sob RH, `Σ μ(n)n^{−s} → 1/ζ(s)` em todo `Re s > ½`, `s ≠ 1` (em `s = 1` o limite é `0`). -/
theorem mu_tendsto_inv_zeta (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1), LSeries.term mu s n) atTop
      (𝓝 (riemannZeta s)⁻¹) := by
  rw [← F_eq hs1]
  exact tendsto_mu (semZeros_meio_iff.mpr hRH) le_rfl (by norm_num) hs

end ATK.ZeroClasses.Abscissa

#print axioms ATK.ZeroClasses.Abscissa.tendsto_gen
#print axioms ATK.ZeroClasses.Abscissa.parametros
#print axioms ATK.ZeroClasses.Abscissa.tendsto_mu
#print axioms ATK.ZeroClasses.Abscissa.tendsto_cL
#print axioms ATK.ZeroClasses.Abscissa.limitada_of_converge
#print axioms ATK.ZeroClasses.Abscissa.mertens_of_converge
#print axioms ATK.ZeroClasses.Abscissa.psi_of_converge
#print axioms ATK.ZeroClasses.Abscissa.semZeros_iff_mu
#print axioms ATK.ZeroClasses.Abscissa.semZeros_iff_cL
#print axioms ATK.ZeroClasses.Abscissa.rh_iff_mu
#print axioms ATK.ZeroClasses.Abscissa.rh_iff_cL
#print axioms ATK.ZeroClasses.Abscissa.mu_tendsto_inv_zeta
