import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# Bohr–Landau, passo 1 — contagem de zeros por Jensen, em forma de média

* `sum_divisor_mul_log_le`: para `f` analítica em `closedBall c R`, `f c ≠ 0`, `0 < r < R`,
  `(∑ᶠ u, divisor f (closedBall c r) u) · log(R/r) ≤ circleAverage (log ‖f‖) c R − log ‖f c‖`
  (a desigualdade de Jensen com a **média** no lugar do máximo — `AnalyticOnNhd.sum_divisor_le`
  da Mathlib usa o máximo, que aqui não serve);
* `ncard_le_sum_divisor`: um conjunto finito de zeros de ordem finita conta no máximo a soma dos
  divisores;
* `zeta_order_ne_top`: a ordem de `ζ` em qualquer `u ≠ 1` é finita (ζ não é localmente nula);
* **`ncard_zeros_zeta_le`**: se `1 ∉ closedBall c R` e `ζ(c) ≠ 0`, todo conjunto finito `S` de
  zeros de `ζ` em `closedBall c r` satisfaz `#S · log(R/r) ≤ circleAverage (log‖ζ‖) c R − log‖ζ(c)‖`.
-/

open Metric Real Filter Topology MeromorphicOn

namespace ATK.BLJensen

/-- **Jensen em média.** -/
theorem sum_divisor_mul_log_le {c : ℂ} {r R : ℝ} {f : ℂ → ℂ} (r_pos : 0 < r) (r_lt_R : r < R)
    (h₁f : AnalyticOnNhd ℂ f (closedBall c R)) (h₂f : f c ≠ 0) :
    (∑ᶠ u, (divisor f (closedBall c r) u : ℝ)) * Real.log (R / r) ≤
      circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖ := by
  have hR : 0 < R := r_pos.trans r_lt_R
  have habs : |R| = R := abs_of_pos hR
  have h₁f' : AnalyticOnNhd ℂ f (closedBall c |R|) := by rw [habs]; exact h₁f
  have jensen := h₁f'.circleAverage_log_norm hR.ne' h₂f
  rw [habs] at jensen
  rw [jensen, add_sub_cancel_right, finsum_mul]
  · refine finsum_le_finsum ?_ ?_ fun u ↦ ?_
    · exact ((divisor f (closedBall c r)).finiteSupport (isCompact_closedBall ..)).subset
        fun _ h ↦ by
          simp only [Function.mem_support, ne_eq] at h ⊢
          intro h'; exact h (by rw [h']; simp)
    · exact ((divisor f (closedBall c R)).finiteSupport (isCompact_closedBall ..)).subset
        fun _ h ↦ by
          simp only [Function.mem_support, ne_eq] at h ⊢
          intro h'; exact h (by rw [h']; simp)
    · by_cases h1 : u ∈ closedBall c R
      · by_cases h2 : u ∈ closedBall c r
        · have hsub : AnalyticOnNhd ℂ f (closedBall c r) :=
            h₁f.mono (closedBall_subset_closedBall r_lt_R.le)
          rw [hsub.divisor_apply h2, h₁f.divisor_apply h1]
          by_cases h3 : u = c
          · rw [h3, (h₁f c (by simp [hR.le])).analyticOrderAt_eq_zero.mpr h₂f]
            simp
          have hpos : 0 < ‖c - u‖ := by
            rw [norm_pos_iff, sub_ne_zero]; exact fun h => h3 h.symm
          have hle : ‖c - u‖ ≤ r := by
            have := mem_closedBall.mp h2
            rw [dist_eq_norm] at this
            rwa [norm_sub_rev]
          have hd : (0 : ℝ) ≤ (((analyticOrderAt f u).map (↑)).untop₀ : ℤ) := by
            have := h₁f.divisor_nonneg u
            rw [h₁f.divisor_apply h1] at this
            exact_mod_cast this
          refine mul_le_mul_of_nonneg_left ?_ hd
          rw [show R * ‖c - u‖⁻¹ = R / ‖c - u‖ by ring]
          exact Real.log_le_log (div_pos hR r_pos) (div_le_div_of_nonneg_left hR.le hpos hle)
        · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h2]
          simp only [Int.cast_zero, zero_mul]
          refine mul_nonneg (by exact_mod_cast h₁f.divisor_nonneg u) ?_
          simp only [mem_closedBall, dist_eq_norm', not_le] at h1 h2
          have hpos : 0 < ‖c - u‖ := r_pos.trans h2
          rw [show R * ‖c - u‖⁻¹ = R / ‖c - u‖ by ring]
          apply Real.log_nonneg
          rw [le_div_iff₀ hpos, one_mul]; exact h1
      · have h2 : u ∉ closedBall c r := fun h => h1 (closedBall_subset_closedBall r_lt_R.le h)
        rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h2,
          Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h1]
        simp

/-- Um conjunto finito de zeros de ordem finita conta no máximo a soma dos divisores. -/
theorem ncard_le_sum_divisor {c : ℂ} {r : ℝ} {f : ℂ → ℂ} {S : Set ℂ} (hS : S.Finite)
    (hSb : S ⊆ closedBall c r) (h₁f : AnalyticOnNhd ℂ f (closedBall c r))
    (hz : ∀ u ∈ S, f u = 0) (hfin : ∀ u ∈ S, analyticOrderAt f u ≠ ⊤) :
    (S.ncard : ℝ) ≤ ∑ᶠ u, (divisor f (closedBall c r) u : ℝ) := by
  set d : ℂ → ℝ := fun u => (divisor f (closedBall c r) u : ℝ) with hd
  have hsupp : (Function.support d).Finite :=
    ((divisor f (closedBall c r)).finiteSupport (isCompact_closedBall ..)).subset fun u h => by
      simp only [Function.mem_support, ne_eq, hd] at h ⊢
      intro h'; exact h (by rw [h']; simp)
  have hnn : ∀ u, 0 ≤ d u := fun u => by
    simp only [hd]; exact_mod_cast h₁f.divisor_nonneg u
  have hone : ∀ u ∈ S, 1 ≤ d u := by
    intro u hu
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hfin u hu)
    have hne : analyticOrderAt f u ≠ 0 :=
      (h₁f u (hSb hu)).analyticOrderAt_ne_zero.mpr (hz u hu)
    have hn0 : n ≠ 0 := by
      intro h; apply hne; rw [← hn, h]; rfl
    simp only [hd]
    rw [h₁f.divisor_apply (hSb hu), ← hn]
    simp only [ENat.map_natCast, WithTop.untop₀_coe]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hSs : S ⊆ Function.support d := fun u hu => by
    simp only [Function.mem_support]; linarith [hone u hu]
  rw [finsum_eq_sum_of_support_subset d (s := hsupp.toFinset) (by simp)]
  calc (S.ncard : ℝ) = ∑ u ∈ hS.toFinset, (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Set.ncard_eq_toFinset_card S hS]
    _ ≤ ∑ u ∈ hS.toFinset, d u := Finset.sum_le_sum fun u hu => hone u (by simpa using hu)
    _ ≤ ∑ u ∈ hsupp.toFinset, d u :=
        Finset.sum_le_sum_of_subset_of_nonneg (by
          intro u hu; simp only [Set.Finite.mem_toFinset] at hu ⊢; exact hSs hu)
          fun u _ _ => hnn u

/-- A ordem de `ζ` em `u ≠ 1` é finita. -/
theorem zeta_order_ne_top {u : ℂ} (hu : u ≠ 1) : analyticOrderAt riemannZeta u ≠ ⊤ := by
  intro h
  have hev : riemannZeta =ᶠ[𝓝 u] 0 := by
    have := analyticOrderAt_eq_top.mp h
    filter_upwards [this] with z hz; simpa using hz
  have heq := analyticOn_riemannZeta.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    (by simpa using hu) hev
  have h2 : riemannZeta 2 = 0 := heq (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
  exact riemannZeta_ne_zero_of_one_le_re (by norm_num) h2

/-- **Contagem de zeros de `ζ` por Jensen.** -/
theorem ncard_zeros_zeta_le {c : ℂ} {r R : ℝ} {S : Set ℂ} (r_pos : 0 < r) (r_lt_R : r < R)
    (h1 : (1 : ℂ) ∉ closedBall c R) (hc : riemannZeta c ≠ 0) (hS : S.Finite)
    (hSb : S ⊆ closedBall c r) (hz : ∀ u ∈ S, riemannZeta u = 0) :
    (S.ncard : ℝ) * Real.log (R / r) ≤
      circleAverage (fun z => Real.log ‖riemannZeta z‖) c R - Real.log ‖riemannZeta c‖ := by
  have han : AnalyticOnNhd ℂ riemannZeta (closedBall c R) :=
    analyticOn_riemannZeta.mono fun z hz h => h1 (by rw [Set.mem_singleton_iff] at h; rwa [← h])
  have hanr : AnalyticOnNhd ℂ riemannZeta (closedBall c r) :=
    han.mono (closedBall_subset_closedBall r_lt_R.le)
  have hfin : ∀ u ∈ S, analyticOrderAt riemannZeta u ≠ ⊤ := fun u hu =>
    zeta_order_ne_top fun h => h1 (closedBall_subset_closedBall r_lt_R.le (h ▸ hSb hu))
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div r_pos).mpr r_lt_R)
  calc (S.ncard : ℝ) * Real.log (R / r)
      ≤ (∑ᶠ u, (divisor riemannZeta (closedBall c r) u : ℝ)) * Real.log (R / r) :=
        mul_le_mul_of_nonneg_right (ncard_le_sum_divisor hS hSb hanr hz hfin) hlog.le
    _ ≤ _ := sum_divisor_mul_log_le r_pos r_lt_R han hc

end ATK.BLJensen

#print axioms ATK.BLJensen.sum_divisor_mul_log_le
#print axioms ATK.BLJensen.ncard_le_sum_divisor
#print axioms ATK.BLJensen.zeta_order_ne_top
#print axioms ATK.BLJensen.ncard_zeros_zeta_le
