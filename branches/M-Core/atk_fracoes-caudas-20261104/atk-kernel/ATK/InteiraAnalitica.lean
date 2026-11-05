import ATK.EdreiInteira

/-!
# ATK — Funções inteiras dadas por coeficientes: analiticidade, Cauchy, zeros, módulo máximo

Ferramentas para `ATK/HadamardGenero0.lean`, sobre `ATK.Edrei.Inteira` / `ATK.Edrei.ev`:

* `hasFPowerSeries_ev`, `ev_differentiable`: `ev c` é inteira (série `ofScalars`, raio `⊤`);
* `iteratedDeriv_ev`: `g⁽ⁿ⁾(0) = n!·cₙ`; `coef_le`: **desigualdade de Cauchy** `|cₙ|Rⁿ ≤ max_{|w|=R}|ev c w|`;
* `zeros_finite`, `existe_zero_min`: num disco fechado há só finitos zeros, e se há algum zero há um de
  módulo mínimo;
* `ev_eq_zero_iff_sub`, `ev_shift`: manipulações de séries.
-/

open Complex Filter Topology Metric Set
open scoped Nat

namespace ATK.InteiraAn

open ATK.Edrei

/-- A série formal de `ev c`. -/
noncomputable def serie (c : ℕ → ℝ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ fun n => (c n : ℂ)

theorem serie_radius {c : ℕ → ℝ} (hc : Inteira c) : (serie c).radius = ⊤ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  refine (serie c).le_radius_of_summable_norm ?_
  refine (hc r r.coe_nonneg).congr fun n => ?_
  simp [serie, FormalMultilinearSeries.ofScalars_norm, Complex.norm_real]

theorem serie_sum (c : ℕ → ℝ) (w : ℂ) : (serie c).sum w = ev c w := by
  simp only [FormalMultilinearSeries.sum, serie, FormalMultilinearSeries.ofScalars_apply_eq, ev,
    smul_eq_mul]

theorem hasFPowerSeries_ev {c : ℕ → ℝ} (hc : Inteira c) :
    HasFPowerSeriesOnBall (ev c) (serie c) 0 ⊤ := by
  have h := (serie c).hasFPowerSeriesOnBall (by rw [serie_radius hc]; exact ENNReal.zero_lt_top)
  rw [serie_radius hc] at h
  have e : (serie c).sum = ev c := funext (serie_sum c)
  rwa [e] at h

theorem ev_differentiable {c : ℕ → ℝ} (hc : Inteira c) : Differentiable ℂ (ev c) := by
  intro w
  have h := (hasFPowerSeries_ev hc).differentiableOn
  exact (h w (by simp [Metric.mem_eball, edist_lt_top])).differentiableAt
    (Metric.isOpen_eball.mem_nhds (by simp [Metric.mem_eball, edist_lt_top]))

theorem ev_analyticOnNhd {c : ℕ → ℝ} (hc : Inteira c) : AnalyticOnNhd ℂ (ev c) univ :=
  fun w _ => (ev_differentiable hc).analyticAt w

theorem iteratedDeriv_ev {c : ℕ → ℝ} (hc : Inteira c) (n : ℕ) :
    iteratedDeriv n (ev c) 0 = n ! * c n := by
  have h := (hasFPowerSeries_ev hc).factorial_smul 1 n
  rw [iteratedDeriv_eq_iteratedFDeriv, ← h]
  simp [serie, FormalMultilinearSeries.ofScalars_apply_eq]

/-- **Desigualdade de Cauchy**: `|cₙ|·Rⁿ ≤ C` se `|ev c| ≤ C` na circunferência `|w| = R`. -/
theorem coef_le {c : ℕ → ℝ} (hc : Inteira c) {R C : ℝ} (hR : 0 < R)
    (hC : ∀ w ∈ sphere (0 : ℂ) R, ‖ev c w‖ ≤ C) (n : ℕ) : |c n| * R ^ n ≤ C := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
    (ev_differentiable hc).diffContOnCl hC
  rw [iteratedDeriv_ev hc, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs] at h
  have hf : (0 : ℝ) < n ! := by exact_mod_cast n.factorial_pos
  have hRn : 0 < R ^ n := pow_pos hR n
  rw [mul_div_assoc] at h
  have := le_of_mul_le_mul_left h hf
  rwa [le_div_iff₀ hRn] at this

/-- Zeros num disco fechado: só finitos. -/
theorem zeros_finite {c : ℕ → ℝ} (hc : Inteira c) (h0 : c 0 ≠ 0) (R : ℝ) :
    (closedBall (0 : ℂ) R ∩ {w | ev c w = 0}).Finite := by
  have hne : ev c 0 ≠ 0 := by rw [ev_zero]; exact_mod_cast h0
  have hcod := (ev_analyticOnNhd hc).preimage_zero_mem_codiscrete hne
  have hK := (isCompact_closedBall (0 : ℂ) R).finite_sdiff_of_mem_codiscreteWithin
    (Filter.codiscreteWithin_mono (subset_univ _) hcod)
  refine hK.subset fun w ⟨hw1, hw2⟩ => ⟨hw1, ?_⟩
  simp only [mem_preimage, mem_compl_iff, mem_singleton_iff, not_not]
  exact hw2

/-- **Zero de módulo mínimo**: se `ev c` tem um zero, tem um zero de módulo mínimo. -/
theorem existe_zero_min {c : ℕ → ℝ} (hc : Inteira c) (h0 : c 0 ≠ 0) {w₀ : ℂ} (hw₀ : ev c w₀ = 0) :
    ∃ w, ev c w = 0 ∧ ∀ v, ev c v = 0 → ‖w‖ ≤ ‖v‖ := by
  set Z := closedBall (0 : ℂ) ‖w₀‖ ∩ {w | ev c w = 0} with hZ
  have hfin := zeros_finite hc h0 ‖w₀‖
  have hne : Z.Nonempty := ⟨w₀, by simp [hZ, hw₀]⟩
  obtain ⟨w, hwZ, hmin⟩ := Set.exists_min_image Z (fun w => ‖w‖) hfin hne
  refine ⟨w, hwZ.2, fun v hv => ?_⟩
  by_cases hvZ : ‖v‖ ≤ ‖w₀‖
  · exact hmin v ⟨by simpa using hvZ, hv⟩
  · have : ‖w‖ ≤ ‖w₀‖ := by simpa using hwZ.1
    push_neg at hvZ
    linarith

end ATK.InteiraAn

#print axioms ATK.InteiraAn.serie_radius
#print axioms ATK.InteiraAn.serie_sum
#print axioms ATK.InteiraAn.hasFPowerSeries_ev
#print axioms ATK.InteiraAn.ev_differentiable
#print axioms ATK.InteiraAn.ev_analyticOnNhd
#print axioms ATK.InteiraAn.iteratedDeriv_ev
#print axioms ATK.InteiraAn.coef_le
#print axioms ATK.InteiraAn.zeros_finite
#print axioms ATK.InteiraAn.existe_zero_min
