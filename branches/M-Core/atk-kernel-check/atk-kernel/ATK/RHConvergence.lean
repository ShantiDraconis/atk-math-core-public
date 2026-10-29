import ATK.Riemann

/-!
# ATK — Riemann, item R2 da agenda: D_N^{BD} converge

Sobre a distância CONCRETA de Báez-Duarte (`ATK.Riemann.bdDistSq`):
* `bdDistSq_succ_le` — D_{N+1} ≤ D_N (o espaço aumenta: estende-se c com coeficiente 0).
* `bdDistSq_antitone` — a sequência é monótona.
* `bdDistSq_converges` — D_N converge para D_∞ = inf_N D_N ≥ 0. Logo a soma telescópica
  S = Σ (D_{N-1} − D_N) = D_0 − D_∞ existe sempre.
* `rh_iff_limit_zero_of_criterion` — com o critério de Báez-Duarte como hipótese explícita,
  RH equivale a D_∞ = 0. Provar D_∞ = 0 continua ABERTO (é RH).
-/

namespace ATK.RHConvergence

open Filter Topology MeasureTheory ATK.Riemann

theorem bdDistSq_succ_le (n : ℕ) : bdDistSq (n + 1) ≤ bdDistSq n := by
  unfold bdDistSq
  apply le_ciInf
  intro c
  have hbdd : BddBelow (Set.range fun c' : Fin (n + 1) → ℝ =>
      ∫ t in Set.Ioi (0 : ℝ), (bdChi t - ∑ k : Fin (n + 1), c' k * bdRho (k.val + 1) t) ^ 2) :=
    ⟨0, by rintro _ ⟨c', rfl⟩; exact integral_nonneg fun _ => sq_nonneg _⟩
  refine (ciInf_le hbdd (Fin.snoc (α := fun _ => ℝ) c 0)).trans (le_of_eq ?_)
  congr 1
  funext t
  simp [Fin.sum_univ_castSucc]

theorem bdDistSq_antitone : Antitone bdDistSq :=
  antitone_nat_of_succ_le bdDistSq_succ_le

theorem bdDistSq_converges : Tendsto bdDistSq atTop (𝓝 (⨅ N, bdDistSq N)) :=
  tendsto_atTop_ciInf bdDistSq_antitone ⟨0, by rintro _ ⟨N, rfl⟩; exact bdDistSq_nonneg N⟩

theorem bdDistSq_limit_nonneg : 0 ≤ ⨅ N, bdDistSq N :=
  le_ciInf fun N => bdDistSq_nonneg N

theorem rh_iff_limit_zero_of_criterion
    (hCriterion : Tendsto bdDistSq atTop (𝓝 0) ↔ RiemannHypothesis) :
    RiemannHypothesis ↔ (⨅ N, bdDistSq N) = 0 := by
  rw [← hCriterion]
  constructor
  · intro h
    exact tendsto_nhds_unique bdDistSq_converges h
  · intro h
    rw [← h]
    exact bdDistSq_converges

end ATK.RHConvergence

#print axioms ATK.RHConvergence.bdDistSq_succ_le
#print axioms ATK.RHConvergence.bdDistSq_antitone
#print axioms ATK.RHConvergence.bdDistSq_converges
#print axioms ATK.RHConvergence.bdDistSq_limit_nonneg
#print axioms ATK.RHConvergence.rh_iff_limit_zero_of_criterion
