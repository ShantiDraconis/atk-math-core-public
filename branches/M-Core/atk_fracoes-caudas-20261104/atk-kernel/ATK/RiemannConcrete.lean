import ATK.IndeterminacyStates

/-!
# ATK — Propriedades provadas da família concreta de Báez-Duarte (rumo à obrigação O1)

Fatos **incondicionais** sobre `D_N = inf_c ‖χ − Σ_{k≤N} c_k ρ_k‖²` (definido em
`ATK.Conditional.Riemann`, com `ρ_k(t) = {1/(k t)}`), verificados pelo kernel:

* `residualSq_extend`: acrescentar um gerador com coeficiente 0 não muda o resíduo;
* `DN_antitone`: `D_{N+1} ≤ D_N` — a sequência concreta é decrescente;
* `DN_le_DN_zero`, `DN_zero_le_one`: `D_N ≤ D_0 ≤ ‖χ‖² = 1`;
* `DN_tendsto_iInf`: `D_N` **converge**, e o limite é `D_∞ = inf_N D_N`;
* `O1_iff_iInf_zero`: a obrigação O1 (`D_N → 0`) equivale a `D_∞ = 0`;
* `O1_iff_dissipacao`: e equivale à dissipação total `Σ (D_n − D_{n+1}) = D_0`.

O que continua aberto é exatamente `D_∞ = 0` (equivalente a RH pelo critério de Nyman–Beurling–
Báez-Duarte). Nada aqui assume RH.
-/

open Filter Topology Set MeasureTheory

namespace ATK.RiemannConcrete

open ATK.Conditional.Riemann

theorem residualSq_nonneg (N : ℕ) (c : Fin N → ℝ) : 0 ≤ residualSq N c :=
  integral_nonneg fun _ => sq_nonneg _

theorem DN_le_residualSq (N : ℕ) (c : Fin N → ℝ) : DN N ≤ residualSq N c :=
  ciInf_le ⟨0, by rintro _ ⟨c, rfl⟩; exact residualSq_nonneg N c⟩ c

/-- Acrescentar o gerador `ρ_{N+1}` com coeficiente 0 não muda o resíduo. -/
theorem residualSq_extend (N : ℕ) (c : Fin N → ℝ) :
    residualSq (N + 1) (Fin.snoc c 0) = residualSq N c := by
  unfold residualSq
  congr 1
  funext t
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- **`D_N` é decrescente.** -/
theorem DN_antitone : Antitone DN := by
  refine antitone_nat_of_succ_le fun N => le_ciInf fun c => ?_
  exact (DN_le_residualSq (N + 1) (Fin.snoc c 0)).trans_eq (residualSq_extend N c)

theorem DN_le_DN_zero (N : ℕ) : DN N ≤ DN 0 := DN_antitone (Nat.zero_le N)

/-- `D_0 = ‖χ‖² ≤ 1`. -/
theorem DN_zero_le_one : DN 0 ≤ 1 := by
  refine (DN_le_residualSq 0 Fin.elim0).trans (le_of_eq ?_)
  unfold residualSq chi
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
  have hsq : (fun t : ℝ => (Set.indicator (Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) t) ^ 2) =
      Set.indicator (Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [ht]
  rw [hsq, integral_indicator measurableSet_Ioc]
  simp only [integral_const, smul_eq_mul, mul_one]
  rw [Measure.restrict_restrict measurableSet_Ioc]
  have : Ioc (0 : ℝ) 1 ∩ Ioi 0 = Ioc 0 1 := by
    ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]; constructor
    · rintro ⟨h, -⟩; exact h
    · intro h; exact ⟨h, h.1⟩
  rw [this]
  simp

theorem DN_le_one (N : ℕ) : DN N ≤ 1 := (DN_le_DN_zero N).trans DN_zero_le_one

/-- **`D_N` converge**, e o limite é `D_∞ = inf_N D_N`. -/
theorem DN_tendsto_iInf : Tendsto DN atTop (𝓝 (⨅ N, DN N)) :=
  tendsto_atTop_ciInf DN_antitone ⟨0, by rintro _ ⟨N, rfl⟩; exact DN_nonneg N⟩

/-- **O1 ⟺ `D_∞ = 0`.** -/
theorem O1_iff_iInf_zero : Tendsto DN atTop (𝓝 0) ↔ ⨅ N, DN N = 0 := by
  constructor
  · intro h; exact tendsto_nhds_unique DN_tendsto_iInf h
  · intro h; rw [← h]; exact DN_tendsto_iInf

/-- **O1 ⟺ dissipação total** da sequência concreta. -/
theorem O1_iff_dissipacao :
    HasSum (fun n => DN n - DN (n + 1)) (DN 0) ↔ Tendsto DN atTop (𝓝 0) :=
  ATK.IndeterminacyStates.dissipacao_iff_limite_zero DN_antitone

/-- RH pela ponte de Báez-Duarte a partir de `D_∞ = 0`. -/
theorem riemann_de_iInf_zero (hB : BaezDuarteCriterion) (h : ⨅ N, DN N = 0) :
    RiemannHypothesis :=
  hB (O1_iff_iInf_zero.mpr h)

end ATK.RiemannConcrete

#print axioms ATK.RiemannConcrete.residualSq_nonneg
#print axioms ATK.RiemannConcrete.DN_le_residualSq
#print axioms ATK.RiemannConcrete.residualSq_extend
#print axioms ATK.RiemannConcrete.DN_antitone
#print axioms ATK.RiemannConcrete.DN_le_DN_zero
#print axioms ATK.RiemannConcrete.DN_zero_le_one
#print axioms ATK.RiemannConcrete.DN_le_one
#print axioms ATK.RiemannConcrete.DN_tendsto_iInf
#print axioms ATK.RiemannConcrete.O1_iff_iInf_zero
#print axioms ATK.RiemannConcrete.O1_iff_dissipacao
#print axioms ATK.RiemannConcrete.riemann_de_iInf_zero
