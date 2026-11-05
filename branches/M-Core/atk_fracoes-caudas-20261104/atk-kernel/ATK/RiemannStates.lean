import ATK.RiemannFaithful

/-!
# ATK — A classificação de 7 estados aplicada a `D_N`: restam exatamente dois estados

Aplicação da teoria de estados (`ATK.IndeterminacyStates`) à obrigação O1, usando somente fatos
**provados** sobre a família concreta (`RiemannConcrete`, `RiemannFaithful`):

* `estado_DN_dicotomia`: o germe de `D_N` (em `N → ∞`) está no estado `zero` ou no estado `finito`;
* `estado_DN_exclui`: os estados `+∞`, `−∞`, `oscila` e `foraDominio` estão **excluídos**;
* `limite_DN_em`: o limite existe e está em `[0, 1)` (porque `D_1 < 1`);
* `O1_iff_nao_finito`: O1 ⟺ `D_N` **não** está no estado `finito`.

Dos 7 estados, a classificação certificada deixa só `{zero, finito}`; a escolha entre eles é a
Hipótese de Riemann (pela ponte de Báez-Duarte) e continua aberta.
-/

open Filter Topology

namespace ATK.RiemannStates

open ATK.Conditional.Riemann ATK.RiemannConcrete ATK.RiemannFaithful ATK.IndeterminacyStates

theorem iInf_DN_nonneg : 0 ≤ ⨅ N, DN N := le_ciInf DN_nonneg

/-- `D_∞ = inf_N D_N ≤ D_1 < 1`. -/
theorem iInf_DN_lt_one : ⨅ N, DN N < 1 :=
  lt_of_le_of_lt (ciInf_le ⟨0, by rintro _ ⟨N, rfl⟩; exact DN_nonneg N⟩ 1) DN_one_lt_one

/-- **Dicotomia**: `D_N` está no estado `zero` ou no estado `finito`. -/
theorem estado_DN_dicotomia :
    Comporta atTop DN Estado7.zero ∨ Comporta atTop DN Estado7.finito := by
  by_cases h : ⨅ N, DN N = 0
  · left
    show Tendsto DN atTop (𝓝 0)
    rw [← h]
    exact DN_tendsto_iInf
  · right
    exact ⟨_, h, DN_tendsto_iInf⟩

theorem estado_DN_zero_iff : Comporta atTop DN Estado7.zero ↔ ⨅ N, DN N = 0 :=
  O1_iff_iInf_zero

theorem estado_DN_finito_iff : Comporta atTop DN Estado7.finito ↔ 0 < ⨅ N, DN N := by
  constructor
  · rintro ⟨L, hL, hT⟩
    have hLeq := tendsto_nhds_unique hT DN_tendsto_iInf
    rcases iInf_DN_nonneg.lt_or_eq with h | h
    · exact h
    · exact absurd (hLeq.trans h.symm) hL
  · intro h
    exact ⟨_, h.ne', DN_tendsto_iInf⟩

/-- Os estados `+∞`, `−∞`, `oscila` e `foraDominio` estão excluídos para `D_N`. -/
theorem estado_DN_exclui :
    ¬ Comporta atTop DN Estado7.maisInf ∧ ¬ Comporta atTop DN Estado7.menosInf ∧
      ¬ Comporta atTop DN Estado7.oscila ∧ ¬ Comporta atTop DN Estado7.foraDominio := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => h⟩
  · rcases estado_DN_dicotomia with h0 | h0
    · exact absurd (classificacao_exclusiva rfl rfl h0 h) (by decide)
    · exact absurd (classificacao_exclusiva rfl rfl h0 h) (by decide)
  · rcases estado_DN_dicotomia with h0 | h0
    · exact absurd (classificacao_exclusiva rfl rfl h0 h) (by decide)
    · exact absurd (classificacao_exclusiva rfl rfl h0 h) (by decide)
  · rcases estado_DN_dicotomia with h0 | h0
    · exact absurd (classificacao_exclusiva rfl rfl h0 h) (by decide)
    · exact absurd (classificacao_exclusiva rfl rfl h0 h) (by decide)

/-- Refinamento quantitativo: o limite de `D_N` existe e pertence a `[0, 1)`. -/
theorem limite_DN_em : ∃ L : ℝ, 0 ≤ L ∧ L < 1 ∧ Tendsto DN atTop (𝓝 L) :=
  ⟨_, iInf_DN_nonneg, iInf_DN_lt_one, DN_tendsto_iInf⟩

/-- **O1 na linguagem dos 7 estados**: `D_N → 0` ⟺ `D_N` não está no estado `finito`. -/
theorem O1_iff_nao_finito : Tendsto DN atTop (𝓝 0) ↔ ¬ Comporta atTop DN Estado7.finito := by
  rw [estado_DN_finito_iff, O1_iff_iInf_zero, not_lt]
  exact ⟨fun h => h.le, fun h => le_antisymm h iInf_DN_nonneg⟩

/-- Com a ponte de Báez-Duarte: excluir o estado `finito` para `D_N` dá RH. -/
theorem riemann_de_nao_finito (hB : BaezDuarteCriterion)
    (h : ¬ Comporta atTop DN Estado7.finito) : RiemannHypothesis :=
  hB (O1_iff_nao_finito.mpr h)

end ATK.RiemannStates

#print axioms ATK.RiemannStates.iInf_DN_nonneg
#print axioms ATK.RiemannStates.iInf_DN_lt_one
#print axioms ATK.RiemannStates.estado_DN_dicotomia
#print axioms ATK.RiemannStates.estado_DN_zero_iff
#print axioms ATK.RiemannStates.estado_DN_finito_iff
#print axioms ATK.RiemannStates.estado_DN_exclui
#print axioms ATK.RiemannStates.limite_DN_em
#print axioms ATK.RiemannStates.O1_iff_nao_finito
#print axioms ATK.RiemannStates.riemann_de_nao_finito
