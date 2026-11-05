import ATK.BaezDuarteBridge

/-!
# ATK — Port de B1 para a distância `bdDistSq` da linha de Riemann

A hipótese `hCriterion : Tendsto bdDistSq atTop (𝓝 0) → RiemannHypothesis` aparece no
`HYPOTHESIS_MAP` (2 usos) em `ATK.Riemann.rh_of_bd_bound`, nos branches `atk-kernel-check`
(`m-core-riemann` a27833a e `M-Core`) e `fix/ns-scaling-false` (`M-Core`). Lá, `bdDistSq` é
definida com `bdChi = 𝟙_(0,1]` e `bdRho k t = {1/(k t)}` — os mesmos termos que `chi`, `rho` e
`DN` de `ATK.Conditional.Riemann`.

Este arquivo:

* recria literalmente `bdChi`, `bdRho`, `bdDistSq` e `ConcreteBDUniformLogBound` (mesmos nomes,
  no namespace `ATK.Riemann`, como na linha);
* prova `bdDistSq_eq_DN : bdDistSq = DN` por `rfl` (igualdade definicional);
* **descarrega a hipótese**: `criterio_bd : Tendsto bdDistSq atTop (𝓝 0) → RiemannHypothesis`,
  transportando a prova de B1 (`ATK.BaezDuarteBridge.baezDuarteCriterion`);
* `rh_of_bd_bound` sem `hCriterion`: a cota uniforme da linha ⇒ RH;
* `concreteBD_iff_uniformLogBound`: o terminal da linha é exatamente O1.

O que **não** sai daqui: a forma "⟺" usada em `ATK.RHConvergence.rh_iff_limit_zero_of_criterion`
exige também RH ⇒ `D_N → 0` (a direção de necessidade de Báez-Duarte), que não está formalizada.
`ConcreteBDUniformLogBound` (= O1) continua aberta. **CLOSED_MATH continua false.**
-/

namespace ATK.Riemann

open MeasureTheory in
/-- χ = indicadora de (0, 1] (definição literal da linha `m-core-riemann`). -/
noncomputable def bdChi (t : ℝ) : ℝ := Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) t

/-- ρ_k(t) = {1/(k t)} (definição literal da linha). -/
noncomputable def bdRho (k : ℕ) (t : ℝ) : ℝ := Int.fract (1 / ((k : ℝ) * t))

open MeasureTheory in
/-- D_N de Báez-Duarte (definição literal da linha). -/
noncomputable def bdDistSq (N : ℕ) : ℝ :=
  ⨅ c : Fin N → ℝ, ∫ t in Set.Ioi (0 : ℝ), (bdChi t - ∑ k : Fin N, c k * bdRho (k.val + 1) t) ^ 2

/-- Terminal da linha: cota uniforme sobre a distância concreta (definição literal). -/
def ConcreteBDUniformLogBound : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, bdDistSq N ≤ K / Real.log ((N : ℝ) + 2)

end ATK.Riemann

namespace ATK.BDDistSqPort

open Filter Topology ATK.Riemann ATK.Conditional.Riemann

/-- `bdChi` é `chi`. -/
theorem bdChi_eq_chi : bdChi = chi := rfl

/-- `bdRho` é `rho`. -/
theorem bdRho_eq_rho : bdRho = rho := rfl

/-- **`bdDistSq` é `DN`**, por igualdade definicional. -/
theorem bdDistSq_eq_DN : bdDistSq = DN := rfl

/-- **Hipótese descarregada**: o critério de Báez-Duarte para `bdDistSq` (direção suficiente),
transportado da prova de B1. -/
theorem criterio_bd : Tendsto bdDistSq atTop (𝓝 0) → RiemannHypothesis := by
  rw [bdDistSq_eq_DN]
  exact ATK.BaezDuarteBridge.baezDuarteCriterion

/-- `rh_of_bd_bound` da linha, agora sem a hipótese `hCriterion`. -/
theorem rh_of_bd_bound (h : ConcreteBDUniformLogBound) : RiemannHypothesis := by
  obtain ⟨K, _, hK⟩ := h
  exact ATK.BaezDuarteBridge.riemann_of_uniformLogBound ⟨K, hK⟩

/-- O terminal da linha é exatamente O1 (`UniformLogBound`). -/
theorem concreteBD_iff_uniformLogBound : ConcreteBDUniformLogBound ↔ UniformLogBound := by
  constructor
  · rintro ⟨K, _, hK⟩
    exact ⟨K, hK⟩
  · rintro ⟨K, hK⟩
    refine ⟨K, ?_, hK⟩
    have h0 := hK 0
    rw [ATK.RiemannFaithful.DN_zero_eq_one] at h0
    simp only [Nat.cast_zero, zero_add] at h0
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    by_contra hneg
    push Not at hneg
    have : K / Real.log 2 < 0 := div_neg_of_neg_of_pos hneg hlog
    linarith

/-- O limite de `bdDistSq` existe (é `⨅ N, bdDistSq N`), e se ele é 0 vale RH. -/
theorem rh_of_iInf_bd_zero (h : ⨅ N, bdDistSq N = 0) : RiemannHypothesis :=
  ATK.BaezDuarteBridge.riemann_of_iInf_zero h

/-- `bdDistSq` é monótona (porte de `ATK.RHConvergence.bdDistSq_antitone`). -/
theorem bdDistSq_antitone : Antitone bdDistSq := ATK.RiemannConcrete.DN_antitone

end ATK.BDDistSqPort

#print axioms ATK.BDDistSqPort.bdChi_eq_chi
#print axioms ATK.BDDistSqPort.bdRho_eq_rho
#print axioms ATK.BDDistSqPort.bdDistSq_eq_DN
#print axioms ATK.BDDistSqPort.criterio_bd
#print axioms ATK.BDDistSqPort.rh_of_bd_bound
#print axioms ATK.BDDistSqPort.concreteBD_iff_uniformLogBound
#print axioms ATK.BDDistSqPort.rh_of_iInf_bd_zero
#print axioms ATK.BDDistSqPort.bdDistSq_antitone
