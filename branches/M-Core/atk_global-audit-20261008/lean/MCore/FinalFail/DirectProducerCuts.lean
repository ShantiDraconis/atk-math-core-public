import MCore.FinalFail.SemanticParallel
import MCore.FinalFail.BSDConcreteDomain

namespace MCore.FinalFail.Semantic

/-!
# Direct producer min-cuts

Forward-only ledger after the semantic frontier audit.

Each entry names the smallest currently admissible material producer. These are
not wrappers around BoundaryAtom and are not promoted by accepted hypotheses.
The only way to move an entry from OPEN_MATH is to construct the named target
(or a strictly stronger object with a kernel-checked projection to it).

This file is aligned to the canonical per-repository GATE_LEDGER.json frontiers
audited through 2026-09-29.
-/

inductive DirectProducerState where
  | openMath
  | produced
  deriving DecidableEq, Repr

structure DirectProducerCut where
  problem : ProblemId
  target : String
  reduction : String
  state : DirectProducerState
  deriving Repr

def directProducerCuts : List DirectProducerCut := [
  { problem := .riemann
    target := "FiniteSpanApproximatesChi concreteGeneratorFamily"
    reduction := "m-core-riemann freezes finiteSpanApproximatesChi_iff_DNLimit_eq_zero; this is also equivalent along the certified DNToZero chain. The concrete finite-span density inhabitant remains OPEN_MATH."
    state := .openMath },
  { problem := .beal
    target := "GCDLowerBoundProducer: ∀ d : BealData, 1 < Nat.gcd d.a (Nat.gcd d.b d.c)"
    reduction := "m-core-beal freezes bealConjecture_iff_gcdLowerBoundProducer and the CommonDivisor/CommonPrime projections on the positive Beal domain; the universal scalar gcd lower bound remains OPEN_MATH."
    state := .openMath },
  { problem := .pVsNP
    target := "P01ConstructionGap ∧ G21Pointwise"
    reduction := "P01 is compressed to Nonempty P01MachineConstruction: close the preserving unary indexed witness read for input tag 000, lift the complete physical evalStep refinement to global evalRun, and compose parser+witness+verifier into one fixed finite-control NTM with polynomial HaltsWithin and AcceptsWithin ↔ SATBits. G21Pointwise remains independently OPEN_MATH and endpoint-equivalent to the bound SAT∉P lane."
    state := .openMath },
  { problem := .navierStokes
    target := "NSProducerFirst.ActualNSToSignedGainCore on genuine flow-derived EnstrophyData"
    reduction := "The frozen signed-gain core keeps exactly theta < 1 and stretch(t) ≤ theta*nu*z(t) + C*y(t)^2; all normalization and downstream differential consequences are certified. The PDE-derived producer from ActualNS remains OPEN_MATH."
    state := .openMath },
  { problem := .hodge
    target := "ConcreteAlgebraicityPayload"
    reduction := "m-core-hodge freezes trivial_qbar_r2_payload_iff_concrete_payload and H01MinimalForwardPayload as a sufficient forward route. The universal ConcreteAlgebraicityPayload inhabitant itself remains OPEN_MATH."
    state := .openMath },
  { problem := .bsd
    target := "realizable elliptic-curve domain + universal rank equality + refined leading-coefficient identity on that same domain"
    reduction := "The abstract BSDArithmeticAnalyticData universal contract is rejected by a certified firewall because it admits unrelated Nat data. Progress requires binding genuine elliptic-curve arithmetic/analytic data first, then proving BSD rank equality and the refined formula on that realizable domain."
    state := .openMath },
  { problem := .yangMills
    target := "Nonempty (B60ConcretePhysicalAdapter C F D H G O)"
    reduction := "The frozen B3-B5 hardening blocks phantom witnesses; B60ConcretePhysicalAdapter is the current sufficient material producer tying the regulated 4D construction to the same physical Hilbert/Hamiltonian/K30 data. No B60 inhabitant is currently supplied."
    state := .openMath }
]

def directProducerCutCount : Nat := directProducerCuts.length

def producedDirectCount : Nat :=
  directProducerCuts.foldl
    (fun n lane => if lane.state = .produced then n + 1 else n) 0

def openDirectCount : Nat :=
  directProducerCuts.foldl
    (fun n lane => if lane.state = .openMath then n + 1 else n) 0

theorem directProducerCutCount_eq_seven :
    directProducerCutCount = 7 := by
  decide

theorem producedDirectCount_eq_zero :
    producedDirectCount = 0 := by
  decide

theorem openDirectCount_eq_seven :
    openDirectCount = 7 := by
  decide

/-- No-wrapper invariant at the administrative layer: merely accepting all
semantic hypotheses does not mutate the direct-producer ledger. -/
theorem accepted_semantics_do_not_move_direct_count :
    assumedSemanticLaneCount = 7 ∧ producedDirectCount = 0 := by
  exact ⟨assumedSemanticLaneCount_eq_seven, producedDirectCount_eq_zero⟩

end MCore.FinalFail.Semantic
