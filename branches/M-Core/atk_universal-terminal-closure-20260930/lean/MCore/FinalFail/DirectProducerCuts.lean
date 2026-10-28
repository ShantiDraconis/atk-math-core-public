import MCore.FinalFail.SemanticParallel
import MCore.FinalFail.BSDConcreteDomain

namespace MCore.FinalFail.Semantic

/-!
# Direct producer min-cuts

Forward-only ledger after the semantic frontier audit.

Each entry names the smallest currently admissible material producer.  These are
not wrappers around BoundaryAtom and are not promoted by accepted hypotheses.
The only way to move an entry from OPEN_MATH is to construct the named target
(or a strictly stronger object with a kernel-checked projection to it).
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
    target := "RiemannOffCriticalZero"
    reduction := "¬RiemannHypothesis ↔ Nonempty RiemannOffCriticalZero; unconditional witness still absent"
    state := .openMath },
  { problem := .beal
    target := "GCDLowerBoundProducer: ∀ d : BealData, 1 < gcd(d.a, gcd(d.b,d.c))"
    reduction := "m-core-beal proves this scalar producer ↔ CommonDivisor ↔ CommonPrime on the positive Beal domain; the universal gcd lower bound itself remains open"
    state := .openMath },
  { problem := .pVsNP
    target := "P01ConstructionGap ∧ G21Pointwise; P01 local evalStep frontier is now only the input-node 000++encodeNat(i) preserving witness read, followed by global evalRun lift and final parser→guess→verifier NTM integration"
    reduction := "P01 finite-frame evaluator is GREEN_FROZEN at f70ab88b/run 36508950379; cursor/frame primitives and all five finite tags const-false/const-true/NOT/AND/OR are GREEN_FROZEN at 6707aa0e/run 36552792426. The existing indexed witness reader is destructive, so the sole remaining local evalStep producer is a fixed unary-index-driven reader that restores the witness exactly. G21Pointwise remains independently OPEN_MATH and equivalent to SAT∉P on the bound official lane"
    state := .openMath },
  { problem := .navierStokes
    target := "NSProducerFirst.ActualNSToSignedGainCore on genuine flow-derived EnstrophyData"
    reduction := "NS run 36496747228 proves, for nonnegative viscosity, SignedGainCertificate is inhabitance-equivalent to SignedGainCore; the material core keeps only theta<1 and stretch ≤ theta*nu*z + C*y^2, while theta≥0 and C≥0 are reconstructed by max-normalization"
    state := .openMath },
  { problem := .hodge
    target := "genuine Hodge geometry/cycle binding + ConcreteAlgebraicityPayload"
    reduction := "constant-Qbar R2 is endpoint-equivalent to the payload, but the abstract payload is vacuously inhabited on an empty-variety model (Hodge audit run 36493536443 SUCCESS); genuine geometry binding is material"
    state := .openMath },
  { problem := .bsd
    target := "on genuine EllipticCurveQ: bind the curve's L-series and rational-point group, then produce rank equality and the refined period/regulator/Sha/Tamagawa/torsion identity"
    reduction := "the pinned Mathlib v4.19 kernel now binds a genuine nonempty elliptic-curve domain and has analyticOrderAt, but lacks the later EllipticCurve.LFunction, rational-point-group/height, and descent APIs; those source bindings are SOURCE_VERSION_BLOCKED before the material BSD equalities"
    state := .openMath },
  { problem := .yangMills
    target := "genuine 4D physical-model binding + B60ConcretePhysicalAdapter/K30 transfer"
    reduction := "B60 alone admits a degenerate Unit/True model (YM audit run 36493055781 SUCCESS); material progress requires binding C/F/D/H/G/O to a genuine 4D Yang-Mills realization"
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
