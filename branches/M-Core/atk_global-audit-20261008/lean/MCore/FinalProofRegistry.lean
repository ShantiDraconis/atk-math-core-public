import MCore.FinalFail.UniversalTerminalClosure
import MCore.FinalFail.RPAConfirmation
import MCore.FinalFail.RPALattice
import MCore.FinalFail.RPALatticeCube3
import MCore.FinalFail.Semantic.RiemannDual
import MCore.FinalFail.Semantic.NavierStokesClay

namespace MCore.FinalProof

inductive ProblemSlot where
  | riemann | beal | navierStokes | hodge | pVsNP | bsd | yangMills
  deriving DecidableEq, Repr

inductive SlotState where
  | linkedReuse
  | openMath
  | proved
  deriving DecidableEq, Repr

structure SlotRecord where
  slot : ProblemSlot
  sourceRepo : String
  sourceRef : String
  /-- Frozen branch whose head is `sourceRef` (resolvable provenance pin). -/
  sourceBranch : String
  terminal : String
  state : SlotState
  deriving Repr

/-!
The registry records the current material terminal producer in each lane.
A GREEN/FROZEN reduction or transport certificate never changes a slot to
`proved`; only an inhabitant of the named terminal target may do that.

Audit 2026-10-09: the P01 conjunct of the pVsNP terminal is inhabited
unconditionally in the source repository (kernel-checked; axioms propext,
Classical.choice, Quot.sound).  The slot stays `openMath` because the lane's
terminal is the conjunction and `G21Pointwise` is open.

Audit 2026-10-08: every `sourceRef` is the head of the listed frozen branch and
defines the named terminal.  Two pins were corrected: pVsNP `a3386d52` contained
neither `G21Pointwise` nor `P01MachineConstruction` (now `b406b806`, the frozen
FinalExternalTwoGap reduction), and bsd `c1e7b245` had no named terminal (now
`a3edf620`, `P06.BSD.BSDTerminal`).  No slot state changed.
-/
def registry : List SlotRecord := [
  { slot := .riemann
    sourceRepo := "ShantiDraconis/m-core-riemann"
    sourceRef := "d6a291b4563f9021f74ab63cc983d44f079472da"
    sourceBranch := "frozen/nb-zero-limit-density-equivalence-green-d6a291b4"
    terminal := "DUAL (FinalFail.Semantic.RiemannDual): prove = RiemannHypothesis, source producer FiniteSpanApproximatesChi concreteGeneratorFamily (Nyman–Beurling); refute = Nonempty RiemannOffCriticalZero; exactly one side is inhabitable"
    state := .openMath },
  { slot := .beal
    sourceRepo := "ShantiDraconis/m-core-beal"
    sourceRef := "d6fe130c44ef91e0f8ceb6b15a6548f186e381fd"
    sourceBranch := "frozen/gcd-lower-bound-producer-green-d6fe130c"
    terminal := "GCDLowerBoundProducer = ∀ d : BealData, 1 < Nat.gcd d.a (Nat.gcd d.b d.c)"
    state := .openMath },
  { slot := .navierStokes
    sourceRepo := "ShantiDraconis/navier-stokes-critical-barrier-audit"
    sourceRef := "df808543535d34d4e8c46096b3455d76b0151fa2"
    sourceBranch := "frozen/ns-signed-gain-core-firewall-green-df808543"
    terminal := "DUAL (FinalFail.Semantic.NavierStokesClay): prove = StatementA (Fefferman (A)), refute = StatementC (Fefferman (C)); source producer ActualNSToSignedGainCore on genuine flow-derived EnstrophyData"
    state := .openMath },
  { slot := .hodge
    sourceRepo := "ShantiDraconis/m-core-hodge"
    sourceRef := "42eaf7d4d639871f82eceb121ee525a6c4f30d84"
    sourceBranch := "frozen/h01-minimal-forward-payload-green-42eaf7d4"
    terminal := "ConcreteAlgebraicityPayload"
    state := .openMath },
  { slot := .pVsNP
    sourceRepo := "ShantiDraconis/m-core-p-vs-np"
    sourceRef := "b406b806da58ebe6bc1f85863ee44054ad42edb2"
    sourceBranch := "frozen/final-external-two-gap-green-b406b806"
    terminal := "Nonempty P01MachineConstruction ∧ G21Pointwise — P01 conjunct CLOSED by P01RawTotalizationProducer.p01ConstructionGap_closed @0dd09383 (frozen/p01-t5-poly-halting-green-0dd09383; audit frozen/p01-closure-audit-green-d97a56e1, run 37913791428); G21Pointwise (≡ SAT ∉ P) OPEN"
    state := .openMath },
  { slot := .bsd
    sourceRepo := "ShantiDraconis/m-core-bsd"
    sourceRef := "a3edf6209a143db063939ada57869b41e49a708f"
    sourceBranch := "frozen/P06-dense-green"
    terminal := "P06.BSD.BSDTerminal M  (↔ BSDP1 M ∧ BSDP2 M: rank equality + refined identity on ConcreteBSDModel)"
    state := .openMath },
  { slot := .yangMills
    sourceRepo := "ShantiDraconis/m-core-yang-mills"
    sourceRef := "cd4bbfd348b607bd24ed0c6d605207b764286f58"
    sourceBranch := "frozen/prefix-y01-b3b5-hardening-cd4bbfd"
    terminal := "Nonempty (B60ConcretePhysicalAdapter C F D H G O)"
    state := .openMath }
]

def provedCount : Nat :=
  registry.foldl (fun n r => if r.state = .proved then n + 1 else n) 0

def openMathCount : Nat :=
  registry.foldl (fun n r => if r.state = .openMath then n + 1 else n) 0

theorem registry_length_eq_seven : registry.length = 7 := by
  decide

theorem provedCount_eq_zero : provedCount = 0 := by
  decide

theorem openMathCount_eq_seven : openMathCount = 7 := by
  decide

/-! ## Semantic-binding firewall

A lane's terminal counts as a solution only if its target is tied to the
official problem statement.  A target that is parametric in abstract predicates
can be inhabited by trivial instantiations, so such a lane may never be marked
`proved`.  The theorem `registry_binding_firewall` is checked by `decide`:
promoting a `parametric` slot makes the library fail to build.
-/

/-- How a lane's semantic target is tied to the official problem statement. -/
inductive SemanticBinding where
  /-- Stated directly over Mathlib / `ℕ` objects (official statement). -/
  | concrete
  /-- Bound to a normalized official model through a certified external
  contract (P vs NP: G3 `cook_normalized_g3_contract_closed`); external source
  fidelity is a separate audit item. -/
  | externalContract
  /-- Parametric in abstract predicates; the official objects are not available
  in Mathlib v4.19 (Hodge classes / cycle class map, L-functions of elliptic
  curves, constructive 4D Yang–Mills / Osterwalder–Schrader). -/
  | parametric
  deriving DecidableEq, Repr

/-- Current binding of each lane (audit 2026-10-08).
* riemann: `Semantic.RiemannDual` over Mathlib `riemannZeta` / `RiemannHypothesis`;
* beal: `Semantic.BealUniversalGCDTarget` over `ℕ`;
* navierStokes: `Semantic.NavierStokesClay` (Fefferman's statements (A) / (C));
* pVsNP: certified G3 contract in `m-core-p-vs-np`;
* hodge, bsd, yangMills: parametric. -/
def bindingOf : ProblemSlot → SemanticBinding
  | .riemann => .concrete
  | .beal => .concrete
  | .navierStokes => .concrete
  | .pVsNP => .externalContract
  | .hodge => .parametric
  | .bsd => .parametric
  | .yangMills => .parametric

def SemanticBinding.admitsPromotion : SemanticBinding → Bool
  | .concrete => true
  | .externalContract => true
  | .parametric => false

/-- No slot may be `proved` unless its target is bound to the official
statement. -/
theorem registry_binding_firewall :
    registry.all (fun r => r.state != .proved || (bindingOf r.slot).admitsPromotion) = true := by
  decide

/-- Three lanes cannot currently be promoted at all, whatever is inhabited. -/
theorem parametric_lanes :
    (registry.filter (fun r => !(bindingOf r.slot).admitsPromotion)).length = 3 := by
  decide

end MCore.FinalProof
