import MCore.FinalFail.UniversalTerminalClosure
import MCore.FinalFail.RPAConfirmation
import MCore.FinalFail.RPALattice
import MCore.FinalFail.RPALatticeCube3

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
  terminal : String
  state : SlotState
  deriving Repr

/-!
The registry records the current material terminal producer in each lane.
A GREEN/FROZEN reduction or transport certificate never changes a slot to
`proved`; only an inhabitant of the named terminal target may do that.
-/
def registry : List SlotRecord := [
  { slot := .riemann
    sourceRepo := "ShantiDraconis/m-core-riemann"
    sourceRef := "d6a291b4563f9021f74ab63cc983d44f079472da"
    terminal := "FiniteSpanApproximatesChi concreteGeneratorFamily"
    state := .openMath },
  { slot := .beal
    sourceRepo := "ShantiDraconis/m-core-beal"
    sourceRef := "d6fe130c44ef91e0f8ceb6b15a6548f186e381fd"
    terminal := "GCDLowerBoundProducer = ∀ d : BealData, 1 < Nat.gcd d.a (Nat.gcd d.b d.c)"
    state := .openMath },
  { slot := .navierStokes
    sourceRepo := "ShantiDraconis/navier-stokes-critical-barrier-audit"
    sourceRef := "df808543535d34d4e8c46096b3455d76b0151fa2"
    terminal := "ActualNSToSignedGainCore on genuine flow-derived EnstrophyData"
    state := .openMath },
  { slot := .hodge
    sourceRepo := "ShantiDraconis/m-core-hodge"
    sourceRef := "42eaf7d4d639871f82eceb121ee525a6c4f30d84"
    terminal := "ConcreteAlgebraicityPayload"
    state := .openMath },
  { slot := .pVsNP
    sourceRepo := "ShantiDraconis/m-core-p-vs-np"
    sourceRef := "a3386d52951f2e886eca9359fc218cd18014e0f0"
    terminal := "Nonempty P01MachineConstruction ∧ G21Pointwise"
    state := .openMath },
  { slot := .bsd
    sourceRepo := "ShantiDraconis/m-core-bsd"
    sourceRef := "c1e7b245726c4c65f5f9f878acefb86460746f4a"
    terminal := "realizable elliptic-curve domain + universal rank equality + refined leading-coefficient identity"
    state := .openMath },
  { slot := .yangMills
    sourceRepo := "ShantiDraconis/m-core-yang-mills"
    sourceRef := "cd4bbfd348b607bd24ed0c6d605207b764286f58"
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

end MCore.FinalProof
