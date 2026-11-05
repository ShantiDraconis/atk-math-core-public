import MCore.FinalFail.DirectProducerCuts

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

def registry : List SlotRecord := [
  { slot := .riemann, sourceRepo := "ShantiDraconis/m-core-riemann", sourceRef := "ad3011f14bdab32161205e053fa925bc8c851ad4", terminal := "DNLimit=0 + audited RH bridge", state := .openMath },
  { slot := .beal, sourceRepo := "ShantiDraconis/m-core-beal", sourceRef := "d039136fe260d626fbf0974a3413d222e13d43f8", terminal := "forall BealData, CommonPrime", state := .openMath },
  { slot := .navierStokes, sourceRepo := "ShantiDraconis/navier-stokes-critical-barrier-audit", sourceRef := "bdf538c84076cece7aae52e9d35d68c226e968d1", terminal := "ActualNS -> uniform signed depletion -> endpoint regularity", state := .openMath },
  { slot := .hodge, sourceRepo := "ShantiDraconis/m-core-hodge", sourceRef := "f0fffbe0eed8bfaf0bd060317fa13f648b3790fd", terminal := "RationalHodgeConjecture / H01UniversalForwardPayload", state := .openMath },
  { slot := .pVsNP, sourceRepo := "ShantiDraconis/m-core-p-vs-np", sourceRef := "final-proof/pnp_reuse_chain.json", terminal := "P01ConstructionGap + G21Pointwise", state := .linkedReuse },
  { slot := .bsd, sourceRepo := "ShantiDraconis/m-core-bsd", sourceRef := "dfa710de6a8646640db8b7010e3e00d439091d31", terminal := "universal BSDRankPart + refined leading coefficient identity", state := .openMath },
  { slot := .yangMills, sourceRepo := "ShantiDraconis/m-core-yang-mills", sourceRef := "645b299959f02902c7e6245855d3b5da9a951139", terminal := "genuine 4D realization + OS/Hamiltonian reconstruction + positive mass gap", state := .openMath }
]

def provedCount : Nat := registry.foldl (fun n r => if r.state = .proved then n + 1 else n) 0

theorem provedCount_eq_zero : provedCount = 0 := by decide

end MCore.FinalProof
