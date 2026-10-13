import AxiomaticMillenium.GlobalStructuralCore

namespace AxiomaticMillenium

/--
Current source-verified terminal min-cut for the seven unresolved lanes.
The entries are administrative descriptions of exact material targets; a
remainingAtoms count greater than one means the terminal target is a genuine
conjunction/package, not that the lane has been solved.
-/
structure GlobalOpenCut where
  problem : String
  exactTarget : String
  remainingAtoms : Nat
  sourceRepo : String
  sourceRef : String
  deriving Repr, DecidableEq

def rhOpenCut : GlobalOpenCut :=
  { problem := "RH"
    exactTarget := "FiniteSpanApproximatesChi concreteGeneratorFamily"
    remainingAtoms := 1
    sourceRepo := "ShantiDraconis/m-core-riemann"
    sourceRef := "d6a291b4563f9021f74ab63cc983d44f079472da" }

def bealOpenCut : GlobalOpenCut :=
  { problem := "BEAL"
    exactTarget := "GCDLowerBoundProducer"
    remainingAtoms := 1
    sourceRepo := "ShantiDraconis/m-core-beal"
    sourceRef := "d6fe130c44ef91e0f8ceb6b15a6548f186e381fd" }

def pnpOpenCut : GlobalOpenCut :=
  { problem := "PVSNP"
    exactTarget := "Nonempty P01MachineConstruction AND G21Pointwise"
    remainingAtoms := 2
    sourceRepo := "ShantiDraconis/m-core-p-vs-np"
    sourceRef := "a3386d52951f2e886eca9359fc218cd18014e0f0" }

def nsOpenCut : GlobalOpenCut :=
  { problem := "NS"
    exactTarget := "ActualNSToSignedGainCore on genuine flow-derived EnstrophyData"
    remainingAtoms := 1
    sourceRepo := "ShantiDraconis/navier-stokes-critical-barrier-audit"
    sourceRef := "df808543535d34d4e8c46096b3455d76b0151fa2" }

def hodgeOpenCut : GlobalOpenCut :=
  { problem := "HODGE"
    exactTarget := "ConcreteAlgebraicityPayload"
    remainingAtoms := 1
    sourceRepo := "ShantiDraconis/m-core-hodge"
    sourceRef := "42eaf7d4d639871f82eceb121ee525a6c4f30d84" }

def bsdOpenCut : GlobalOpenCut :=
  { problem := "BSD"
    exactTarget := "realizable elliptic-curve domain + universal rank equality + refined leading-coefficient identity"
    remainingAtoms := 3
    sourceRepo := "ShantiDraconis/m-core-bsd"
    sourceRef := "c1e7b245726c4c65f5f9f878acefb86460746f4a" }

def ymOpenCut : GlobalOpenCut :=
  { problem := "YM"
    exactTarget := "Nonempty (B60ConcretePhysicalAdapter C F D H G O)"
    remainingAtoms := 1
    sourceRepo := "ShantiDraconis/m-core-yang-mills"
    sourceRef := "cd4bbfd348b607bd24ed0c6d605207b764286f58" }

def globalOpenCuts : List GlobalOpenCut :=
  [rhOpenCut, bealOpenCut, pnpOpenCut, nsOpenCut, hodgeOpenCut, bsdOpenCut, ymOpenCut]

def globalOpenLaneCount : Nat := globalOpenCuts.length

def globalMaterialAtomCount : Nat :=
  globalOpenCuts.foldl (fun n c => n + c.remainingAtoms) 0

theorem global_open_lane_count_eq_seven :
    globalOpenLaneCount = 7 := by
  decide

theorem global_material_atom_count_eq_ten :
    globalMaterialAtomCount = 10 := by
  decide

/--
The P-vs-NP lane has two independent terminal atoms in the current direct cut.
Closing the physical NP-verifier construction does not by itself supply the
G21 lower-bound producer.
-/
theorem pnp_has_two_terminal_atoms :
    pnpOpenCut.remainingAtoms = 2 := by
  rfl

/--
The BSD lane is a bound package: a realizable elliptic-curve domain, universal
rank equality, and the refined leading-coefficient identity must refer to that
same realizable domain.
-/
theorem bsd_has_three_bound_atoms :
    bsdOpenCut.remainingAtoms = 3 := by
  rfl

/--
No structural similarity theorem can lower this material atom count by itself.
Cross-problem reuse still requires a concrete, verified projection/transfer
operator, as enforced by boundaryTransferObligation.
-/
theorem similarity_does_not_discharge_open_cut
    (source target : VerifiedBoundary)
    (p : Pattern)
    (operatorId : String)
    (hTarget : Bool) :
    (boundaryTransferObligation source target p operatorId hTarget false).closed = false :=
  shared_pattern_is_not_automatic_transfer source target p operatorId hTarget

end AxiomaticMillenium
