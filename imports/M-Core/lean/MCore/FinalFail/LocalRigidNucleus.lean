namespace MCore.FinalFail

/--
A Beal-like behavior is abstracted as: an ambient object has a primitive/core
predicate and closure means that the primitive obstruction is eliminated.
No statement about the Beal conjecture itself is assumed.
-/
structure BealBehaviorTemplate where
  Ambient : Type
  Core : Ambient → Prop
  Closed : Ambient → Prop
  coreElimination : ∀ x, Closed x ↔ ¬ Core x

/--
Each problem owns its own rigid nucleus.  The commonality with Beal is not the
underlying object but the factorization pattern: isolate a primitive obstruction,
then characterize endpoint closure by elimination of that obstruction.
-/
structure LocalRigidNucleus where
  Ambient : Type
  Obstruction : Ambient → Prop
  EndpointClosed : Ambient → Prop
  endpoint_iff_obstruction_eliminated :
    ∀ x, EndpointClosed x ↔ ¬ Obstruction x

/-- Exact behavioral equivalence between a local nucleus and a Beal-like
template requires maps in both directions preserving both obstruction and
closure. -/
structure BealBehaviorEquivalence
    (B : BealBehaviorTemplate) (N : LocalRigidNucleus) where
  toBeal : N.Ambient → B.Ambient
  fromBeal : B.Ambient → N.Ambient
  leftInverse : ∀ x, fromBeal (toBeal x) = x
  rightInverse : ∀ y, toBeal (fromBeal y) = y
  preservesObstruction : ∀ x, N.Obstruction x ↔ B.Core (toBeal x)
  preservesClosure : ∀ x, N.EndpointClosed x ↔ B.Closed (toBeal x)

/-- Transporting the Beal-like elimination law across a proved behavioral
equivalence recovers the local endpoint law. -/
theorem transport_core_elimination
    (B : BealBehaviorTemplate) (N : LocalRigidNucleus)
    (e : BealBehaviorEquivalence B N) (x : N.Ambient) :
    N.EndpointClosed x ↔ ¬ N.Obstruction x := by
  constructor
  · intro hClosed hObs
    have hBClosed : B.Closed (e.toBeal x) :=
      (e.preservesClosure x).mp hClosed
    have hNotCore : ¬ B.Core (e.toBeal x) :=
      (B.coreElimination (e.toBeal x)).mp hBClosed
    exact hNotCore ((e.preservesObstruction x).mp hObs)
  · intro hNotObs
    have hNotCore : ¬ B.Core (e.toBeal x) := by
      intro hCore
      exact hNotObs ((e.preservesObstruction x).mpr hCore)
    have hBClosed : B.Closed (e.toBeal x) :=
      (B.coreElimination (e.toBeal x)).mpr hNotCore
    exact (e.preservesClosure x).mpr hBClosed

/--
Family form: every indexed problem has its own nucleus; a common template may
classify them only when an explicit equivalence is supplied for that index.
-/
structure NucleusFamily (ι : Type) where
  nucleus : ι → LocalRigidNucleus

structure BealModeledFamily (ι : Type) (B : BealBehaviorTemplate)
    extends NucleusFamily ι where
  equivalence : ∀ i, BealBehaviorEquivalence B (nucleus i)

theorem family_endpoint_iff_local_obstruction_eliminated
    {ι : Type} (B : BealBehaviorTemplate) (F : BealModeledFamily ι B)
    (i : ι) (x : (F.nucleus i).Ambient) :
    (F.nucleus i).EndpointClosed x ↔ ¬ (F.nucleus i).Obstruction x :=
  transport_core_elimination B (F.nucleus i) (F.equivalence i) x

end MCore.FinalFail
