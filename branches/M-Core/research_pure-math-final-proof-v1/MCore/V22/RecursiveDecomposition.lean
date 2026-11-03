import MCore.V22.ResidualCalculus

namespace MCore.V22

structure ExactDecomposition (Parent Child : Prop) where
  forward : Parent → Child
  backward : Child → Parent

namespace ExactDecomposition

variable {A B C : Prop}

theorem asIff (d : ExactDecomposition A B) : A ↔ B :=
  ⟨d.forward, d.backward⟩

def refl (A : Prop) : ExactDecomposition A A where
  forward := id
  backward := id

def trans (ab : ExactDecomposition A B)
    (bc : ExactDecomposition B C) : ExactDecomposition A C where
  forward := bc.forward ∘ ab.forward
  backward := ab.backward ∘ bc.backward

theorem child_proof_closes_parent
    (d : ExactDecomposition A B) (hB : B) : A :=
  d.backward hB

end ExactDecomposition

structure ResearchObligation where
  Start : Prop
  Middle : Prop
  Final : Prop
  startToMiddle : Start → Middle
  finalToMiddle : Final → Middle

structure ClosedDirections (o : ResearchObligation) where
  middleToStart : o.Middle → o.Start
  middleToFinal : o.Middle → o.Final

theorem closedDirections_start_iff_final
    (o : ResearchObligation) (h : ClosedDirections o) :
    o.Start ↔ o.Final := by
  constructor
  · intro hs
    exact h.middleToFinal (o.startToMiddle hs)
  · intro hf
    exact h.middleToStart (o.finalToMiddle hf)

structure RecursiveFrontier (Parent : Prop) where
  Child : Prop
  exact : ExactDecomposition Parent Child

theorem recursive_frontier_exact
    {Parent : Prop} (r : RecursiveFrontier Parent) :
    Parent ↔ r.Child :=
  r.exact.asIff

def certifyClosedDirections
    (o : ResearchObligation)
    (hdir : ClosedDirections o)
    (hStart : o.Start)
    (statementMatch quantifierMatch noCircularity dependenciesClosed : Prop)
    (hStatement : statementMatch)
    (hQuantifier : quantifierMatch)
    (hNoCircularity : noCircularity)
    (hDependencies : dependenciesClosed) :
    ClosureCertificate o.Final where
  finalProof := hdir.middleToFinal (o.startToMiddle hStart)
  statementMatch := statementMatch
  statementMatchProof := hStatement
  quantifierMatch := quantifierMatch
  quantifierMatchProof := hQuantifier
  directionality := o.Start ↔ o.Final
  directionalityProof := closedDirections_start_iff_final o hdir
  noCircularity := noCircularity
  noCircularityProof := hNoCircularity
  dependenciesClosed := dependenciesClosed
  dependenciesClosedProof := hDependencies

end MCore.V22
