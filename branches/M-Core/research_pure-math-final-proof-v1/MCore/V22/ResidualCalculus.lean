import MCore.V22.BidirectionalClosure

namespace MCore.V22

/-!
Residual calculus.  The core records only logically justified reductions.
It does not provide a reduction relation for a mathematical problem.
-/

structure ResidualSystem where
  Residual : Type
  smaller : Residual → Residual → Prop
  wellFounded : WellFounded smaller

namespace ResidualSystem

variable (S : ResidualSystem)

def Closed (r : S.Residual) : Prop :=
  ¬ ∃ r', S.smaller r' r

structure Step (before after : S.Residual) : Prop where
  decreases : S.smaller after before

private theorem acc_irrefl
    (x : S.Residual) (hx : Acc S.smaller x) :
    ¬ S.smaller x x := by
  intro hxx
  induction hx with
  | intro y ih =>
      have hy : Acc S.smaller y := ih y hxx
      exact acc_irrefl y hy hxx

theorem step_irrefl {r : S.Residual} :
    ¬ Step S r r := by
  intro h
  exact acc_irrefl r (S.wellFounded.apply r) h.decreases

theorem no_step_from_closed {r : S.Residual}
    (h : Closed S r) :
    ¬ ∃ r', Step S r r' := by
  intro hex
  rcases hex with ⟨r', hr'⟩
  exact h ⟨r', hr'.decreases⟩

/-- Recursive attack is justified only along the problem-supplied well-founded
    residual relation.  This gives termination of the decomposition mechanism,
    not a proof that the terminal residual is the desired final theorem. -/
def attackAcc (r : S.Residual) : Acc S.smaller r :=
  S.wellFounded.apply r

end ResidualSystem

/-- A closure certificate keeps the final proposition as an explicit field.
    Constructing this object therefore requires an actual term of Final. -/
structure ClosureCertificate (Final : Prop) where
  finalProof : Final
  statementMatch : Prop
  statementMatchProof : statementMatch
  quantifierMatch : Prop
  quantifierMatchProof : quantifierMatch
  directionality : Prop
  directionalityProof : directionality
  noCircularity : Prop
  noCircularityProof : noCircularity
  dependenciesClosed : Prop
  dependenciesClosedProof : dependenciesClosed

theorem certificate_implies_final {Final : Prop}
    (c : ClosureCertificate Final) : Final :=
  c.finalProof

end MCore.V22
