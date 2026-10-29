/-!
ATK universal terminal contracts. These are conditional bridge theorems.
The required universal witnesses are NOT supplied by this module.
-/
namespace ATK.Universal

namespace RH
variable (DN : Nat → Rat) (Converges : (Nat → Rat) → Prop)
structure Producer where
  K : Rat
  nonneg : 0 ≤ K
  uniformBound : ∀ n : Nat, DN n ≤ K / (n + 1)
  boundImpliesConvergence : (∀ n : Nat, DN n ≤ K / (n + 1)) → Converges DN
variable (RHStatement : Prop)
structure SemanticBridge where
  criterion : Converges DN → RHStatement
theorem terminal (p : Producer DN Converges)
    (b : SemanticBridge DN Converges RHStatement) : RHStatement :=
  b.criterion (p.boundImpliesConvergence p.uniformBound)
end RH

namespace NS
variable (InitialData Solution : Type) (Admissible : InitialData → Prop)
  (Solves : InitialData → Solution → Prop)
  (GlobalRegular : Solution → Prop)
def Target : Prop := ∀ u, Admissible u → ∃ v, Solves u v ∧ GlobalRegular v
structure Producer where
  construct : InitialData → Solution
  solves : ∀ u, Admissible u → Solves u (construct u)
  regular : ∀ u, Admissible u → GlobalRegular (construct u)
theorem terminal (p : Producer InitialData Solution Admissible Solves GlobalRegular) :
    Target InitialData Solution Admissible Solves GlobalRegular := by
  intro u hu
  exact ⟨p.construct u, p.solves u hu, p.regular u hu⟩
end NS

namespace YM
variable (Theory : Type) (Physical : Theory → Prop)
  (MassGap : Theory → Prop)
def Target : Prop := ∃ t, Physical t ∧ MassGap t
structure Producer where
  theory : Theory
  physical : Physical theory
  gap : MassGap theory
theorem terminal (p : Producer Theory Physical MassGap) :
    Target Theory Physical MassGap := ⟨p.theory, p.physical, p.gap⟩
end YM

namespace BSD
variable (Curve : Type) (Admissible RankEquality RefinedFormula : Curve → Prop)
def Target : Prop := ∀ e, Admissible e → RankEquality e ∧ RefinedFormula e
structure Producer where
  rank : ∀ e, Admissible e → RankEquality e
  refined : ∀ e, Admissible e → RefinedFormula e
theorem terminal (p : Producer Curve Admissible RankEquality RefinedFormula) :
    Target Curve Admissible RankEquality RefinedFormula := by
  intro e he
  exact ⟨p.rank e he, p.refined e he⟩
end BSD

namespace Hodge
variable (Variety Class Cycle : Type)
  (SmoothProjective : Variety → Prop)
  (HodgeClass : Variety → Class → Prop)
  (Represents : Variety → Cycle → Class → Prop)
def Target : Prop := ∀ x a, SmoothProjective x → HodgeClass x a →
  ∃ z, Represents x z a
structure Producer where
  realize : Variety → Class → Cycle
  correct : ∀ x a, SmoothProjective x → HodgeClass x a →
    Represents x (realize x a) a
theorem terminal
    (p : Producer Variety Class Cycle SmoothProjective HodgeClass Represents) :
    Target Variety Class Cycle SmoothProjective HodgeClass Represents := by
  intro x a hx ha
  exact ⟨p.realize x a, p.correct x a hx ha⟩
end Hodge

namespace Beal
variable (Triple : Type) (Counterexample : Triple → Prop)
def Target : Prop := ∀ t, ¬ Counterexample t
structure Producer where
  noCounterexample : ∀ t, Counterexample t → False
theorem terminal (p : Producer Triple Counterexample) : Target Triple Counterexample := by
  intro t h
  exact p.noCounterexample t h
end Beal

namespace PNP
variable (Machine : Type) (DecidesSAT : Machine → Prop)
  (PolynomialTime : Machine → Prop)
def Target : Prop := ∀ m, DecidesSAT m → ¬ PolynomialTime m
structure Producer where
  lowerBound : ∀ m, DecidesSAT m → PolynomialTime m → False
theorem terminal (p : Producer Machine DecidesSAT PolynomialTime) :
    Target Machine DecidesSAT PolynomialTime := by
  intro m hm hp
  exact p.lowerBound m hm hp
end PNP

end ATK.Universal
