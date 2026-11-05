import MCore.FinalFail.ExactGapLedger

namespace MCore.FinalFail

structure RecoveryFirewall where
  statementChecked : Prop
  hypothesesChecked : Prop
  quantifiersChecked : Prop
  domainChecked : Prop
  axiomsChecked : Prop
  circularityChecked : Prop
  semanticFidelityChecked : Prop

def RecoveryFirewall.closed (f : RecoveryFirewall) : Prop :=
  f.statementChecked ∧ f.hypothesesChecked ∧ f.quantifiersChecked ∧
  f.domainChecked ∧ f.axiomsChecked ∧ f.circularityChecked ∧
  f.semanticFidelityChecked

structure BoundaryCollapse (Expr Boundary Collapsed : Type) where
  cross : Expr → Boundary
  collapse : Boundary → Collapsed

def losesInformation {Expr Boundary Collapsed}
    (B : BoundaryCollapse Expr Boundary Collapsed) : Prop :=
  ∃ x y, x ≠ y ∧ B.collapse (B.cross x) = B.collapse (B.cross y)

structure EndpointAdapter (Core Endpoint : Prop) where
  core_to_endpoint : Core → Endpoint
  endpoint_to_core : Endpoint → Core

theorem endpoint_adapter_iff {Core Endpoint : Prop}
    (A : EndpointAdapter Core Endpoint) : Core ↔ Endpoint :=
  ⟨A.core_to_endpoint, A.endpoint_to_core⟩

end MCore.FinalFail
