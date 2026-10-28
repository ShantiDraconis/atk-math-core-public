import MCore.K12
namespace MCore

/-- K13 names the exact unresolved rank-part proposition at this abstraction
level.  No theorem below manufactures a proof of this proposition. -/
def BSDOpenCore (d : BSDArithmeticAnalyticData) : Prop := BSDRankPart d

/-- A supplied proof can be transported through the definition.  This is an
interface theorem, not a proof that such a witness exists for every curve. -/
theorem k13_consume_open_core (d : BSDArithmeticAnalyticData)
    (h : BSDRankPart d) : BSDOpenCore d := h

theorem k13_open_core_iff_rank_part (d : BSDArithmeticAnalyticData) :
    BSDOpenCore d ↔ BSDRankPart d := Iff.rfl

/-- Certification node for the unresolved core inherits the K12 firewall. -/
def k13_open_core_node : CertNode :=
  { status := .openBridge,
    statement := k12_rank_part_node.status = .openBridge }

theorem k13_open_core_status : k13_open_core_node.status = .openBridge := rfl

theorem k13_open_core_not_proved :
    k13_open_core_node.status ≠ .provedProperty := by decide

theorem k13_open_core_not_certified :
    ¬ Nonempty (ProofCertificate k13_open_core_node) := by
  intro h
  rcases h with ⟨c⟩
  exact k13_open_core_not_proved c.status_proved

/-- K13 explicitly preserves the dependency chain K11 -> K12 -> K13. -/
theorem k13_upstream_k12_open : k12_rank_part_node.status = .openBridge :=
  k12_rank_part_open

theorem k13_upstream_k11_open : k11_rank_core_node.status = .openBridge :=
  k11_rank_core_open

end MCore
