import MCore.K13
namespace MCore

/-- Final typed audit record for the BSD K-chain.  It records only facts that
are already proved by preceding stages. -/
structure BSDFinalAudit where
  k11CoreOpen : k11_rank_core_node.status = .openBridge
  k12CoreOpen : k12_rank_part_node.status = .openBridge
  k13CoreOpen : k13_open_core_node.status = .openBridge
  k13CertificateBlocked : ¬ Nonempty (ProofCertificate k13_open_core_node)

/-- K14 assembles the final internal audit without adding mathematical
assumptions or promoting the open BSD core. -/
def k14_final_audit : BSDFinalAudit :=
  { k11CoreOpen := k11_rank_core_open,
    k12CoreOpen := k12_rank_part_open,
    k13CoreOpen := k13_open_core_status,
    k13CertificateBlocked := k13_open_core_not_certified }

theorem k14_chain_preserves_open_core :
    k11_rank_core_node.status = .openBridge ∧
    k12_rank_part_node.status = .openBridge ∧
    k13_open_core_node.status = .openBridge := by
  exact ⟨k14_final_audit.k11CoreOpen,
    k14_final_audit.k12CoreOpen,
    k14_final_audit.k13CoreOpen⟩

theorem k14_no_false_final_certificate :
    ¬ Nonempty (ProofCertificate k13_open_core_node) :=
  k14_final_audit.k13CertificateBlocked

/-- The final audit node itself describes the audit result.  It deliberately
remains an openBridge node because the scientific target is still open. -/
def k14_final_node : CertNode :=
  { status := .openBridge,
    statement := k13_open_core_node.status = .openBridge }

theorem k14_final_node_open : k14_final_node.status = .openBridge := rfl

theorem k14_final_node_not_certified :
    ¬ Nonempty (ProofCertificate k14_final_node) := by
  intro h
  rcases h with ⟨c⟩
  have hne : k14_final_node.status ≠ .provedProperty := by decide
  exact hne c.status_proved

end MCore
