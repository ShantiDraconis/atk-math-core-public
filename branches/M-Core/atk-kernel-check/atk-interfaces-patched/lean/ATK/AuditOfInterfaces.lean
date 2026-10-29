import ATK.KernelInterfaces
import ATK.Terminal.SevenEndpoints

/-!
Auditoria (ATK-kernel) das interfaces acima — arquivo NOVO, não faz parte dos originais.

* `obligation_iff` — ter um habitante de `Obligation T` é exatamente o mesmo que provar `T`.
  Logo `seven_targets` não reduz nada: pedir sete `Obligation` é pedir as sete conjecturas.
* `endpoint_vacuous` — `Endpoint` com campos `Prop` livres admite habitante trivial; só tem
  conteúdo quando `concreteStatement` for a definição matemática exata da conjectura.
-/

namespace ATK.AuditOfInterfaces

open ATK.KernelInterfaces ATK.Terminal

theorem obligation_iff (T : Prop) : Nonempty (Obligation T) ↔ T :=
  ⟨fun ⟨o⟩ => discharge o, fun h => ⟨{ Material := True, material := trivial, bridge := fun _ => h }⟩⟩

theorem endpoint_vacuous : ∃ e : Endpoint, e.materialObligation ∧ e.concreteStatement :=
  ⟨{ concreteStatement := True, materialObligation := True, materialImpliesStatement := fun _ => trivial },
   trivial, trivial⟩

end ATK.AuditOfInterfaces
