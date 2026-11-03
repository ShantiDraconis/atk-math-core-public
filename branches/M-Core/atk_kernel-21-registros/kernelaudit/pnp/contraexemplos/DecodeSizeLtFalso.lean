import MCore.Real.CanonicalCircuitBits

/-!
Contraexemplo verificado no kernel para `P01DecodeCoreLaws.decodeCircuitCore_size_lt`
(ramos `atk/p01-*` de m-core-p-vs-np):

  `decodeCircuitCore fuel bits = some (phi, tail) → CircuitK1.size phi < fuel`

é falso. Com `fuel = 1` e `bits = [false, false, false, false]` o decodificador devolve
`(.input 0, [])`, cujo tamanho é `1`, e `1 < 1` é falso. O combustível limita a profundidade,
não o tamanho (num `and` os dois filhos gastam o mesmo combustível).
-/

namespace MCore
namespace Real
namespace AuditoriaP01

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits

theorem decode_exemplo :
    decodeCircuitCore 1 [false, false, false, false] = some (.input 0, []) := by
  first | rfl | decide | simp [decodeCircuitCore, decodeNat]

theorem decodeCircuitCore_size_lt_falso :
    ¬ ∀ (fuel : Nat) (bits : BitString) (phi : Circuit) (tail : BitString),
        decodeCircuitCore fuel bits = some (phi, tail) → CircuitK1.size phi < fuel := by
  intro h
  have h1 := h 1 [false, false, false, false] (.input 0) [] decode_exemplo
  revert h1
  first | decide | simp [CircuitK1.size]

end AuditoriaP01
end Real
end MCore

#print axioms MCore.Real.AuditoriaP01.decode_exemplo
#print axioms MCore.Real.AuditoriaP01.decodeCircuitCore_size_lt_falso
