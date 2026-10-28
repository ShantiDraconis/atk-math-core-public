/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat

/-!
# Cópia do enunciado da conjectura de Beal do formal-conjectures (Google DeepMind)

Fonte: `google-deepmind/formal-conjectures`, `FormalConjectures/Wikipedia/BealConjecture.lean`
(licença Apache 2.0, cabeçalho original mantido acima). Só a definição foi copiada, sem mudar o
significado, dentro do namespace `ATK.FC` e sem o sistema de módulos. O teorema
`beal_conjecture` de lá é um `sorry` (problema aberto) e **não** foi copiado.
-/

namespace ATK.FC

/-- A conjectura de Beal, como enunciada no formal-conjectures. -/
def bealConjecture : Prop := ∀ {A B C x y z : ℕ},
    A ≠ 0 → B ≠ 0 → C ≠ 0 → 2 < x → 2 < y → 2 < z →
    A^x + B^y = C^z → 1 < Finset.gcd {A, B, C} id

end ATK.FC
