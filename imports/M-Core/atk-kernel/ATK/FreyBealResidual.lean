import ATK.FreyBeal
import ATK.BealFermatDescent

/-!
# ATK — Curva de Frey no residual reduzido de Beal

Complementa `ATK.FreyBeal` (curva `Y² = X(X − A)(X + B)`, discriminante, elipticidade) com:

* `frey_c₄`: `c₄ = 16 (A² + AB + B²)` (logo `j = 256 (A² + AB + B²)³ / (AB(A + B))²`);
* `contraexemplo_da_frey`: **se Beal for falsa, existe uma solução dois a dois coprima no
  residual reduzido de `ATK.BealFermatDescent`** (fora de FLT(3), FLT(4) e das três assinaturas
  de descida) **cuja curva de Frey é elíptica**, com `Δ = 16 (aˣ bʸ cᶻ)²`.

Isto localiza o objeto onde um contraexemplo teria de viver. Não há ponte de modularidade: o
argumento de Ribet exige um primo comum aos três expoentes, que é justamente o caso já reduzido
a FLT; no residual (`mdc ≤ 2`) ele não se aplica. `OPEN_MATH` não muda.
-/

namespace ATK.FreyBeal

open ATK.Conditional.Beal

/-- `c₄ = 16 (A² + AB + B²)`. -/
theorem frey_c₄ {R : Type*} [CommRing R] (A B : R) :
    (frey A B).c₄ = 16 * (A ^ 2 + A * B + B ^ 2) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, frey_a₁, frey_a₂,
    frey_a₃, frey_a₄]
  ring

/-- **Um contraexemplo de Beal produz uma curva de Frey elíptica no residual reduzido.** -/
theorem contraexemplo_da_frey (h : ¬ BealConjecture) :
    ∃ a b c x y z : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 2 < x ∧ 2 < y ∧ 2 < z ∧
      ¬ 3 ∣ Nat.gcd x (Nat.gcd y z) ∧ ¬ 4 ∣ Nat.gcd x (Nat.gcd y z) ∧
      ¬ (4 ∣ x ∧ 4 ∣ y ∧ 2 ∣ z) ∧ ¬ (4 ∣ x ∧ 2 ∣ y ∧ 4 ∣ z) ∧ ¬ (2 ∣ x ∧ 4 ∣ y ∧ 4 ∣ z) ∧
      Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c ∧ a ^ x + b ^ y = c ^ z ∧
      (freyBeal a b x y).IsElliptic ∧
      (freyBeal a b x y).Δ = 16 * ((a : ℚ) ^ x * (b : ℚ) ^ y * (c : ℚ) ^ z) ^ 2 := by
  rw [ATK.BealFermatDescent.beal_iff_residual_descida_pairwise] at h
  by_contra hne
  apply h
  intro a b c x y z ha hb hc hx hy hz h3 h4 h442 h424 h244 hab hac hbc heq
  exact hne ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, h3, h4, h442, h424, h244, hab, hac, hbc,
    heq, freyBeal_isElliptic ha hb, freyBeal_Δ heq⟩

end ATK.FreyBeal

#print axioms ATK.FreyBeal.frey_c₄
#print axioms ATK.FreyBeal.contraexemplo_da_frey
