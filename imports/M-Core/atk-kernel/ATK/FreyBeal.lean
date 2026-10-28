import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# ATK — A curva de Frey–Hellegouarch de uma suposta solução de Beal

Para `A + B = C`, a curva `E_{A,B} : Y² = X(X − A)(X + B)` (Hellegouarch 1975, Frey 1986), como
`WeierstrassCurve` da Mathlib (`a₂ = B − A`, `a₄ = −AB`, demais coeficientes `0`):

* `frey_equation_iff`: a equação de Weierstrass é `Y² = X(X − A)(X + B)`;
* `frey_Δ`: `Δ = 16 (A B (A + B))²` em qualquer anel comutativo;
* `frey_Δ_eq_zero_iff`, `frey_isElliptic`: sobre `ℚ`, a curva é singular exatamente quando
  `A = 0`, `B = 0` ou `A + B = 0`; caso contrário é elíptica;
* `frey_two_torsion`: `(0, 0)`, `(A, 0)` e `(−B, 0)` estão na curva;
* `freyBeal`, `freyBeal_Δ`, `freyBeal_isElliptic`: para `aˣ + bʸ = cᶻ` com `a, b > 0`, a curva
  `E_{aˣ, bʸ}` é elíptica com `Δ = 16 (aˣ bʸ cᶻ)²`.

**Status e limite.** É a formalização de um objeto clássico; não reduz a obrigação O2. O argumento
de Fermat via esta curva usa modularidade (Breuil–Conrad–Diamond–Taylor 2001) **e** o rebaixamento
de nível de Ribet, que exige um mesmo primo `p` dividindo os três expoentes — justamente o caso que já
se reduz a FLT. No residual de O2 (`mdc(x, y, z) ≤ 2`) esse passo não se aplica. A Mathlib também não
tem modularidade de curvas elípticas, nem condutor, nem rebaixamento de nível.
-/

namespace ATK.FreyBeal

section General

variable {R : Type*} [CommRing R]

/-- Curva de Frey–Hellegouarch `Y² = X(X − A)(X + B) = X³ + (B − A)X² − AB·X`. -/
def frey (A B : R) : WeierstrassCurve R where
  a₁ := 0
  a₂ := B - A
  a₃ := 0
  a₄ := -(A * B)
  a₆ := 0

theorem frey_a₁ (A B : R) : (frey A B).a₁ = 0 := rfl
theorem frey_a₂ (A B : R) : (frey A B).a₂ = B - A := rfl
theorem frey_a₃ (A B : R) : (frey A B).a₃ = 0 := rfl
theorem frey_a₄ (A B : R) : (frey A B).a₄ = -(A * B) := rfl
theorem frey_a₆ (A B : R) : (frey A B).a₆ = 0 := rfl

/-- A equação de Weierstrass da curva de Frey é `Y² = X(X − A)(X + B)`. -/
theorem frey_equation_iff (A B x y : R) :
    (frey A B).toAffine.Equation x y ↔ y ^ 2 = x * (x - A) * (x + B) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  change y ^ 2 + 0 * x * y + 0 * y = x ^ 3 + (B - A) * x ^ 2 + (-(A * B)) * x + 0 ↔
    y ^ 2 = x * (x - A) * (x + B)
  constructor <;> intro h <;> linear_combination h

/-- **Discriminante**: `Δ = 16 (A B (A + B))²`. -/
theorem frey_Δ (A B : R) : (frey A B).Δ = 16 * (A * B * (A + B)) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, frey_a₁, frey_a₂, frey_a₃, frey_a₄, frey_a₆]
  ring

/-- Os três pontos de 2-torção `(0, 0)`, `(A, 0)`, `(−B, 0)` estão na curva. -/
theorem frey_two_torsion (A B : R) :
    (frey A B).toAffine.Equation 0 0 ∧ (frey A B).toAffine.Equation A 0 ∧
      (frey A B).toAffine.Equation (-B) 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [frey_equation_iff] <;> ring

end General

/-- Sobre `ℚ`: a curva de Frey é singular exatamente quando `A B (A + B) = 0`. -/
theorem frey_Δ_eq_zero_iff (A B : ℚ) : (frey A B).Δ = 0 ↔ A = 0 ∨ B = 0 ∨ A + B = 0 := by
  rw [frey_Δ]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · norm_num at h
    · rcases mul_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h) with h' | h'
      · rcases mul_eq_zero.mp h' with h3 | h3
        · exact Or.inl h3
        · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr h')
  · rintro (h | h | h)
    · rw [h]; ring
    · rw [h]; ring
    · rw [h]; ring

/-- Sobre `ℚ`, com `A, B, A + B ≠ 0`, a curva de Frey é elíptica (`IsElliptic` da Mathlib). -/
theorem frey_isElliptic {A B : ℚ} (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A + B ≠ 0) :
    (frey A B).IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  intro h
  rcases (frey_Δ_eq_zero_iff A B).mp h with h | h | h
  · exact hA h
  · exact hB h
  · exact hAB h

/-- Curva de Frey de uma suposta solução de Beal `aˣ + bʸ = cᶻ`: `Y² = X(X − aˣ)(X + bʸ)`. -/
def freyBeal (a b x y : ℕ) : WeierstrassCurve ℚ :=
  frey ((a : ℚ) ^ x) ((b : ℚ) ^ y)

/-- Numa solução de `aˣ + bʸ = cᶻ`, o discriminante é `16 (aˣ bʸ cᶻ)²`. -/
theorem freyBeal_Δ {a b c x y z : ℕ} (h : a ^ x + b ^ y = c ^ z) :
    (freyBeal a b x y).Δ = 16 * ((a : ℚ) ^ x * (b : ℚ) ^ y * (c : ℚ) ^ z) ^ 2 := by
  have hq : (a : ℚ) ^ x + (b : ℚ) ^ y = (c : ℚ) ^ z := by exact_mod_cast h
  rw [freyBeal, frey_Δ, hq]

/-- Com `a, b > 0`, a curva de Frey é elíptica. -/
theorem freyBeal_isElliptic {a b x y : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (freyBeal a b x y).IsElliptic := by
  have hA : (0 : ℚ) < (a : ℚ) ^ x := pow_pos (by exact_mod_cast ha) x
  have hB : (0 : ℚ) < (b : ℚ) ^ y := pow_pos (by exact_mod_cast hb) y
  exact frey_isElliptic hA.ne' hB.ne' (add_pos hA hB).ne'

/-- Exemplo: a solução não primitiva `2³ + 2³ = 2⁴` dá uma curva elíptica com `Δ = 16 (2³·2³·2⁴)²`. -/
theorem freyBeal_exemplo :
    (freyBeal 2 2 3 3).Δ = 16 * (((2 : ℕ) : ℚ) ^ 3 * ((2 : ℕ) : ℚ) ^ 3 * ((2 : ℕ) : ℚ) ^ 4) ^ 2 ∧
      (freyBeal 2 2 3 3).IsElliptic :=
  ⟨freyBeal_Δ (by norm_num : 2 ^ 3 + 2 ^ 3 = 2 ^ 4),
    freyBeal_isElliptic (by norm_num) (by norm_num)⟩

end ATK.FreyBeal

#print axioms ATK.FreyBeal.frey_equation_iff
#print axioms ATK.FreyBeal.frey_Δ
#print axioms ATK.FreyBeal.frey_two_torsion
#print axioms ATK.FreyBeal.frey_Δ_eq_zero_iff
#print axioms ATK.FreyBeal.frey_isElliptic
#print axioms ATK.FreyBeal.freyBeal_Δ
#print axioms ATK.FreyBeal.freyBeal_isElliptic
#print axioms ATK.FreyBeal.freyBeal_exemplo
