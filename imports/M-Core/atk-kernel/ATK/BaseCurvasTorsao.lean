/-
ATK.Base (B1a) — Pontos de ordem 2 em curvas elípticas.

Primeiro degrau da base de torsão para BSD (o caminho segue para Nagell–Lutz e redução mod p).
A Mathlib tem o grupo `W.Point` dos pontos de uma curva de Weierstrass, mas nenhuma descrição da
torsão.  Para uma curva com `a₁ = a₃ = 0` (forma `y² = x³ + a₂x² + a₄x + a₆`) sobre um corpo de
característica ≠ 2:

* **`ordem_dois_iff`**: um ponto afim `(x, y)` satisfaz `P + P = 0` ⟺ `y = 0`;
* **`ordem_dois_iff_raiz`**: ⟺ `x` é raiz da cúbica `x³ + a₂x² + a₄x + a₆`;
* `ordem_dois_de_raiz`: toda raiz da cúbica dá um ponto `(x, 0)` de ordem 2.

Assim `E[2] = {O} ∪ {(r, 0) : r raiz}` — a 2-torsão é lida das raízes, como na 2-descida.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

namespace ATK.BaseCurvasTorsao

open WeierstrassCurve WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve.Affine F}

/-- `P + P = 0 ⟺ P = −P` em qualquer grupo aditivo. -/
theorem dobro_zero_iff (P : W.Point) : P + P = 0 ↔ P = -P := add_eq_zero_iff_eq_neg

/-- **Pontos de ordem 2**: com `a₁ = a₃ = 0` e `2 ≠ 0`, `(x, y) + (x, y) = 0 ⟺ y = 0`. -/
theorem ordem_dois_iff (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (h2 : (2 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) : Point.some x y h + Point.some x y h = 0 ↔ y = 0 := by
  rw [dobro_zero_iff, Point.neg_some]
  simp only [Point.some.injEq, true_and, negY, ha₁, ha₃, zero_mul, sub_zero]
  constructor
  · intro hy
    have : 2 * y = 0 := by linear_combination hy
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' h2
    · exact h'
  · intro hy; rw [hy, neg_zero]

/-- **2-torsão ⟺ raiz da cúbica.** -/
theorem ordem_dois_iff_raiz (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (h2 : (2 : F) ≠ 0) {x y : F}
    (h : W.Nonsingular x y) :
    Point.some x y h + Point.some x y h = 0 ↔ x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ = 0 := by
  rw [ordem_dois_iff ha₁ ha₃ h2 h]
  have heq := (equation_iff x y).mp h.1
  rw [ha₁, ha₃] at heq
  simp only [zero_mul, mul_zero, add_zero] at heq
  constructor
  · intro hy; rw [← heq, hy]; ring
  · intro hc
    rw [hc] at heq
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp heq

/-- Toda raiz `r` da cúbica com `(r, 0)` não singular dá um ponto de ordem 2. -/
theorem ordem_dois_de_raiz (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (h2 : (2 : F) ≠ 0) {r : F}
    (h : W.Nonsingular r 0) : Point.some r 0 h + Point.some r 0 h = 0 :=
  (ordem_dois_iff ha₁ ha₃ h2 h).mpr rfl

end ATK.BaseCurvasTorsao

#print axioms ATK.BaseCurvasTorsao.dobro_zero_iff
#print axioms ATK.BaseCurvasTorsao.ordem_dois_iff
#print axioms ATK.BaseCurvasTorsao.ordem_dois_iff_raiz
#print axioms ATK.BaseCurvasTorsao.ordem_dois_de_raiz
