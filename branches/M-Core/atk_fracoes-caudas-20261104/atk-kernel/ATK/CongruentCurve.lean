import ATK.FermatRightTriangle
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# ATK — A curva `E : y² = x³ − x` sobre `ℚ`: `E(ℚ) = {O, (0, 0), (1, 0), (−1, 0)}`

A Mathlib v4.34.1 tem `WeierstrassCurve` e `WeierstrassCurve.Affine.Point`, mas nenhum cálculo de
`E(ℚ)` para uma curva concreta e nenhuma noção de posto de Mordell–Weil. Este arquivo determina
todos os pontos racionais da curva do número congruente `1`, no próprio objeto da Mathlib:

* `y_eq_zero`, `rational_points`: todo ponto racional afim de `y² = x³ − x` tem `y = 0` e
  `x ∈ {0, 1, −1}`;
* `E`: a curva como `WeierstrassCurve ℚ` (`a₄ = −1`, demais coeficientes `0`);
* `E_point_cases`: todo `P : E.toAffine.Point` é `O` ou um dos três pontos de 2-torção;
* `E_torsion_points`: os três pontos são de fato pontos não singulares de `E`;
* `point_of_fermatM42`: o mapa explícito `(a, b, c) ↦ (a²/b², ac/b³)` leva uma solução de
  `a⁴ − b⁴ = c²` (`b, c ≠ 0`) a um ponto racional de `E` com `y ≠ 0`;
* `fermatM42_iff_point`: soluções de `a⁴ − b⁴ = c²` ⟺ pontos de `E` com `y ≠ 0`.

Logo `E(ℚ)` é finito com 4 pontos (posto 0, com os três pontos de 2-torção). A Mathlib não define
posto, e o isomorfismo de grupo `E(ℚ) ≅ ℤ/2 × ℤ/2` não é formalizado aqui.

Sobre `fermatM42_iff_point`: os dois lados são falsos (`not_fermat_4m4`, `y_eq_zero`), então o
conteúdo útil é o mapa de `point_of_fermatM42` (→) e o triângulo de área 1 de `y_eq_zero` (←),
não o "⟺" em si.

Prova: um ponto `(x, y)` com `y ≠ 0` daria o triângulo retângulo racional de catetos
`(x² − 1)/y`, `2x/y`, hipotenusa `(x² + 1)/y` e área `(x³ − x)/y² = 1`, contra
`ATK.FermatRightTriangle.one_not_congruent` (descida de Fermat para `x⁴ − y⁴ ≠ z²`).

Status: clássico (Fermat). É o caso de **uma** curva; não é a conjectura BSD (O6/O7 continuam
abertas) e não constrói a ligação L4 (função L / posto em geral).
-/

namespace ATK.CongruentCurve

open ATK.FermatRightTriangle

/-- Todo ponto racional afim de `y² = x³ − x` tem `y = 0`. -/
theorem y_eq_zero {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) : y = 0 := by
  by_contra hy
  have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 hy
  have harea : (x ^ 2 - 1) / y * (2 * x / y) / 2 = 1 := by
    have e : (x ^ 2 - 1) / y * (2 * x / y) / 2 = (x ^ 3 - x) / y ^ 2 := by ring
    rw [e, ← h, div_self hy2]
  exact one_not_congruent (a := (x ^ 2 - 1) / y) (b := 2 * x / y) (c := (x ^ 2 + 1) / y)
    (by ring) harea

/-- Pontos racionais afins de `y² = x³ − x`: `y = 0` e `x ∈ {0, 1, −1}`. -/
theorem rational_points {x y : ℚ} (h : y ^ 2 = x ^ 3 - x) :
    y = 0 ∧ (x = 0 ∨ x = 1 ∨ x = -1) := by
  have hy := y_eq_zero h
  refine ⟨hy, ?_⟩
  subst hy
  have h0 : x * ((x - 1) * (x + 1)) = 0 := by linear_combination -h
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact Or.inl h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (by linarith))

/-- Forma "se e somente se": exatamente três pontos afins. -/
theorem rational_points_iff (x y : ℚ) :
    y ^ 2 = x ^ 3 - x ↔ (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) := by
  constructor
  · intro h
    obtain ⟨hy, hx | hx | hx⟩ := rational_points h
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr (Or.inl ⟨hx, hy⟩)
    · exact Or.inr (Or.inr ⟨hx, hy⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num

/-- `E : y² = x³ − x` como `WeierstrassCurve ℚ` da Mathlib. -/
def E : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -1
  a₆ := 0

/-- A equação de Weierstrass da Mathlib para `E` é `y² = x³ − x`. -/
theorem E_equation_iff (x y : ℚ) : E.toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - x := by
  rw [WeierstrassCurve.Affine.equation_iff]
  change y ^ 2 + 0 * x * y + 0 * y = x ^ 3 + 0 * x ^ 2 + (-1) * x + 0 ↔ y ^ 2 = x ^ 3 - x
  constructor <;> intro h <;> linear_combination h

/-- Todo ponto afim de `E` é não singular. -/
theorem E_nonsingular {x y : ℚ} (h : E.toAffine.Equation x y) : E.toAffine.Nonsingular x y := by
  rw [WeierstrassCurve.Affine.nonsingular_iff]
  refine ⟨h, Or.inl ?_⟩
  change (0 : ℚ) * y ≠ 3 * x ^ 2 + 2 * 0 * x + (-1)
  obtain ⟨-, hx⟩ := rational_points ((E_equation_iff x y).mp h)
  rcases hx with rfl | rfl | rfl <;> norm_num

/-- **`E(ℚ)` tem 4 pontos**: todo ponto é `O` ou `(x, 0)` com `x ∈ {0, 1, −1}`. -/
theorem E_point_cases (P : E.toAffine.Point) :
    P = .zero ∨ ∃ (x : ℚ) (h : E.toAffine.Nonsingular x 0),
      P = .some x 0 h ∧ (x = 0 ∨ x = 1 ∨ x = -1) := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y h =>
    right
    have heq : E.toAffine.Equation x y := ((WeierstrassCurve.Affine.nonsingular_iff x y).mp h).1
    obtain ⟨hy, hx⟩ := rational_points ((E_equation_iff x y).mp heq)
    subst hy
    exact ⟨x, h, rfl, hx⟩

/-- Os três pontos de 2-torção são pontos não singulares de `E`. -/
theorem E_torsion_points :
    E.toAffine.Nonsingular 0 0 ∧ E.toAffine.Nonsingular 1 0 ∧ E.toAffine.Nonsingular (-1) 0 :=
  ⟨E_nonsingular ((E_equation_iff 0 0).mpr (by norm_num)),
    E_nonsingular ((E_equation_iff 1 0).mpr (by norm_num)),
    E_nonsingular ((E_equation_iff (-1) 0).mpr (by norm_num))⟩

/-- **Solução ⇒ ponto**: `a⁴ − b⁴ = c²` com `b, c ≠ 0` dá o ponto racional `(a²/b², ac/b³)` de
`y² = x³ − x`, com `y ≠ 0`. -/
theorem point_of_fermatM42 {a b c : ℤ} (hb : b ≠ 0) (hc : c ≠ 0) (h : a ^ 4 - b ^ 4 = c ^ 2) :
    ((a * c : ℚ) / b ^ 3) ^ 2 = ((a : ℚ) ^ 2 / b ^ 2) ^ 3 - (a : ℚ) ^ 2 / b ^ 2 ∧
      (a * c : ℚ) / b ^ 3 ≠ 0 := by
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hq : (a : ℚ) ^ 4 - (b : ℚ) ^ 4 = (c : ℚ) ^ 2 := by exact_mod_cast h
  have hu : (b : ℚ) * (b : ℚ)⁻¹ = 1 := mul_inv_cancel₀ hb'
  have ha : a ≠ 0 := FermatM42.a_ne_zero ⟨hb, hc, h⟩
  refine ⟨?_, div_ne_zero (mul_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hc))
    (pow_ne_zero 3 hb')⟩
  linear_combination (-(a : ℚ) ^ 2 * ((b : ℚ)⁻¹) ^ 6) * hq +
    (-(a : ℚ) ^ 2 * ((b : ℚ)⁻¹) ^ 2 * ((b : ℚ) * (b : ℚ)⁻¹ + 1) *
      ((b : ℚ) ^ 2 * ((b : ℚ)⁻¹) ^ 2 + 1)) * hu

/-- Soluções de `a⁴ − b⁴ = c²` (`b, c ≠ 0`) ⟺ pontos racionais de `y² = x³ − x` com `y ≠ 0`.
(→ pelo mapa explícito; ← pelo triângulo de área 1. Os dois lados são vazios.) -/
theorem fermatM42_iff_point :
    (∃ a b c : ℤ, b ≠ 0 ∧ c ≠ 0 ∧ a ^ 4 - b ^ 4 = c ^ 2) ↔
      (∃ x y : ℚ, y ≠ 0 ∧ y ^ 2 = x ^ 3 - x) := by
  constructor
  · rintro ⟨a, b, c, hb, hc, h⟩
    obtain ⟨h1, h2⟩ := point_of_fermatM42 hb hc h
    exact ⟨_, _, h2, h1⟩
  · rintro ⟨x, y, hy, h⟩
    exact absurd (y_eq_zero h) hy

end ATK.CongruentCurve

#print axioms ATK.CongruentCurve.y_eq_zero
#print axioms ATK.CongruentCurve.rational_points
#print axioms ATK.CongruentCurve.rational_points_iff
#print axioms ATK.CongruentCurve.E_equation_iff
#print axioms ATK.CongruentCurve.E_nonsingular
#print axioms ATK.CongruentCurve.E_point_cases
#print axioms ATK.CongruentCurve.E_torsion_points
#print axioms ATK.CongruentCurve.point_of_fermatM42
#print axioms ATK.CongruentCurve.fermatM42_iff_point
