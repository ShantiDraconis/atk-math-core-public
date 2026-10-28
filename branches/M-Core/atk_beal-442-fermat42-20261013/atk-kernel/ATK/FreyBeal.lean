import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import ATK.BealFermatDescent

/-!
# ATK — A curva de Frey–Hellegouarch de uma solução de Beal

Para `A + B = C`, a curva de Frey–Hellegouarch é `Y² = X(X − A)(X + B)`. Para Beal,
`A = aˣ`, `B = bʸ`, `C = cᶻ`. Este arquivo a define como `WeierstrassCurve ℚ` da Mathlib e prova:

* `freyCurve_equation`: a equação de Weierstrass é exatamente `Y² = X(X − A)(X + B)`;
* `freyCurve_Δ`: `Δ = 16 (A · B · (A + B))²`; `freyCurve_c₄`: `c₄ = 16 (A² + AB + B²)`;
* `freyBeal_Δ`: numa solução, `Δ = 16 (aˣ bʸ cᶻ)²`;
* `freyBeal_isElliptic`: numa solução com `a, b, c > 0`, a curva é elíptica (`Δ` é unidade);
* `contraexemplo_da_frey`: **se Beal for falsa, existe uma solução dois a dois coprima no
  residual reduzido** (`ATK.BealFermatDescent`) **cuja curva de Frey é elíptica**, com o
  discriminante acima.

**O que NÃO está aqui, e por quê.** Para Fermat (`x = y = z = p`), o argumento é: a curva é
modular (Wiles; Breuil–Conrad–Diamond–Taylor 2001 para toda curva sobre ℚ) e, pelo rebaixamento
de nível de Ribet, a representação mod `p` viria de uma forma de nível 2, que não existe. O passo
de Ribet exige que `p` divida a valuação de `Δ` em cada primo de `abc`, isto é, `p ∣ 2x·v(a)`,
`p ∣ 2y·v(b)`, `p ∣ 2z·v(c)` — na prática, um primo comum aos três expoentes. Esse é o caso
`mdc(x, y, z)` com fator primo ímpar, que já se reduz a FLT. No residual da obrigação O2
(`mdc ≤ 2`, fora dos casos de descida) o argumento **não se aplica**: por isso uma "ponte"
`Beal ↔ (Frey modular → False)` seria falsa como teorema conhecido. Além disso, a Mathlib não
define formas modulares de curvas elípticas, então "modular" nem é um predicado disponível.

Objeto clássico (Hellegouarch 1975, Frey 1986); nova só a formalização. `OPEN_MATH` não muda.
-/

namespace ATK.FreyBeal

open ATK.Conditional.Beal

/-- Curva de Frey–Hellegouarch de `A + B = C`: `Y² = X(X − A)(X + B)`. -/
def freyCurve (A B : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := B - A
  a₃ := 0
  a₄ := -(A * B)
  a₆ := 0

/-- A curva de Frey de Beal: `A = aˣ`, `B = bʸ`. -/
def freyBeal (a b x y : ℕ) : WeierstrassCurve ℚ :=
  freyCurve ((a : ℚ) ^ x) ((b : ℚ) ^ y)

/-- A equação afim é `Y² = X(X − A)(X + B)`. -/
theorem freyCurve_equation (A B X Y : ℚ) :
    (freyCurve A B).toAffine.Equation X Y ↔ Y ^ 2 = X * (X - A) * (X + B) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [freyCurve, WeierstrassCurve.toAffine]
  constructor <;> intro h <;> linear_combination h

/-- **Discriminante**: `Δ = 16 (A · B · (A + B))²`. -/
theorem freyCurve_Δ (A B : ℚ) : (freyCurve A B).Δ = 16 * (A * B * (A + B)) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, freyCurve]
  ring

/-- `c₄ = 16 (A² + AB + B²)`. -/
theorem freyCurve_c₄ (A B : ℚ) : (freyCurve A B).c₄ = 16 * (A ^ 2 + A * B + B ^ 2) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, freyCurve]
  ring

/-- Numa solução de `aˣ + bʸ = cᶻ`: `Δ = 16 (aˣ bʸ cᶻ)²`. -/
theorem freyBeal_Δ {a b c x y z : ℕ} (h : a ^ x + b ^ y = c ^ z) :
    (freyBeal a b x y).Δ = 16 * ((a : ℚ) ^ x * (b : ℚ) ^ y * (c : ℚ) ^ z) ^ 2 := by
  have hq : (a : ℚ) ^ x + (b : ℚ) ^ y = (c : ℚ) ^ z := by exact_mod_cast h
  rw [freyBeal, freyCurve_Δ, hq]

/-- Numa solução com `a, b, c > 0`, a curva de Frey é **elíptica**. -/
theorem freyBeal_isElliptic {a b c x y z : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ x + b ^ y = c ^ z) : (freyBeal a b x y).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, freyBeal_Δ h]
  exact isUnit_iff_ne_zero.mpr (by positivity)

/-- **Um contraexemplo de Beal produz uma curva de Frey elíptica**, já no residual reduzido
(dois a dois coprimo, fora de FLT(3), FLT(4) e das três assinaturas de descida). -/
theorem contraexemplo_da_frey (h : ¬ BealConjecture) :
    ∃ a b c x y z : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 2 < x ∧ 2 < y ∧ 2 < z ∧
      ¬ 3 ∣ Nat.gcd x (Nat.gcd y z) ∧ ¬ 4 ∣ Nat.gcd x (Nat.gcd y z) ∧
      Nat.Coprime a b ∧ Nat.Coprime a c ∧ Nat.Coprime b c ∧ a ^ x + b ^ y = c ^ z ∧
      (freyBeal a b x y).IsElliptic ∧
      (freyBeal a b x y).Δ = 16 * ((a : ℚ) ^ x * (b : ℚ) ^ y * (c : ℚ) ^ z) ^ 2 := by
  rw [ATK.BealFermatDescent.beal_iff_residual_descida_pairwise] at h
  by_contra hne
  apply h
  intro a b c x y z ha hb hc hx hy hz h3 h4 _ _ _ hab hac hbc heq
  exact hne ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, h3, h4, hab, hac, hbc, heq,
    freyBeal_isElliptic ha hb hc heq, freyBeal_Δ heq⟩

end ATK.FreyBeal

#print axioms ATK.FreyBeal.freyCurve_equation
#print axioms ATK.FreyBeal.freyCurve_Δ
#print axioms ATK.FreyBeal.freyCurve_c₄
#print axioms ATK.FreyBeal.freyBeal_Δ
#print axioms ATK.FreyBeal.freyBeal_isElliptic
#print axioms ATK.FreyBeal.contraexemplo_da_frey
