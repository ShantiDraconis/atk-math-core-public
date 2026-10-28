/-
ATK — Beal para polinômios: a parte provável do análogo de corpo de funções.

A Mathlib prova (Baek–Lee, via o teorema de Mason–Stothers, o "abc para polinômios") que a
equação de Fermat–Catalan `u aᵖ + v b^q + w cʳ = 0` não tem soluções coprimas não constantes
quando `qr + rp + pq ≤ pqr` (isto é, `1/p + 1/q + 1/r ≤ 1`).  Daí, no kernel:

* **`beal_polinomial`**: sobre um corpo `k` em que `x, y, z` não se anulam, se `fˣ + gʸ = hᶻ` com
  `f, g, h ≠ 0`, `f, g` coprimos e `x, y, z > 2`, então `f, g, h` são **constantes**;
* `beal_polinomial_char0`: em característica 0 não há hipótese sobre `x, y, z`;
* **`contraste_7_3_2`**: na assinatura `(7, 3, 2)` o análogo polinomial ainda vale (não há solução
  coprima não constante), mas os inteiros têm `2⁷ + 17³ = 71²`.  A conjectura de Beal para
  inteiros é genuinamente aritmética: o "abc inteiro" (aberto) é o que falta para transportar
  o argumento de Mason–Stothers.

Nada aqui prova Beal para inteiros.
-/
import ATK.RefutacoesBeal
import Mathlib.NumberTheory.FLT.Polynomial

namespace ATK.BealPolinomial

open Polynomial

/-- `x, y, z > 2` ⇒ `yz + zx + xy ≤ xyz` (isto é, `1/x + 1/y + 1/z ≤ 1`). -/
theorem desigualdade_beal {x y z : ℕ} (hx : 2 < x) (hy : 2 < y) (hz : 2 < z) :
    y * z + z * x + x * y ≤ x * y * z := by
  have h1 : 3 * (y * z) ≤ x * (y * z) := Nat.mul_le_mul_right _ hx
  have h2 : 3 * (z * x) ≤ y * (z * x) := Nat.mul_le_mul_right _ hy
  have h3 : 3 * (x * y) ≤ z * (x * y) := Nat.mul_le_mul_right _ hz
  have e2 : y * (z * x) = x * y * z := by ring
  have e3 : z * (x * y) = x * y * z := by ring
  have e1 : x * (y * z) = x * y * z := by ring
  omega

/-- **Beal para polinômios.** -/
theorem beal_polinomial {k : Type*} [Field k] {x y z : ℕ} (hx : 2 < x) (hy : 2 < y) (hz : 2 < z)
    (chx : (x : k) ≠ 0) (chy : (y : k) ≠ 0) (chz : (z : k) ≠ 0)
    {f g h : k[X]} (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0) (hfg : IsCoprime f g)
    (heq : f ^ x + g ^ y = h ^ z) :
    f.natDegree = 0 ∧ g.natDegree = 0 ∧ h.natDegree = 0 := by
  have heq' : C 1 * f ^ x + C 1 * g ^ y + C (-1) * h ^ z = 0 := by
    simp only [map_one, one_mul, map_neg, neg_mul]
    rw [heq]
    ring
  exact Polynomial.flt_catalan (by omega) (by omega) (by omega) (desigualdade_beal hx hy hz)
    chx chy chz hf hg hh hfg one_ne_zero one_ne_zero (neg_ne_zero.mpr one_ne_zero) heq'

/-- Em característica 0. -/
theorem beal_polinomial_char0 {k : Type*} [Field k] [CharZero k] {x y z : ℕ} (hx : 2 < x)
    (hy : 2 < y) (hz : 2 < z) {f g h : k[X]} (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (hfg : IsCoprime f g) (heq : f ^ x + g ^ y = h ^ z) :
    f.natDegree = 0 ∧ g.natDegree = 0 ∧ h.natDegree = 0 :=
  beal_polinomial hx hy hz (Nat.cast_ne_zero.mpr (by omega)) (Nat.cast_ne_zero.mpr (by omega))
    (Nat.cast_ne_zero.mpr (by omega)) hf hg hh hfg heq

/-- Fermat–Catalan polinomial na assinatura `(7, 3, 2)` sobre ℚ. -/
theorem fermat_catalan_poly_7_3_2 {f g h : ℚ[X]} (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (hfg : IsCoprime f g) (heq : f ^ 7 + g ^ 3 = h ^ 2) :
    f.natDegree = 0 ∧ g.natDegree = 0 ∧ h.natDegree = 0 := by
  have heq' : C 1 * f ^ 7 + C 1 * g ^ 3 + C (-1) * h ^ 2 = 0 := by
    simp only [map_one, one_mul, map_neg, neg_mul]
    rw [heq]
    ring
  exact Polynomial.flt_catalan (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hf hg hh hfg one_ne_zero one_ne_zero
    (neg_ne_zero.mpr one_ne_zero) heq'

/-- **Contraste**: o análogo polinomial vale em `(7, 3, 2)`, mas os inteiros têm a solução
coprima `2⁷ + 17³ = 71²`. -/
theorem contraste_7_3_2 :
    (∀ {f g h : ℚ[X]}, f ≠ 0 → g ≠ 0 → h ≠ 0 → IsCoprime f g → f ^ 7 + g ^ 3 = h ^ 2 →
        f.natDegree = 0 ∧ g.natDegree = 0 ∧ h.natDegree = 0) ∧
      (2 : ℕ) ^ 7 + 17 ^ 3 = 71 ^ 2 ∧ Nat.Coprime 2 17 :=
  ⟨fun hf hg hh hfg heq => fermat_catalan_poly_7_3_2 hf hg hh hfg heq,
    ATK.RefutacoesBeal.fc4, by norm_num⟩

end ATK.BealPolinomial

#print axioms ATK.BealPolinomial.desigualdade_beal
#print axioms ATK.BealPolinomial.beal_polinomial
#print axioms ATK.BealPolinomial.beal_polinomial_char0
#print axioms ATK.BealPolinomial.fermat_catalan_poly_7_3_2
#print axioms ATK.BealPolinomial.contraste_7_3_2
