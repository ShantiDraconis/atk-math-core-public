import Mathlib.Algebra.Polynomial.Basic

/-!
# ATK — Polinômios inteiros por listas de coeficientes (reflexão para certificados)

`poly [a₀, a₁, …, aₙ] = a₀ + X·(a₁ + X·(⋯ + X·aₙ))`. Soma, produto por escalar e produto de listas
(`soma`, `escala`, `produto`) são funções computáveis, e `poly` as transporta para `ℤ[X]`
(`poly_soma`, `poly_escala`, `poly_produto`); zeros à direita não mudam o polinômio
(`poly_ceros`). Assim uma identidade polinomial grande em `ℤ[X]` reduz-se a uma igualdade de
listas de inteiros, que o kernel confere por cálculo (`decide +kernel`), sem `ring` sobre termos
enormes. Usado pelos certificados de `ATK.FermatDezessete`.
-/

open Polynomial

namespace ATK.PolyLista

/-- O polinômio de uma lista de coeficientes (forma de Horner). -/
noncomputable def poly : List ℤ → ℤ[X]
  | [] => 0
  | a :: l => C a + X * poly l

/-- Soma de listas de coeficientes. -/
def soma : List ℤ → List ℤ → List ℤ
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: soma l m

/-- Produto por escalar. -/
def escala (c : ℤ) : List ℤ → List ℤ
  | [] => []
  | a :: l => (c * a) :: escala c l

/-- Produto de listas de coeficientes. -/
def produto : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a :: l, m => soma (escala a m) (0 :: produto l m)

theorem poly_nil : poly [] = 0 := rfl

theorem poly_cons (a : ℤ) (l : List ℤ) : poly (a :: l) = C a + X * poly l := rfl

theorem poly_soma (l m : List ℤ) : poly (soma l m) = poly l + poly m := by
  induction l generalizing m with
  | nil => simp [soma, poly]
  | cons a l ih =>
    cases m with
    | nil => simp [soma, poly]
    | cons b m =>
      simp only [soma, poly, ih, map_add]
      ring

theorem poly_escala (c : ℤ) (l : List ℤ) : poly (escala c l) = C c * poly l := by
  induction l with
  | nil => simp [escala, poly]
  | cons a l ih =>
    simp only [escala, poly, ih, map_mul]
    ring

theorem poly_produto (l m : List ℤ) : poly (produto l m) = poly l * poly m := by
  induction l with
  | nil => simp [produto, poly]
  | cons a l ih =>
    simp only [produto, poly_soma, poly_escala, poly, ih, map_zero]
    ring

theorem poly_replicate (k : ℕ) : poly (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, poly, ih]

theorem poly_ceros (l : List ℤ) (k : ℕ) : poly (l ++ List.replicate k 0) = poly l := by
  induction l with
  | nil =>
    rw [List.nil_append, poly_replicate, poly_nil]
  | cons a l ih => simp [poly, ih]

/-- Uma constante. -/
theorem poly_const (c : ℤ) : poly [c] = C c := by simp [poly]

/-- Igualdade de polinômios a partir de igualdade de listas, a menos de zeros à direita. -/
theorem igual_de_listas {l m : List ℤ} (k j : ℕ)
    (h : l ++ List.replicate k 0 = m ++ List.replicate j 0) : poly l = poly m := by
  rw [← poly_ceros l k, h, poly_ceros]

end ATK.PolyLista

#print axioms ATK.PolyLista.poly_nil
#print axioms ATK.PolyLista.poly_cons
#print axioms ATK.PolyLista.poly_soma
#print axioms ATK.PolyLista.poly_escala
#print axioms ATK.PolyLista.poly_produto
#print axioms ATK.PolyLista.poly_replicate
#print axioms ATK.PolyLista.poly_ceros
#print axioms ATK.PolyLista.poly_const
#print axioms ATK.PolyLista.igual_de_listas
