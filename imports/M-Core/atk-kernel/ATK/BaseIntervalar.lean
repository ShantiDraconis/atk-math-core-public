/-
ATK.Base — Aritmética intervalar certificada sobre ℚ.

Infraestrutura comum às frentes de prova assistida por computador do programa de ataque
(`ATAQUE.md`): explosão de Navier–Stokes pelo método de Chen–Hou, certificados de sinal de Ξ
(alvo R5 de `ATK.AtaqueRH`), valores de funções L.  O cálculo é feito em `ℚ` (decidível,
verificável por `norm_num`/`decide`); os teoremas de **correção** transportam o resultado para `ℝ`.

* `Intervalo`: `[lo, hi]` com extremos racionais; `contem I x : lo ≤ x ≤ hi`;
* **`contem_add`**, **`contem_neg`**, **`contem_sub`**, **`contem_mul`**: as operações são
  corretas (o produto usa o mínimo e o máximo dos quatro cantos);
* **`pos_de_contem`**, **`neg_de_contem`**: um intervalo estritamente positivo (negativo)
  certifica o sinal;
* `expI q n`: série de Taylor de grau `n` com o resto de Lagrange da Mathlib
  (`Real.exp_bound`); **`contem_exp`**: `e^q ∈ expI q n` para `|q| ≤ 1`;
* `piI`: **`contem_pi`**: `π ∈ [3.14, 3.15]`;
* **`exemplo_exp`**: `e^{−1} < 0,37`, certificado por um intervalo calculado em ℚ.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Rat.Cast.Order

namespace ATK.BaseIntervalar

open Finset

/-- Intervalo fechado com extremos racionais. -/
structure Intervalo where
  lo : ℚ
  hi : ℚ

namespace Intervalo

/-- `x ∈ [lo, hi]`. -/
def contem (I : Intervalo) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- Intervalo degenerado. -/
def ponto (q : ℚ) : Intervalo := ⟨q, q⟩

def add (I J : Intervalo) : Intervalo := ⟨I.lo + J.lo, I.hi + J.hi⟩

def neg (I : Intervalo) : Intervalo := ⟨-I.hi, -I.lo⟩

def sub (I J : Intervalo) : Intervalo := add I (neg J)

/-- Produto: mínimo e máximo dos quatro cantos. -/
def mul (I J : Intervalo) : Intervalo :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

theorem contem_ponto (q : ℚ) : (ponto q).contem q := ⟨le_rfl, le_rfl⟩

theorem contem_add {I J : Intervalo} {x y : ℝ} (hx : I.contem x) (hy : J.contem y) :
    (add I J).contem (x + y) := by
  constructor <;> simp only [add, Rat.cast_add] <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem contem_neg {I : Intervalo} {x : ℝ} (hx : I.contem x) : (neg I).contem (-x) := by
  constructor <;> simp only [neg, Rat.cast_neg] <;> linarith [hx.1, hx.2]

theorem contem_sub {I J : Intervalo} {x y : ℝ} (hx : I.contem x) (hy : J.contem y) :
    (sub I J).contem (x - y) := by
  rw [sub_eq_add_neg]
  exact contem_add hx (contem_neg hy)

/-- Cota inferior do produto em reais. -/
theorem min_le_mul {a b c d x y : ℝ} (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  have h1 : min (a * y) (b * y) ≤ x * y := by
    rcases le_total 0 y with hy | hy
    · exact min_le_of_left_le (by nlinarith)
    · exact min_le_of_right_le (by nlinarith)
  have h2 : min (a * c) (a * d) ≤ a * y := by
    rcases le_total 0 a with h | h
    · exact min_le_of_left_le (by nlinarith)
    · exact min_le_of_right_le (by nlinarith)
  have h3 : min (b * c) (b * d) ≤ b * y := by
    rcases le_total 0 b with h | h
    · exact min_le_of_left_le (by nlinarith)
    · exact min_le_of_right_le (by nlinarith)
  exact (min_le_min h2 h3).trans h1

/-- Cota superior do produto em reais. -/
theorem mul_le_max {a b c d x y : ℝ} (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have h1 : x * y ≤ max (a * y) (b * y) := by
    rcases le_total 0 y with hy | hy
    · exact le_max_of_le_right (by nlinarith)
    · exact le_max_of_le_left (by nlinarith)
  have h2 : a * y ≤ max (a * c) (a * d) := by
    rcases le_total 0 a with h | h
    · exact le_max_of_le_right (by nlinarith)
    · exact le_max_of_le_left (by nlinarith)
  have h3 : b * y ≤ max (b * c) (b * d) := by
    rcases le_total 0 b with h | h
    · exact le_max_of_le_right (by nlinarith)
    · exact le_max_of_le_left (by nlinarith)
  exact h1.trans (max_le_max h2 h3)

theorem contem_mul {I J : Intervalo} {x y : ℝ} (hx : I.contem x) (hy : J.contem y) :
    (mul I J).contem (x * y) := by
  constructor
  · simp only [mul]
    push_cast
    exact min_le_mul hx.1 hx.2 hy.1 hy.2
  · simp only [mul]
    push_cast
    exact mul_le_max hx.1 hx.2 hy.1 hy.2

/-- Um intervalo estritamente positivo certifica o sinal. -/
theorem pos_de_contem {I : Intervalo} {x : ℝ} (hx : I.contem x) (h : 0 < I.lo) : 0 < x := by
  have : (0 : ℝ) < I.lo := by exact_mod_cast h
  linarith [hx.1]

theorem neg_de_contem {I : Intervalo} {x : ℝ} (hx : I.contem x) (h : I.hi < 0) : x < 0 := by
  have : (I.hi : ℝ) < 0 := by exact_mod_cast h
  linarith [hx.2]

theorem lt_de_contem {I : Intervalo} {x : ℝ} {q : ℚ} (hx : I.contem x) (h : I.hi < q) :
    x < q := by
  have : (I.hi : ℝ) < q := by exact_mod_cast h
  linarith [hx.2]

end Intervalo

open Intervalo

/-! ### Exponencial e π -/

/-- Soma de Taylor `Σ_{i<n} qⁱ/i!` em ℚ. -/
def taylorExp (q : ℚ) (n : ℕ) : ℚ := ∑ i ∈ range n, q ^ i / (i.factorial : ℚ)

/-- Resto de Lagrange `|q|ⁿ (n+1)/(n! n)` em ℚ. -/
def restoExp (q : ℚ) (n : ℕ) : ℚ := |q| ^ n * ((n.succ : ℚ) / ((n.factorial : ℚ) * n))

/-- Intervalo certificado para `e^q`. -/
def expI (q : ℚ) (n : ℕ) : Intervalo := ⟨taylorExp q n - restoExp q n, taylorExp q n + restoExp q n⟩

theorem contem_exp {q : ℚ} (hq : |q| ≤ 1) {n : ℕ} (hn : 0 < n) :
    (expI q n).contem (Real.exp q) := by
  have hq' : |(q : ℝ)| ≤ 1 := by exact_mod_cast hq
  have h := Real.exp_bound hq' hn
  have hT : ((taylorExp q n : ℚ) : ℝ) = ∑ i ∈ range n, (q : ℝ) ^ i / (i.factorial : ℝ) := by
    simp [taylorExp]
  have hR : ((restoExp q n : ℚ) : ℝ) = |(q : ℝ)| ^ n * ((n.succ : ℝ) / ((n.factorial : ℝ) * n)) := by
    simp [restoExp]
  rw [← hT, ← hR] at h
  constructor
  · simp only [expI]
    push_cast
    linarith [(abs_le.mp h).1]
  · simp only [expI]
    push_cast
    linarith [(abs_le.mp h).2]

/-- `π ∈ [3.14, 3.15]`. -/
def piI : Intervalo := ⟨314 / 100, 315 / 100⟩

theorem contem_pi : piI.contem Real.pi := by
  constructor
  · simp only [piI]
    have := Real.pi_gt_d2
    norm_num at this ⊢
    linarith
  · simp only [piI]
    have := Real.pi_lt_d2
    norm_num at this ⊢
    linarith

/-- **Exemplo de certificado**: `e^{−1} < 0,37`, por um intervalo de grau 8 calculado em ℚ. -/
theorem exemplo_exp : Real.exp (-1) < 37 / 100 := by
  have h := contem_exp (q := -1) (by norm_num) (n := 8) (by norm_num)
  have hlt : (expI (-1) 8).hi < 37 / 100 := by
    simp only [expI, taylorExp, restoExp]
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have := lt_de_contem h hlt
  push_cast at this
  exact this

end ATK.BaseIntervalar

#print axioms ATK.BaseIntervalar.Intervalo.contem_ponto
#print axioms ATK.BaseIntervalar.Intervalo.contem_add
#print axioms ATK.BaseIntervalar.Intervalo.contem_neg
#print axioms ATK.BaseIntervalar.Intervalo.contem_sub
#print axioms ATK.BaseIntervalar.Intervalo.min_le_mul
#print axioms ATK.BaseIntervalar.Intervalo.mul_le_max
#print axioms ATK.BaseIntervalar.Intervalo.contem_mul
#print axioms ATK.BaseIntervalar.Intervalo.pos_de_contem
#print axioms ATK.BaseIntervalar.Intervalo.neg_de_contem
#print axioms ATK.BaseIntervalar.Intervalo.lt_de_contem
#print axioms ATK.BaseIntervalar.contem_exp
#print axioms ATK.BaseIntervalar.contem_pi
#print axioms ATK.BaseIntervalar.exemplo_exp
