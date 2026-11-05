import Mathlib

/-!
# Aritmética de intervalos verificada sobre `ℚ` (fase 2)

Intervalos reais `[lo, hi]` com extremos racionais (`IR`) e retângulos complexos (`IC`). Cada operação vem
com um teorema de correção: se os argumentos estão nos intervalos, o resultado está no intervalo
calculado. As contas são em `ℚ` e podem ser verificadas pelo **kernel** (`decide +kernel`), sem
`native_decide`. O arredondamento para fora (`IR.round`) mantém os racionais pequenos.
-/

namespace ATK.Cert

/-- Intervalo real com extremos racionais. -/
structure IR where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

/-- Retângulo complexo. -/
structure IC where
  re : IR
  im : IR
  deriving DecidableEq, Repr

namespace IR

def mem (x : ℝ) (I : IR) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ I.hi

def pt (q : ℚ) : IR := ⟨q, q⟩

def add (I J : IR) : IR := ⟨I.lo + J.lo, I.hi + J.hi⟩

def neg (I : IR) : IR := ⟨-I.hi, -I.lo⟩

def sub (I J : IR) : IR := add I (neg J)

def mul (I J : IR) : IR :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

/-- Alarga por `e ≥ 0` dos dois lados. -/
def widen (I : IR) (e : ℚ) : IR := ⟨I.lo - e, I.hi + e⟩

/-- Inverso de um intervalo positivo. -/
def inv (I : IR) : IR := ⟨1 / I.hi, 1 / I.lo⟩

/-- Arredondamento para fora na precisão `2^{-p}`. -/
def round (p : ℕ) (I : IR) : IR :=
  ⟨(⌊I.lo * 2 ^ p⌋ : ℚ) / 2 ^ p, (⌈I.hi * 2 ^ p⌉ : ℚ) / 2 ^ p⟩

/-- Cota de `|x|` em `I`. -/
def absMax (I : IR) : ℚ := max |I.lo| |I.hi|

theorem mem_pt (q : ℚ) : mem (q : ℝ) (pt q) := ⟨le_rfl, le_rfl⟩

theorem mem_add {x y : ℝ} {I J : IR} (hx : mem x I) (hy : mem y J) : mem (x + y) (add I J) := by
  unfold mem add at *; push_cast; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_neg {x : ℝ} {I : IR} (hx : mem x I) : mem (-x) (neg I) := by
  unfold mem neg at *; push_cast; constructor <;> linarith [hx.1, hx.2]

theorem mem_sub {x y : ℝ} {I J : IR} (hx : mem x I) (hy : mem y J) : mem (x - y) (sub I J) := by
  rw [sub_eq_add_neg]; exact mem_add hx (mem_neg hy)

theorem min_le_mul {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) : min (a * y) (b * y) ≤ x * y := by
  rcases le_total 0 y with hy | hy
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

theorem mul_le_max {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) : x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact (by nlinarith : x * y ≤ b * y).trans (le_max_right _ _)
  · exact (by nlinarith : x * y ≤ a * y).trans (le_max_left _ _)

theorem mem_mul {x y : ℝ} {I J : IR} (hx : mem x I) (hy : mem y J) : mem (x * y) (mul I J) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  unfold mem mul
  push_cast
  constructor
  · have h1 := min_le_mul (y := y) hx1 hx2
    have h2 : min ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi) ≤ (I.lo : ℝ) * y := by
      have := min_le_mul (y := (I.lo : ℝ)) hy1 hy2
      simpa [mul_comm] using this
    have h3 : min ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi) ≤ (I.hi : ℝ) * y := by
      have := min_le_mul (y := (I.hi : ℝ)) hy1 hy2
      simpa [mul_comm] using this
    calc min (min ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi)) (min ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi))
        ≤ min ((I.lo : ℝ) * y) ((I.hi : ℝ) * y) := min_le_min h2 h3
      _ ≤ x * y := h1
  · have h1 := mul_le_max (y := y) hx1 hx2
    have h2 : (I.lo : ℝ) * y ≤ max ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi) := by
      have := mul_le_max (y := (I.lo : ℝ)) hy1 hy2
      simpa [mul_comm] using this
    have h3 : (I.hi : ℝ) * y ≤ max ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi) := by
      have := mul_le_max (y := (I.hi : ℝ)) hy1 hy2
      simpa [mul_comm] using this
    calc x * y ≤ max ((I.lo : ℝ) * y) ((I.hi : ℝ) * y) := h1
      _ ≤ _ := max_le_max h2 h3

theorem mem_widen {x : ℝ} {I : IR} {e : ℚ} (hx : mem x I) (he : 0 ≤ e) : mem x (widen I e) := by
  unfold mem widen at *; push_cast
  have : (0 : ℝ) ≤ e := by exact_mod_cast he
  constructor <;> linarith [hx.1, hx.2]

/-- Um ponto a distância `≤ e` de um ponto de `I` está em `I` alargado por `e`. -/
theorem mem_widen_of_dist {x y : ℝ} {I : IR} {e : ℚ} (hy : mem y I) (h : |x - y| ≤ e) :
    mem x (widen I e) := by
  unfold mem widen at *; push_cast
  have := abs_le.mp h
  constructor <;> linarith [hy.1, hy.2, this.1, this.2]

theorem mem_inv {x : ℝ} {I : IR} (hx : mem x I) (hpos : 0 < I.lo) : mem x⁻¹ (inv I) := by
  obtain ⟨h1, h2⟩ := hx
  have hl : (0 : ℝ) < I.lo := by exact_mod_cast hpos
  have hx0 : 0 < x := hl.trans_le h1
  unfold mem inv
  push_cast
  constructor
  · rw [one_div]; exact inv_anti₀ hx0 h2
  · rw [one_div]; exact inv_anti₀ hl h1

theorem mem_round {x : ℝ} {I : IR} (p : ℕ) (hx : mem x I) : mem x (round p I) := by
  obtain ⟨h1, h2⟩ := hx
  have hp : (0 : ℚ) < 2 ^ p := by positivity
  unfold mem round
  constructor
  · have : ((⌊I.lo * 2 ^ p⌋ : ℚ) / 2 ^ p) ≤ I.lo := by
      rw [div_le_iff₀ hp]; exact Int.floor_le _
    exact le_trans (by exact_mod_cast this) h1
  · have : I.hi ≤ ((⌈I.hi * 2 ^ p⌉ : ℚ) / 2 ^ p) := by
      rw [le_div_iff₀ hp]; exact Int.le_ceil _
    exact le_trans h2 (by exact_mod_cast this)

theorem abs_le_absMax {x : ℝ} {I : IR} (hx : mem x I) : |x| ≤ (absMax I : ℝ) := by
  obtain ⟨h1, h2⟩ := hx
  unfold absMax
  push_cast
  rw [abs_le]
  constructor
  · have := neg_abs_le (I.lo : ℝ)
    have := le_max_left |(I.lo : ℝ)| |(I.hi : ℝ)|
    linarith
  · have := le_abs_self (I.hi : ℝ)
    have := le_max_right |(I.lo : ℝ)| |(I.hi : ℝ)|
    linarith

end IR

namespace IC

def mem (z : ℂ) (I : IC) : Prop := IR.mem z.re I.re ∧ IR.mem z.im I.im

def pt (a b : ℚ) : IC := ⟨IR.pt a, IR.pt b⟩

def add (I J : IC) : IC := ⟨IR.add I.re J.re, IR.add I.im J.im⟩

def sub (I J : IC) : IC := ⟨IR.sub I.re J.re, IR.sub I.im J.im⟩

def mul (I J : IC) : IC :=
  ⟨IR.sub (IR.mul I.re J.re) (IR.mul I.im J.im), IR.add (IR.mul I.re J.im) (IR.mul I.im J.re)⟩

/-- Multiplicação por um real num intervalo. -/
def smul (K : IR) (I : IC) : IC := ⟨IR.mul K I.re, IR.mul K I.im⟩

def widen (I : IC) (e : ℚ) : IC := ⟨IR.widen I.re e, IR.widen I.im e⟩

def round (p : ℕ) (I : IC) : IC := ⟨IR.round p I.re, IR.round p I.im⟩

/-- Cota de `‖z‖` em `I`: `|re| + |im|`. -/
def normMax (I : IC) : ℚ := IR.absMax I.re + IR.absMax I.im

theorem mem_pt (a b : ℚ) : mem ((a : ℂ) + (b : ℂ) * Complex.I) (pt a b) := by
  unfold mem pt IR.mem IR.pt; simp

theorem mem_add {z w : ℂ} {I J : IC} (hz : mem z I) (hw : mem w J) : mem (z + w) (add I J) :=
  ⟨by simpa [add] using IR.mem_add hz.1 hw.1, by simpa [add] using IR.mem_add hz.2 hw.2⟩

theorem mem_sub {z w : ℂ} {I J : IC} (hz : mem z I) (hw : mem w J) : mem (z - w) (sub I J) :=
  ⟨by simpa [sub] using IR.mem_sub hz.1 hw.1, by simpa [sub] using IR.mem_sub hz.2 hw.2⟩

theorem mem_mul {z w : ℂ} {I J : IC} (hz : mem z I) (hw : mem w J) : mem (z * w) (mul I J) := by
  constructor
  · rw [Complex.mul_re]; exact IR.mem_sub (IR.mem_mul hz.1 hw.1) (IR.mem_mul hz.2 hw.2)
  · rw [Complex.mul_im]; exact IR.mem_add (IR.mem_mul hz.1 hw.2) (IR.mem_mul hz.2 hw.1)

theorem mem_smul {x : ℝ} {z : ℂ} {K : IR} {I : IC} (hx : IR.mem x K) (hz : mem z I) :
    mem ((x : ℂ) * z) (smul K I) := by
  constructor
  · simpa [smul] using IR.mem_mul hx hz.1
  · simpa [smul] using IR.mem_mul hx hz.2

theorem mem_round {z : ℂ} {I : IC} (p : ℕ) (hz : mem z I) : mem z (round p I) :=
  ⟨IR.mem_round p hz.1, IR.mem_round p hz.2⟩

theorem mem_widen {z : ℂ} {I : IC} {e : ℚ} (hz : mem z I) (he : 0 ≤ e) : mem z (widen I e) :=
  ⟨IR.mem_widen hz.1 he, IR.mem_widen hz.2 he⟩

/-- Um ponto a distância `≤ e` (em norma) de um ponto de `I` está em `I` alargado por `e`. -/
theorem mem_widen_of_norm {z w : ℂ} {I : IC} {e : ℚ} (hw : mem w I) (h : ‖z - w‖ ≤ e) :
    mem z (widen I e) := by
  constructor
  · refine IR.mem_widen_of_dist hw.1 ?_
    have := Complex.abs_re_le_norm (z - w)
    rw [Complex.sub_re] at this; linarith
  · refine IR.mem_widen_of_dist hw.2 ?_
    have := Complex.abs_im_le_norm (z - w)
    rw [Complex.sub_im] at this; linarith

theorem norm_le_normMax {z : ℂ} {I : IC} (hz : mem z I) : ‖z‖ ≤ (normMax I : ℝ) := by
  unfold normMax
  push_cast
  exact (Complex.norm_le_abs_re_add_abs_im z).trans
    (add_le_add (IR.abs_le_absMax hz.1) (IR.abs_le_absMax hz.2))

end IC

end ATK.Cert

#print axioms ATK.Cert.IR.mem_mul
#print axioms ATK.Cert.IR.mem_round
#print axioms ATK.Cert.IC.mem_mul
#print axioms ATK.Cert.IC.mem_widen_of_norm
#print axioms ATK.Cert.IC.norm_le_normMax
#print axioms ATK.Cert.IR.mem_pt
#print axioms ATK.Cert.IR.mem_add
#print axioms ATK.Cert.IR.mem_neg
#print axioms ATK.Cert.IR.mem_sub
#print axioms ATK.Cert.IR.min_le_mul
#print axioms ATK.Cert.IR.mul_le_max
#print axioms ATK.Cert.IR.mem_widen
#print axioms ATK.Cert.IR.mem_widen_of_dist
#print axioms ATK.Cert.IR.mem_inv
#print axioms ATK.Cert.IR.abs_le_absMax
#print axioms ATK.Cert.IC.mem_pt
#print axioms ATK.Cert.IC.mem_add
#print axioms ATK.Cert.IC.mem_sub
#print axioms ATK.Cert.IC.mem_smul
#print axioms ATK.Cert.IC.mem_round
#print axioms ATK.Cert.IC.mem_widen
