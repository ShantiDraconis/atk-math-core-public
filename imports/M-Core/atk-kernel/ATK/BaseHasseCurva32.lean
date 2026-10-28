/-
ATK.Base — Cota de Hasse para `y² = x³ − x` sobre corpos finitos (Gauss, Jacobsthal).

Núcleo aritmético da ponte P2 de `ATK.AtaqueBSD` (cota dos coeficientes de `L(E, s)` para a curva
de condutor 32).  Sobre um corpo finito `F` de característica ímpar, com `χ` o caráter
quadrático e `q = |F|`:

* `S k = Σₓ χ(x (x² + k))` (soma de Jacobsthal); `a = −S(−1)` é o traço de Frobenius da curva;
* **`S_escala`**: `S(k t²) = χ(t) S(k)` — `S(k)²` só depende da classe de `k` módulo quadrados;
* **`soma_par`**: `Σ_k χ((k + a)(k + b)) = −1` para `a ≠ b`;
* **`soma_S_sq`**: se `−1` é quadrado, `Σ_k S(k)² = 2q(q − 1)`;
* **`soma_AB`**: `S(1)² + S(g)² = 4q` (`g` não quadrado) — a identidade `p = a² + b²` de Gauss;
* **`traco_zero`**: se `−1` não é quadrado (`q ≡ 3 mod 4`), `Σₓ χ(x³ − x) = 0` (supersingular);
* **`hasse_curva32`**: `(Σₓ χ(x³ − x))² ≤ 4q`, isto é `|a| ≤ 2√q` (**cota de Hasse**);
* **`card_afim`**: o número de soluções afins de `y² = x³ − x` é `q + Σₓ χ(x³ − x)`, logo
  **`hasse_pontos`**: `(q + 1 − #E(F))² ≤ 4q` com `#E(F) = 1 + #afins`.

Falta, para a ponte P2 completa, identificar estes traços com os coeficientes `aₚ` da função L
da Mathlib (redução do modelo minimal em `ℤ_p`) e usar a recursão de Hecke.
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset

namespace ATK.BaseHasseCurva32

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Soma de Jacobsthal `S k = Σₓ χ(x (x² + k))`. -/
def S (k : F) : ℤ := ∑ x : F, quadraticChar F (x * (x ^ 2 + k))

theorem chi_cubo (t : F) : quadraticChar F (t ^ 3) = quadraticChar F t := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [map_pow, pow_succ, quadraticChar_sq_one ht, one_mul]

theorem chi_sq_eq_one {t : F} (ht : t ≠ 0) : quadraticChar F t * quadraticChar F t = 1 := by
  rw [← sq, quadraticChar_sq_one ht]

/-- **`S(k t²) = χ(t) S(k)`.** -/
theorem S_escala {t : F} (ht : t ≠ 0) (k : F) : S (k * t ^ 2) = quadraticChar F t * S k := by
  unfold S
  rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft₀ t ht)]
  refine Finset.sum_congr rfl fun y _ => ?_
  have e : (Equiv.mulLeft₀ t ht) y * (((Equiv.mulLeft₀ t ht) y) ^ 2 + k * t ^ 2) =
      t ^ 3 * (y * (y ^ 2 + k)) := by
    change t * y * ((t * y) ^ 2 + k * t ^ 2) = _
    ring
  rw [e, map_mul, chi_cubo]

theorem S_sq_escala {t : F} (ht : t ≠ 0) (k : F) : S (k * t ^ 2) ^ 2 = S k ^ 2 := by
  rw [S_escala ht, mul_pow, quadraticChar_sq_one ht, one_mul]

theorem S_zero (hF : ringChar F ≠ 2) : S (0 : F) = 0 := by
  unfold S
  have e : ∀ x : F, x * (x ^ 2 + 0) = x ^ 3 := fun x => by ring
  simp_rw [e, chi_cubo]
  exact quadraticChar_sum_zero hF

/-- `Σₖ χ(k (k + d)) = −1` para `d ≠ 0`. -/
theorem soma_desloc (hF : ringChar F ≠ 2) {d : F} (hd : d ≠ 0) :
    ∑ k : F, quadraticChar F (k * (k + d)) = -1 := by
  classical
  set φ : F → F := fun k => if k = 0 then 1 else 1 + d * k⁻¹ with hφ
  have hinj : Function.Injective φ := by
    intro a b hab
    simp only [hφ] at hab
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [ha, hb]
    · rw [if_pos ha, if_neg hb] at hab
      exfalso
      have : d * b⁻¹ = 0 := by linear_combination -hab
      rcases mul_eq_zero.mp this with h | h
      · exact hd h
      · exact hb (inv_eq_zero.mp h)
    · rw [if_neg ha, if_pos hb] at hab
      exfalso
      have : d * a⁻¹ = 0 := by linear_combination hab
      rcases mul_eq_zero.mp this with h | h
      · exact hd h
      · exact ha (inv_eq_zero.mp h)
    · rw [if_neg ha, if_neg hb] at hab
      have h1 : d * a⁻¹ = d * b⁻¹ := by linear_combination hab
      have h2 := mul_left_cancel₀ hd h1
      exact inv_injective h2
  have hbij : Function.Bijective φ := hinj.bijective_of_finite
  have htot : ∑ k : F, quadraticChar F (φ k) = 0 := by
    rw [hbij.sum_comp (fun z => quadraticChar F z)]
    exact quadraticChar_sum_zero hF
  have hpt : ∀ k : F, quadraticChar F (k * (k + d)) =
      quadraticChar F (φ k) - if k = 0 then 1 else 0 := by
    intro k
    by_cases hk : k = 0
    · simp [hk, hφ]
    · simp only [hφ, if_neg hk, sub_zero]
      have e : k * (k + d) = k ^ 2 * (1 + d * k⁻¹) := by
        field_simp
      rw [e, map_mul, quadraticChar_sq_one' hk, one_mul]
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib, htot]
  simp

/-- **`Σₖ χ((k + a)(k + b)) = −1` para `a ≠ b`.** -/
theorem soma_par (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ k : F, quadraticChar F ((k + a) * (k + b)) = -1 := by
  have h := soma_desloc hF (d := a - b) (sub_ne_zero.mpr hab)
  rw [← h, ← Equiv.sum_comp (Equiv.subRight b)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Equiv.subRight_apply]
  congr 1
  ring

/-- `Σₖ χ((k + a)²) = q − 1`. -/
theorem soma_diag (a : F) :
    ∑ k : F, quadraticChar F ((k + a) * (k + a)) = (Fintype.card F : ℤ) - 1 := by
  classical
  have hpt : ∀ k : F, quadraticChar F ((k + a) * (k + a)) = 1 - if k = -a then 1 else 0 := by
    intro k
    by_cases hk : k = -a
    · simp [hk]
    · have hk' : k + a ≠ 0 := fun h => hk (eq_neg_of_add_eq_zero_left h)
      rw [if_neg hk, sub_zero, ← sq, quadraticChar_sq_one' hk']
  simp_rw [hpt]
  rw [Finset.sum_sub_distrib]
  simp

/-- Soma interna: `Σₖ χ((k + x²)(k + y²)) = −1 + q·[x² = y²]`. -/
theorem soma_interna (hF : ringChar F ≠ 2) (x y : F) :
    ∑ k : F, quadraticChar F ((k + x ^ 2) * (k + y ^ 2)) =
      -1 + if x ^ 2 = y ^ 2 then (Fintype.card F : ℤ) else 0 := by
  by_cases h : x ^ 2 = y ^ 2
  · rw [if_pos h, h, soma_diag]
    ring
  · rw [if_neg h, soma_par hF h]
    ring

/-- `Σ_y χ(xy)·[x² = y²] = 2·[x ≠ 0]` quando `χ(−1) = 1`. -/
theorem soma_diagonal (hF : ringChar F ≠ 2) (h1 : quadraticChar F (-1) = 1) (x : F) :
    ∑ y : F, (if x ^ 2 = y ^ 2 then quadraticChar F (x * y) else 0) =
      if x = 0 then 0 else 2 := by
  classical
  by_cases hx : x = 0
  · subst hx
    simp
  · rw [if_neg hx, ← Finset.sum_filter]
    have hfil : (univ.filter fun y : F => x ^ 2 = y ^ 2) = {x, -x} := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      rw [sq_eq_sq_iff_eq_or_eq_neg]
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · right
          rw [h, neg_neg]
      · rintro (h | h)
        · exact Or.inl h.symm
        · right
          rw [h, neg_neg]
    have hne : x ≠ -x := fun h =>
      hx ((Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h.symm)
    rw [hfil, Finset.sum_pair hne, ← sq, quadraticChar_sq_one' hx,
      show x * -x = -1 * x ^ 2 by ring, map_mul, h1, quadraticChar_sq_one' hx]
    norm_num

/-- **`Σₖ S(k)² = 2q(q − 1)`** quando `−1` é quadrado. -/
theorem soma_S_sq (hF : ringChar F ≠ 2) (h1 : quadraticChar F (-1) = 1) :
    ∑ k : F, S k ^ 2 = 2 * (Fintype.card F : ℤ) * ((Fintype.card F : ℤ) - 1) := by
  classical
  have e1 : ∀ k : F, S k ^ 2 = ∑ x : F, ∑ y : F,
      quadraticChar F (x * y) * quadraticChar F ((k + x ^ 2) * (k + y ^ 2)) := by
    intro k
    rw [sq, S, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [← map_mul, ← map_mul]
    congr 1
    ring
  simp_rw [e1]
  rw [Finset.sum_comm]
  have e2 : ∀ x : F, ∑ k : F, ∑ y : F,
      quadraticChar F (x * y) * quadraticChar F ((k + x ^ 2) * (k + y ^ 2)) =
      ∑ y : F, quadraticChar F (x * y) * (-1 + if x ^ 2 = y ^ 2 then (Fintype.card F : ℤ) else 0) := by
    intro x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.mul_sum, soma_interna hF]
  simp_rw [e2]
  have e3 : ∀ x : F, ∑ y : F,
      quadraticChar F (x * y) * (-1 + if x ^ 2 = y ^ 2 then (Fintype.card F : ℤ) else 0) =
      -(quadraticChar F x * ∑ y : F, quadraticChar F y) +
        (Fintype.card F : ℤ) * (if x = 0 then 0 else 2) := by
    intro x
    rw [← soma_diagonal hF h1 x, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul]
    split_ifs <;> ring
  simp_rw [e3, quadraticChar_sum_zero hF, mul_zero, neg_zero, zero_add]
  rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
    Finset.filter_ne' univ (0 : F), Finset.card_erase_of_mem (mem_univ _), card_univ]
  have hc : 1 ≤ Fintype.card F := Fintype.card_pos
  rw [nsmul_eq_mul, Nat.cast_sub hc]
  push_cast
  ring

/-- `S(k)²` vale `S(1)²` nos quadrados e `S(g)²` nos não quadrados. -/
theorem S_sq_classe (hF : ringChar F ≠ 2) {g : F} (hg : ¬IsSquare g) {k : F} (hk : k ≠ 0) :
    2 * S k ^ 2 = (S (1 : F) ^ 2 + S g ^ 2) + quadraticChar F k * (S (1 : F) ^ 2 - S g ^ 2) := by
  have hg0 : g ≠ 0 := fun h => hg (h ▸ ⟨0, by simp⟩)
  rcases quadraticChar_dichotomy hk with hχ | hχ
  · obtain ⟨t, rfl⟩ := (quadraticChar_one_iff_isSquare hk).mp hχ
    have ht : t ≠ 0 := fun h => hk (by rw [h, mul_zero])
    have := S_sq_escala ht (1 : F)
    rw [one_mul] at this
    rw [hχ, show t * t = t ^ 2 from (sq t).symm, this]
    ring
  · have hq : IsSquare (k * g⁻¹) := by
      have hkg : k * g⁻¹ ≠ 0 := mul_ne_zero hk (inv_ne_zero hg0)
      apply (quadraticChar_one_iff_isSquare hkg).mp
      have hgχ : quadraticChar F g = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hg
      have hinv : quadraticChar F g⁻¹ = -1 := by
        have h' := map_mul (quadraticChar F) g g⁻¹
        rw [mul_inv_cancel₀ hg0, map_one, hgχ] at h'
        linarith
      rw [map_mul, hχ, hinv]
      norm_num
    obtain ⟨t, ht⟩ := hq
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [mul_zero, mul_eq_zero] at ht
      rcases ht with h | h
      · exact hk h
      · exact hg0 (inv_eq_zero.mp h)
    have hk' : k = g * t ^ 2 := by
      rw [sq, ← ht]
      field_simp
    have := S_sq_escala ht0 g
    rw [← hk'] at this
    rw [hχ, this]
    ring

/-- **Identidade de Gauss**: `S(1)² + S(g)² = 4q` (quando `−1` é quadrado). -/
theorem soma_AB (hF : ringChar F ≠ 2) (h1 : quadraticChar F (-1) = 1) {g : F} (hg : ¬IsSquare g) :
    S (1 : F) ^ 2 + S g ^ 2 = 4 * (Fintype.card F : ℤ) := by
  classical
  set A := S (1 : F) ^ 2 + S g ^ 2
  set B := S (1 : F) ^ 2 - S g ^ 2
  have hpt : ∀ k : F, 2 * S k ^ 2 = A * (if k = 0 then 0 else 1) + quadraticChar F k * B := by
    intro k
    by_cases hk : k = 0
    · subst hk
      rw [S_zero hF]
      simp
    · rw [if_neg hk, mul_one]
      exact S_sq_classe hF hg hk
  have hsum : 2 * ∑ k : F, S k ^ 2 = A * ((Fintype.card F : ℤ) - 1) := by
    rw [Finset.mul_sum]
    simp_rw [hpt]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, quadraticChar_sum_zero hF,
      zero_mul, add_zero, Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
      Finset.filter_ne' univ (0 : F), Finset.card_erase_of_mem (mem_univ _), card_univ]
    have hc : 1 ≤ Fintype.card F := Fintype.card_pos
    rw [nsmul_eq_mul, Nat.cast_sub hc]
    push_cast
    ring
  rw [soma_S_sq hF h1] at hsum
  have hq : (1 : ℤ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hq1 : (Fintype.card F : ℤ) - 1 ≠ 0 := by linarith
  have : A * ((Fintype.card F : ℤ) - 1) = (4 * (Fintype.card F : ℤ)) * ((Fintype.card F : ℤ) - 1) := by
    linarith
  exact mul_right_cancel₀ hq1 this

/-- O traço da curva: `Σₓ χ(x³ − x) = S(−1)`. -/
theorem traco_eq_S : ∑ x : F, quadraticChar F (x ^ 3 - x) = S (-1 : F) := by
  unfold S
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  ring

/-- **Caso supersingular**: se `−1` não é quadrado, `Σₓ χ(x³ − x) = 0`. -/
theorem traco_zero (hF : ringChar F ≠ 2) (h1 : quadraticChar F (-1) = -1) :
    ∑ x : F, quadraticChar F (x ^ 3 - x) = 0 := by
  have h2 : ∀ x : F, quadraticChar F ((-x) ^ 3 - -x) = -quadraticChar F (x ^ 3 - x) := by
    intro x
    rw [show (-x) ^ 3 - -x = -1 * (x ^ 3 - x) by ring, map_mul, h1]
    ring
  have h := (Equiv.sum_comp (Equiv.neg F) (fun x : F => quadraticChar F (x ^ 3 - x))).symm
  simp only [Equiv.neg_apply, h2, Finset.sum_neg_distrib] at h
  linarith

/-- **Cota de Hasse para `y² = x³ − x`**: `(Σₓ χ(x³ − x))² ≤ 4q`. -/
theorem hasse_curva32 (hF : ringChar F ≠ 2) :
    (∑ x : F, quadraticChar F (x ^ 3 - x)) ^ 2 ≤ 4 * (Fintype.card F : ℤ) := by
  rcases quadraticChar_dichotomy (neg_ne_zero.mpr (one_ne_zero : (1 : F) ≠ 0)) with h1 | h1
  · -- `−1 = i²`: `S(−1)² = S(1)²`
    have hsq : IsSquare (-1 : F) := (quadraticChar_one_iff_isSquare (by simp)).mp h1
    obtain ⟨i, hi⟩ := hsq
    have hi0 : i ≠ 0 := by
      rintro rfl
      simp at hi
    obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare hF
    have hS : S (-1 : F) ^ 2 = S (1 : F) ^ 2 := by
      have := S_sq_escala hi0 (1 : F)
      rwa [one_mul, sq i, ← hi] at this
    rw [traco_eq_S, hS]
    have := soma_AB hF h1 hg
    nlinarith [sq_nonneg (S g)]
  · rw [traco_zero hF h1]
    positivity

/-- Número de soluções afins de `y² = x³ − x`: `q + Σₓ χ(x³ − x)`. -/
theorem card_afim (hF : ringChar F ≠ 2) :
    ((univ.filter fun p : F × F => p.2 ^ 2 = p.1 ^ 3 - p.1).card : ℤ) =
      Fintype.card F + ∑ x : F, quadraticChar F (x ^ 3 - x) := by
  classical
  have e : (univ.filter fun p : F × F => p.2 ^ 2 = p.1 ^ 3 - p.1).card =
      ∑ x : F, (univ.filter fun y : F => y ^ 2 = x ^ 3 - x).card := by
    rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.card_filter]
  rw [e]
  push_cast
  have h2 : ∀ x : F, ((univ.filter fun y : F => y ^ 2 = x ^ 3 - x).card : ℤ) =
      quadraticChar F (x ^ 3 - x) + 1 := by
    intro x
    rw [← quadraticChar_card_sqrts hF]
    congr 2
    ext y
    simp
  simp_rw [h2]
  rw [Finset.sum_add_distrib]
  simp
  ring

/-- **Hasse em termos de pontos**: com `#E(F) = 1 + #afins`, `(q + 1 − #E(F))² ≤ 4q`. -/
theorem hasse_pontos (hF : ringChar F ≠ 2) :
    ((Fintype.card F : ℤ) + 1 -
      (1 + (univ.filter fun p : F × F => p.2 ^ 2 = p.1 ^ 3 - p.1).card)) ^ 2 ≤
      4 * (Fintype.card F : ℤ) := by
  rw [card_afim hF]
  have := hasse_curva32 (F := F) hF
  nlinarith [this]

end ATK.BaseHasseCurva32

#print axioms ATK.BaseHasseCurva32.chi_cubo
#print axioms ATK.BaseHasseCurva32.chi_sq_eq_one
#print axioms ATK.BaseHasseCurva32.S_escala
#print axioms ATK.BaseHasseCurva32.S_sq_escala
#print axioms ATK.BaseHasseCurva32.S_zero
#print axioms ATK.BaseHasseCurva32.soma_desloc
#print axioms ATK.BaseHasseCurva32.soma_par
#print axioms ATK.BaseHasseCurva32.soma_diag
#print axioms ATK.BaseHasseCurva32.soma_interna
#print axioms ATK.BaseHasseCurva32.soma_diagonal
#print axioms ATK.BaseHasseCurva32.soma_S_sq
#print axioms ATK.BaseHasseCurva32.S_sq_classe
#print axioms ATK.BaseHasseCurva32.soma_AB
#print axioms ATK.BaseHasseCurva32.traco_eq_S
#print axioms ATK.BaseHasseCurva32.traco_zero
#print axioms ATK.BaseHasseCurva32.hasse_curva32
#print axioms ATK.BaseHasseCurva32.card_afim
#print axioms ATK.BaseHasseCurva32.hasse_pontos
