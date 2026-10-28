import ATK.BaezDuarteBridge

/-!
# ATK — ZetaSimetria: a órbita de um zero não trivial sob reflexão e conjugação

Usando só a equação funcional (`riemannZeta_one_sub`) e a simetria de conjugação
(`riemannZeta_conj`) da Mathlib:

* `orbita_zeros`: se `ζ(s) = 0` com `0 < Re s < 1`, então `ζ(1 − s) = ζ(s̄) = ζ(1 − s̄) = 0`;
* `orbita_distinta`: se além disso `Re s ≠ 1/2` e `Im s ≠ 0`, os quatro pontos
  `s, 1 − s, s̄, 1 − s̄` são dois a dois distintos — um zero fora da reta nunca aparece sozinho;
* `zero_fora_da_reta_tem_par_a_direita`: todo zero fora da reta na faixa tem um parceiro com
  `1/2 < Re < 1`;
* `rh_iff_faixa`: **RH ⟺ nenhum zero em `1/2 < Re s < 1`** (a volta usa
  `ATK.BaezDuarteBridge.riemannHypothesis_of_strip`, já certificada).

Fatos clássicos; o valor aqui é tê-los no kernel. Nada disso restringe onde os zeros estão:
`OPEN_MATH` não muda.
-/

open Complex ComplexConjugate

namespace ATK.ZetaSimetria

/-- `ζ(s) = 0 ⇒ ζ(s̄) = 0`. -/
theorem zero_conj {s : ℂ} (hz : riemannZeta s = 0) : riemannZeta (conj s) = 0 := by
  rw [riemannZeta_conj, hz, map_zero]

/-- `ζ(s) = 0` na faixa crítica `⇒ ζ(1 − s) = 0`. -/
theorem zero_one_sub {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  have hs : ∀ n : ℕ, s ≠ -n := by
    intro n hn
    have hre : s.re = -(n : ℝ) := by rw [hn]; simp
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs' : s ≠ 1 := by
    intro h
    have hre : s.re = 1 := by rw [h]; simp
    linarith
  rw [riemannZeta_one_sub hs hs', hz, mul_zero]

/-- **A órbita**: os quatro pontos `s, 1 − s, s̄, 1 − s̄` são zeros. -/
theorem orbita_zeros {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 ∧ riemannZeta (conj s) = 0 ∧ riemannZeta (1 - conj s) = 0 := by
  refine ⟨zero_one_sub h0 h1 hz, zero_conj hz, ?_⟩
  exact zero_one_sub (by simpa using h0) (by simpa using h1) (zero_conj hz)

/-- **Fora da reta, a órbita tem 4 elementos distintos.** -/
theorem orbita_distinta {s : ℂ} (hre : s.re ≠ 1 / 2) (him : s.im ≠ 0) :
    s ≠ 1 - s ∧ s ≠ conj s ∧ s ≠ 1 - conj s ∧ 1 - s ≠ conj s ∧ 1 - s ≠ 1 - conj s ∧
      conj s ≠ 1 - conj s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro e
  · have h := congrArg Complex.re e
    simp only [Complex.sub_re, Complex.one_re] at h
    exact hre (by linarith)
  · have h := congrArg Complex.im e
    simp only [Complex.conj_im] at h
    exact him (by linarith)
  · have h := congrArg Complex.re e
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h
    exact hre (by linarith)
  · have h := congrArg Complex.re e
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h
    exact hre (by linarith)
  · have h := congrArg Complex.im e
    simp only [Complex.sub_im, Complex.one_im, Complex.conj_im] at h
    exact him (by linarith)
  · have h := congrArg Complex.re e
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at h
    exact hre (by linarith)

/-- Todo zero fora da reta na faixa tem um parceiro com `1/2 < Re < 1`. -/
theorem zero_fora_da_reta_tem_par_a_direita {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    (hz : riemannZeta s = 0) (hre : s.re ≠ 1 / 2) :
    ∃ w : ℂ, riemannZeta w = 0 ∧ 1 / 2 < w.re ∧ w.re < 1 := by
  rcases lt_or_gt_of_ne hre with hlt | hgt
  · refine ⟨1 - s, zero_one_sub h0 h1 hz, ?_, ?_⟩ <;> simp <;> linarith
  · exact ⟨s, hz, hgt, h1⟩

/-- **RH ⟺ nenhum zero em `1/2 < Re s < 1`.** -/
theorem rh_iff_faixa :
    RiemannHypothesis ↔ ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 → riemannZeta s ≠ 0 := by
  constructor
  · intro hRH s hs0 hs1 hz
    have htriv : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      have hre : s.re = -2 * ((n : ℝ) + 1) := by rw [hn]; simp
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hs1' : s ≠ 1 := by
      intro h
      have hre : s.re = 1 := by rw [h]; simp
      linarith
    have := hRH s hz htriv hs1'
    linarith
  · exact ATK.BaezDuarteBridge.riemannHypothesis_of_strip

end ATK.ZetaSimetria

#print axioms ATK.ZetaSimetria.zero_conj
#print axioms ATK.ZetaSimetria.zero_one_sub
#print axioms ATK.ZetaSimetria.orbita_zeros
#print axioms ATK.ZetaSimetria.orbita_distinta
#print axioms ATK.ZetaSimetria.zero_fora_da_reta_tem_par_a_direita
#print axioms ATK.ZetaSimetria.rh_iff_faixa
