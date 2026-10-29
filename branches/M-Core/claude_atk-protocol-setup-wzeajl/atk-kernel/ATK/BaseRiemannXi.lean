/-
ATK.Base — A função ξ de Riemann e a função Ξ na reta crítica.

Base que falta na Mathlib (v4.34.1 tem `completedRiemannZeta`, `completedRiemannZeta₀`, a equação
funcional e `riemannZeta_conj`, mas não tem `ξ`, nem `Ξ`, nem a conjugação de `Λ₀`).  Escrito no
estilo da Mathlib para poder ser proposto a ela.

* `riemannXi s = s(s−1)/2 · Λ₀(s) + 1/2`, **inteira** (`differentiable_riemannXi`), e igual a
  `s(s−1)/2 · Λ(s)` fora de `{0, 1}` (`riemannXi_eq`);
* simetrias: `ξ(1 − s) = ξ(s)` e **`ξ(s̄) = conj ξ(s)`** (via `completedRiemannZeta₀_conj`, novo);
* `ξ(0) = ξ(1) = 1/2`;
* zeros: na faixa, `ξ(s) = 0 ⟺ ζ(s) = 0`; `ξ ≠ 0` em `Re s ≥ 1` e em `Re s ≤ 0`; todo zero de ξ
  está em `0 < Re s < 1`;
* **`Ξ(t) = ξ(1/2 + it)` é real**, par e contínua; `ζ(1/2 + it) = 0 ⟺ Ξ(t) = 0`;
* **critério de troca de sinal**: `Ξ(a) Ξ(b) < 0` ⇒ há zero de ζ na reta crítica com `a < t < b`
  (é assim que se certificam zeros na reta);
* **`riemannHypothesis_iff_xi`**: RH (da Mathlib) ⟺ todo zero de ξ tem parte real 1/2, e
  **`riemannHypothesis_iff_Xi`**: RH ⟺ todos os zeros de `z ↦ ξ(1/2 + iz)` são reais.

Nada aqui prova RH: é a base para Hardy (infinitos zeros na reta) e para certificar zeros.
-/
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Order.IntermediateValue

open Complex ComplexConjugate Set Filter Topology

namespace ATK.BaseRiemannXi

/-! ### Conjugação de Γℝ e de Λ₀ -/

theorem Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul]
  have hpi : (Real.pi : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_ne_zero.symm
  have c2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
  have e1 : -conj s / 2 = conj (-s / 2) := by rw [map_div₀, map_neg, c2]
  have e2 : conj s / 2 = conj (s / 2) := by rw [map_div₀, c2]
  rw [e1, e2, cpow_conj _ _ hpi, conj_ofReal, Gamma_conj]

/-- **Λ₀ comuta com a conjugação** (novo; a Mathlib só tem a versão para ζ). -/
theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  set B : Set ℂ := ({0, 1} : Set ℂ) ∪ Set.range (fun n : ℕ => -(2 * (n : ℂ))) with hBdef
  have hB : B.Countable :=
    (Set.toFinite ({0, 1} : Set ℂ)).countable.union (Set.countable_range _)
  have hD : Dense Bᶜ := hB.dense_compl ℝ
  have hc1 : Continuous (fun s => completedRiemannZeta₀ (conj s)) :=
    differentiable_completedZeta₀.continuous.comp continuous_conj
  have hc2 : Continuous (fun s => conj (completedRiemannZeta₀ s)) :=
    continuous_conj.comp differentiable_completedZeta₀.continuous
  have key : ∀ z : ℂ, z ≠ 0 → z ≠ 1 → Gammaℝ z ≠ 0 →
      completedRiemannZeta₀ z = riemannZeta z * Gammaℝ z + 1 / z + 1 / (1 - z) := by
    intro z hz0 hz1 hzG
    rw [riemannZeta_def_of_ne_zero hz0, div_mul_cancel₀ _ hzG, completedRiemannZeta_eq]
    ring
  have heq : EqOn (fun s => completedRiemannZeta₀ (conj s))
      (fun s => conj (completedRiemannZeta₀ s)) Bᶜ := by
    intro z hz
    simp only [hBdef, Set.mem_compl_iff, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_range, not_or, not_exists] at hz
    obtain ⟨⟨hz0, hz1⟩, hzn⟩ := hz
    have hG : Gammaℝ z ≠ 0 := by
      rw [Ne, Gammaℝ_eq_zero_iff]
      rintro ⟨n, hn⟩
      exact hzn n hn.symm
    have hcz0 : conj z ≠ 0 := by rwa [Ne, map_eq_zero]
    have hcz1 : conj z ≠ 1 := by
      intro h
      apply hz1
      have := congrArg conj h
      simpa using this
    have hcG : Gammaℝ (conj z) ≠ 0 := by
      rw [Gammaℝ_conj]
      exact (map_ne_zero _).mpr hG
    simp only
    rw [key _ hcz0 hcz1 hcG, key _ hz0 hz1 hG, riemannZeta_conj, Gammaℝ_conj]
    simp [map_add, map_mul, map_div₀, map_one, map_sub]
  exact congrFun (hc1.ext_on hD hc2 heq) s

/-! ### A função ξ -/

/-- `ξ(s) = s(s−1)/2 · Λ₀(s) + 1/2` (`= s(s−1)/2 · Λ(s)` fora de 0 e 1). -/
noncomputable def riemannXi (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2

/-- **ξ é inteira.** -/
theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  unfold riemannXi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).div_const 2).mul
    differentiable_completedZeta₀).add_const _

theorem continuous_riemannXi : Continuous riemannXi := differentiable_riemannXi.continuous

theorem riemannXi_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  rw [completedRiemannZeta_eq]
  unfold riemannXi
  have h1 : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

/-- `ξ(s) = s(s−1)/2 · Γℝ(s) · ζ(s)` quando `Γℝ(s) ≠ 0`. -/
theorem riemannXi_eq_zeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hG : Gammaℝ s ≠ 0) :
    riemannXi s = s * (s - 1) / 2 * Gammaℝ s * riemannZeta s := by
  rw [riemannXi_eq hs0 hs1, riemannZeta_def_of_ne_zero hs0]
  field_simp

/-- Equação funcional `ξ(1 − s) = ξ(s)`. -/
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  unfold riemannXi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- Simetria de Schwarz `ξ(s̄) = conj ξ(s)`. -/
theorem riemannXi_conj (s : ℂ) : riemannXi (conj s) = conj (riemannXi s) := by
  unfold riemannXi
  rw [completedRiemannZeta₀_conj]
  have c2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
  simp only [map_add, map_mul, map_div₀, map_sub, map_one, c2]

theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by simp [riemannXi]

theorem riemannXi_one : riemannXi 1 = 1 / 2 := by simp [riemannXi]

/-! ### Zeros -/

/-- Na metade direita (fora de 1): `ξ(s) = 0 ⟺ ζ(s) = 0`. -/
theorem riemannXi_eq_zero_iff {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h, zero_re] at hre; exact lt_irrefl 0 hre
  have hG := Gammaℝ_ne_zero_of_re_pos hre
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [riemannXi_eq_zeta hs0 hs1 hG]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · exfalso
      rcases mul_eq_zero.mp h' with h'' | h''
      · rcases div_eq_zero_iff.mp h'' with h3 | h3
        · rcases mul_eq_zero.mp h3 with h4 | h4
          · exact hs0 h4
          · exact hs1' h4
        · exact two_ne_zero h3
      · exact hG h''
    · exact h'
  · intro h; rw [h, mul_zero]

theorem riemannXi_ne_zero_of_one_le_re {s : ℂ} (h : 1 ≤ s.re) : riemannXi s ≠ 0 := by
  by_cases hs1 : s = 1
  · rw [hs1, riemannXi_one]; norm_num
  · rw [Ne, riemannXi_eq_zero_iff (by linarith) hs1]
    exact riemannZeta_ne_zero_of_one_le_re h

theorem riemannXi_ne_zero_of_re_le_zero {s : ℂ} (h : s.re ≤ 0) : riemannXi s ≠ 0 := by
  rw [← riemannXi_one_sub]
  apply riemannXi_ne_zero_of_one_le_re
  simp only [sub_re, one_re]
  linarith

/-- **Todo zero de ξ está na faixa crítica aberta.** -/
theorem riemannXi_zero_mem_strip {s : ℂ} (h : riemannXi s = 0) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra h0
    exact riemannXi_ne_zero_of_re_le_zero (not_lt.mp h0) h
  · by_contra h1
    exact riemannXi_ne_zero_of_one_le_re (not_lt.mp h1) h

/-- Zeros não triviais de ζ têm parte real positiva. -/
theorem re_pos_of_zeta_zero {s : ℂ} (hz : riemannZeta s = 0) (hnt : ¬∃ n : ℕ, s = -2 * (n + 1)) :
    0 < s.re := by
  by_contra h0
  have hle : s.re ≤ 0 := not_lt.mp h0
  have hs0 : s ≠ 0 := by
    intro h; rw [h, riemannZeta_zero] at hz; norm_num at hz
  have hs1 : s ≠ 1 := by
    intro h; rw [h, one_re] at hle; norm_num at hle
  by_cases hG : Gammaℝ s = 0
  · obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hG
    rcases n with _ | m
    · apply hs0; rw [hn]; simp
    · apply hnt
      exact ⟨m, by rw [hn]; push_cast; ring⟩
  · apply riemannXi_ne_zero_of_re_le_zero hle
    rw [riemannXi_eq_zeta hs0 hs1 hG, hz, mul_zero]

/-! ### Ξ na reta crítica -/

/-- `Ξ(t) = ξ(1/2 + it)` (parte real; a parte imaginária é 0). -/
noncomputable def Xi (t : ℝ) : ℝ := (riemannXi (1 / 2 + t * I)).re

theorem riemannXi_critical_im (t : ℝ) : (riemannXi (1 / 2 + t * I)).im = 0 := by
  have h1 : riemannXi (1 / 2 + t * I) = riemannXi (conj (1 / 2 + t * I)) := by
    rw [← riemannXi_one_sub]
    congr 1
    apply Complex.ext <;> simp <;> norm_num
  rw [riemannXi_conj] at h1
  exact Complex.conj_eq_iff_im.mp h1.symm

/-- **Ξ é real**: `ξ(1/2 + it) = Ξ(t)`. -/
theorem riemannXi_critical (t : ℝ) : riemannXi (1 / 2 + t * I) = (Xi t : ℂ) := by
  apply Complex.ext
  · rw [ofReal_re]; rfl
  · rw [ofReal_im]; exact riemannXi_critical_im t

/-- Ξ é par. -/
theorem Xi_neg (t : ℝ) : Xi (-t) = Xi t := by
  unfold Xi
  have : (1 / 2 + ((-t : ℝ) : ℂ) * I) = 1 - (1 / 2 + (t : ℂ) * I) := by push_cast; ring
  rw [this, riemannXi_one_sub]

theorem continuous_Xi : Continuous Xi := by
  unfold Xi
  exact continuous_re.comp (continuous_riemannXi.comp
    (continuous_const.add (continuous_ofReal.mul continuous_const)))

/-- `ζ(1/2 + it) = 0 ⟺ Ξ(t) = 0`. -/
theorem zeta_critical_zero_iff (t : ℝ) : riemannZeta (1 / 2 + t * I) = 0 ↔ Xi t = 0 := by
  have hre : 0 < (1 / 2 + (t : ℂ) * I).re := by simp
  have hs1 : (1 / 2 + (t : ℂ) * I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  rw [← riemannXi_eq_zero_iff hre hs1, riemannXi_critical, ofReal_eq_zero]

/-- **Critério de troca de sinal**: `Ξ(a)·Ξ(b) < 0` ⇒ zero de ζ na reta crítica entre a e b. -/
theorem zero_of_sign_change {a b : ℝ} (hab : a ≤ b) (h : Xi a * Xi b < 0) :
    ∃ t ∈ Ioo a b, riemannZeta (1 / 2 + t * I) = 0 := by
  have hc : ContinuousOn Xi (Icc a b) := continuous_Xi.continuousOn
  rcases lt_or_gt_of_ne (show Xi a ≠ 0 by intro h0; rw [h0, zero_mul] at h; exact lt_irrefl 0 h)
    with ha | ha
  · have hb : 0 < Xi b := by
      by_contra hb
      have hb' := not_lt.mp hb
      nlinarith
    obtain ⟨t, ht, ht0⟩ := intermediate_value_Ioo hab hc ⟨ha, hb⟩
    exact ⟨t, ht, (zeta_critical_zero_iff t).mpr ht0⟩
  · have hb : Xi b < 0 := by
      by_contra hb
      have hb' := not_lt.mp hb
      nlinarith
    obtain ⟨t, ht, ht0⟩ := intermediate_value_Ioo' hab hc ⟨hb, ha⟩
    exact ⟨t, ht, (zeta_critical_zero_iff t).mpr ht0⟩

/-! ### RH em termos de ξ e Ξ -/

/-- **RH ⟺ todo zero de ξ tem parte real 1/2.** -/
theorem riemannHypothesis_iff_xi :
    RiemannHypothesis ↔ ∀ s : ℂ, riemannXi s = 0 → s.re = 1 / 2 := by
  constructor
  · intro hRH s hs
    obtain ⟨h0, h1⟩ := riemannXi_zero_mem_strip hs
    have hs1 : s ≠ 1 := by intro h; rw [h, one_re] at h1; exact lt_irrefl 1 h1
    have hz : riemannZeta s = 0 := (riemannXi_eq_zero_iff h0 hs1).mp hs
    refine hRH s hz ?_ hs1
    rintro ⟨n, hn⟩
    rw [hn] at h0
    have : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [this] at h0
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  · intro h s hz hnt hs1
    exact h s ((riemannXi_eq_zero_iff (re_pos_of_zeta_zero hz hnt) hs1).mpr hz)

/-- **RH ⟺ todos os zeros de `z ↦ ξ(1/2 + iz)` são reais.** -/
theorem riemannHypothesis_iff_Xi :
    RiemannHypothesis ↔ ∀ z : ℂ, riemannXi (1 / 2 + z * I) = 0 → z.im = 0 := by
  rw [riemannHypothesis_iff_xi]
  constructor
  · intro h z hz
    have := h _ hz
    simp at this
    linarith
  · intro h s hs
    have e : s = 1 / 2 + (-(s - 1 / 2) * I) * I := by
      rw [mul_assoc, I_mul_I]; ring
    rw [e] at hs
    have := h _ hs
    simp at this
    linarith

end ATK.BaseRiemannXi

#print axioms ATK.BaseRiemannXi.Gammaℝ_conj
#print axioms ATK.BaseRiemannXi.completedRiemannZeta₀_conj
#print axioms ATK.BaseRiemannXi.differentiable_riemannXi
#print axioms ATK.BaseRiemannXi.continuous_riemannXi
#print axioms ATK.BaseRiemannXi.riemannXi_eq
#print axioms ATK.BaseRiemannXi.riemannXi_eq_zeta
#print axioms ATK.BaseRiemannXi.riemannXi_one_sub
#print axioms ATK.BaseRiemannXi.riemannXi_conj
#print axioms ATK.BaseRiemannXi.riemannXi_zero
#print axioms ATK.BaseRiemannXi.riemannXi_one
#print axioms ATK.BaseRiemannXi.riemannXi_eq_zero_iff
#print axioms ATK.BaseRiemannXi.riemannXi_ne_zero_of_one_le_re
#print axioms ATK.BaseRiemannXi.riemannXi_ne_zero_of_re_le_zero
#print axioms ATK.BaseRiemannXi.riemannXi_zero_mem_strip
#print axioms ATK.BaseRiemannXi.re_pos_of_zeta_zero
#print axioms ATK.BaseRiemannXi.riemannXi_critical_im
#print axioms ATK.BaseRiemannXi.riemannXi_critical
#print axioms ATK.BaseRiemannXi.Xi_neg
#print axioms ATK.BaseRiemannXi.continuous_Xi
#print axioms ATK.BaseRiemannXi.zeta_critical_zero_iff
#print axioms ATK.BaseRiemannXi.zero_of_sign_change
#print axioms ATK.BaseRiemannXi.riemannHypothesis_iff_xi
#print axioms ATK.BaseRiemannXi.riemannHypothesis_iff_Xi
