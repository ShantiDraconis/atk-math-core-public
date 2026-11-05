import ATK.ForaDaLinha

/-!
# ATK-RH — Hipótese H: um eixo deslocado `κ = 1/2 + ε`, `ε ≠ 0`

Sistema: `ζ(α + iβ) = 0` e `ζ(2κ − α + iβ) = 0`. Dois zeros `ρ₁, ρ₂` na mesma altura `β` têm eixo
`κ = (α₁ + α₂)/2` e desvio `ε = κ − 1/2` (`eps`). O que o kernel decide:

* `eps_torcao`: o par formado por um zero e seu reflexo funcional `1 − ρ̄` (mesma altura,
  `im_torcao`) tem **sempre** `ε = 0` — mesmo que `ρ` esteja fora da linha. A simetria da equação
  funcional nunca desloca o eixo.
* `eps_par_trivial`: no par trivial `ρ₂ = ρ₁`, `ε ≠ 0 ⟺ Re ρ₁ ≠ 1/2` — H com par trivial é
  exatamente um zero fora da linha.
* `par_deslocado_refuta`: qualquer par na mesma altura com `ε ≠ 0` refuta RH; `rh_um_por_altura`:
  sob RH há no máximo um zero não trivial por altura.
* **`tres_zeros`**: um par **distinto** com `ε ≠ 0` obriga **três zeros distintos na mesma altura**
  (o par e o reflexo de um membro fora da linha) — mais do que `¬RH` exige.

Nada aqui produz um zero fora da linha nem prova RH.
-/

namespace ATK.EixoDeslocado

open ATK.ZetaSimetria ATK.ForaDaLinha

theorem im_torcao (s : ℂ) : (torcao s).im = s.im := by unfold torcao; simp

/-- Sob RH, todo zero não trivial tem parte real `1/2`. -/
theorem re_de_rh (h : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ Z) : ρ.re = 1 / 2 := by
  rw [riemann_iff_vazio] at h
  by_contra hne
  exact h.false ⟨ρ, hρ, hne⟩

/-- Sob RH, há no máximo um zero não trivial em cada altura. -/
theorem rh_um_por_altura (h : RiemannHypothesis) {ρ₁ ρ₂ : ℂ} (h1 : ρ₁ ∈ Z) (h2 : ρ₂ ∈ Z)
    (him : ρ₁.im = ρ₂.im) : ρ₁ = ρ₂ :=
  Complex.ext (by rw [re_de_rh h h1, re_de_rh h h2]) him

/-- Desvio do eixo de um par: `ε = (α₁ + α₂)/2 − 1/2`. -/
noncomputable def eps (ρ₁ ρ₂ : ℂ) : ℝ := (ρ₁.re + ρ₂.re) / 2 - 1 / 2

/-- O reflexo funcional nunca desloca o eixo: `ε(ρ, 1 − ρ̄) = 0`, na mesma altura. -/
theorem eps_torcao (ρ : ℂ) : eps ρ (torcao ρ) = 0 ∧ (torcao ρ).im = ρ.im := by
  refine ⟨?_, im_torcao ρ⟩
  unfold eps; rw [re_torcao]; ring

/-- Par trivial: `ε(ρ, ρ) ≠ 0 ⟺ Re ρ ≠ 1/2`. -/
theorem eps_par_trivial (ρ : ℂ) : eps ρ ρ ≠ 0 ↔ ρ.re ≠ 1 / 2 := by
  unfold eps
  constructor
  · intro h hr; apply h; rw [hr]; ring
  · intro h he; apply h; linarith

/-- **H refuta RH**: um par de zeros na mesma altura com `ε ≠ 0` implica `¬RH`. -/
theorem par_deslocado_refuta {ρ₁ ρ₂ : ℂ} (h1 : ρ₁ ∈ Z) (h2 : ρ₂ ∈ Z) (he : eps ρ₁ ρ₂ ≠ 0) :
    ¬ RiemannHypothesis := by
  intro h
  apply he
  unfold eps; rw [re_de_rh h h1, re_de_rh h h2]; ring

/-- **H com par distinto exige três zeros distintos na mesma altura.** -/
theorem tres_zeros {ρ₁ ρ₂ : ℂ} (h1 : ρ₁ ∈ Z) (h2 : ρ₂ ∈ Z) (him : ρ₁.im = ρ₂.im)
    (hne : ρ₁ ≠ ρ₂) (he : eps ρ₁ ρ₂ ≠ 0) :
    ∃ ρ₃ ∈ Z, ρ₃.im = ρ₁.im ∧ ρ₃ ≠ ρ₁ ∧ ρ₃ ≠ ρ₂ := by
  by_cases hr1 : ρ₁.re = 1 / 2
  · have hr2 : ρ₂.re ≠ 1 / 2 := by
      intro hr2; exact hne (Complex.ext (by rw [hr1, hr2]) him)
    refine ⟨torcao ρ₂, torcao_mem_Z h2, by rw [im_torcao, him], ?_, ?_⟩
    · intro h; apply hr2
      have := congrArg Complex.re h; rw [re_torcao, hr1] at this; linarith
    · intro h; apply hr2
      have := congrArg Complex.re h; rw [re_torcao] at this; linarith
  · refine ⟨torcao ρ₁, torcao_mem_Z h1, im_torcao ρ₁, ?_, ?_⟩
    · intro h; apply hr1
      have := congrArg Complex.re h; rw [re_torcao] at this; linarith
    · intro h; apply he
      have := congrArg Complex.re h; rw [re_torcao] at this
      unfold eps; linarith

end ATK.EixoDeslocado

#print axioms ATK.EixoDeslocado.im_torcao
#print axioms ATK.EixoDeslocado.re_de_rh
#print axioms ATK.EixoDeslocado.rh_um_por_altura
#print axioms ATK.EixoDeslocado.eps_torcao
#print axioms ATK.EixoDeslocado.eps_par_trivial
#print axioms ATK.EixoDeslocado.par_deslocado_refuta
#print axioms ATK.EixoDeslocado.tres_zeros
