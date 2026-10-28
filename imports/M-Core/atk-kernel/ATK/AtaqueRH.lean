/-
ATK — Programa de ataque, frente RH: os alvos da escada clássica e as reduções entre eles.

Sobre `ATK.BaseRiemannXi` (Ξ real, par, contínua), `ATK.BaseRiemannXiSinal` (`Ξ(0) > 0`) e
`ATK.BaseRiemannTeta` (fórmula de Riemann para Ξ):

* `zerosReta`: as alturas `t > 0` com `ζ(1/2 + it) = 0`;
* **alvo R4 — `Hardy`**: `zerosReta` é infinito (Hardy, 1914);
* `TrocasInfinitas`: Ξ troca de sinal arbitrariamente longe;
* **`hardy_of_trocas`**: `TrocasInfinitas ⇒ Hardy` — o argumento de Hardy fica reduzido a
  produzir trocas de sinal;
* **alvo R5 — `SinalNegativo`**: existe `t > 0` com `Ξ(t) < 0` (o primeiro zero está em
  `t ≈ 14,13`); **`zero_de_sinalNegativo`**: R5 ⇒ ζ tem um zero na reta crítica;
* `integralRiemann t = ∫₁^∞ ψ(x) x^{−3/4} cos((t/2) log x) dx` e **`sinal_de_integral`**: uma
  cota inferior certificada `(t² + 1/4)·I(t) > 1/2` basta para R5 — é a forma em que a
  aritmética intervalar (`ATK.BaseIntervalar`) entra;
* **`trocas_de_sequencia`**: uma sequência de pontos com sinais alternados e alturas sem
  cota dá `TrocasInfinitas`.

A Hipótese de Riemann (alvo O1, `riemannHypothesis_iff_Xi`) não é tocada aqui.
-/
import ATK.BaseRiemannXiSinal
import ATK.BaseRiemannTeta

open Complex Set MeasureTheory Filter
open scoped Real

namespace ATK.AtaqueRH

open ATK.BaseRiemannXi ATK.BaseRiemannXiSinal ATK.BaseRiemannTeta

/-- Alturas positivas dos zeros de ζ na reta crítica. -/
def zerosReta : Set ℝ := {t | 0 < t ∧ riemannZeta (1 / 2 + t * I) = 0}

/-- **Alvo R4 (Hardy, 1914)**: infinitos zeros na reta crítica. -/
def Hardy : Prop := zerosReta.Infinite

/-- Ξ troca de sinal arbitrariamente longe. -/
def TrocasInfinitas : Prop := ∀ T : ℝ, ∃ a b : ℝ, T ≤ a ∧ a ≤ b ∧ Xi a * Xi b < 0

/-- Uma troca de sinal em `[a, b]`, `a ≥ 0`, dá um zero na reta com altura em `(a, b)`. -/
theorem zero_de_troca {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (h : Xi a * Xi b < 0) :
    ∃ t ∈ zerosReta, a < t ∧ t < b := by
  obtain ⟨t, ht, hz⟩ := zero_of_sign_change hab h
  exact ⟨t, ⟨by linarith [ht.1], hz⟩, ht.1, ht.2⟩

/-- **Redução de Hardy**: infinitas trocas de sinal de Ξ ⇒ infinitos zeros na reta crítica. -/
theorem hardy_of_trocas (h : TrocasInfinitas) : Hardy := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨M, hM⟩
  obtain ⟨a, b, hTa, hab, hs⟩ := h (max M 0)
  obtain ⟨t, htz, hat, -⟩ := zero_de_troca (le_trans (le_max_right _ _) hTa) hab hs
  have := hM htz
  linarith [le_max_left M 0]

/-- Uma sequência `tₖ → ∞` com `Ξ(tₖ) Ξ(tₖ₊₁) < 0` dá `TrocasInfinitas`. -/
theorem trocas_de_sequencia (t : ℕ → ℝ) (hmono : Monotone t) (hlim : Tendsto t atTop atTop)
    (hsinal : ∀ k, Xi (t k) * Xi (t (k + 1)) < 0) : TrocasInfinitas := by
  intro T
  obtain ⟨k, hk⟩ := (tendsto_atTop.mp hlim T).exists
  exact ⟨t k, t (k + 1), hk, hmono (Nat.le_succ k), hsinal k⟩

/-- **Alvo R5**: existe `t > 0` com `Ξ(t) < 0`. -/
def SinalNegativo : Prop := ∃ t : ℝ, 0 < t ∧ Xi t < 0

/-- R5 ⇒ ζ tem um zero na reta crítica (com `Ξ(0) > 0`). -/
theorem zero_de_sinalNegativo (h : SinalNegativo) : zerosReta.Nonempty := by
  obtain ⟨t, ht, hneg⟩ := h
  obtain ⟨u, hu, hz⟩ := zero_of_Xi_neg ht hneg
  exact ⟨u, hu.1, hz⟩

/-- A integral da fórmula de Riemann. -/
noncomputable def integralRiemann (t : ℝ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), psi x * x ^ (-(3 / 4 : ℝ)) * Real.cos (t / 2 * Real.log x)

theorem Xi_eq_integral (t : ℝ) : Xi t = 1 / 2 - (t ^ 2 + 1 / 4) * integralRiemann t :=
  Xi_riemann t

/-- **Certificado numérico para R5**: uma cota inferior para a integral de Riemann basta. -/
theorem sinal_de_integral {t : ℝ} (ht : 0 < t) (h : 1 / 2 < (t ^ 2 + 1 / 4) * integralRiemann t) :
    SinalNegativo :=
  ⟨t, ht, by rw [Xi_eq_integral]; linarith⟩

/-- E, simetricamente, uma cota superior certifica `Ξ(t) > 0`. -/
theorem Xi_pos_de_integral {t : ℝ} (h : (t ^ 2 + 1 / 4) * integralRiemann t < 1 / 2) :
    0 < Xi t := by
  rw [Xi_eq_integral]
  linarith

/-- Dois certificados de sinal opostos em `0 ≤ a ≤ b` dão um zero na reta entre eles. -/
theorem zero_de_certificados {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hpos : (a ^ 2 + 1 / 4) * integralRiemann a < 1 / 2)
    (hneg : 1 / 2 < (b ^ 2 + 1 / 4) * integralRiemann b) :
    ∃ t ∈ zerosReta, a < t ∧ t < b := by
  have h1 := Xi_pos_de_integral hpos
  have h2 : Xi b < 0 := by rw [Xi_eq_integral]; linarith
  exact zero_de_troca ha hab (mul_neg_of_pos_of_neg h1 h2)

end ATK.AtaqueRH

#print axioms ATK.AtaqueRH.zero_de_troca
#print axioms ATK.AtaqueRH.hardy_of_trocas
#print axioms ATK.AtaqueRH.trocas_de_sequencia
#print axioms ATK.AtaqueRH.zero_de_sinalNegativo
#print axioms ATK.AtaqueRH.Xi_eq_integral
#print axioms ATK.AtaqueRH.sinal_de_integral
#print axioms ATK.AtaqueRH.Xi_pos_de_integral
#print axioms ATK.AtaqueRH.zero_de_certificados
