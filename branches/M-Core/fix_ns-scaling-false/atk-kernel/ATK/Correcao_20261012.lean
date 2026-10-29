import Mathlib

/-!
# ATK — correção NS-SCALING-FALSE (12/10/2026)

Os itens 19, 20 e 21 da lista de 72 são FALSOS; o item 52 cai por dependência.
Isto é sobre a rota interna do ATK (cotas absolutas subcríticas), NÃO sobre o problema do milênio:
os enunciados (A)–(D) do Clay em `ATK/Exact.lean` continuam abertos.

## Formalização

Um `ScalingModel` abstrai os três funcionais de Navier–Stokes
  y = ‖ω‖²,  z = ‖∇ω‖²,  S = ∫ ω·(∇u)ω
e as duas operações que os reescalam:
  amplitude  u ↦ a·u         : y·a², z·a², S·a³
  dilatação  u ↦ λ·u(λ·)      : y·λ,  z·λ³, S·λ³   (ℝ³; mudança de variáveis)
As leis de escala entram como campos da estrutura: são identidades de mudança de variáveis,
conferidas numericamente com expoentes exatos até 10⁻⁶ em `ns_data/scaling_counterexample.py`
(m-core-openai-ns-audit). O único dado empírico é um estado com S > 0: o campo semente
v = rot ψ tem y = 43.4111, z = 1258.88, S = 0.111925 (estável em 64³, 96³, 128³).

* `ns_20_21_false` / `ns_20_21_no_split`: nenhuma constante c com S ≤ c·ν·z; logo nenhuma divisão
  S = B + T com B ≤ c_B ν z e T ≤ c_T ν z (c_B* + c_T* = +∞).
* `ns_19_false`: nenhum C com S ≤ θνz + C·y², qualquer que seja θ.
* `ns_52_failed`: o orçamento bulk + tail + resto quadrático cai junto.
* `only_cubic_survives`: o teste de escala como teorema — uma cota S ≤ θνz + C·yᵖ válida para todos os
  estados obriga p = 3, o expoente da cota clássica (ν/2)z + C ν⁻³ y³ (que só dá regularidade local).
-/

namespace ATK.Correcao_20261012

/-- Funcionais y, z, S sobre um espaço de estados, com as leis de escala de Navier–Stokes em ℝ³. -/
structure ScalingModel where
  State : Type
  y : State → ℝ
  z : State → ℝ
  S : State → ℝ
  amp : ℝ → State → State
  dil : ℝ → State → State
  y_amp : ∀ a, 0 < a → ∀ u, y (amp a u) = a ^ 2 * y u
  z_amp : ∀ a, 0 < a → ∀ u, z (amp a u) = a ^ 2 * z u
  S_amp : ∀ a, 0 < a → ∀ u, S (amp a u) = a ^ 3 * S u
  y_dil : ∀ l, 0 < l → ∀ u, y (dil l u) = l * y u
  z_dil : ∀ l, 0 < l → ∀ u, z (dil l u) = l ^ 3 * z u
  S_dil : ∀ l, 0 < l → ∀ u, S (dil l u) = l ^ 3 * S u

variable (M : ScalingModel)

/-- Lema A (amplitude): de um estado com S > 0 obtém-se, para qualquer θ, um estado com S > θνz. -/
theorem exists_supercritical {ν : ℝ} (hν : 0 < ν) (u₀ : M.State) (hS : 0 < M.S u₀)
    (hz : 0 ≤ M.z u₀) (θ : ℝ) : ∃ u₁, 0 < M.S u₁ - θ * ν * M.z u₁ := by
  have hnum : 0 < |θ| * ν * M.z u₀ + 1 := by
    have := mul_nonneg (mul_nonneg (abs_nonneg θ) hν.le) hz
    linarith
  have ha : 0 < (|θ| * ν * M.z u₀ + 1) / M.S u₀ := div_pos hnum hS
  refine ⟨M.amp ((|θ| * ν * M.z u₀ + 1) / M.S u₀) u₀, ?_⟩
  rw [M.S_amp _ ha, M.z_amp _ ha]
  set a := (|θ| * ν * M.z u₀ + 1) / M.S u₀ with ha_def
  have haS : a * M.S u₀ = |θ| * ν * M.z u₀ + 1 := by
    rw [ha_def, div_mul_cancel₀ _ hS.ne']
  have hθ : θ * ν * M.z u₀ ≤ |θ| * ν * M.z u₀ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self θ) hν.le) hz
  have e : a ^ 3 * M.S u₀ - θ * ν * (a ^ 2 * M.z u₀) =
      a ^ 2 * (a * M.S u₀ - θ * ν * M.z u₀) := by ring
  rw [e]
  exact mul_pos (pow_pos ha 2) (by linarith)

/-- Itens 20/21: sup S/(νz) = +∞ — nenhuma constante c tem S ≤ c·ν·z para todos os estados. -/
theorem ns_20_21_false {ν : ℝ} (hν : 0 < ν) (u₀ : M.State) (hS : 0 < M.S u₀)
    (hz : 0 ≤ M.z u₀) : ¬ ∃ c : ℝ, ∀ u, M.S u ≤ c * ν * M.z u := by
  rintro ⟨c, hc⟩
  obtain ⟨u₁, h⟩ := exists_supercritical M hν u₀ hS hz c
  have := hc u₁
  linarith

/-- Itens 20/21 na forma do ATK: nenhuma divisão S = B + T com B ≤ c_B ν z e T ≤ c_T ν z. -/
theorem ns_20_21_no_split {ν : ℝ} (hν : 0 < ν) (u₀ : M.State) (hS : 0 < M.S u₀)
    (hz : 0 ≤ M.z u₀) :
    ¬ ∃ (B T : M.State → ℝ) (cB cT : ℝ), (∀ u, B u + T u = M.S u) ∧
      (∀ u, B u ≤ cB * ν * M.z u) ∧ (∀ u, T u ≤ cT * ν * M.z u) := by
  rintro ⟨B, T, cB, cT, hBT, hB, hT⟩
  refine ns_20_21_false M hν u₀ hS hz ⟨cB + cT, fun u => ?_⟩
  have e : (cB + cT) * ν * M.z u = cB * ν * M.z u + cT * ν * M.z u := by ring
  linarith [hBT u, hB u, hT u]

/-- Núcleo aritmético da dilatação: l³·D ≤ K·l² para todo l > 0 é impossível se D > 0. -/
theorem no_quadratic_absorption {D K : ℝ} (hD : 0 < D)
    (h : ∀ l : ℝ, 0 < l → l ^ 3 * D ≤ K * l ^ 2) : False := by
  have hl : 0 < (|K| + 1) / D := div_pos (by positivity) hD
  have h1 := h _ hl
  set l := (|K| + 1) / D with hl_def
  have hlD : l * D = |K| + 1 := by rw [hl_def, div_mul_cancel₀ _ hD.ne']
  have hl2 : 0 < l ^ 2 := pow_pos hl 2
  have e1 : l ^ 3 * D = l ^ 2 * (l * D) := by ring
  have e2 : K * l ^ 2 = l ^ 2 * K := by ring
  have h2 : l ^ 2 * (l * D) ≤ l ^ 2 * K := by rw [← e1, ← e2]; exact h1
  have h3 : l * D ≤ K := le_of_mul_le_mul_left h2 hl2
  have := le_abs_self K
  linarith

/-- Item 19: nenhum C com S ≤ θνz + C·y² para todos os estados (qualquer θ). -/
theorem ns_19_false {ν θ : ℝ} (hν : 0 < ν) (u₀ : M.State) (hS : 0 < M.S u₀)
    (hz : 0 ≤ M.z u₀) : ¬ ∃ C : ℝ, ∀ u, M.S u ≤ θ * ν * M.z u + C * M.y u ^ 2 := by
  rintro ⟨C, hC⟩
  obtain ⟨u₁, hD⟩ := exists_supercritical M hν u₀ hS hz θ
  refine no_quadratic_absorption (K := C * M.y u₁ ^ 2) hD fun l hl => ?_
  have h := hC (M.dil l u₁)
  rw [M.S_dil l hl, M.z_dil l hl, M.y_dil l hl] at h
  have e1 : l ^ 3 * (M.S u₁ - θ * ν * M.z u₁) = l ^ 3 * M.S u₁ - θ * ν * (l ^ 3 * M.z u₁) := by
    ring
  have e2 : C * M.y u₁ ^ 2 * l ^ 2 = C * (l * M.y u₁) ^ 2 := by ring
  rw [e1, e2]
  linarith

/-- Item 52 (dependência): o orçamento S = B + T + R com B + T ≤ θνz e R ≤ C·y² é impossível. -/
theorem ns_52_failed {ν : ℝ} (hν : 0 < ν) (u₀ : M.State) (hS : 0 < M.S u₀) (hz : 0 ≤ M.z u₀) :
    ¬ ∃ (B T R : M.State → ℝ) (θ C : ℝ), (∀ u, M.S u = B u + T u + R u) ∧
      (∀ u, B u + T u ≤ θ * ν * M.z u) ∧ (∀ u, R u ≤ C * M.y u ^ 2) := by
  rintro ⟨B, T, R, θ, C, hsplit, hbt, hR⟩
  exact ns_19_false M (θ := θ) hν u₀ hS hz ⟨C, fun u => by linarith [hsplit u, hbt u, hR u]⟩

/-- Rigidez de expoente: l³·D ≤ K·lᵖ para todo l > 0, com D > 0, obriga p = 3. -/
theorem exponent_rigidity {D K : ℝ} {p : ℕ} (hD : 0 < D)
    (h : ∀ l : ℝ, 0 < l → l ^ 3 * D ≤ K * l ^ p) : p = 3 := by
  rcases lt_trichotomy p 3 with hp | hp | hp
  · exfalso
    have hl : 0 < max 1 ((|K| + 1) / D) := lt_of_lt_of_le one_pos (le_max_left _ _)
    have h1 := h _ hl
    set l := max 1 ((|K| + 1) / D) with hl_def
    have hl1 : 1 ≤ l := le_max_left _ _
    have hlD : |K| + 1 ≤ l * D := by
      have : (|K| + 1) / D ≤ l := le_max_right _ _
      rwa [div_le_iff₀ hD] at this
    have hpow : l ^ p ≤ l ^ 2 := pow_le_pow_right₀ hl1 (by omega)
    have hK : K * l ^ p ≤ |K| * l ^ 2 :=
      calc K * l ^ p ≤ |K| * l ^ p := mul_le_mul_of_nonneg_right (le_abs_self K) (pow_nonneg hl.le p)
        _ ≤ |K| * l ^ 2 := mul_le_mul_of_nonneg_left hpow (abs_nonneg K)
    have hl2 : 0 < l ^ 2 := pow_pos hl 2
    have e : l ^ 3 * D = l ^ 2 * (l * D) := by ring
    have h2 : l ^ 2 * (|K| + 1) ≤ l ^ 2 * (l * D) := mul_le_mul_of_nonneg_left hlD hl2.le
    have h3 : l ^ 2 * (|K| + 1) = |K| * l ^ 2 + l ^ 2 := by ring
    linarith
  · exact hp
  · exfalso
    have hl : 0 < min 1 (D / (|K| + 1)) := lt_min one_pos (div_pos hD (by positivity))
    have h1 := h _ hl
    set l := min 1 (D / (|K| + 1)) with hl_def
    have hl1 : l ≤ 1 := min_le_left _ _
    have hlK : l * (|K| + 1) ≤ D := by
      have : l ≤ D / (|K| + 1) := min_le_right _ _
      rwa [le_div_iff₀ (by positivity)] at this
    have hpow : l ^ p ≤ l ^ 4 := pow_le_pow_of_le_one hl.le hl1 (by omega)
    have hK : K * l ^ p ≤ |K| * l ^ 4 :=
      calc K * l ^ p ≤ |K| * l ^ p := mul_le_mul_of_nonneg_right (le_abs_self K) (pow_nonneg hl.le p)
        _ ≤ |K| * l ^ 4 := mul_le_mul_of_nonneg_left hpow (abs_nonneg K)
    have hl3 : 0 < l ^ 3 := pow_pos hl 3
    have e : |K| * l ^ 4 = l ^ 3 * (|K| * l) := by ring
    have hlt : |K| * l < D := by
      have : l * (|K| + 1) = |K| * l + l := by ring
      linarith
    have h4 : l ^ 3 * (|K| * l) < l ^ 3 * D := mul_lt_mul_of_pos_left hlt hl3
    linarith

/-- Teste de escala como teorema: uma cota S ≤ θνz + C·yᵖ válida para todos os estados obriga p = 3. -/
theorem only_cubic_survives {ν θ C : ℝ} (hν : 0 < ν) (u₀ : M.State) (hS : 0 < M.S u₀)
    (hz : 0 ≤ M.z u₀) (p : ℕ) (h : ∀ u, M.S u ≤ θ * ν * M.z u + C * M.y u ^ p) : p = 3 := by
  obtain ⟨u₁, hD⟩ := exists_supercritical M hν u₀ hS hz θ
  refine exponent_rigidity (K := C * M.y u₁ ^ p) hD fun l hl => ?_
  have h1 := h (M.dil l u₁)
  rw [M.S_dil l hl, M.z_dil l hl, M.y_dil l hl, mul_pow] at h1
  have e1 : l ^ 3 * (M.S u₁ - θ * ν * M.z u₁) = l ^ 3 * M.S u₁ - θ * ν * (l ^ 3 * M.z u₁) := by
    ring
  have e2 : C * M.y u₁ ^ p * l ^ p = C * (l ^ p * M.y u₁ ^ p) := by ring
  rw [e1, e2]
  linarith

end ATK.Correcao_20261012

#print axioms ATK.Correcao_20261012.exists_supercritical
#print axioms ATK.Correcao_20261012.ns_20_21_false
#print axioms ATK.Correcao_20261012.ns_20_21_no_split
#print axioms ATK.Correcao_20261012.no_quadratic_absorption
#print axioms ATK.Correcao_20261012.ns_19_false
#print axioms ATK.Correcao_20261012.ns_52_failed
#print axioms ATK.Correcao_20261012.exponent_rigidity
#print axioms ATK.Correcao_20261012.only_cubic_survives
