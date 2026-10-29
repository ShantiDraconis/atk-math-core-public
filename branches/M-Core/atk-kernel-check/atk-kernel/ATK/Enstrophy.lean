import Mathlib

/-!
# ATK — Enstrofia: certificação da dedução NS (proposta de 13/10) e a sua linha crítica

Dedução proposta (toro, vorticidade de média nula, `y = ½‖ω‖²`, `W = ‖ω‖`, `Z = ‖∇ω‖`):

1. `y' + νZ² = S`, `S = ∫(ω·∇)u·ω` (identidade exata para soluções suaves);
2. `|S| ≤ ‖∇u‖₂‖ω‖₄² ≤ C₀ W^{3/2} Z^{3/2}` (Hölder + Gagliardo–Nirenberg + Calderón–Zygmund);
3. Young: `C₀W^{3/2}Z^{3/2} ≤ θνZ² + 27C₀⁴W⁶/(256θ³ν³)`, e com `W² = 2y`:
   `y' + (1−θ)νZ² ≤ A·y³`, `A = 27C₀⁴/(32θ³ν³)`;
4. Poincaré `Z² ≥ λ₁W² = 2λ₁y`: `y' ≤ −a·y + A·y³`, `a = 2(1−θ)νλ₁`;
5. limiar `y_crit = √(a/A)`, ótimo em `θ* = 3/4` (`(1−θ)θ³ ≤ 27/256`): `y_crit = ν²√λ₁/(2C₀²)`.

Os passos 1, 2 e a desigualdade de Poincaré são análise padrão (não formalizada aqui). A ÁLGEBRA
dos passos 3–5 e a dinâmica da comparação são certificadas pelo kernel:

* `young_four`, `young_scaled`: com `X = C₀W^{3/2}`, `q = Z^{1/2}`, `s = θν`:
  `X·q³ ≤ s·q⁴ + 27X⁴/(256s³)` — exatamente o passo 3.
* `young_coefficient`: `27C₀⁴(2y)³/(256(θν)³) = (27C₀⁴/(32θ³ν³))·y³`.
* `theta_optimal`, `theta_optimal_attained`: `(1−θ)θ³ ≤ 27/256` para TODO `θ` real, com igualdade em `3/4`.
* `ycrit_optimal`: em `θ = 3/4`, `a/A = (ν²√λ₁/(2C₀²))²`.
* **Linha crítica para a enstrofia** (`y' ≤ −a y + A y³`):
  `cubic_inside` — abaixo da linha (`A c² < a`) o nível `c ≥ y(0)` nunca é ultrapassado;
  `cubic_on_line_equilibrium` — na linha a comparação é estacionária;
  `cubic_beyond_drift` — acima da linha a comparação empurra para cima (`−ac + Ac³ > 0`).
  A explosão da EQUAÇÃO DE COMPARAÇÃO acima da linha não implica explosão de Navier–Stokes.

Diferença essencial para `ATK.Transition`: lá o número crítico `R = C√E/ν` é invariante por
escala (norma crítica Ḣ^{1/2}); aqui `y_crit ∝ ν²√λ₁` depende do tamanho do toro — a enstrofia é
supercrítica, e o limiar é o resultado clássico de dados pequenos em H¹, não uma lei de escala.
-/

noncomputable section

namespace ATK.Enstrophy

open Set

/-- Young normalizada: `4μ ≤ 3 + μ⁴` (igualdade em `μ = 1`). -/
theorem young_four (μ : ℝ) : 4 * μ ≤ 3 + μ ^ 4 := by
  nlinarith [sq_nonneg (μ - 1), sq_nonneg (μ + 1), sq_nonneg (μ ^ 2 - 1)]

/-- **Passo 3 (Young 4/3–4):** `X q³ ≤ s q⁴ + 27 X⁴/(256 s³)` para `X, q ≥ 0`, `s > 0`. -/
theorem young_scaled {s X q : ℝ} (hs : 0 < s) (hX : 0 ≤ X) (hq : 0 ≤ q) :
    X * q ^ 3 ≤ s * q ^ 4 + 27 * X ^ 4 / (256 * s ^ 3) := by
  rcases eq_or_lt_of_le hq with hq0 | hqpos
  · rw [← hq0]
    have : 0 ≤ 27 * X ^ 4 / (256 * s ^ 3) := by positivity
    simpa using this
  · set μ := 3 * X / (4 * s * q) with hμ
    have hden : 0 < 4 * s * q := by positivity
    have hXμ : X = 4 * s * q * μ / 3 := by
      rw [hμ]
      field_simp
    have key := young_four μ
    have hsq4 : 0 ≤ s * q ^ 4 := by positivity
    have hR : s * q ^ 4 + 27 * X ^ 4 / (256 * s ^ 3) = s * q ^ 4 * (1 + μ ^ 4 / 3) := by
      rw [hXμ]
      field_simp
      ring
    have hL : X * q ^ 3 = s * q ^ 4 * (4 * μ / 3) := by
      rw [hXμ]
      ring
    rw [hR, hL]
    apply mul_le_mul_of_nonneg_left _ hsq4
    linarith

/-- Coeficiente cúbico: com `W² = 2y`, `27C₀⁴W⁶/(256(θν)³) = A(θ,ν)·y³`. -/
theorem young_coefficient (C₀ θ ν y : ℝ) (hθ : θ ≠ 0) (hν : ν ≠ 0) :
    27 * C₀ ^ 4 * (2 * y) ^ 3 / (256 * (θ * ν) ^ 3) = 27 * C₀ ^ 4 / (32 * θ ^ 3 * ν ^ 3) * y ^ 3 := by
  field_simp
  ring

/-- **Ótimo do limiar:** `(1−θ)θ³ ≤ 27/256` para todo `θ` real. -/
theorem theta_optimal (θ : ℝ) : (1 - θ) * θ ^ 3 ≤ 27 / 256 := by
  nlinarith [sq_nonneg (θ - 3 / 4), sq_nonneg (θ + 1 / 4), mul_nonneg (sq_nonneg (θ - 3 / 4))
    (add_nonneg (sq_nonneg (θ + 1 / 4)) (by norm_num : (0 : ℝ) ≤ 1 / 8))]

theorem theta_optimal_attained : (1 - (3 / 4 : ℝ)) * (3 / 4) ^ 3 = 27 / 256 := by norm_num

/-- **Limiar ótimo:** em `θ = 3/4`, `a/A = (ν²√λ₁/(2C₀²))²` com `a = 2(1−θ)νλ₁`,
`A = 27C₀⁴/(32θ³ν³)`; logo `y_crit = √(a/A) = ν²√λ₁/(2C₀²)`. -/
theorem ycrit_optimal {C₀ ν l : ℝ} (hC : 0 < C₀) (hν : 0 < ν) (hl : 0 ≤ l) :
    (2 * (1 - 3 / 4) * ν * l) / (27 * C₀ ^ 4 / (32 * (3 / 4) ^ 3 * ν ^ 3)) =
      (ν ^ 2 * Real.sqrt l / (2 * C₀ ^ 2)) ^ 2 := by
  have hs : Real.sqrt l ^ 2 = l := Real.sq_sqrt hl
  have hR : (ν ^ 2 * Real.sqrt l / (2 * C₀ ^ 2)) ^ 2 = ν ^ 4 * l / (4 * C₀ ^ 4) := by
    rw [div_pow, mul_pow, hs]
    ring
  rw [hR]
  have hC' : C₀ ≠ 0 := hC.ne'
  have hν' : ν ≠ 0 := hν.ne'
  field_simp
  ring

theorem ycrit_value {C₀ ν l : ℝ} (hC : 0 < C₀) (hν : 0 < ν) (hl : 0 ≤ l) :
    Real.sqrt ((2 * (1 - 3 / 4) * ν * l) / (27 * C₀ ^ 4 / (32 * (3 / 4) ^ 3 * ν ^ 3))) =
      ν ^ 2 * Real.sqrt l / (2 * C₀ ^ 2) := by
  rw [ycrit_optimal hC hν hl, Real.sqrt_sq (by positivity)]

/-- **Abaixo da linha:** se `y' ≤ −a y + A y³`, `A ≥ 0` e o nível `c ≥ y(0)` satisfaz
`0 < c`, `A c² < a`, então `y(t) ≤ c` em `[0,T]`. -/
theorem cubic_inside {y y' : ℝ → ℝ} {a A T c : ℝ}
    (hcont : ContinuousOn y (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt y (y' t) (Ici t) t)
    (hineq : ∀ t ∈ Ico 0 T, y' t ≤ -a * y t + A * y t ^ 3)
    (hc0 : y 0 ≤ c) (hcpos : 0 < c) (hline : A * c ^ 2 < a) :
    ∀ t ∈ Icc 0 T, y t ≤ c := by
  have hbound : ∀ t ∈ Ico 0 T, y t = c → y' t < 0 := by
    intro t ht hyt
    have h1 := hineq t ht
    rw [hyt] at h1
    have h2 : -a * c + A * c ^ 3 = c * (A * c ^ 2 - a) := by ring
    have h3 : c * (A * c ^ 2 - a) < 0 := mul_neg_of_pos_of_neg hcpos (by linarith)
    linarith
  have key := image_le_of_deriv_right_lt_deriv_boundary (B := fun _ => c) (B' := fun _ => 0)
    hcont hderiv hc0 (fun x => hasDerivAt_const x c) hbound
  exact fun t ht => key ht

/-- Na linha `A c² = a` o lado direito da comparação se anula: equilíbrio. -/
theorem cubic_on_line_equilibrium {a A c : ℝ} (hline : A * c ^ 2 = a) :
    -a * c + A * c ^ 3 = 0 := by
  rw [← hline]
  ring

/-- Acima da linha (`A c² > a`, `c > 0`) a comparação empurra para cima: nenhum aprisionamento. -/
theorem cubic_beyond_drift {a A c : ℝ} (hcpos : 0 < c) (hline : a < A * c ^ 2) :
    0 < -a * c + A * c ^ 3 := by
  have : -a * c + A * c ^ 3 = c * (A * c ^ 2 - a) := by ring
  rw [this]
  exact mul_pos hcpos (by linarith)

end ATK.Enstrophy

end

#print axioms ATK.Enstrophy.young_four
#print axioms ATK.Enstrophy.young_scaled
#print axioms ATK.Enstrophy.young_coefficient
#print axioms ATK.Enstrophy.theta_optimal
#print axioms ATK.Enstrophy.theta_optimal_attained
#print axioms ATK.Enstrophy.ycrit_optimal
#print axioms ATK.Enstrophy.ycrit_value
#print axioms ATK.Enstrophy.cubic_inside
#print axioms ATK.Enstrophy.cubic_on_line_equilibrium
#print axioms ATK.Enstrophy.cubic_beyond_drift
