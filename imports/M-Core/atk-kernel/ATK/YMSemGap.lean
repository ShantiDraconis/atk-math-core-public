/-
ATK — Yang–Mills: por que o grupo precisa ser simples (variante sem massa, na rede).

O Clay pede o gap de massa para grupo de calibre compacto **simples**.  Para o grupo abeliano
U(1) a teoria livre é o fóton, sem massa: não há gap.  Este arquivo mostra o mecanismo num modelo
de rede exato (campo escalar livre na rede `ℤ`, que é cada componente do campo U(1) livre):

* `lap_cos`: as ondas planas `n ↦ cos(θ n)` são autofunções do Laplaciano de rede
  `(Δf)(n) = 2f(n) − f(n+1) − f(n−1)`, com autovalor **`4 sin²(θ/2)`**;
* **`sem_gap`** (caso sem massa): para todo `ε > 0` existe modo não constante com energia
  `0 < 4 sin²(θ/2) < ε` — o espectro acumula em 0;
* **`gap_massivo`** (caso com massa m): os mesmos modos têm energia `m² + 4 sin²(θ/2) ≥ m²`, e
  no volume finito `ℤ/L` a forma quadrática satisfaz `⟨f, (Δ + m²) f⟩ ≥ m² ‖f‖²` para **todo** f,
  uniformemente em L (`forma_massiva`, via `⟨f, Δf⟩ = Σ (f(n+1) − f(n))²`).

É um modelo de brinquedo: não é Yang–Mills não abeliano em 4D, cuja construção e gap seguem OPEN.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace ATK.YMSemGap

open Real Finset

/-! ### Rede infinita ℤ -/

/-- Laplaciano de rede em `ℤ`. -/
def lap (f : ℤ → ℝ) (n : ℤ) : ℝ := 2 * f n - f (n + 1) - f (n - 1)

/-- Autovalor da onda plana de frequência θ. -/
noncomputable def energia (θ : ℝ) : ℝ := 4 * sin (θ / 2) ^ 2

/-- **Ondas planas são autofunções**: `Δ cos(θ·) = 4 sin²(θ/2) · cos(θ·)`. -/
theorem lap_cos (θ : ℝ) (n : ℤ) :
    lap (fun m : ℤ => cos (θ * m)) n = energia θ * cos (θ * n) := by
  unfold lap energia
  push_cast
  have h1 : cos (θ * (n + 1)) = cos (θ * n) * cos θ - sin (θ * n) * sin θ := by
    rw [mul_add, mul_one, cos_add]
  have h2 : cos (θ * (n - 1)) = cos (θ * n) * cos θ + sin (θ * n) * sin θ := by
    rw [mul_sub, mul_one, cos_sub]
  have h3 : cos θ = 1 - 2 * sin (θ / 2) ^ 2 := by
    have := cos_sq_add_sin_sq (θ / 2)
    have h4 : cos θ = cos (2 * (θ / 2)) := by ring_nf
    rw [h4, cos_two_mul]
    linarith
  rw [h1, h2, h3]
  ring

theorem energia_nonneg (θ : ℝ) : 0 ≤ energia θ := by
  unfold energia; positivity

theorem energia_pos {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 2 * π) : 0 < energia θ := by
  unfold energia
  have : 0 < sin (θ / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  positivity

theorem energia_le (θ : ℝ) : energia θ ≤ θ ^ 2 := by
  unfold energia
  have h : sin (θ / 2) ^ 2 ≤ (θ / 2) ^ 2 := sin_sq_le_sq
  nlinarith

/-- **Sem massa, sem gap**: há modos não constantes de energia positiva arbitrariamente pequena. -/
theorem sem_gap (ε : ℝ) (hε : 0 < ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 2 * π ∧ 0 < energia θ ∧ energia θ < ε ∧
      (∀ n : ℤ, lap (fun m : ℤ => cos (θ * m)) n = energia θ * cos (θ * n)) := by
  set θ := min (1 / 2) (ε / 2) with hθ
  have hθ0 : 0 < θ := lt_min (by norm_num) (by linarith)
  have hθ1 : θ ≤ 1 / 2 := min_le_left _ _
  have hθ2 : θ ≤ ε / 2 := min_le_right _ _
  have hpi : θ < 2 * π := by linarith [two_le_pi]
  refine ⟨θ, hθ0, hpi, energia_pos hθ0 hpi, ?_, lap_cos θ⟩
  have h1 := energia_le θ
  nlinarith

/-- **Com massa m, gap ≥ m²** nos mesmos modos. -/
theorem gap_massivo (m θ : ℝ) (n : ℤ) :
    lap (fun k : ℤ => cos (θ * k)) n + m ^ 2 * cos (θ * n) =
        (m ^ 2 + energia θ) * cos (θ * n) ∧ m ^ 2 ≤ m ^ 2 + energia θ := by
  refine ⟨by rw [lap_cos]; ring, by linarith [energia_nonneg θ]⟩

/-! ### Volume finito ℤ/L -/

section Finito

variable {L : ℕ} [NeZero L]

/-- Laplaciano no ciclo `ℤ/L`. -/
def lapL (f : ZMod L → ℝ) (n : ZMod L) : ℝ := 2 * f n - f (n + 1) - f (n - 1)

theorem soma_desloc (g : ZMod L → ℝ) (a : ZMod L) : ∑ n, g (n + a) = ∑ n, g n :=
  Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)

/-- `⟨f, Δf⟩ = Σ (f(n+1) − f(n))²`. -/
theorem forma_lap (f : ZMod L → ℝ) : ∑ n, f n * lapL f n = ∑ n, (f (n + 1) - f n) ^ 2 := by
  unfold lapL
  have e1 : ∑ n, f n * f (n - 1) = ∑ n, f (n + 1) * f n := by
    rw [← soma_desloc (fun n => f n * f (n - 1)) 1]
    simp
  have e2 : ∑ n, f (n + 1) ^ 2 = ∑ n, f n ^ 2 := soma_desloc (fun n => f n ^ 2) 1
  have lhs : ∑ n, f n * (2 * f n - f (n + 1) - f (n - 1))
      = 2 * ∑ n, f n ^ 2 - ∑ n, f (n + 1) * f n - ∑ n, f n * f (n - 1) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have rhs : ∑ n, (f (n + 1) - f n) ^ 2
      = ∑ n, f (n + 1) ^ 2 - 2 * ∑ n, f (n + 1) * f n + ∑ n, f n ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [lhs, rhs, e1, e2]
  ring

theorem forma_lap_nonneg (f : ZMod L → ℝ) : 0 ≤ ∑ n, f n * lapL f n := by
  rw [forma_lap]
  exact Finset.sum_nonneg fun n _ => sq_nonneg _

/-- **Gap massivo uniforme em L**: `⟨f, (Δ + m²) f⟩ ≥ m² ‖f‖²`. -/
theorem forma_massiva (m : ℝ) (f : ZMod L → ℝ) :
    m ^ 2 * ∑ n, f n ^ 2 ≤ ∑ n, f n * (lapL f n + m ^ 2 * f n) := by
  have h := forma_lap_nonneg f
  have e : ∑ n, f n * (lapL f n + m ^ 2 * f n) = ∑ n, f n * lapL f n + m ^ 2 * ∑ n, f n ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [e]
  linarith

end Finito

end ATK.YMSemGap

#print axioms ATK.YMSemGap.lap_cos
#print axioms ATK.YMSemGap.energia_nonneg
#print axioms ATK.YMSemGap.energia_pos
#print axioms ATK.YMSemGap.energia_le
#print axioms ATK.YMSemGap.sem_gap
#print axioms ATK.YMSemGap.gap_massivo
#print axioms ATK.YMSemGap.soma_desloc
#print axioms ATK.YMSemGap.forma_lap
#print axioms ATK.YMSemGap.forma_lap_nonneg
#print axioms ATK.YMSemGap.forma_massiva
