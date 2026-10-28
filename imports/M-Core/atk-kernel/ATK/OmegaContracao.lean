/-
ATK-Ω — Teorema de anulação por contração acoplada.

Vetores de defeitos δ_n ≥ 0 indexados por um tipo finito ι (as sete ou oito
classes), acoplados por uma matriz A ≥ 0 com somas de linha ≤ q < 1:

    δ_{n+1} ≤ A δ_n   ⇒   max_i δ_n(i) ≤ q^n · max_i δ_0(i),

com versão perturbada (δ_{n+1} ≤ A δ_n + b_n, ‖b_n‖ ≤ β_n) e o teorema
condicional de certificação (fidelidade + acoplamento + estabilidade ⇒ conjunção).

É álgebra linear elementar.  A matriz A e a fidelidade dos defeitos aos sete
problemas são hipóteses, não teoremas.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ATK.OmegaContracao

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Norma do máximo de um vetor de defeitos. -/
noncomputable def normInf (v : ι → ℝ) : ℝ := univ.sup' univ_nonempty (fun i => |v i|)

theorem le_normInf (v : ι → ℝ) (i : ι) : |v i| ≤ normInf v :=
  le_sup' (fun i => |v i|) (mem_univ i)

theorem normInf_nonneg (v : ι → ℝ) : 0 ≤ normInf v :=
  (abs_nonneg _).trans (le_normInf v (Classical.arbitrary ι))

theorem normInf_le {v : ι → ℝ} {c : ℝ} (h : ∀ i, |v i| ≤ c) : normInf v ≤ c :=
  (sup'_le_iff _ _).2 fun i _ => h i

/-- Vetor não negativo. -/
def Nonneg (v : ι → ℝ) : Prop := ∀ i, 0 ≤ v i

/-- Acoplamento: δ' ≤ A δ coordenada a coordenada. -/
def Acopla (A : ι → ι → ℝ) (δ δ' : ι → ℝ) : Prop :=
  ∀ i, δ' i ≤ ∑ j, A i j * δ j

/-- Somas de linha limitadas por q. -/
def RowSumLe (A : ι → ι → ℝ) (q : ℝ) : Prop := ∀ i, ∑ j, A i j ≤ q

/-- Passo único: se δ ≥ 0, δ' ≥ 0, A ≥ 0 com somas de linha ≤ q, então
‖δ'‖∞ ≤ q ‖δ‖∞. -/
theorem step_bound (A : ι → ι → ℝ) (hA : ∀ i j, 0 ≤ A i j) {q : ℝ} (hq : RowSumLe A q)
    {δ δ' : ι → ℝ} (_hδ : Nonneg δ) (hδ' : Nonneg δ') (h : Acopla A δ δ') :
    normInf δ' ≤ q * normInf δ := by
  apply normInf_le
  intro i
  rw [abs_of_nonneg (hδ' i)]
  calc δ' i ≤ ∑ j, A i j * δ j := h i
    _ ≤ ∑ j, A i j * normInf δ := by
        apply sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (le_normInf δ j)) (hA i j)
    _ = (∑ j, A i j) * normInf δ := by rw [sum_mul]
    _ ≤ q * normInf δ := mul_le_mul_of_nonneg_right (hq i) (normInf_nonneg δ)

/-- Teorema ATK-Ω (versão em norma): ‖δ_n‖∞ ≤ q^n ‖δ_0‖∞. -/
theorem contraction (A : ι → ι → ℝ) (hA : ∀ i j, 0 ≤ A i j) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : RowSumLe A q) (δ : ℕ → ι → ℝ) (hpos : ∀ n, Nonneg (δ n))
    (hstep : ∀ n, Acopla A (δ n) (δ (n + 1))) :
    ∀ n, normInf (δ n) ≤ q ^ n * normInf (δ 0) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc normInf (δ (n + 1)) ≤ q * normInf (δ n) :=
          step_bound A hA hq (hpos n) (hpos (n + 1)) (hstep n)
      _ ≤ q * (q ^ n * normInf (δ 0)) := mul_le_mul_of_nonneg_left ih hq0
      _ = q ^ (n + 1) * normInf (δ 0) := by ring

/-- Versão perturbada: δ_{n+1} ≤ A δ_n + b_n com ‖b_n‖∞ ≤ β.  Então
‖δ_n‖∞ ≤ q^n ‖δ_0‖∞ + β (1 + q + … + q^{n-1}) ≤ q^n ‖δ_0‖∞ + β/(1 − q). -/
theorem contraction_perturbed (A : ι → ι → ℝ) (hA : ∀ i j, 0 ≤ A i j) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) (hq : RowSumLe A q) (δ b : ℕ → ι → ℝ) (hpos : ∀ n, Nonneg (δ n))
    {β : ℝ} (hβ : ∀ n, normInf (b n) ≤ β)
    (hstep : ∀ n i, δ (n + 1) i ≤ (∑ j, A i j * δ n j) + b n i) :
    ∀ n, normInf (δ n) ≤ q ^ n * normInf (δ 0) + β / (1 - q) := by
  have hβ0 : 0 ≤ β := (normInf_nonneg _).trans (hβ 0)
  have h1q : 0 < 1 - q := by linarith
  intro n
  induction n with
  | zero =>
    simp only [pow_zero, one_mul]
    have : 0 ≤ β / (1 - q) := div_nonneg hβ0 h1q.le
    linarith
  | succ n ih =>
    have hstepn : normInf (δ (n + 1)) ≤ q * normInf (δ n) + β := by
      apply normInf_le
      intro i
      rw [abs_of_nonneg (hpos (n + 1) i)]
      calc δ (n + 1) i ≤ (∑ j, A i j * δ n j) + b n i := hstep n i
        _ ≤ (∑ j, A i j * normInf (δ n)) + β := by
            apply add_le_add
            · apply sum_le_sum; intro j _
              exact mul_le_mul_of_nonneg_left
                ((le_abs_self _).trans (le_normInf (δ n) j)) (hA i j)
            · exact (le_abs_self _).trans ((le_normInf (b n) i).trans (hβ n))
        _ = (∑ j, A i j) * normInf (δ n) + β := by rw [sum_mul]
        _ ≤ q * normInf (δ n) + β := by
            have := mul_le_mul_of_nonneg_right (hq i) (normInf_nonneg (δ n)); linarith
    calc normInf (δ (n + 1)) ≤ q * normInf (δ n) + β := hstepn
      _ ≤ q * (q ^ n * normInf (δ 0) + β / (1 - q)) + β := by
          have := mul_le_mul_of_nonneg_left ih hq0; linarith
      _ = q ^ (n + 1) * normInf (δ 0) + (q * (β / (1 - q)) + β) := by ring
      _ = q ^ (n + 1) * normInf (δ 0) + β / (1 - q) := by
          congr 1
          field_simp
          ring

/-- Redução de oito classes a sete: se a oitava coordenada é identicamente nula
(Poincaré já demonstrada), as sete primeiras obedecem ao bloco B = A restrito. -/
theorem block_reduction {κ : Type*} [Fintype κ] (A : Option κ → Option κ → ℝ)
    (δ δ' : Option κ → ℝ)
    (h0 : δ none = 0) (h : Acopla A δ δ') :
    ∀ i : κ, δ' (some i) ≤ ∑ j : κ, A (some i) (some j) * δ (some j) := by
  intro i
  calc δ' (some i) ≤ ∑ j, A (some i) j * δ j := h (some i)
    _ = A (some i) none * δ none + ∑ j : κ, A (some i) (some j) * δ (some j) := by
        rw [Fintype.sum_option]
    _ = ∑ j : κ, A (some i) (some j) * δ (some j) := by rw [h0]; ring

/-- Lema "resolver uma coordenada não resolve as outras": A = diag(1, 1/2) mantém
a primeira coordenada em 1 para sempre. -/
theorem uma_coordenada_nao_basta :
    ∃ (A : Fin 2 → Fin 2 → ℝ) (δ : ℕ → Fin 2 → ℝ),
      (∀ i j, 0 ≤ A i j) ∧ (∀ n, Acopla A (δ n) (δ (n + 1))) ∧
      (∀ n, δ n 0 = 1) ∧ (∀ n, δ n 1 = (1 / 2) ^ n) := by
  refine ⟨![![1, 0], ![0, 1 / 2]], fun n => ![1, (1 / 2) ^ n], ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp
  · intro n i; fin_cases i <;> simp [Acopla, Fin.sum_univ_two, pow_succ] <;> ring_nf <;> simp
  · intro n; simp
  · intro n; simp

/-! ### Teorema condicional de certificação -/

/-- Fidelidade: defeito nulo no limite ⇒ enunciado.  Representamos "δ_i(n) → 0"
pelo predicado `Vanishes`. -/
def Vanishes (d : ℕ → ℝ) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, d n < ε

theorem vanishes_of_geometric {d : ℕ → ℝ} {C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hd0 : ∀ n, 0 ≤ d n) (hd : ∀ n, d n ≤ C * q ^ n) : Vanishes d := by
  intro ε hε
  have hC : 0 ≤ C := by
    have := (hd0 0).trans (hd 0); simpa using this
  -- q^n → 0: escolhe N com C q^N < ε
  obtain ⟨N, hN⟩ : ∃ N : ℕ, C * q ^ N < ε := by
    rcases eq_or_lt_of_le hq0 with rfl | hqpos
    · exact ⟨1, by simpa using hε⟩
    · rcases eq_or_lt_of_le hC with rfl | hCpos
      · exact ⟨0, by simpa using hε⟩
      · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hCpos) hq1
        exact ⟨N, by rwa [← lt_div_iff₀' hCpos]⟩
  refine ⟨N, fun n hn => lt_of_le_of_lt (hd n) (lt_of_le_of_lt ?_ hN)⟩
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1.le hn) hC

/-- Teorema condicional: fidelidade + acoplamento + estabilidade ⇒ todos os
enunciados.  As três hipóteses são exatamente as obrigações abertas. -/
theorem certificacao_condicional (C : ι → Prop) (A : ι → ι → ℝ) (hA : ∀ i j, 0 ≤ A i j)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hq : RowSumLe A q)
    (δ : ℕ → ι → ℝ) (hpos : ∀ n, Nonneg (δ n))
    (hstep : ∀ n, Acopla A (δ n) (δ (n + 1)))
    (fidelidade : ∀ i, Vanishes (fun n => δ n i) → C i) :
    ∀ i, C i := by
  intro i
  apply fidelidade i
  apply vanishes_of_geometric hq0 hq1 (fun n => hpos n i)
  intro n
  have := contraction A hA hq0 hq δ hpos hstep n
  have h2 := (le_abs_self _).trans (le_normInf (δ n) i)
  linarith

end ATK.OmegaContracao

#print axioms ATK.OmegaContracao.le_normInf
#print axioms ATK.OmegaContracao.normInf_nonneg
#print axioms ATK.OmegaContracao.normInf_le
#print axioms ATK.OmegaContracao.step_bound
#print axioms ATK.OmegaContracao.contraction
#print axioms ATK.OmegaContracao.contraction_perturbed
#print axioms ATK.OmegaContracao.block_reduction
#print axioms ATK.OmegaContracao.uma_coordenada_nao_basta
#print axioms ATK.OmegaContracao.vanishes_of_geometric
#print axioms ATK.OmegaContracao.certificacao_condicional
