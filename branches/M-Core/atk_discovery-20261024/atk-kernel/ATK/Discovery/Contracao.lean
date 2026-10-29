import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# ATK-Discovery — Defeitos: contração acumulada, a cota `5/(2(N+1))` e as precisões `10⁻ᵐ`

Resultados sobre uma sequência abstrata de defeitos `D : ℕ → ℝ` (nenhuma hipótese sobre RH):

* **contração acumulada** (`tende_zero_de_contracao`): se `D_{n+1} ≤ (1 − αₙ) D_n` com `0 ≤ αₙ ≤ 1` e
  `Σ αₙ = ∞`, então `D_n → 0`, via `D_N ≤ D_0 · exp(−Σ_{n<N} αₙ)` (`cota_exp`). Generaliza a forma usada
  para a sequência genuína em `ATK.CapturaRH.le_exp`.
* **a cota condicional do texto** (`cota_cinco_meios`): se `D₂ = 5/6` e `D_{n+1} ≤ ((n+1)/(n+2)) D_n`
  para `n ≥ 2` (isto é, o ganho `g_n ≥ D_n/(n+2)`), então `D_N ≤ 5/(2(N+1))` para `N ≥ 2`, e `D_N → 0`
  (`tende_zero_cinco_meios`). A hipótese de ganho **não** está provada para o defeito de Riemann.
* **valor inicial e monotonia não determinam o limite** (`mesmo_inicio_limites_distintos`):
  `A_N = 5/(2(N+1))` e `B_N = 1/2 + 1/(N+1)` são decrescentes, valem `5/6` em `N = 2`, e convergem para
  `0` e `1/2`.
* **as precisões** (`tende_zero_iff_precisoes`): para `D` decrescente e `≥ 0`,
  `D_N → 0 ⟺ ∀ m, ∃ N, D_N < 10⁻ᵐ` — "acumular zeros" é exatamente o limite zero.
-/

namespace ATK.Discovery.Contracao

open Filter Topology Finset

/-- `D_N ≤ D_0 · exp(−Σ_{n<N} αₙ)` sob `D_{n+1} ≤ (1 − αₙ) D_n`, `D ≥ 0`, `αₙ ≤ 1`. -/
theorem cota_exp {D α : ℕ → ℝ} (hD : ∀ n, 0 ≤ D n) (hα1 : ∀ n, α n ≤ 1)
    (hrec : ∀ n, D (n + 1) ≤ (1 - α n) * D n) (N : ℕ) :
    D N ≤ D 0 * Real.exp (-∑ n ∈ range N, α n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h1 : 1 - α N ≤ Real.exp (-α N) := by
      have := Real.add_one_le_exp (-α N); linarith
    have h0 : 0 ≤ 1 - α N := by linarith [hα1 N]
    calc D (N + 1) ≤ (1 - α N) * D N := hrec N
      _ ≤ Real.exp (-α N) * D N := mul_le_mul_of_nonneg_right h1 (hD N)
      _ ≤ Real.exp (-α N) * (D 0 * Real.exp (-∑ n ∈ range N, α n)) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = D 0 * Real.exp (-∑ n ∈ range (N + 1), α n) := by
          rw [sum_range_succ, neg_add, Real.exp_add]; ring

/-- **Contração acumulada**: `Σ αₙ = ∞` força `D_n → 0`. -/
theorem tende_zero_de_contracao {D α : ℕ → ℝ} (hD : ∀ n, 0 ≤ D n) (hα1 : ∀ n, α n ≤ 1)
    (hrec : ∀ n, D (n + 1) ≤ (1 - α n) * D n)
    (hdiv : Tendsto (fun N => ∑ n ∈ range N, α n) atTop atTop) :
    Tendsto D atTop (𝓝 0) := by
  have hexp : Tendsto (fun N => D 0 * Real.exp (-∑ n ∈ range N, α n)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hdiv)).const_mul (D 0)
    simpa using this
  exact squeeze_zero hD (cota_exp hD hα1 hrec) hexp

/-- **A cota condicional `5/(2(N+1))`**: de `D₂ = 5/6` e `D_{n+1} ≤ ((n+1)/(n+2)) D_n` para `n ≥ 2`. -/
theorem cota_cinco_meios {D : ℕ → ℝ} (h2 : D 2 = 5 / 6)
    (hrec : ∀ n ≥ 2, D (n + 1) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2) * D n) :
    ∀ N ≥ 2, D N ≤ 5 / (2 * ((N : ℝ) + 1)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rw [h2]; norm_num
  | succ n hn ih =>
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hq : 0 ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2) := by positivity
    calc D (n + 1) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2) * D n := hrec n hn
      _ ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2) * (5 / (2 * ((n : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left ih hq
      _ = 5 / (2 * (((n + 1 : ℕ) : ℝ) + 1)) := by
          push_cast; field_simp; ring

/-- Sob as mesmas hipóteses (e `D ≥ 0`), `D_N → 0`. -/
theorem tende_zero_cinco_meios {D : ℕ → ℝ} (hD : ∀ n, 0 ≤ D n) (h2 : D 2 = 5 / 6)
    (hrec : ∀ n ≥ 2, D (n + 1) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2) * D n) :
    Tendsto D atTop (𝓝 0) := by
  have hcota := cota_cinco_meios h2 hrec
  have hlim : Tendsto (fun N : ℕ => 5 / (2 * ((N : ℝ) + 1))) atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (5 / 2 : ℝ)
    rw [mul_zero] at h
    refine h.congr fun N => ?_
    field_simp
  refine squeeze_zero' (Eventually.of_forall hD) ?_ hlim
  filter_upwards [eventually_ge_atTop 2] with N hN using hcota N hN

/-- **Valor inicial e monotonia não determinam o limite.** -/
theorem mesmo_inicio_limites_distintos :
    let A : ℕ → ℝ := fun N => 5 / (2 * ((N : ℝ) + 1))
    let B : ℕ → ℝ := fun N => 1 / 2 + 1 / ((N : ℝ) + 1)
    A 2 = 5 / 6 ∧ B 2 = 5 / 6 ∧ Antitone A ∧ Antitone B ∧
      Tendsto A atTop (𝓝 0) ∧ Tendsto B atTop (𝓝 (1 / 2)) := by
  intro A B
  have hinv : Antitone fun N : ℕ => 1 / ((N : ℝ) + 1) := by
    intro m n hmn
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  refine ⟨by norm_num [A], by norm_num [B], ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    simp only [A]
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
  · intro m n hmn
    simp only [B]
    linarith [hinv hmn]
  · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (5 / 2 : ℝ)
    rw [mul_zero] at h
    refine h.congr fun N => ?_
    simp only [A]; field_simp
  · have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_add (1 / 2 : ℝ)
    rw [add_zero] at h
    exact h

/-- **As precisões**: para `D` decrescente e `≥ 0`, `D_N → 0 ⟺ ∀ m, ∃ N, D_N < 10⁻ᵐ`. -/
theorem tende_zero_iff_precisoes {D : ℕ → ℝ} (hanti : Antitone D) (hD : ∀ n, 0 ≤ D n) :
    Tendsto D atTop (𝓝 0) ↔ ∀ m : ℕ, ∃ N, D N < ((1 : ℝ) / 10) ^ m := by
  constructor
  · intro h m
    have hpos : (0 : ℝ) < ((1 : ℝ) / 10) ^ m := by positivity
    obtain ⟨N, hN⟩ := (h.eventually (gt_mem_nhds hpos)).exists_forall_of_atTop
    exact ⟨N, hN N le_rfl⟩
  · intro h
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (by norm_num : ((1 : ℝ) / 10) < 1)
    obtain ⟨N, hN⟩ := h m
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hD n)]
    exact lt_of_le_of_lt (hanti hn) (hN.trans hm)

end ATK.Discovery.Contracao

#print axioms ATK.Discovery.Contracao.cota_exp
#print axioms ATK.Discovery.Contracao.tende_zero_de_contracao
#print axioms ATK.Discovery.Contracao.cota_cinco_meios
#print axioms ATK.Discovery.Contracao.tende_zero_cinco_meios
#print axioms ATK.Discovery.Contracao.mesmo_inicio_limites_distintos
#print axioms ATK.Discovery.Contracao.tende_zero_iff_precisoes
