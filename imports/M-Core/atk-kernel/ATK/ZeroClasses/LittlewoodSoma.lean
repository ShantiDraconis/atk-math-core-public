import ATK.ZeroClasses.LittlewoodBase
import ATK.ZeroClasses.RiemannVonMangoldt
import ATK.ZeroClasses.Expoente

/-!
# Littlewood, parte 2: a soma sobre os zeros sob RH (rodada 91)

Segunda parte de Littlewood `ψ(x) − x = Ω±(√x log log log x)`: as estimativas da soma sobre os zeros na
fórmula gaussiana (rodadas 89–90) sob RH, com `τ = A/T²` e `u = n ± 1/T`, onde `n` alinha os zeros com
`|γ| ≤ 3T` (aproximação simultânea de Dirichlet).

* §1 massa: `massa_le` (`Σ_{|γ| ≤ k+7} m_ρ ≤ 4(k + 1)(a₀ + log(k + 9))/l₀`, das janelas `soma_faixa_le`),
  `massa_le_real`, `N_le_massa`, `card_le_massa`, `soma_inv_sq_le` (`Σ m_ρ/|ρ|² ≤ C₀` uniforme).
* §2 `cauda_le`: `Σ_{3T < |γ| ≤ T′} m_ρ e^{−Aγ²/T²}/|ρ| ≤ 3(a₀ + log 5T)e^{−4A}/l₀` (`T, A ≥ 1`), por fibras
  `⌊|γ|⌋ = n`, caixas de Jensen e soma geométrica.
* §3 o modelo alinhado `D(v) = Σ_{|γ| ≤ 3T} m_ρ e^{−τγ²} γ sen(γv)/|ρ|²`:
  `D_ge` (sem hipóteses) `D(1/T) ≥ e^{−A}/(πT) Σ_{|γ| ≤ T} m_ρ`; `decomp` (sob RH): se `|nγ − 2πk_ρ| ≤ ε`
  para `|γ| ≤ 3T`, então `|Σ_{|γ| ≤ T′} m_ρ Re(W_{n+v}(ρ)/ρ) − D(v)| ≤ C₀/2 + ε Σ_{|γ| ≤ 3T} m_ρ/|ρ| + cauda`.
* §4 `massa_ge` (`Σ_{|γ| ≤ T} m_ρ ≥ T log T/(4π)` para `T` grande, Riemann–von Mangoldt) e **`soma_forcada`**:
  com `A₀ = 1 + log(24π²/l₀)` e `c = e^{−A₀}/(8π²)`, para `T` grande,
  `Σ m_ρ Re(W_{n+1/T}(ρ)/ρ) ≥ c log T − C₁ − ε Σ m_ρ/|ρ|` e `Σ m_ρ Re(W_{n−1/T}(ρ)/ρ) ≤ −c log T + C₁ + ε Σ m_ρ/|ρ|`.
* §5 `dirichlet_Q`: `n₀ ≤ n ≤ n₀Q^{|A|}` com `‖n a_i‖ < 1/Q`; `alinha`: `|nγ − 2πk_ρ| ≤ 2π/Q` para `|γ| ≤ 3T`.

Classificação: **ferramenta**. O teorema de Littlewood continua BUILD_PENDING: falta a montagem (o resto
`e^{−u/2}`, `E = O(e^{−3u})` com constante explícita em `τ`, a localização da rodada 90 com `u ≤ n₀Q^K + 1`,
`log log u ≍ log T`, e o caso `¬RH` pela rodada 87).
-/

open Complex Set Filter Topology
open scoped Real

namespace ATK.ZeroClasses.LittlewoodSoma

open ATK.ZeroClasses.ExplicitaGauss (Wg pw)
open ATK.ZeroClasses.ExplicitaT (Zfin mem_Zfin)
open ATK.ZeroClasses.SomaZeros (a0 l0)
open ATK.ZeroClasses.JensenLocal (Lc)

/-! ## 1. Massa dos zeros -/

theorem mem_Z_of_Zfin {T : ℝ} {ρ : ℂ} (h : ρ ∈ Zfin T) : ρ ∈ ATK.ZetaSimetria.Z ∧ |ρ.im| ≤ T := by
  rw [mem_Zfin] at h
  exact ⟨⟨h.1, h.2.1, ATK.ZeroClasses.ExplicitaT.re_lt_one h.1⟩, h.2.2⟩

theorem Zfin_mono {T T' : ℝ} (h : T ≤ T') : Zfin T ⊆ Zfin T' := by
  intro ρ hρ
  rw [mem_Zfin] at hρ ⊢
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.trans h⟩

theorem Zfin_vazio {T : ℝ} (hT : T ≤ 13) : Zfin T = ∅ := by
  ext ρ
  simp only [Finset.notMem_empty, iff_false]
  intro h
  obtain ⟨hZ, hle⟩ := mem_Z_of_Zfin h
  have := ATK.ZeroClasses.Faixa.zeros_acima_13 ρ hZ
  linarith

/-- **`Σ_{|γ| ≤ k + 7} m_ρ ≤ 4(k + 1)(a₀ + log(k + 9))/l₀`**: as janelas unitárias de `soma_faixa_le` somadas. -/
theorem massa_le (k : ℕ) : ∑ ρ ∈ Zfin ((k : ℝ) + 7), (analyticOrderNatAt riemannZeta ρ : ℝ) ≤
    4 * ((k : ℝ) + 1) * ((a0 + Real.log ((k : ℝ) + 9)) / l0) := by
  have hl0 := ATK.ZeroClasses.SomaZeros.l0_pos
  have ha0 := ATK.ZeroClasses.SomaZeros.one_le_a0
  induction k with
  | zero =>
    have h := ATK.ZeroClasses.ExplicitaT.soma_faixa_le 0
    rw [Zfin_vazio (by norm_num : ((0 : ℕ) : ℝ) + 6 ≤ 13), Finset.sdiff_empty] at h
    simpa using h
  | succ k ih =>
    have h := ATK.ZeroClasses.ExplicitaT.soma_faixa_le (k + 1)
    have e7 : ((k + 1 : ℕ) : ℝ) + 7 = ((k : ℝ) + 7) + 1 := by push_cast; ring
    have e6 : ((k + 1 : ℕ) : ℝ) + 6 = (k : ℝ) + 7 := by push_cast; ring
    rw [e6] at h
    have hsub : Zfin ((k : ℝ) + 7) ⊆ Zfin ((k + 1 : ℕ) + 7 : ℝ) := Zfin_mono (by push_cast; linarith)
    rw [← Finset.sum_sdiff hsub]
    have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
    have hlog : Real.log ((k : ℝ) + 9) ≤ Real.log (((k + 1 : ℕ) : ℝ) + 9) :=
      Real.log_le_log (by linarith) (by push_cast; linarith)
    have hlog0 : 0 ≤ Real.log ((k : ℝ) + 9) := Real.log_nonneg (by linarith)
    have h1 : 4 * ((k : ℝ) + 1) * ((a0 + Real.log ((k : ℝ) + 9)) / l0) ≤
        4 * ((k : ℝ) + 1) * ((a0 + Real.log (((k + 1 : ℕ) : ℝ) + 9)) / l0) := by
      gcongr
    have e : 4 * (((k + 1 : ℕ) : ℝ) + 1) * ((a0 + Real.log (((k + 1 : ℕ) : ℝ) + 9)) / l0) =
        4 * ((a0 + Real.log (((k + 1 : ℕ) : ℝ) + 9)) / l0) +
          4 * ((k : ℝ) + 1) * ((a0 + Real.log (((k + 1 : ℕ) : ℝ) + 9)) / l0) := by
      push_cast; ring
    rw [e]
    linarith

/-- **`Σ_{|γ| ≤ X} m_ρ ≤ 4X(a₀ + log(X + 3))/l₀`** para `X ≥ 7`. -/
theorem massa_le_real {X : ℝ} (hX : 7 ≤ X) : ∑ ρ ∈ Zfin X, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤
    4 * X * ((a0 + Real.log (X + 3)) / l0) := by
  have hl0 := ATK.ZeroClasses.SomaZeros.l0_pos
  have ha0 := ATK.ZeroClasses.SomaZeros.one_le_a0
  set k : ℕ := ⌈X⌉₊ - 7 with hk
  have hc1 := Nat.le_ceil X
  have hc2 := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ X)
  have h7 : 7 ≤ ⌈X⌉₊ := by exact_mod_cast (show (7 : ℝ) ≤ ⌈X⌉₊ from hX.trans hc1)
  have hkX : (k : ℝ) = (⌈X⌉₊ : ℝ) - 7 := by
    rw [hk, Nat.cast_sub h7]; norm_num
  have hsub : Zfin X ⊆ Zfin ((k : ℝ) + 7) := Zfin_mono (by rw [hkX]; linarith)
  have hm : ∀ ρ ∈ Zfin ((k : ℝ) + 7), (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) :=
    fun _ _ => Nat.cast_nonneg _
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ρ h _ => hm ρ h)).trans ((massa_le k).trans ?_)
  have hlog : Real.log ((k : ℝ) + 9) ≤ Real.log (X + 3) :=
    Real.log_le_log (by positivity) (by rw [hkX]; linarith)
  have hlog0 : 0 ≤ Real.log ((k : ℝ) + 9) := Real.log_nonneg (by have := k.cast_nonneg (α := ℝ); linarith)
  have hk1 : (k : ℝ) + 1 ≤ X := by rw [hkX]; linarith
  have hk0 : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  calc 4 * ((k : ℝ) + 1) * ((a0 + Real.log ((k : ℝ) + 9)) / l0)
      ≤ 4 * X * ((a0 + Real.log (X + 3)) / l0) := by
        gcongr

/-- O número de zeros distintos é `≤` a massa. -/
theorem card_le_massa (S : Finset ℂ) (hS : ∀ ρ ∈ S, ρ ∈ ATK.ZetaSimetria.Z) :
    (S.card : ℝ) ≤ ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have := ATK.ZeroClasses.Expoente.ordem_pos (hS ρ hρ)
  push_cast
  exact_mod_cast this

/-- `N(T) ≤ Σ_{|γ| ≤ T} m_ρ`. -/
theorem N_le_massa (T : ℝ) : (ATK.FechamentoO1.N T : ℝ) ≤ ∑ ρ ∈ Zfin T, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
  unfold ATK.FechamentoO1.N
  push_cast
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => ?_) (fun _ _ _ => Nat.cast_nonneg _)
  rw [Set.Finite.mem_toFinset] at hρ
  obtain ⟨hZ, h0, hT⟩ := hρ
  rw [mem_Zfin]
  exact ⟨hZ.1, hZ.2.1, by rw [abs_of_pos h0]; exact hT⟩

/-- **`Σ_{ρ ∈ S} m_ρ/|ρ|² ≤ C₀`** uniformemente nos conjuntos finitos de zeros da faixa. -/
theorem soma_inv_sq_le : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ S : Finset ℂ, (∀ ρ ∈ S, ρ ∈ ATK.ZetaSimetria.Z) →
    ∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ 2 ≤ C₀ := by
  classical
  have hs := ATK.ZeroClasses.JensenLocal.soma_ordem_inv_quadrado
  refine ⟨∑' ρ : ATK.ZetaSimetria.Z, (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2,
    tsum_nonneg fun ρ => by positivity, fun S hS => ?_⟩
  rw [← Finset.sum_subtype_of_mem (fun ρ : ℂ => (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ 2) hS]
  exact hs.sum_le_tsum _ (fun i _ => by positivity)

/-! ## 2. A cauda gaussiana `|γ| > 3T` -/

/-- Para `n ≥ 2T > 0`: `(a₀ + log(n + 5/2))/n ≤ (a₀ + log(2T + 3))/(2T)`. -/
theorem log_razao_le {T n : ℝ} (hT : 0 < T) (hn : 2 * T ≤ n) :
    (a0 + Real.log (n + 5 / 2)) / n ≤ (a0 + Real.log (2 * T + 3)) / (2 * T) := by
  have ha0 := ATK.ZeroClasses.SomaZeros.one_le_a0
  have hn0 : 0 < n := by linarith
  have h1 : Real.log (n + 5 / 2) - Real.log (2 * T + 3) ≤ n / (2 * T) - 1 := by
    rw [← Real.log_div (by linarith) (by linarith)]
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    have : (n + 5 / 2) / (2 * T + 3) ≤ n / (2 * T) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    linarith
  have hl : 0 ≤ Real.log (2 * T + 3) := Real.log_nonneg (by linarith)
  rw [div_le_div_iff₀ hn0 (by linarith)]
  have h2 : Real.log (n + 5 / 2) * (2 * T) ≤ (Real.log (2 * T + 3) + n / (2 * T) - 1) * (2 * T) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have e : (Real.log (2 * T + 3) + n / (2 * T) - 1) * (2 * T) = Real.log (2 * T + 3) * (2 * T) + n - 2 * T := by
    field_simp
  rw [e] at h2
  nlinarith [mul_nonneg (show 0 ≤ a0 + Real.log (2 * T + 3) - 1 by linarith) (show 0 ≤ n - 2 * T by linarith)]

theorem geom_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (s : Finset ℕ) (m₀ : ℕ) (hs : ∀ n ∈ s, m₀ ≤ n) :
    ∑ n ∈ s, r ^ n ≤ r ^ m₀ / (1 - r) := by
  have hsub : s ⊆ Finset.Ico m₀ (s.sup id + 1) := by
    intro n hn
    rw [Finset.mem_Ico]
    exact ⟨hs n hn, Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)⟩
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => pow_nonneg h0 _)).trans
    (geom_sum_Ico_le_of_lt_one h0 h1)

theorem inv_um_menos_exp {x : ℝ} (hx : 0 < x) : 1 / (1 - Real.exp (-x)) ≤ 1 + 1 / x := by
  have h1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h2 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have h3 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
  have h4 : x / (1 + x) ≤ 1 - Real.exp (-x) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-x)).le]
  rw [div_le_iff₀ (by linarith)]
  have e : (1 + 1 / x) * (x / (1 + x)) = 1 := by
    field_simp
    ring
  calc (1 : ℝ) = (1 + 1 / x) * (x / (1 + x)) := e.symm
    _ ≤ (1 + 1 / x) * (1 - Real.exp (-x)) := by gcongr

/-- **A cauda gaussiana**: para `T ≥ 1`, `A ≥ 1` e `τ = A/T²`,
`Σ_{3T < |γ| ≤ T′} m_ρ e^{−τγ²}/|ρ| ≤ 3(a₀ + log 5T)e^{−4A}/l₀`, uniformemente em `T′`. -/
theorem cauda_le {T A : ℝ} (hT : 1 ≤ T) (hA : 1 ≤ A) (T' : ℝ) :
    ∑ ρ ∈ Zfin T' \ Zfin (3 * T), (analyticOrderNatAt riemannZeta ρ : ℝ) *
      Real.exp (-(A / T ^ 2 * ρ.im ^ 2)) / ‖ρ‖ ≤
      3 * ((a0 + Real.log (5 * T)) / l0) * Real.exp (-(4 * A)) := by
  classical
  have hl0 := ATK.ZeroClasses.SomaZeros.l0_pos
  have ha0 := ATK.ZeroClasses.SomaZeros.one_le_a0
  have hT0 : 0 < T := by linarith
  set S₂ := Zfin T' \ Zfin (3 * T) with hS₂
  have hmem : ∀ ρ ∈ S₂, ρ ∈ ATK.ZetaSimetria.Z ∧ 3 * T < |ρ.im| := by
    intro ρ hρ
    rw [hS₂, Finset.mem_sdiff] at hρ
    obtain ⟨hZ, _⟩ := mem_Z_of_Zfin hρ.1
    refine ⟨hZ, ?_⟩
    by_contra h
    exact hρ.2 (by rw [mem_Zfin]; exact ⟨hZ.1, hZ.2.1, not_lt.mp h⟩)
  set f : ℂ → ℝ := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) *
    Real.exp (-(A / T ^ 2 * ρ.im ^ 2)) / ‖ρ‖ with hf
  set κ : ℂ → ℕ := fun ρ => ⌊|ρ.im|⌋₊ with hκ
  set r := Real.exp (-(2 * A / T)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hAT : 0 < 2 * A / T := by positivity
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  set c := 4 / l0 * ((a0 + Real.log (2 * T + 3)) / (2 * T)) with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ Real.log (2 * T + 3) := Real.log_nonneg (by linarith)
    exact mul_nonneg (div_nonneg (by norm_num) hl0.le) (div_nonneg (by linarith) (by linarith))
  have hfib : ∀ n ∈ S₂.image κ, (∑ ρ ∈ S₂.filter (fun ρ => κ ρ = n), f ρ) ≤ c * r ^ n ∧ ⌈2 * T⌉₊ ≤ n := by
    intro n hn
    obtain ⟨ρ₀, hρ₀, hκ₀⟩ := Finset.mem_image.mp hn
    obtain ⟨hZ₀, h3₀⟩ := hmem ρ₀ hρ₀
    have hlt₀ : |ρ₀.im| < (n : ℝ) + 1 := hκ₀ ▸ Nat.lt_floor_add_one |ρ₀.im|
    have hn2 : 2 * T ≤ (n : ℝ) := by linarith
    have h13 : 13 ≤ n := by
      rw [← hκ₀]
      exact Nat.le_floor (by have := ATK.ZeroClasses.Faixa.zeros_acima_13 ρ₀ hZ₀; push_cast; linarith)
    have hn13 : (13 : ℝ) ≤ n := by exact_mod_cast h13
    refine ⟨?_, Nat.ceil_le.mpr hn2⟩
    set W := S₂.filter (fun ρ => κ ρ = n) with hW
    have hWm : ∀ ρ ∈ W, ρ ∈ ATK.ZetaSimetria.Z ∧ (n : ℝ) ≤ |ρ.im| ∧ |ρ.im| < (n : ℝ) + 1 := by
      intro ρ hρ
      rw [hW, Finset.mem_filter] at hρ
      refine ⟨(hmem ρ hρ.1).1, ?_, ?_⟩
      · rw [← hρ.2]; exact Nat.floor_le (abs_nonneg _)
      · rw [← hρ.2]; exact Nat.lt_floor_add_one _
    -- a massa da fibra
    have hy : 4 ≤ |(n : ℝ) + 1 / 2| := by rw [abs_of_pos (by linarith)]; linarith
    have hy' : 4 ≤ |-((n : ℝ) + 1 / 2)| := by rwa [abs_neg]
    have hmais := ATK.ZeroClasses.JensenLocal.caixa_le hy (W.filter (fun ρ => 0 < ρ.im)) (fun ρ hρ => by
      rw [Finset.mem_filter] at hρ
      obtain ⟨hz, h1, h2⟩ := hWm ρ hρ.1
      rw [abs_of_pos hρ.2] at h1 h2
      exact ⟨hz.2.1, hz.2.2, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
    have hmenos := ATK.ZeroClasses.JensenLocal.caixa_le hy' (W.filter (fun ρ => ¬ 0 < ρ.im)) (fun ρ hρ => by
      rw [Finset.mem_filter] at hρ
      obtain ⟨hz, h1, h2⟩ := hWm ρ hρ.1
      rw [abs_of_nonpos (not_lt.mp hρ.2)] at h1 h2
      exact ⟨hz.2.1, hz.2.2, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
    rw [abs_neg, abs_of_pos (by linarith : (0 : ℝ) < (n : ℝ) + 1 / 2)] at hmenos
    rw [abs_of_pos (by linarith : (0 : ℝ) < (n : ℝ) + 1 / 2)] at hmais
    have hLc := ATK.ZeroClasses.SomaZeros.Lc_le (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1 / 2)
    have hmassa : ∑ ρ ∈ W, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤
        4 * ((a0 + Real.log ((n : ℝ) + 5 / 2)) / l0) := by
      rw [← Finset.sum_filter_add_sum_filter_not W (fun ρ : ℂ => 0 < ρ.im)]
      have e : (2 : ℝ) + ((n : ℝ) + 1 / 2) = (n : ℝ) + 5 / 2 := by ring
      rw [e] at hLc
      linarith
    -- o peso na fibra
    set e := Real.exp (-(A / T ^ 2 * (n : ℝ) ^ 2)) / n with he
    have hpt : ∀ ρ ∈ W, f ρ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * e := by
      intro ρ hρ
      obtain ⟨_, h1, _⟩ := hWm ρ hρ
      have hn0 : (0 : ℝ) < n := by linarith
      have hsq : (n : ℝ) ^ 2 ≤ ρ.im ^ 2 := by
        rw [← sq_abs ρ.im]
        exact pow_le_pow_left₀ hn0.le h1 2
      have hex : Real.exp (-(A / T ^ 2 * ρ.im ^ 2)) ≤ Real.exp (-(A / T ^ 2 * (n : ℝ) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        have : 0 ≤ A / T ^ 2 := by positivity
        nlinarith
      have hnr : (n : ℝ) ≤ ‖ρ‖ := h1.trans (Complex.abs_im_le_norm ρ)
      simp only [hf, he]
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact div_le_div₀ (Real.exp_pos _).le hex hn0 hnr
    have he0 : 0 ≤ e := by positivity
    have hexp : Real.exp (-(A / T ^ 2 * (n : ℝ) ^ 2)) ≤ r ^ n := by
      rw [hr, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have : A / T ^ 2 * (n : ℝ) ^ 2 - (n : ℝ) * (2 * A / T) = A * n / T ^ 2 * ((n : ℝ) - 2 * T) := by
        field_simp
      have : 0 ≤ A * n / T ^ 2 * ((n : ℝ) - 2 * T) :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith
    have hraz := log_razao_le hT0 hn2
    calc ∑ ρ ∈ W, f ρ ≤ ∑ ρ ∈ W, (analyticOrderNatAt riemannZeta ρ : ℝ) * e := Finset.sum_le_sum hpt
      _ = e * ∑ ρ ∈ W, (analyticOrderNatAt riemannZeta ρ : ℝ) := by rw [Finset.mul_sum]; simp [mul_comm]
      _ ≤ e * (4 * ((a0 + Real.log ((n : ℝ) + 5 / 2)) / l0)) := mul_le_mul_of_nonneg_left hmassa he0
      _ = 4 / l0 * ((a0 + Real.log ((n : ℝ) + 5 / 2)) / n) * Real.exp (-(A / T ^ 2 * (n : ℝ) ^ 2)) := by
        rw [he]; ring
      _ ≤ 4 / l0 * ((a0 + Real.log (2 * T + 3)) / (2 * T)) * r ^ n := by
        have : 0 ≤ (a0 + Real.log ((n : ℝ) + 5 / 2)) / n := by
          have : 0 ≤ Real.log ((n : ℝ) + 5 / 2) := Real.log_nonneg (by linarith)
          have : (0 : ℝ) < n := by linarith
          positivity
        gcongr
      _ = c * r ^ n := by rw [hc]
  rw [← Finset.sum_fiberwise_of_maps_to (fun ρ hρ => Finset.mem_image_of_mem κ hρ)]
  have hgeo := geom_le hr0 hr1 (S₂.image κ) ⌈2 * T⌉₊ (fun n hn => (hfib n hn).2)
  have hpow : r ^ ⌈2 * T⌉₊ ≤ Real.exp (-(4 * A)) := by
    rw [hr, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have h1 : 2 * T ≤ (⌈2 * T⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 * T⌉₊ : ℝ) * (-(2 * A / T)) ≤ 2 * T * (-(2 * A / T)) :=
      mul_le_mul_of_nonpos_right h1 (by linarith)
    have e : 2 * T * (-(2 * A / T)) = -(4 * A) := by field_simp; ring
    linarith
  have hinv : 1 / (1 - r) ≤ 1 + T / (2 * A) := by
    have := inv_um_menos_exp hAT
    rw [hr]
    convert this using 2
    field_simp
  have h1r : 0 < 1 - r := by linarith
  have hlog : Real.log (2 * T + 3) ≤ Real.log (5 * T) := Real.log_le_log (by linarith) (by linarith)
  have hl0' : 0 ≤ Real.log (2 * T + 3) := Real.log_nonneg (by linarith)
  calc ∑ n ∈ S₂.image κ, ∑ ρ ∈ S₂.filter (fun ρ => κ ρ = n), f ρ
      ≤ ∑ n ∈ S₂.image κ, c * r ^ n := Finset.sum_le_sum fun n hn => (hfib n hn).1
    _ = c * ∑ n ∈ S₂.image κ, r ^ n := by rw [Finset.mul_sum]
    _ ≤ c * (r ^ ⌈2 * T⌉₊ / (1 - r)) := mul_le_mul_of_nonneg_left hgeo hc0
    _ = c * r ^ ⌈2 * T⌉₊ * (1 / (1 - r)) := by ring
    _ ≤ c * Real.exp (-(4 * A)) * (1 + T / (2 * A)) := by
        gcongr
    _ = 4 / l0 * (a0 + Real.log (2 * T + 3)) * Real.exp (-(4 * A)) * (1 / (2 * T) + 1 / (4 * A)) := by
        rw [hc]; field_simp; ring
    _ ≤ 4 / l0 * (a0 + Real.log (5 * T)) * Real.exp (-(4 * A)) * (3 / 4) := by
        have h1 : 1 / (2 * T) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
        have h2 : 1 / (4 * A) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
        have hX : 0 ≤ 4 / l0 * (a0 + Real.log (2 * T + 3)) * Real.exp (-(4 * A)) :=
          mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hl0.le) (by linarith)) (Real.exp_pos _).le
        calc 4 / l0 * (a0 + Real.log (2 * T + 3)) * Real.exp (-(4 * A)) * (1 / (2 * T) + 1 / (4 * A))
            ≤ 4 / l0 * (a0 + Real.log (2 * T + 3)) * Real.exp (-(4 * A)) * (3 / 4) :=
              mul_le_mul_of_nonneg_left (by linarith) hX
          _ ≤ 4 / l0 * (a0 + Real.log (5 * T)) * Real.exp (-(4 * A)) * (3 / 4) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
                (by linarith) (div_nonneg (by norm_num) hl0.le)) (Real.exp_pos _).le) (by norm_num)
    _ = 3 * ((a0 + Real.log (5 * T)) / l0) * Real.exp (-(4 * A)) := by ring

/-! ## 3. O modelo alinhado e a decomposição sob RH -/

/-- O termo `m_ρ e^{−τγ²} γ sen(γw)/|ρ|²`. -/
noncomputable def termo (τ w : ℝ) (ρ : ℂ) : ℝ := (analyticOrderNatAt riemannZeta ρ : ℝ) *
  Real.exp (-(τ * ρ.im ^ 2)) * (ρ.im * Real.sin (ρ.im * w)) / ‖ρ‖ ^ 2

/-- O modelo alinhado `D(v) = Σ_{|γ| ≤ 3T} m_ρ e^{−τγ²} γ sen(γv)/|ρ|²`, `τ = A/T²`. -/
noncomputable def D (T A v : ℝ) : ℝ := ∑ ρ ∈ Zfin (3 * T), termo (A / T ^ 2) v ρ

theorem D_neg (T A v : ℝ) : D T A (-v) = -D T A v := by
  unfold D termo
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [mul_neg, Real.sin_neg]
  ring

theorem mul_sin_abs (γ v : ℝ) : γ * Real.sin (γ * v) = |γ| * Real.sin (|γ| * v) := by
  rcases le_or_gt 0 γ with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, neg_mul, neg_mul, Real.sin_neg]
    ring

theorem norm_pos_Z {ρ : ℂ} (hρ : ρ ∈ ATK.ZetaSimetria.Z) : 0 < ‖ρ‖ := by
  have h13 := ATK.ZeroClasses.Faixa.zeros_acima_13 ρ hρ
  linarith [Complex.abs_im_le_norm ρ]

/-- `|ρ|² ≤ 2γ²` para os zeros da faixa. -/
theorem norm_sq_le {ρ : ℂ} (hρ : ρ ∈ ATK.ZetaSimetria.Z) : ‖ρ‖ ^ 2 ≤ 2 * ρ.im ^ 2 := by
  have h13 := ATK.ZeroClasses.Faixa.zeros_acima_13 ρ hρ
  rw [Complex.sq_norm, Complex.normSq_apply]
  have h0 := hρ.2.1
  have h1 := hρ.2.2
  have : 169 ≤ ρ.im ^ 2 := by
    rw [← sq_abs]
    nlinarith
  nlinarith

theorem abs_div_sq_le {ρ : ℂ} (hρ : ρ ∈ ATK.ZetaSimetria.Z) : |ρ.im| / ‖ρ‖ ^ 2 ≤ 1 / ‖ρ‖ := by
  have hn := norm_pos_Z hρ
  rw [div_le_div_iff₀ (by positivity) hn]
  have := Complex.abs_im_le_norm ρ
  nlinarith

/-- **O termo principal** (sem hipóteses): para `T ≥ 1` e `A ≥ 0`,
`D(1/T) ≥ e^{−A}/(πT) · Σ_{|γ| ≤ T} m_ρ`. Os termos com `T < |γ| ≤ 3T` são `≥ 0` (`|γ|/T ≤ 3 < π`). -/
theorem D_ge {T A : ℝ} (hT : 1 ≤ T) (hA : 0 ≤ A) :
    Real.exp (-A) / (π * T) * ∑ ρ ∈ Zfin T, (analyticOrderNatAt riemannZeta ρ : ℝ) ≤ D T A (1 / T) := by
  have hT0 : 0 < T := by linarith
  have hsub : Zfin T ⊆ Zfin (3 * T) := Zfin_mono (by linarith)
  unfold D
  rw [← Finset.sum_sdiff hsub, Finset.mul_sum]
  have hg0 : ∀ ρ ∈ Zfin (3 * T), 0 ≤ termo (A / T ^ 2) (1 / T) ρ := by
    intro ρ hρ
    obtain ⟨hZ, hle⟩ := mem_Z_of_Zfin hρ
    unfold termo
    rw [mul_sin_abs]
    have : 0 ≤ Real.sin (|ρ.im| * (1 / T)) := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi (by positivity)
      calc |ρ.im| * (1 / T) ≤ 3 * T * (1 / T) := by gcongr
        _ = 3 := by field_simp
        _ ≤ π := by linarith [Real.pi_gt_three]
    positivity
  have h1 : 0 ≤ ∑ ρ ∈ Zfin (3 * T) \ Zfin T, termo (A / T ^ 2) (1 / T) ρ :=
    Finset.sum_nonneg fun ρ hρ => hg0 ρ (Finset.mem_sdiff.mp hρ).1
  have h2 : ∑ ρ ∈ Zfin T, Real.exp (-A) / (π * T) * (analyticOrderNatAt riemannZeta ρ : ℝ) ≤
      ∑ ρ ∈ Zfin T, termo (A / T ^ 2) (1 / T) ρ := by
    refine Finset.sum_le_sum fun ρ hρ => ?_
    obtain ⟨hZ, hle⟩ := mem_Z_of_Zfin hρ
    have hn := norm_pos_Z hZ
    have hsq := norm_sq_le hZ
    have hx0 : 0 ≤ |ρ.im| * (1 / T) := by positivity
    have hx1 : |ρ.im| * (1 / T) ≤ π / 2 := by
      calc |ρ.im| * (1 / T) ≤ T * (1 / T) := by gcongr
        _ = 1 := by field_simp
        _ ≤ π / 2 := by linarith [Real.pi_gt_three]
    have hs := Real.mul_le_sin hx0 hx1
    have hq : 1 / (π * T) ≤ |ρ.im| * Real.sin (|ρ.im| * (1 / T)) / ‖ρ‖ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have e : 2 * ρ.im ^ 2 = |ρ.im| * (2 / π * (|ρ.im| * (1 / T))) * (π * T) := by
        rw [← sq_abs ρ.im]
        field_simp
      calc 1 * ‖ρ‖ ^ 2 ≤ 2 * ρ.im ^ 2 := by linarith
        _ = |ρ.im| * (2 / π * (|ρ.im| * (1 / T))) * (π * T) := e
        _ ≤ |ρ.im| * Real.sin (|ρ.im| * (1 / T)) * (π * T) := by gcongr
    have hexp : Real.exp (-A) ≤ Real.exp (-(A / T ^ 2 * ρ.im ^ 2)) := by
      apply Real.exp_le_exp.mpr
      have : ρ.im ^ 2 ≤ T ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hle 2
      have : A / T ^ 2 * ρ.im ^ 2 ≤ A := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    unfold termo
    rw [mul_sin_abs, mul_div_assoc]
    have hm : (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := Nat.cast_nonneg _
    calc Real.exp (-A) / (π * T) * (analyticOrderNatAt riemannZeta ρ : ℝ)
        = (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.exp (-A) * (1 / (π * T)) := by ring
      _ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.exp (-(A / T ^ 2 * ρ.im ^ 2)) *
          (|ρ.im| * Real.sin (|ρ.im| * (1 / T)) / ‖ρ‖ ^ 2) := by
        gcongr
  linarith

/-- O erro de alinhamento num termo: se `|nγ − 2πk| ≤ ε` então
`|termo(n + v) − termo(v)| ≤ ε m_ρ/|ρ|`. -/
theorem termo_alinha {ρ : ℂ} (hZ : ρ ∈ ATK.ZetaSimetria.Z) {τ : ℝ} (hτ : 0 ≤ τ) {n v ε : ℝ} {k : ℤ}
    (hk : |n * ρ.im - 2 * π * k| ≤ ε) :
    |termo τ (n + v) ρ - termo τ v ρ| ≤ ε * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) := by
  have hn := norm_pos_Z hZ
  have hm : (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := Nat.cast_nonneg _
  have hs : |Real.sin (ρ.im * (n + v)) - Real.sin (ρ.im * v)| ≤ ε := by
    have e : ρ.im * (n + v) = (ρ.im * v + (n * ρ.im - 2 * π * k)) + k * (2 * π) := by ring
    rw [e, Real.sin_add_int_mul_two_pi]
    refine (Real.abs_sin_sub_sin_le _ _).trans ?_
    rw [add_sub_cancel_left]
    exact hk
  have he1 : Real.exp (-(τ * ρ.im ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he0 : 0 ≤ Real.exp (-(τ * ρ.im ^ 2)) := (Real.exp_pos _).le
  unfold termo
  have e : (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.exp (-(τ * ρ.im ^ 2)) *
      (ρ.im * Real.sin (ρ.im * (n + v))) / ‖ρ‖ ^ 2 -
      (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.exp (-(τ * ρ.im ^ 2)) *
      (ρ.im * Real.sin (ρ.im * v)) / ‖ρ‖ ^ 2 =
      (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.exp (-(τ * ρ.im ^ 2)) *
      (ρ.im / ‖ρ‖ ^ 2) * (Real.sin (ρ.im * (n + v)) - Real.sin (ρ.im * v)) := by
    field_simp
  rw [e, abs_mul, abs_mul, abs_mul, abs_of_nonneg hm, abs_of_nonneg he0, abs_div,
    abs_of_pos (by positivity : 0 < ‖ρ‖ ^ 2)]
  have hq := abs_div_sq_le hZ
  calc (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.exp (-(τ * ρ.im ^ 2)) * (|ρ.im| / ‖ρ‖ ^ 2) *
        |Real.sin (ρ.im * (n + v)) - Real.sin (ρ.im * v)|
      ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * 1 * (1 / ‖ρ‖) * ε := by gcongr
    _ = ε * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) := by ring

theorem abs_termo_le {ρ : ℂ} (hZ : ρ ∈ ATK.ZetaSimetria.Z) (τ w : ℝ) :
    |termo τ w ρ| ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.exp (-(τ * ρ.im ^ 2)) / ‖ρ‖ := by
  have hn := norm_pos_Z hZ
  have hm : (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := Nat.cast_nonneg _
  unfold termo
  rw [mul_div_assoc, abs_mul, abs_mul, abs_of_nonneg hm, abs_of_pos (Real.exp_pos _), abs_div,
    abs_of_pos (by positivity : 0 < ‖ρ‖ ^ 2), abs_mul, mul_div_assoc]
  have hq := abs_div_sq_le hZ
  have hs := Real.abs_sin_le_one (ρ.im * w)
  calc (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.exp (-(τ * ρ.im ^ 2)) *
        (|ρ.im| * (|Real.sin (ρ.im * w)| / ‖ρ‖ ^ 2))
      = (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.exp (-(τ * ρ.im ^ 2)) *
        (|ρ.im| / ‖ρ‖ ^ 2 * |Real.sin (ρ.im * w)|) := by ring
    _ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.exp (-(τ * ρ.im ^ 2)) * (1 / ‖ρ‖ * 1) := by gcongr
    _ = (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.exp (-(τ * ρ.im ^ 2)) / ‖ρ‖ := by ring

/-- **A decomposição sob RH**: se `n` alinha os zeros com `|γ| ≤ 3T` a menos de `ε`
(`|nγ − 2πk_ρ| ≤ ε`), então para todo `T′ ≥ 3T`

  `|Σ_{|γ| ≤ T′} m_ρ Re(W(ρ)/ρ) − D(v)| ≤ C₀/2 + ε Σ_{|γ| ≤ 3T} m_ρ/|ρ| + 3(a₀ + log 5T)e^{−4A}/l₀`,

com `W = W_{n+v, A/T²}`; `C₀` é a soma `Σ m_ρ/|ρ|²` (`soma_inv_sq_le`). -/
theorem decomp (hRH : RiemannHypothesis) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {T A n v ε T' : ℝ}, 1 ≤ T → 1 ≤ A →
    3 * T ≤ T' → (∀ ρ ∈ Zfin (3 * T), ∃ k : ℤ, |n * ρ.im - 2 * π * k| ≤ ε) →
    |∑ ρ ∈ Zfin T', (analyticOrderNatAt riemannZeta ρ : ℝ) * (pw (Wg (n + v) (A / T ^ 2)) ρ).re - D T A v| ≤
      C₀ / 2 + ε * ∑ ρ ∈ Zfin (3 * T), (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ +
        3 * ((a0 + Real.log (5 * T)) / l0) * Real.exp (-(4 * A)) := by
  obtain ⟨C₀, hC₀, hC⟩ := soma_inv_sq_le
  refine ⟨C₀, hC₀, fun {T A n v ε T'} hT hA hT' hal => ?_⟩
  have hT0 : 0 < T := by linarith
  set τ := A / T ^ 2 with hτ
  have hτ0 : 0 ≤ τ := by positivity
  set a : ℂ → ℝ := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.exp (-(τ * ρ.im ^ 2)) *
    (Real.cos (ρ.im * (n + v)) / 2) / ‖ρ‖ ^ 2 with ha
  have hsplit : ∀ ρ ∈ Zfin T', (analyticOrderNatAt riemannZeta ρ : ℝ) * (pw (Wg (n + v) τ) ρ).re =
      a ρ + termo τ (n + v) ρ := by
    intro ρ hρ
    rw [ATK.ZeroClasses.LittlewoodBase.re_pw_RH
      (ATK.ZeroClasses.LagariasHadamard.re_de_RH hRH (mem_Z_of_Zfin hρ).1) (n + v) τ]
    simp only [ha, termo]
    ring
  have hsub : Zfin (3 * T) ⊆ Zfin T' := Zfin_mono hT'
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    ← Finset.sum_sdiff hsub (f := fun ρ => termo τ (n + v) ρ)]
  -- as três partes
  have hA1 : |∑ ρ ∈ Zfin T', a ρ| ≤ C₀ / 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h := hC (Zfin T') (fun ρ hρ => (mem_Z_of_Zfin hρ).1)
    rw [div_eq_mul_one_div C₀ 2]
    refine le_trans (Finset.sum_le_sum fun ρ hρ => ?_) (le_trans (le_of_eq (Finset.sum_mul ..).symm)
      (mul_le_mul_of_nonneg_right h (by norm_num)))
    have hn := norm_pos_Z (mem_Z_of_Zfin hρ).1
    have hm : (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := Nat.cast_nonneg _
    have he1 : Real.exp (-(τ * ρ.im ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hc := Real.abs_cos_le_one (ρ.im * (n + v))
    simp only [ha]
    rw [abs_div, abs_mul, abs_mul, abs_div, abs_of_nonneg hm, abs_of_pos (Real.exp_pos _),
      abs_of_pos (by positivity : 0 < ‖ρ‖ ^ 2), abs_two]
    calc (analyticOrderNatAt riemannZeta ρ : ℝ) * Real.exp (-(τ * ρ.im ^ 2)) * (|Real.cos (ρ.im * (n + v))| / 2) /
          ‖ρ‖ ^ 2 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * 1 * (1 / 2) / ‖ρ‖ ^ 2 := by gcongr
      _ = (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ 2 * (1 / 2) := by ring
  have hB1 : |∑ ρ ∈ Zfin (3 * T), termo τ (n + v) ρ - D T A v| ≤
      ε * ∑ ρ ∈ Zfin (3 * T), (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
    unfold D
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
    obtain ⟨k, hk⟩ := hal ρ hρ
    exact termo_alinha (mem_Z_of_Zfin hρ).1 hτ0 hk
  have hC1 : |∑ ρ ∈ Zfin T' \ Zfin (3 * T), termo τ (n + v) ρ| ≤
      3 * ((a0 + Real.log (5 * T)) / l0) * Real.exp (-(4 * A)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun ρ hρ => ?_).trans (cauda_le hT hA T'))
    exact abs_termo_le (mem_Z_of_Zfin (Finset.mem_sdiff.mp hρ).1).1 τ (n + v)
  have e : ∑ ρ ∈ Zfin T', a ρ + (∑ ρ ∈ Zfin T' \ Zfin (3 * T), termo τ (n + v) ρ +
      ∑ ρ ∈ Zfin (3 * T), termo τ (n + v) ρ) - D T A v =
      ∑ ρ ∈ Zfin T', a ρ + ∑ ρ ∈ Zfin T' \ Zfin (3 * T), termo τ (n + v) ρ +
      (∑ ρ ∈ Zfin (3 * T), termo τ (n + v) ρ - D T A v) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have := (abs_add_le (∑ ρ ∈ Zfin T', a ρ) (∑ ρ ∈ Zfin T' \ Zfin (3 * T), termo τ (n + v) ρ))
  linarith

/-! ## 4. O termo principal via Riemann–von Mangoldt, e a soma forçada -/

/-- **`Σ_{|γ| ≤ T} m_ρ ≥ T log T/(4π)`** para `T` grande (Riemann–von Mangoldt, rodada 42). -/
theorem massa_ge : ∀ᶠ T in atTop, T * Real.log T / (4 * π) ≤
    ∑ ρ ∈ Zfin T, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
  obtain ⟨C, hC⟩ := ATK.ZeroClasses.RvM.riemannVonMangoldt
  have hpi := Real.pi_pos
  have hlo := (Real.isLittleO_log_id_atTop).bound (show (0 : ℝ) < 1 / (4 * π * (|C| + 1)) by positivity)
  filter_upwards [hlo, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * (Real.log (2 * π) + 1) + 1)] with T h1 h2 h3
  have hT0 : 0 < T := by linarith
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0, id, abs_of_pos hT0] at h1
  have hN := (abs_le.mp (hC T h2)).1
  have hNm := N_le_massa T
  have hlogd : Real.log (T / (2 * π)) = Real.log T - Real.log (2 * π) :=
    Real.log_div hT0.ne' (by positivity)
  rw [hlogd] at hN
  have hCl : C * Real.log T ≤ T / (4 * π) := by
    calc C * Real.log T ≤ |C| * Real.log T := mul_le_mul_of_nonneg_right (le_abs_self C) hlog0
      _ ≤ |C| * (1 / (4 * π * (|C| + 1)) * T) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
      _ ≤ T / (4 * π) := by
        rw [show |C| * (1 / (4 * π * (|C| + 1)) * T) = T / (4 * π) * (|C| / (|C| + 1)) by
          field_simp]
        have : |C| / (|C| + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith
        calc T / (4 * π) * (|C| / (|C| + 1)) ≤ T / (4 * π) * 1 := by gcongr
          _ = T / (4 * π) := by ring
  have key : T * Real.log T / (4 * π) ≤ T / (2 * π) * (Real.log T - Real.log (2 * π)) - T / (2 * π) -
      C * Real.log T := by
    have e : T / (2 * π) * (Real.log T - Real.log (2 * π)) - T / (2 * π) - T * Real.log T / (4 * π) =
        T / (4 * π) * (Real.log T - 2 * (Real.log (2 * π) + 1)) := by
      field_simp
      ring
    have : T / (4 * π) ≤ T / (4 * π) * (Real.log T - 2 * (Real.log (2 * π) + 1)) := by
      have h0 : 0 ≤ T / (4 * π) := by positivity
      nlinarith
    linarith
  linarith

/-- A escolha `A = 1 + log(24π²/l₀)`: `A ≥ 1` e `e^{−A} ≤ l₀/(24π²)`. -/
noncomputable def A₀ : ℝ := 1 + Real.log (24 * π ^ 2 / l0)

theorem um_le_A₀ : 1 ≤ A₀ := by
  have hl0 := ATK.ZeroClasses.SomaZeros.l0_pos
  have hl1 : l0 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 19 / 16)
    unfold ATK.ZeroClasses.SomaZeros.l0
    linarith
  have : 1 ≤ 24 * π ^ 2 / l0 := by
    rw [le_div_iff₀ hl0]
    nlinarith [Real.pi_gt_three]
  unfold A₀
  linarith [Real.log_nonneg this]

theorem exp_A₀_le : Real.exp (-A₀) ≤ l0 / (24 * π ^ 2) := by
  have hl0 := ATK.ZeroClasses.SomaZeros.l0_pos
  unfold A₀
  rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (by positivity), inv_div]
  have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have h0 : 0 ≤ l0 / (24 * π ^ 2) := by positivity
  nlinarith

/-- **A soma sobre os zeros forçada pelo alinhamento** (sob RH). Com `A = A₀`, `c = e^{−A}/(8π²)` e uma
constante `C₁`, para `T` grande, todo `n` que alinha os zeros com `|γ| ≤ 3T` a menos de `ε` e todo `T′ ≥ 3T`:

  `Σ_{|γ| ≤ T′} m_ρ Re(W_{n + 1/T}(ρ)/ρ) ≥ c log T − C₁ − ε Σ_{|γ| ≤ 3T} m_ρ/|ρ|`,
  `Σ_{|γ| ≤ T′} m_ρ Re(W_{n − 1/T}(ρ)/ρ) ≤ −c log T + C₁ + ε Σ_{|γ| ≤ 3T} m_ρ/|ρ|`,

com `W_u = W_{u, A/T²}`. -/
theorem soma_forcada (hRH : RiemannHypothesis) : ∃ c C₁ : ℝ, 0 < c ∧ ∀ᶠ T in atTop,
    ∀ n ε T' : ℝ, 3 * T ≤ T' → (∀ ρ ∈ Zfin (3 * T), ∃ k : ℤ, |n * ρ.im - 2 * π * k| ≤ ε) →
      c * Real.log T - C₁ - ε * ∑ ρ ∈ Zfin (3 * T), (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ≤
        ∑ ρ ∈ Zfin T', (analyticOrderNatAt riemannZeta ρ : ℝ) * (pw (Wg (n + 1 / T) (A₀ / T ^ 2)) ρ).re ∧
      ∑ ρ ∈ Zfin T', (analyticOrderNatAt riemannZeta ρ : ℝ) * (pw (Wg (n - 1 / T) (A₀ / T ^ 2)) ρ).re ≤
        -(c * Real.log T) + C₁ + ε * ∑ ρ ∈ Zfin (3 * T), (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ := by
  obtain ⟨C₀, hC₀, hdec⟩ := decomp hRH
  have hl0 := ATK.ZeroClasses.SomaZeros.l0_pos
  have hpi := Real.pi_pos
  have hA := um_le_A₀
  have hEA := exp_A₀_le
  refine ⟨Real.exp (-A₀) / (8 * π ^ 2), C₀ / 2 + Real.exp (-A₀) * (a0 + Real.log 5) / (8 * π ^ 2),
    by positivity, ?_⟩
  filter_upwards [massa_ge, eventually_ge_atTop (1 : ℝ)] with T hM hT n ε T' hT' hal
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  -- o termo principal
  have hD : Real.exp (-A₀) * Real.log T / (4 * π ^ 2) ≤ D T A₀ (1 / T) := by
    refine le_trans ?_ (D_ge hT (by linarith))
    calc Real.exp (-A₀) * Real.log T / (4 * π ^ 2) = Real.exp (-A₀) / (π * T) * (T * Real.log T / (4 * π)) := by
          field_simp
      _ ≤ Real.exp (-A₀) / (π * T) * ∑ ρ ∈ Zfin T, (analyticOrderNatAt riemannZeta ρ : ℝ) := by gcongr
  -- a cauda
  have hcauda : 3 * ((a0 + Real.log (5 * T)) / l0) * Real.exp (-(4 * A₀)) ≤
      Real.exp (-A₀) * (a0 + Real.log 5) / (8 * π ^ 2) + Real.exp (-A₀) / (8 * π ^ 2) * Real.log T := by
    have h4 : Real.exp (-(4 * A₀)) ≤ Real.exp (-A₀) * Real.exp (-A₀) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have h5 : 3 / l0 * Real.exp (-(4 * A₀)) ≤ Real.exp (-A₀) / (8 * π ^ 2) := by
      calc 3 / l0 * Real.exp (-(4 * A₀)) ≤ 3 / l0 * (Real.exp (-A₀) * Real.exp (-A₀)) := by gcongr
        _ ≤ 3 / l0 * (Real.exp (-A₀) * (l0 / (24 * π ^ 2))) := by gcongr
        _ = Real.exp (-A₀) / (8 * π ^ 2) := by field_simp; ring
    have hlog5 : Real.log (5 * T) = Real.log 5 + Real.log T := Real.log_mul (by norm_num) hT0.ne'
    have ha0 : 0 ≤ a0 + Real.log (5 * T) := by
      have := ATK.ZeroClasses.SomaZeros.one_le_a0
      have : 0 ≤ Real.log (5 * T) := Real.log_nonneg (by linarith)
      linarith
    calc 3 * ((a0 + Real.log (5 * T)) / l0) * Real.exp (-(4 * A₀))
        = (a0 + Real.log (5 * T)) * (3 / l0 * Real.exp (-(4 * A₀))) := by ring
      _ ≤ (a0 + Real.log (5 * T)) * (Real.exp (-A₀) / (8 * π ^ 2)) := by gcongr
      _ = Real.exp (-A₀) * (a0 + Real.log 5) / (8 * π ^ 2) + Real.exp (-A₀) / (8 * π ^ 2) * Real.log T := by
        rw [hlog5]; ring
  have hmeio : Real.exp (-A₀) * Real.log T / (4 * π ^ 2) =
      2 * (Real.exp (-A₀) / (8 * π ^ 2) * Real.log T) := by
    field_simp; ring
  constructor
  · have h := abs_le.mp (hdec (v := 1 / T) hT hA hT' hal)
    linarith [h.1]
  · have h := abs_le.mp (hdec (v := -(1 / T)) hT hA hT' hal)
    rw [D_neg, ← sub_eq_add_neg] at h
    linarith [h.2]

/-! ## 5. Dirichlet simultâneo com cota explícita -/

theorem fract_proximo_Q {Q : ℕ} (hQ : 1 ≤ Q) {y₁ y₂ : ℝ}
    (h : ⌊(Q : ℝ) * Int.fract y₁⌋₊ = ⌊(Q : ℝ) * Int.fract y₂⌋₊) :
    |Int.fract y₂ - Int.fract y₁| < 1 / Q := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have a1 := Nat.floor_le (by have := Int.fract_nonneg y₁; positivity : (0 : ℝ) ≤ Q * Int.fract y₁)
  have a2 := Nat.lt_floor_add_one ((Q : ℝ) * Int.fract y₁)
  have b1 := Nat.floor_le (by have := Int.fract_nonneg y₂; positivity : (0 : ℝ) ≤ Q * Int.fract y₂)
  have b2 := Nat.lt_floor_add_one ((Q : ℝ) * Int.fract y₂)
  rw [h] at a1 a2
  have : |(Q : ℝ) * (Int.fract y₂ - Int.fract y₁)| < 1 := by
    rw [abs_lt]
    constructor <;> nlinarith
  rw [abs_mul, abs_of_pos hQ0] at this
  rw [lt_div_iff₀ hQ0]
  linarith

theorem floor_lt_Q {Q : ℕ} (hQ : 1 ≤ Q) (y : ℝ) : ⌊(Q : ℝ) * Int.fract y⌋₊ < Q := by
  have h := Int.fract_lt_one y
  have h0 := Int.fract_nonneg y
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [Nat.floor_lt (by positivity)]
  nlinarith

/-- **Dirichlet simultâneo com cota**: para `n₀, Q ≥ 1` e `a_i` (`i ∈ A` finito) há `n` com
`n₀ ≤ n ≤ n₀ Q^{|A|}` e `‖n a_i‖ < 1/Q` para todo `i ∈ A`. -/
theorem dirichlet_Q {ι : Type*} (A : Finset ι) (a : ι → ℝ) {n₀ Q : ℕ} (_hn₀ : 1 ≤ n₀) (hQ : 1 ≤ Q) :
    ∃ n : ℕ, n₀ ≤ n ∧ n ≤ n₀ * Q ^ A.card ∧ ∀ i ∈ A, ∃ m : ℤ, |(n : ℝ) * a i - m| < 1 / Q := by
  classical
  set k := A.card with hk
  let f : Fin (Q ^ k + 1) → (A → Fin Q) := fun j i =>
    ⟨⌊(Q : ℝ) * Int.fract ((j : ℕ) * n₀ * a i)⌋₊, floor_lt_Q hQ _⟩
  have hcard : Fintype.card (A → Fin Q) < Fintype.card (Fin (Q ^ k + 1)) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_coe, ← hk]
    omega
  obtain ⟨j₁, j₂, hne, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have key : ∀ i₁ i₂ : Fin (Q ^ k + 1), f i₁ = f i₂ → (i₁ : ℕ) < i₂ →
      ∃ n : ℕ, n₀ ≤ n ∧ n ≤ n₀ * Q ^ k ∧ ∀ i ∈ A, ∃ m : ℤ, |(n : ℝ) * a i - m| < 1 / Q := by
    intro i₁ i₂ hf hlt
    refine ⟨((i₂ : ℕ) - i₁) * n₀, ?_, ?_, fun i hi => ?_⟩
    · have : 1 ≤ (i₂ : ℕ) - i₁ := by omega
      nlinarith
    · have h2 : (i₂ : ℕ) ≤ Q ^ k := Nat.lt_succ_iff.mp i₂.2
      have : (i₂ : ℕ) - i₁ ≤ Q ^ k := (Nat.sub_le _ _).trans h2
      calc ((i₂ : ℕ) - i₁) * n₀ ≤ Q ^ k * n₀ := Nat.mul_le_mul_right _ this
        _ = n₀ * Q ^ k := Nat.mul_comm _ _
    · have hq' := congrFun hf ⟨i, hi⟩
      simp only [f, Fin.mk.injEq] at hq'
      have hp := fract_proximo_Q hQ hq'
      set y₁ := ((i₁ : ℕ) : ℝ) * n₀ * a i with hy₁
      set y₂ := ((i₂ : ℕ) : ℝ) * n₀ * a i with hy₂
      refine ⟨⌊y₂⌋ - ⌊y₁⌋, ?_⟩
      have e : ((((i₂ : ℕ) - i₁) * n₀ : ℕ) : ℝ) * a i - ((⌊y₂⌋ - ⌊y₁⌋ : ℤ) : ℝ) =
          Int.fract y₂ - Int.fract y₁ := by
        rw [Nat.cast_mul, Nat.cast_sub hlt.le, Int.fract, Int.fract, hy₁, hy₂]
        push_cast
        ring
      rw [e]
      exact hp
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with h | h
  · exact key j₁ j₂ hfeq h
  · exact key j₂ j₁ hfeq.symm h

/-- **O alinhamento dos zeros**: para `n₀, Q ≥ 1` há `n ∈ [n₀, n₀ Q^K]`, `K = #{ρ : |γ| ≤ 3T}`, com
`|nγ − 2πk_ρ| < 2π/Q` para todo zero com `|γ| ≤ 3T`. -/
theorem alinha (T : ℝ) {n₀ Q : ℕ} (hn₀ : 1 ≤ n₀) (hQ : 1 ≤ Q) :
    ∃ n : ℕ, n₀ ≤ n ∧ n ≤ n₀ * Q ^ (Zfin (3 * T)).card ∧
      ∀ ρ ∈ Zfin (3 * T), ∃ k : ℤ, |(n : ℝ) * ρ.im - 2 * π * k| ≤ 2 * π / Q := by
  obtain ⟨n, h1, h2, h3⟩ := dirichlet_Q (Zfin (3 * T)) (fun ρ => ρ.im / (2 * π)) hn₀ hQ
  refine ⟨n, h1, h2, fun ρ hρ => ?_⟩
  obtain ⟨k, hk⟩ := h3 ρ hρ
  refine ⟨k, ?_⟩
  have hpi := Real.pi_pos
  have e : (n : ℝ) * ρ.im - 2 * π * k = 2 * π * ((n : ℝ) * (ρ.im / (2 * π)) - k) := by
    field_simp
  rw [e, abs_mul, abs_of_pos (by positivity)]
  have : 2 * π * |(n : ℝ) * (ρ.im / (2 * π)) - k| ≤ 2 * π * (1 / Q) :=
    mul_le_mul_of_nonneg_left hk.le (by positivity)
  calc 2 * π * |(n : ℝ) * (ρ.im / (2 * π)) - k| ≤ 2 * π * (1 / Q) := this
    _ = 2 * π / Q := by ring

end ATK.ZeroClasses.LittlewoodSoma

#print axioms ATK.ZeroClasses.LittlewoodSoma.mem_Z_of_Zfin
#print axioms ATK.ZeroClasses.LittlewoodSoma.Zfin_mono
#print axioms ATK.ZeroClasses.LittlewoodSoma.Zfin_vazio
#print axioms ATK.ZeroClasses.LittlewoodSoma.massa_le
#print axioms ATK.ZeroClasses.LittlewoodSoma.massa_le_real
#print axioms ATK.ZeroClasses.LittlewoodSoma.card_le_massa
#print axioms ATK.ZeroClasses.LittlewoodSoma.N_le_massa
#print axioms ATK.ZeroClasses.LittlewoodSoma.soma_inv_sq_le
#print axioms ATK.ZeroClasses.LittlewoodSoma.log_razao_le
#print axioms ATK.ZeroClasses.LittlewoodSoma.geom_le
#print axioms ATK.ZeroClasses.LittlewoodSoma.inv_um_menos_exp
#print axioms ATK.ZeroClasses.LittlewoodSoma.cauda_le
#print axioms ATK.ZeroClasses.LittlewoodSoma.D_neg
#print axioms ATK.ZeroClasses.LittlewoodSoma.mul_sin_abs
#print axioms ATK.ZeroClasses.LittlewoodSoma.norm_pos_Z
#print axioms ATK.ZeroClasses.LittlewoodSoma.norm_sq_le
#print axioms ATK.ZeroClasses.LittlewoodSoma.abs_div_sq_le
#print axioms ATK.ZeroClasses.LittlewoodSoma.D_ge
#print axioms ATK.ZeroClasses.LittlewoodSoma.termo_alinha
#print axioms ATK.ZeroClasses.LittlewoodSoma.abs_termo_le
#print axioms ATK.ZeroClasses.LittlewoodSoma.decomp
#print axioms ATK.ZeroClasses.LittlewoodSoma.massa_ge
#print axioms ATK.ZeroClasses.LittlewoodSoma.um_le_A₀
#print axioms ATK.ZeroClasses.LittlewoodSoma.exp_A₀_le
#print axioms ATK.ZeroClasses.LittlewoodSoma.soma_forcada
#print axioms ATK.ZeroClasses.LittlewoodSoma.fract_proximo_Q
#print axioms ATK.ZeroClasses.LittlewoodSoma.floor_lt_Q
#print axioms ATK.ZeroClasses.LittlewoodSoma.dirichlet_Q
#print axioms ATK.ZeroClasses.LittlewoodSoma.alinha
