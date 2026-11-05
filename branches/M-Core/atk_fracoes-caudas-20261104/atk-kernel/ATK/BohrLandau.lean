import ATK.EixoDeslocado
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# ATK-RH — O teorema de aproximação em 1/2 (Bohr–Landau, 1914)

**Enunciado clássico.** Para todo `δ > 0`, o número `N(1/2 + δ, T)` de zeros não triviais com
`Re ρ > 1/2 + δ` e `0 < Im ρ ≤ T` é `O(T)`. Como o número total `N(T)` cresce como
`(T/2π) log T` (Riemann–von Mangoldt), a proporção de zeros com `|Re ρ − 1/2| > δ` tende a zero:
**quase todos os zeros estão arbitrariamente perto de 1/2**. Isso é "aproximadamente 1/2" para quase
todos; RH é "exatamente 1/2" para todos.

O que este arquivo faz, sem `sorry` e sem axiomas novos:

* contagens fiéis: `direita σ T`, `esquerda σ T`, `todos T` são conjuntos **finitos**
  (`todos_finite`, pela discreção dos zeros na Mathlib: `IsCompact.inter_riemannZetaZeros_finite`),
  então `ncard` conta de verdade;
* `torcao_direita`, `simetria_contagem`: `N(1/2 + δ, T)` à direita = contagem à esquerda de `1/2 − δ`
  (a reflexão `ρ ↦ 1 − ρ̄` preserva a altura);
* **`TeoremaBohrLandau`** (o enunciado `O(T)`) e **`Densidade`** (a proporção fora de `|Re − 1/2| ≤ δ` → 0);
* `rh_bohrLandau`, `rh_densidade`: RH implica os dois (o teorema é mais fraco que RH);
* **`densidade_de_bohrLandau`**: `TeoremaBohrLandau` + crescimento de `N(T)/T → ∞` ⇒ `Densidade`.

**O que falta para provar `TeoremaBohrLandau` incondicionalmente** (literatura: Titchmarsh §9.15):
(i) a média quadrática `∫_1^T |ζ(σ + it)|² dt = O(T)` para `σ > 1/2` (não está na Mathlib);
(ii) o lema de contagem de Littlewood, ou Jensen em discos (Jensen **está** na Mathlib:
`MeromorphicOn.circleAverage_log_norm`); (iii) para `Densidade`, o lado inferior de
Riemann–von Mangoldt (`CrescimentoN`, nem a infinitude dos zeros está na Mathlib). Ficam como
obrigações B9 e B10, publicadas e não formalizadas.
-/

open Set Filter Topology

namespace ATK.BohrLandau

open ATK.ZetaSimetria ATK.ForaDaLinha ATK.EixoDeslocado

/-- Zeros não triviais à direita de `σ`, com `0 < Im ρ ≤ T`. -/
def direita (σ T : ℝ) : Set ℂ := {ρ | ρ ∈ Z ∧ σ < ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- Zeros não triviais à esquerda de `σ`, com `0 < Im ρ ≤ T`. -/
def esquerda (σ T : ℝ) : Set ℂ := {ρ | ρ ∈ Z ∧ ρ.re < σ ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- Todos os zeros não triviais com `0 < Im ρ ≤ T`. -/
def todos (T : ℝ) : Set ℂ := {ρ | ρ ∈ Z ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- Há só finitos zeros não triviais até a altura `T`. -/
theorem todos_finite (T : ℝ) : (todos T).Finite := by
  refine ((isCompact_closedBall (0 : ℂ) (1 + |T|)).inter_riemannZetaZeros_finite).subset ?_
  rintro ρ ⟨⟨hz, h0, h1⟩, hi0, hiT⟩
  refine ⟨?_, hz⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have := Complex.norm_le_abs_re_add_abs_im ρ
  have hr : |ρ.re| ≤ 1 := by rw [abs_of_pos h0]; linarith
  have hi : |ρ.im| ≤ |T| := by
    rw [abs_of_pos hi0]; exact hiT.trans (le_abs_self T)
  linarith

theorem direita_subset (σ T : ℝ) : direita σ T ⊆ todos T :=
  fun _ ⟨h, _, h2, h3⟩ => ⟨h, h2, h3⟩

theorem esquerda_subset (σ T : ℝ) : esquerda σ T ⊆ todos T :=
  fun _ ⟨h, _, h2, h3⟩ => ⟨h, h2, h3⟩

theorem torcao_torcao (s : ℂ) : torcao (torcao s) = s := by
  unfold torcao; simp

theorem torcao_injective : Function.Injective torcao :=
  fun a b h => by rw [← torcao_torcao a, h, torcao_torcao]

/-- A reflexão leva os zeros à direita de `σ` exatamente nos zeros à esquerda de `1 − σ`. -/
theorem torcao_direita (σ T : ℝ) : torcao '' direita σ T = esquerda (1 - σ) T := by
  ext ρ
  constructor
  · rintro ⟨r, ⟨hr, hσ, h0, hT⟩, rfl⟩
    refine ⟨torcao_mem_Z hr, ?_, ?_, ?_⟩
    · rw [re_torcao]; linarith
    · rw [im_torcao]; exact h0
    · rw [im_torcao]; exact hT
  · rintro ⟨hr, hσ, h0, hT⟩
    refine ⟨torcao ρ, ⟨torcao_mem_Z hr, ?_, ?_, ?_⟩, torcao_torcao ρ⟩
    · rw [re_torcao]; linarith
    · rw [im_torcao]; exact h0
    · rw [im_torcao]; exact hT

/-- **Simetria das contagens**: tantos zeros à direita de `1/2 + δ` quanto à esquerda de `1/2 − δ`. -/
theorem simetria_contagem (δ T : ℝ) :
    (direita (1 / 2 + δ) T).ncard = (esquerda (1 / 2 - δ) T).ncard := by
  have h := torcao_direita (1 / 2 + δ) T
  rw [show 1 - (1 / 2 + δ) = 1 / 2 - δ by ring] at h
  rw [← h, Set.ncard_image_of_injective _ torcao_injective]

/-- **Bohr–Landau (1914)**: `N(1/2 + δ, T) = O(T)` para todo `δ > 0`. -/
def TeoremaBohrLandau : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → ((direita (1 / 2 + δ) T).ncard : ℝ) ≤ C * T

/-- **Aproximação em 1/2**: a proporção dos zeros com `|Re ρ − 1/2| > δ` tende a zero. -/
def Densidade : Prop :=
  ∀ δ : ℝ, 0 < δ → Tendsto (fun T : ℝ =>
    (((direita (1 / 2 + δ) T).ncard : ℝ) + (esquerda (1 / 2 - δ) T).ncard) / (todos T).ncard)
    atTop (𝓝 0)

/-- Lado inferior de Riemann–von Mangoldt, na forma fraca `N(T)/T → ∞`. -/
def CrescimentoN : Prop := Tendsto (fun T : ℝ => ((todos T).ncard : ℝ) / T) atTop atTop

theorem direita_vazia_de_rh (h : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    direita (1 / 2 + δ) T = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun ρ hm => ?_
  obtain ⟨hρ, hre, -, -⟩ := hm
  rw [re_de_rh h hρ] at hre; linarith

theorem esquerda_vazia_de_rh (h : RiemannHypothesis) {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    esquerda (1 / 2 - δ) T = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun ρ hm => ?_
  obtain ⟨hρ, hre, -, -⟩ := hm
  rw [re_de_rh h hρ] at hre; linarith

/-- RH implica Bohr–Landau (com `C = 0`): o teorema de aproximação é mais fraco que RH. -/
theorem rh_bohrLandau (h : RiemannHypothesis) : TeoremaBohrLandau :=
  fun δ hδ => ⟨0, fun T _ => by rw [direita_vazia_de_rh h hδ T]; simp⟩

/-- RH implica a densidade (a proporção é identicamente zero). -/
theorem rh_densidade (h : RiemannHypothesis) : Densidade := by
  intro δ hδ
  have : (fun T : ℝ => (((direita (1 / 2 + δ) T).ncard : ℝ) + (esquerda (1 / 2 - δ) T).ncard) /
      (todos T).ncard) = fun _ => 0 := by
    funext T; rw [direita_vazia_de_rh h hδ T, esquerda_vazia_de_rh h hδ T]; simp
  rw [this]; exact tendsto_const_nhds

/-- **Bohr–Landau + crescimento de `N(T)` ⇒ aproximação em 1/2.** -/
theorem densidade_de_bohrLandau (hBL : TeoremaBohrLandau) (hN : CrescimentoN) : Densidade := by
  intro δ hδ
  obtain ⟨C, hC⟩ := hBL δ hδ
  set K : ℝ := 2 * |C|
  have hlim : Tendsto (fun T : ℝ => K / (((todos T).ncard : ℝ) / T)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hN
  have hev : ∀ᶠ T : ℝ in atTop, 2 ≤ T ∧ 1 ≤ ((todos T).ncard : ℝ) / T :=
    (eventually_ge_atTop 2).and (hN.eventually_ge_atTop 1)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards with T
    positivity
  · filter_upwards [hev] with T ⟨hT, hr⟩
    have hT0 : (0 : ℝ) < T := by linarith
    have hn : (0 : ℝ) < (todos T).ncard := by
      have := (one_le_div hT0).mp hr; linarith
    have hs : ((esquerda (1 / 2 - δ) T).ncard : ℝ) = (direita (1 / 2 + δ) T).ncard := by
      rw [simetria_contagem]
    have hd := hC T hT
    have hdC : ((direita (1 / 2 + δ) T).ncard : ℝ) ≤ |C| * T :=
      hd.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hT0.le)
    rw [hs, div_le_div_iff₀ hn (div_pos hn hT0)]
    have e : K * ((todos T).ncard : ℝ) = (K * T) * (((todos T).ncard : ℝ) / T) := by
      field_simp
    rw [e]
    have : (((direita (1 / 2 + δ) T).ncard : ℝ) + (direita (1 / 2 + δ) T).ncard) ≤ K * T := by
      simp only [K]; linarith
    calc (((direita (1 / 2 + δ) T).ncard : ℝ) + (direita (1 / 2 + δ) T).ncard) *
          (((todos T).ncard : ℝ) / T) ≤ (K * T) * (((todos T).ncard : ℝ) / T) :=
        mul_le_mul_of_nonneg_right this (div_pos hn hT0).le
      _ = _ := rfl

end ATK.BohrLandau

#print axioms ATK.BohrLandau.todos_finite
#print axioms ATK.BohrLandau.torcao_direita
#print axioms ATK.BohrLandau.simetria_contagem
#print axioms ATK.BohrLandau.rh_bohrLandau
#print axioms ATK.BohrLandau.rh_densidade
#print axioms ATK.BohrLandau.densidade_de_bohrLandau
#print axioms ATK.BohrLandau.direita_subset
#print axioms ATK.BohrLandau.esquerda_subset
#print axioms ATK.BohrLandau.torcao_torcao
#print axioms ATK.BohrLandau.torcao_injective
#print axioms ATK.BohrLandau.direita_vazia_de_rh
#print axioms ATK.BohrLandau.esquerda_vazia_de_rh
