import Mathlib.Analysis.Real.Hyperreal

/-!
# ATK — Oscilação 0/1: diverge em `ℝ`, mas é 0 ou 1 nos hiper-reais

O acervo trata a oscilação `0, 1, 0, 1, …` como "estado indeterminado entre 0 e 1". O que é
verdade, certificado aqui:

* `nao_converge`: em `ℝ`, a sequência `n mod 2` **não converge** (as subsequências par e ímpar
  têm limites 0 e 1);
* `oscilacao_01`: em `ℝ* = Germ (hyperfilter ℕ) ℝ`, **toda** sequência com valores em `{0, 1}`
  define exatamente `0` ou exatamente `1` (o ultrafiltro decide; não há valor intermediário);
* `oscilacao_sinal`: `(−1)ⁿ` define `1` ou `−1` em `ℝ*`;
* `classe_menos_classe`: `[a] − [a] = 0` em `ℝ*` (refuta A193/A194 do catálogo).

Qual dos dois valores aparece depende do ultrafiltro escolhido (não construtivo); a dicotomia em si
é teorema. Matemática conhecida (teorema de Łoś, caso elementar); nova só a formalização.
-/

open Filter Topology

namespace ATK.OscilacaoHiperreal

/-- A classe de uma sequência constante é o real correspondente. -/
theorem ofSeq_const (r : ℝ) : Hyperreal.ofSeq (fun _ => r) = (r : ℝ*) := rfl

/-- Se `f n = r` para quase todo `n` (no ultrafiltro), então `[f] = r`. -/
theorem ofSeq_eq_of_eventually {f : ℕ → ℝ} {r : ℝ}
    (h : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n = r) : Hyperreal.ofSeq f = (r : ℝ*) := by
  rw [← ofSeq_const]
  exact Germ.coe_eq.mpr h

/-- **Uma sequência com valores em `{0, 1}` vale exatamente 0 ou 1 em `ℝ*`.** -/
theorem oscilacao_01 (f : ℕ → ℝ) (hf : ∀ n, f n = 0 ∨ f n = 1) :
    Hyperreal.ofSeq f = 0 ∨ Hyperreal.ofSeq f = 1 := by
  have h : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), f n = 0 ∨ f n = 1 := Eventually.of_forall hf
  rcases Ultrafilter.eventually_or.mp h with h0 | h1
  · left
    rw [ofSeq_eq_of_eventually h0, Hyperreal.coe_zero]
  · right
    rw [ofSeq_eq_of_eventually h1, Hyperreal.coe_one]

/-- **`(−1)ⁿ` vale `1` ou `−1` em `ℝ*`.** -/
theorem oscilacao_sinal :
    Hyperreal.ofSeq (fun n => (-1 : ℝ) ^ n) = 1 ∨ Hyperreal.ofSeq (fun n => (-1 : ℝ) ^ n) = -1 := by
  have h : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), (-1 : ℝ) ^ n = 1 ∨ (-1 : ℝ) ^ n = -1 :=
    Eventually.of_forall fun n => neg_one_pow_eq_or ℝ n
  rcases Ultrafilter.eventually_or.mp h with h1 | h2
  · left
    rw [ofSeq_eq_of_eventually h1, Hyperreal.coe_one]
  · right
    rw [ofSeq_eq_of_eventually h2, Hyperreal.coe_neg, Hyperreal.coe_one]

/-- A sequência `0, 1, 0, 1, …` como função de `ℕ`. -/
theorem paridade_01 (n : ℕ) : ((n % 2 : ℕ) : ℝ) = 0 ∨ ((n % 2 : ℕ) : ℝ) = 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

/-- Logo a oscilação `n mod 2` é 0 ou 1 em `ℝ*`. -/
theorem paridade_hiperreal :
    Hyperreal.ofSeq (fun n => ((n % 2 : ℕ) : ℝ)) = 0 ∨
      Hyperreal.ofSeq (fun n => ((n % 2 : ℕ) : ℝ)) = 1 :=
  oscilacao_01 _ paridade_01

/-- **Em `ℝ`, `n mod 2` não converge.** -/
theorem nao_converge : ¬ ∃ L : ℝ, Tendsto (fun n : ℕ => ((n % 2 : ℕ) : ℝ)) atTop (𝓝 L) := by
  rintro ⟨L, h⟩
  have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => show id n ≤ 2 * n by simp only [id_eq]; omega) tendsto_id
  have h3 : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => show id n ≤ 2 * n + 1 by simp only [id_eq]; omega) tendsto_id
  have e0 : Tendsto (fun n : ℕ => ((2 * n % 2 : ℕ) : ℝ)) atTop (𝓝 L) := h.comp h2
  have e1 : Tendsto (fun n : ℕ => (((2 * n + 1) % 2 : ℕ) : ℝ)) atTop (𝓝 L) := h.comp h3
  have z0 : (fun n : ℕ => ((2 * n % 2 : ℕ) : ℝ)) = fun _ => 0 := by
    funext n
    have : 2 * n % 2 = 0 := by omega
    simp [this]
  have z1 : (fun n : ℕ => (((2 * n + 1) % 2 : ℕ) : ℝ)) = fun _ => 1 := by
    funext n
    have : (2 * n + 1) % 2 = 1 := by omega
    simp [this]
  rw [z0] at e0
  rw [z1] at e1
  have hL0 : L = 0 := tendsto_nhds_unique e0 tendsto_const_nhds
  have hL1 : L = 1 := tendsto_nhds_unique e1 tendsto_const_nhds
  linarith

/-- `[a] − [a] = 0` em `ℝ*`. -/
theorem classe_menos_classe (f : ℕ → ℝ) : Hyperreal.ofSeq f - Hyperreal.ofSeq f = 0 :=
  sub_self _

end ATK.OscilacaoHiperreal

#print axioms ATK.OscilacaoHiperreal.ofSeq_const
#print axioms ATK.OscilacaoHiperreal.ofSeq_eq_of_eventually
#print axioms ATK.OscilacaoHiperreal.oscilacao_01
#print axioms ATK.OscilacaoHiperreal.oscilacao_sinal
#print axioms ATK.OscilacaoHiperreal.paridade_01
#print axioms ATK.OscilacaoHiperreal.paridade_hiperreal
#print axioms ATK.OscilacaoHiperreal.nao_converge
#print axioms ATK.OscilacaoHiperreal.classe_menos_classe
