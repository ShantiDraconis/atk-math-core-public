import ATK.NecessidadeBD
import ATK.ForaDaLinha
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected

/-!
# O1 (Riemann): a estrutura completa do fechamento e o que falta na Mathlib

O1 está em `N = ⟨false, false⟩`: nenhuma prova, nenhuma refutação. Este arquivo:

**1. Prova o que a Mathlib já permite** (incondicional):

* `zeros_finitos_compacto`: os zeros de `ζ` num compacto que não contém `1` são **finitos**
  (`ζ` é analítica e não nula em `ℂ ∖ {1}`, que é conexo, então os zeros são isolados);
* `zerosAte_finito`, `zerosSim_finito`: os zeros não triviais com `0 < Im ρ ≤ T` (e com
  `|Im ρ| ≤ T`) são finitos, logo a **função de contagem `N(T)`** (com multiplicidade, via
  `analyticOrderNatAt`) está **bem definida**; `N_mono`; `N_baixo`: `N(T) = 0` para `T < 1/2`;
* `xi`: a função `ξ(s) = s(s−1)/2 · Λ₀(s) + 1/2`, inteira, e `xi_zero`: `ξ(0) = 1/2`.

**2. Define formalmente o que falta na Mathlib** (enunciados com tipo exato, não provados):

* `RiemannVonMangoldt`: `N(T) = (T/2π) log(T/2π) − T/2π + O(log T)`;
* `HadamardXi`: `ξ(s) = e^{A+Bs} ∏_ρ (1 − s/ρ) e^{s/ρ}` (produtos parciais simétricos `|Im ρ| ≤ T`);
* `LittlewoodSobRH`: sob RH, `1/ζ(σ + it) = O(|t|^ε)` para `σ ≥ 1/2 + δ`.

**3. Dá a estrutura do fechamento real de O1**:

* `NecessidadeRH`: os três teoremas acima, mais a dedução analítica clássica até
  `EntradasNecessidade`. Com ela, `rh_iff_DN` vale: **RH ⟺ `D_N → 0`**, e
  `entradas_iff_rh` vale (as entradas têm a força exata de RH);
* `RotaO1`: as três rotas que fechariam O1 (zero fora da linha impossível; `D_N → 0` via B1, já
  provada; entradas via `rh_of_entradas`). `rotaO1_iff_rh` diz que **toda rota tem exatamente
  a força de RH**, e não existe produtor mais fraco.

`NecessidadeRH` fecharia a **necessidade** (o iff), não RH. O1 continua `N`.
-/

open Complex Set Filter Topology
open ATK.ZetaSimetria ATK.ZetaRetangulo ATK.ForaDaLinha ATK.NecessidadeBD ATK.Conditional.Riemann
  ATK.BaezDuarteBridge

namespace ATK.FechamentoO1

/-! ## 1. Finitude dos zeros e a função de contagem -/

/-- Os zeros de `ζ` num compacto que não contém `1` são finitos. -/
theorem zeros_finitos_compacto {K : Set ℂ} (hK : IsCompact K) (h1 : (1 : ℂ) ∉ K) :
    {z ∈ K | riemannZeta z = 0}.Finite := by
  set U : Set ℂ := {1}ᶜ
  have hU : IsOpen U := isOpen_compl_singleton
  have hd : DifferentiableOn ℂ riemannZeta U := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  have ha : AnalyticOnNhd ℂ riemannZeta U := hd.analyticOnNhd hU
  have hconn : IsPreconnected U :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [rank_real_complex]; norm_num) 1).isPreconnected
  rcases ha.eqOn_zero_or_eventually_ne_zero_of_preconnected hconn with h | h
  · exfalso
    have h2U : (2 : ℂ) ∈ U := by
      simp only [U, mem_compl_iff, mem_singleton_iff]
      norm_num
    exact riemannZeta_ne_zero_of_one_lt_re (s := 2) (by norm_num) (h h2U)
  · have hKU : K ⊆ U := fun z hz hz1 => h1 ((mem_singleton_iff.mp hz1) ▸ hz)
    have hs : {x | riemannZeta x ≠ 0} ∈ codiscreteWithin K := Filter.codiscreteWithin_mono hKU h
    refine (hK.finite_sdiff_of_mem_codiscreteWithin hs).subset ?_
    rintro z ⟨hzK, hz0⟩
    exact ⟨hzK, fun hne => hne hz0⟩

/-- Todo zero não trivial tem `|Im ρ| ≥ 1/2` (de `sem_zeros_ate_altura`: `Im ρ² ≥ 3/4`). -/
theorem abs_im_ge {ρ : ℂ} (hρ : ρ ∈ Z) : 1 / 2 ≤ |ρ.im| := by
  have h := sem_zeros_ate_altura ρ hρ
  by_contra hlt
  push_neg at hlt
  have : ρ.im ^ 2 < 1 / 4 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg ρ.im]
  linarith

/-- Zeros não triviais com `0 < Im ρ ≤ T`. -/
def zerosAte (T : ℝ) : Set ℂ := {ρ ∈ Z | 0 < ρ.im ∧ ρ.im ≤ T}

/-- Zeros não triviais com `|Im ρ| ≤ T` (para os produtos simétricos de Hadamard). -/
def zerosSim (T : ℝ) : Set ℂ := {ρ ∈ Z | |ρ.im| ≤ T}

theorem zerosAte_finito (T : ℝ) : (zerosAte T).Finite := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc (1 / 2) T) := isCompact_Icc.reProdIm isCompact_Icc
  have h1 : (1 : ℂ) ∉ Icc (0 : ℝ) 1 ×ℂ Icc (1 / 2) T := by
    simp [mem_reProdIm]
  refine (zeros_finitos_compacto hK h1).subset ?_
  rintro ρ ⟨hZ, hpos, hT⟩
  have hge := abs_im_ge hZ
  rw [abs_of_pos hpos] at hge
  exact ⟨⟨⟨hZ.2.1.le, hZ.2.2.le⟩, hge, hT⟩, hZ.1⟩

theorem zerosSim_finito (T : ℝ) : (zerosSim T).Finite := by
  have hK1 : IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc (1 / 2) T) := isCompact_Icc.reProdIm isCompact_Icc
  have hK2 : IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc (-T) (-(1 / 2))) := isCompact_Icc.reProdIm isCompact_Icc
  have h1 : (1 : ℂ) ∉ Icc (0 : ℝ) 1 ×ℂ Icc (1 / 2) T := by simp [mem_reProdIm]
  have h2 : (1 : ℂ) ∉ Icc (0 : ℝ) 1 ×ℂ Icc (-T) (-(1 / 2)) := by simp [mem_reProdIm]
  refine ((zeros_finitos_compacto hK1 h1).union (zeros_finitos_compacto hK2 h2)).subset ?_
  rintro ρ ⟨hZ, hT⟩
  have hge := abs_im_ge hZ
  have hre : ρ.re ∈ Icc (0 : ℝ) 1 := ⟨hZ.2.1.le, hZ.2.2.le⟩
  rcases le_or_gt 0 ρ.im with h | h
  · rw [abs_of_nonneg h] at hge hT
    exact Or.inl ⟨⟨hre, hge, hT⟩, hZ.1⟩
  · rw [abs_of_neg h] at hge hT
    exact Or.inr ⟨⟨hre, by linarith, by linarith⟩, hZ.1⟩

/-- **A função de contagem** `N(T)`: zeros não triviais com `0 < Im ρ ≤ T`, com multiplicidade. -/
noncomputable def N (T : ℝ) : ℕ :=
  ∑ ρ ∈ (zerosAte_finito T).toFinset, analyticOrderNatAt riemannZeta ρ

theorem zerosAte_mono {T T' : ℝ} (h : T ≤ T') : zerosAte T ⊆ zerosAte T' :=
  fun _ ⟨hZ, hp, hT⟩ => ⟨hZ, hp, hT.trans h⟩

/-- `N` é monótona. -/
theorem N_mono {T T' : ℝ} (h : T ≤ T') : N T ≤ N T' :=
  Finset.sum_le_sum_of_subset
    (Set.Finite.toFinset_subset_toFinset.mpr (zerosAte_mono h))

/-- Não há zero não trivial com `0 < Im ρ < 1/2`: `N(T) = 0` para `T < 1/2`. -/
theorem N_baixo {T : ℝ} (hT : T < 1 / 2) : N T = 0 := by
  have : zerosAte T = ∅ := by
    ext ρ
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨hZ, hpos, hle⟩
    have := abs_im_ge hZ
    rw [abs_of_pos hpos] at this
    linarith
  unfold N
  simp [this]

/-! ## 2. O que falta na Mathlib, com tipo exato -/

/-- `ξ(s) = s(s−1)/2 · Λ(s)`, escrita com a parte inteira `Λ₀` (`Λ = Λ₀ − 1/s − 1/(1−s)`):
`ξ(s) = s(s−1)/2 · Λ₀(s) + 1/2`, inteira. -/
noncomputable def xi (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2

theorem xi_zero : xi 0 = 1 / 2 := by simp [xi]

/-- **Riemann–von Mangoldt**: `N(T) = (T/2π) log(T/2π) − T/2π + O(log T)`. -/
def RiemannVonMangoldt : Prop :=
  ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    |(N T : ℝ) - (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi))| ≤
      C * Real.log T

/-- **Hadamard para `ξ`** (função inteira de ordem 1): produtos parciais simétricos com
multiplicidade convergem para `ξ`. -/
def HadamardXi : Prop :=
  ∃ A B : ℂ, ∀ s : ℂ, Tendsto (fun T : ℝ => cexp (A + B * s) *
    ∏ ρ ∈ (zerosSim_finito T).toFinset,
      ((1 - s / ρ) * cexp (s / ρ)) ^ analyticOrderNatAt riemannZeta ρ) atTop (𝓝 (xi s))

/-- **Littlewood sob RH**: `1/ζ(σ + it) = O(|t|^ε)` uniformemente em `σ ≥ 1/2 + δ`. -/
def LittlewoodSobRH : Prop :=
  RiemannHypothesis → ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ σ t : ℝ,
    1 / 2 + δ ≤ σ → 1 ≤ |t| → ‖(riemannZeta (σ + t * I))⁻¹‖ ≤ C * |t| ^ ε

/-! ## 3. A estrutura do fechamento real de O1 -/

/-- **A necessidade de Báez-Duarte**, em peças: os três teoremas ausentes da Mathlib e a dedução
analítica clássica (Littlewood 1912; Titchmarsh §14; Báez-Duarte 2003) até as entradas. -/
structure NecessidadeRH : Prop where
  rvm : RiemannVonMangoldt
  hadamard : HadamardXi
  littlewood : LittlewoodSobRH
  deducao : RiemannVonMangoldt → HadamardXi → LittlewoodSobRH →
    RiemannHypothesis → EntradasNecessidade

/-- Com a necessidade, **RH ⟺ `D_N → 0`** (a volta é B1, já provada). -/
theorem rh_iff_DN (h : NecessidadeRH) : RiemannHypothesis ↔ Tendsto DN atTop (𝓝 0) :=
  ⟨fun hRH => DN_tendsto_zero_of_entradas (h.deducao h.rvm h.hadamard h.littlewood hRH),
    baezDuarteCriterion⟩

/-- Com a necessidade, **as entradas têm a força exata de RH**. -/
theorem entradas_iff_rh (h : NecessidadeRH) : EntradasNecessidade ↔ RiemannHypothesis :=
  ⟨rh_of_entradas, h.deducao h.rvm h.hadamard h.littlewood⟩

/-- **As rotas que fechariam O1**, cada uma com o seu produtor. -/
inductive RotaO1 : Prop
  /-- Produtor direto: não existe zero não trivial fora da reta. -/
  | semZeroFora : IsEmpty ZeroFora → RotaO1
  /-- Via B1 (Báez-Duarte, suficiência, provada): `D_N → 0`. -/
  | baezDuarte : Tendsto DN atTop (𝓝 0) → RotaO1
  /-- Via as entradas, sem hipótese (`rh_of_entradas`). -/
  | entradas : EntradasNecessidade → RotaO1

/-- **Fechamento de O1**: qualquer rota fecha RH. -/
theorem fecha_O1 : RotaO1 → RiemannHypothesis
  | .semZeroFora h => riemann_iff_vazio.mpr h
  | .baezDuarte h => baezDuarteCriterion h
  | .entradas h => rh_of_entradas h

/-- **Toda rota tem exatamente a força de RH**: não existe produtor de O1 mais fraco que RH. -/
theorem rotaO1_iff_rh : RotaO1 ↔ RiemannHypothesis :=
  ⟨fecha_O1, fun h => .semZeroFora (riemann_iff_vazio.mp h)⟩

/-- Refutar RH fecha todas as rotas. -/
theorem sem_rota_se_refutado (h : ¬ RiemannHypothesis) : ¬ RotaO1 := fun r => h (fecha_O1 r)

end ATK.FechamentoO1

#print axioms ATK.FechamentoO1.zeros_finitos_compacto
#print axioms ATK.FechamentoO1.abs_im_ge
#print axioms ATK.FechamentoO1.zerosAte_finito
#print axioms ATK.FechamentoO1.zerosSim_finito
#print axioms ATK.FechamentoO1.zerosAte_mono
#print axioms ATK.FechamentoO1.N_mono
#print axioms ATK.FechamentoO1.N_baixo
#print axioms ATK.FechamentoO1.xi_zero
#print axioms ATK.FechamentoO1.rh_iff_DN
#print axioms ATK.FechamentoO1.entradas_iff_rh
#print axioms ATK.FechamentoO1.fecha_O1
#print axioms ATK.FechamentoO1.rotaO1_iff_rh
#print axioms ATK.FechamentoO1.sem_rota_se_refutado
