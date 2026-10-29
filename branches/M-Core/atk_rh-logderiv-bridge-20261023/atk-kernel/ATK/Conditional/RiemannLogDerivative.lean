import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import ATK.ZetaSimetria

/-!
# Condicional — Hipótese de Riemann via positividade da derivada logarítmica

Enunciado-alvo: `RiemannHypothesis` **da própria Mathlib** (fidelidade: OFICIAL).

Rota proposta (esboço de uma IA externa, honesto e não fabricado): define-se a hipótese de
positividade da derivada logarítmica

  `P : ∀ s, 1/2 < s.re → ζ(s) ≠ 0 → 0 < Re(ζ'(s)/ζ(s))`

e argumenta-se `P → RH` via um argumento local de ordem de zero: se `ζ` tivesse um zero `ρ`
com `Re ρ > 1/2` (todo zero fora da reta se reflete para este lado via `torcao`/`tensao` de
`ATK.ZetaSimetria`), então perto de `ρ`, `ζ(z) = (z-ρ)^m · g(z)` com `g(ρ) ≠ 0` analítica, logo
`ζ'(z)/ζ(z) = m/(z-ρ) + g'(z)/g(z)`; tomando `z = ρ - ε` (`ε` real, `0 < ε < Re ρ`), a parte real
do primeiro termo é `-m/ε → -∞` enquanto a do segundo fica limitada perto de `ρ` — logo, para
`ε` pequeno, a soma é negativa, contradizendo `P`.

## O núcleo duro, geral (independente de ζ)

`neg_reLogDeriv_near_zero_of_order_lt_top`: para `f` analítica em `z₀`, com `f z₀ = 0` e ordem de
anulamento **finita** (`analyticOrderAt f z₀ ≠ ⊤`, i.e. `f` não é identicamente nula numa
vizinhança de `z₀` — a hipótese honesta que documenta exatamente o que se usa, no lugar de um
`axiom`), existe `δ > 0` tal que para todo `ε ∈ (0, δ)`, `Re(f'(z₀-ε)/f(z₀-ε)) < 0`. A prova usa a
fatoração local de Mathlib (`AnalyticAt.analyticOrderAt_ne_top`, `Mathlib.Analysis.Analytic.Order`)
e é completamente geral — vale para qualquer ordem finita `m ≥ 1`, não apenas zeros simples.

## A ponte para ζ

`logDerivPositivity_implies_RH`: instancia o lema geral em `f = riemannZeta`, usa a simetria de
`ATK.ZetaSimetria` (`torcao_mem_Z`) para reduzir ao caso `Re ρ > 1/2`, e conclui `RiemannHypothesis`
via `ATK.ZetaSimetria.riemann_iff_torcao`.
-/

namespace ATK.Conditional.RiemannLogDerivative

open Complex Filter Topology Set ATK.ZetaSimetria

/-! ## O núcleo duro: lema geral de análise complexa -/

/-- **Lema geral** (independente de `ζ`): se `f` é analítica em `z₀`, `f z₀ = 0`, e a ordem de
anulamento de `f` em `z₀` é finita (isto é, `f` não é identicamente nula numa vizinhança de
`z₀`), então existe `δ > 0` tal que para todo `ε` real com `0 < ε < δ`, a parte real da derivada
logarítmica de `f` em `z₀ - ε` é negativa. -/
theorem neg_reLogDeriv_near_zero_of_order_lt_top {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) (hz₀ : f z₀ = 0) (hord : analyticOrderAt f z₀ ≠ ⊤) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      (deriv f (z₀ - (ε : ℂ)) / f (z₀ - (ε : ℂ))).re < 0 := by
  classical
  -- A fatoração local `f = (· - z₀) ^ m • g` com `g z₀ ≠ 0`.
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_ne_top.mp hord
  set m := analyticOrderNatAt f z₀ with hm_def
  have hcast : (m : ℕ∞) = analyticOrderAt f z₀ := Nat.cast_analyticOrderNatAt hord
  have hm0 : analyticOrderAt f z₀ ≠ 0 := hf.analyticOrderAt_ne_zero.mpr hz₀
  have hmne : m ≠ 0 := by intro h0; apply hm0; rw [← hcast, h0]; simp
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 :=
    ⟨m - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hmne)).symm⟩
  rw [hk] at hfg
  -- Reescrevemos `•` como `*` em `ℂ`.
  have hfg' : f =ᶠ[𝓝 z₀] fun z => (z - z₀) ^ (k + 1) * g z := by
    filter_upwards [hfg] with z hz using by rw [hz]; simp [smul_eq_mul]
  -- `g'/g`, cuja parte real é continua em `z₀`.
  have hgderiv : AnalyticAt ℂ (deriv g) z₀ := hg.deriv
  have hφcont : ContinuousAt (fun z => deriv g z / g z) z₀ :=
    ContinuousAt.div₀ hgderiv.continuousAt hg.continuousAt hg0
  have hboundEv : ∀ᶠ z in 𝓝 z₀, (deriv g z / g z).re < (deriv g z₀ / g z₀).re + 1 := by
    have hre : ContinuousAt (fun z => (deriv g z / g z).re) z₀ :=
      Complex.continuous_re.continuousAt.comp hφcont
    exact hre.tendsto.eventually_lt_const (by linarith)
  have hgnz : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have hganalytic : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ g z := hg.eventually_analyticAt
  -- Tudo junto, numa única vizinhança aberta `U` de `z₀`.
  have hev : ∀ᶠ z in 𝓝 z₀,
      (f z = (z - z₀) ^ (k + 1) * g z) ∧ g z ≠ 0 ∧ AnalyticAt ℂ g z ∧
        (deriv g z / g z).re < (deriv g z₀ / g z₀).re + 1 :=
    hfg'.and (hgnz.and (hganalytic.and hboundEv))
  obtain ⟨U, hU, hUopen, hUmem⟩ := eventually_nhds_iff.mp hev
  -- A identidade algébrica, válida em todo `x ∈ U` com `x ≠ z₀`.
  have hidentity : ∀ x ∈ U, x ≠ z₀ →
      deriv f x / f x = (↑(k + 1) : ℂ) / (x - z₀) + deriv g x / g x := by
    intro x hx hxz
    obtain ⟨hfx, hgx, hgx_an, _⟩ := hU x hx
    have hw : x - z₀ ≠ 0 := sub_ne_zero.mpr hxz
    have heqU : f =ᶠ[𝓝 x] fun z => (z - z₀) ^ (k + 1) * g z :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hx) (fun y hy => (hU y hy).1)
    have hu' : HasDerivAt (fun z : ℂ => (z - z₀) ^ (k + 1)) ((↑(k + 1) : ℂ) * (x - z₀) ^ k) x := by
      have h1 : HasDerivAt (fun z : ℂ => z - z₀) 1 x := (hasDerivAt_id x).sub_const z₀
      have h2 := h1.fun_pow (k + 1)
      simpa using h2
    have hv' : HasDerivAt g (deriv g x) x := hgx_an.differentiableAt.hasDerivAt
    have hmul := hu'.mul hv'
    have hfderiv : HasDerivAt f
        ((↑(k + 1) : ℂ) * (x - z₀) ^ k * g x + (x - z₀) ^ (k + 1) * deriv g x) x :=
      hmul.congr_of_eventuallyEq heqU
    have hwk : (x - z₀) ^ (k + 1) ≠ 0 := pow_ne_zero _ hw
    rw [hfderiv.deriv, hfx]
    field_simp [hw, hgx, hwk]
    ring
  -- Existe `δ₁ > 0` tal que `z₀ - ε ∈ U` para `0 < ε < δ₁`.
  have hVopen : IsOpen ((fun ε : ℝ => z₀ - (ε : ℂ)) ⁻¹' U) :=
    (continuous_const.sub Complex.continuous_ofReal).isOpen_preimage U hUopen
  have hVmem : (0 : ℝ) ∈ (fun ε : ℝ => z₀ - (ε : ℂ)) ⁻¹' U := by simpa using hUmem
  have hVnhds : ((fun ε : ℝ => z₀ - (ε : ℂ)) ⁻¹' U) ∈ 𝓝[>] (0 : ℝ) :=
    nhdsWithin_le_nhds (hVopen.mem_nhds hVmem)
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hVnhds
  have hδ₁pos' : (0:ℝ) < δ₁ := hδ₁pos
  -- O limiar a partir do crescimento do termo polar.
  set C : ℝ := |(deriv g z₀ / g z₀).re| + 1 with hC_def
  have hC_pos : 0 < C := by positivity
  have hk1pos : (0:ℝ) < (↑(k + 1) : ℝ) := by positivity
  set δ₃ : ℝ := (↑(k + 1) : ℝ) / C with hδ₃_def
  have hδ₃pos : 0 < δ₃ := div_pos hk1pos hC_pos
  refine ⟨min δ₁ δ₃, lt_min hδ₁pos' hδ₃pos, fun ε hε0 hεδ => ?_⟩
  have hε1 : ε < δ₁ := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hε3 : ε < δ₃ := lt_of_lt_of_le hεδ (min_le_right _ _)
  have hxU : z₀ - (ε : ℂ) ∈ U := hδ₁ ⟨hε0, hε1⟩
  have hxz : z₀ - (ε : ℂ) ≠ z₀ := by
    intro h
    have hε0' : (ε : ℂ) = 0 := by linear_combination -h
    have : ε = 0 := by exact_mod_cast hε0'
    exact absurd this hε0.ne'
  have hbound : (deriv g (z₀ - (ε : ℂ)) / g (z₀ - (ε : ℂ))).re < C := by
    obtain ⟨_, _, _, hb⟩ := hU (z₀ - (ε : ℂ)) hxU
    have hle := le_abs_self (deriv g z₀ / g z₀).re
    linarith
  have hid := hidentity (z₀ - (ε : ℂ)) hxU hxz
  have hsub : (z₀ - (ε : ℂ)) - z₀ = -(ε : ℂ) := by ring
  have hre1 : ((↑(k + 1) : ℂ) / (-(ε : ℂ))).re = -((↑(k + 1) : ℝ) / ε) := by
    have heq : (↑(k + 1) : ℂ) / (-(ε : ℂ)) = ((-((↑(k + 1) : ℝ) / ε) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq, Complex.ofReal_re]
  have hCε : C < (↑(k + 1) : ℝ) / ε := by
    rw [hδ₃_def] at hε3
    have hstep : ε * C < (↑(k + 1) : ℝ) := (lt_div_iff₀ hC_pos).mp hε3
    rw [lt_div_iff₀ hε0]
    linarith [mul_comm C ε]
  rw [hid, hsub, Complex.add_re, hre1]
  have hXY : (deriv g (z₀ - (ε : ℂ)) / g (z₀ - (ε : ℂ))).re < (↑(k + 1) : ℝ) / ε :=
    lt_trans hbound hCε
  linarith [hXY]

/-! ## A ponte para ζ -/

/-- **Hipótese de positividade da derivada logarítmica.** -/
def LogDerivPositivity : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0 → 0 < (deriv riemannZeta s / riemannZeta s).re

/-- `ζ` não é identicamente nula numa vizinhança de ponto algum: a ordem de anulamento de `ζ` é
sempre finita fora do pólo `s = 1`. -/
theorem riemannZeta_analyticOrderAt_ne_top {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  have hU : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h2mem : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hρmem : ρ ∈ ({1}ᶜ : Set ℂ) := hρ1
  have h2ne0 : analyticOrderAt riemannZeta (2 : ℂ) ≠ ⊤ := by
    have h2 : riemannZeta (2 : ℂ) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by norm_num)
    rw [(analyticOn_riemannZeta (2 : ℂ) h2mem).analyticOrderAt_eq_zero.2 h2]
    exact ENat.zero_ne_top
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected analyticOn_riemannZeta hU h2mem
    hρmem h2ne0

/-- Instância ζ-específica do lema geral: num zero `ρ` com `Re ρ > 1/2`, perto de `ρ` na direção
real negativa a parte real da derivada logarítmica de `ζ` é negativa. -/
theorem neg_reLogDeriv_riemannZeta {ρ : ℂ} (hζρ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      (deriv riemannZeta (ρ - (ε : ℂ)) / riemannZeta (ρ - (ε : ℂ))).re < 0 :=
  neg_reLogDeriv_near_zero_of_order_lt_top (analyticOn_riemannZeta ρ hρ1) hζρ
    (riemannZeta_analyticOrderAt_ne_top hρ1)

/-- **Condicional RH.** Sob a positividade da derivada logarítmica, todo zero não trivial de `ζ`
está sobre a reta crítica. -/
theorem logDerivPositivity_implies_RH (hP : LogDerivPositivity) : RiemannHypothesis := by
  rw [riemann_iff_torcao]
  by_contra hcon
  push_neg at hcon
  obtain ⟨ρ, hρZ, hρne⟩ := hcon
  -- Reduzimos ao caso `Re ρ' > 1/2`, refletindo por `torcao` se necessário.
  obtain ⟨ρ', hρ'Z, hρ'half⟩ : ∃ ρ' ∈ Z, 1 / 2 < ρ'.re := by
    rcases lt_trichotomy ρ.re (1 / 2) with h | h | h
    · refine ⟨torcao ρ, torcao_mem_Z hρZ, ?_⟩
      rw [re_torcao]; linarith
    · exact absurd ((torcao_fixo_iff ρ).mpr h) hρne
    · exact ⟨ρ, hρZ, h⟩
  obtain ⟨hζρ', hρ'0, hρ'1⟩ := hρ'Z
  have hρ'ne1 : ρ' ≠ 1 := by
    intro h; subst h; simp at hρ'1
  obtain ⟨δ, hδpos, hδ⟩ := neg_reLogDeriv_riemannZeta hζρ' hρ'ne1
  have hgap : 0 < ρ'.re - 1 / 2 := by linarith
  set ε : ℝ := min (δ / 2) ((ρ'.re - 1 / 2) / 2) with hε_def
  -- Precisamos de `0 < ε`, `ε < δ` (para aplicar `hδ`) e `1/2 < (ρ' - ε).re` (para aplicar `hP`).
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεgap : ε < ρ'.re - 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hreρε : 1 / 2 < (ρ' - (ε : ℂ)).re := by
    have hre_eq : (ρ' - (ε : ℂ)).re = ρ'.re - ε := by simp
    rw [hre_eq]; linarith
  have hneg := hδ ε hε0 hεδ
  have hζne : riemannZeta (ρ' - (ε : ℂ)) ≠ 0 := by
    intro hz
    rw [hz, div_zero] at hneg
    simp at hneg
  have hpos := hP (ρ' - (ε : ℂ)) hreρε hζne
  linarith

end ATK.Conditional.RiemannLogDerivative

#print axioms ATK.Conditional.RiemannLogDerivative.neg_reLogDeriv_near_zero_of_order_lt_top
#print axioms ATK.Conditional.RiemannLogDerivative.riemannZeta_analyticOrderAt_ne_top
#print axioms ATK.Conditional.RiemannLogDerivative.neg_reLogDeriv_riemannZeta
#print axioms ATK.Conditional.RiemannLogDerivative.logDerivPositivity_implies_RH
