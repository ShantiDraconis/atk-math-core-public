import ATK.ZeroClasses.Fronteira

/-!
# A competição analítica `Re(ξ′/ξ)` e a meia-ponte de Lagarias (rodada 28)

A versão analítica da competição `Δ₀₁` da rodada 27 é `L(s) = Re(ξ′(s)/ξ(s))`:

* **antissimetria** (`deriv_reflexao`, `deriv_conj`, `logDeriv_reflexao`, `logDeriv_conj`, `Lg_antissim`):
  `L(1 − s̄) = −L(s)`, a mesma lei de `Δ₀₁(1 − x) = −Δ₀₁(x)` (`Lg_e_Dif_antissim`);
* **zero na linha** (`Lg_linha`): `L(½ + it) = 0` para todo `t`, como `Δ₀₁(½) = 0`;
* **é a derivada horizontal de `log|ξ|`** (`deriv_log_norm`): `∂_σ log|ξ(σ + it)| = L(σ + it)` onde `ξ ≠ 0` —
  o sinal de `L` diz para que lado `|ξ|` cresce;
* **o sinal num zero fora da linha** (`sinal_negativo`): se `ξ(ρ) = 0` com `Re ρ > ½`, existe `s` com
  `Re s > ½`, `ξ(s) ≠ 0` e `L(s) < 0` (à esquerda de `ρ`, o resíduo `m/(s − ρ)` domina);
* **meia-ponte de Lagarias** (`positividade_implica_RH`): se `L ≥ 0` em todo `Re s > ½` fora dos zeros, então RH;
* **critério de monotonia** (`monotonia_implica_RH`, Sondow–Dumitrescu): se `σ ↦ |ξ(σ + it)|` é estritamente
  crescente em `σ > ½` para todo `t`, então RH;
* **a recíproca está condicionada a RH** (`positividade_iff_RH_de`, `monotonia_iff_RH_de`): com a
  recíproca como hipótese nomeada (Lagarias 1999 / Sondow–Dumitrescu 2010, via o produto de Hadamard de `ξ`,
  ausente da Mathlib: BUILD_PENDING), as duas condições ficam **equivalentes** a RH.

Classificação (rodada 28): **reformulação** — `L ≥ 0` e a monotonia são equivalentes a RH; provar qualquer uma
delas sem RH seria a alavanca. O que é incondicional: a antissimetria, `L = 0` na linha, `L = ∂_σ log|ξ|`, e o
sentido "zero fora ⟹ `L < 0` em algum ponto".
-/

open Complex ComplexConjugate Set Filter Topology
open scoped Real

namespace ATK.ZeroClasses.Lagarias

open ATK.BaseRiemannXi ATK.ZeroClasses ATK.ZeroClasses.Fronteira

/-- A competição analítica `L(s) = Re(ξ′(s)/ξ(s))`. -/
noncomputable def Lg (s : ℂ) : ℝ := (logDeriv riemannXi s).re

/-! ## 1. Antissimetria e a linha -/

/-- `ξ′(1 − s) = −ξ′(s)`. -/
theorem deriv_reflexao (s : ℂ) : deriv riemannXi (1 - s) = -deriv riemannXi s := by
  have h : (fun x => riemannXi (1 - x)) = riemannXi := funext riemannXi_one_sub
  have e := deriv_comp_const_sub (f := riemannXi) (a := 1) (x := s)
  rw [h] at e
  rw [e, neg_neg]

/-- `ξ′(s̄) = conj ξ′(s)`. -/
theorem deriv_conj (s : ℂ) : deriv riemannXi (conj s) = conj (deriv riemannXi s) := by
  have h : (conj ∘ riemannXi ∘ conj) = riemannXi := by
    funext w
    simp [Function.comp, riemannXi_conj]
  have e := congrFun (deriv_conj_conj (f := riemannXi)) (conj s)
  rw [h] at e
  simpa using e

theorem logDeriv_reflexao (s : ℂ) : logDeriv riemannXi (1 - s) = -logDeriv riemannXi s := by
  simp only [logDeriv_apply, deriv_reflexao, riemannXi_one_sub, neg_div]

theorem logDeriv_conj (s : ℂ) : logDeriv riemannXi (conj s) = conj (logDeriv riemannXi s) := by
  simp only [logDeriv_apply, deriv_conj, riemannXi_conj, map_div₀]

/-- **`L(1 − s̄) = −L(s)`.** -/
theorem Lg_antissim (s : ℂ) : Lg (1 - conj s) = -Lg s := by
  unfold Lg
  rw [logDeriv_reflexao, logDeriv_conj, neg_re, conj_re]

/-- **`L(½ + it) = 0`** para todo `t`. -/
theorem Lg_linha (t : ℝ) : Lg (1 / 2 + t * I) = 0 := by
  have e : 1 - conj ((1 / 2 : ℂ) + t * I) = 1 / 2 + t * I := by
    apply Complex.ext <;> norm_num
  have := Lg_antissim ((1 / 2 : ℂ) + t * I)
  rw [e] at this
  linarith

/-- `L` e `Δ₀₁` obedecem à mesma lei de reflexão. -/
theorem Lg_e_Dif_antissim (s : ℂ) :
    Lg (1 - conj s) = -Lg s ∧ Dif 0 1 (1 - conj s).re = -Dif 0 1 s.re := by
  refine ⟨Lg_antissim s, ?_⟩
  rw [show (1 - conj s).re = 1 - s.re by simp, Dif01_antissim]

/-! ## 2. `L` é a derivada horizontal de `log|ξ|` -/

/-- **`∂_σ log|ξ(σ + it)| = L(σ + it)`** onde `ξ ≠ 0`. -/
theorem deriv_log_norm (σ t : ℝ) (h : riemannXi (σ + t * I) ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log ‖riemannXi (x + t * I)‖) (Lg (σ + t * I)) σ := by
  set g : ℝ → ℂ := fun x => riemannXi (x + t * I) with hg
  set d := deriv riemannXi (σ + t * I) with hd
  have hgd : HasDerivAt g d σ := by
    have h1 : HasDerivAt (fun w : ℂ => riemannXi (w + t * I)) d (σ : ℂ) :=
      ((differentiable_riemannXi _).hasDerivAt).comp_add_const _ _
    exact h1.comp_ofReal
  have hn := hgd.norm_sq
  have hpos : (0 : ℝ) < ‖g σ‖ ^ 2 := by
    have : g σ ≠ 0 := h
    positivity
  have hlog := hn.log hpos.ne'
  have e1 : (fun x : ℝ => Real.log ‖riemannXi (x + t * I)‖) = fun x => Real.log (‖g x‖ ^ 2) / 2 := by
    funext x
    rw [Real.log_pow]
    push_cast
    ring
  rw [e1]
  convert hlog.div_const 2 using 1
  rw [Complex.inner]
  unfold Lg
  rw [logDeriv_apply]
  have hgs : g σ = riemannXi (σ + t * I) := rfl
  rw [← hgs, ← hd]
  have hne : g σ ≠ 0 := h
  rw [Complex.div_re, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  field_simp
  ring

/-! ## 3. O sinal num zero fora da linha -/

theorem analitica (z : ℂ) : AnalyticAt ℂ riemannXi z := differentiable_riemannXi.analyticAt z

theorem ordem_xi_finita (z : ℂ) : analyticOrderAt riemannXi z ≠ ⊤ :=
  ATK.ArgPrincipio.ordem_finita (U := univ) (fun w _ => analitica w) isPreconnected_univ (mem_univ 0)
    (by rw [riemannXi_zero]; norm_num) (mem_univ z)

/-- O caminho `h ↦ ρ − h`, `h → 0⁺`, chega a `ρ` sem passar por `ρ`. -/
theorem caminho_esquerda (ρ : ℂ) : Tendsto (fun h : ℝ => ρ - (h : ℂ)) (𝓝[>] 0) (𝓝[≠] ρ) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hc : Continuous fun h : ℝ => ρ - (h : ℂ) := continuous_const.sub continuous_ofReal
    have := hc.tendsto 0
    simp only [ofReal_zero, sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with h hh
    intro e
    have : (h : ℂ) = 0 := by
      have e' : ρ - (h : ℂ) = ρ := e
      linear_combination -e'
    exact (ne_of_gt (mem_Ioi.mp hh)) (by exact_mod_cast this)

/-- **Num zero de `ξ` com `Re ρ > ½`, `L` fica negativo logo à esquerda.** -/
theorem sinal_negativo {ρ : ℂ} (h0 : riemannXi ρ = 0) (hre : 1 / 2 < ρ.re) :
    ∃ s : ℂ, 1 / 2 < s.re ∧ riemannXi s ≠ 0 ∧ Lg s < 0 := by
  have ha := analitica ρ
  have htop := ordem_xi_finita ρ
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
  have hmN : analyticOrderNatAt riemannXi ρ = m := by simp [analyticOrderNatAt, ← hm]
  have hm1 : 1 ≤ m := by
    by_contra hlt
    have hm0 : m = 0 := by omega
    have := (ATK.ArgPrincipio.ordemNat_zero_iff ha htop).mp (by rw [hmN, hm0])
    exact this h0
  have hlim := ATK.ZeroClasses.Componentes.residuo_logderiv ha (m := m) hm.symm
  have hcomp := hlim.comp (caminho_esquerda ρ)
  have hre_lim : Tendsto (fun h : ℝ => (((ρ - (h : ℂ)) - ρ) * deriv riemannXi (ρ - h) /
      riemannXi (ρ - h)).re) (𝓝[>] 0) (𝓝 (m : ℝ)) := by
    have := (Complex.continuous_re.tendsto _).comp hcomp
    simpa [Function.comp_def] using this
  have hm2 : (m : ℝ) / 2 < m := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have hev1 := hre_lim.eventually (lt_mem_nhds hm2)
  have hne : ∀ᶠ z in 𝓝[≠] ρ, riemannXi z ≠ 0 :=
    ha.eventually_eq_zero_or_eventually_ne_zero.resolve_left fun hz =>
      htop (analyticOrderAt_eq_top.mpr hz)
  have hev2 := (caminho_esquerda ρ).eventually hne
  have hev3 : ∀ᶠ h in 𝓝[>] (0 : ℝ), h < ρ.re - 1 / 2 := by
    have : ∀ᶠ h in 𝓝 (0 : ℝ), h < ρ.re - 1 / 2 := gt_mem_nhds (show (0 : ℝ) < ρ.re - 1 / 2 by linarith)
    exact nhdsWithin_le_nhds this
  have hev4 : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  obtain ⟨h, h1, h2, h3, h4⟩ := (hev1.and (hev2.and (hev3.and hev4))).exists
  refine ⟨ρ - h, ?_, h2, ?_⟩
  · simp only [sub_re, ofReal_re]
    linarith
  · have e : ((ρ - (h : ℂ)) - ρ) * deriv riemannXi (ρ - h) / riemannXi (ρ - h) =
        (-h : ℝ) * logDeriv riemannXi (ρ - h) := by
      rw [logDeriv_apply]
      push_cast
      ring
    rw [e, re_ofReal_mul] at h1
    unfold Lg
    have hm0 : (0 : ℝ) < m / 2 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      linarith
    by_contra hc
    have hc' : 0 ≤ (logDeriv riemannXi (ρ - h)).re := not_lt.mp hc
    nlinarith

/-! ## 4. As duas meias-pontes -/

/-- Um zero de `ζ` com `½ < Re s < 1` é zero de `ξ`. -/
theorem xi_zero_de_ZR {s : ℂ} (hs : s ∈ ATK.ZeroClasses.Regions.ZR) : riemannXi s = 0 := by
  obtain ⟨⟨h0, h1, h2⟩, _⟩ := hs
  have hs1 : s ≠ 1 := by
    intro e
    rw [e, one_re] at h2
    exact lt_irrefl _ h2
  exact (riemannXi_eq_zero_iff h1 hs1).mpr h0

theorem rh_de_ZR_vazio (h : ∀ s ∈ ATK.ZeroClasses.Regions.ZR, False) : RiemannHypothesis :=
  ATK.ZeroClasses.Regions.rh_iff_ZL.mpr
    (ATK.ZeroClasses.Regions.ZL_vazio_iff_ZR.mpr (Set.eq_empty_iff_forall_notMem.mpr h))

/-- **Meia-ponte de Lagarias**: `L ≥ 0` em `Re s > ½` (fora dos zeros) ⟹ RH. -/
theorem positividade_implica_RH (h : ∀ s : ℂ, 1 / 2 < s.re → riemannXi s ≠ 0 → 0 ≤ Lg s) :
    RiemannHypothesis := by
  refine rh_de_ZR_vazio fun s hs => ?_
  obtain ⟨w, hw1, hw2, hw3⟩ := sinal_negativo (xi_zero_de_ZR hs) hs.2
  exact absurd (h w hw1 hw2) (not_le.mpr hw3)

/-- **Critério de monotonia** (Sondow–Dumitrescu): `|ξ(σ + it)|` estritamente crescente em `σ > ½` ⟹ RH. -/
theorem monotonia_implica_RH
    (h : ∀ t : ℝ, StrictMonoOn (fun σ : ℝ => ‖riemannXi (σ + t * I)‖) (Ioi (1 / 2))) :
    RiemannHypothesis := by
  refine rh_de_ZR_vazio fun s hs => ?_
  have hx := xi_zero_de_ZR hs
  have hβ : 1 / 2 < s.re := hs.2
  set σ' : ℝ := (1 / 2 + s.re) / 2
  have h1 : σ' ∈ Ioi (1 / 2 : ℝ) := by simp only [mem_Ioi, σ']; linarith
  have h2 : s.re ∈ Ioi (1 / 2 : ℝ) := hβ
  have h3 : σ' < s.re := by simp only [σ']; linarith
  have hlt := h s.im h1 h2 h3
  simp only at hlt
  rw [Complex.re_add_im, hx, norm_zero] at hlt
  exact absurd hlt (not_lt.mpr (norm_nonneg _))

/-- A recíproca de Lagarias (via o produto de Hadamard de `ξ`, BUILD_PENDING), como hipótese nomeada. -/
def RecLagarias : Prop :=
  RiemannHypothesis → ∀ s : ℂ, 1 / 2 < s.re → riemannXi s ≠ 0 → 0 ≤ Lg s

/-- A recíproca de Sondow–Dumitrescu, como hipótese nomeada. -/
def RecMonotonia : Prop :=
  RiemannHypothesis → ∀ t : ℝ, StrictMonoOn (fun σ : ℝ => ‖riemannXi (σ + t * I)‖) (Ioi (1 / 2))

/-- **Com a recíproca nomeada, `L ≥ 0` ⟺ RH.** -/
theorem positividade_iff_RH_de (hr : RecLagarias) :
    (∀ s : ℂ, 1 / 2 < s.re → riemannXi s ≠ 0 → 0 ≤ Lg s) ↔ RiemannHypothesis :=
  ⟨positividade_implica_RH, hr⟩

/-- **Com a recíproca nomeada, a monotonia ⟺ RH.** -/
theorem monotonia_iff_RH_de (hr : RecMonotonia) :
    (∀ t : ℝ, StrictMonoOn (fun σ : ℝ => ‖riemannXi (σ + t * I)‖) (Ioi (1 / 2))) ↔ RiemannHypothesis :=
  ⟨monotonia_implica_RH, hr⟩

/-- **Negar a positividade em um único ponto não refuta RH sozinho; mas um zero fora força esse ponto.** -/
theorem nao_RH_forca_negativo (h : ¬ RiemannHypothesis) :
    ∃ s : ℂ, 1 / 2 < s.re ∧ riemannXi s ≠ 0 ∧ Lg s < 0 := by
  by_contra hc
  simp only [not_exists, not_and, not_lt] at hc
  exact h (positividade_implica_RH hc)

end ATK.ZeroClasses.Lagarias

#print axioms ATK.ZeroClasses.Lagarias.deriv_reflexao
#print axioms ATK.ZeroClasses.Lagarias.deriv_conj
#print axioms ATK.ZeroClasses.Lagarias.logDeriv_reflexao
#print axioms ATK.ZeroClasses.Lagarias.logDeriv_conj
#print axioms ATK.ZeroClasses.Lagarias.Lg_antissim
#print axioms ATK.ZeroClasses.Lagarias.Lg_linha
#print axioms ATK.ZeroClasses.Lagarias.Lg_e_Dif_antissim
#print axioms ATK.ZeroClasses.Lagarias.deriv_log_norm
#print axioms ATK.ZeroClasses.Lagarias.analitica
#print axioms ATK.ZeroClasses.Lagarias.ordem_xi_finita
#print axioms ATK.ZeroClasses.Lagarias.caminho_esquerda
#print axioms ATK.ZeroClasses.Lagarias.sinal_negativo
#print axioms ATK.ZeroClasses.Lagarias.xi_zero_de_ZR
#print axioms ATK.ZeroClasses.Lagarias.rh_de_ZR_vazio
#print axioms ATK.ZeroClasses.Lagarias.positividade_implica_RH
#print axioms ATK.ZeroClasses.Lagarias.monotonia_implica_RH
#print axioms ATK.ZeroClasses.Lagarias.positividade_iff_RH_de
#print axioms ATK.ZeroClasses.Lagarias.monotonia_iff_RH_de
#print axioms ATK.ZeroClasses.Lagarias.nao_RH_forca_negativo
