import ATK.ZeroClasses.Hadamard
import ATK.ZeroCertificadoAplicado
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn

/-!
# As recíprocas de Lagarias e de Sondow–Dumitrescu, sem hipóteses (rodada 34)

A rodada 28 provou as meias-pontes `L ≥ 0 em Re s > ½ ⟹ RH` e `|ξ(σ + it)| crescente em σ > ½ ⟹ RH`, e deixou as
recíprocas como hipóteses nomeadas (`RecLagarias`, `RecMonotonia`), porque dependiam do produto de Hadamard de `ξ`.
Com `hadamardXi` (rodada 33) elas viram teoremas:

* **convergência localmente uniforme** do produto canônico em `ℂ` (`Pcan_localmente`);
* `logDeriv_E1`: `(E1(z/ρ))′/E1(z/ρ) = 1/(z − ρ) + 1/ρ`; `summable_logDeriv`;
* **a derivada logarítmica de `ξ`** (`logDeriv_xi_eq`, via `logDeriv_tprod_eq_tsum` da Mathlib):
  `ξ′/ξ(s) = B + Σ_{(ρ,j)} (1/(s − ρ) + 1/ρ)` onde `ξ(s) ≠ 0`; `Lg_eq`: a parte real;
* **sob RH** (`Lg_sob_RH`): `L(s) = Σ_{(ρ,j)} (σ − ½)/|s − ρ|²`, usando `L(½) = 0` (`Lg_linha`) para eliminar a
  constante; daí `rec_lagarias : RecLagarias` e, com um zero de verdade (`existe_zero_altura`), `Lg_pos`: `L > 0`;
* **`rec_monotonia : RecMonotonia`**: sob RH, `σ ↦ |ξ(σ + it)|` é estritamente crescente em `σ > ½`
  (`∂_σ log|ξ| = L > 0`, `deriv_log_norm` da rodada 28);
* **`positividade_iff_RH`**: `(Re ξ′/ξ ≥ 0 em Re s > ½ fora dos zeros) ⟺ RH`; **`monotonia_iff_RH`**:
  `(|ξ(σ + it)| estritamente crescente em σ > ½ para todo t) ⟺ RH`. Sem hipóteses.

Classificação (rodada 34): **reformulação** — duas equivalências exatas com RH, agora incondicionais. Provar qualquer
um dos lados esquerdos sem RH seria a alavanca. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.LagariasHadamard

open ATK.BaseRiemannXi ATK.ZeroClasses.Canonico ATK.ZeroClasses.CanonicoInteira
  ATK.ZeroClasses.Hadamard ATK.ZeroClasses.Lagarias

/-- O zero `ρ` de uma cópia `(ρ, j)`. -/
abbrev rZ (q : ZM) : ℂ := ((q.1 : ATK.ZetaSimetria.Z) : ℂ)

/-! ## 1. O produto converge localmente uniformemente em `ℂ` -/

theorem Pcan_localmente :
    MultipliableLocallyUniformlyOn (fun (q : ZM) (z : ℂ) => E1 (z / rZ q)) univ := by
  refine ⟨Pcan, hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ fun K _ hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hR1 : (0 : ℝ) < max R 1 := lt_max_of_lt_right one_pos
  have hT := prodE_tendstoUniformlyOn (r := rZ) ZM_ne_zero summable_ZM hR1
  have hH : HasProdUniformlyOn (fun (q : ZM) (z : ℂ) => E1 (z / rZ q)) Pcan (closedBall 0 (max R 1)) :=
    hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr hT
  exact hH.mono (hR.trans (closedBall_subset_closedBall (le_max_left _ _)))

/-! ## 2. A derivada logarítmica -/

theorem logDeriv_E1 {ρ x : ℂ} (hρ : ρ ≠ 0) (hx : x ≠ ρ) :
    logDeriv (fun z => E1 (z / ρ)) x = 1 / (x - ρ) + 1 / ρ := by
  have h1 : HasDerivAt (fun z : ℂ => z / ρ) (1 / ρ) x := by
    simpa using (hasDerivAt_id' x).div_const ρ
  have hd : HasDerivAt (fun z => E1 (z / ρ))
      (-(1 / ρ) * cexp (x / ρ) + (1 - x / ρ) * (cexp (x / ρ) * (1 / ρ))) x := by
    unfold E1
    exact (h1.const_sub 1).mul h1.cexp
  have hxρ : x - ρ ≠ 0 := sub_ne_zero.mpr hx
  have hρx : ρ - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  rw [logDeriv_apply, hd.deriv]
  unfold E1
  have he : cexp (x / ρ) ≠ 0 := Complex.exp_ne_zero _
  field_simp
  ring

theorem summable_logDeriv (x : ℂ) : Summable (fun q : ZM => 1 / (x - rZ q) + 1 / rZ q) := by
  have hR : (0 : ℝ) < 2 * ‖x‖ + 1 := by positivity
  refine (summable_ZM.mul_left (2 * (‖x‖ + 1))).of_norm_bounded_eventually ?_
  filter_upwards [eventualmente_longe (r := rZ) ZM_ne_zero summable_ZM hR] with q hq
  have hρ0 : rZ q ≠ 0 := ZM_ne_zero q
  have hn0 : 0 < ‖rZ q‖ := norm_pos_iff.mpr hρ0
  have hxρ : ‖rZ q‖ / 2 ≤ ‖x - rZ q‖ := by
    have := norm_sub_norm_le (rZ q) x
    rw [norm_sub_rev] at this
    linarith
  have hxρ0 : x - rZ q ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxρ
    linarith
  have e : 1 / (x - rZ q) + 1 / rZ q = x / (rZ q * (x - rZ q)) := by
    field_simp
    ring
  rw [e, norm_div, norm_mul]
  have hden : ‖rZ q‖ * (‖rZ q‖ / 2) ≤ ‖rZ q‖ * ‖x - rZ q‖ := mul_le_mul_of_nonneg_left hxρ hn0.le
  calc ‖x‖ / (‖rZ q‖ * ‖x - rZ q‖) ≤ ‖x‖ / (‖rZ q‖ * (‖rZ q‖ / 2)) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hden
    _ = 2 * ‖x‖ * (1 / ‖rZ q‖ ^ 2) := by field_simp
    _ ≤ 2 * (‖x‖ + 1) * (1 / ‖rZ q‖ ^ 2) := by gcongr; linarith

/-- **`ξ′/ξ(s) = B + Σ_{(ρ,j)} (1/(s − ρ) + 1/ρ)`** onde `ξ(s) ≠ 0`. -/
theorem logDeriv_xi_eq {A B : ℂ} (hAB : ∀ s, riemannXi s = cexp (A + B * s) * Pcan s) {x : ℂ}
    (hx : riemannXi x ≠ 0) :
    logDeriv riemannXi x = B + ∑' q : ZM, (1 / (x - rZ q) + 1 / rZ q) := by
  have hfun : riemannXi = (fun s => cexp (A + B * s)) * Pcan := funext fun s => hAB s
  have hxZ : x ∉ ATK.ZetaSimetria.Z := fun h => hx ((xi_eq_zero_iff_Z x).mpr h)
  have hP : Pcan x ≠ 0 := Pcan_ne_zero hxZ
  rw [hfun, logDeriv_mul (f := fun s => cexp (A + B * s)) (g := Pcan) x (Complex.exp_ne_zero _) hP
    (by fun_prop) (Pcan_differentiable x)]
  congr 1
  · have : HasDerivAt (fun s => cexp (A + B * s)) (cexp (A + B * x) * B) x :=
      (((hasDerivAt_id' x).const_mul B).const_add A).cexp.congr_deriv (by ring)
    rw [logDeriv_apply, this.deriv]
    field_simp [Complex.exp_ne_zero]
  · have hne : ∀ q : ZM, E1 (x / rZ q) ≠ 0 := fun q h => by
      rw [E1_eq_zero_iff, div_eq_one_iff_eq (ZM_ne_zero q)] at h
      exact hxZ (h ▸ q.1.2)
    have hdif : ∀ q : ZM, DifferentiableOn ℂ (fun z => E1 (z / rZ q)) univ := fun q => by
      apply Differentiable.differentiableOn
      unfold E1
      fun_prop
    have hlog : ∀ q : ZM, logDeriv (fun z => E1 (z / rZ q)) x = 1 / (x - rZ q) + 1 / rZ q :=
      fun q => logDeriv_E1 (ZM_ne_zero q) (fun h => hxZ (h ▸ q.1.2))
    have hm : Summable fun q : ZM => logDeriv (fun z => E1 (z / rZ q)) x :=
      (summable_logDeriv x).congr fun q => (hlog q).symm
    have := logDeriv_tprod_eq_tsum isOpen_univ (mem_univ x) hne hdif hm Pcan_localmente hP
    change logDeriv (fun z => ∏' q : ZM, E1 (z / rZ q)) x = _
    rw [this]
    exact tsum_congr hlog

theorem summable_re (x : ℂ) : Summable (fun q : ZM => (1 / (x - rZ q) + 1 / rZ q).re) :=
  (Complex.hasSum_re (summable_logDeriv x).hasSum).summable

theorem Lg_eq {A B : ℂ} (hAB : ∀ s, riemannXi s = cexp (A + B * s) * Pcan s) {x : ℂ}
    (hx : riemannXi x ≠ 0) :
    Lg x = B.re + ∑' q : ZM, (1 / (x - rZ q) + 1 / rZ q).re := by
  unfold Lg
  rw [logDeriv_xi_eq hAB hx, add_re, Complex.re_tsum (summable_logDeriv x)]

/-! ## 3. Sob RH -/

theorem re_de_RH (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ ATK.ZetaSimetria.Z) : ρ.re = 1 / 2 := by
  apply hRH ρ hρ.1
  · rintro ⟨n, hn⟩
    have h := hρ.2.1
    rw [hn] at h
    simp at h
    linarith
  · rintro rfl
    have := hρ.2.2
    simp at this

theorem termo_sob_RH (hRH : RiemannHypothesis) (q : ZM) (s : ℂ) :
    (1 / (s - rZ q) + 1 / rZ q).re - (1 / (1 / 2 - rZ q) + 1 / rZ q).re =
      (s.re - 1 / 2) / Complex.normSq (s - rZ q) := by
  have hre := re_de_RH hRH q.1.2
  have hw0 : ((1 / 2 : ℂ) - rZ q).re = 0 := by
    rw [sub_re, hre]
    norm_num
  have t1 : (1 / ((1 / 2 : ℂ) - rZ q)).re = 0 := by
    rw [one_div, Complex.inv_re, hw0, zero_div]
  have t2 : (1 / (s - rZ q)).re = (s.re - 1 / 2) / Complex.normSq (s - rZ q) := by
    rw [one_div, Complex.inv_re, sub_re, hre]
  rw [add_re, add_re, t1, t2]
  ring

/-- **Sob RH, `L(s) = Σ_{(ρ,j)} (σ − ½)/|s − ρ|²`** (a constante sai de `L(½) = 0`). -/
theorem Lg_sob_RH (hRH : RiemannHypothesis) {s : ℂ} (hs : riemannXi s ≠ 0) :
    Lg s = ∑' q : ZM, (s.re - 1 / 2) / Complex.normSq (s - rZ q) := by
  obtain ⟨A, B, hAB⟩ := xi_hadamard
  have hhalf : riemannXi (1 / 2) ≠ 0 := ATK.ZeroClasses.Jensen.xi_metade_ne_zero
  have h0 : Lg (1 / 2) = 0 := by simpa using Lg_linha 0
  have e1 := Lg_eq hAB hs
  have e2 := Lg_eq hAB hhalf
  have hdif : Lg s = ∑' q : ZM, ((1 / (s - rZ q) + 1 / rZ q).re - (1 / (1 / 2 - rZ q) + 1 / rZ q).re) := by
    rw [(summable_re s).tsum_sub (summable_re (1 / 2))]
    linarith
  rw [hdif]
  refine tsum_congr fun q => ?_
  exact termo_sob_RH hRH q s

/-- **A recíproca de Lagarias**, sem hipóteses: sob RH, `L ≥ 0` em `Re s > ½`. -/
theorem rec_lagarias : RecLagarias := by
  intro hRH s hs hξ
  rw [Lg_sob_RH hRH hξ]
  refine tsum_nonneg fun q => div_nonneg (by linarith) (Complex.normSq_nonneg _)

/-- Sob RH, `L > 0` em `Re s > ½` (há um zero de verdade, `ρ ≈ ½ + 14,13i`). -/
theorem Lg_pos (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re) (hξ : riemannXi s ≠ 0) :
    0 < Lg s := by
  rw [Lg_sob_RH hRH hξ]
  obtain ⟨ρ₁, hρ₁, hre₁, _, _⟩ := ATK.ZeroCertAplicado.existe_zero_altura
  have h1 : ρ₁ ≠ 1 := by
    rintro rfl
    simp at hre₁
  have htop := ATK.ZeroClasses.JensenLocal.ordem_zeta_finita hρ₁.2.1 h1
  have hm : 0 < analyticOrderNatAt riemannZeta ρ₁ := by
    by_contra hlt
    have h0' : analyticOrderNatAt riemannZeta ρ₁ = 0 := by omega
    exact ((ATK.ArgPrincipio.ordemNat_zero_iff (analyticOn_riemannZeta _ h1) htop).mp h0') hρ₁.1
  set q₀ : ZM := ⟨⟨ρ₁, hρ₁⟩, ⟨0, hm⟩⟩
  have hsum : Summable (fun q : ZM => (s.re - 1 / 2) / Complex.normSq (s - rZ q)) := by
    obtain ⟨A, B, hAB⟩ := xi_hadamard
    have := (summable_re s).sub (summable_re (1 / 2))
    refine this.congr fun q => ?_
    exact termo_sob_RH hRH q s
  refine hsum.tsum_pos (fun q => div_nonneg (by linarith) (Complex.normSq_nonneg _)) q₀ ?_
  apply div_pos (by linarith)
  apply Complex.normSq_pos.mpr
  intro h
  have : (s - rZ q₀).re = 0 := by rw [h, zero_re]
  simp only [sub_re] at this
  have hq : (rZ q₀).re = 1 / 2 := hre₁
  linarith

/-- **A recíproca de Sondow–Dumitrescu**, sem hipóteses: sob RH, `|ξ(σ + it)|` cresce estritamente em `σ > ½`. -/
theorem rec_monotonia : RecMonotonia := by
  intro hRH t
  have hne : ∀ σ : ℝ, 1 / 2 < σ → riemannXi (σ + t * I) ≠ 0 := fun σ hσ h => by
    have hZ := (xi_eq_zero_iff_Z _).mp h
    have := re_de_RH hRH hZ
    simp at this
    linarith
  set f : ℝ → ℝ := fun σ => Real.log ‖riemannXi (σ + t * I)‖ with hf
  have hcont : ContinuousOn f (Ioi (1 / 2)) := fun σ hσ =>
    (deriv_log_norm σ t (hne σ hσ)).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f (Ioi (1 / 2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi _) hcont fun σ hσ => ?_
    rw [interior_Ioi] at hσ
    rw [(deriv_log_norm σ t (hne σ hσ)).deriv]
    exact Lg_pos hRH (by simpa using hσ) (hne σ hσ)
  intro a ha b hb hab
  have h := hmono ha hb hab
  have ea : ‖riemannXi (a + t * I)‖ = Real.exp (f a) :=
    (Real.exp_log (norm_pos_iff.mpr (hne a ha))).symm
  have eb : ‖riemannXi (b + t * I)‖ = Real.exp (f b) :=
    (Real.exp_log (norm_pos_iff.mpr (hne b hb))).symm
  show ‖riemannXi (a + t * I)‖ < ‖riemannXi (b + t * I)‖
  rw [ea, eb]
  exact Real.exp_lt_exp.mpr h

/-! ## 4. As duas equivalências, sem hipóteses -/

/-- **`Re ξ′/ξ ≥ 0` em `Re s > ½` (fora dos zeros) `⟺` RH.** -/
theorem positividade_iff_RH :
    (∀ s : ℂ, 1 / 2 < s.re → riemannXi s ≠ 0 → 0 ≤ Lg s) ↔ RiemannHypothesis :=
  positividade_iff_RH_de rec_lagarias

/-- **`|ξ(σ + it)|` estritamente crescente em `σ > ½` para todo `t` `⟺` RH.** -/
theorem monotonia_iff_RH :
    (∀ t : ℝ, StrictMonoOn (fun σ : ℝ => ‖riemannXi (σ + t * I)‖) (Ioi (1 / 2))) ↔ RiemannHypothesis :=
  monotonia_iff_RH_de rec_monotonia

end ATK.ZeroClasses.LagariasHadamard

#print axioms ATK.ZeroClasses.LagariasHadamard.Pcan_localmente
#print axioms ATK.ZeroClasses.LagariasHadamard.logDeriv_E1
#print axioms ATK.ZeroClasses.LagariasHadamard.summable_logDeriv
#print axioms ATK.ZeroClasses.LagariasHadamard.logDeriv_xi_eq
#print axioms ATK.ZeroClasses.LagariasHadamard.summable_re
#print axioms ATK.ZeroClasses.LagariasHadamard.Lg_eq
#print axioms ATK.ZeroClasses.LagariasHadamard.re_de_RH
#print axioms ATK.ZeroClasses.LagariasHadamard.termo_sob_RH
#print axioms ATK.ZeroClasses.LagariasHadamard.Lg_sob_RH
#print axioms ATK.ZeroClasses.LagariasHadamard.rec_lagarias
#print axioms ATK.ZeroClasses.LagariasHadamard.Lg_pos
#print axioms ATK.ZeroClasses.LagariasHadamard.rec_monotonia
#print axioms ATK.ZeroClasses.LagariasHadamard.positividade_iff_RH
#print axioms ATK.ZeroClasses.LagariasHadamard.monotonia_iff_RH
