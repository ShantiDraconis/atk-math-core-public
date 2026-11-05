import ATK.LigacaoBSD
import ATK.CongruentCurve
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.FieldTheory.Cardinality
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# ATK — Ligação L4: testes de sanidade e a forma de Taylor do enunciado oficial

Complementa `ATK/LigacaoBSD.lean` (parte do posto de BSD sobre `WeierstrassCurve.LSeries`), sem
mudar as suas definições.

* **`a₁ = 1`** (`LFunction_um`): cada fator de Euler local da Mathlib é multiplicativo
  (`fator_multiplicativo`), logo o produto de Euler `WeierstrassCurve.LFunction` também.
* **A cláusula `≠ ⊤` de `Modularidade` é redundante** (`ordem_ne_top`,
  `modularidade_de_continuacao`): se a série L converge em algum ponto, nenhuma continuação se
  anula identicamente perto de `s = 1`. Sobra só a existência da continuação (modularidade) e a
  convergência da série (cota de Hasse), ambos teoremas publicados ausentes da Mathlib.
* **Forma de Taylor** (`ClayBSDTaylor`): o texto oficial palavra por palavra —
  `L(C, s) = c (s − 1)^r + …` com `c ≠ 0` e `r = rank C(ℚ)`. `clay_of_taylor` (sem hipóteses) e
  `taylor_iff` (com Mordell–Weil): equivale a `ClayBSD`.
* **Teste numa curva concreta**: `y² = x³ − x` (de `ATK.CongruentCurve`) é elíptica
  (`Δ = 64`), todo ponto racional tem ordem 2 (`dois_torcao`) e o posto é `0`
  (`posto_curva32`). Logo `ClayBSD` obriga `L(E, 1) ≠ 0` nessa curva (`clay_curva32`), que é o
  valor conhecido. A função nula não é continuação (`zero_nao_e_continuacao`).

Nada aqui prova BSD. Sem `sorry`, sem `axiom`.
-/

namespace ATK.LigacaoBSDTestes

open Filter Topology ATK.LigacaoBSD

/-! ## `a₁ = 1` -/

/-- Cada fator de Euler local da Mathlib é multiplicativo. -/
theorem fator_multiplicativo (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K) :
    (W.localEulerFactor R).IsMultiplicative := by
  have hc : (W.localPowerSeries R).constantCoeff = 1 := by
    simp [WeierstrassCurve.localPowerSeries, PowerSeries.constantCoeff_invOfUnit]
  unfold WeierstrassCurve.localEulerFactor
  by_cases hq : IsPrimePow (Nat.card (IsLocalRing.ResidueField R))
  · exact ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow _ hq _ hc
  · have h0 : Nat.card (IsLocalRing.ResidueField R) = 0 := by
      by_contra hne
      have : Finite (IsLocalRing.ResidueField R) := Nat.finite_of_card_ne_zero hne
      have := Fintype.ofFinite (IsLocalRing.ResidueField R)
      exact hq (by rw [Nat.card_eq_fintype_card]; exact Fintype.isPrimePow_card_of_field)
    rw [h0]
    have h1 : ArithmeticFunction.ofPowerSeries 0 (W.localPowerSeries R) = 1 := by
      ext n
      simp [ArithmeticFunction.ofPowerSeries, hc]
    rw [h1]
    exact ArithmeticFunction.isMultiplicative_one

/-- `a₁ = 1`: o primeiro coeficiente de `L(E, s)`. -/
theorem LFunction_um (W : WeierstrassCurve ℚ) : W.LFunction 1 = 1 := by
  have key : W.LFunction.IsMultiplicative := by
    unfold WeierstrassCurve.LFunction
    exact ArithmeticFunction.isMultiplicative_eulerProduct _ fun _ => fator_multiplicativo _ _
  exact key.map_one

/-- Coeficientes `aₙ` de `L(E, s)`, em `ℂ`. -/
noncomputable def coef (W : WeierstrassCurve ℚ) : ℕ → ℂ := fun n => (W.LFunction n : ℂ)

theorem lseries_coef (W : WeierstrassCurve ℚ) (s : ℂ) : W.LSeries s = LSeries (coef W) s := rfl

theorem coef_um (W : WeierstrassCurve ℚ) : coef W 1 = 1 := by
  simp [coef, LFunction_um]

/-! ## A continuação não se anula identicamente -/

/-- Se a série L de `W` converge (absolutamente) em algum ponto, nenhuma continuação se anula
identicamente perto de `s = 1`: a ordem em `s = 1` é finita. -/
theorem ordem_ne_top {W : WeierstrassCurve ℚ} {F : ℂ → ℂ} {s₀ : ℂ}
    (hconv : LSeriesSummable (coef W) s₀) (hF : Continuacao W F) : analyticOrderAt F 1 ≠ ⊤ := by
  intro htop
  have hloc : ∀ᶠ z in 𝓝 (1 : ℂ), F z = 0 := analyticOrderAt_eq_top.mp htop
  have hA : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.1.analyticAt z
  have h0 : F = fun _ => 0 :=
    AnalyticOnNhd.eq_of_eventuallyEq hA (fun _ _ => analyticAt_const) hloc
  have hab : LSeries.abscissaOfAbsConv (coef W) < ⊤ :=
    hconv.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
  have ht := LSeries.tendsto_atTop hab
  have hz : (fun x : ℝ => LSeries (coef W) x) =ᶠ[atTop] fun _ => 0 := by
    filter_upwards [eventually_gt_atTop (3 / 2 : ℝ)] with x hx
    have hx' : (3 / 2 : ℝ) < (x : ℂ).re := by simpa using hx
    show LSeries (coef W) x = 0
    rw [← lseries_coef, ← hF.2 x hx', h0]
  have h1 : coef W 1 = 0 := tendsto_nhds_unique ht (tendsto_const_nhds.congr' hz.symm)
  rw [coef_um] at h1
  exact one_ne_zero h1

/-- A hipótese `Modularidade` de `ATK.LigacaoBSD` segue só da existência da continuação e da
convergência da série em algum ponto: a cláusula `≠ ⊤` está provada. -/
theorem modularidade_de_continuacao
    (hCont : ∀ W : WeierstrassCurve ℚ, W.IsElliptic → ∃ F, Continuacao W F)
    (hConv : ∀ W : WeierstrassCurve ℚ, W.IsElliptic → ∃ s₀, LSeriesSummable (coef W) s₀) :
    Modularidade := by
  intro W hW
  obtain ⟨F, hF⟩ := hCont W hW
  obtain ⟨s₀, hs₀⟩ := hConv W hW
  exact ⟨F, hF, ordem_ne_top hs₀ hF⟩

/-- Teste: onde a série converge, a função nula não é continuação de `L(E, s)`. -/
theorem zero_nao_e_continuacao {W : WeierstrassCurve ℚ} {s₀ : ℂ}
    (hconv : LSeriesSummable (coef W) s₀) : ¬ Continuacao W (fun _ => 0) := fun h =>
  ordem_ne_top hconv h (analyticOrderAt_eq_top.mpr (Eventually.of_forall fun _ => rfl))

/-! ## A forma de Taylor do texto oficial -/

/-- **O texto oficial do Clay, palavra por palavra**: para toda curva elíptica `C/ℚ`,
`L(C, s) = c (s − 1)^r + termos de ordem maior`, com `c ≠ 0` e `r = rank C(ℚ)`. -/
def ClayBSDTaylor : Prop :=
  ∀ W : WeierstrassCurve ℚ, W.IsElliptic → ∃ F : ℂ → ℂ, Continuacao W F ∧
    ∃ r : ℕ, postoMW W = r ∧ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧
      ∀ᶠ s in 𝓝 (1 : ℂ), F s = (s - 1) ^ r * g s

theorem taylor_iff_ordem {W : WeierstrassCurve ℚ} {F : ℂ → ℂ} (hF : Continuacao W F) (r : ℕ) :
    (∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧ ∀ᶠ s in 𝓝 (1 : ℂ), F s = (s - 1) ^ r * g s) ↔
      analyticOrderAt F 1 = r := by
  rw [(hF.1.analyticAt 1).analyticOrderAt_eq_natCast]
  simp only [smul_eq_mul]

/-- A forma de Taylor implica `ClayBSD` (sem hipóteses). -/
theorem clay_of_taylor : ClayBSDTaylor → ClayBSD := by
  intro h W hW
  obtain ⟨F, hF, r, hr, hg⟩ := h W hW
  exact ⟨F, hF, by rw [hr]; exact (taylor_iff_ordem hF r).mp hg⟩

/-- Com Mordell–Weil (posto finito), `ClayBSD` implica a forma de Taylor. -/
theorem taylor_of_clay (hMW : MordellWeil) : ClayBSD → ClayBSDTaylor := by
  intro h W hW
  obtain ⟨F, hF, hord⟩ := h W hW
  refine ⟨F, hF, (postoMW W).toNat, (ENat.natCast_toNat (hMW W hW)).symm, ?_⟩
  rw [taylor_iff_ordem hF, ENat.natCast_toNat (hMW W hW), hord]

/-- **Fidelidade**: com Mordell–Weil, `ClayBSD` é o texto oficial na forma de Taylor. -/
theorem taylor_iff (hMW : MordellWeil) : ClayBSDTaylor ↔ ClayBSD :=
  ⟨clay_of_taylor, taylor_of_clay hMW⟩

/-! ## Teste: `y² = x³ − x` -/

/-- `y² = x³ − x` é elíptica: `Δ = 64`. -/
theorem curva32_eliptica : ATK.CongruentCurve.E.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (by
    norm_num [ATK.CongruentCurve.E, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈])⟩

/-- Todo ponto racional de `y² = x³ − x` tem ordem dividindo 2. -/
theorem dois_torcao (P : ATK.CongruentCurve.E.toAffine.Point) : P + P = 0 := by
  rcases ATK.CongruentCurve.E_point_cases P with rfl | ⟨x, h, rfl, -⟩
  · exact add_zero 0
  · exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq (by simp [ATK.CongruentCurve.E])

/-- `posto(y² = x³ − x) = 0`, calculado no grupo de pontos da Mathlib. -/
theorem posto_curva32 : postoMW ATK.CongruentCurve.E = 0 := by
  have h : Module.rank ℤ ATK.CongruentCurve.E.toAffine.Point = 0 := by
    rw [rank_eq_zero_iff]
    intro P
    exact ⟨2, two_ne_zero, by rw [two_zsmul]; exact dois_torcao P⟩
  unfold postoMW
  rw [h]
  simp

/-- Teste: na curva `y² = x³ − x`, o enunciado do Clay obriga `L(E, 1) ≠ 0`. -/
theorem clay_curva32 (h : ClayBSD) {F : ℂ → ℂ} (hF : Continuacao ATK.CongruentCurve.E F) :
    F 1 ≠ 0 := by
  obtain ⟨G, hG, hord⟩ := h _ curva32_eliptica
  rw [continuacao_unica hF hG]
  intro h0
  have hpos := (zero_iff_posto_pos hG hord).mp h0
  rw [posto_curva32] at hpos
  exact lt_irrefl _ hpos

end ATK.LigacaoBSDTestes

#print axioms ATK.LigacaoBSDTestes.fator_multiplicativo
#print axioms ATK.LigacaoBSDTestes.LFunction_um
#print axioms ATK.LigacaoBSDTestes.lseries_coef
#print axioms ATK.LigacaoBSDTestes.coef_um
#print axioms ATK.LigacaoBSDTestes.ordem_ne_top
#print axioms ATK.LigacaoBSDTestes.modularidade_de_continuacao
#print axioms ATK.LigacaoBSDTestes.zero_nao_e_continuacao
#print axioms ATK.LigacaoBSDTestes.taylor_iff_ordem
#print axioms ATK.LigacaoBSDTestes.clay_of_taylor
#print axioms ATK.LigacaoBSDTestes.taylor_of_clay
#print axioms ATK.LigacaoBSDTestes.taylor_iff
#print axioms ATK.LigacaoBSDTestes.curva32_eliptica
#print axioms ATK.LigacaoBSDTestes.dois_torcao
#print axioms ATK.LigacaoBSDTestes.posto_curva32
#print axioms ATK.LigacaoBSDTestes.clay_curva32
