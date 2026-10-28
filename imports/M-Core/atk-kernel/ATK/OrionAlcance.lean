/-
ATK — O alcance real da análise Orion: tudo o que ela atinge, provado ou refutado.

1. Teorema-mãe UCIF = ponto fixo de Banach: `ucif_fixed_point` (da Mathlib).
2. Regularização dual: `regularizacao_e_identidade` — C_ε⁻¹ C_ε = 1 sempre que a
   inversa existe, logo "I_Ω = lim C_ε⁻¹ C_ε" é a IDENTIDADE, não um estado
   indeterminado.  Não-go para a Seção 2 do núcleo.
3. Instância RH: `critical_line_iff_symmetric` — Re ρ = ½ ⇔ 1 − ρ̄ = ρ.  É exatamente
   o que Fix(P_Ω^RH) teria de fixar; nada sobre ζ.
4. HREF L2/L3 (focalização): `focusing_blowup_bound` — Θ' ≤ −aΘ² com Θ(t₀) < 0 força
   T ≤ t₀ + 1/(a|Θ(t₀)|).  Versão com absorção θ < 1: `focusing_blowup_bound_absorb`.
   São as fórmulas `ode_focusing_time_bound_L2/L3` do repositório, agora teoremas.
5. Classificação collapse/gap/boundedness sobre ℝ.

Nenhum destes toca O1–O8.  A Lei 6 (que a desigualdade de focalização VALE para
NS) continua OPEN; aqui prova-se só a consequência da desigualdade.
-/
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ATK.OrionAlcance

open Set

/-! ### 1. Teorema-mãe UCIF -/

/-- Se Φ é K-contração num espaço métrico completo não vazio, existe um único
ponto fixo M* e Φⁿ(M₀) → M* para todo M₀.  (Banach, via Mathlib.) -/
theorem ucif_fixed_point {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {K : NNReal} (Φ : X → X) (hΦ : ContractingWith K Φ) :
    (∃! M : X, Φ M = M) ∧
    ∀ M₀ : X, Filter.Tendsto (fun n => Φ^[n] M₀) Filter.atTop (nhds (hΦ.fixedPoint Φ)) := by
  refine ⟨⟨hΦ.fixedPoint Φ, hΦ.fixedPoint_isFixedPt, fun y hy => hΦ.fixedPoint_unique hy⟩, ?_⟩
  intro M₀
  exact hΦ.tendsto_iterate_fixedPoint M₀

/-! ### 2. Regularização dual: não-go -/

/-- C_ε⁻¹ C_ε = 1 sempre que C_ε = A + ε·1 é inversível.  O "limite" é a identidade;
não define um estado ⊥. -/
theorem regularizacao_e_identidade {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (ε : ℂ) (h : IsUnit (A + ε • (1 : Matrix n n ℂ)).det) :
    (A + ε • (1 : Matrix n n ℂ))⁻¹ * (A + ε • 1) = 1 :=
  Matrix.nonsing_inv_mul _ h

/-- Consequência: qualquer limite de C_ε⁻¹ C_ε ao longo de ε inversíveis é 1. -/
theorem regularizacao_limite_e_um {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (ε : ℕ → ℂ) (h : ∀ k, IsUnit (A + ε k • (1 : Matrix n n ℂ)).det) :
    (fun k => (A + ε k • (1 : Matrix n n ℂ))⁻¹ * (A + ε k • 1)) = fun _ => 1 := by
  funext k; exact regularizacao_e_identidade A (ε k) (h k)

/-! ### 3. Instância RH: a simetria que P_Ω^RH teria de fixar -/

/-- ρ está na reta crítica ⇔ ρ é fixo pela reflexão ρ ↦ 1 − ρ̄. -/
theorem critical_line_iff_symmetric (ρ : ℂ) :
    ρ.re = 1 / 2 ↔ 1 - (starRingEnd ℂ) ρ = ρ := by
  constructor
  · intro h
    apply Complex.ext
    · simp [Complex.sub_re, Complex.conj_re, h]; norm_num
    · simp [Complex.sub_im, Complex.conj_im]
  · intro h
    have := congrArg Complex.re h
    simp [Complex.sub_re, Complex.conj_re] at this
    linarith

/-- O par (M₊, M₋) = (s − ρ, (1 − s) − ρ̄) é simétrico sob s ↦ 1 − s̄ exatamente na reta
crítica: M₋(s) = −conj(M₊(1 − s̄)) sempre, e M₋(s) = M₊(s) · (−1) ... reduz ao lema acima. -/
theorem dual_state_symmetric (ρ : ℂ) (hρ : ρ.re = 1 / 2) (s : ℂ) :
    (1 - s) - (starRingEnd ℂ) ρ = -(s - ρ) := by
  have := (critical_line_iff_symmetric ρ).mp hρ
  linear_combination this

/-! ### 4. HREF — focalização (L2/L3) como teorema -/

/-- **Lema de focalização.**  Se Θ é derivável em [t₀, T) com Θ' ≤ −a Θ² (a > 0) e
Θ(t₀) < 0, então T ≤ t₀ + 1/(a·|Θ(t₀)|).  Em particular uma solução assim não
pode existir para sempre. -/
theorem focusing_blowup_bound (Θ Θ' : ℝ → ℝ) (t₀ T a : ℝ) (ha : 0 < a)
    (hd : ∀ t ∈ Ico t₀ T, HasDerivAt Θ (Θ' t) t)
    (hineq : ∀ t ∈ Ico t₀ T, Θ' t ≤ -a * Θ t ^ 2)
    (h0 : Θ t₀ < 0) (ht : t₀ < T) :
    T ≤ t₀ + 1 / (a * (-Θ t₀)) := by
  -- passo chave: para todo t₁ ∈ [t₀, T), t₁ < t₀ + 1/(a(−Θ t₀))
  have key : ∀ t₁ ∈ Ico t₀ T, t₁ < t₀ + 1 / (a * (-Θ t₀)) := by
    intro t₁ ht₁
    obtain ⟨h01, h1T⟩ := ht₁
    rcases eq_or_lt_of_le h01 with heq | hlt
    · have : 0 < 1 / (a * (-Θ t₀)) := by
        apply div_pos one_pos; exact mul_pos ha (by linarith)
      rw [← heq]; linarith
    -- D = Icc t₀ t₁ ⊆ Ico t₀ T
    have hD : Icc t₀ t₁ ⊆ Ico t₀ T := fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 h1T⟩
    have hcont : ContinuousOn Θ (Icc t₀ t₁) := fun s hs =>
      (hd s (hD hs)).continuousAt.continuousWithinAt
    have hint : interior (Icc t₀ t₁) = Ioo t₀ t₁ := interior_Icc
    have hdiff : DifferentiableOn ℝ Θ (interior (Icc t₀ t₁)) := by
      rw [hint]; intro s hs
      exact (hd s (hD (Ioo_subset_Icc_self hs))).differentiableAt.differentiableWithinAt
    -- Θ é antítona em D, logo Θ ≤ Θ t₀ < 0 em D
    have hanti : AntitoneOn Θ (Icc t₀ t₁) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hcont hdiff
      intro s hs; rw [hint] at hs
      have hs' := hD (Ioo_subset_Icc_self hs)
      rw [(hd s hs').deriv]
      have := hineq s hs'
      nlinarith [sq_nonneg (Θ s)]
    have hneg : ∀ s ∈ Icc t₀ t₁, Θ s < 0 := fun s hs =>
      lt_of_le_of_lt (hanti ⟨le_refl _, le_of_lt hlt⟩ hs hs.1) h0
    -- g = 1/Θ tem derivada ≥ a em D
    let g : ℝ → ℝ := fun s => (Θ s)⁻¹
    have hg : ∀ s ∈ Icc t₀ t₁, HasDerivAt g (-(Θ' s) / (Θ s) ^ 2) s := fun s hs =>
      (hd s (hD hs)).inv (hneg s hs).ne
    have hgcont : ContinuousOn g (Icc t₀ t₁) := fun s hs =>
      (hg s hs).continuousAt.continuousWithinAt
    have hgdiff : DifferentiableOn ℝ g (interior (Icc t₀ t₁)) := by
      rw [hint]; intro s hs
      exact (hg s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    have hgder : ∀ s ∈ interior (Icc t₀ t₁), a ≤ deriv g s := by
      intro s hs; rw [hint] at hs
      have hs' := Ioo_subset_Icc_self hs
      rw [(hg s hs').deriv]
      have hΘ := hneg s hs'
      have hsq : 0 < Θ s ^ 2 := by have := hΘ.ne; positivity
      rw [le_div_iff₀ hsq]
      have := hineq s (hD hs'); linarith
    have hmv := (convex_Icc t₀ t₁).mul_sub_le_image_sub_of_le_deriv hgcont hgdiff hgder
      t₀ ⟨le_refl _, le_of_lt hlt⟩ t₁ ⟨le_of_lt hlt, le_refl _⟩ (le_of_lt hlt)
    -- a(t₁ − t₀) ≤ g t₁ − g t₀ < −g t₀ = 1/(−Θ t₀)
    have hg1 : g t₁ < 0 := inv_lt_zero.mpr (hneg t₁ ⟨le_of_lt hlt, le_refl _⟩)
    have hg0 : g t₀ = -(1 / (-Θ t₀)) := by
      simp only [g]; field_simp
    have hΘ0 : 0 < -Θ t₀ := by linarith
    have h2 : a * (t₁ - t₀) < 1 / (-Θ t₀) := by linarith
    have h3 : t₁ - t₀ < 1 / (-Θ t₀) / a := by
      rw [lt_div_iff₀ ha]; linarith
    have h4 : 1 / (-Θ t₀) / a = 1 / (a * (-Θ t₀)) := by field_simp
    linarith
  -- se T > bound, então bound ∈ [t₀, T) e key dá contradição
  by_contra hcon
  have hcon : t₀ + 1 / (a * (-Θ t₀)) < T := lt_of_not_ge hcon
  have hb : t₀ + 1 / (a * (-Θ t₀)) ∈ Ico t₀ T := by
    refine ⟨?_, hcon⟩
    have : 0 < 1 / (a * (-Θ t₀)) := by apply div_pos one_pos; exact mul_pos ha (by linarith)
    linarith
  exact lt_irrefl _ (key _ hb)

/-- Versão com absorção (L3): Θ' ≤ −aΘ² + θ a Θ² com θ < 1 é Θ' ≤ −(1−θ)aΘ². -/
theorem focusing_blowup_bound_absorb (Θ Θ' : ℝ → ℝ) (t₀ T a θ : ℝ) (ha : 0 < a) (hθ : θ < 1)
    (hd : ∀ t ∈ Ico t₀ T, HasDerivAt Θ (Θ' t) t)
    (hineq : ∀ t ∈ Ico t₀ T, Θ' t ≤ -a * Θ t ^ 2 + θ * a * Θ t ^ 2)
    (h0 : Θ t₀ < 0) (ht : t₀ < T) :
    T ≤ t₀ + 1 / ((1 - θ) * a * (-Θ t₀)) := by
  have ha' : 0 < (1 - θ) * a := mul_pos (by linarith) ha
  have := focusing_blowup_bound Θ Θ' t₀ T ((1 - θ) * a) ha' hd
    (fun t ht => by have := hineq t ht; nlinarith [sq_nonneg (Θ t)]) h0 ht
  exact this

/-! ### 5. Classificação de defeitos -/

inductive DefectMode
  | collapse
  | gap
  | boundedness
  deriving DecidableEq, Repr

noncomputable def classifyDefect (defect threshold : ℝ) : DefectMode :=
  if defect = 0 then .collapse else if threshold ≤ defect then .gap else .boundedness

theorem classify_collapse_iff (d θ : ℝ) : classifyDefect d θ = .collapse ↔ d = 0 := by
  unfold classifyDefect
  by_cases h : d = 0
  · simp [h]
  · by_cases h2 : θ ≤ d <;> simp [h, h2]

theorem classify_gap_iff (d θ : ℝ) : classifyDefect d θ = .gap ↔ d ≠ 0 ∧ θ ≤ d := by
  unfold classifyDefect
  by_cases h : d = 0
  · simp [h]
  · by_cases h2 : θ ≤ d <;> simp [h, h2]

end ATK.OrionAlcance

#print axioms ATK.OrionAlcance.ucif_fixed_point
#print axioms ATK.OrionAlcance.regularizacao_e_identidade
#print axioms ATK.OrionAlcance.regularizacao_limite_e_um
#print axioms ATK.OrionAlcance.critical_line_iff_symmetric
#print axioms ATK.OrionAlcance.dual_state_symmetric
#print axioms ATK.OrionAlcance.focusing_blowup_bound
#print axioms ATK.OrionAlcance.focusing_blowup_bound_absorb
#print axioms ATK.OrionAlcance.classify_collapse_iff
#print axioms ATK.OrionAlcance.classify_gap_iff
