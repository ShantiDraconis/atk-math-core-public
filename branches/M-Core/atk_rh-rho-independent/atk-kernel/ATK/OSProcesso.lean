import ATK.OSTransferencia
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# ATK — B7: de uma medida euclidiana positiva por reflexão aos dados OS

Camada OS-0 do ataque a B7. Uma **medida euclidiana estacionária e positiva por reflexão**
(`ProcessoOS`): uma probabilidade `μ` num espaço `X` (para Yang–Mills, as configurações de campo em
`S′(ℝ⁴)`), translações temporais `τ_t` e uma reflexão temporal `θ` que preservam `μ`, com
`θ τ_t = τ_{−t} θ`, e uma álgebra `A` de observáveis limitadas de tempo positivo, invariante pelas
translações de tempo positivo, com a **positividade por reflexão** `∫ conj(f ∘ θ) f dμ ≥ 0`.

* `dados`: `B(f, g) = ∫ conj(f ∘ θ) g dμ`, `S(t) f = f ∘ τ_t`, `Ω = 1` formam `DadosOS`
  (hermiticidade pela invariância sob `θ`, simetria de `S(t)` pela invariância sob `τ_t`,
  limitação pela de `f`);
* `lacuna_processo`, `vacuo_unico_processo`: **mistura exponencial** `|∫ conj(f ∘ θ)(g ∘ τ_t) − ∫ conj(f ∘ θ) ∫ g| ≤ C e^{−m t}`
  ⇒ a matriz de transferência reconstruída tem lacuna `≥ m` no complemento do vácuo, e o vácuo
  é o único vetor invariante.

Junto com `ATK.OSTransferencia` e `ATK.OSLacuna`: medida euclidiana positiva por reflexão com
mistura exponencial ⇒ espaço de Hilbert, `e^{−tH}` e lacuna — a parte temporal da ponte
`OSReconstruction`. **CLOSED_MATH continua false.**
-/

open MeasureTheory Filter
open scoped ComplexConjugate InnerProductSpace

namespace ATK.OSProcesso

/-- **Medida euclidiana estacionária e positiva por reflexão.** -/
structure ProcessoOS (X : Type*) [MeasurableSpace X] where
  μ : Measure X
  prob : IsProbabilityMeasure μ
  /-- Translações temporais. -/
  τ : ℝ → X ≃ᵐ X
  τ_mp : ∀ t, MeasurePreserving (τ t) μ μ
  τ_zero : ∀ x, τ 0 x = x
  τ_add : ∀ s t x, τ (s + t) x = τ t (τ s x)
  /-- Reflexão temporal. -/
  θ : X ≃ᵐ X
  θ_mp : MeasurePreserving θ μ μ
  θ_θ : ∀ x, θ (θ x) = x
  θ_τ : ∀ t x, θ (τ t x) = τ (-t) (θ x)
  /-- Observáveis de tempo positivo. -/
  A : Submodule ℂ (X → ℂ)
  A_meas : ∀ f ∈ A, Measurable f
  A_bdd : ∀ f ∈ A, ∃ C, ∀ x, ‖f x‖ ≤ C
  A_τ : ∀ t, 0 ≤ t → ∀ f ∈ A, (fun x => f (τ t x)) ∈ A
  A_one : (fun _ => (1 : ℂ)) ∈ A
  /-- **Positividade por reflexão.** -/
  rp : ∀ f ∈ A, 0 ≤ (∫ x, conj (f (θ x)) * f x ∂μ).re

namespace ProcessoOS

variable {X : Type*} [MeasurableSpace X] (P : ProcessoOS X)

/-- `B(f, g) = ∫ conj(f ∘ θ) g dμ`. -/
noncomputable def B (f g : X → ℂ) : ℂ := ∫ x, conj (f (P.θ x)) * g x ∂P.μ

theorem integrable_B {f g : X → ℂ} (hf : f ∈ P.A) (hg : g ∈ P.A) :
    Integrable (fun x => conj (f (P.θ x)) * g x) P.μ := by
  haveI := P.prob
  obtain ⟨C, hC⟩ := P.A_bdd f hf
  obtain ⟨D, hD⟩ := P.A_bdd g hg
  have hm : Measurable fun x => conj (f (P.θ x)) * g x :=
    (Complex.continuous_conj.measurable.comp ((P.A_meas f hf).comp P.θ.measurable)).mul
      (P.A_meas g hg)
  refine Integrable.of_bound hm.aestronglyMeasurable (C * D) (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul (hC _) (hD _) (norm_nonneg _) ((norm_nonneg _).trans (hC (P.θ x)))

theorem τ_neg (t : ℝ) (x : X) : P.τ (-t) (P.τ t x) = x := by
  rw [← P.τ_add, add_neg_cancel, P.τ_zero]

/-- `S(t) f = f ∘ τ_t` em `A`, para `t ≥ 0`. -/
noncomputable def Sc (t : ℝ) (ht : 0 ≤ t) : P.A →ₗ[ℂ] P.A where
  toFun f := ⟨fun x => (f : X → ℂ) (P.τ t x), P.A_τ t ht f f.2⟩
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

/-- As translações temporais (identidade para `t < 0`). -/
noncomputable def S (t : ℝ) : P.A →ₗ[ℂ] P.A :=
  if ht : 0 ≤ t then P.Sc t ht else LinearMap.id

theorem S_apply {t : ℝ} (ht : 0 ≤ t) (f : P.A) (x : X) :
    ((P.S t f : P.A) : X → ℂ) x = (f : X → ℂ) (P.τ t x) := by
  rw [S, dif_pos ht]
  rfl

/-- **Os dados OS da medida euclidiana.** -/
noncomputable def dados : ATK.OSTransferencia.DadosOS P.A where
  B f g := P.B f g
  conj_symm f g := by
    show conj (∫ x, conj ((g : X → ℂ) (P.θ x)) * (f : X → ℂ) x ∂P.μ) =
      ∫ x, conj ((f : X → ℂ) (P.θ x)) * (g : X → ℂ) x ∂P.μ
    rw [← integral_conj]
    have h := P.θ_mp.integral_comp'
      (fun y => (g : X → ℂ) y * conj ((f : X → ℂ) (P.θ y)))
    simp only [P.θ_θ] at h
    simp only [map_mul, Complex.conj_conj]
    rw [h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  pos f := P.rp f f.2
  add_left f f' g := by
    show ∫ x, conj (((f : X → ℂ) + (f' : X → ℂ)) (P.θ x)) * (g : X → ℂ) x ∂P.μ =
      (∫ x, conj ((f : X → ℂ) (P.θ x)) * (g : X → ℂ) x ∂P.μ) +
        ∫ x, conj ((f' : X → ℂ) (P.θ x)) * (g : X → ℂ) x ∂P.μ
    rw [← integral_add (P.integrable_B f.2 g.2) (P.integrable_B f'.2 g.2)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, map_add]
    ring
  smul_left c f g := by
    show ∫ x, conj ((c • (f : X → ℂ)) (P.θ x)) * (g : X → ℂ) x ∂P.μ =
      conj c * ∫ x, conj ((f : X → ℂ) (P.θ x)) * (g : X → ℂ) x ∂P.μ
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  S := P.S
  S_zero := by
    ext f x
    rw [S_apply P le_rfl, P.τ_zero]
    rfl
  S_add s t hs ht := by
    ext f x
    rw [LinearMap.comp_apply, S_apply P (add_nonneg hs ht), S_apply P hs, S_apply P ht,
      P.τ_add]
  S_symm t ht f g := by
    show ∫ x, conj ((f : X → ℂ) (P.θ x)) * ((P.S t g : P.A) : X → ℂ) x ∂P.μ =
      ∫ x, conj (((P.S t f : P.A) : X → ℂ) (P.θ x)) * (g : X → ℂ) x ∂P.μ
    simp only [S_apply P ht]
    -- `τ_t θ = θ τ_{−t}` e a invariância sob `τ_t`
    have e1 : ∀ x, P.τ t (P.θ x) = P.θ (P.τ (-t) x) := by
      intro x
      rw [P.θ_τ, neg_neg]
    simp only [e1]
    have h := (P.τ_mp t).integral_comp'
      (fun y => conj ((f : X → ℂ) (P.θ (P.τ (-t) y))) * (g : X → ℂ) y)
    simp only [τ_neg] at h
    exact h
  S_bdd f := by
    haveI := P.prob
    obtain ⟨C, hC⟩ := P.A_bdd f f.2
    refine ⟨C * C, 0, fun t ht => ?_⟩
    rw [pow_zero, mul_one]
    refine (Complex.re_le_norm _).trans ?_
    show ‖∫ x, conj (((P.S t f : P.A) : X → ℂ) (P.θ x)) * ((P.S t f : P.A) : X → ℂ) x ∂P.μ‖ ≤
      C * C
    have hpt : ∀ x, ‖conj (((P.S t f : P.A) : X → ℂ) (P.θ x)) * ((P.S t f : P.A) : X → ℂ) x‖ ≤
        C * C := by
      intro x
      rw [norm_mul, Complex.norm_conj, S_apply P ht, S_apply P ht]
      exact mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC (P.τ t x)))
    refine (norm_integral_le_of_norm_le_const (C := C * C) (Eventually.of_forall hpt)).trans
      (le_of_eq ?_)
    rw [probReal_univ, mul_one]
  Ω := ⟨fun _ => (1 : ℂ), P.A_one⟩
  S_Ω t ht := by
    ext x
    rw [S_apply P ht]
  B_ΩΩ := by
    haveI := P.prob
    show ∫ x, conj ((fun _ => (1 : ℂ)) (P.θ x)) * (fun _ => (1 : ℂ)) x ∂P.μ = 1
    simp

/-- A mistura exponencial da medida é o decaimento das correlações conexas dos dados OS. -/
theorem clu_de_mistura {m : ℝ}
    (hmix : ∀ f ∈ P.A, ∃ C, ∀ t, 0 ≤ t →
      ‖(∫ x, conj (f (P.θ x)) * f (P.τ t x) ∂P.μ) -
        (∫ x, conj (f (P.θ x)) ∂P.μ) * ∫ x, f x ∂P.μ‖ ≤ C * Real.exp (-(m * t))) :
    ∀ f : P.A, ∃ C, ∀ t, 0 ≤ t →
      ‖P.dados.B f (P.dados.S t f) - P.dados.B f P.dados.Ω * P.dados.B P.dados.Ω f‖ ≤
        C * Real.exp (-(m * t)) := by
  intro f
  obtain ⟨C, hC⟩ := hmix f f.2
  refine ⟨C, fun s hs => ?_⟩
  have e1 : P.dados.B f (P.dados.S s f) = ∫ x, conj ((f : X → ℂ) (P.θ x)) *
      (f : X → ℂ) (P.τ s x) ∂P.μ := by
    show ∫ x, conj ((f : X → ℂ) (P.θ x)) * ((P.S s f : P.A) : X → ℂ) x ∂P.μ = _
    simp only [S_apply P hs]
  have e2 : P.dados.B f P.dados.Ω = ∫ x, conj ((f : X → ℂ) (P.θ x)) ∂P.μ := by
    show ∫ x, conj ((f : X → ℂ) (P.θ x)) * (fun _ => (1 : ℂ)) x ∂P.μ = _
    simp
  have e3 : P.dados.B P.dados.Ω f = ∫ x, (f : X → ℂ) x ∂P.μ := by
    show ∫ x, conj ((fun _ => (1 : ℂ)) (P.θ x)) * (f : X → ℂ) x ∂P.μ = _
    simp
  rw [e1, e2, e3]
  exact hC s hs

/-- **Mistura exponencial ⇒ lacuna** para a teoria reconstruída a partir da medida euclidiana. -/
theorem lacuna_processo {m : ℝ}
    (hmix : ∀ f ∈ P.A, ∃ C, ∀ t, 0 ≤ t →
      ‖(∫ x, conj (f (P.θ x)) * f (P.τ t x) ∂P.μ) -
        (∫ x, conj (f (P.θ x)) ∂P.μ) * ∫ x, f x ∂P.μ‖ ≤ C * Real.exp (-(m * t)))
    (w : P.dados.Hil) (hw : ⟪P.dados.ι P.dados.Ω, w⟫_ℂ = 0) (t : ℝ) (ht : 0 ≤ t) :
    ‖P.dados.P t w‖ ≤ Real.exp (-(m * t)) * ‖w‖ :=
  P.dados.lacuna_OS (P.clu_de_mistura hmix) w hw t ht

/-- **Mistura exponencial ⇒ vácuo único** na teoria reconstruída. -/
theorem vacuo_unico_processo {m : ℝ} (hm : 0 < m)
    (hmix : ∀ f ∈ P.A, ∃ C, ∀ t, 0 ≤ t →
      ‖(∫ x, conj (f (P.θ x)) * f (P.τ t x) ∂P.μ) -
        (∫ x, conj (f (P.θ x)) ∂P.μ) * ∫ x, f x ∂P.μ‖ ≤ C * Real.exp (-(m * t)))
    (w : P.dados.Hil) {t : ℝ} (ht : 0 < t) (hw : P.dados.P t w = w) :
    w = ⟪P.dados.ι P.dados.Ω, w⟫_ℂ • P.dados.ι P.dados.Ω :=
  P.dados.vacuo_unico hm (P.clu_de_mistura hmix) w ht hw

end ProcessoOS

end ATK.OSProcesso

#print axioms ATK.OSProcesso.ProcessoOS.integrable_B
#print axioms ATK.OSProcesso.ProcessoOS.τ_neg
#print axioms ATK.OSProcesso.ProcessoOS.S_apply
#print axioms ATK.OSProcesso.ProcessoOS.clu_de_mistura
#print axioms ATK.OSProcesso.ProcessoOS.lacuna_processo
#print axioms ATK.OSProcesso.ProcessoOS.vacuo_unico_processo
