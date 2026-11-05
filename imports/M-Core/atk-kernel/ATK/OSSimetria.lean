import ATK.OSProcesso

/-!
# ATK — B7: simetrias euclidianas do tempo zero na teoria reconstruída

Camada OS-5 do ataque a B7. Uma **simetria** de uma medida euclidiana positiva por reflexão
(`SimetriaOS`): uma bijeção mensurável `g` que preserva `μ`, comuta com a reflexão temporal `θ` e
com as translações temporais `τ_t`, e preserva as observáveis de tempo positivo — por exemplo as
translações e rotações espaciais de `ℝ³` agindo nas configurações de campo em `S′(ℝ⁴)`.

* `U`: `g` induz uma **isometria** `U_g` do espaço de Hilbert reconstruído
  (`⟪U_g v, U_g w⟫ = ⟪v, w⟫`, pela invariância de `μ` e `θ g = g θ`);
* `U_P`: `U_g` **comuta com a matriz de transferência** `P(t) = e^{−tH}`;
* `U_Ω`: `U_g Ω = Ω`;
* `U_comp`: `U_{g₂ ∘ g₁} = U_{g₁} U_{g₂}` (representação do grupo de simetrias).

**CLOSED_MATH continua false.**
-/

open MeasureTheory Filter
open scoped ComplexConjugate InnerProductSpace

namespace ATK.OSSimetria

open ATK.OSProcesso ATK.OSTransferencia

variable {X : Type*} [MeasurableSpace X] {P : ProcessoOS X}

/-- **Uma simetria euclidiana do tempo zero.** -/
structure SimetriaOS (P : ProcessoOS X) where
  g : X ≃ᵐ X
  mp : MeasurePreserving g P.μ P.μ
  θ_g : ∀ x, P.θ (g x) = g (P.θ x)
  τ_g : ∀ t x, P.τ t (g x) = g (P.τ t x)
  A_g : ∀ f ∈ P.A, (fun x => f (g x)) ∈ P.A

namespace SimetriaOS

variable (σ : SimetriaOS P)

/-- `f ↦ f ∘ g` em `A`. -/
noncomputable def Ug : P.A →ₗ[ℂ] P.A where
  toFun f := ⟨fun x => (f : X → ℂ) (σ.g x), σ.A_g f f.2⟩
  map_add' f h := by ext x; rfl
  map_smul' c f := by ext x; rfl

theorem Ug_apply (f : P.A) (x : X) : ((σ.Ug f : P.A) : X → ℂ) x = (f : X → ℂ) (σ.g x) := rfl

/-- `B(f ∘ g, h ∘ g) = B(f, h)`. -/
theorem B_Ug (f h : P.A) : P.dados.B (σ.Ug f) (σ.Ug h) = P.dados.B f h := by
  show ∫ x, conj (((σ.Ug f : P.A) : X → ℂ) (P.θ x)) * ((σ.Ug h : P.A) : X → ℂ) x ∂P.μ =
    ∫ x, conj ((f : X → ℂ) (P.θ x)) * (h : X → ℂ) x ∂P.μ
  simp only [Ug_apply]
  have e : ∀ x, σ.g (P.θ x) = P.θ (σ.g x) := fun x => (σ.θ_g x).symm
  simp only [e]
  exact σ.mp.integral_comp' (fun y => conj ((f : X → ℂ) (P.θ y)) * (h : X → ℂ) y)

theorem norm_Ug (f : P.A) : ‖P.dados.toP (σ.Ug f)‖ = ‖P.dados.toP f‖ := by
  have h1 := P.dados.norm_pre_sq (σ.Ug f)
  have h2 := P.dados.norm_pre_sq f
  rw [B_Ug] at h1
  rw [← h2] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

/-- `U_g` em `(V, B)`. -/
noncomputable def UL : P.dados.Pre →L[ℂ] P.dados.Pre :=
  LinearMap.mkContinuous (σ.Ug : P.dados.Pre →ₗ[ℂ] P.dados.Pre) 1 (fun f => by
    rw [one_mul]; exact le_of_eq (σ.norm_Ug f))

/-- **A isometria induzida no espaço de Hilbert reconstruído.** -/
noncomputable def U : P.dados.Hil →L[ℂ] P.dados.Hil := σ.UL.completion

theorem U_ι (f : P.A) : σ.U (P.dados.ι f) = P.dados.ι (σ.Ug f) := by
  unfold U DadosOS.ι
  rw [ContinuousLinearMap.completion_apply_coe]
  rfl

theorem inner_U (v w : P.dados.Hil) : ⟪σ.U v, σ.U w⟫_ℂ = ⟪v, w⟫_ℂ := by
  refine P.dados.denseRange_ι.induction_on₂ (p := fun v w => ⟪σ.U v, σ.U w⟫_ℂ = ⟪v, w⟫_ℂ)
    (isClosed_eq (by fun_prop) (by fun_prop)) (fun f h => ?_) v w
  rw [U_ι, U_ι, DadosOS.inner_ι, DadosOS.inner_ι, B_Ug]

theorem norm_U (w : P.dados.Hil) : ‖σ.U w‖ = ‖w‖ := by
  have h1 := norm_sq_eq_re_inner (𝕜 := ℂ) (σ.U w)
  have h2 := norm_sq_eq_re_inner (𝕜 := ℂ) w
  rw [inner_U] at h1
  rw [← h2] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

/-- **`U_g` comuta com a matriz de transferência.** -/
theorem U_P (t : ℝ) (ht : 0 ≤ t) : σ.U.comp (P.dados.P t) = (P.dados.P t).comp σ.U := by
  refine P.dados.ext_ι (fun f => ?_)
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, DadosOS.P_ι _ ht, U_ι,
    U_ι, DadosOS.P_ι _ ht]
  congr 1
  ext x
  show ((P.S t f : P.A) : X → ℂ) (σ.g x) = ((P.S t (σ.Ug f) : P.A) : X → ℂ) x
  rw [ProcessoOS.S_apply P ht, ProcessoOS.S_apply P ht, Ug_apply, σ.τ_g]

/-- `U_g Ω = Ω`. -/
theorem U_Ω : σ.U (P.dados.ι P.dados.Ω) = P.dados.ι P.dados.Ω := by
  rw [U_ι]
  rfl

/-- **Representação**: `U_{g₂ ∘ g₁} = U_{g₁} U_{g₂}`. -/
theorem U_comp (σ₁ σ₂ σ₁₂ : SimetriaOS P) (h : ∀ x, σ₁₂.g x = σ₂.g (σ₁.g x)) :
    σ₁₂.U = σ₁.U.comp σ₂.U := by
  refine P.dados.ext_ι (fun f => ?_)
  rw [ContinuousLinearMap.comp_apply, U_ι, U_ι, U_ι]
  congr 1
  ext x
  rw [Ug_apply, Ug_apply, Ug_apply, h]

end SimetriaOS

end ATK.OSSimetria

#print axioms ATK.OSSimetria.SimetriaOS.Ug_apply
#print axioms ATK.OSSimetria.SimetriaOS.B_Ug
#print axioms ATK.OSSimetria.SimetriaOS.norm_Ug
#print axioms ATK.OSSimetria.SimetriaOS.U_ι
#print axioms ATK.OSSimetria.SimetriaOS.inner_U
#print axioms ATK.OSSimetria.SimetriaOS.norm_U
#print axioms ATK.OSSimetria.SimetriaOS.U_P
#print axioms ATK.OSSimetria.SimetriaOS.U_Ω
#print axioms ATK.OSSimetria.SimetriaOS.U_comp
