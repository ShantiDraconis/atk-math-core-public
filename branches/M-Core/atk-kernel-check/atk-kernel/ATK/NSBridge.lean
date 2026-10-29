import Mathlib
import ATK.Exact
import ATK.FCNavierStokes

/-!
# ATK — Ponte: enunciado (C) da OpenAI / Formal Conjectures  ⇒  `ATK.Exact.ClayC`

Em 8/9/2026 a OpenAI publicou (`github.com/openai/NavierStokesAndEuler`, commit f9e8bc5) uma
formalização Lean de `NavierStokes.Comparator.navier_stokes_breakdown_R3`, cujo tipo é
`FCBreakdownR3` abaixo — a alternativa (C) do Clay escrita com as definições do desafio Comparator
(Formal Conjectures). O ATK tem o seu próprio enunciado `ATK.Exact.ClayC`, com outras definições
(derivadas parciais `pd`, `div3`, `lap3`, `grad3`, `conv3`, energia por `lintegral`, tempo antes do
espaço). Este arquivo PROVA, no kernel e só com Mathlib, que

  `clayC_of_fc : FCBreakdownR3 → ATK.Exact.ClayC`.

Ou seja: se o teorema deles está correto, o nosso alvo oficial (C) está provado. Isso NÃO verifica
a prova deles (816 arquivos, ~412 mil linhas, Lean v4.34.0-rc2); só garante que as duas
formalizações do enunciado dizem a mesma coisa na direção necessária. A verificação externa é o
passo `nsbridge-external` (manual).

Peças (todas sem hipótese de conjectura):
* `conv3_eq`: `(v·∇)v = Dv(x)·v(x)`; `grad3_eq`: gradiente por coordenadas = `gradient`;
  `lap3_eq`: Laplaciano por derivadas parciais = `Δ` da Mathlib (para `v` suave);
  `div3_eq`: divergência por coordenadas = traço de `Dv(x)` (para `v` diferenciável).
* `rapidDecay_of_fc`, `forceDecay_of_fc`, `smoothForce_of_fc`: as condições de dado e força deles
  implicam as nossas (expoente real ⇒ natural; troca `(x,t) ↔ (t,x)` é isometria).
* `solution_of_classical`: toda solução no sentido ATK é solução no sentido deles.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped ContDiff Laplacian InnerProductSpace

namespace ATK.NSBridge

open ATK.Exact (R3 e pd div3 lap3 grad3 conv3)

/-- O enunciado (C) exatamente como o tipo de `NavierStokes.Comparator.navier_stokes_breakdown_R3`. -/
def FCBreakdownR3 : Prop :=
  ∀ (nu : ℝ), nu > 0 → ∃ (u₀ : R3 → R3) (f : R3 → ℝ → R3),
    NavierStokes.Comparator.InitialVelocityConditionDecay u₀ ∧
    NavierStokes.Comparator.ForceConditionDecay f ∧
    ¬ (∃ v p, NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn nu u₀ f v p)

/-! ## Operadores: coordenadas ATK = operadores intrínsecos da Mathlib -/

/-- `w = Σⱼ wⱼ eⱼ`. -/
theorem sum_single (w : R3) : ∑ j, w j • e j = w := by
  have h := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
  simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using h

/-- Termo convectivo: `Σⱼ vⱼ ∂ⱼ v = Dv(x) (v(x))`. -/
theorem conv3_eq (v : R3 → R3) (x : R3) : conv3 v x = fderiv ℝ v x (v x) := by
  conv_rhs => rw [← sum_single (v x)]
  rw [map_sum]
  simp only [map_smul]
  rfl

/-- Gradiente por coordenadas = `gradient` da Mathlib. -/
theorem grad3_eq (q : R3 → ℝ) (x : R3) : grad3 q x = gradient q x := by
  conv_rhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr' (gradient q x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_apply, real_inner_comm, inner_gradient_left] <;> rfl

/-- Derivada de `y ↦ c(y) w` (com `c` diferenciável a valores em operadores). -/
theorem fderiv_apply_const {c : R3 → (R3 →L[ℝ] R3)} {x : R3} (hc : DifferentiableAt ℝ c x)
    (w w' : R3) : fderiv ℝ (fun y => c y w) x w' = fderiv ℝ c x w' w := by
  rw [fderiv_clm_apply hc (differentiableAt_const w)]
  simp

/-- Laplaciano por derivadas parciais = `Δ` da Mathlib, para `v` suave. -/
theorem lap3_eq (v : R3 → R3) (hv : ContDiff ℝ ∞ v) (x : R3) : lap3 v x = Δ v x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ v) x :=
    ((contDiff_infty_iff_fderiv.1 hv).2.differentiable (by simp)) x
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis v
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    EuclideanSpace.basisFun_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  show fderiv ℝ (fun y => fderiv ℝ v y (e i)) x (e i) = _
  rw [fderiv_apply_const hd]

/-- Derivada de uma coordenada. -/
theorem fderiv_coord {v : R3 → R3} {x : R3} (hv : DifferentiableAt ℝ v x) (i : Fin 3) (w : R3) :
    fderiv ℝ (fun y => v y i) x w = fderiv ℝ v x w i := by
  have h := ((EuclideanSpace.proj i : R3 →L[ℝ] ℝ).hasFDerivAt.comp x hv.hasFDerivAt).fderiv
  have hfun : (fun y => v y i) = (EuclideanSpace.proj i : R3 →L[ℝ] ℝ) ∘ v := by
    funext y
    first
      | rfl
      | simp
  rw [hfun, h] <;> first
    | rfl
    | simp

/-- Divergência por coordenadas = traço de `Dv(x)`. -/
theorem div3_eq (v : R3 → R3) (x : R3) (hv : DifferentiableAt ℝ v x) :
    div3 v x = NavierStokes.Comparator.divergence v x := by
  unfold NavierStokes.Comparator.divergence
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]
  show fderiv ℝ (fun y => v y i) x (e i) = _
  rw [fderiv_coord hv]
  simp

/-! ## Regularidade e troca de variáveis `(t, x) ↔ (x, t)` -/

/-- Fatias no tempo de uma função suave em `[0,∞) × ℝ³` são suaves em `ℝ³`. -/
theorem slice_contDiff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u : ℝ → R3 → F}
    (h : ContDiffOn ℝ ∞ (fun z : ℝ × R3 => u z.1 z.2) (Ici 0 ×ˢ univ)) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (u t) := by
  have hm : MapsTo (fun x : R3 => (t, x)) univ (Ici 0 ×ˢ univ) := fun x _ =>
    Set.mk_mem_prod ht (mem_univ x)
  have h2 := h.comp ((contDiff_const (c := t)).prodMk contDiff_id).contDiffOn hm
  exact contDiffOn_univ.mp h2

/-- Troca das coordenadas preserva suavidade (com o domínio trocado). -/
theorem contDiffOn_swap {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E₁ × E₂ → F} {s : Set E₁} {t : Set E₂} (h : ContDiffOn ℝ ∞ g (s ×ˢ t)) :
    ContDiffOn ℝ ∞ (fun p : E₂ × E₁ => g (p.2, p.1)) (t ×ˢ s) :=
  h.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hp => Set.mk_mem_prod hp.2 hp.1)

/-! ## Dado e força -/

theorem rapidDecay_of_fc {u0 : R3 → R3}
    (h : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ m u0 x‖ ≤ C / (1 + ‖x‖) ^ K) :
    ATK.Exact.RapidDecay u0 := by
  intro k K
  obtain ⟨C, hC⟩ := h k K
  refine ⟨C, fun x => ?_⟩
  have hpos : (0 : ℝ) < (1 + ‖x‖) ^ (K : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hb := hC x
  rw [le_div_iff₀ hpos] at hb
  rw [← Real.rpow_natCast]
  calc (1 + ‖x‖) ^ (K : ℝ) * ‖iteratedFDeriv ℝ k u0 x‖
      = ‖iteratedFDeriv ℝ k u0 x‖ * (1 + ‖x‖) ^ (K : ℝ) := mul_comm _ _
    _ ≤ C := hb

theorem smoothForce_of_fc {f : R3 → ℝ → R3}
    (h : ContDiffOn ℝ ∞ (↿f) ((univ : Set R3) ×ˢ Ici (0 : ℝ))) :
    ATK.Exact.SmoothForce (fun t x => f x t) :=
  contDiffOn_swap h

theorem forceDecay_of_fc {f : R3 → ℝ → R3} (hf : NavierStokes.Comparator.ForceConditionDecay f) :
    ATK.Exact.ForceDecay (fun t x => f x t) := by
  intro k K
  obtain ⟨C, hC⟩ := hf.decay k K
  refine ⟨C, fun t ht x => ?_⟩
  set g := LinearIsometryEquiv.prodComm ℝ ℝ R3 with hg
  have hs : UniqueDiffOn ℝ ((univ : Set R3) ×ˢ Ici (0 : ℝ)) :=
    uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)
  have hgx : g (t, x) = (x, t) := by
    first
      | rfl
      | simp [hg]
  have hx : g (t, x) ∈ (univ : Set R3) ×ˢ Ici (0 : ℝ) := by
    rw [hgx]
    exact Set.mk_mem_prod (mem_univ x) ht
  have key := g.norm_iteratedFDerivWithin_comp_right (↿f) hs hx k
  have hset : g ⁻¹' ((univ : Set R3) ×ˢ Ici (0 : ℝ)) = Ici (0 : ℝ) ×ˢ (univ : Set R3) := by
    ext ⟨a, b⟩
    simp [hg, and_comm]
  have hfun : (↿f) ∘ g = fun z : ℝ × R3 => f z.2 z.1 := by
    funext z
    first
      | rfl
      | simp [hg]
  rw [hset, hgx, hfun] at key
  show (1 + ‖x‖ + t) ^ K *
    ‖iteratedFDerivWithin ℝ k (fun z : ℝ × R3 => f z.2 z.1) (Ici 0 ×ˢ univ) (t, x)‖ ≤ C
  rw [key]
  have hpos : (0 : ℝ) < (1 + ‖x‖ + t) ^ (K : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hb := hC x t ht
  rw [le_div_iff₀ hpos] at hb
  rw [← Real.rpow_natCast]
  calc (1 + ‖x‖ + t) ^ (K : ℝ) * ‖iteratedFDerivWithin ℝ k (↿f) (univ ×ˢ Ici 0) (x, t)‖
      = ‖iteratedFDerivWithin ℝ k (↿f) (univ ×ˢ Ici 0) (x, t)‖ * (1 + ‖x‖ + t) ^ (K : ℝ) :=
        mul_comm _ _
    _ ≤ C := hb

/-! ## Soluções: toda solução ATK é solução no sentido deles -/

theorem solution_of_classical {ν : ℝ} {u0 : R3 → R3} {f : R3 → ℝ → R3} {u : ℝ → R3 → R3}
    {p : ℝ → R3 → ℝ} (hns : ATK.Exact.NSClassical ν u0 (fun t x => f x t) u p)
    (hbe : ATK.Exact.BoundedEnergy u) :
    NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn ν u0 f
      (fun x t => u t x) (fun x t => p t x) := by
  obtain ⟨C, hC⟩ := hbe
  have hcont : ∀ t, 0 ≤ t → Continuous (u t) := fun t ht =>
    (slice_contDiff hns.smooth_u ht).continuous
  have hsq : ∀ t, 0 ≤ t → ∀ x, ‖(‖u t x‖ ^ 2 : ℝ)‖ₑ = ‖u t x‖ₑ ^ 2 := by
    intro t _ x
    simp [enorm_pow]
  exact
    { navier_stokes := by
        intro x t ht
        have hm := hns.momentum t ht x
        rw [conv3_eq, lap3_eq (u t) (slice_contDiff hns.smooth_u ht), grad3_eq] at hm
        exact hm
      div_free := by
        intro x t ht
        show NavierStokes.Comparator.divergence (u t) x = 0
        rw [← div3_eq (u t) x ((slice_contDiff hns.smooth_u ht).differentiable (by simp) x)]
        exact hns.incompressible t ht x
      initial_condition := fun x => hns.initial x
      velocity_smooth := contDiffOn_swap hns.smooth_u
      pressure_smooth := contDiffOn_swap hns.smooth_p
      integrable := by
        intro t ht
        have hmeas : AEStronglyMeasurable (fun x => ‖u t x‖) volume :=
          (continuous_norm.comp (hcont t ht)).aestronglyMeasurable
        rw [memLp_two_iff_integrable_sq hmeas]
        refine ⟨((continuous_norm.comp (hcont t ht)).pow 2).aestronglyMeasurable, ?_⟩
        show ∫⁻ x, ‖(‖u t x‖ ^ 2 : ℝ)‖ₑ < ⊤
        simp only [hsq t ht]
        exact lt_of_le_of_lt (hC t ht) ENNReal.ofReal_lt_top
      globally_bounded_energy := by
        refine ⟨|C| + 1, fun t ht => ?_⟩
        have hm2 : AEStronglyMeasurable (fun x => ‖u t x‖ ^ 2) volume :=
          ((continuous_norm.comp (hcont t ht)).pow 2).aestronglyMeasurable
        show ∫ x, ‖u t x‖ ^ 2 < |C| + 1
        rw [integral_eq_lintegral_of_nonneg_ae
          (Eventually.of_forall fun x => (show (0 : ℝ) ≤ ‖u t x‖ ^ 2 from sq_nonneg _)) hm2]
        have h1 : ∫⁻ x, ENNReal.ofReal (‖u t x‖ ^ 2) = ∫⁻ x, ‖u t x‖ₑ ^ 2 := by
          congr 1
          funext x
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
        rw [h1]
        have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC t ht)
        rw [ENNReal.toReal_ofReal'] at h3
        have h4 : max C 0 ≤ |C| := max_le (le_abs_self C) (abs_nonneg C)
        linarith }

/-! ## A ponte -/

/-- **Ponte (C).** O enunciado (C) no formato Formal Conjectures/OpenAI implica o alvo oficial
do ATK `ClayC`. Combinado com uma verificação externa de
`NavierStokes.Comparator.navier_stokes_breakdown_R3`, fecha a linha NS do portão por (C). -/
theorem clayC_of_fc (h : FCBreakdownR3) : ATK.Exact.ClayC := by
  intro ν hν
  obtain ⟨u0, f, hu0, hf, hno⟩ := h ν hν
  refine ⟨u0, fun t x => f x t, hu0.smooth, fun x => ?_, rapidDecay_of_fc hu0.decay,
    smoothForce_of_fc hf.smooth, forceDecay_of_fc hf, ?_⟩
  · rw [div3_eq u0 x ((hu0.smooth.differentiable (by simp)) x)]
    exact hu0.div_free x
  · rintro ⟨u, p, hns, hbe⟩
    exact hno ⟨fun x t => u t x, fun x t => p t x, solution_of_classical hns hbe⟩

/-- Consequência: com (C) deles, a disjunção oficial `NavierStokes` vale por (C) — e, mais
importante, a DECISÃO exigida pelo portão (`ClayC` como declaração) fica disponível. -/
theorem navierStokes_of_fc (h : FCBreakdownR3) : ATK.Exact.NavierStokes :=
  Or.inr (Or.inr (Or.inl (clayC_of_fc h)))

end ATK.NSBridge

end

#print axioms ATK.NSBridge.sum_single
#print axioms ATK.NSBridge.conv3_eq
#print axioms ATK.NSBridge.grad3_eq
#print axioms ATK.NSBridge.fderiv_apply_const
#print axioms ATK.NSBridge.lap3_eq
#print axioms ATK.NSBridge.fderiv_coord
#print axioms ATK.NSBridge.div3_eq
#print axioms ATK.NSBridge.slice_contDiff
#print axioms ATK.NSBridge.contDiffOn_swap
#print axioms ATK.NSBridge.rapidDecay_of_fc
#print axioms ATK.NSBridge.smoothForce_of_fc
#print axioms ATK.NSBridge.forceDecay_of_fc
#print axioms ATK.NSBridge.solution_of_classical
#print axioms ATK.NSBridge.clayC_of_fc
#print axioms ATK.NSBridge.navierStokes_of_fc
