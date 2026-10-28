import ATK.LigacaoNS
import ATK.Externo.FCNavierStokes
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.MeasureTheory.Function.L2Space

/-!
# ATK — O enunciado (A) de Navier–Stokes do ATK contra o do formal-conjectures

A ligação L1 (`ATK/LigacaoNS.lean`) escreve o enunciado (A) do Clay com operadores próprios
(derivadas parciais `dX`, `div`, `lap`, `conv`, `grad`), dado inicial na classe de Schwartz da
Mathlib, equação imposta para `t > 0` com derivada temporal bilateral, e energia
`Integrable ∧ ∫ ≤ C`. O formal-conjectures (cópia em `ATK/Externo/FCNavierStokes.lean`) escreve
o mesmo enunciado com outros objetos: divergência como traço de `fderiv`, `Δ` e `gradient` da
Mathlib, o decaimento (4) com expoente real `K`, a equação para `t ≥ 0` com derivada temporal
lateral (`derivWithin` em `[0, ∞)`), e energia `MemLp _ 2 ∧ ∫ < E`.

Provado aqui, sem hipóteses:

* §1 os operadores coincidem: `div_eq`, `conv_eq`, `grad_eq` (sempre) e `lap_eq` (para `C²`);
* §2–3 em `ℝ³ × [0, ∞)`, cada termo da equação é contínuo em `t`, e a equação em `t = 0` segue
  da equação em `t > 0` (`ns_em_zero`) — é a observação "em `t = 0` ela segue por continuidade"
  da docstring de L1, agora provada;
* §4 classe de Schwartz com `div = 0` ⟺ `InitialVelocityConditionDecay` (`dado_iff`);
* §5 `SolucaoGlobal` ⟺ `NavierStokesExistenceAndSmoothnessRn` com força nula
  (`fc_of_atk`, `atk_of_fc`);
* §6 **`clayA_iff_fc : ClayStatementA modeloNS ↔ ExistenceAndSmoothnessR3`**.

Consequência: o alvo do ATK para Navier–Stokes é exatamente a alternativa (A) do formal-conjectures,
a mesma que a prova da OpenAI (setembro de 2026, alternativas (C) e (D), verificada no `atk-ns`)
**não** resolve. Nada aqui prova (A); a obrigação O3 continua aberta.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff Laplacian
open ATK.LigacaoNS

namespace ATK.IntegracaoFCNS

/-! ## 1. Os operadores do ATK são os da Mathlib usados pelo formal-conjectures -/

theorem div_eq (u : E3 → E3) (x : E3) : div u x = ATK.FC.NS.divergence u x := by
  rw [ATK.FC.NS.divergence, LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [div, dX, EuclideanSpace.inner_single_left]

theorem conv_eq (u : E3 → E3) (x : E3) : conv u x = fderiv ℝ u x (u x) := by
  conv_rhs => rw [← sum_coord (u x)]
  simp [conv, dX, map_sum, map_smul]

theorem grad_eq (p : E3 → ℝ) (x : E3) : grad p x = gradient p x := by
  have h : ∀ j, (gradient p x) j = fderiv ℝ p x (e j) := by
    intro j
    have := EuclideanSpace.inner_single_left j (1 : ℝ) (gradient p x)
    rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply] at this
    simpa [gradient] using this.symm
  rw [grad, ← sum_coord (gradient p x)]
  simp only [dX, h]

theorem lap_eq {f : E3 → E3} (hf : ContDiff ℝ 2 f) (x : E3) : lap f x = Δ f x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [iteratedFDeriv_two_apply]
  unfold lap dX
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  rw [fderiv_clm_apply h1 (differentiableAt_const _)]
  simp

/-! ## 2. Fatias de funções suaves em `ℝ³ × [0, ∞)` -/

section Fatias

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- O domínio `ℝ³ × [0, ∞)`. -/
abbrev Dom : Set (E3 × ℝ) := univ ×ˢ Ici 0

theorem uniqueDiffOn_dom : UniqueDiffOn ℝ Dom := uniqueDiffOn_univ.prod (uniqueDiffOn_Ici 0)

theorem mapsTo_espaco {t : ℝ} (ht : 0 ≤ t) : MapsTo (fun y : E3 => (y, t)) univ Dom :=
  fun _ _ => ⟨mem_univ _, ht⟩

theorem mapsTo_tempo (x : E3) : MapsTo (fun s : ℝ => (x, s)) (Ici 0) Dom :=
  fun _ hs => ⟨mem_univ _, hs⟩

theorem contDiff_espaco {F : E3 × ℝ → W} (hF : ContDiffOn ℝ ∞ F Dom) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ ∞ (fun y => F (y, t)) := by
  rw [← contDiffOn_univ]
  exact hF.comp (contDiffOn_id.prodMk contDiffOn_const) (mapsTo_espaco ht)

theorem contDiffOn_tempo {F : E3 × ℝ → W} (hF : ContDiffOn ℝ ∞ F Dom) (x : E3) :
    ContDiffOn ℝ ∞ (fun s => F (x, s)) (Ici 0) :=
  hF.comp (contDiffOn_const.prodMk contDiffOn_id) (mapsTo_tempo x)

/-- A derivada espacial da fatia no tempo `t ≥ 0` é a derivada no domínio, restrita a `ℝ³`. -/
theorem hasFDerivAt_espaco {F : E3 × ℝ → W} (hF : ContDiffOn ℝ ∞ F Dom) {t : ℝ} (ht : 0 ≤ t)
    (x : E3) :
    HasFDerivAt (fun y => F (y, t))
      ((fderivWithin ℝ F Dom (x, t)).comp (ContinuousLinearMap.inl ℝ E3 ℝ)) x := by
  have hd : DifferentiableWithinAt ℝ F Dom (x, t) :=
    hF.differentiableOn (by simp) (x, t) ⟨mem_univ _, ht⟩
  have hg : HasFDerivAt (fun y : E3 => (y, t)) (ContinuousLinearMap.inl ℝ E3 ℝ) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  exact hasFDerivWithinAt_univ.mp
    (hd.hasFDerivWithinAt.comp x hg.hasFDerivWithinAt (mapsTo_espaco ht))

theorem fderiv_espaco {F : E3 × ℝ → W} (hF : ContDiffOn ℝ ∞ F Dom) {t : ℝ} (ht : 0 ≤ t) :
    fderiv ℝ (fun y => F (y, t)) =
      fun x => (fderivWithin ℝ F Dom (x, t)).comp (ContinuousLinearMap.inl ℝ E3 ℝ) :=
  funext fun x => (hasFDerivAt_espaco hF ht x).fderiv

theorem continuousOn_fderivWithin_tempo {F : E3 × ℝ → W} (hF : ContDiffOn ℝ ∞ F Dom) (x : E3) :
    ContinuousOn (fun t => fderivWithin ℝ F Dom (x, t)) (Ici 0) :=
  (hF.continuousOn_fderivWithin uniqueDiffOn_dom (by simp)).comp
    (continuousOn_const.prodMk continuousOn_id) (mapsTo_tempo x)

/-- A derivada espacial, como função no domínio, é de novo suave. -/
theorem contDiffOn_derivEspacial {F : E3 × ℝ → W} (hF : ContDiffOn ℝ ∞ F Dom) :
    ContDiffOn ℝ ∞ (fun q => (fderivWithin ℝ F Dom q).comp (ContinuousLinearMap.inl ℝ E3 ℝ))
      Dom :=
  (hF.fderivWithin uniqueDiffOn_dom (m := ∞) (by simp)).clm_comp contDiffOn_const

omit [NormedSpace ℝ W] in
/-- Duas funções contínuas em `[0, ∞)` que coincidem em `(0, ∞)` coincidem em `0`. -/
theorem eq_em_zero {g h : ℝ → W} (hg : ContinuousOn g (Ici 0)) (hh : ContinuousOn h (Ici 0))
    (he : ∀ t, 0 < t → g t = h t) : g 0 = h 0 := by
  have h1 : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) := (hg 0 self_mem_Ici).mono Ioi_subset_Ici_self
  have h2 : Tendsto h (𝓝[>] 0) (𝓝 (h 0)) := (hh 0 self_mem_Ici).mono Ioi_subset_Ici_self
  have h3 : g =ᶠ[𝓝[>] 0] h := eventually_nhdsWithin_of_forall fun t ht => he t ht
  exact tendsto_nhds_unique (h1.congr' h3) h2

end Fatias

/-! ## 3. Cada termo da equação é contínuo em `t ∈ [0, ∞)` -/

section Tempo

variable {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}

local notation "ι₁" => ContinuousLinearMap.inl ℝ E3 ℝ
local notation "b" => EuclideanSpace.basisFun (Fin 3) ℝ

theorem continuousOn_dt (hU : ContDiffOn ℝ ∞ U Dom) (x : E3) :
    ContinuousOn (derivWithin (fun s => U (x, s)) (Ici 0)) (Ici 0) :=
  (contDiffOn_tempo hU x).continuousOn_derivWithin (uniqueDiffOn_Ici 0) (by simp)

theorem continuousOn_conv (hU : ContDiffOn ℝ ∞ U Dom) (x : E3) :
    ContinuousOn (fun t => fderiv ℝ (fun y => U (y, t)) x (U (x, t))) (Ici 0) := by
  have h : ContinuousOn (fun t => ((fderivWithin ℝ U Dom (x, t)).comp ι₁) (U (x, t))) (Ici 0) :=
    ((continuousOn_fderivWithin_tempo hU x).clm_comp continuousOn_const).clm_apply
      (hU.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) (mapsTo_tempo x))
  refine h.congr fun t ht => ?_
  rw [fderiv_espaco hU ht]

/-- O laplaciano da fatia, pelas derivadas no domínio. -/
theorem laplacian_espaco (hU : ContDiffOn ℝ ∞ U Dom) {t : ℝ} (ht : 0 ≤ t) (x : E3) :
    Δ (fun y => U (y, t)) x = ∑ i, ((fderivWithin ℝ (fun q => (fderivWithin ℝ U Dom q).comp ι₁)
      Dom (x, t)).comp ι₁) (b i) (b i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only [iteratedFDeriv_two_apply]
  rw [fderiv_espaco hU ht, fderiv_espaco (contDiffOn_derivEspacial hU) ht]
  simp

theorem continuousOn_laplacian (hU : ContDiffOn ℝ ∞ U Dom) (x : E3) :
    ContinuousOn (fun t => Δ (fun y => U (y, t)) x) (Ici 0) := by
  have hH := continuousOn_fderivWithin_tempo (contDiffOn_derivEspacial hU) x
  have h : ContinuousOn (fun t => ∑ i, ((fderivWithin ℝ (fun q => (fderivWithin ℝ U Dom q).comp ι₁)
      Dom (x, t)).comp ι₁) (b i) (b i)) (Ici 0) :=
    continuousOn_finsetSum _ fun i _ =>
      ((hH.clm_comp continuousOn_const).clm_apply continuousOn_const).clm_apply continuousOn_const
  exact h.congr fun t ht => laplacian_espaco hU ht x

theorem gradient_espaco (hP : ContDiffOn ℝ ∞ P Dom) {t : ℝ} (ht : 0 ≤ t) (x : E3) :
    gradient (fun y => P (y, t)) x =
      (InnerProductSpace.toDual ℝ E3).symm ((fderivWithin ℝ P Dom (x, t)).comp ι₁) := by
  rw [gradient, fderiv_espaco hP ht]

theorem continuousOn_gradient (hP : ContDiffOn ℝ ∞ P Dom) (x : E3) :
    ContinuousOn (fun t => gradient (fun y => P (y, t)) x) (Ici 0) := by
  have h1 : ContinuousOn (fun t => (fderivWithin ℝ P Dom (x, t)).comp ι₁) (Ici 0) :=
    (continuousOn_fderivWithin_tempo hP x).clm_comp continuousOn_const
  have h2 : ContinuousOn
      (fun t => (InnerProductSpace.toDual ℝ E3).symm ((fderivWithin ℝ P Dom (x, t)).comp ι₁))
      (Ici 0) :=
    (InnerProductSpace.toDual ℝ E3).symm.continuous.comp_continuousOn h1
  refine h2.congr fun t ht => ?_
  exact gradient_espaco hP ht x

/-- **A equação em `t = 0` segue da equação em `t > 0`** (por continuidade, com `∂ₜ` lateral). -/
theorem ns_em_zero {ν : ℝ} (hU : ContDiffOn ℝ ∞ U Dom) (hP : ContDiffOn ℝ ∞ P Dom) (x : E3)
    (h : ∀ t, 0 < t → derivWithin (fun s => U (x, s)) (Ici 0) t +
      fderiv ℝ (fun y => U (y, t)) x (U (x, t)) =
        ν • Δ (fun y => U (y, t)) x - gradient (fun y => P (y, t)) x) :
    derivWithin (fun s => U (x, s)) (Ici 0) 0 + fderiv ℝ (fun y => U (y, 0)) x (U (x, 0)) =
      ν • Δ (fun y => U (y, 0)) x - gradient (fun y => P (y, 0)) x := by
  have hg : ContinuousOn (fun t => derivWithin (fun s => U (x, s)) (Ici 0) t +
      fderiv ℝ (fun y => U (y, t)) x (U (x, t))) (Ici 0) :=
    (continuousOn_dt hU x).add (continuousOn_conv hU x)
  have hh : ContinuousOn (fun t => ν • Δ (fun y => U (y, t)) x -
      gradient (fun y => P (y, t)) x) (Ici 0) :=
    ((continuousOn_laplacian hU x).const_smul ν).sub (continuousOn_gradient hP x)
  have key := eq_em_zero hg hh h
  exact key

end Tempo

/-! ## 4. Dado inicial: classe de Schwartz ⟺ decaimento do formal-conjectures -/

/-- Uma função de Schwartz tem o decaimento (4) do formal-conjectures (expoente `K` real). -/
theorem decay_of_schwartz (S : SchwartzMap E3 E3) (m : ℕ) (K : ℝ) :
    ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ m S x‖ ≤ C / (1 + ‖x‖) ^ K := by
  set k := ⌈K⌉₊
  set C := 2 ^ k * ((Finset.Iic (k, m)).sup fun q => SchwartzMap.seminorm ℝ q.1 q.2) S
  have hb : ∀ x, (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ m S x‖ ≤ C := fun x =>
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, m)) le_rfl le_rfl S x
  have hC : 0 ≤ C := le_trans (by positivity) (hb 0)
  refine ⟨C, fun x => ?_⟩
  have h1 : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have h2 : (1 + ‖x‖) ^ K ≤ (1 + ‖x‖) ^ (k : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) (Nat.le_ceil K)
  rw [Real.rpow_natCast] at h2
  calc ‖iteratedFDeriv ℝ m S x‖ ≤ C / (1 + ‖x‖) ^ k := by
        rw [le_div_iff₀ (by positivity), mul_comm]; exact hb x
    _ ≤ C / (1 + ‖x‖) ^ K := div_le_div_of_nonneg_left hC (Real.rpow_pos_of_pos h1 K) h2

/-- Uma função suave com o decaimento (4) do formal-conjectures é de Schwartz. -/
theorem schwartz_of_decay {u : E3 → E3} (hs : ContDiff ℝ ∞ u)
    (hd : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ m u x‖ ≤ C / (1 + ‖x‖) ^ K) :
    ∃ S : SchwartzMap E3 E3, ⇑S = u := by
  refine ⟨⟨u, hs, fun k n => ?_⟩, rfl⟩
  obtain ⟨C, hC⟩ := hd n k
  refine ⟨C, fun x => ?_⟩
  have h1 : (0 : ℝ) < (1 + ‖x‖) ^ k := by positivity
  have hx := hC x
  rw [Real.rpow_natCast, le_div_iff₀ h1] at hx
  have h2 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ (norm_nonneg x) (by linarith) k
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n u x‖ ≤ (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ n u x‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ ≤ C := by rw [mul_comm]; exact hx

/-- **O dado inicial do ATK (Schwartz, divergência nula) é o do formal-conjectures.** -/
theorem dado_iff (u : E3 → E3) :
    ((∃ S : SchwartzMap E3 E3, ⇑S = u) ∧ ∀ x, div u x = 0) ↔
      ATK.FC.NS.InitialVelocityConditionDecay u := by
  constructor
  · rintro ⟨⟨S, rfl⟩, hdiv⟩
    exact { div_free := fun x => (div_eq _ x) ▸ hdiv x, smooth := S.smooth ⊤,
            decay := decay_of_schwartz S }
  · intro h
    exact ⟨schwartz_of_decay h.smooth h.decay, fun x => (div_eq _ x).symm ▸ h.div_free x⟩

/-! ## 5. Soluções: `SolucaoGlobal` do ATK ⟺ `NavierStokesExistenceAndSmoothnessRn` (força nula) -/

theorem contDiff_dois {f : E3 → E3} (h : ContDiff ℝ ∞ f) : ContDiff ℝ 2 f :=
  h.of_le (by simp)

/-- Uma solução do ATK é uma solução do formal-conjectures. A equação em `t = 0`, que o ATK
não impõe, segue por continuidade (`ns_em_zero`). -/
theorem fc_of_atk {ν : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}
    (h : SolucaoGlobal ν u₀ U P) :
    ATK.FC.NS.NavierStokesExistenceAndSmoothnessRn ν u₀ 0 (fun x t => U (x, t))
      (fun x t => P (x, t)) := by
  obtain ⟨hU, hP, h0, hns, hdiv, C, hE⟩ := h
  have key : ∀ x t, 0 < t → derivWithin (fun s => U (x, s)) (Ici 0) t +
      fderiv ℝ (fun y => U (y, t)) x (U (x, t)) =
        ν • Δ (fun y => U (y, t)) x - gradient (fun y => P (y, t)) x := by
    intro x t ht
    have := hns x t ht
    unfold NSEq at this
    simp only [fatia_eq] at this
    rw [conv_eq, lap_eq (f := fun y => U (y, t)) (contDiff_dois (contDiff_espaco hU ht.le)),
      grad_eq] at this
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht)]
    exact this
  exact
    { navier_stokes := fun x t ht => by
        simp only [Pi.zero_apply, add_zero]
        rcases ht.lt_or_eq with ht | rfl
        · exact key x t ht
        · exact ns_em_zero hU hP x (key x)
      div_free := fun x t ht => (div_eq _ x) ▸ hdiv x t ht
      initial_condition := h0
      velocity_smooth := hU
      pressure_smooth := hP
      integrable := fun t ht =>
        (memLp_two_iff_integrable_sq_norm
          (contDiff_espaco hU ht).continuous.norm.aestronglyMeasurable).mpr
          (by simpa using (hE t ht).1)
      globally_bounded_energy := ⟨C + 1, fun t ht => lt_of_le_of_lt (hE t ht).2 (lt_add_one C)⟩ }

/-- Uma solução do formal-conjectures (força nula) é uma solução do ATK. -/
theorem atk_of_fc {ν : ℝ} {u₀ : E3 → E3} {v : E3 → ℝ → E3} {p : E3 → ℝ → ℝ}
    (h : ATK.FC.NS.NavierStokesExistenceAndSmoothnessRn ν u₀ 0 v p) :
    SolucaoGlobal ν u₀ (fun q => v q.1 q.2) (fun q => p q.1 q.2) := by
  have hU : ContDiffOn ℝ ∞ (fun q : E3 × ℝ => v q.1 q.2) Dom := h.velocity_smooth
  have hP : ContDiffOn ℝ ∞ (fun q : E3 × ℝ => p q.1 q.2) Dom := h.pressure_smooth
  refine ⟨hU, hP, h.initial_condition, fun x t ht => ?_, fun x t ht => ?_, ?_⟩
  · have := h.navier_stokes x t ht.le
    simp only [Pi.zero_apply, add_zero] at this
    unfold NSEq
    simp only [fatia_eq]
    rw [conv_eq, lap_eq (f := fun y => v y t) (contDiff_dois (contDiff_espaco hU ht.le)), grad_eq,
      ← derivWithin_of_mem_nhds (Ici_mem_nhds ht)]
    exact this
  · rw [div_eq]
    exact h.div_free x t ht
  · obtain ⟨E, hE⟩ := h.globally_bounded_energy
    refine ⟨E, fun t ht => ⟨?_, (hE t ht).le⟩⟩
    have := (memLp_two_iff_integrable_sq_norm
      (contDiff_espaco hU ht).continuous.norm.aestronglyMeasurable).mp (h.integrable t ht)
    simpa using this

/-! ## 6. O enunciado (A) do ATK é o (A) do formal-conjectures -/

/-- **Fidelidade de L1 contra o formal-conjectures**: o enunciado (A) do ATK sobre o modelo
genuíno é o enunciado (A) do formal-conjectures (`navier_stokes_existence_and_smoothness_R3`),
**sem hipóteses**. -/
theorem clayA_iff_fc :
    ATK.Conditional.NavierStokes.ClayStatementA modeloNS ↔ ATK.FC.NS.ExistenceAndSmoothnessR3 := by
  rw [clayA_iff]
  constructor
  · intro h nu hnu u₀ hu
    obtain ⟨⟨S, hS⟩, hdiv⟩ := (dado_iff u₀).mpr hu
    subst hS
    obtain ⟨U, P, hsol⟩ := h nu hnu S hdiv
    exact ⟨_, _, fc_of_atk hsol⟩
  · intro h ν hν S hdiv
    obtain ⟨v, p, hsol⟩ := h ν hν S ((dado_iff S).mp ⟨⟨S, rfl⟩, hdiv⟩)
    exact ⟨_, _, atk_of_fc hsol⟩

end ATK.IntegracaoFCNS

#print axioms ATK.IntegracaoFCNS.div_eq
#print axioms ATK.IntegracaoFCNS.conv_eq
#print axioms ATK.IntegracaoFCNS.grad_eq
#print axioms ATK.IntegracaoFCNS.lap_eq
#print axioms ATK.IntegracaoFCNS.uniqueDiffOn_dom
#print axioms ATK.IntegracaoFCNS.mapsTo_espaco
#print axioms ATK.IntegracaoFCNS.mapsTo_tempo
#print axioms ATK.IntegracaoFCNS.contDiff_espaco
#print axioms ATK.IntegracaoFCNS.contDiffOn_tempo
#print axioms ATK.IntegracaoFCNS.hasFDerivAt_espaco
#print axioms ATK.IntegracaoFCNS.fderiv_espaco
#print axioms ATK.IntegracaoFCNS.continuousOn_fderivWithin_tempo
#print axioms ATK.IntegracaoFCNS.contDiffOn_derivEspacial
#print axioms ATK.IntegracaoFCNS.eq_em_zero
#print axioms ATK.IntegracaoFCNS.continuousOn_dt
#print axioms ATK.IntegracaoFCNS.continuousOn_conv
#print axioms ATK.IntegracaoFCNS.laplacian_espaco
#print axioms ATK.IntegracaoFCNS.continuousOn_laplacian
#print axioms ATK.IntegracaoFCNS.gradient_espaco
#print axioms ATK.IntegracaoFCNS.continuousOn_gradient
#print axioms ATK.IntegracaoFCNS.ns_em_zero
#print axioms ATK.IntegracaoFCNS.decay_of_schwartz
#print axioms ATK.IntegracaoFCNS.schwartz_of_decay
#print axioms ATK.IntegracaoFCNS.dado_iff
#print axioms ATK.IntegracaoFCNS.contDiff_dois
#print axioms ATK.IntegracaoFCNS.fc_of_atk
#print axioms ATK.IntegracaoFCNS.atk_of_fc
#print axioms ATK.IntegracaoFCNS.clayA_iff_fc
