import ATK.NSContinua
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# ATK — Navier–Stokes, marco NS8a: a formulação fraca (sem pressão)

Ponte B3, marco NS8 (primeira parte). Para qualquer solução da classe `SolucaoLocal` (pressão
**arbitrária**, sem hipótese de decaimento além de energia e enstrofia finitas) e qualquer campo
teste `φ` de suporte compacto, `C¹` e de divergência nula:

`∫ (U(t) − U(0))·φ = ∫₀ᵗ (−ν ∫ ∇U(s) : ∇φ + ∫ U(s) ⊗ U(s) : ∇φ) ds`

(**`fraca_compacta`**). A pressão some por integração por partes contra `div φ = 0`; o termo
`∂ₜU` é tratado derivando sob o sinal de integral (suporte compacto) e pelo teorema fundamental
do cálculo.

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta**; **CLOSED_MATH continua
false**.
-/

set_option autoImplicit false

open MeasureTheory Real Set Filter Topology
open scoped ContDiff
open ATK.LigacaoNS (E3 dX e div lap conv grad gradSq fatia NSEq SolucaoLocal)

open ATK.NSEnergia (hasDerivWithinAt_integral_gen)

namespace ATK.NSFraca

/-! ### Cálculo em `ℝ³` -/

theorem inner_E3 (a b : E3) : inner ℝ a b = ∑ i, a i * b i := by
  simp [PiLp.inner_apply, mul_comm]

theorem dX_coord {G : E3 → E3} {x : E3} (hG : DifferentiableAt ℝ G x) (j i : Fin 3) :
    dX j G x i = dX j (fun y => G y i) x := by
  have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := G x)).comp x hG.hasFDerivAt
  show (fderiv ℝ G x (e j)) i = fderiv ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i) ∘ G) x (e j)
  rw [h.fderiv]
  rfl

theorem hasCompactSupport_dX {g : E3 → ℝ} (hg : HasCompactSupport g) (j : Fin 3) :
    HasCompactSupport (dX j g) := by
  have h := hg.fderiv (𝕜 := ℝ)
  have : dX j g = (fun L : E3 →L[ℝ] ℝ => L (e j)) ∘ fderiv ℝ g := rfl
  rw [this]
  exact h.comp_left (by simp)

theorem hasCompactSupport_coord {G : E3 → E3} (hG : HasCompactSupport G) (i : Fin 3) :
    HasCompactSupport (fun x => G x i) := by
  have : (fun x => G x i) = (fun a : E3 => a i) ∘ G := rfl
  rw [this]
  exact hG.comp_left (by simp)

theorem continuous_dX {f : E3 → ℝ} (hf : ContDiff ℝ 1 f) (j : Fin 3) : Continuous (dX j f) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- **Integração por partes** (escalar, suporte compacto). -/
theorem ibp {f g : E3 → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (j : Fin 3) :
    ∫ x, f x * dX j g x = -∫ x, dX j f x * g x := by
  have h1 : Integrable fun x => fderiv ℝ f x (e j) * g x :=
    ((continuous_dX hf j).mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have h2 : Integrable fun x => f x * fderiv ℝ g x (e j) :=
    (hf.continuous.mul (continuous_dX hg j)).integrable_of_hasCompactSupport
      (hasCompactSupport_dX hgc j).mul_left
  have h3 : Integrable fun x => f x * g x :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 h3
    (fun x _ => hf.differentiable one_ne_zero x) (fun x _ => hg.differentiable one_ne_zero x)

/-- **Integração por partes** (campos, suporte compacto). -/
theorem ibp_vec {F G : E3 → E3} (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (hGc : HasCompactSupport G) (j : Fin 3) :
    ∫ x, inner ℝ (F x) (dX j G x) = -∫ x, inner ℝ (dX j F x) (G x) := by
  have hFi : ∀ i, ContDiff ℝ 1 fun x => F x i := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hF
  have hGi : ∀ i, ContDiff ℝ 1 fun x => G x i := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hG
  have e1 : (fun x => inner ℝ (F x) (dX j G x)) = fun x => ∑ i, F x i * dX j (fun y => G y i) x := by
    funext x
    rw [inner_E3]
    congr 1
    funext i
    rw [dX_coord (hG.differentiable one_ne_zero x)]
  have e2 : (fun x => inner ℝ (dX j F x) (G x)) = fun x => ∑ i, dX j (fun y => F y i) x * G x i := by
    funext x
    rw [inner_E3]
    congr 1
    funext i
    rw [dX_coord (hF.differentiable one_ne_zero x)]
  rw [e1, e2, integral_finsetSum, integral_finsetSum, ← Finset.sum_neg_distrib]
  · congr 1
    funext i
    exact ibp (hFi i) (hGi i) (hasCompactSupport_coord hGc i) j
  · intro i _
    exact ((continuous_dX (hFi i) j).mul (hGi i).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_coord hGc i).mul_left
  · intro i _
    exact ((hFi i).continuous.mul (continuous_dX (hGi i) j)).integrable_of_hasCompactSupport
      (hasCompactSupport_dX (hasCompactSupport_coord hGc i) j).mul_left

theorem hcs_of_zero {X Y : Type*} [Zero X] [Zero Y] {φ : E3 → X} {g : E3 → Y}
    (hφ : HasCompactSupport φ) (h : ∀ x, φ x = 0 → g x = 0) : HasCompactSupport g :=
  hφ.mono fun x hx hφx => hx (h x hφx)

theorem contDiff_dX_top {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : E3 → V}
    (hF : ContDiff ℝ ∞ F) (j : Fin 3) : ContDiff ℝ ∞ (dX j F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem continuous_dX_gen {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : E3 → V}
    (hF : ContDiff ℝ 1 F) (j : Fin 3) : Continuous (dX j F) :=
  (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem inner_e_left (j : Fin 3) (v : E3) : inner ℝ (e j) v = v j := by
  simp [e, EuclideanSpace.inner_single_left]

/-! ### Fatias e derivada temporal de uma solução suave -/

section Solucao

variable {T : ℝ} {U : E3 × ℝ → E3}

theorem slice_contDiff (hU : ContDiffOn ℝ ∞ U (univ ×ˢ Ico 0 T)) {s : ℝ} (hs : s ∈ Ico 0 T) :
    ContDiff ℝ ∞ (fatia U s) :=
  hU.comp_contDiff (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, hs⟩)

theorem uniqueDiffOn_S : UniqueDiffOn ℝ ((univ : Set E3) ×ˢ Ico 0 T) :=
  uniqueDiffOn_univ.prod (uniqueDiffOn_Ico 0 T)

/-- A derivada temporal `∂ₜU` (dentro do domínio `ℝ³ × [0, T)`). -/
noncomputable def Dt (T : ℝ) (U : E3 × ℝ → E3) (z : E3 × ℝ) : E3 :=
  fderivWithin ℝ U ((univ : Set E3) ×ˢ Ico 0 T) z (0, 1)

theorem continuousOn_Dt (hU : ContDiffOn ℝ ∞ U (univ ×ˢ Ico 0 T)) :
    ContinuousOn (Dt T U) (univ ×ˢ Ico 0 T) :=
  (hU.continuousOn_fderivWithin uniqueDiffOn_S (by simp)).clm_apply continuousOn_const

theorem hasDerivWithinAt_Dt (hU : ContDiffOn ℝ ∞ U (univ ×ˢ Ico 0 T)) {τ : ℝ} (hτ : τ < T)
    (x : E3) {s : ℝ} (hs : s ∈ Icc 0 τ) :
    HasDerivWithinAt (fun r => U (x, r)) (Dt T U (x, s)) (Icc 0 τ) s := by
  have hsS : (x, s) ∈ (univ : Set E3) ×ˢ Ico 0 T := ⟨mem_univ _, hs.1, hs.2.trans_lt hτ⟩
  have hd : HasFDerivWithinAt U (fderivWithin ℝ U (univ ×ˢ Ico 0 T) (x, s)) (univ ×ˢ Ico 0 T)
      (x, s) := ((hU.differentiableOn (by simp)) _ hsS).hasFDerivWithinAt
  have hl : HasDerivWithinAt (fun r : ℝ => ((x, r) : E3 × ℝ)) (0, 1) (Icc 0 τ) s :=
    (hasDerivAt_const s x).prodMk (hasDerivAt_id s) |>.hasDerivWithinAt
  exact hd.comp_hasDerivWithinAt s hl fun r hr => ⟨mem_univ _, hr.1, hr.2.trans_lt hτ⟩

theorem Dt_eq_deriv (hU : ContDiffOn ℝ ∞ U (univ ×ˢ Ico 0 T)) (x : E3) {s : ℝ}
    (hs : s ∈ Ioo 0 T) : Dt T U (x, s) = deriv (fun r => U (x, r)) s := by
  obtain ⟨τ, hsτ, hτ⟩ := exists_between hs.2
  have h := hasDerivWithinAt_Dt hU hτ x ⟨hs.1.le, hsτ.le⟩
  exact ((h.hasDerivAt (Icc_mem_nhds hs.1 hsτ)).deriv).symm

end Solucao

/-! ### A identidade fraca para testes de suporte compacto -/

/-- O integrando da formulação fraca: `−ν ∫ ∇U : ∇φ + ∫ U ⊗ U : ∇φ` no tempo `s`. -/
noncomputable def Fw (ν : ℝ) (U : E3 × ℝ → E3) (φ : E3 → E3) (s : ℝ) : ℝ :=
  -ν * (∑ j, ∫ x, inner ℝ (dX j (fatia U s) x) (dX j φ x)) +
    ∑ j, ∫ x, fatia U s x j * inner ℝ (fatia U s x) (dX j φ x)

theorem dX_smul_scalar {a : E3 → ℝ} {F : E3 → E3} {x : E3} (ha : DifferentiableAt ℝ a x)
    (hF : DifferentiableAt ℝ F x) (j : Fin 3) :
    dX j (fun y => a y • F y) x = dX j a x • F x + a x • dX j F x := by
  unfold dX
  have : (fun y => a y • F y) = a • F := rfl
  rw [this, fderiv_smul ha hF]
  simp [add_comm]

/-- O integrando da formulação fraca é o `∫ ∂ₜU · φ` (pressão eliminada). -/
theorem integral_Dt_eq {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}
    (hS : SolucaoLocal ν u₀ T U P) {φ : E3 → E3} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hdiv : ∀ x, div φ x = 0) {s : ℝ} (hs : s ∈ Ioo 0 T) :
    ∫ x, inner ℝ (Dt T U (x, s)) (φ x) = Fw ν U φ s := by
  obtain ⟨hU, hP, -, hNS, hdivU, -⟩ := hS
  have hsI : s ∈ Ico 0 T := ⟨hs.1.le, hs.2⟩
  have hUs := slice_contDiff hU hsI
  have hPs : ContDiff ℝ ∞ (fatia P s) :=
    hP.comp_contDiff (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, hsI⟩)
  have hU1 : ContDiff ℝ 1 (fatia U s) := hUs.of_le (by simp)
  have hU2 : ∀ j, ContDiff ℝ 1 (dX j (fatia U s)) := fun j =>
    ((hUs.fderiv_right (m := 1) (by simp)).clm_apply contDiff_const)
  have hUj : ∀ j, ContDiff ℝ 1 fun x => fatia U s x j := fun j =>
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hU1
  have hφj : ∀ j, ContDiff ℝ 1 fun x => φ x j := fun j =>
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hφ
  have hP1 : ContDiff ℝ 1 (fatia P s) := hPs.of_le (by simp)
  -- a equação
  have hpt : ∀ x, Dt T U (x, s) = ν • lap (fatia U s) x - conv (fatia U s) x - grad (fatia P s) x := by
    intro x
    rw [Dt_eq_deriv hU x hs, eq_sub_of_add_eq (hNS x s hs)]
    abel
  -- integrabilidade
  have hint : ∀ {G : E3 → E3}, Continuous G →
      Integrable fun x => inner ℝ (G x) (φ x) := fun hG =>
    (hG.inner hφ.continuous).integrable_of_hasCompactSupport
      (hcs_of_zero hφc fun x hx => by simp [hx])
  have hdφ : ∀ j, Continuous (dX j φ) := fun j => continuous_dX_gen hφ j
  have hdφc : ∀ j, HasCompactSupport (dX j φ) := fun j => by
    have h := hφc.fderiv (𝕜 := ℝ)
    have : dX j φ = (fun L : E3 →L[ℝ] E3 => L (e j)) ∘ fderiv ℝ φ := rfl
    rw [this]
    exact h.comp_left (by simp)
  have hintd : ∀ j, ∀ {G : E3 → E3}, Continuous G →
      Integrable fun x => inner ℝ (G x) (dX j φ x) := fun j _ hG =>
    (hG.inner (hdφ j)).integrable_of_hasCompactSupport
      (hcs_of_zero (hdφc j) fun x hx => by simp [hx])
  have hcU : Continuous (fatia U s) := hU1.continuous
  have hcdU : ∀ j, Continuous (dX j (fatia U s)) := fun j => continuous_dX_gen hU1 j
  have hcddU : ∀ j, Continuous (dX j (dX j (fatia U s))) := fun j => continuous_dX_gen (hU2 j) j
  -- o laplaciano
  have hlap : ∫ x, inner ℝ (lap (fatia U s) x) (φ x) =
      -∑ j, ∫ x, inner ℝ (dX j (fatia U s) x) (dX j φ x) := by
    have e1 : (fun x => inner ℝ (lap (fatia U s) x) (φ x)) =
        fun x => ∑ j, inner ℝ (dX j (dX j (fatia U s)) x) (φ x) := by
      funext x
      simp only [lap, sum_inner]
    rw [e1, integral_finsetSum _ fun j _ => hint (hcddU j), ← Finset.sum_neg_distrib]
    congr 1
    funext j
    rw [ibp_vec (hU2 j) hφ hφc j, neg_neg]
  -- o termo convectivo
  have hconv : ∫ x, inner ℝ (conv (fatia U s) x) (φ x) =
      -∑ j, ∫ x, fatia U s x j * inner ℝ (fatia U s x) (dX j φ x) := by
    set G : Fin 3 → E3 → E3 := fun j y => fatia U s y j • φ y with hG_def
    have hG1 : ∀ j, ContDiff ℝ 1 (G j) := fun j => (hUj j).smul hφ
    have hGc : ∀ j, HasCompactSupport (G j) := fun j =>
      hcs_of_zero hφc fun x hx => by simp [hG_def, hx]
    have hdG : ∀ j x, dX j (G j) x = dX j (fun y => fatia U s y j) x • φ x +
        fatia U s x j • dX j φ x := fun j x =>
      dX_smul_scalar ((hUj j).differentiable one_ne_zero x) (hφ.differentiable one_ne_zero x) j
    have hcdG : ∀ j, Continuous (dX j (G j)) := fun j => continuous_dX_gen (hG1 j) j
    have hcdGc : ∀ j, HasCompactSupport (dX j (G j)) := fun j => by
      have h := (hGc j).fderiv (𝕜 := ℝ)
      have : dX j (G j) = (fun L : E3 →L[ℝ] E3 => L (e j)) ∘ fderiv ℝ (G j) := rfl
      rw [this]
      exact h.comp_left (by simp)
    have e1 : (fun x => inner ℝ (conv (fatia U s) x) (φ x)) =
        fun x => ∑ j, inner ℝ (dX j (fatia U s) x) (G j x) := by
      funext x
      simp only [conv, sum_inner, hG_def, real_inner_smul_left, real_inner_smul_right]
    have hint1 : ∀ j, Integrable fun x => inner ℝ (dX j (fatia U s) x) (G j x) := fun j =>
      ((hcdU j).inner (hG1 j).continuous).integrable_of_hasCompactSupport
        (hcs_of_zero (hGc j) fun x hx => by simp [hx])
    have hint2 : ∀ j, Integrable fun x => inner ℝ (fatia U s x) (dX j (G j) x) := fun j =>
      (hcU.inner (hcdG j)).integrable_of_hasCompactSupport
        (hcs_of_zero (hcdGc j) fun x hx => by simp [hx])
    have step : ∀ j, ∫ x, inner ℝ (dX j (fatia U s) x) (G j x) =
        -∫ x, inner ℝ (fatia U s x) (dX j (G j) x) := fun j => by
      rw [ibp_vec hU1 (hG1 j) (hGc j) j, neg_neg]
    rw [e1, integral_finsetSum _ fun j _ => hint1 j, Finset.sum_congr rfl fun j _ => step j,
      Finset.sum_neg_distrib, ← integral_finsetSum _ fun j _ => hint2 j]
    have e2 : (fun x => ∑ j, inner ℝ (fatia U s x) (dX j (G j) x)) =
        fun x => ∑ j, fatia U s x j * inner ℝ (fatia U s x) (dX j φ x) := by
      funext x
      have hdivx : ∑ j, dX j (fun y => fatia U s y j) x = 0 := by
        have := hdivU x s hsI
        unfold div at this
        rw [← this]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [dX_coord (hU1.differentiable one_ne_zero x)]
      simp only [hdG, inner_add_right, real_inner_smul_right, Finset.sum_add_distrib,
        ← Finset.sum_mul, hdivx, zero_mul, zero_add]
    rw [e2, integral_finsetSum _ fun j _ => ?_]
    exact ((hUj j).continuous.mul (hcU.inner (hdφ j))).integrable_of_hasCompactSupport
      (hcs_of_zero (hdφc j) fun x hx => by simp [hx])
  -- a pressão
  have hgrad : ∫ x, inner ℝ (grad (fatia P s) x) (φ x) = 0 := by
    have e1 : (fun x => inner ℝ (grad (fatia P s) x) (φ x)) =
        fun x => ∑ j, dX j (fatia P s) x * φ x j := by
      funext x
      simp only [grad, sum_inner, real_inner_smul_left, inner_e_left]
    have hint1 : ∀ j, Integrable fun x => dX j (fatia P s) x * φ x j := fun j =>
      ((continuous_dX_gen hP1 j).mul (hφj j).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_coord hφc j).mul_left
    have hint2 : ∀ j, Integrable fun x => fatia P s x * dX j (fun y => φ y j) x := fun j =>
      (hP1.continuous.mul (continuous_dX_gen (hφj j) j)).integrable_of_hasCompactSupport
        (hasCompactSupport_dX (hasCompactSupport_coord hφc j) j).mul_left
    rw [e1, integral_finsetSum _ fun j _ => hint1 j]
    have step : ∀ j, ∫ x, dX j (fatia P s) x * φ x j =
        -∫ x, fatia P s x * dX j (fun y => φ y j) x := fun j => by
      rw [ibp hP1 (hφj j) (hasCompactSupport_coord hφc j) j, neg_neg]
    rw [Finset.sum_congr rfl fun j _ => step j, Finset.sum_neg_distrib,
      ← integral_finsetSum _ fun j _ => hint2 j]
    have e2 : (fun x => ∑ j, fatia P s x * dX j (fun y => φ y j) x) = fun _ => 0 := by
      funext x
      rw [← Finset.mul_sum]
      have := hdiv x
      unfold div at this
      have e3 : ∑ j, dX j (fun y => φ y j) x = ∑ j, dX j φ x j :=
        Finset.sum_congr rfl fun j _ => (dX_coord (hφ.differentiable one_ne_zero x) j j).symm
      rw [e3, this, mul_zero]
    rw [e2, integral_zero, neg_zero]
  -- montagem
  have hcl : Continuous (lap (fatia U s)) := by
    unfold lap
    exact continuous_finsetSum _ fun j _ => hcddU j
  have hcc : Continuous (conv (fatia U s)) := by
    unfold conv
    exact continuous_finsetSum _ fun j _ => ((hUj j).continuous).smul (hcdU j)
  have hcg : Continuous (grad (fatia P s)) := by
    unfold grad
    exact continuous_finsetSum _ fun j _ => (continuous_dX_gen hP1 j).smul continuous_const
  have e1 : (fun x => inner ℝ (Dt T U (x, s)) (φ x)) = fun x =>
      ν * inner ℝ (lap (fatia U s) x) (φ x) - inner ℝ (conv (fatia U s) x) (φ x) -
        inner ℝ (grad (fatia P s) x) (φ x) := by
    funext x
    rw [hpt x, inner_sub_left, inner_sub_left, real_inner_smul_left]
  have i1 : Integrable fun x => ν * inner ℝ (lap (fatia U s) x) (φ x) := (hint hcl).const_mul ν
  have i2 : Integrable fun x => inner ℝ (conv (fatia U s) x) (φ x) := hint hcc
  have i3 : Integrable fun x => inner ℝ (grad (fatia P s) x) (φ x) := hint hcg
  have i12 : Integrable fun x =>
      ν * inner ℝ (lap (fatia U s) x) (φ x) - inner ℝ (conv (fatia U s) x) (φ x) := i1.sub i2
  rw [e1, integral_sub i12 i3, integral_sub i1 i2, integral_const_mul, hlap, hconv, hgrad]
  unfold Fw
  ring


/-- **A formulação fraca** (testes de suporte compacto, `C¹`, divergência nula). A pressão,
arbitrária, não aparece. -/
theorem fraca_compacta {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}
    (hS : SolucaoLocal ν u₀ T U P) {τ : ℝ} (hτ : τ < T) {φ : E3 → E3} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hdiv : ∀ x, div φ x = 0) {t : ℝ} (ht : t ∈ Icc 0 τ) :
    (∫ x, inner ℝ (U (x, t)) (φ x)) - ∫ x, inner ℝ (u₀ x) (φ x) =
      ∫ s in (0 : ℝ)..t, Fw ν U φ s := by
  have hU := hS.1
  have h0 := hS.2.2.1
  have hτ0 : 0 ≤ τ := ht.1.trans ht.2
  set S : Set (E3 × ℝ) := (univ : Set E3) ×ˢ Ico 0 T
  have hKs : tsupport φ ×ˢ Icc 0 τ ⊆ S := fun z hz => ⟨mem_univ _, hz.2.1, hz.2.2.trans_lt hτ⟩
  obtain ⟨C, hC⟩ := (hφc.isCompact.prod isCompact_Icc).exists_bound_of_continuousOn
    ((continuousOn_Dt hU).mono hKs)
  have hcs : ∀ {r : ℝ}, r ∈ Icc 0 τ → Continuous (fatia U r) := fun hr =>
    (slice_contDiff hU ⟨hr.1, hr.2.trans_lt hτ⟩).continuous
  have hb : Integrable fun x => C * ‖φ x‖ :=
    (hφ.continuous.norm.integrable_of_hasCompactSupport hφc.norm).const_mul C
  have hbound : ∀ x, ∀ r ∈ Icc 0 τ, ‖inner ℝ (Dt T U (x, r)) (φ x)‖ ≤ C * ‖φ x‖ := by
    intro x r hr
    by_cases hx : x ∈ tsupport φ
    · calc ‖inner ℝ (Dt T U (x, r)) (φ x)‖ ≤ ‖Dt T U (x, r)‖ * ‖φ x‖ := norm_inner_le_norm _ _
        _ ≤ C * ‖φ x‖ := by gcongr; exact hC (x, r) ⟨hx, hr⟩
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  set g : ℝ → ℝ := fun r => ∫ x, inner ℝ (U (x, r)) (φ x) with hg_def
  set g' : ℝ → ℝ := fun r => ∫ x, inner ℝ (Dt T U (x, r)) (φ x) with hg'_def
  have hgd : ∀ r ∈ Icc 0 τ, HasDerivWithinAt g (g' r) (Icc 0 τ) r := by
    intro r hr
    refine hasDerivWithinAt_integral_gen (V := ℝ)
      (F := fun r x => inner ℝ (U (x, r)) (φ x)) (F' := fun r x => inner ℝ (Dt T U (x, r)) (φ x))
      (convex_Icc 0 τ) hr (fun r hr => ((hcs hr).inner hφ.continuous).aestronglyMeasurable)
      (((hcs hr).inner hφ.continuous).integrable_of_hasCompactSupport
        (hcs_of_zero hφc fun x hx => by simp [hx])) hb (fun x r hr => ?_) hbound
    have h1 := (hasDerivWithinAt_Dt hU hτ x hr).inner ℝ (hasDerivWithinAt_const r (Icc 0 τ) (φ x))
    exact h1.congr_deriv (by simp)
  have hg'c : ContinuousOn g' (Icc 0 τ) := by
    refine continuousOn_of_dominated (bound := fun x => C * ‖φ x‖)
      (fun r hr => ?_) (fun r hr => Eventually.of_forall fun x => hbound x r hr) hb
      (Eventually.of_forall fun x => ?_)
    · have hcd : Continuous fun y => Dt T U (y, r) :=
        continuousOn_univ.mp ((continuousOn_Dt hU).comp
          (continuous_id.prodMk continuous_const).continuousOn
          fun y _ => ⟨mem_univ _, hr.1, hr.2.trans_lt hτ⟩)
      exact (hcd.inner hφ.continuous).aestronglyMeasurable
    · have hcd : ContinuousOn (fun r => Dt T U (x, r)) (Icc 0 τ) :=
        (continuousOn_Dt hU).comp (continuous_const.prodMk continuous_id).continuousOn
          fun r hr => ⟨mem_univ _, hr.1, hr.2.trans_lt hτ⟩
      exact hcd.inner continuousOn_const
  have hsub : Icc 0 t ⊆ Icc 0 τ := Icc_subset_Icc le_rfl ht.2
  have hFTC : ∫ r in (0 : ℝ)..t, g' r = g t - g 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      (fun r hr => (hgd r (hsub hr)).continuousWithinAt.mono hsub) (fun r hr => ?_)
      ((hg'c.mono (by rw [uIcc_of_le ht.1]; exact hsub)).intervalIntegrable)
    exact (hgd r (hsub (Ioo_subset_Icc_self hr))).hasDerivAt
      (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2))
  have hcongr : ∫ r in (0 : ℝ)..t, g' r = ∫ r in (0 : ℝ)..t, Fw ν U φ r := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ t := by
      rw [ae_iff]
      simp
    filter_upwards [hne] with r hrt hr
    rw [uIoc_of_le ht.1] at hr
    exact integral_Dt_eq hS hφ hφc hdiv ⟨hr.1, (lt_of_le_of_ne hr.2 hrt).trans_le
      (ht.2.trans hτ.le)⟩
  have hg0 : g 0 = ∫ x, inner ℝ (u₀ x) (φ x) := by
    simp only [hg_def, h0]
  rw [← hcongr, hFTC, hg0]

end ATK.NSFraca

#print axioms ATK.NSFraca.inner_E3
#print axioms ATK.NSFraca.dX_coord
#print axioms ATK.NSFraca.hasCompactSupport_dX
#print axioms ATK.NSFraca.hasCompactSupport_coord
#print axioms ATK.NSFraca.continuous_dX
#print axioms ATK.NSFraca.ibp
#print axioms ATK.NSFraca.ibp_vec
#print axioms ATK.NSFraca.hcs_of_zero
#print axioms ATK.NSFraca.contDiff_dX_top
#print axioms ATK.NSFraca.continuous_dX_gen
#print axioms ATK.NSFraca.inner_e_left
#print axioms ATK.NSFraca.slice_contDiff
#print axioms ATK.NSFraca.uniqueDiffOn_S
#print axioms ATK.NSFraca.Dt
#print axioms ATK.NSFraca.continuousOn_Dt
#print axioms ATK.NSFraca.hasDerivWithinAt_Dt
#print axioms ATK.NSFraca.Dt_eq_deriv
#print axioms ATK.NSFraca.Fw
#print axioms ATK.NSFraca.dX_smul_scalar
#print axioms ATK.NSFraca.integral_Dt_eq
#print axioms ATK.NSFraca.fraca_compacta
