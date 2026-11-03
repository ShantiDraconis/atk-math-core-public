import ATK.NSContinuacao

/-!
# ATK — Navier–Stokes: formulação fraca sem pressão

Camada 16 do ataque a B3 (rumo à unicidade fraca–forte). Para **qualquer** solução suave
`(U, P)` (classe `SolucaoLocal`, sem hipótese nenhuma sobre a pressão) e qualquer campo-teste
`Φ` suave, de suporte compacto e de divergência nula:

`∫ ⟪U(t), Φ⟫ − ∫ ⟪u₀, Φ⟫ = ∫₀ᵗ (ν ∫ ⟪U(s), ΔΦ⟫ + ∫ Σⱼₖ Uⱼ Uₖ ∂ⱼΦₖ) ds`  (`formulacao_fraca`).

A pressão desaparece porque `∫ ⟪∇P, Φ⟫ = −∫ P div Φ = 0` (integração por partes com suporte
compacto); o termo viscoso e o convectivo passam as derivadas para `Φ`.

**CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff Real

namespace ATK.NSFraca

open ATK.LigacaoNS ATK.NSReducao

/-! ### Componentes e derivadas parciais -/

theorem inner_E3 (v w : E3) : inner ℝ v w = ∑ k, v k * w k := by
  simp [PiLp.inner_apply, mul_comm]

theorem dX_comp {f : E3 → E3} {x : E3} (hf : DifferentiableAt ℝ f x) (j k : Fin 3) :
    dX j (fun y => f y k) x = dX j f x k := by
  have h : HasFDerivAt (fun y => f y k)
      ((EuclideanSpace.proj k : E3 →L[ℝ] ℝ).comp (fderiv ℝ f x)) x :=
    (EuclideanSpace.proj k : E3 →L[ℝ] ℝ).hasFDerivAt.comp x hf.hasFDerivAt
  unfold dX; rw [h.fderiv]; rfl

theorem contDiff_dX {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {g : E3 → W}
    (hg : ContDiff ℝ ∞ g) (j : Fin 3) : ContDiff ℝ ∞ (dX j g) := by
  have h : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  exact h.clm_apply contDiff_const

theorem contDiff_comp {f : E3 → E3} (hf : ContDiff ℝ ∞ f) (k : Fin 3) :
    ContDiff ℝ ∞ fun y => f y k :=
  (EuclideanSpace.proj k : E3 →L[ℝ] ℝ).contDiff.comp hf

theorem continuous_dX {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {g : E3 → W}
    (hg : ContDiff ℝ ∞ g) (j : Fin 3) : Continuous (dX j g) :=
  (contDiff_dX hg j).continuous

theorem hasCompactSupport_dX {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {g : E3 → W}
    (hg : HasCompactSupport g) (j : Fin 3) : HasCompactSupport (dX j g) := by
  have h : HasCompactSupport (fderiv ℝ g) := hg.fderiv (𝕜 := ℝ)
  exact h.comp_left (g := fun L : E3 →L[ℝ] W => L (e j)) (by simp)

theorem dX_mul {a b : E3 → ℝ} {x : E3} (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) (j : Fin 3) :
    dX j (fun y => a y * b y) x = dX j a x * b x + a x * dX j b x := by
  unfold dX
  show fderiv ℝ (a * b) x (e j) = _
  rw [fderiv_mul ha hb]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-! ### Integração por partes com suporte compacto -/

theorem hcs_mul {u v : E3 → ℝ} (h : HasCompactSupport u ∨ HasCompactSupport v) :
    HasCompactSupport fun x => u x * v x := by
  rcases h with h | h
  · exact h.mul_right
  · exact h.mul_left

/-- `∫ a ∂ⱼb = −∫ ∂ⱼa b` se `a` ou `b` tem suporte compacto. -/
theorem ibp {a b : E3 → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hc : HasCompactSupport a ∨ HasCompactSupport b) (j : Fin 3) :
    ∫ x, a x * dX j b x = -∫ x, dX j a x * b x := by
  have hca : HasCompactSupport (dX j a) ∨ HasCompactSupport b := by
    rcases hc with h | h
    · exact Or.inl (hasCompactSupport_dX h j)
    · exact Or.inr h
  have hcb : HasCompactSupport a ∨ HasCompactSupport (dX j b) := by
    rcases hc with h | h
    · exact Or.inl h
    · exact Or.inr (hasCompactSupport_dX h j)
  have i1 : Integrable fun x => dX j a x * b x :=
    ((continuous_dX ha j).mul hb.continuous).integrable_of_hasCompactSupport (hcs_mul hca)
  have i2 : Integrable fun x => a x * dX j b x :=
    (ha.continuous.mul (continuous_dX hb j)).integrable_of_hasCompactSupport (hcs_mul hcb)
  have i3 : Integrable fun x => a x * b x :=
    (ha.continuous.mul hb.continuous).integrable_of_hasCompactSupport (hcs_mul hc)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := e j)
    (f := a) (g := b) i1 i2 i3 (fun x _ => (ha.differentiable (by simp)) x)
    (fun x _ => (hb.differentiable (by simp)) x)
  simpa [dX] using h

theorem integrable_cs {u v : E3 → ℝ} (hu : Continuous u) (hv : Continuous v)
    (h : HasCompactSupport u ∨ HasCompactSupport v) : Integrable fun x => u x * v x :=
  (hu.mul hv).integrable_of_hasCompactSupport (hcs_mul h)

/-! ### Os três termos -/

section

variable {Φ : E3 → E3} (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ)
include hΦ hc

theorem hcs_comp (k : Fin 3) : HasCompactSupport fun y => Φ y k :=
  hc.comp_left (g := fun v : E3 => v k) (by simp)

theorem lap_comp {f : E3 → E3} (hf : ContDiff ℝ ∞ f) (x : E3) (k : Fin 3) :
    lap f x k = lap (fun y => f y k) x := by
  unfold lap
  rw [show (∑ j, dX j (dX j f) x) k = ∑ j, dX j (dX j f) x k by simp]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (fun y => dX j f y k) = dX j (fun y => f y k) := funext fun y =>
    (dX_comp ((hf.differentiable (by simp)) y) j k).symm
  rw [← dX_comp ((contDiff_dX hf j).differentiable (by simp) x) j k, h1]

/-- `∫ ⟪Δf, Φ⟫ = ∫ ⟪f, ΔΦ⟫`. -/
theorem integral_inner_lap {f : E3 → E3} (hf : ContDiff ℝ ∞ f) :
    ∫ x, inner ℝ (lap f x) (Φ x) = ∫ x, inner ℝ (f x) (lap Φ x) := by
  simp_rw [inner_E3, fun x k => lap_comp hΦ hc hf x k, fun x k => lap_comp hΦ hc hΦ x k]
  have hfk := fun k => contDiff_comp hf k
  have hΦk := fun k => contDiff_comp hΦ k
  have hck := fun k => hcs_comp hΦ hc k
  -- cada componente
  have key : ∀ k, ∫ x, lap (fun y => f y k) x * Φ x k = ∫ x, f x k * lap (fun y => Φ y k) x := by
    intro k
    unfold lap
    have i1 : ∀ j, Integrable fun x => dX j (dX j fun y => f y k) x * Φ x k := fun j =>
      integrable_cs (continuous_dX (contDiff_dX (hfk k) j) j) (hΦk k).continuous
        (Or.inr (hck k))
    have i2 : ∀ j, Integrable fun x => f x k * dX j (dX j fun y => Φ y k) x := fun j =>
      integrable_cs (hfk k).continuous (continuous_dX (contDiff_dX (hΦk k) j) j)
        (Or.inr (hasCompactSupport_dX (hasCompactSupport_dX (hck k) j) j))
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [integral_finsetSum _ fun j _ => i1 j, integral_finsetSum _ fun j _ => i2 j]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 := ibp (hΦk k) (contDiff_dX (hfk k) j) (Or.inl (hck k)) j
    have e2 := ibp (hfk k) (contDiff_dX (hΦk k) j) (Or.inr (hasCompactSupport_dX (hck k) j)) j
    have e3 : ∫ x, dX j (fun y => Φ y k) x * dX j (fun y => f y k) x =
        ∫ x, dX j (fun y => f y k) x * dX j (fun y => Φ y k) x := by
      congr 1 with x; ring
    calc ∫ x, dX j (dX j fun y => f y k) x * Φ x k
        = ∫ x, Φ x k * dX j (dX j fun y => f y k) x := by congr 1 with x; ring
      _ = -∫ x, dX j (fun y => Φ y k) x * dX j (fun y => f y k) x := e1
      _ = ∫ x, f x k * dX j (dX j fun y => Φ y k) x := by rw [e2, e3]
  have i3 : ∀ k ∈ Finset.univ, Integrable fun x => lap (fun y => f y k) x * Φ x k := by
    intro k _
    unfold lap
    simp_rw [Finset.sum_mul]
    exact integrable_finsetSum _ fun j _ =>
      integrable_cs (continuous_dX (contDiff_dX (hfk k) j) j) (hΦk k).continuous
        (Or.inr (hck k))
  have i4 : ∀ k ∈ Finset.univ, Integrable fun x => f x k * lap (fun y => Φ y k) x := by
    intro k _
    unfold lap
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ fun j _ =>
      integrable_cs (hfk k).continuous (continuous_dX (contDiff_dX (hΦk k) j) j)
        (Or.inr (hasCompactSupport_dX (hasCompactSupport_dX (hck k) j) j))
  rw [integral_finsetSum _ i3, integral_finsetSum _ i4]
  exact Finset.sum_congr rfl fun k _ => key k

/-- **A pressão desaparece**: `∫ ⟪∇p, Φ⟫ = 0` se `div Φ = 0`. -/
theorem integral_inner_grad {p : E3 → ℝ} (hp : ContDiff ℝ ∞ p) (hdiv : ∀ x, div Φ x = 0) :
    ∫ x, inner ℝ (grad p x) (Φ x) = 0 := by
  have hΦk := fun k => contDiff_comp hΦ k
  have hck := fun k => hcs_comp hΦ hc k
  have e1 : ∀ x, inner ℝ (grad p x) (Φ x) = ∑ j, dX j p x * Φ x j := by
    intro x
    unfold grad
    rw [inner_E3]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coord_sum (fun j => dX j p x) k]
  simp_rw [e1]
  have i1 : ∀ j ∈ Finset.univ, Integrable fun x => dX j p x * Φ x j := fun j _ =>
    integrable_cs (continuous_dX hp j) (hΦk j).continuous (Or.inr (hck j))
  rw [integral_finsetSum _ i1]
  have e2 : ∀ j, ∫ x, dX j p x * Φ x j = -∫ x, p x * dX j (fun y => Φ y j) x := by
    intro j
    rw [ibp hp (hΦk j) (Or.inr (hck j)) j, neg_neg]
  simp_rw [e2]
  have i2 : ∀ j ∈ Finset.univ, Integrable fun x => p x * dX j (fun y => Φ y j) x := fun j _ =>
    integrable_cs hp.continuous (continuous_dX (hΦk j) j) (Or.inr (hasCompactSupport_dX (hck j) j))
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ i2]
  have e3 : ∀ x, ∑ j, p x * dX j (fun y => Φ y j) x = p x * div Φ x := by
    intro x
    rw [← Finset.mul_sum]
    congr 1
    unfold div
    exact Finset.sum_congr rfl fun j _ => dX_comp ((hΦ.differentiable (by simp)) x) j j
  simp_rw [e3, hdiv, mul_zero, integral_zero, neg_zero]

/-- **O termo convectivo** (com `div f = 0`): `∫ ⟪(f·∇)f, Φ⟫ = −∫ Σⱼₖ fⱼ fₖ ∂ⱼΦₖ`. -/
theorem integral_inner_conv {f : E3 → E3} (hf : ContDiff ℝ ∞ f) (hdivf : ∀ x, div f x = 0) :
    ∫ x, inner ℝ (conv f x) (Φ x) = -∫ x, ∑ j, ∑ k, f x j * f x k * dX j Φ x k := by
  have hfk := fun k => contDiff_comp hf k
  have hΦk := fun k => contDiff_comp hΦ k
  have hck := fun k => hcs_comp hΦ hc k
  have hdf : ∀ x j k, dX j f x k = dX j (fun y => f y k) x := fun x j k =>
    (dX_comp ((hf.differentiable (by simp)) x) j k).symm
  have hdΦ : ∀ x j k, dX j Φ x k = dX j (fun y => Φ y k) x := fun x j k =>
    (dX_comp ((hΦ.differentiable (by simp)) x) j k).symm
  have e1 : ∀ x, inner ℝ (conv f x) (Φ x) =
      ∑ k, ∑ j, f x j * dX j (fun y => f y k) x * Φ x k := by
    intro x
    unfold conv
    rw [inner_E3]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (∑ j, f x j • dX j f x) k = ∑ j, f x j * dX j f x k by simp, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [hdf]
  simp_rw [e1]
  -- integrabilidades
  have ijk : ∀ j k, Integrable fun x => f x j * dX j (fun y => f y k) x * Φ x k := fun j k =>
    integrable_cs ((hfk j).continuous.mul (continuous_dX (hfk k) j)) (hΦk k).continuous
      (Or.inr (hck k))
  have ijk' : ∀ j k, Integrable fun x => f x j * f x k * dX j (fun y => Φ y k) x := fun j k =>
    integrable_cs ((hfk j).continuous.mul (hfk k).continuous) (continuous_dX (hΦk k) j)
      (Or.inr (hasCompactSupport_dX (hck k) j))
  have ijk'' : ∀ j k, Integrable fun x => dX j (fun y => f y j) x * Φ x k * f x k := fun j k =>
    integrable_cs ((continuous_dX (hfk j) j).mul (hΦk k).continuous) (hfk k).continuous
      (Or.inl (hck k).mul_left)
  -- cada termo `(j, k)` por partes
  have key : ∀ j k, ∫ x, f x j * dX j (fun y => f y k) x * Φ x k =
      -(∫ x, dX j (fun y => f y j) x * Φ x k * f x k) -
        ∫ x, f x j * f x k * dX j (fun y => Φ y k) x := by
    intro j k
    have hjk : ContDiff ℝ ∞ fun y => f y j * Φ y k := (hfk j).mul (hΦk k)
    have h := ibp hjk (hfk k) (Or.inl (hck k).mul_left) j
    have hd : ∀ x, dX j (fun y => f y j * Φ y k) x =
        dX j (fun y => f y j) x * Φ x k + f x j * dX j (fun y => Φ y k) x := fun x =>
      dX_mul (((hfk j).differentiable (by simp)) x) (((hΦk k).differentiable (by simp)) x) j
    calc ∫ x, f x j * dX j (fun y => f y k) x * Φ x k
        = ∫ x, f x j * Φ x k * dX j (fun y => f y k) x := by congr 1 with x; ring
      _ = -∫ x, dX j (fun y => f y j * Φ y k) x * f x k := h
      _ = -∫ x, (dX j (fun y => f y j) x * Φ x k * f x k +
            f x j * f x k * dX j (fun y => Φ y k) x) := by
          congr 1; congr 1 with x; rw [hd]; ring
      _ = -(∫ x, dX j (fun y => f y j) x * Φ x k * f x k) -
            ∫ x, f x j * f x k * dX j (fun y => Φ y k) x := by
          rw [integral_add (ijk'' j k) (ijk' j k)]; ring
  have hsum : ∀ k, ∑ j, ∫ x, dX j (fun y => f y j) x * Φ x k * f x k = 0 := by
    intro k
    rw [← integral_finsetSum _ fun j _ => ijk'' j k]
    have : ∀ x, ∑ j, dX j (fun y => f y j) x * Φ x k * f x k = 0 := by
      intro x
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      have hd0 : ∑ j, dX j (fun y => f y j) x = 0 := by
        rw [← hdivf x]; unfold div
        exact Finset.sum_congr rfl fun j _ => (hdf x j j).symm
      rw [hd0, zero_mul, zero_mul]
    simp_rw [this, integral_zero]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => ijk j k]
  have hk : ∀ k, ∫ x, ∑ j, f x j * dX j (fun y => f y k) x * Φ x k =
      -∑ j, ∫ x, f x j * f x k * dX j (fun y => Φ y k) x := by
    intro k
    rw [integral_finsetSum _ fun j _ => ijk j k,
      Finset.sum_congr rfl fun j _ => key j k, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      hsum k, neg_zero, zero_sub]
  rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_neg_distrib]
  have i5 : ∀ k ∈ Finset.univ, Integrable fun x =>
      ∑ j, f x j * f x k * dX j (fun y => Φ y k) x := fun k _ =>
    integrable_finsetSum _ fun j _ => ijk' j k
  have e5 : ∀ x, ∑ j, ∑ k, f x j * f x k * dX j Φ x k =
      ∑ k, ∑ j, f x j * f x k * dX j (fun y => Φ y k) x := by
    intro x
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by rw [hdΦ]
  simp_rw [e5]
  rw [integral_finsetSum _ i5]
  congr 1
  exact Finset.sum_congr rfl fun k _ => (integral_finsetSum _ fun j _ => ijk' j k).symm

end


/-! ### Suportes -/

theorem dX_of_not_mem {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {g : E3 → W} {x : E3}
    (hx : x ∉ tsupport g) (j : Fin 3) : dX j g x = 0 := by
  have : fderiv ℝ g x = 0 := by
    by_contra h
    exact hx (support_fderiv_subset (𝕜 := ℝ) h)
  simp [dX, this]

theorem tsupport_dX {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (g : E3 → W)
    (j : Fin 3) : tsupport (dX j g) ⊆ tsupport g := by
  refine closure_minimal ?_ (isClosed_tsupport g)
  intro x hx
  by_contra h
  exact hx (dX_of_not_mem h j)

theorem lap_of_not_mem {g : E3 → E3} {x : E3} (hx : x ∉ tsupport g) : lap g x = 0 := by
  unfold lap
  refine Finset.sum_eq_zero fun j _ => dX_of_not_mem (fun h => hx (tsupport_dX g j h)) j

/-! ### A formulação fraca -/

/-- O lado direito da formulação fraca. -/
noncomputable def Bw (ν : ℝ) (U : E3 × ℝ → E3) (Φ : E3 → E3) (s : ℝ) : ℝ :=
  ν * (∫ x, inner ℝ (U (x, s)) (lap Φ x)) + ∫ x, ∑ j, ∑ k, U (x, s) j * U (x, s) k * dX j Φ x k

section

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ} {Φ : E3 → E3}

theorem mapsTo_fatia {x : E3} {a b : ℝ} (h0 : 0 ≤ a) (hb : b < T) :
    MapsTo (fun r : ℝ => (x, r)) (Icc a b) (univ ×ˢ Ico 0 T) :=
  fun r hr => ⟨mem_univ _, h0.trans hr.1, hr.2.trans_lt hb⟩

/-- Continuidade de integrais paramétricas dominadas por `C |H|`, `H` de suporte compacto. -/
theorem continuousOn_integral_dom {F : E3 → ℝ → ℝ} {S : Set ℝ} {H : E3 → ℝ} (hH : Continuous H)
    (hHc : HasCompactSupport H) (hmeas : ∀ r ∈ S, Continuous fun x => F x r)
    (hcont : ∀ x, ContinuousOn (F x) S) {C : ℝ} (hb : ∀ r ∈ S, ∀ x, |F x r| ≤ C * |H x|) :
    ContinuousOn (fun r => ∫ x, F x r) S := by
  refine continuousOn_of_dominated (bound := fun x => C * |H x|) (fun r hr =>
    (hmeas r hr).aestronglyMeasurable) (fun r hr => Eventually.of_forall fun x => ?_)
    ((continuous_const.mul hH.abs).integrable_of_hasCompactSupport
      (hHc.norm.mul_left (f := fun _ => C) |>.mono fun x hx => by simpa using hx))
    (Eventually.of_forall fun x => hcont x)
  rw [Real.norm_eq_abs]; exact hb r hr x

/-- Cota de `U` num compacto `K × [a, b]` dentro da faixa. -/
theorem bound_U (hU : ContDiffOn ℝ ∞ U (univ ×ˢ Ico 0 T)) {K : Set E3} (hK : IsCompact K)
    {a b : ℝ} (ha : 0 ≤ a) (hb : b < T) :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ K, ∀ r ∈ Icc a b, ‖U (x, r)‖ ≤ M := by
  have hsub : K ×ˢ Icc a b ⊆ univ ×ˢ Ico 0 T := fun p hp =>
    ⟨mem_univ _, ha.trans hp.2.1, hp.2.2.trans_lt hb⟩
  obtain ⟨M, hM⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
    (hU.continuousOn.mono hsub)
  exact ⟨max M 0, le_max_right _ _, fun x hx r hr => (hM (x, r) ⟨hx, hr⟩).trans (le_max_left _ _)⟩

theorem continuous_fatia_U (hU : ContDiffOn ℝ ∞ U (univ ×ˢ Ico 0 T)) {r : ℝ} (hr : r ∈ Ico 0 T) :
    Continuous fun x => U (x, r) :=
  (contDiff_fatia hU hr).continuous

theorem continuousOn_U_r (hU : ContDiffOn ℝ ∞ U (univ ×ˢ Ico 0 T)) (x : E3) {t : ℝ}
    (ht : t < T) : ContinuousOn (fun r => U (x, r)) (Icc 0 t) :=
  hU.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (mapsTo_fatia le_rfl ht)

theorem contDiff_lap {g : E3 → E3} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (lap g) := by
  unfold lap
  exact ContDiff.sum fun j _ => contDiff_dX (contDiff_dX hg j) j

theorem hasCompactSupport_lap {g : E3 → E3} (hg : HasCompactSupport g) :
    HasCompactSupport (lap g) :=
  HasCompactSupport.intro hg fun x hx => lap_of_not_mem hx

/-- **Formulação fraca sem pressão.** Para qualquer solução suave `(U, P)` e qualquer campo-teste
`Φ` suave, de suporte compacto e de divergência nula:
`∫ ⟪U(t), Φ⟫ − ∫ ⟪u₀, Φ⟫ = ∫₀ᵗ (ν ∫ ⟪U(s), ΔΦ⟫ + ∫ Σⱼₖ Uⱼ Uₖ ∂ⱼΦₖ) ds`. -/
theorem formulacao_fraca (h : SolucaoLocal ν u₀ T U P) (hΦ : ContDiff ℝ ∞ Φ)
    (hc : HasCompactSupport Φ) (hdivΦ : ∀ x, div Φ x = 0) {t : ℝ} (ht : t ∈ Ico 0 T) :
    (∫ x, inner ℝ (U (x, t)) (Φ x)) - ∫ x, inner ℝ (u₀ x) (Φ x) =
      ∫ s in (0 : ℝ)..t, Bw ν U Φ s := by
  obtain ⟨hU, hP, h0, hns, hdiv, -⟩ := h
  set K := tsupport Φ with hKdef
  have hK : IsCompact K := hc
  have hΦ0 : ∀ x, x ∉ K → Φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hdΦ0 : ∀ x, x ∉ K → ∀ j, dX j Φ x = 0 := fun x hx j => dX_of_not_mem hx j
  have hlΦ0 : ∀ x, x ∉ K → lap Φ x = 0 := fun x hx => lap_of_not_mem hx
  set g : ℝ → ℝ := fun r => ∫ x, inner ℝ (U (x, r)) (Φ x) with hg
  obtain ⟨M, hM0, hM⟩ := bound_U hU hK le_rfl ht.2
  -- (1) continuidade de `g`
  have hgc : ContinuousOn g (Icc 0 t) := by
    refine continuousOn_integral_dom (H := fun x => ‖Φ x‖) hΦ.continuous.norm hc.norm
      (fun r hr => (continuous_fatia_U hU ⟨hr.1, hr.2.trans_lt ht.2⟩).inner hΦ.continuous)
      (fun x => (continuousOn_U_r hU x ht.2).inner continuousOn_const) (C := M) fun r hr x => ?_
    by_cases hx : x ∈ K
    · rw [abs_norm, ← Real.norm_eq_abs]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM x hx r hr)
        (norm_nonneg _))
    · rw [hΦ0 x hx, inner_zero_right, abs_zero, norm_zero, abs_zero, mul_zero]
  -- (2) continuidade de `Bw`
  have hBc : ContinuousOn (Bw ν U Φ) (Icc 0 t) := by
    unfold Bw
    refine ContinuousOn.add (ContinuousOn.mul (continuousOn_const (c := ν)) ?_) ?_
    · refine continuousOn_integral_dom (H := fun x => ‖lap Φ x‖) (contDiff_lap hΦ).continuous.norm
        (hasCompactSupport_lap hc).norm
        (fun r hr => (continuous_fatia_U hU ⟨hr.1, hr.2.trans_lt ht.2⟩).inner
          (contDiff_lap hΦ).continuous)
        (fun x => (continuousOn_U_r hU x ht.2).inner continuousOn_const) (C := M) fun r hr x => ?_
      by_cases hx : x ∈ K
      · rw [abs_norm, ← Real.norm_eq_abs]
        exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM x hx r hr)
          (norm_nonneg _))
      · rw [hlΦ0 x hx, inner_zero_right, abs_zero, norm_zero, abs_zero, mul_zero]
    · have hH : Continuous fun x => ∑ j, ‖dX j Φ x‖ :=
        continuous_finsetSum _ fun j _ => (continuous_dX hΦ j).norm
      have hHc : HasCompactSupport fun x => ∑ j, ‖dX j Φ x‖ :=
        HasCompactSupport.intro hK fun x hx => by simp [hdΦ0 x hx]
      refine continuousOn_integral_dom (H := fun x => ∑ j, ‖dX j Φ x‖) hH hHc
        (fun r hr => ?_) (fun x => ?_) (C := 3 * M ^ 2) fun r hr x => ?_
      · have hu := continuous_fatia_U hU ⟨hr.1, hr.2.trans_lt ht.2⟩
        have hu' : ∀ i, Continuous fun x => U (x, r) i := fun i =>
          (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous.comp hu
        have hd' : ∀ j k, Continuous fun x => dX j Φ x k := fun j k =>
          (EuclideanSpace.proj k : E3 →L[ℝ] ℝ).continuous.comp (continuous_dX hΦ j)
        exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
          ((hu' j).mul (hu' k)).mul (hd' j k)
      · have hu := continuousOn_U_r hU x ht.2
        have hu' : ∀ i, ContinuousOn (fun r => U (x, r) i) (Icc 0 t) := fun i =>
          (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous.comp_continuousOn hu
        exact continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ =>
          ((hu' j).mul (hu' k)).mul continuousOn_const
      · by_cases hx : x ∈ K
        · have hHn : 0 ≤ ∑ j, ‖dX j Φ x‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
          rw [abs_of_nonneg hHn]
          have hcomp : ∀ i, |U (x, r) i| ≤ M := fun i => by
            have := PiLp.norm_apply_le (U (x, r)) i
            rw [Real.norm_eq_abs] at this
            exact this.trans (hM x hx r hr)
          have hdc : ∀ j k, |dX j Φ x k| ≤ ‖dX j Φ x‖ := fun j k => by
            have := PiLp.norm_apply_le (dX j Φ x) k
            rwa [Real.norm_eq_abs] at this
          calc |∑ j, ∑ k, U (x, r) j * U (x, r) k * dX j Φ x k|
              ≤ ∑ j, ∑ k, |U (x, r) j * U (x, r) k * dX j Φ x k| :=
                (Finset.abs_sum_le_sum_abs _ _).trans
                  (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
            _ ≤ ∑ j, ∑ _k : Fin 3, M * M * ‖dX j Φ x‖ := by
                refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
                rw [abs_mul, abs_mul]
                exact mul_le_mul (mul_le_mul (hcomp j) (hcomp k) (abs_nonneg _) hM0) (hdc j k)
                  (abs_nonneg _) (by positivity)
            _ = 3 * M ^ 2 * ∑ j, ‖dX j Φ x‖ := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun j _ => ?_
                push_cast; ring
        · simp [hdΦ0 x hx]
  -- (3) a derivada de `g`
  have hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt g (Bw ν U Φ s) s := by
    intro s hs
    have hsT : s ∈ Ioo 0 T := ⟨hs.1, hs.2.trans ht.2⟩
    have hopen : IsOpen ((univ : Set E3) ×ˢ Ioo 0 T) := isOpen_univ.prod isOpen_Ioo
    have hUo : ContDiffOn ℝ ∞ U (univ ×ˢ Ioo 0 T) :=
      hU.mono (prod_mono subset_rfl Ioo_subset_Ico_self)
    have hfd : ContinuousOn (fderiv ℝ U) (univ ×ˢ Ioo 0 T) :=
      hUo.continuousOn_fderiv_of_isOpen hopen (by simp)
    set D : E3 → ℝ → E3 := fun x r => fderiv ℝ U (x, r) ((0 : E3), (1 : ℝ)) with hD
    have hDd : ∀ x, ∀ r ∈ Ioo 0 T, HasDerivAt (fun r' => U (x, r')) (D x r) r := by
      intro x r hr
      have hdiff : DifferentiableAt ℝ U (x, r) :=
        (hUo.contDiffAt (hopen.mem_nhds ⟨mem_univ _, hr⟩)).differentiableAt (by simp)
      have hp : HasDerivAt (fun r' : ℝ => (x, r')) ((0 : E3), (1 : ℝ)) r :=
        (hasDerivAt_const r x).prodMk (hasDerivAt_id r)
      exact hdiff.hasFDerivAt.comp_hasDerivAt r hp
    -- vizinhança compacta de `s` dentro de `(0, T)`
    set δ := min (s / 2) ((T - s) / 2) with hδ
    have hδ0 : 0 < δ := lt_min (by linarith [hsT.1]) (by linarith [hsT.2])
    have hS : Icc (s - δ) (s + δ) ⊆ Ioo 0 T := fun r hr =>
      ⟨by linarith [hr.1, min_le_left (s / 2) ((T - s) / 2)],
        by linarith [hr.2, min_le_right (s / 2) ((T - s) / 2)]⟩
    have hSn : Icc (s - δ) (s + δ) ∈ 𝓝 s := Icc_mem_nhds (by linarith) (by linarith)
    have hKS : IsCompact (K ×ˢ Icc (s - δ) (s + δ)) := hK.prod isCompact_Icc
    have hDc : ContinuousOn (fun p : E3 × ℝ => fderiv ℝ U p ((0 : E3), (1 : ℝ)))
        (univ ×ˢ Ioo 0 T) := hfd.clm_apply continuousOn_const
    obtain ⟨M', hM'⟩ := hKS.exists_bound_of_continuousOn
      (hDc.mono fun p hp => ⟨mem_univ _, hS hp.2⟩)
    have hM'0 : 0 ≤ max M' 0 := le_max_right _ _
    have hbint : Integrable fun x => max M' 0 * ‖Φ x‖ :=
      (continuous_const.mul hΦ.continuous.norm).integrable_of_hasCompactSupport
        (hc.norm.mul_left (f := fun _ => max M' 0))
    have hInt0 : Integrable fun x => inner ℝ (U (x, s)) (Φ x) :=
      ((continuous_fatia_U hU ⟨hsT.1.le, hsT.2⟩).inner hΦ.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hK fun x hx => by simp [hΦ0 x hx])
    have hDs : Continuous fun x => D x s :=
      hDc.comp_continuous (continuous_id.prodMk continuous_const) fun x => ⟨mem_univ _, hsT⟩
    have hF := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (F := fun r x => inner ℝ (U (x, r)) (Φ x))
      (F' := fun r x => inner ℝ (D x r) (Φ x)) (bound := fun x => max M' 0 * ‖Φ x‖) hSn
      (by
        filter_upwards [hSn] with r hr
        exact ((continuous_fatia_U hU ⟨(hS hr).1.le, (hS hr).2⟩).inner
          hΦ.continuous).aestronglyMeasurable)
      hInt0 (hDs.inner hΦ.continuous).aestronglyMeasurable
      (Eventually.of_forall fun x r hr => by
        by_cases hx : x ∈ K
        · refine (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
          exact (hM' (x, r) ⟨hx, hr⟩).trans (le_max_left _ _)
        · simp [hΦ0 x hx])
      hbint
      (Eventually.of_forall fun x r hr => by
        have := (hDd x r (hS hr)).inner ℝ (hasDerivAt_const r (Φ x))
        simpa using this)
    have hgd : HasDerivAt g (∫ x, inner ℝ (D x s) (Φ x)) s := hF.2
    -- identificação com `Bw`
    have hsI : s ∈ Ico 0 T := ⟨hsT.1.le, hsT.2⟩
    set f := fatia U s with hf
    have hfc : ContDiff ℝ ∞ f := contDiff_fatia hU hsI
    have hpc : ContDiff ℝ ∞ (fatia P s) := contDiff_fatia hP hsI
    have hDeq : ∀ x, D x s = ν • lap f x - grad (fatia P s) x - conv f x := by
      intro x
      have hns' := hns x s hsT
      unfold NSEq at hns'
      rw [← (hDd x s hsT).deriv]
      rw [← hns']
      abel
    have hcsI : ∀ {F : E3 → E3}, Continuous F → Integrable fun x => inner ℝ (F x) (Φ x) :=
      fun {F} hF => (hF.inner hΦ.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.intro hK fun x hx => by simp [hΦ0 x hx])
    have cl : Continuous (lap f) := (contDiff_lap hfc).continuous
    have cg : Continuous (grad (fatia P s)) := by
      unfold grad
      exact continuous_finsetSum _ fun j _ => (continuous_dX hpc j).smul continuous_const
    have cc : Continuous (conv f) := by
      unfold conv
      refine continuous_finsetSum _ fun j _ => ?_
      have h1 : Continuous fun x => f x j :=
        (EuclideanSpace.proj j : E3 →L[ℝ] ℝ).continuous.comp hfc.continuous
      exact h1.smul (continuous_dX hfc j)
    have hint_eq : ∫ x, inner ℝ (D x s) (Φ x) = Bw ν U Φ s := by
      simp_rw [hDeq, inner_sub_left, real_inner_smul_left]
      have i1 : Integrable fun x => ν * inner ℝ (lap f x) (Φ x) := (hcsI cl).const_mul ν
      have i2 : Integrable fun x => inner ℝ (grad (fatia P s) x) (Φ x) := hcsI cg
      have i12 : Integrable fun x => ν * inner ℝ (lap f x) (Φ x) -
          inner ℝ (grad (fatia P s) x) (Φ x) := i1.sub i2
      rw [integral_sub i12 (hcsI cc), integral_sub i1 i2, integral_const_mul,
        integral_inner_lap hΦ hc hfc, integral_inner_grad hΦ hc hpc hdivΦ,
        integral_inner_conv hΦ hc hfc (fun x => hdiv x s hsI)]
      unfold Bw
      simp only [hf, fatia]
      ring
    rw [← hint_eq]
    exact hgd
  -- (4) o teorema fundamental do cálculo
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hgc hderiv
    (hBc.intervalIntegrable_of_Icc ht.1)
  rw [hftc]
  simp only [hg, h0]


/-- **Continuidade do lado direito** `s ↦ Bw ν U Φ s` em `[0, t]`, `t < T`. -/
theorem continuousOn_Bw {ν T : ℝ} {U : E3 × ℝ → E3} {Φ : E3 → E3}
    (hU : ContDiffOn ℝ ∞ U (univ ×ˢ Ico 0 T)) (hΦ : ContDiff ℝ ∞ Φ) (hc : HasCompactSupport Φ)
    {t : ℝ} (ht : t ∈ Ico 0 T) : ContinuousOn (Bw ν U Φ) (Icc 0 t) := by
  set K := tsupport Φ with hKdef
  have hK : IsCompact K := hc
  have hdΦ0 : ∀ x, x ∉ K → ∀ j, dX j Φ x = 0 := fun x hx j => dX_of_not_mem hx j
  have hlΦ0 : ∀ x, x ∉ K → lap Φ x = 0 := fun x hx => lap_of_not_mem hx
  obtain ⟨M, hM0, hM⟩ := bound_U hU hK le_rfl ht.2
  unfold Bw
  refine ContinuousOn.add (ContinuousOn.mul (continuousOn_const (c := ν)) ?_) ?_
  · refine continuousOn_integral_dom (H := fun x => ‖lap Φ x‖) (contDiff_lap hΦ).continuous.norm
      (hasCompactSupport_lap hc).norm
      (fun r hr => (continuous_fatia_U hU ⟨hr.1, hr.2.trans_lt ht.2⟩).inner
        (contDiff_lap hΦ).continuous)
      (fun x => (continuousOn_U_r hU x ht.2).inner continuousOn_const) (C := M) fun r hr x => ?_
    by_cases hx : x ∈ K
    · rw [abs_norm, ← Real.norm_eq_abs]
      exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM x hx r hr)
        (norm_nonneg _))
    · rw [hlΦ0 x hx, inner_zero_right, abs_zero, norm_zero, abs_zero, mul_zero]
  · have hH : Continuous fun x => ∑ j, ‖dX j Φ x‖ :=
      continuous_finsetSum _ fun j _ => (continuous_dX hΦ j).norm
    have hHc : HasCompactSupport fun x => ∑ j, ‖dX j Φ x‖ :=
      HasCompactSupport.intro hK fun x hx => by simp [hdΦ0 x hx]
    refine continuousOn_integral_dom (H := fun x => ∑ j, ‖dX j Φ x‖) hH hHc
      (fun r hr => ?_) (fun x => ?_) (C := 3 * M ^ 2) fun r hr x => ?_
    · have hu := continuous_fatia_U hU ⟨hr.1, hr.2.trans_lt ht.2⟩
      have hu' : ∀ i, Continuous fun x => U (x, r) i := fun i =>
        (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous.comp hu
      have hd' : ∀ j k, Continuous fun x => dX j Φ x k := fun j k =>
        (EuclideanSpace.proj k : E3 →L[ℝ] ℝ).continuous.comp (continuous_dX hΦ j)
      exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
        ((hu' j).mul (hu' k)).mul (hd' j k)
    · have hu := continuousOn_U_r hU x ht.2
      have hu' : ∀ i, ContinuousOn (fun r => U (x, r) i) (Icc 0 t) := fun i =>
        (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous.comp_continuousOn hu
      exact continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun k _ =>
        ((hu' j).mul (hu' k)).mul continuousOn_const
    · by_cases hx : x ∈ K
      · have hHn : 0 ≤ ∑ j, ‖dX j Φ x‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
        rw [abs_of_nonneg hHn]
        have hcomp : ∀ i, |U (x, r) i| ≤ M := fun i => by
          have := PiLp.norm_apply_le (U (x, r)) i
          rw [Real.norm_eq_abs] at this
          exact this.trans (hM x hx r hr)
        have hdc : ∀ j k, |dX j Φ x k| ≤ ‖dX j Φ x‖ := fun j k => by
          have := PiLp.norm_apply_le (dX j Φ x) k
          rwa [Real.norm_eq_abs] at this
        calc |∑ j, ∑ k, U (x, r) j * U (x, r) k * dX j Φ x k|
            ≤ ∑ j, ∑ k, |U (x, r) j * U (x, r) k * dX j Φ x k| :=
              (Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
          _ ≤ ∑ j, ∑ _k : Fin 3, M * M * ‖dX j Φ x‖ := by
              refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
              rw [abs_mul, abs_mul]
              exact mul_le_mul (mul_le_mul (hcomp j) (hcomp k) (abs_nonneg _) hM0) (hdc j k)
                (abs_nonneg _) (by positivity)
          _ = 3 * M ^ 2 * ∑ j, ‖dX j Φ x‖ := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              push_cast; ring
      · simp [hdΦ0 x hx]

end

end ATK.NSFraca

#print axioms ATK.NSFraca.inner_E3
#print axioms ATK.NSFraca.dX_comp
#print axioms ATK.NSFraca.contDiff_dX
#print axioms ATK.NSFraca.contDiff_comp
#print axioms ATK.NSFraca.continuous_dX
#print axioms ATK.NSFraca.hasCompactSupport_dX
#print axioms ATK.NSFraca.dX_mul
#print axioms ATK.NSFraca.hcs_mul
#print axioms ATK.NSFraca.ibp
#print axioms ATK.NSFraca.integrable_cs
#print axioms ATK.NSFraca.hcs_comp
#print axioms ATK.NSFraca.lap_comp
#print axioms ATK.NSFraca.integral_inner_lap
#print axioms ATK.NSFraca.integral_inner_grad
#print axioms ATK.NSFraca.integral_inner_conv
#print axioms ATK.NSFraca.dX_of_not_mem
#print axioms ATK.NSFraca.tsupport_dX
#print axioms ATK.NSFraca.lap_of_not_mem
#print axioms ATK.NSFraca.mapsTo_fatia
#print axioms ATK.NSFraca.continuousOn_integral_dom
#print axioms ATK.NSFraca.bound_U
#print axioms ATK.NSFraca.continuous_fatia_U
#print axioms ATK.NSFraca.continuousOn_U_r
#print axioms ATK.NSFraca.contDiff_lap
#print axioms ATK.NSFraca.hasCompactSupport_lap
#print axioms ATK.NSFraca.formulacao_fraca
#print axioms ATK.NSFraca.continuousOn_Bw
