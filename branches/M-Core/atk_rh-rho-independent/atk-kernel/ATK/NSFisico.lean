import ATK.NSSuave
import ATK.NSSimetria
import Mathlib.MeasureTheory.Group.Prod

/-!
# ATK — Navier–Stokes: do lado de Fourier ao espaço físico

Camada 5 do ataque a B3. Para uma amplitude suave `b` (`ATK.NSSuave.Amp`) e
`V(x, t) = ∫ e^{2πi⟪ξ, x⟫} b(t, ξ) dξ`:

* **derivadas das fatias** (`dX_V`, `hasDerivAt_V_t`): `∂_{x_j} V(·, t) = V[2πiξ_j b]` em todo
  `x`, e `∂ₜ V(x, ·) = V[b 1]` no interior;
* **realidade** (`Vf_real`): se `b(t, ·)` é hermitiana, `V` é real (`conj V = V`), e então
  `V = cpx(re₃ V)` (`cpx_re3`);
* **o termo convectivo** (`conv_Vf`): para `f` de divergência nula (`⟪ξ, f(ξ)⟫ = 0`),
  `Σ_j V_j[f] · V[2πiξ_j f] = V[Nl(f, f)]` — o teorema da convolução, com Fubini e o
  cisalhamento `(η, ζ) ↦ (η, ζ − η)`.

**CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped Real

namespace ATK.NSFisico

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSSuave ATK.NSSimetria

/-! ### Linearidade de `Vf` -/

theorem Vf_add {f g : E3 → C3} {x : E3} (hf : Integrable fun ξ => ex x ξ • f ξ)
    (hg : Integrable fun ξ => ex x ξ • g ξ) :
    Vf (fun ξ => f ξ + g ξ) x = Vf f x + Vf g x := by
  unfold Vf
  rw [← integral_add hf hg]
  simp only [smul_add]

theorem Vf_sub {f g : E3 → C3} {x : E3} (hf : Integrable fun ξ => ex x ξ • f ξ)
    (hg : Integrable fun ξ => ex x ξ • g ξ) :
    Vf (fun ξ => f ξ - g ξ) x = Vf f x - Vf g x := by
  unfold Vf
  rw [← integral_sub hf hg]
  simp only [smul_sub]

theorem Vf_smul (c : ℂ) (f : E3 → C3) (x : E3) : Vf (fun ξ => c • f ξ) x = c • Vf f x := by
  unfold Vf
  rw [← integral_smul]
  simp only [smul_comm (ex x _) c]

/-! ### A parte real -/

/-- Parte real componente a componente, `ℂ³ → ℝ³`. -/
noncomputable def re3 (v : C3) : E3 := WithLp.toLp 2 fun k => (v k).re

@[simp] theorem re3_apply (v : C3) (k : Fin 3) : re3 v k = (v k).re := rfl

/-- `re₃` como aplicação `ℝ`-linear contínua. -/
noncomputable def re3L : C3 →L[ℝ] E3 :=
  LinearMap.mkContinuous
    { toFun := re3
      map_add' := fun v w => by ext k; simp
      map_smul' := fun r v => by ext k; simp [Complex.real_smul] }
    1 (fun v => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => ?_)
      simp only [re3_apply, Real.norm_eq_abs, sq_abs]
      have := Complex.abs_re_le_norm (v k)
      nlinarith [abs_nonneg (v k).re, sq_abs (v k).re])

theorem re3L_apply (v : C3) : re3L v = re3 v := rfl

theorem cpx_re3 {v : C3} (hv : cj3 v = v) : cpx (re3 v) = v := by
  ext k
  have h := congrArg (fun u : C3 => u k) hv
  simp only [cj3_apply] at h
  have him : (v k).im = 0 := Complex.conj_eq_iff_im.mp h
  apply Complex.ext <;> simp [cpx, him]

theorem re3_cpx (ξ : E3) : re3 (cpx ξ) = ξ := by
  ext k; simp [cpx]

/-! ### Realidade -/

theorem conj_ex (x ξ : E3) : conj (ex x ξ) = ex x (-ξ) := by
  unfold ex
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, inner_neg_left]
  congr 1
  push_cast
  ring

/-- **`V` de uma amplitude hermitiana é real.** -/
theorem Vf_real {f : E3 → C3} (hf : Herm f) (x : E3) : cj3 (Vf f x) = Vf f x := by
  unfold Vf
  rw [← integral_cj3]
  rw [← integral_neg_eq_self (fun ξ => ex x ξ • f ξ)]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [cj3_smul, conj_ex, hf ξ]

/-! ### Derivadas das fatias -/

/-- A derivada de `y ↦ V(y, t)`. -/
theorem Amp.hasFDerivAt_fatia {T : ℝ} {b : ℕ → ℝ → E3 → C3} (hb : Amp T b) {t : ℝ}
    (ht : t ∈ Icc 0 T) (x : E3) :
    HasFDerivAt (fun y => V (b 0) (y, t))
      ((Lmap b (x, t)).comp ((ContinuousLinearMap.id ℝ E3).prod 0)) x := by
  have hV := hb.hasFDerivWithinAt_V (p := (x, t)) ⟨mem_univ _, ht⟩
  have hg : HasFDerivAt (fun y : E3 => (y, t)) ((ContinuousLinearMap.id ℝ E3).prod 0) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  have := hV.comp x hg.hasFDerivWithinAt (s := univ)
    (fun y _ => show (y, t) ∈ univ ×ˢ Icc 0 T from ⟨mem_univ _, ht⟩)
  exact hasFDerivWithinAt_univ.mp this

theorem sum_single_smul (j : Fin 3) (W : Fin 3 → C3) :
    ∑ k, (EuclideanSpace.single j (1 : ℝ) : E3) k • W k = W j := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk; simp [PiLp.single_apply, hk]
  · simp

/-- `∂_{x_j} V(·, t) = V[2πiξ_j b]`. -/
theorem Amp.dX_V {T : ℝ} {b : ℕ → ℝ → E3 → C3} (hb : Amp T b) {t : ℝ} (ht : t ∈ Icc 0 T)
    (j : Fin 3) (x : E3) :
    dX j (fun y => V (b 0) (y, t)) x = V (mulC (cj j) b 0) (x, t) := by
  have h := Amp.hasFDerivAt_fatia hb ht x
  unfold dX
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply, Lmap_apply, zero_smul,
    add_zero]
  exact sum_single_smul j _

/-- `∂ₜ V(x, ·) = V[b 1]` no interior. -/
theorem Amp.hasDerivAt_V_t {T : ℝ} {b : ℕ → ℝ → E3 → C3} (hb : Amp T b) {t : ℝ}
    (ht : t ∈ Ioo 0 T) (x : E3) :
    HasDerivAt (fun s => V (b 0) (x, s)) (V (b 1) (x, t)) t := by
  have hV := hb.hasFDerivWithinAt_V (p := (x, t)) ⟨mem_univ _, Ioo_subset_Icc_self ht⟩
  have hn : univ ×ˢ Icc 0 T ∈ 𝓝 (x, t) :=
    prod_mem_nhds univ_mem (Icc_mem_nhds ht.1 ht.2)
  have hV' := hV.hasFDerivAt hn
  have hg : HasDerivAt (fun s : ℝ => (x, s)) ((0 : E3), (1 : ℝ)) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have := hV'.comp_hasDerivAt t hg
  rw [Lmap_apply] at this
  simp only [PiLp.zero_apply, zero_smul, Finset.sum_const_zero, one_smul,
    zero_add] at this
  exact this

/-! ### O termo convectivo: o teorema da convolução -/

theorem ex_add_right (x η ζ : E3) : ex x (η + ζ) = ex x η * ex x ζ := by
  unfold ex
  rw [← Complex.exp_add, inner_add_left]
  congr 1
  push_cast
  ring

theorem cpx_sub (ξ η : E3) : cpx (ξ - η) = cpx ξ - cpx η := by
  ext k; simp [cpx]

theorem sum_cj_mul (ζ : E3) (v : C3) :
    ∑ j, v j * cj j ζ = ((2 * π : ℝ) * Complex.I : ℂ) * inner ℂ (cpx ζ) v := by
  rw [inner_cpx]
  simp only [cj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

theorem Vf_apply {f : E3 → C3} {x : E3} (hf : Integrable fun ξ => ex x ξ • f ξ) (j : Fin 3) :
    Vf f x j = ∫ ξ, ex x ξ * f ξ j := by
  unfold Vf
  have := (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) j).integral_comp_comm hf
  simp only [PiLp.proj_apply] at this
  rw [← this]
  simp

/-- **O termo convectivo (teorema da convolução)**: para `f` contínua, de decaimento rápido e de
divergência nula, `Σ_j V_j[f](x) · V[2πiξ_j f](x) = V[Nl(f, f)](x)`. -/
theorem conv_Vf {f : E3 → C3} (hf : Continuous f) {A : ℝ} (hA : ∀ ξ, ‖f ξ‖ ≤ A * (w 5 ξ)⁻¹)
    (hdiv : ∀ ξ, inner ℂ (cpx ξ) (f ξ) = 0) (x : E3) :
    ∑ j, Vf f x j • Vf (fun ζ => cj j ζ • f ζ) x = Vf (Nl f f) x := by
  have hA0 : 0 ≤ A := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hA 0))
    (inv_pos.mpr (w_pos 5 0))
  have hA4 : ∀ ξ, ‖f ξ‖ ≤ A * (w 4 ξ)⁻¹ := fun ξ =>
    (hA ξ).trans (mul_le_mul_of_nonneg_left (w_inv_anti (by norm_num) ξ) hA0)
  set μ : Measure E3 := volume
  -- integrabilidades básicas
  have hfi : Integrable f := (integrable_w_inv.const_mul A).mono' hf.aestronglyMeasurable
    (Eventually.of_forall hA4)
  have hg : ∀ j, Integrable fun η => ex x η * f η j := by
    intro j
    refine (hfi.norm).mono' ((continuous_ex_right x).mul
      ((PiLp.continuous_apply 2 _ j).comp hf)).aestronglyMeasurable
      (Eventually.of_forall fun η => ?_)
    rw [norm_mul, norm_ex, one_mul]
    exact PiLp.norm_apply_le (f η) j
  have hzf : Integrable fun ζ => ‖ζ‖ * ‖f ζ‖ := by
    refine (integrable_w_inv.const_mul A).mono' (continuous_norm.mul hf.norm).aestronglyMeasurable
      (Eventually.of_forall fun ζ => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    calc ‖ζ‖ * ‖f ζ‖ ≤ w 1 ζ * (A * (w 5 ζ)⁻¹) :=
          mul_le_mul (norm_le_w1 ζ) (hA ζ) (norm_nonneg _) (w_pos 1 ζ).le
      _ = A * (w 4 ζ)⁻¹ := by
          rw [show (5 : ℕ) = 4 + 1 from rfl, w_add]
          have := w_pos 4 ζ; have := w_pos 1 ζ; field_simp
  have hh : ∀ j, Integrable fun ζ => ex x ζ • (cj j ζ • f ζ) := by
    intro j
    refine (hzf.const_mul (2 * π)).mono' ((continuous_ex_right x).smul
      ((continuous_cj j).smul hf)).aestronglyMeasurable (Eventually.of_forall fun ζ => ?_)
    rw [norm_smul, norm_ex, one_mul, norm_smul]
    calc ‖cj j ζ‖ * ‖f ζ‖ ≤ (2 * π * ‖ζ‖) * ‖f ζ‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          unfold cj
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
            abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have := PiLp.norm_apply_le ζ j
          rwa [Real.norm_eq_abs] at this
      _ = 2 * π * (‖ζ‖ * ‖f ζ‖) := by ring
  have hvi : Integrable fun ξ => ex x ξ • f ξ := by
    refine hfi.norm.mono' ((continuous_ex_right x).smul hf).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [norm_smul, norm_ex, one_mul]
  -- passo 1: produto de integrais = integral no produto
  have h1 : ∀ j, Vf f x j • Vf (fun ζ => cj j ζ • f ζ) x =
      ∫ z, (ex x z.1 * f z.1 j) • (ex x z.2 • (cj j z.2 • f z.2)) ∂(μ.prod μ) := by
    intro j
    rw [Vf_apply hvi j]
    exact (integral_prod_smul (fun η => ex x η * f η j)
      (fun ζ => ex x ζ • (cj j ζ • f ζ))).symm
  -- passo 2: soma
  set F : E3 × E3 → C3 := fun z => ex x (z.1 + z.2) •
    ((((2 * π : ℝ) * Complex.I : ℂ) * inner ℂ (cpx z.2) (f z.1)) • f z.2) with hF
  have hsum : ∀ z : E3 × E3, ∑ j, (ex x z.1 * f z.1 j) • (ex x z.2 • (cj j z.2 • f z.2)) = F z := by
    intro z
    simp only [hF, smul_smul, ← Finset.sum_smul]
    congr 1
    rw [ex_add_right, ← sum_cj_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint1 : ∀ j, Integrable (fun z : E3 × E3 => (ex x z.1 * f z.1 j) •
      (ex x z.2 • (cj j z.2 • f z.2))) (μ.prod μ) := fun j => (hg j).smul_prod (hh j)
  have h2 : ∑ j, Vf f x j • Vf (fun ζ => cj j ζ • f ζ) x = ∫ z, F z ∂(μ.prod μ) := by
    simp only [h1]
    rw [← integral_finset_sum _ fun j _ => hint1 j]
    exact integral_congr_ae (Eventually.of_forall hsum)
  -- integrabilidade de `F`
  have hFc : Continuous F := by
    rw [hF]
    have e1 : Continuous fun z : E3 × E3 => ex x (z.1 + z.2) :=
      (continuous_ex_right x).comp (continuous_fst.add continuous_snd)
    have e2 : Continuous fun z : E3 × E3 => inner ℂ (cpx z.2) (f z.1) :=
      Continuous.inner (𝕜 := ℂ) (ATK.NSPicard.continuous_cpx.comp continuous_snd)
        (hf.comp continuous_fst)
    exact e1.smul ((continuous_const.mul e2).smul (hf.comp continuous_snd))
  have hFi : Integrable F (μ.prod μ) := by
    have hP : Integrable (fun z : E3 × E3 => ‖f z.1‖ * (2 * π * (‖z.2‖ * ‖f z.2‖))) (μ.prod μ) :=
      hfi.norm.mul_prod (hzf.const_mul (2 * π))
    refine hP.mono' hFc.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
    rw [hF]
    simp only
    rw [norm_smul, norm_ex, one_mul, norm_smul, norm_mul]
    have hcn : ‖((2 * π : ℝ) * Complex.I : ℂ)‖ = 2 * π := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    rw [hcn]
    have := norm_inner_cpx_le z.2 (f z.1)
    calc 2 * π * ‖inner ℂ (cpx z.2) (f z.1)‖ * ‖f z.2‖
        ≤ 2 * π * (‖z.2‖ * ‖f z.1‖) * ‖f z.2‖ := by gcongr
      _ = ‖f z.1‖ * (2 * π * (‖z.2‖ * ‖f z.2‖)) := by ring
  -- passo 3: cisalhamento `(η, ξ) ↦ (η, ξ − η)`
  have hS : MeasurePreserving (MeasurableEquiv.shearSubRight E3) (μ.prod μ) (μ.prod μ) :=
    measurePreserving_prod_sub μ μ
  have h3 : ∫ z, F z ∂(μ.prod μ) = ∫ z, F (MeasurableEquiv.shearSubRight E3 z) ∂(μ.prod μ) :=
    (hS.integral_comp' F).symm
  have hHi : Integrable (fun z => F (MeasurableEquiv.shearSubRight E3 z)) (μ.prod μ) :=
    (hS.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hFi
  -- passo 4: Fubini
  have h4 := integral_prod_symm _ hHi
  rw [h2, h3, h4]
  unfold Vf
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  have hpt : ∀ η, F (MeasurableEquiv.shearSubRight E3 (η, ξ)) =
      ex x ξ • (((2 * π : ℝ) * Complex.I : ℂ) • (inner ℂ (cpx ξ) (f η) • f (ξ - η))) := by
    intro η
    show ex x (η + (ξ - η)) • ((((2 * π : ℝ) * Complex.I : ℂ) * inner ℂ (cpx (ξ - η)) (f η)) •
      f (ξ - η)) = _
    rw [show η + (ξ - η) = ξ by abel, cpx_sub, inner_sub_left, hdiv η, sub_zero, mul_smul]
  simp only [hpt]
  rw [integral_smul, integral_smul]
  rfl

end ATK.NSFisico

#print axioms ATK.NSFisico.Vf_add
#print axioms ATK.NSFisico.Vf_sub
#print axioms ATK.NSFisico.Vf_smul
#print axioms ATK.NSFisico.re3L_apply
#print axioms ATK.NSFisico.cpx_re3
#print axioms ATK.NSFisico.re3_cpx
#print axioms ATK.NSFisico.conj_ex
#print axioms ATK.NSFisico.Vf_real
#print axioms ATK.NSFisico.Amp.hasFDerivAt_fatia
#print axioms ATK.NSFisico.sum_single_smul
#print axioms ATK.NSFisico.Amp.dX_V
#print axioms ATK.NSFisico.Amp.hasDerivAt_V_t
#print axioms ATK.NSFisico.ex_add_right
#print axioms ATK.NSFisico.cpx_sub
#print axioms ATK.NSFisico.sum_cj_mul
#print axioms ATK.NSFisico.Vf_apply
#print axioms ATK.NSFisico.conv_Vf
