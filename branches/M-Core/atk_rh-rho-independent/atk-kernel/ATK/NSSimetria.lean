import ATK.NSMild

/-!
# ATK — Navier–Stokes: simetria hermitiana da solução branda

Camada 4b do ataque a B3. Um campo real tem transformada de Fourier **hermitiana**:
`â(−ξ) = conj â(ξ)` (componente a componente). Aqui:

* `cj3`: conjugação componente a componente em `ℂ³` (isometria `ℝ`-linear, comuta com integrais);
* `Nl_herm`: o termo não linear preserva a simetria (mudança de variáveis `η ↦ −η`);
* `lp_herm`: o projetor de Leray também (`P(−ξ) conj v = conj P(ξ) v`);
* `it_herm`, `lim_herm`: as iteradas de Picard e o limite são hermitianos;
* **`existe_branda_herm`**: a solução branda de `ATK.NSMild.existe_branda`, agora com a simetria
  (é o que torna real o campo de velocidades reconstruído).

**CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped Real

namespace ATK.NSSimetria

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSPicard ATK.NSMild

/-! ### Conjugação em `ℂ³` -/

/-- Conjugação componente a componente. -/
noncomputable def cj3 (v : C3) : C3 := WithLp.toLp 2 fun k => conj (v k)

@[simp] theorem cj3_apply (v : C3) (k : Fin 3) : cj3 v k = conj (v k) := rfl

theorem cj3_add (v v' : C3) : cj3 (v + v') = cj3 v + cj3 v' := by
  ext k; simp

theorem cj3_sub (v v' : C3) : cj3 (v - v') = cj3 v - cj3 v' := by
  ext k; simp

theorem cj3_neg (v : C3) : cj3 (-v) = -cj3 v := by
  ext k; simp

theorem cj3_zero : cj3 0 = 0 := by
  ext k; simp

theorem cj3_smul (c : ℂ) (v : C3) : cj3 (c • v) = conj c • cj3 v := by
  ext k; simp

theorem cj3_real_smul (r : ℝ) (v : C3) : cj3 (r • v) = r • cj3 v := by
  ext k; simp [Complex.real_smul, map_mul, Complex.conj_ofReal]

theorem norm_cj3 (v : C3) : ‖cj3 v‖ = ‖v‖ := by
  simp [EuclideanSpace.norm_eq, Complex.norm_conj]

/-- `cj3` como isometria `ℝ`-linear. -/
noncomputable def cj3Li : C3 →ₗᵢ[ℝ] C3 where
  toFun := cj3
  map_add' := cj3_add
  map_smul' r v := cj3_real_smul r v
  norm_map' := norm_cj3

theorem integral_cj3 {X : Type*} [MeasurableSpace X] {μ : Measure X} (f : X → C3) :
    ∫ x, cj3 (f x) ∂μ = cj3 (∫ x, f x ∂μ) :=
  cj3Li.integral_comp_comm f

theorem intervalIntegral_cj3 (f : ℝ → C3) (a b : ℝ) :
    ∫ s in a..b, cj3 (f s) = cj3 (∫ s in a..b, f s) := by
  simp only [intervalIntegral, integral_cj3, cj3_sub]

theorem continuous_cj3 : Continuous cj3 := cj3Li.continuous

/-! ### Simetria -/

/-- `f` hermitiana: `f(−ξ) = conj f(ξ)`. -/
def Herm (f : E3 → C3) : Prop := ∀ ξ, f (-ξ) = cj3 (f ξ)

theorem cpx_neg (ξ : E3) : cpx (-ξ) = -cpx ξ := by
  ext k; simp [cpx]

theorem inner_cpx_cj3 (ξ : E3) (v : C3) : inner ℂ (cpx ξ) (cj3 v) = conj (inner ℂ (cpx ξ) v) := by
  simp only [inner_cpx, cj3_apply, map_sum, map_mul, Complex.conj_ofReal]

/-- `P(−ξ) conj v = conj P(ξ) v`. -/
theorem lp_herm (ξ : E3) (v : C3) : lp (-ξ) (cj3 v) = cj3 (lp ξ v) := by
  unfold lp
  rw [cpx_neg, norm_neg, inner_neg_left, inner_cpx_cj3, cj3_sub, cj3_smul]
  congr 1
  rw [neg_div, neg_smul, smul_neg, neg_neg, map_div₀, Complex.conj_ofReal]
  congr 1
  ext k; simp [cpx]

/-- **`Nl` preserva a simetria hermitiana.** -/
theorem Nl_herm {f g : E3 → C3} (hf : Herm f) (hg : Herm g) (ξ : E3) :
    Nl f g (-ξ) = cj3 (Nl f g ξ) := by
  unfold Nl
  rw [cj3_smul, ← integral_cj3]
  have hc : conj ((2 * π : ℝ) * Complex.I : ℂ) = -((2 * π : ℝ) * Complex.I : ℂ) := by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  rw [hc, ← integral_neg_eq_self (fun η => inner ℂ (cpx (-ξ)) (f η) • g (-ξ - η)), neg_smul,
    ← smul_neg, ← integral_neg]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only
  rw [hf η, show -ξ - -η = -(ξ - η) by abel, hg (ξ - η), cpx_neg, inner_neg_left,
    inner_cpx_cj3, cj3_smul, neg_smul]

theorem herm_heat_smul {f : E3 → C3} (hf : Herm f) (ν t : ℝ) :
    Herm fun ξ => heat ν t ξ • f ξ := by
  intro ξ
  simp only [heat_neg, hf ξ, cj3_real_smul]

theorem duhI_herm (ν : ℝ) {a : ℝ → E3 → C3} (ha : ∀ s, Herm (a s)) (τ s : ℝ) (ξ : E3) :
    duhI ν a a τ s (-ξ) = cj3 (duhI ν a a τ s ξ) := by
  unfold duhI
  rw [heat_neg, Nl_herm (ha s) (ha s), lp_herm, cj3_real_smul]

theorem Phi_herm {ν T : ℝ} {a₀ : E3 → C3} (h₀ : Herm a₀) {a : ℝ → E3 → C3}
    (ha : ∀ s, Herm (a s)) (t : ℝ) : Herm (Phi ν T a₀ a t) := by
  intro ξ
  unfold Phi
  rw [heat_neg, h₀ ξ, cj3_sub, cj3_real_smul, ← intervalIntegral_cj3]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  exact duhI_herm ν ha _ s ξ

/-- As iteradas de Picard são hermitianas. -/
theorem it_herm {ν T : ℝ} {a₀ : E3 → C3} (h₀ : Herm a₀) : ∀ n t, Herm (it ν T a₀ n t) := by
  intro n
  induction n with
  | zero => intro t; exact herm_heat_smul h₀ ν _
  | succ n ih => intro t; exact Phi_herm h₀ ih t

/-- O limite é hermitiano. -/
theorem lim_herm {ν M T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTT : T ≤ T0 ν M)
    {a₀ : E3 → C3} (h₀ : Dado a₀ M) (hh : Herm a₀) (t : ℝ) : Herm (lim ν T a₀ t) := by
  intro ξ
  have h1 := tendsto_it hν hT hTT h₀ t (-ξ)
  have h2 := (continuous_cj3.tendsto _).comp (tendsto_it hν hT hTT h₀ t ξ)
  have e : (fun n => it ν T a₀ n t (-ξ)) = cj3 ∘ fun n => it ν T a₀ n t ξ := by
    funext n; exact it_herm hh n t ξ
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2

/-- **Solução branda com simetria hermitiana.** -/
theorem existe_branda_herm {ν M : ℝ} (hν : 0 < ν) {a₀ : E3 → C3} (h₀ : Dado a₀ M)
    (hdiv : ∀ ξ, inner ℂ (cpx ξ) (a₀ ξ) = 0) (hh : Herm a₀) :
    ∃ T > 0, ∃ a : ℝ → E3 → C3, Boa4 a (2 * M) ∧
      (∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a₀ ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ) ∧
      (∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0) ∧
      (∀ t, a t = a (cl T t)) ∧
      (∀ (m : ℕ) (Mm : ℝ), (∀ ξ, ‖a₀ ξ‖ ≤ Mm * (w m ξ)⁻¹) →
        ∃ C, ∀ t ξ, ‖a t ξ‖ ≤ C * (w m ξ)⁻¹) ∧
      ∀ t, Herm (a t) := by
  have hM := h₀.nonneg
  set T := T0 ν M
  have hT := T0_pos hν hM
  refine ⟨T, hT, lim ν T a₀, lim_boa hν hT.le le_rfl h₀, fun t ht ξ => ?_, fun t ξ => ?_,
    fun t => ?_, fun m Mm hm => ?_, lim_herm hν hT.le le_rfl h₀ hh⟩
  · have := (lim_fixo hν hT.le le_rfl h₀ t ξ).symm
    rw [this]
    unfold Phi
    rw [cl_of_mem ht]
  · rw [← lim_fixo hν hT.le le_rfl h₀ t ξ]
    exact inner_Phi hdiv (lim_boa hν hT.le le_rfl h₀) t ξ
  · funext ξ
    rw [← lim_fixo hν hT.le le_rfl h₀ t ξ, ← lim_fixo hν hT.le le_rfl h₀ (cl T t) ξ]
    unfold Phi
    have : cl T (cl T t) = cl T t := cl_of_mem (cl_mem hT.le t)
    rw [this]
  · refine ⟨2 * Mm * Real.exp (kap ν M m * T), fun t ξ => ?_⟩
    have hMm : 0 ≤ Mm := by
      have := (norm_nonneg _).trans (hm 0)
      exact nonneg_of_mul_nonneg_left this (inv_pos.mpr (w_pos m 0))
    refine (lim_bound_m hν hT.le le_rfl h₀ hm t ξ).trans ?_
    have hk : 0 ≤ kap ν M m := by unfold kap; positivity
    have : Real.exp (kap ν M m * cl T t) ≤ Real.exp (kap ν M m * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (cl_mem hT.le t).2 hk)
    have hw := inv_pos.mpr (w_pos m ξ)
    gcongr

end ATK.NSSimetria

#print axioms ATK.NSSimetria.cj3_add
#print axioms ATK.NSSimetria.cj3_sub
#print axioms ATK.NSSimetria.cj3_neg
#print axioms ATK.NSSimetria.cj3_zero
#print axioms ATK.NSSimetria.cj3_smul
#print axioms ATK.NSSimetria.cj3_real_smul
#print axioms ATK.NSSimetria.norm_cj3
#print axioms ATK.NSSimetria.integral_cj3
#print axioms ATK.NSSimetria.intervalIntegral_cj3
#print axioms ATK.NSSimetria.continuous_cj3
#print axioms ATK.NSSimetria.cpx_neg
#print axioms ATK.NSSimetria.inner_cpx_cj3
#print axioms ATK.NSSimetria.lp_herm
#print axioms ATK.NSSimetria.Nl_herm
#print axioms ATK.NSSimetria.herm_heat_smul
#print axioms ATK.NSSimetria.duhI_herm
#print axioms ATK.NSSimetria.Phi_herm
#print axioms ATK.NSSimetria.it_herm
#print axioms ATK.NSSimetria.lim_herm
#print axioms ATK.NSSimetria.existe_branda_herm
