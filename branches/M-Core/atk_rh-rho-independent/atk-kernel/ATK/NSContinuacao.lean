import ATK.NSCotaUniforme

/-!
# ATK — Navier–Stokes: a continuação com enstrofia limitada (critério de Leray)

Camada 15 do ataque a B3: **`continuacaoF : ContinuacaoD (fun d => ClasseF d.1)`** — uma
solução da classe de Fourier em `[0, T)` com enstrofia limitada continua (na classe) além de `T`.

Ingredientes:

* `existe_branda_T`: a solução branda com tempo explícito `T₀(ν, M) = ν / L(M)²`;
* `amp_inj`: `V[f] = V[g] ⇒ f = g` (injetividade da transformada em `L²`);
* `enstrofia_eq`: `∫ |∇u|² = 4π² ∫ ‖ξ‖² ‖â‖²`;
* `colagem_amp`: concatenação de duas soluções brandas (propriedade de semigrupo do calor);
* `solucao_de_amp`: a solução física construída a partir de uma amplitude branda qualquer;
* a cota uniforme `ATK.NSCotaUniforme` dá um tempo de reinício uniforme `T₀(ν, M₄)`.

**CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology FourierTransform
open scoped Real ContDiff

namespace ATK.NSContinuacao

open ATK.LigacaoNS ATK.NSReducao ATK.NSFourierBase ATK.NSPicard ATK.NSMild ATK.NSSuave
  ATK.NSTempo ATK.NSSimetria ATK.NSFisico ATK.NSPressao ATK.NSDado ATK.NSPlancherel
  ATK.NSExistencia ATK.NSEnergia ATK.NSClasse ATK.NSEstimativas ATK.NSAltaOrdem
  ATK.NSCotaUniforme

/-! ### A solução branda com tempo explícito -/

/-- **Solução branda hermitiana em `[0, T₀(ν, M)]`** (tempo explícito). -/
theorem existe_branda_T {ν M : ℝ} (hν : 0 < ν) {a₀ : E3 → C3} (h₀ : Dado a₀ M)
    (hdiv : ∀ ξ, inner ℂ (cpx ξ) (a₀ ξ) = 0) (hh : Herm a₀) :
    ∃ a : ℝ → E3 → C3, Boa4 a (2 * M) ∧
      (∀ t ∈ Icc 0 (T0 ν M), ∀ ξ,
        a t ξ = heat ν t ξ • a₀ ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ) ∧
      (∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0) ∧
      (∀ (m : ℕ) (Mm : ℝ), (∀ ξ, ‖a₀ ξ‖ ≤ Mm * (w m ξ)⁻¹) →
        ∃ C, ∀ t ξ, ‖a t ξ‖ ≤ C * (w m ξ)⁻¹) ∧
      ∀ t, Herm (a t) := by
  have hM := h₀.nonneg
  set T := T0 ν M
  have hT := T0_pos hν hM
  refine ⟨lim ν T a₀, lim_boa hν hT.le le_rfl h₀, fun t ht ξ => ?_, fun t ξ => ?_,
    fun m Mm hm => ?_, lim_herm hν hT.le le_rfl h₀ hh⟩
  · have := (lim_fixo hν hT.le le_rfl h₀ t ξ).symm
    rw [this]
    unfold Phi
    rw [cl_of_mem ht]
  · rw [← lim_fixo hν hT.le le_rfl h₀ t ξ]
    exact inner_Phi hdiv (lim_boa hν hT.le le_rfl h₀) t ξ
  · refine ⟨2 * Mm * Real.exp (kap ν M m * T), fun t ξ => ?_⟩
    refine (lim_bound_m hν hT.le le_rfl h₀ hm t ξ).trans ?_
    have hMm : 0 ≤ Mm := by
      have := (norm_nonneg _).trans (hm 0)
      exact nonneg_of_mul_nonneg_left this (inv_pos.mpr (w_pos m 0))
    have hk : 0 ≤ kap ν M m := by unfold kap; positivity
    have : Real.exp (kap ν M m * cl T t) ≤ Real.exp (kap ν M m * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (cl_mem hT.le t).2 hk)
    have hw := inv_pos.mpr (w_pos m ξ)
    gcongr

/-! ### Injetividade da transformada -/

/-- **`V[f] = V[g] ⇒ f = g`** para amplitudes contínuas com decaimento `w₄⁻¹`. -/
theorem amp_inj {f g : E3 → C3} (hf : Continuous f) (hg : Continuous g) {A B : ℝ}
    (hA : ∀ ξ, ‖f ξ‖ ≤ A * (w 4 ξ)⁻¹) (hB : ∀ ξ, ‖g ξ‖ ≤ B * (w 4 ξ)⁻¹)
    (h : ∀ x, Vf f x = Vf g x) : f = g := by
  have hf1 := integrable_of_bound hf.aestronglyMeasurable hA
  have hf2 := memLp_two_of_bound hf.aestronglyMeasurable hA
  have hg1 := integrable_of_bound hg.aestronglyMeasurable hB
  have hg2 := memLp_two_of_bound hg.aestronglyMeasurable hB
  have e1 := fourierInv_toLp_ae_eq hf1 hf2
  have e2 := fourierInv_toLp_ae_eq hg1 hg2
  have hfg : 𝓕⁻ f = 𝓕⁻ g := funext fun x => by
    rw [← Vf_eq_fourierInv, ← Vf_eq_fourierInv, h]
  have hL : (𝓕⁻ (hf2.toLp f) : Lp C3 2 (volume : Measure E3)) = 𝓕⁻ (hg2.toLp g) := by
    refine Lp.ext ?_
    refine e1.trans ?_
    rw [hfg]
    exact e2.symm
  have hL' : hf2.toLp f = hg2.toLp g := by
    have := congrArg (fun u : Lp C3 2 (volume : Measure E3) => 𝓕 u) hL
    simpa [FourierTransform.fourier_fourierInv_eq] using this
  have hae : f =ᵐ[volume] g := (MemLp.toLp_eq_toLp_iff hf2 hg2).mp hL'
  exact (hf.ae_eq_iff_eq volume hg).mp hae

/-! ### A enstrofia no lado de Fourier -/

theorem herm_cj_smul {f : E3 → C3} (hf : Herm f) (j : Fin 3) :
    Herm fun ξ => cj j ξ • f ξ := by
  intro ξ
  simp only
  rw [hf ξ, cj3_smul]
  congr 1
  unfold cj
  simp only [PiLp.neg_apply, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem norm_cj_smul_sq (j : Fin 3) (ξ : E3) (v : C3) :
    ‖cj j ξ • v‖ ^ 2 = (2 * π * ξ j) ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_smul, mul_pow]
  congr 1
  unfold cj
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]

section

variable {ν T : ℝ} {a : ℝ → E3 → C3}

/-- **Enstrofia no lado de Fourier**: `∫ |∇u(t)|² = 4π² ∫ ‖ξ‖² ‖â(t)‖²`. -/
theorem enstrofia_eq (ha : BoaW a)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a 0 ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    (hherm : ∀ t, Herm (a t)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫ x, gradSq (fatia (Uf ν a) t) x = 4 * π ^ 2 * ∫ ξ, ‖ξ‖ ^ 2 * ‖a t ξ‖ ^ 2 := by
  obtain ⟨A, hA0, hA⟩ := ha.bound 5
  set g : Fin 3 → E3 → C3 := fun j ξ => cj j ξ • a t ξ with hg
  have hgm : ∀ j, AEStronglyMeasurable (g j) := fun j =>
    ((continuous_cj j).smul (ha.cont_s t)).aestronglyMeasurable
  have hgb : ∀ j ξ, ‖g j ξ‖ ≤ (2 * π * A) * (w 4 ξ)⁻¹ := fun j ξ => norm_cj_smul_le (hA t) j ξ
  have hP := fun j => integral_norm_sq_Vf (hgm j) (hgb j)
  have eD : ∀ j x, dX j (fatia (Uf ν a) t) x = re3 (Vf (g j) x) := by
    intro j x
    rw [dX_Uf ha hmild ht j x]
    have hm : mulC (cj j) (ader ν a) 0 t = g j := by
      funext ξ; simp [mulC, ader_zero, hg]
    simp only [V, hm]
  have hgr : ∀ x, gradSq (fatia (Uf ν a) t) x = ∑ j, ‖Vf (g j) x‖ ^ 2 := by
    intro x
    unfold gradSq
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eD, norm_re3_of_real (Vf_real (herm_cj_smul (hherm t) j) x)]
  simp_rw [hgr]
  rw [integral_finsetSum _ fun j _ => (hP j).1]
  simp_rw [fun j => (hP j).2]
  have hi : ∀ j, Integrable fun ξ => ‖g j ξ‖ ^ 2 := fun j => by
    have := memLp_two_of_bound (hgm j) (hgb j)
    exact (memLp_two_iff_integrable_sq_norm (hgm j)).mp this
  rw [← integral_finsetSum _ fun j _ => hi j, ← integral_const_mul]
  congr 1 with ξ
  simp only [hg, norm_cj_smul_sq]
  rw [← Finset.sum_mul, EuclideanSpace.real_norm_sq_eq]
  simp only [mul_pow, ← Finset.mul_sum]
  ring

/-- **`J₁` limitado pela energia e pela enstrofia.** -/
theorem J1_le_of (hν : 0 ≤ ν) (ha : BoaW a)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a 0 ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    (hherm : ∀ t, Herm (a t)) (hdivF : ∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0) {B : ℝ}
    {s : ℝ} (hs : s ∈ Icc 0 T) (hB : ∫ x, gradSq (fatia (Uf ν a) s) x ≤ B) :
    J 1 (a s) ≤ 2 * (∫ ξ, ‖a 0 ξ‖ ^ 2) + 2 * (B / (4 * π ^ 2)) := by
  have hE := energia_decresce hν ha hmild hherm hdivF hs
  have hEns := enstrofia_eq ha hmild hherm hs
  have hpi : 0 < 4 * π ^ 2 := by positivity
  have hK : ∫ ξ, ‖ξ‖ ^ 2 * ‖a s ξ‖ ^ 2 ≤ B / (4 * π ^ 2) := by
    rw [le_div_iff₀ hpi]; linarith
  have i1 := BoaW.integrable_norm_sq ha s
  have i2 : Integrable fun ξ => ‖ξ‖ ^ 2 * ‖a s ξ‖ ^ 2 := by
    refine (BoaW.integrable_J ha 1 s).mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · have c := ha.cont_s s
      exact (by fun_prop : Continuous fun ξ : E3 => ‖ξ‖ ^ 2 * ‖a s ξ‖ ^ 2).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      have : ‖ξ‖ ^ 2 ≤ w 1 ξ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_le_w1 ξ) 2
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  unfold J
  calc ∫ ξ, w 1 ξ ^ 2 * ‖a s ξ‖ ^ 2 ≤ ∫ ξ, (2 * ‖a s ξ‖ ^ 2 + 2 * (‖ξ‖ ^ 2 * ‖a s ξ‖ ^ 2)) :=
        integral_mono (BoaW.integrable_J ha 1 s) ((i1.const_mul 2).add (i2.const_mul 2))
          fun ξ => by
            have : w 1 ξ ^ 2 ≤ 2 + 2 * ‖ξ‖ ^ 2 := by
              unfold w; nlinarith [sq_nonneg (1 - ‖ξ‖), norm_nonneg ξ]
            nlinarith [sq_nonneg ‖a s ξ‖]
    _ = 2 * (∫ ξ, ‖a s ξ‖ ^ 2) + 2 * ∫ ξ, ‖ξ‖ ^ 2 * ‖a s ξ‖ ^ 2 := by
        rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul,
          integral_const_mul]
    _ ≤ 2 * (∫ ξ, ‖a 0 ξ‖ ^ 2) + 2 * (B / (4 * π ^ 2)) := by linarith

end


/-! ### Concatenação de soluções brandas -/

theorem heat_add (ν x y : ℝ) (ξ : E3) : heat ν x ξ * heat ν y ξ = heat ν (x + y) ξ := by
  unfold heat; rw [← Real.exp_add]; ring_nf

/-- Concatenação de `a` (em `[0, t₀]`) com `b` (deslocada para `[t₀, t₀ + τ]`). -/
noncomputable def cola (t₀ : ℝ) (a b : ℝ → E3 → C3) : ℝ → E3 → C3 :=
  fun t ξ => if t ≤ t₀ then a t ξ else b (t - t₀) ξ

theorem cola_le {t₀ t : ℝ} (a b : ℝ → E3 → C3) (h : t ≤ t₀) : cola t₀ a b t = a t := by
  funext ξ; simp [cola, h]

theorem cola_gt {t₀ t : ℝ} (a b : ℝ → E3 → C3) (h : t₀ < t) : cola t₀ a b t = b (t - t₀) := by
  funext ξ; simp [cola, not_le.mpr h]

theorem cola_ge {t₀ t : ℝ} {a b : ℝ → E3 → C3} (hab : b 0 = a t₀) (h : t₀ ≤ t) :
    cola t₀ a b t = b (t - t₀) := by
  rcases h.lt_or_eq with h | h
  · exact cola_gt a b h
  · subst h; rw [cola_le a b le_rfl, sub_self, hab]

theorem BoaW.de_cola {t₀ : ℝ} {a b : ℝ → E3 → C3} (ha : BoaW a) (hb : BoaW b)
    (hab : b 0 = a t₀) : BoaW (cola t₀ a b) where
  cont := by
    unfold cola
    refine Continuous.if_le ha.cont (hb.cont.comp ((continuous_fst.sub continuous_const).prodMk
      continuous_snd)) continuous_fst continuous_const fun p hp => ?_
    simp only [hp, sub_self, hab]
  bound m := by
    obtain ⟨A, hA0, hA⟩ := ha.bound m
    obtain ⟨B, hB0, hB⟩ := hb.bound m
    refine ⟨max A B, le_max_of_le_left hA0, fun t ξ => ?_⟩
    have hw := (inv_pos.mpr (w_pos m ξ)).le
    unfold cola
    split_ifs
    · exact (hA t ξ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw)
    · exact (hB _ ξ).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw)

theorem cola_herm {t₀ : ℝ} {a b : ℝ → E3 → C3} (ha : ∀ t, Herm (a t)) (hb : ∀ t, Herm (b t))
    (t : ℝ) : Herm (cola t₀ a b t) := by
  by_cases h : t ≤ t₀
  · rw [cola_le a b h]; exact ha t
  · rw [cola_gt a b (not_le.mp h)]; exact hb _

theorem cola_div {t₀ : ℝ} {a b : ℝ → E3 → C3} (ha : ∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0)
    (hb : ∀ t ξ, inner ℂ (cpx ξ) (b t ξ) = 0) (t : ℝ) (ξ : E3) :
    inner ℂ (cpx ξ) (cola t₀ a b t ξ) = 0 := by
  unfold cola; split_ifs
  · exact ha t ξ
  · exact hb _ ξ

theorem duhI_congr {ν τ s : ℝ} {a c : ℝ → E3 → C3} (h : c s = a s) (ξ : E3) :
    duhI ν c c τ s ξ = duhI ν a a τ s ξ := by
  unfold duhI; rw [h]

theorem continuous_duhI_s {ν τ : ℝ} {a : ℝ → E3 → C3} (ha : BoaW a) (ξ : E3) :
    Continuous fun s => duhI ν a a τ s ξ := by
  unfold duhI
  have h1 : Continuous fun s => heat ν (τ - s) ξ := by
    have := continuous_heat ν
    unfold heat; fun_prop
  exact h1.smul ((ha.lpNl ha).cont_t ξ)

/-- **A concatenação é branda** em `[0, t₀ + τ]` (propriedade de semigrupo do calor). -/
theorem cola_mild {ν t₀ τ : ℝ} (ht₀ : 0 ≤ t₀) {a b : ℝ → E3 → C3} (ha : BoaW a) (hb : BoaW b)
    (hma : ∀ t ∈ Icc 0 t₀, ∀ ξ, a t ξ = heat ν t ξ • a 0 ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    (hmb : ∀ t ∈ Icc 0 τ, ∀ ξ, b t ξ = heat ν t ξ • a t₀ ξ - ∫ s in (0 : ℝ)..t, duhI ν b b t s ξ)
    (hτ : 0 ≤ τ) :
    ∀ t ∈ Icc 0 (t₀ + τ), ∀ ξ, cola t₀ a b t ξ =
      heat ν t ξ • cola t₀ a b 0 ξ - ∫ s in (0 : ℝ)..t, duhI ν (cola t₀ a b) (cola t₀ a b) t s ξ := by
  have hab : b 0 = a t₀ := by
    funext ξ
    rw [hmb 0 ⟨le_rfl, hτ⟩ ξ, heat_zero, one_smul, intervalIntegral.integral_same, sub_zero]
  have hc := BoaW.de_cola ha hb hab
  have hc0 : cola t₀ a b 0 = a 0 := cola_le a b ht₀
  intro t ht ξ
  rw [hc0]
  by_cases htt : t ≤ t₀
  · rw [cola_le a b htt, hma t ⟨ht.1, htt⟩ ξ]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    exact (duhI_congr (cola_le a b (hs.2.trans htt)) ξ).symm
  · push Not at htt
    rw [cola_gt a b htt, hmb (t - t₀) ⟨by linarith, by linarith [ht.2]⟩ ξ, hma t₀ ⟨ht₀, le_rfl⟩ ξ]
    -- o calor de `a t₀`
    have e1 : heat ν (t - t₀) ξ • (heat ν t₀ ξ • a 0 ξ - ∫ s in (0 : ℝ)..t₀, duhI ν a a t₀ s ξ) =
        heat ν t ξ • a 0 ξ - ∫ s in (0 : ℝ)..t₀, duhI ν (cola t₀ a b) (cola t₀ a b) t s ξ := by
      rw [smul_sub, smul_smul, heat_add, sub_add_cancel, ← intervalIntegral.integral_smul]
      congr 1
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht₀] at hs
      rw [duhI_congr (cola_le a b hs.2) ξ]
      unfold duhI
      rw [smul_smul, heat_add]
      congr 2
      ring
    -- a integral de `b`
    have e2 : ∫ r in (0 : ℝ)..(t - t₀), duhI ν b b (t - t₀) r ξ =
        ∫ s in t₀..t, duhI ν (cola t₀ a b) (cola t₀ a b) t s ξ := by
      have := intervalIntegral.integral_comp_sub_right
        (fun r => duhI ν b b (t - t₀) r ξ) t₀ (a := t₀) (b := t)
      rw [sub_self] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le htt.le] at hs
      have hcs := cola_ge hab hs.1
      unfold duhI
      rw [hcs]
      congr 2
      ring
    rw [e1, e2, sub_sub, intervalIntegral.integral_add_adjacent_intervals
      ((continuous_duhI_s hc ξ).intervalIntegrable _ _)
      ((continuous_duhI_s hc ξ).intervalIntegrable _ _)]

/-! ### A solução física a partir de uma amplitude branda -/

/-- **A solução (na classe) construída a partir de qualquer amplitude branda boa.** -/
theorem solucao_de_amp {ν T : ℝ} (hν : 0 < ν) (hT : 0 < T) {a : ℝ → E3 → C3} (haW : BoaW a)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a 0 ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    (hherm : ∀ t, Herm (a t)) (hdivF : ∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0) :
    SolR (ClasseF ν) ν (fun x => re3 (Vf (a 0) x)) T (Uf ν a) (Pf ν a) := by
  have hb := amp_ader haW hmild
  have hp := amp_pk haW hmild
  obtain ⟨A, hA0, hA⟩ := haW.bound 5
  have hsub : univ ×ˢ Ico 0 T ⊆ (univ : Set E3) ×ˢ Icc 0 T :=
    prod_mono subset_rfl Ico_subset_Icc_self
  refine ⟨⟨?_, ?_, fun x => ?_, fun x t ht => ?_, fun x t ht => ?_, fun T' hT' => ?_⟩,
    fun T' hT'0 hT' => ?_⟩
  · exact (re3L.contDiff.comp_contDiffOn (hb.contDiffOn_V_infty hT)).mono hsub
  · exact (re0L.contDiff.comp_contDiffOn (hp.contDiffOn_V_infty hT)).mono hsub
  · show re3 (V (ader ν a 0) (x, 0)) = re3 (Vf (a 0) x)
    simp only [V, ader_zero]
  · exact NSEq_Uf haW hmild hherm hdivF ht x
  · exact div_Uf haW hmild hdivF (Ico_subset_Icc_self ht) x
  · refine ⟨A ^ 2 * I4 + 3 * ((2 * π * A) ^ 2 * I4), fun t ht => ?_⟩
    have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hT'.le⟩
    have hI4 := I4_nonneg
    obtain ⟨hE1, hE2⟩ := energia_Uf haW hmild hA0 hA htT
    obtain ⟨hG1, hG2⟩ := enstrofia_Uf haW hmild hA0 hA htT
    refine ⟨⟨hE1, hE2.trans ?_⟩, hG1, hG2.trans ?_⟩
    · have : 0 ≤ 3 * ((2 * π * A) ^ 2 * I4) := by positivity
      linarith
    · have : 0 ≤ A ^ 2 * I4 := by positivity
      linarith
  · exact ⟨a, haW, hherm, hdivF, fun t ht ξ => hmild t ⟨ht.1, ht.2.trans hT'.le⟩ ξ,
      fun x t _ _ => rfl⟩


/-! ### A continuação -/

/-- **Continuação na classe de Fourier (critério de Leray)**: uma solução da classe em `[0, T)`
com enstrofia limitada continua, na classe, além de `T`. -/
theorem continuacaoF : ContinuacaoD fun d => ClasseF d.1 := by
  rintro ⟨ν, u₀f⟩ ⟨hν, ⟨u₀, hu₀⟩, hdiv⟩ T U P hT ⟨hsol, hR⟩ ⟨B, hB⟩
  simp only at hν hdiv hu₀ hsol hR hB ⊢
  subst hu₀
  -- constantes que só dependem do dado, de `ν`, de `T` e de `B`
  obtain ⟨M0, hM00, hM0⟩ := ahat_bound u₀ 4
  have hB0 : 0 ≤ B := (integral_nonneg fun x => Finset.sum_nonneg fun j _ =>
    sq_nonneg _).trans (hB 0 ⟨le_rfl, hT⟩)
  set E0 : ℝ := ∫ ξ, ‖ahat u₀ ξ‖ ^ 2 with hE0
  have hE00 : 0 ≤ E0 := integral_nonneg fun ξ => sq_nonneg _
  set M1 : ℝ := 2 * E0 + 2 * (B / (4 * π ^ 2)) with hM1
  have hM10 : 0 ≤ M1 := by positivity
  set M2 : ℝ := J 2 (ahat u₀) * Real.exp (E2 ν T M1 (J 1 (ahat u₀))) with hM2
  have hM20 : 0 ≤ M2 := mul_nonneg (J_nonneg _ _) (Real.exp_pos _).le
  set M3 : ℝ := J 3 (ahat u₀) * Real.exp (T * (8 * π ^ 2 * ν + K3 ν * M2)) with hM3
  have hM30 : 0 ≤ M3 := mul_nonneg (J_nonneg _ _) (Real.exp_pos _).le
  set M4 : ℝ := Mfin ν T M0 M3 with hM4
  have hM40 : 0 ≤ M4 := by
    rw [hM4]; unfold Mfin; have := Real.pi_pos; positivity
  set τ : ℝ := T0 ν M4 with hτ
  have hτ0 : 0 < τ := T0_pos hν hM40
  set t₀ : ℝ := max 0 (T - τ / 2) with ht₀
  have ht₀0 : 0 ≤ t₀ := le_max_left _ _
  have ht₀T : t₀ < T := max_lt hT (by linarith)
  have hT₂ : T < t₀ + τ := by
    have : T - τ / 2 ≤ t₀ := le_max_right _ _
    linarith
  -- a amplitude em `[0, t₀]`
  obtain ⟨a, ha, hh, hd, hm, hU⟩ := hR t₀ ht₀0 ht₀T
  -- `â(0) = 𝓕 u₀`
  have ha0 : a 0 = ahat u₀ := by
    obtain ⟨C, -, hC⟩ := ha.bound 4
    refine amp_inj (ha.cont_s 0) (ahat_cont u₀) (hC 0) hM0 fun x => ?_
    rw [Vf_ahat, ← cpx_re3 (Vf_real (hh 0) x), ← hsol.2.2.1 x, hU x 0 le_rfl ht₀0]
    simp [Uf, V, ader_zero]
  have hfat : ∀ s ∈ Icc 0 t₀, fatia U s = fatia (Uf ν a) s := fun s hs =>
    funext fun x => hU x s hs.1 hs.2
  -- cotas uniformes em `[0, t₀]`
  have hJ1 : ∀ s ∈ Icc 0 t₀, J 1 (a s) ≤ M1 := by
    intro s hs
    have hBs : ∫ x, gradSq (fatia (Uf ν a) s) x ≤ B := by
      rw [← hfat s hs]; exact hB s ⟨hs.1, hs.2.trans_lt ht₀T⟩
    have := J1_le_of hν.le ha hm hh hd hs hBs
    rw [ha0] at this
    exact this
  have hJ2 : ∀ s ∈ Icc 0 t₀, J 2 (a s) ≤ M2 := by
    intro s hs
    have := J2_le hν ha hd hm hM10 hJ1 ht₀T.le hs
    rw [ha0] at this
    exact this
  have hJ3 : ∀ s ∈ Icc 0 t₀, J 3 (a s) ≤ M3 := by
    intro s hs
    have := J3_le hν ha hd hm hM20 hJ2 ht₀T.le hs
    rw [ha0] at this
    exact this
  have hM0' : ∀ ξ, ‖a 0 ξ‖ ≤ M0 * (w 4 ξ)⁻¹ := by rw [ha0]; exact hM0
  have hcota : ∀ ξ, ‖a t₀ ξ‖ ≤ M4 * (w 4 ξ)⁻¹ := fun ξ =>
    cota_de_J3 hν ha hd hm hM0' hM30 hJ3 ht₀T.le ⟨ht₀0, le_rfl⟩ ξ
  -- reinício em `t₀`
  have hDado : Dado (a t₀) M4 := ⟨ha.cont_s t₀, hcota⟩
  obtain ⟨b, hb4, hmb, hdb, hbm, hhb⟩ := existe_branda_T hν hDado (hd t₀) (hh t₀)
  have hbW : BoaW b := by
    refine ⟨hb4.cont, fun m => ?_⟩
    obtain ⟨C0, -, hC0⟩ := ha.bound m
    obtain ⟨C, hC⟩ := hbm m C0 (hC0 t₀)
    refine ⟨max C 0, le_max_right _ _, fun t ξ => (hC t ξ).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_pos.mpr (w_pos m ξ)).le
  have hab : b 0 = a t₀ := by
    funext ξ
    rw [hmb 0 ⟨le_rfl, hτ0.le⟩ ξ, heat_zero, one_smul, intervalIntegral.integral_same, sub_zero]
  -- colagem
  have hcW := BoaW.de_cola ha hbW hab
  have hcm := cola_mild ht₀0 ha hbW (fun t ht ξ => hm t ht ξ) hmb hτ0.le
  have hc0 : cola t₀ a b 0 = a 0 := cola_le a b ht₀0
  have hcm' : ∀ t ∈ Icc 0 (t₀ + τ), ∀ ξ, cola t₀ a b t ξ =
      heat ν t ξ • cola t₀ a b 0 ξ -
        ∫ s in (0 : ℝ)..t, duhI ν (cola t₀ a b) (cola t₀ a b) t s ξ := hcm
  have hsolc := solucao_de_amp hν (by linarith) hcW hcm' (cola_herm hh hhb) (cola_div hd hdb)
  have hu : (fun x => re3 (Vf (cola t₀ a b 0) x)) = ⇑u₀ := by
    funext x
    rw [hc0, ← hsol.2.2.1 x, hU x 0 le_rfl ht₀0]
    simp [Uf, V, ader_zero]
  rw [hu] at hsolc
  exact ⟨t₀ + τ, hT₂, Uf ν (cola t₀ a b), Pf ν (cola t₀ a b), hsolc⟩

end ATK.NSContinuacao

#print axioms ATK.NSContinuacao.existe_branda_T
#print axioms ATK.NSContinuacao.amp_inj
#print axioms ATK.NSContinuacao.herm_cj_smul
#print axioms ATK.NSContinuacao.norm_cj_smul_sq
#print axioms ATK.NSContinuacao.enstrofia_eq
#print axioms ATK.NSContinuacao.J1_le_of
#print axioms ATK.NSContinuacao.heat_add
#print axioms ATK.NSContinuacao.cola_le
#print axioms ATK.NSContinuacao.cola_gt
#print axioms ATK.NSContinuacao.cola_ge
#print axioms ATK.NSContinuacao.BoaW.de_cola
#print axioms ATK.NSContinuacao.cola_herm
#print axioms ATK.NSContinuacao.cola_div
#print axioms ATK.NSContinuacao.duhI_congr
#print axioms ATK.NSContinuacao.continuous_duhI_s
#print axioms ATK.NSContinuacao.cola_mild
#print axioms ATK.NSContinuacao.solucao_de_amp
#print axioms ATK.NSContinuacao.continuacaoF
