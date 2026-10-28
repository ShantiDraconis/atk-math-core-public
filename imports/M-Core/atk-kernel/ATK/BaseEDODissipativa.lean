/-
ATK.Base (N2) — Existência e unicidade globais para EDOs dissipativas localmente Lipschitz.

Base que falta na Mathlib: ela tem Picard–Lindelöf local (`IsPicardLindelof`) e unicidade
(`ODE_solution_unique_of_mem_Icc_right`), mas nenhum teorema de existência **global** a partir de
uma estimativa de energia.  É exatamente o passo que leva o sistema de Galerkin de Navier–Stokes
(`ATK.BaseGalerkinNS`) de "a energia decresce ao longo de soluções" para "soluções existem para
todo tempo".

Num espaço de Hilbert real `H`, seja `F : H → H` Lipschitz em cada bola fechada e **dissipativo**,
`⟪F v, v⟫ ≤ 0`.  Então:

* **`existencia_global`**: para todo `v₀` e todo `T ≥ 0` existe `u` com `u 0 = v₀`,
  `u' = F(u)` em `[0, T]` e `‖u(t)‖ ≤ ‖v₀‖`;
* **`unicidade_global`**: duas soluções em `[0, T]` com o mesmo dado inicial e que ficam na bola de
  raio `‖v₀‖` coincidem.

Prova: retração radial `ret_R` na bola de raio `R = ‖v₀‖ + 1` (`ret_lipschitz`: 2-Lipschitz);
o campo cortado `F ∘ ret_R` é globalmente Lipschitz e limitado, logo Picard–Lindelöf dá solução em
`[0, T]` inteiro; o campo cortado continua dissipativo (`⟪x, F(c x)⟫ = c⁻¹⟪cx, F(cx)⟫`), então
`‖u‖²` não cresce, a solução fica na bola de raio `‖v₀‖ < R` e lá o corte é a identidade.
-/
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Metric Set
open scoped NNReal RealInnerProductSpace

namespace ATK.BaseEDODissipativa

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ### Retração radial -/

/-- Retração radial na bola fechada de raio `R`. -/
noncomputable def ret (R : ℝ) (x : H) : H := if ‖x‖ ≤ R then x else (R / ‖x‖) • x

theorem ret_of_norm_le {R : ℝ} {x : H} (h : ‖x‖ ≤ R) : ret R x = x := by
  simp [ret, h]

theorem ret_of_lt {R : ℝ} {x : H} (h : R < ‖x‖) : ret R x = (R / ‖x‖) • x := by
  simp [ret, not_le.mpr h]

theorem norm_ret_le {R : ℝ} (hR : 0 ≤ R) (x : H) : ‖ret R x‖ ≤ R := by
  by_cases h : ‖x‖ ≤ R
  · rw [ret_of_norm_le h]; exact h
  · have hx : R < ‖x‖ := not_le.mp h
    have hpos : 0 < ‖x‖ := lt_of_le_of_lt hR hx
    rw [ret_of_lt hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hR hpos.le),
      div_mul_cancel₀ _ hpos.ne']

/-- Lema auxiliar: `x` dentro, `y` fora da bola. -/
theorem dist_ret_dentro_fora {R : ℝ} {x y : H} (hx : ‖x‖ ≤ R) (hy : R < ‖y‖) :
    ‖x - (R / ‖y‖) • y‖ ≤ 2 * ‖x - y‖ := by
  have hR : 0 ≤ R := le_trans (norm_nonneg _) hx
  have hpos : 0 < ‖y‖ := lt_of_le_of_lt hR hy
  have hc0 : 0 ≤ R / ‖y‖ := div_nonneg hR hpos.le
  have hc1 : R / ‖y‖ ≤ 1 := (div_le_one hpos).mpr hy.le
  have e : ‖y - (R / ‖y‖) • y‖ = ‖y‖ - R := by
    have : y - (R / ‖y‖) • y = (1 - R / ‖y‖) • y := by rw [sub_smul, one_smul]
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith), sub_mul, one_mul,
      div_mul_cancel₀ _ hpos.ne']
  have h1 : ‖x - (R / ‖y‖) • y‖ ≤ ‖x - y‖ + ‖y - (R / ‖y‖) • y‖ := by
    have := norm_add_le (x - y) (y - (R / ‖y‖) • y)
    simpa using this
  have h2 : ‖y‖ - ‖x‖ ≤ ‖x - y‖ := by
    have := norm_sub_norm_le y x
    rw [norm_sub_rev] at this
    exact this
  linarith

/-- **A retração radial é 2-Lipschitz** (em qualquer espaço normado real com produto interno). -/
theorem ret_lipschitz {R : ℝ} (hR : 0 ≤ R) : LipschitzWith 2 (ret R : H → H) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [dist_eq_norm, NNReal.coe_ofNat]
  by_cases hx : ‖x‖ ≤ R <;> by_cases hy : ‖y‖ ≤ R
  · rw [ret_of_norm_le hx, ret_of_norm_le hy]
    linarith [norm_nonneg (x - y)]
  · rw [ret_of_norm_le hx, ret_of_lt (not_le.mp hy)]
    exact dist_ret_dentro_fora hx (not_le.mp hy)
  · rw [ret_of_lt (not_le.mp hx), ret_of_norm_le hy, norm_sub_rev, norm_sub_rev x y]
    exact dist_ret_dentro_fora hy (not_le.mp hx)
  · have hx' : R < ‖x‖ := not_le.mp hx
    have hy' : R < ‖y‖ := not_le.mp hy
    rw [ret_of_lt hx', ret_of_lt hy']
    have hxp : 0 < ‖x‖ := lt_of_le_of_lt hR hx'
    have hyp : 0 < ‖y‖ := lt_of_le_of_lt hR hy'
    have hc0 : 0 ≤ R / ‖x‖ := div_nonneg hR hxp.le
    have hc1 : R / ‖x‖ ≤ 1 := (div_le_one hxp).mpr hx'.le
    -- c_x x − c_y y = c_x (x − (‖x‖/‖y‖) y)
    have e : (R / ‖x‖) • x - (R / ‖y‖) • y = (R / ‖x‖) • (x - (‖x‖ / ‖y‖) • y) := by
      rw [smul_sub, smul_smul]
      congr 2
      field_simp
    have h3 : ‖y - (‖x‖ / ‖y‖) • y‖ = |‖y‖ - ‖x‖| := by
      have : y - (‖x‖ / ‖y‖) • y = (1 - ‖x‖ / ‖y‖) • y := by rw [sub_smul, one_smul]
      rw [this, norm_smul, Real.norm_eq_abs, ← abs_of_pos hyp, ← abs_mul, abs_of_pos hyp]
      congr 1
      field_simp
    have h4 : ‖x - (‖x‖ / ‖y‖) • y‖ ≤ ‖x - y‖ + ‖y - (‖x‖ / ‖y‖) • y‖ := by
      have := norm_add_le (x - y) (y - (‖x‖ / ‖y‖) • y)
      simpa using this
    have h5 : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
      rw [norm_sub_rev x y]
      exact abs_norm_sub_norm_le y x
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
    have h6 : ‖x - (‖x‖ / ‖y‖) • y‖ ≤ 2 * ‖x - y‖ := by linarith
    calc R / ‖x‖ * ‖x - (‖x‖ / ‖y‖) • y‖ ≤ 1 * ‖x - (‖x‖ / ‖y‖) • y‖ :=
          mul_le_mul_of_nonneg_right hc1 (norm_nonneg _)
      _ ≤ 2 * ‖x - y‖ := by linarith

/-! ### Existência global -/

variable [CompleteSpace H]

/-- **Existência global para EDOs dissipativas localmente Lipschitz.** -/
theorem existencia_global {F : H → H}
    (hlip : ∀ R : ℝ≥0, ∃ K : ℝ≥0, LipschitzOnWith K F (closedBall 0 R))
    (hdiss : ∀ v, ⟪F v, v⟫ ≤ 0) (v₀ : H) {T : ℝ} (hT : 0 ≤ T) :
    ∃ u : ℝ → H, u 0 = v₀ ∧ (∀ t ∈ Icc 0 T, HasDerivWithinAt u (F (u t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, ‖u t‖ ≤ ‖v₀‖ := by
  -- raio de corte R = ‖v₀‖ + 1 > 0
  set R : ℝ := ‖v₀‖ + 1 with hRdef
  have hR0 : 0 < R := by positivity
  set Rn : ℝ≥0 := ⟨R, hR0.le⟩
  obtain ⟨K, hK⟩ := hlip Rn
  set G : H → H := fun x => F (ret R x) with hGdef
  -- G é globalmente Lipschitz
  have hmaps : MapsTo (ret R) univ (closedBall (0 : H) Rn) := by
    intro x _
    rw [mem_closedBall, dist_zero_right]
    exact norm_ret_le hR0.le x
  have hGlip : LipschitzOnWith (K * 2) G univ :=
    hK.comp ((ret_lipschitz hR0.le).lipschitzOnWith) hmaps
  -- G é limitado
  set Lr : ℝ := ‖F 0‖ + K * R with hLr
  have hLr0 : 0 ≤ Lr := by positivity
  set L : ℝ≥0 := ⟨Lr, hLr0⟩
  have hb : ∀ x, ‖G x‖ ≤ L := by
    intro x
    have h0 : (0 : H) ∈ closedBall (0 : H) Rn := mem_closedBall_self (by positivity)
    have hx : ret R x ∈ closedBall (0 : H) Rn := hmaps (mem_univ x)
    have hd := hK.dist_le_mul (ret R x) hx 0 h0
    rw [dist_eq_norm, dist_eq_norm, sub_zero] at hd
    have hn := norm_ret_le hR0.le x
    have : ‖F (ret R x)‖ ≤ ‖F 0‖ + ‖F (ret R x) - F 0‖ := by
      have := norm_add_le (F 0) (F (ret R x) - F 0)
      simpa using this
    show ‖F (ret R x)‖ ≤ Lr
    have hK0 : (0 : ℝ) ≤ K := K.2
    nlinarith
  -- Picard–Lindelöf em [0, T]
  set Tn : ℝ≥0 := ⟨T, hT⟩
  let t₀ : Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have hPL : IsPicardLindelof (fun _ => G) t₀ v₀ (L * Tn) 0 L (K * 2) := by
    refine IsPicardLindelof.of_time_independent (fun x _ => hb x)
      (hGlip.mono (subset_univ _)) ?_
    simp only [t₀, sub_zero, zero_sub, NNReal.coe_mul, NNReal.coe_zero, NNReal.coe_mk]
    exact le_of_eq (by rw [max_eq_left hT]; rfl)
  obtain ⟨u, hu0, hu⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hu0' : u 0 = v₀ := hu0
  -- G é dissipativo
  have hdissG : ∀ x, ⟪x, G x⟫ ≤ 0 := by
    intro x
    by_cases hx : ‖x‖ ≤ R
    · simp only [hGdef, ret_of_norm_le hx]
      rw [real_inner_comm]; exact hdiss x
    · have hx' : R < ‖x‖ := not_le.mp hx
      have hxp : 0 < ‖x‖ := lt_trans hR0 hx'
      set c : ℝ := R / ‖x‖ with hc
      have hcpos : 0 < c := div_pos hR0 hxp
      simp only [hGdef, ret_of_lt hx']
      have h1 := hdiss (c • x)
      rw [real_inner_comm, real_inner_smul_left] at h1
      exact le_of_not_gt fun ha => absurd h1 (not_le.mpr (mul_pos hcpos ha))
  -- energia ‖u‖² não cresce em [0, T]
  have hE : ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => ‖u s‖ ^ 2) (2 * ⟪u t, G (u t)⟫) (Icc 0 T) t :=
    fun t ht => (hu t ht).norm_sq
  have hanti : AntitoneOn (fun s => ‖u s‖ ^ 2) (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => 2 * ⟪u t, G (u t)⟫)
      (convex_Icc 0 T) (fun t ht => (hE t ht).continuousWithinAt) (fun t ht => ?_) (fun t _ => ?_)
    · exact (hE t (interior_subset ht)).mono interior_subset
    · have := hdissG (u t); linarith
  have hbound : ∀ t ∈ Icc 0 T, ‖u t‖ ≤ ‖v₀‖ := by
    intro t ht
    have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
    have := hanti h0 ht ht.1
    simp only [hu0'] at this
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this
  refine ⟨u, hu0', fun t ht => ?_, hbound⟩
  have hin : ‖u t‖ ≤ R := by linarith [hbound t ht]
  have := hu t ht
  simp only [hGdef, ret_of_norm_le hin] at this
  exact this

/-- **Unicidade**: duas soluções em `[0, T]` que ficam na bola de raio `ρ` e partem do mesmo
ponto coincidem. -/
theorem unicidade_global {F : H → H}
    (hlip : ∀ R : ℝ≥0, ∃ K : ℝ≥0, LipschitzOnWith K F (closedBall 0 R)) {T : ℝ} {ρ : ℝ≥0}
    {u w : ℝ → H}
    (hu : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (F (u t)) (Icc 0 T) t)
    (hw : ∀ t ∈ Icc 0 T, HasDerivWithinAt w (F (w t)) (Icc 0 T) t)
    (hub : ∀ t ∈ Icc 0 T, ‖u t‖ ≤ ρ) (hwb : ∀ t ∈ Icc 0 T, ‖w t‖ ≤ ρ) (h0 : u 0 = w 0) :
    EqOn u w (Icc 0 T) := by
  obtain ⟨K, hK⟩ := hlip ρ
  have hIco : ∀ t ∈ Ico (0 : ℝ) T, Icc (0 : ℝ) T ∈ nhdsWithin t (Ici t) := by
    intro t ht
    exact Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2⟩
  refine ODE_solution_unique_of_mem_Icc_right (v := fun _ => F) (s := fun _ => closedBall 0 ρ)
    (K := K) (fun _ _ => hK)
    (fun t ht => (hu t ht).continuousWithinAt)
    (fun t ht => ((hu t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hIco t ht)))
    (fun t ht => by rw [mem_closedBall, dist_zero_right]; exact hub t (Ico_subset_Icc_self ht))
    (fun t ht => (hw t ht).continuousWithinAt)
    (fun t ht => ((hw t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hIco t ht)))
    (fun t ht => by rw [mem_closedBall, dist_zero_right]; exact hwb t (Ico_subset_Icc_self ht))
    h0

end ATK.BaseEDODissipativa

#print axioms ATK.BaseEDODissipativa.ret_of_norm_le
#print axioms ATK.BaseEDODissipativa.ret_of_lt
#print axioms ATK.BaseEDODissipativa.norm_ret_le
#print axioms ATK.BaseEDODissipativa.dist_ret_dentro_fora
#print axioms ATK.BaseEDODissipativa.ret_lipschitz
#print axioms ATK.BaseEDODissipativa.existencia_global
#print axioms ATK.BaseEDODissipativa.unicidade_global
