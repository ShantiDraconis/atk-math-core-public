import ATK.ZeroClasses.LiCompleto

/-!
# `λ₁ = 1 + γ/2 − ½ log 4π` e RH ⟺ `Σ_ρ 1/|ρ|² = 2 + γ − log 4π` (rodada 69)

Com o produto de Hadamard (rodada 33) e os valores da Mathlib `Λ₀(0) = Λ₀(1) = (γ − log 4π)/2 + 1`
(`completedRiemannZeta₀_zero`, `completedRiemannZeta₀_one`):

* **a reflexão nas cópias** (`refl`, `reflEquiv`): `(ρ, j) ↦ (1 − ρ, j)` é uma involução de `ZM` (as ordens são
  simétricas, rodada 31); daí **`Σ_ρ Re 1/(½ − ρ) = 0`** (`soma_meio_zero`);
* **a constante de Hadamard** (`B_eq`): `B = ξ′/ξ(0) = −((γ − log 4π)/2 + 1)`;
* **`λ₁ = Σ_ρ Re(1/ρ) = 1 + γ/2 − ½ log 4π`** (`lam_um`; `L(½) = 0` da rodada 28 elimina `B`), e `λ₁ > 0`
  (`lam_um_pos`) — em particular **`log 4π < 2 + γ`** sai dos zeros (`log_quatro_pi_lt`);
* **`Σ_ρ 1/|ρ|² ≥ 2 + γ − log 4π`** (`soma_inv_quad_ge`): pareando `ρ` com `1 − ρ`,
  `2 Σ (1 − 2β)/|ρ|² = Σ (1 − 2β)(1/|ρ|² − 1/|1 − ρ|²) ≥ 0` termo a termo;
* **RH ⟺ `Σ_ρ 1/|ρ|² = 2 + γ − log 4π`** (`rh_iff_soma_inv_quad`): a igualdade força cada parcela a zero, isto é,
  `β = ½`.

Classificação (rodada 69): **reformulação** (o critério) e **consequência** (os valores). RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.LiUm

open ATK.ZeroClasses.Canonico ATK.ZeroClasses.CanonicoInteira ATK.ZeroClasses.LagariasHadamard
  ATK.ZeroClasses.SomaZeros ATK.ZeroClasses.LiCompleto ATK.BaseRiemannXi

/-! ## 1. A reflexão `(ρ, j) ↦ (1 − ρ, j)` -/

theorem ordem_refl (q : ZM) :
    analyticOrderNatAt riemannZeta (rZ q) = analyticOrderNatAt riemannZeta (1 - rZ q) :=
  (ATK.ZeroClasses.JensenLocal.ordemNat_zeta_reflexao q.1.2.2.1 q.1.2.2.2).symm

/-- A reflexão nas cópias. -/
noncomputable def refl (q : ZM) : ZM :=
  ⟨⟨1 - rZ q, ATK.ZetaSimetria.tensao_mem_Z q.1.2⟩, Fin.cast (ordem_refl q) q.2⟩

theorem rZ_refl (q : ZM) : rZ (refl q) = 1 - rZ q := rfl

theorem refl_refl (q : ZM) : refl (refl q) = q := by
  rcases q with ⟨⟨ρ, hρ⟩, j⟩
  have e : (1 : ℂ) - (1 - ρ) = ρ := sub_sub_cancel 1 ρ
  refine Sigma.ext (Subtype.ext e) ?_
  refine (Fin.heq_ext_iff ?_).mpr ?_
  · show analyticOrderNatAt riemannZeta (1 - (1 - ρ)) = analyticOrderNatAt riemannZeta ρ
    rw [e]
  · simp [refl]

/-- A reflexão como equivalência de `ZM`. -/
noncomputable def reflEquiv : ZM ≃ ZM := Function.Involutive.toPerm refl refl_refl

/-! ## 2. `Σ_ρ Re 1/(½ − ρ) = 0` -/

theorem summable_re_inv : Summable (fun q : ZM => (1 / rZ q).re) :=
  Summable.of_nonneg_of_le (fun q => (inv_props q).1) (fun q => (inv_props q).2.1) summable_inv_sq

theorem summable_meio : Summable (fun q : ZM => (1 / ((1 / 2 : ℂ) - rZ q)).re) := by
  have h := (summable_re (1 / 2 : ℂ)).sub summable_re_inv
  refine h.congr fun q => ?_
  simp only [add_re]
  ring

/-- **`Σ_ρ Re 1/(½ − ρ) = 0`**, pela reflexão `ρ ↦ 1 − ρ`. -/
theorem soma_meio_zero : ∑' q : ZM, (1 / ((1 / 2 : ℂ) - rZ q)).re = 0 := by
  set X := ∑' q : ZM, (1 / ((1 / 2 : ℂ) - rZ q)).re with hX
  have h := Equiv.tsum_eq reflEquiv (fun q : ZM => (1 / ((1 / 2 : ℂ) - rZ q)).re)
  have e : ∀ q : ZM, (1 / ((1 / 2 : ℂ) - rZ (reflEquiv q))).re = -(1 / ((1 / 2 : ℂ) - rZ q)).re := by
    intro q
    show (1 / ((1 / 2 : ℂ) - rZ (refl q))).re = _
    rw [rZ_refl]
    have e1 : (1 / 2 : ℂ) - (1 - rZ q) = -((1 / 2 : ℂ) - rZ q) := by ring
    rw [e1, div_neg, neg_re]
  rw [tsum_congr e, tsum_neg] at h
  linarith

/-! ## 3. A constante de Hadamard e `λ₁` -/

theorem hasDerivAt_xi (s : ℂ) :
    HasDerivAt riemannXi ((1 * (s - 1) + s * 1) / 2 * completedRiemannZeta₀ s +
      s * (s - 1) / 2 * deriv completedRiemannZeta₀ s) s := by
  have h1 : HasDerivAt (fun z : ℂ => z * (z - 1) / 2) ((1 * (s - 1) + s * 1) / 2) s :=
    ((hasDerivAt_id' s).mul ((hasDerivAt_id' s).sub_const 1)).div_const 2
  have h2 := (h1.mul (differentiable_completedZeta₀ s).hasDerivAt).add_const (1 / 2 : ℂ)
  exact h2

theorem logDeriv_xi_zero : logDeriv riemannXi 0 = -completedRiemannZeta₀ 0 := by
  rw [logDeriv_apply, (hasDerivAt_xi 0).deriv, riemannXi_zero]
  ring

/-- **A constante de Hadamard**: `B = ξ′/ξ(0)`. -/
theorem B_eq {A B : ℂ} (hAB : ∀ s, riemannXi s = cexp (A + B * s) * Pcan s) :
    B = -completedRiemannZeta₀ 0 := by
  have hx : riemannXi 0 ≠ 0 := by rw [riemannXi_zero]; norm_num
  have h := logDeriv_xi_eq hAB hx
  have e : ∀ q : ZM, 1 / ((0 : ℂ) - rZ q) + 1 / rZ q = 0 := fun q => by
    rw [zero_sub, div_neg]
    ring
  rw [tsum_congr e, tsum_zero, add_zero, logDeriv_xi_zero] at h
  exact h.symm

theorem re_completed_zero :
    (completedRiemannZeta₀ 0).re = (Real.eulerMascheroniConstant - Real.log (4 * π)) / 2 + 1 := by
  rw [completedRiemannZeta₀_zero]
  have e : Complex.log (4 * (π : ℂ)) = ((Real.log (4 * π) : ℝ) : ℂ) := by
    rw [show (4 * (π : ℂ)) = ((4 * π : ℝ) : ℂ) by push_cast; ring]
    exact (Complex.ofReal_log (by positivity)).symm
  rw [e]
  simp

theorem termo_um (q : ZM) : termo 1 q = (1 / rZ q).re := by
  unfold termo wq ATK.Li.w
  simp

/-- **`λ₁ = Σ_ρ Re(1/ρ) = 1 + γ/2 − ½ log 4π`**. -/
theorem lam_um : lam 1 = 1 + Real.eulerMascheroniConstant / 2 - Real.log (4 * π) / 2 := by
  obtain ⟨A, B, hAB⟩ := ATK.ZeroClasses.Hadamard.xi_hadamard
  have hmeio : riemannXi (1 / 2) ≠ 0 := by
    obtain ⟨x, hx, hz⟩ := ATK.ZetaSimetria.zeta_meio_neg
    intro h
    have h' := (riemannXi_eq_zero_iff (by norm_num : (0 : ℝ) < (1 / 2 : ℂ).re)
      (by norm_num : (1 / 2 : ℂ) ≠ 1)).mp h
    rw [hz] at h'
    have : x = 0 := by exact_mod_cast h'
    linarith
  have hL := Lg_eq hAB hmeio
  have hL0 : ATK.ZeroClasses.Lagarias.Lg (1 / 2) = 0 := by
    have := ATK.ZeroClasses.Lagarias.Lg_linha 0
    simpa using this
  rw [hL0] at hL
  have hsplit : ∑' q : ZM, (1 / ((1 / 2 : ℂ) - rZ q) + 1 / rZ q).re =
      ∑' q : ZM, (1 / ((1 / 2 : ℂ) - rZ q)).re + ∑' q : ZM, (1 / rZ q).re := by
    rw [← summable_meio.tsum_add summable_re_inv]
    exact tsum_congr fun q => by rw [add_re]
  rw [hsplit, soma_meio_zero, zero_add, B_eq hAB, neg_re, re_completed_zero] at hL
  unfold lam
  rw [tsum_congr termo_um]
  linarith

theorem termo_um_pos (q : ZM) : 0 < termo 1 q := by
  rw [termo_um]
  obtain ⟨_, h0, _⟩ := q.1.2
  have hn := norm_rZ_ge q
  have hre : (1 / rZ q).re = (rZ q).re / ‖rZ q‖ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  rw [hre]
  have : 0 < ‖rZ q‖ := by linarith
  positivity

/-- **`λ₁ > 0`** (há um zero: rodada 34). -/
theorem lam_um_pos : 0 < lam 1 := by
  obtain ⟨ρ, hρ, _⟩ := ATK.ZeroCertAplicado.existe_zero_altura
  obtain ⟨q, _⟩ := ATK.ZeroClasses.Explicita.existe_q hρ
  exact (summable_termo 1).tsum_pos (fun q => (termo_um_pos q).le) q (termo_um_pos q)

/-- **`log 4π < 2 + γ`**, a partir dos zeros. -/
theorem log_quatro_pi_lt : Real.log (4 * π) < 2 + Real.eulerMascheroniConstant := by
  have := lam_um_pos
  rw [lam_um] at this
  linarith

/-! ## 4. `Σ_ρ 1/|ρ|²` -/

/-- A parcela `(1 − 2β)/|ρ|²`. -/
noncomputable def fD (q : ZM) : ℝ := (1 - 2 * (rZ q).re) / ‖rZ q‖ ^ 2

theorem norm_sq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem fD_eq (q : ZM) : fD q = 1 / ‖rZ q‖ ^ 2 - 2 * (1 / rZ q).re := by
  have hre : (1 / rZ q).re = (rZ q).re / ‖rZ q‖ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  rw [hre]
  unfold fD
  ring

theorem summable_fD : Summable fD :=
  (summable_inv_sq.sub (summable_re_inv.mul_left 2)).congr fun q => (fD_eq q).symm

theorem par_eq (q : ZM) :
    fD q + fD (refl q) = (1 - 2 * (rZ q).re) ^ 2 / (‖rZ q‖ ^ 2 * ‖1 - rZ q‖ ^ 2) := by
  have h0 : rZ q ≠ 0 := ZM_ne_zero q
  have h1 : (1 : ℂ) - rZ q ≠ 0 := ATK.Li.ne_zero_of_mem_Z (ATK.ZetaSimetria.tensao_mem_Z q.1.2)
  have hp : 0 < ‖rZ q‖ ^ 2 := by have := norm_pos_iff.mpr h0; positivity
  have hp' : 0 < ‖1 - rZ q‖ ^ 2 := by have := norm_pos_iff.mpr h1; positivity
  have hdiff : ‖1 - rZ q‖ ^ 2 - ‖rZ q‖ ^ 2 = 1 - 2 * (rZ q).re := by
    rw [norm_sq_eq, norm_sq_eq]
    simp only [sub_re, one_re, sub_im, one_im]
    ring
  unfold fD
  rw [rZ_refl]
  have hre1 : (1 - rZ q).re = 1 - (rZ q).re := by simp
  rw [hre1]
  field_simp
  have e : (1 - 2 * (1 - (rZ q).re)) = -(1 - 2 * (rZ q).re) := by ring
  rw [e]
  nlinarith [hdiff]

theorem par_nonneg (q : ZM) : 0 ≤ fD q + fD (refl q) := by
  rw [par_eq]
  positivity

theorem tsum_fD_refl : ∑' q, fD (refl q) = ∑' q, fD q :=
  Equiv.tsum_eq reflEquiv fD

theorem summable_fD_refl : Summable (fun q => fD (refl q)) :=
  (Equiv.summable_iff reflEquiv).mpr summable_fD

theorem tsum_fD_nonneg : 0 ≤ ∑' q, fD q := by
  have h : 0 ≤ ∑' q, (fD q + fD (refl q)) := tsum_nonneg par_nonneg
  rw [summable_fD.tsum_add summable_fD_refl, tsum_fD_refl] at h
  linarith

theorem soma_inv_quad_eq : ∑' q : ZM, 1 / ‖rZ q‖ ^ 2 = ∑' q, fD q + 2 * lam 1 := by
  unfold lam
  rw [tsum_congr termo_um, ← tsum_mul_left, ← summable_fD.tsum_add (summable_re_inv.mul_left 2)]
  exact tsum_congr fun q => by rw [fD_eq]; ring

/-- **`Σ_ρ 1/|ρ|² ≥ 2 + γ − log 4π`**. -/
theorem soma_inv_quad_ge :
    2 + Real.eulerMascheroniConstant - Real.log (4 * π) ≤ ∑' q : ZM, 1 / ‖rZ q‖ ^ 2 := by
  rw [soma_inv_quad_eq, lam_um]
  have := tsum_fD_nonneg
  linarith

/-- **RH ⟺ `Σ_ρ 1/|ρ|² = 2 + γ − log 4π`** (com multiplicidade). -/
theorem rh_iff_soma_inv_quad :
    RiemannHypothesis ↔ ∑' q : ZM, 1 / ‖rZ q‖ ^ 2 = 2 + Real.eulerMascheroniConstant - Real.log (4 * π) := by
  constructor
  · intro hRH
    rw [soma_inv_quad_eq, lam_um]
    have h0 : ∀ q, fD q = 0 := fun q => by
      unfold fD
      rw [re_de_RH hRH q.1.2]
      ring
    rw [tsum_congr h0, tsum_zero]
    ring
  · intro h
    rw [soma_inv_quad_eq, lam_um] at h
    have hD : ∑' q, fD q = 0 := by linarith
    have hpar : ∑' q, (fD q + fD (refl q)) = 0 := by
      rw [summable_fD.tsum_add summable_fD_refl, tsum_fD_refl, hD, add_zero]
    have hhs : HasSum (fun q => fD q + fD (refl q)) 0 := by
      have := (summable_fD.add summable_fD_refl).hasSum
      rwa [hpar] at this
    have hall : ∀ q, fD q + fD (refl q) = 0 := fun q =>
      congrFun ((hasSum_zero_iff_of_nonneg par_nonneg).mp hhs) q
    rw [ATK.Li.rh_iff_li_unitario]
    intro ρ hρ
    obtain ⟨q, rfl⟩ := ATK.ZeroClasses.Explicita.existe_q hρ
    rw [ATK.Li.w_unitario_iff (ZM_ne_zero q)]
    have h1 := hall q
    rw [par_eq] at h1
    have h0 : rZ q ≠ 0 := ZM_ne_zero q
    have h1' : (1 : ℂ) - rZ q ≠ 0 := ATK.Li.ne_zero_of_mem_Z (ATK.ZetaSimetria.tensao_mem_Z q.1.2)
    have hp : 0 < ‖rZ q‖ ^ 2 * ‖1 - rZ q‖ ^ 2 := by
      have := norm_pos_iff.mpr h0
      have := norm_pos_iff.mpr h1'
      positivity
    rw [div_eq_zero_iff] at h1
    rcases h1 with h1 | h1
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      linarith
    · linarith

end ATK.ZeroClasses.LiUm

#print axioms ATK.ZeroClasses.LiUm.ordem_refl
#print axioms ATK.ZeroClasses.LiUm.rZ_refl
#print axioms ATK.ZeroClasses.LiUm.refl_refl
#print axioms ATK.ZeroClasses.LiUm.summable_re_inv
#print axioms ATK.ZeroClasses.LiUm.summable_meio
#print axioms ATK.ZeroClasses.LiUm.soma_meio_zero
#print axioms ATK.ZeroClasses.LiUm.hasDerivAt_xi
#print axioms ATK.ZeroClasses.LiUm.logDeriv_xi_zero
#print axioms ATK.ZeroClasses.LiUm.B_eq
#print axioms ATK.ZeroClasses.LiUm.re_completed_zero
#print axioms ATK.ZeroClasses.LiUm.termo_um
#print axioms ATK.ZeroClasses.LiUm.lam_um
#print axioms ATK.ZeroClasses.LiUm.termo_um_pos
#print axioms ATK.ZeroClasses.LiUm.lam_um_pos
#print axioms ATK.ZeroClasses.LiUm.log_quatro_pi_lt
#print axioms ATK.ZeroClasses.LiUm.norm_sq_eq
#print axioms ATK.ZeroClasses.LiUm.fD_eq
#print axioms ATK.ZeroClasses.LiUm.summable_fD
#print axioms ATK.ZeroClasses.LiUm.par_eq
#print axioms ATK.ZeroClasses.LiUm.par_nonneg
#print axioms ATK.ZeroClasses.LiUm.tsum_fD_refl
#print axioms ATK.ZeroClasses.LiUm.summable_fD_refl
#print axioms ATK.ZeroClasses.LiUm.tsum_fD_nonneg
#print axioms ATK.ZeroClasses.LiUm.soma_inv_quad_eq
#print axioms ATK.ZeroClasses.LiUm.soma_inv_quad_ge
#print axioms ATK.ZeroClasses.LiUm.rh_iff_soma_inv_quad
