import ATK.ZeroClasses.LiouvilleRH

/-!
# A conjectura de Turán implica RH (rodada 100)

Com `λ` a função de Liouville e `T(N) = Σ_{n ≤ N} λ(n)/n` (`T`):

**`rh_of_turan`** (Turán 1948): se `T(N) ≥ 0` para todo `N`, vale RH. (A conjectura de Turán é falsa — Haselgrove
1958; o menor contraexemplo é `N = 72 185 376 951 205`, Borwein–Ferguson–Mossinghoff 2008 —, mas a implicação é
teorema.)

A prova é o teorema de Landau (rodada 87, `Unilateral.landau`) aplicado a `f(x) = T(⌊x⌋) ≥ 0`, desta vez **abaixo
de `Re s = 0`**:

* §1 `GA_T_eq`: `Σ λ(n)n^{−1−s} = L(λ, s + 1) = ζ(2s + 2)F(s + 1)` (rodada 99), e `∫_{x>1} x^{−s−1}T(⌊x⌋) dx =
  GA T(s)/s = Φ(s)` em `Re s > 1` (`Ik_fT`, `Phi_mul`);
* §2 `Φ(s) = ζ(2s + 2)/ζ₁(s + 1)` é holomorfa no disco `|s − 2| < 5/2`: lá `Re(2s + 2) > 1` e `ζ₁(s + 1) ≠ 0`,
  porque `Re(s + 1) > ½` e `|Im s| < 5/2` (sem zeros com `|γ| ≤ 13`, `Faixa.faixa_sem_zeros`). O polo de `1/s` em
  `s = 0` é removível, porque `F(1) = 0`;
* §3 Landau dá a convergência de `∫ x^{−σ−1}T(⌊x⌋) dx` em `σ > −½`. Então `G(s) = s·∫…` é holomorfa em
  `Re s > −½` e, pelo princípio da identidade, vale `ζ(2s + 2)F(s + 1)` em `Re s > 0`. Logo `w ↦ G(w − 1)` estende
  `ζ(2w)/ζ(w)` a `Re w > ½`, e `LiouvilleRH.semZeros_of_ext_liouville` dá `ζ ≠ 0` em `Re w > ½`.

Classificação: **reformulação** (Turán 1948; clássico, aqui formalizado). RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric MeasureTheory
open scoped Real

namespace ATK.ZeroClasses.TuranLiouville

open ATK.ZeroClasses.QuasiRH (SemZeros)
open ATK.RHLogZeta (F zeta₁_eq)
open ATK.ZeroClasses.VonKoch (GA)
open ATK.ZeroClasses.Unilateral (Ik IntAcima landau differentiableAt_Ik integral_escada integrable_escada)
open ATK.ZeroClasses.LiouvilleRH (lam norm_lam_le LSeries_lam LSeriesSummable_lam semZeros_of_ext_liouville
  abs_liouville_le)

/-! ## 1. `T(N) = Σ_{n ≤ N} λ(n)/n` e sua série -/

/-- `c(n) = λ(n)/n`. -/
noncomputable def cT (n : ℕ) : ℂ := lam n / n

/-- `T(N) = Σ_{n ≤ N} λ(n)/n` (a soma de Turán). -/
noncomputable def T (N : ℕ) : ℝ := ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.liouville n : ℝ) / n

theorem abs_termo_le (n : ℕ) : |(ArithmeticFunction.liouville n : ℝ) / n| ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    rw [abs_div, Nat.abs_cast, div_le_one (by linarith)]
    exact (abs_liouville_le n).trans hn1

theorem abs_T_le (N : ℕ) : |T N| ≤ 1 * ((N : ℝ) + 1) := by
  unfold T
  calc |∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.liouville n : ℝ) / n|
      ≤ ∑ n ∈ Finset.range (N + 1), |(ArithmeticFunction.liouville n : ℝ) / n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range (N + 1), (1 : ℝ) := Finset.sum_le_sum fun n _ => abs_termo_le n
    _ = 1 * ((N : ℝ) + 1) := by simp

theorem T_succ_eq (n : ℕ) : ((T (n + 1) : ℝ) : ℂ) = ∑ k ∈ Finset.range (n + 1), cT (k + 1) := by
  unfold T cT lam
  rw [Finset.sum_range_succ']
  push_cast
  simp

theorem term_cT (s : ℂ) (n : ℕ) : LSeries.term cT s n = LSeries.term lam (s + 1) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, cpow_add _ _ (Nat.cast_ne_zero.mpr hn),
      cpow_one]
    unfold cT
    field_simp

theorem LSeries_cT (s : ℂ) : LSeries cT s = LSeries lam (s + 1) := by
  unfold LSeries
  simp only [term_cT]

theorem LSeriesSummable_cT {s : ℂ} (hs : 0 < s.re) : LSeriesSummable cT s := by
  have h := LSeriesSummable_lam (s := s + 1) (by simp; linarith)
  unfold LSeriesSummable at h ⊢
  rw [show LSeries.term cT s = LSeries.term lam (s + 1) from funext (term_cT s)]
  exact h

theorem GA_T_eq {s : ℂ} (hs : 1 < s.re) : GA T s = riemannZeta (2 * s + 2) * F (s + 1) := by
  rw [ATK.ZeroClasses.Unilateral.GA_eq_LSeries' (θ := 1) (C := 1) zero_le_one
    (fun N => by rw [Real.rpow_one]; exact abs_T_le N) T_succ_eq hs (LSeriesSummable_cT (by linarith)),
    LSeries_cT, LSeries_lam (by simp; linarith)]
  congr 2
  ring

/-! ## 2. `Φ(s) = ζ(2s + 2)/ζ₁(s + 1)` no disco `|s − 2| < 5/2` -/

/-- `Φ(s) = ζ(2s + 2)/ζ₁(s + 1)`; é `GA T(s)/s` em `Re s > 1`. -/
noncomputable def Phi (s : ℂ) : ℂ := riemannZeta (2 * s + 2) / riemannZeta₁ (s + 1)

theorem zeta₁_ne_zero_faixa {w : ℂ} (h0 : 0 < w.re) (him : |w.im| ≤ 13) : riemannZeta₁ w ≠ 0 := by
  by_cases hw1 : w = 1
  · subst hw1; rw [riemannZeta₁_one]; exact one_ne_zero
  rw [zeta₁_eq hw1]
  refine mul_ne_zero (sub_ne_zero.mpr hw1) ?_
  rcases le_or_gt 1 w.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · exact ATK.ZeroClasses.Faixa.faixa_sem_zeros h0 h1 him

theorem mem_disco {s : ℂ} (hs : s ∈ ball (2 : ℂ) (5 / 2)) : -1 / 2 < s.re ∧ |s.im| < 5 / 2 := by
  rw [mem_ball, dist_eq_norm] at hs
  have h1 := abs_re_le_norm (s - 2)
  have h2 := abs_im_le_norm (s - 2)
  simp only [sub_re, sub_im, re_ofNat, im_ofNat, sub_zero] at h1 h2
  constructor
  · have := neg_abs_le (s.re - 2)
    linarith
  · linarith

theorem differentiableOn_Phi : DifferentiableOn ℂ Phi (ball (2 : ℂ) (5 / 2)) := by
  intro s hs
  obtain ⟨hre, him⟩ := mem_disco hs
  have h2s : 2 * s + 2 ≠ 1 := fun h => by
    have := congrArg re h
    simp at this
    linarith
  have hz : riemannZeta₁ (s + 1) ≠ 0 := zeta₁_ne_zero_faixa (by simp; linarith) (by simp; linarith)
  have d1 : DifferentiableAt ℂ (fun s => riemannZeta (2 * s + 2)) s :=
    (differentiableAt_riemannZeta h2s).comp s ((differentiableAt_id.const_mul 2).add_const 2)
  have d2 : DifferentiableAt ℂ (fun s => riemannZeta₁ (s + 1)) s :=
    (differentiable_riemannZeta₁ _).comp s (differentiableAt_id.add_const 1)
  exact (d1.div d2 hz).differentiableWithinAt

theorem Phi_mul (s : ℂ) : Phi s * s = riemannZeta (2 * s + 2) * F (s + 1) := by
  unfold Phi F
  rw [show s + 1 - 1 = s by ring]
  ring

/-! ## 3. Landau com `f(x) = T(⌊x⌋) ≥ 0` -/

/-- `f(x) = T(⌊x⌋)`. -/
noncomputable def fT (x : ℝ) : ℝ := T ⌊x⌋₊

theorem measurable_fT : Measurable fT := (measurable_from_nat (f := T)).comp Nat.measurable_floor

theorem intAcima_fT : IntAcima fT 1 := by
  intro σ hσ
  have hb := (integrableOn_Ioi_rpow_of_lt (show -σ < -1 by linarith) zero_lt_one).const_mul 2
  refine hb.mono' ((measurable_id.pow_const _).mul measurable_fT.abs).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx1 : (1 : ℝ) < x := hx
  have hx0 : 0 < x := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (abs_nonneg _))]
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have h1 := abs_T_le ⌊x⌋₊
  have hf : |fT x| ≤ 2 * x := by unfold fT; linarith
  calc x ^ (-σ - 1) * |fT x| ≤ x ^ (-σ - 1) * (2 * x) := mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg hx0.le _)
    _ = 2 * x ^ (-σ) := by
        rw [Real.rpow_sub_one hx0.ne']
        field_simp

theorem Ik_fT {s : ℂ} (hs : 1 < s.re) : Ik fT 0 s = GA T s / s := by
  unfold Ik fT
  rw [← integral_escada (fun N => by rw [one_mul]; exact (abs_T_le N).trans (by rw [one_mul]))
    hs]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  simp

/-- **A conjectura de Turán implica RH** (Turán 1948): se `T(N) = Σ_{n ≤ N} λ(n)/n ≥ 0` para todo `N`, vale RH.
(A conjectura é falsa — Haselgrove 1958 —, mas a implicação é o teorema.) -/
theorem rh_of_turan (h : ∀ N : ℕ, 0 ≤ T N) : RiemannHypothesis := by
  have hpos : ∀ x : ℝ, 1 < x → 0 ≤ fT x := fun x _ => h _
  have e2 : ((2 : ℝ) : ℂ) = 2 := by norm_num
  have hEq : ∀ s : ℂ, s ∈ ball ((2 : ℝ) : ℂ) (5 / 2) → 1 < s.re → Phi s = Ik fT 0 s := by
    intro s _ hs
    have hs0 : s ≠ 0 := fun h0 => by rw [h0, zero_re] at hs; linarith
    rw [Ik_fT hs, GA_T_eq hs, ← Phi_mul, mul_div_assoc, div_self hs0, mul_one]
  -- Landau: a integral converge em `σ > −½`
  have hI : IntAcima fT (-1 / 2) := by
    intro σ hσ
    rcases le_or_gt σ 2 with h2 | h2
    · have hL := (landau measurable_fT hpos intAcima_fT (by norm_num : (1 : ℝ) < 2)
        (by rw [e2]; exact differentiableOn_Phi) hEq (σ := σ) (by linarith) h2).1
      refine hL.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [abs_of_nonneg (hpos x hx)]
    · exact intAcima_fT σ (by linarith)
  -- `G(s) = s·Ik fT 0 s` é holomorfa em `Re s > −½` e vale `ζ(2s + 2)F(s + 1)` em `Re s > 0`
  set G : ℂ → ℂ := fun s => s * Ik fT 0 s with hG
  have hGd : ∀ s : ℂ, -1 / 2 < s.re → DifferentiableAt ℂ G s := fun s hs =>
    differentiableAt_id.mul (differentiableAt_Ik measurable_fT hI hs)
  set K : ℂ → ℂ := fun s => riemannZeta (2 * s + 2) * F (s + 1) with hK
  set U : Set ℂ := {s : ℂ | 0 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hKd : DifferentiableOn ℂ K U := by
    intro s hs
    have hs' : (0 : ℝ) < s.re := hs
    have h2s : 2 * s + 2 ≠ 1 := fun h => by
      have := congrArg re h
      simp at this
      linarith
    have hz : riemannZeta₁ (s + 1) ≠ 0 := by
      have hs1 : s + 1 ≠ 1 := fun h => by
        have := congrArg re h
        simp at this
        linarith
      rw [zeta₁_eq hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_le_re (by simp; linarith))
    have d1 : DifferentiableAt ℂ (fun s => riemannZeta (2 * s + 2)) s :=
      (differentiableAt_riemannZeta h2s).comp s ((differentiableAt_id.const_mul 2).add_const 2)
    have d2 : DifferentiableAt ℂ (fun s => F (s + 1)) s := by
      unfold F
      exact ((differentiableAt_id.add_const 1).sub_const 1).div
        ((differentiable_riemannZeta₁ _).comp s (differentiableAt_id.add_const 1)) hz
    exact (d1.mul d2).differentiableWithinAt
  have hGU : DifferentiableOn ℂ G U := fun s hs => (hGd s (by have : (0 : ℝ) < s.re := hs; linarith)).differentiableWithinAt
  have h2U : (2 : ℂ) ∈ U := by simp [hU]
  have hev : G =ᶠ[𝓝 (2 : ℂ)] K := by
    have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [hmem] with s hs
    have hs0 : s ≠ 0 := fun h0 => by rw [h0, zero_re] at hs; norm_num at hs
    simp only [hG, hK]
    rw [Ik_fT hs, GA_T_eq hs]
    field_simp
  have hGK := (hGU.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hKd.analyticOnNhd hUo) hUc h2U hev
  -- `H(w) = G(w − 1)`: extensão de `ζ(2w)F(w)` a `Re w > ½`
  have hZ : SemZeros (1 / 2) := by
    refine semZeros_of_ext_liouville (θ := 1 / 2) le_rfl (G := fun w => G (w - 1)) (fun w hw => ?_) fun w hw => ?_
    · exact (hGd (w - 1) (by simp; linarith)).comp w (differentiableAt_id.sub_const 1)
    · have hmem : w - 1 ∈ U := by simp [hU]; linarith
      rw [hGK hmem]
      simp only [hK]
      congr 2 <;> ring
  exact ATK.ZeroClasses.QuasiRH.semZeros_meio_iff.mp hZ

end ATK.ZeroClasses.TuranLiouville

#print axioms ATK.ZeroClasses.TuranLiouville.abs_termo_le
#print axioms ATK.ZeroClasses.TuranLiouville.abs_T_le
#print axioms ATK.ZeroClasses.TuranLiouville.T_succ_eq
#print axioms ATK.ZeroClasses.TuranLiouville.term_cT
#print axioms ATK.ZeroClasses.TuranLiouville.LSeries_cT
#print axioms ATK.ZeroClasses.TuranLiouville.LSeriesSummable_cT
#print axioms ATK.ZeroClasses.TuranLiouville.GA_T_eq
#print axioms ATK.ZeroClasses.TuranLiouville.zeta₁_ne_zero_faixa
#print axioms ATK.ZeroClasses.TuranLiouville.mem_disco
#print axioms ATK.ZeroClasses.TuranLiouville.differentiableOn_Phi
#print axioms ATK.ZeroClasses.TuranLiouville.Phi_mul
#print axioms ATK.ZeroClasses.TuranLiouville.measurable_fT
#print axioms ATK.ZeroClasses.TuranLiouville.intAcima_fT
#print axioms ATK.ZeroClasses.TuranLiouville.Ik_fT
#print axioms ATK.ZeroClasses.TuranLiouville.rh_of_turan
