import ATK.ZetaLog
import ATK.RHTerminal

/-!
# ATK-RH — O critério das somas parciais de `η`

`P_M(s) = Σ_{k=1}^{2M} (−1)^{k+1} k^{−s}` e `η(s) = (1 − 2^{1−s})ζ(s)`.

* `Peta_eq`: `P_M(s) = Σ_{n≤2M} n^{−s} − 2^{1−s} Σ_{n≤M} n^{−s}`.
* `eta_sub_Peta`: para `Re s > 0`, `s ≠ 1`, `M ≥ 1`: **`η(s) − P_M(s) = −s(H_{2M}(s) − 2^{1−s}H_M(s))`**
  (`H_N` = cauda `∫_N^∞ {u}u^{−s−1}du` de `ATK.ZetaParcial`).
* `norm_eta_sub_Peta`: **`|η(s) − P_M(s)| ≤ 3|s|(2M)^{−σ}/σ`**; em `K_n`:
  `≤ E_{n,M} = 6√(1+n²)(2M)^{−1/2} → 0`.
* **`rh_iff_criterioEta`**: HR ⟺ para todo `n ≥ 5` existe `M` com `E_{n,M} < inf_{K_n} |P_M|` (no formato
  `∃ L, L ≤ |P_M| em K_n ∧ E_{n,M} < L`). Cada instância é uma conta finita sobre somas de Dirichlet
  alternadas; o `∀ n` é HR.
-/

open Complex Filter Topology Set

namespace ATK.EtaCriterio

open ATK.ZetaParcial ATK.ClosedMath.Terminal

/-- `P_M(s) = Σ_{k=1}^{2M} (−1)^{k+1} k^{−s}`. -/
noncomputable def Peta (M : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 (2 * M), (-1 : ℂ) ^ (k + 1) * (k : ℂ) ^ (-s)

theorem cpow_dois (m : ℕ) (s : ℂ) : ((2 * m : ℕ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * (m : ℂ) ^ (-s) := by
  have := Complex.mul_cpow_ofReal_nonneg (a := 2) (b := m) (by norm_num) (by positivity) (-s)
  push_cast at this ⊢
  exact this

theorem Peta_eq (M : ℕ) (s : ℂ) :
    Peta M s = ∑ n ∈ Finset.Icc 1 (2 * M), (n : ℂ) ^ (-s) -
      (2 : ℂ) ^ (1 - s) * ∑ n ∈ Finset.Icc 1 M, (n : ℂ) ^ (-s) := by
  induction M with
  | zero => simp [Peta]
  | succ M ih =>
    unfold Peta at ih ⊢
    rw [show 2 * (M + 1) = (2 * M + 1) + 1 by ring, Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have e1 : (-1 : ℂ) ^ (2 * M + 1 + 1) = 1 := by
      rw [show 2 * M + 1 + 1 = 2 * (M + 1) by ring, pow_mul]; norm_num
    have e2 : (-1 : ℂ) ^ (2 * M + 1 + 1 + 1) = -1 := by
      rw [show 2 * M + 1 + 1 + 1 = 2 * (M + 1) + 1 by ring, pow_succ, pow_mul]; norm_num
    have e3 : (((2 * M + 1 + 1 : ℕ) : ℂ)) ^ (-s) = (2 : ℂ) ^ (-s) * ((M + 1 : ℕ) : ℂ) ^ (-s) := by
      rw [show 2 * M + 1 + 1 = 2 * (M + 1) by ring]; exact cpow_dois (M + 1) s
    have e4 : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := ATK.ZetaParcial.cpow_one_sub h2 s
    rw [e1, e2, e3, e4]
    ring

/-- **`η(s) − P_M(s) = −s(H_{2M}(s) − 2^{1−s}H_M(s))`.** -/
theorem eta_sub_Peta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {M : ℕ} (hM : 1 ≤ M) :
    ATK.ClosedMath.Terminal.eta s - Peta M s = -s * (HN (2 * M) s - (2 : ℂ) ^ (1 - s) * HN M s) := by
  have h1 := zeta_parcial hs hs1 (2 * M) (by omega)
  have h2 := zeta_parcial hs hs1 M hM
  have hB : ((2 * M : ℕ) : ℂ) ^ (1 - s) / (s - 1) = (2 : ℂ) ^ (1 - s) * ((M : ℂ) ^ (1 - s) / (s - 1)) := by
    rw [ATK.ZetaParcial.cpow_one_sub (by exact_mod_cast (show 2 * M ≠ 0 by omega)) s,
      ATK.ZetaParcial.cpow_one_sub (two_ne_zero) s,
      ATK.ZetaParcial.cpow_one_sub (by exact_mod_cast (show M ≠ 0 by omega)) s, cpow_dois]
    push_cast
    ring
  unfold ATK.ClosedMath.Terminal.eta
  rw [Peta_eq]
  linear_combination h1 - (2 : ℂ) ^ (1 - s) * h2 + hB

/-- **`|η(s) − P_M(s)| ≤ 3|s|(2M)^{−σ}/σ`.** -/
theorem norm_eta_sub_Peta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {M : ℕ} (hM : 1 ≤ M) :
    ‖ATK.ClosedMath.Terminal.eta s - Peta M s‖ ≤ 3 * ‖s‖ * ((2 * M : ℕ) : ℝ) ^ (-s.re) / s.re := by
  rw [eta_sub_Peta hs hs1 hM, norm_mul, norm_neg]
  have hA := ATK.ZetaLog.norm_HN_le (N := 2 * M) (by omega) hs
  have hB := ATK.ZetaLog.norm_HN_le (N := M) hM hs
  have h2 : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos (x := 2) (by norm_num) (1 - s)
    push_cast at this
    rw [this]; simp
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hk : (2 : ℝ) ^ (1 - s.re) * (M : ℝ) ^ (-s.re) = 2 * ((2 * M : ℕ) : ℝ) ^ (-s.re) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
    push_cast
    rw [Real.mul_rpow (by norm_num) hM0.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have htri : ‖HN (2 * M) s - (2 : ℂ) ^ (1 - s) * HN M s‖ ≤
      ((2 * M : ℕ) : ℝ) ^ (-s.re) / s.re + (2 : ℝ) ^ (1 - s.re) * ((M : ℝ) ^ (-s.re) / s.re) := by
    refine (norm_sub_le _ _).trans (add_le_add hA ?_)
    rw [norm_mul, h2]
    exact mul_le_mul_of_nonneg_left hB (by positivity)
  have e : ((2 * M : ℕ) : ℝ) ^ (-s.re) / s.re + (2 : ℝ) ^ (1 - s.re) * ((M : ℝ) ^ (-s.re) / s.re) =
      3 * ((2 * M : ℕ) : ℝ) ^ (-s.re) / s.re := by
    rw [mul_div_assoc', hk]; ring
  rw [e] at htri
  calc ‖s‖ * ‖HN (2 * M) s - (2 : ℂ) ^ (1 - s) * HN M s‖ ≤ ‖s‖ * (3 * ((2 * M : ℕ) : ℝ) ^ (-s.re) / s.re) :=
        mul_le_mul_of_nonneg_left htri (norm_nonneg _)
    _ = 3 * ‖s‖ * ((2 * M : ℕ) : ℝ) ^ (-s.re) / s.re := by ring

/-- A cota uniforme em `K_n`: `E_{n,M} = 6√(1+n²)(2M)^{−1/2}`. -/
noncomputable def Ebeta (n M : ℕ) : ℝ := 6 * Real.sqrt (1 + (n : ℝ) ^ 2) * ((2 * M : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))

theorem eta_uniforme {n : ℕ} (hn : 5 ≤ n) {M : ℕ} (hM : 1 ≤ M) :
    ∀ s ∈ Kn n, ‖ATK.ClosedMath.Terminal.eta s - Peta M s‖ ≤ Ebeta n M := by
  intro s hs
  have hS := Kn_sub hn hs
  have hσ : 1 / 2 < s.re := hS.1
  have hσ0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by rintro rfl; have := hS.2; simp at this
  refine (norm_eta_sub_Peta hσ0 hs1 hM).trans ?_
  have hN : (1 : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * M by omega)
  have hpow : ((2 * M : ℕ) : ℝ) ^ (-s.re) ≤ ((2 * M : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hnorm := norm_le_Kn hn hs
  have hinv : 1 / s.re ≤ 2 := by rw [div_le_iff₀ hσ0]; linarith
  have hp0 : 0 ≤ ((2 * M : ℕ) : ℝ) ^ (-s.re) := by positivity
  unfold Ebeta
  calc 3 * ‖s‖ * ((2 * M : ℕ) : ℝ) ^ (-s.re) / s.re
      = 3 * ‖s‖ * ((2 * M : ℕ) : ℝ) ^ (-s.re) * (1 / s.re) := by ring
    _ ≤ 3 * Real.sqrt (1 + (n : ℝ) ^ 2) * ((2 * M : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * 2 := by
        gcongr
    _ = 6 * Real.sqrt (1 + (n : ℝ) ^ 2) * ((2 * M : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by ring

theorem Ebeta_tende_zero (n : ℕ) : Tendsto (fun M : ℕ => Ebeta n M) atTop (𝓝 0) := by
  unfold Ebeta
  have h2 : Tendsto (fun M : ℕ => ((2 * M : ℕ) : ℝ)) atTop atTop := by
    have : Tendsto (fun M : ℕ => 2 * M) atTop atTop :=
      Filter.tendsto_atTop_mono (fun M => by show M ≤ 2 * M; omega) tendsto_id
    exact tendsto_natCast_atTop_atTop.comp this
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp h2
  simpa using h.const_mul (6 * Real.sqrt (1 + (n : ℝ) ^ 2))

/-- O critério de somas parciais de `η`. -/
def CriterioEta : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∃ M : ℕ, 1 ≤ M ∧ ∃ L : ℝ, (∀ s ∈ Kn n, L ≤ ‖Peta M s‖) ∧ Ebeta n M < L

/-- **HR ⟺ critério de somas parciais de `η`.** -/
theorem rh_iff_criterioEta : RiemannHypothesis ↔ CriterioEta := by
  rw [rh_iff_delta]
  constructor
  · intro h n hn
    have hd := h n hn
    obtain ⟨-, hmin⟩ := delta_atingido hn
    have ev := (Ebeta_tende_zero n).eventually (gt_mem_nhds (half_pos hd))
    obtain ⟨M, hM2, hM1⟩ := (ev.and (eventually_ge_atTop 1)).exists
    refine ⟨M, hM1, delta n / 2, fun s hs => ?_, hM2⟩
    have e := eta_uniforme hn hM1 s hs
    have t := norm_sub_norm_le (ATK.ClosedMath.Terminal.eta s) (ATK.ClosedMath.Terminal.eta s - Peta M s)
    rw [sub_sub_cancel] at t
    have := hmin s hs
    linarith
  · intro h n hn
    obtain ⟨M, hM, L, hL, hEL⟩ := h n hn
    obtain ⟨⟨s₀, hs₀, he⟩, -⟩ := delta_atingido hn
    rw [he]
    have e := eta_uniforme hn hM s₀ hs₀
    have t := norm_sub_norm_le (Peta M s₀) (Peta M s₀ - ATK.ClosedMath.Terminal.eta s₀)
    rw [sub_sub_cancel, norm_sub_rev] at t
    have := hL s₀ hs₀
    linarith

end ATK.EtaCriterio

-- Auditoria de axiomas (kernel)
#print axioms ATK.EtaCriterio.cpow_dois
#print axioms ATK.EtaCriterio.Peta_eq
#print axioms ATK.EtaCriterio.eta_sub_Peta
#print axioms ATK.EtaCriterio.norm_eta_sub_Peta
#print axioms ATK.EtaCriterio.eta_uniforme
#print axioms ATK.EtaCriterio.Ebeta_tende_zero
#print axioms ATK.EtaCriterio.rh_iff_criterioEta
