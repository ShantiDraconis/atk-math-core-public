import ATK.BLCauda
import ATK.BLDirichlet

/-!
# Bohr–Landau, passo 5 — média quadrática de `ζ` à direita de `1/2`

Para `1/2 < σ₀ ≤ 3/4` existe `C` tal que, para todo `σ ∈ [σ₀, 4]` e todo `Y ≥ 1`,

  **`∫_{1/2}^{Y} |ζ(σ + it)|² dt ≤ C·Y`** (`media_zeta`).

Bloco `[U, 2U]` (`bloco`): Euler–Maclaurin com `N = ⌊U⌋`, `ζ = D_N + N^{1−s}/(s−1) − s·I_N`;
`∫|D_N|² ≤ C U` (`BLDirichlet.media_D`), `|N^{1−s}/(s−1)| ≤ 1`, e
`∫|s I_N|² ≤ 16U² ∫_ℝ |I_N|² ≤ 16U² π N^{−2σ}/σ ≤ 32πU/σ₀` (`BLCauda.cauda_L2`).
Parte baixa `[1/2, 2]` por compacidade; o resto por blocos diádicos.
-/

open Complex Set MeasureTheory intervalIntegral Filter

namespace ATK.BLMediaZeta

open ATK.BLEulerMaclaurin ATK.BLCauda ATK.BLDirichlet

/-- `t ↦ |ζ(σ + it)|²` é contínua em `t > 0`. -/
theorem continuousOn_sq (σ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) (Set.uIcc a b) := by
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  have ht0 : 0 < t := ha.trans_le ht.1
  have hs1 : (σ : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have hin : ContinuousAt (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) t := by fun_prop
  have hc : ContinuousAt (fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I)) t :=
    ContinuousAt.comp (g := riemannZeta) (differentiableAt_riemannZeta hs1).continuousAt hin
  exact (hc.norm.pow 2).continuousWithinAt

theorem intervalIntegrable_sq (σ : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume a b :=
  (continuousOn_sq σ ha hab).intervalIntegrable

theorem sq_three (x y z : ℂ) : ‖x + y - z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have h : ‖x + y - z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ :=
    (norm_sub_le _ _).trans (by linarith [norm_add_le x y])
  have h0 : 0 ≤ ‖x + y - z‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖y‖ - ‖z‖), sq_nonneg (‖x‖ - ‖z‖),
    norm_nonneg x, norm_nonneg y, norm_nonneg z]

/-- **Bloco diádico**: `∫_U^{2U} |ζ(σ+it)|² ≤ C U` para `U ≥ 2`, `σ ∈ [σ₀, 4]`. -/
theorem bloco {σ0 : ℝ} (h0 : 1 / 2 < σ0) (h1 : σ0 ≤ 3 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ0 ≤ σ → σ ≤ 4 → ∀ U : ℝ, 2 ≤ U →
      ∫ t in U..2 * U, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ C * U := by
  obtain ⟨CD, hCD0, hCD⟩ := media_D h0 h1
  have hσ0 : 0 < σ0 := by linarith
  refine ⟨3 * (CD + 1 + 32 * Real.pi / σ0), by positivity, fun σ hσ hσ4 U hU => ?_⟩
  have hσpos : 0 < σ := by linarith
  set N : ℕ := ⌊U⌋₊ with hNdef
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hU)
  have hN1 : 1 ≤ N := by omega
  have hNU : (N : ℝ) ≤ U := Nat.floor_le (by linarith)
  have hUN : U < (N : ℝ) + 1 := Nat.lt_floor_add_one U
  have hN2r : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hU2N : U ≤ 2 * (N : ℝ) := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨hcInt, hcBound⟩ := cauda_L2 hσpos hN1
  set g : ℝ → ℝ := fun t =>
    3 * (‖D N σ t‖ ^ 2 + 1 + 16 * U ^ 2 * ‖cauda N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) with hg
  -- cota pontual
  have hpt : ∀ t ∈ Set.Icc U (2 * U),
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ g t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
    have hsre : s.re = σ := by simp [hs]
    have hsim : s.im = t := by simp [hs]
    have hs1 : s ≠ 1 := by intro h; have := congrArg Complex.im h; simp [hs] at this; linarith
    have hEM := zeta_eq (by rw [hsre]; exact hσpos) hs1 N hN1
    have hD : (∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-s)) = D N σ t := rfl
    rw [hEM, hD]
    have hX : ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ ≤ 1 := by
      rw [norm_div, Complex.norm_natCast_cpow_of_pos (by omega)]
      have hre : (1 - s).re = 1 - σ := by simp [hsre]
      rw [hre]
      have hden : U ≤ ‖s - 1‖ := by
        have := Complex.abs_im_le_norm (s - 1)
        have him : (s - 1).im = t := by simp [hsim]
        rw [him, abs_of_pos ht0] at this
        linarith [ht.1]
      have hnum : (N : ℝ) ^ (1 - σ) ≤ U := by
        calc (N : ℝ) ^ (1 - σ) ≤ (N : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
          _ = N := Real.rpow_one _
          _ ≤ U := hNU
      rw [div_le_one (by linarith)]
      linarith
    have hY : ‖s * cauda N s‖ ^ 2 ≤ 16 * U ^ 2 * ‖cauda N s‖ ^ 2 := by
      rw [norm_mul, mul_pow]
      have hsn : ‖s‖ ≤ 4 * U := by
        calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
          _ = σ + t := by rw [hsre, hsim, abs_of_pos hσpos, abs_of_pos ht0]
          _ ≤ 4 * U := by linarith [ht.2]
      have : ‖s‖ ^ 2 ≤ 16 * U ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg s) hsn 2; nlinarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have h3 := sq_three (D N σ t) ((N : ℂ) ^ (1 - s) / (s - 1)) (s * cauda N s)
    have hX2 : ‖(N : ℂ) ^ (1 - s) / (s - 1)‖ ^ 2 ≤ 1 := by
      have := norm_nonneg ((N : ℂ) ^ (1 - s) / (s - 1)); nlinarith
    simp only [hg]
    nlinarith
  -- integrabilidade
  have hU0 : (0 : ℝ) < U := by linarith
  have hDcont : Continuous fun t : ℝ => ‖D N σ t‖ ^ 2 := by
    have : Continuous fun t : ℝ => D N σ t := by
      unfold D
      refine continuous_finset_sum _ fun n _ => ?_
      exact Continuous.const_cpow (by fun_prop) (Or.inl (Nat.cast_add_one_ne_zero n))
    exact this.norm.pow 2
  have hgInt : IntervalIntegrable g volume U (2 * U) := by
    have h1 : IntervalIntegrable (fun t : ℝ => ‖D N σ t‖ ^ 2) volume U (2 * U) :=
      hDcont.intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun t : ℝ => ‖cauda N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume U (2 * U) :=
      hcInt.intervalIntegrable
    exact ((h1.add intervalIntegrable_const).add (h2.const_mul _)).const_mul _
  have hle := intervalIntegral.integral_mono_on (by linarith) (intervalIntegrable_sq σ hU0 (by linarith))
    hgInt hpt
  -- integral de g
  have hcauda : ∫ t in U..2 * U, ‖cauda N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      Real.pi * (N : ℝ) ^ (-2 * σ) / σ := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine le_trans ?_ hcBound
    exact setIntegral_le_integral hcInt (Filter.Eventually.of_forall fun t => sq_nonneg _)
  have hpow : (N : ℝ) ^ (-2 * σ) ≤ (N : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hcauda2 : 16 * U ^ 2 * ∫ t in U..2 * U, ‖cauda N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      32 * Real.pi / σ0 * U := by
    have hNinv : (N : ℝ) ^ (-1 : ℝ) = 1 / N := by rw [Real.rpow_neg_one, one_div]
    have step1 : Real.pi * (N : ℝ) ^ (-2 * σ) / σ ≤ Real.pi / (σ0 * N) := by
      calc Real.pi * (N : ℝ) ^ (-2 * σ) / σ ≤ Real.pi * (1 / N) / σ := by
            rw [← hNinv]; gcongr
        _ ≤ Real.pi * (1 / N) / σ0 := by
            apply div_le_div_of_nonneg_left (by positivity) hσ0 hσ
        _ = Real.pi / (σ0 * N) := by field_simp
    have step2 : 16 * U ^ 2 * (Real.pi / (σ0 * N)) ≤ 32 * Real.pi / σ0 * U := by
      rw [show 16 * U ^ 2 * (Real.pi / (σ0 * N)) = 16 * Real.pi / σ0 * (U * (U / N)) by
        field_simp]
      have hUN' : U / N ≤ 2 := by rw [div_le_iff₀ hNpos]; linarith
      have : U * (U / N) ≤ U * 2 := mul_le_mul_of_nonneg_left hUN' hU0.le
      calc 16 * Real.pi / σ0 * (U * (U / N)) ≤ 16 * Real.pi / σ0 * (U * 2) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = 32 * Real.pi / σ0 * U := by ring
    calc 16 * U ^ 2 * ∫ t in U..2 * U, ‖cauda N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
        ≤ 16 * U ^ 2 * (Real.pi / (σ0 * N)) :=
          mul_le_mul_of_nonneg_left (hcauda.trans step1) (by positivity)
      _ ≤ _ := step2
  have hDb := hCD σ hσ N U (by linarith) hNU
  have hgval : ∫ t in U..2 * U, g t =
      3 * ((∫ t in U..2 * U, ‖D N σ t‖ ^ 2) + U +
        16 * U ^ 2 * ∫ t in U..2 * U, ‖cauda N ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) := by
    simp only [hg]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      ((hDcont.intervalIntegrable _ _).add intervalIntegrable_const)
      (hcInt.intervalIntegrable.const_mul _), intervalIntegral.integral_add
      (hDcont.intervalIntegrable _ _) intervalIntegrable_const, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, smul_eq_mul, mul_one]
    ring
  calc ∫ t in U..2 * U, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ ∫ t in U..2 * U, g t := hle
    _ = _ := hgval
    _ ≤ 3 * (CD * U + U + 32 * Real.pi / σ0 * U) := by gcongr
    _ = 3 * (CD + 1 + 32 * Real.pi / σ0) * U := by ring

/-- Parte baixa `[1/2, 2]`, uniforme em `σ ∈ [σ₀, 4]`. -/
theorem parte_baixa (σ0 : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ0 ≤ σ → σ ≤ 4 →
      ∫ t in (1 / 2 : ℝ)..2, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ C := by
  set K : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * I) ''
    (Set.Icc σ0 4 ×ˢ Set.Icc (1 / 2 : ℝ) 2) with hK
  have hKc : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  have hcont : ContinuousOn riemannZeta K := by
    rintro z ⟨p, hp, rfl⟩
    have hs1 : (p.1 : ℂ) + (p.2 : ℂ) * I ≠ 1 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith [hp.2.1]
    exact (differentiableAt_riemannZeta hs1).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨3 / 2 * M ^ 2, by positivity, fun σ hσ hσ4 => ?_⟩
  have hb : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 2, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ M ^ 2 := by
    intro t ht
    have hz := hM ((σ : ℂ) + (t : ℂ) * I) ⟨(σ, t), ⟨⟨hσ, hσ4⟩, ht⟩, rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg _) hz 2
  calc ∫ t in (1 / 2 : ℝ)..2, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ ∫ t in (1 / 2 : ℝ)..2, M ^ 2 :=
        intervalIntegral.integral_mono_on (by norm_num)
          (intervalIntegrable_sq σ (by norm_num) (by norm_num)) intervalIntegrable_const hb
    _ = 3 / 2 * M ^ 2 := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- **Média quadrática de `ζ`**: `∫_{1/2}^{Y} |ζ(σ+it)|² dt ≤ C·Y`. -/
theorem media_zeta {σ0 : ℝ} (h0 : 1 / 2 < σ0) (h1 : σ0 ≤ 3 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, σ0 ≤ σ → σ ≤ 4 → ∀ Y : ℝ, 1 ≤ Y →
      ∫ t in (1 / 2 : ℝ)..Y, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ C * Y := by
  obtain ⟨C2, hC20, hC2⟩ := bloco h0 h1
  obtain ⟨C1, hC10, hC1⟩ := parte_baixa σ0
  refine ⟨C1 + 4 * C2, by positivity, fun σ hσ hσ4 Y hY => ?_⟩
  -- diádico: ∫_{1/2}^{2^(k+1)} ≤ C1 + C2 * 2^(k+1)
  have hdy : ∀ k : ℕ, ∫ t in (1 / 2 : ℝ)..2 ^ (k + 1),
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ C1 + C2 * 2 ^ (k + 1) := by
    intro k
    induction k with
    | zero =>
      norm_num
      have := hC1 σ hσ hσ4
      linarith [mul_nonneg hC20 (by norm_num : (0:ℝ) ≤ 2)]
    | succ k ih =>
      have hpk : (2 : ℝ) ≤ 2 ^ (k + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_sq σ (a := 1 / 2) (b := 2 ^ (k + 1)) (by norm_num) (by linarith))
        (intervalIntegrable_sq σ (a := 2 ^ (k + 1)) (b := 2 * 2 ^ (k + 1)) (by linarith) (by linarith))
      have e : (2 : ℝ) ^ (k + 1 + 1) = 2 * 2 ^ (k + 1) := by ring
      rw [e, ← hsplit]
      have hb := hC2 σ hσ hσ4 (2 ^ (k + 1)) hpk
      nlinarith
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hY (by norm_num : (1 : ℝ) < 2)
  have hYk : Y ≤ 2 ^ (n + 1) := hn2.le
  have hkY : (2 : ℝ) ^ (n + 1) ≤ 2 * Y := by rw [pow_succ]; linarith
  have hmono : ∫ t in (1 / 2 : ℝ)..Y, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      ∫ t in (1 / 2 : ℝ)..2 ^ (n + 1), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
    refine intervalIntegral.integral_mono_interval le_rfl (by linarith) hYk ?_
      (intervalIntegrable_sq σ (by norm_num) (by linarith))
    exact Filter.Eventually.of_forall fun t => sq_nonneg _
  calc ∫ t in (1 / 2 : ℝ)..Y, ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2
      ≤ C1 + C2 * 2 ^ (n + 1) := hmono.trans (hdy n)
    _ ≤ C1 * Y + C2 * (2 * Y) := by
        have : C1 ≤ C1 * Y := le_mul_of_one_le_right hC10 hY
        nlinarith
    _ ≤ (C1 + 4 * C2) * Y := by nlinarith

end ATK.BLMediaZeta

#print axioms ATK.BLMediaZeta.bloco
#print axioms ATK.BLMediaZeta.parte_baixa
#print axioms ATK.BLMediaZeta.media_zeta
#print axioms ATK.BLMediaZeta.continuousOn_sq
#print axioms ATK.BLMediaZeta.intervalIntegrable_sq
#print axioms ATK.BLMediaZeta.sq_three
