import ATK.ZetaStrip

/-!
# Bohr–Landau, passo 2 — Euler–Maclaurin de primeira ordem para `N` geral

Para `0 < Re s`, `s ≠ 1` e `N ≥ 1`:

  **`ζ(s) = Σ_{n=1}^{N} n^{−s} + N^{1−s}/(s−1) − s·I_N(s)`**, `I_N(s) = ∫_N^∞ t^{−s−1} {t} dt`.

O caso `N = 1` sai de `ATK.ZetaStrip.H_eq_zeta`; o passo `N → N+1` é o cálculo exato da integral
num degrau `(N, N+1]`, onde `{t} = t − N`.
-/

open Complex Set MeasureTheory intervalIntegral

namespace ATK.BLEulerMaclaurin

open ATK.ZetaStrip

/-- A cauda `I_N(s) = ∫_N^∞ t^{−s−1} {t} dt`. -/
noncomputable def cauda (N : ℕ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (N : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)

theorem integrableOn_cauda {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 1 ≤ a) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)) (Ioi a) :=
  (integrableOn_cpow_mul_fract hs).mono_set (Ioi_subset_Ioi ha)

/-- A integral num degrau `(N, N+1]`. -/
theorem degrau {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    ∫ t in Ioc (N : ℝ) (N + 1), (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ) =
      (((N : ℂ) + 1) ^ (1 - s) - (N : ℂ) ^ (1 - s)) / (1 - s) +
        ((N : ℂ) / s) * (((N : ℂ) + 1) ^ (-s) - (N : ℂ) ^ (-s)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hle : (N : ℝ) ≤ N + 1 := by linarith
  rw [← intervalIntegral.integral_of_le hle]
  have hcongr : ∀ᵐ t ∂volume, t ∈ Set.uIoc (N : ℝ) (N + 1) →
      (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ) =
        (t : ℂ) ^ (-s) - (N : ℂ) * (t : ℂ) ^ (-s - 1) := by
    have hfin : ∀ᵐ t ∂volume, t ≠ (N : ℝ) + 1 := by
      have : volume ({(N : ℝ) + 1} : Set ℝ) = 0 := Real.volume_singleton
      filter_upwards [compl_mem_ae_iff.mpr this] with t ht
      simpa using ht
    filter_upwards [hfin] with t hne ht
    rw [Set.uIoc_of_le hle] at ht
    have htlt : t < N + 1 := lt_of_le_of_ne ht.2 hne
    have hfl : ⌊t⌋ = (N : ℤ) := by
      rw [Int.floor_eq_iff]; push_cast; exact ⟨ht.1.le, htlt⟩
    have hfr : Int.fract t = t - N := by
      rw [Int.fract, hfl]; push_cast; ring
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (hN0.trans ht.1).ne'
    have hpow : (t : ℂ) ^ (-s) = (t : ℂ) ^ (-s - 1) * (t : ℂ) := by
      rw [show -s = (-s - 1) + 1 by ring, cpow_add _ _ ht0, cpow_one]; ring_nf
    rw [hfr, hpow]; push_cast; ring
  rw [intervalIntegral.integral_congr_ae hcongr]
  have h0 : (0 : ℝ) ∉ Set.uIcc (N : ℝ) (N + 1) := by
    rw [Set.uIcc_of_le hle]; intro h; linarith [h.1]
  have i1 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s)) volume (N : ℝ) (N + 1) :=
    intervalIntegral.intervalIntegrable_cpow (Or.inr h0)
  have i2 : IntervalIntegrable (fun t : ℝ => (N : ℂ) * (t : ℂ) ^ (-s - 1)) volume (N : ℝ) (N + 1) :=
    (intervalIntegral.intervalIntegrable_cpow (Or.inr h0)).const_mul _
  rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
    integral_cpow (Or.inr ⟨by intro h; apply hs1; linear_combination -h, h0⟩),
    integral_cpow (Or.inr ⟨by intro h; apply hs0; linear_combination -h, h0⟩)]
  have e1 : -s + 1 = 1 - s := by ring
  have e2 : -s - 1 + 1 = -s := by ring
  rw [e1, e2]
  push_cast
  have hs' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring

/-- `I_N = ∫_{(N, N+1]} + I_{N+1}`. -/
theorem cauda_split {s : ℂ} (hs : 0 < s.re) (N : ℕ) (hN : 1 ≤ N) :
    cauda N s = (∫ t in Ioc (N : ℝ) (N + 1), (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)) +
      cauda (N + 1) s := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hint := integrableOn_cauda hs hN1
  have hu := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self)
    (hint.mono_set (Ioi_subset_Ioi (by linarith : (N : ℝ) ≤ N + 1)))
  rw [Ioc_union_Ioi_eq_Ioi (by linarith : (N : ℝ) ≤ N + 1)] at hu
  unfold cauda
  rw [hu]
  push_cast
  rfl

/-- **Euler–Maclaurin**: `ζ(s) = Σ_{n<N} (n+1)^{−s} + N^{1−s}/(s−1) − s·I_N(s)`. -/
theorem zeta_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (N : ℕ) (hN : 1 ≤ N) :
    riemannZeta s = (∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-s)) +
      (N : ℂ) ^ (1 - s) / (s - 1) - s * cauda N s := by
  have hs0 : s ≠ 0 := by intro h; rw [h, zero_re] at hs; exact lt_irrefl 0 hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  induction N, hN using Nat.le_induction with
  | base =>
    have hH := H_eq_zeta hs hs1
    rw [H_eq_integral] at hH
    have hc : cauda 1 s = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ) := by
      unfold cauda; simp
    rw [hc, hH]
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, zero_add, one_cpow,
      Nat.cast_one]
    field_simp
    ring
  | succ N hN ih =>
    rw [ih, cauda_split hs N hN, degrau hs0 hs1 N hN, Finset.sum_range_succ]
    have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hN1c : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast (show N + 1 ≠ 0 by omega)
    have hA : ((N : ℂ) + 1) ^ (1 - s) = ((N : ℂ) + 1) * ((N : ℂ) + 1) ^ (-s) := by
      rw [show 1 - s = 1 + -s by ring, cpow_add _ _ hN1c, cpow_one]
    have hB : (N : ℂ) ^ (1 - s) = (N : ℂ) * (N : ℂ) ^ (-s) := by
      rw [show 1 - s = 1 + -s by ring, cpow_add _ _ hNc, cpow_one]
    have hcast : ((N + 1 : ℕ) : ℂ) = (N : ℂ) + 1 := by push_cast; ring
    rw [hcast, hA, hB]
    have hs' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    field_simp
    ring

end ATK.BLEulerMaclaurin

#print axioms ATK.BLEulerMaclaurin.degrau
#print axioms ATK.BLEulerMaclaurin.cauda_split
#print axioms ATK.BLEulerMaclaurin.zeta_eq
#print axioms ATK.BLEulerMaclaurin.integrableOn_cauda
