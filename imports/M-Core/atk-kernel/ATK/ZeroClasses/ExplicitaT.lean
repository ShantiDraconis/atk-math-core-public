import ATK.ZeroClasses.ExplicitaLimite

/-!
# A fórmula explícita com `T → ∞` (rodada 72)

A rodada 71 deu a fórmula explícita ao longo de alturas boas `T_k ∈ [k + 6, k + 7]`. Aqui ela vale para
**todo** `T → ∞`: para `x = N + ½` (`N ≥ 1`),

  **`lim_{T → ∞} Σ_{|γ| ≤ T} m_ρ x^ρ/ρ = x − ψ(N) − log 2π − ½ log(1 − x^{−2})`**   (`formula_explicita_T`),

a soma sobre os zeros não triviais `Zfin T` (`ζ(ρ) = 0`, `Re ρ > 0`, `|Im ρ| ≤ T`; finito por `zfin_finite`).

* `norm_termo_le`: `‖m_ρ x^ρ/ρ‖ ≤ m_ρ x/Y` se `Re ρ ≤ 1` e `|Im ρ| ≥ Y > 0`;
* `soma_faixa_le`: a massa `Σ m_ρ` dos zeros com `k + 6 < |γ| ≤ k + 7` é `≤ 4 (a₀ + log(k + 9))/l₀` (as caixas de
  Jensen da rodada 63, `caixa_le'`);
* `dif_le`: para `T, T′ ∈ [k + 6, k + 7]`, `‖Σ_{Zfin T} − Σ_{Zfin T′}‖ ≤ 8 (a₀ + log(k + 9))/l₀ · x/(k + 6)`, que
  tende a zero.

Classificação (rodada 72): **consequência**. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology
open scoped Real

namespace ATK.ZeroClasses.ExplicitaT

open ATK.ZeroClasses.PsiRH (px)
open ATK.ZeroClasses.PerronD (xN)
open ATK.ZeroClasses.Canonico ATK.ZeroClasses.LagariasHadamard ATK.ZeroClasses.JensenLocal
  ATK.ZeroClasses.SomaZeros

theorem zfin_finite (T : ℝ) : {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ |ρ.im| ≤ T}.Finite := by
  refine ((ATK.ZeroClasses.Explicita.faixa_finito T).image rZ).subset ?_
  rintro ρ ⟨hz, hre, him⟩
  have h1 : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  obtain ⟨q, hq⟩ := ATK.ZeroClasses.Explicita.existe_q (ρ := ρ) ⟨hz, hre, h1⟩
  refine ⟨q, ?_, hq⟩
  show |(rZ q).im| ≤ T
  rw [hq]
  exact him

/-- Os zeros não triviais com `|γ| ≤ T`. -/
noncomputable def Zfin (T : ℝ) : Finset ℂ := (zfin_finite T).toFinset

theorem mem_Zfin {T : ℝ} {ρ : ℂ} : ρ ∈ Zfin T ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ |ρ.im| ≤ T := by
  unfold Zfin
  rw [Set.Finite.mem_toFinset]
  rfl

theorem re_lt_one {ρ : ℂ} (hz : riemannZeta ρ = 0) : ρ.re < 1 := by
  by_contra h
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz

/-- `‖m_ρ x^ρ/ρ‖ ≤ m_ρ x/Y`. -/
theorem norm_termo_le {x : ℝ} (hx : 1 ≤ x) {ρ : ℂ} (hρ1 : ρ.re ≤ 1) {Y : ℝ} (hY : 0 < Y)
    (hYρ : Y ≤ |ρ.im|) :
    ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * px x ρ‖ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * (x / Y) := by
  unfold px
  rw [norm_mul, Complex.norm_natCast, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have h1 : x ^ ρ.re ≤ x := by
    calc x ^ ρ.re ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hρ1
      _ = x := Real.rpow_one x
  exact div_le_div₀ (by linarith) h1 hY (hYρ.trans (abs_im_le_norm ρ))

/-- **A massa dos zeros com `k + 6 < |γ| ≤ k + 7`**: `≤ 4 (a₀ + log(k + 9))/l₀`. -/
theorem soma_faixa_le (k : ℕ) :
    ∑ ρ ∈ Zfin ((k : ℝ) + 7) \ Zfin ((k : ℝ) + 6), (analyticOrderNatAt riemannZeta ρ : ℝ) ≤
      4 * ((a0 + Real.log ((k : ℝ) + 9)) / l0) := by
  classical
  set D := Zfin ((k : ℝ) + 7) \ Zfin ((k : ℝ) + 6) with hD
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hmem : ∀ ρ ∈ D, ρ ∈ ATK.ZetaSimetria.Z ∧ (k : ℝ) + 6 < |ρ.im| ∧ |ρ.im| ≤ (k : ℝ) + 7 := by
    intro ρ hρ
    rw [hD, Finset.mem_sdiff, mem_Zfin, mem_Zfin] at hρ
    obtain ⟨⟨hz, hre, him⟩, hn⟩ := hρ
    refine ⟨⟨hz, hre, re_lt_one hz⟩, ?_, him⟩
    by_contra h
    exact hn ⟨hz, hre, not_lt.mp h⟩
  have hLc : Lc |(k : ℝ) + 13 / 2| ≤ (a0 + Real.log ((k : ℝ) + 9)) / l0 := by
    rw [abs_of_pos (by linarith)]
    refine (Lc_le (by linarith)).trans (div_le_div_of_nonneg_right ?_ l0_pos.le)
    have := Real.log_le_log (by linarith : (0 : ℝ) < 2 + ((k : ℝ) + 13 / 2)) (by linarith :
      2 + ((k : ℝ) + 13 / 2) ≤ (k : ℝ) + 9)
    linarith
  have hpos := (Finset.sum_filter_add_sum_filter_not D (fun ρ : ℂ => 0 < ρ.im)
    (fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ))).symm
  rw [hpos]
  have h1 : ∑ ρ ∈ D.filter (fun ρ : ℂ => 0 < ρ.im), (analyticOrderNatAt riemannZeta ρ : ℝ) ≤
      2 * Lc |(k : ℝ) + 13 / 2| := by
    refine caixa_le' _ fun ρ hρ => ?_
    obtain ⟨hρD, hpos⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hZ, h6, h7⟩ := hmem ρ hρD
    rw [abs_of_pos hpos] at h6 h7
    exact ⟨hZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have h2 : ∑ ρ ∈ D.filter (fun ρ : ℂ => ¬ 0 < ρ.im), (analyticOrderNatAt riemannZeta ρ : ℝ) ≤
      2 * Lc |(k : ℝ) + 13 / 2| := by
    have e : |(k : ℝ) + 13 / 2| = |-((k : ℝ) + 13 / 2)| := (abs_neg _).symm
    rw [e]
    refine caixa_le' _ fun ρ hρ => ?_
    obtain ⟨hρD, hneg⟩ := Finset.mem_filter.mp hρ
    obtain ⟨hZ, h6, h7⟩ := hmem ρ hρD
    have hle : ρ.im ≤ 0 := not_lt.mp hneg
    rw [abs_of_nonpos hle] at h6 h7
    exact ⟨hZ, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  linarith

/-- **`‖Σ_{Zfin T} − Σ_{Zfin T′}‖ ≤ 8 (a₀ + log(k + 9))/l₀ · x/(k + 6)`** para `T, T′ ∈ [k + 6, k + 7]`. -/
theorem dif_le {x : ℝ} (hx : 1 ≤ x) (k : ℕ) {T T' : ℝ} (h1 : (k : ℝ) + 6 ≤ T) (h2 : T ≤ k + 7)
    (h1' : (k : ℝ) + 6 ≤ T') (h2' : T' ≤ k + 7) :
    ‖∑ ρ ∈ Zfin T, (analyticOrderNatAt riemannZeta ρ : ℂ) * px x ρ -
      ∑ ρ ∈ Zfin T', (analyticOrderNatAt riemannZeta ρ : ℂ) * px x ρ‖ ≤
      2 * (4 * ((a0 + Real.log ((k : ℝ) + 9)) / l0) * (x / ((k : ℝ) + 6))) := by
  classical
  set f : ℂ → ℂ := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℂ) * px x ρ with hf
  set D := Zfin ((k : ℝ) + 7) \ Zfin ((k : ℝ) + 6) with hD
  have hk0 : (0 : ℝ) ≤ k := k.cast_nonneg
  have hY : (0 : ℝ) < (k : ℝ) + 6 := by linarith
  have hsub : ∀ {A B : ℝ}, (k : ℝ) + 6 ≤ B → A ≤ k + 7 → Zfin A \ Zfin B ⊆ D := by
    intro A B hB hA ρ hρ
    rw [Finset.mem_sdiff, mem_Zfin, mem_Zfin] at hρ
    obtain ⟨⟨hz, hre, him⟩, hn⟩ := hρ
    rw [hD, Finset.mem_sdiff, mem_Zfin, mem_Zfin]
    refine ⟨⟨hz, hre, him.trans hA⟩, fun ⟨_, _, h⟩ => hn ⟨hz, hre, h.trans hB⟩⟩
  have hDb : ∑ ρ ∈ D, ‖f ρ‖ ≤ 4 * ((a0 + Real.log ((k : ℝ) + 9)) / l0) * (x / ((k : ℝ) + 6)) := by
    have hterm : ∀ ρ ∈ D, ‖f ρ‖ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * (x / ((k : ℝ) + 6)) := by
      intro ρ hρ
      rw [hD, Finset.mem_sdiff, mem_Zfin, mem_Zfin] at hρ
      obtain ⟨⟨hz, _, _⟩, hn⟩ := hρ
      have hY' : (k : ℝ) + 6 ≤ |ρ.im| := by
        by_contra h
        exact hn ⟨hz, by assumption, (not_le.mp h).le⟩
      exact norm_termo_le hx (re_lt_one hz).le hY hY'
    calc ∑ ρ ∈ D, ‖f ρ‖ ≤ ∑ ρ ∈ D, (analyticOrderNatAt riemannZeta ρ : ℝ) * (x / ((k : ℝ) + 6)) :=
          Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ D, (analyticOrderNatAt riemannZeta ρ : ℝ)) * (x / ((k : ℝ) + 6)) := by
          rw [Finset.sum_mul]
      _ ≤ 4 * ((a0 + Real.log ((k : ℝ) + 9)) / l0) * (x / ((k : ℝ) + 6)) :=
          mul_le_mul_of_nonneg_right (soma_faixa_le k) (by positivity)
  have hpart : ∀ {A B : ℝ}, (k : ℝ) + 6 ≤ B → A ≤ k + 7 →
      ‖∑ ρ ∈ Zfin A \ Zfin B, f ρ‖ ≤ 4 * ((a0 + Real.log ((k : ℝ) + 9)) / l0) * (x / ((k : ℝ) + 6)) := by
    intro A B hB hA
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum_of_subset_of_nonneg (hsub hB hA)
      fun _ _ _ => norm_nonneg _).trans hDb)
  rw [← Finset.sum_sdiff_sub_sum_sdiff]
  refine (norm_sub_le _ _).trans ?_
  have a1 := hpart (A := T) (B := T') h1' h2
  have a2 := hpart (A := T') (B := T) h1 h2'
  linarith

/-- **A fórmula explícita com `T → ∞`**: para `x = N + ½`, `N ≥ 1`,
`Σ_{|γ| ≤ T} m_ρ x^ρ/ρ → x − ψ(N) − log 2π − ½ log(1 − x^{−2})` quando `T → ∞`. -/
theorem formula_explicita_T (N : ℕ) (hN : 1 ≤ N) :
    Tendsto (fun T : ℝ => ∑ ρ ∈ Zfin T, (analyticOrderNatAt riemannZeta ρ : ℂ) * px (xN N) ρ) atTop
      (𝓝 ((xN N : ℂ) - Chebyshev.psi N - Real.log (2 * π) - 1 / 2 * Real.log (1 - (xN N ^ 2)⁻¹))) := by
  obtain ⟨Tk, hTk, S, hS, hlim⟩ := ATK.ZeroClasses.ExplicitaLimite.formula_explicita N hN
  have hSZ : ∀ k, S k = Zfin (Tk k) := fun k => by
    ext u
    rw [hS, mem_Zfin]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx : 1 ≤ xN N := by unfold xN; linarith
  have hl0 := l0_pos
  set e : ℕ → ℝ := fun k => 2 * (4 * ((a0 + Real.log ((k : ℝ) + 9)) / l0) * (xN N / ((k : ℝ) + 6)))
    with he_def
  have he : Tendsto e atTop (𝓝 0) := by
    have := ((ATK.ZeroClasses.ExplicitaLimite.lim_log 0).const_mul (8 * a0 * xN N / l0)).add
      ((ATK.ZeroClasses.ExplicitaLimite.lim_log 1).const_mul (8 * xN N / l0))
    simp only [mul_zero, add_zero] at this
    refine this.congr fun k => ?_
    have hk : (k : ℝ) + 6 ≠ 0 := by positivity
    simp only [he_def, pow_zero, pow_one]
    field_simp
    ring
  rw [Metric.tendsto_atTop] at hlim he ⊢
  intro ε hε
  obtain ⟨K₁, hK₁⟩ := hlim (ε / 2) (by linarith)
  obtain ⟨K₂, hK₂⟩ := he (ε / 2) (by linarith)
  refine ⟨(max K₁ K₂ : ℕ) + 6, fun T hT => ?_⟩
  have hT6 : (6 : ℝ) ≤ T := by
    have : (0 : ℝ) ≤ (max K₁ K₂ : ℕ) := Nat.cast_nonneg _
    linarith
  have hfl : max K₁ K₂ + 6 ≤ ⌊T⌋₊ := Nat.le_floor (by push_cast at hT ⊢; linarith)
  set k : ℕ := ⌊T⌋₊ - 6 with hk
  have hkr : (k : ℝ) = (⌊T⌋₊ : ℝ) - 6 := by
    rw [hk, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hk1 : (k : ℝ) + 6 ≤ T := by rw [hkr]; linarith [Nat.floor_le (by linarith : (0 : ℝ) ≤ T)]
  have hk2 : T ≤ (k : ℝ) + 7 := by rw [hkr]; linarith [Nat.lt_floor_add_one T]
  have hkK : max K₁ K₂ ≤ k := by omega
  have hd := dif_le hx k hk1 hk2 (hTk k).1 (hTk k).2
  rw [← hSZ k] at hd
  have hA := hK₁ k (le_of_max_le_left hkK)
  have hB := hK₂ k (le_of_max_le_right hkK)
  rw [Real.dist_eq, sub_zero] at hB
  rw [dist_eq_norm] at hA ⊢
  have hBabs : e k < ε / 2 := (le_abs_self _).trans_lt hB
  calc ‖∑ ρ ∈ Zfin T, (analyticOrderNatAt riemannZeta ρ : ℂ) * px (xN N) ρ -
        ((xN N : ℂ) - Chebyshev.psi N - Real.log (2 * π) - 1 / 2 * Real.log (1 - (xN N ^ 2)⁻¹))‖
      ≤ ‖∑ ρ ∈ Zfin T, (analyticOrderNatAt riemannZeta ρ : ℂ) * px (xN N) ρ -
          ∑ u ∈ S k, (analyticOrderNatAt riemannZeta u : ℂ) * px (xN N) u‖ +
        ‖∑ u ∈ S k, (analyticOrderNatAt riemannZeta u : ℂ) * px (xN N) u -
          ((xN N : ℂ) - Chebyshev.psi N - Real.log (2 * π) - 1 / 2 * Real.log (1 - (xN N ^ 2)⁻¹))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hd.trans hBabs.le) hA
    _ = ε := by ring

end ATK.ZeroClasses.ExplicitaT

#print axioms ATK.ZeroClasses.ExplicitaT.zfin_finite
#print axioms ATK.ZeroClasses.ExplicitaT.mem_Zfin
#print axioms ATK.ZeroClasses.ExplicitaT.re_lt_one
#print axioms ATK.ZeroClasses.ExplicitaT.norm_termo_le
#print axioms ATK.ZeroClasses.ExplicitaT.soma_faixa_le
#print axioms ATK.ZeroClasses.ExplicitaT.dif_le
#print axioms ATK.ZeroClasses.ExplicitaT.formula_explicita_T
