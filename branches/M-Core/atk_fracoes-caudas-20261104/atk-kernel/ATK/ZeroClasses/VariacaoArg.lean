import ATK.ZeroClasses.ArgRetangulo

/-!
# `S(T) = O(log T)`: a variação do argumento de `ζ` no segmento horizontal (rodada 41)

**Teorema** (`variacao_log`). Existe `C` tal que, para `T ≥ 4` sem zero de `ζ` no segmento `[½ + iT, 2 + iT]`,

  `|Im ∫_{1/2}^{2} ζ′/ζ(σ + iT) dσ| ≤ C log T`.

É o termo `S(T)` de Riemann–von Mangoldt. A prova é a de Backlund:

1. **variação simples** (`variacao_simples`): num intervalo onde `Re ζ(σ + iT)` não se anula no interior, `±ζ` fica no
   semiplano fechado `Re ≥ 0`, `log(±ζ)` é uma primitiva de `ζ′/ζ` e `|Im ∫| ≤ π` (os dois argumentos estão em
   `[−π/2, π/2]`);
2. **indução** (`variacao`): com `k` zeros de `Re ζ(σ + iT)` no interior, `|Im ∫| ≤ (k + 1)π`;
3. **contagem por Jensen** (`conta_zeros_re`): `Re ζ(σ + iT) = g(σ)` para `g(s) = (ζ(s + iT) + ζ(s − iT))/2`, que
   é analítica em `‖s − 2‖ ≤ 7/4`. Lá vale `|g| ≤ 6T + 38` (`cota_zeta_quarto`, por Euler–Maclaurin de ordem 1),
   e `|g(2)| ≥ 2 − π²/6` (`re_zeta_dois`). Daí o número de zeros reais em `[½, 2]` é
   `≤ log((6T + 38)/(2 − π²/6))/log(7/6)`.

Classificação (rodada 41): **ferramenta** — o terceiro ingrediente de Riemann–von Mangoldt. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real Interval

namespace ATK.ZeroClasses.VariacaoArg

/-! ## 1. `|ζ|` em `Re s ≥ ¼` -/

theorem EM11 (s : ℂ) : ATK.EMGeral.EM 1 1 s = 1 / 2 + 1 / (s - 1) := by
  simp [ATK.EMGeral.EM]
  ring

theorem poch1 (s : ℂ) : ATK.EMGeral.poch s 1 = s := by simp [ATK.EMGeral.poch]

theorem Cb1 : ATK.EMGeral.Cb 1 = 3 / 2 := by
  simp [ATK.EMGeral.Cb, Finset.sum_range_succ, bernoulli_one]
  norm_num

/-- **`|ζ(s)| ≤ ½ + 1/|s − 1| + 6|s|`** em `Re s ≥ ¼`, pela fórmula de Euler–Maclaurin de ordem 1 do kernel. -/
theorem cota_zeta_quarto {s : ℂ} (hs : 1 / 4 ≤ s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / 2 + 1 / ‖s - 1‖ + 6 * ‖s‖ := by
  have hpos : 0 < s.re := by linarith
  have h := ATK.EMGeral.norm_zeta_sub_EM_le hpos hs1 (N := 1) le_rfl (M := 1) le_rfl
  rw [EM11, poch1, Cb1] at h
  simp only [Nat.factorial_one, Nat.cast_one, div_one, Real.one_rpow, mul_one] at h
  have hσ : s.re + 1 - 1 = s.re := by ring
  rw [hσ] at h
  have hs0 : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
  have hEM : ‖(1 / 2 + 1 / (s - 1) : ℂ)‖ ≤ 1 / 2 + 1 / ‖s - 1‖ := by
    calc ‖(1 / 2 + 1 / (s - 1) : ℂ)‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖1 / (s - 1)‖ := norm_add_le _ _
      _ = 1 / 2 + 1 / ‖s - 1‖ := by rw [norm_div, norm_one]; norm_num
  have hr : ‖s‖ * (3 / 2 / s.re) ≤ 6 * ‖s‖ := by
    have : 3 / 2 / s.re ≤ 6 := by rw [div_le_iff₀ hpos]; linarith
    nlinarith [norm_nonneg s]
  have htri : ‖riemannZeta s‖ ≤ ‖(1 / 2 + 1 / (s - 1) : ℂ)‖ +
      ‖riemannZeta s - (1 / 2 + 1 / (s - 1))‖ := by
    have := norm_add_le (1 / 2 + 1 / (s - 1) : ℂ) (riemannZeta s - (1 / 2 + 1 / (s - 1)))
    rwa [add_sub_cancel] at this
  linarith

/-- `Re ζ(s) ≥ 2 − π²/6` em `Re s ≥ 2`. -/
theorem re_zeta_dois {s : ℂ} (hs : 2 ≤ s.re) : 2 - π ^ 2 / 6 ≤ (riemannZeta s).re := by
  have hs1 : 1 < s.re := by linarith
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow hs1
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hf
  have hnorm : ∀ n : ℕ, ‖f n‖ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    simp only [hf, norm_div, norm_one]
    have e : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_natCast_cpow_of_pos (by omega)]
    have e2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [e2]
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have h2 : ((n : ℝ) + 1) ^ (2 : ℝ) ≤ ((n : ℝ) + 1) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le h1 hs
    rw [Real.rpow_two] at h2
    exact one_div_le_one_div_of_le (by positivity) h2
  have hR : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hsum : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnorm hR.summable
  have hfs : Summable f := hsum.of_norm
  have hf0 : f 0 = 1 := by simp [hf]
  have htot : ∑' n, ‖f n‖ ≤ Real.pi ^ 2 / 6 := by
    rw [← hR.tsum_eq]
    exact hsum.tsum_le_tsum hnorm hR.summable
  have htail : ∑' n, ‖f (n + 1)‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    have h1 := hsum.tsum_eq_zero_add
    rw [hf0, norm_one] at h1
    linarith
  have hs1' : Summable (fun n => ‖f (n + 1)‖) := (summable_nat_add_iff 1).mpr hsum
  have hle : ‖∑' n, f (n + 1)‖ ≤ Real.pi ^ 2 / 6 - 1 := (norm_tsum_le_tsum_norm hs1').trans htail
  have hzeta : riemannZeta s = 1 + ∑' n, f (n + 1) := by
    rw [hz]
    change ∑' n, f n = _
    rw [hfs.tsum_eq_zero_add, hf0]
  rw [hzeta, add_re, one_re]
  have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hle)).1
  linarith

/-! ## 2. A variação do argumento -/

theorem ne_um {T : ℝ} (hT : 1 ≤ |T|) (σ : ℝ) : (σ : ℂ) + T * I ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  rw [this, abs_zero] at hT
  norm_num at hT

theorem hasDerivAt_zeta_horiz {T : ℝ} (hT : 1 ≤ |T|) (σ : ℝ) :
    HasDerivAt (fun x : ℝ => riemannZeta (x + T * I)) (deriv riemannZeta (σ + T * I)) σ := by
  have h1 : HasDerivAt (fun w : ℂ => riemannZeta (w + T * I)) (deriv riemannZeta (σ + T * I)) (σ : ℂ) :=
    ((differentiableAt_riemannZeta (ne_um hT σ)).hasDerivAt).comp_add_const (σ : ℂ) ((T : ℂ) * I)
  exact h1.comp_ofReal

theorem continuous_zeta_horiz {T : ℝ} (hT : 1 ≤ |T|) : Continuous fun x : ℝ => riemannZeta (x + T * I) :=
  continuous_iff_continuousAt.mpr fun σ => (hasDerivAt_zeta_horiz hT σ).continuousAt

theorem continuousOn_logDeriv_horiz {T a b : ℝ} (hT : 1 ≤ |T|)
    (hnz : ∀ σ ∈ Icc a b, riemannZeta (σ + T * I) ≠ 0) :
    ContinuousOn (fun σ : ℝ => logDeriv riemannZeta (σ + T * I)) (Icc a b) := by
  intro σ hσ
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have han : AnalyticAt ℂ riemannZeta ((σ : ℂ) + T * I) :=
    analyticOn_riemannZeta _ (ne_um hT σ)
  have hc : ContinuousAt (fun x : ℝ => (x : ℂ) + T * I) σ := by fun_prop
  have h1 : ContinuousAt (fun x : ℝ => deriv riemannZeta (x + T * I)) σ :=
    han.deriv.continuousAt.comp (f := fun x : ℝ => (x : ℂ) + T * I) hc
  have h2 : ContinuousAt (fun x : ℝ => riemannZeta (x + T * I)) σ := (continuous_zeta_horiz hT).continuousAt
  exact (h1.div h2 (hnz σ hσ)).continuousWithinAt

theorem integrable_logDeriv_horiz {T a b : ℝ} (hT : 1 ≤ |T|) (hab : a ≤ b)
    (hnz : ∀ σ ∈ Icc a b, riemannZeta (σ + T * I) ≠ 0) :
    IntervalIntegrable (fun σ : ℝ => logDeriv riemannZeta (σ + T * I)) MeasureTheory.volume a b :=
  (continuousOn_logDeriv_horiz hT hnz).intervalIntegrable_of_Icc hab

/-- **Variação simples**: sem zeros de `Re ζ(σ + iT)` no interior de `[a, b]`, `|Im ∫_a^b ζ′/ζ| ≤ π`. -/
theorem variacao_simples {T a b : ℝ} (hT : 1 ≤ |T|) (hab : a ≤ b)
    (hnz : ∀ σ ∈ Icc a b, riemannZeta (σ + T * I) ≠ 0)
    (hre : ∀ σ ∈ Ioo a b, (riemannZeta (σ + T * I)).re ≠ 0) :
    |(∫ σ in a..b, logDeriv riemannZeta (σ + T * I)).im| ≤ π := by
  rcases eq_or_lt_of_le hab with rfl | hab'
  · simp only [intervalIntegral.integral_same, zero_im, abs_zero]
    exact Real.pi_pos.le
  set h : ℝ → ℝ := fun σ => (riemannZeta (σ + T * I)).re with hh
  have hcont : Continuous h := Complex.continuous_re.comp (continuous_zeta_horiz hT)
  obtain ⟨ε, hε, hpos⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ σ ∈ Ioo a b, 0 < ε * h σ := by
    set m := (a + b) / 2
    have hm : m ∈ Ioo a b := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
    rcases lt_or_gt_of_ne (hre m hm) with hneg | hpos'
    · refine ⟨-1, Or.inr rfl, fun σ hσ => ?_⟩
      by_contra hc
      have h0 : 0 < h σ := lt_of_le_of_ne (by linarith) (Ne.symm (hre σ hσ))
      obtain ⟨x, hx, hx0⟩ := isPreconnected_Ioo.intermediate_value hm hσ hcont.continuousOn
        ⟨hneg.le, h0.le⟩
      exact hre x hx hx0
    · refine ⟨1, Or.inl rfl, fun σ hσ => ?_⟩
      by_contra hc
      have h0 : h σ < 0 := lt_of_le_of_ne (by linarith) (hre σ hσ)
      obtain ⟨x, hx, hx0⟩ := isPreconnected_Ioo.intermediate_value hσ hm hcont.continuousOn
        ⟨h0.le, hpos'.le⟩
      exact hre x hx hx0
  have hε0 : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hcl : IsClosed {σ : ℝ | 0 ≤ ε * h σ} := isClosed_le continuous_const (continuous_const.mul hcont)
  have hIcc : ∀ σ ∈ Icc a b, 0 ≤ ε * h σ := by
    have : Icc a b ⊆ {σ : ℝ | 0 ≤ ε * h σ} := by
      rw [← closure_Ioo hab'.ne]
      exact hcl.closure_subset_iff.mpr fun σ hσ => (hpos σ hσ).le
    exact fun σ hσ => this hσ
  have hreε : ∀ σ : ℝ, ((ε : ℂ) * riemannZeta (σ + T * I)).re = ε * h σ := by
    intro σ
    simp [hh]
  have hslit : ∀ σ ∈ Icc a b, (ε : ℂ) * riemannZeta (σ + T * I) ∈ slitPlane := by
    intro σ hσ
    rw [mem_slitPlane_iff]
    rcases lt_or_eq_of_le (hIcc σ hσ) with hlt | heq
    · left
      rw [hreε]
      exact hlt
    · right
      intro him
      have hz : (ε : ℂ) * riemannZeta (σ + T * I) = 0 := by
        apply Complex.ext
        · rw [hreε, ← heq, zero_re]
        · rw [him, zero_im]
      exact (mul_ne_zero hε0 (hnz σ hσ)) hz
  set L : ℝ → ℂ := fun σ => log ((ε : ℂ) * riemannZeta (σ + T * I)) with hL
  have hLcont : ContinuousOn L (Icc a b) := by
    intro σ hσ
    have hc : ContinuousAt (fun x : ℝ => (ε : ℂ) * riemannZeta (x + T * I)) σ :=
      (continuous_const.mul (continuous_zeta_horiz hT)).continuousAt
    exact (hc.clog (hslit σ hσ)).continuousWithinAt
  have hLder : ∀ σ ∈ Ioo a b, HasDerivAt L (logDeriv riemannZeta (σ + T * I)) σ := by
    intro σ hσ
    have hσ' : σ ∈ Icc a b := Ioo_subset_Icc_self hσ
    have h1 := ((hasDerivAt_zeta_horiz hT σ).const_mul (ε : ℂ)).clog_real (hslit σ hσ')
    have e : (ε : ℂ) * deriv riemannZeta (σ + T * I) / ((ε : ℂ) * riemannZeta (σ + T * I)) =
        logDeriv riemannZeta (σ + T * I) := by
      rw [logDeriv_apply, mul_div_mul_left _ _ hε0]
    rw [e] at h1
    exact h1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hLcont hLder
    (integrable_logDeriv_horiz hT hab hnz)
  rw [hFTC, sub_im, hL]
  simp only [log_im]
  have ha := abs_arg_le_pi_div_two_iff.mpr
    (show 0 ≤ ((ε : ℂ) * riemannZeta (a + T * I)).re by rw [hreε]; exact hIcc a ⟨le_rfl, hab⟩)
  have hb := abs_arg_le_pi_div_two_iff.mpr
    (show 0 ≤ ((ε : ℂ) * riemannZeta (b + T * I)).re by rw [hreε]; exact hIcc b ⟨hab, le_rfl⟩)
  rw [abs_le] at ha hb ⊢
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

/-- **Indução**: se os zeros de `Re ζ(σ + iT)` em `(a, b)` estão num conjunto com `≤ k` pontos,
`|Im ∫_a^b ζ′/ζ| ≤ (k + 1)π`. -/
theorem variacao {T : ℝ} (hT : 1 ≤ |T|) (k : ℕ) : ∀ a b : ℝ, a ≤ b →
    (∀ σ ∈ Icc a b, riemannZeta (σ + T * I) ≠ 0) → ∀ A : Finset ℝ,
    (∀ σ ∈ Ioo a b, (riemannZeta (σ + T * I)).re = 0 → σ ∈ A) → A.card ≤ k →
    |(∫ σ in a..b, logDeriv riemannZeta (σ + T * I)).im| ≤ (k + 1) * π := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro a b hab hnz A hA hk
    by_cases hz : ∃ c ∈ Ioo a b, (riemannZeta (c + T * I)).re = 0
    · obtain ⟨c, hc, hc0⟩ := hz
      have hcA : c ∈ A := hA c hc hc0
      set A₁ := (A.erase c).filter (· < c) with hA₁
      set A₂ := (A.erase c).filter (c < ·) with hA₂
      have hdisj : Disjoint A₁ A₂ := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        rw [hA₁, Finset.mem_filter] at hx1
        rw [hA₂, Finset.mem_filter] at hx2
        linarith [hx1.2, hx2.2]
      have hsub : A₁ ∪ A₂ ⊆ A.erase c := by
        intro x hx
        rcases Finset.mem_union.mp hx with h | h <;> exact (Finset.mem_filter.mp h).1
      have hcard : A₁.card + A₂.card ≤ k - 1 := by
        rw [← Finset.card_union_of_disjoint hdisj]
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hcA] at this
        omega
      have hk0 : 1 ≤ k := by
        have := Finset.card_pos.mpr ⟨c, hcA⟩
        omega
      have hac : a ≤ c := hc.1.le
      have hcb : c ≤ b := hc.2.le
      have hnz1 : ∀ σ ∈ Icc a c, riemannZeta (σ + T * I) ≠ 0 := fun σ hσ =>
        hnz σ ⟨hσ.1, hσ.2.trans hcb⟩
      have hnz2 : ∀ σ ∈ Icc c b, riemannZeta (σ + T * I) ≠ 0 := fun σ hσ =>
        hnz σ ⟨hac.trans hσ.1, hσ.2⟩
      have hA1 : ∀ σ ∈ Ioo a c, (riemannZeta (σ + T * I)).re = 0 → σ ∈ A₁ := by
        intro σ hσ h0
        rw [hA₁, Finset.mem_filter, Finset.mem_erase]
        exact ⟨⟨hσ.2.ne, hA σ ⟨hσ.1, hσ.2.trans hc.2⟩ h0⟩, hσ.2⟩
      have hA2 : ∀ σ ∈ Ioo c b, (riemannZeta (σ + T * I)).re = 0 → σ ∈ A₂ := by
        intro σ hσ h0
        rw [hA₂, Finset.mem_filter, Finset.mem_erase]
        exact ⟨⟨hσ.1.ne', hA σ ⟨hc.1.trans hσ.1, hσ.2⟩ h0⟩, hσ.1⟩
      have h1 := ih A₁.card (by omega) a c hac hnz1 A₁ hA1 le_rfl
      have h2 := ih A₂.card (by omega) c b hcb hnz2 A₂ hA2 le_rfl
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (integrable_logDeriv_horiz hT hac hnz1) (integrable_logDeriv_horiz hT hcb hnz2), add_im]
      have hsum : ((A₁.card : ℝ) + 1) * π + ((A₂.card : ℝ) + 1) * π ≤ (k + 1) * π := by
        have : (A₁.card : ℝ) + A₂.card ≤ k - 1 := by
          have := hcard
          have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
            rw [Nat.cast_sub hk0]
            simp
          exact_mod_cast (hk1 ▸ (by exact_mod_cast this : ((A₁.card + A₂.card : ℕ) : ℝ) ≤ ((k - 1 : ℕ) : ℝ)))
        nlinarith [Real.pi_pos]
      calc |(∫ σ in a..c, logDeriv riemannZeta (σ + T * I)).im +
            (∫ σ in c..b, logDeriv riemannZeta (σ + T * I)).im|
          ≤ |(∫ σ in a..c, logDeriv riemannZeta (σ + T * I)).im| +
            |(∫ σ in c..b, logDeriv riemannZeta (σ + T * I)).im| := abs_add_le _ _
        _ ≤ ((A₁.card : ℝ) + 1) * π + ((A₂.card : ℝ) + 1) * π := add_le_add h1 h2
        _ ≤ (k + 1) * π := hsum
    · push_neg at hz
      have := variacao_simples hT hab hnz hz
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [Real.pi_pos]

/-! ## 3. Contagem dos zeros de `Re ζ(σ + iT)` por Jensen -/

/-- `g(s) = (ζ(s + iT) + ζ(s − iT))/2`, que vale `Re ζ(σ + iT)` no eixo real. -/
noncomputable def gT (T : ℝ) (s : ℂ) : ℂ := (riemannZeta (s + T * I) + riemannZeta (s - T * I)) / 2

theorem gT_real (T σ : ℝ) : gT T σ = ((riemannZeta (σ + T * I)).re : ℂ) := by
  have hc : riemannZeta ((σ : ℂ) - T * I) = (starRingEnd ℂ) (riemannZeta (σ + T * I)) := by
    rw [← riemannZeta_conj]
    congr 1
    apply Complex.ext <;> simp
  unfold gT
  rw [hc, Complex.add_conj]
  push_cast
  ring

theorem gT_analitica {T : ℝ} (hT : 4 ≤ T) : AnalyticOnNhd ℂ (gT T) (closedBall (2 : ℂ) 2) := by
  intro s hs
  rw [mem_closedBall, dist_eq_norm] at hs
  have him : |s.im| ≤ 2 := by
    have := Complex.abs_im_le_norm (s - 2)
    simp only [sub_im, im_ofNat, sub_zero] at this
    linarith
  have h1 : s + T * I ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith [(abs_le.mp him).1]
  have h2 : s - T * I ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith [(abs_le.mp him).2]
  have a1 : AnalyticAt ℂ (fun s : ℂ => riemannZeta (s + T * I)) s :=
    (analyticOn_riemannZeta _ h1).comp (f := fun s : ℂ => s + T * I) (x := s)
      (analyticAt_id.add analyticAt_const : AnalyticAt ℂ (fun s : ℂ => s + T * I) s)
  have a2 : AnalyticAt ℂ (fun s : ℂ => riemannZeta (s - T * I)) s :=
    (analyticOn_riemannZeta _ h2).comp (f := fun s : ℂ => s - T * I) (x := s)
      (analyticAt_id.sub analyticAt_const : AnalyticAt ℂ (fun s : ℂ => s - T * I) s)
  exact (a1.add a2).div_const

/-- `|ζ(s ± iT)| ≤ 6T + 38` no disco `‖s − 2‖ ≤ 7/4`, logo `‖gT T s‖ ≤ 6T + 38`. -/
theorem cota_gT {T : ℝ} (hT : 4 ≤ T) {s : ℂ} (hs : ‖s - 2‖ ≤ 7 / 4) : ‖gT T s‖ ≤ 6 * T + 38 := by
  have hre : |s.re - 2| ≤ 7 / 4 := by
    have := Complex.abs_re_le_norm (s - 2)
    simp only [sub_re, re_ofNat] at this
    linarith
  have him : |s.im| ≤ 7 / 4 := by
    have := Complex.abs_im_le_norm (s - 2)
    simp only [sub_im, im_ofNat, sub_zero] at this
    linarith
  have hb : ∀ w : ℂ, w.re = s.re → T - 7 / 4 ≤ |w.im| → |w.im| ≤ T + 7 / 4 → w ≠ 1 →
      ‖riemannZeta w‖ ≤ 6 * T + 38 := by
    intro w hwr hwi1 hwi2 hw1
    have h := cota_zeta_quarto (by rw [hwr]; linarith [(abs_le.mp hre).1]) hw1
    have hn1 : 1 ≤ ‖w - 1‖ := by
      have := Complex.abs_im_le_norm (w - 1)
      simp only [sub_im, one_im, sub_zero] at this
      linarith
    have hn : ‖w‖ ≤ 15 / 4 + (T + 7 / 4) := by
      have := Complex.norm_le_abs_re_add_abs_im w
      have hwre : |w.re| ≤ 15 / 4 := by
        rw [hwr, abs_le]
        constructor <;> linarith [(abs_le.mp hre).1, (abs_le.mp hre).2]
      linarith
    have hinv : 1 / ‖w - 1‖ ≤ 1 := by rw [div_le_one (by linarith)]; exact hn1
    nlinarith
  have hip : (s + T * I).im = s.im + T := by simp
  have him' : (s - T * I).im = s.im - T := by simp
  have hp : ‖riemannZeta (s + T * I)‖ ≤ 6 * T + 38 := by
    refine hb _ (by simp) ?_ ?_ ?_
    · rw [hip, abs_of_pos (by linarith [(abs_le.mp him).1])]
      linarith [(abs_le.mp him).1]
    · rw [hip, abs_of_pos (by linarith [(abs_le.mp him).1])]
      linarith [(abs_le.mp him).2]
    · intro h
      have := congrArg Complex.im h
      simp at this
      linarith [(abs_le.mp him).1]
  have hm : ‖riemannZeta (s - T * I)‖ ≤ 6 * T + 38 := by
    refine hb _ (by simp) ?_ ?_ ?_
    · rw [him', abs_of_neg (by linarith [(abs_le.mp him).2])]
      linarith [(abs_le.mp him).2]
    · rw [him', abs_of_neg (by linarith [(abs_le.mp him).2])]
      linarith [(abs_le.mp him).1]
    · intro h
      have := congrArg Complex.im h
      simp at this
      linarith [(abs_le.mp him).2]
  unfold gT
  rw [norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have := norm_add_le (riemannZeta (s + T * I)) (riemannZeta (s - T * I))
  rw [div_le_iff₀ (by norm_num)]
  linarith

/-- **Contagem**: os zeros de `Re ζ(σ + iT)` em `(½, 2)` formam um conjunto finito com
`≤ log((6T + 38)/(2 − π²/6))/log(7/6)` pontos. -/
theorem conta_zeros_re {T : ℝ} (hT : 4 ≤ T) :
    ∃ A : Finset ℝ, (∀ σ ∈ Ioo (1 / 2 : ℝ) 2, (riemannZeta (σ + T * I)).re = 0 → σ ∈ A) ∧
      (A.card : ℝ) ≤ Real.log ((6 * T + 38) / (2 - π ^ 2 / 6)) / Real.log (7 / 6) := by
  classical
  have hb := ATK.BLProva.dois_menos_pos
  have hg2 : 2 - π ^ 2 / 6 ≤ ‖gT T 2‖ := by
    have e : gT T 2 = gT T ((2 : ℝ) : ℂ) := by norm_num
    rw [e, gT_real, Complex.norm_real, Real.norm_eq_abs]
    have := re_zeta_dois (s := (2 : ℂ) + T * I) (by simp)
    have e2 : ((2 : ℝ) : ℂ) + T * I = (2 : ℂ) + T * I := by norm_num
    rw [e2]
    exact this.trans (le_abs_self _)
  have hg0 : gT T 2 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hg2
    linarith
  have han := gT_analitica hT
  have han' : AnalyticOnNhd ℂ (gT T) (closedBall (2 : ℂ) |(7 / 4 : ℝ)|) := by
    rw [abs_of_pos (by norm_num)]
    exact han.mono (closedBall_subset_closedBall (by norm_num))
  have htop : ∀ u ∈ closedBall (2 : ℂ) (3 / 2), analyticOrderAt (gT T) u ≠ ⊤ := fun u hu =>
    ATK.ArgPrincipio.ordem_finita han (convex_closedBall (2 : ℂ) 2).isPreconnected
      (mem_closedBall_self (by norm_num)) hg0 (closedBall_subset_closedBall (by norm_num) hu)
  set Zr := {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 2 ∧ (riemannZeta (σ + T * I)).re = 0} with hZr
  set Zc := {u : ℂ | u ∈ closedBall (2 : ℂ) (3 / 2) ∧ gT T u = 0} with hZc
  have hZcfin : Zc.Finite := by
    have hD := (MeromorphicOn.divisor (gT T) (closedBall (2 : ℂ) (3 / 2))).finiteSupport
      (isCompact_closedBall _ _)
    refine hD.subset fun u ⟨hu, hgu⟩ => ?_
    rw [Function.mem_support, ATK.ArgPrincipio.divisor_eq_ordem
      (han.mono (closedBall_subset_closedBall (by norm_num))) hu (htop u hu)]
    have h0 : analyticOrderNatAt (gT T) u ≠ 0 := fun h =>
      ((ATK.ArgPrincipio.ordemNat_zero_iff (han u (closedBall_subset_closedBall (by norm_num) hu))
        (htop u hu)).mp h) hgu
    exact_mod_cast h0
  have hmap : ∀ σ ∈ Zr, (σ : ℂ) ∈ Zc := by
    intro σ hσ
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm]
      have e : (σ : ℂ) - 2 = ((σ - 2 : ℝ) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hσ.1.1, hσ.1.2]
    · rw [gT_real, hσ.2]
      simp
  have hZrfin : Zr.Finite := (hZcfin.preimage (Complex.ofReal_injective.injOn)).subset hmap
  set A := hZrfin.toFinset with hA
  refine ⟨A, fun σ hσ h0 => by rw [hA, Set.Finite.mem_toFinset]; exact ⟨hσ, h0⟩, ?_⟩
  set B := A.image (fun σ : ℝ => (σ : ℂ)) with hB
  have hBcard : B.card = A.card := Finset.card_image_of_injective _ Complex.ofReal_injective
  have hBmem : ∀ u ∈ B, u ∈ Zc := by
    intro u hu
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hu
    exact hmap σ ((Set.Finite.mem_toFinset _).mp hσ)
  have hsum := ATK.ZeroClasses.JensenLocal.soma_ordem_le (isCompact_closedBall (2 : ℂ) (3 / 2))
    (han.mono (closedBall_subset_closedBall (by norm_num))) B (fun u hu => (hBmem u hu).1)
    (fun u hu => htop u (hBmem u hu).1)
  have hone : (B.card : ℤ) ≤ ∑ w ∈ B, (analyticOrderNatAt (gT T) w : ℤ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_le_sum fun u hu => ?_
    have h0 : analyticOrderNatAt (gT T) u ≠ 0 := fun h =>
      ((ATK.ArgPrincipio.ordemNat_zero_iff (han u (closedBall_subset_closedBall (by norm_num)
        (hBmem u hu).1)) (htop u (hBmem u hu).1)).mp h) (hBmem u hu).2
    have : 1 ≤ analyticOrderNatAt (gT T) u := Nat.one_le_iff_ne_zero.mpr h0
    exact_mod_cast this
  have hbd : ∀ z ∈ sphere (2 : ℂ) |(7 / 4 : ℝ)|, ‖gT T z‖ ≤ 6 * T + 38 := by
    intro z hz
    rw [mem_sphere_iff_norm, abs_of_pos (by norm_num)] at hz
    exact cota_gT hT hz.le
  have J := AnalyticOnNhd.sum_divisor_le (r := 3 / 2) (by norm_num) (by norm_num) (by linarith) han' hg0 hbd
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at J
  have e : (7 / 4 : ℝ) / (3 / 2) = 7 / 6 := by norm_num
  rw [e] at J
  have hl : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hM : (6 * T + 38) / ‖gT T 2‖ ≤ (6 * T + 38) / (2 - π ^ 2 / 6) :=
    div_le_div_of_nonneg_left (by linarith) hb hg2
  have hlogM := Real.log_le_log (div_pos (by linarith) (lt_of_lt_of_le hb hg2)) hM
  have hcast : (A.card : ℝ) ≤ ((∑ᶠ u, MeromorphicOn.divisor (gT T) (closedBall (2 : ℂ) (3 / 2)) u : ℤ) : ℝ) := by
    rw [← hBcard]
    exact_mod_cast hone.trans hsum
  calc (A.card : ℝ) ≤ _ := hcast
    _ ≤ Real.log ((6 * T + 38) / ‖gT T 2‖) / Real.log (7 / 6) := J
    _ ≤ Real.log ((6 * T + 38) / (2 - π ^ 2 / 6)) / Real.log (7 / 6) :=
        div_le_div_of_nonneg_right hlogM hl.le

/-! ## 4. `S(T) = O(log T)` -/

/-- **`S(T) = O(log T)`**: existe `C` com `|Im ∫_{1/2}^{2} ζ′/ζ(σ + iT) dσ| ≤ C log T` para `T ≥ 4` sem zero de
`ζ` no segmento. -/
theorem variacao_log : ∃ C : ℝ, ∀ T : ℝ, 4 ≤ T →
    (∀ σ ∈ Icc (1 / 2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0) →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ C * Real.log T := by
  have hb := ATK.BLProva.dois_menos_pos
  set K := Real.log (16 / (2 - π ^ 2 / 6)) with hK
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hl76 : 0 < Real.log (7 / 6) := Real.log_pos (by norm_num)
  have hK0 : 0 ≤ K := by
    rw [hK]
    apply Real.log_nonneg
    rw [le_div_iff₀ hb]
    nlinarith [Real.pi_pos]
  refine ⟨π * ((K / Real.log 4 + 1) / Real.log (7 / 6) + 1 / Real.log 4), fun T hT hnz => ?_⟩
  have hT1 : 1 ≤ |T| := by rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨A, hA, hcard⟩ := conta_zeros_re hT
  have hv := variacao hT1 A.card (1 / 2) 2 (by norm_num) hnz A hA le_rfl
  have hlogT : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hTpos : 0 < T := by linarith
  -- log((6T + 38)/(2 − π²/6)) ≤ log T + K
  have hfrac : (6 * T + 38) / (2 - π ^ 2 / 6) ≤ T * (16 / (2 - π ^ 2 / 6)) := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hb]
    linarith
  have hlogf : Real.log ((6 * T + 38) / (2 - π ^ 2 / 6)) ≤ Real.log T + K := by
    calc Real.log ((6 * T + 38) / (2 - π ^ 2 / 6)) ≤ Real.log (T * (16 / (2 - π ^ 2 / 6))) :=
          Real.log_le_log (div_pos (by linarith) hb) hfrac
      _ = Real.log T + K := by rw [Real.log_mul hTpos.ne' (div_pos (by norm_num) hb).ne']
  have hKT : K ≤ K / Real.log 4 * Real.log T := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl4]
    exact mul_le_mul_of_nonneg_left hlogT hK0
  have hcard' : (A.card : ℝ) ≤ (K / Real.log 4 + 1) / Real.log (7 / 6) * Real.log T := by
    calc (A.card : ℝ) ≤ Real.log ((6 * T + 38) / (2 - π ^ 2 / 6)) / Real.log (7 / 6) := hcard
      _ ≤ (Real.log T + K) / Real.log (7 / 6) := div_le_div_of_nonneg_right hlogf hl76.le
      _ ≤ (K / Real.log 4 * Real.log T + Real.log T) / Real.log (7 / 6) :=
          div_le_div_of_nonneg_right (by linarith) hl76.le
      _ = (K / Real.log 4 + 1) / Real.log (7 / 6) * Real.log T := by ring
  have h1 : (1 : ℝ) ≤ 1 / Real.log 4 * Real.log T := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hl4]
    linarith
  calc |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ (A.card + 1) * π := hv
    _ ≤ ((K / Real.log 4 + 1) / Real.log (7 / 6) * Real.log T + 1 / Real.log 4 * Real.log T) * π := by
        gcongr
    _ = π * ((K / Real.log 4 + 1) / Real.log (7 / 6) + 1 / Real.log 4) * Real.log T := by ring

end ATK.ZeroClasses.VariacaoArg

#print axioms ATK.ZeroClasses.VariacaoArg.EM11
#print axioms ATK.ZeroClasses.VariacaoArg.poch1
#print axioms ATK.ZeroClasses.VariacaoArg.Cb1
#print axioms ATK.ZeroClasses.VariacaoArg.cota_zeta_quarto
#print axioms ATK.ZeroClasses.VariacaoArg.re_zeta_dois
#print axioms ATK.ZeroClasses.VariacaoArg.ne_um
#print axioms ATK.ZeroClasses.VariacaoArg.hasDerivAt_zeta_horiz
#print axioms ATK.ZeroClasses.VariacaoArg.continuous_zeta_horiz
#print axioms ATK.ZeroClasses.VariacaoArg.continuousOn_logDeriv_horiz
#print axioms ATK.ZeroClasses.VariacaoArg.integrable_logDeriv_horiz
#print axioms ATK.ZeroClasses.VariacaoArg.variacao_simples
#print axioms ATK.ZeroClasses.VariacaoArg.variacao
#print axioms ATK.ZeroClasses.VariacaoArg.gT_real
#print axioms ATK.ZeroClasses.VariacaoArg.gT_analitica
#print axioms ATK.ZeroClasses.VariacaoArg.cota_gT
#print axioms ATK.ZeroClasses.VariacaoArg.conta_zeros_re
#print axioms ATK.ZeroClasses.VariacaoArg.variacao_log
