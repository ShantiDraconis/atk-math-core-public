import ATK.ClosedMathToro
import ATK.EMGeral

/-!
# ATK — Redução terminal de HR a uma desigualdade de somas finitas

Formaliza, **sem assumir HR nem sua negação**, a cadeia de reduções proposta (T25–T31):

* `T25`: HR ⟺ `ζ` não se anula na metade direita `S₊ = {½ < Re s < 1}` (e o mesmo para `ξ`).
* `cobertura`: `S₊ = ⋃_{n ≥ 5} K_n`, `K_n = {½ + 1/n ≤ σ ≤ 1 − 1/n, |t| ≤ n}`, compactos.
* `rh_iff_minimos`: HR ⟺ para todo `n ≥ 5`, `|ζ|` tem cota inferior positiva em `K_n`
  (mínimo positivo, atingido por compacidade).
* `criterio_aproximacao` (T28): `|F − P| ≤ E < L ≤ |P|` em `K` ⇒ `F ≠ 0` em `K`.
* `T31_iff`: HR ⟺ existe, para cada `n`, um aproximante com `E_n < L_n` — o critério **é** HR.
* **Aproximante explícito** (independente de HR): a soma finita de Euler–Maclaurin `EM_{N,M}` com
  erro uniforme `|ζ − EM_{N,M}| ≤ E(n,N,M)` em todo `K_n`, e `E(n,N,M) → 0` quando `N → ∞`.
* `rh_iff_criterioEM`: **HR ⟺ ∀ n ≥ 5, ∃ N M L, L ≤ |EM_{N,M}| em `K_n` e `E(n,N,M) < L`.**

O último teorema mostra que provar a desigualdade universal para somas finitas é *exatamente*
provar HR: a redução não diminui a dificuldade. Cada instância com `n` fixo é uma conta finita;
o quantificador `∀ n` é o conteúdo da Hipótese de Riemann.
-/

open Complex Filter Topology Set

namespace ATK.ClosedMath.Terminal

open ATK.ZetaSimetria ATK.CEZ ATK.EMGeral

/-- Metade externa direita da faixa. -/
def Splus : Set ℂ := {s | 1 / 2 < s.re ∧ s.re < 1}

/-- **T25** — redução por simetria. -/
theorem T25 : RiemannHypothesis ↔ ∀ s ∈ Splus, riemannZeta s ≠ 0 := by
  rw [rh_iff_externa_vazia]
  constructor
  · intro h s hs hz
    have hm : s ∈ ZE := ⟨⟨hz, by linarith [hs.1], hs.2⟩, by linarith [hs.1]⟩
    rw [h] at hm
    exact hm
  · intro h
    ext s
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hz, h0, h1⟩, hne⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have ht := torcao_mem_Z (s := s) ⟨hz, h0, h1⟩
      exact h (torcao s) ⟨by rw [re_torcao]; linarith, by rw [re_torcao]; linarith⟩ ht.1
    · exact h s ⟨hgt, h1⟩ hz

/-- **T25 para `ξ`**. -/
theorem T25_xi : RiemannHypothesis ↔ ∀ s ∈ Splus, xi s ≠ 0 := by
  rw [T25]
  refine forall₂_congr fun s hs => ?_
  have h1 : s ≠ 1 := by rintro rfl; simp [Splus] at hs
  rw [Ne, Ne, xi_zero_iff (by linarith [hs.1]) h1]

/-- Compactos `K_n`. -/
def Kn (n : ℕ) : Set ℂ := {s | 1 / 2 + 1 / (n : ℝ) ≤ s.re ∧ s.re ≤ 1 - 1 / (n : ℝ) ∧ |s.im| ≤ n}

theorem Kn_sub {n : ℕ} (hn : 5 ≤ n) : Kn n ⊆ Splus := by
  intro s hs
  have : (0 : ℝ) < 1 / (n : ℝ) := by
    have : (5 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  exact ⟨by linarith [hs.1], by linarith [hs.2.1]⟩

theorem Kn_nonempty {n : ℕ} (hn : 5 ≤ n) : (Kn n).Nonempty := by
  have h5 : (5 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : 1 / (n : ℝ) ≤ 1 / 5 := one_div_le_one_div_of_le (by norm_num) h5
  have hre : (3 / 4 : ℂ).re = 3 / 4 := by norm_num
  have him : (3 / 4 : ℂ).im = 0 := by norm_num
  refine ⟨3 / 4, ?_, ?_, ?_⟩
  · show 1 / 2 + 1 / (n : ℝ) ≤ (3 / 4 : ℂ).re
    rw [hre]; linarith
  · show (3 / 4 : ℂ).re ≤ 1 - 1 / (n : ℝ)
    rw [hre]; linarith
  · show |(3 / 4 : ℂ).im| ≤ n
    rw [him, abs_zero]; linarith

theorem Kn_compacto (n : ℕ) : IsCompact (Kn n) := by
  apply Metric.isCompact_of_isClosed_isBounded
  · apply IsClosed.inter (isClosed_le continuous_const Complex.continuous_re)
    apply IsClosed.inter (isClosed_le Complex.continuous_re continuous_const)
    exact isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨|1 / 2 + 1 / (n : ℝ)| + |1 - 1 / (n : ℝ)| + n, fun s hs => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : |s.re| ≤ |1 / 2 + 1 / (n : ℝ)| + |1 - 1 / (n : ℝ)| := by
      rw [abs_le]
      constructor
      · have := hs.1; have := le_abs_self (1 / 2 + 1 / (n : ℝ)); have := abs_nonneg (1 - 1 / (n : ℝ))
        have := neg_abs_le (1 / 2 + 1 / (n : ℝ)); linarith
      · have := hs.2.1; have := le_abs_self (1 - 1 / (n : ℝ)); have := abs_nonneg (1 / 2 + 1 / (n : ℝ))
        linarith
    have := Complex.norm_le_abs_re_add_abs_im s
    linarith [hs.2.2]

/-- **Cobertura** `S₊ = ⋃_{n ≥ 5} K_n`. -/
theorem cobertura : Splus = ⋃ n ∈ {n : ℕ | 5 ≤ n}, Kn n := by
  ext s
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
  constructor
  · intro hs
    have a : 0 < s.re - 1 / 2 := by linarith [hs.1]
    have b : 0 < 1 - s.re := by linarith [hs.2]
    obtain ⟨n, hn⟩ := exists_nat_gt (max (max (1 / (s.re - 1 / 2)) (1 / (1 - s.re))) (max |s.im| 5))
    have hn5 : (5 : ℝ) < n := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hn
    have hnpos : (0 : ℝ) < n := by linarith
    have h1 : 1 / (s.re - 1 / 2) < n := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have h2 : 1 / (1 - s.re) < n := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have h3 : |s.im| < n := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    refine ⟨n, by exact_mod_cast hn5.le, ?_, ?_, h3.le⟩
    · have : 1 / (n : ℝ) < s.re - 1 / 2 := by
        rw [div_lt_iff₀ hnpos]; rw [div_lt_iff₀ a] at h1; linarith
      linarith
    · have : 1 / (n : ℝ) < 1 - s.re := by
        rw [div_lt_iff₀ hnpos]; rw [div_lt_iff₀ b] at h2; linarith
      linarith
  · rintro ⟨n, hn, hs⟩
    exact Kn_sub hn hs

theorem zeta_continua_Kn {n : ℕ} (hn : 5 ≤ n) : ContinuousOn riemannZeta (Kn n) := by
  intro s hs
  have h1 : s ≠ 1 := by
    rintro rfl
    have := (Kn_sub hn hs).2
    simp at this
  exact (differentiableAt_riemannZeta h1).continuousAt.continuousWithinAt

/-- **HR ⟺ mínimos positivos**: `|ζ|` tem cota inferior positiva em cada `K_n`. -/
theorem rh_iff_minimos : RiemannHypothesis ↔
    ∀ n : ℕ, 5 ≤ n → ∃ m > 0, ∀ s ∈ Kn n, m ≤ ‖riemannZeta s‖ := by
  rw [T25]
  constructor
  · intro h n hn
    obtain ⟨s₀, hs₀, hmin⟩ := (Kn_compacto n).exists_isMinOn (Kn_nonempty hn)
      ((zeta_continua_Kn hn).norm)
    exact ⟨‖riemannZeta s₀‖, norm_pos_iff.mpr (h s₀ (Kn_sub hn hs₀)), fun s hs => hmin hs⟩
  · intro h s hs hz
    rw [cobertura] at hs
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hs
    obtain ⟨n, hn, hsn⟩ := hs
    obtain ⟨m, hm, hb⟩ := h n hn
    have := hb s hsn
    rw [hz, norm_zero] at this
    linarith

/-- **T28** — critério de aproximação (desigualdade triangular inversa). -/
theorem criterio_aproximacao {F P : ℂ → ℂ} {K : Set ℂ} {E L : ℝ}
    (hE : ∀ s ∈ K, ‖F s - P s‖ ≤ E) (hL : ∀ s ∈ K, L ≤ ‖P s‖) (hEL : E < L) :
    ∀ s ∈ K, F s ≠ 0 := by
  intro s hs hz
  have h1 := hE s hs
  have h2 := hL s hs
  rw [hz, zero_sub, norm_neg] at h1
  linarith

/-- O critério terminal com aproximantes arbitrários. -/
def Criterio : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∃ (P : ℂ → ℂ) (E L : ℝ), (∀ s ∈ Kn n, ‖riemannZeta s - P s‖ ≤ E) ∧
    (∀ s ∈ Kn n, L ≤ ‖P s‖) ∧ E < L

/-- **T31** — o critério implica HR … -/
theorem T31 (h : Criterio) : RiemannHypothesis := by
  rw [rh_iff_minimos]
  intro n hn
  obtain ⟨P, E, L, hE, hL, hEL⟩ := h n hn
  refine ⟨L - E, by linarith, fun s hs => ?_⟩
  have h1 := hE s hs
  have h2 := hL s hs
  have := norm_sub_norm_le (P s) (P s - riemannZeta s)
  rw [sub_sub_cancel, norm_sub_rev] at this
  linarith

/-- … e é **equivalente** a HR: provar o critério é provar HR. -/
theorem T31_iff : RiemannHypothesis ↔ Criterio := by
  refine ⟨fun h n hn => ?_, T31⟩
  obtain ⟨m, hm, hb⟩ := rh_iff_minimos.mp h n hn
  exact ⟨riemannZeta, 0, m, fun s _ => by simp, hb, hm⟩

/-! ### Aproximante explícito por somas finitas (Euler–Maclaurin) -/

theorem norm_poch_le (s : ℂ) (m : ℕ) : ‖poch s m‖ ≤ (‖s‖ + m) ^ m := by
  induction m with
  | zero => simp [poch]
  | succ k ih =>
    simp only [poch, norm_mul]
    have h1 : ‖s + k‖ ≤ ‖s‖ + k := by
      have := norm_add_le s (k : ℂ); rwa [Complex.norm_natCast] at this
    have h2 : (‖s‖ + k) ^ k ≤ (‖s‖ + (k + 1 : ℕ)) ^ k := by
      apply pow_le_pow_left₀ (by positivity); push_cast; linarith
    have h3 : ‖s‖ + k ≤ ‖s‖ + (k + 1 : ℕ) := by push_cast; linarith
    calc ‖poch s k‖ * ‖s + k‖ ≤ (‖s‖ + k) ^ k * (‖s‖ + k) :=
          mul_le_mul ih h1 (norm_nonneg _) (by positivity)
      _ ≤ (‖s‖ + (k + 1 : ℕ)) ^ k * (‖s‖ + (k + 1 : ℕ)) :=
          mul_le_mul h2 h3 (by positivity) (by positivity)
      _ = (‖s‖ + (k + 1 : ℕ)) ^ (k + 1) := by ring

theorem Cb_nonneg (k : ℕ) : 0 ≤ Cb k := by
  unfold Cb
  exact Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)

/-- Cota uniforme do erro em `K_n`. -/
noncomputable def Eb (n N M : ℕ) : ℝ :=
  (Real.sqrt (1 + (n : ℝ) ^ 2) + M) ^ M / (M.factorial : ℝ) *
    (Cb M * (N : ℝ) ^ ((1 : ℝ) / 2 - M) / ((M : ℝ) - 1 / 2))

theorem norm_le_Kn {n : ℕ} (hn : 5 ≤ n) {s : ℂ} (hs : s ∈ Kn n) :
    ‖s‖ ≤ Real.sqrt (1 + (n : ℝ) ^ 2) := by
  have hre : |s.re| ≤ 1 := by
    have := Kn_sub hn hs
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have him : |s.im| ≤ n := hs.2.2
  rw [← Real.sqrt_sq (norm_nonneg s), Complex.sq_norm, Complex.normSq_apply]
  apply Real.sqrt_le_sqrt
  have a : s.re * s.re ≤ 1 := by
    have := abs_mul_abs_self s.re
    nlinarith [abs_nonneg s.re]
  have b : s.im * s.im ≤ (n : ℝ) ^ 2 := by
    have := abs_mul_abs_self s.im
    nlinarith [abs_nonneg s.im]
  linarith

/-- **Aproximação uniforme independente de HR**: `|ζ − EM_{N,M}| ≤ E(n,N,M)` em todo `K_n`. -/
theorem EM_uniforme {n N M : ℕ} (hn : 5 ≤ n) (hN : 1 ≤ N) (hM : 1 ≤ M) :
    ∀ s ∈ Kn n, ‖riemannZeta s - EM N M s‖ ≤ Eb n N M := by
  intro s hs
  have hS := Kn_sub hn hs
  have hσ : (1 : ℝ) / 2 < s.re := hS.1
  have hs1 : s ≠ 1 := by rintro rfl; have := hS.2; simp at this
  refine le_trans (norm_zeta_sub_EM_le (by linarith) hs1 hN hM) ?_
  unfold Eb
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hf : (0 : ℝ) < M.factorial := by exact_mod_cast Nat.factorial_pos M
  have hp : ‖poch s M‖ / (M.factorial : ℝ) ≤
      (Real.sqrt (1 + (n : ℝ) ^ 2) + M) ^ M / (M.factorial : ℝ) := by
    apply div_le_div_of_nonneg_right _ hf.le
    refine le_trans (norm_poch_le s M) (pow_le_pow_left₀ (by positivity) ?_ M)
    linarith [norm_le_Kn hn hs]
  have hpow : (N : ℝ) ^ (1 - s.re - M) ≤ (N : ℝ) ^ ((1 : ℝ) / 2 - M) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  have hden : (M : ℝ) - 1 / 2 ≤ s.re + M - 1 := by linarith
  have hden0 : (0 : ℝ) < (M : ℝ) - 1 / 2 := by linarith
  have hq : Cb M * (N : ℝ) ^ (1 - s.re - M) / (s.re + M - 1) ≤
      Cb M * (N : ℝ) ^ ((1 : ℝ) / 2 - M) / ((M : ℝ) - 1 / 2) := by
    apply div_le_div₀ (mul_nonneg (Cb_nonneg M) (by positivity)) _ hden0 hden
    exact mul_le_mul_of_nonneg_left hpow (Cb_nonneg M)
  exact mul_le_mul hp hq (div_nonneg (mul_nonneg (Cb_nonneg M) (by positivity)) (by linarith))
    (by positivity)

/-- `E(n,N,M) → 0` quando `N → ∞` (`n`, `M ≥ 1` fixos). -/
theorem Eb_tende_zero (n M : ℕ) (hM : 1 ≤ M) : Tendsto (fun N : ℕ => Eb n N M) atTop (𝓝 0) := by
  unfold Eb
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h : Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2 - M)) atTop (𝓝 0) := by
    have e : (1 : ℝ) / 2 - M = -((M : ℝ) - 1 / 2) := by ring
    rw [e]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have := ((h.const_mul (Cb M)).div_const ((M : ℝ) - 1 / 2)).const_mul
    ((Real.sqrt (1 + (n : ℝ) ^ 2) + M) ^ M / (M.factorial : ℝ))
  simpa using this

/-- Critério com o aproximante **explícito** de somas finitas. -/
def CriterioEM : Prop :=
  ∀ n : ℕ, 5 ≤ n → ∃ N M : ℕ, 1 ≤ N ∧ 1 ≤ M ∧ ∃ L : ℝ,
    (∀ s ∈ Kn n, L ≤ ‖EM N M s‖) ∧ Eb n N M < L

/-- **HR ⟺ critério de somas finitas**. Cada instância (`n` fixo) é uma conta finita; o `∀ n` é HR. -/
theorem rh_iff_criterioEM : RiemannHypothesis ↔ CriterioEM := by
  constructor
  · intro h n hn
    obtain ⟨m, hm, hb⟩ := rh_iff_minimos.mp h n hn
    have ev := (Eb_tende_zero n 1 le_rfl).eventually (gt_mem_nhds (half_pos hm))
    obtain ⟨N, hN⟩ := (ev.and (eventually_ge_atTop 1)).exists
    refine ⟨N, 1, hN.2, le_rfl, m / 2, fun s hs => ?_, hN.1⟩
    have e := EM_uniforme hn hN.2 le_rfl s hs
    have t := norm_sub_norm_le (riemannZeta s) (riemannZeta s - EM N 1 s)
    rw [sub_sub_cancel] at t
    have := hb s hs
    linarith [hN.1]
  · intro h
    apply T31
    intro n hn
    obtain ⟨N, M, hN, hM, L, hL, hEL⟩ := h n hn
    exact ⟨EM N M, Eb n N M, L, EM_uniforme hn hN hM, hL, hEL⟩

/-! ### O parâmetro terminal `δ_n = min_{K_n} |η|` -/

/-- Função eta de Dirichlet, `η(s) = (1 − 2^{1−s}) ζ(s)`. -/
noncomputable def eta (s : ℂ) : ℂ := (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

/-- `1 − 2^{1−s} ≠ 0` para `Re s < 1` (pois `|2^{1−s}| = 2^{1−σ} > 1`). -/
theorem fator_eta_ne {s : ℂ} (h : s.re < 1) : 1 - (2 : ℂ) ^ (1 - s) ≠ 0 := by
  intro h0
  have h1 : (2 : ℂ) ^ (1 - s) = 1 := by linear_combination -h0
  have hn := Complex.norm_cpow_eq_rpow_re_of_pos (x := 2) (by norm_num) (1 - s)
  push_cast at hn
  rw [h1, norm_one] at hn
  have : (1 : ℝ) < 2 ^ (1 - s).re := Real.one_lt_rpow (by norm_num) (by simp; linarith)
  linarith

/-- Em `K_n`, `η = 0 ⟺ ζ = 0` (mesmos zeros, mesmas multiplicidades). -/
theorem eta_zero_iff {n : ℕ} (hn : 5 ≤ n) {s : ℂ} (hs : s ∈ Kn n) : eta s = 0 ↔ riemannZeta s = 0 := by
  unfold eta
  rw [mul_eq_zero, or_iff_right (fator_eta_ne (Kn_sub hn hs).2)]

theorem eta_continua_Kn {n : ℕ} (hn : 5 ≤ n) : ContinuousOn eta (Kn n) := by
  intro s hs
  have h1 : s ≠ 1 := by
    rintro rfl
    have := (Kn_sub hn hs).2
    simp at this
  have hc : ContinuousAt (fun s : ℂ => (2 : ℂ) ^ (1 - s)) s :=
    (continuousAt_const.sub continuousAt_id).const_cpow (Or.inl two_ne_zero)
  exact ((continuousAt_const.sub hc).mul
    (differentiableAt_riemannZeta h1).continuousAt).continuousWithinAt

/-- **O parâmetro** `δ_n = min_{s ∈ K_n} |η(s)|`. -/
noncomputable def delta (n : ℕ) : ℝ := sInf ((fun s => ‖eta s‖) '' Kn n)

/-- O mínimo é atingido: `δ_n = |η(s₀)|` para algum `s₀ ∈ K_n`, e `δ_n ≤ |η(s)|` em `K_n`. -/
theorem delta_atingido {n : ℕ} (hn : 5 ≤ n) :
    (∃ s₀ ∈ Kn n, delta n = ‖eta s₀‖) ∧ ∀ s ∈ Kn n, delta n ≤ ‖eta s‖ := by
  have hK : IsCompact ((fun s => ‖eta s‖) '' Kn n) :=
    (Kn_compacto n).image_of_continuousOn (eta_continua_Kn hn).norm
  have hne : ((fun s => ‖eta s‖) '' Kn n).Nonempty := (Kn_nonempty hn).image _
  refine ⟨?_, fun s hs => csInf_le ⟨0, ?_⟩ ⟨s, hs, rfl⟩⟩
  · obtain ⟨s₀, hs₀, he⟩ := hK.sInf_mem hne
    exact ⟨s₀, hs₀, he.symm⟩
  · rintro _ ⟨t, -, rfl⟩
    exact norm_nonneg _

/-- **HR ⟺ ∀ n ≥ 5, δ_n > 0** (com `δ_n = min_{K_n} |η|`): o parâmetro proposto é exatamente HR. -/
theorem rh_iff_delta : RiemannHypothesis ↔ ∀ n : ℕ, 5 ≤ n → 0 < delta n := by
  rw [T25]
  constructor
  · intro h n hn
    obtain ⟨⟨s₀, hs₀, he⟩, -⟩ := delta_atingido hn
    rw [he, norm_pos_iff, Ne, eta_zero_iff hn hs₀]
    exact h s₀ (Kn_sub hn hs₀)
  · intro h s hs hz
    rw [cobertura] at hs
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hs
    obtain ⟨n, hn, hsn⟩ := hs
    have h1 := (delta_atingido hn).2 s hsn
    rw [(eta_zero_iff hn hsn).mpr hz, norm_zero] at h1
    linarith [h n hn]

end ATK.ClosedMath.Terminal

-- Auditoria de axiomas (kernel): cada teorema deve depender só de propext, Classical.choice, Quot.sound.
#print axioms ATK.ClosedMath.Terminal.T25
#print axioms ATK.ClosedMath.Terminal.T25_xi
#print axioms ATK.ClosedMath.Terminal.Kn_sub
#print axioms ATK.ClosedMath.Terminal.Kn_nonempty
#print axioms ATK.ClosedMath.Terminal.Kn_compacto
#print axioms ATK.ClosedMath.Terminal.cobertura
#print axioms ATK.ClosedMath.Terminal.zeta_continua_Kn
#print axioms ATK.ClosedMath.Terminal.rh_iff_minimos
#print axioms ATK.ClosedMath.Terminal.criterio_aproximacao
#print axioms ATK.ClosedMath.Terminal.T31
#print axioms ATK.ClosedMath.Terminal.T31_iff
#print axioms ATK.ClosedMath.Terminal.norm_poch_le
#print axioms ATK.ClosedMath.Terminal.Cb_nonneg
#print axioms ATK.ClosedMath.Terminal.norm_le_Kn
#print axioms ATK.ClosedMath.Terminal.EM_uniforme
#print axioms ATK.ClosedMath.Terminal.Eb_tende_zero
#print axioms ATK.ClosedMath.Terminal.rh_iff_criterioEM
#print axioms ATK.ClosedMath.Terminal.fator_eta_ne
#print axioms ATK.ClosedMath.Terminal.eta_zero_iff
#print axioms ATK.ClosedMath.Terminal.eta_continua_Kn
#print axioms ATK.ClosedMath.Terminal.delta_atingido
#print axioms ATK.ClosedMath.Terminal.rh_iff_delta
