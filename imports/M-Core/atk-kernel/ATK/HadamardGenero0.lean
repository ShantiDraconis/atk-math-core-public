import ATK.InteiraAnalitica

/-!
# ATK — Fatoração de Hadamard de gênero 0 (zeros reais negativos) e a volta de Edrei

**Teorema (`hadamard_tn`)**: seja `F(z) = Σcₙzⁿ` inteira com `c₀ > 0`, de crescimento de ordem `σ < 1`
(`|F(w)| ≤ A·exp(A|w|^σ)`), e com todos os zeros reais negativos. Então `F = c₀∏(1 + αⱼz)` com `αⱼ ≥ 0`,
`Σαⱼ < ∞` (coeficiente a coeficiente, `coef_eq_lim`), e a matriz de Toeplitz `T(c)` é totalmente não
negativa. Com `ATK.Edrei.edrei_inteira`: **para ordem `< 1`, `T(c)` TN ⟺ zeros reais negativos**
(`tn_iff_zeros`).

Construção (`seqH`, `alphaH`): a cada passo tira-se um zero de módulo mínimo `−1/αₖ` (`passo`, via
`ATK.Edrei.divLin`), de modo que `F = ∏_{j<k}(1 + αⱼz)·Gₖ` e os `αₖ` decrescem.

* **Contagem** (`contagem`): pelo módulo máximo em `|w| = 3/αₖ`, `2^{k+1}c₀ ≤ A·exp(A(3/αₖ)^σ)`; daí
  `Σαⱼ^s < ∞` para `σ < s` (`summable_alpha_rpow`).
* **Gₖ → c₀** (`coef_seqH_tendsto`): `log|Gₖ|` é harmônica no disco sem zeros; pela fórmula de Poisson e
  pelo valor médio, `log|Gₖ(w)| ≤ log c₀ + (2|w|/(r−|w|))·média|log|Gₖ||`, e a média é controlada pelo
  crescimento de `F` e pela fórmula de Jensen para o polinômio `∏(1 + αⱼz)`; Borel–Carathéodory e a
  desigualdade de Cauchy dão `Gₖ` coeficiente a coeficiente → `c₀`.
-/

open Complex Filter Topology Metric Set
open scoped Nat

namespace ATK.Hadamard

open ATK.Edrei ATK.InteiraAn
open ATK.ToeplitzTN (toep)

/-! ## 1. A construção -/

/-- Todo zero de `ev c` é real e negativo. -/
def ZerosNeg (c : ℕ → ℝ) : Prop := ∀ w : ℂ, ev c w = 0 → w.im = 0 ∧ w.re < 0

/-- `w` é um zero de módulo mínimo de `ev c`. -/
def ZeroMin (c : ℕ → ℝ) (w : ℂ) : Prop := ev c w = 0 ∧ ∀ v, ev c v = 0 → ‖w‖ ≤ ‖v‖

open Classical in
/-- Um passo: tira um zero de módulo mínimo `−ρ`, devolvendo `(F/(1 + z/ρ), 1/ρ)`; sem zeros, `(F, 0)`. -/
noncomputable def passo (c : ℕ → ℝ) : (ℕ → ℝ) × ℝ :=
  if h : ∃ w, ZeroMin c w then (divLin c (‖h.choose‖)⁻¹, (‖h.choose‖)⁻¹) else (c, 0)

noncomputable def seqH (c : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => c
  | k + 1 => (passo (seqH c k)).1

noncomputable def alphaH (c : ℕ → ℝ) (k : ℕ) : ℝ := (passo (seqH c k)).2

/-- Uma sequência "boa": inteira, valor `c₀` em `0` e só zeros reais negativos. -/
structure Boa (c0 : ℝ) (G : ℕ → ℝ) : Prop where
  inteira : Inteira G
  zero : G 0 = c0
  zeros : ZerosNeg G

theorem ev_ofReal (c : ℕ → ℝ) {y : ℝ} (hs : Summable fun j => c j * y ^ j) :
    ev c (y : ℂ) = ((∑' j, c j * y ^ j : ℝ) : ℂ) := by
  unfold ev
  rw [Complex.ofReal_tsum]
  congr 1
  funext j
  push_cast
  ring

theorem passo_spec {c0 : ℝ} (hc0 : 0 < c0) {G : ℕ → ℝ} (hG : Boa c0 G) :
    Boa c0 (passo G).1 ∧ 0 ≤ (passo G).2 ∧
    (∀ m, G (m + 1) = (passo G).1 (m + 1) + (passo G).2 * (passo G).1 m) ∧ G 0 = (passo G).1 0 ∧
    (∀ z, ev G z = (1 + ((passo G).2 : ℂ) * z) * ev (passo G).1 z) ∧
    ((passo G).2 = 0 → ∀ w, ev G w ≠ 0) ∧
    (0 < (passo G).2 → ∀ v, ev G v = 0 → ((passo G).2)⁻¹ ≤ ‖v‖) ∧
    (0 < (passo G).2 → ∃ v, ev G v = 0 ∧ ‖v‖ = ((passo G).2)⁻¹) := by
  classical
  have hG0 : G 0 ≠ 0 := by rw [hG.zero]; exact hc0.ne'
  unfold passo
  split_ifs with h
  · set w := h.choose with hwdef
    have hw : ZeroMin G w := h.choose_spec
    obtain ⟨hwim, hwre⟩ := hG.zeros w hw.1
    have hwne : w ≠ 0 := fun h0 => by rw [h0] at hwre; simp at hwre
    have hρ : 0 < ‖w‖ := norm_pos_iff.mpr hwne
    set L : ℝ := ‖w‖⁻¹ with hL
    have hLpos : 0 < L := inv_pos.mpr hρ
    have hwreal : w = ((-L⁻¹ : ℝ) : ℂ) := by
      apply Complex.ext
      · have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [hwim])
        have hn : ‖w‖ = |w.re| := by rw [hw', Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
        simp only [Complex.ofReal_re, hL, inv_inv]
        rw [hn, abs_of_neg hwre]
        ring
      · simp [hwim]
    have hsy : Summable fun j => G j * (-L⁻¹) ^ j := by
      refine Summable.of_norm ((hG.inteira L⁻¹ (inv_nonneg.mpr hLpos.le)).congr fun j => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_of_pos (inv_pos.mpr hLpos)]
    have hroot : ∑' j, G j * (-L⁻¹) ^ j = 0 := by
      have h1 := hw.1
      rw [hwreal, ev_ofReal G hsy] at h1
      exact_mod_cast h1
    have hd := inteira_divLin hG.inteira hLpos hroot
    have hev : ∀ z, ev G z = (1 + (L : ℂ) * z) * ev (divLin G L) z := ev_divLin hG.inteira hd
    refine ⟨⟨hd, by simp [divLin, hG.zero], fun v hv => hG.zeros v ?_⟩, hLpos.le, fun m => ?_,
      by simp [divLin], hev, fun h0 => absurd h0 hLpos.ne', fun _ v hv => ?_, fun _ => ⟨w, hw.1, ?_⟩⟩
    · rw [hev v, hv, mul_zero]
    · simp only [divLin]
      ring
    · rw [hL, inv_inv]
      exact hw.2 v hv
    · rw [hL, inv_inv]
  · refine ⟨hG, le_rfl, fun m => by ring, rfl, fun z => by simp, fun _ w hw => ?_,
      fun h0 => absurd h0 (lt_irrefl 0), fun h0 => absurd h0 (lt_irrefl 0)⟩
    exact h (existe_zero_min hG.inteira hG0 hw)

theorem seqH_boa {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) : ∀ k, Boa c0 (seqH c k)
  | 0 => hc
  | k + 1 => (passo_spec hc0 (seqH_boa hc0 hc k)).1

theorem alphaH_nonneg {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) (k : ℕ) :
    0 ≤ alphaH c k := (passo_spec hc0 (seqH_boa hc0 hc k)).2.1

theorem seqH_succ_coef {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) (k m : ℕ) :
    seqH c k (m + 1) = seqH c (k + 1) (m + 1) + alphaH c k * seqH c (k + 1) m :=
  (passo_spec hc0 (seqH_boa hc0 hc k)).2.2.1 m

theorem seqH_succ_zero {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) (k : ℕ) :
    seqH c k 0 = seqH c (k + 1) 0 :=
  (passo_spec hc0 (seqH_boa hc0 hc k)).2.2.2.1

theorem ev_seqH_succ {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) (k : ℕ) (z : ℂ) :
    ev (seqH c k) z = (1 + (alphaH c k : ℂ) * z) * ev (seqH c (k + 1)) z :=
  (passo_spec hc0 (seqH_boa hc0 hc k)).2.2.2.2.1 z

theorem alphaH_zero_free {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) (k : ℕ)
    (h : alphaH c k = 0) : ∀ w, ev (seqH c k) w ≠ 0 :=
  (passo_spec hc0 (seqH_boa hc0 hc k)).2.2.2.2.2.1 h

theorem alphaH_min {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) (k : ℕ)
    (h : 0 < alphaH c k) : ∀ v, ev (seqH c k) v = 0 → (alphaH c k)⁻¹ ≤ ‖v‖ :=
  (passo_spec hc0 (seqH_boa hc0 hc k)).2.2.2.2.2.2.1 h

theorem alphaH_exists {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) (k : ℕ)
    (h : 0 < alphaH c k) : ∃ v, ev (seqH c k) v = 0 ∧ ‖v‖ = (alphaH c k)⁻¹ :=
  (passo_spec hc0 (seqH_boa hc0 hc k)).2.2.2.2.2.2.2 h

/-- Os `αₖ` decrescem (zeros tirados em ordem crescente de módulo). -/
theorem alphaH_succ_le {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) (k : ℕ) :
    alphaH c (k + 1) ≤ alphaH c k := by
  rcases (alphaH_nonneg hc0 hc (k + 1)).lt_or_eq with hpos | h0
  · obtain ⟨v, hv, hvn⟩ := alphaH_exists hc0 hc (k + 1) hpos
    have hvk : ev (seqH c k) v = 0 := by rw [ev_seqH_succ hc0 hc k v, hv, mul_zero]
    rcases (alphaH_nonneg hc0 hc k).lt_or_eq with hk | hk0
    · have := alphaH_min hc0 hc k hk v hvk
      rw [hvn] at this
      exact (inv_le_inv₀ hk hpos).mp this
    · exact absurd hvk (alphaH_zero_free hc0 hc k hk0.symm v)
  · rw [← h0]
    exact alphaH_nonneg hc0 hc k

theorem alphaH_antitone {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) :
    Antitone (alphaH c) := antitone_nat_of_succ_le (alphaH_succ_le hc0 hc)

/-- `F(z) = ∏_{j<k}(1 + αⱼz)·Gₖ(z)`. -/
theorem ev_seqH {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) (z : ℂ) :
    ∀ k, ev c z = (∏ j ∈ Finset.range k, (1 + (alphaH c j : ℂ) * z)) * ev (seqH c k) z
  | 0 => by simp [seqH]
  | k + 1 => by
    rw [ev_seqH hc0 hc z k, ev_seqH_succ hc0 hc k z, Finset.prod_range_succ]
    ring
termination_by k => k

/-- Coeficientes: `F = ∏_{j<k}(1 + αⱼz)·Gₖ` como séries formais. -/
theorem mk_seqH {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) : ∀ k,
    PowerSeries.mk c = PowerSeries.mk (prodCoef 1 (alphaH c) k) * PowerSeries.mk (seqH c k)
  | 0 => by
    have : PowerSeries.mk (prodCoef 1 (alphaH c) 0) = 1 := by
      ext n
      simp [prodCoef, PowerSeries.coeff_one]
    rw [this, one_mul]
    rfl
  | k + 1 => by
    have h1 : PowerSeries.mk (seqH c k) =
        (1 + PowerSeries.C (alphaH c k) * PowerSeries.X) * PowerSeries.mk (seqH c (k + 1)) := by
      ext n
      rw [add_mul, one_mul, mul_assoc, map_add, PowerSeries.coeff_C_mul]
      cases n with
      | zero =>
        simp [PowerSeries.coeff_zero_X_mul, seqH_succ_zero hc0 hc k]
      | succ m =>
        rw [PowerSeries.coeff_succ_X_mul]
        simp only [PowerSeries.coeff_mk]
        exact seqH_succ_coef hc0 hc k m
    have h2 : PowerSeries.mk (prodCoef 1 (alphaH c) (k + 1)) =
        PowerSeries.mk (prodCoef 1 (alphaH c) k) *
          (1 + PowerSeries.C (alphaH c k) * PowerSeries.X) := by
      ext n
      rw [mul_add, mul_one, map_add, mul_comm (PowerSeries.C (alphaH c k)), ← mul_assoc,
        PowerSeries.coeff_mul_C]
      cases n with
      | zero =>
        simp [prodCoef, PowerSeries.coeff_zero_mul_X]
      | succ m =>
        rw [PowerSeries.coeff_succ_mul_X]
        simp only [PowerSeries.coeff_mk, prodCoef, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        ring
    rw [mk_seqH hc0 hc k, h1, h2]
    ring
termination_by k => k

theorem coef_seqH {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) (k n : ℕ) :
    c n = ∑ i ∈ Finset.range (n + 1), prodCoef 1 (alphaH c) k i * seqH c k (n - i) := by
  have h := congrArg (PowerSeries.coeff n) (mk_seqH hc0 hc k)
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => PowerSeries.coeff i (PowerSeries.mk (prodCoef 1 (alphaH c) k)) *
      PowerSeries.coeff j (PowerSeries.mk (seqH c k)))] at h
  simpa only [PowerSeries.coeff_mk] using h

/-! ## 2. Contagem de zeros (módulo máximo) e somabilidade dos `αⱼ` -/

theorem norm_one_add_ge {α : ℝ} (hα : 0 ≤ α) (w : ℂ) : α * ‖w‖ - 1 ≤ ‖1 + (α : ℂ) * w‖ := by
  have h1 : ‖(α : ℂ) * w‖ = α * ‖w‖ := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hα]
  have h2 : ‖(α : ℂ) * w‖ ≤ ‖1 + (α : ℂ) * w‖ + ‖(1 : ℂ)‖ := by
    have := norm_sub_le (1 + (α : ℂ) * w) 1
    simpa using this
  rw [norm_one] at h2
  linarith

theorem norm_one_add_le {α : ℝ} (hα : 0 ≤ α) (w : ℂ) : ‖1 + (α : ℂ) * w‖ ≤ 1 + α * ‖w‖ := by
  calc ‖1 + (α : ℂ) * w‖ ≤ ‖(1 : ℂ)‖ + ‖(α : ℂ) * w‖ := norm_add_le _ _
    _ = 1 + α * ‖w‖ := by rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hα]

/-- **Contagem**: se `αₖ > 0`, pelo módulo máximo de `G_{k+1}` em `|w| = 3/αₖ`,
`2^{k+1}·c₀ ≤ A·exp(A·(3/αₖ)^σ)`. -/
theorem contagem {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) {A σ : ℝ}
    (hgr : ∀ w, ‖ev c w‖ ≤ A * Real.exp (A * ‖w‖ ^ σ)) {k : ℕ} (hk : 0 < alphaH c k) :
    2 ^ (k + 1) * c0 ≤ A * Real.exp (A * (3 * (alphaH c k)⁻¹) ^ σ) := by
  set R := 3 * (alphaH c k)⁻¹ with hR
  have hRpos : 0 < R := by positivity
  have hGd : Differentiable ℂ (ev (seqH c (k + 1))) :=
    ev_differentiable (seqH_boa hc0 hc (k + 1)).inteira
  have hfac : ∀ w ∈ sphere (0 : ℂ) R, ∀ j ∈ Finset.range (k + 1),
      (2 : ℝ) ≤ ‖1 + (alphaH c j : ℂ) * w‖ := by
    intro w hw j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hαj : alphaH c k ≤ alphaH c j := alphaH_antitone hc0 hc hjk
    have hnw : ‖w‖ = R := mem_sphere_zero_iff_norm.mp hw
    have h1 := norm_one_add_ge (alphaH_nonneg hc0 hc j) w
    rw [hnw] at h1
    have h3 : 3 ≤ alphaH c j * R := by
      rw [hR, ← mul_assoc, mul_comm (alphaH c j) 3, mul_assoc]
      have : 1 ≤ alphaH c j * (alphaH c k)⁻¹ := by
        rw [← div_eq_mul_inv, one_le_div hk]
        exact hαj
      linarith
    linarith
  have hP : ∀ w ∈ sphere (0 : ℂ) R,
      (2 : ℝ) ^ (k + 1) ≤ ‖∏ j ∈ Finset.range (k + 1), (1 + (alphaH c j : ℂ) * w)‖ := by
    intro w hw
    rw [norm_prod]
    calc (2 : ℝ) ^ (k + 1) = ∏ _j ∈ Finset.range (k + 1), (2 : ℝ) := by simp
      _ ≤ ∏ j ∈ Finset.range (k + 1), ‖1 + (alphaH c j : ℂ) * w‖ :=
        Finset.prod_le_prod₀ (fun _ _ => by norm_num) (hfac w hw)
  have hbound : ∀ w ∈ sphere (0 : ℂ) R,
      ‖ev (seqH c (k + 1)) w‖ ≤ A * Real.exp (A * R ^ σ) / 2 ^ (k + 1) := by
    intro w hw
    have h1 := ev_seqH hc0 hc w (k + 1)
    have hPw := hP w hw
    rw [le_div_iff₀ (by positivity)]
    calc ‖ev (seqH c (k + 1)) w‖ * 2 ^ (k + 1)
        ≤ ‖ev (seqH c (k + 1)) w‖ *
            ‖∏ j ∈ Finset.range (k + 1), (1 + (alphaH c j : ℂ) * w)‖ :=
          mul_le_mul_of_nonneg_left hPw (norm_nonneg _)
      _ = ‖ev c w‖ := by rw [h1, norm_mul, mul_comm]
      _ ≤ A * Real.exp (A * ‖w‖ ^ σ) := hgr w
      _ = A * Real.exp (A * R ^ σ) := by rw [mem_sphere_zero_iff_norm.mp hw]
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) R)
    isBounded_ball hGd.diffContOnCl
    (fun z hz => hbound z (by rwa [frontier_ball (0 : ℂ) hRpos.ne'] at hz))
    (subset_closure (mem_ball_self hRpos))
  have h0 : ev (seqH c (k + 1)) 0 = (c0 : ℂ) := by
    rw [ev_zero, (seqH_boa hc0 hc (k + 1)).zero]
  rw [h0, Complex.norm_real, Real.norm_of_nonneg hc0.le, le_div_iff₀ (by positivity)] at hmax
  linarith

/-- Dos `contagem`: `αₖ^σ ≤ D/(k+1)` a partir de algum `N`. -/
theorem alpha_rpow_le {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) {A σ : ℝ} (hA : 0 < A)
    (hσ : 0 < σ) (hgr : ∀ w, ‖ev c w‖ ≤ A * Real.exp (A * ‖w‖ ^ σ)) :
    ∃ D > 0, ∃ N : ℕ, ∀ k ≥ N, alphaH c k ^ σ ≤ D / (k + 1) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set D := 2 * (A * 3 ^ σ) / Real.log 2 with hD
  have hDpos : 0 < D := by positivity
  refine ⟨D, hDpos, ⌈2 * |Real.log (A / c0)| / Real.log 2⌉₊, fun k hk => ?_⟩
  have hk' : 2 * |Real.log (A / c0)| / Real.log 2 ≤ (k : ℝ) := by
    have := Nat.le_ceil (2 * |Real.log (A / c0)| / Real.log 2)
    have h2 : (⌈2 * |Real.log (A / c0)| / Real.log 2⌉₊ : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  rcases (alphaH_nonneg hc0 hc k).lt_or_eq with hpos | h0
  · have hcont := contagem hc0 hc hgr hpos
    set x := alphaH c k ^ σ with hx
    have hxpos : 0 < x := Real.rpow_pos_of_pos hpos σ
    have e : (3 * (alphaH c k)⁻¹) ^ σ = 3 ^ σ / x := by
      rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr hpos.le), Real.inv_rpow hpos.le, hx,
        div_eq_mul_inv]
    rw [e] at hcont
    have hlog := Real.log_le_log (by positivity) hcont
    rw [Real.log_mul (by positivity) hc0.ne', Real.log_pow, Real.log_mul hA.ne' (Real.exp_pos _).ne',
      Real.log_exp] at hlog
    have hlogA : Real.log (A / c0) = Real.log A - Real.log c0 := Real.log_div hA.ne' hc0.ne'
    have habs : Real.log (A / c0) ≤ |Real.log (A / c0)| := le_abs_self _
    -- A·3^σ/x ≥ (k+1)·log 2/2
    have hkey : ((k : ℝ) + 1) * Real.log 2 / 2 ≤ A * (3 ^ σ / x) := by
      push_cast at hlog
      have : |Real.log (A / c0)| * 2 ≤ (k : ℝ) * Real.log 2 := by
        rw [div_le_iff₀ hl2] at hk'
        linarith
      nlinarith
    have h3 : 0 < A * 3 ^ σ := by positivity
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [mul_div_assoc', le_div_iff₀ hxpos] at hkey
    rw [hD, div_div, le_div_iff₀ (by positivity)]
    nlinarith
  · rw [← h0, Real.zero_rpow hσ.ne']
    positivity

/-- **`Σ αₖ^s < ∞` para `s > σ`.** -/
theorem summable_alpha_rpow {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) {A σ : ℝ} (hA : 0 < A)
    (hσ : 0 < σ) (hgr : ∀ w, ‖ev c w‖ ≤ A * Real.exp (A * ‖w‖ ^ σ)) {s : ℝ} (hs : σ < s) :
    Summable fun k => alphaH c k ^ s := by
  obtain ⟨D, hD, N, hN⟩ := alpha_rpow_le hc0 hc hA hσ hgr
  set p := s / σ with hp
  have hp1 : 1 < p := by rw [hp, one_lt_div hσ]; exact hs
  have hg : Summable fun k : ℕ => D ^ p * (((k : ℝ) + 1) ^ p)⁻¹ := by
    have h1 := (Real.summable_nat_rpow_inv.mpr hp1)
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ p)⁻¹) 1).mpr h1
    refine (h2.mul_left (D ^ p)).congr fun k => ?_
    push_cast
    ring_nf
  refine Summable.of_norm_bounded_eventually hg ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop N] with k hk
  have hαk := alphaH_nonneg hc0 hc k
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hαk s)]
  have e : alphaH c k ^ s = (alphaH c k ^ σ) ^ p := by
    rw [← Real.rpow_mul hαk, hp, mul_div_cancel₀ s hσ.ne']
  rw [e]
  calc (alphaH c k ^ σ) ^ p ≤ (D / (k + 1)) ^ p :=
        Real.rpow_le_rpow (Real.rpow_nonneg hαk σ) (hN k hk) (by linarith)
    _ = D ^ p * (((k : ℝ) + 1) ^ p)⁻¹ := by
        rw [Real.div_rpow hD.le (by positivity), div_eq_mul_inv]

theorem summable_alpha {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) {A σ : ℝ} (hA : 0 < A)
    (hσ : 0 < σ) (hσ1 : σ < 1) (hgr : ∀ w, ‖ev c w‖ ≤ A * Real.exp (A * ‖w‖ ^ σ)) :
    Summable (alphaH c) := by
  have := summable_alpha_rpow hc0 hc hA hσ hgr hσ1
  simpa using this

theorem tendsto_alpha {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) {A σ : ℝ} (hA : 0 < A)
    (hσ : 0 < σ) (hσ1 : σ < 1) (hgr : ∀ w, ‖ev c w‖ ≤ A * Real.exp (A * ‖w‖ ^ σ)) :
    Tendsto (alphaH c) atTop (𝓝 0) :=
  (summable_alpha hc0 hc hA hσ hσ1 hgr).tendsto_atTop_zero

/-! ## 3. Poisson, Jensen para `∏(1 + αⱼz)` e Borel–Carathéodory -/

theorem log_one_add_le_rpow {x s : ℝ} (hx : 0 ≤ x) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    Real.log (1 + x) ≤ x ^ s / s := by
  rcases le_total x 1 with hx1 | hx1
  · have h1 : Real.log (1 + x) ≤ x := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + x)
      linarith
    have h2 : x ≤ x ^ s := by
      rcases hx.lt_or_eq with hxp | hx0
      · calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
          _ ≤ x ^ s := Real.rpow_le_rpow_of_exponent_ge hxp hx1 hs1
      · rw [← hx0, Real.zero_rpow hs0.ne']
    have h3 : x ^ s ≤ x ^ s / s := by
      rw [le_div_iff₀ hs0]
      have := Real.rpow_nonneg hx s
      nlinarith
    linarith
  · have hxp : 0 < x := by linarith
    have h1 : Real.log (1 + x) ≤ Real.log 2 + Real.log x := by
      rw [← Real.log_mul (by norm_num) hxp.ne']
      exact Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log x ≤ (x ^ s - 1) / s := by
      have := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hxp s)
      rw [Real.log_rpow hxp] at this
      rw [le_div_iff₀ hs0]
      linarith
    have h3 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have h4 : 1 ≤ 1 / s := by rw [le_div_iff₀ hs0]; linarith
    have e : (x ^ s - 1) / s = x ^ s / s - 1 / s := by ring
    linarith

/-- **Poisson + valor médio**: para `G` inteira sem zeros em `|z| ≤ r` e `|w| < r`,
`log|G(w)| ≤ log|G(0)| + (2|w|/(r − |w|))·média_{|z|=r}|log|G(z)||`. -/
theorem log_norm_le_poisson {G : ℂ → ℂ} (hG : Differentiable ℂ G) {r : ℝ} (hr : 0 < r)
    (hfree : ∀ z ∈ closedBall (0 : ℂ) r, G z ≠ 0) {w : ℂ} (hw : ‖w‖ < r) :
    Real.log ‖G w‖ ≤ Real.log ‖G 0‖ +
      2 * ‖w‖ / (r - ‖w‖) * Real.circleAverage (fun z => |Real.log ‖G z‖|) 0 r := by
  set u : ℂ → ℝ := fun z => Real.log ‖G z‖ with hu_def
  have hharm : InnerProductSpace.HarmonicOnNhd u (closedBall 0 r) :=
    fun z hz => (hG.analyticAt z).harmonicAt_log_norm (hfree z hz)
  have hcont : ContinuousOn u (closedBall 0 r) := fun z hz =>
    ((hG.continuous.norm.continuousAt).log (norm_ne_zero_iff.mpr (hfree z hz))).continuousWithinAt
  have hw' : w ∈ ball (0 : ℂ) r := mem_ball_zero_iff.mpr hw
  have hP := hharm.circleAverage_poissonKernel_smul hw'
  have hM : Real.circleAverage u 0 r = u 0 := by
    have h := (AnalyticOnNhd.circleAverage_log_norm_of_ne_zero (c := 0) (R := r) (g := G)
      (fun z _ => hG.analyticAt z) (by rw [abs_of_pos hr]; exact hfree))
    exact h
  have hsph : sphere (0 : ℂ) r ⊆ closedBall 0 r := sphere_subset_closedBall
  have hne : ∀ z ∈ sphere (0 : ℂ) r, z - 0 - (w - 0) ≠ 0 := by
    intro z hz h
    have : z = w := by simpa [sub_eq_zero] using h
    rw [this, mem_sphere_zero_iff_norm] at hz
    linarith
  have hPk_cont : ContinuousOn (poissonKernel 0 w) (sphere 0 r) := by
    have e : poissonKernel 0 w =
        fun z => (‖z - 0‖ ^ 2 - ‖w - 0‖ ^ 2) / ‖(z - 0) - (w - 0)‖ ^ 2 :=
      funext (poissonKernel_def 0 w)
    rw [e]
    intro z hz
    have hz' : ‖(z - 0) - (w - 0)‖ ≠ 0 := norm_ne_zero_iff.mpr (hne z hz)
    exact (ContinuousAt.div
      (by fun_prop : Continuous fun z : ℂ => ‖z - 0‖ ^ 2 - ‖w - 0‖ ^ 2).continuousAt
      (by fun_prop : Continuous fun z : ℂ => ‖(z - 0) - (w - 0)‖ ^ 2).continuousAt
      (pow_ne_zero 2 hz')).continuousWithinAt
  have hu_int : CircleIntegrable u 0 r := (hcont.mono hsph).circleIntegrable hr.le
  have hPu_int : CircleIntegrable (poissonKernel 0 w • u) 0 r :=
    (hPk_cont.smul (hcont.mono hsph)).circleIntegrable hr.le
  have hd_int : CircleIntegrable (fun z => (poissonKernel 0 w z - 1) * u z) 0 r :=
    ((hPk_cont.sub continuousOn_const).mul (hcont.mono hsph)).circleIntegrable hr.le
  have habs_int : CircleIntegrable (fun z => 2 * ‖w‖ / (r - ‖w‖) * |u z|) 0 r :=
    (continuousOn_const.mul (hcont.mono hsph).abs).circleIntegrable hr.le
  have hdiff : u w - u 0 = Real.circleAverage (fun z => (poissonKernel 0 w z - 1) * u z) 0 r := by
    rw [← hP, ← hM, ← Real.circleAverage_sub hPu_int hu_int]
    congr 1
    funext z
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hpt : ∀ z ∈ sphere (0 : ℂ) |r|,
      (poissonKernel 0 w z - 1) * u z ≤ 2 * ‖w‖ / (r - ‖w‖) * |u z| := by
    intro z hz
    rw [abs_of_pos hr] at hz
    have hlo := le_re_herglotzRieszKernel (c := 0) hz hw'
    have hhi := re_herglotzRieszKernel_le (c := 0) hz hw'
    have hPeq : poissonKernel 0 w z = ((z - 0 + (w - 0)) / ((z - 0) - (w - 0))).re := by
      rw [poissonKernel_eq_re_herglotzRieszKernel]
      rfl
    rw [hPeq]
    simp only [sub_zero] at hlo hhi ⊢
    set P := ((z + w) / (z - w)).re with hPdef
    have hra : 0 < r - ‖w‖ := by linarith
    have hrb : 0 < r + ‖w‖ := by linarith [norm_nonneg w]
    have h1 : P - 1 ≤ 2 * ‖w‖ / (r - ‖w‖) := by
      have e : (r + ‖w‖) / (r - ‖w‖) - 1 = 2 * ‖w‖ / (r - ‖w‖) := by
        field_simp
        ring
      linarith
    have h2 : 1 - P ≤ 2 * ‖w‖ / (r - ‖w‖) := by
      have e1 : 1 - (r - ‖w‖) / (r + ‖w‖) = 2 * ‖w‖ / (r + ‖w‖) := by
        field_simp
        ring
      have e2 : 2 * ‖w‖ / (r + ‖w‖) ≤ 2 * ‖w‖ / (r - ‖w‖) :=
        div_le_div_of_nonneg_left (by positivity) hra (by linarith [norm_nonneg w])
      linarith
    have habsP : |P - 1| ≤ 2 * ‖w‖ / (r - ‖w‖) := abs_le.mpr ⟨by linarith, h1⟩
    calc (P - 1) * u z ≤ |P - 1| * |u z| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ 2 * ‖w‖ / (r - ‖w‖) * |u z| := mul_le_mul_of_nonneg_right habsP (abs_nonneg _)
  have hmono := Real.circleAverage_mono hd_int habs_int hpt
  have hsm : Real.circleAverage (fun z => 2 * ‖w‖ / (r - ‖w‖) * |u z|) 0 r =
      2 * ‖w‖ / (r - ‖w‖) * Real.circleAverage (fun z => |u z|) 0 r := by
    have := Real.circleAverage_fun_smul (a := 2 * ‖w‖ / (r - ‖w‖)) (f := fun z => |u z|) (c := 0)
      (R := r)
    simpa only [smul_eq_mul] using this
  rw [hsm, ← hdiff] at hmono
  linarith

/-- **Jensen para o polinômio**: `média_{|z|=r} log|∏(1 + αⱼz)| ≥ 0` (cada fator dá `log⁺(αⱼr)`). -/
theorem avg_log_prod_nonneg {α : ℕ → ℝ} (hα : ∀ j, 0 ≤ α j) (k : ℕ) {r : ℝ} (hr : 0 < r)
    (hPr : ∀ j < k, α j * r ≠ 1) :
    0 ≤ Real.circleAverage (fun z => Real.log ‖∏ j ∈ Finset.range k, (1 + (α j : ℂ) * z)‖) 0 r := by
  have hfac : ∀ j < k, ∀ z ∈ sphere (0 : ℂ) r, (1 + (α j : ℂ) * z) ≠ 0 := by
    intro j hj z hz h
    have hn := congrArg norm h
    have hz' : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
    have e : (α j : ℂ) * z = -1 := by linear_combination h
    have := congrArg norm e
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hα j), hz', norm_neg, norm_one] at this
    exact hPr j hj this
  have hcongr : Set.EqOn (fun z => Real.log ‖∏ j ∈ Finset.range k, (1 + (α j : ℂ) * z)‖)
      (fun z => ∑ j ∈ Finset.range k, Real.log ‖1 + (α j : ℂ) * z‖) (sphere 0 |r|) := by
    intro z hz
    rw [abs_of_pos hr] at hz
    simp only
    rw [norm_prod, Real.log_prod]
    intro j hj
    exact norm_ne_zero_iff.mpr (hfac j (Finset.mem_range.mp hj) z hz)
  rw [Real.circleAverage_congr_sphere hcongr]
  have hint : ∀ j ∈ Finset.range k, CircleIntegrable (fun z => Real.log ‖1 + (α j : ℂ) * z‖) 0 r := by
    intro j hj
    refine ContinuousOn.circleIntegrable hr.le fun z hz => ?_
    exact ((by fun_prop : Continuous fun z : ℂ => ‖1 + (α j : ℂ) * z‖).continuousAt.log
      (norm_ne_zero_iff.mpr (hfac j (Finset.mem_range.mp hj) z hz))).continuousWithinAt
  rw [Real.circleAverage_fun_sum hint]
  refine Finset.sum_nonneg fun j hj => ?_
  rcases (hα j).lt_or_eq with hpos | h0
  · have hαc : (α j : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hfact : ∀ z : ℂ, 1 + (α j : ℂ) * z = (α j : ℂ) * (z - ((-(α j)⁻¹ : ℝ) : ℂ)) := by
      intro z
      push_cast
      field_simp
      ring
    have hcongr' : Set.EqOn (fun z => Real.log ‖1 + (α j : ℂ) * z‖)
        (fun z => Real.log (α j) + Real.log ‖z - ((-(α j)⁻¹ : ℝ) : ℂ)‖) (sphere 0 |r|) := by
      intro z hz
      rw [abs_of_pos hr] at hz
      have hz2 : z - ((-(α j)⁻¹ : ℝ) : ℂ) ≠ 0 := by
        intro h
        apply hfac j (Finset.mem_range.mp hj) z hz
        rw [hfact z, h, mul_zero]
      simp only
      rw [hfact z, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le,
        Real.log_mul hpos.ne' (norm_ne_zero_iff.mpr hz2)]
    rw [Real.circleAverage_congr_sphere hcongr']
    rw [Real.circleAverage_fun_add (circleIntegrable_const _ _ _)
      (circleIntegrable_log_norm_sub_const r), Real.circleAverage_const,
      circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne']
    have e : r⁻¹ * ‖(0 : ℂ) - ((-(α j)⁻¹ : ℝ) : ℂ)‖ = (α j * r)⁻¹ := by
      rw [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        abs_of_pos (inv_pos.mpr hpos), mul_inv]
      ring
    rw [e]
    have h1 := Real.posLog_sub_posLog_inv (x := α j * r)
    rw [Real.log_mul hpos.ne' hr.ne'] at h1
    have h2 : 0 ≤ Real.posLog (α j * r) := Real.posLog_nonneg
    linarith
  · have e : (fun z : ℂ => Real.log ‖1 + (α j : ℂ) * z‖) = fun _ => (0 : ℝ) := by
      funext z
      simp [← h0]
    rw [e, Real.circleAverage_const]

theorem ev_shift {c : ℕ → ℝ} (hc : Inteira c) (z : ℂ) :
    ev (fun m => if m = 0 then 0 else c m) z = ev c z - c 0 := by
  have hs : Summable fun n => (c n : ℂ) * z ^ n := (summable_norm_ev hc z).of_norm
  have hd : Inteira fun m => if m = 0 then 0 else c m := by
    intro R hR
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hc R hR)
    by_cases hn : n = 0
    · simp only [hn, if_true, abs_zero, zero_mul]
      positivity
    · simp only [hn, if_false, le_refl]
  have hs' : Summable fun n => ((if n = 0 then 0 else c n : ℝ) : ℂ) * z ^ n :=
    (summable_norm_ev hd z).of_norm
  unfold ev
  rw [hs.tsum_eq_zero_add, hs'.tsum_eq_zero_add]
  simp

/-- **Cota de `Gₖ` no disco unitário** (Poisson + Jensen + crescimento). -/
theorem norm_seqH_le {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) {A σ s : ℝ} (hA : 0 < A)
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hsum : Summable fun j => alphaH c j ^ s)
    (hgr : ∀ w, ‖ev c w‖ ≤ A * Real.exp (A * ‖w‖ ^ σ)) (k : ℕ) {r : ℝ} (hr : 2 ≤ r)
    (hfree : ∀ z ∈ closedBall (0 : ℂ) r, ev (seqH c k) z ≠ 0)
    (hPr : ∀ j < k, alphaH c j * r ≠ 1) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖ev (seqH c k) w‖ ≤ c0 * Real.exp (2 / (r - 1) *
      (2 * (Real.posLog A + A * r ^ σ + r ^ s * (∑' j, alphaH c j ^ s) / s) - Real.log c0)) := by
  set G := ev (seqH c k) with hGdef
  set S := ∑' j, alphaH c j ^ s with hS
  set K := Real.posLog A + A * r ^ σ + r ^ s * S / s with hK
  have hrpos : 0 < r := by linarith
  have hGd : Differentiable ℂ G := ev_differentiable (seqH_boa hc0 hc k).inteira
  have hG0 : G 0 = (c0 : ℂ) := by rw [hGdef, ev_zero, (seqH_boa hc0 hc k).zero]
  have hG0n : ‖G 0‖ = c0 := by rw [hG0, Complex.norm_real, Real.norm_of_nonneg hc0.le]
  have hwr : ‖w‖ < r := by linarith
  have hpois := log_norm_le_poisson hGd hrpos hfree hwr
  rw [hG0n] at hpois
  set P : ℂ → ℂ := fun z => ∏ j ∈ Finset.range k, (1 + (alphaH c j : ℂ) * z) with hPdef
  have hPne : ∀ z ∈ sphere (0 : ℂ) r, P z ≠ 0 := by
    intro z hz h
    rw [hPdef, Finset.prod_eq_zero_iff] at h
    obtain ⟨j, hj, hj0⟩ := h
    have e : (alphaH c j : ℂ) * z = -1 := by linear_combination hj0
    have := congrArg norm e
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (alphaH_nonneg hc0 hc j),
      mem_sphere_zero_iff_norm.mp hz, norm_neg, norm_one] at this
    exact hPr j (Finset.mem_range.mp hj) this
  have hsph : sphere (0 : ℂ) r ⊆ closedBall 0 r := sphere_subset_closedBall
  have hGne : ∀ z ∈ sphere (0 : ℂ) r, G z ≠ 0 := fun z hz => hfree z (hsph hz)
  -- cota pontual de `log⁺|G|` na circunferência
  have hpt : ∀ z ∈ sphere (0 : ℂ) |r|, Real.posLog ‖G z‖ ≤ K - Real.log ‖P z‖ := by
    intro z hz
    rw [abs_of_pos hrpos] at hz
    have hz' : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
    have hPz := hPne z hz
    have hev : ev c z = P z * G z := by rw [hPdef]; exact ev_seqH hc0 hc z k
    have hGz : ‖G z‖ = ‖ev c z‖ * ‖P z‖⁻¹ := by
      rw [hev, norm_mul, mul_comm (‖P z‖), mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hPz),
        mul_one]
    rw [hGz]
    have h1 := Real.posLog_mul (x := ‖ev c z‖) (y := ‖P z‖⁻¹)
    have h2 := Real.posLog_sub_posLog_inv (x := ‖P z‖)
    have h3 : Real.posLog ‖ev c z‖ ≤ Real.posLog A + A * r ^ σ := by
      have hb := hgr z
      rw [hz'] at hb
      calc Real.posLog ‖ev c z‖ ≤ Real.posLog (A * Real.exp (A * r ^ σ)) :=
            Real.posLog_le_posLog (by linarith [norm_nonneg (ev c z)]) hb
        _ ≤ Real.posLog A + Real.posLog (Real.exp (A * r ^ σ)) := Real.posLog_mul
        _ = Real.posLog A + A * r ^ σ := by
            have hexp : 1 ≤ |Real.exp (A * r ^ σ)| := by
              rw [abs_of_pos (Real.exp_pos _)]
              exact Real.one_le_exp (by positivity)
            rw [Real.posLog_eq_log hexp, Real.log_exp]
    have h4 : Real.posLog ‖P z‖ ≤ r ^ s * S / s := by
      have hle : ‖P z‖ ≤ ∏ j ∈ Finset.range k, (1 + alphaH c j * r) := by
        rw [hPdef, norm_prod]
        refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun j _ => ?_
        have := norm_one_add_le (alphaH_nonneg hc0 hc j) z
        rwa [hz'] at this
      have hge1 : 1 ≤ ∏ j ∈ Finset.range k, (1 + alphaH c j * r) := by
        apply Finset.one_le_prod₀
        intro j _
        have := mul_nonneg (alphaH_nonneg hc0 hc j) hrpos.le
        linarith
      calc Real.posLog ‖P z‖ ≤ Real.posLog (∏ j ∈ Finset.range k, (1 + alphaH c j * r)) :=
            Real.posLog_le_posLog (by linarith [norm_nonneg (P z)]) hle
        _ = Real.log (∏ j ∈ Finset.range k, (1 + alphaH c j * r)) :=
            Real.posLog_eq_log (by rw [abs_of_pos (by linarith)]; exact hge1)
        _ = ∑ j ∈ Finset.range k, Real.log (1 + alphaH c j * r) := by
            rw [Real.log_prod]
            intro j _
            have := mul_nonneg (alphaH_nonneg hc0 hc j) hrpos.le
            linarith
        _ ≤ ∑ j ∈ Finset.range k, (alphaH c j * r) ^ s / s :=
            Finset.sum_le_sum fun j _ =>
              log_one_add_le_rpow (mul_nonneg (alphaH_nonneg hc0 hc j) hrpos.le) hs0 hs1
        _ = r ^ s / s * ∑ j ∈ Finset.range k, alphaH c j ^ s := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Real.mul_rpow (alphaH_nonneg hc0 hc j) hrpos.le]
            ring
        _ ≤ r ^ s / s * S := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact hsum.sum_le_tsum _ fun j _ => Real.rpow_nonneg (alphaH_nonneg hc0 hc j) s
        _ = r ^ s * S / s := by ring
    rw [hK]
    linarith
  -- integrabilidade
  have hlogP_int : CircleIntegrable (fun z => Real.log ‖P z‖) 0 r := by
    refine ContinuousOn.circleIntegrable hrpos.le fun z hz => ?_
    exact ((by fun_prop : Continuous fun z : ℂ => ‖P z‖).continuousAt.log
      (norm_ne_zero_iff.mpr (hPne z hz))).continuousWithinAt
  have hcontG : ContinuousOn (fun z => Real.log ‖G z‖) (sphere 0 r) := fun z hz =>
    ((hGd.continuous.norm.continuousAt).log (norm_ne_zero_iff.mpr (hGne z hz))).continuousWithinAt
  have hposG_int : CircleIntegrable (fun z => Real.posLog ‖G z‖) 0 r :=
    (Real.continuous_posLog.comp_continuousOn hGd.continuous.norm.continuousOn).circleIntegrable
      hrpos.le
  have hKP_int : CircleIntegrable (fun z => K - Real.log ‖P z‖) 0 r :=
    (circleIntegrable_const K 0 r).sub hlogP_int
  have havgpos : Real.circleAverage (fun z => Real.posLog ‖G z‖) 0 r ≤ K := by
    have h1 := Real.circleAverage_mono hposG_int hKP_int hpt
    rw [Real.circleAverage_fun_sub (circleIntegrable_const K 0 r) hlogP_int, Real.circleAverage_const] at h1
    have h2 := avg_log_prod_nonneg (alphaH_nonneg hc0 hc) k hrpos hPr
    linarith
  -- média de |log|G||
  have hmv : Real.circleAverage (fun z => Real.log ‖G z‖) 0 r = Real.log c0 := by
    have h := (AnalyticOnNhd.circleAverage_log_norm_of_ne_zero (c := 0) (R := r) (g := G)
      (fun z _ => hGd.analyticAt z) (by rw [abs_of_pos hrpos]; exact hfree))
    rw [h, hG0n]
  have habs_eq : Set.EqOn (fun z => |Real.log ‖G z‖|)
      (fun z => 2 * Real.posLog ‖G z‖ - Real.log ‖G z‖) (sphere 0 |r|) := by
    intro z _
    simp only
    have := Real.half_mul_log_add_log_abs (x := ‖G z‖)
    linarith
  have hlogG_int : CircleIntegrable (fun z => Real.log ‖G z‖) 0 r :=
    hcontG.circleIntegrable hrpos.le
  have havgabs : Real.circleAverage (fun z => |Real.log ‖G z‖|) 0 r ≤ 2 * K - Real.log c0 := by
    have h2int : CircleIntegrable (fun z => 2 * Real.posLog ‖G z‖) 0 r :=
      ContinuousOn.circleIntegrable hrpos.le
        ((continuous_const.mul (Real.continuous_posLog.comp hGd.continuous.norm)).continuousOn)
    have hsub := Real.circleAverage_fun_sub h2int hlogG_int
    try simp only at hsub
    rw [Real.circleAverage_congr_sphere habs_eq, hsub, hmv]
    have : Real.circleAverage (fun z => 2 * Real.posLog ‖G z‖) 0 r =
        2 * Real.circleAverage (fun z => Real.posLog ‖G z‖) 0 r := by
      have := Real.circleAverage_fun_smul (a := (2 : ℝ)) (f := fun z => Real.posLog ‖G z‖) (c := 0)
        (R := r)
      simpa only [smul_eq_mul] using this
    rw [this]
    linarith
  have havgabs0 : 0 ≤ Real.circleAverage (fun z => |Real.log ‖G z‖|) 0 r :=
    Real.circleAverage_nonneg_of_nonneg fun z _ => abs_nonneg _
  have hcoef : 2 * ‖w‖ / (r - ‖w‖) ≤ 2 / (r - 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [norm_nonneg w]
  have hlog : Real.log ‖G w‖ ≤ Real.log c0 + 2 / (r - 1) * (2 * K - Real.log c0) := by
    calc Real.log ‖G w‖ ≤ Real.log c0 + 2 * ‖w‖ / (r - ‖w‖) *
          Real.circleAverage (fun z => |Real.log ‖G z‖|) 0 r := hpois
      _ ≤ Real.log c0 + 2 / (r - 1) * Real.circleAverage (fun z => |Real.log ‖G z‖|) 0 r := by
          gcongr
      _ ≤ Real.log c0 + 2 / (r - 1) * (2 * K - Real.log c0) := by
          gcongr
          · have : (0 : ℝ) < r - 1 := by linarith
            positivity
  have hGw : G w ≠ 0 := hfree w (by rw [mem_closedBall_zero_iff]; linarith)
  calc ‖G w‖ = Real.exp (Real.log ‖G w‖) := (Real.exp_log (norm_pos_iff.mpr hGw)).symm
    _ ≤ Real.exp (Real.log c0 + 2 / (r - 1) * (2 * K - Real.log c0)) := Real.exp_le_exp.mpr hlog
    _ = c0 * Real.exp (2 / (r - 1) * (2 * K - Real.log c0)) := by
        rw [Real.exp_add, Real.exp_log hc0]

/-- **Coeficientes de `Gₖ`** (Borel–Carathéodory + Cauchy): `|Gₖ,ₙ| ≤ 2^{n+1}·c₀(e^E − 1)` para `n ≥ 1`. -/
theorem coef_seqH_le {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) {k : ℕ} {E : ℝ}
    (hbd : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖ev (seqH c k) w‖ ≤ c0 * Real.exp E) {n : ℕ} (hn : 1 ≤ n) :
    |seqH c k n| ≤ 2 ^ (n + 1) * (c0 * (Real.exp E - 1)) := by
  set G := ev (seqH c k) with hGdef
  have hB := seqH_boa hc0 hc k
  have hGd : Differentiable ℂ G := ev_differentiable hB.inteira
  have hG0 : G 0 = (c0 : ℂ) := by rw [hGdef, ev_zero, hB.zero]
  set M := c0 * (Real.exp E - 1) with hM
  have hM0 : 0 ≤ M := by
    have := hbd 0 (by simp)
    rw [hG0, Complex.norm_real, Real.norm_of_nonneg hc0.le] at this
    have h1 : 1 ≤ Real.exp E := by
      by_contra h
      push_neg at h
      have := mul_lt_mul_of_pos_left h hc0
      linarith
    rw [hM]
    have : 0 ≤ Real.exp E - 1 := by linarith
    positivity
  set d : ℕ → ℝ := fun m => if m = 0 then 0 else seqH c k m with hd
  have hdI : Inteira d := by
    intro R hR
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun m => ?_) (hB.inteira R hR)
    simp only [hd]
    by_cases hm : m = 0
    · simp only [hm, if_true, abs_zero, zero_mul]
      positivity
    · simp only [hm, if_false, le_refl]
  have hevd : ∀ z, ev d z = G z - c0 := by
    intro z
    rw [hd, ev_shift hB.inteira z, hB.zero]
  suffices h : ∀ η > 0, |seqH c k n| ≤ 2 ^ (n + 1) * (M + η) by
    by_contra hcon
    push_neg at hcon
    have hpos : 0 < (|seqH c k n| - 2 ^ (n + 1) * M) / 2 ^ (n + 2) := by
      apply div_pos _ (by positivity)
      linarith
    have := h _ hpos
    have e : 2 ^ (n + 1) * (M + (|seqH c k n| - 2 ^ (n + 1) * M) / 2 ^ (n + 2)) =
        2 ^ (n + 1) * M + (|seqH c k n| - 2 ^ (n + 1) * M) / 2 := by
      rw [pow_succ 2 (n + 1)]
      field_simp
    rw [e] at this
    linarith
  intro η hη
  have hMη : 0 < M + η := by linarith
  have hBC : ∀ w ∈ sphere (0 : ℂ) (1 / 2), ‖ev d w‖ ≤ 2 * (M + η) := by
    intro w hw
    have hw' : ‖w‖ = 1 / 2 := mem_sphere_zero_iff_norm.mp hw
    rw [hevd]
    have hmaps : Set.MapsTo (fun z => G z - c0) (ball (0 : ℂ) 1) {z | z.re ≤ M + η} := by
      intro z hz
      have hz' : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
      have h1 := hbd z hz'
      simp only [Set.mem_setOf_eq, Complex.sub_re, Complex.ofReal_re]
      have h2 := Complex.re_le_norm (G z)
      rw [hM]
      nlinarith
    have hbc := Complex.borelCaratheodory_zero hMη (hGd.sub_const _).differentiableOn hmaps one_pos
      (mem_ball_zero_iff.mpr (by rw [hw']; norm_num)) (by rw [hG0]; simp)
    rw [hw'] at hbc
    calc ‖G w - c0‖ ≤ 2 * (M + η) * (1 / 2) / (1 - 1 / 2) := hbc
      _ = 2 * (M + η) := by ring
  have hcau := coef_le hdI (by norm_num : (0 : ℝ) < 1 / 2) hBC n
  have hdn : d n = seqH c k n := by simp only [hd]; rw [if_neg (by omega)]
  rw [hdn] at hcau
  have h2n : (0 : ℝ) < (1 / 2) ^ n := by positivity
  calc |seqH c k n| = |seqH c k n| * (1 / 2) ^ n * 2 ^ n := by
        rw [mul_assoc, ← mul_pow]; norm_num
    _ ≤ 2 * (M + η) * 2 ^ n := mul_le_mul_of_nonneg_right hcau (by positivity)
    _ = 2 ^ (n + 1) * (M + η) := by ring

/-! ## 4. `Gₖ → c₀` e o teorema -/

theorem tendsto_rpow_div_sub_one {p : ℝ} (hp : p < 1) :
    Tendsto (fun r : ℝ => r ^ p / (r - 1)) atTop (𝓝 0) := by
  have hup : Tendsto (fun r : ℝ => 2 * r ^ (-(1 - p))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - p)).const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
    have : 0 < r - 1 := by linarith
    positivity
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
    have hr0 : 0 < r := by linarith
    have hr1 : 0 < r - 1 := by linarith
    have e : r ^ (-(1 - p)) = r ^ p / r := by
      rw [neg_sub, Real.rpow_sub hr0, Real.rpow_one]
    rw [e, div_le_iff₀ hr1]
    have hrp : 0 ≤ r ^ p := Real.rpow_nonneg hr0.le p
    rw [show 2 * (r ^ p / r) * (r - 1) = r ^ p * (2 * (r - 1) / r) by ring]
    have : 1 ≤ 2 * (r - 1) / r := by rw [le_div_iff₀ hr0]; linarith
    nlinarith

/-- `E(r) = (2/(r−1))(2(log⁺A + A r^σ + r^s S/s) − log c₀) → 0`. -/
theorem tendsto_E {A σ s S c0 : ℝ} (hσ1 : σ < 1) (hs1 : s < 1) :
    Tendsto (fun r : ℝ => 2 / (r - 1) *
      (2 * (Real.posLog A + A * r ^ σ + r ^ s * S / s) - Real.log c0)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => 2 / (r - 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ (-1) tendsto_id)
  have h2 := tendsto_rpow_div_sub_one hσ1
  have h3 := tendsto_rpow_div_sub_one hs1
  have hsum := ((h1.mul_const (2 * Real.posLog A - Real.log c0)).add
    ((h2.const_mul (4 * A)).add (h3.const_mul (4 * S / s))))
  simp only [zero_mul, mul_zero, add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  have hr1 : r - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **Os coeficientes de `Gₖ` convergem**: `Gₖ,ₙ → 0` para `n ≥ 1` (e `Gₖ,₀ = c₀`). -/
theorem coef_seqH_tendsto {c0 : ℝ} (hc0 : 0 < c0) {c : ℕ → ℝ} (hc : Boa c0 c) {A σ : ℝ} (hA : 0 < A)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hgr : ∀ w, ‖ev c w‖ ≤ A * Real.exp (A * ‖w‖ ^ σ)) {n : ℕ}
    (hn : 1 ≤ n) : Tendsto (fun k => seqH c k n) atTop (𝓝 0) := by
  classical
  set s := (σ + 1) / 2 with hsdef
  have hs0 : 0 < s := by rw [hsdef]; linarith
  have hσs : σ < s := by rw [hsdef]; linarith
  have hs1 : s < 1 := by rw [hsdef]; linarith
  have hsum := summable_alpha_rpow hc0 hc hA hσ0 hgr hσs
  set S := ∑' j, alphaH c j ^ s with hS
  set E : ℝ → ℝ := fun r => 2 / (r - 1) *
    (2 * (Real.posLog A + A * r ^ σ + r ^ s * S / s) - Real.log c0) with hE
  have hEt : Tendsto E atTop (𝓝 0) := tendsto_E hσ1 hs1
  have hFt : Tendsto (fun r => 2 ^ (n + 1) * (c0 * (Real.exp (E r) - 1))) atTop (𝓝 0) := by
    have := ((Real.continuous_exp.tendsto 0).comp hEt)
    simp only [Real.exp_zero] at this
    have h2 := ((this.sub_const 1).const_mul c0).const_mul (2 ^ (n + 1))
    simpa using h2
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨r0, hr0⟩ := (Metric.tendsto_atTop.mp hFt) ε hε
  set r1 := max r0 2 with hr1
  have hα := tendsto_alpha hc0 hc hA hσ0 hσ1 hgr
  obtain ⟨k0, hk0⟩ := (Metric.tendsto_atTop.mp hα) (1 / (r1 + 1)) (by positivity)
  refine ⟨k0, fun k hk => ?_⟩
  -- escolher `r ∈ (r1, r1 + 1)` fora de `{1/αⱼ}`
  obtain ⟨r, hrI, hrT⟩ := (Set.Ioo_infinite (by linarith : r1 < r1 + 1)).exists_notMem_finset
    ((Finset.range k).image fun j => (alphaH c j)⁻¹)
  have hr2 : 2 ≤ r := by have := hrI.1; rw [hr1] at this; linarith [le_max_right r0 2]
  have hrr0 : r0 ≤ r := by have := hrI.1; linarith [le_max_left r0 2]
  have hPr : ∀ j < k, alphaH c j * r ≠ 1 := by
    intro j hj h
    apply hrT
    rw [Finset.mem_image]
    refine ⟨j, Finset.mem_range.mpr hj, ?_⟩
    have hαj : alphaH c j ≠ 0 := by intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h
    field_simp
    linarith
  have hαk : alphaH c k < 1 / (r1 + 1) := by
    have := hk0 k hk
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (alphaH_nonneg hc0 hc k)] at this
    exact this
  have hfree : ∀ z ∈ closedBall (0 : ℂ) r, ev (seqH c k) z ≠ 0 := by
    intro z hz h
    rcases (alphaH_nonneg hc0 hc k).lt_or_eq with hpos | h0
    · have h1 := alphaH_min hc0 hc k hpos z h
      have h2 : r1 + 1 < (alphaH c k)⁻¹ := by
        rw [lt_inv_comm₀ (by positivity) hpos]
        simpa [one_div] using hαk
      have h3 : ‖z‖ ≤ r := mem_closedBall_zero_iff.mp hz
      linarith [hrI.2]
    · exact alphaH_zero_free hc0 hc k h0.symm z h
  have hbd : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖ev (seqH c k) w‖ ≤ c0 * Real.exp (E r) := fun w hw =>
    norm_seqH_le hc0 hc hA hs0 hs1.le hsum hgr k hr2 hfree hPr hw
  have hcoef := coef_seqH_le hc0 hc hbd hn
  have hF := hr0 r hrr0
  rw [Real.dist_eq, sub_zero] at hF ⊢
  have h0 : 0 ≤ 2 ^ (n + 1) * (c0 * (Real.exp (E r) - 1)) := (abs_nonneg _).trans hcoef
  rw [abs_of_nonneg h0] at hF
  linarith

theorem prodCoef_smul (a0 : ℝ) (α : ℕ → ℝ) : ∀ N n, prodCoef a0 α N n = a0 * prodCoef 1 α N n
  | 0, n => by simp only [prodCoef]; split_ifs <;> ring
  | N + 1, n => by
    simp only [prodCoef]
    rw [prodCoef_smul a0 α N n, prodCoef_smul a0 α N (n - 1)]
    split_ifs <;> ring

/-- **Hadamard de gênero 0, coeficientes**: `cₙ = c₀·eₙ(α)`, com `eₙ(α)` os coeficientes de `∏(1 + αⱼz)`. -/
theorem coef_eq_lim {c : ℕ → ℝ} (hc : Inteira c) (h0 : 0 < c 0) (hz : ZerosNeg c) {A σ : ℝ}
    (hA : 0 < A) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hgr : ∀ w, ‖ev c w‖ ≤ A * Real.exp (A * ‖w‖ ^ σ))
    (n : ℕ) : Tendsto (fun k => prodCoef (c 0) (alphaH c) k n) atTop (𝓝 (c n)) := by
  have hB : Boa (c 0) c := ⟨hc, rfl, hz⟩
  have hα := alphaH_nonneg h0 hB
  have hsα := summable_alpha h0 hB hA hσ0 hσ1 hgr
  -- `Σ_{i≤n} p_k(i)·G_k(n−i) → c₀·eₙ`
  have hlim : Tendsto (fun k => ∑ i ∈ Finset.range (n + 1),
      prodCoef 1 (alphaH c) k i * seqH c k (n - i)) atTop
      (𝓝 (∑ i ∈ Finset.range (n + 1), coefGenero0 1 (alphaH c) i * (if n - i = 0 then c 0 else 0))) := by
    refine tendsto_finset_sum _ fun i hi => ?_
    refine (tendsto_prodCoef zero_le_one hα hsα i).mul ?_
    by_cases hni : n - i = 0
    · rw [if_pos hni, hni]
      have : (fun k => seqH c k 0) = fun _ => c 0 := funext fun k => (seqH_boa h0 hB k).zero
      rw [this]
      exact tendsto_const_nhds
    · rw [if_neg hni]
      exact coef_seqH_tendsto h0 hB hA hσ0 hσ1 hgr (by omega)
  have hconst : (fun k => ∑ i ∈ Finset.range (n + 1),
      prodCoef 1 (alphaH c) k i * seqH c k (n - i)) = fun _ => c n :=
    funext fun k => (coef_seqH h0 hB k n).symm
  rw [hconst] at hlim
  have hval : ∑ i ∈ Finset.range (n + 1), coefGenero0 1 (alphaH c) i * (if n - i = 0 then c 0 else 0) =
      coefGenero0 1 (alphaH c) n * c 0 := by
    rw [Finset.sum_eq_single n]
    · simp
    · intro i hi hin
      have : n - i ≠ 0 := by have := Finset.mem_range.mp hi; omega
      rw [if_neg this, mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  rw [hval] at hlim
  have hcn : c n = coefGenero0 1 (alphaH c) n * c 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  have := (tendsto_prodCoef zero_le_one hα hsα n).const_mul (c 0)
  rw [hcn, mul_comm]
  refine this.congr fun k => ?_
  rw [prodCoef_smul (c 0)]

/-- **Hadamard de gênero 0 + Edrei (⇐)**: `F = Σcₙzⁿ` inteira de ordem `σ < 1`, `c₀ > 0`, só zeros reais
negativos ⇒ `T(c)` é totalmente não negativa. -/
theorem hadamard_tn {c : ℕ → ℝ} (hc : Inteira c) (h0 : 0 < c 0) (hz : ZerosNeg c) {A σ : ℝ}
    (hA : 0 < A) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hgr : ∀ w, ‖ev c w‖ ≤ A * Real.exp (A * ‖w‖ ^ σ)) :
    (toep c).IsTotallyNonneg := by
  have hB : Boa (c 0) c := ⟨hc, rfl, hz⟩
  refine tn_closed (A := fun k => toep (prodCoef (c 0) (alphaH c) k))
    (tn_prodCoef h0.le (alphaH_nonneg h0 hB)) fun i j => ?_
  simp only [toep]
  split_ifs
  · exact coef_eq_lim hc h0 hz hA hσ0 hσ1 hgr _
  · exact tendsto_const_nhds

/-- **Teorema de Aissen–Schoenberg–Whitney–Edrei para funções inteiras de ordem `< 1`**: para
`F = Σcₙzⁿ` inteira com `c₀ > 0` e `|F(w)| ≤ A·exp(A|w|^σ)`, `σ < 1`:
`T(c)` totalmente não negativa ⟺ todos os zeros de `F` são reais negativos. -/
theorem tn_iff_zeros {c : ℕ → ℝ} (hc : Inteira c) (h0 : 0 < c 0) {A σ : ℝ} (hA : 0 < A)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hgr : ∀ w, ‖ev c w‖ ≤ A * Real.exp (A * ‖w‖ ^ σ)) :
    (toep c).IsTotallyNonneg ↔ ZerosNeg c :=
  ⟨fun h w hw => edrei_inteira hc h0 h hw, fun h => hadamard_tn hc h0 h hA hσ0 hσ1 hgr⟩

end ATK.Hadamard

#print axioms ATK.Hadamard.ev_ofReal
#print axioms ATK.Hadamard.passo_spec
#print axioms ATK.Hadamard.seqH_boa
#print axioms ATK.Hadamard.alphaH_nonneg
#print axioms ATK.Hadamard.seqH_succ_coef
#print axioms ATK.Hadamard.seqH_succ_zero
#print axioms ATK.Hadamard.ev_seqH_succ
#print axioms ATK.Hadamard.alphaH_zero_free
#print axioms ATK.Hadamard.alphaH_min
#print axioms ATK.Hadamard.alphaH_exists
#print axioms ATK.Hadamard.alphaH_succ_le
#print axioms ATK.Hadamard.alphaH_antitone
#print axioms ATK.Hadamard.ev_seqH
#print axioms ATK.Hadamard.mk_seqH
#print axioms ATK.Hadamard.coef_seqH
#print axioms ATK.Hadamard.norm_one_add_ge
#print axioms ATK.Hadamard.norm_one_add_le
#print axioms ATK.Hadamard.contagem
#print axioms ATK.Hadamard.alpha_rpow_le
#print axioms ATK.Hadamard.summable_alpha_rpow
#print axioms ATK.Hadamard.summable_alpha
#print axioms ATK.Hadamard.tendsto_alpha
#print axioms ATK.Hadamard.log_one_add_le_rpow
#print axioms ATK.Hadamard.log_norm_le_poisson
#print axioms ATK.Hadamard.avg_log_prod_nonneg
#print axioms ATK.Hadamard.ev_shift
#print axioms ATK.Hadamard.norm_seqH_le
#print axioms ATK.Hadamard.coef_seqH_le
#print axioms ATK.Hadamard.tendsto_rpow_div_sub_one
#print axioms ATK.Hadamard.tendsto_E
#print axioms ATK.Hadamard.coef_seqH_tendsto
#print axioms ATK.Hadamard.prodCoef_smul
#print axioms ATK.Hadamard.coef_eq_lim
#print axioms ATK.Hadamard.hadamard_tn
#print axioms ATK.Hadamard.tn_iff_zeros
