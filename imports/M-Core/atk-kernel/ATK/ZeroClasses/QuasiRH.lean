import ATK.ZeroClasses.VonKochRH

/-!
# Quasi-RH: `ζ ≠ 0` em `Re s > θ` ⟺ `ψ(x) = x + O(x^{θ+ε})` ⟺ `M(x) = O(x^{θ+ε})` (rodada 57)

Para `½ ≤ θ < 1`, com `SemZeros θ := ∀ s, θ < Re s → ζ(s) ≠ 0`:

* **`semZeros_iff_psi`**: `SemZeros θ ⟺ ∀ ε > 0, ψ(N) − N = O((N + 1)^{θ+ε})`;
* **`semZeros_iff_mertens`**: `SemZeros θ ⟺ ∀ ε > 0, M(N) = O((N + 1)^{θ+ε})`;
* **`psi_iff_mertens`**: as duas cotas são equivalentes para cada `θ`;
* `semZeros_meio_iff`: `SemZeros ½ ⟺ RH` (e `θ = ½` recupera os critérios de von Koch e de Littlewood).

As direções ⇐ são a rodada 55 (`ATK.ZeroClasses.VonKoch.zeroFree_of_psi`, `zeroFree_of_mertens`). As ⇒ refazem a
rodada 56 com `θ` no lugar de `½`:

1. o ramo de `log ζ` no disco de centro `cθ = 5/2 + θ + it` e raio `5/2` (contido em `Re s > θ`), com
   `|log ζ| ≤ (10(log(2(|t| + 6)) + 1)/δ)^{θ₂(δ)}` em `|s − cθ| ≤ 5/2 − δ` (`norm_L_le`: Borel–Carathéodory e três
   círculos, como em `ATK.RHLogZeta`, sob `SemZeros θ` em vez de RH);
2. `|1/ζ(s)| ≤ C(1 + |t|)^η` (`norm_F_le`) e `|ζ′/ζ(s) + ζ(s)| ≤ C(1 + |t|)^η` (`norm_H_le`) em `Re s ≥ θ + δ`;
3. o **deslocamento por `θ − ½`**: os coeficientes `a(n)n^{−(θ − ½ + δ)}` têm série holomorfa em `Re u > ½`, e o
   Littlewood geral da rodada 56 (`cota_gen`) se aplica sem mudança;
4. somação por partes (`abel_cota`).

Classificação (rodada 57): **reformulação** (Ingham, Cap. IV; Titchmarsh §14.25), parametrizada por `θ`. Não dá
nenhum semiplano sem zeros: `SemZeros θ` é OPEN_MATH para todo `θ < 1`.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.QuasiRH

open ATK.RHLogZeta (existe_log_bola tres_circulos norm_zeta_sub_one_le zeta_ne_zero_re_ge norm_log_zeta_le
  norm_inv_zeta_le_two young θ₂ θ₂_bounds F F_eq zeta₁_eq)
open ATK.ZeroClasses.VonKochRH (Hf Hf_eq norm_logDeriv_le_dois fco norm_fco_le term_fco LSeries_fco cota_gen
  abel_cota E_eq_sum term_mul_rpow)
open ATK.ZeroClasses.VonKoch (cL E zeroFree_of_psi zeroFree_of_mertens)
open ATK.ZeroClasses.PerronD (xN)
open ATK.ZeroClasses.LittlewoodMu (xN_ge_um mu norm_mu_le LSeries_mu)

/-- `ζ` sem zeros em `Re s > θ`. -/
def SemZeros (θ : ℝ) : Prop := ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

/-! ## 1. `ζ₁`, `F` e `H` em `Re s > θ` -/

theorem zeta₁_ne_zero {θ : ℝ} (hZ : SemZeros θ) {s : ℂ} (hs : θ < s.re) : riemannZeta₁ s ≠ 0 := by
  by_cases hs1 : s = 1
  · subst hs1; rw [riemannZeta₁_one]; exact one_ne_zero
  rw [zeta₁_eq hs1]
  exact mul_ne_zero (sub_ne_zero.mpr hs1) (hZ s hs)

theorem differentiableAt_F {θ : ℝ} (hZ : SemZeros θ) {s : ℂ} (hs : θ < s.re) : DifferentiableAt ℂ F s :=
  ((differentiableAt_id.sub (differentiableAt_const _))).div
    (differentiable_riemannZeta₁ s) (zeta₁_ne_zero hZ hs)

theorem differentiableAt_Hf {θ : ℝ} (hZ : SemZeros θ) {s : ℂ} (hs : θ < s.re) :
    DifferentiableAt ℂ Hf s := by
  have h1 := zeta₁_ne_zero hZ hs
  have hd : DifferentiableAt ℂ (deriv riemannZeta₁) s :=
    (differentiable_riemannZeta₁.analyticAt s).deriv.differentiableAt
  exact ((hd.neg.div (differentiable_riemannZeta₁ s) h1).sub (differentiable_riemannZeta₀ s))

/-! ## 2. O ramo de `log ζ` no disco `|s − (5/2 + θ + it)| < 5/2` -/

/-- O centro `cθ = 5/2 + θ + it`. -/
noncomputable def cθ (θ t : ℝ) : ℂ := ((5 / 2 + θ : ℝ) : ℂ) + t * I

theorem cθ_re (θ t : ℝ) : (cθ θ t).re = 5 / 2 + θ := by simp [cθ]

theorem cθ_im (θ t : ℝ) : (cθ θ t).im = t := by simp [cθ]

theorem bola_props {θ t : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (ht : 4 ≤ |t|) {z : ℂ}
    (hz : z ∈ ball (cθ θ t) (5 / 2)) :
    θ < z.re ∧ z ≠ 1 ∧ ‖z‖ ≤ |t| + 6 ∧ 3 / 2 ≤ ‖z - 1‖ := by
  rw [mem_ball, dist_eq_norm] at hz
  have hre : |z.re - (5 / 2 + θ)| < 5 / 2 := by
    have := Complex.abs_re_le_norm (z - cθ θ t)
    rw [sub_re, cθ_re] at this; linarith
  have him : |z.im - t| < 5 / 2 := by
    have := Complex.abs_im_le_norm (z - cθ θ t)
    rw [sub_im, cθ_im] at this; linarith
  have hre' := abs_lt.mp hre
  have him' := abs_lt.mp him
  have himz : 3 / 2 ≤ |z.im| := by
    rcases le_total 0 t with h0 | h0
    · rw [abs_of_nonneg h0] at ht
      rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_nonpos h0] at ht
      rw [abs_of_neg (by linarith)]; linarith
  have hz1 : 3 / 2 ≤ ‖z - 1‖ := by
    refine himz.trans ?_
    have := Complex.abs_im_le_norm (z - 1)
    simpa using this
  refine ⟨by linarith, ?_, ?_, hz1⟩
  · intro h; rw [h] at hz1; simp at hz1; norm_num at hz1
  · have hc : ‖cθ θ t‖ ≤ (5 / 2 + θ) + |t| := by
      unfold cθ
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      simp
    calc ‖z‖ = ‖(z - cθ θ t) + cθ θ t‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - cθ θ t‖ + ‖cθ θ t‖ := norm_add_le _ _
      _ ≤ 5 / 2 + ((5 / 2 + θ) + |t|) := by linarith
      _ ≤ |t| + 6 := by linarith

theorem norm_zeta_le_bola {θ t : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (ht : 4 ≤ |t|) {z : ℂ}
    (hz : z ∈ ball (cθ θ t) (5 / 2)) : ‖riemannZeta z‖ ≤ 2 * (|t| + 6) := by
  obtain ⟨hre, hz1, hn, hd⟩ := bola_props hθ hθ1 ht hz
  have h := ATK.ZetaRegiao.norm_zeta_le (by linarith) hz1
  have hd0 : 0 < ‖z - 1‖ := by linarith
  have h1 : ‖z‖ / ‖z - 1‖ ≤ |t| + 6 := by
    rw [div_le_iff₀ hd0]; nlinarith [norm_nonneg z]
  have h2 : ‖z‖ / (2 * z.re) ≤ |t| + 6 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [norm_nonneg z]
  linarith

theorem log_zeta_cθ {θ : ℝ} (hθ : 0 ≤ θ) (t : ℝ) :
    Complex.exp (Complex.log (riemannZeta (cθ θ t))) = riemannZeta (cθ θ t) :=
  Complex.exp_log (zeta_ne_zero_re_ge (by rw [cθ_re]; linarith))

/-- **Sob `SemZeros θ`**: o ramo de `log ζ` no disco, com `L(cθ) = Log ζ(cθ)`. -/
theorem existe_log_zeta {θ : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) {t : ℝ} (ht : 4 ≤ |t|) :
    ∃ L : ℂ → ℂ, L (cθ θ t) = Complex.log (riemannZeta (cθ θ t)) ∧
      (∀ z ∈ ball (cθ θ t) (5 / 2), Complex.exp (L z) = riemannZeta z) ∧
      ∀ z ∈ ball (cθ θ t) (5 / 2), HasDerivAt L (deriv riemannZeta z / riemannZeta z) z := by
  refine existe_log_bola ?_ ?_ (log_zeta_cθ (by linarith) t) (by norm_num)
  · intro z hz
    exact (differentiableAt_riemannZeta (bola_props hθ hθ1 ht hz).2.1).differentiableWithinAt
  · intro z hz
    exact hZ z (bola_props hθ hθ1 ht hz).1

/-- O ramo coincide com o logaritmo principal perto de `cθ` (onde `Re s ≥ 5/2`). -/
theorem L_eq_log {θ : ℝ} (hθ : 1 / 2 ≤ θ) {t : ℝ} {L : ℂ → ℂ}
    (hL0 : L (cθ θ t) = Complex.log (riemannZeta (cθ θ t)))
    (hLd : ∀ z ∈ ball (cθ θ t) (5 / 2), HasDerivAt L (deriv riemannZeta z / riemannZeta z) z) :
    EqOn L (fun z => Complex.log (riemannZeta z)) (ball (cθ θ t) (1 / 2)) := by
  have hsub : ball (cθ θ t) (1 / 2) ⊆ ball (cθ θ t) (5 / 2) := ball_subset_ball (by norm_num)
  have hre : ∀ z ∈ ball (cθ θ t) (1 / 2), 5 / 2 ≤ z.re := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have := Complex.abs_re_le_norm (z - cθ θ t)
    rw [sub_re, cθ_re] at this
    linarith [abs_lt.mp (lt_of_le_of_lt this hz)]
  have hg : ∀ z ∈ ball (cθ θ t) (1 / 2), HasDerivAt (fun z => Complex.log (riemannZeta z))
      (deriv riemannZeta z / riemannZeta z) z := by
    intro z hz
    have hz1 : z ≠ 1 := by intro h; have := hre z hz; rw [h, one_re] at this; norm_num at this
    have hζ := (differentiableAt_riemannZeta hz1).hasDerivAt
    refine hζ.clog ?_
    left
    have h := norm_zeta_sub_one_le (hre z hz)
    have := Complex.abs_re_le_norm (riemannZeta z - 1)
    rw [sub_re, one_re] at this
    linarith [abs_le.mp (this.trans h)]
  refine isOpen_ball.eqOn_of_deriv_eq (convex_ball _ _).isPreconnected
    (fun z hz => (hLd z (hsub hz)).differentiableAt.differentiableWithinAt)
    (fun z hz => (hg z hz).differentiableAt.differentiableWithinAt) ?_
    (mem_ball_self (by norm_num)) hL0
  intro z hz
  rw [(hLd z (hsub hz)).deriv, (hg z hz).deriv]

/-- **A cota de `log ζ`** em `|s − cθ| ≤ 5/2 − δ` (três círculos + Borel–Carathéodory), `|t| ≥ 4`. -/
theorem norm_L_le {θ : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) {t δ : ℝ} (ht : 4 ≤ |t|)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {L : ℂ → ℂ} (hL0 : L (cθ θ t) = Complex.log (riemannZeta (cθ θ t)))
    (hLe : ∀ z ∈ ball (cθ θ t) (5 / 2), Complex.exp (L z) = riemannZeta z)
    (hLd : ∀ z ∈ ball (cθ θ t) (5 / 2), HasDerivAt L (deriv riemannZeta z / riemannZeta z) z)
    {z : ℂ} (hz : ‖z - cθ θ t‖ ≤ 5 / 2 - δ) :
    ‖L z‖ ≤ (10 * (Real.log (2 * (|t| + 6)) + 1) / δ) ^ θ₂ δ := by
  set M := Real.log (2 * (|t| + 6)) with hMdef
  set B₃ := 10 * (M + 1) / δ with hB₃
  have hM0 : 0 < M := Real.log_pos (by linarith [abs_nonneg t])
  have hB₃1 : 1 ≤ B₃ := by
    rw [hB₃, le_div_iff₀ hδ]; linarith
  have hθ₂ := θ₂_bounds hδ hδ1
  have hLdiff : DifferentiableOn ℂ L (ball (cθ θ t) (5 / 2)) :=
    fun z hz => (hLd z hz).differentiableAt.differentiableWithinAt
  have hEq := L_eq_log hθ hL0 hLd
  have hin : ∀ w ∈ ball (cθ θ t) (1 / 2), ‖L w‖ ≤ 3 / 4 := by
    intro w hw
    rw [hEq hw]
    apply norm_log_zeta_le
    rw [mem_ball, dist_eq_norm] at hw
    have := Complex.abs_re_le_norm (w - cθ θ t)
    rw [sub_re, cθ_re] at this
    linarith [abs_lt.mp (lt_of_le_of_lt this hw)]
  have hLc₀ : ‖L (cθ θ t)‖ ≤ 3 / 4 := hin _ (mem_ball_self (by norm_num))
  have hout : ∀ w, ‖w - cθ θ t‖ = 5 / 2 - δ / 2 → ‖L w‖ ≤ B₃ := by
    intro w hw
    have hmem : w - cθ θ t ∈ ball (0 : ℂ) (5 / 2) := by
      rw [mem_ball_zero_iff, hw]; linarith
    have hBC := Complex.borelCaratheodory (f := fun u => L (cθ θ t + u)) (M := M) (R := 5 / 2)
      hM0 (fun u hu => by
        have : cθ θ t + u ∈ ball (cθ θ t) (5 / 2) := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact mem_ball_zero_iff.mp hu
        exact ((hLd _ this).differentiableAt.comp u
          ((differentiableAt_const _).add differentiableAt_id)).differentiableWithinAt)
      (fun u hu => by
        have hmb : cθ θ t + u ∈ ball (cθ θ t) (5 / 2) := by
          rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact mem_ball_zero_iff.mp hu
        show (L (cθ θ t + u)).re ≤ M
        have hre : (L (cθ θ t + u)).re = Real.log ‖riemannZeta (cθ θ t + u)‖ := by
          rw [← hLe _ hmb, Complex.norm_exp, Real.log_exp]
        rw [hre, hMdef]
        have hne := hZ _ (bola_props hθ hθ1 ht hmb).1
        exact Real.log_le_log (norm_pos_iff.mpr hne) (norm_zeta_le_bola hθ hθ1 ht hmb))
      (by norm_num) hmem
    simp only [add_sub_cancel, add_zero] at hBC
    rw [hw] at hBC
    have hden : (5 / 2 : ℝ) - (5 / 2 - δ / 2) = δ / 2 := by ring
    rw [hden] at hBC
    refine hBC.trans ?_
    rw [hB₃]
    have h1 : 2 * M * (5 / 2 - δ / 2) / (δ / 2) ≤ 10 * M / δ := by
      rw [div_le_div_iff₀ (by positivity) hδ]; nlinarith [mul_pos hM0 (mul_pos hδ hδ)]
    have h2 : ‖L (cθ θ t)‖ * (5 / 2 + (5 / 2 - δ / 2)) / (δ / 2) ≤ 10 / δ := by
      rw [div_le_div_iff₀ (by positivity) hδ]
      have hk : ‖L (cθ θ t)‖ * ((5 / 2 + (5 / 2 - δ / 2)) * δ) ≤
          3 / 4 * ((5 / 2 + (5 / 2 - δ / 2)) * δ) :=
        mul_le_mul_of_nonneg_right hLc₀ (by nlinarith)
      nlinarith
    calc 2 * M * (5 / 2 - δ / 2) / (δ / 2) + ‖L (cθ θ t)‖ * (5 / 2 + (5 / 2 - δ / 2)) / (δ / 2)
        ≤ 10 * M / δ + 10 / δ := add_le_add h1 h2
      _ = 10 * (M + 1) / δ := by ring
  rcases lt_or_ge ‖z - cθ θ t‖ (1 / 4) with hz4 | hz4
  · have hzb : z ∈ ball (cθ θ t) (1 / 2) := by
      rw [mem_ball, dist_eq_norm]; linarith
    calc ‖L z‖ ≤ 3 / 4 := hin z hzb
      _ ≤ 1 := by norm_num
      _ ≤ B₃ ^ θ₂ δ := Real.one_le_rpow hB₃1 hθ₂.1
  · have h3 := tres_circulos (L := L) (c := cθ θ t) (R := 5 / 2) (r₁ := 1 / 4)
      (r₃ := 5 / 2 - δ / 2) (by norm_num) (by linarith) (by linarith) hLdiff (a := 1) (b := B₃)
      (fun w hw => by
        have : w ∈ ball (cθ θ t) (1 / 2) := by rw [mem_ball, dist_eq_norm, hw]; norm_num
        linarith [hin w this])
      hout hz4 (by linarith)
    rw [Real.one_rpow, one_mul] at h3
    refine h3.trans (Real.rpow_le_rpow_of_exponent_le hB₃1 ?_)
    unfold θ₂
    have hden : 0 < Real.log (5 / 2 - δ / 2) - Real.log (1 / 4) := by
      have := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 4) (by linarith : (1 / 4 : ℝ) < 5 / 2 - δ / 2)
      linarith
    rw [div_le_div_iff_of_pos_right hden]
    have := Real.log_le_log (by linarith) hz
    linarith

/-- O passo de Young comum: `exp((10(M + 1)/δ)^{θ₂(δ)}) ≤ e^{η+K} 12^η (1 + |t|)^η`. -/
theorem exp_young {δ η K t : ℝ} (hδ : 0 < δ) (hη : 0 < η) (_hθ : 0 ≤ θ₂ δ)
    (hK : ∀ x : ℝ, 0 ≤ x → (10 / δ) ^ θ₂ δ * x ^ θ₂ δ ≤ η * x + K) :
    Real.exp ((10 * (Real.log (2 * (|t| + 6)) + 1) / δ) ^ θ₂ δ) ≤
      Real.exp (η + K) * (12 ^ η * (1 + |t|) ^ η) := by
  set M := Real.log (2 * (|t| + 6)) with hM
  have hM0 : 0 ≤ M := (Real.log_pos (by linarith [abs_nonneg t])).le
  have hsplit : (10 * (M + 1) / δ) ^ θ₂ δ = (10 / δ) ^ θ₂ δ * (M + 1) ^ θ₂ δ := by
    rw [show 10 * (M + 1) / δ = (10 / δ) * (M + 1) by ring, Real.mul_rpow (by positivity) (by linarith)]
  have hY := hK (M + 1) (by linarith)
  have hexpM : Real.exp (η * M) = (2 * (|t| + 6)) ^ η := by
    rw [Real.rpow_def_of_pos (by positivity), hM, mul_comm]
  have hpow : (2 * (|t| + 6)) ^ η ≤ 12 ^ η * (1 + |t|) ^ η := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith [abs_nonneg t]) hη.le
  calc Real.exp ((10 * (M + 1) / δ) ^ θ₂ δ) ≤ Real.exp (η * (M + 1) + K) := by
        rw [hsplit]; exact Real.exp_le_exp.mpr hY
    _ = Real.exp (η + K) * Real.exp (η * M) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (η + K) * (12 ^ η * (1 + |t|) ^ η) := by rw [hexpM]; gcongr

/-! ## 3. As cotas de `1/ζ` e de `ζ′/ζ + ζ` em `Re s ≥ θ + δ` -/

/-- O compacto `θ + δ ≤ Re s ≤ 5/2`, `|Im s| ≤ 4`. -/
theorem compacto {θ δ : ℝ} (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    IsCompact ({s : ℂ | θ + δ ≤ s.re} ∩ {s : ℂ | s.re ≤ 5 / 2} ∩ {s : ℂ | |s.im| ≤ 4}) := by
  refine (isCompact_closedBall (0 : ℂ) 10).of_isClosed_subset ?_ ?_
  · exact ((isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const)).inter
      (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
  · rintro s ⟨⟨h1, h2⟩, h3⟩
    simp only [mem_ofPred_eq] at h1 h2 h3
    rw [mem_closedBall, dist_zero_right]
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 3 + 4 := by
          gcongr
          rw [abs_le]; constructor <;> linarith
      _ ≤ 10 := by norm_num

/-- **Sob `SemZeros θ`**: `|1/ζ(s)| ≤ C(1 + |Im s|)^η` em `Re s ≥ θ + δ` (`F = (s − 1)/ζ₁`). -/
theorem norm_F_le {θ : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) {δ η : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hη : 0 < η) :
    ∃ C, 0 < C ∧ ∀ s : ℂ, θ + δ ≤ s.re → ‖F s‖ ≤ C * (1 + |s.im|) ^ η := by
  have hθ₂ := θ₂_bounds hδ hδ1
  obtain ⟨K, hK⟩ := young (A := (10 / δ) ^ θ₂ δ) (θ := θ₂ δ) (η := η)
    (Real.rpow_nonneg (by positivity) _) hθ₂.1 hθ₂.2 hη
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = Real.exp (η + K) * 12 ^ η := ⟨_, rfl⟩
  have hFc : ContinuousOn F ({s : ℂ | θ + δ ≤ s.re} ∩ {s : ℂ | s.re ≤ 5 / 2} ∩ {s : ℂ | |s.im| ≤ 4}) :=
    fun s hs => (differentiableAt_F hZ (by
      have := hs.1.1; simp only [mem_ofPred_eq] at this; linarith)).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := (compacto (by linarith) hδ).exists_bound_of_continuousOn hFc
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (max 2 C₀) C₁ + 1 := ⟨_, rfl⟩
  have hC2 : 2 ≤ C := by
    have := le_max_left (max 2 C₀) C₁; have := le_max_left 2 C₀; linarith
  have hCC₀ : C₀ ≤ C := by
    have := le_max_left (max 2 C₀) C₁; have := le_max_right 2 C₀; linarith
  have hCC₁ : C₁ ≤ C := by have := le_max_right (max 2 C₀) C₁; linarith
  have hCpos : 0 < C := by linarith
  refine ⟨C, hCpos, fun s hs => ?_⟩
  have h1 : 1 ≤ (1 + |s.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hη.le
  have hCle : ∀ x, x ≤ C → x ≤ C * (1 + |s.im|) ^ η := fun x hx =>
    hx.trans (le_mul_of_one_le_right hCpos.le h1)
  rcases le_or_gt (5 / 2) s.re with h52 | h52
  · have hs1 : s ≠ 1 := by intro h; rw [h, one_re] at h52; norm_num at h52
    rw [F_eq hs1]
    exact hCle _ ((norm_inv_zeta_le_two h52).trans hC2)
  rcases le_or_gt |s.im| 4 with h4 | h4
  · exact hCle _ ((hC₀ s ⟨⟨hs, h52.le⟩, h4⟩).trans hCC₀)
  · set t := s.im with htdef
    have ht : 4 ≤ |t| := h4.le
    obtain ⟨L, hL0, hLe, hLd⟩ := existe_log_zeta hZ hθ hθ1 ht
    have hsc : s - cθ θ t = ((s.re - (5 / 2 + θ) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [cθ, htdef]
    have hz : ‖s - cθ θ t‖ ≤ 5 / 2 - δ := by
      rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith
    have hsmem : s ∈ ball (cθ θ t) (5 / 2) := by
      rw [mem_ball, dist_eq_norm]; linarith
    have hLs := norm_L_le hZ hθ hθ1 ht hδ hδ1 hL0 hLe hLd hz
    have hs1 : s ≠ 1 := by
      intro h
      have h0 : t = 0 := by rw [htdef, h, one_im]
      rw [h0, abs_zero] at h4
      norm_num at h4
    rw [F_eq hs1, ← hLe s hsmem, ← Complex.exp_neg, Complex.norm_exp, neg_re]
    calc Real.exp (-(L s).re) ≤ Real.exp ‖L s‖ := by
          apply Real.exp_le_exp.mpr
          have := Complex.abs_re_le_norm (L s)
          linarith [neg_abs_le (L s).re]
      _ ≤ Real.exp ((10 * (Real.log (2 * (|t| + 6)) + 1) / δ) ^ θ₂ δ) := Real.exp_le_exp.mpr hLs
      _ ≤ Real.exp (η + K) * (12 ^ η * (1 + |t|) ^ η) := exp_young hδ hη hθ₂.1 hK
      _ = C₁ * (1 + |t|) ^ η := by rw [hC₁]; ring
      _ ≤ C * (1 + |t|) ^ η := by gcongr

/-- **Sob `SemZeros θ`**: `|ζ′/ζ(s) + ζ(s)| ≤ C(1 + |Im s|)^η` em `Re s ≥ θ + δ`. -/
theorem norm_H_le {θ : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) {δ η : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hη : 0 < η) :
    ∃ C, 0 < C ∧ ∀ s : ℂ, θ + δ ≤ s.re → ‖Hf s‖ ≤ C * (1 + |s.im|) ^ η := by
  have hδ2 : 0 < δ / 2 := by linarith
  have hθ₂ := θ₂_bounds hδ2 (by linarith : δ / 2 ≤ 1)
  obtain ⟨K, hK⟩ := young (A := (10 / (δ / 2)) ^ θ₂ (δ / 2)) (θ := θ₂ (δ / 2)) (η := η)
    (Real.rpow_nonneg (by positivity) _) hθ₂.1 hθ₂.2 hη
  obtain ⟨A, hA⟩ := norm_logDeriv_le_dois
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : ℝ, C₁ = (2 / δ + 1) * (Real.exp (η + K) * 12 ^ η) := ⟨_, rfl⟩
  have hHc : ContinuousOn Hf ({s : ℂ | θ + δ ≤ s.re} ∩ {s : ℂ | s.re ≤ 5 / 2} ∩ {s : ℂ | |s.im| ≤ 4}) :=
    fun s hs => (differentiableAt_Hf hZ (by
      have := hs.1.1; simp only [mem_ofPred_eq] at this; linarith)).continuousAt.continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := (compacto (by linarith) hδ).exists_bound_of_continuousOn hHc
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (max (A + 3 / 2) C₀) C₁ + 1 := ⟨_, rfl⟩
  have hCA : A + 3 / 2 ≤ C := by
    have := le_max_left (max (A + 3 / 2) C₀) C₁; have := le_max_left (A + 3 / 2) C₀; linarith
  have hCC₀ : C₀ ≤ C := by
    have := le_max_left (max (A + 3 / 2) C₀) C₁; have := le_max_right (A + 3 / 2) C₀; linarith
  have hCC₁ : C₁ ≤ C := by have := le_max_right (max (A + 3 / 2) C₀) C₁; linarith
  have hC₁0 : 0 < C₁ := by rw [hC₁]; positivity
  have hCpos : 0 < C := by linarith
  refine ⟨C, hCpos, fun s hs => ?_⟩
  have h1 : 1 ≤ (1 + |s.im|) ^ η := Real.one_le_rpow (by linarith [abs_nonneg s.im]) hη.le
  have hCle : ∀ x, x ≤ C → x ≤ C * (1 + |s.im|) ^ η := fun x hx =>
    hx.trans (le_mul_of_one_le_right hCpos.le h1)
  rcases le_or_gt (5 / 2) s.re with h52 | h52
  · have hs1 : s ≠ 1 := by intro h; rw [h, one_re] at h52; norm_num at h52
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by linarith)
    rw [Hf_eq hs1 hz]
    have hζ : ‖riemannZeta s‖ ≤ 3 / 2 := by
      have := norm_zeta_sub_one_le h52
      calc ‖riemannZeta s‖ = ‖(riemannZeta s - 1) + 1‖ := by ring_nf
        _ ≤ ‖riemannZeta s - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ 3 / 2 := by rw [norm_one]; linarith
    refine hCle _ ((norm_sub_le _ _).trans ?_)
    rw [norm_neg]
    have := hA s (by linarith)
    linarith
  rcases le_or_gt |s.im| 4 with h4 | h4
  · exact hCle _ ((hC₀ s ⟨⟨hs, h52.le⟩, h4⟩).trans hCC₀)
  · set t := s.im with htdef
    have ht : 4 ≤ |t| := h4.le
    obtain ⟨L, hL0, hLe, hLd⟩ := existe_log_zeta hZ hθ hθ1 ht
    have hsc : s - cθ θ t = ((s.re - (5 / 2 + θ) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [cθ, htdef]
    have hz : ‖s - cθ θ t‖ ≤ 5 / 2 - δ := by
      rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      linarith
    have hsmem : s ∈ ball (cθ θ t) (5 / 2) := by
      rw [mem_ball, dist_eq_norm]; linarith
    obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, Λ = (10 * (Real.log (2 * (|t| + 6)) + 1) / (δ / 2)) ^ θ₂ (δ / 2) := ⟨_, rfl⟩
    have hLb : ∀ z, ‖z - cθ θ t‖ ≤ 5 / 2 - δ / 2 → ‖L z‖ ≤ Λ := fun z hz' => by
      rw [hΛ]
      exact norm_L_le hZ hθ hθ1 ht hδ2 (by linarith) hL0 hLe hLd hz'
    have hdiffL : DifferentiableOn ℂ L (ball (cθ θ t) (5 / 2)) :=
      fun z hz' => (hLd z hz').differentiableAt.differentiableWithinAt
    have hcl : closedBall s (δ / 2) ⊆ ball (cθ θ t) (5 / 2) := by
      intro z hz'
      rw [mem_closedBall, dist_eq_norm] at hz'
      rw [mem_ball, dist_eq_norm]
      calc ‖z - cθ θ t‖ = ‖(z - s) + (s - cθ θ t)‖ := by ring_nf
        _ ≤ ‖z - s‖ + ‖s - cθ θ t‖ := norm_add_le _ _
        _ < 5 / 2 := by linarith
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ2 (hdiffL.diffContOnCl_ball hcl)
      (C := Λ) (fun z hz' => hLb z (by
        rw [mem_sphere, dist_eq_norm] at hz'
        calc ‖z - cθ θ t‖ = ‖(z - s) + (s - cθ θ t)‖ := by ring_nf
          _ ≤ ‖z - s‖ + ‖s - cθ θ t‖ := norm_add_le _ _
          _ ≤ 5 / 2 - δ / 2 := by linarith))
    have hderiv : deriv L s = logDeriv riemannZeta s := by
      rw [(hLd s hsmem).deriv, logDeriv_apply]
    rw [hderiv] at hcauchy
    have hs1 : s ≠ 1 := by
      intro h
      have h0 : t = 0 := by rw [htdef, h, one_im]
      rw [h0, abs_zero] at h4
      norm_num at h4
    have hzs : riemannZeta s ≠ 0 := hZ s (by linarith)
    have hLs : ‖L s‖ ≤ Λ := hLb s (by linarith)
    have hζ : ‖riemannZeta s‖ ≤ Real.exp Λ := by
      rw [← hLe s hsmem, Complex.norm_exp]
      exact Real.exp_le_exp.mpr ((Complex.re_le_norm (L s)).trans hLs)
    have hld : ‖logDeriv riemannZeta s‖ ≤ 2 / δ * Real.exp Λ := by
      refine hcauchy.trans ?_
      rw [div_le_iff₀ hδ2]
      have e : 2 / δ * Real.exp Λ * (δ / 2) = Real.exp Λ := by field_simp
      linarith [Real.add_one_le_exp Λ]
    have hH : ‖Hf s‖ ≤ (2 / δ + 1) * Real.exp Λ := by
      rw [Hf_eq hs1 hzs]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_neg]
      linarith
    have hexp : Real.exp Λ ≤ Real.exp (η + K) * (12 ^ η * (1 + |t|) ^ η) := by
      rw [hΛ]; exact exp_young hδ2 hη hθ₂.1 hK
    calc ‖Hf s‖ ≤ (2 / δ + 1) * Real.exp Λ := hH
      _ ≤ (2 / δ + 1) * (Real.exp (η + K) * (12 ^ η * (1 + |t|) ^ η)) := by gcongr
      _ = C₁ * (1 + |t|) ^ η := by rw [hC₁]; ring
      _ ≤ C * (1 + |t|) ^ η := by gcongr

/-! ## 4. Os coeficientes deslocados -/

/-- `a(n)/n^δ` (e `0` em `n = 0`). -/
noncomputable def escala (a : ℕ → ℂ) (δ : ℝ) (n : ℕ) : ℂ := a n / (((n : ℝ) ^ δ : ℝ) : ℂ)

theorem norm_escala_le {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    ‖escala a δ n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [escala, Real.zero_rpow hδ.ne']
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hp : 1 ≤ (n : ℝ) ^ δ := Real.one_le_rpow hn1 hδ.le
    unfold escala
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), div_le_one (by linarith)]
    exact (ha n).trans hp

theorem term_escala (a : ℕ → ℂ) (δ : ℝ) (u : ℂ) (n : ℕ) :
    LSeries.term (escala a δ) u n = LSeries.term a (u + δ) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, cpow_add _ _ hnc]
    have e : (((n : ℝ) ^ δ : ℝ) : ℂ) = (n : ℂ) ^ (δ : ℂ) := by
      rw [ofReal_cpow (Nat.cast_nonneg n)]; push_cast; ring
    have h1 : (n : ℂ) ^ (δ : ℂ) ≠ 0 := fun h => hnc ((cpow_eq_zero_iff _ _).mp h).1
    have h2 : (n : ℂ) ^ u ≠ 0 := fun h => hnc ((cpow_eq_zero_iff _ _).mp h).1
    unfold escala
    rw [e]
    field_simp

theorem LSeries_escala (a : ℕ → ℂ) (δ : ℝ) (u : ℂ) : LSeries (escala a δ) u = LSeries a (u + δ) := by
  unfold LSeries
  simp_rw [term_escala]

/-- **Littlewood deslocado**: se `|a(n)| ≤ 1`, `L(a, v) = Φ(v)` em `Re v > 1`, `Φ` é holomorfa em `Re v > θ` e
`|Φ(v)| ≤ C(1 + |Im v|)^{ε/16}` em `Re v ≥ θ + ε/2`, então as somas parciais de `Σ a(n)n^{−σ}` são limitadas para
`σ = θ + ε + δ` (`0 < ε ≤ 1`, `δ > 0`). -/
theorem somas_limitadas_gen {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ 1) {Φ : ℂ → ℂ} {θ ε δ CF : ℝ} (hθ : 1 / 2 ≤ θ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hΦd : ∀ v : ℂ, θ < v.re → DifferentiableAt ℂ Φ v)
    (hΦL : ∀ v : ℂ, 1 < v.re → LSeries a v = Φ v) (hCF0 : 0 ≤ CF)
    (hCF : ∀ v : ℂ, θ + ε / 2 ≤ v.re → ‖Φ v‖ ≤ CF * (1 + |v.im|) ^ (ε / 16)) :
    ∃ B : ℝ, ∀ N : ℕ, ‖∑ n ∈ Finset.range (N + 1), LSeries.term a ((θ + ε + δ : ℝ) : ℂ) n‖ ≤ B := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = θ - 1 / 2 + δ := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; linarith
  have hΦd' : ∀ u : ℂ, 1 / 2 < u.re → DifferentiableAt ℂ (fun u => Φ (u + d)) u := by
    intro u hu
    have hre : θ < (u + (d : ℂ)).re := by simp; rw [hd]; linarith
    exact (hΦd _ hre).comp u (differentiableAt_id.add_const _)
  have hΦL' : ∀ u : ℂ, 1 < u.re → LSeries (escala a d) u = (fun u => Φ (u + d)) u := by
    intro u hu
    have hre : 1 < (u + (d : ℂ)).re := by simp; linarith
    rw [LSeries_escala, hΦL _ hre]
  have hCF' : ∀ u : ℂ, 1 / 2 + ε / 2 ≤ u.re → ‖(fun u => Φ (u + d)) u‖ ≤ CF * (1 + |u.im|) ^ (ε / 16) := by
    intro u hu
    have hre : θ + ε / 2 ≤ (u + (d : ℂ)).re := by simp; rw [hd]; linarith
    have h := hCF _ hre
    have him : (u + (d : ℂ)).im = u.im := by simp
    rw [him] at h
    exact h
  obtain ⟨K, hK0, hK⟩ := cota_gen (norm_escala_le ha hd0) hΦd' hΦL' hε hε1 hCF0 hCF'
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = ((1 / 2 + ε : ℝ) : ℂ) := ⟨_, rfl⟩
  have hwre : w.re = 1 / 2 + ε := by rw [hw, ofReal_re]
  have hwim : w.im = 0 := by rw [hw, ofReal_im]
  refine ⟨‖Φ (w + d)‖ + K, fun N => ?_⟩
  have e : ∑ n ∈ Finset.range (N + 1), LSeries.term a ((θ + ε + δ : ℝ) : ℂ) n =
      ∑ n ∈ Finset.range (N + 1), LSeries.term (escala a d) w n := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [term_escala, hw, hd]
    congr 1
    push_cast
    ring
  rw [e]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [zero_add, Finset.range_one, Finset.sum_singleton, LSeries.term_zero, norm_zero]
    positivity
  · have h := hK w hwre N hN
    have hx1 := xN_ge_um hN
    have hxle : xN N ^ (-(ε / 4)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    rw [hwim, abs_zero, add_zero, Real.one_rpow, one_mul] at h
    have h' : ‖∑ n ∈ Finset.range (N + 1), LSeries.term (escala a d) w n - Φ (w + d)‖ ≤ K :=
      h.trans (by nlinarith)
    calc ‖∑ n ∈ Finset.range (N + 1), LSeries.term (escala a d) w n‖
        = ‖(∑ n ∈ Finset.range (N + 1), LSeries.term (escala a d) w n - Φ (w + d)) + Φ (w + d)‖ := by
          ring_nf
      _ ≤ ‖∑ n ∈ Finset.range (N + 1), LSeries.term (escala a d) w n - Φ (w + d)‖ + ‖Φ (w + d)‖ :=
          norm_add_le _ _
      _ ≤ ‖Φ (w + d)‖ + K := by linarith

/-! ## 5. Quasi-RH ⟹ as cotas de `ψ` e de `M` -/

/-- Reduzir `ε > 0` a `0 < ε ≤ 1`. -/
theorem reduz {θ : ℝ} {A : ℕ → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C : ℝ, ∀ N : ℕ, |A N| ≤ C * ((N : ℝ) + 1) ^ (θ + ε)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |A N| ≤ C * ((N : ℝ) + 1) ^ (θ + ε) := by
  intro ε hε
  rcases le_or_gt ε 1 with h1 | h1
  · exact h ε hε h1
  · obtain ⟨C, hC⟩ := h 1 one_pos le_rfl
    have hC0 : 0 ≤ C := by
      have := hC 0
      simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one] at this
      exact le_trans (abs_nonneg _) this
    refine ⟨C, fun N => (hC N).trans ?_⟩
    have hN : (1 : ℝ) ≤ (N : ℝ) + 1 := by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) hC0

/-- **`ζ ≠ 0` em `Re s > θ` ⟹ `ψ(N) = N + O((N + 1)^{θ+ε})`** (`½ ≤ θ < 1`). -/
theorem psi_of_semZeros {θ : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |Chebyshev.psi N - N| ≤ C * ((N : ℝ) + 1) ^ (θ + ε) := by
  refine reduz (A := fun N => Chebyshev.psi N - N) fun ε hε hε1 => ?_
  -- a série `f = (Λ − 1)/((1/δ₀ + 1)n^{δ₀})` com `δ₀ = ε/8`
  have hδ0 : 0 < ε / 8 := by linarith
  have hB0 : (0 : ℝ) < 1 / (ε / 8) + 1 := by positivity
  obtain ⟨CH, hCH0, hCH⟩ := norm_H_le hZ hθ hθ1 (δ := ε / 4) (η := ε / 2 / 16) (by linarith) (by linarith)
    (by linarith)
  have hΦd : ∀ v : ℂ, θ < v.re → DifferentiableAt ℂ
      (fun v => ((1 / (ε / 8) + 1 : ℝ) : ℂ)⁻¹ * Hf (v + ((ε / 8 : ℝ) : ℂ))) v := by
    intro v hv
    have hre : θ < (v + ((ε / 8 : ℝ) : ℂ)).re := by simp; linarith
    exact (differentiableAt_const _).mul ((differentiableAt_Hf hZ hre).comp v (differentiableAt_id.add_const _))
  have hΦL : ∀ v : ℂ, 1 < v.re → LSeries (fco (ε / 8)) v =
      (fun v => ((1 / (ε / 8) + 1 : ℝ) : ℂ)⁻¹ * Hf (v + ((ε / 8 : ℝ) : ℂ))) v :=
    fun v hv => LSeries_fco hδ0 hv
  have hCF : ∀ v : ℂ, θ + ε / 2 / 2 ≤ v.re →
      ‖(fun v => ((1 / (ε / 8) + 1 : ℝ) : ℂ)⁻¹ * Hf (v + ((ε / 8 : ℝ) : ℂ))) v‖ ≤
        CH / (1 / (ε / 8) + 1) * (1 + |v.im|) ^ (ε / 2 / 16) := by
    intro v hv
    have hre : θ + ε / 4 ≤ (v + ((ε / 8 : ℝ) : ℂ)).re := by simp; linarith
    have h := hCH _ hre
    have him : (v + ((ε / 8 : ℝ) : ℂ)).im = v.im := by simp
    rw [him] at h
    simp only
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB0]
    calc (1 / (ε / 8) + 1)⁻¹ * ‖Hf (v + ((ε / 8 : ℝ) : ℂ))‖ ≤
          (1 / (ε / 8) + 1)⁻¹ * (CH * (1 + |v.im|) ^ (ε / 2 / 16)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = CH / (1 / (ε / 8) + 1) * (1 + |v.im|) ^ (ε / 2 / 16) := by ring
  obtain ⟨B, hB⟩ := somas_limitadas_gen (norm_fco_le hδ0) (θ := θ) (ε := ε / 2) (δ := ε / 8) hθ
    (by linarith) (by linarith) hδ0 hΦd hΦL (by positivity) hCF
  -- de `fco` para `Λ − 1`, com `σ = θ + ε/2 + ε/8 + ε/8`
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = θ + ε / 2 + ε / 8 + ε / 8 := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  have hBσ : ∀ N : ℕ, ‖∑ n ∈ Finset.range (N + 1), LSeries.term cL (σ : ℂ) n‖ ≤ (1 / (ε / 8) + 1) * B := by
    intro N
    have e : ∑ n ∈ Finset.range (N + 1), LSeries.term cL (σ : ℂ) n =
        ((1 / (ε / 8) + 1 : ℝ) : ℂ) *
          ∑ n ∈ Finset.range (N + 1), LSeries.term (fco (ε / 8)) ((θ + ε / 2 + ε / 8 : ℝ) : ℂ) n := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hBc : ((1 / (ε / 8) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hB0.ne'
      rw [term_fco hδ0, ← mul_assoc, mul_inv_cancel₀ hBc, one_mul, hσ]
      congr 1
      push_cast
      ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB0]
    exact mul_le_mul_of_nonneg_left (hB N) hB0.le
  have hB1 : 0 ≤ (1 / (ε / 8) + 1) * B := le_trans (norm_nonneg _) (hBσ 0)
  refine ⟨2 * ((1 / (ε / 8) + 1) * B), fun N => ?_⟩
  have hn := congrArg norm (E_eq_sum σ N)
  rw [Complex.norm_real, Real.norm_eq_abs] at hn
  have h1 : |E N| ≤ 2 * ((1 / (ε / 8) + 1) * B) * (N : ℝ) ^ σ := by rw [hn]; exact abel_cota hσ0 hBσ N
  have hEN : |Chebyshev.psi N - N| = |E N| := rfl
  show |Chebyshev.psi N - N| ≤ _
  rw [hEN]
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hN0 := (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  calc (N : ℝ) ^ σ ≤ ((N : ℝ) + 1) ^ σ := Real.rpow_le_rpow hN0 (by linarith) hσ0.le
    _ ≤ ((N : ℝ) + 1) ^ (θ + ε) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hσ]; linarith)

/-- `M(N) = Σ_{n ≤ N} μ(n)n^{−σ} n^σ`. -/
theorem M_eq_sum (σ : ℝ) (N : ℕ) :
    ((ATK.ZeroClasses.Mertens.M N : ℝ) : ℂ) =
      ∑ n ∈ Finset.range (N + 1), LSeries.term mu (σ : ℂ) n * (((n : ℝ) ^ σ : ℝ) : ℂ) := by
  unfold ATK.ZeroClasses.Mertens.M
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [term_mul_rpow mu σ hn]

/-- **`ζ ≠ 0` em `Re s > θ` ⟹ `M(N) = O((N + 1)^{θ+ε})`** (`½ ≤ θ < 1`). -/
theorem mertens_of_semZeros {θ : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |ATK.ZeroClasses.Mertens.M N| ≤ C * ((N : ℝ) + 1) ^ (θ + ε) := by
  refine reduz fun ε hε hε1 => ?_
  obtain ⟨CF, hCF0, hCF⟩ := norm_F_le hZ hθ hθ1 (δ := ε / 4) (η := ε / 2 / 16) (by linarith) (by linarith)
    (by linarith)
  have hFL : ∀ v : ℂ, 1 < v.re → LSeries mu v = F v := fun v hv => LSeries_mu hv
  obtain ⟨B, hB⟩ := somas_limitadas_gen norm_mu_le (Φ := F) (θ := θ) (ε := ε / 2) (δ := ε / 4) hθ
    (by linarith) (by linarith) (by linarith) (fun v hv => differentiableAt_F hZ hv) hFL hCF0.le
    (fun v hv => hCF v (by linarith))
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = θ + ε / 2 + ε / 4 := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  have hBσ : ∀ N : ℕ, ‖∑ n ∈ Finset.range (N + 1), LSeries.term mu (σ : ℂ) n‖ ≤ B := by
    intro N; rw [hσ]; exact hB N
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hBσ 0)
  refine ⟨2 * B, fun N => ?_⟩
  have hn := congrArg norm (M_eq_sum σ N)
  rw [Complex.norm_real, Real.norm_eq_abs] at hn
  have h1 : |ATK.ZeroClasses.Mertens.M N| ≤ 2 * B * (N : ℝ) ^ σ := by rw [hn]; exact abel_cota hσ0 hBσ N
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hN0 := (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  calc (N : ℝ) ^ σ ≤ ((N : ℝ) + 1) ^ σ := Real.rpow_le_rpow hN0 (by linarith) hσ0.le
    _ ≤ ((N : ℝ) + 1) ^ (θ + ε) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hσ]; linarith)

/-! ## 6. As equivalências -/

/-- **Quasi-RH ⟺ erro de `ψ`**: `ζ ≠ 0` em `Re s > θ` ⟺ `ψ(N) = N + O((N + 1)^{θ+ε})` para todo `ε > 0`. -/
theorem semZeros_iff_psi {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    SemZeros θ ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ,
      |Chebyshev.psi N - N| ≤ C * ((N : ℝ) + 1) ^ (θ + ε) := by
  refine ⟨fun hZ => psi_of_semZeros hZ hθ hθ1, fun h s hs => ?_⟩
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  obtain ⟨C, hC⟩ := h ((s.re - θ) / 2) (by linarith)
  exact zeroFree_of_psi (θ := θ + (s.re - θ) / 2) (by linarith) (by linarith) hC (by linarith)

/-- **Quasi-RH ⟺ cota de Mertens**: `ζ ≠ 0` em `Re s > θ` ⟺ `M(N) = O((N + 1)^{θ+ε})` para todo `ε > 0`. -/
theorem semZeros_iff_mertens {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    SemZeros θ ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ,
      |ATK.ZeroClasses.Mertens.M N| ≤ C * ((N : ℝ) + 1) ^ (θ + ε) := by
  refine ⟨fun hZ => mertens_of_semZeros hZ hθ hθ1, fun h s hs => ?_⟩
  rcases le_or_gt 1 s.re with h1 | h1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  obtain ⟨C, hC⟩ := h ((s.re - θ) / 2) (by linarith)
  exact zeroFree_of_mertens (θ := θ + (s.re - θ) / 2) (by linarith) (by linarith) hC (by linarith)

/-- As cotas de `ψ` e de `M` com o mesmo expoente `θ + ε` são equivalentes (`½ ≤ θ < 1`). -/
theorem psi_iff_mertens {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |Chebyshev.psi N - N| ≤ C * ((N : ℝ) + 1) ^ (θ + ε)) ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |ATK.ZeroClasses.Mertens.M N| ≤ C * ((N : ℝ) + 1) ^ (θ + ε) :=
  (semZeros_iff_psi hθ hθ1).symm.trans (semZeros_iff_mertens hθ hθ1)

/-- `SemZeros ½ ⟺ RH`. -/
theorem semZeros_meio_iff : SemZeros (1 / 2) ↔ RiemannHypothesis :=
  ⟨fun hZ => ATK.BaezDuarteBridge.riemannHypothesis_of_strip fun s hs1 _ => hZ s hs1,
    fun hRH _s hs => ATK.RHLogZeta.zeta_ne_zero_of_RH hRH hs⟩

end ATK.ZeroClasses.QuasiRH

#print axioms ATK.ZeroClasses.QuasiRH.zeta₁_ne_zero
#print axioms ATK.ZeroClasses.QuasiRH.differentiableAt_F
#print axioms ATK.ZeroClasses.QuasiRH.differentiableAt_Hf
#print axioms ATK.ZeroClasses.QuasiRH.cθ_re
#print axioms ATK.ZeroClasses.QuasiRH.cθ_im
#print axioms ATK.ZeroClasses.QuasiRH.bola_props
#print axioms ATK.ZeroClasses.QuasiRH.norm_zeta_le_bola
#print axioms ATK.ZeroClasses.QuasiRH.log_zeta_cθ
#print axioms ATK.ZeroClasses.QuasiRH.existe_log_zeta
#print axioms ATK.ZeroClasses.QuasiRH.L_eq_log
#print axioms ATK.ZeroClasses.QuasiRH.norm_L_le
#print axioms ATK.ZeroClasses.QuasiRH.exp_young
#print axioms ATK.ZeroClasses.QuasiRH.compacto
#print axioms ATK.ZeroClasses.QuasiRH.norm_F_le
#print axioms ATK.ZeroClasses.QuasiRH.norm_H_le
#print axioms ATK.ZeroClasses.QuasiRH.norm_escala_le
#print axioms ATK.ZeroClasses.QuasiRH.term_escala
#print axioms ATK.ZeroClasses.QuasiRH.LSeries_escala
#print axioms ATK.ZeroClasses.QuasiRH.somas_limitadas_gen
#print axioms ATK.ZeroClasses.QuasiRH.reduz
#print axioms ATK.ZeroClasses.QuasiRH.psi_of_semZeros
#print axioms ATK.ZeroClasses.QuasiRH.M_eq_sum
#print axioms ATK.ZeroClasses.QuasiRH.mertens_of_semZeros
#print axioms ATK.ZeroClasses.QuasiRH.semZeros_iff_psi
#print axioms ATK.ZeroClasses.QuasiRH.semZeros_iff_mertens
#print axioms ATK.ZeroClasses.QuasiRH.psi_iff_mertens
#print axioms ATK.ZeroClasses.QuasiRH.semZeros_meio_iff
