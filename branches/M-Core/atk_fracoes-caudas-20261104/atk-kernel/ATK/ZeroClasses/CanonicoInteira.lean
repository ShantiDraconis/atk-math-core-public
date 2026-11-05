import ATK.ZeroClasses.Canonico
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# O produto canônico é inteiro, tem exatamente os zeros de `ξ` e cresce no máximo como `e^{C|s|^{3/2}}`
(rodada 32)

A rodada 31 provou que `P(s) = ∏_{(ρ, j)} (1 − s/ρ)e^{s/ρ}` converge para cada `s`. Aqui:

* **`Σ_ρ m_ρ/|ρ|^p < ∞` para todo `p > 1`** (`soma_ordem_inv_pot`, `summable_ZM_pot`), pelo mesmo argumento de
  blocos da rodada 31, com comparação a `n^{−(p+1)/2}`;
* **cotas do fator** (`E1_eq_zero_iff`, `norm_E1_le`): `E1 z = 0 ⟺ z = 1` e `‖E1 z‖ ≤ e^{3‖z‖^{3/2}}`;
* **produtos gerais** `∏'_i E1(z/r_i)` com `r_i ≠ 0` e `Σ 1/|r_i|² < ∞`: convergência uniforme em bolas
  (`prodE_tendstoUniformlyOn`, via `hasProdUniformlyOn_one_add`), **inteiro** (`prodE_differentiable`, limite
  localmente uniforme de funções holomorfas), **não nulo** fora dos `r_i` (`prodE_ne_zero`, via
  `cexp_tsum_eq_tprod`) e **`‖∏'‖ ≤ exp(3‖z‖^{3/2} Σ 1/|r_i|^{3/2})`** (`prodE_norm_le`);
* para o produto canônico dos zeros de `ζ`: `Pcan_differentiable`, `Pcan_norm_le`, `Pcan_ne_zero` fora de `Z`,
  `Pcan_fator` (`P = E1(s/ρ₀)^{m₀} · P_resto` com `P_resto(ρ₀) ≠ 0`) e **`ordem_Pcan`: `ord_ρ P = m_ρ`**;
* **os zeros de `ξ` são exatamente `Z`** (`xi_eq_zero_iff_Z`), logo **`ordem_Pcan_eq_xi`: `ord_z P = ord_z ξ` para
  todo `z ∈ ℂ`**.

Isso é tudo o que a identidade de Hadamard `ξ = e^{A+Bs} P` precisa do lado de `P`: `ξ/P` é inteira e sem zeros,
e `log|P| = O(|s|^{3/2})`. O argumento de ordem (Nevanlinna/coeficientes de Fourier) fica para a rodada seguinte:
`HadamardXi` segue BUILD_PENDING.

Classificação (rodada 32): **ferramenta**. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.CanonicoInteira

open ATK.BaseRiemannXi ATK.ZeroClasses.Canonico ATK.ZeroClasses.JensenLocal

/-! ## 1. `Σ_ρ m_ρ/|ρ|^p < ∞` para `p > 1` -/

/-- O termo de comparação dos blocos, expoente `p`. -/
noncomputable def gp (p : ℝ) (n : ℕ) : ℝ :=
  if 14 ≤ n then 4 * Lc ((n : ℝ) - 1 / 2) / ((n : ℝ) - 1) ^ p else 0

theorem gp_nonneg (p : ℝ) (n : ℕ) : 0 ≤ gp p n := by
  unfold gp
  split_ifs with h
  · have : (14 : ℝ) ≤ n := by exact_mod_cast h
    have := Lc_nonneg (t := (n : ℝ) - 1 / 2) (by linarith)
    have : 0 ≤ ((n : ℝ) - 1) ^ p := Real.rpow_nonneg (by linarith) p
    positivity
  · exact le_rfl

theorem gp_le {p : ℝ} (hp : 1 < p) (n : ℕ) :
    gp p n ≤ 4 * (3 / ((p - 1) / 2) + |Real.log (2 - π ^ 2 / 6)|) / Real.log (19 / 16) * 2 ^ p *
      ((n : ℝ) ^ ((p + 1) / 2))⁻¹ := by
  set b := 2 - π ^ 2 / 6 with hb
  have hb0 : 0 < b := ATK.BLProva.dois_menos_pos
  have hl0 : 0 < Real.log (19 / 16) := Real.log_pos (by norm_num)
  set δ := (p - 1) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  set A := |Real.log b| with hA
  have hA0 : 0 ≤ A := abs_nonneg _
  have hc0 : 0 ≤ 4 * (3 / δ + A) / Real.log (19 / 16) := by positivity
  unfold gp
  split_ifs with h
  · set x : ℝ := (n : ℝ) with hx
    have hx14 : (14 : ℝ) ≤ x := by rw [hx]; exact_mod_cast h
    have hx0 : 0 < x := by linarith
    have hr : 1 ≤ x ^ δ := Real.one_le_rpow (by linarith) hδ0.le
    have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ0
    have hcub : 15 * (x - 1 / 2) + 62 ≤ x ^ 3 := by
      have hxx : 196 ≤ x * x := by nlinarith
      have := mul_le_mul_of_nonneg_right hxx hx0.le
      nlinarith
    have hq : Real.log (15 * (x - 1 / 2) + 62) ≤ 3 * Real.log x := by
      have := Real.log_le_log (by linarith) hcub
      rw [Real.log_pow] at this
      push_cast at this
      exact this
    have hLc : Lc (x - 1 / 2) ≤ (3 / δ + A) * x ^ δ / Real.log (19 / 16) := by
      unfold Lc
      rw [← hb, Real.log_div (by linarith) hb0.ne']
      apply div_le_div_of_nonneg_right _ hl0.le
      have h1 : -Real.log b ≤ A := neg_le_abs _
      have h2 : A ≤ A * x ^ δ := le_mul_of_one_le_right hA0 hr
      have h3 : 3 * Real.log x ≤ 3 / δ * x ^ δ := by
        have : 3 * (x ^ δ / δ) = 3 / δ * x ^ δ := by ring
        nlinarith
      nlinarith
    have hp1 : x ^ δ * x ^ ((p + 1) / 2) = x ^ p := by
      rw [← Real.rpow_add hx0]
      congr 1
      rw [hδ]
      ring
    have hpos2 : 0 < x ^ ((p + 1) / 2) := Real.rpow_pos_of_pos hx0 _
    have hx1 : 0 < x - 1 := by linarith
    have hpos1 : 0 < (x - 1) ^ p := Real.rpow_pos_of_pos hx1 _
    have hden : x ^ p ≤ 2 ^ p * (x - 1) ^ p := by
      have h1 : x / 2 ≤ x - 1 := by linarith
      have h2 := Real.rpow_le_rpow (by linarith) h1 (by linarith : (0 : ℝ) ≤ p)
      rw [Real.div_rpow hx0.le (by norm_num)] at h2
      have h22 : (0 : ℝ) < 2 ^ p := Real.rpow_pos_of_pos (by norm_num) _
      rw [div_le_iff₀ h22] at h2
      linarith
    rw [← div_eq_mul_inv, div_le_div_iff₀ hpos1 hpos2]
    calc 4 * Lc (x - 1 / 2) * x ^ ((p + 1) / 2)
        ≤ 4 * ((3 / δ + A) * x ^ δ / Real.log (19 / 16)) * x ^ ((p + 1) / 2) := by gcongr
      _ = 4 * (3 / δ + A) / Real.log (19 / 16) * (x ^ δ * x ^ ((p + 1) / 2)) := by ring
      _ = 4 * (3 / δ + A) / Real.log (19 / 16) * x ^ p := by rw [hp1]
      _ ≤ 4 * (3 / δ + A) / Real.log (19 / 16) * (2 ^ p * (x - 1) ^ p) := by gcongr
      _ = 4 * (3 / δ + A) / Real.log (19 / 16) * 2 ^ p * (x - 1) ^ p := by ring
  · have : 0 ≤ ((n : ℝ) ^ ((p + 1) / 2))⁻¹ := by positivity
    have : (0 : ℝ) ≤ 2 ^ p := (Real.rpow_pos_of_pos (by norm_num) _).le
    positivity

theorem summable_gp {p : ℝ} (hp : 1 < p) : Summable (gp p) :=
  Summable.of_nonneg_of_le (gp_nonneg p) (gp_le hp)
    ((Real.summable_nat_rpow_inv.mpr (by linarith)).mul_left _)

/-- **`Σ_ρ m_ρ/|ρ|^p < ∞`** para todo `p > 1`, sobre todos os zeros da faixa. -/
theorem soma_ordem_inv_pot {p : ℝ} (hp : 1 < p) :
    Summable (fun ρ : ATK.ZetaSimetria.Z =>
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ p) := by
  classical
  have hp0 : (0 : ℝ) ≤ p := by linarith
  refine summable_of_sum_le (c := ∑' n, gp p n) (fun ρ => by
      simp only [Pi.zero_apply]
      have := Real.rpow_nonneg (norm_nonneg ((ρ : ℂ))) p
      positivity) (fun u => ?_)
  set F : ℂ → ℝ := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ p with hF
  set v := u.map (Function.Embedding.subtype (· ∈ ATK.ZetaSimetria.Z)) with hv
  have hsum : ∑ x ∈ u, (analyticOrderNatAt riemannZeta (x : ℂ) : ℝ) / ‖(x : ℂ)‖ ^ p =
      ∑ ρ ∈ v, F ρ := by
    rw [hv, Finset.sum_map]
    rfl
  have hvZ : ∀ ρ ∈ v, ρ ∈ ATK.ZetaSimetria.Z := by
    intro ρ hρ
    obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hρ
    exact a.2
  set κ : ℂ → ℕ := fun ρ => ⌈|ρ.im|⌉₊ with hκ
  have hκ1 : ∀ ρ ∈ v, ((κ ρ : ℕ) : ℝ) - 1 < |ρ.im| ∧ |ρ.im| ≤ (κ ρ : ℕ) ∧ 14 ≤ κ ρ := by
    intro ρ hρ
    have h13 := ATK.ZeroClasses.Faixa.zeros_acima_13 ρ (hvZ ρ hρ)
    have ha := Nat.ceil_lt_add_one (abs_nonneg ρ.im)
    have hb := Nat.le_ceil |ρ.im|
    refine ⟨by simp only [hκ]; linarith, hb, ?_⟩
    have : (13 : ℝ) < (κ ρ : ℕ) := by simp only [hκ]; linarith
    have : 13 < κ ρ := by exact_mod_cast this
    omega
  rw [hsum, ← Finset.sum_fiberwise_of_maps_to (fun ρ hρ => Finset.mem_image_of_mem κ hρ)]
  refine le_trans (Finset.sum_le_sum fun n hn => ?_) ((summable_gp hp).sum_le_tsum _
    (fun i _ => gp_nonneg p i))
  set W := v.filter (fun ρ => κ ρ = n) with hW
  obtain ⟨ρ₀, hρ₀, hκ₀⟩ := Finset.mem_image.mp hn
  have hn14 : 14 ≤ n := hκ₀ ▸ (hκ1 ρ₀ hρ₀).2.2
  have hn' : (14 : ℝ) ≤ n := by exact_mod_cast hn14
  have hWv : ∀ ρ ∈ W, ρ ∈ v ∧ κ ρ = n := fun ρ hρ => Finset.mem_filter.mp hρ
  have hpos1 : 0 < ((n : ℝ) - 1) ^ p := Real.rpow_pos_of_pos (by linarith) _
  have hFle : ∀ ρ ∈ W, F ρ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) / ((n : ℝ) - 1) ^ p := by
    intro ρ hρ
    obtain ⟨hρv, hκn⟩ := hWv ρ hρ
    obtain ⟨h1, _, _⟩ := hκ1 ρ hρv
    rw [hκn] at h1
    have hn1 : ((n : ℝ) - 1) ≤ ‖ρ‖ := h1.le.trans (Complex.abs_im_le_norm ρ)
    have hsq : ((n : ℝ) - 1) ^ p ≤ ‖ρ‖ ^ p := Real.rpow_le_rpow (by linarith) hn1 hp0
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos1 hsq
  have hy : 4 ≤ |(n : ℝ) - 1 / 2| := by
    rw [abs_of_pos (by linarith)]
    linarith
  have hy' : 4 ≤ |-((n : ℝ) - 1 / 2)| := by rwa [abs_neg]
  have hmais := caixa_le hy (W.filter (fun ρ => 0 < ρ.im)) (fun ρ hρ => by
    rw [Finset.mem_filter] at hρ
    obtain ⟨hρv, hκn⟩ := hWv ρ hρ.1
    obtain ⟨h1, h2, _⟩ := hκ1 ρ hρv
    rw [hκn, abs_of_pos hρ.2] at h1 h2
    have hz := hvZ ρ hρv
    exact ⟨hz.2.1, hz.2.2, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  have hmenos := caixa_le hy' (W.filter (fun ρ => ¬ 0 < ρ.im)) (fun ρ hρ => by
    rw [Finset.mem_filter] at hρ
    obtain ⟨hρv, hκn⟩ := hWv ρ hρ.1
    obtain ⟨h1, h2, _⟩ := hκ1 ρ hρv
    have h13 := ATK.ZeroClasses.Faixa.zeros_acima_13 ρ (hvZ ρ hρv)
    have hneg : ρ.im < 0 := by
      rcases lt_trichotomy ρ.im 0 with h | h | h
      · exact h
      · rw [h, abs_zero] at h13; norm_num at h13
      · exact absurd h hρ.2
    rw [hκn, abs_of_neg hneg] at h1 h2
    have hz := hvZ ρ hρv
    exact ⟨hz.2.1, hz.2.2, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  rw [abs_neg] at hmenos
  have hWs : (∑ ρ ∈ W, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ 4 * Lc ((n : ℝ) - 1 / 2) := by
    rw [← Finset.sum_filter_add_sum_filter_not W (fun ρ => 0 < ρ.im)]
    rw [abs_of_pos (by linarith : (0 : ℝ) < (n : ℝ) - 1 / 2)] at hmais hmenos
    linarith
  calc ∑ ρ ∈ v with κ ρ = n, F ρ
      ≤ ∑ ρ ∈ W, (analyticOrderNatAt riemannZeta ρ : ℝ) / ((n : ℝ) - 1) ^ p :=
        Finset.sum_le_sum hFle
    _ = (∑ ρ ∈ W, (analyticOrderNatAt riemannZeta ρ : ℝ)) / ((n : ℝ) - 1) ^ p := by
        rw [Finset.sum_div]
    _ ≤ 4 * Lc ((n : ℝ) - 1 / 2) / ((n : ℝ) - 1) ^ p :=
        div_le_div_of_nonneg_right hWs hpos1.le
    _ = gp p n := by simp [gp, hn14]

/-- `Σ_{(ρ, j)} 1/|ρ|^p < ∞` para `p > 1`. -/
theorem summable_ZM_pot {p : ℝ} (hp : 1 < p) :
    Summable (fun q : ZM => 1 / ‖((q.1 : ATK.ZetaSimetria.Z) : ℂ)‖ ^ p) := by
  rw [summable_sigma_of_nonneg (fun q => by
    have := Real.rpow_nonneg (norm_nonneg (((q.1 : ATK.ZetaSimetria.Z) : ℂ))) p
    positivity)]
  refine ⟨fun x => Summable.of_finite, ?_⟩
  convert soma_ordem_inv_pot hp using 1
  funext x
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ## 2. O fator `E1` -/

theorem E1_eq_zero_iff {z : ℂ} : E1 z = 0 ↔ z = 1 := by
  unfold E1
  rw [mul_eq_zero]
  constructor
  · rintro (h | h)
    · linear_combination -h
    · exact absurd h (Complex.exp_ne_zero z)
  · rintro rfl
    left
    ring

/-- **`‖E1 z‖ ≤ e^{3‖z‖^{3/2}}`** para todo `z`. -/
theorem norm_E1_le (z : ℂ) : ‖E1 z‖ ≤ Real.exp (3 * ‖z‖ ^ (3 / 2 : ℝ)) := by
  rcases le_or_gt ‖z‖ 1 with h | h
  · have h1 := E1_sub_one_le h
    have h2 : ‖E1 z‖ ≤ 1 + 3 * ‖z‖ ^ 2 := by
      calc ‖E1 z‖ = ‖(E1 z - 1) + 1‖ := by ring_nf
        _ ≤ ‖E1 z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 + 3 * ‖z‖ ^ 2 := by rw [norm_one]; linarith
    have h3 : ‖z‖ ^ 2 ≤ ‖z‖ ^ (3 / 2 : ℝ) := by
      rcases (norm_nonneg z).eq_or_lt with h0 | h0
      · rw [← h0]
        simp
      · rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge h0 h (by norm_num)
    calc ‖E1 z‖ ≤ 1 + 3 * ‖z‖ ^ 2 := h2
      _ ≤ Real.exp (3 * ‖z‖ ^ 2) := by linarith [Real.add_one_le_exp (3 * ‖z‖ ^ 2)]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · have e : ‖E1 z‖ = ‖1 - z‖ * Real.exp z.re := by
      unfold E1
      rw [norm_mul, Complex.norm_exp]
    have h1 : ‖1 - z‖ ≤ 1 + ‖z‖ := by
      calc ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
        _ = 1 + ‖z‖ := by rw [norm_one]
    have h2 : 1 + ‖z‖ ≤ Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
    have h3 : Real.exp z.re ≤ Real.exp ‖z‖ := Real.exp_le_exp.mpr (Complex.re_le_norm z)
    have h4 : ‖z‖ ≤ ‖z‖ ^ (3 / 2 : ℝ) := by
      conv_lhs => rw [← Real.rpow_one ‖z‖]
      exact Real.rpow_le_rpow_of_exponent_le h.le (by norm_num)
    rw [e]
    calc ‖1 - z‖ * Real.exp z.re ≤ Real.exp ‖z‖ * Real.exp ‖z‖ :=
          mul_le_mul (h1.trans h2) h3 (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (2 * ‖z‖) := by rw [← Real.exp_add]; ring_nf
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-! ## 3. Produtos `∏'_i E1(z/r_i)` -/

section Geral

variable {ι : Type*} {r : ι → ℂ}

theorem eventualmente_longe (hr0 : ∀ i, r i ≠ 0) (hs : Summable (fun i => 1 / ‖r i‖ ^ 2))
    {R : ℝ} (hR : 0 < R) : ∀ᶠ i in cofinite, R ≤ ‖r i‖ := by
  have h := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / R ^ 2 by positivity))
  filter_upwards [h] with i hi
  have hri : 0 < ‖r i‖ := norm_pos_iff.mpr (hr0 i)
  rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul, one_mul] at hi
  exact (lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hi).le

theorem cota_uniforme (hr0 : ∀ i, r i ≠ 0) (hs : Summable (fun i => 1 / ‖r i‖ ^ 2))
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ i in cofinite, ∀ z ∈ closedBall (0 : ℂ) R,
      ‖E1 (z / r i) - 1‖ ≤ 3 * R ^ 2 * (1 / ‖r i‖ ^ 2) := by
  filter_upwards [eventualmente_longe hr0 hs hR] with i hi z hz
  have hz' : ‖z‖ ≤ R := by simpa using hz
  have hri : 0 < ‖r i‖ := norm_pos_iff.mpr (hr0 i)
  have hq : ‖z / r i‖ ≤ 1 := by
    rw [norm_div, div_le_one hri]
    linarith
  have hz2 : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz' 2
  calc ‖E1 (z / r i) - 1‖ ≤ 3 * ‖z / r i‖ ^ 2 := E1_sub_one_le hq
    _ = 3 * ‖z‖ ^ 2 * (1 / ‖r i‖ ^ 2) := by rw [norm_div, div_pow]; ring
    _ ≤ 3 * R ^ 2 * (1 / ‖r i‖ ^ 2) := by gcongr

theorem summable_E1_sub (hr0 : ∀ i, r i ≠ 0) (hs : Summable (fun i => 1 / ‖r i‖ ^ 2)) (z : ℂ) :
    Summable (fun i => E1 (z / r i) - 1) := by
  have hR : (0 : ℝ) < ‖z‖ + 1 := by positivity
  refine (hs.mul_left (3 * (‖z‖ + 1) ^ 2)).of_norm_bounded_eventually ?_
  filter_upwards [cota_uniforme hr0 hs hR] with i hi
  exact hi z (by simp)

theorem prodE_multipliable (hr0 : ∀ i, r i ≠ 0) (hs : Summable (fun i => 1 / ‖r i‖ ^ 2)) (z : ℂ) :
    Multipliable (fun i => E1 (z / r i)) := by
  have := Complex.multipliable_one_add_of_summable (summable_E1_sub hr0 hs z)
  simpa using this

/-- Convergência uniforme em `‖z‖ ≤ R`. -/
theorem prodE_tendstoUniformlyOn (hr0 : ∀ i, r i ≠ 0) (hs : Summable (fun i => 1 / ‖r i‖ ^ 2))
    {R : ℝ} (hR : 0 < R) :
    TendstoUniformlyOn (fun (F : Finset ι) z => ∏ i ∈ F, E1 (z / r i))
      (fun z => ∏' i, E1 (z / r i)) atTop (closedBall (0 : ℂ) R) := by
  have h := Summable.hasProdUniformlyOn_one_add (f := fun i z => E1 (z / r i) - 1)
    (isCompact_closedBall (0 : ℂ) R) (hs.mul_left (3 * R ^ 2)) (cota_uniforme hr0 hs hR)
    (fun i => by
      apply Continuous.continuousOn
      unfold E1
      fun_prop)
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at h
  simpa using h

/-- **O produto é inteiro.** -/
theorem prodE_differentiable (hr0 : ∀ i, r i ≠ 0) (hs : Summable (fun i => 1 / ‖r i‖ ^ 2)) :
    Differentiable ℂ (fun z => ∏' i, E1 (z / r i)) := by
  intro z
  have hR : (0 : ℝ) < ‖z‖ + 1 := by positivity
  have hU := (prodE_tendstoUniformlyOn hr0 hs hR).mono ball_subset_closedBall
  have hd := hU.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun F => by
      apply Differentiable.differentiableOn
      unfold E1
      fun_prop) isOpen_ball
  exact hd.differentiableAt (isOpen_ball.mem_nhds (by simp))

/-- **O produto não se anula fora dos `r_i`.** -/
theorem prodE_ne_zero (hr0 : ∀ i, r i ≠ 0) (hs : Summable (fun i => 1 / ‖r i‖ ^ 2)) {w : ℂ}
    (hw : ∀ i, r i ≠ w) : ∏' i, E1 (w / r i) ≠ 0 := by
  have hlog := Complex.summable_log_one_add_of_summable (summable_E1_sub hr0 hs w)
  have hne : ∀ i, 1 + (E1 (w / r i) - 1) ≠ 0 := fun i => by
    rw [add_sub_cancel, Ne, E1_eq_zero_iff, div_eq_one_iff_eq (hr0 i)]
    exact fun h => hw i h.symm
  have := Complex.cexp_tsum_eq_tprod hne hlog
  simp only [add_sub_cancel] at this
  rw [← this]
  exact Complex.exp_ne_zero _

/-- **`‖∏'_i E1(z/r_i)‖ ≤ exp(3‖z‖^{3/2} Σ 1/|r_i|^{3/2})`**. -/
theorem prodE_norm_le (hr0 : ∀ i, r i ≠ 0) (hs : Summable (fun i => 1 / ‖r i‖ ^ 2))
    (h32 : Summable (fun i => 1 / ‖r i‖ ^ (3 / 2 : ℝ))) (z : ℂ) :
    ‖∏' i, E1 (z / r i)‖ ≤
      Real.exp (3 * ‖z‖ ^ (3 / 2 : ℝ) * ∑' i, 1 / ‖r i‖ ^ (3 / 2 : ℝ)) := by
  have hp : Tendsto (fun F : Finset ι => ∏ i ∈ F, E1 (z / r i)) atTop
      (𝓝 (∏' i, E1 (z / r i))) := (prodE_multipliable hr0 hs z).hasProd
  have hn := (continuous_norm.tendsto _).comp hp
  refine le_of_tendsto' hn fun F => ?_
  simp only [Function.comp_apply]
  rw [norm_prod]
  have e : ∀ i, 3 * ‖z / r i‖ ^ (3 / 2 : ℝ) = 3 * ‖z‖ ^ (3 / 2 : ℝ) * (1 / ‖r i‖ ^ (3 / 2 : ℝ)) := by
    intro i
    rw [norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
    ring
  calc ∏ i ∈ F, ‖E1 (z / r i)‖ ≤ ∏ i ∈ F, Real.exp (3 * ‖z / r i‖ ^ (3 / 2 : ℝ)) :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => norm_E1_le _)
    _ = Real.exp (∑ i ∈ F, 3 * ‖z / r i‖ ^ (3 / 2 : ℝ)) := (Real.exp_sum F _).symm
    _ ≤ Real.exp (3 * ‖z‖ ^ (3 / 2 : ℝ) * ∑' i, 1 / ‖r i‖ ^ (3 / 2 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        simp_rw [e]
        rw [← Finset.mul_sum]
        have h0 : 0 ≤ 3 * ‖z‖ ^ (3 / 2 : ℝ) := by
          have := Real.rpow_nonneg (norm_nonneg z) (3 / 2 : ℝ)
          positivity
        refine mul_le_mul_of_nonneg_left (h32.sum_le_tsum F (fun i _ => ?_)) h0
        have := Real.rpow_nonneg (norm_nonneg (r i)) (3 / 2 : ℝ)
        positivity

end Geral

/-! ## 4. O produto canônico dos zeros de `ζ` -/

theorem Z_ne_zero (ρ : ATK.ZetaSimetria.Z) : (ρ : ℂ) ≠ 0 := by
  intro h
  have := ρ.2.2.1
  rw [h, zero_re] at this
  exact lt_irrefl 0 this

theorem ZM_ne_zero (q : ZM) : ((q.1 : ATK.ZetaSimetria.Z) : ℂ) ≠ 0 := Z_ne_zero q.1

/-- **`P` é inteira.** -/
theorem Pcan_differentiable : Differentiable ℂ Pcan :=
  prodE_differentiable (r := fun q : ZM => ((q.1 : ATK.ZetaSimetria.Z) : ℂ)) ZM_ne_zero summable_ZM

/-- **`‖P(s)‖ ≤ exp(3 S |s|^{3/2})`**, `S = Σ_{(ρ, j)} 1/|ρ|^{3/2}`. -/
theorem Pcan_norm_le (z : ℂ) :
    ‖Pcan z‖ ≤ Real.exp (3 * ‖z‖ ^ (3 / 2 : ℝ) *
      ∑' q : ZM, 1 / ‖((q.1 : ATK.ZetaSimetria.Z) : ℂ)‖ ^ (3 / 2 : ℝ)) :=
  prodE_norm_le (r := fun q : ZM => ((q.1 : ATK.ZetaSimetria.Z) : ℂ)) ZM_ne_zero summable_ZM
    (summable_ZM_pot (by norm_num)) z

/-- **`P(z) ≠ 0` fora dos zeros de `ζ` na faixa.** -/
theorem Pcan_ne_zero {w : ℂ} (hw : w ∉ ATK.ZetaSimetria.Z) : Pcan w ≠ 0 :=
  prodE_ne_zero (r := fun q : ZM => ((q.1 : ATK.ZetaSimetria.Z) : ℂ)) ZM_ne_zero summable_ZM
    (fun q h => hw (h ▸ q.1.2))

/-- As cópias `(ρ₀, j)`, `j < m₀`. -/
noncomputable def copias (ρ₀ : ATK.ZetaSimetria.Z) : Finset ZM :=
  (Finset.univ : Finset (Fin (analyticOrderNatAt riemannZeta (ρ₀ : ℂ)))).map
    ⟨Sigma.mk ρ₀, sigma_mk_injective⟩

theorem mem_copias {ρ₀ : ATK.ZetaSimetria.Z} {q : ZM} (h : ((q.1 : ATK.ZetaSimetria.Z) : ℂ) = ρ₀) :
    q ∈ copias ρ₀ := by
  obtain ⟨ρ, j⟩ := q
  have : ρ = ρ₀ := Subtype.ext h
  subst this
  simp [copias]

/-- O resto do produto, sem as cópias de `ρ₀`. -/
noncomputable def Presto (ρ₀ : ATK.ZetaSimetria.Z) (z : ℂ) : ℂ :=
  ∏' q : ↑((copias ρ₀ : Set ZM)ᶜ), E1 (z / ((q.1.1 : ATK.ZetaSimetria.Z) : ℂ))

theorem summable_resto (ρ₀ : ATK.ZetaSimetria.Z) :
    Summable (fun q : ↑((copias ρ₀ : Set ZM)ᶜ) => 1 / ‖((q.1.1 : ATK.ZetaSimetria.Z) : ℂ)‖ ^ 2) :=
  summable_ZM.subtype _

theorem Presto_differentiable (ρ₀ : ATK.ZetaSimetria.Z) : Differentiable ℂ (Presto ρ₀) :=
  prodE_differentiable (r := fun q : ↑((copias ρ₀ : Set ZM)ᶜ) => ((q.1.1 : ATK.ZetaSimetria.Z) : ℂ))
    (fun q => ZM_ne_zero q.1) (summable_resto ρ₀)

theorem Presto_ne_zero (ρ₀ : ATK.ZetaSimetria.Z) : Presto ρ₀ ρ₀ ≠ 0 :=
  prodE_ne_zero (r := fun q : ↑((copias ρ₀ : Set ZM)ᶜ) => ((q.1.1 : ATK.ZetaSimetria.Z) : ℂ))
    (fun q => ZM_ne_zero q.1) (summable_resto ρ₀) (fun q h => q.2 (mem_copias h))

/-- **`P = E1(z/ρ₀)^{m₀} · P_resto`**. -/
theorem Pcan_fator (ρ₀ : ATK.ZetaSimetria.Z) (z : ℂ) :
    Pcan z = E1 (z / (ρ₀ : ℂ)) ^ analyticOrderNatAt riemannZeta (ρ₀ : ℂ) * Presto ρ₀ z := by
  set f : ZM → ℂ := fun q => E1 (z / ((q.1 : ATK.ZetaSimetria.Z) : ℂ)) with hf
  have h1 : Multipliable (f ∘ (↑) : ↑(copias ρ₀ : Set ZM) → ℂ) := Multipliable.of_finite
  have h2 : Multipliable (f ∘ (↑) : ↑((copias ρ₀ : Set ZM)ᶜ) → ℂ) :=
    prodE_multipliable (r := fun q : ↑((copias ρ₀ : Set ZM)ᶜ) => ((q.1.1 : ATK.ZetaSimetria.Z) : ℂ))
      (fun q => ZM_ne_zero q.1) (summable_resto ρ₀) z
  have hsplit := h1.tprod_mul_tprod_compl h2
  have hfin : ∏' q : ↑(copias ρ₀ : Set ZM), f q =
      E1 (z / (ρ₀ : ℂ)) ^ analyticOrderNatAt riemannZeta (ρ₀ : ℂ) := by
    rw [Finset.tprod_subtype' (copias ρ₀) f]
    unfold copias
    rw [Finset.prod_map]
    simp [hf]
  unfold Pcan Presto
  rw [← hsplit, hfin]

theorem E1_fator (w z : ℂ) (hw : w ≠ 0) : E1 (z / w) = (z - w) * (-cexp (z / w) / w) := by
  unfold E1
  field_simp
  ring

/-- **`ord_ρ P = m_ρ`**. -/
theorem ordem_Pcan (ρ₀ : ATK.ZetaSimetria.Z) :
    analyticOrderAt Pcan (ρ₀ : ℂ) = (analyticOrderNatAt riemannZeta (ρ₀ : ℂ) : ℕ∞) := by
  have hw := Z_ne_zero ρ₀
  set m := analyticOrderNatAt riemannZeta (ρ₀ : ℂ) with hm
  set G : ℂ → ℂ := fun z => (-cexp (z / (ρ₀ : ℂ)) / (ρ₀ : ℂ)) ^ m * Presto ρ₀ z with hG
  have hGd : Differentiable ℂ G := by
    have := Presto_differentiable ρ₀
    simp only [hG]
    fun_prop (disch := exact hw)
  have hG0 : G (ρ₀ : ℂ) ≠ 0 := by
    simp only [hG]
    refine mul_ne_zero (pow_ne_zero _ (div_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero _)) hw))
      (Presto_ne_zero ρ₀)
  refine (Pcan_differentiable.analyticAt _).analyticOrderAt_eq_natCast.mpr
    ⟨G, hGd.analyticAt _, hG0, Eventually.of_forall fun z => ?_⟩
  rw [Pcan_fator ρ₀ z, E1_fator _ _ hw, mul_pow, smul_eq_mul, hG]
  ring

/-! ## 5. Os zeros de `ξ` são exatamente `Z`, e `ord P = ord ξ` em todo ponto -/

theorem xi_ne_zero_re_ge_um {s : ℂ} (h : 1 ≤ s.re) : riemannXi s ≠ 0 := by
  by_cases hs1 : s = 1
  · rw [hs1, riemannXi_one]
    norm_num
  · rw [Ne, riemannXi_eq_zero_iff (by linarith) hs1]
    exact riemannZeta_ne_zero_of_one_le_re h

/-- **`ξ(s) = 0 ⟺ s ∈ Z`**. -/
theorem xi_eq_zero_iff_Z (s : ℂ) : riemannXi s = 0 ↔ s ∈ ATK.ZetaSimetria.Z := by
  constructor
  · intro h
    rcases le_or_gt 1 s.re with h1 | h1
    · exact absurd h (xi_ne_zero_re_ge_um h1)
    rcases le_or_gt s.re 0 with h0 | h0
    · have h' : riemannXi (1 - s) = 0 := by rw [riemannXi_one_sub]; exact h
      exact absurd h' (xi_ne_zero_re_ge_um (by simp; linarith))
    · have hs1 : s ≠ 1 := by
        rintro rfl
        simp at h1
      exact ⟨(riemannXi_eq_zero_iff h0 hs1).mp h, h0, h1⟩
  · intro hz
    have hs1 : s ≠ 1 := by
      rintro rfl
      have := hz.2.2
      simp at this
    exact (riemannXi_eq_zero_iff hz.2.1 hs1).mpr hz.1

/-- **`ord_z P = ord_z ξ` para todo `z`**. -/
theorem ordem_Pcan_eq_xi (z : ℂ) : analyticOrderAt Pcan z = analyticOrderAt riemannXi z := by
  by_cases hz : z ∈ ATK.ZetaSimetria.Z
  · have h1 : z ≠ 1 := by
      rintro rfl
      have := hz.2.2
      simp at this
    have hP := ordem_Pcan ⟨z, hz⟩
    simp only at hP
    rw [hP, ← ATK.ZeroClasses.Jensen.ordem_zeta_eq_xi hz.2.1 h1]
    have htop := ordem_zeta_finita hz.2.1 h1
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hn]
    simp [analyticOrderNatAt, ← hn]
  · rw [analyticOrderAt_eq_zero.mpr (Or.inr (Pcan_ne_zero hz)),
      analyticOrderAt_eq_zero.mpr (Or.inr (fun h => hz ((xi_eq_zero_iff_Z z).mp h)))]

end ATK.ZeroClasses.CanonicoInteira

#print axioms ATK.ZeroClasses.CanonicoInteira.gp_nonneg
#print axioms ATK.ZeroClasses.CanonicoInteira.gp_le
#print axioms ATK.ZeroClasses.CanonicoInteira.summable_gp
#print axioms ATK.ZeroClasses.CanonicoInteira.soma_ordem_inv_pot
#print axioms ATK.ZeroClasses.CanonicoInteira.summable_ZM_pot
#print axioms ATK.ZeroClasses.CanonicoInteira.E1_eq_zero_iff
#print axioms ATK.ZeroClasses.CanonicoInteira.norm_E1_le
#print axioms ATK.ZeroClasses.CanonicoInteira.eventualmente_longe
#print axioms ATK.ZeroClasses.CanonicoInteira.cota_uniforme
#print axioms ATK.ZeroClasses.CanonicoInteira.summable_E1_sub
#print axioms ATK.ZeroClasses.CanonicoInteira.prodE_multipliable
#print axioms ATK.ZeroClasses.CanonicoInteira.prodE_tendstoUniformlyOn
#print axioms ATK.ZeroClasses.CanonicoInteira.prodE_differentiable
#print axioms ATK.ZeroClasses.CanonicoInteira.prodE_ne_zero
#print axioms ATK.ZeroClasses.CanonicoInteira.prodE_norm_le
#print axioms ATK.ZeroClasses.CanonicoInteira.Z_ne_zero
#print axioms ATK.ZeroClasses.CanonicoInteira.ZM_ne_zero
#print axioms ATK.ZeroClasses.CanonicoInteira.Pcan_differentiable
#print axioms ATK.ZeroClasses.CanonicoInteira.Pcan_norm_le
#print axioms ATK.ZeroClasses.CanonicoInteira.Pcan_ne_zero
#print axioms ATK.ZeroClasses.CanonicoInteira.mem_copias
#print axioms ATK.ZeroClasses.CanonicoInteira.summable_resto
#print axioms ATK.ZeroClasses.CanonicoInteira.Presto_differentiable
#print axioms ATK.ZeroClasses.CanonicoInteira.Presto_ne_zero
#print axioms ATK.ZeroClasses.CanonicoInteira.Pcan_fator
#print axioms ATK.ZeroClasses.CanonicoInteira.E1_fator
#print axioms ATK.ZeroClasses.CanonicoInteira.ordem_Pcan
#print axioms ATK.ZeroClasses.CanonicoInteira.xi_ne_zero_re_ge_um
#print axioms ATK.ZeroClasses.CanonicoInteira.xi_eq_zero_iff_Z
#print axioms ATK.ZeroClasses.CanonicoInteira.ordem_Pcan_eq_xi
