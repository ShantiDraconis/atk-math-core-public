import ATK.ZeroClasses.LagariasHadamard
import ATK.ZeroClasses.JensenLocal
import ATK.ZeroClasses.RiemannVonMangoldt
import ATK.ZeroClasses.LogDerivZeta

/-!
# A soma sobre os zeros e `ζ′/ζ` local (rodada 63)

Primeira peça da fórmula explícita (Davenport, cap. 15). Com o produto de Hadamard (rodada 33), Jensen local
(rodada 31) e Stirling complexo (rodada 39):

* **`soma_wz_le`**: `Σ_{(ρ,j)} 1/(1 + (t − γ)²) ≤ (16/log(19/16)) (a₀ + log(2 + |t|)) Σ_n f(n)`, somando sobre os
  zeros com multiplicidade (`ZM`), com `f(n) = (1 + log(2 + n))/(1 + n²)` somável; daí
  **`Σ_ρ 1/(1 + (t − γ)²) = O(log(2 + |t|))`** (`soma_wz_O`). A prova agrupa os zeros por `⌈|γ − t|⌉ = n` e conta
  cada bloco com duas caixas de Jensen (`caixa_le`, rodada 31);
* **digama** (`norm_digamma_le`): `|ψ(z)| ≤ log(2 + |Im z|) + 11` em `0 < Re z ≤ 1`, `|Im z| ≥ 3` — Cauchy no resto
  de Stirling (`RS`, `hasDerivAt_RS`: `RS′ = ψ − log + 1/(2z)`) e `ψ(z + 1) = ψ(z) + 1/z` da Mathlib;
* **a diferença de Hadamard** (`logDeriv_xi_sub`): `ξ′/ξ(s) − ξ′/ξ(s₀) = Σ_{(ρ,j)} (1/(s − ρ) − 1/(s₀ − ρ))`;
* **`ζ′/ζ` local** (`zeta_local`, `zeta_local_O`): para `0 < σ ≤ 2`, `|t| ≥ 6` e `ζ(σ + it) ≠ 0`,
  `ζ′/ζ(σ + it) = Σ_{|γ − t| ≤ 1} 1/(s − ρ) + O(log |t|)`, com no máximo `O(log |t|)` termos (`card_perto_O`);
* **sob RH** (`logDeriv_RH`): `|ζ′/ζ(σ + it)| ≤ C log(2 + |t|)/(σ − ½)` em `½ < σ ≤ 2`, `|t| ≥ 6`.

Classificação (rodada 63): **ferramenta** — a cota de `ζ′/ζ` que o deslocamento de contorno até `Re s = ½ + 1/log x`
pede para `RH ⟹ ψ(x) = x + O(√x log³ x)`. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.SomaZeros

open ATK.ZeroClasses.Canonico ATK.ZeroClasses.CanonicoInteira ATK.ZeroClasses.LagariasHadamard
  ATK.ZeroClasses.JensenLocal ATK.ZeroClasses.StirlingComplexo ATK.BaseRiemannXi

/-! ## 1. O peso `1/(1 + (t − γ)²)` -/

/-- O peso de um zero `(ρ, j)` na altura `t`. -/
noncomputable def wz (t : ℝ) (q : ZM) : ℝ := 1 / (1 + (t - (rZ q).im) ^ 2)

theorem wz_pos (t : ℝ) (q : ZM) : 0 < wz t q := by
  unfold wz
  positivity

theorem wz_le (t : ℝ) (q : ZM) : wz t q ≤ 2 * (1 + t ^ 2) * (1 / ‖rZ q‖ ^ 2) := by
  obtain ⟨_, h0, h1⟩ := q.1.2
  have hn : ‖rZ q‖ ^ 2 = (rZ q).re ^ 2 + (rZ q).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hpos : 0 < ‖rZ q‖ ^ 2 := by
    have := ZM_ne_zero q
    positivity
  have h2 : ‖rZ q‖ ^ 2 ≤ 2 * (1 + t ^ 2) * (1 + (t - (rZ q).im) ^ 2) := by
    rw [hn]
    nlinarith [sq_nonneg (2 * t - (rZ q).im), sq_nonneg (t * (t - (rZ q).im))]
  unfold wz
  rw [mul_one_div, div_le_div_iff₀ (by positivity) hpos]
  linarith

theorem summable_wz (t : ℝ) : Summable (wz t) :=
  Summable.of_nonneg_of_le (fun q => (wz_pos t q).le) (wz_le t) (summable_ZM.mul_left _)

theorem wz_ge {t : ℝ} {q : ZM} (h : |(rZ q).im - t| ≤ 1) : 1 / 2 ≤ wz t q := by
  have hsq : (t - (rZ q).im) ^ 2 ≤ 1 := by
    have e : (t - (rZ q).im) ^ 2 = |(rZ q).im - t| ^ 2 := by
      rw [sq_abs]
      ring
    rw [e]
    nlinarith [abs_nonneg ((rZ q).im - t)]
  unfold wz
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  linarith

/-! ## 2. A contagem por blocos -/

/-- As caixas de Jensen para qualquer altura `y` (vazias se `|y| < 4`, pois `|γ| > 13`). -/
theorem caixa_le' {y : ℝ} (B : Finset ℂ)
    (hB : ∀ ρ ∈ B, ρ ∈ ATK.ZetaSimetria.Z ∧ |ρ.im - y| ≤ 1 / 2) :
    (∑ ρ ∈ B, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ 2 * Lc |y| := by
  by_cases hy : 4 ≤ |y|
  · exact caixa_le hy B fun ρ hρ => ⟨(hB ρ hρ).1.2.1, (hB ρ hρ).1.2.2, (hB ρ hρ).2⟩
  · have hBe : B = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ρ hρ
      obtain ⟨hz, hi⟩ := hB ρ hρ
      have h13 := ATK.ZeroClasses.Faixa.zeros_acima_13 ρ hz
      have := abs_sub_abs_le_abs_sub ρ.im y
      have hy' := not_le.mp hy
      linarith
    rw [hBe, Finset.sum_empty]
    have := Lc_nonneg (abs_nonneg y)
    linarith

/-- Um conjunto finito de cópias `(ρ, j)` tem no máximo `Σ_ρ m_ρ` elementos. -/
theorem card_le_ordens (G : Finset ZM) :
    (G.card : ℝ) ≤ ∑ ρ ∈ (G.image (fun q : ZM => q.1)).map (Function.Embedding.subtype _),
      (analyticOrderNatAt riemannZeta ρ : ℝ) := by
  classical
  rw [Finset.sum_map]
  have hsub : G ⊆ (G.image (fun q : ZM => q.1)).sigma (fun _ => Finset.univ) := by
    intro q hq
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_image_of_mem _ hq, Finset.mem_univ _⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_sigma] at h
  simp only [Finset.card_univ, Fintype.card_fin] at h
  simp only [Function.Embedding.coe_subtype]
  exact_mod_cast h

theorem card_caixa {y : ℝ} (G : Finset ZM) (hG : ∀ q ∈ G, |(rZ q).im - y| ≤ 1 / 2) :
    (G.card : ℝ) ≤ 2 * Lc |y| := by
  refine (card_le_ordens G).trans (caixa_le' _ fun ρ hρ => ?_)
  rw [Finset.mem_map] at hρ
  obtain ⟨a, ha, rfl⟩ := hρ
  rw [Finset.mem_image] at ha
  obtain ⟨q, hq, rfl⟩ := ha
  exact ⟨q.1.2, hG q hq⟩

/-- A constante `a₀ = log 31 + |log(2 − π²/6)|`. -/
noncomputable def a0 : ℝ := Real.log 31 + |Real.log (2 - π ^ 2 / 6)|

/-- `l₀ = log(19/16)`. -/
noncomputable def l0 : ℝ := Real.log (19 / 16)

theorem l0_pos : 0 < l0 := Real.log_pos (by norm_num)

theorem one_le_a0 : 1 ≤ a0 := by
  have h31 : 1 ≤ Real.log 31 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  have := abs_nonneg (Real.log (2 - π ^ 2 / 6))
  unfold a0
  linarith

theorem Lc_le {u : ℝ} (hu : 0 ≤ u) : Lc u ≤ (a0 + Real.log (2 + u)) / l0 := by
  have hb0 : 0 < 2 - π ^ 2 / 6 := ATK.BLProva.dois_menos_pos
  unfold Lc
  apply div_le_div_of_nonneg_right _ l0_pos.le
  rw [Real.log_div (by linarith : (0 : ℝ) < 15 * u + 62).ne' hb0.ne']
  have h1 : Real.log (15 * u + 62) ≤ Real.log 31 + Real.log (2 + u) := by
    rw [← Real.log_mul (by norm_num) (by linarith : (0 : ℝ) < 2 + u).ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have h2 : -Real.log (2 - π ^ 2 / 6) ≤ |Real.log (2 - π ^ 2 / 6)| := neg_le_abs _
  unfold a0
  linarith

theorem Lc_caixa {t y : ℝ} {n : ℕ} (hy : |y| ≤ |t| + n + 1 / 2) :
    Lc |y| ≤ (a0 + Real.log (2 + |t|) + Real.log (2 + n)) / l0 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ht := abs_nonneg t
  refine (Lc_le (abs_nonneg y)).trans (div_le_div_of_nonneg_right ?_ l0_pos.le)
  have h : Real.log (2 + |y|) ≤ Real.log (2 + |t|) + Real.log (2 + n) := by
    rw [← Real.log_mul (by linarith : (0 : ℝ) < 2 + |t|).ne' (by linarith : (0 : ℝ) < 2 + n).ne']
    refine Real.log_le_log (by linarith [abs_nonneg y]) ?_
    nlinarith [mul_nonneg ht hn]
  linarith

/-- O termo somável dos blocos. -/
noncomputable def fz (n : ℕ) : ℝ := (1 + Real.log (2 + n)) / (1 + (n : ℝ) ^ 2)

theorem fz_nonneg (n : ℕ) : 0 ≤ fz n := by
  unfold fz
  have : 0 ≤ Real.log (2 + n) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  positivity

theorem fz_le (n : ℕ) : fz n ≤ 15 * (1 / |(n : ℝ) + 2| ^ (3 / 2 : ℝ)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set x : ℝ := (n : ℝ) + 2 with hx
  have hx0 : 0 < x := by linarith
  rw [abs_of_pos hx0]
  have hlog : Real.log x ≤ 2 * x ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 2)
    linarith
  have hr1 : 1 ≤ x ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hp : x ^ (1 / 2 : ℝ) * x ^ (3 / 2 : ℝ) = x ^ 2 := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hpos : 0 < x ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hden : x ^ 2 ≤ 5 * (1 + (n : ℝ) ^ 2) := by
    rw [hx]
    nlinarith [sq_nonneg (2 * (n : ℝ) - 1)]
  unfold fz
  rw [show (2 : ℝ) + n = x by rw [hx]; ring]
  rw [mul_one_div, div_le_div_iff₀ (by positivity) hpos]
  calc (1 + Real.log x) * x ^ (3 / 2 : ℝ) ≤ (3 * x ^ (1 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) := by
        gcongr
        linarith
    _ = 3 * x ^ 2 := by rw [mul_assoc, hp]
    _ ≤ 15 * (1 + (n : ℝ) ^ 2) := by linarith

theorem summable_fz : Summable fz :=
  Summable.of_nonneg_of_le fz_nonneg fz_le
    (((Real.summable_one_div_nat_add_rpow 2 (3 / 2)).mpr (by norm_num)).mul_left 15)

/-- **Um bloco** `⌈|γ − t|⌉ = n` pesa no máximo `(16/l₀)(a₀ + log(2 + |t|)) f(n)`. -/
theorem bloco_le (t : ℝ) (n : ℕ) (W : Finset ZM) (hW : ∀ q ∈ W, ⌈|(rZ q).im - t|⌉₊ = n) :
    ∑ q ∈ W, wz t q ≤ 16 / l0 * (a0 + Real.log (2 + |t|)) * fz n := by
  classical
  have hl0 := l0_pos
  have ha1 := one_le_a0
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hLn : 0 ≤ Real.log (2 + n) := Real.log_nonneg (by linarith)
  have hceil : ∀ q ∈ W, |(rZ q).im - t| ≤ n ∧ (n : ℝ) - 1 < |(rZ q).im - t| := by
    intro q hq
    have h1 := Nat.le_ceil |(rZ q).im - t|
    have h2 := Nat.ceil_lt_add_one (abs_nonneg ((rZ q).im - t))
    rw [hW q hq] at h1 h2
    exact ⟨h1, by linarith⟩
  have hw : ∀ q ∈ W, wz t q ≤ 4 / (1 + (n : ℝ) ^ 2) := by
    intro q hq
    obtain ⟨h1, h2⟩ := hceil q hq
    have hsq : (t - (rZ q).im) ^ 2 = |(rZ q).im - t| ^ 2 := by
      rw [sq_abs]
      ring
    have key : 1 + (n : ℝ) ^ 2 ≤ 4 * (1 + (t - (rZ q).im) ^ 2) := by
      rw [hsq]
      rcases le_or_gt (n : ℝ) 1 with hn1 | hn1
      · nlinarith [sq_nonneg |(rZ q).im - t|]
      · have h3 : ((n : ℝ) - 1) ^ 2 ≤ |(rZ q).im - t| ^ 2 := by
          have : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
          gcongr
        nlinarith [sq_nonneg (3 * (n : ℝ) - 4)]
    unfold wz
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hy1 : |t + n - 1 / 2| ≤ |t| + n + 1 / 2 := by
    have e : t + n - 1 / 2 = t + ((n : ℝ) - 1 / 2) := by ring
    have h : |(n : ℝ) - 1 / 2| ≤ n + 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [e]
    linarith [abs_add_le t ((n : ℝ) - 1 / 2)]
  have hy2 : |t - n + 1 / 2| ≤ |t| + n + 1 / 2 := by
    have e : t - n + 1 / 2 = t + -((n : ℝ) - 1 / 2) := by ring
    have h : |-((n : ℝ) - 1 / 2)| ≤ n + 1 / 2 := by
      rw [abs_neg]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    rw [e]
    linarith [abs_add_le t (-((n : ℝ) - 1 / 2))]
  have hplus := card_caixa (y := t + n - 1 / 2) (W.filter (fun q => t < (rZ q).im)) (fun q hq => by
    rw [Finset.mem_filter] at hq
    obtain ⟨h1, h2⟩ := hceil q hq.1
    have hpos : 0 < (rZ q).im - t := by linarith [hq.2]
    rw [abs_of_pos hpos] at h1 h2
    rw [abs_le]
    constructor <;> linarith)
  have hminus := card_caixa (y := t - n + 1 / 2) (W.filter (fun q => ¬ t < (rZ q).im)) (fun q hq => by
    rw [Finset.mem_filter] at hq
    obtain ⟨h1, h2⟩ := hceil q hq.1
    have hneg : (rZ q).im - t ≤ 0 := by linarith [not_lt.mp hq.2]
    rw [abs_of_nonpos hneg] at h1 h2
    rw [abs_le]
    constructor <;> linarith)
  have hcard : (W.card : ℝ) = (W.filter (fun q => t < (rZ q).im)).card +
      (W.filter (fun q => ¬ t < (rZ q).im)).card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := W) _).symm
  have hc1 := Lc_caixa (n := n) hy1
  have hc2 := Lc_caixa (n := n) hy2
  have hW' : (W.card : ℝ) ≤ 4 * (a0 + Real.log (2 + |t|) + Real.log (2 + n)) / l0 := by
    rw [hcard]
    have e : 4 * (a0 + Real.log (2 + |t|) + Real.log (2 + n)) / l0 =
        2 * ((a0 + Real.log (2 + |t|) + Real.log (2 + n)) / l0) +
          2 * ((a0 + Real.log (2 + |t|) + Real.log (2 + n)) / l0) := by ring
    rw [e]
    linarith
  have hmix : a0 + Real.log (2 + |t|) + Real.log (2 + n) ≤
      (a0 + Real.log (2 + |t|)) * (1 + Real.log (2 + n)) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a0 + Real.log (2 + |t|) - 1) hLn]
  have hpos : 0 < 1 + (n : ℝ) ^ 2 := by positivity
  calc ∑ q ∈ W, wz t q ≤ ∑ q ∈ W, 4 / (1 + (n : ℝ) ^ 2) := Finset.sum_le_sum hw
    _ = W.card * (4 / (1 + (n : ℝ) ^ 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (4 * (a0 + Real.log (2 + |t|) + Real.log (2 + n)) / l0) * (4 / (1 + (n : ℝ) ^ 2)) := by
        gcongr
    _ = 16 / (l0 * (1 + (n : ℝ) ^ 2)) * (a0 + Real.log (2 + |t|) + Real.log (2 + n)) := by
        field_simp
        ring
    _ ≤ 16 / (l0 * (1 + (n : ℝ) ^ 2)) * ((a0 + Real.log (2 + |t|)) * (1 + Real.log (2 + n))) := by
        gcongr
    _ = 16 / l0 * (a0 + Real.log (2 + |t|)) * fz n := by
        unfold fz
        field_simp

/-- **`Σ_{(ρ,j)} 1/(1 + (t − γ)²) ≤ (16/l₀)(a₀ + log(2 + |t|)) Σ_n f(n)`.** -/
theorem soma_wz_le (t : ℝ) :
    ∑' q, wz t q ≤ 16 / l0 * (a0 + Real.log (2 + |t|)) * ∑' n, fz n := by
  classical
  have hc : 0 ≤ 16 / l0 * (a0 + Real.log (2 + |t|)) := by
    have := l0_pos
    have := one_le_a0
    have : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
    positivity
  refine (summable_wz t).tsum_le_of_sum_le fun F => ?_
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun q hq => Finset.mem_image_of_mem (fun q : ZM => ⌈|(rZ q).im - t|⌉₊) hq)]
  calc _ ≤ ∑ n ∈ F.image (fun q : ZM => ⌈|(rZ q).im - t|⌉₊),
        16 / l0 * (a0 + Real.log (2 + |t|)) * fz n :=
        Finset.sum_le_sum fun n _ => bloco_le t n _ fun q hq => (Finset.mem_filter.mp hq).2
    _ ≤ ∑' n, 16 / l0 * (a0 + Real.log (2 + |t|)) * fz n :=
        (summable_fz.mul_left _).sum_le_tsum _ fun n _ => mul_nonneg hc (fz_nonneg n)
    _ = _ := tsum_mul_left

/-- **`Σ_ρ 1/(1 + (t − γ)²) = O(log(2 + |t|))`.** -/
theorem soma_wz_O : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ∑' q, wz t q ≤ C * Real.log (2 + |t|) := by
  have hl0 := l0_pos
  have ha1 := one_le_a0
  have hS : 0 ≤ ∑' n, fz n := tsum_nonneg fz_nonneg
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨16 / l0 * (a0 / Real.log 2 + 1) * ∑' n, fz n, by positivity, fun t => ?_⟩
  have hL2 : Real.log 2 ≤ Real.log (2 + |t|) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hA : a0 + Real.log (2 + |t|) ≤ (a0 / Real.log 2 + 1) * Real.log (2 + |t|) := by
    have : a0 ≤ a0 / Real.log 2 * Real.log (2 + |t|) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hL2 (by linarith)
    linarith
  calc ∑' q, wz t q ≤ 16 / l0 * (a0 + Real.log (2 + |t|)) * ∑' n, fz n := soma_wz_le t
    _ ≤ 16 / l0 * ((a0 / Real.log 2 + 1) * Real.log (2 + |t|)) * ∑' n, fz n := by gcongr
    _ = _ := by ring

/-! ## 3. A digama -/

/-- O resto de Stirling. -/
noncomputable def RS (u : ℂ) : ℂ :=
  ell u - ((u - 1 / 2) * log u - u + ((Real.log (2 * π) / 2 : ℝ) : ℂ))

theorem hasDerivAt_RS {u : ℂ} (hu : 0 < u.re) :
    HasDerivAt RS (digamma u - (log u - 1 / (2 * u))) u := by
  have hslit : u ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hu)
  have hu0 : u ≠ 0 := slitPlane_ne_zero hslit
  have h2 : HasDerivAt (fun u : ℂ => (u - 1 / 2) * log u - u + ((Real.log (2 * π) / 2 : ℝ) : ℂ))
      (1 * log u + (u - 1 / 2) * u⁻¹ - 1) u :=
    ((((hasDerivAt_id' u).sub_const (1 / 2)).mul (Complex.hasDerivAt_log hslit)).sub
      (hasDerivAt_id' u)).add_const _
  have h := (hasDerivAt_ell hu).sub h2
  show HasDerivAt (fun u : ℂ => ell u - ((u - 1 / 2) * log u - u + ((Real.log (2 * π) / 2 : ℝ) : ℂ)))
    _ u
  convert h using 1
  field_simp
  ring

/-- **`|ψ(z)| ≤ log(2 + |Im z|) + 11`** em `0 < Re z ≤ 1`, `|Im z| ≥ 3`. -/
theorem norm_digamma_le {z : ℂ} (h0 : 0 < z.re) (h1 : z.re ≤ 1) (h3 : 3 ≤ |z.im|) :
    ‖digamma z‖ ≤ Real.log (2 + |z.im|) + 11 := by
  set w := z + 1 with hw
  have hwre : w.re = z.re + 1 := by simp [hw]
  have hwim : w.im = z.im := by simp [hw]
  have hball : ∀ u ∈ closedBall w (1 / 2), 0 < u.re ∧ 5 / 2 ≤ |u.im| := by
    intro u hu
    rw [mem_closedBall, dist_eq_norm] at hu
    have hre := (abs_re_le_norm (u - w)).trans hu
    have him := (abs_im_le_norm (u - w)).trans hu
    rw [sub_re] at hre
    rw [sub_im] at him
    constructor
    · have := neg_abs_le (u.re - w.re)
      linarith
    · have := abs_sub_abs_le_abs_sub w.im u.im
      rw [abs_sub_comm w.im u.im] at this
      have hw3 : 3 ≤ |w.im| := by rw [hwim]; exact h3
      linarith
  have hdiff : DifferentiableOn ℂ RS (closedBall w (1 / 2)) := fun u hu =>
    (hasDerivAt_RS (hball u hu).1).differentiableAt.differentiableWithinAt
  have hC : ∀ u ∈ sphere w (1 / 2), ‖RS u‖ ≤ 16 / 5 := by
    intro u hu
    obtain ⟨hre, him⟩ := hball u (sphere_subset_closedBall hu)
    have hs := stirling hre (by linarith)
    calc ‖RS u‖ ≤ 8 / |u.im| := hs
      _ ≤ 8 / (5 / 2) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) him
      _ = 16 / 5 := by norm_num
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 2)
    (hdiff.diffContOnCl_ball subset_rfl) hC
  have hwre0 : 0 < w.re := by rw [hwre]; linarith
  rw [(hasDerivAt_RS hwre0).deriv] at hcau
  have hcau' : ‖digamma w - (log w - 1 / (2 * w))‖ ≤ 32 / 5 := by
    have e : (16 / 5 : ℝ) / (1 / 2) = 32 / 5 := by norm_num
    rw [e] at hcau
    exact hcau
  -- a recorrência
  have hzm : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.im h
    simp at this
    rw [this, abs_zero] at h3
    norm_num at h3
  have hrec : digamma w = digamma z + z⁻¹ := digamma_apply_add_one z hzm
  -- as cotas
  have hwn : |z.im| ≤ ‖w‖ := by rw [← hwim]; exact abs_im_le_norm w
  have hzn : |z.im| ≤ ‖z‖ := abs_im_le_norm z
  have hwn2 : ‖w‖ ≤ 2 + |z.im| := by
    have := Complex.norm_le_abs_re_add_abs_im w
    rw [hwre, hwim, abs_of_pos (by linarith : (0 : ℝ) < z.re + 1)] at this
    linarith
  have hlog : ‖log w‖ ≤ Real.log (2 + |z.im|) + π := by
    have h := Complex.norm_le_abs_re_add_abs_im (log w)
    rw [Complex.log_re, Complex.log_im] at h
    have hl0 : 0 ≤ Real.log ‖w‖ := Real.log_nonneg (by linarith)
    have hl1 : Real.log ‖w‖ ≤ Real.log (2 + |z.im|) := Real.log_le_log (by linarith) hwn2
    have ha := Complex.abs_arg_le_pi w
    rw [abs_of_nonneg hl0] at h
    linarith
  have hw2 : ‖1 / (2 * w)‖ ≤ 1 / 6 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_two]
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hzi : ‖z⁻¹‖ ≤ 1 / 3 := by
    rw [norm_inv]
    rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have e : digamma z = (digamma w - (log w - 1 / (2 * w))) + log w - 1 / (2 * w) - z⁻¹ := by
    rw [hrec]
    ring
  rw [e]
  have hpi := Real.pi_lt_d2
  calc ‖(digamma w - (log w - 1 / (2 * w))) + log w - 1 / (2 * w) - z⁻¹‖
      ≤ ‖digamma w - (log w - 1 / (2 * w))‖ + ‖log w‖ + ‖1 / (2 * w)‖ + ‖z⁻¹‖ := by
        have a1 := norm_sub_le ((digamma w - (log w - 1 / (2 * w))) + log w - 1 / (2 * w)) z⁻¹
        have a2 := norm_sub_le ((digamma w - (log w - 1 / (2 * w))) + log w) (1 / (2 * w))
        have a3 := norm_add_le (digamma w - (log w - 1 / (2 * w))) (log w)
        linarith
    _ ≤ 32 / 5 + (Real.log (2 + |z.im|) + π) + 1 / 6 + 1 / 3 := by linarith
    _ ≤ Real.log (2 + |z.im|) + 11 := by norm_num at hpi ⊢; linarith

/-! ## 4. A diferença de Hadamard -/

/-- **`ξ′/ξ(s) − ξ′/ξ(s₀) = Σ_{(ρ,j)} (1/(s − ρ) − 1/(s₀ − ρ))`.** -/
theorem logDeriv_xi_sub {s s₀ : ℂ} (hs : riemannXi s ≠ 0) (hs₀ : riemannXi s₀ ≠ 0) :
    logDeriv riemannXi s - logDeriv riemannXi s₀ =
      ∑' q : ZM, (1 / (s - rZ q) - 1 / (s₀ - rZ q)) := by
  obtain ⟨A, B, hAB⟩ := ATK.ZeroClasses.Hadamard.xi_hadamard
  rw [logDeriv_xi_eq hAB hs, logDeriv_xi_eq hAB hs₀, add_sub_add_left_eq_sub,
    ← (summable_logDeriv s).tsum_sub (summable_logDeriv s₀)]
  congr 1
  funext q
  ring

theorem summable_dif (s s₀ : ℂ) : Summable (fun q : ZM => 1 / (s - rZ q) - 1 / (s₀ - rZ q)) :=
  ((summable_logDeriv s).sub (summable_logDeriv s₀)).congr fun q => by ring

/-! ## 5. `ζ′/ζ` local -/

theorem perto_finito (t : ℝ) : {q : ZM | |(rZ q).im - t| ≤ 1}.Finite := by
  have h := (summable_wz t).tendsto_cofinite_zero
  have hev : ∀ᶠ q in cofinite, wz t q < 1 / 2 := h.eventually (gt_mem_nhds (by norm_num))
  refine (Filter.eventually_cofinite.mp hev).subset fun q hq => ?_
  simp only [Set.mem_ofPred_eq, not_lt] at hq ⊢
  exact wz_ge hq

/-- Os zeros `(ρ, j)` com `|γ − t| ≤ 1`. -/
noncomputable def perto (t : ℝ) : Finset ZM := (perto_finito t).toFinset

theorem mem_perto {t : ℝ} {q : ZM} : q ∈ perto t ↔ |(rZ q).im - t| ≤ 1 := by
  simp [perto]

/-- **`#{(ρ, j) : |γ − t| ≤ 1} ≤ 2 Σ_ρ 1/(1 + (t − γ)²)`.** -/
theorem card_perto_le (t : ℝ) : ((perto t).card : ℝ) ≤ 2 * ∑' q, wz t q := by
  calc ((perto t).card : ℝ) = ∑ q ∈ perto t, (1 : ℝ) := by simp
    _ ≤ ∑ q ∈ perto t, 2 * wz t q := Finset.sum_le_sum fun q hq => by
        have := wz_ge (mem_perto.mp hq)
        linarith
    _ ≤ ∑' q, 2 * wz t q :=
        ((summable_wz t).mul_left 2).sum_le_tsum _ fun q _ => by
          have := wz_pos t q
          positivity
    _ = 2 * ∑' q, wz t q := tsum_mul_left

theorem card_perto_O : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ((perto t).card : ℝ) ≤ C * Real.log (2 + |t|) := by
  obtain ⟨C, hC0, hC⟩ := soma_wz_O
  exact ⟨2 * C, by positivity, fun t => (card_perto_le t).trans (by linarith [hC t])⟩

/-- `ζ′/ζ` é limitada em `Re s = 2`. -/
noncomputable def K0 : ℝ := (-(logDeriv riemannZeta ((2 : ℝ) : ℂ))).re

theorem norm_E'_le {σ t : ℝ} (hσ0 : 0 < σ) (hσ2 : σ ≤ 2) (ht : 6 ≤ |t|) :
    ‖ATK.ZeroClasses.RvM.E' ((σ : ℂ) + t * I)‖ ≤ (Real.log (2 + |t|) + 14) / 2 := by
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hsim : s.im = t := by simp [hs]
  have hn : 6 ≤ ‖s‖ := ht.trans (by rw [← hsim]; exact abs_im_le_norm s)
  have hn1 : 6 ≤ ‖s - 1‖ := ht.trans (by
    have : (s - 1).im = t := by simp [hs]
    rw [← this]
    exact abs_im_le_norm _)
  have hz2re : 0 < (s / 2).re := by simp [hs]; linarith
  have hz2re1 : (s / 2).re ≤ 1 := by simp [hs]; linarith
  have hz2im : |(s / 2).im| = |t| / 2 := by simp [hs, abs_div]
  have hψ := norm_digamma_le hz2re hz2re1 (by rw [hz2im]; linarith)
  rw [hz2im] at hψ
  have hL : Real.log (2 + |t| / 2) ≤ Real.log (2 + |t|) :=
    Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
  have hlogπ : Real.log π ≤ π - 1 := Real.log_le_sub_one_of_pos Real.pi_pos
  have hlogπ0 : 0 ≤ Real.log π := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hpi := Real.pi_lt_d2
  have e1 : ‖1 / s‖ ≤ 1 / 6 := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by norm_num) hn
  have e2 : ‖1 / (s - 1)‖ ≤ 1 / 6 := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by norm_num) hn1
  have e3 : ‖((Real.log π : ℝ) : ℂ) / 2‖ = Real.log π / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogπ0, Complex.norm_two]
  have e4 : ‖digamma (s / 2) / 2‖ = ‖digamma (s / 2)‖ / 2 := by
    rw [norm_div, Complex.norm_two]
  unfold ATK.ZeroClasses.RvM.E'
  have a1 := norm_add_le (1 / s + 1 / (s - 1) - ((Real.log π : ℝ) : ℂ) / 2) (digamma (s / 2) / 2)
  have a2 := norm_sub_le (1 / s + 1 / (s - 1)) (((Real.log π : ℝ) : ℂ) / 2)
  have a3 := norm_add_le (1 / s) (1 / (s - 1))
  norm_num at hpi
  linarith

/-- **`ζ′/ζ` local**: `‖ζ′/ζ(s) − Σ_{|γ − t| ≤ 1} 1/(s − ρ)‖ ≤ K₀ + 4 Σ_ρ 1/(1 + (t − γ)²) + log(2 + |t|) + 14`
para `s = σ + it`, `0 < σ ≤ 2`, `|t| ≥ 6`, `ζ(s) ≠ 0`. -/
theorem zeta_local {t σ : ℝ} (ht : 6 ≤ |t|) (hσ0 : 0 < σ) (hσ2 : σ ≤ 2)
    (hz : riemannZeta ((σ : ℂ) + t * I) ≠ 0) :
    ‖logDeriv riemannZeta ((σ : ℂ) + t * I) - ∑ q ∈ perto t, 1 / ((σ : ℂ) + t * I - rZ q)‖ ≤
      K0 + 4 * ∑' q, wz t q + (Real.log (2 + |t|) + 14) := by
  classical
  set s : ℂ := (σ : ℂ) + t * I with hs
  set s₀ : ℂ := ((2 : ℝ) : ℂ) + t * I with hs₀
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    norm_num at ht
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hs₀re : s₀.re = 2 := by simp [hs₀]
  have hs₀im : s₀.im = t := by simp [hs₀]
  have hs1 : s ≠ 1 := fun h => ht0 (by rw [← hsim, h, one_im])
  have hs₀1 : s₀ ≠ 1 := fun h => ht0 (by rw [← hs₀im, h, one_im])
  have hsre0 : 0 < s.re := by rw [hsre]; exact hσ0
  have hs₀re0 : 0 < s₀.re := by rw [hs₀re]; norm_num
  have hz₀ : riemannZeta s₀ ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hs₀re]; norm_num)
  have hξ : riemannXi s ≠ 0 := fun h => hz ((ATK.BaseRiemannXi.riemannXi_eq_zero_iff hsre0 hs1).mp h)
  have hξ₀ : riemannXi s₀ ≠ 0 := fun h => hz₀ ((ATK.BaseRiemannXi.riemannXi_eq_zero_iff hs₀re0 hs₀1).mp h)
  have hE := ATK.ZeroClasses.RvM.E'_eq hsre0 hs1 hz
  have hE₀ := ATK.ZeroClasses.RvM.E'_eq hs₀re0 hs₀1 hz₀
  have hdif := logDeriv_xi_sub hξ hξ₀
  -- a parte perto e o resto
  set e : ZM → ℂ := fun q => if q ∈ perto t then 1 / (s - rZ q) else 0 with he
  set c : ZM → ℂ := fun q => (1 / (s - rZ q) - 1 / (s₀ - rZ q)) - e q with hc
  have hes : Summable e := summable_of_ne_finset_zero (s := perto t) fun q hq => by
    simp [he, hq]
  have hcs : Summable c := (summable_dif s s₀).sub hes
  have hesum : ∑' q, e q = ∑ q ∈ perto t, 1 / (s - rZ q) := by
    rw [tsum_eq_sum (s := perto t) fun q hq => by simp [he, hq]]
    exact Finset.sum_congr rfl fun q hq => by simp [he, hq]
  have hsplit : ∑' q : ZM, (1 / (s - rZ q) - 1 / (s₀ - rZ q)) = ∑' q, c q + ∑' q, e q := by
    rw [← hcs.tsum_add hes]
    congr 1
    funext q
    simp only [hc]
    ring
  -- a cota termo a termo
  have hcb : ∀ q, ‖c q‖ ≤ 4 * wz t q := by
    intro q
    obtain ⟨_, hρ0, hρ1⟩ := q.1.2
    have hwz := wz_pos t q
    have hs₀ρ : 1 ≤ ‖s₀ - rZ q‖ := by
      have := abs_re_le_norm (s₀ - rZ q)
      rw [sub_re, hs₀re, abs_of_pos (by linarith)] at this
      linarith
    by_cases hq : q ∈ perto t
    · have hcq : c q = -(1 / (s₀ - rZ q)) := by
        simp only [hc, he]
        simp only [hq, ↓reduceIte]
        ring
      rw [hcq, norm_neg, norm_div, norm_one]
      have h1 : 1 / ‖s₀ - rZ q‖ ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact hs₀ρ
      have h2 := wz_ge (mem_perto.mp hq)
      linarith
    · have hfar : 1 < |(rZ q).im - t| := by
        rw [mem_perto, not_le] at hq
        exact hq
      have hcq : c q = 1 / (s - rZ q) - 1 / (s₀ - rZ q) := by
        simp only [hc, he]
        simp only [hq, ↓reduceIte]
        ring
      have hsρ : |(rZ q).im - t| ≤ ‖s - rZ q‖ := by
        have := abs_im_le_norm (s - rZ q)
        rw [sub_im, hsim, abs_sub_comm] at this
        exact this
      have hs₀ρ' : |(rZ q).im - t| ≤ ‖s₀ - rZ q‖ := by
        have := abs_im_le_norm (s₀ - rZ q)
        rw [sub_im, hs₀im, abs_sub_comm] at this
        exact this
      have hne : s - rZ q ≠ 0 := fun h => by
        rw [h, norm_zero] at hsρ
        linarith
      have hne₀ : s₀ - rZ q ≠ 0 := fun h => by
        rw [h, norm_zero] at hs₀ρ'
        linarith
      have hdiff : s₀ - s = ((2 - σ : ℝ) : ℂ) := by
        rw [hs, hs₀]
        push_cast
        ring
      have he' : 1 / (s - rZ q) - 1 / (s₀ - rZ q) = (s₀ - s) / ((s - rZ q) * (s₀ - rZ q)) := by
        field_simp
        ring
      rw [hcq, he', hdiff, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      set d := |(rZ q).im - t| with hd
      have hd1 : 1 < d := hfar
      have hprod : d * d ≤ ‖s - rZ q‖ * ‖s₀ - rZ q‖ :=
        mul_le_mul hsρ hs₀ρ' (by linarith) (norm_nonneg _)
      have hwz' : wz t q = 1 / (1 + d ^ 2) := by
        unfold wz
        congr 2
        rw [hd, ← sq_abs, abs_sub_comm]
      rw [hwz', div_le_iff₀ (by nlinarith)]
      have h4 : 4 * (1 / (1 + d ^ 2)) * (d * d) ≥ 2 := by
        rw [ge_iff_le, mul_comm (4 * (1 / (1 + d ^ 2))), ← mul_assoc, mul_one_div,
          le_div_iff₀ (by positivity)]
        nlinarith
      have h5 : 4 * (1 / (1 + d ^ 2)) * (d * d) ≤ 4 * (1 / (1 + d ^ 2)) * (‖s - rZ q‖ * ‖s₀ - rZ q‖) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      linarith
  have hcn : Summable (fun q => ‖c q‖) :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) hcb ((summable_wz t).mul_left 4)
  have hcb' : ‖∑' q, c q‖ ≤ 4 * ∑' q, wz t q := by
    calc ‖∑' q, c q‖ ≤ ∑' q, ‖c q‖ := norm_tsum_le_tsum_norm hcn
      _ ≤ ∑' q, 4 * wz t q := hcn.tsum_le_tsum hcb ((summable_wz t).mul_left 4)
      _ = 4 * ∑' q, wz t q := tsum_mul_left
  -- a identidade
  have hid : logDeriv riemannZeta s - ∑ q ∈ perto t, 1 / (s - rZ q) =
      logDeriv riemannZeta s₀ + ∑' q, c q - ATK.ZeroClasses.RvM.E' s + ATK.ZeroClasses.RvM.E' s₀ := by
    have h1 : logDeriv riemannXi s - logDeriv riemannXi s₀ =
        ∑' q, c q + ∑ q ∈ perto t, 1 / (s - rZ q) := by
      rw [hdif, hsplit, hesum]
    change ATK.ZeroClasses.RvM.g s = _ at hE
    change ATK.ZeroClasses.RvM.g s₀ = _ at hE₀
    change logDeriv riemannXi s = _ at hE
    change logDeriv riemannXi s₀ = _ at hE₀
    rw [hE, hE₀] at h1
    linear_combination h1
  rw [hid]
  have hK := ATK.ZeroClasses.LogDerivZeta.norm_logDeriv_le (by norm_num : (1 : ℝ) < 2) t
  have hEs := norm_E'_le hσ0 hσ2 ht
  have hEs₀ := norm_E'_le (σ := 2) (by norm_num) le_rfl ht
  have a1 := norm_add_le (logDeriv riemannZeta s₀ + ∑' q, c q - ATK.ZeroClasses.RvM.E' s)
    (ATK.ZeroClasses.RvM.E' s₀)
  have a2 := norm_sub_le (logDeriv riemannZeta s₀ + ∑' q, c q) (ATK.ZeroClasses.RvM.E' s)
  have a3 := norm_add_le (logDeriv riemannZeta s₀) (∑' q, c q)
  unfold K0
  linarith

/-- **`ζ′/ζ(s) = Σ_{|γ − t| ≤ 1} 1/(s − ρ) + O(log |t|)`** em `0 < σ ≤ 2`, `|t| ≥ 6`. -/
theorem zeta_local_O : ∃ C : ℝ, 0 ≤ C ∧ ∀ t σ : ℝ, 6 ≤ |t| → 0 < σ → σ ≤ 2 →
    riemannZeta ((σ : ℂ) + t * I) ≠ 0 →
    ‖logDeriv riemannZeta ((σ : ℂ) + t * I) - ∑ q ∈ perto t, 1 / ((σ : ℂ) + t * I - rZ q)‖ ≤
      C * Real.log (2 + |t|) := by
  obtain ⟨C, hC0, hC⟩ := soma_wz_O
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK0 : 0 ≤ K0 := by
    have := ATK.ZeroClasses.LogDerivZeta.norm_logDeriv_le (by norm_num : (1 : ℝ) < 2) 0
    unfold K0
    linarith [norm_nonneg (logDeriv riemannZeta ((2 : ℝ) + (0 : ℝ) * I))]
  refine ⟨(K0 + 14) / Real.log 2 + 4 * C + 1, by positivity, fun t σ ht hσ0 hσ2 hz => ?_⟩
  have hL2 : Real.log 2 ≤ Real.log (2 + |t|) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hL0 : 0 < Real.log (2 + |t|) := hl2.trans_le hL2
  have h1 : K0 + 14 ≤ (K0 + 14) / Real.log 2 * Real.log (2 + |t|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hL2 (by linarith)
  refine (zeta_local ht hσ0 hσ2 hz).trans ?_
  have h2 := hC t
  nlinarith

/-! ## 6. Sob RH -/

/-- **Sob RH**: `|ζ′/ζ(σ + it)| ≤ C log(2 + |t|)/(σ − ½)` em `½ < σ ≤ 2`, `|t| ≥ 6`. -/
theorem logDeriv_RH (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t σ : ℝ, 6 ≤ |t| → 1 / 2 < σ →
    σ ≤ 2 → ‖logDeriv riemannZeta ((σ : ℂ) + t * I)‖ ≤ C * Real.log (2 + |t|) / (σ - 1 / 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := zeta_local_O
  obtain ⟨C₂, hC₂0, hC₂⟩ := card_perto_O
  refine ⟨3 / 2 * C₁ + C₂, by positivity, fun t σ ht hσ hσ2 => ?_⟩
  set s : ℂ := (σ : ℂ) + t * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    norm_num at ht
  have hz : riemannZeta s ≠ 0 := by
    intro h
    have hre := hRH s h (by
      rintro ⟨n, hn⟩
      have := congrArg Complex.re hn
      rw [hsre] at this
      simp at this
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith) (fun h1 => ht0 (by rw [← hsim, h1, one_im]))
    rw [hsre] at hre
    linarith
  have hd : 0 < σ - 1 / 2 := by linarith
  have hL0 : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hloc := hC₁ t σ ht (by linarith) hσ2 hz
  have hsum : ‖∑ q ∈ perto t, 1 / (s - rZ q)‖ ≤ ((perto t).card : ℝ) / (σ - 1 / 2) := by
    calc ‖∑ q ∈ perto t, 1 / (s - rZ q)‖ ≤ ∑ q ∈ perto t, ‖1 / (s - rZ q)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ perto t, 1 / (σ - 1 / 2) := Finset.sum_le_sum fun q _ => by
          have hρ := re_de_RH hRH q.1.2
          have h := abs_re_le_norm (s - rZ q)
          rw [sub_re, hsre, hρ, abs_of_pos hd] at h
          rw [norm_div, norm_one]
          exact one_div_le_one_div_of_le hd h
      _ = ((perto t).card : ℝ) / (σ - 1 / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
  have htri : ‖logDeriv riemannZeta s‖ ≤
      ‖logDeriv riemannZeta s - ∑ q ∈ perto t, 1 / (s - rZ q)‖ + ‖∑ q ∈ perto t, 1 / (s - rZ q)‖ := by
    have := norm_add_le (logDeriv riemannZeta s - ∑ q ∈ perto t, 1 / (s - rZ q))
      (∑ q ∈ perto t, 1 / (s - rZ q))
    rwa [sub_add_cancel] at this
  have hcard := hC₂ t
  have h1 : C₁ * Real.log (2 + |t|) ≤ 3 / 2 * C₁ * Real.log (2 + |t|) / (σ - 1 / 2) := by
    rw [le_div_iff₀ hd]
    have : 0 ≤ C₁ * Real.log (2 + |t|) := by positivity
    nlinarith
  have h2 : ((perto t).card : ℝ) / (σ - 1 / 2) ≤ C₂ * Real.log (2 + |t|) / (σ - 1 / 2) :=
    div_le_div_of_nonneg_right hcard hd.le
  have e : (3 / 2 * C₁ + C₂) * Real.log (2 + |t|) / (σ - 1 / 2) =
      3 / 2 * C₁ * Real.log (2 + |t|) / (σ - 1 / 2) + C₂ * Real.log (2 + |t|) / (σ - 1 / 2) := by
    ring
  rw [e]
  linarith

end ATK.ZeroClasses.SomaZeros

#print axioms ATK.ZeroClasses.SomaZeros.wz_pos
#print axioms ATK.ZeroClasses.SomaZeros.wz_le
#print axioms ATK.ZeroClasses.SomaZeros.summable_wz
#print axioms ATK.ZeroClasses.SomaZeros.wz_ge
#print axioms ATK.ZeroClasses.SomaZeros.caixa_le'
#print axioms ATK.ZeroClasses.SomaZeros.card_le_ordens
#print axioms ATK.ZeroClasses.SomaZeros.card_caixa
#print axioms ATK.ZeroClasses.SomaZeros.l0_pos
#print axioms ATK.ZeroClasses.SomaZeros.one_le_a0
#print axioms ATK.ZeroClasses.SomaZeros.Lc_le
#print axioms ATK.ZeroClasses.SomaZeros.Lc_caixa
#print axioms ATK.ZeroClasses.SomaZeros.fz_nonneg
#print axioms ATK.ZeroClasses.SomaZeros.fz_le
#print axioms ATK.ZeroClasses.SomaZeros.summable_fz
#print axioms ATK.ZeroClasses.SomaZeros.bloco_le
#print axioms ATK.ZeroClasses.SomaZeros.soma_wz_le
#print axioms ATK.ZeroClasses.SomaZeros.soma_wz_O
#print axioms ATK.ZeroClasses.SomaZeros.hasDerivAt_RS
#print axioms ATK.ZeroClasses.SomaZeros.norm_digamma_le
#print axioms ATK.ZeroClasses.SomaZeros.logDeriv_xi_sub
#print axioms ATK.ZeroClasses.SomaZeros.summable_dif
#print axioms ATK.ZeroClasses.SomaZeros.perto_finito
#print axioms ATK.ZeroClasses.SomaZeros.mem_perto
#print axioms ATK.ZeroClasses.SomaZeros.card_perto_le
#print axioms ATK.ZeroClasses.SomaZeros.card_perto_O
#print axioms ATK.ZeroClasses.SomaZeros.norm_E'_le
#print axioms ATK.ZeroClasses.SomaZeros.zeta_local
#print axioms ATK.ZeroClasses.SomaZeros.zeta_local_O
#print axioms ATK.ZeroClasses.SomaZeros.logDeriv_RH
