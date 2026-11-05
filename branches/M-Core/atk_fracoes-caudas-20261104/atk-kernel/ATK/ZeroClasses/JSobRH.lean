import ATK.ZeroClasses.RiemannVonMangoldt
import ATK.ZeroClasses.LagariasHadamard

/-!
# `J(ε) → 0` sob RH (rodada 43)

`ATK.NecessidadeBD` isola as duas entradas que a prova clássica da necessidade de Báez-Duarte tira de RH:
a entrada de Littlewood (convergência dominada de `Σ μ(n) n^{−ε−s}`) e

  `J(ε) = ∫ |1 − ζ(½ + iτ)/ζ(½ + ε + iτ)|² / |½ + iτ|² dτ → 0` quando `ε → 0⁺`.

Aqui a segunda vira teorema (`tendsto_J`). A prova:

1. **monotonia** (`xi_meio_le`): sob RH, `|ξ(½ + iτ)| ≤ |ξ(½ + ε + iτ)|`, pela recíproca de Sondow–Dumitrescu
   (`rec_monotonia`, rodada 34) e continuidade em `σ = ½`;
2. **o fator `Γ`** (`razao_Gamma`, `razao_Gammaℝ`): `|Γℝ(½ + ε + iτ)| ≤ K (1 + |τ|)^{1/4} |Γℝ(½ + iτ)|` para
   `0 ≤ ε ≤ ½`, por Stirling complexo (rodada 39) em `|τ| ≥ 4` e compacidade em `|τ| ≤ 4`;
3. **a razão** (`razao_zeta`): sob RH, `|ζ(½ + iτ)| ≤ K (1 + |τ|)^{1/4} |ζ(½ + ε + iτ)|`, uniformemente em
   `0 < ε < ½`, de `ξ = s(s − 1)/2 · Γℝ · ζ`;
4. **convergência dominada** (`cota_erro`, `ae_zeta_ne_zero`, `tendsto_erro`): o integrando é
   `≤ 16(1 + K²)(1 + |τ|)^{−3/2}`, integrável, e tende a `0` fora dos zeros de `ζ` na linha crítica, que são
   enumeráveis.

`ATK.NecessidadeRH.tendsto_J_RH` (2026-10-15) já prova o mesmo enunciado por outro caminho (Phragmén–Lindelöf
para `ζ(s)/ζ(s + ε)`, `ATK.RazaoZeta`), e `ATK.NecessidadeRH.rh_iff_DN` já certifica `RH ⟺ D_N → 0` com o
mollificador suavizado. Esta é uma **segunda prova, independente**: troca Phragmén–Lindelöf pela monotonia de
Sondow–Dumitrescu e por Stirling.

Daí `necessidade_iff_entrada`: a estrutura nomeada `FechamentoO1.NecessidadeRH`, que usa o mollificador de corte
abrupto, reduz-se à entrada de Littlewood. A entrada segue BUILD_PENDING; RH segue OPEN_MATH.

Classificação (rodada 43): **ferramenta** (segunda prova de uma consequência de RH já certificada).
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace ATK.ZeroClasses.JRH

open ATK.ZeroClasses.StirlingComplexo (ell exp_ell stirling)
open ATK.BaseRiemannXi (riemannXi continuous_riemannXi riemannXi_eq_zeta)
open ATK.NecessidadeBD (lc lc_re lc_ne_zero continuous_lc erro erro_nonneg J EntradaLittlewood)

/-! ## 1. A razão de `Γ` na horizontal -/

theorem norm_Gamma_eq {z : ℂ} (hz : 0 < z.re) : ‖Gamma z‖ = Real.exp (ell z).re := by
  rw [← exp_ell hz, Complex.norm_exp]

theorem continuousAt_Gamma {w : ℂ} (hw : 0 < w.re) : ContinuousAt Gamma w := by
  refine (Complex.differentiableAt_Gamma w fun m h => ?_).continuousAt
  have h2 : w.re = -(m : ℝ) := by rw [h]; simp
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

/-- `‖log(z + h) − log z‖ ≤ h/|Im z|` para `Re z > 0`, `h ≥ 0`. -/
theorem norm_log_add_sub_le {z : ℂ} (hz : 0 < z.re) (hy : z.im ≠ 0) {h : ℝ} (hh : 0 ≤ h) :
    ‖log (z + h) - log z‖ ≤ h / |z.im| := by
  have hyp : 0 < |z.im| := abs_pos.mpr hy
  have hd : ∀ u ∈ Icc (0 : ℝ) h, HasDerivAt (fun u : ℝ => log (z + u)) (z + u)⁻¹ u := by
    intro u hu
    have hs : z + (u : ℂ) ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simp; linarith [hu.1]))
    have := ((Complex.hasDerivAt_log hs).comp (u : ℂ) ((hasDerivAt_id (u : ℂ)).const_add z)).comp_ofReal
    simpa using this
  have hb : ∀ u ∈ Ico (0 : ℝ) h, ‖(z + u)⁻¹‖ ≤ 1 / |z.im| := by
    intro u _
    rw [norm_inv, one_div]
    have : |z.im| ≤ ‖z + u‖ := by
      have := Complex.abs_im_le_norm (z + u)
      simpa using this
    exact inv_anti₀ hyp this
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun u : ℝ => log (z + u))
    (fun u hu => (hd u hu).hasDerivWithinAt) hb h (right_mem_Icc.mpr hh)
  simp only [ofReal_zero, add_zero, sub_zero] at this
  calc ‖log (z + h) - log z‖ ≤ 1 / |z.im| * h := this
    _ = h / |z.im| := by ring

/-- **Stirling** dá `|Γ(¼ + h + iy)| ≤ e^{17/2} (1 + |y|)^{1/4} |Γ(¼ + iy)|` para `|y| ≥ 2`, `0 ≤ h ≤ ¼`. -/
theorem razao_Gamma_alto {y h : ℝ} (hy : 2 ≤ |y|) (h0 : 0 ≤ h) (h1 : h ≤ 1 / 4) :
    ‖Gamma (((1 / 4 + h : ℝ) : ℂ) + y * I)‖ ≤
      Real.exp (17 / 2) * (1 + |y|) ^ (1 / 4 : ℝ) * ‖Gamma (((1 / 4 : ℝ) : ℂ) + y * I)‖ := by
  set z : ℂ := ((1 / 4 : ℝ) : ℂ) + y * I with hz
  set w : ℂ := ((1 / 4 + h : ℝ) : ℂ) + y * I with hw
  have hzre : z.re = 1 / 4 := by simp [hz]
  have hzim : z.im = y := by simp [hz]
  have hwre : w.re = 1 / 4 + h := by simp [hw]
  have hwim : w.im = y := by simp [hw]
  have hwz : w = z + h := by rw [hw, hz]; push_cast; ring
  have hy0 : 0 < |y| := by linarith
  have hzp : 0 < z.re := by rw [hzre]; norm_num
  have hwp : 0 < w.re := by rw [hwre]; linarith
  have sz := stirling hzp (by rw [hzim]; exact hy)
  have sw := stirling hwp (by rw [hwim]; exact hy)
  rw [hzim] at sz
  rw [hwim] at sw
  have e8 : 8 / |y| ≤ 4 := by rw [div_le_iff₀ hy0]; linarith
  have rz : ((z - 1 / 2) * log z - z + ((Real.log (2 * π) / 2 : ℝ) : ℂ)).re - 4 ≤ (ell z).re := by
    have := (Complex.abs_re_le_norm _).trans sz
    rw [sub_re] at this
    linarith [(abs_le.mp this).1]
  have rw' : (ell w).re ≤ ((w - 1 / 2) * log w - w + ((Real.log (2 * π) / 2 : ℝ) : ℂ)).re + 4 := by
    have := (Complex.abs_re_le_norm _).trans sw
    rw [sub_re] at this
    linarith [(abs_le.mp this).2]
  have hdiff : ((w - 1 / 2) * log w - w + ((Real.log (2 * π) / 2 : ℝ) : ℂ)) -
      ((z - 1 / 2) * log z - z + ((Real.log (2 * π) / 2 : ℝ) : ℂ)) =
      (z - 1 / 2) * (log w - log z) + (h : ℂ) * log w - h := by
    rw [hwz]; ring
  have hre := congrArg Complex.re hdiff
  simp only [sub_re, add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, log_re] at hre
  -- o termo `(z − ½)(log w − log z)`
  have hlog : ‖log w - log z‖ ≤ h / |y| := by
    rw [hwz]
    have := norm_log_add_sub_le hzp (by rw [hzim]; exact abs_pos.mp hy0) h0
    rwa [hzim] at this
  have hz12 : ‖z - 1 / 2‖ ≤ 1 / 4 + |y| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e1 : (z - 1 / 2).re = -(1 / 4) := by rw [sub_re, hzre]; norm_num
    have e2 : (z - 1 / 2).im = y := by rw [sub_im, hzim]; simp
    rw [e1, e2]
    norm_num
  have hA : ((z - 1 / 2) * (log w - log z)).re ≤ 1 / 2 := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul]
    calc ‖z - 1 / 2‖ * ‖log w - log z‖ ≤ (1 / 4 + |y|) * (h / |y|) :=
          mul_le_mul hz12 hlog (norm_nonneg _) (by positivity)
      _ = h / (4 * |y|) + h := by field_simp
      _ ≤ 1 / 2 := by
          have : h / (4 * |y|) ≤ h := by
            rw [div_le_iff₀ (by positivity)]
            nlinarith
          linarith
  -- o termo `h log |w|`
  have hwn : ‖w‖ ≤ 1 + |y| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hwre, hwim, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 / 4 + h)]
    linarith
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr fun h' => by rw [h', zero_re] at hwp; exact lt_irrefl 0 hwp
  have hl1 : 0 ≤ Real.log (1 + |y|) := Real.log_nonneg (by linarith)
  have hB : h * Real.log ‖w‖ ≤ 1 / 4 * Real.log (1 + |y|) :=
    (mul_le_mul_of_nonneg_left (Real.log_le_log hwpos hwn) h0).trans
      (mul_le_mul_of_nonneg_right h1 hl1)
  have hA' : ((z - 1 / 2) * (log w - log z)).re =
      (z - 1 / 2).re * (log w - log z).re - (z - 1 / 2).im * (log w - log z).im := mul_re _ _
  have hfin : (ell w).re ≤ 17 / 2 + 1 / 4 * Real.log (1 + |y|) + (ell z).re := by
    have : ((w - 1 / 2) * log w - w + ((Real.log (2 * π) / 2 : ℝ) : ℂ)).re -
        ((z - 1 / 2) * log z - z + ((Real.log (2 * π) / 2 : ℝ) : ℂ)).re =
        ((z - 1 / 2) * (log w - log z)).re + h * Real.log ‖w‖ - h := by
      rw [← sub_re, hdiff]
      simp [log_re]
    linarith
  rw [norm_Gamma_eq hwp, norm_Gamma_eq hzp, Real.rpow_def_of_pos (by linarith), mul_assoc,
    ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Compacidade em `|y| ≤ 2`. -/
theorem razao_Gamma_baixo : ∃ C : ℝ, ∀ y h : ℝ, |y| ≤ 2 → 0 ≤ h → h ≤ 1 / 4 →
    ‖Gamma (((1 / 4 + h : ℝ) : ℂ) + y * I)‖ ≤ C * ‖Gamma (((1 / 4 : ℝ) : ℂ) + y * I)‖ := by
  have hK : IsCompact (Icc (0 : ℝ) (1 / 4) ×ˢ Icc (-2 : ℝ) 2) := isCompact_Icc.prod isCompact_Icc
  have hc : ContinuousOn (fun p : ℝ × ℝ => ‖Gamma (((1 / 4 + p.1 : ℝ) : ℂ) + p.2 * I)‖ /
      ‖Gamma (((1 / 4 : ℝ) : ℂ) + p.2 * I)‖) (Icc (0 : ℝ) (1 / 4) ×ˢ Icc (-2 : ℝ) 2) := by
    intro p hp
    have hp1 : 0 ≤ p.1 := hp.1.1
    have h1 : ContinuousAt (fun p : ℝ × ℝ => Gamma (((1 / 4 + p.1 : ℝ) : ℂ) + p.2 * I)) p :=
      (continuousAt_Gamma (by simp; linarith)).comp
        (f := fun p : ℝ × ℝ => ((1 / 4 + p.1 : ℝ) : ℂ) + p.2 * I) (by fun_prop)
    have h2 : ContinuousAt (fun p : ℝ × ℝ => Gamma (((1 / 4 : ℝ) : ℂ) + p.2 * I)) p :=
      (continuousAt_Gamma (by norm_num)).comp (f := fun p : ℝ × ℝ => ((1 / 4 : ℝ) : ℂ) + p.2 * I)
        (by fun_prop)
    have hne : ‖Gamma (((1 / 4 : ℝ) : ℂ) + p.2 * I)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr (Gamma_ne_zero_of_re_pos (by norm_num))
    exact (h1.norm.div h2.norm hne).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨C, fun y h hy h0 h1 => ?_⟩
  have hmem : (h, y) ∈ Icc (0 : ℝ) (1 / 4) ×ˢ Icc (-2 : ℝ) 2 := ⟨⟨h0, h1⟩, abs_le.mp hy⟩
  have := hC (h, y) hmem
  have hpos : 0 < ‖Gamma (((1 / 4 : ℝ) : ℂ) + y * I)‖ :=
    norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos (by norm_num))
  dsimp only at this
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)), div_le_iff₀ hpos] at this
  exact this

/-- **A razão de `Γ`**: `|Γ(¼ + h + iy)| ≤ K (1 + |y|)^{1/4} |Γ(¼ + iy)|` para `0 ≤ h ≤ ¼`. -/
theorem razao_Gamma : ∃ K : ℝ, 0 < K ∧ ∀ y h : ℝ, 0 ≤ h → h ≤ 1 / 4 →
    ‖Gamma (((1 / 4 + h : ℝ) : ℂ) + y * I)‖ ≤
      K * (1 + |y|) ^ (1 / 4 : ℝ) * ‖Gamma (((1 / 4 : ℝ) : ℂ) + y * I)‖ := by
  obtain ⟨C, hC⟩ := razao_Gamma_baixo
  have hK0 : 0 < max C 0 + Real.exp (17 / 2) := by positivity
  refine ⟨max C 0 + Real.exp (17 / 2), hK0, fun y h h0 h1 => ?_⟩
  have hq : 1 ≤ (1 + |y|) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith [abs_nonneg y]) (by norm_num)
  have hG := norm_nonneg (Gamma (((1 / 4 : ℝ) : ℂ) + y * I))
  rcases le_or_gt |y| 2 with hy | hy
  · refine (hC y h hy h0 h1).trans (mul_le_mul_of_nonneg_right ?_ hG)
    calc C ≤ max C 0 + Real.exp (17 / 2) :=
          (le_max_left C 0).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
      _ = (max C 0 + Real.exp (17 / 2)) * 1 := by ring
      _ ≤ (max C 0 + Real.exp (17 / 2)) * (1 + |y|) ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hq hK0.le
  · refine (razao_Gamma_alto hy.le h0 h1).trans (mul_le_mul_of_nonneg_right ?_ hG)
    exact mul_le_mul_of_nonneg_right (by linarith [le_max_right C 0]) (by positivity)

theorem norm_Gammaℝ (w : ℂ) : ‖Gammaℝ w‖ = π ^ (-w.re / 2) * ‖Gamma (w / 2)‖ := by
  rw [Gammaℝ_def, norm_mul, norm_cpow_eq_rpow_re_of_pos Real.pi_pos, div_ofNat_re, neg_re]

/-- **A razão de `Γℝ`** na linha crítica: `|Γℝ(½ + ε + iτ)| ≤ K (1 + |τ|)^{1/4} |Γℝ(½ + iτ)|`, `0 ≤ ε ≤ ½`. -/
theorem razao_Gammaℝ : ∃ K : ℝ, 0 < K ∧ ∀ τ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 2 →
    ‖Gammaℝ (lc τ + ε)‖ ≤ K * (1 + |τ|) ^ (1 / 4 : ℝ) * ‖Gammaℝ (lc τ)‖ := by
  obtain ⟨K, hK, hG⟩ := razao_Gamma
  refine ⟨K, hK, fun τ ε h0 h1 => ?_⟩
  have e1 : (lc τ + ε) / 2 = ((1 / 4 + ε / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [lc] <;> ring
  have e2 : lc τ / 2 = ((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [lc] <;> ring
  have hre1 : (lc τ + ε).re = 1 / 2 + ε := by simp [lc]
  rw [norm_Gammaℝ, norm_Gammaℝ, e1, e2, hre1, lc_re]
  have hg := hG (τ / 2) (ε / 2) (by linarith) (by linarith)
  have hπ : π ^ (-(1 / 2 + ε) / 2) ≤ π ^ (-(1 / 2 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
  have hq : (1 + |τ / 2|) ^ (1 / 4 : ℝ) ≤ (1 + |τ|) ^ (1 / 4 : ℝ) := by
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    rw [abs_div, abs_two]
    linarith [abs_nonneg τ]
  have hGn := norm_nonneg (Gamma (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I))
  calc π ^ (-(1 / 2 + ε) / 2) * ‖Gamma (((1 / 4 + ε / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖
      ≤ π ^ (-(1 / 2 : ℝ) / 2) * (K * (1 + |τ / 2|) ^ (1 / 4 : ℝ) *
          ‖Gamma (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖) :=
        mul_le_mul hπ hg (norm_nonneg _) (by positivity)
    _ ≤ π ^ (-(1 / 2 : ℝ) / 2) * (K * (1 + |τ|) ^ (1 / 4 : ℝ) *
          ‖Gamma (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hGn
        exact mul_le_mul_of_nonneg_left hq hK.le
    _ = K * (1 + |τ|) ^ (1 / 4 : ℝ) * (π ^ (-(1 / 2 : ℝ) / 2) *
          ‖Gamma (((1 / 4 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I)‖) := by ring

/-! ## 2. Sob RH: a razão `ζ(½ + iτ)/ζ(½ + ε + iτ)` -/

/-- **Monotonia em `σ = ½`**: sob RH, `|ξ(½ + iτ)| ≤ |ξ(½ + ε + iτ)|`. -/
theorem xi_meio_le (hRH : RiemannHypothesis) (τ ε : ℝ) (hε : 0 < ε) :
    ‖riemannXi (lc τ)‖ ≤ ‖riemannXi (lc τ + ε)‖ := by
  have hm := ATK.ZeroClasses.LagariasHadamard.rec_monotonia hRH τ
  have hfc : Continuous fun σ : ℝ => ‖riemannXi (σ + τ * I)‖ :=
    (continuous_riemannXi.comp (f := fun σ : ℝ => (σ : ℂ) + τ * I) (by fun_prop)).norm
  have e0 : lc τ = ((1 / 2 : ℝ) : ℂ) + τ * I := by apply Complex.ext <;> simp [lc]
  have e1 : lc τ + ε = ((1 / 2 + ε : ℝ) : ℂ) + τ * I := by apply Complex.ext <;> simp [lc]
  rw [e1, e0]
  have hlim : Tendsto (fun σ : ℝ => ‖riemannXi (σ + τ * I)‖) (𝓝[>] (1 / 2))
      (𝓝 ‖riemannXi (((1 / 2 : ℝ) : ℂ) + τ * I)‖) :=
    hfc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (by linarith : (1 / 2 : ℝ) < 1 / 2 + ε)] with u hu
  exact (hm hu.1 (show 1 / 2 + ε ∈ Ioi (1 / 2 : ℝ) by simp; linarith) hu.2).le

/-- **A razão**: sob RH, `|ζ(½ + iτ)| ≤ K (1 + |τ|)^{1/4} |ζ(½ + ε + iτ)|`, uniformemente em `0 < ε < ½`. -/
theorem razao_zeta (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 < K ∧ ∀ τ ε : ℝ, 0 < ε → ε < 1 / 2 →
    ‖riemannZeta (lc τ)‖ ≤ K * (1 + |τ|) ^ (1 / 4 : ℝ) * ‖riemannZeta (lc τ + ε)‖ := by
  obtain ⟨K, hK, hG⟩ := razao_Gammaℝ
  refine ⟨4 * K, by positivity, fun τ ε h0 h1 => ?_⟩
  have hGτ := hG τ ε h0.le h1.le
  have hmono := xi_meio_le hRH τ ε h0
  have hsre : (lc τ).re = 1 / 2 := lc_re τ
  have hwre : (lc τ + ε).re = 1 / 2 + ε := by simp [lc]
  have hs0 : lc τ ≠ 0 := lc_ne_zero τ
  have hs1 : lc τ ≠ 1 := fun h => by rw [h, one_re] at hsre; norm_num at hsre
  have hw0 : lc τ + ε ≠ 0 := fun h => by rw [h, zero_re] at hwre; linarith
  have hw1 : lc τ + ε ≠ 1 := fun h => by rw [h, one_re] at hwre; linarith
  have hGs : Gammaℝ (lc τ) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num)
  have hGw : Gammaℝ (lc τ + ε) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hwre]; linarith)
  rw [riemannXi_eq_zeta hs0 hs1 hGs, riemannXi_eq_zeta hw0 hw1 hGw] at hmono
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  simp only [norm_mul, norm_div, h2] at hmono
  have hA : 1 / 2 ≤ ‖lc τ‖ := by
    have := Complex.abs_re_le_norm (lc τ)
    rwa [hsre, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
  have hB : 1 / 2 ≤ ‖lc τ - 1‖ := by
    have := Complex.abs_re_le_norm (lc τ - 1)
    rw [sub_re, one_re, hsre] at this
    norm_num at this
    linarith
  have hεn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]
  have hwA : ‖lc τ + ε‖ ≤ 2 * ‖lc τ‖ := by
    have := norm_add_le (lc τ) (ε : ℂ)
    rw [hεn] at this
    linarith
  have hwB : ‖lc τ + ε - 1‖ ≤ 2 * ‖lc τ - 1‖ := by
    have := norm_add_le (lc τ - 1) (ε : ℂ)
    rw [hεn, show lc τ - 1 + ε = lc τ + ε - 1 by ring] at this
    linarith
  have hgpos : 0 < ‖Gammaℝ (lc τ)‖ := norm_pos_iff.mpr hGs
  have hpos : 0 < ‖lc τ‖ * ‖lc τ - 1‖ / 2 * ‖Gammaℝ (lc τ)‖ := by
    have : 0 < ‖lc τ‖ := by linarith
    have : 0 < ‖lc τ - 1‖ := by linarith
    positivity
  have hw_le : ‖lc τ + ε‖ * ‖lc τ + ε - 1‖ / 2 * ‖Gammaℝ (lc τ + ε)‖ * ‖riemannZeta (lc τ + ε)‖ ≤
      (2 * ‖lc τ‖) * (2 * ‖lc τ - 1‖) / 2 *
        (K * (1 + |τ|) ^ (1 / 4 : ℝ) * ‖Gammaℝ (lc τ)‖) * ‖riemannZeta (lc τ + ε)‖ := by
    gcongr
  have key : ‖lc τ‖ * ‖lc τ - 1‖ / 2 * ‖Gammaℝ (lc τ)‖ * ‖riemannZeta (lc τ)‖ ≤
      ‖lc τ‖ * ‖lc τ - 1‖ / 2 * ‖Gammaℝ (lc τ)‖ *
        (4 * K * (1 + |τ|) ^ (1 / 4 : ℝ) * ‖riemannZeta (lc τ + ε)‖) :=
    hmono.trans (hw_le.trans_eq (by ring))
  exact le_of_mul_le_mul_left key hpos

/-! ## 3. Convergência dominada -/

theorem integrable_dom : Integrable (fun τ : ℝ => (1 + |τ|) ^ (-(3 / 2 : ℝ))) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by norm_num)
  simpa [Real.norm_eq_abs] using this

theorem norm_lc_sq (τ : ℝ) : ‖lc τ‖ ^ 2 = (1 / 2) ^ 2 + τ ^ 2 := by
  have e : lc τ = ((1 / 2 : ℝ) : ℂ) + τ * I := by apply Complex.ext <;> simp [lc]
  rw [e, Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]

/-- **A dominação**: sob RH, para `0 < ε < ½`, `|1 − ζ(s)/ζ(s + ε)|²/|s|² ≤ 16(1 + K²)(1 + |τ|)^{−3/2}`. -/
theorem cota_erro (hRH : RiemannHypothesis) : ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ τ : ℝ,
    erro (riemannZeta (lc τ + ε))⁻¹ τ ≤ 16 * (1 + K ^ 2) * (1 + |τ|) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨K, hK, hz⟩ := razao_zeta hRH
  refine ⟨K, hK, fun ε h0 h1 τ => ?_⟩
  have hw : riemannZeta (lc τ + ε) ≠ 0 :=
    ATK.ZeroClasses.LittlewoodRH.zeta_ne_zero_RH hRH (by simp [lc]; linarith)
  have hr : ‖riemannZeta (lc τ) * (riemannZeta (lc τ + ε))⁻¹‖ ≤ K * (1 + |τ|) ^ (1 / 4 : ℝ) := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_le_iff₀ (norm_pos_iff.mpr hw)]
    exact hz τ ε h0 h1
  have hs2 : (1 + |τ|) ^ 2 ≤ 8 * ‖lc τ‖ ^ 2 := by
    rw [norm_lc_sq]
    nlinarith [sq_abs τ, abs_nonneg τ, sq_nonneg (|τ| - 1)]
  have hL : 0 < ‖lc τ‖ ^ 2 := pow_pos (norm_pos_iff.mpr (lc_ne_zero τ)) 2
  set a := 1 + |τ| with ha
  have ha1 : 1 ≤ a := by linarith [abs_nonneg τ]
  have ha0 : 0 < a := by linarith
  set q := a ^ (1 / 4 : ℝ) with hq
  have hq1 : 1 ≤ q := Real.one_le_rpow ha1 (by norm_num)
  have hq2 : q ^ 2 = a ^ (1 / 2 : ℝ) := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
    norm_num
  have e3 : a ^ (1 / 2 : ℝ) = a ^ (-(3 / 2) : ℝ) * a ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ha0]
    norm_num
  have hp : 0 ≤ a ^ (-(3 / 2) : ℝ) := by positivity
  have h1' : ‖1 - riemannZeta (lc τ) * (riemannZeta (lc τ + ε))⁻¹‖ ≤ 1 + K * q :=
    (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have hqq : 1 ≤ q ^ 2 := by nlinarith
  unfold erro
  rw [norm_div, div_pow, div_le_iff₀ hL]
  calc ‖1 - riemannZeta (lc τ) * (riemannZeta (lc τ + ε))⁻¹‖ ^ 2 ≤ (1 + K * q) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1' 2
    _ ≤ 2 * (1 + K ^ 2) * q ^ 2 := by nlinarith [sq_nonneg (1 - K * q), sq_nonneg K]
    _ = 2 * (1 + K ^ 2) * (a ^ (-(3 / 2) : ℝ) * a ^ 2) := by rw [hq2, e3]
    _ ≤ 2 * (1 + K ^ 2) * (a ^ (-(3 / 2) : ℝ) * (8 * ‖lc τ‖ ^ 2)) := by gcongr
    _ = 16 * (1 + K ^ 2) * a ^ (-(3 / 2) : ℝ) * ‖lc τ‖ ^ 2 := by ring

theorem lc_injective : Function.Injective lc := fun a b h => by
  have := congrArg Complex.im h
  simpa [lc] using this

/-- **Os zeros de `ζ` na linha crítica formam um conjunto nulo.** -/
theorem ae_zeta_ne_zero : ∀ᵐ τ ∂(volume : Measure ℝ), riemannZeta (lc τ) ≠ 0 := by
  have hcount : {τ : ℝ | riemannZeta (lc τ) = 0}.Countable := by
    have hsub : {τ : ℝ | riemannZeta (lc τ) = 0} ⊆ ⋃ n : ℕ, lc ⁻¹' ATK.FechamentoO1.zerosSim n := by
      intro τ hτ
      obtain ⟨n, hn⟩ := exists_nat_ge |τ|
      refine mem_iUnion.mpr ⟨n, ?_⟩
      have him : (lc τ).im = τ := by simp [lc]
      refine ⟨⟨hτ, ?_, ?_⟩, ?_⟩
      · rw [lc_re]; norm_num
      · rw [lc_re]; norm_num
      · rw [him]; exact hn
    refine Countable.mono hsub (countable_iUnion fun n => ?_)
    exact ((ATK.FechamentoO1.zerosSim_finito n).preimage fun _ _ _ _ h => lc_injective h).countable
  have h0 := hcount.measure_zero volume
  rw [ae_iff]
  simpa using h0

theorem continuous_erro (hRH : RiemannHypothesis) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 2) :
    Continuous fun τ => erro (riemannZeta (lc τ + ε))⁻¹ τ := by
  have hz1 : ∀ τ, lc τ ≠ 1 := fun τ h => by
    have := lc_re τ
    rw [h, one_re] at this
    norm_num at this
  have hwre : ∀ τ, (lc τ + ε).re = 1 / 2 + ε := fun τ => by simp [lc]
  have hw1 : ∀ τ, lc τ + ε ≠ 1 := fun τ h => by
    have := hwre τ
    rw [h, one_re] at this
    linarith
  have cz : Continuous fun τ => riemannZeta (lc τ) := continuous_iff_continuousAt.mpr fun τ =>
    (differentiableAt_riemannZeta (hz1 τ)).continuousAt.comp continuous_lc.continuousAt
  have cw : Continuous fun τ : ℝ => riemannZeta (lc τ + ε) := continuous_iff_continuousAt.mpr fun τ =>
    (differentiableAt_riemannZeta (hw1 τ)).continuousAt.comp
      (f := fun τ : ℝ => lc τ + (ε : ℂ)) (continuous_lc.add continuous_const).continuousAt
  have cinv : Continuous fun τ => (riemannZeta (lc τ + ε))⁻¹ :=
    cw.inv₀ fun τ => ATK.ZeroClasses.LittlewoodRH.zeta_ne_zero_RH hRH (by rw [hwre]; linarith)
  unfold erro
  exact (((continuous_const.sub (cz.mul cinv)).div continuous_lc lc_ne_zero).norm).pow 2

/-- Fora dos zeros, o integrando tende a `0`. -/
theorem tendsto_erro {τ : ℝ} (hτ : riemannZeta (lc τ) ≠ 0) :
    Tendsto (fun ε : ℝ => erro (riemannZeta (lc τ + ε))⁻¹ τ) (𝓝[>] 0) (𝓝 0) := by
  have hz1 : lc τ ≠ 1 := fun h => by
    have := lc_re τ
    rw [h, one_re] at this
    norm_num at this
  have hc0 : ContinuousAt riemannZeta (lc τ + ((0 : ℝ) : ℂ)) := by
    simpa using (differentiableAt_riemannZeta hz1).continuousAt
  have hc : ContinuousAt (fun ε : ℝ => riemannZeta (lc τ + ε)) 0 :=
    hc0.comp (f := fun ε : ℝ => lc τ + (ε : ℂ)) (by fun_prop)
  have h1 : Tendsto (fun ε : ℝ => riemannZeta (lc τ + ε)) (𝓝[>] 0) (𝓝 (riemannZeta (lc τ))) := by
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have h3 : Tendsto (fun ε : ℝ => (1 - riemannZeta (lc τ) * (riemannZeta (lc τ + ε))⁻¹) / lc τ)
      (𝓝[>] 0) (𝓝 ((1 - riemannZeta (lc τ) * (riemannZeta (lc τ))⁻¹) / lc τ)) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul (h1.inv₀ hτ))).div_const _
  rw [mul_inv_cancel₀ hτ, sub_self, zero_div] at h3
  have h4 := h3.norm.pow 2
  rw [norm_zero, zero_pow two_ne_zero] at h4
  exact h4

/-! ## 4. `J(ε) → 0` -/

/-- **`J(ε) → 0` sob RH**: `∫ |1 − ζ(½ + iτ)/ζ(½ + ε + iτ)|²/|½ + iτ|² dτ → 0` quando `ε → 0⁺`. -/
theorem tendsto_J (hRH : RiemannHypothesis) : Tendsto J (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K, _, hb⟩ := cota_erro hRH
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  have hmeas : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun τ => erro (riemannZeta (lc τ + (ε : ℂ)))⁻¹ τ) volume := by
    filter_upwards [hev] with ε hε
    exact (continuous_erro hRH hε.1 hε.2).aestronglyMeasurable
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ τ ∂volume,
      ‖erro (riemannZeta (lc τ + (ε : ℂ)))⁻¹ τ‖ ≤ 16 * (1 + K ^ 2) * (1 + |τ|) ^ (-(3 / 2 : ℝ)) := by
    filter_upwards [hev] with ε hε
    refine ae_of_all _ fun τ => ?_
    rw [Real.norm_of_nonneg (erro_nonneg _ _)]
    exact hb ε hε.1 hε.2 τ
  have hint : Integrable (fun τ : ℝ => 16 * (1 + K ^ 2) * (1 + |τ|) ^ (-(3 / 2 : ℝ))) :=
    integrable_dom.const_mul _
  have hlim : ∀ᵐ τ ∂volume,
      Tendsto (fun ε : ℝ => erro (riemannZeta (lc τ + ε))⁻¹ τ) (𝓝[>] 0) (𝓝 0) := by
    filter_upwards [ae_zeta_ne_zero] with τ hτ
    exact tendsto_erro hτ
  have := tendsto_integral_filter_of_dominated_convergence (μ := volume) (f := fun _ : ℝ => (0 : ℝ))
    _ hmeas hbound hint hlim
  rw [integral_zero] at this
  exact this

/-- **`NecessidadeRH` reduz-se à entrada de Littlewood**: RvM, Hadamard, Littlewood sob RH e `J(ε) → 0` sob RH
são teoremas; resta a convergência dominada das somas parciais de Möbius. -/
theorem necessidade_iff_entrada : ATK.FechamentoO1.NecessidadeRH ↔
    (RiemannHypothesis → ∀ᶠ ε in 𝓝[>] (0 : ℝ), EntradaLittlewood ε) := by
  rw [ATK.ZeroClasses.RvM.necessidade_iff_deducao]
  constructor
  · intro h hRH
    exact (h ATK.ZeroClasses.RvM.riemannVonMangoldt ATK.ZeroClasses.Hadamard.hadamardXi
      ATK.ZeroClasses.LittlewoodRH.littlewoodSobRH hRH).1
  · intro h _ _ _ hRH
    exact ⟨h hRH, tendsto_J hRH⟩

end ATK.ZeroClasses.JRH

#print axioms ATK.ZeroClasses.JRH.norm_Gamma_eq
#print axioms ATK.ZeroClasses.JRH.continuousAt_Gamma
#print axioms ATK.ZeroClasses.JRH.norm_log_add_sub_le
#print axioms ATK.ZeroClasses.JRH.razao_Gamma_alto
#print axioms ATK.ZeroClasses.JRH.razao_Gamma_baixo
#print axioms ATK.ZeroClasses.JRH.razao_Gamma
#print axioms ATK.ZeroClasses.JRH.norm_Gammaℝ
#print axioms ATK.ZeroClasses.JRH.razao_Gammaℝ
#print axioms ATK.ZeroClasses.JRH.xi_meio_le
#print axioms ATK.ZeroClasses.JRH.razao_zeta
#print axioms ATK.ZeroClasses.JRH.integrable_dom
#print axioms ATK.ZeroClasses.JRH.norm_lc_sq
#print axioms ATK.ZeroClasses.JRH.cota_erro
#print axioms ATK.ZeroClasses.JRH.lc_injective
#print axioms ATK.ZeroClasses.JRH.ae_zeta_ne_zero
#print axioms ATK.ZeroClasses.JRH.continuous_erro
#print axioms ATK.ZeroClasses.JRH.tendsto_erro
#print axioms ATK.ZeroClasses.JRH.tendsto_J
#print axioms ATK.ZeroClasses.JRH.necessidade_iff_entrada
