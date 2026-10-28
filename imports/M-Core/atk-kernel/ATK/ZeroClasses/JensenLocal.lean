import ATK.ZeroClasses.Jensen
import ATK.ZeroClasses.Faixa
import ATK.BLProva

/-!
# Jensen local: `N(T + 1) − N(T) = O(log T)` e `Σ_ρ m_ρ/|ρ|² < ∞` (rodada 31)

A rodada 30 aplicou a fórmula de Jensen da Mathlib a `ξ` numa bola grande e obteve `N(T) = O(T log T)`.
Aqui ela é aplicada a `ζ` em bolas de raio fixo `19/10` centradas em `2 + iy`, onde `|ζ(2 + iy)| ≥ 2 − π²/6`
(`ATK.BLProva.zeta_dois_lb`) e `|ζ| = O(|y|)`:

* **cota no círculo** (`cota_zeta_circ`): `|ζ(s)| ≤ 15|y| + 62` em `‖s − (2 + iy)‖ ≤ 19/10`, `|y| ≥ 4`;
* **Jensen local** (`jensen_local`): os zeros (com multiplicidade) em `‖s − (2 + iy)‖ ≤ 8/5` são `≤ Lc |y|`, com
  `Lc t = log((15t + 62)/(2 − π²/6))/log(19/16)`;
* **simetria das ordens** (`ordem_xi_reflexao`, `ordemNat_zeta_reflexao`): `ord_{1−ρ} ζ = ord_ρ ζ` na faixa,
  via `ξ(1 − s) = ξ(s)` e `analyticOrderAt_comp_of_deriv_ne_zero`;
* **caixas** (`caixa_le`): para qualquer conjunto finito de pontos da faixa com `|Im ρ − y| ≤ ½`,
  `Σ m_ρ ≤ 2 Lc |y|` (a metade `Re ρ ≥ ½` na bola de `2 + iy`, a outra refletida na de `2 − iy`);
* **`N(T + 1) − N(T) ≤ 2 Lc(T + ½)`** (`N_succ_le`) e **`N(T + 1) − N(T) = O(log T)`** (`N_local_O_log`);
* **`Σ_ρ m_ρ/|ρ|² < ∞`** (`soma_ordem_inv_quadrado`) e `Σ_ρ 1/|ρ|² < ∞` (`soma_inv_quadrado`), somando
  sobre **todos** os zeros da faixa (os dois sinais de `Im ρ`), por blocos `⌈|Im ρ|⌉ = n` (com `|Im ρ| > 13`
  da rodada 29) e comparação com `n^{−3/2}`.

`Σ 1/|ρ|² < ∞` é a condição de convergência do produto canônico de gênero 1, `∏ (1 − s/ρ) e^{s/ρ}`, que aparece
em `HadamardXi` (`ATK.FechamentoO1`). Falta a fatoração de Hadamard em si: BUILD_PENDING.

Classificação (rodada 31): **ferramenta/parcial** — resultados clássicos sobre a **quantidade** de zeros; nada
sobre a **posição**. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.JensenLocal

open ATK.BaseRiemannXi

/-! ## 1. Bolas centradas em `2 + iy` -/

/-- O centro `2 + iy`. -/
noncomputable def cen (y : ℝ) : ℂ := 2 + (y : ℂ) * I

theorem cen_re (y : ℝ) : (cen y).re = 2 := by simp [cen]

theorem cen_im (y : ℝ) : (cen y).im = y := by simp [cen]

theorem coord_bola {y r : ℝ} {s : ℂ} (hs : ‖s - cen y‖ ≤ r) :
    |s.re - 2| ≤ r ∧ |s.im - y| ≤ r := by
  have h1 := Complex.abs_re_le_norm (s - cen y)
  have h2 := Complex.abs_im_le_norm (s - cen y)
  rw [sub_re, cen_re] at h1
  rw [sub_im, cen_im] at h2
  exact ⟨h1.trans hs, h2.trans hs⟩

theorem perto_cen {y : ℝ} (hy : 4 ≤ |y|) {s : ℂ} (hs : ‖s - cen y‖ ≤ 19 / 10) :
    1 / 10 ≤ s.re ∧ 1 ≤ ‖s - 1‖ ∧ ‖s‖ ≤ |y| + 4 := by
  obtain ⟨hre, him⟩ := coord_bola hs
  refine ⟨by linarith [(abs_le.mp hre).1], ?_, ?_⟩
  · have h := abs_sub_abs_le_abs_sub y s.im
    rw [abs_sub_comm] at h
    have h2 : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    rw [sub_im, one_im, sub_zero] at h2
    linarith
  · have hc : ‖cen y‖ ≤ 2 + |y| := by
      have := Complex.norm_le_abs_re_add_abs_im (cen y)
      rw [cen_re, cen_im] at this
      norm_num at this
      linarith
    calc ‖s‖ = ‖(s - cen y) + cen y‖ := by ring_nf
      _ ≤ ‖s - cen y‖ + ‖cen y‖ := norm_add_le _ _
      _ ≤ |y| + 4 := by linarith

theorem ne_um_de {y : ℝ} (hy : 4 ≤ |y|) {s : ℂ} (hs : ‖s - cen y‖ ≤ 19 / 10) : s ≠ 1 := by
  rintro rfl
  have := (perto_cen hy hs).2.1
  norm_num at this

/-- **`|ζ(s)| ≤ 15|y| + 62`** em `‖s − (2 + iy)‖ ≤ 19/10`. -/
theorem cota_zeta_circ {y : ℝ} (hy : 4 ≤ |y|) {s : ℂ} (hs : ‖s - cen y‖ ≤ 19 / 10) :
    ‖riemannZeta s‖ ≤ 15 * |y| + 62 := by
  obtain ⟨hre, hs1n, hsn⟩ := perto_cen hy hs
  have hs1 := ne_um_de hy hs
  have hpos : 0 < s.re := by linarith
  have hEM := ATK.EMGeral.norm_zeta_sub_EM_le hpos hs1 (N := 1) le_rfl (M := 1) le_rfl
  have hp : ATK.EMGeral.poch s 1 = s := by simp [ATK.EMGeral.poch]
  have hR0 : ‖riemannZeta s - ATK.EMGeral.EM 1 1 s‖ ≤ 3 / 2 * ‖s‖ / s.re := by
    refine hEM.trans (le_of_eq ?_)
    rw [hp, ATK.ZeroCert.Cb_um]
    simp
    ring
  have hR : ‖riemannZeta s - ATK.EMGeral.EM 1 1 s‖ ≤ 15 * ‖s‖ := by
    refine hR0.trans ?_
    rw [div_le_iff₀ hpos]
    nlinarith [norm_nonneg s]
  have hE : ‖ATK.EMGeral.EM 1 1 s‖ ≤ 3 / 2 := by
    rw [ATK.ZeroCert.EM_um]
    have h1 : ‖1 / (s - 1)‖ ≤ 1 := by
      rw [norm_div, norm_one]
      exact (div_le_one (by linarith)).mpr hs1n
    calc ‖(1 / 2 : ℂ) + 1 / (s - 1)‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖1 / (s - 1)‖ := norm_add_le _ _
      _ ≤ 1 / 2 + 1 := by
        have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
        rw [this]
        linarith
      _ = 3 / 2 := by norm_num
  calc ‖riemannZeta s‖ = ‖ATK.EMGeral.EM 1 1 s + (riemannZeta s - ATK.EMGeral.EM 1 1 s)‖ := by
        ring_nf
    _ ≤ ‖ATK.EMGeral.EM 1 1 s‖ + ‖riemannZeta s - ATK.EMGeral.EM 1 1 s‖ := norm_add_le _ _
    _ ≤ 3 / 2 + 15 * (|y| + 4) := by nlinarith
    _ ≤ 15 * |y| + 62 := by linarith

theorem zeta_analitica_bola {y : ℝ} (hy : 4 ≤ |y|) {r : ℝ} (hr : r ≤ 19 / 10) :
    AnalyticOnNhd ℂ riemannZeta (closedBall (cen y) r) :=
  analyticOn_riemannZeta.mono fun _ hz =>
    Set.mem_compl_singleton_iff.mpr (ne_um_de hy ((mem_closedBall_iff_norm.mp hz).trans hr))

/-! ## 2. Jensen local -/

/-- A cota local: `Lc t = log((15t + 62)/(2 − π²/6))/log(19/16)`. -/
noncomputable def Lc (t : ℝ) : ℝ := Real.log ((15 * t + 62) / (2 - π ^ 2 / 6)) / Real.log (19 / 16)

theorem Lc_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Lc t := by
  unfold Lc
  have hb := ATK.BLProva.dois_menos_pos
  have hb1 := ATK.BLProva.dois_menos_le_one
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  apply Real.log_nonneg
  rw [le_div_iff₀ hb]
  linarith

/-- **Jensen local**: zeros de `ζ` (com multiplicidade) em `‖s − (2 + iy)‖ ≤ 8/5` são `≤ Lc |y|`. -/
theorem jensen_local {y : ℝ} (hy : 4 ≤ |y|) :
    ((∑ᶠ u, MeromorphicOn.divisor riemannZeta (closedBall (cen y) (8 / 5)) u : ℤ) : ℝ) ≤ Lc |y| := by
  have hr : 0 < |(8 / 5 : ℝ)| := by norm_num
  have hrR : |(8 / 5 : ℝ)| < |(19 / 10 : ℝ)| := by
    rw [abs_of_pos (by norm_num), abs_of_pos (by norm_num)]
    norm_num
  have hM : 1 ≤ 15 * |y| + 62 := by linarith [abs_nonneg y]
  have han : AnalyticOnNhd ℂ riemannZeta (closedBall (cen y) |(19 / 10 : ℝ)|) :=
    zeta_analitica_bola hy (by rw [abs_of_pos (by norm_num)])
  have hlb : 2 - π ^ 2 / 6 ≤ ‖riemannZeta (cen y)‖ := ATK.BLProva.zeta_dois_lb y
  have hb := ATK.BLProva.dois_menos_pos
  have hne : riemannZeta (cen y) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlb
    linarith
  have hbd : ∀ z ∈ sphere (cen y) |(19 / 10 : ℝ)|, ‖riemannZeta z‖ ≤ 15 * |y| + 62 := by
    intro z hz
    rw [mem_sphere_iff_norm, abs_of_pos (by norm_num)] at hz
    exact cota_zeta_circ hy hz.le
  have J := AnalyticOnNhd.sum_divisor_le hr hrR hM han hne hbd
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 8 / 5)] at J
  have e : (19 / 10 : ℝ) / (8 / 5) = 19 / 16 := by norm_num
  rw [e] at J
  refine J.trans ?_
  unfold Lc
  have hl : 0 < Real.log (19 / 16) := Real.log_pos (by norm_num)
  have h1 : (15 * |y| + 62) / ‖riemannZeta (cen y)‖ ≤ (15 * |y| + 62) / (2 - π ^ 2 / 6) :=
    div_le_div_of_nonneg_left (by linarith) hb hlb
  have h2 := Real.log_le_log (div_pos (by linarith) (lt_of_lt_of_le hb hlb)) h1
  exact div_le_div_of_nonneg_right h2 hl.le

/-! ## 3. Somas de ordens e a simetria `ρ ↦ 1 − ρ` -/

/-- Uma soma finita de ordens num compacto é `≤ Σᶠ` do divisor. -/
theorem soma_ordem_le {f : ℂ → ℂ} {U : Set ℂ} (hU : IsCompact U) (han : AnalyticOnNhd ℂ f U)
    (B : Finset ℂ) (hB : ∀ w ∈ B, w ∈ U) (htop : ∀ w ∈ B, analyticOrderAt f w ≠ ⊤) :
    ∑ w ∈ B, (analyticOrderNatAt f w : ℤ) ≤ ∑ᶠ u, MeromorphicOn.divisor f U u := by
  set D := MeromorphicOn.divisor f U with hD
  have hfin : (Function.support D).Finite := D.finiteSupport hU
  have hnn : ∀ u, 0 ≤ D u := fun u => by
    simpa using MeromorphicOn.AnalyticOnNhd.divisor_nonneg han u
  rw [finsum_eq_sum_of_support_subset D (s := hfin.toFinset ∪ B) (by intro u hu; simp [hu])]
  calc ∑ w ∈ B, (analyticOrderNatAt f w : ℤ) = ∑ w ∈ B, D w :=
        Finset.sum_congr rfl fun w hw =>
          (ATK.ArgPrincipio.divisor_eq_ordem han (hB w hw) (htop w hw)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun u _ _ => hnn u)

theorem ordem_zeta_finita {ρ : ℂ} (hre : 0 < ρ.re) (h1 : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  rw [ATK.ZeroClasses.Jensen.ordem_zeta_eq_xi hre h1]
  exact ATK.ZeroClasses.Lagarias.ordem_xi_finita ρ

/-- **`ord_{1−z} ξ = ord_z ξ`**. -/
theorem ordem_xi_reflexao (z : ℂ) :
    analyticOrderAt riemannXi (1 - z) = analyticOrderAt riemannXi z := by
  have hg : AnalyticAt ℂ (fun s : ℂ => 1 - s) z := analyticAt_const.sub analyticAt_id
  have hd : deriv (fun s : ℂ => 1 - s) z ≠ 0 := by
    rw [((hasDerivAt_id' z).const_sub 1).deriv]
    norm_num
  have h := analyticOrderAt_comp_of_deriv_ne_zero (f := riemannXi) hg hd
  have hc : riemannXi ∘ (fun s : ℂ => 1 - s) = riemannXi := funext fun s => riemannXi_one_sub s
  rw [hc] at h
  exact h.symm

/-- **`ord_{1−ρ} ζ = ord_ρ ζ`** na faixa. -/
theorem ordemNat_zeta_reflexao {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderNatAt riemannZeta (1 - ρ) = analyticOrderNatAt riemannZeta ρ := by
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    simp at h1
  have hre' : 0 < (1 - ρ).re := by
    simp only [sub_re, one_re]
    linarith
  have hρ1' : 1 - ρ ≠ 1 := by
    intro h
    have : ρ = 0 := by linear_combination -h
    rw [this, zero_re] at h0
    exact lt_irrefl 0 h0
  unfold analyticOrderNatAt
  rw [ATK.ZeroClasses.Jensen.ordem_zeta_eq_xi hre' hρ1', ordem_xi_reflexao,
    ATK.ZeroClasses.Jensen.ordem_zeta_eq_xi h0 hρ1]

/-! ## 4. Caixas `|Im ρ − y| ≤ ½` -/

theorem caixa_na_bola {y : ℝ} {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 1) (h3 : |w.im - y| ≤ 1 / 2) :
    w ∈ closedBall (cen y) (8 / 5) := by
  rw [mem_closedBall_iff_norm]
  have e : ‖w - cen y‖ ^ 2 = (w.re - 2) ^ 2 + (w.im - y) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sub_re, sub_im, cen_re, cen_im]
    ring
  have ha : (w.im - y) ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp h3
    nlinarith
  have hb : (w.re - 2) ^ 2 ≤ 9 / 4 := by nlinarith
  nlinarith [norm_nonneg (w - cen y)]

/-- **Caixas**: pontos distintos da faixa com `|Im ρ − y| ≤ ½` têm `Σ m_ρ ≤ 2 Lc |y|`. -/
theorem caixa_le {y : ℝ} (hy : 4 ≤ |y|) (B : Finset ℂ)
    (hB : ∀ ρ ∈ B, 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - y| ≤ 1 / 2) :
    (∑ ρ ∈ B, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ 2 * Lc |y| := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not B (fun ρ : ℂ => 1 / 2 ≤ ρ.re)]
  have hy' : 4 ≤ |-y| := by rwa [abs_neg]
  have h1 : (∑ ρ ∈ B.filter (fun ρ : ℂ => 1 / 2 ≤ ρ.re), (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
      Lc |y| := by
    have hs := soma_ordem_le (isCompact_closedBall (cen y) (8 / 5))
      (zeta_analitica_bola hy (by norm_num)) (B.filter (fun ρ : ℂ => 1 / 2 ≤ ρ.re))
      (fun ρ hρ => by
        rw [Finset.mem_filter] at hρ
        obtain ⟨_, h1', h3⟩ := hB ρ hρ.1
        exact caixa_na_bola hρ.2 h1'.le h3)
      (fun ρ hρ => by
        rw [Finset.mem_filter] at hρ
        obtain ⟨h0, h1', _⟩ := hB ρ hρ.1
        exact ordem_zeta_finita h0 (by rintro rfl; simp at h1'))
    have hc : ((∑ w ∈ B.filter (fun ρ : ℂ => 1 / 2 ≤ ρ.re),
        (analyticOrderNatAt riemannZeta w : ℤ) : ℤ) : ℝ) ≤
        ((∑ᶠ u, MeromorphicOn.divisor riemannZeta (closedBall (cen y) (8 / 5)) u : ℤ) : ℝ) := by
      exact_mod_cast hs
    push_cast at hc
    exact hc.trans (jensen_local hy)
  have h2 : (∑ ρ ∈ B.filter (fun ρ : ℂ => ¬ 1 / 2 ≤ ρ.re),
      (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ Lc |y| := by
    set B₂ := B.filter (fun ρ : ℂ => ¬ 1 / 2 ≤ ρ.re) with hB₂
    have hinj : Set.InjOn (fun ρ : ℂ => 1 - ρ) B₂ := fun a _ b _ h => by
      have h' : 1 - a = 1 - b := h
      linear_combination -h'
    have e : (∑ ρ ∈ B₂, (analyticOrderNatAt riemannZeta ρ : ℝ)) =
        ∑ w ∈ B₂.image (fun ρ : ℂ => 1 - ρ), (analyticOrderNatAt riemannZeta w : ℝ) := by
      rw [Finset.sum_image hinj]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      rw [Finset.mem_filter] at hρ
      obtain ⟨h0, h1', _⟩ := hB ρ hρ.1
      rw [ordemNat_zeta_reflexao h0 h1']
    have hmem : ∀ w ∈ B₂.image (fun ρ : ℂ => 1 - ρ),
        0 < w.re ∧ 1 / 2 < w.re ∧ w.re < 1 ∧ |w.im - -y| ≤ 1 / 2 := by
      intro w hw
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
      rw [Finset.mem_filter] at hρ
      obtain ⟨h0, h1', h3⟩ := hB ρ hρ.1
      have hn := hρ.2
      simp only [sub_re, one_re, sub_im, one_im]
      refine ⟨by linarith, by linarith, by linarith, ?_⟩
      have : (0 - ρ.im - -y) = -(ρ.im - y) := by ring
      rw [this, abs_neg]
      exact h3
    have hs := soma_ordem_le (isCompact_closedBall (cen (-y)) (8 / 5))
      (zeta_analitica_bola hy' (by norm_num)) (B₂.image (fun ρ : ℂ => 1 - ρ))
      (fun w hw => by
        obtain ⟨_, h1', h2', h3⟩ := hmem w hw
        exact caixa_na_bola h1'.le h2'.le h3)
      (fun w hw => by
        obtain ⟨h0, _, h2', _⟩ := hmem w hw
        exact ordem_zeta_finita h0 (by rintro rfl; simp at h2'))
    have hc : ((∑ w ∈ B₂.image (fun ρ : ℂ => 1 - ρ),
        (analyticOrderNatAt riemannZeta w : ℤ) : ℤ) : ℝ) ≤
        ((∑ᶠ u, MeromorphicOn.divisor riemannZeta (closedBall (cen (-y)) (8 / 5)) u : ℤ) : ℝ) := by
      exact_mod_cast hs
    push_cast at hc
    rw [e]
    have := jensen_local hy'
    rw [abs_neg] at this
    exact hc.trans this
  linarith

/-! ## 5. `N(T + 1) − N(T) = O(log T)` -/

theorem N_succ (T : ℝ) :
    (ATK.FechamentoO1.N (T + 1) : ℝ) - ATK.FechamentoO1.N T =
      ∑ ρ ∈ (ATK.FechamentoO1.zerosAte_finito (T + 1)).toFinset \
        (ATK.FechamentoO1.zerosAte_finito T).toFinset, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
  have hsub : (ATK.FechamentoO1.zerosAte_finito T).toFinset ⊆
      (ATK.FechamentoO1.zerosAte_finito (T + 1)).toFinset := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ ⊢
    obtain ⟨hz, h0, h1⟩ := hρ
    exact ⟨hz, h0, by linarith⟩
  unfold ATK.FechamentoO1.N
  rw [← Finset.sum_sdiff hsub]
  push_cast
  ring

/-- **`N(T + 1) − N(T) ≤ 2 Lc(T + ½)`** para `T ≥ 4`. -/
theorem N_succ_le {T : ℝ} (hT : 4 ≤ T) :
    (ATK.FechamentoO1.N (T + 1) : ℝ) - ATK.FechamentoO1.N T ≤ 2 * Lc (T + 1 / 2) := by
  rw [N_succ]
  have hy : 4 ≤ |T + 1 / 2| := by
    rw [abs_of_pos (by linarith)]
    linarith
  have := caixa_le hy ((ATK.FechamentoO1.zerosAte_finito (T + 1)).toFinset \
      (ATK.FechamentoO1.zerosAte_finito T).toFinset) (fun ρ hρ => by
    rw [Finset.mem_sdiff, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset] at hρ
    obtain ⟨⟨hz, h0, h1⟩, hn⟩ := hρ
    have hT' : T < ρ.im := by
      by_contra h
      exact hn ⟨hz, h0, le_of_not_gt h⟩
    refine ⟨hz.2.1, hz.2.2, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
  rw [abs_of_pos (by linarith : (0 : ℝ) < T + 1 / 2)] at this
  exact this

/-- **`N(T + 1) − N(T) = O(log T)`**. -/
theorem N_local_O_log : ∃ C : ℝ, ∀ T : ℝ, 4 ≤ T →
    (ATK.FechamentoO1.N (T + 1) : ℝ) - ATK.FechamentoO1.N T ≤ C * Real.log T := by
  set b := 2 - π ^ 2 / 6 with hb
  have hb0 : 0 < b := ATK.BLProva.dois_menos_pos
  set l := Real.log (19 / 16) with hl
  have hl0 : 0 < l := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨2 * (4 + |Real.log b| / Real.log 4) / l, fun T hT => ?_⟩
  have hL4 : Real.log 4 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hL0 : 0 < Real.log T := lt_of_lt_of_le hl4 hL4
  refine (N_succ_le hT).trans ?_
  unfold Lc
  rw [← hb, ← hl, Real.log_div (by linarith) hb0.ne']
  have h3 : (64 : ℝ) ≤ T ^ 3 := by
    calc (64 : ℝ) = 4 ^ 3 := by norm_num
      _ ≤ T ^ 3 := pow_le_pow_left₀ (by norm_num) hT 3
  have hpow : 15 * (T + 1 / 2) + 62 ≤ T ^ 4 := by
    have : T ^ 4 = T ^ 3 * T := by ring
    rw [this]
    nlinarith
  have hq : Real.log (15 * (T + 1 / 2) + 62) ≤ 4 * Real.log T := by
    have := Real.log_le_log (by linarith) hpow
    rw [Real.log_pow] at this
    push_cast at this
    exact this
  have hA : -Real.log b ≤ |Real.log b| / Real.log 4 * Real.log T := by
    have h1 : -Real.log b ≤ |Real.log b| := neg_le_abs _
    have h2 : |Real.log b| ≤ |Real.log b| / Real.log 4 * Real.log T := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl4]
      exact mul_le_mul_of_nonneg_left hL4 (abs_nonneg _)
    linarith
  have hnum : Real.log (15 * (T + 1 / 2) + 62) - Real.log b ≤
      (4 + |Real.log b| / Real.log 4) * Real.log T := by nlinarith
  calc 2 * ((Real.log (15 * (T + 1 / 2) + 62) - Real.log b) / l)
      ≤ 2 * ((4 + |Real.log b| / Real.log 4) * Real.log T / l) := by gcongr
    _ = _ := by ring

/-! ## 6. `Σ_ρ m_ρ/|ρ|² < ∞` -/

/-- O termo de comparação dos blocos `⌈|Im ρ|⌉ = n`. -/
noncomputable def gq (n : ℕ) : ℝ :=
  if 14 ≤ n then 4 * Lc ((n : ℝ) - 1 / 2) / ((n : ℝ) - 1) ^ 2 else 0

theorem gq_nonneg (n : ℕ) : 0 ≤ gq n := by
  unfold gq
  split_ifs with h
  · have : (14 : ℝ) ≤ n := by exact_mod_cast h
    have := Lc_nonneg (t := (n : ℝ) - 1 / 2) (by linarith)
    positivity
  · exact le_rfl

theorem gq_le (n : ℕ) :
    gq n ≤ 16 * (6 + |Real.log (2 - π ^ 2 / 6)|) / Real.log (19 / 16) * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  set b := 2 - π ^ 2 / 6 with hb
  have hb0 : 0 < b := ATK.BLProva.dois_menos_pos
  have hl0 : 0 < Real.log (19 / 16) := Real.log_pos (by norm_num)
  set K := 16 * (6 + |Real.log b|) / Real.log (19 / 16) with hK
  have hK0 : 0 ≤ K := by positivity
  unfold gq
  split_ifs with h
  · set x : ℝ := (n : ℝ) with hx
    have hx14 : (14 : ℝ) ≤ x := by rw [hx]; exact_mod_cast h
    have hx0 : 0 < x := by linarith
    have hr : 1 ≤ x ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have hlog : Real.log x ≤ 2 * x ^ (1 / 2 : ℝ) := by
      have := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 2)
      linarith
    have hcub : 15 * (x - 1 / 2) + 62 ≤ x ^ 3 := by
      have hxx : 196 ≤ x * x := by nlinarith
      have := mul_le_mul_of_nonneg_right hxx hx0.le
      nlinarith
    have hq : Real.log (15 * (x - 1 / 2) + 62) ≤ 3 * Real.log x := by
      have := Real.log_le_log (by linarith) hcub
      rw [Real.log_pow] at this
      push_cast at this
      exact this
    have hLc : Lc (x - 1 / 2) ≤ (6 + |Real.log b|) * x ^ (1 / 2 : ℝ) / Real.log (19 / 16) := by
      unfold Lc
      rw [← hb, Real.log_div (by linarith) hb0.ne']
      apply div_le_div_of_nonneg_right _ hl0.le
      have h1 : -Real.log b ≤ |Real.log b| := neg_le_abs _
      have h2 : |Real.log b| ≤ |Real.log b| * x ^ (1 / 2 : ℝ) := le_mul_of_one_le_right (abs_nonneg _) hr
      nlinarith
    have hp : x ^ (1 / 2 : ℝ) * x ^ (3 / 2 : ℝ) = x ^ 2 := by
      rw [← Real.rpow_add hx0]
      norm_num
    have hpos2 : 0 < x ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hpos1 : 0 < (x - 1) ^ 2 := by nlinarith
    rw [← div_eq_mul_inv, div_le_div_iff₀ hpos1 hpos2]
    have hd : x ^ 2 ≤ 4 * (x - 1) ^ 2 := by nlinarith
    calc 4 * Lc (x - 1 / 2) * x ^ (3 / 2 : ℝ)
        ≤ 4 * ((6 + |Real.log b|) * x ^ (1 / 2 : ℝ) / Real.log (19 / 16)) * x ^ (3 / 2 : ℝ) := by
          gcongr
      _ = 4 * (6 + |Real.log b|) / Real.log (19 / 16) * (x ^ (1 / 2 : ℝ) * x ^ (3 / 2 : ℝ)) := by
          ring
      _ = 4 * (6 + |Real.log b|) / Real.log (19 / 16) * x ^ 2 := by rw [hp]
      _ ≤ 4 * (6 + |Real.log b|) / Real.log (19 / 16) * (4 * (x - 1) ^ 2) := by
          gcongr
      _ = K * (x - 1) ^ 2 := by rw [hK]; ring
  · have : 0 ≤ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by positivity
    positivity

theorem summable_gq : Summable gq :=
  Summable.of_nonneg_of_le gq_nonneg gq_le
    ((Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left _)

/-- **`Σ_ρ m_ρ/|ρ|² < ∞`**, sobre todos os zeros da faixa crítica. -/
theorem soma_ordem_inv_quadrado :
    Summable (fun ρ : ATK.ZetaSimetria.Z =>
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2) := by
  classical
  refine summable_of_sum_le (c := ∑' n, gq n) (fun ρ => by simp only [Pi.zero_apply]; positivity)
    (fun u => ?_)
  set F : ℂ → ℝ := fun ρ => (analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖ ^ 2 with hF
  set v := u.map (Function.Embedding.subtype (· ∈ ATK.ZetaSimetria.Z)) with hv
  have hsum : ∑ x ∈ u, (analyticOrderNatAt riemannZeta (x : ℂ) : ℝ) / ‖(x : ℂ)‖ ^ 2 =
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
  refine le_trans (Finset.sum_le_sum fun n hn => ?_) (summable_gq.sum_le_tsum _
    (fun i _ => gq_nonneg i))
  -- o bloco `κ ρ = n`
  set W := v.filter (fun ρ => κ ρ = n) with hW
  obtain ⟨ρ₀, hρ₀, hκ₀⟩ := Finset.mem_image.mp hn
  have hn14 : 14 ≤ n := hκ₀ ▸ (hκ1 ρ₀ hρ₀).2.2
  have hn' : (14 : ℝ) ≤ n := by exact_mod_cast hn14
  have hWv : ∀ ρ ∈ W, ρ ∈ v ∧ κ ρ = n := fun ρ hρ => Finset.mem_filter.mp hρ
  have hpos1 : 0 < ((n : ℝ) - 1) ^ 2 := by nlinarith
  -- `F ρ ≤ m_ρ/(n − 1)²`
  have hF : ∀ ρ ∈ W, F ρ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) / ((n : ℝ) - 1) ^ 2 := by
    intro ρ hρ
    obtain ⟨hρv, hκn⟩ := hWv ρ hρ
    obtain ⟨h1, _, _⟩ := hκ1 ρ hρv
    rw [hκn] at h1
    have hn1 : ((n : ℝ) - 1) ≤ ‖ρ‖ := h1.le.trans (Complex.abs_im_le_norm ρ)
    have hsq : ((n : ℝ) - 1) ^ 2 ≤ ‖ρ‖ ^ 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
      gcongr
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos1 hsq
  -- as duas caixas `Im ρ ≈ ±(n − ½)`
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
  have hW : (∑ ρ ∈ W, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ 4 * Lc ((n : ℝ) - 1 / 2) := by
    rw [← Finset.sum_filter_add_sum_filter_not W (fun ρ => 0 < ρ.im)]
    rw [abs_of_pos (by linarith : (0 : ℝ) < (n : ℝ) - 1 / 2)] at hmais hmenos
    linarith
  calc ∑ ρ ∈ v with κ ρ = n, F ρ
      ≤ ∑ ρ ∈ W, (analyticOrderNatAt riemannZeta ρ : ℝ) / ((n : ℝ) - 1) ^ 2 :=
        Finset.sum_le_sum hF
    _ = (∑ ρ ∈ W, (analyticOrderNatAt riemannZeta ρ : ℝ)) / ((n : ℝ) - 1) ^ 2 := by
        rw [Finset.sum_div]
    _ ≤ 4 * Lc ((n : ℝ) - 1 / 2) / ((n : ℝ) - 1) ^ 2 :=
        div_le_div_of_nonneg_right hW hpos1.le
    _ = gq n := by simp [gq, hn14]

/-- **`Σ_ρ 1/|ρ|² < ∞`** (sem multiplicidade). -/
theorem soma_inv_quadrado :
    Summable (fun ρ : ATK.ZetaSimetria.Z => 1 / ‖(ρ : ℂ)‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_) soma_ordem_inv_quadrado
  have hz := ρ.2
  have h0 := hz.2.1
  have h1 : (ρ : ℂ) ≠ 1 := by
    intro h
    have := hz.2.2
    rw [h, one_re] at this
    exact lt_irrefl 1 this
  have htop := ordem_zeta_finita h0 h1
  have hord : 1 ≤ analyticOrderNatAt riemannZeta (ρ : ℂ) := by
    by_contra hlt
    have h0' : analyticOrderNatAt riemannZeta (ρ : ℂ) = 0 := by omega
    exact ((ATK.ArgPrincipio.ordemNat_zero_iff (analyticOn_riemannZeta _ h1) htop).mp h0') hz.1
  have : (1 : ℝ) ≤ analyticOrderNatAt riemannZeta (ρ : ℂ) := by exact_mod_cast hord
  gcongr

end ATK.ZeroClasses.JensenLocal

#print axioms ATK.ZeroClasses.JensenLocal.cen_re
#print axioms ATK.ZeroClasses.JensenLocal.cen_im
#print axioms ATK.ZeroClasses.JensenLocal.coord_bola
#print axioms ATK.ZeroClasses.JensenLocal.perto_cen
#print axioms ATK.ZeroClasses.JensenLocal.ne_um_de
#print axioms ATK.ZeroClasses.JensenLocal.cota_zeta_circ
#print axioms ATK.ZeroClasses.JensenLocal.zeta_analitica_bola
#print axioms ATK.ZeroClasses.JensenLocal.Lc_nonneg
#print axioms ATK.ZeroClasses.JensenLocal.jensen_local
#print axioms ATK.ZeroClasses.JensenLocal.soma_ordem_le
#print axioms ATK.ZeroClasses.JensenLocal.ordem_zeta_finita
#print axioms ATK.ZeroClasses.JensenLocal.ordem_xi_reflexao
#print axioms ATK.ZeroClasses.JensenLocal.ordemNat_zeta_reflexao
#print axioms ATK.ZeroClasses.JensenLocal.caixa_na_bola
#print axioms ATK.ZeroClasses.JensenLocal.caixa_le
#print axioms ATK.ZeroClasses.JensenLocal.N_succ
#print axioms ATK.ZeroClasses.JensenLocal.N_succ_le
#print axioms ATK.ZeroClasses.JensenLocal.N_local_O_log
#print axioms ATK.ZeroClasses.JensenLocal.gq_nonneg
#print axioms ATK.ZeroClasses.JensenLocal.gq_le
#print axioms ATK.ZeroClasses.JensenLocal.summable_gq
#print axioms ATK.ZeroClasses.JensenLocal.soma_ordem_inv_quadrado
#print axioms ATK.ZeroClasses.JensenLocal.soma_inv_quadrado
