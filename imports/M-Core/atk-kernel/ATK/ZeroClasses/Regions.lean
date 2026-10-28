import ATK.ZeroClasses.Zeta

/-!
# ATK-ZERO-CLASSES — o cerco: região residual, compactos, mínimos e certificados

* **produtor `F(σ,t) = |ζ(σ+it)|²`**: `F ≥ 0` (`F_nonneg`); `F > 0 ⟺ ζ ≠ 0` (`F_pos_iff`) — a positividade
  estrita **não** decorre da não negatividade; incondicionalmente `F > 0` na faixa baixa
  `t² < 3/4` (`F_pos_baixo`) e na borda `σ ≤ c(t)` (`F_pos_borda`); **a obrigação exata que resta é RH**
  (`obrigacao_exata`: `RH ⟺ F > 0` em `0 < σ < 1/2, t > 0`);
* **redução por simetria**: `Z_L = ∅ ⟺ Z_R = ∅` (`ZL_vazio_iff_ZR`), `RH ⟺ Z_L = ∅` (`rh_iff_ZL`),
  `RH ⟺ Ω` sem zeros, `Ω = {0 < Re s < 1/2, Im s > 0}` (`rh_iff_Omega`);
* **compactos** `K_n = [1/n, 1/2 − 1/n] × [1/n, n]`: compactos (`isCompact_K`), crescentes
  (`K_mono`), dentro de `Ω` (`K_sub_Omega`), **cobrem `Ω`** (`cobertura`). **Correção**: `K₃ = ∅`
  (`K_tres`, pois `1/3 > 1/6`); `K_n ≠ ∅` para `n ≥ 4` (`K_nonempty`);
* **mínimos** `m_n = inf_{K_n} |ζ|`: atingidos (`m_atingido`), `0 ≤ m_{n+1} ≤ m_n` (`m_antitone`),
  `m₃ = 0` por convenção (`m_tres`); **`m_n > 0 ⟺ K_n sem zeros`** para `n ≥ 4` (`m_pos_iff`, camada B);
  **`RH ⟺ ∀ n ≥ 4, m_n > 0`** (`rh_iff_m_pos`); e, incondicionalmente, **`m_n → 0`** (`m_tende_zero`,
  pelo zero crítico certificado): **não há cota uniforme** (`sem_cota_uniforme`) — a camada C só pode
  ser positividade ponto a ponto;
* **certificados** (`PositiveCertificate`): excluem zeros (`certificate_excludes_zeros`), ficam abaixo dos
  mínimos (`cert_le_m`), e **existe um certificado ⟺ RH** (`rh_iff_certificado`). Certificados de malha:
  `|f(c)| > L·h` nos centros + variação `≤ L·h` ⇒ sem zeros (`certificado_malha`), com a variação vinda de
  uma cota da derivada num convexo (`certificado_derivada`).

Para um `n` fixo, `m_n > 0` é uma afirmação finita, verificável por aritmética intervalar certificada: o
kernel já a faz para `ζ` na reta crítica (`ATK.ZeroCert.mem_zetaI`, §4f); para `K_n` (`σ < 1/2`) falta
estender a avaliação e montar a malha (BUILD_PENDING, mecânico). Para todo `n` é RH.
-/

open Complex ComplexConjugate Set Filter Topology Metric

namespace ATK.ZeroClasses.Regions

open ATK.ZeroClasses ATK.ZeroClasses.Zeta

/-! ## 1. O produtor `F` -/

noncomputable def F (σ t : ℝ) : ℝ := ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2

theorem F_nonneg (σ t : ℝ) : 0 ≤ F σ t := by unfold F; positivity

theorem F_pos_iff (σ t : ℝ) : 0 < F σ t ↔ riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
  unfold F
  constructor
  · intro h hz
    rw [hz, norm_zero] at h
    norm_num at h
  · intro h
    have := norm_pos_iff.mpr h
    positivity

theorem re_ponto (σ t : ℝ) : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
theorem im_ponto (σ t : ℝ) : ((σ : ℂ) + (t : ℂ) * I).im = t := by simp

theorem ponto_eta (s : ℂ) : (s.re : ℂ) + (s.im : ℂ) * I = s := Complex.re_add_im s

/-- Incondicional: `F > 0` na faixa baixa. -/
theorem F_pos_baixo {σ t : ℝ} (h0 : 0 < σ) (h1 : σ < 1) (ht : t ^ 2 < 3 / 4) : 0 < F σ t :=
  (F_pos_iff σ t).mpr (ATK.ZetaRetangulo.zeta_ne_zero_baixo (by simpa using h0) (by simpa using h1)
    (by simpa using ht))

/-- Incondicional: `F > 0` na borda `0 < σ ≤ c(t) = 1/(256·A(t))`. -/
theorem F_pos_borda {σ t : ℝ} (h0 : 0 < σ) (hb : σ ≤ 1 / (256 * ATK.ZetaRegiao.A t)) :
    0 < F σ t := by
  rw [F_pos_iff]
  intro hz
  have hA := ATK.ZetaRegiao.A_ge t
  have hσ1 : σ < 1 := by
    have : 1 / (256 * ATK.ZetaRegiao.A t) ≤ 1 / 256 :=
      one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    linarith
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hn : NaoTrivial s := by
    rcases dicotomia (s := s) hz with ht | hn
    · have := ATK.ZetaSimetria.re_trivial ht
      rw [re_ponto] at this; linarith
    · exact hn
  have := (ATK.ZetaRegiao.faixa_estreitada s hn).1
  rw [re_ponto, im_ponto] at this
  linarith

/-! ## 2. Redução por simetria -/

/-- A região residual. -/
def Omega : Set ℂ := {s | 0 < s.re ∧ s.re < 1 / 2 ∧ 0 < s.im}

def ZL : Set ℂ := {s | s ∈ ATK.ZetaSimetria.Z ∧ s.re < 1 / 2}
def ZR : Set ℂ := {s | s ∈ ATK.ZetaSimetria.Z ∧ 1 / 2 < s.re}

theorem tensao_ZR {s : ℂ} (h : s ∈ ZR) : ATK.ZetaSimetria.tensao s ∈ ZL :=
  ⟨ATK.ZetaSimetria.tensao_mem_Z h.1, by rw [ATK.ZetaSimetria.re_tensao]; linarith [h.2]⟩

theorem tensao_ZL {s : ℂ} (h : s ∈ ZL) : ATK.ZetaSimetria.tensao s ∈ ZR :=
  ⟨ATK.ZetaSimetria.tensao_mem_Z h.1, by rw [ATK.ZetaSimetria.re_tensao]; linarith [h.2]⟩

/-- **`Z_L = ∅ ⟺ Z_R = ∅`.** -/
theorem ZL_vazio_iff_ZR : ZL = ∅ ↔ ZR = ∅ := by
  constructor
  · intro h
    ext s
    simp only [mem_empty_iff_false, iff_false]
    intro hs
    have := tensao_ZR hs
    rw [h] at this
    exact this
  · intro h
    ext s
    simp only [mem_empty_iff_false, iff_false]
    intro hs
    have := tensao_ZL hs
    rw [h] at this
    exact this

/-- **`RH ⟺ Z_L = ∅`.** -/
theorem rh_iff_ZL : RiemannHypothesis ↔ ZL = ∅ := by
  rw [rh_iff_classes]
  constructor
  · intro h
    ext s
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨hs, hl⟩
    have := (h s hs).2
    linarith
  · intro h s hs
    refine ⟨hs.1, ?_⟩
    rcases lt_trichotomy s.re (1 / 2) with hl | he | hr
    · exact absurd (h ▸ (show s ∈ ZL from ⟨hs, hl⟩)) (Set.notMem_empty s)
    · exact he
    · exact absurd ((ZL_vazio_iff_ZR.mp h) ▸ (show s ∈ ZR from ⟨hs, hr⟩)) (Set.notMem_empty s)

/-- **`RH ⟺ ζ` não se anula em `Ω`.** -/
theorem rh_iff_Omega : RiemannHypothesis ↔ ∀ s ∈ Omega, riemannZeta s ≠ 0 := by
  rw [rh_iff_ZL]
  constructor
  · rintro h s ⟨h0, h1, _⟩ hz
    have hs : s ∈ ATK.ZetaSimetria.Z := ⟨hz, h0, by linarith⟩
    have : s ∈ ZL := ⟨hs, h1⟩
    rw [h] at this
    exact this
  · intro h
    ext s
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨hs, hl⟩
    rcases lt_or_gt_of_ne (ATK.ZetaSimetria.im_ne_zero_of_mem_Z hs) with him | him
    · have hc : conj s ∈ Omega := ⟨by simpa using hs.2.1, by simpa using hl, by simp; linarith⟩
      exact h _ hc (by rw [riemannZeta_conj, hs.1, map_zero])
    · exact h s ⟨hs.2.1, hl, him⟩ hs.1

/-- **A obrigação exata**: `RH ⟺ F(σ,t) > 0` para `0 < σ < 1/2`, `t > 0`. -/
theorem obrigacao_exata :
    RiemannHypothesis ↔ ∀ σ t : ℝ, 0 < σ → σ < 1 / 2 → 0 < t → 0 < F σ t := by
  rw [rh_iff_Omega]
  constructor
  · intro h σ t h0 h1 ht
    exact (F_pos_iff σ t).mpr (h _ ⟨by simpa using h0, by simpa using h1, by simpa using ht⟩)
  · intro h s ⟨h0, h1, ht⟩
    have := (F_pos_iff s.re s.im).mp (h s.re s.im h0 h1 ht)
    rwa [ponto_eta] at this

/-! ## 3. Os compactos `K_n` -/

def K (n : ℕ) : Set ℂ :=
  {s | 1 / (n : ℝ) ≤ s.re ∧ s.re ≤ 1 / 2 - 1 / (n : ℝ) ∧ 1 / (n : ℝ) ≤ s.im ∧ s.im ≤ n}

/-- **`K₃ = ∅`**: `1/3 > 1/2 − 1/3`. -/
theorem K_tres : K 3 = ∅ := by
  ext s
  simp only [K, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2, _, _⟩
  norm_num at h1 h2
  linarith

theorem K_nonempty {n : ℕ} (hn : 4 ≤ n) : (K n).Nonempty := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hinv : (n : ℝ)⁻¹ ≤ 1 / 4 := by rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hn'
  refine ⟨(1 / 4 : ℂ) + I, ?_, ?_, ?_, ?_⟩
  · simp; linarith
  · simp; linarith
  · simp; linarith
  · simp; linarith

theorem K_mono {n n' : ℕ} (hn : 1 ≤ n) (h : n ≤ n') : K n ⊆ K n' := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnn : (n : ℝ) ≤ n' := by exact_mod_cast h
  have hinv : 1 / (n' : ℝ) ≤ 1 / n := one_div_le_one_div_of_le hn0 hnn
  rintro s ⟨h1, h2, h3, h4⟩
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem K_sub_Omega {n : ℕ} (hn : 1 ≤ n) : K n ⊆ Omega := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < 1 / (n : ℝ) := by positivity
  rintro s ⟨h1, h2, h3, _⟩
  exact ⟨by linarith, by linarith, by linarith⟩

theorem inv_le_de_lt {x r : ℝ} (hx : 0 < x) (hr : 0 < r) (h : 1 / x < r) : 1 / r ≤ x := by
  rw [div_lt_iff₀ hx] at h
  rw [div_le_iff₀ hr]
  linarith

/-- **`Ω = ⋃_{n ≥ 3} K_n`.** -/
theorem cobertura : (⋃ n ≥ 3, K n) = Omega := by
  ext s
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨n, hn, hs⟩
    exact K_sub_Omega (by omega) hs
  · rintro ⟨h0, h1, ht⟩
    have hd : 0 < 1 / 2 - s.re := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (max (max 3 (1 / s.re)) (max (1 / (1 / 2 - s.re)) (max (1 / s.im) s.im)))
    have h3 : (3 : ℝ) < n := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hnp : (0 : ℝ) < n := by linarith
    have ha : 1 / s.re < n := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hb : 1 / (1 / 2 - s.re) < n :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hn
    have hc : 1 / s.im < n :=
      lt_of_le_of_lt (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hn
    have hd' : s.im < n :=
      lt_of_le_of_lt (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hn
    refine ⟨n, by exact_mod_cast h3.le, inv_le_de_lt h0 hnp ha, ?_, inv_le_de_lt ht hnp hc, hd'.le⟩
    have := inv_le_de_lt hd hnp hb
    linarith

theorem isCompact_K (n : ℕ) : IsCompact (K n) := by
  have e : K n = (Complex.re ⁻¹' Icc (1 / (n : ℝ)) (1 / 2 - 1 / n)) ∩
      (Complex.im ⁻¹' Icc (1 / (n : ℝ)) n) := by
    ext s; simp only [K, mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Icc]; tauto
  have hc : IsClosed (K n) := by
    rw [e]
    exact (isClosed_Icc.preimage continuous_re).inter (isClosed_Icc.preimage continuous_im)
  refine Metric.isCompact_of_isClosed_isBounded hc ?_
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1 / 2 + 1 / n + n, fun s hs => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hs
  have hinv : 0 ≤ 1 / (n : ℝ) := by positivity
  have := Complex.norm_le_abs_re_add_abs_im s
  have hr : |s.re| ≤ 1 / 2 + 1 / n := by rw [abs_le]; constructor <;> linarith
  have hi : |s.im| ≤ n := by rw [abs_le]; constructor <;> linarith
  linarith

theorem um_nao_em_K (n : ℕ) : (1 : ℂ) ∉ K n := by
  rintro ⟨_, h2, _, _⟩
  have : 0 ≤ (n : ℝ)⁻¹ := by positivity
  simp at h2
  linarith

/-! ## 4. Os mínimos `m_n` -/

noncomputable def m (n : ℕ) : ℝ := sInf ((fun s => ‖riemannZeta s‖) '' K n)

theorem continuousOn_K (n : ℕ) : ContinuousOn (fun s => ‖riemannZeta s‖) (K n) := by
  intro s hs
  have hs1 : s ≠ 1 := fun h => um_nao_em_K n (h ▸ hs)
  exact (differentiableAt_riemannZeta hs1).continuousAt.norm.continuousWithinAt

theorem bdd (n : ℕ) : BddBelow ((fun s => ‖riemannZeta s‖) '' K n) :=
  ⟨0, by rw [mem_lowerBounds]; rintro _ ⟨w, _, rfl⟩; exact norm_nonneg _⟩

theorem m_nonneg (n : ℕ) : 0 ≤ m n :=
  Real.sInf_nonneg (by rintro _ ⟨w, _, rfl⟩; exact norm_nonneg _)

theorem m_le {n : ℕ} {s : ℂ} (hs : s ∈ K n) : m n ≤ ‖riemannZeta s‖ :=
  csInf_le (bdd n) ⟨s, hs, rfl⟩

theorem m_tres : m 3 = 0 := by
  unfold m
  rw [K_tres, image_empty, Real.sInf_empty]

/-- **O mínimo é atingido** (`n ≥ 4`). -/
theorem m_atingido {n : ℕ} (hn : 4 ≤ n) : ∃ s ∈ K n, ‖riemannZeta s‖ = m n := by
  obtain ⟨s, hs, hmin⟩ := (isCompact_K n).exists_isMinOn (K_nonempty hn) (continuousOn_K n)
  refine ⟨s, hs, ?_⟩
  have hl : IsLeast ((fun s => ‖riemannZeta s‖) '' K n) ‖riemannZeta s‖ := by
    refine ⟨⟨s, hs, rfl⟩, ?_⟩
    rw [mem_lowerBounds]
    rintro _ ⟨w, hw, rfl⟩
    exact hmin hw
  exact hl.csInf_eq.symm

/-- **`m_n > 0 ⟺ K_n` não contém zeros** (`n ≥ 4`). -/
theorem m_pos_iff {n : ℕ} (hn : 4 ≤ n) : 0 < m n ↔ ∀ s ∈ K n, riemannZeta s ≠ 0 := by
  constructor
  · intro h s hs hz
    have := m_le hs
    rw [hz, norm_zero] at this
    linarith
  · intro h
    obtain ⟨s, hs, he⟩ := m_atingido hn
    rw [← he]
    exact norm_pos_iff.mpr (h s hs)

/-- **`0 ≤ m_{n+1} ≤ m_n`.** -/
theorem m_antitone {n : ℕ} (hn : 4 ≤ n) : m (n + 1) ≤ m n := by
  obtain ⟨s, hs, he⟩ := m_atingido hn
  rw [← he]
  exact m_le (K_mono (by omega) (Nat.le_succ n) hs)

/-- **`RH ⟺ ∀ n ≥ 4, m_n > 0`.** -/
theorem rh_iff_m_pos : RiemannHypothesis ↔ ∀ n ≥ 4, 0 < m n := by
  rw [rh_iff_Omega]
  constructor
  · intro h n hn
    exact (m_pos_iff hn).mpr fun s hs => h s (K_sub_Omega (by omega) hs)
  · intro h s hs
    rw [← cobertura] at hs
    simp only [mem_iUnion, exists_prop] at hs
    obtain ⟨n, hn, hsn⟩ := hs
    have hs4 : s ∈ K (max n 4) := K_mono (by omega) (le_max_left _ _) hsn
    exact (m_pos_iff (le_max_right n 4)).mp (h _ (le_max_right n 4)) s hs4

/-- **`m_n → 0`** (incondicional): o zero crítico certificado `1/2 + iγ` é limite dos pontos
`(1/2 − 1/n) + iγ ∈ K_n`. Não há cota inferior uniforme; o alvo é `m_n > 0` para **cada** `n`. -/
theorem m_tende_zero : Tendsto m atTop (𝓝 0) := by
  obtain ⟨ρ, hρ, hre⟩ := existe_critico
  have him := ATK.ZetaSimetria.im_ne_zero_of_mem_Z hρ
  set γ := |ρ.im| with hγ
  have hγ0 : 0 < γ := abs_pos.mpr him
  have hz : riemannZeta (((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I) = 0 := by
    rcases lt_or_gt_of_ne him with h | h
    · have e : (((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I) = conj ρ := by
        apply Complex.ext
        · rw [re_ponto, conj_re, hre]
        · rw [im_ponto, conj_im, hγ, abs_of_neg h]
      rw [e, riemannZeta_conj, hρ.1, map_zero]
    · have e : (((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I) = ρ := by
        apply Complex.ext
        · rw [re_ponto, hre]
        · rw [im_ponto, hγ, abs_of_pos h]
      rw [e]; exact hρ.1
  set w : ℂ := ((1 / 2 : ℝ) : ℂ) + (γ : ℂ) * I with hw
  have hw1 : w ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    rw [hw, im_ponto] at this
    simp at this
    linarith
  let s : ℕ → ℂ := fun n => ((1 / 2 - 1 / (n : ℝ) : ℝ) : ℂ) + (γ : ℂ) * I
  have hs : Tendsto s atTop (𝓝 w) := by
    have h1 : Tendsto (fun n : ℕ => (1 / 2 - 1 / (n : ℝ) : ℝ)) atTop (𝓝 (1 / 2 - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_atTop_nhds_zero_nat
    rw [sub_zero] at h1
    exact ((Complex.continuous_ofReal.tendsto _).comp h1).add tendsto_const_nhds
  have hzt : Tendsto (fun n => ‖riemannZeta (s n)‖) atTop (𝓝 0) := by
    have := ((differentiableAt_riemannZeta hw1).continuousAt.tendsto.comp hs).norm
    rwa [hz, norm_zero] at this
  obtain ⟨N0, hN0⟩ := exists_nat_gt (max 4 (max (1 / γ) γ))
  have hev : ∀ᶠ n in atTop, s n ∈ K n := by
    filter_upwards [eventually_ge_atTop N0] with n hn
    have hn' : (N0 : ℝ) ≤ n := by exact_mod_cast hn
    have hlt : max 4 (max (1 / γ) γ) < n := hN0.trans_le hn'
    have h4 : (4 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hlt
    have hg1 : 1 / γ < n := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hlt
    have hg2 : γ < n := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hlt
    have hnp : (0 : ℝ) < n := by linarith
    have hinv : 1 / (n : ℝ) < 1 / 4 := one_div_lt_one_div_of_lt (by norm_num) h4
    refine ⟨?_, ?_, ?_, ?_⟩
    · show 1 / (n : ℝ) ≤ (s n).re
      simp only [s, re_ponto]; linarith
    · show (s n).re ≤ 1 / 2 - 1 / (n : ℝ)
      simp only [s, re_ponto]; exact le_rfl
    · show 1 / (n : ℝ) ≤ (s n).im
      simp only [s, im_ponto]; exact inv_le_de_lt hγ0 hnp hg1
    · show (s n).im ≤ n
      simp only [s, im_ponto]; exact hg2.le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hzt
    (Eventually.of_forall m_nonneg) (hev.mono fun n hn => m_le hn)

/-- **Não existe cota inferior uniforme** `m_n ≥ δ > 0`. -/
theorem sem_cota_uniforme : ¬ ∃ δ > 0, ∀ n ≥ 4, δ ≤ m n := by
  rintro ⟨δ, hδ, h⟩
  have := (m_tende_zero.eventually (gt_mem_nhds hδ)).and (eventually_ge_atTop 4)
  obtain ⟨n, h1, h2⟩ := this.exists
  linarith [h n h2]

/-! ## 5. Certificados -/

/-- Um certificado de positividade: `L_n > 0` e `L_n ≤ |f|` em `K_n`, para `n ≥ 3`. -/
def PositiveCertificate (K : ℕ → Set ℂ) (f : ℂ → ℂ) (L : ℕ → ℝ) : Prop :=
  ∀ n ≥ 3, 0 < L n ∧ ∀ s ∈ K n, L n ≤ ‖f s‖

theorem certificate_excludes_zeros {K : ℕ → Set ℂ} {f : ℂ → ℂ} {L : ℕ → ℝ}
    (h : PositiveCertificate K f L) : ∀ n ≥ 3, ∀ s ∈ K n, f s ≠ 0 := by
  intro n hn s hs hz
  obtain ⟨hpos, hbound⟩ := h n hn
  have hle := hbound s hs
  rw [hz, norm_zero] at hle
  exact (not_le_of_gt hpos) hle

theorem cert_le_m {L : ℕ → ℝ} (h : PositiveCertificate K riemannZeta L) {n : ℕ} (hn : 4 ≤ n) :
    L n ≤ m n :=
  le_csInf ((K_nonempty hn).image _) (by rintro _ ⟨w, hw, rfl⟩; exact (h n (by omega)).2 w hw)

/-- **Existe um certificado de positividade para `ζ` ⟺ RH.** -/
theorem rh_iff_certificado : RiemannHypothesis ↔ ∃ L, PositiveCertificate K riemannZeta L := by
  constructor
  · intro hrh
    have hm := rh_iff_m_pos.mp hrh
    refine ⟨fun n => if 4 ≤ n then m n else 1, fun n hn => ?_⟩
    by_cases h4 : 4 ≤ n
    · simp only [h4, ↓reduceIte]
      exact ⟨hm n h4, fun s hs => m_le hs⟩
    · have : n = 3 := by omega
      subst this
      simp only [h4, ↓reduceIte]
      exact ⟨one_pos, fun s hs => by rw [K_tres] at hs; exact absurd hs (Set.notMem_empty s)⟩
  · rintro ⟨L, hL⟩
    rw [rh_iff_Omega]
    intro s hs
    rw [← cobertura] at hs
    simp only [mem_iUnion, exists_prop] at hs
    obtain ⟨n, hn, hsn⟩ := hs
    exact certificate_excludes_zeros hL n hn s hsn

/-- **Certificado de malha**: centros `C` a distância `≤ h` de todo ponto de `K`, variação `≤ L·h`, e
`|f(c)| ≥ L·h + δ` nos centros ⇒ `|f| ≥ δ` em `K`. -/
theorem certificado_malha {f : ℂ → ℂ} {K' : Set ℂ} {C : Finset ℂ} {h L δ : ℝ}
    (hcov : ∀ z ∈ K', ∃ c ∈ C, ‖z - c‖ ≤ h)
    (hvar : ∀ z ∈ K', ∀ c ∈ C, ‖z - c‖ ≤ h → ‖f z - f c‖ ≤ L * h)
    (hval : ∀ c ∈ C, L * h + δ ≤ ‖f c‖) : ∀ z ∈ K', δ ≤ ‖f z‖ := by
  intro z hz
  obtain ⟨c, hc, hzc⟩ := hcov z hz
  have h1 := hvar z hz c hc hzc
  have h2 := hval c hc
  have h3 : ‖f c‖ ≤ ‖f z‖ + ‖f z - f c‖ := by
    have := norm_sub_le (f z) (f z - f c)
    rwa [sub_sub_cancel] at this
  linarith

/-- A variação vem de uma cota da derivada num convexo `U ⊇ K ∪ C`. -/
theorem certificado_derivada {f : ℂ → ℂ} {U K' : Set ℂ} {C : Finset ℂ} {h L δ : ℝ}
    (hU : Convex ℝ U) (hKU : K' ⊆ U) (hCU : ∀ c ∈ C, c ∈ U)
    (hd : ∀ x ∈ U, DifferentiableAt ℂ f x) (hb : ∀ x ∈ U, ‖deriv f x‖ ≤ L) (hL : 0 ≤ L)
    (hcov : ∀ z ∈ K', ∃ c ∈ C, ‖z - c‖ ≤ h) (hval : ∀ c ∈ C, L * h + δ ≤ ‖f c‖) :
    ∀ z ∈ K', δ ≤ ‖f z‖ := by
  refine certificado_malha hcov (fun z hz c hc hzc => ?_) hval
  have := hU.norm_image_sub_le_of_norm_deriv_le hd hb (hCU c hc) (hKU hz)
  calc ‖f z - f c‖ ≤ L * ‖z - c‖ := this
    _ ≤ L * h := mul_le_mul_of_nonneg_left hzc hL

end ATK.ZeroClasses.Regions

#print axioms ATK.ZeroClasses.Regions.F_nonneg
#print axioms ATK.ZeroClasses.Regions.F_pos_iff
#print axioms ATK.ZeroClasses.Regions.re_ponto
#print axioms ATK.ZeroClasses.Regions.im_ponto
#print axioms ATK.ZeroClasses.Regions.ponto_eta
#print axioms ATK.ZeroClasses.Regions.F_pos_baixo
#print axioms ATK.ZeroClasses.Regions.F_pos_borda
#print axioms ATK.ZeroClasses.Regions.tensao_ZR
#print axioms ATK.ZeroClasses.Regions.tensao_ZL
#print axioms ATK.ZeroClasses.Regions.ZL_vazio_iff_ZR
#print axioms ATK.ZeroClasses.Regions.rh_iff_ZL
#print axioms ATK.ZeroClasses.Regions.rh_iff_Omega
#print axioms ATK.ZeroClasses.Regions.obrigacao_exata
#print axioms ATK.ZeroClasses.Regions.K_tres
#print axioms ATK.ZeroClasses.Regions.K_nonempty
#print axioms ATK.ZeroClasses.Regions.K_mono
#print axioms ATK.ZeroClasses.Regions.K_sub_Omega
#print axioms ATK.ZeroClasses.Regions.inv_le_de_lt
#print axioms ATK.ZeroClasses.Regions.cobertura
#print axioms ATK.ZeroClasses.Regions.isCompact_K
#print axioms ATK.ZeroClasses.Regions.um_nao_em_K
#print axioms ATK.ZeroClasses.Regions.continuousOn_K
#print axioms ATK.ZeroClasses.Regions.bdd
#print axioms ATK.ZeroClasses.Regions.m_nonneg
#print axioms ATK.ZeroClasses.Regions.m_le
#print axioms ATK.ZeroClasses.Regions.m_tres
#print axioms ATK.ZeroClasses.Regions.m_atingido
#print axioms ATK.ZeroClasses.Regions.m_pos_iff
#print axioms ATK.ZeroClasses.Regions.m_antitone
#print axioms ATK.ZeroClasses.Regions.rh_iff_m_pos
#print axioms ATK.ZeroClasses.Regions.m_tende_zero
#print axioms ATK.ZeroClasses.Regions.sem_cota_uniforme
#print axioms ATK.ZeroClasses.Regions.certificate_excludes_zeros
#print axioms ATK.ZeroClasses.Regions.cert_le_m
#print axioms ATK.ZeroClasses.Regions.rh_iff_certificado
#print axioms ATK.ZeroClasses.Regions.certificado_malha
#print axioms ATK.ZeroClasses.Regions.certificado_derivada
