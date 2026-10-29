import ATK.BaezDuarteBridge

/-!
# ATK — Geometria da faixa crítica: extremos fechados, meio neutro, tensão, compressão e torção

Materialização, no kernel, da geometria "início fechado e fim fechado tendendo ao mesmo meio",
aplicada aos zeros da função zeta **da Mathlib**:

* **extremos fechados**: o semiplano fechado `Re s ≥ 1` não tem zeros (Mathlib) e o semiplano fechado
  `Re s ≤ 0` só tem os zeros triviais (`zero_trivial_de_re_nao_pos`, equação funcional);
* **o neutro**: o ponto `1/2` é o único ponto fixo da **tensão** `s ↦ 1 − s`; a reta `Re s = 1/2`
  é exatamente o conjunto fixo da **torção** `s ↦ 1 − s̄`; tensão, conjugação e torção formam um
  grupo de Klein;
* **o eixo neutro é livre de zeros**: `ζ(σ)` é real e **negativo** para `0 < σ < 1`
  (`zeta_real_neg`), em particular `ζ(1/2) < 0`; logo nenhum zero não trivial é real;
* **simetria dos zeros**: o conjunto `Z` dos zeros na faixa é invariante pela tensão, pela conjugação
  e pela torção; cada zero fora da reta tem órbita de 4 pontos distintos, cada zero na reta tem
  órbita de 2 (`quarteto`);
* **os dois processos são um só**: "fim fechado `[a, ∞)` livre de zeros" ⟺ "início fechado
  `(−∞, 1 − a]` livre de zeros não triviais" (`fim_iff_inicio`), e
  RH ⟺ os dois processos chegam ao meio (`riemann_iff_fim`, `riemann_iff_inicio`)
  ⟺ todo zero é fixo pela torção (`riemann_iff_torcao`)
  ⟺ toda compressão preserva as partes reais dos zeros (`riemann_iff_compressao`).

Nada aqui prova RH: os extremos conhecidos são `a = 1` e `b = 0`; o limite `a ↓ 1/2` é a
obrigação O1.
-/

open Complex Set Filter Topology MeasureTheory

namespace ATK.ZetaSimetria

open ATK.ZetaStrip ATK.BaezDuarteBridge

/-! ## As três operações sobre o neutro -/

/-- **Tensão**: reflexão `s ↦ 1 − s` em torno do neutro `1/2`. -/
def tensao (s : ℂ) : ℂ := 1 - s

/-- Espelho horizontal (conjugação). -/
noncomputable def espelho (s : ℂ) : ℂ := (starRingEnd ℂ) s

/-- **Torção**: `s ↦ 1 − s̄`, reflexão em torno da reta `Re s = 1/2`. -/
noncomputable def torcao (s : ℂ) : ℂ := 1 - (starRingEnd ℂ) s

/-- **Compressão** (`0 ≤ λ < 1`) ou tração (`λ > 1`) em direção ao neutro. -/
noncomputable def compressao (l : ℝ) (s : ℂ) : ℂ := 1 / 2 + (l : ℂ) * (s - 1 / 2)

theorem tensao_tensao (s : ℂ) : tensao (tensao s) = s := by unfold tensao; ring

theorem espelho_espelho (s : ℂ) : espelho (espelho s) = s := by unfold espelho; simp

theorem torcao_torcao (s : ℂ) : torcao (torcao s) = s := by unfold torcao; simp

/-- Klein: torção = tensão ∘ espelho = espelho ∘ tensão. -/
theorem torcao_eq (s : ℂ) : torcao s = tensao (espelho s) ∧ torcao s = espelho (tensao s) := by
  unfold torcao tensao espelho
  constructor
  · rfl
  · simp

theorem tensao_fixo_iff (s : ℂ) : tensao s = s ↔ s = 1 / 2 := by
  unfold tensao
  constructor
  · intro h; linear_combination -h / 2
  · intro h; rw [h]; ring

theorem espelho_fixo_iff (s : ℂ) : espelho s = s ↔ s.im = 0 := by
  unfold espelho
  exact Complex.conj_eq_iff_im

/-- **A reta crítica é exatamente o conjunto fixo da torção.** -/
theorem torcao_fixo_iff (s : ℂ) : torcao s = s ↔ s.re = 1 / 2 := by
  unfold torcao
  constructor
  · intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  · intro h
    apply Complex.ext
    · simp [h]; norm_num
    · simp

theorem re_tensao (s : ℂ) : (tensao s).re = 1 - s.re := by unfold tensao; simp

theorem re_torcao (s : ℂ) : (torcao s).re = 1 - s.re := by unfold torcao; simp

theorem re_compressao (l : ℝ) (s : ℂ) : (compressao l s).re = 1 / 2 + l * (s.re - 1 / 2) := by
  unfold compressao; simp

/-- O neutro `1/2` é fixo por toda compressão. -/
theorem compressao_neutro (l : ℝ) : compressao l (1 / 2) = 1 / 2 := by unfold compressao; ring

/-- Compressões compõem multiplicativamente. -/
theorem compressao_comp (l m : ℝ) (s : ℂ) :
    compressao l (compressao m s) = compressao (l * m) s := by
  unfold compressao; push_cast; ring

/-- Compressão comuta com a tensão. -/
theorem compressao_tensao (l : ℝ) (s : ℂ) : compressao l (tensao s) = tensao (compressao l s) := by
  unfold compressao tensao; ring

/-- **Rigidez do neutro**: toda aplicação que comuta com a tensão fixa `1/2`. -/
theorem rigidez_neutro (f : ℂ → ℂ) (hf : ∀ s, f (tensao s) = tensao (f s)) : f (1 / 2) = 1 / 2 := by
  have h := hf (1 / 2)
  rw [(tensao_fixo_iff _).mpr rfl] at h
  exact (tensao_fixo_iff _).mp h.symm

/-! ## Extremos fechados -/

/-- Zeros triviais (enunciado da Mathlib). -/
def Trivial (s : ℂ) : Prop := ∃ n : ℕ, s = -2 * (n + 1)

theorem re_trivial {s : ℂ} (h : Trivial s) : s.re < 0 := by
  obtain ⟨n, rfl⟩ := h
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp
  linarith

theorem nao_neg_nat_of_re_pos {s : ℂ} (h : 0 < s.re) : ∀ n : ℕ, s ≠ -n := by
  intro n hn
  have := congrArg Complex.re hn
  rw [neg_re, natCast_re] at this
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- **Início fechado**: no semiplano fechado `Re s ≤ 0`, todo zero é trivial. -/
theorem zero_trivial_de_re_nao_pos {s : ℂ} (hz : riemannZeta s = 0) (hre : s.re ≤ 0) :
    Trivial s := by
  set w : ℂ := 1 - s with hw
  have hwre : 1 ≤ w.re := by rw [hw, sub_re, one_re]; linarith
  have hw0 : ∀ n : ℕ, w ≠ -n := nao_neg_nat_of_re_pos (by linarith)
  have hζw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hw1 : w ≠ 1 := by
    intro hw1
    have hs0 : s = 0 := by linear_combination -hw1 + hw
    rw [hs0, riemannZeta_zero] at hz
    norm_num at hz
  have hfe := riemannZeta_one_sub hw0 hw1
  rw [show (1 : ℂ) - w = s by rw [hw]; ring, hz] at hfe
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h2π : (2 : ℂ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero hπ
  have hpow : ((2 : ℂ) * Real.pi) ^ (-w) ≠ 0 := by
    intro hp
    rw [cpow_eq_zero_iff] at hp
    exact h2π hp.1
  have hΓ : Gamma w ≠ 0 := Complex.Gamma_ne_zero hw0
  by_contra htriv
  have hcos : Complex.cos (Real.pi * w / 2) ≠ 0 := by
    intro hc
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
    have h2 : w * Real.pi = (2 * k + 1) * Real.pi := by linear_combination 2 * hk
    have hwk : w = 2 * k + 1 := mul_right_cancel₀ hπ h2
    have hre' : w.re = 2 * (k : ℝ) + 1 := by rw [hwk]; simp
    have hk0 : (0 : ℤ) ≤ k := by
      by_contra hneg
      have : k ≤ -1 := by omega
      have : (k : ℝ) ≤ -1 := by exact_mod_cast this
      linarith
    have hk1 : k ≠ 0 := by
      intro hk0'
      apply hw1
      rw [hwk, hk0']
      simp
    apply htriv
    refine ⟨(k - 1).toNat, ?_⟩
    have hcast : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
      have : (((k - 1).toNat : ℕ) : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [hcast]
    linear_combination hw - hwk
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hΓ) hcos) hζw)
    hfe.symm

/-- **Os dois extremos fechados juntos**: todo zero não trivial está na faixa aberta `0 < Re s < 1`. -/
theorem zero_na_faixa {s : ℂ} (hz : riemannZeta s = 0) (ht : ¬ Trivial s) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra h
    exact ht (zero_trivial_de_re_nao_pos hz (not_lt.mp h))
  · by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz

/-! ## O conjunto dos zeros na faixa e suas simetrias -/

/-- Zeros na faixa aberta (= zeros não triviais, por `zero_na_faixa`). -/
def Z : Set ℂ := {s | riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1}

theorem mem_Z_iff_nao_trivial (s : ℂ) : s ∈ Z ↔ riemannZeta s = 0 ∧ ¬ Trivial s := by
  constructor
  · rintro ⟨hz, h0, _⟩
    exact ⟨hz, fun ht => absurd (re_trivial ht) (not_lt.mpr h0.le)⟩
  · rintro ⟨hz, ht⟩
    exact ⟨hz, zero_na_faixa hz ht⟩

/-- **Invariância pela tensão** (equação funcional). -/
theorem tensao_mem_Z {s : ℂ} (hs : s ∈ Z) : tensao s ∈ Z := by
  obtain ⟨hz, h0, h1⟩ := hs
  have hs1 : s ≠ 1 := by intro h; rw [h, one_re] at h1; exact lt_irrefl 1 h1
  refine ⟨?_, by rw [re_tensao]; linarith, by rw [re_tensao]; linarith⟩
  unfold tensao
  rw [riemannZeta_one_sub (nao_neg_nat_of_re_pos h0) hs1, hz, mul_zero]

/-- **Invariância pelo espelho** (`riemannZeta_conj` da Mathlib). -/
theorem espelho_mem_Z {s : ℂ} (hs : s ∈ Z) : espelho s ∈ Z := by
  obtain ⟨hz, h0, h1⟩ := hs
  unfold espelho
  refine ⟨?_, by simpa using h0, by simpa using h1⟩
  rw [riemannZeta_conj, hz, map_zero]

/-- **Invariância pela torção.** -/
theorem torcao_mem_Z {s : ℂ} (hs : s ∈ Z) : torcao s ∈ Z := by
  rw [(torcao_eq s).1]
  exact tensao_mem_Z (espelho_mem_Z hs)

/-! ## O eixo neutro: `ζ(σ) < 0` em `(0, 1)` -/

theorem H_real {σ : ℝ} :
    H σ = ((∫ t in Ioi (1 : ℝ), t ^ (-σ - 1) * Int.fract t : ℝ) : ℂ) := by
  rw [H_eq_integral, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one (le_of_lt ht)
  rw [ofReal_mul, ofReal_cpow ht0]
  push_cast
  ring_nf

theorem H_real_nonneg (σ : ℝ) : 0 ≤ ∫ t in Ioi (1 : ℝ), t ^ (-σ - 1) * Int.fract t := by
  refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one (le_of_lt ht)
  exact mul_nonneg (Real.rpow_nonneg ht0 _) (Int.fract_nonneg t)

/-- **`ζ(σ)` é real e negativo para `0 < σ < 1`.** -/
theorem zeta_real_neg {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    ∃ x : ℝ, x < 0 ∧ riemannZeta σ = x := by
  set J := ∫ t in Ioi (1 : ℝ), t ^ (-σ - 1) * Int.fract t with hJ
  have hσ0 : (0 : ℝ) < (σ : ℂ).re := by simpa using h0
  have hσ1 : (σ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hH := H_eq_zeta hσ0 hσ1
  rw [H_real] at hH
  have hσne : (σ : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have hσm1 : (σ : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr hσ1
  have hζ : riemannZeta σ = ((σ / (σ - 1) - σ * J : ℝ) : ℂ) := by
    have e : riemannZeta σ = σ * (1 / ((σ : ℂ) - 1) - (J : ℂ)) := by
      rw [hH]
      field_simp
      ring
    rw [e]
    push_cast
    field_simp
  refine ⟨σ / (σ - 1) - σ * J, ?_, hζ⟩
  have hneg : σ / (σ - 1) < 0 := div_neg_of_pos_of_neg h0 (by linarith)
  have hJ0 : 0 ≤ σ * J := mul_nonneg h0.le (H_real_nonneg σ)
  linarith

theorem zeta_ne_zero_real {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) : riemannZeta σ ≠ 0 := by
  obtain ⟨x, hx, he⟩ := zeta_real_neg h0 h1
  rw [he]
  exact_mod_cast hx.ne

/-- **O neutro não é zero**: `ζ(1/2)` é um real negativo. -/
theorem zeta_meio_neg : ∃ x : ℝ, x < 0 ∧ riemannZeta (1 / 2) = x := by
  have := zeta_real_neg (σ := 1 / 2) (by norm_num) (by norm_num)
  simpa using this

/-- Nenhum zero não trivial é real. -/
theorem im_ne_zero_of_mem_Z {s : ℂ} (hs : s ∈ Z) : s.im ≠ 0 := by
  intro him
  obtain ⟨hz, h0, h1⟩ := hs
  have hs : s = (s.re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [hs] at hz
  exact zeta_ne_zero_real h0 h1 hz

/-! ## Quartetos: a órbita de Klein de um zero -/

/-- **Quarteto**: para `s ∈ Z`, o espelho e a tensão nunca fixam `s`; a torção fixa `s` ⟺
`Re s = 1/2`; fora da reta, os quatro pontos `s, s̄, 1 − s, 1 − s̄` são dois a dois distintos. -/
theorem quarteto {s : ℂ} (hs : s ∈ Z) :
    espelho s ≠ s ∧ tensao s ≠ s ∧ (torcao s = s ↔ s.re = 1 / 2) ∧
      (s.re ≠ 1 / 2 → torcao s ≠ s ∧ espelho s ≠ tensao s ∧ espelho s ≠ torcao s ∧
        tensao s ≠ torcao s) := by
  have him := im_ne_zero_of_mem_Z hs
  have hesp : espelho s ≠ s := fun h => him ((espelho_fixo_iff s).mp h)
  have hten : tensao s ≠ s := by
    intro h
    have h' := (tensao_fixo_iff s).mp h
    apply him
    rw [h']
    norm_num
  refine ⟨hesp, hten, torcao_fixo_iff s, fun hre => ⟨fun h => hre ((torcao_fixo_iff s).mp h), ?_, ?_, ?_⟩⟩
  · intro h
    apply hre
    have := congrArg Complex.re h
    unfold espelho tensao at this
    simp at this
    linarith
  · intro h
    apply him
    have := congrArg Complex.im h
    unfold espelho torcao at this
    simp at this
    linarith
  · intro h
    apply him
    have := congrArg Complex.im h
    unfold tensao torcao at this
    simp at this
    linarith

/-! ## Os dois processos (início → meio, fim → meio) e a Hipótese de Riemann -/

/-- Fim fechado `[a, ∞)` livre de zeros. -/
def FimLivre (a : ℝ) : Prop := ∀ s : ℂ, riemannZeta s = 0 → a ≤ s.re → False

/-- Início fechado `(−∞, b]` livre de zeros não triviais. -/
def InicioLivre (b : ℝ) : Prop := ∀ s : ℂ, riemannZeta s = 0 → ¬ Trivial s → s.re ≤ b → False

/-- Extremo conhecido do fim: `a = 1` (Mathlib). -/
theorem fimLivre_um : FimLivre 1 := fun _ hz h => riemannZeta_ne_zero_of_one_le_re h hz

/-- Extremo conhecido do início: `b = 0` (equação funcional). -/
theorem inicioLivre_zero : InicioLivre 0 := fun _ hz ht h => ht (zero_trivial_de_re_nao_pos hz h)

theorem fimLivre_mono {a a' : ℝ} (h : a ≤ a') (ha : FimLivre a) : FimLivre a' :=
  fun s hz hs => ha s hz (le_trans h hs)

theorem inicioLivre_mono {b b' : ℝ} (h : b' ≤ b) (hb : InicioLivre b) : InicioLivre b' :=
  fun s hz ht hs => hb s hz ht (le_trans hs h)

/-- **Os dois processos são o mesmo** (pela tensão): para `a > 0`,
`[a, ∞)` livre de zeros ⟺ `(−∞, 1 − a]` livre de zeros não triviais. -/
theorem fim_iff_inicio {a : ℝ} (ha : 0 < a) : FimLivre a ↔ InicioLivre (1 - a) := by
  constructor
  · intro hF s hz ht hs
    have hmem : s ∈ Z := (mem_Z_iff_nao_trivial s).mpr ⟨hz, ht⟩
    have h2 := tensao_mem_Z hmem
    exact hF _ h2.1 (by rw [re_tensao]; linarith)
  · intro hI s hz hs
    have ht : ¬ Trivial s := fun ht => by have := re_trivial ht; linarith
    have hmem : s ∈ Z := (mem_Z_iff_nao_trivial s).mpr ⟨hz, ht⟩
    have h2 := tensao_mem_Z hmem
    have ht2 : ¬ Trivial (tensao s) := ((mem_Z_iff_nao_trivial _).mp h2).2
    exact hI _ h2.1 ht2 (by rw [re_tensao]; linarith)

theorem riemann_imp_re {s : ℂ} (hRH : RiemannHypothesis) (hs : s ∈ Z) : s.re = 1 / 2 := by
  obtain ⟨hz, h0, h1⟩ := hs
  refine hRH s hz (fun ht => absurd (re_trivial ht) (not_lt.mpr h0.le)) ?_
  intro h; rw [h, one_re] at h1; exact lt_irrefl 1 h1

/-- **RH ⟺ o fim fechado chega ao meio**: `[a, ∞)` livre de zeros para todo `a > 1/2`. -/
theorem riemann_iff_fim : RiemannHypothesis ↔ ∀ a : ℝ, 1 / 2 < a → FimLivre a := by
  constructor
  · intro hRH a ha s hz hs
    rcases le_or_gt 1 s.re with h1 | h1
    · exact riemannZeta_ne_zero_of_one_le_re h1 hz
    · have ht : ¬ Trivial s := fun ht => by have := re_trivial ht; linarith
      have hre := riemann_imp_re hRH ((mem_Z_iff_nao_trivial s).mpr ⟨hz, ht⟩)
      linarith
  · intro h
    refine riemannHypothesis_of_strip fun s hs0 _ hz => ?_
    exact h s.re hs0 s hz le_rfl

/-- **RH ⟺ o início fechado chega ao meio**: `(−∞, b]` livre de zeros não triviais para todo
`b < 1/2`. -/
theorem riemann_iff_inicio : RiemannHypothesis ↔ ∀ b : ℝ, b < 1 / 2 → InicioLivre b := by
  rw [riemann_iff_fim]
  constructor
  · intro h b hb
    by_cases hb0 : b < 1
    · have := (fim_iff_inicio (a := 1 - b) (by linarith)).mp (h (1 - b) (by linarith))
      simpa using this
    · exact absurd hb (by linarith)
  · intro h a ha
    exact (fim_iff_inicio (by linarith)).mpr (h (1 - a) (by linarith))

/-- O limite dos fins fechados `[a, ∞)`, `a ↓ 1/2`, é o meio **aberto** `(1/2, ∞)`. -/
theorem uniao_fins : ⋃ a ∈ Ioi (1 / 2 : ℝ), Ici a = Ioi (1 / 2 : ℝ) := by
  ext x
  simp only [mem_iUnion, mem_Ioi, mem_Ici, exists_prop]
  constructor
  · rintro ⟨a, ha, hx⟩; linarith
  · intro hx; exact ⟨x, hx, le_rfl⟩

/-- O limite dos inícios fechados `(−∞, b]`, `b ↑ 1/2`, é `(−∞, 1/2)`. -/
theorem uniao_inicios : ⋃ b ∈ Iio (1 / 2 : ℝ), Iic b = Iio (1 / 2 : ℝ) := by
  ext x
  simp only [mem_iUnion, mem_Iio, mem_Iic, exists_prop]
  constructor
  · rintro ⟨b, hb, hx⟩; linarith
  · intro hx; exact ⟨x, hx, le_rfl⟩

/-- **RH ⟺ todo zero não trivial é fixo pela torção** (o neutro absorve todos os zeros). -/
theorem riemann_iff_torcao : RiemannHypothesis ↔ ∀ s ∈ Z, torcao s = s := by
  constructor
  · intro hRH s hs
    exact (torcao_fixo_iff s).mpr (riemann_imp_re hRH hs)
  · intro h
    refine riemannHypothesis_of_strip fun s hs0 hs1 hz => ?_
    have hmem : s ∈ Z := ⟨hz, by linarith, hs1⟩
    have := (torcao_fixo_iff s).mp (h s hmem)
    linarith

/-- **RH ⟺ toda compressão preserva as partes reais dos zeros.** -/
theorem riemann_iff_compressao :
    RiemannHypothesis ↔ ∀ s ∈ Z, ∀ l : ℝ, (compressao l s).re = s.re := by
  rw [riemann_iff_torcao]
  constructor
  · intro h s hs l
    rw [re_compressao, (torcao_fixo_iff s).mp (h s hs)]
    ring
  · intro h s hs
    have h0 := h s hs 0
    rw [re_compressao] at h0
    exact (torcao_fixo_iff s).mpr (by linarith)

/-- **RH ⟺ colares arbitrariamente finos**: para todo `ε > 0`, todo zero tem `|Re s − 1/2| < ε`;
o colar `ε = 1/2` é incondicional. -/
theorem colar_meio : ∀ s ∈ Z, |s.re - 1 / 2| < 1 / 2 := by
  rintro s ⟨_, h0, h1⟩
  rw [abs_lt]
  constructor <;> linarith

theorem riemann_iff_colares : RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ s ∈ Z, |s.re - 1 / 2| < ε := by
  constructor
  · intro hRH ε hε s hs
    rw [riemann_imp_re hRH hs, sub_self, abs_zero]
    exact hε
  · intro h
    rw [riemann_iff_torcao]
    intro s hs
    apply (torcao_fixo_iff s).mpr
    have h0 : |s.re - 1 / 2| = 0 := by
      by_contra hne
      have hpos : 0 < |s.re - 1 / 2| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
      exact lt_irrefl _ (h _ hpos s hs)
    have := abs_eq_zero.mp h0
    linarith

end ATK.ZetaSimetria

#print axioms ATK.ZetaSimetria.tensao_tensao
#print axioms ATK.ZetaSimetria.espelho_espelho
#print axioms ATK.ZetaSimetria.torcao_torcao
#print axioms ATK.ZetaSimetria.torcao_eq
#print axioms ATK.ZetaSimetria.tensao_fixo_iff
#print axioms ATK.ZetaSimetria.espelho_fixo_iff
#print axioms ATK.ZetaSimetria.torcao_fixo_iff
#print axioms ATK.ZetaSimetria.re_tensao
#print axioms ATK.ZetaSimetria.re_torcao
#print axioms ATK.ZetaSimetria.re_compressao
#print axioms ATK.ZetaSimetria.compressao_neutro
#print axioms ATK.ZetaSimetria.compressao_comp
#print axioms ATK.ZetaSimetria.compressao_tensao
#print axioms ATK.ZetaSimetria.rigidez_neutro
#print axioms ATK.ZetaSimetria.re_trivial
#print axioms ATK.ZetaSimetria.nao_neg_nat_of_re_pos
#print axioms ATK.ZetaSimetria.zero_trivial_de_re_nao_pos
#print axioms ATK.ZetaSimetria.zero_na_faixa
#print axioms ATK.ZetaSimetria.mem_Z_iff_nao_trivial
#print axioms ATK.ZetaSimetria.tensao_mem_Z
#print axioms ATK.ZetaSimetria.espelho_mem_Z
#print axioms ATK.ZetaSimetria.torcao_mem_Z
#print axioms ATK.ZetaSimetria.H_real
#print axioms ATK.ZetaSimetria.H_real_nonneg
#print axioms ATK.ZetaSimetria.zeta_real_neg
#print axioms ATK.ZetaSimetria.zeta_ne_zero_real
#print axioms ATK.ZetaSimetria.zeta_meio_neg
#print axioms ATK.ZetaSimetria.im_ne_zero_of_mem_Z
#print axioms ATK.ZetaSimetria.quarteto
#print axioms ATK.ZetaSimetria.fimLivre_um
#print axioms ATK.ZetaSimetria.inicioLivre_zero
#print axioms ATK.ZetaSimetria.fimLivre_mono
#print axioms ATK.ZetaSimetria.inicioLivre_mono
#print axioms ATK.ZetaSimetria.fim_iff_inicio
#print axioms ATK.ZetaSimetria.riemann_imp_re
#print axioms ATK.ZetaSimetria.riemann_iff_fim
#print axioms ATK.ZetaSimetria.riemann_iff_inicio
#print axioms ATK.ZetaSimetria.uniao_fins
#print axioms ATK.ZetaSimetria.uniao_inicios
#print axioms ATK.ZetaSimetria.riemann_iff_torcao
#print axioms ATK.ZetaSimetria.riemann_iff_compressao
#print axioms ATK.ZetaSimetria.colar_meio
#print axioms ATK.ZetaSimetria.riemann_iff_colares
