import ATK.FechamentoO1

/-!
# Zeros fora da linha: órbitas, contagem e como se escondem no truncamento

Análise dos zeros não triviais de `ζ` que poderiam estar fora da reta crítica (RH falsa).

**1. Órbitas** (`orbita`): as simetrias `s ↦ 1 − s` (equação funcional) e `s ↦ s̄` (conjugação)
geram o grupo de Klein, de 4 elementos. A órbita de qualquer ponto tem tamanho **1, 2 ou 4**
(`orbita_card`), **nunca 3 nem 5** (`orbita_nao_tres_nem_cinco`). Um zero fora da linha tem órbita
de exatamente **4** (`card_fora`); um zero na linha, de **2** (`card_na_linha`). Toda a órbita de
um zero é feita de zeros (`orbita_sub_Z`).

**2. Contagem**: abaixo de qualquer altura há só **finitos** zeros fora da linha
(`foraAte_finito`). Existem **infinitos** zeros fora da linha **se e só se** existe zero fora da
linha acima de **qualquer** altura (`infinitos_iff`): não há "zero no infinito" em `ℂ`, só zeros
de altura arbitrariamente grande.

**3. Como se escondem no truncamento**: um zero `ρ` com `1/2 < Re ρ < 1` força o piso
`D_N ≥ m(ρ)²` para todo `N` (`ATK.ForaDaLinha.piso_DN`). Este piso garantido é **pequeno** quando
o zero está alto ou perto da linha:
`m(ρ)² ≤ (2 Re ρ − 1)/‖ρ‖²` e `m(ρ)² ≤ 1/(4‖ρ‖²)` (`piso_esconde`). Um zero na altura `10¹²`
garante um piso de no máximo `≈ 10⁻²⁴`: invisível a qualquer truncamento calculável, mas positivo.

Nada aqui decide RH.
-/

open Complex Set Filter Topology
open ATK.ZetaSimetria ATK.ForaDaLinha ATK.FechamentoO1

namespace ATK.ZerosFora

/-! ## 1. Órbitas sob as simetrias de `ζ` -/

/-- A órbita de `s`: `{s, 1 − s, s̄, 1 − s̄}`. -/
noncomputable def orbita (s : ℂ) : Finset ℂ :=
  open Classical in {s, tensao s, espelho s, torcao s}

theorem tensao_ext (s : ℂ) : (tensao s).re = 1 - s.re ∧ (tensao s).im = -s.im := by
  unfold tensao; simp

theorem espelho_ext (s : ℂ) : (espelho s).re = s.re ∧ (espelho s).im = -s.im := by
  unfold espelho; simp

theorem torcao_ext (s : ℂ) : (torcao s).re = 1 - s.re ∧ (torcao s).im = s.im := by
  unfold torcao; simp

/-- Fora da linha e fora do eixo real: os quatro pontos são distintos. -/
theorem card_quatro {s : ℂ} (hre : s.re ≠ 1 / 2) (him : s.im ≠ 0) : (orbita s).card = 4 := by
  classical
  obtain ⟨t1, t2⟩ := tensao_ext s
  obtain ⟨e1, e2⟩ := espelho_ext s
  obtain ⟨o1, o2⟩ := torcao_ext s
  have hre' : s.re ≠ 1 - s.re := fun h => hre (by linarith)
  have him' : s.im ≠ -s.im := fun h => him (by linarith)
  have a1 : s ≠ tensao s := fun h => hre' (by have := congrArg Complex.re h; rwa [t1] at this)
  have a2 : s ≠ espelho s := fun h => him' (by have := congrArg Complex.im h; rwa [e2] at this)
  have a3 : s ≠ torcao s := fun h => hre' (by have := congrArg Complex.re h; rwa [o1] at this)
  have a4 : tensao s ≠ espelho s := fun h => hre' (by
    have := congrArg Complex.re h; rw [t1, e1] at this; exact this.symm)
  have a5 : tensao s ≠ torcao s := fun h => him' (by
    have := congrArg Complex.im h; rw [t2, o2] at this; exact this.symm)
  have a6 : espelho s ≠ torcao s := fun h => hre' (by
    have := congrArg Complex.re h; rwa [e1, o1] at this)
  unfold orbita
  rw [Finset.card_insert_of_notMem (by simp [a1, a2, a3]),
    Finset.card_insert_of_notMem (by simp [a4, a5]), Finset.card_pair a6]

/-- Na linha e fora do eixo real: `1 − s = s̄` e `1 − s̄ = s`, órbita `{s, s̄}`. -/
theorem card_dois_linha {s : ℂ} (hre : s.re = 1 / 2) (him : s.im ≠ 0) : (orbita s).card = 2 := by
  classical
  have h1 : tensao s = espelho s := by
    apply Complex.ext <;> simp [(tensao_ext s).1, (tensao_ext s).2, (espelho_ext s).1,
      (espelho_ext s).2, hre] <;> norm_num
  have h2 : torcao s = s := (torcao_fixo_iff s).mpr hre
  have hne : s ≠ espelho s := fun h => him (by
    have := congrArg Complex.im h; rw [(espelho_ext s).2] at this; linarith)
  unfold orbita
  rw [h1, h2]
  simp
  exact Finset.card_pair (Ne.symm hne)

/-- No eixo real e fora da linha: `s̄ = s`, órbita `{s, 1 − s}`. -/
theorem card_dois_eixo {s : ℂ} (hre : s.re ≠ 1 / 2) (him : s.im = 0) : (orbita s).card = 2 := by
  classical
  have h1 : espelho s = s := (espelho_fixo_iff s).mpr him
  have h2 : torcao s = tensao s := by
    apply Complex.ext <;> simp [(torcao_ext s).1, (torcao_ext s).2, (tensao_ext s).1,
      (tensao_ext s).2, him]
  have hne : s ≠ tensao s := fun h => hre (by
    have := congrArg Complex.re h; rw [(tensao_ext s).1] at this; linarith)
  unfold orbita
  rw [h1, h2]
  simp [Finset.card_pair hne]

/-- O ponto fixo `s = 1/2`: órbita `{1/2}`. -/
theorem card_um {s : ℂ} (hre : s.re = 1 / 2) (him : s.im = 0) : (orbita s).card = 1 := by
  classical
  have hs : s = 1 / 2 := by apply Complex.ext <;> simp [hre, him]
  have h1 : tensao s = s := (tensao_fixo_iff s).mpr hs
  have h2 : espelho s = s := (espelho_fixo_iff s).mpr him
  have h3 : torcao s = s := (torcao_fixo_iff s).mpr hre
  unfold orbita
  rw [h1, h2, h3]
  simp

/-- **A órbita tem 1, 2 ou 4 elementos.** -/
theorem orbita_card (s : ℂ) : (orbita s).card = 1 ∨ (orbita s).card = 2 ∨ (orbita s).card = 4 := by
  by_cases hre : s.re = 1 / 2 <;> by_cases him : s.im = 0
  · exact Or.inl (card_um hre him)
  · exact Or.inr (Or.inl (card_dois_linha hre him))
  · exact Or.inr (Or.inl (card_dois_eixo hre him))
  · exact Or.inr (Or.inr (card_quatro hre him))

/-- **Nunca 3, nunca 5.** -/
theorem orbita_nao_tres_nem_cinco (s : ℂ) : (orbita s).card ≠ 3 ∧ (orbita s).card ≠ 5 := by
  rcases orbita_card s with h | h | h <;> rw [h] <;> decide

/-- A órbita de um zero não trivial é feita de zeros não triviais. -/
theorem orbita_sub_Z {s : ℂ} (hs : s ∈ Z) : ∀ t ∈ orbita s, t ∈ Z := by
  intro t ht
  classical
  simp only [orbita, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl
  · exact hs
  · exact tensao_mem_Z hs
  · exact espelho_mem_Z hs
  · exact torcao_mem_Z hs

/-- Zero fora da linha: **quarteto**. -/
theorem card_fora {s : ℂ} (hs : s ∈ Z) (hre : s.re ≠ 1 / 2) : (orbita s).card = 4 :=
  card_quatro hre (im_ne_zero_of_mem_Z hs)

/-- Zero na linha: **par** `{ρ, ρ̄}`. -/
theorem card_na_linha {s : ℂ} (hs : s ∈ Z) (hre : s.re = 1 / 2) : (orbita s).card = 2 :=
  card_dois_linha hre (im_ne_zero_of_mem_Z hs)

/-! ## 2. Contagem dos zeros fora da linha -/

/-- Os zeros não triviais fora da reta crítica. -/
def Fora : Set ℂ := {ρ ∈ Z | ρ.re ≠ 1 / 2}

/-- Os de altura `|Im ρ| ≤ T`. -/
def foraAte (T : ℝ) : Set ℂ := {ρ ∈ Fora | |ρ.im| ≤ T}

/-- **Abaixo de cada altura, só finitos zeros fora da linha.** -/
theorem foraAte_finito (T : ℝ) : (foraAte T).Finite :=
  (zerosSim_finito T).subset fun _ ⟨⟨hZ, _⟩, hT⟩ => ⟨hZ, hT⟩

/-- RH ⟺ não há zero fora da linha. -/
theorem rh_iff_fora_vazio : RiemannHypothesis ↔ Fora = ∅ := by
  rw [riemann_iff_vazio, Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h ρ hρ
    exact h.false ⟨ρ, hρ.1, hρ.2⟩
  · intro h
    exact ⟨fun ρ => h ρ.1 ⟨ρ.2.1, ρ.2.2⟩⟩

/-- **Infinitos zeros fora da linha ⟺ há zero fora da linha acima de qualquer altura.** -/
theorem infinitos_iff : Fora.Infinite ↔ ∀ T : ℝ, ∃ ρ ∈ Fora, T < |ρ.im| := by
  constructor
  · intro hinf T
    by_contra h
    push_neg at h
    exact hinf ((foraAte_finito T).subset fun ρ hρ => ⟨hρ, h ρ hρ⟩)
  · intro h hfin
    obtain ⟨M, hM⟩ := (hfin.image fun ρ => |ρ.im|).bddAbove
    obtain ⟨ρ, hρ, hlt⟩ := h M
    exact absurd (hM ⟨ρ, hρ, rfl⟩) (not_le.mpr hlt)

/-- Finitos zeros fora da linha ⟺ todos abaixo de alguma altura. -/
theorem finitos_iff : Fora.Finite ↔ ∃ T : ℝ, Fora ⊆ {ρ | |ρ.im| ≤ T} := by
  constructor
  · intro hfin
    obtain ⟨M, hM⟩ := (hfin.image fun ρ => |ρ.im|).bddAbove
    exact ⟨M, fun ρ hρ => hM ⟨ρ, hρ, rfl⟩⟩
  · rintro ⟨T, hT⟩
    exact (foraAte_finito T).subset fun ρ hρ => ⟨hρ, hT hρ⟩

/-! ## 3. Como um zero se esconde no truncamento -/

/-- O piso garantido é **pequeno** para zeros altos ou perto da linha:
`m(ρ)² ≤ (2 Re ρ − 1)/‖ρ‖²` e `m(ρ)² ≤ 1/(4‖ρ‖²)`. -/
theorem piso_esconde {ρ : ℂ} (h0 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    m ρ ^ 2 ≤ (2 * ρ.re - 1) / ‖ρ‖ ^ 2 ∧ m ρ ^ 2 ≤ 1 / (4 * ‖ρ‖ ^ 2) := by
  have hρ : ρ ≠ 0 := by intro h; rw [h, zero_re] at h0; linarith
  have hn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  set a := Real.sqrt (2 * ρ.re - 1) with ha
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < 1 - ρ.re := by linarith
  have hm0 := m_pos h0 h1
  have hm_a : m ρ ≤ a / ‖ρ‖ := by
    unfold m
    rw [← ha, div_le_div_iff₀ (by positivity) hn, one_mul]
    have : 1 ≤ a * (1 / a + 1 / (1 - ρ.re)) := by
      rw [mul_add, mul_one_div_cancel ha0.ne']
      have : 0 ≤ a * (1 / (1 - ρ.re)) := by positivity
      linarith
    nlinarith
  have hm_b : m ρ ≤ (1 - ρ.re) / ‖ρ‖ := by
    unfold m
    rw [← ha, div_le_div_iff₀ (by positivity) hn, one_mul]
    have : 1 ≤ (1 - ρ.re) * (1 / a + 1 / (1 - ρ.re)) := by
      rw [mul_add, mul_one_div_cancel hb0.ne']
      have : 0 ≤ (1 - ρ.re) * (1 / a) := by positivity
      linarith
    nlinarith
  constructor
  · have h2 : a ^ 2 = 2 * ρ.re - 1 := Real.sq_sqrt (by linarith)
    calc m ρ ^ 2 ≤ (a / ‖ρ‖) ^ 2 := pow_le_pow_left₀ hm0.le hm_a 2
      _ = (2 * ρ.re - 1) / ‖ρ‖ ^ 2 := by rw [div_pow, h2]
  · have hb : (1 - ρ.re) / ‖ρ‖ ≤ 1 / (2 * ‖ρ‖) := by
      rw [div_le_div_iff₀ hn (by positivity)]
      nlinarith
    calc m ρ ^ 2 ≤ (1 / (2 * ‖ρ‖)) ^ 2 := pow_le_pow_left₀ hm0.le (hm_b.trans hb) 2
      _ = 1 / (4 * ‖ρ‖ ^ 2) := by ring

/-- O piso garantido de um zero tende a **zero** quando a altura cresce: para todo `ε > 0` há uma
altura acima da qual o piso garantido é `< ε`. -/
theorem piso_some {ε : ℝ} (hε : 0 < ε) : ∃ R : ℝ, ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ.re < 1 →
    R < ‖ρ‖ → m ρ ^ 2 < ε := by
  refine ⟨1 / Real.sqrt (4 * ε), fun ρ h0 h1 hR => ?_⟩
  have hs : 0 < Real.sqrt (4 * ε) := Real.sqrt_pos.mpr (by linarith)
  have hn : 0 < ‖ρ‖ := lt_trans (by positivity) hR
  have hb := (piso_esconde h0 h1).2
  have hR' : 1 < Real.sqrt (4 * ε) * ‖ρ‖ := by
    rw [div_lt_iff₀ hs] at hR; linarith
  have hsq : 1 < 4 * ε * ‖ρ‖ ^ 2 := by
    have h4 : Real.sqrt (4 * ε) ^ 2 = 4 * ε := Real.sq_sqrt (by linarith)
    nlinarith [sq_nonneg (Real.sqrt (4 * ε) * ‖ρ‖ - 1)]
  calc m ρ ^ 2 ≤ 1 / (4 * ‖ρ‖ ^ 2) := hb
    _ < ε := by rw [div_lt_iff₀ (by positivity)]; linarith

end ATK.ZerosFora

#print axioms ATK.ZerosFora.tensao_ext
#print axioms ATK.ZerosFora.espelho_ext
#print axioms ATK.ZerosFora.torcao_ext
#print axioms ATK.ZerosFora.card_quatro
#print axioms ATK.ZerosFora.card_dois_linha
#print axioms ATK.ZerosFora.card_dois_eixo
#print axioms ATK.ZerosFora.card_um
#print axioms ATK.ZerosFora.orbita_card
#print axioms ATK.ZerosFora.orbita_nao_tres_nem_cinco
#print axioms ATK.ZerosFora.orbita_sub_Z
#print axioms ATK.ZerosFora.card_fora
#print axioms ATK.ZerosFora.card_na_linha
#print axioms ATK.ZerosFora.foraAte_finito
#print axioms ATK.ZerosFora.rh_iff_fora_vazio
#print axioms ATK.ZerosFora.infinitos_iff
#print axioms ATK.ZerosFora.finitos_iff
#print axioms ATK.ZerosFora.piso_esconde
#print axioms ATK.ZerosFora.piso_some
