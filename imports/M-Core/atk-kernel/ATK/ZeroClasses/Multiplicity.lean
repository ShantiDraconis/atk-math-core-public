import ATK.ZeroClasses.Basic

/-!
# ATK-ZERO-CLASSES — multiplicidade, isolamento e acumulação

Classes 10–14 do prompt mestre, separando o que é **lógica pura** do que exige **holomorfia**:

* lógica pura (qualquer `f`): todo zero é **isolado** ou **de acumulação**, e não ambos
  (`isolado_ou_acumulacao`, `particao_isolamento`);
* continuidade: um ponto de acumulação de zeros é zero (`acumulacao_zero`);
* analiticidade em `z`: **multiplicidade finita ⟺ isolado** (`multFinita_iff_isolado`); zero isolado ou
  `f ≡ 0` perto de `z` (`isolado_ou_nulo`); **simples ⟺ ordem 1** (`simples_iff`); todo zero de
  multiplicidade finita é **simples ou múltiplo**, não ambos (`simples_ou_multiplo`);
* analiticidade num aberto conexo `U` com `f ≢ 0`: **nenhum ponto de `U` acumula zeros**, e todo zero
  em `U` tem multiplicidade finita (`sem_acumulacao`, `multFinita_de_conexo`).
-/

open Complex Set Filter Topology

namespace ATK.ZeroClasses

/-- Zero simples: `f z = 0` e `f′(z) ≠ 0`. -/
def Simples (f : ℂ → ℂ) (z : ℂ) : Prop := IsZero f z ∧ deriv f z ≠ 0

/-- Zero de multiplicidade finita. -/
def MultFinita (f : ℂ → ℂ) (z : ℂ) : Prop :=
  IsZero f z ∧ AnalyticAt ℂ f z ∧ analyticOrderAt f z ≠ ⊤

/-- Zero múltiplo: multiplicidade finita `≥ 2`. -/
def Multiplo (f : ℂ → ℂ) (z : ℂ) : Prop := MultFinita f z ∧ 2 ≤ analyticOrderAt f z

/-- Zero isolado. -/
def Isolado (f : ℂ → ℂ) (z : ℂ) : Prop := IsZero f z ∧ ∀ᶠ w in 𝓝[≠] z, f w ≠ 0

/-- `z` acumula zeros de `f` (não precisa ser zero). -/
def Acumulacao (f : ℂ → ℂ) (z : ℂ) : Prop := ∃ᶠ w in 𝓝[≠] z, f w = 0

variable {f : ℂ → ℂ} {z : ℂ}

/-! ## Lógica pura -/

theorem nao_acumulacao_iff : ¬ Acumulacao f z ↔ ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := not_frequently

/-- **Todo zero é isolado ou de acumulação.** -/
theorem isolado_ou_acumulacao (hz : IsZero f z) : Isolado f z ∨ Acumulacao f z := by
  by_cases h : Acumulacao f z
  · exact Or.inr h
  · exact Or.inl ⟨hz, nao_acumulacao_iff.mp h⟩

theorem isolado_nao_acumulacao (h : Isolado f z) : ¬ Acumulacao f z := nao_acumulacao_iff.mpr h.2

/-- **`Z(f) = Z_isol ⊔ Z_acum`.** -/
theorem particao_isolamento :
    Z f = {z | Isolado f z} ∪ {z | IsZero f z ∧ Acumulacao f z} ∧
      Disjoint {z | Isolado f z} {z | IsZero f z ∧ Acumulacao f z} := by
  refine ⟨?_, Set.disjoint_left.mpr fun z h1 h2 => isolado_nao_acumulacao h1 h2.2⟩
  ext w
  simp only [Z, mem_union, mem_ofPred_eq]
  constructor
  · intro hw
    rcases isolado_ou_acumulacao (show IsZero f w from hw) with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hw, h⟩
  · rintro (h | h)
    · exact h.1
    · exact h.1

/-! ## Continuidade -/

/-- Um ponto de acumulação de zeros de uma `f` contínua é zero. -/
theorem acumulacao_zero (hf : ContinuousAt f z) (h : Acumulacao f z) : IsZero f z := by
  by_contra hne
  have hev : ∀ᶠ w in 𝓝 z, f w ≠ 0 := hf.eventually_ne hne
  exact h (hev.filter_mono nhdsWithin_le_nhds)

/-! ## Analiticidade num ponto -/

/-- Zero de função analítica: isolado, ou `f ≡ 0` perto de `z`. -/
theorem isolado_ou_nulo (ha : AnalyticAt ℂ f z) (hz : IsZero f z) :
    Isolado f z ∨ ∀ᶠ w in 𝓝 z, f w = 0 := by
  rcases ha.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact Or.inr h
  · exact Or.inl ⟨hz, h⟩

/-- **Multiplicidade finita ⟺ isolado.** -/
theorem multFinita_iff_isolado (ha : AnalyticAt ℂ f z) (hz : IsZero f z) :
    MultFinita f z ↔ Isolado f z := by
  constructor
  · rintro ⟨_, _, htop⟩
    rcases isolado_ou_nulo ha hz with h | h
    · exact h
    · exact absurd (analyticOrderAt_eq_top.mpr h) htop
  · rintro ⟨_, hne⟩
    refine ⟨hz, ha, fun htop => ?_⟩
    have h0 : ∀ᶠ w in 𝓝[≠] z, f w = 0 := (analyticOrderAt_eq_top.mp htop).filter_mono nhdsWithin_le_nhds
    obtain ⟨w, hw1, hw2⟩ := (h0.and hne).exists
    exact hw2 hw1

/-- A ordem de um zero de multiplicidade finita é um natural `≥ 1`. -/
theorem ordem_nat (h : MultFinita f z) : ∃ n : ℕ, 1 ≤ n ∧ analyticOrderAt f z = n := by
  obtain ⟨hz, ha, htop⟩ := h
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  have h0 : analyticOrderAt f z ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨ha, hz⟩
  refine ⟨n, ?_, hn.symm⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; exact absurd hn.symm (by simpa using h0)
  · exact h

/-- **Simples ⟺ multiplicidade finita de ordem 1** (para `f` analítica em `z`). -/
theorem simples_iff (ha : AnalyticAt ℂ f z) :
    Simples f z ↔ MultFinita f z ∧ analyticOrderAt f z = 1 := by
  constructor
  · rintro ⟨hz, hd⟩
    have h1 := ha.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hz hd
    exact ⟨⟨hz, ha, by rw [h1]; exact ENat.one_ne_top⟩, h1⟩
  · rintro ⟨⟨hz, _, _⟩, h1⟩
    refine ⟨hz, fun hd => ?_⟩
    have h2 : ((2 : ℕ) : ℕ∞) ≤ analyticOrderAt f z := by
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha]
      intro i hi
      interval_cases i
      · simpa using (show f z = 0 from hz)
      · simpa [iteratedDeriv_one] using hd
    rw [h1] at h2
    exact absurd h2 (by decide)

/-- **Simples ou múltiplo**, e não ambos. -/
theorem simples_ou_multiplo (h : MultFinita f z) :
    (analyticOrderAt f z = 1 ∨ Multiplo f z) ∧ ¬ (analyticOrderAt f z = 1 ∧ Multiplo f z) := by
  obtain ⟨n, hn1, hn⟩ := ordem_nat h
  refine ⟨?_, ?_⟩
  · rcases Nat.lt_or_ge n 2 with h2 | h2
    · left; rw [hn]; have : n = 1 := by omega
      subst this; rfl
    · right; refine ⟨h, ?_⟩; rw [hn]; exact_mod_cast h2
  · rintro ⟨h1, _, h2⟩
    rw [h1] at h2
    exact absurd h2 (by decide)

theorem simples_nao_multiplo (ha : AnalyticAt ℂ f z) (h : Simples f z) : ¬ Multiplo f z := by
  obtain ⟨hm, h1⟩ := (simples_iff ha).mp h
  exact fun hmul => (simples_ou_multiplo hm).2 ⟨h1, hmul⟩

/-! ## Analiticidade num aberto conexo -/

/-- **Sem acumulação**: `f` analítica num conexo `U` e não identicamente nula em `U` não tem ponto de
acumulação de zeros em `U`. -/
theorem sem_acumulacao {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hne : f z₀ ≠ 0) {z : ℂ} (hz : z ∈ U) : ¬ Acumulacao f z := by
  intro h
  exact hne (hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hz h hz₀)

/-- Todo zero em `U` é isolado e de multiplicidade finita. -/
theorem multFinita_de_conexo {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U) (hne : f z₀ ≠ 0) {z : ℂ} (hz : z ∈ U) (h0 : IsZero f z) :
    Isolado f z ∧ MultFinita f z := by
  have hiso : Isolado f z := ⟨h0, nao_acumulacao_iff.mp (sem_acumulacao hf hU hz₀ hne hz)⟩
  exact ⟨hiso, (multFinita_iff_isolado (hf z hz) h0).mpr hiso⟩

end ATK.ZeroClasses

#print axioms ATK.ZeroClasses.nao_acumulacao_iff
#print axioms ATK.ZeroClasses.isolado_ou_acumulacao
#print axioms ATK.ZeroClasses.isolado_nao_acumulacao
#print axioms ATK.ZeroClasses.particao_isolamento
#print axioms ATK.ZeroClasses.acumulacao_zero
#print axioms ATK.ZeroClasses.isolado_ou_nulo
#print axioms ATK.ZeroClasses.multFinita_iff_isolado
#print axioms ATK.ZeroClasses.ordem_nat
#print axioms ATK.ZeroClasses.simples_iff
#print axioms ATK.ZeroClasses.simples_ou_multiplo
#print axioms ATK.ZeroClasses.simples_nao_multiplo
#print axioms ATK.ZeroClasses.sem_acumulacao
#print axioms ATK.ZeroClasses.multFinita_de_conexo
