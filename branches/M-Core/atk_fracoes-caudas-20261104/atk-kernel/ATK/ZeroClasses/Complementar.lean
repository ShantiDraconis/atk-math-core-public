import ATK.ZeroClasses.MundoFora

/-!
# ATK-ZERO-CLASSES — os dois casos: onde se excluem e onde se complementam

A proposta: "os dois casos valem, porque se complementam; a rigidez está na forma da pergunta". O kernel
separa com precisão onde isso é contraditório e onde é exato.

* **Para a mesma `ζ`, exatamente um** (`exatamente_um`): `RH ∨ H_fora` e `¬(RH ∧ H_fora)`. Aceitar os dois
  provaria qualquer coisa (`explosao`), inclusive `1 = 0`, e todo certificado perderia o sentido. Isto é o
  princípio de não contradição, não uma escolha de Riemann.
* **Numa família, os dois coexistem** (`dois_casos_na_familia`, `ambos_realizados`): no modelo
  `F_{d,t}(z) = (w² + t²)((w − d)² + t²)((w + d)² + t²)`, `w = z − 1/2` — com a **mesma equação funcional**
  `F(1 − z) = F(z)` e a mesma conjugação de `ζ` — todos os zeros estão na reta **se e só se `d = 0`**. O membro
  `d = 0` é "RH"; todo `d ≠ 0` tem zeros centrais **e** um quarteto externo cujo ponto médio é o zero
  central (`FM_ponto_medio`, a construção do texto encaminhado, agora compilada).
* **Um número em vez de sim/não** (`Theta`): `Θ = sup Re ρ ∈ [1/2, 1]` (`Theta_mem`); **RH ⟺ Θ = 1/2**,
  **H_fora ⟺ Θ > 1/2** (`rh_iff_Theta`, `fora_iff_Theta`). A pergunta de Riemann é o caso extremo de um
  parâmetro contínuo; se `Θ < 1` também é `OPEN_MATH`.
* **A rigidez dos triviais** (`triv_segunda_diferenca`): `Δ²zₙ = 0`; e eles são **compensados** em `ξ`
  (`triv_compensados`: `ζ(−2(n+1)) = 0`, `ξ(−2(n+1)) ≠ 0`, os polos de `Γ` cancelam os zeros).
* **A lei `sin(πs/2)`** (`triv_iff_sin`): `sin(πs/2) = 0 ∧ Re s < 0 ⟺ s` é trivial.
* **Necessidade** (`equilibrio_sem_fora`): a lei de equilíbrio `Σ(β − 1/2) = 0` vale **também sem** zeros
  externos — ela não os torna necessários. **Teste decisivo** (`teste_decisivo`, `necessidade_iff`): uma
  propriedade provada que seria falsa sem externos prova `H_fora`; e existe tal teste **⟺ ¬RH**. Uma lei de acoplamento em que **cada** zero é necessário é a
  fórmula explícita de Riemann–von Mangoldt (triviais, críticos e externos contribuem termos distintos para
  `ψ(x)`): BUILD_PENDING.
-/

open Complex ComplexConjugate Set

namespace ATK.ZeroClasses.Complementar

open ATK.ZeroClasses ATK.ZeroClasses.Zeta ATK.ZeroClasses.Hipotetico

/-! ## 1. Para a mesma `ζ`: exatamente um dos dois -/

theorem exatamente_um : (RiemannHypothesis ∨ HFora) ∧ ¬ (RiemannHypothesis ∧ HFora) := by
  refine ⟨?_, fun ⟨h1, h2⟩ => hFora_iff.mp h2 h1⟩
  by_cases h : RiemannHypothesis
  · exact Or.inl h
  · exact Or.inr (hFora_iff.mpr h)

/-- Aceitar os dois casos para a mesma `ζ` prova qualquer proposição. -/
theorem explosao (h : RiemannHypothesis ∧ HFora) (P : Prop) : P :=
  absurd h.1 (hFora_iff.mp h.2)

/-! ## 2. `Θ = sup Re ρ` -/

/-- `Θ = sup{Re ρ : ρ zero não trivial}`. -/
noncomputable def Theta : ℝ := sSup (Complex.re '' ATK.ZetaSimetria.Z)

theorem re_nonempty : (Complex.re '' ATK.ZetaSimetria.Z).Nonempty :=
  let ⟨s, hs⟩ := existe_nao_trivial; ⟨s.re, s, hs, rfl⟩

theorem re_bdd : BddAbove (Complex.re '' ATK.ZetaSimetria.Z) :=
  ⟨1, by rw [mem_upperBounds]; rintro _ ⟨s, hs, rfl⟩; exact hs.2.2.le⟩

theorem re_le_Theta {s : ℂ} (hs : s ∈ ATK.ZetaSimetria.Z) : s.re ≤ Theta :=
  le_csSup re_bdd ⟨s, hs, rfl⟩

theorem Theta_le_one : Theta ≤ 1 :=
  csSup_le re_nonempty (by rintro _ ⟨s, hs, rfl⟩; exact hs.2.2.le)

theorem meio_le_Theta : 1 / 2 ≤ Theta := by
  obtain ⟨s, hs, hre⟩ := existe_critico
  rw [← hre]
  exact re_le_Theta hs

theorem Theta_mem : Theta ∈ Icc (1 / 2 : ℝ) 1 := ⟨meio_le_Theta, Theta_le_one⟩

/-- **RH ⟺ Θ = 1/2.** -/
theorem rh_iff_Theta : RiemannHypothesis ↔ Theta = 1 / 2 := by
  rw [rh_iff_classes]
  constructor
  · intro h
    refine le_antisymm (csSup_le re_nonempty ?_) meio_le_Theta
    rintro _ ⟨s, hs, rfl⟩
    exact (h s hs).2.le
  · intro hT s hs
    refine ⟨hs.1, le_antisymm (hT ▸ re_le_Theta hs) ?_⟩
    have := re_le_Theta (ATK.ZetaSimetria.tensao_mem_Z hs)
    rw [ATK.ZetaSimetria.re_tensao, hT] at this
    linarith

/-- **H_fora ⟺ Θ > 1/2.** -/
theorem fora_iff_Theta : HFora ↔ 1 / 2 < Theta := by
  rw [hFora_iff, rh_iff_Theta]
  constructor
  · intro h; exact lt_of_le_of_ne meio_le_Theta (Ne.symm h)
  · intro h he; rw [he] at h; exact lt_irrefl _ h

/-! ## 3. O modelo: uma família em que os dois casos coexistem -/

/-- `F_{d,t}(z) = (w² + t²)((w − d)² + t²)((w + d)² + t²)`, `w = z − 1/2`. -/
noncomputable def FM (d t : ℝ) (z : ℂ) : ℂ :=
  ((z - 1 / 2) ^ 2 + (t : ℂ) ^ 2) * ((z - 1 / 2 - d) ^ 2 + (t : ℂ) ^ 2) *
    ((z - 1 / 2 + d) ^ 2 + (t : ℂ) ^ 2)

/-- **A mesma equação funcional de `ξ`**: `F(1 − z) = F(z)`. -/
theorem FM_eq_func (d t : ℝ) (z : ℂ) : FM d t (1 - z) = FM d t z := by
  unfold FM; ring

/-- **A mesma conjugação de `ζ`**. -/
theorem FM_conj (d t : ℝ) : ConjEquiv (FM d t) := by
  intro z
  have h2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  simp only [FM, map_mul, map_add, map_sub, map_pow, Complex.conj_ofReal, h2]

theorem FM_refl (d t : ℝ) : ReflZeros (FM d t) (1 / 2) := by
  refine refl_de_equacao (u := fun _ => 1) fun z => ?_
  have : 2 * (((1 / 2 : ℝ)) : ℂ) - z = 1 - z := by push_cast; ring
  rw [this, FM_eq_func, one_mul]

theorem sq_add_sq_eq_zero (w : ℂ) (t : ℝ) :
    w ^ 2 + (t : ℂ) ^ 2 = 0 ↔ w = (t : ℂ) * I ∨ w = -((t : ℂ) * I) := by
  have e : w ^ 2 + (t : ℂ) ^ 2 = w ^ 2 - ((t : ℂ) * I) ^ 2 := by
    rw [mul_pow, I_sq]; ring
  rw [e, sub_eq_zero, sq_eq_sq_iff_eq_or_eq_neg]

/-- **Os zeros de `F_{d,t}`**: `1/2 ± it`, `1/2 + d ± it`, `1/2 − d ± it`. -/
theorem FM_zero_iff (d t : ℝ) (z : ℂ) :
    FM d t z = 0 ↔
      (z = 1 / 2 + (t : ℂ) * I ∨ z = 1 / 2 - (t : ℂ) * I) ∨
        (z = 1 / 2 + d + (t : ℂ) * I ∨ z = 1 / 2 + d - (t : ℂ) * I) ∨
        (z = 1 / 2 - d + (t : ℂ) * I ∨ z = 1 / 2 - d - (t : ℂ) * I) := by
  unfold FM
  rw [mul_eq_zero, mul_eq_zero, sq_add_sq_eq_zero, sq_add_sq_eq_zero, sq_add_sq_eq_zero]
  constructor
  · rintro (((h | h) | (h | h)) | (h | h))
    · exact Or.inl (Or.inl (by linear_combination h))
    · exact Or.inl (Or.inr (by linear_combination h))
    · exact Or.inr (Or.inl (Or.inl (by linear_combination h)))
    · exact Or.inr (Or.inl (Or.inr (by linear_combination h)))
    · exact Or.inr (Or.inr (Or.inl (by linear_combination h)))
    · exact Or.inr (Or.inr (Or.inr (by linear_combination h)))
  · rintro ((h | h) | (h | h) | (h | h)) <;> rw [h]
    · exact Or.inl (Or.inl (Or.inl (by ring)))
    · exact Or.inl (Or.inl (Or.inr (by ring)))
    · exact Or.inl (Or.inr (Or.inl (by ring)))
    · exact Or.inl (Or.inr (Or.inr (by ring)))
    · exact Or.inr (Or.inl (by ring))
    · exact Or.inr (Or.inr (by ring))

theorem FM_zero_re {d t : ℝ} {z : ℂ} (h : FM d t z = 0) :
    z.re = 1 / 2 ∨ z.re = 1 / 2 + d ∨ z.re = 1 / 2 - d := by
  rcases (FM_zero_iff d t z).mp h with (rfl | rfl) | (rfl | rfl) | (rfl | rfl) <;> simp

/-- Zeros **centrais** (na reta). -/
theorem FM_centrais (d t : ℝ) :
    FM d t (1 / 2 + (t : ℂ) * I) = 0 ∧ FM d t (1 / 2 - (t : ℂ) * I) = 0 ∧
      (1 / 2 + (t : ℂ) * I).re = 1 / 2 := by
  refine ⟨(FM_zero_iff d t _).mpr (Or.inl (Or.inl rfl)), (FM_zero_iff d t _).mpr (Or.inl (Or.inr rfl)),
    by simp⟩

/-- Zeros **externos**: para `d ≠ 0`, `t ≠ 0`, um quarteto fora da reta, todo de zeros. -/
theorem FM_externos {d t : ℝ} (hd : d ≠ 0) (ht : t ≠ 0) :
    FM d t (1 / 2 + d + (t : ℂ) * I) = 0 ∧ (1 / 2 + d + (t : ℂ) * I).re ≠ 1 / 2 ∧
      (orbita (1 / 2) (1 / 2 + d + (t : ℂ) * I)).card = 4 ∧
      ∀ w ∈ orbita (1 / 2) (1 / 2 + d + (t : ℂ) * I), FM d t w = 0 := by
  have hz : FM d t (1 / 2 + d + (t : ℂ) * I) = 0 := (FM_zero_iff d t _).mpr (Or.inr (Or.inl (Or.inl rfl)))
  have hre : (1 / 2 + d + (t : ℂ) * I).re ≠ 1 / 2 := by simpa using hd
  exact ⟨hz, hre, card_quatro hre (by simpa using ht), orbita_sub (FM_conj d t) (FM_refl d t) hz⟩

/-- **Ponto médio**: o zero central é o ponto médio de dois externos, `ρ_C = (ρ₁ + ρ₃)/2`. -/
theorem FM_ponto_medio (d t : ℝ) :
    ((1 / 2 - d + (t : ℂ) * I) + (1 / 2 + d + (t : ℂ) * I)) / 2 = 1 / 2 + (t : ℂ) * I := by ring

/-- **Os dois casos na família**: todos os zeros de `F_{d,t}` estão na reta ⟺ `d = 0`. -/
theorem dois_casos_na_familia {t : ℝ} (d : ℝ) :
    (∀ z, FM d t z = 0 → z.re = 1 / 2) ↔ d = 0 := by
  constructor
  · intro h
    by_contra hd
    have hz : FM d t (1 / 2 + d + (t : ℂ) * I) = 0 :=
      (FM_zero_iff d t _).mpr (Or.inr (Or.inl (Or.inl rfl)))
    have := h _ hz
    simp at this
    exact hd this
  · rintro rfl z hz
    rcases FM_zero_re hz with h | h | h <;> simpa using h

/-- **Ambos realizados** — em membros diferentes da família, nunca no mesmo. -/
theorem ambos_realizados :
    (∃ d : ℝ, ∀ z, FM d 1 z = 0 → z.re = 1 / 2) ∧
      (∃ d : ℝ, (∃ z, FM d 1 z = 0 ∧ z.re = 1 / 2) ∧ ∃ z, FM d 1 z = 0 ∧ z.re ≠ 1 / 2) := by
  have he := FM_externos (d := 1 / 4) (t := 1) (by norm_num) one_ne_zero
  refine ⟨⟨0, (dois_casos_na_familia 0).mpr rfl⟩, ⟨1 / 4,
    ⟨1 / 2 + ((1 : ℝ) : ℂ) * I, (FM_centrais (1 / 4) 1).1, (FM_centrais (1 / 4) 1).2.2⟩,
    ⟨1 / 2 + (((1 / 4 : ℝ)) : ℂ) + ((1 : ℝ) : ℂ) * I, he.1, he.2.1⟩⟩⟩

/-! ## 4. Os triviais: rigidez e compensação -/

/-- `zₙ = −2(n+1)`. -/
def ztriv (n : ℕ) : ℂ := -2 * ((n : ℂ) + 1)

theorem triv_passo (n : ℕ) : ztriv (n + 1) - ztriv n = -2 := by
  unfold ztriv; push_cast; ring

/-- **`Δ²zₙ = 0`.** -/
theorem triv_segunda_diferenca (n : ℕ) : ztriv (n + 2) - 2 * ztriv (n + 1) + ztriv n = 0 := by
  unfold ztriv; push_cast; ring

/-- **Compensação**: os triviais são zeros de `ζ` mas não de `ξ` (os polos de `Γ` os cancelam). -/
theorem triv_compensados (n : ℕ) :
    riemannZeta (ztriv n) = 0 ∧ ATK.BaseRiemannXi.riemannXi (ztriv n) ≠ 0 := by
  refine ⟨riemannZeta_neg_two_mul_nat_add_one n, ATK.BaseRiemannXi.riemannXi_ne_zero_of_re_le_zero ?_⟩
  unfold ztriv
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp
  linarith

/-! ## 5. Necessidade -/

/-- **A lei de equilíbrio não torna os externos necessários**: ela vale para qualquer família só de zeros
centrais. -/
theorem equilibrio_sem_fora (S : Finset ℂ) (h : ∀ ρ ∈ S, ρ.re = 1 / 2) :
    ∑ ρ ∈ S, (ρ.re - 1 / 2) = 0 :=
  Finset.sum_eq_zero fun ρ hρ => by rw [h ρ hρ, sub_self]

/-! ## 6. A lei `sin(πs/2)` dos triviais -/

theorem sin_meio_zero_iff (s : ℂ) : Complex.sin ((Real.pi : ℂ) * s / 2) = 0 ↔ ∃ k : ℤ, s = 2 * k := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Complex.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, mul_left_cancel₀ hπ ?_⟩
    linear_combination 2 * hk
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

/-- **`sin(πs/2) = 0 ∧ Re s < 0 ⟺ s` é trivial**: a classe trivial é imposta pelo fator `sin` da equação
funcional. -/
theorem triv_iff_sin (s : ℂ) :
    (Complex.sin ((Real.pi : ℂ) * s / 2) = 0 ∧ s.re < 0) ↔ ATK.ZetaSimetria.Trivial s := by
  rw [sin_meio_zero_iff]
  constructor
  · rintro ⟨⟨k, rfl⟩, hre⟩
    have hk : (k : ℝ) < 0 := by simp at hre; linarith
    have hk' : k ≤ -1 := by
      have : k < 0 := by exact_mod_cast hk
      omega
    obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat (show k ≤ 0 by omega)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨m, ?_⟩
    rw [hn]; push_cast; ring
  · rintro ⟨n, rfl⟩
    refine ⟨⟨-((n : ℤ) + 1), by push_cast; ring⟩, ATK.ZetaSimetria.re_trivial ⟨n, rfl⟩⟩

/-! ## 7. O teste decisivo da necessidade -/

open ATK.ZeroClasses.MundoFora (ForaSet)

/-- **O teste decisivo**: uma propriedade `P` provada, que seria falsa sem zeros externos, prova `H_fora`. -/
theorem teste_decisivo {P : Prop} (hP : P) (hne : ForaSet = ∅ → ¬ P) : HFora := by
  rw [hFora_iff_fora]
  by_contra h
  apply hne _ hP
  ext s
  simp only [mem_empty_iff_false, iff_false]
  exact fun hs => h ⟨s, hs⟩

/-- **Todo teste decisivo é uma prova de `¬RH`, e vice-versa**: a "necessidade dos externos" não é mais
fraca do que refutar RH. -/
theorem necessidade_iff :
    (∃ P : Prop, P ∧ (ForaSet = ∅ → ¬ P)) ↔ ¬ RiemannHypothesis := by
  constructor
  · rintro ⟨P, hP, hne⟩
    exact hFora_iff.mp (teste_decisivo hP hne)
  · intro h
    refine ⟨¬ RiemannHypothesis, h, fun hv hn => hn ?_⟩
    rw [ATK.ZerosFora.rh_iff_fora_vazio, ← ATK.ZeroClasses.MundoFora.foraSet_eq]
    exact hv

end ATK.ZeroClasses.Complementar

#print axioms ATK.ZeroClasses.Complementar.exatamente_um
#print axioms ATK.ZeroClasses.Complementar.explosao
#print axioms ATK.ZeroClasses.Complementar.re_nonempty
#print axioms ATK.ZeroClasses.Complementar.re_bdd
#print axioms ATK.ZeroClasses.Complementar.re_le_Theta
#print axioms ATK.ZeroClasses.Complementar.Theta_le_one
#print axioms ATK.ZeroClasses.Complementar.meio_le_Theta
#print axioms ATK.ZeroClasses.Complementar.Theta_mem
#print axioms ATK.ZeroClasses.Complementar.rh_iff_Theta
#print axioms ATK.ZeroClasses.Complementar.fora_iff_Theta
#print axioms ATK.ZeroClasses.Complementar.FM_eq_func
#print axioms ATK.ZeroClasses.Complementar.FM_conj
#print axioms ATK.ZeroClasses.Complementar.FM_refl
#print axioms ATK.ZeroClasses.Complementar.sq_add_sq_eq_zero
#print axioms ATK.ZeroClasses.Complementar.FM_zero_iff
#print axioms ATK.ZeroClasses.Complementar.FM_zero_re
#print axioms ATK.ZeroClasses.Complementar.FM_centrais
#print axioms ATK.ZeroClasses.Complementar.FM_externos
#print axioms ATK.ZeroClasses.Complementar.FM_ponto_medio
#print axioms ATK.ZeroClasses.Complementar.dois_casos_na_familia
#print axioms ATK.ZeroClasses.Complementar.ambos_realizados
#print axioms ATK.ZeroClasses.Complementar.triv_passo
#print axioms ATK.ZeroClasses.Complementar.triv_segunda_diferenca
#print axioms ATK.ZeroClasses.Complementar.triv_compensados
#print axioms ATK.ZeroClasses.Complementar.equilibrio_sem_fora
#print axioms ATK.ZeroClasses.Complementar.sin_meio_zero_iff
#print axioms ATK.ZeroClasses.Complementar.triv_iff_sin
#print axioms ATK.ZeroClasses.Complementar.teste_decisivo
#print axioms ATK.ZeroClasses.Complementar.necessidade_iff
