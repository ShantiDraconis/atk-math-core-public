import ATK.ZeroClasses.Basic

/-!
# ATK-ZERO-CLASSES — simetrias e órbitas para uma reta `x = c` arbitrária

Hipóteses explícitas, nunca embutidas:

* `ConjEquiv f`: `f(z̄) = conj(f z)` ⇒ `z ∈ Z(f) → z̄ ∈ Z(f)` (`zero_conj`);
* `ReflZeros f c`: `z ∈ Z(f) → 2c − z ∈ Z(f)` (`zero_refl`); basta uma equação funcional
  `f(2c − z) = u(z)·f(z)` com `u` **qualquer** (`refl_de_equacao`);
* as duas juntas dão a **torção** `z ↦ 2c − z̄`, cujo conjunto fixo é exatamente a reta `x = c`
  (`tor_fixo_iff`), e a órbita `𝒪(z) = {z, z̄, 2c − z, 2c − z̄} ⊆ Z(f)` (`orbita_sub`).

**Classificação** (`orbita_card_iff`): `|𝒪(z)| = 1 ⟺ z = c`; `|𝒪(z)| = 4 ⟺ x ≠ c ∧ y ≠ 0`; nos outros
casos `|𝒪(z)| = 2`; nunca `3` (`orbita_nao_tres`).

**A simetria não exclui zeros fora da reta** (`simetria_nao_basta`): `g(z) = (z − c)⁴ + 4` satisfaz as duas
simetrias e tem o quarteto `c ± 1 ± i` fora da reta `x = c`.
-/

open Complex ComplexConjugate Set

namespace ATK.ZeroClasses

variable {f : ℂ → ℂ} {c : ℝ}

/-- `f(z̄) = conj(f z)`. -/
def ConjEquiv (f : ℂ → ℂ) : Prop := ∀ z, f (conj z) = conj (f z)

/-- Os zeros são preservados pela reflexão `z ↦ 2c − z`. -/
def ReflZeros (f : ℂ → ℂ) (c : ℝ) : Prop := ∀ z, f z = 0 → f (2 * (c : ℂ) - z) = 0

/-- Reflexão central em `c`. -/
def refl (c : ℝ) (z : ℂ) : ℂ := 2 * (c : ℂ) - z

/-- Torção `z ↦ 2c − z̄` (reflexão na reta `x = c`). -/
noncomputable def tor (c : ℝ) (z : ℂ) : ℂ := 2 * (c : ℂ) - conj z

@[simp] theorem refl_re (z : ℂ) : (refl c z).re = 2 * c - z.re := by simp [refl]
@[simp] theorem refl_im (z : ℂ) : (refl c z).im = -z.im := by simp [refl]
@[simp] theorem tor_re (z : ℂ) : (tor c z).re = 2 * c - z.re := by simp [tor]
@[simp] theorem tor_im (z : ℂ) : (tor c z).im = z.im := by simp [tor]

theorem zero_conj (hf : ConjEquiv f) {z : ℂ} (hz : IsZero f z) : IsZero f (conj z) := by
  unfold IsZero at *
  rw [hf, hz, map_zero]

theorem zero_refl (hf : ReflZeros f c) {z : ℂ} (hz : IsZero f z) : IsZero f (refl c z) := hf z hz

theorem zero_tor (hc : ConjEquiv f) (hr : ReflZeros f c) {z : ℂ} (hz : IsZero f z) :
    IsZero f (tor c z) := hr _ (zero_conj hc hz)

/-- Uma equação funcional `f(2c − z) = u(z) f(z)`, com `u` arbitrário, já basta. -/
theorem refl_de_equacao {u : ℂ → ℂ} (h : ∀ z, f (2 * (c : ℂ) - z) = u z * f z) : ReflZeros f c :=
  fun z hz => by rw [h, hz, mul_zero]

theorem tor_tor (z : ℂ) : tor c (tor c z) = z := by
  apply Complex.ext <;> simp

theorem refl_refl (z : ℂ) : refl c (refl c z) = z := by
  apply Complex.ext <;> simp

/-- **O conjunto fixo da torção é a reta `x = c`.** -/
theorem tor_fixo_iff (z : ℂ) : tor c z = z ↔ z.re = c := by
  constructor
  · intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  · intro h
    apply Complex.ext <;> simp
    linarith

theorem conj_fixo_iff (z : ℂ) : conj z = z ↔ z.im = 0 := Complex.conj_eq_iff_im

theorem refl_fixo_iff (z : ℂ) : refl c z = z ↔ z = c := by
  constructor
  · intro h
    apply Complex.ext
    · have := congrArg Complex.re h; simp at this; simp; linarith
    · have := congrArg Complex.im h; simp at this; simp; linarith
  · rintro rfl
    unfold refl; ring

/-- Um zero na reta é fixo pela torção: na reta, a simetria não produz zeros novos além de `z̄`. -/
theorem onLine_tor {z : ℂ} (h : OnLine f c z) : tor c z = z := (tor_fixo_iff z).mpr h.2

/-! ## A órbita -/

/-- `𝒪(z) = {z, z̄, 2c − z, 2c − z̄}`. -/
noncomputable def orbita (c : ℝ) (z : ℂ) : Finset ℂ :=
  open Classical in {z, conj z, refl c z, tor c z}

theorem mem_orbita_self (z : ℂ) : z ∈ orbita c z := by
  classical
  simp [orbita]

/-- **A órbita de um zero é feita de zeros** (sob as duas simetrias). -/
theorem orbita_sub (hc : ConjEquiv f) (hr : ReflZeros f c) {z : ℂ} (hz : IsZero f z) :
    ∀ w ∈ orbita c z, IsZero f w := by
  intro w hw
  classical
  simp only [orbita, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact hz
  · exact zero_conj hc hz
  · exact zero_refl hr hz
  · exact zero_tor hc hr hz

theorem card_quatro {z : ℂ} (hre : z.re ≠ c) (him : z.im ≠ 0) : (orbita c z).card = 4 := by
  classical
  have hre' : z.re ≠ 2 * c - z.re := fun h => hre (by linarith)
  have him' : z.im ≠ -z.im := fun h => him (by linarith)
  have a1 : z ≠ conj z := fun h => him' (by have := congrArg Complex.im h; simpa using this)
  have a2 : z ≠ refl c z := fun h => hre' (by have := congrArg Complex.re h; simpa using this)
  have a3 : z ≠ tor c z := fun h => hre' (by have := congrArg Complex.re h; simpa using this)
  have a4 : conj z ≠ refl c z := fun h => hre' (by have := congrArg Complex.re h; simpa using this)
  have a5 : conj z ≠ tor c z := fun h => hre' (by have := congrArg Complex.re h; simpa using this)
  have a6 : refl c z ≠ tor c z := fun h => him' (by have := congrArg Complex.im h; simpa using this.symm)
  unfold orbita
  rw [Finset.card_insert_of_notMem (by simp [a1, a2, a3]),
    Finset.card_insert_of_notMem (by simp [a4, a5]), Finset.card_pair a6]

theorem card_dois_linha {z : ℂ} (hre : z.re = c) (him : z.im ≠ 0) : (orbita c z).card = 2 := by
  classical
  have h1 : refl c z = conj z := by apply Complex.ext <;> simp; linarith
  have h2 : tor c z = z := (tor_fixo_iff z).mpr hre
  have hne : z ≠ conj z := fun h => him (by
    have := congrArg Complex.im h; simp at this; linarith)
  unfold orbita
  rw [h1, h2]
  simp
  exact Finset.card_pair (Ne.symm hne)

theorem card_dois_eixo {z : ℂ} (hre : z.re ≠ c) (him : z.im = 0) : (orbita c z).card = 2 := by
  classical
  have h1 : conj z = z := (conj_fixo_iff z).mpr him
  have h2 : tor c z = refl c z := by apply Complex.ext <;> simp [him]
  have hne : z ≠ refl c z := fun h => hre (by
    have := congrArg Complex.re h; simp at this; linarith)
  unfold orbita
  rw [h1, h2]
  simp [Finset.card_pair hne]

theorem card_um {z : ℂ} (hre : z.re = c) (him : z.im = 0) : (orbita c z).card = 1 := by
  classical
  have hz : z = c := by apply Complex.ext <;> simp [hre, him]
  have h1 : conj z = z := (conj_fixo_iff z).mpr him
  have h2 : refl c z = z := (refl_fixo_iff z).mpr hz
  have h3 : tor c z = z := (tor_fixo_iff z).mpr hre
  unfold orbita
  rw [h1, h2, h3]
  simp

/-- **Classificação das órbitas**: `1 ⟺ z = c`, `4 ⟺ x ≠ c ∧ y ≠ 0`, e `2` nos casos mistos. -/
theorem orbita_card_iff (z : ℂ) :
    ((orbita c z).card = 1 ↔ z.re = c ∧ z.im = 0) ∧
      ((orbita c z).card = 2 ↔ (z.re = c ∧ z.im ≠ 0) ∨ (z.re ≠ c ∧ z.im = 0)) ∧
      ((orbita c z).card = 4 ↔ z.re ≠ c ∧ z.im ≠ 0) := by
  by_cases hre : z.re = c <;> by_cases him : z.im = 0
  · simp [card_um hre him, hre, him]
  · simp [card_dois_linha hre him, hre, him]
  · simp [card_dois_eixo hre him, hre, him]
  · simp [card_quatro hre him, hre, him]

theorem orbita_card (z : ℂ) :
    (orbita c z).card = 1 ∨ (orbita c z).card = 2 ∨ (orbita c z).card = 4 := by
  by_cases hre : z.re = c <;> by_cases him : z.im = 0
  · exact Or.inl (card_um hre him)
  · exact Or.inr (Or.inl (card_dois_linha hre him))
  · exact Or.inr (Or.inl (card_dois_eixo hre him))
  · exact Or.inr (Or.inr (card_quatro hre him))

theorem orbita_nao_tres (z : ℂ) : (orbita c z).card ≠ 3 := by
  rcases orbita_card (c := c) z with h | h | h <;> rw [h] <;> decide

/-- Um zero **misto e fora da reta** (sob as duas simetrias) traz quatro zeros distintos. -/
theorem quarteto_de_zero (hc : ConjEquiv f) (hr : ReflZeros f c) {z : ℂ} (hz : IsZero f z)
    (hre : z.re ≠ c) (him : z.im ≠ 0) :
    (orbita c z).card = 4 ∧ ∀ w ∈ orbita c z, OffLine f c w := by
  refine ⟨card_quatro hre him, fun w hw => ⟨orbita_sub hc hr hz w hw, ?_⟩⟩
  classical
  simp only [orbita, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact hre
  · simpa using hre
  · simp; intro h; exact hre (by linarith)
  · simp; intro h; exact hre (by linarith)

/-! ## A simetria não basta -/

/-- `g(z) = (z − c)⁴ + 4`. -/
def gSim (c : ℝ) (z : ℂ) : ℂ := (z - c) ^ 4 + 4

/-- **Contraexemplo**: `g` tem as duas simetrias e um zero fora da reta `x = c`. -/
theorem simetria_nao_basta (c : ℝ) :
    ConjEquiv (gSim c) ∧ ReflZeros (gSim c) c ∧ OffLine (gSim c) c ((c : ℂ) + 1 + I) ∧
      (orbita c ((c : ℂ) + 1 + I)).card = 4 := by
  refine ⟨fun z => ?_, refl_de_equacao (u := fun _ => 1) fun z => ?_, ⟨?_, ?_⟩, card_quatro ?_ ?_⟩
  · have h4 : (starRingEnd ℂ) (4 : ℂ) = 4 := map_ofNat _ 4
    simp [gSim, map_add, map_pow, map_sub, Complex.conj_ofReal, h4]
  · simp only [gSim, one_mul]; ring
  · unfold IsZero gSim
    have : ((c : ℂ) + 1 + I - c) = 1 + I := by ring
    rw [this]
    have h4 : (1 + I) ^ 4 = -4 := by
      have h2 : (1 + I) ^ 2 = 2 * I := by ring_nf; rw [I_sq]; ring
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2]; ring_nf; rw [I_sq]; ring
    rw [h4]; ring
  · simp
  · simp
  · simp

end ATK.ZeroClasses

#print axioms ATK.ZeroClasses.refl_re
#print axioms ATK.ZeroClasses.refl_im
#print axioms ATK.ZeroClasses.tor_re
#print axioms ATK.ZeroClasses.tor_im
#print axioms ATK.ZeroClasses.zero_conj
#print axioms ATK.ZeroClasses.zero_refl
#print axioms ATK.ZeroClasses.zero_tor
#print axioms ATK.ZeroClasses.refl_de_equacao
#print axioms ATK.ZeroClasses.tor_tor
#print axioms ATK.ZeroClasses.refl_refl
#print axioms ATK.ZeroClasses.tor_fixo_iff
#print axioms ATK.ZeroClasses.conj_fixo_iff
#print axioms ATK.ZeroClasses.refl_fixo_iff
#print axioms ATK.ZeroClasses.onLine_tor
#print axioms ATK.ZeroClasses.mem_orbita_self
#print axioms ATK.ZeroClasses.orbita_sub
#print axioms ATK.ZeroClasses.card_quatro
#print axioms ATK.ZeroClasses.card_dois_linha
#print axioms ATK.ZeroClasses.card_dois_eixo
#print axioms ATK.ZeroClasses.card_um
#print axioms ATK.ZeroClasses.orbita_card_iff
#print axioms ATK.ZeroClasses.orbita_card
#print axioms ATK.ZeroClasses.orbita_nao_tres
#print axioms ATK.ZeroClasses.quarteto_de_zero
#print axioms ATK.ZeroClasses.simetria_nao_basta
