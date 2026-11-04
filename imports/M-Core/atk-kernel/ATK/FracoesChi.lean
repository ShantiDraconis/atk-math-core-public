import Mathlib.NumberTheory.FLT.Three
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# ATK — A fração `χ(p, q, r) = 1/p + 1/q + 1/r − 1` (rodada 103)

Uma única fração decide três geometrias e o comportamento de três equações:

* `χ > 0` (**esférico**): `(2, 2, n)`, `(2, 3, 3)`, `(2, 3, 4)`, `(2, 3, 5)` — `chi_pos_iff`. A ordem do grupo de
  rotações correspondente é `2/χ`: diedral `2n`, `A₄` (12), `S₄` (24), `A₅` (60) — `ordem_*`. É a simetria
  do tetraedro, do octaedro e do icosaedro (bola de futebol, cúpulas geodésicas, cápsides de vírus).
* `χ = 0` (**euclidiano**): `(2, 3, 6)`, `(2, 4, 4)`, `(3, 3, 3)` — `chi_zero_iff`. Os três ladrilhamentos
  periódicos do plano: hexágonos (favo de mel, grafeno), quadrados (piso), triângulos (treliças).
* **Euler** (`euler_de_chi`, `platonicos`): com `E = 1/χ(2, p, q)`, `V = 2/(qχ)`, `F = 2/(pχ)`,
  `V − E + F = 2χ/χ = 2` — a característica de Euler da esfera (a sombra topológica de Hodge) é `χ`.
* `χ < 0` (**hiperbólico**): todo o resto, e então `χ ≤ −1/42`, com igualdade só em `(2, 3, 7)` —
  `chi_neg_le`, `chi_eq_iff`. Daí a cota de Hurwitz `(2g − 2)/|χ| ≤ 84(g − 1)` (`hurwitz`), atingida na
  quártica de Klein (`g = 3`, `168 = |GL₃(𝔽₂)|`, `hurwitz_klein`).

**Beal.** Para `A^x + B^y = C^z` com `x, y, z ≥ 3`: `χ ≤ 0`, `χ = 0` só em `(3, 3, 3)` e, fora dele,
`χ ≤ −1/12` (`beal_chi_*`). No ponto `χ = 0` não há solução alguma (Euler, `fermatLastTheoremThree` da
Mathlib: `beal_333`). No lado esférico há infinitas soluções primitivas (`esferico_222_infinito`, para
`(2, 2, 2)`). No lado hiperbólico, a finitude das soluções primitivas é o teorema de Darmon–Granville (1995),
aqui uma ponte nomeada (`PonteDarmonGranville`); Beal pede **zero** soluções primitivas, o que continua
`OPEN_MATH`. A fração `χ` é o expoente da cauda heurística: o número de soluções com `C^z ≤ X` cresce como
`X^χ` (companheiro numérico).

Classificação: **reformulação/consequência** (resultados clássicos). Nada aqui prova Beal.
-/

namespace ATK.Fracoes.Chi

/-- `χ(p, q, r) = 1/p + 1/q + 1/r − 1`. -/
def chi (p q r : ℕ) : ℚ := 1 / p + 1 / q + 1 / r - 1

theorem chi_symm₁ (p q r : ℕ) : chi p q r = chi q p r := by unfold chi; ring
theorem chi_symm₂ (p q r : ℕ) : chi p q r = chi p r q := by unfold chi; ring

/-- `1/b ≤ 1/a` para `0 < a ≤ b` (naturais). -/
theorem inv_le {a b : ℕ} (ha : 0 < a) (h : a ≤ b) : (1 : ℚ) / b ≤ 1 / a :=
  one_div_le_one_div_of_le (by exact_mod_cast ha) (by exact_mod_cast h)

theorem inv_pos' {a : ℕ} (ha : 0 < a) : (0 : ℚ) < 1 / a := by
  have : (0 : ℚ) < a := by exact_mod_cast ha
  positivity

/-! ## 1. A tricotomia -/

/-- **Esférico.** Para `2 ≤ p ≤ q ≤ r`: `χ > 0` exatamente para `(2, 2, r)` e `(2, 3, 3..5)`. -/
theorem chi_pos_iff {p q r : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) :
    0 < chi p q r ↔ (p = 2 ∧ q = 2) ∨ (p = 2 ∧ q = 3 ∧ r ≤ 5) := by
  unfold chi
  rcases (show p = 2 ∨ 3 ≤ p by omega) with rfl | hp3
  · rcases (show q = 2 ∨ q = 3 ∨ 4 ≤ q by omega) with rfl | rfl | hq4
    · simp only [true_and, true_or, iff_true]
      have := inv_pos' (a := r) (by omega)
      push_cast; linarith
    · constructor
      · intro h
        right
        refine ⟨rfl, rfl, ?_⟩
        by_contra hr
        have := inv_le (a := 6) (b := r) (by omega) (by omega)
        push_cast at h this
        linarith
      · rintro (⟨-, h⟩ | ⟨-, -, hr⟩)
        · omega
        · have := inv_le (a := r) (b := 5) (by omega) hr
          push_cast at this ⊢
          linarith
    · simp only [show q ≠ 2 by omega, show q ≠ 3 by omega, false_and, and_false, or_self,
        iff_false, not_lt]
      have h1 := inv_le (a := 4) (b := q) (by omega) hq4
      have h2 := inv_le (a := 4) (b := r) (by omega) (by omega)
      push_cast at h1 h2 ⊢; linarith
  · simp only [show p ≠ 2 by omega, false_and, or_self, iff_false, not_lt]
    have h1 := inv_le (a := 3) (b := p) (by omega) hp3
    have h2 := inv_le (a := 3) (b := q) (by omega) (by omega)
    have h3 := inv_le (a := 3) (b := r) (by omega) (by omega)
    push_cast at h1 h2 h3; linarith

/-- **Euclidiano.** Para `2 ≤ p ≤ q ≤ r`: `χ = 0` exatamente para `(2, 3, 6)`, `(2, 4, 4)`, `(3, 3, 3)`. -/
theorem chi_zero_iff {p q r : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) :
    chi p q r = 0 ↔ (p = 2 ∧ q = 3 ∧ r = 6) ∨ (p = 2 ∧ q = 4 ∧ r = 4) ∨ (p = 3 ∧ q = 3 ∧ r = 3) := by
  constructor
  · intro h
    unfold chi at h
    rcases (show p = 2 ∨ p = 3 ∨ 4 ≤ p by omega) with rfl | rfl | hp4
    · rcases (show q = 2 ∨ q = 3 ∨ q = 4 ∨ 5 ≤ q by omega) with rfl | rfl | rfl | hq5
      · have := inv_pos' (a := r) (by omega); push_cast at h; linarith
      · rcases (show r ≤ 5 ∨ r = 6 ∨ 7 ≤ r by omega) with hr | rfl | hr
        · have := inv_le (a := r) (b := 5) (by omega) hr; push_cast at h; linarith
        · left; exact ⟨rfl, rfl, rfl⟩
        · have := inv_le (a := 7) (b := r) (by omega) hr; push_cast at h this; linarith
      · rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | hr
        · right; left; exact ⟨rfl, rfl, rfl⟩
        · have := inv_le (a := 5) (b := r) (by omega) hr; push_cast at h this; linarith
      · have h1 := inv_le (a := 5) (b := q) (by omega) hq5
        have h2 := inv_le (a := 5) (b := r) (by omega) (by omega)
        push_cast at h h1 h2; linarith
    · rcases (show q = 3 ∨ 4 ≤ q by omega) with rfl | hq4
      · rcases (show r = 3 ∨ 4 ≤ r by omega) with rfl | hr
        · right; right; exact ⟨rfl, rfl, rfl⟩
        · have := inv_le (a := 4) (b := r) (by omega) hr; push_cast at h this; linarith
      · have h1 := inv_le (a := 4) (b := q) (by omega) hq4
        have h2 := inv_le (a := 4) (b := r) (by omega) (by omega)
        push_cast at h h1 h2; linarith
    · have h1 := inv_le (a := 4) (b := p) (by omega) hp4
      have h2 := inv_le (a := 4) (b := q) (by omega) (by omega)
      have h3 := inv_le (a := 4) (b := r) (by omega) (by omega)
      push_cast at h h1 h2 h3; linarith
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num [chi]

/-- **Hiperbólico: a lacuna `1/42`.** Para `2 ≤ p ≤ q ≤ r`, se `χ < 0` então `χ ≤ −1/42`. -/
theorem chi_neg_le {p q r : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) (h : chi p q r < 0) :
    chi p q r ≤ -1 / 42 := by
  unfold chi at h ⊢
  rcases (show p = 2 ∨ p = 3 ∨ 4 ≤ p by omega) with rfl | rfl | hp4
  · rcases (show q = 2 ∨ q = 3 ∨ q = 4 ∨ 5 ≤ q by omega) with rfl | rfl | rfl | hq5
    · have := inv_pos' (a := r) (by omega); push_cast at h; linarith
    · rcases (show r ≤ 6 ∨ 7 ≤ r by omega) with hr | hr
      · have := inv_le (a := r) (b := 6) (by omega) hr; push_cast at h this; linarith
      · have := inv_le (a := 7) (b := r) (by omega) hr; push_cast at h this ⊢; linarith
    · rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | hr
      · norm_num at h
      · have := inv_le (a := 5) (b := r) (by omega) hr; push_cast at this ⊢; linarith
    · have h1 := inv_le (a := 5) (b := q) (by omega) hq5
      have h2 := inv_le (a := 5) (b := r) (by omega) (by omega)
      push_cast at h1 h2 ⊢; linarith
  · rcases (show q = 3 ∨ 4 ≤ q by omega) with rfl | hq4
    · rcases (show r = 3 ∨ 4 ≤ r by omega) with rfl | hr
      · norm_num at h
      · have := inv_le (a := 4) (b := r) (by omega) hr; push_cast at this ⊢; linarith
    · have h1 := inv_le (a := 4) (b := q) (by omega) hq4
      have h2 := inv_le (a := 4) (b := r) (by omega) (by omega)
      push_cast at h1 h2 ⊢; linarith
  · have h1 := inv_le (a := 4) (b := p) (by omega) hp4
    have h2 := inv_le (a := 4) (b := q) (by omega) (by omega)
    have h3 := inv_le (a := 4) (b := r) (by omega) (by omega)
    push_cast at h1 h2 h3 ⊢; linarith

/-- **A lacuna é atingida só em `(2, 3, 7)`.** -/
theorem chi_eq_iff {p q r : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) :
    chi p q r = -1 / 42 ↔ p = 2 ∧ q = 3 ∧ r = 7 := by
  constructor
  · intro h
    unfold chi at h
    rcases (show p = 2 ∨ p = 3 ∨ 4 ≤ p by omega) with rfl | rfl | hp4
    · rcases (show q = 2 ∨ q = 3 ∨ q = 4 ∨ 5 ≤ q by omega) with rfl | rfl | rfl | hq5
      · have := inv_pos' (a := r) (by omega); push_cast at h; linarith
      · rcases (show r ≤ 6 ∨ r = 7 ∨ 8 ≤ r by omega) with hr | rfl | hr
        · have := inv_le (a := r) (b := 6) (by omega) hr; push_cast at h this; linarith
        · exact ⟨rfl, rfl, rfl⟩
        · have := inv_le (a := 8) (b := r) (by omega) hr; push_cast at h this; linarith
      · rcases (show r = 4 ∨ 5 ≤ r by omega) with rfl | hr
        · norm_num at h
        · have := inv_le (a := 5) (b := r) (by omega) hr; push_cast at h this; linarith
      · have h1 := inv_le (a := 5) (b := q) (by omega) hq5
        have h2 := inv_le (a := 5) (b := r) (by omega) (by omega)
        push_cast at h h1 h2; linarith
    · rcases (show q = 3 ∨ 4 ≤ q by omega) with rfl | hq4
      · rcases (show r = 3 ∨ 4 ≤ r by omega) with rfl | hr
        · norm_num at h
        · have := inv_le (a := 4) (b := r) (by omega) hr; push_cast at h this; linarith
      · have h1 := inv_le (a := 4) (b := q) (by omega) hq4
        have h2 := inv_le (a := 4) (b := r) (by omega) (by omega)
        push_cast at h h1 h2; linarith
    · have h1 := inv_le (a := 4) (b := p) (by omega) hp4
      have h2 := inv_le (a := 4) (b := q) (by omega) (by omega)
      have h3 := inv_le (a := 4) (b := r) (by omega) (by omega)
      push_cast at h h1 h2 h3; linarith
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num [chi]

/-! ## 2. As ordens `2/χ` dos grupos esféricos -/

theorem ordem_diedral (n : ℕ) (hn : 2 ≤ n) :
    2 / chi 2 2 n = ((Nat.card (DihedralGroup n) : ℕ) : ℚ) := by
  rw [DihedralGroup.nat_card]
  have : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold chi
  push_cast
  field_simp
  ring

theorem ordem_tetraedral : 2 / chi 2 3 3 = ((Fintype.card (alternatingGroup (Fin 4)) : ℕ) : ℚ) := by
  rw [card_alternatingGroup, Fintype.card_fin]
  norm_num [chi, Nat.factorial]

theorem ordem_octaedral : 2 / chi 2 3 4 = ((Fintype.card (Equiv.Perm (Fin 4)) : ℕ) : ℚ) := by
  rw [Fintype.card_perm, Fintype.card_fin]
  norm_num [chi, Nat.factorial]

theorem ordem_icosaedral : 2 / chi 2 3 5 = ((Fintype.card (alternatingGroup (Fin 5)) : ℕ) : ℚ) := by
  rw [card_alternatingGroup, Fintype.card_fin]
  norm_num [chi, Nat.factorial]

/-! ## 2b. Euler `V − E + F = 2` é `2χ/χ` -/

/-- **Euler a partir de `χ`**: com faces `p`-gonais, `q` faces por vértice e `χ = χ(2, p, q) ≠ 0`,
`E = 1/χ`, `V = 2/(qχ)`, `F = 2/(pχ)` satisfazem `V − E + F = 2` (é a identidade `2χ/χ = 2`). -/
theorem euler_de_chi {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (h : chi 2 p q ≠ 0) :
    2 / (q * chi 2 p q) - 1 / chi 2 p q + 2 / (p * chi 2 p q) = 2 := by
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  set c := chi 2 p q with hc
  have hc' : 1 / (p : ℚ) + 1 / q - 1 / 2 = c := by
    rw [hc, chi]; push_cast; ring
  have key : 2 / (q * c) - 1 / c + 2 / (p * c) = 2 * (1 / (p : ℚ) + 1 / q - 1 / 2) / c := by
    field_simp
    ring
  rw [key, hc']
  field_simp

/-- **Os cinco sólidos platônicos** `(V, E, F)` saem de `χ(2, p, q)`: tetraedro `{3,3}`, cubo `{4,3}`,
octaedro `{3,4}`, dodecaedro `{5,3}`, icosaedro `{3,5}`. -/
theorem platonicos :
    (1 / chi 2 3 3 = 6 ∧ 2 / (3 * chi 2 3 3) = 4 ∧ 2 / (3 * chi 2 3 3) = 4) ∧
    (1 / chi 2 4 3 = 12 ∧ 2 / (3 * chi 2 4 3) = 8 ∧ 2 / (4 * chi 2 4 3) = 6) ∧
    (1 / chi 2 3 4 = 12 ∧ 2 / (4 * chi 2 3 4) = 6 ∧ 2 / (3 * chi 2 3 4) = 8) ∧
    (1 / chi 2 5 3 = 30 ∧ 2 / (3 * chi 2 5 3) = 20 ∧ 2 / (5 * chi 2 5 3) = 12) ∧
    (1 / chi 2 3 5 = 30 ∧ 2 / (5 * chi 2 3 5) = 12 ∧ 2 / (3 * chi 2 3 5) = 20) := by
  norm_num [chi]

/-! ## 3. Hurwitz: `84(g − 1)` -/

/-- **Cota de Hurwitz (forma aritmética).** Se `χ < 0`, `(2g − 2)/|χ| ≤ 84(g − 1)` para `g ≥ 1`. -/
theorem hurwitz {p q r : ℕ} (hp : 2 ≤ p) (hpq : p ≤ q) (hqr : q ≤ r) (h : chi p q r < 0)
    {g : ℚ} (hg : 1 ≤ g) : (2 * g - 2) / (-chi p q r) ≤ 84 * (g - 1) := by
  have h42 := chi_neg_le hp hpq hqr h
  have hpos : 0 < -chi p q r := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith

/-- **Quártica de Klein**: `84(3 − 1) = 168 = |GL₃(𝔽₂)|`. -/
theorem hurwitz_klein : (84 * (3 - 1) : ℕ) = Nat.card (GL (Fin 3) (ZMod 2)) := by
  rw [Matrix.card_GL_field, ZMod.card]
  decide

/-! ## 4. Beal: `x, y, z ≥ 3` -/

theorem beal_chi_nonpos {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) : chi x y z ≤ 0 := by
  have h1 := inv_le (a := 3) (b := x) (by omega) hx
  have h2 := inv_le (a := 3) (b := y) (by omega) hy
  have h3 := inv_le (a := 3) (b := z) (by omega) hz
  unfold chi; push_cast at h1 h2 h3; linarith

/-- Fora de `(3, 3, 3)`, a região de Beal tem `χ ≤ −1/12`. -/
theorem beal_chi_gap {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (h : ¬ (x = 3 ∧ y = 3 ∧ z = 3)) : chi x y z ≤ -1 / 12 := by
  have h1 := inv_le (a := 3) (b := x) (by omega) hx
  have h2 := inv_le (a := 3) (b := y) (by omega) hy
  have h3 := inv_le (a := 3) (b := z) (by omega) hz
  unfold chi
  rcases (show 4 ≤ x ∨ 4 ≤ y ∨ 4 ≤ z by omega) with h4 | h4 | h4
  · have := inv_le (a := 4) (b := x) (by omega) h4; push_cast at h1 h2 h3 this ⊢; linarith
  · have := inv_le (a := 4) (b := y) (by omega) h4; push_cast at h1 h2 h3 this ⊢; linarith
  · have := inv_le (a := 4) (b := z) (by omega) h4; push_cast at h1 h2 h3 this ⊢; linarith

theorem beal_chi_zero_iff {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    chi x y z = 0 ↔ x = 3 ∧ y = 3 ∧ z = 3 := by
  constructor
  · intro h
    by_contra hn
    have := beal_chi_gap hx hy hz hn
    linarith
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num [chi]

/-- **No ponto `χ = 0` de Beal não há solução** (Euler; `fermatLastTheoremThree`, Mathlib). -/
theorem beal_333 : ∀ A B C : ℕ, A ≠ 0 → B ≠ 0 → C ≠ 0 → A ^ 3 + B ^ 3 ≠ C ^ 3 :=
  fermatLastTheoremThree

/-- Soluções primitivas positivas de `A^x + B^y = C^z`. -/
def Primitivas (x y z : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {t | 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧ Nat.gcd t.1 (Nat.gcd t.2.1 t.2.2) = 1 ∧
    t.1 ^ x + t.2.1 ^ y = t.2.2 ^ z}

/-- **Lado esférico**: `(2, 2, 2)` (`χ = ½`) tem infinitas soluções primitivas:
`(2k + 1)² + (2k² + 2k)² = (2k² + 2k + 1)²`. -/
theorem esferico_222_infinito : (Primitivas 2 2 2).Infinite := by
  have hinj : Function.Injective
      (fun k : ℕ => ((2 * (k + 1) + 1, 2 * (k + 1) ^ 2 + 2 * (k + 1), 2 * (k + 1) ^ 2 + 2 * (k + 1) + 1) :
        ℕ × ℕ × ℕ)) := by
    intro a b h
    simp only [Prod.mk.injEq] at h
    omega
  refine Set.infinite_of_injective_forall_mem hinj fun k => ?_
  refine ⟨by positivity, by positivity, by positivity, ?_, by ring⟩
  have : Nat.gcd (2 * (k + 1) ^ 2 + 2 * (k + 1)) (2 * (k + 1) ^ 2 + 2 * (k + 1) + 1) = 1 := by
    simp
  simp only [this, Nat.gcd_one_right]

/-- **Ponte (Darmon–Granville 1995; publicada, não formalizada).** Para `χ < 0`, só há finitas soluções
primitivas. -/
def PonteDarmonGranville : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → chi x y z < 0 → (Primitivas x y z).Finite

/-- Com Darmon–Granville: na região de Beal fora de `(3, 3, 3)`, finitas soluções primitivas; em
`(3, 3, 3)`, nenhuma. Beal (nenhuma, sempre) continua aberto. -/
theorem beal_por_chi (hDG : PonteDarmonGranville) {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    (Primitivas x y z).Finite := by
  by_cases h3 : x = 3 ∧ y = 3 ∧ z = 3
  · obtain ⟨rfl, rfl, rfl⟩ := h3
    refine Set.Finite.subset (Set.finite_empty) ?_
    rintro ⟨A, B, C⟩ ⟨hA, hB, hC, -, hE⟩
    exact absurd hE (beal_333 A B C hA.ne' hB.ne' hC.ne')
  · exact hDG x y z (by omega) (by omega) (by omega)
      (lt_of_le_of_lt (beal_chi_gap hx hy hz h3) (by norm_num))

end ATK.Fracoes.Chi

#print axioms ATK.Fracoes.Chi.chi_symm₁
#print axioms ATK.Fracoes.Chi.chi_symm₂
#print axioms ATK.Fracoes.Chi.inv_le
#print axioms ATK.Fracoes.Chi.inv_pos'
#print axioms ATK.Fracoes.Chi.chi_pos_iff
#print axioms ATK.Fracoes.Chi.chi_zero_iff
#print axioms ATK.Fracoes.Chi.chi_neg_le
#print axioms ATK.Fracoes.Chi.chi_eq_iff
#print axioms ATK.Fracoes.Chi.ordem_diedral
#print axioms ATK.Fracoes.Chi.ordem_tetraedral
#print axioms ATK.Fracoes.Chi.ordem_octaedral
#print axioms ATK.Fracoes.Chi.ordem_icosaedral
#print axioms ATK.Fracoes.Chi.euler_de_chi
#print axioms ATK.Fracoes.Chi.platonicos
#print axioms ATK.Fracoes.Chi.hurwitz
#print axioms ATK.Fracoes.Chi.hurwitz_klein
#print axioms ATK.Fracoes.Chi.beal_chi_nonpos
#print axioms ATK.Fracoes.Chi.beal_chi_gap
#print axioms ATK.Fracoes.Chi.beal_chi_zero_iff
#print axioms ATK.Fracoes.Chi.beal_333
#print axioms ATK.Fracoes.Chi.esferico_222_infinito
#print axioms ATK.Fracoes.Chi.beal_por_chi
