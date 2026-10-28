/-
ATK.Base (B2, parcial) — Redução mod p separa a 2-torsão racional.

Continua `ATK.BaseNagellLutzDois`.  Para `y² = x³ + a₂x² + a₄x + a₆` com `aᵢ ∈ ℤ`, o discriminante
da cúbica é `d = a₂²a₄² − 4a₄³ − 4a₂³a₆ + 18a₂a₄a₆ − 27a₆²` e o da curva é `Δ = 16 d`.

* **`Δ_eq`**: `Δ = 16 d` quando `a₁ = a₃ = 0`;
* **`disc_eq_raizes`**: se `x ≠ y` são raízes inteiras, a terceira raiz é `z = −a₂ − x − y` e
  `d = ((x − y)(x − z)(y − z))²`;
* **`raizes_separadas`**: `p ∤ d` ⇒ `p ∤ (x − y)`;
* **`reducao_dois_torsao`**: dois pontos racionais distintos de ordem 2 têm coordenadas `x`
  inteiras **distintas módulo p** para todo `p` com `p ∤ d` — a redução `E(ℚ)[2] → E(𝔽_p)` é
  injetiva em boa redução (`p ∤ Δ`, `p` ímpar).

O caso geral (`E(ℚ)_tors ↪ E(𝔽_p)` para toda a torsão) exige o grupo formal e fica em B2.
-/
import ATK.BaseNagellLutzDois
import Mathlib.Data.ZMod.Basic

namespace ATK.BaseReducaoDois

open WeierstrassCurve WeierstrassCurve.Affine ATK.BaseCurvasTorsao ATK.BaseNagellLutzDois

/-- Discriminante da cúbica mônica `x³ + ax² + bx + c`. -/
def discCubica {R : Type*} [CommRing R] (a b c : R) : R :=
  a ^ 2 * b ^ 2 - 4 * b ^ 3 - 4 * a ^ 3 * c + 18 * a * b * c - 27 * c ^ 2

/-- **`Δ = 16 d`** para `y² = x³ + a₂x² + a₄x + a₆`. -/
theorem Δ_eq {R : Type*} [CommRing R] {W : WeierstrassCurve R} (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) :
    W.Δ = 16 * discCubica W.a₂ W.a₄ W.a₆ := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, ha₁, ha₃, discCubica]
  ring

/-- **Discriminante pelas raízes**: com duas raízes distintas `x, y`, a terceira é
`z = −a − x − y` e `d = ((x − y)(x − z)(y − z))²`. -/
theorem disc_eq_raizes {R : Type*} [CommRing R] [IsDomain R] {a b c x y : R}
    (hx : x ^ 3 + a * x ^ 2 + b * x + c = 0) (hy : y ^ 3 + a * y ^ 2 + b * y + c = 0)
    (hxy : x ≠ y) :
    discCubica a b c = ((x - y) * (x - (-a - x - y)) * (y - (-a - x - y))) ^ 2 := by
  have hb : b = -(x ^ 2 + x * y + y ^ 2 + a * (x + y)) := by
    have h : (x - y) * (x ^ 2 + x * y + y ^ 2 + a * (x + y) + b) = 0 := by
      linear_combination hx - hy
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hxy
    · linear_combination h
  have hc : c = -(x ^ 3 + a * x ^ 2 + b * x) := by linear_combination hx
  subst hc
  subst hb
  unfold discCubica
  ring

/-- **Raízes separadas mod p**: `p ∤ d ⇒ p ∤ (x − y)`. -/
theorem raizes_separadas {a b c x y p : ℤ}
    (hx : x ^ 3 + a * x ^ 2 + b * x + c = 0) (hy : y ^ 3 + a * y ^ 2 + b * y + c = 0)
    (hxy : x ≠ y) (hp : ¬ p ∣ discCubica a b c) : ¬ p ∣ (x - y) := by
  intro hd
  apply hp
  rw [disc_eq_raizes hx hy hxy]
  exact Dvd.dvd.pow (Dvd.dvd.mul_right (Dvd.dvd.mul_right hd _) _) two_ne_zero

/-- **Redução mod p injetiva na 2-torsão racional.** Dois pontos racionais distintos de ordem 2
de `y² = x³ + a₂x² + a₄x + a₆` (`aᵢ ∈ ℤ`) têm coordenadas `x` inteiras e distintas em `ZMod p`
sempre que `p ∤ d`. -/
theorem reducao_dois_torsao {W : WeierstrassCurve.Affine ℚ} (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {a₂ a₄ a₆ : ℤ} (h₂ : W.a₂ = a₂) (h₄ : W.a₄ = a₄) (h₆ : W.a₆ = a₆) {p : ℕ}
    (hp : ¬ (p : ℤ) ∣ discCubica a₂ a₄ a₆) {x y x' y' : ℚ} (h : W.Nonsingular x y)
    (h' : W.Nonsingular x' y') (hP : Point.some x y h + Point.some x y h = 0)
    (hQ : Point.some x' y' h' + Point.some x' y' h' = 0)
    (hne : Point.some x y h ≠ Point.some x' y' h') :
    ∃ n n' : ℤ, x = n ∧ x' = n' ∧ ((n : ZMod p) ≠ (n' : ZMod p)) := by
  obtain ⟨hy0, n, hn, -⟩ := nagellLutz_dois ha₁ ha₃ h₂ h₄ h₆ h hP
  obtain ⟨hy0', n', hn', -⟩ := nagellLutz_dois ha₁ ha₃ h₂ h₄ h₆ h' hQ
  refine ⟨n, n', hn, hn', ?_⟩
  have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
  have hr := (ordem_dois_iff_raiz ha₁ ha₃ h2 h).mp hP
  have hr' := (ordem_dois_iff_raiz ha₁ ha₃ h2 h').mp hQ
  rw [h₂, h₄, h₆, hn] at hr
  rw [h₂, h₄, h₆, hn'] at hr'
  have hz : n ^ 3 + a₂ * n ^ 2 + a₄ * n + a₆ = 0 := by exact_mod_cast hr
  have hz' : n' ^ 3 + a₂ * n' ^ 2 + a₄ * n' + a₆ = 0 := by exact_mod_cast hr'
  have hnn : n ≠ n' := by
    intro he
    apply hne
    subst hy0 hy0'
    have : x = x' := by rw [hn, hn', he]
    subst this
    rfl
  intro heq
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at heq
  exact raizes_separadas hz' hz (Ne.symm hnn) hp heq

end ATK.BaseReducaoDois

#print axioms ATK.BaseReducaoDois.Δ_eq
#print axioms ATK.BaseReducaoDois.disc_eq_raizes
#print axioms ATK.BaseReducaoDois.raizes_separadas
#print axioms ATK.BaseReducaoDois.reducao_dois_torsao
