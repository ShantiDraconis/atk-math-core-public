import ATK.BSDInvariantes
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# ATK — Teorema de Mordell–Weil para curvas com 2-torção racional completa

Para `E : y² = (x − e₁)(x − e₂)(x − e₃)` com `e₁, e₂, e₃ ∈ ℤ` distintos (toda curva elíptica sobre
`ℚ` com os três pontos de 2-torção racionais é isomorfa a uma destas), este arquivo prova, sobre o
grupo de pontos da Mathlib:

* **Mordell–Weil fraco** (`mordellWeil_fraco`): `E(ℚ)/2E(ℚ)` é finito;
* **Mordell–Weil** (`mordellWeil`): `E(ℚ)` é finitamente gerado (com a descida da Mathlib,
  `ATK.BSDInvariantes.fg_of_fraco`), e `posto_finito`: o posto é finito.

A prova é a 2-descida clássica (Silverman, *The Arithmetic of Elliptic Curves*, X.1; Knapp,
*Elliptic Curves*, IV):

1. **o homomorfismo** `φ : E(ℚ) → (ℚˣ/ℚˣ²)²`, `P ↦ ([x − e₁], [x − e₂])` (`phi`): pela identidade
   da reta `(x₁ − e)(x₂ − e)(x₃ − e) = (ℓ(e − x₁) + y₁)²` (de `addPolynomial_slope` da Mathlib,
   `identidade_reta`) e o caso dos pontos de 2-torção (`lado_T`), `δ(P + Q)·δ(P)·δ(Q)` é sempre um
   quadrado (`produto`);
2. **o núcleo está em `2E(ℚ)`** (`nucleo_le`): se `x − eᵢ = rᵢ²` e `y = r₁r₂r₃`, então `(x, y) = 2Q`
   com `Q = (x + r₁r₂ + r₁r₃ + r₂r₃, (r₁ + r₂)(r₁ + r₃)(r₂ + r₃))` (`metade`);
3. **a imagem é finita** (`finito_phi`): `v_p(x − e)` é par para todo primo `p ∤ (e − e')(e − e'')`
   (`par_x_menos_e`, pela ultrametricidade da valuação `p`-ádica), e um racional positivo com todas
   as valuações pares é um quadrado (`Rat.isSquare_iff_even_factorization`, Mathlib).

Teste: `y² = x³ − x` é desta forma (`curva_E32`).

Consequência para a ligação L4: a hipótese `MordellWeil` deixa de ser necessária para essas curvas.
O teorema para **toda** curva elíptica sobre `ℚ` exige a descida com aritmética de corpos de números
(grupos de classes e de unidades), fora do alcance desta etapa.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace ATK.MordellWeilDois

/-- Três raízes inteiras distintas. -/
structure Raizes where
  e₁ : ℤ
  e₂ : ℤ
  e₃ : ℤ
  h₁₂ : e₁ ≠ e₂
  h₁₃ : e₁ ≠ e₃
  h₂₃ : e₂ ≠ e₃

variable (R : Raizes)

/-- `y² = (x − e₁)(x − e₂)(x − e₃)`. -/
def curva : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := -((R.e₁ : ℚ) + R.e₂ + R.e₃)
  a₃ := 0
  a₄ := (R.e₁ : ℚ) * R.e₂ + R.e₁ * R.e₃ + R.e₂ * R.e₃
  a₆ := -((R.e₁ : ℚ) * R.e₂ * R.e₃)

/-- O polinômio cúbico. -/
def f (x : ℚ) : ℚ := (x - R.e₁) * (x - R.e₂) * (x - R.e₃)

theorem equacao_iff (x y : ℚ) : (curva R).toAffine.Equation x y ↔ y ^ 2 = f R x := by
  rw [Affine.equation_iff]
  simp only [curva, f]
  constructor <;> intro h <;> linear_combination h

theorem delta_curva : (curva R).Δ =
    16 * (((R.e₁ : ℚ) - R.e₂) * ((R.e₁ : ℚ) - R.e₃) * ((R.e₂ : ℚ) - R.e₃)) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curva]
  ring

instance eliptica : (curva R).IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [delta_curva]
  have h1 : (R.e₁ : ℚ) - R.e₂ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast R.h₁₂)
  have h2 : (R.e₁ : ℚ) - R.e₃ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast R.h₁₃)
  have h3 : (R.e₂ : ℚ) - R.e₃ ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast R.h₂₃)
  positivity

theorem negY_curva (x y : ℚ) : (curva R).toAffine.negY x y = -y := by
  simp [Affine.negY, curva]

/-- Uma raiz `e` com as outras duas `e', e''`. -/
structure Raiz (e e' e'' : ℚ) : Prop where
  fat : ∀ x, f R x = (x - e) * (x - e') * (x - e'')
  soma : e + e' + e'' = (R.e₁ : ℚ) + R.e₂ + R.e₃
  ne₁ : e ≠ e'
  ne₂ : e ≠ e''

variable {R}

/-- `d_e = (e − e')(e − e'') = f'(e)`. -/
def dd (e e' e'' : ℚ) : ℚ := (e - e') * (e - e'')

theorem dd_ne_zero {e e' e'' : ℚ} (hr : Raiz R e e' e'') : dd e e' e'' ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr hr.ne₁) (sub_ne_zero.mpr hr.ne₂)

theorem y_zero {e e' e'' : ℚ} (hr : Raiz R e e' e'') {y : ℚ}
    (h : (curva R).toAffine.Equation e y) : y = 0 := by
  rw [equacao_iff, hr.fat] at h
  simpa using h

/-- **A reta por `(e, 0)` e `Q = (x₂, y₂)`**: o terceiro ponto tem `(x₂ − e)(x₃ − e) = d_e`. -/
theorem lado_T {e e' e'' : ℚ} (hr : Raiz R e e' e'') {x₂ y₂ : ℚ}
    (h₂ : (curva R).toAffine.Equation x₂ y₂) (hx : x₂ ≠ e) :
    (x₂ - e) * ((curva R).toAffine.addX e x₂ ((curva R).toAffine.slope e x₂ 0 y₂) - e) =
      dd e e' e'' := by
  rw [equacao_iff, hr.fat] at h₂
  rw [slope_of_X_ne (Ne.symm hx)]
  have hs := hr.soma
  have hx' : x₂ - e ≠ 0 := sub_ne_zero.mpr hx
  have hx'' : e - x₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have key : (x₂ - e) * ((0 - y₂) / (e - x₂)) ^ 2 = (x₂ - e') * (x₂ - e'') := by
    rw [div_pow, show (e - x₂) ^ 2 = (x₂ - e) ^ 2 by ring, zero_sub, neg_sq, h₂]
    field_simp
  simp only [WeierstrassCurve.Affine.addX, curva, dd]
  linear_combination key - (x₂ - e) * hs

/-- **A identidade da reta**: `(x₁ − e)(x₂ − e)(x₃ − e) = (ℓ(e − x₁) + y₁)²`. -/
theorem identidade_reta {e e' e'' : ℚ} (hr : Raiz R e e' e'') {x₁ y₁ x₂ y₂ : ℚ}
    (h₁ : (curva R).toAffine.Equation x₁ y₁) (h₂ : (curva R).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (curva R).toAffine.negY x₂ y₂)) :
    (x₁ - e) * (x₂ - e) *
        ((curva R).toAffine.addX x₁ x₂ ((curva R).toAffine.slope x₁ x₂ y₁ y₂) - e) =
      ((curva R).toAffine.slope x₁ x₂ y₁ y₂ * (e - x₁) + y₁) ^ 2 := by
  have h := congrArg (Polynomial.eval e) (addPolynomial_slope h₁ h₂ hxy)
  rw [addPolynomial_eq] at h
  set ℓ := (curva R).toAffine.slope x₁ x₂ y₁ y₂
  have hfe := hr.fat e
  simp only [Cubic.toPoly, Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
    WeierstrassCurve.Affine.addX] at h
  simp only [curva, f] at h hfe
  simp only [WeierstrassCurve.Affine.addX, curva]
  linear_combination -h - hfe


/-! ## O mapa de descida `δ_e` -/

variable (R) in
/-- `E(ℚ)`. -/
abbrev Pt := (curva R).toAffine.Point

/-- `δ_e(O) = 1`, `δ_e(x, y) = x − e` (e `d_e` no ponto `(e, 0)`). -/
def delta (e e' e'' : ℚ) : Pt R → ℚ
  | .zero => 1
  | .some x _ _ => if x = e then dd e e' e'' else x - e

theorem delta_ne_zero {e e' e'' : ℚ} (hr : Raiz R e e' e'') (P : Pt R) :
    delta e e' e'' P ≠ 0 := by
  cases P with
  | zero => simp [delta]
  | some x y h =>
    simp only [delta]
    split_ifs with hx
    · exact dd_ne_zero hr
    · exact sub_ne_zero.mpr hx

theorem nonsingular_raiz {e e' e'' : ℚ} (hr : Raiz R e e' e'') :
    (curva R).toAffine.Nonsingular e 0 :=
  (equation_iff_nonsingular).mp ((equacao_iff R e 0).mpr (by rw [hr.fat]; ring))

/-- O caso em que o primeiro ponto é `(e, y₁)` (logo `y₁ = 0`). -/
theorem caso_raiz {e e' e'' : ℚ} (hr : Raiz R e e' e'') {y₁ x₂ y₂ : ℚ}
    (h₁ : (curva R).toAffine.Nonsingular e y₁) (h₂ : (curva R).toAffine.Nonsingular x₂ y₂) :
    ∃ c : ℚ, delta e e' e'' (.some e y₁ h₁ + .some x₂ y₂ h₂) * delta e e' e'' (.some e y₁ h₁) *
      delta e e' e'' (.some x₂ y₂ h₂) = c ^ 2 := by
  have hy₁ : y₁ = 0 := y_zero hr h₁.1
  subst hy₁
  by_cases hx₂ : x₂ = e
  · subst hx₂
    have hy₂ : y₂ = 0 := y_zero hr h₂.1
    subst hy₂
    rw [Point.add_of_Y_eq rfl (by rw [negY_curva]; simp)]
    exact ⟨dd x₂ e' e'', by simp [delta]; ring⟩
  · have hxy : ¬(e = x₂ ∧ (0 : ℚ) = (curva R).toAffine.negY x₂ y₂) := fun h => hx₂ h.1.symm
    rw [Point.add_some hxy]
    have key := lado_T hr h₂.1 hx₂
    have hx₃ : (curva R).toAffine.addX e x₂ ((curva R).toAffine.slope e x₂ 0 y₂) ≠ e := by
      intro h
      rw [h, sub_self, mul_zero] at key
      exact dd_ne_zero hr key.symm
    refine ⟨dd e e' e'', ?_⟩
    simp only [delta, hx₃, hx₂, ite_true, ite_false]
    linear_combination dd e e' e'' * key

/-- **`δ_e(P + Q)·δ_e(P)·δ_e(Q)` é um quadrado.** -/
theorem produto {e e' e'' : ℚ} (hr : Raiz R e e' e'') (P Q : Pt R) :
    ∃ c : ℚ, delta e e' e'' (P + Q) * delta e e' e'' P * delta e e' e'' Q = c ^ 2 := by
  cases P with
  | zero =>
    have h0 : (Point.zero : Pt R) + Q = Q := zero_add Q
    rw [h0]
    refine ⟨delta e e' e'' Q, ?_⟩
    show delta e e' e'' Q * 1 * delta e e' e'' Q = _
    ring
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      have h0 : Point.some x₁ y₁ h₁ + (Point.zero : Pt R) = Point.some x₁ y₁ h₁ := add_zero _
      rw [h0]
      refine ⟨delta e e' e'' (.some x₁ y₁ h₁), ?_⟩
      show _ * _ * 1 = _
      ring
    | some x₂ y₂ h₂ =>
      by_cases hx₁ : x₁ = e
      · subst hx₁
        exact caso_raiz hr h₁ h₂
      by_cases hx₂ : x₂ = e
      · subst hx₂
        obtain ⟨c, hc⟩ := caso_raiz hr h₂ h₁
        refine ⟨c, ?_⟩
        rw [add_comm, ← hc]
        ring
      by_cases hxy : x₁ = x₂ ∧ y₁ = (curva R).toAffine.negY x₂ y₂
      · rw [Point.add_of_Y_eq hxy.1 hxy.2]
        refine ⟨x₁ - e, ?_⟩
        simp only [delta, hx₁, hx₂, ite_false]
        rw [hxy.1]
        ring
      rw [Point.add_some hxy]
      by_cases hx₃ : (curva R).toAffine.addX x₁ x₂ ((curva R).toAffine.slope x₁ x₂ y₁ y₂) = e
      · -- `P + Q = (e, 0)`, logo `P = (e, 0) − Q`
        have hT := nonsingular_raiz hr
        have hy₃ : (curva R).toAffine.addY x₁ x₂ y₁ ((curva R).toAffine.slope x₁ x₂ y₁ y₂) = 0 := by
          have := (nonsingular_add h₁ h₂ hxy).1
          rw [hx₃] at this
          exact y_zero hr this
        have hPQ : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ = Point.some e 0 hT := by
          rw [Point.add_some hxy]
          simp only [Point.some.injEq]
          exact ⟨hx₃, hy₃⟩
        have hP : Point.some x₁ y₁ h₁ = Point.some e 0 hT + -Point.some x₂ y₂ h₂ := by
          rw [← hPQ, add_neg_cancel_right]
        rw [Point.neg_some] at hP
        have hxy' : ¬(e = x₂ ∧ (0 : ℚ) = (curva R).toAffine.negY x₂
            ((curva R).toAffine.negY x₂ y₂)) := fun h => hx₂ h.1.symm
        rw [Point.add_some hxy'] at hP
        simp only [Point.some.injEq] at hP
        have key := lado_T hr ((nonsingular_neg x₂ y₂).mpr h₂).1 hx₂
        rw [← hP.1] at key
        refine ⟨dd e e' e'', ?_⟩
        simp only [delta, hx₃, hx₁, hx₂, ite_true, ite_false]
        linear_combination dd e e' e'' * key
      · refine ⟨((curva R).toAffine.slope x₁ x₂ y₁ y₂) * (e - x₁) + y₁, ?_⟩
        simp only [delta, hx₃, hx₁, hx₂, ite_false]
        linear_combination identidade_reta hr h₁.1 h₂.1 hxy


/-! ## Classes módulo quadrados e o homomorfismo de descida -/

/-- `ℚˣ/ℚˣ²`. -/
abbrev Q2 := ℚˣ ⧸ (powMonoidHom (α := ℚˣ) 2).range

open Classical in
/-- A classe de `a ∈ ℚ` em `ℚˣ/ℚˣ²` (`1` para `a = 0`). -/
noncomputable def cls (a : ℚ) : Q2 :=
  if h : a = 0 then 1 else QuotientGroup.mk (Units.mk0 a h)

theorem cls_mul {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) : cls (a * b) = cls a * cls b := by
  simp only [cls, ha, hb, mul_ne_zero ha hb, dite_false, ← QuotientGroup.mk_mul]
  congr 1
  ext
  simp

theorem cls_eq_one_iff {a : ℚ} (ha : a ≠ 0) : cls a = 1 ↔ ∃ c : ℚ, a = c ^ 2 := by
  simp only [cls, ha, dite_false, QuotientGroup.eq_one_iff, MonoidHom.mem_range,
    powMonoidHom_apply]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨(v : ℚ), by rw [← Units.val_pow_eq_pow_val, hv, Units.val_mk0]⟩
  · rintro ⟨c, rfl⟩
    have hc : c ≠ 0 := fun h => ha (by rw [h]; ring)
    exact ⟨Units.mk0 c hc, by ext; simp⟩

theorem cls_mul_self {a : ℚ} (ha : a ≠ 0) : cls a * cls a = 1 := by
  rw [← cls_mul ha ha, cls_eq_one_iff (mul_ne_zero ha ha)]
  exact ⟨a, by ring⟩

/-- `φ_e(P) = [δ_e(P)] ∈ ℚˣ/ℚˣ²`. -/
noncomputable def phiE (e e' e'' : ℚ) (P : Pt R) : Q2 := cls (delta e e' e'' P)

/-- **`φ_e` é um homomorfismo.** -/
theorem phiE_add {e e' e'' : ℚ} (hr : Raiz R e e' e'') (P Q : Pt R) :
    phiE e e' e'' (P + Q) = phiE e e' e'' P * phiE e e' e'' Q := by
  obtain ⟨c, hc⟩ := produto hr P Q
  have hA := delta_ne_zero hr (P + Q)
  have hB := delta_ne_zero hr P
  have hC := delta_ne_zero hr Q
  have h1 : phiE e e' e'' (P + Q) * phiE e e' e'' P * phiE e e' e'' Q = 1 := by
    simp only [phiE]
    rw [← cls_mul hA hB, ← cls_mul (mul_ne_zero hA hB) hC, cls_eq_one_iff
      (mul_ne_zero (mul_ne_zero hA hB) hC)]
    exact ⟨c, hc⟩
  have hBB : phiE e e' e'' P * phiE e e' e'' P = 1 := cls_mul_self hB
  have hCC : phiE e e' e'' Q * phiE e e' e'' Q = 1 := cls_mul_self hC
  calc phiE e e' e'' (P + Q)
      = phiE e e' e'' (P + Q) * (phiE e e' e'' P * phiE e e' e'' P) *
          (phiE e e' e'' Q * phiE e e' e'' Q) := by rw [hBB, hCC, mul_one, mul_one]
    _ = (phiE e e' e'' (P + Q) * phiE e e' e'' P * phiE e e' e'' Q) *
          (phiE e e' e'' P * phiE e e' e'' Q) := by
        simp only [mul_assoc, mul_comm, mul_left_comm]
    _ = phiE e e' e'' P * phiE e e' e'' Q := by rw [h1, one_mul]

theorem raiz₁ : Raiz R R.e₁ R.e₂ R.e₃ :=
  ⟨fun x => rfl, rfl, by exact_mod_cast R.h₁₂, by exact_mod_cast R.h₁₃⟩

theorem raiz₂ : Raiz R R.e₂ R.e₁ R.e₃ :=
  ⟨fun x => by simp only [f]; ring, by ring, by exact_mod_cast R.h₁₂.symm,
    by exact_mod_cast R.h₂₃⟩

theorem raiz₃ : Raiz R R.e₃ R.e₁ R.e₂ :=
  ⟨fun x => by simp only [f]; ring, by ring, by exact_mod_cast R.h₁₃.symm,
    by exact_mod_cast R.h₂₃.symm⟩

variable (R) in
/-- **O homomorfismo de descida** `E(ℚ) → (ℚˣ/ℚˣ²)²`, `P ↦ ([x − e₁], [x − e₂])`. -/
noncomputable def phi : Pt R →+ Additive (Q2 × Q2) :=
  AddMonoidHom.mk' (fun P => Additive.ofMul (phiE R.e₁ R.e₂ R.e₃ P, phiE R.e₂ R.e₁ R.e₃ P))
    (fun P Q => by
      rw [phiE_add raiz₁, phiE_add raiz₂]
      rfl)

/-! ## O núcleo está em `2E(ℚ)` -/

/-- **Divisão por 2**: se `x − eᵢ = rᵢ²` e `y = r₁r₂r₃`, então `(x, y) = 2Q` com
`Q = (x + r₁r₂ + r₁r₃ + r₂r₃, (r₁ + r₂)(r₁ + r₃)(r₂ + r₃))`. -/
theorem metade {x y : ℚ} (h : (curva R).toAffine.Nonsingular x y) {r₁ r₂ r₃ : ℚ}
    (h₁ : x - R.e₁ = r₁ ^ 2) (h₂ : x - R.e₂ = r₂ ^ 2) (h₃ : x - R.e₃ = r₃ ^ 2)
    (hy : y = r₁ * r₂ * r₃) : ∃ Q : Pt R, Q + Q = .some x y h := by
  have he₁ : (R.e₁ : ℚ) = x - r₁ ^ 2 := by linarith
  have he₂ : (R.e₂ : ℚ) = x - r₂ ^ 2 := by linarith
  have he₃ : (R.e₃ : ℚ) = x - r₃ ^ 2 := by linarith
  have n12 : (R.e₁ : ℚ) ≠ R.e₂ := by exact_mod_cast R.h₁₂
  have n13 : (R.e₁ : ℚ) ≠ R.e₃ := by exact_mod_cast R.h₁₃
  have n23 : (R.e₂ : ℚ) ≠ R.e₃ := by exact_mod_cast R.h₂₃
  have s12 : r₁ + r₂ ≠ 0 := by
    intro hs; apply n12; rw [he₁, he₂, show r₁ = -r₂ by linarith]; ring
  have s13 : r₁ + r₃ ≠ 0 := by
    intro hs; apply n13; rw [he₁, he₃, show r₁ = -r₃ by linarith]; ring
  have s23 : r₂ + r₃ ≠ 0 := by
    intro hs; apply n23; rw [he₂, he₃, show r₂ = -r₃ by linarith]; ring
  set x₀ := x + r₁ * r₂ + r₁ * r₃ + r₂ * r₃ with hx₀
  set y₀ := (r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃) with hy₀
  have hy₀0 : y₀ ≠ 0 := mul_ne_zero (mul_ne_zero s12 s13) s23
  have heq : (curva R).toAffine.Equation x₀ y₀ := by
    rw [equacao_iff]
    simp only [f, hx₀, hy₀, he₁, he₂, he₃]
    ring
  have hns : (curva R).toAffine.Nonsingular x₀ y₀ := equation_iff_nonsingular.mp heq
  have hne : y₀ ≠ (curva R).toAffine.negY x₀ y₀ := by
    rw [negY_curva]
    intro h'
    exact hy₀0 (by linarith)
  have hℓ : (curva R).toAffine.slope x₀ x₀ y₀ y₀ = r₁ + r₂ + r₃ := by
    rw [slope_of_Y_ne rfl hne, negY_curva, div_eq_iff (by intro h'; exact hy₀0 (by linarith))]
    simp only [curva, hx₀, hy₀, he₁, he₂, he₃]
    ring
  refine ⟨.some x₀ y₀ hns, ?_⟩
  rw [Point.add_some (fun h' => hne h'.2)]
  simp only [Point.some.injEq]
  constructor
  · simp only [WeierstrassCurve.Affine.addX]
    rw [hℓ]
    simp only [curva, hx₀, he₁, he₂, he₃]
    ring
  · simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.negY]
    rw [hℓ]
    simp only [curva, hx₀, hy₀, hy, he₁, he₂, he₃]
    ring


theorem phi_eq_zero_iff (P : Pt R) :
    phi R P = 0 ↔ phiE R.e₁ R.e₂ R.e₃ P = 1 ∧ phiE R.e₂ R.e₁ R.e₃ P = 1 := by
  change Additive.ofMul (phiE R.e₁ R.e₂ R.e₃ P, phiE R.e₂ R.e₁ R.e₃ P) = 0 ↔ _
  rw [ofMul_eq_zero, Prod.mk_eq_one]

/-- **O núcleo de `φ` está em `2E(ℚ)`.** -/
theorem nucleo_le : (phi R).ker ≤ (nsmulAddMonoidHom (α := Pt R) 2).range := by
  intro P hP
  rw [AddMonoidHom.mem_ker, phi_eq_zero_iff] at hP
  obtain ⟨hφ₁, hφ₂⟩ := hP
  obtain ⟨c₁, hc₁⟩ := (cls_eq_one_iff (delta_ne_zero raiz₁ P)).mp hφ₁
  obtain ⟨c₂, hc₂⟩ := (cls_eq_one_iff (delta_ne_zero raiz₂ P)).mp hφ₂
  rw [AddMonoidHom.mem_range]
  suffices h : ∃ Q : Pt R, Q + Q = P by
    obtain ⟨Q, hQ⟩ := h
    exact ⟨Q, by rw [nsmulAddMonoidHom_apply, two_nsmul, hQ]⟩
  cases P with
  | zero => exact ⟨0, add_zero 0⟩
  | some x y h =>
    have n12 : (R.e₁ : ℚ) ≠ R.e₂ := by exact_mod_cast R.h₁₂
    have n13 : (R.e₁ : ℚ) ≠ R.e₃ := by exact_mod_cast R.h₁₃
    have n23 : (R.e₂ : ℚ) ≠ R.e₃ := by exact_mod_cast R.h₂₃
    have heq := (equacao_iff R x y).mp h.1
    simp only [f] at heq
    simp only [delta] at hc₁ hc₂
    by_cases hx₁ : x = R.e₁
    · subst hx₁
      have hy : y = 0 := y_zero raiz₁ h.1
      rw [ite_eq_left rfl, dd] at hc₁
      rw [ite_eq_right n12] at hc₂
      have hc₂0 : c₂ ≠ 0 := by
        rintro rfl; apply n12; linarith [hc₂]
      refine metade h (r₁ := 0) (r₂ := c₂) (r₃ := c₁ / c₂) (by ring) hc₂ ?_ (by rw [hy]; ring)
      field_simp
      linear_combination hc₁ - ((R.e₁ : ℚ) - R.e₃) * hc₂
    by_cases hx₂ : x = R.e₂
    · subst hx₂
      have hy : y = 0 := y_zero raiz₂ h.1
      rw [ite_eq_right (Ne.symm n12)] at hc₁
      rw [ite_eq_left rfl, dd] at hc₂
      have hc₁0 : c₁ ≠ 0 := by
        rintro rfl; apply n12; linarith [hc₁]
      refine metade h (r₁ := c₁) (r₂ := 0) (r₃ := c₂ / c₁) hc₁ (by ring) ?_ (by rw [hy]; ring)
      field_simp
      linear_combination hc₂ - ((R.e₂ : ℚ) - R.e₃) * hc₁
    rw [ite_eq_right hx₁] at hc₁
    rw [ite_eq_right hx₂] at hc₂
    by_cases hx₃ : x = R.e₃
    · subst hx₃
      have hy : y = 0 := y_zero raiz₃ h.1
      exact metade h (r₁ := c₁) (r₂ := c₂) (r₃ := 0) hc₁ hc₂ (by ring) (by rw [hy]; ring)
    · have hc₁0 : c₁ ≠ 0 := by
        rintro rfl; apply hx₁; linarith [hc₁]
      have hc₂0 : c₂ ≠ 0 := by
        rintro rfl; apply hx₂; linarith [hc₂]
      refine metade h (r₁ := c₁) (r₂ := c₂) (r₃ := y / (c₁ * c₂)) hc₁ hc₂ ?_ (by field_simp)
      field_simp
      rw [hc₁, hc₂] at heq
      linear_combination -heq


/-! ## A imagem de `φ` é finita -/

section valuacao

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem vInt_nonneg (z : ℤ) : 0 ≤ padicValRat p (z : ℚ) := by
  rw [padicValRat.of_int]; exact Int.natCast_nonneg _

omit hp in
theorem vInt_zero {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) : padicValRat p (z : ℚ) = 0 := by
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hz, Nat.cast_zero]

/-- `v(q) < 0` ⇒ `v(q + z) = v(q)` para `z ∈ ℤ`. -/
theorem v_add_int_neg {q : ℚ} (hq : q ≠ 0) (hv : padicValRat p q < 0) (z : ℤ) :
    q + z ≠ 0 ∧ padicValRat p (q + z) = padicValRat p q := by
  by_cases hz : (z : ℚ) = 0
  · rw [hz, add_zero]; exact ⟨hq, rfl⟩
  have hlt : padicValRat p q < padicValRat p (z : ℚ) := lt_of_lt_of_le hv (vInt_nonneg z)
  have hne : q + z ≠ 0 := by
    intro h
    have : q = -(z : ℚ) := by linarith
    rw [this, padicValRat.neg] at hlt
    exact lt_irrefl _ hlt
  exact ⟨hne, padicValRat.add_eq_of_lt hne hq hz hlt⟩

/-- `v(q) ≥ 0` ⇒ `v(q + z) ≥ 0`. -/
theorem v_add_int_nonneg {q : ℚ} (hv : 0 ≤ padicValRat p q) (z : ℤ) (hqz : q + z ≠ 0) :
    0 ≤ padicValRat p (q + z) :=
  le_trans (le_min hv (vInt_nonneg z)) (padicValRat.min_le_padicValRat_add hqz)

/-- `v(q) > 0` e `p ∤ z` ⇒ `v(q + z) = 0`. -/
theorem v_add_int_pos {q : ℚ} (hq : q ≠ 0) (hv : 0 < padicValRat p q) {z : ℤ}
    (hz : ¬ (p : ℤ) ∣ z) : q + z ≠ 0 ∧ padicValRat p (q + z) = 0 := by
  have hz0 : (z : ℚ) ≠ 0 := by
    intro h; apply hz; rw [Int.cast_eq_zero.mp h]; exact dvd_zero _
  have h0 := vInt_zero (p := p) hz
  have hne : q + z ≠ 0 := by
    intro h
    have : q = -(z : ℚ) := by linarith
    rw [this, padicValRat.neg, h0] at hv
    exact lt_irrefl _ hv
  refine ⟨hne, ?_⟩
  rw [padicValRat.add_eq_min hne hq hz0 (by rw [h0]; exact ne_of_gt hv), h0, min_eq_right hv.le]

end valuacao

/-- `q` tem valuação par em todo primo que não divide `D`. -/
def Bom (D : ℤ) (q : ℚ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ D → Even (padicValRat p q)

/-- **Paridade das valuações**: para `P = (x, y)` com `x ∉ {e, e', e''}` e `p ∤ (e − e')(e − e'')`,
`v_p(x − e)` é par. -/
theorem par_x_menos_e {e e' e'' : ℤ} (hr : Raiz R e e' e'') {x y : ℚ}
    (h : (curva R).toAffine.Equation x y) (hx : x ≠ e) (hx' : x ≠ e') (hx'' : x ≠ e'') :
    Bom ((e - e') * (e - e'')) (x - e) := by
  intro p hpp hpD
  have := Fact.mk hpp
  have hp1 : ¬ (p : ℤ) ∣ e - e' := fun h => hpD (dvd_mul_of_dvd_left h _)
  have hp2 : ¬ (p : ℤ) ∣ e - e'' := fun h => hpD (dvd_mul_of_dvd_right h _)
  rw [equacao_iff, hr.fat] at h
  have hu : x - e ≠ 0 := sub_ne_zero.mpr hx
  have hu' : x - e' ≠ 0 := sub_ne_zero.mpr hx'
  have hu'' : x - e'' ≠ 0 := sub_ne_zero.mpr hx''
  have hy : y ≠ 0 := by
    rintro rfl
    have : (x - e) * (x - e') * (x - e'') ≠ 0 := mul_ne_zero (mul_ne_zero hu hu') hu''
    exact this (by rw [← h]; ring)
  have hsum : 2 * padicValRat p y = padicValRat p (x - e) + padicValRat p (x - e') +
      padicValRat p (x - e'') := by
    have := congrArg (padicValRat p) h
    rw [padicValRat.pow, padicValRat.mul (mul_ne_zero hu hu') hu'', padicValRat.mul hu hu'] at this
    push_cast at this
    linarith
  have e1 : x - (e : ℚ) = x + ((-e : ℤ) : ℚ) := by push_cast; ring
  have e2 : x - (e' : ℚ) = x + ((-e' : ℤ) : ℚ) := by push_cast; ring
  have e3 : x - (e'' : ℚ) = x + ((-e'' : ℤ) : ℚ) := by push_cast; ring
  by_cases hneg : padicValRat p x < 0
  · have hx0 : x ≠ 0 := by rintro rfl; simp at hneg
    obtain ⟨-, h1⟩ := v_add_int_neg hx0 hneg (-e)
    obtain ⟨-, h2⟩ := v_add_int_neg hx0 hneg (-e')
    obtain ⟨-, h3⟩ := v_add_int_neg hx0 hneg (-e'')
    rw [← e1] at h1
    rw [← e2] at h2
    rw [← e3] at h3
    rw [h1, h2, h3] at hsum
    rw [h1]
    exact ⟨padicValRat p y - padicValRat p x, by linarith⟩
  · push Not at hneg
    have hv : 0 ≤ padicValRat p (x - e) := by
      rw [e1]; exact v_add_int_nonneg hneg _ (by rw [← e1]; exact hu)
    rcases hv.lt_or_eq with hpos | hzero
    · have e4 : x - (e' : ℚ) = (x - e) + ((e - e' : ℤ) : ℚ) := by push_cast; ring
      have e5 : x - (e'' : ℚ) = (x - e) + ((e - e'' : ℤ) : ℚ) := by push_cast; ring
      obtain ⟨-, h4⟩ := v_add_int_pos hu hpos hp1
      obtain ⟨-, h5⟩ := v_add_int_pos hu hpos hp2
      rw [← e4] at h4
      rw [← e5] at h5
      rw [h4, h5] at hsum
      exact ⟨padicValRat p y, by linarith⟩
    · rw [← hzero]; exact ⟨0, by ring⟩

/-- `δ_e(P)` tem valuação par fora dos primos de `(e − e')(e − e'')`. -/
theorem bom_delta {e e' e'' : ℤ} (hr : Raiz R e e' e'') (P : Pt R) :
    Bom ((e - e') * (e - e'')) (delta e e' e'' P) := by
  intro p hpp hpD
  have := Fact.mk hpp
  have hp1 : ¬ (p : ℤ) ∣ e - e' := fun h => hpD (dvd_mul_of_dvd_left h _)
  have hp2 : ¬ (p : ℤ) ∣ e - e'' := fun h => hpD (dvd_mul_of_dvd_right h _)
  cases P with
  | zero => exact ⟨0, by simp [delta]⟩
  | some x y h =>
    simp only [delta]
    split_ifs with hx
    · have : dd (e : ℚ) e' e'' = (((e - e') * (e - e'') : ℤ) : ℚ) := by simp [dd]
      rw [this, vInt_zero hpD]
      exact ⟨0, rfl⟩
    · by_cases hx' : x = e'
      · have : x - (e : ℚ) = ((-(e - e') : ℤ) : ℚ) := by rw [hx']; push_cast; ring
        rw [this, vInt_zero (by rwa [dvd_neg])]
        exact ⟨0, rfl⟩
      by_cases hx'' : x = e''
      · have : x - (e : ℚ) = ((-(e - e'') : ℤ) : ℚ) := by rw [hx'']; push_cast; ring
        rw [this, vInt_zero (by rwa [dvd_neg])]
        exact ⟨0, rfl⟩
      exact par_x_menos_e hr h.1 hx hx' hx'' p hpp hpD

/-- **Finitude**: há só um número finito de classes de racionais "bons" em `ℚˣ/ℚˣ²`. -/
theorem finito_classes {D : ℤ} (hD : D ≠ 0) :
    {c : Q2 | ∃ q : ℚ, q ≠ 0 ∧ Bom D q ∧ cls q = c}.Finite := by
  classical
  let T := Bool × (D.natAbs.primeFactors → ZMod 2)
  let ψ : ℚ → T := fun q => (decide (0 < q), fun p => ((padicValRat p.1 q : ℤ) : ZMod 2))
  have key : ∀ q₁ q₂ : ℚ, q₁ ≠ 0 → q₂ ≠ 0 → Bom D q₁ → Bom D q₂ → ψ q₁ = ψ q₂ →
      cls q₁ = cls q₂ := by
    intro q₁ q₂ h₁ h₂ b₁ b₂ hψ
    have hψ1 := congrArg Prod.fst hψ
    have hψ2 := congrArg Prod.snd hψ
    simp only [ψ, decide_eq_decide] at hψ1 hψ2
    have hpos : 0 ≤ q₁ / q₂ := by
      rcases lt_or_gt_of_ne h₂ with hn | hp
      · have : q₁ < 0 := by
          by_contra hc; push Not at hc
          exact absurd (hψ1.mp (lt_of_le_of_ne hc (Ne.symm h₁))) (not_lt.mpr hn.le)
        exact (div_pos_of_neg_of_neg this hn).le
      · exact (div_pos (hψ1.mpr hp) hp).le
    have hsq : IsSquare (q₁ / q₂) := by
      rw [Rat.isSquare_iff_even_factorization]
      refine ⟨hpos, fun p hp => ?_⟩
      have := Fact.mk hp
      rw [padicValRat.div h₁ h₂]
      by_cases hpD : (p : ℤ) ∣ D
      · have hmem : p ∈ D.natAbs.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp, Int.ofNat_dvd_left.mp hpD, Int.natAbs_ne_zero.mpr hD⟩
        have := congrFun hψ2 ⟨p, hmem⟩
        simp only at this
        rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
        rw [even_iff_two_dvd, ← dvd_neg]
        simpa using this
      · exact (b₁ p hp hpD).sub (b₂ p hp hpD)
    obtain ⟨c, hc⟩ := hsq
    have hc0 : c ≠ 0 := by
      rintro rfl; simp at hc; exact h₁ (by rcases hc with h | h <;> simp_all)
    have hq : q₁ = c ^ 2 * q₂ := by
      rw [sq, ← hc]; field_simp
    rw [hq, cls_mul (pow_ne_zero 2 hc0) h₂, (cls_eq_one_iff (pow_ne_zero 2 hc0)).mpr ⟨c, rfl⟩,
      one_mul]
  refine Set.Finite.subset (Set.finite_iUnion fun t : T =>
    (show {c : Q2 | ∃ q : ℚ, q ≠ 0 ∧ Bom D q ∧ ψ q = t ∧ cls q = c}.Subsingleton from ?_).finite) ?_
  · rintro _ ⟨q₁, h₁, b₁, t₁, rfl⟩ _ ⟨q₂, h₂, b₂, t₂, rfl⟩
    exact key q₁ q₂ h₁ h₂ b₁ b₂ (t₁.trans t₂.symm)
  · rintro _ ⟨q, hq, hb, rfl⟩
    exact Set.mem_iUnion.mpr ⟨ψ q, q, hq, hb, rfl, rfl⟩

theorem finito_phiE {e e' e'' : ℤ} (hr : Raiz R e e' e'') :
    (Set.range (phiE (R := R) e e' e'')).Finite := by
  have hD : (e - e') * (e - e'') ≠ 0 := by
    have h1 : (e : ℚ) - e' ≠ 0 := sub_ne_zero.mpr hr.ne₁
    have h2 : (e : ℚ) - e'' ≠ 0 := sub_ne_zero.mpr hr.ne₂
    exact_mod_cast mul_ne_zero h1 h2
  refine (finito_classes hD).subset ?_
  rintro _ ⟨P, rfl⟩
  exact ⟨delta e e' e'' P, delta_ne_zero hr P, bom_delta hr P, rfl⟩

theorem raizInt₁ : Raiz R (R.e₁ : ℤ) (R.e₂ : ℤ) (R.e₃ : ℤ) := raiz₁

theorem raizInt₂ : Raiz R (R.e₂ : ℤ) (R.e₁ : ℤ) (R.e₃ : ℤ) := raiz₂

/-- **A imagem do homomorfismo de descida é finita.** -/
theorem finito_phi : (Set.range (phi R)).Finite := by
  refine ((finito_phiE (raizInt₁ (R := R))).prod (finito_phiE (raizInt₂ (R := R)))).image
    (fun ab : Q2 × Q2 => Additive.ofMul ab) |>.subset ?_
  rintro _ ⟨P, rfl⟩
  exact ⟨(phiE R.e₁ R.e₂ R.e₃ P, phiE R.e₂ R.e₁ R.e₃ P), ⟨⟨P, rfl⟩, ⟨P, rfl⟩⟩, rfl⟩

/-! ## Mordell–Weil fraco e Mordell–Weil -/

variable (R) in
/-- **Teorema de Mordell–Weil fraco** para `y² = (x − e₁)(x − e₂)(x − e₃)`: `E(ℚ)/2E(ℚ)` é finito. -/
theorem mordellWeil_fraco : (nsmulAddMonoidHom (α := Pt R) 2).range.FiniteIndex := by
  have : Finite (phi R).range := by
    have h := finito_phi (R := R)
    rw [← AddMonoidHom.coe_range] at h
    exact h.to_subtype
  exact AddSubgroup.finiteIndex_of_le nucleo_le

variable (R) in
/-- **Teorema de Mordell–Weil** para `y² = (x − e₁)(x − e₂)(x − e₃)` (`eᵢ ∈ ℤ` distintos):
`E(ℚ)` é finitamente gerado. -/
theorem mordellWeil : AddGroup.FG (Pt R) :=
  ATK.BSDInvariantes.fg_of_fraco (curva R) (mordellWeil_fraco R)

variable (R) in
/-- O posto de Mordell–Weil dessas curvas é finito. -/
theorem posto_finito : ATK.LigacaoBSD.postoMW (curva R) ≠ ⊤ := by
  have : Module.Finite ℤ (Pt R) := Module.Finite.iff_addGroup_fg.mpr (mordellWeil R)
  unfold ATK.LigacaoBSD.postoMW
  rw [Ne, Cardinal.toENat_eq_top, not_le]
  exact Module.rank_lt_aleph0 ℤ _

/-- **Teste**: `y² = x³ − x` é `y² = (x − 0)(x − 1)(x + 1)`. -/
def R32 : Raizes := ⟨0, 1, -1, by decide, by decide, by decide⟩

theorem curva_E32 : curva R32 = ATK.L4Base.E32 := by
  ext <;> simp [curva, R32, ATK.L4Base.E32, ATK.CongruentCurve.E]

end ATK.MordellWeilDois

#print axioms ATK.MordellWeilDois.equacao_iff
#print axioms ATK.MordellWeilDois.delta_curva
#print axioms ATK.MordellWeilDois.negY_curva
#print axioms ATK.MordellWeilDois.dd_ne_zero
#print axioms ATK.MordellWeilDois.y_zero
#print axioms ATK.MordellWeilDois.lado_T
#print axioms ATK.MordellWeilDois.identidade_reta
#print axioms ATK.MordellWeilDois.delta_ne_zero
#print axioms ATK.MordellWeilDois.nonsingular_raiz
#print axioms ATK.MordellWeilDois.caso_raiz
#print axioms ATK.MordellWeilDois.produto
#print axioms ATK.MordellWeilDois.cls_mul
#print axioms ATK.MordellWeilDois.cls_eq_one_iff
#print axioms ATK.MordellWeilDois.cls_mul_self
#print axioms ATK.MordellWeilDois.phiE_add
#print axioms ATK.MordellWeilDois.raiz₁
#print axioms ATK.MordellWeilDois.raiz₂
#print axioms ATK.MordellWeilDois.raiz₃
#print axioms ATK.MordellWeilDois.metade
#print axioms ATK.MordellWeilDois.phi_eq_zero_iff
#print axioms ATK.MordellWeilDois.nucleo_le
#print axioms ATK.MordellWeilDois.vInt_nonneg
#print axioms ATK.MordellWeilDois.vInt_zero
#print axioms ATK.MordellWeilDois.v_add_int_neg
#print axioms ATK.MordellWeilDois.v_add_int_nonneg
#print axioms ATK.MordellWeilDois.v_add_int_pos
#print axioms ATK.MordellWeilDois.par_x_menos_e
#print axioms ATK.MordellWeilDois.bom_delta
#print axioms ATK.MordellWeilDois.finito_classes
#print axioms ATK.MordellWeilDois.finito_phiE
#print axioms ATK.MordellWeilDois.raizInt₁
#print axioms ATK.MordellWeilDois.raizInt₂
#print axioms ATK.MordellWeilDois.finito_phi
#print axioms ATK.MordellWeilDois.mordellWeil_fraco
#print axioms ATK.MordellWeilDois.mordellWeil
#print axioms ATK.MordellWeilDois.posto_finito
#print axioms ATK.MordellWeilDois.curva_E32
