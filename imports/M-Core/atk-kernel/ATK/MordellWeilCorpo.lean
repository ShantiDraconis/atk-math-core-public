import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# ATK — 2-descida sobre um corpo qualquer

Para um corpo `F` com `2 ≠ 0` e `E : y² = (x − e₁)(x − e₂)(x − e₃)` com `e₁, e₂, e₃ ∈ F` distintos,
este arquivo constrói, sobre o grupo de pontos da Mathlib:

* **o homomorfismo de descida** `φ : E(F) → (F*/F*²)²`, `P ↦ ([x − e₁], [x − e₂])` (`phi`), pela
  identidade da reta `(x₁ − e)(x₂ − e)(x₃ − e) = (ℓ(e − x₁) + y₁)²` (`identidade_reta`);
* **o núcleo de `φ` está em `2E(F)`** (`nucleo_le`): se `x − eᵢ = rᵢ²` e `y = r₁r₂r₃`, então
  `(x, y) = 2Q` com `Q = (x + r₁r₂ + r₁r₃ + r₂r₃, (r₁ + r₂)(r₁ + r₃)(r₂ + r₃))` (`metade`);
* **critério de finitude** (`fraco_de_finito`): se a imagem de `φ` é finita, `2E(F)` tem índice
  finito em `E(F)`.

É a parte algébrica da 2-descida de `ATK.MordellWeilDois` (que trata `F = ℚ`), agora para qualquer
corpo: será aplicada ao corpo de decomposição da cúbica de uma curva elíptica sobre `ℚ`.

Também: os pontos de 2-torção são `O` e `(eᵢ, 0)` (`dois_torcao`), logo `E(F)[2]` é finito
(`finito_dois_torcao`).
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace ATK.MordellWeilCorpo

variable {F : Type*} [Field F]

/-- Três raízes distintas em `F`. -/
structure Raizes (F : Type*) [Field F] where
  e₁ : F
  e₂ : F
  e₃ : F
  h₁₂ : e₁ ≠ e₂
  h₁₃ : e₁ ≠ e₃
  h₂₃ : e₂ ≠ e₃

variable (R : Raizes F)

/-- `y² = (x − e₁)(x − e₂)(x − e₃)`. -/
def curva : WeierstrassCurve F where
  a₁ := 0
  a₂ := -(R.e₁ + R.e₂ + R.e₃)
  a₃ := 0
  a₄ := R.e₁ * R.e₂ + R.e₁ * R.e₃ + R.e₂ * R.e₃
  a₆ := -(R.e₁ * R.e₂ * R.e₃)

/-- O polinômio cúbico. -/
def f (x : F) : F := (x - R.e₁) * (x - R.e₂) * (x - R.e₃)

theorem equacao_iff (x y : F) : (curva R).toAffine.Equation x y ↔ y ^ 2 = f R x := by
  rw [Affine.equation_iff]
  simp only [curva, f]
  constructor <;> intro h <;> linear_combination h

theorem delta_curva : (curva R).Δ =
    16 * ((R.e₁ - R.e₂) * (R.e₁ - R.e₃) * (R.e₂ - R.e₃)) ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, curva]
  ring

instance eliptica [NeZero (2 : F)] : (curva R).IsElliptic := by
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [delta_curva]
  have h1 : R.e₁ - R.e₂ ≠ 0 := sub_ne_zero.mpr R.h₁₂
  have h2 : R.e₁ - R.e₃ ≠ 0 := sub_ne_zero.mpr R.h₁₃
  have h3 : R.e₂ - R.e₃ ≠ 0 := sub_ne_zero.mpr R.h₂₃
  have h16 : (16 : F) ≠ 0 := by
    have h2' : (2 : F) ≠ 0 := NeZero.ne 2
    have : (16 : F) = 2 ^ 4 := by norm_num
    rw [this]
    exact pow_ne_zero 4 h2'
  exact mul_ne_zero h16 (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero h1 h2) h3))

theorem negY_curva (x y : F) : (curva R).toAffine.negY x y = -y := by
  simp [Affine.negY, curva]

/-- Uma raiz `e` com as outras duas `e', e''`. -/
structure Raiz (e e' e'' : F) : Prop where
  fat : ∀ x, f R x = (x - e) * (x - e') * (x - e'')
  soma : e + e' + e'' = R.e₁ + R.e₂ + R.e₃
  ne₁ : e ≠ e'
  ne₂ : e ≠ e''

variable {R}

/-- `d_e = (e − e')(e − e'') = f'(e)`. -/
def dd (e e' e'' : F) : F := (e - e') * (e - e'')

theorem dd_ne_zero {e e' e'' : F} (hr : Raiz R e e' e'') : dd e e' e'' ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr hr.ne₁) (sub_ne_zero.mpr hr.ne₂)

theorem y_zero {e e' e'' : F} (hr : Raiz R e e' e'') {y : F}
    (h : (curva R).toAffine.Equation e y) : y = 0 := by
  rw [equacao_iff, hr.fat] at h
  simpa using h

variable [DecidableEq F]

/-- **A reta por `(e, 0)` e `Q = (x₂, y₂)`**: o terceiro ponto tem `(x₂ − e)(x₃ − e) = d_e`. -/
theorem lado_T {e e' e'' : F} (hr : Raiz R e e' e'') {x₂ y₂ : F}
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
theorem identidade_reta {e e' e'' : F} (hr : Raiz R e e' e'') {x₁ y₁ x₂ y₂ : F}
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
/-- `E(F)`. -/
abbrev Pt := (curva R).toAffine.Point

/-- `δ_e(O) = 1`, `δ_e(x, y) = x − e` (e `d_e` no ponto `(e, 0)`). -/
noncomputable def delta (e e' e'' : F) : Pt R → F
  | .zero => 1
  | .some x _ _ => if x = e then dd e e' e'' else x - e

theorem delta_zero (e e' e'' : F) : delta (R := R) e e' e'' 0 = 1 := rfl

theorem delta_some_ne {e e' e'' x y : F} (h : (curva R).toAffine.Nonsingular x y) (hx : x ≠ e) :
    delta e e' e'' (.some x y h) = x - e := by
  simp only [delta, hx, ite_false]

theorem delta_some_eq {e e' e'' y : F} (h : (curva R).toAffine.Nonsingular e y) :
    delta e e' e'' (.some e y h) = dd e e' e'' := by
  simp only [delta, ite_true]

theorem delta_ne_zero {e e' e'' : F} (hr : Raiz R e e' e'') (P : Pt R) :
    delta e e' e'' P ≠ 0 := by
  cases P with
  | zero => simp [delta]
  | some x y h =>
    simp only [delta]
    split_ifs with hx
    · exact dd_ne_zero hr
    · exact sub_ne_zero.mpr hx

variable [NeZero (2 : F)]

omit [DecidableEq F] in
theorem nonsingular_raiz {e e' e'' : F} (hr : Raiz R e e' e'') :
    (curva R).toAffine.Nonsingular e 0 :=
  (equation_iff_nonsingular).mp ((equacao_iff R e 0).mpr (by rw [hr.fat]; ring))

omit [NeZero (2 : F)] in
/-- O caso em que o primeiro ponto é `(e, y₁)` (logo `y₁ = 0`). -/
theorem caso_raiz {e e' e'' : F} (hr : Raiz R e e' e'') {y₁ x₂ y₂ : F}
    (h₁ : (curva R).toAffine.Nonsingular e y₁) (h₂ : (curva R).toAffine.Nonsingular x₂ y₂) :
    ∃ c : F, delta e e' e'' (.some e y₁ h₁ + .some x₂ y₂ h₂) * delta e e' e'' (.some e y₁ h₁) *
      delta e e' e'' (.some x₂ y₂ h₂) = c ^ 2 := by
  have hy₁ : y₁ = 0 := y_zero hr h₁.1
  subst hy₁
  by_cases hx₂ : x₂ = e
  · subst hx₂
    have hy₂ : y₂ = 0 := y_zero hr h₂.1
    subst hy₂
    rw [Point.add_of_Y_eq rfl (by rw [negY_curva]; simp)]
    exact ⟨dd x₂ e' e'', by simp [delta]; ring⟩
  · have hxy : ¬(e = x₂ ∧ (0 : F) = (curva R).toAffine.negY x₂ y₂) := fun h => hx₂ h.1.symm
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
theorem produto {e e' e'' : F} (hr : Raiz R e e' e'') (P Q : Pt R) :
    ∃ c : F, delta e e' e'' (P + Q) * delta e e' e'' P * delta e e' e'' Q = c ^ 2 := by
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
        show 1 * _ * _ = _
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
        have hxy' : ¬(e = x₂ ∧ (0 : F) = (curva R).toAffine.negY x₂
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

omit [DecidableEq F] [NeZero (2 : F)] in
variable (F) in
/-- `F*/F*²` (o mesmo tipo que `Fˣ ⧸ (powMonoidHom 2).range` da Mathlib). -/
def F2 := Fˣ ⧸ (powMonoidHom (α := Fˣ) 2).range

omit [DecidableEq F] [NeZero (2 : F)] in
noncomputable instance : CommGroup (F2 F) := QuotientGroup.Quotient.commGroup _

omit [DecidableEq F] [NeZero (2 : F)] in
/-- A projeção `Fˣ → F*/F*²`. -/
noncomputable def mk2 : Fˣ →* F2 F := QuotientGroup.mk' _

omit [DecidableEq F] [NeZero (2 : F)] in
theorem mk2_eq_one_iff (a : Fˣ) : mk2 a = 1 ↔ ∃ c : Fˣ, c ^ 2 = a := by
  show (QuotientGroup.mk' (powMonoidHom (α := Fˣ) 2).range a = 1) ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, MonoidHom.mem_range]
  simp only [powMonoidHom_apply]

omit [DecidableEq F] [NeZero (2 : F)] in
theorem mk2_surjective : Function.Surjective (mk2 (F := F)) :=
  QuotientGroup.mk'_surjective _

/-- A classe de `a ∈ F` em `F*/F*²` (`1` para `a = 0`). -/
noncomputable def cls (a : F) : F2 F :=
  if h : a = 0 then 1 else mk2 (Units.mk0 a h)

omit [NeZero (2 : F)] in
theorem cls_of_ne {a : F} (ha : a ≠ 0) : cls a = mk2 (Units.mk0 a ha) := by
  simp only [cls, ha, dite_false]

omit [NeZero (2 : F)] in
theorem cls_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) : cls (a * b) = cls a * cls b := by
  rw [cls_of_ne ha, cls_of_ne hb, cls_of_ne (mul_ne_zero ha hb), ← map_mul]
  congr 1
  ext
  simp

omit [NeZero (2 : F)] in
theorem cls_eq_one_iff {a : F} (ha : a ≠ 0) : cls a = 1 ↔ ∃ c : F, a = c ^ 2 := by
  rw [cls_of_ne ha, mk2_eq_one_iff]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨(v : F), by rw [← Units.val_pow_eq_pow_val, hv, Units.val_mk0]⟩
  · rintro ⟨c, rfl⟩
    have hc : c ≠ 0 := fun h => ha (by rw [h]; ring)
    exact ⟨Units.mk0 c hc, by ext; simp⟩

omit [NeZero (2 : F)] in
theorem cls_mul_self {a : F} (ha : a ≠ 0) : cls a * cls a = 1 := by
  rw [← cls_mul ha ha, cls_eq_one_iff (mul_ne_zero ha ha)]
  exact ⟨a, by ring⟩

/-- `φ_e(P) = [δ_e(P)] ∈ F*/F*²`. -/
noncomputable def phiE (e e' e'' : F) (P : Pt R) : F2 F := cls (delta e e' e'' P)

/-- **`φ_e` é um homomorfismo.** -/
theorem phiE_add {e e' e'' : F} (hr : Raiz R e e' e'') (P Q : Pt R) :
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

omit [DecidableEq F] [NeZero (2 : F)] in
theorem raiz₁ : Raiz R R.e₁ R.e₂ R.e₃ :=
  ⟨fun _ => rfl, rfl, R.h₁₂, R.h₁₃⟩

omit [DecidableEq F] [NeZero (2 : F)] in
theorem raiz₂ : Raiz R R.e₂ R.e₁ R.e₃ :=
  ⟨fun x => by simp only [f]; ring, by ring, R.h₁₂.symm, R.h₂₃⟩

omit [DecidableEq F] [NeZero (2 : F)] in
theorem raiz₃ : Raiz R R.e₃ R.e₁ R.e₂ :=
  ⟨fun x => by simp only [f]; ring, by ring, R.h₁₃.symm, R.h₂₃.symm⟩

variable (R) in
/-- **O homomorfismo de descida** `E(F) → (F*/F*²)²`, `P ↦ ([x − e₁], [x − e₂])`. -/
noncomputable def phi : Pt R →+ Additive (F2 F × F2 F) :=
  AddMonoidHom.mk' (fun P => Additive.ofMul (phiE R.e₁ R.e₂ R.e₃ P, phiE R.e₂ R.e₁ R.e₃ P))
    (fun P Q => by
      rw [phiE_add raiz₁, phiE_add raiz₂]
      rfl)

/-! ## O núcleo está em `2E(F)` -/

/-- **Divisão por 2**: se `x − eᵢ = rᵢ²` e `y = r₁r₂r₃`, então `(x, y) = 2Q` com
`Q = (x + r₁r₂ + r₁r₃ + r₂r₃, (r₁ + r₂)(r₁ + r₃)(r₂ + r₃))`. -/
theorem metade {x y : F} (h : (curva R).toAffine.Nonsingular x y) {r₁ r₂ r₃ : F}
    (h₁ : x - R.e₁ = r₁ ^ 2) (h₂ : x - R.e₂ = r₂ ^ 2) (h₃ : x - R.e₃ = r₃ ^ 2)
    (hy : y = r₁ * r₂ * r₃) : ∃ Q : Pt R, Q + Q = .some x y h := by
  have he₁ : R.e₁ = x - r₁ ^ 2 := by linear_combination -h₁
  have he₂ : R.e₂ = x - r₂ ^ 2 := by linear_combination -h₂
  have he₃ : R.e₃ = x - r₃ ^ 2 := by linear_combination -h₃
  have n12 : R.e₁ ≠ R.e₂ := R.h₁₂
  have n13 : R.e₁ ≠ R.e₃ := R.h₁₃
  have n23 : R.e₂ ≠ R.e₃ := R.h₂₃
  have s12 : r₁ + r₂ ≠ 0 := by
    intro hs; apply n12; rw [he₁, he₂, show r₁ = -r₂ by linear_combination hs]; ring
  have s13 : r₁ + r₃ ≠ 0 := by
    intro hs; apply n13; rw [he₁, he₃, show r₁ = -r₃ by linear_combination hs]; ring
  have s23 : r₂ + r₃ ≠ 0 := by
    intro hs; apply n23; rw [he₂, he₃, show r₂ = -r₃ by linear_combination hs]; ring
  set x₀ := x + r₁ * r₂ + r₁ * r₃ + r₂ * r₃ with hx₀
  set y₀ := (r₁ + r₂) * (r₁ + r₃) * (r₂ + r₃) with hy₀
  have hy₀0 : y₀ ≠ 0 := mul_ne_zero (mul_ne_zero s12 s13) s23
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  have heq : (curva R).toAffine.Equation x₀ y₀ := by
    rw [equacao_iff]
    simp only [f, hx₀, hy₀, he₁, he₂, he₃]
    ring
  have hns : (curva R).toAffine.Nonsingular x₀ y₀ := equation_iff_nonsingular.mp heq
  have hne : y₀ ≠ (curva R).toAffine.negY x₀ y₀ := by
    rw [negY_curva]
    intro h'
    exact hy₀0 (by
      have : 2 * y₀ = 0 := by linear_combination h'
      rcases mul_eq_zero.mp this with h'' | h''
      · exact absurd h'' h2
      · exact h'')
  have h2y : y₀ - (curva R).toAffine.negY x₀ y₀ ≠ 0 := sub_ne_zero.mpr hne
  have hℓ : (curva R).toAffine.slope x₀ x₀ y₀ y₀ = r₁ + r₂ + r₃ := by
    rw [slope_of_Y_ne rfl hne, div_eq_iff h2y]
    rw [negY_curva]
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

/-- **O núcleo de `φ` está em `2E(F)`.** -/
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
    have n12 : R.e₁ ≠ R.e₂ := R.h₁₂
    have n13 : R.e₁ ≠ R.e₃ := R.h₁₃
    have n23 : R.e₂ ≠ R.e₃ := R.h₂₃
    have heq := (equacao_iff R x y).mp h.1
    simp only [f] at heq
    by_cases hx₁ : x = R.e₁
    · subst hx₁
      have hy : y = 0 := y_zero raiz₁ h.1
      rw [delta_some_eq, dd] at hc₁
      rw [delta_some_ne h n12] at hc₂
      have hc₂0 : c₂ ≠ 0 := by
        rintro rfl; apply n12; linear_combination hc₂
      refine metade h (r₁ := 0) (r₂ := c₂) (r₃ := c₁ / c₂) (by ring) hc₂ ?_ (by rw [hy]; ring)
      field_simp
      linear_combination hc₁ - (R.e₁ - R.e₃) * hc₂
    by_cases hx₂ : x = R.e₂
    · subst hx₂
      have hy : y = 0 := y_zero raiz₂ h.1
      rw [delta_some_ne h (Ne.symm n12)] at hc₁
      rw [delta_some_eq, dd] at hc₂
      have hc₁0 : c₁ ≠ 0 := by
        rintro rfl; apply n12; linear_combination -hc₁
      refine metade h (r₁ := c₁) (r₂ := 0) (r₃ := c₂ / c₁) hc₁ (by ring) ?_ (by rw [hy]; ring)
      field_simp
      linear_combination hc₂ - (R.e₂ - R.e₃) * hc₁
    rw [delta_some_ne h hx₁] at hc₁
    rw [delta_some_ne h hx₂] at hc₂
    by_cases hx₃ : x = R.e₃
    · subst hx₃
      have hy : y = 0 := y_zero raiz₃ h.1
      exact metade h (r₁ := c₁) (r₂ := c₂) (r₃ := 0) hc₁ hc₂ (by ring) (by rw [hy]; ring)
    · have hc₁0 : c₁ ≠ 0 := by
        rintro rfl; apply hx₁; linear_combination hc₁
      have hc₂0 : c₂ ≠ 0 := by
        rintro rfl; apply hx₂; linear_combination hc₂
      refine metade h (r₁ := c₁) (r₂ := c₂) (r₃ := y / (c₁ * c₂)) hc₁ hc₂ ?_ (by field_simp)
      field_simp
      rw [hc₁, hc₂] at heq
      linear_combination -heq

/-- **Critério**: se a imagem de `φ` é finita, `2E(F)` tem índice finito em `E(F)`. -/
theorem fraco_de_finito (h : (Set.range (phi R)).Finite) :
    (nsmulAddMonoidHom (α := Pt R) 2).range.FiniteIndex := by
  have : Finite (phi R).range := by
    rw [← AddMonoidHom.coe_range] at h
    exact h.to_subtype
  exact AddSubgroup.finiteIndex_of_le nucleo_le

/-! ## A 2-torção -/

/-- **Os pontos de 2-torção** são `O` e os `(eᵢ, 0)`. -/
theorem dois_torcao {P : Pt R} (hP : P + P = 0) :
    P = 0 ∨ ∃ (x y : F) (h : (curva R).toAffine.Nonsingular x y), P = .some x y h ∧
      y = 0 ∧ (x = R.e₁ ∨ x = R.e₂ ∨ x = R.e₃) := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y h =>
    right
    have hneg : Point.some x y h = -Point.some x y h := add_eq_zero_iff_eq_neg.mp hP
    rw [Point.neg_some] at hneg
    simp only [Point.some.injEq, negY_curva] at hneg
    have hy : y = 0 := by
      have h2 : (2 : F) ≠ 0 := NeZero.ne 2
      have : 2 * y = 0 := by linear_combination hneg.2
      rcases mul_eq_zero.mp this with h'' | h''
      · exact absurd h'' h2
      · exact h''
    refine ⟨x, y, h, rfl, hy, ?_⟩
    have heq := (equacao_iff R x y).mp h.1
    rw [hy, f] at heq
    have : (x - R.e₁) * (x - R.e₂) * (x - R.e₃) = 0 := by linear_combination -heq
    rcases mul_eq_zero.mp this with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · exact Or.inl (sub_eq_zero.mp h1)
      · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h3))

/-- **`E(F)[2]` é finito.** -/
theorem finito_dois_torcao : {P : Pt R | P + P = 0}.Finite := by
  classical
  let g : Option (Fin 3) → Pt R := fun o => match o with
    | none => 0
    | some i =>
      if hi : (curva R).toAffine.Nonsingular (![R.e₁, R.e₂, R.e₃] i) 0 then
        .some _ _ hi else 0
  refine (Set.finite_range g).subset ?_
  intro P hP
  rcases dois_torcao hP with h0 | ⟨x, y, h, rfl, rfl, hx⟩
  · exact ⟨none, h0.symm⟩
  · rcases hx with rfl | rfl | rfl
    · exact ⟨some 0, by simp [g, h]⟩
    · exact ⟨some 1, by simp [g, h]⟩
    · exact ⟨some 2, by simp [g, h]⟩

end ATK.MordellWeilCorpo

#print axioms ATK.MordellWeilCorpo.equacao_iff
#print axioms ATK.MordellWeilCorpo.delta_curva
#print axioms ATK.MordellWeilCorpo.negY_curva
#print axioms ATK.MordellWeilCorpo.dd_ne_zero
#print axioms ATK.MordellWeilCorpo.y_zero
#print axioms ATK.MordellWeilCorpo.lado_T
#print axioms ATK.MordellWeilCorpo.identidade_reta
#print axioms ATK.MordellWeilCorpo.delta_zero
#print axioms ATK.MordellWeilCorpo.delta_some_ne
#print axioms ATK.MordellWeilCorpo.delta_some_eq
#print axioms ATK.MordellWeilCorpo.delta_ne_zero
#print axioms ATK.MordellWeilCorpo.nonsingular_raiz
#print axioms ATK.MordellWeilCorpo.caso_raiz
#print axioms ATK.MordellWeilCorpo.produto
#print axioms ATK.MordellWeilCorpo.mk2_eq_one_iff
#print axioms ATK.MordellWeilCorpo.mk2_surjective
#print axioms ATK.MordellWeilCorpo.cls_of_ne
#print axioms ATK.MordellWeilCorpo.cls_mul
#print axioms ATK.MordellWeilCorpo.cls_eq_one_iff
#print axioms ATK.MordellWeilCorpo.cls_mul_self
#print axioms ATK.MordellWeilCorpo.phiE_add
#print axioms ATK.MordellWeilCorpo.raiz₁
#print axioms ATK.MordellWeilCorpo.raiz₂
#print axioms ATK.MordellWeilCorpo.raiz₃
#print axioms ATK.MordellWeilCorpo.metade
#print axioms ATK.MordellWeilCorpo.phi_eq_zero_iff
#print axioms ATK.MordellWeilCorpo.nucleo_le
#print axioms ATK.MordellWeilCorpo.fraco_de_finito
#print axioms ATK.MordellWeilCorpo.dois_torcao
#print axioms ATK.MordellWeilCorpo.finito_dois_torcao
