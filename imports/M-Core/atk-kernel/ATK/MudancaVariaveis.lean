import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# ATK — Completar o quadrado: `E(ℚ) ≅ E'(ℚ)` com `E' : y² = x³ + a₂'x² + a₄'x + a₆'`

Para `W : y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` sobre `ℚ`, a mudança de variáveis
`(x, y) ↦ (x, y + (a₁x + a₃)/2)` leva `W` em

  `normal W : y² = x³ + (a₂ + a₁²/4)x² + (a₄ + a₁a₃/2)x + (a₆ + a₃²/4)`

(`a₁ = a₃ = 0`), com o mesmo discriminante (`delta_normal`). Este arquivo prova que ela é um
**isomorfismo de grupos** entre os pontos racionais (`mudarEquiv`): a inclinação muda por `a₁/2`
(`slope_normal`), e `addX`, `addY` correspondem. Consequência: `E(ℚ)/2E(ℚ)` é finito se
`E'(ℚ)/2E'(ℚ)` o é (`fraco_de_normal`).
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace ATK.MudancaVariaveis

variable (W : WeierstrassCurve ℚ)

/-- A forma `a₁ = a₃ = 0` de `W` (completando o quadrado em `y`). -/
def normal : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := W.a₂ + W.a₁ ^ 2 / 4
  a₃ := 0
  a₄ := W.a₄ + W.a₁ * W.a₃ / 2
  a₆ := W.a₆ + W.a₃ ^ 2 / 4

theorem delta_normal : (normal W).Δ = W.Δ := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, normal]
  ring

instance eliptica_normal [W.IsElliptic] : (normal W).IsElliptic :=
  ⟨by rw [delta_normal]; exact W.isUnit_Δ⟩

/-- `y' = y + (a₁x + a₃)/2`. -/
def yN (x y : ℚ) : ℚ := y + (W.a₁ * x + W.a₃) / 2

theorem equation_normal (x y : ℚ) :
    (normal W).toAffine.Equation x (yN W x y) ↔ W.toAffine.Equation x y := by
  rw [Affine.equation_iff, Affine.equation_iff]
  simp only [normal, yN]
  constructor <;> intro h <;> linear_combination h

theorem negY_normal (x y : ℚ) : (normal W).toAffine.negY x y = -y := by
  simp [Affine.negY, normal]

theorem yN_negY (x y : ℚ) : yN W x (W.toAffine.negY x y) = -yN W x y := by
  simp only [yN, Affine.negY]
  ring

theorem yN_inj {x y y' : ℚ} (h : yN W x y = yN W x y') : y = y' := by
  simp only [yN] at h
  linarith

variable [W.IsElliptic]

theorem nonsingular_normal {x y : ℚ} (h : W.toAffine.Nonsingular x y) :
    (normal W).toAffine.Nonsingular x (yN W x y) :=
  equation_iff_nonsingular.mp ((equation_normal W x y).mpr (equation_iff_nonsingular.mpr h))

/-- **A mudança de variáveis** nos pontos. -/
def mudar : W.toAffine.Point → (normal W).toAffine.Point
  | .zero => .zero
  | .some x y h => .some x (yN W x y) (nonsingular_normal W h)

theorem mudar_zero : mudar W 0 = 0 := rfl

theorem mudar_some {x y : ℚ} (h : W.toAffine.Nonsingular x y) :
    mudar W (.some x y h) = .some x (yN W x y) (nonsingular_normal W h) := rfl

/-- **A inclinação muda por `a₁/2`.** -/
theorem slope_normal {x₁ x₂ y₁ y₂ : ℚ} (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (normal W).toAffine.slope x₁ x₂ (yN W x₁ y₁) (yN W x₂ y₂) =
      W.toAffine.slope x₁ x₂ y₁ y₂ + W.a₁ / 2 := by
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ W.toAffine.negY x₁ y₂ := fun h => hxy ⟨rfl, h⟩
    have h12 : y₁ = y₂ := Y_eq_of_Y_ne h₁ h₂ rfl hy
    subst h12
    have hy' : yN W x₁ y₁ ≠ (normal W).toAffine.negY x₁ (yN W x₁ y₁) := by
      rw [negY_normal, ← yN_negY]
      exact fun h => hy (yN_inj W h)
    rw [slope_of_Y_ne rfl hy, slope_of_Y_ne rfl hy', negY_normal]
    have hD : y₁ - W.toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    have hD' : yN W x₁ y₁ - -yN W x₁ y₁ ≠ 0 := by
      have : yN W x₁ y₁ - -yN W x₁ y₁ = y₁ - W.toAffine.negY x₁ y₁ := by
        simp only [yN, Affine.negY]; ring
      rw [this]; exact hD
    have hE : yN W x₁ y₁ - -yN W x₁ y₁ = y₁ - W.toAffine.negY x₁ y₁ := by
      simp only [yN, Affine.negY]; ring
    rw [hE, div_add' _ _ _ hD, div_left_inj' hD]
    simp only [yN, normal, Affine.negY]
    ring
  · rw [slope_of_X_ne hx, slope_of_X_ne hx]
    have hx' : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    rw [div_add' _ _ _ hx', div_left_inj' hx']
    simp only [yN]
    ring

theorem addX_normal (x₁ x₂ ℓ : ℚ) :
    (normal W).toAffine.addX x₁ x₂ (ℓ + W.a₁ / 2) = W.toAffine.addX x₁ x₂ ℓ := by
  simp only [Affine.addX, normal]
  ring

theorem addY_normal (x₁ x₂ y₁ ℓ : ℚ) :
    (normal W).toAffine.addY x₁ x₂ (yN W x₁ y₁) (ℓ + W.a₁ / 2) =
      yN W (W.toAffine.addX x₁ x₂ ℓ) (W.toAffine.addY x₁ x₂ y₁ ℓ) := by
  simp only [Affine.addY, Affine.negAddY, Affine.negY, Affine.addX, normal, yN]
  ring

/-- **A mudança de variáveis é aditiva.** -/
theorem mudar_add (P Q : W.toAffine.Point) : mudar W (P + Q) = mudar W P + mudar W Q := by
  cases P with
  | zero =>
    show mudar W (0 + Q) = 0 + mudar W Q
    rw [zero_add, zero_add]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      show mudar W (.some x₁ y₁ h₁ + 0) = mudar W (.some x₁ y₁ h₁) + 0
      rw [add_zero, add_zero]
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
      · have hxy' : x₁ = x₂ ∧ yN W x₁ y₁ = (normal W).toAffine.negY x₂ (yN W x₂ y₂) := by
          refine ⟨hxy.1, ?_⟩
          rw [negY_normal, ← yN_negY, hxy.1, hxy.2]
        rw [Point.add_of_Y_eq hxy.1 hxy.2, mudar_some, mudar_some,
          Point.add_of_Y_eq hxy'.1 hxy'.2]
        rfl
      · have hxy' : ¬(x₁ = x₂ ∧ yN W x₁ y₁ = (normal W).toAffine.negY x₂ (yN W x₂ y₂)) := by
          rintro ⟨hx, hy⟩
          subst hx
          apply hxy
          refine ⟨rfl, yN_inj W (x := x₁) ?_⟩
          rw [hy, negY_normal, yN_negY]
        rw [Point.add_some hxy, mudar_some, mudar_some, mudar_some, Point.add_some hxy']
        simp only [Point.some.injEq]
        rw [slope_normal W h₁.1 h₂.1 hxy, addX_normal, addY_normal]
        exact ⟨rfl, rfl⟩

/-- O homomorfismo `E(ℚ) → E'(ℚ)`. -/
def mudarHom : W.toAffine.Point →+ (normal W).toAffine.Point :=
  AddMonoidHom.mk' (mudar W) (mudar_add W)

theorem mudar_injective : Function.Injective (mudar W) := by
  intro P Q h
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y hQ => exact absurd h (by simp [mudar])
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => exact absurd h (by simp [mudar])
    | some x₂ y₂ h₂ =>
      rw [mudar_some, mudar_some, Point.some.injEq] at h
      obtain ⟨hx, hy⟩ := h
      subst hx
      have := yN_inj W hy
      subst this
      rfl

theorem mudar_surjective : Function.Surjective (mudar W) := by
  intro P'
  cases P' with
  | zero => exact ⟨0, rfl⟩
  | some x y' h =>
    have hy : yN W x (y' - (W.a₁ * x + W.a₃) / 2) = y' := by simp only [yN]; ring
    have heq : W.toAffine.Equation x (y' - (W.a₁ * x + W.a₃) / 2) := by
      rw [← equation_normal, hy]
      exact h.1
    refine ⟨.some x _ (equation_iff_nonsingular.mp heq), ?_⟩
    rw [mudar_some, Point.some.injEq]
    exact ⟨rfl, hy⟩

/-- **`E(ℚ) ≃ E'(ℚ)`** como grupos. -/
noncomputable def mudarEquiv : W.toAffine.Point ≃+ (normal W).toAffine.Point :=
  AddEquiv.ofBijective (mudarHom W) ⟨mudar_injective W, mudar_surjective W⟩

/-- **`E(ℚ)/2E(ℚ)` é finito se `E'(ℚ)/2E'(ℚ)` o é.** -/
theorem fraco_de_normal
    (h : (nsmulAddMonoidHom (α := (normal W).toAffine.Point) 2).range.FiniteIndex) :
    (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range.FiniteIndex := by
  have hc : (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range =
      (nsmulAddMonoidHom (α := (normal W).toAffine.Point) 2).range.comap
        (mudarEquiv W).toAddMonoidHom := by
    ext P
    simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, AddSubgroup.mem_comap,
      AddEquiv.coe_toAddMonoidHom]
    constructor
    · rintro ⟨Q, rfl⟩
      exact ⟨mudarEquiv W Q, (map_nsmul (mudarEquiv W) 2 Q).symm⟩
    · rintro ⟨Q', hQ'⟩
      refine ⟨(mudarEquiv W).symm Q', (mudarEquiv W).injective ?_⟩
      rw [map_nsmul, AddEquiv.apply_symm_apply, hQ']
  refine ⟨?_⟩
  rw [hc, AddSubgroup.index_comap_of_surjective _ (f := (mudarEquiv W).toAddMonoidHom)
    (mudarEquiv W).surjective]
  exact h.index_ne_zero

end ATK.MudancaVariaveis

#print axioms ATK.MudancaVariaveis.delta_normal
#print axioms ATK.MudancaVariaveis.equation_normal
#print axioms ATK.MudancaVariaveis.negY_normal
#print axioms ATK.MudancaVariaveis.yN_negY
#print axioms ATK.MudancaVariaveis.yN_inj
#print axioms ATK.MudancaVariaveis.nonsingular_normal
#print axioms ATK.MudancaVariaveis.mudar_zero
#print axioms ATK.MudancaVariaveis.mudar_some
#print axioms ATK.MudancaVariaveis.slope_normal
#print axioms ATK.MudancaVariaveis.addX_normal
#print axioms ATK.MudancaVariaveis.addY_normal
#print axioms ATK.MudancaVariaveis.mudar_add
#print axioms ATK.MudancaVariaveis.mudar_injective
#print axioms ATK.MudancaVariaveis.mudar_surjective
#print axioms ATK.MudancaVariaveis.fraco_de_normal
