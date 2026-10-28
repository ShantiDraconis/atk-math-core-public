import ATK.BSDTamagawaE32
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# O fator de Euler de `y² = x³ − x` nos primos supersingulares, na função L da Mathlib

`WeierstrassCurve.localPolynomial` (Mathlib) é `1 − a T + q T²` com `a = q + 1 − #W̄(κ)`, onde
`W̄` é a redução do **modelo minimal** escolhido pela Mathlib e `q = #κ`. Aqui:

1. **Contagem em corpo finito** (`card_pontos`): sobre todo corpo finito `F` com `|F| ≡ 3 (mod 4)`,
   a curva `y² = x³ − x` tem `|F| + 1` pontos (`Σ_x χ(x³ − x) = 0`, pois `χ(−1) = −1`).
2. **Invariância por mudança de variáveis** (`card_pontos_mudanca`): `#(C • W)(F) = #W(F)`, pela
   bijeção `(x, y) ↦ (u²x + r, u³y + u²sx + t)` (`equacao_mudanca`).
3. **Modelo minimal** (`reducao_minimal`): se `W` é integral com `Δ` unidade e o modelo minimal tem
   redução boa, a redução do modelo minimal é `C̄ • W̄` para alguma mudança `C̄` sobre `κ` (o `u`
   da mudança é unidade de `R`: raiz de `X¹² − w`, `R` integralmente fechado).
4. **O fator de Euler** (`polinomioLocal_E32`): para todo primo `v ∤ 2` com `#κ_v ≡ 3 (mod 4)`,
   `localPolynomial = 1 + q T²`, isto é, `a_v = 0`, na função `L` da própria Mathlib.

Não toca O6/O7 em geral: é o fator local da função `L` desta curva nesses primos.
-/

open Finset Polynomial WeierstrassCurve IsDedekindDomain NumberField

namespace ATK.BSDEulerE32

/-! ## 1. Contagem em corpo finito -/

section Finito

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem car_ne_dois (h3 : Fintype.card F % 4 = 3) : ringChar F ≠ 2 := fun h => by
  have := FiniteField.even_card_of_char_two h
  omega

theorem chi_menos_um (h3 : Fintype.card F % 4 = 3) : quadraticChar F (-1) = -1 := by
  rw [quadraticChar_neg_one (car_ne_dois h3)]
  exact ZMod.χ₄_nat_three_mod_four h3

theorem soma_chi_zero (h3 : Fintype.card F % 4 = 3) :
    ∑ x : F, quadraticChar F (x ^ 3 - x) = 0 := by
  have hterm : ∀ x : F, quadraticChar F ((-x) ^ 3 - -x) = -quadraticChar F (x ^ 3 - x) := by
    intro x
    have : (-x) ^ 3 - -x = (-1) * (x ^ 3 - x) := by ring
    rw [this, map_mul, chi_menos_um h3, neg_one_mul]
  have h1 : ∑ x : F, quadraticChar F (x ^ 3 - x) = ∑ x : F, quadraticChar F ((-x) ^ 3 - -x) :=
    Fintype.sum_equiv (Equiv.neg F) _ _ (fun x => by simp only [Equiv.neg_apply, neg_neg])
  rw [Finset.sum_congr rfl (fun x _ => hterm x), Finset.sum_neg_distrib] at h1
  linarith

theorem card_raizes (h3 : Fintype.card F % 4 = 3) (x : F) :
    ((univ.filter (fun y : F => y ^ 2 = x ^ 3 - x)).card : ℤ) = quadraticChar F (x ^ 3 - x) + 1 := by
  rw [← quadraticChar_card_sqrts (car_ne_dois h3) (x ^ 3 - x)]
  congr 2
  ext y
  simp

/-- `#{(x, y) ∈ F² : y² = x³ − x} = |F|` para `|F| ≡ 3 (mod 4)`. -/
theorem card_afim (h3 : Fintype.card F % 4 = 3) :
    ((univ.filter (fun xy : F × F => xy.2 ^ 2 = xy.1 ^ 3 - xy.1)).card : ℤ) = Fintype.card F := by
  have hprod : (univ.filter (fun xy : F × F => xy.2 ^ 2 = xy.1 ^ 3 - xy.1)).card =
      ∑ x : F, (univ.filter (fun y : F => y ^ 2 = x ^ 3 - x)).card := by
    rw [Finset.card_filter, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun x _ => (Finset.card_filter _ _).symm)
  rw [hprod]
  push_cast
  rw [Finset.sum_congr rfl (fun x _ => card_raizes h3 x), Finset.sum_add_distrib, soma_chi_zero h3]
  simp

/-- **`#W(F) = |F| + 1`** para toda curva `y² = x³ − x` (coeficientes `0, 0, 0, −1, 0`) sobre `F`
com `|F| ≡ 3 (mod 4)`. -/
theorem card_pontos (W : WeierstrassCurve F) [W.IsElliptic]
    (h1 : W.a₁ = 0) (h2 : W.a₂ = 0) (h3' : W.a₃ = 0) (h4 : W.a₄ = -1) (h6 : W.a₆ = 0)
    (h3 : Fintype.card F % 4 = 3) : Nat.card W.toAffine.Point = Fintype.card F + 1 := by
  have hS : {xy : F × F // W.toAffine.Equation xy.1 xy.2} ≃
      (univ.filter (fun xy : F × F => xy.2 ^ 2 = xy.1 ^ 3 - xy.1)) :=
    Equiv.subtypeEquivRight (fun xy => by
      rw [Finset.mem_filter, Affine.equation_iff, h1, h2, h3', h4, h6]
      simp only [mem_univ, true_and]
      constructor <;> intro h <;> linear_combination h)
  have hc : Nat.card W.toAffine.Point =
      Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} + 1 := by
    rw [Nat.card_congr (Affine.pointEquiv W.toAffine)]
    first
    | exact Finite.card_option
    | exact Nat.card_option
  rw [hc, Nat.card_congr hS, Nat.card_eq_fintype_card, Fintype.card_coe]
  have := card_afim (F := F) h3
  omega

end Finito

/-! ## 2. Mudança de variáveis preserva a contagem -/

section Mudanca

variable {F : Type*} [Field F]

/-- `(C • W)(x, y) = 0 ⟺ W(u²x + r, u³y + u²sx + t) = 0`. -/
theorem equacao_mudanca (W : WeierstrassCurve F) (C : VariableChange F) (x y : F) :
    (C • W).toAffine.Equation x y ↔
      W.toAffine.Equation (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rw [Affine.equation_iff', Affine.equation_iff', variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]
  have key : ∀ a b : F, a = (C.u : F) ^ 6 * b → (b = 0 ↔ a = 0) := fun a b h => by
    rw [h, mul_eq_zero]
    simp [hu]
  apply key
  first
  | (field_simp; ring)
  | field_simp
  | ring

/-- A bijeção afim `(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
noncomputable def cambio (C : VariableChange F) : F × F ≃ F × F where
  toFun p := (C.u ^ 2 * p.1 + C.r, C.u ^ 3 * p.2 + C.u ^ 2 * C.s * p.1 + C.t)
  invFun q := ((q.1 - C.r) / C.u ^ 2, (q.2 - C.s * (q.1 - C.r) - C.t) / C.u ^ 3)
  left_inv p := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    refine Prod.ext ?_ ?_ <;> dsimp only <;>
      first
      | (field_simp; ring)
      | field_simp
      | ring
  right_inv q := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    refine Prod.ext ?_ ?_ <;> dsimp only <;>
      first
      | (field_simp; ring)
      | field_simp
      | ring

/-- **`#(C • W)(F) = #W(F)`**. -/
theorem card_pontos_mudanca (W : WeierstrassCurve F) [W.IsElliptic] (C : VariableChange F) :
    Nat.card (C • W).toAffine.Point = Nat.card W.toAffine.Point := by
  have e : {xy : F × F // (C • W).toAffine.Equation xy.1 xy.2} ≃
      {xy : F × F // W.toAffine.Equation xy.1 xy.2} :=
    (cambio C).subtypeEquiv (fun p => equacao_mudanca W C p.1 p.2)
  exact Nat.card_congr ((Affine.pointEquiv (C • W).toAffine).trans
    (e.optionCongr.trans (Affine.pointEquiv W.toAffine).symm))

end Mudanca

/-! ## 3. A redução do modelo minimal -/

section Minimal

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Se o modelo integral de `W` tem `Δ` unidade e o modelo minimal tem redução boa, a redução do
modelo minimal é `C̄ • W̄` para alguma mudança de variáveis `C̄` sobre o corpo residual. -/
theorem reducao_minimal (W : WeierstrassCurve K) [IsIntegral R W]
    (hΔ : IsUnit (integralModel R W).Δ) (hgood : (W.minimal R).HasGoodReduction R) :
    ∃ C : VariableChange (IsLocalRing.ResidueField R),
      (W.minimal R).reduction R = C • (integralModel R W).map (IsLocalRing.residue R) := by
  set CK := (W.exists_isMinimal R).choose with hCK
  have hmin : W.minimal R = CK • W := rfl
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  -- o Δ do modelo minimal é unidade de `R`
  have hΔ' : IsUnit (integralModel R (W.minimal R)).Δ := by
    have h := hgood.goodReduction
    rw [← integralModel_Δ_eq R (W.minimal R), HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff] at h
    exact IsLocalRing.notMem_maximalIdeal.mp h
  -- `u¹² = w` com `w = Δ(W)/Δ(W_min)` unidade de `R`
  have e1 := integralModel_Δ_eq R W
  have e2 := integralModel_Δ_eq R (W.minimal R)
  have hΔK : (W.minimal R).Δ = ((CK.u⁻¹ : Kˣ) : K) ^ 12 * W.Δ := by
    rw [hmin, variableChange_Δ]
  set a : K := ((CK.u : Kˣ) : K) with ha
  set ai : K := ((CK.u⁻¹ : Kˣ) : K) with hai
  have haai : a * ai = 1 := Units.mul_inv CK.u
  have h2' : (a * ai) ^ 12 = 1 := by rw [haai, one_pow]
  set w : Rˣ := hΔ.unit * hΔ'.unit⁻¹ with hw
  have hM : algebraMap R K (integralModel R (W.minimal R)).Δ =
      ai ^ 12 * algebraMap R K (integralModel R W).Δ := by
    rw [e2, hΔK, e1]
  have hinvM : algebraMap R K ((hΔ'.unit⁻¹ : Rˣ) : R) *
      algebraMap R K (integralModel R (W.minimal R)).Δ = 1 := by
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  have h1 : algebraMap R K ((hΔ'.unit⁻¹ : Rˣ) : R) *
      (ai ^ 12 * algebraMap R K (integralModel R W).Δ) = 1 := by
    rw [← hM]; exact hinvM
  have hu12 : a ^ 12 = algebraMap R K (w : R) := by
    rw [hw, Units.val_mul, map_mul, IsUnit.unit_spec]
    linear_combination (-(a ^ 12)) * h1 +
      (algebraMap R K (integralModel R W).Δ * algebraMap R K ((hΔ'.unit⁻¹ : Rˣ) : R)) * h2'
  have hw1 : algebraMap R K ((w⁻¹ : Rˣ) : R) * algebraMap R K (w : R) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hai12 : ai ^ 12 = algebraMap R K ((w⁻¹ : Rˣ) : R) := by
    linear_combination (algebraMap R K ((w⁻¹ : Rˣ) : R)) * h2' -
      ai ^ 12 * algebraMap R K ((w⁻¹ : Rˣ) : R) * hu12 - ai ^ 12 * hw1
  -- `u` e `u⁻¹` são inteiros sobre `R` (raízes de `X¹² − w`, `X¹² − w⁻¹`)
  obtain ⟨aR, haR⟩ : ∃ y : R, algebraMap R K y = a :=
    IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 12 - C (w : R), monic_X_pow_sub_C _ (by norm_num),
      by simp [hu12]⟩
  obtain ⟨bR, hbR⟩ : ∃ y : R, algebraMap R K y = ai :=
    IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 12 - C ((w⁻¹ : Rˣ) : R),
      monic_X_pow_sub_C _ (by norm_num), by simp [hai12]⟩
  let uR : Rˣ := ⟨aR, bR, hinj (by rw [map_mul, haR, hbR, haai, map_one]),
    hinj (by rw [map_mul, haR, hbR, mul_comm, haai, map_one])⟩
  have huR : algebraMap R K (uR : R) = ((CK.u : Kˣ) : K) := haR
  obtain ⟨CR, hCR⟩ := variableChange_integral_of_u_integral (R := R) hmin.symm huR
  -- o modelo integral do minimal é `CR • W_R`
  have hmodel : integralModel R (W.minimal R) = CR • integralModel R W := by
    refine WeierstrassCurve.map_injective hinj ?_
    show (integralModel R (W.minimal R)).map (algebraMap R K) =
      (CR • integralModel R W).map (algebraMap R K)
    rw [← map_variableChange]
    show (integralModel R (W.minimal R))⁄K = (CR.baseChange K) • (integralModel R W)⁄K
    rw [baseChange_integralModel_eq R (W.minimal R), baseChange_integralModel_eq R W, hCR]
    exact hmin
  refine ⟨CR.map (IsLocalRing.residue R), ?_⟩
  show (integralModel R (W.minimal R)).map (IsLocalRing.residue R) = _
  rw [hmodel, map_variableChange]

end Minimal

/-! ## 4. O fator de Euler de `y² = x³ − x` nos primos `≡ 3 (mod 4)` -/

section E32

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- **`localPolynomial = 1 + q T²`** (isto é, `a_v = 0`) para `y² = x³ − x` em todo primo `v ∤ 2`
com `q = #κ_v ≡ 3 (mod 4)`, na função `L` da Mathlib (`WeierstrassCurve.LFunction`). -/
theorem polinomioLocal_E32 (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal)
    (h3 : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) % 4 = 3) :
    (ATK.L4Base.E32.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
      1 + C (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) : ℤ) * X ^ 2 := by
  classical
  set R := v.adicCompletionIntegers ℚ with hRdef
  set W := ATK.L4Base.E32.baseChange (v.adicCompletion ℚ) with hWdef
  have hinj : Function.Injective (algebraMap R (v.adicCompletion ℚ)) :=
    IsFractionRing.injective R (v.adicCompletion ℚ)
  have hint : IsIntegral R W := by
    apply isIntegral_of_exists_lift
    · exact ⟨0, by simp [hWdef, ATK.L4Base.E32, ATK.CongruentCurve.E]⟩
    · exact ⟨0, by simp [hWdef, ATK.L4Base.E32, ATK.CongruentCurve.E]⟩
    · exact ⟨0, by simp [hWdef, ATK.L4Base.E32, ATK.CongruentCurve.E]⟩
    · exact ⟨-1, by simp [hWdef, ATK.L4Base.E32, ATK.CongruentCurve.E]⟩
    · exact ⟨0, by simp [hWdef, ATK.L4Base.E32, ATK.CongruentCurve.E]⟩
  have ha1 : (integralModel R W).a₁ = 0 := hinj (by
    rw [integralModel_a₁_eq, map_zero]; simp [hWdef, ATK.L4Base.E32, ATK.CongruentCurve.E])
  have ha2 : (integralModel R W).a₂ = 0 := hinj (by
    rw [integralModel_a₂_eq, map_zero]; simp [hWdef, ATK.L4Base.E32, ATK.CongruentCurve.E])
  have ha3 : (integralModel R W).a₃ = 0 := hinj (by
    rw [integralModel_a₃_eq, map_zero]; simp [hWdef, ATK.L4Base.E32, ATK.CongruentCurve.E])
  have ha4 : (integralModel R W).a₄ = -1 := hinj (by
    rw [integralModel_a₄_eq, map_neg, map_one]; simp [hWdef, ATK.L4Base.E32, ATK.CongruentCurve.E])
  have ha6 : (integralModel R W).a₆ = 0 := hinj (by
    rw [integralModel_a₆_eq, map_zero]; simp [hWdef, ATK.L4Base.E32, ATK.CongruentCurve.E])
  have hΔR : (integralModel R W).Δ = 2 ^ 6 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, ha1, ha2, ha3, ha4, ha6]
    norm_num
  have hunit : IsUnit (integralModel R W).Δ := by
    rw [hΔR]
    exact (ATK.BSDTamagawaE32.dois_unidade v h2).pow 6
  -- a curva reduzida `W̄ : y² = x³ − x` sobre `κ_v`
  set Wb := (integralModel R W).map (IsLocalRing.residue R) with hWb
  haveI : Wb.IsElliptic := ⟨by
    show IsUnit (IsLocalRing.residue R (integralModel R W).Δ)
    exact hunit.map _⟩
  have hb1 : Wb.a₁ = 0 := by show IsLocalRing.residue R _ = 0; rw [ha1, map_zero]
  have hb2 : Wb.a₂ = 0 := by show IsLocalRing.residue R _ = 0; rw [ha2, map_zero]
  have hb3 : Wb.a₃ = 0 := by show IsLocalRing.residue R _ = 0; rw [ha3, map_zero]
  have hb4 : Wb.a₄ = -1 := by show IsLocalRing.residue R _ = -1; rw [ha4, map_neg, map_one]
  have hb6 : Wb.a₆ = 0 := by show IsLocalRing.residue R _ = 0; rw [ha6, map_zero]
  haveI : Finite (IsLocalRing.ResidueField R) := Nat.finite_of_card_ne_zero (by omega)
  letI : Fintype (IsLocalRing.ResidueField R) := Fintype.ofFinite _
  have h3F : Fintype.card (IsLocalRing.ResidueField R) % 4 = 3 := by
    rw [← Nat.card_eq_fintype_card]; exact h3
  obtain ⟨Cb, hCb⟩ := reducao_minimal R W hunit (ATK.BSDTamagawaE32.boa_E32 v h2)
  have hcard : (Nat.card ((W.minimal R).reduction R).toAffine.Point : ℤ) =
      (Nat.card (IsLocalRing.ResidueField R) : ℤ) + 1 := by
    rw [hCb, card_pontos_mudanca, card_pontos Wb hb1 hb2 hb3 hb4 hb6 h3F, Nat.card_eq_fintype_card]
    push_cast
    ring
  unfold localPolynomial
  rw [if_pos (ATK.BSDTamagawaE32.boa_E32 v h2), hcard, sub_self, map_zero, zero_mul, sub_zero]

end E32

end ATK.BSDEulerE32

#print axioms ATK.BSDEulerE32.car_ne_dois
#print axioms ATK.BSDEulerE32.chi_menos_um
#print axioms ATK.BSDEulerE32.soma_chi_zero
#print axioms ATK.BSDEulerE32.card_raizes
#print axioms ATK.BSDEulerE32.card_afim
#print axioms ATK.BSDEulerE32.card_pontos
#print axioms ATK.BSDEulerE32.equacao_mudanca
#print axioms ATK.BSDEulerE32.card_pontos_mudanca
#print axioms ATK.BSDEulerE32.reducao_minimal
#print axioms ATK.BSDEulerE32.polinomioLocal_E32
