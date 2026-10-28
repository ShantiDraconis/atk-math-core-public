import ATK.PonteCoefCurva32
import ATK.BSDTamagawaE32
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# ATK — Ponte P2a provada: os fatores locais de `L(E, s)` para `y² = x³ − x`

`PonteCoefCurva32` reduziu a cota `|aₙ| ≤ n` (ponte P2) à ponte **definicional** P2a
(`FatoresPadrao`): os coeficientes de `WeierstrassCurve.LFunction` da Mathlib são os padrão.
Este arquivo prova P2a desdobrando as definições da Mathlib, sem hipóteses:

* **Parte C** (`coef_inv_quad`, `coef_inv_um`): os coeficientes de `1 / (1 − aX + qX²)` seguem a
  recursão de Hecke; os de `1 / 1` se anulam fora de `0`;
* **Parte A** (`card_residuo`, `lfun_pot`): o corpo residual de `ℤ_v` tem `p` elementos
  (via `ℤ_v ≅ ℤ_p`), a cardinalidade residual é Northcott, e o produto de Euler da Mathlib avaliado
  em `p^k` é o `k`-ésimo coeficiente da série local em `p`;
* **Parte B** (`card_reducao`, `nao_boa_dois`, `nao_mult_dois`): em `p` ímpar, o `u` da mudança
  para o modelo minimal é unidade, o modelo integral minimal desce a `ℤ_v`, a redução é uma
  mudança de variáveis de `y² = x³ − x` sobre `𝔽_p` e `#Ẽ(𝔽_p) = p + 1 + Σ χ(x³ − x)`; em `2`,
  `2` é uniformizador (`ℤ_2`), `v(Δ_min) = 6 − 12·v(u) ≠ 0` (paridade) e
  `c₄³ = 1728 Δ` com `c₆ = 0` impede redução multiplicativa: a redução é aditiva;
* **Parte D** (`fatoresPadrao`, `cotaCoef_curva32`, `bsd_posto_curva32_modP1`): P2a, a cota
  `|aₙ| ≤ n` incondicional, e BSD (posto) para `y² = x³ − x` módulo só a ponte P1
  (modularidade com sinal `+1`).
-/

open IsDedekindDomain NumberField WeierstrassCurve ArithmeticFunction

namespace ATK.PonteFatoresCurva32

open ATK.PonteCoefCurva32

/-! ## Parte C: coeficientes de `1 / (1 − aX + qX²)` -/

section Serie

open PowerSeries

theorem coef_inv_quad (a q : ℤ) (k : ℕ) :
    coeff k (invOfUnit (((1 - Polynomial.C a * Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 :
      Polynomial ℤ)) : PowerSeries ℤ) 1) = hecke a q k := by
  set φ : PowerSeries ℤ := ((1 - Polynomial.C a * Polynomial.X + Polynomial.C q * Polynomial.X ^ 2 :
      Polynomial ℤ) : PowerSeries ℤ) with hφdef
  have hφ : φ = 1 - C a * X + C q * X ^ 2 := by
    simp only [hφdef, Polynomial.coe_sub, Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_C, Polynomial.coe_X, Polynomial.coe_one]
  set ψ := invOfUnit φ 1 with hψ
  have h1 : φ * ψ = 1 := mul_invOfUnit φ 1 (by simp [hφ])
  have hexp : φ * ψ = ψ - C a * (X * ψ) + C q * (X * (X * ψ)) := by rw [hφ]; ring
  rw [hexp] at h1
  have c0 : coeff 0 ψ = 1 := by
    have := congrArg (coeff 0) h1
    simpa [coeff_C_mul, coeff_zero_X_mul] using this
  have c1 : coeff 1 ψ = a := by
    have := congrArg (coeff 1) h1
    simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_one,
      c0] at this
    simp at this
    linarith
  have c2 : ∀ k, coeff (k + 2) ψ = a * coeff (k + 1) ψ - q * coeff k ψ := by
    intro k
    have := congrArg (coeff (k + 2)) h1
    simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_one] at this
    simp at this
    linarith
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [c0, hecke]
    | 1 => simp [c1, hecke]
    | k + 2 =>
      rw [c2 k, ih (k + 1) (by omega), ih k (by omega)]
      rfl

theorem coef_inv_um (k : ℕ) :
    coeff k (invOfUnit (((1 : Polynomial ℤ)) : PowerSeries ℤ) 1) = if k = 0 then 1 else 0 := by
  have h1 : (1 : PowerSeries ℤ) * invOfUnit (((1 : Polynomial ℤ)) : PowerSeries ℤ) 1 = 1 := by
    have := mul_invOfUnit (((1 : Polynomial ℤ)) : PowerSeries ℤ) 1 (by simp)
    simpa using this
  rw [one_mul] at h1
  rw [h1, coeff_one]

end Serie

/-! ## Parte A: o produto de Euler em potências de primos -/

section Euler

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

open Rat.HeightOneSpectrum

/-- **Corpo residual de `ℤ_v`**: tem `p` elementos, `p` o gerador de `v`. -/
theorem card_residuo (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = natGenerator v := by
  let e1 := IsLocalRing.ResidueField.mapEquiv
    (adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv
  let e2 := PadicInt.residueField (p := (primesEquiv v : ℕ))
  rw [Nat.card_congr (e1.trans e2).toEquiv, Nat.card_zmod]
  rfl

/-- `(F * G)(p^k) = F(p^k)` se `G(1) = 1` e `G` se anula em `p^j`, `j ≥ 1`. -/
theorem mul_pot {R : Type*} [CommSemiring R] {F G : ArithmeticFunction R} {p : ℕ} (hp : p.Prime)
    (hG1 : G 1 = 1) (hG : ∀ j, 1 ≤ j → G (p ^ j) = 0) (k : ℕ) :
    (F * G) (p ^ k) = F (p ^ k) := by
  rw [ArithmeticFunction.mul_apply, Finset.sum_eq_single (p ^ k, 1)]
  · simp [hG1]
  · rintro ⟨a, b⟩ hab hne
    rw [Nat.mem_divisorsAntidiagonal] at hab
    obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro_left a hab.1)
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp only [pow_zero, mul_one] at hab
      exact absurd (by rw [hab.1, pow_zero]) hne
    · simp [hG j hj0]
  · intro h
    exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, pow_ne_zero _ hp.ne_zero⟩) h

/-- Funções que valem `1` em `1` e se anulam nas potências positivas de `p`. -/
def Nula (p : ℕ) {R : Type*} [CommSemiring R] (G : ArithmeticFunction R) : Prop :=
  G 1 = 1 ∧ ∀ j, 1 ≤ j → G (p ^ j) = 0

theorem nula_mul {R : Type*} [CommSemiring R] {p : ℕ} (hp : p.Prime) {F G : ArithmeticFunction R}
    (hF : Nula p F) (hG : Nula p G) : Nula p (F * G) := by
  refine ⟨?_, fun j hj => ?_⟩
  · have := mul_pot (F := F) hp hG.1 hG.2 0
    simpa [hF.1] using this
  · rw [mul_pot hp hG.1 hG.2 j, hF.2 j hj]

theorem nula_um {R : Type*} [CommSemiring R] (p : ℕ) (hp : p.Prime) :
    Nula p (1 : ArithmeticFunction R) := by
  refine ⟨by simp, fun j hj => ?_⟩
  rw [ArithmeticFunction.one_apply_ne]
  exact (Nat.one_lt_pow (by omega) hp.one_lt).ne'

theorem nula_ofPowerSeries {R : Type*} [CommSemiring R] {p l : ℕ} (hp : p.Prime) (hl : l.Prime)
    (hpl : l ≠ p) (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 1) :
    Nula p (ofPowerSeries l f) := by
  refine ⟨by simp [hf], fun j hj => ?_⟩
  rw [ofPowerSeries_apply hl.one_lt, Function.extend_apply']
  · rfl
  rintro ⟨m, hm⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp only [pow_zero] at hm
    exact (Nat.one_lt_pow (by omega) hp.one_lt).ne hm
  · have hdvd : l ∣ p ^ j := hm ▸ dvd_pow_self l hm0.ne'
    exact hpl ((Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow hdvd))

/-- Northcott para a cardinalidade do corpo residual. -/
instance northcott_residuo : Northcott fun v : HeightOneSpectrum (𝓞 ℚ) =>
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) where
  finite_le b := by
    simp_rw [card_residuo]
    have hfin : {p : Nat.Primes | (p : ℕ) ≤ b}.Finite :=
      (Set.finite_Iic b).preimage Subtype.val_injective.injOn
    exact hfin.preimage (primesEquiv (R := 𝓞 ℚ)).injective.injOn

/-- Série local de `W` em `v`. -/
noncomputable def serieLocal (W : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    PowerSeries ℤ :=
  (W.baseChange (v.adicCompletion ℚ)).localPowerSeries (v.adicCompletionIntegers ℚ)

theorem lfun_eq (W : WeierstrassCurve ℚ) :
    W.LFunction = eulerProduct fun v : HeightOneSpectrum (𝓞 ℚ) =>
      ofPowerSeries (Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)))
        (serieLocal W v) := rfl

theorem natGenerator_inj {v w : HeightOneSpectrum (𝓞 ℚ)} (h : natGenerator v = natGenerator w) :
    v = w :=
  (primesEquiv (R := 𝓞 ℚ)).injective (Subtype.ext h)

/-- **Produto de Euler em potências de primos**: `a_{p^k}(W) = [X^k] ψ_v(X)`, `p` o gerador de `v`. -/
theorem lfun_pot (W : WeierstrassCurve ℚ) (v₀ : HeightOneSpectrum (𝓞 ℚ)) (k : ℕ) :
    W.LFunction (natGenerator v₀ ^ k) = PowerSeries.coeff k (serieLocal W v₀) := by
  classical
  have hp := prime_natGenerator v₀
  have hf : ∀ v, PowerSeries.constantCoeff (serieLocal W v) = 1 := fun v => by
    simp [serieLocal, WeierstrassCurve.localPowerSeries]
  obtain ⟨s, hs, hv₀⟩ := ((tendsTo_eulerProduct_ofPowerSeries (fun v : HeightOneSpectrum (𝓞 ℚ) =>
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))) (serieLocal W) hf
    (natGenerator v₀ ^ k)).and (Filter.eventually_ge_atTop {v₀})).exists
  rw [lfun_eq, ← hs, ← Finset.mul_prod_erase s _ (Finset.singleton_subset_iff.mp hv₀),
    mul_pot hp]
  · rw [card_residuo, ofPowerSeries_apply_pow hp.one_lt]
  all_goals
    have hN : Nula (natGenerator v₀) (∏ x ∈ s.erase v₀,
        ofPowerSeries (Nat.card (IsLocalRing.ResidueField (x.adicCompletionIntegers ℚ)))
          (serieLocal W x)) := by
      refine Finset.prod_induction _ (Nula (natGenerator v₀)) (fun _ _ => nula_mul hp)
        (nula_um _ hp) fun v hv => ?_
      rw [card_residuo]
      exact nula_ofPowerSeries hp (prime_natGenerator v)
        (fun h => (Finset.ne_of_mem_erase hv) (natGenerator_inj h)) _ (hf v)
  · exact hN.1
  · exact hN.2

end Euler


/-! ## Parte B0: contagem de pontos sobre um corpo -/

section Contagem

variable {F : Type*} [Field F]

/-- **Mudança de variáveis na equação**: `(C • W)(x, y) = 0 ⟺ W(u²x + r, u³y + u²sx + t) = 0`. -/
theorem equation_vc (W : WeierstrassCurve F) (C : VariableChange F) (x y : F) :
    (C • W).toAffine.Equation x y ↔
      W.toAffine.Equation (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rw [Affine.equation_iff', Affine.equation_iff']
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, Units.val_inv_eq_inv_val]
  constructor
  · intro h
    linear_combination (norm := skip) (C.u : F) ^ 6 * h
    field_simp
    ring
  · intro h
    linear_combination (norm := skip) ((C.u : F)⁻¹) ^ 6 * h
    field_simp
    ring

/-- A bijeção afim `(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
def transf (C : VariableChange F) : F × F ≃ F × F where
  toFun p := (C.u ^ 2 * p.1 + C.r, C.u ^ 3 * p.2 + C.u ^ 2 * C.s * p.1 + C.t)
  invFun q := ((q.1 - C.r) / C.u ^ 2, (q.2 - C.s * (q.1 - C.r) - C.t) / C.u ^ 3)
  left_inv p := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    ext <;> dsimp only <;> field_simp <;> ring
  right_inv q := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    ext <;> dsimp only <;> field_simp <;> ring

theorem card_vc (W : WeierstrassCurve F) (C : VariableChange F) :
    Nat.card {xy : F × F // (C • W).toAffine.Equation xy.1 xy.2} =
      Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} :=
  Nat.card_congr ((transf C).subtypeEquiv fun p => equation_vc W C p.1 p.2)

/-- `#W(F) = #{(x, y) : W(x, y) = 0} + 1` quando `Δ ≠ 0`. -/
theorem card_pontos [Finite F] (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0) :
    Nat.card W.toAffine.Point = Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} + 1 := by
  rw [Nat.card_congr (Affine.nonsingularPointEquiv W.toAffine)]
  change Nat.card (Option {xy : F × F // W.toAffine.Nonsingular xy.1 xy.2}) = _
  rw [Finite.card_option]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun xy =>
    (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).symm)

end Contagem

/-- A curva `y² = x³ − x` sobre um anel qualquer. -/
def E32 (A : Type*) [CommRing A] : WeierstrassCurve A := ⟨0, 0, 0, -1, 0⟩

theorem E32_equation {A : Type*} [CommRing A] (x y : A) :
    (E32 A).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - x := by
  rw [Affine.equation_iff]
  simp only [E32, zero_mul, add_zero, mul_zero]
  constructor <;> intro h <;> linear_combination h

theorem E32_Δ (A : Type*) [CommRing A] : (E32 A).Δ = 64 := by
  simp only [E32, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem E32_c₆ (A : Type*) [CommRing A] : (E32 A).c₆ = 0 := by
  simp only [E32, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  ring

theorem card_E32_equiv {F G : Type*} [CommRing F] [CommRing G] (σ : F ≃+* G) :
    Nat.card {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3 - xy.1} =
      Nat.card {xy : G × G // xy.2 ^ 2 = xy.1 ^ 3 - xy.1} :=
  Nat.card_congr ((σ.toEquiv.prodCongr σ.toEquiv).subtypeEquiv fun xy => by
    change _ ↔ (σ xy.2) ^ 2 = (σ xy.1) ^ 3 - σ xy.1
    rw [← map_pow, ← map_pow, ← map_sub, σ.injective.eq_iff])

theorem card_E32_zmod (p : ℕ) [Fact p.Prime] (h2 : p ≠ 2) :
    (Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - xy.1} : ℤ) = p - traco p := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [ATK.BaseHasseCurva32.card_afim (by rwa [ZMod.ringChar_zmod_n]), ZMod.card, traco]
  ring

/-! ## Parte B: o modelo minimal da Mathlib em cada primo -/

section Local

local instance instFactPrimes (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

open Rat.HeightOneSpectrum IsDiscreteValuationRing

variable (v : HeightOneSpectrum (𝓞 ℚ))

noncomputable abbrev Rv := v.adicCompletionIntegers ℚ
noncomputable abbrev Kv := v.adicCompletion ℚ
noncomputable abbrev Wv : WeierstrassCurve (Kv v) := ATK.CongruentCurve.E.baseChange (Kv v)

/-- Corpo residual de `ℤ_v` ≅ `𝔽_p`. -/
noncomputable def residuoEquiv :
    IsLocalRing.ResidueField (Rv v) ≃+* ZMod (natGenerator v) :=
  (IsLocalRing.ResidueField.mapEquiv
    (adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv).trans
    (PadicInt.residueField (p := (primesEquiv v : ℕ)))

theorem E_baseChange : (E32 (Rv v)).baseChange (Kv v) = Wv v := by
  ext <;> simp [E32, Wv, ATK.CongruentCurve.E, WeierstrassCurve.baseChange]

instance integral_E : IsIntegral (Rv v) (Wv v) := ⟨⟨E32 _, (E_baseChange v).symm⟩⟩

theorem Δ_E : (Wv v).Δ = algebraMap (Rv v) (Kv v) 2 ^ 6 := by
  rw [← E_baseChange, WeierstrassCurve.baseChange, map_Δ, E32_Δ, ← map_pow]
  norm_num

theorem c₆_E : (Wv v).c₆ = 0 := by
  rw [← E_baseChange, WeierstrassCurve.baseChange, map_c₆, E32_c₆, _root_.map_zero]

theorem unidade_de_val {x : Kv v}
    (hx : HeightOneSpectrum.valuation (Kv v) (maximalIdeal (Rv v)) x = 1) :
    ∃ u : (Rv v)ˣ, algebraMap (Rv v) (Kv v) u = x := by
  have hmem : x ∈ MonoidHom.mker (HeightOneSpectrum.valuation (Kv v) (maximalIdeal (Rv v))) := by
    rw [MonoidHom.mem_mker]; exact hx
  rw [mker_valuation_eq_isUnitSubmonoid] at hmem
  obtain ⟨b, hb, rfl⟩ := Submonoid.mem_map.mp hmem
  exact ⟨((IsUnit.mem_submonoid_iff b).mp hb).unit, rfl⟩

theorem eq_one_of_pow {x : WithZero (Multiplicative ℤ)} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) :
    x = 1 := by
  rcases lt_trichotomy x 1 with hx | hx | hx
  · exact absurd h (pow_lt_one₀ (WithZero.zero_le x) hx hn).ne
  · exact hx
  · exact absurd h (one_lt_pow₀ hx hn).ne'

/-- **Descida do modelo integral**: se o `u` da mudança para o modelo minimal é unidade de `ℤ_v`,
a redução do modelo minimal é uma mudança de variáveis de `y² = x³ − x` sobre `𝔽_v`. -/
theorem reducao_vc (hu : ∃ u : (Rv v)ˣ,
      algebraMap (Rv v) (Kv v) u = ((Wv v).exists_isMinimal (Rv v)).choose.u) :
    ∃ C : VariableChange (IsLocalRing.ResidueField (Rv v)),
      ((Wv v).minimal (Rv v)).reduction (Rv v) = C • E32 _ := by
  obtain ⟨u, hu⟩ := hu
  obtain ⟨CR, hCR⟩ := variableChange_integral_of_u_integral (R := Rv v) (W := Wv v)
    (W' := (Wv v).minimal (Rv v)) (CK := ((Wv v).exists_isMinimal (Rv v)).choose) rfl hu
  have hI : integralModel (Rv v) ((Wv v).minimal (Rv v)) = CR • E32 (Rv v) := by
    apply map_injective (IsFractionRing.injective (Rv v) (Kv v))
    change (integralModel (Rv v) ((Wv v).minimal (Rv v))).baseChange (Kv v) =
      (CR • E32 (Rv v)).map (algebraMap (Rv v) (Kv v))
    rw [baseChange_integralModel_eq, ← map_variableChange]
    change ((Wv v).exists_isMinimal (Rv v)).choose • Wv v =
      CR.baseChange (Kv v) • (E32 (Rv v)).baseChange (Kv v)
    rw [hCR, E_baseChange]
  refine ⟨CR.map (IsLocalRing.residue (Rv v)), ?_⟩
  change (integralModel (Rv v) ((Wv v).minimal (Rv v))).map (IsLocalRing.residue (Rv v)) = _
  rw [hI, ← map_variableChange]
  congr 1
  all_goals ext <;> simp [E32]

/-! ### Primos ímpares: redução boa e contagem -/

theorem dois_nao_mem {p : ℕ} (hv : natGenerator v = p) (h2 : p ≠ 2) :
    (2 : 𝓞 ℚ) ∉ v.asIdeal := by
  intro h
  have hp : p.Prime := hv ▸ prime_natGenerator v
  have hmem : ((2 : ℕ) : ℤ) ∈ v.asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
    have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) h
    rw [map_ofNat] at this
    rwa [Nat.cast_ofNat]
  have hd := (natGenerator_dvd_iff v).mpr hmem
  rw [hv] at hd
  exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)

theorem val_Δ_impar (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) :
    HeightOneSpectrum.valuation (Kv v) (maximalIdeal (Rv v)) (Wv v).Δ = 1 := by
  rw [Δ_E, ← map_pow, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff]
  exact IsLocalRing.notMem_maximalIdeal.mpr ((ATK.BSDTamagawaE32.dois_unidade v h2).pow 6)

theorem u_unidade (h2 : (2 : 𝓞 ℚ) ∉ v.asIdeal) :
    ∃ u : (Rv v)ˣ, algebraMap (Rv v) (Kv v) u = ((Wv v).exists_isMinimal (Rv v)).choose.u := by
  apply unidade_de_val
  have hg := (ATK.BSDTamagawaE32.boa_E32 v h2).goodReduction
  change HeightOneSpectrum.valuation _ _
    ((((Wv v).exists_isMinimal (Rv v)).choose • Wv v).Δ) = 1 at hg
  rw [variableChange_Δ, map_mul, map_pow, val_Δ_impar v h2, mul_one] at hg
  have h1 := eq_one_of_pow (by norm_num) hg
  rwa [Units.val_inv_eq_inv_val, map_inv₀, inv_eq_one] at h1

/-- **Contagem de pontos da redução**: `#Ẽ(𝔽_p) = p + 1 − a_p`, `a_p = −Σ χ(x³ − x)`. -/
theorem card_reducao (p : ℕ) [Fact p.Prime] (hv : natGenerator v = p) (h2 : p ≠ 2) :
    (Nat.card (((Wv v).minimal (Rv v)).reduction (Rv v)).toAffine.Point : ℤ) =
      p + 1 - traco p := by
  have h2' : (2 : 𝓞 ℚ) ∉ v.asIdeal := dois_nao_mem v hv h2
  obtain ⟨C, hC⟩ := reducao_vc v (u_unidade v h2')
  subst hv
  let σ := residuoEquiv v
  haveI : Finite (IsLocalRing.ResidueField (Rv v)) := Finite.of_equiv _ σ.toEquiv.symm
  have h64 : (64 : IsLocalRing.ResidueField (Rv v)) ≠ 0 := by
    intro h
    have h' := congrArg σ h
    rw [map_ofNat, _root_.map_zero] at h'
    have h'' : ((64 : ℕ) : ZMod (natGenerator v)) = 0 := by exact_mod_cast h'
    rw [ZMod.natCast_eq_zero_iff] at h''
    have hp := prime_natGenerator v
    have : natGenerator v ∣ 2 ^ 6 := by norm_num; exact h''
    exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
  rw [hC, card_pontos _ (by
      rw [variableChange_Δ, E32_Δ]
      exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) h64), card_vc,
    Nat.card_congr (Equiv.subtypeEquivRight (α := IsLocalRing.ResidueField (Rv v) × IsLocalRing.ResidueField (Rv v))
      fun xy => E32_equation xy.1 xy.2),
    card_E32_equiv σ]
  push_cast
  rw [card_E32_zmod _ h2]
  ring

/-! ### O primo 2: redução aditiva -/

theorem dois_irredutivel (hv : natGenerator v = 2) : Irreducible (2 : Rv v) := by
  let e := (adicCompletionIntegers.padicIntEquiv v).toAlgEquiv.toRingEquiv
  refine (MulEquiv.irreducible_iff e.toMulEquiv (x := 2)).mp ?_
  have h2e : e.toMulEquiv 2 = 2 := map_ofNat e 2
  rw [h2e]
  have hp := PadicInt.irreducible_p (p := (primesEquiv v : ℕ))
  have h : (((primesEquiv v : ℕ) : ℤ_[(primesEquiv v : ℕ)])) = 2 := by
    change ((natGenerator v : ℕ) : ℤ_[(primesEquiv v : ℕ)]) = 2
    rw [hv]; norm_num
  rwa [h] at hp

theorem val_dois (hv : natGenerator v = 2) :
    HeightOneSpectrum.valuation (Kv v) (maximalIdeal (Rv v)) (algebraMap (Rv v) (Kv v) 2) =
      WithZero.exp (-1 : ℤ) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ (dois_irredutivel v hv).ne_zero
    ((irreducible_iff_uniformizer _).mp (dois_irredutivel v hv))

theorem nao_boa_dois (hv : natGenerator v = 2) :
    ¬ ((Wv v).minimal (Rv v)).HasGoodReduction (Rv v) := by
  intro hg
  have h := hg.goodReduction
  change HeightOneSpectrum.valuation _ _
    ((((Wv v).exists_isMinimal (Rv v)).choose • Wv v).Δ) = 1 at h
  rw [variableChange_Δ, Δ_E, map_mul, map_pow, map_pow, val_dois v hv] at h
  set y := HeightOneSpectrum.valuation (Kv v) (maximalIdeal (Rv v))
    ((((Wv v).exists_isMinimal (Rv v)).choose.u⁻¹ : (Kv v)ˣ) : Kv v) with hy
  have hy0 : y ≠ 0 := (Valuation.ne_zero_iff _).mpr (Units.ne_zero _)
  rw [← WithZero.exp_log hy0, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add,
    WithZero.exp_eq_one] at h
  simp only [nsmul_eq_mul] at h
  push_cast at h
  omega

theorem nao_mult_dois (hv : natGenerator v = 2) :
    ¬ ((Wv v).minimal (Rv v)).HasMultiplicativeReduction (Rv v) := by
  intro hm
  have h1 := hm.multiplicativeReduction
  have hc6 : ((Wv v).minimal (Rv v)).c₆ = 0 := by
    change ((((Wv v).exists_isMinimal (Rv v)).choose • Wv v)).c₆ = 0
    rw [variableChange_c₆, c₆_E, mul_zero]
  have hrel := ((Wv v).minimal (Rv v)).c_relation
  rw [hc6] at hrel
  have hΔ : HeightOneSpectrum.valuation (Kv v) (maximalIdeal (Rv v))
      ((Wv v).minimal (Rv v)).Δ ≤ 1 := by
    rw [← integralModel_Δ_eq (Rv v) ((Wv v).minimal (Rv v))]
    exact HeightOneSpectrum.valuation_le_one _ _
  have h1728 : (1728 : Kv v) =
      algebraMap (Rv v) (Kv v) 2 ^ 6 * algebraMap (Rv v) (Kv v) 27 := by
    simp only [map_ofNat]; norm_num
  have hval := congrArg (HeightOneSpectrum.valuation (Kv v) (maximalIdeal (Rv v))) hrel
  rw [h1728, map_mul, map_mul, map_pow, val_dois v hv, zero_pow (by norm_num), sub_zero,
    map_pow, h1, one_pow] at hval
  have h27 : HeightOneSpectrum.valuation (Kv v) (maximalIdeal (Rv v))
      (algebraMap (Rv v) (Kv v) 27) ≤ 1 := HeightOneSpectrum.valuation_le_one _ _
  have hle : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-1 : ℤ) ^ 6 := by
    rw [← hval]
    calc _ ≤ WithZero.exp (-1 : ℤ) ^ 6 * 1 * 1 := mul_le_mul' (mul_le_mul' le_rfl h27) hΔ
      _ = _ := by rw [mul_one, mul_one]
  rw [← WithZero.exp_nsmul, WithZero.one_le_exp_iff] at hle
  norm_num at hle

end Local

/-! ## Parte D: a ponte P2a e a cota `|aₙ| ≤ n` incondicional -/

section Final

local instance instFactPrimes' (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

open Rat.HeightOneSpectrum ATK.LigacaoBSD ATK.AtaqueBSD

/-- O lugar de `ℚ` acima do primo `p`. -/
noncomputable def lugar (p : ℕ) (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (primesEquiv (R := 𝓞 ℚ)).symm ⟨p, hp⟩

theorem natGenerator_lugar (p : ℕ) (hp : p.Prime) : natGenerator (lugar p hp) = p :=
  congrArg Subtype.val ((primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨p, hp⟩)

/-- **Fator local em `p` ímpar**: `[X^k] ψ_p = c_k(a_p, p)`, `a_p = −Σ χ(x³ − x)`. -/
theorem serie_impar (v : HeightOneSpectrum (𝓞 ℚ)) (p : ℕ) [Fact p.Prime]
    (hv : natGenerator v = p) (h2 : p ≠ 2) (k : ℕ) :
    PowerSeries.coeff k (serieLocal ATK.CongruentCurve.E v) = hecke (traco p) p k := by
  have hg := ATK.BSDTamagawaE32.boa_E32 v (dois_nao_mem v hv h2)
  have hq : (Nat.card (IsLocalRing.ResidueField (Rv v)) : ℤ) = p := by rw [card_residuo, hv]
  have ha : (Nat.card (IsLocalRing.ResidueField (Rv v)) : ℤ) + 1 -
      Nat.card (((Wv v).minimal (Rv v)).reduction (Rv v)).toAffine.Point = traco p := by
    rw [card_reducao v p hv h2, hq]; ring
  unfold serieLocal localPowerSeries localPolynomial
  rw [if_pos hg, ha, hq]
  exact coef_inv_quad _ _ k

/-- **Fator local em 2**: redução aditiva, `ψ_2 = 1`. -/
theorem serie_dois (v : HeightOneSpectrum (𝓞 ℚ)) (hv : natGenerator v = 2) (k : ℕ)
    (hk : 1 ≤ k) : PowerSeries.coeff k (serieLocal ATK.CongruentCurve.E v) = 0 := by
  have hng := nao_boa_dois v hv
  have hnm := nao_mult_dois v hv
  have hns : ¬ ((Wv v).minimal (Rv v)).HasSplitMultiplicativeReduction (Rv v) :=
    fun h => hnm h.toHasMultiplicativeReduction
  unfold serieLocal localPowerSeries localPolynomial
  rw [if_neg hng, if_neg hns, if_neg hnm, coef_inv_um, if_neg (by omega)]

/-- **Ponte P2a provada**: os coeficientes de `WeierstrassCurve.LFunction` da Mathlib para
`y² = x³ − x` são os padrão (`a_{2^k} = 0`, `a_{p^k} = c_k(a_p, p)`). -/
theorem fatoresPadrao : FatoresPadrao := by
  refine ⟨fun k hk => ?_, fun p _ h2 k => ?_⟩
  · have h := lfun_pot ATK.CongruentCurve.E (lugar 2 Nat.prime_two) k
    rw [natGenerator_lugar] at h
    rw [h, serie_dois _ (natGenerator_lugar _ _) k hk]
  · have hp : p.Prime := Fact.out
    have h := lfun_pot ATK.CongruentCurve.E (lugar p hp) k
    rw [natGenerator_lugar] at h
    rw [h, serie_impar _ p (natGenerator_lugar _ _) h2 k]

/-- **P2 incondicional**: `|aₙ| ≤ n` para `y² = x³ − x`. -/
theorem cotaCoef_curva32 : CotaCoef ATK.CongruentCurve.E :=
  cotaCoef_de_fatores fatoresPadrao

/-- **BSD (posto) para `y² = x³ − x` módulo só P1** (modularidade com sinal `+1`). -/
theorem bsd_posto_curva32_modP1 (hM : PonteModular ATK.CongruentCurve.E c32 1)
    {G : ℂ → ℂ} (hG : Continuacao ATK.CongruentCurve.E G) :
    G 1 ≠ 0 ∧ analyticOrderAt G 1 = postoMW ATK.CongruentCurve.E :=
  bsd_posto_curva32_P1 hM fatoresPadrao hG

end Final

end ATK.PonteFatoresCurva32

#print axioms ATK.PonteFatoresCurva32.coef_inv_quad
#print axioms ATK.PonteFatoresCurva32.coef_inv_um
#print axioms ATK.PonteFatoresCurva32.card_residuo
#print axioms ATK.PonteFatoresCurva32.mul_pot
#print axioms ATK.PonteFatoresCurva32.nula_mul
#print axioms ATK.PonteFatoresCurva32.nula_um
#print axioms ATK.PonteFatoresCurva32.nula_ofPowerSeries
#print axioms ATK.PonteFatoresCurva32.lfun_eq
#print axioms ATK.PonteFatoresCurva32.natGenerator_inj
#print axioms ATK.PonteFatoresCurva32.lfun_pot
#print axioms ATK.PonteFatoresCurva32.equation_vc
#print axioms ATK.PonteFatoresCurva32.card_vc
#print axioms ATK.PonteFatoresCurva32.card_pontos
#print axioms ATK.PonteFatoresCurva32.E32_equation
#print axioms ATK.PonteFatoresCurva32.E32_Δ
#print axioms ATK.PonteFatoresCurva32.E32_c₆
#print axioms ATK.PonteFatoresCurva32.card_E32_equiv
#print axioms ATK.PonteFatoresCurva32.card_E32_zmod
#print axioms ATK.PonteFatoresCurva32.E_baseChange
#print axioms ATK.PonteFatoresCurva32.Δ_E
#print axioms ATK.PonteFatoresCurva32.c₆_E
#print axioms ATK.PonteFatoresCurva32.unidade_de_val
#print axioms ATK.PonteFatoresCurva32.eq_one_of_pow
#print axioms ATK.PonteFatoresCurva32.reducao_vc
#print axioms ATK.PonteFatoresCurva32.dois_nao_mem
#print axioms ATK.PonteFatoresCurva32.val_Δ_impar
#print axioms ATK.PonteFatoresCurva32.u_unidade
#print axioms ATK.PonteFatoresCurva32.card_reducao
#print axioms ATK.PonteFatoresCurva32.dois_irredutivel
#print axioms ATK.PonteFatoresCurva32.val_dois
#print axioms ATK.PonteFatoresCurva32.nao_boa_dois
#print axioms ATK.PonteFatoresCurva32.nao_mult_dois
#print axioms ATK.PonteFatoresCurva32.natGenerator_lugar
#print axioms ATK.PonteFatoresCurva32.serie_impar
#print axioms ATK.PonteFatoresCurva32.serie_dois
#print axioms ATK.PonteFatoresCurva32.fatoresPadrao
#print axioms ATK.PonteFatoresCurva32.cotaCoef_curva32
#print axioms ATK.PonteFatoresCurva32.bsd_posto_curva32_modP1
