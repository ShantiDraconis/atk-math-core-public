import ATK.BSDInvariantes
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Algebra.BigOperators.Finprod

/-!
# ATK — Ligação L4: Tamagawa, Ш e a fórmula refinada de BSD

Completa os invariantes de `ATK.BSDInvariantes` com os dois que dependem de aritmética local e
global, e enuncia a fórmula refinada sobre os objetos da Mathlib:

* `tamagawaLocal`: `c_v = [E(K_v) : E⁰(K_v)]`, com `E⁰` os pontos do modelo minimal
  (`WeierstrassCurve.minimal` da Mathlib) cuja redução (`WeierstrassCurve.reduction`) é não singular;
  `tamagawaLocal_of_good`: redução boa ⇒ `c_v = 1`;
  `tamagawa = ∏_p c_p` (`finprod` sobre os primos de `ℚ`), `tamagawa_eq_prod`: fora de um conjunto
  finito de primos de redução boa, o produto é finito;
* `sha`: `Ш(E/ℚ) = ker(H¹(G_ℚ, E(ℚ̄)) → ∏_v H¹(G_{ℚ_v}, E(ℚ̄_v)))`, com cociclos contínuos
  (localmente constantes na topologia de Krull) e todas as places (`ℝ` e os completamentos
  `p`-ádicos da Mathlib); `cobordo_localmenteTrivial`: os cobordos morrem em toda place;
* `FormulaRefinada E`: `Ш` finito e
  `L^{(r)}(E,1)/r! = Ω_E · Reg_E · ∏ c_p · #Ш / #E(ℚ)_tors²`;
* `modeloCompleto`: o `BSDModel` com posto, posto analítico e fórmula refinada genuínos;
  `bsdFull_iff`: sob modularidade e Mordell–Weil (teoremas publicados, hipóteses explícitas),
  `BSDFull modeloCompleto` é exatamente o enunciado completo (posto do Clay + fórmula refinada);
  `bsdFull_iff_fraco`: o mesmo com Mordell–Weil fraco (`E(ℚ)/2E(ℚ)` finito) no lugar de Mordell–Weil;
* `formula_E32_iff`: em `y² = x³ − x` (posto 0, torção de ordem 4, `Reg = 1`), a fórmula refinada
  reduz-se a `L(E,1) = Ω · ∏ c_p · #Ш / 16` (com `Ш` finito).

Nada aqui prova BSD: as obrigações O6 (`RankOpen`) e O7 (`RefinedOpen`) continuam `OPEN_MATH`, e a
ponte B6 (Gross–Zagier–Kolyvagin) continua publicada e não formalizada.
-/

open WeierstrassCurve Field

namespace ATK.BSDRefinada

open ATK.BSDInvariantes

/-! ## Números de Tamagawa -/

section Tamagawa

open IsLocalRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq K]

/-- `E⁰(K)`: os pontos do modelo minimal cuja redução é não singular. O ponto no infinito reduz a
`O` (não singular); um ponto afim com coordenadas fora de `R` também reduz a `O`; um ponto com
coordenadas `x', y' ∈ R` reduz a `(x̄', ȳ')`. -/
def pontosE0 (W : WeierstrassCurve K) : Set (W.minimal R).toAffine.Point :=
  {P | ∀ (x y : K) (h : (W.minimal R).toAffine.Nonsingular x y), P = .some x y h →
    ∀ x' y' : R, algebraMap R K x' = x → algebraMap R K y' = y →
      ((W.minimal R).reduction R).toAffine.Nonsingular (residue R x') (residue R y')}

/-- **Número de Tamagawa local** `c_v = [E(K) : E⁰(K)]` (índice do subgrupo gerado por `E⁰`, que é
o próprio `E⁰`). -/
noncomputable def tamagawaLocal (W : WeierstrassCurve K) : ℕ :=
  (AddSubgroup.closure (pontosE0 R W)).index

omit [DecidableEq K] in
/-- A redução de um ponto integral satisfaz a equação reduzida. -/
theorem reducao_equacao (W : WeierstrassCurve K) {x y : K}
    (h : (W.minimal R).toAffine.Equation x y) {x' y' : R} (hx : algebraMap R K x' = x)
    (hy : algebraMap R K y' = y) :
    ((W.minimal R).reduction R).toAffine.Equation (residue R x') (residue R y') := by
  set W' := W.minimal R
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  rw [← hx, ← hy, ← integralModel_a₁_eq R W', ← integralModel_a₂_eq R W',
    ← integralModel_a₃_eq R W', ← integralModel_a₄_eq R W', ← integralModel_a₆_eq R W'] at h
  have hR : y' ^ 2 + (integralModel R W').a₁ * x' * y' + (integralModel R W').a₃ * y' =
      x' ^ 3 + (integralModel R W').a₂ * x' ^ 2 + (integralModel R W').a₄ * x' +
        (integralModel R W').a₆ := by
    apply IsFractionRing.injective R K
    simpa only [map_add, map_mul, map_pow] using h
  have := congrArg (residue R) hR
  simp only [map_add, map_mul, map_pow] at this
  simpa only [reduction, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] using this

/-- **Redução boa ⇒ `c_v = 1`**: todo ponto reduz a um ponto não singular. -/
theorem tamagawaLocal_of_good (W : WeierstrassCurve K)
    (hg : (W.minimal R).HasGoodReduction R) : tamagawaLocal R W = 1 := by
  have hell : ((W.minimal R).reduction R).IsElliptic :=
    (hasGoodReduction_iff_isElliptic_reduction R).mp hg
  have huniv : pontosE0 R W = Set.univ := by
    ext P
    simp only [Set.mem_univ, iff_true]
    intro x y hns _ x' y' hx hy
    exact WeierstrassCurve.Affine.equation_iff_nonsingular.mp
      (reducao_equacao R W ((WeierstrassCurve.Affine.nonsingular_iff _ _).mp hns).1 hx hy)
  rw [tamagawaLocal, huniv, AddSubgroup.closure_univ, AddSubgroup.index_top]

end Tamagawa

section TamagawaGlobal

open IsDedekindDomain NumberField

/-- O fator local em `v`. -/
noncomputable def fatorTamagawa (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ :=
  letI := Classical.decEq (v.adicCompletion ℚ)
  tamagawaLocal (v.adicCompletionIntegers ℚ) (E.baseChange (v.adicCompletion ℚ))

/-- **O produto de Tamagawa** `∏_p c_p` sobre os primos de `ℚ`. -/
noncomputable def tamagawa (E : WeierstrassCurve ℚ) : ℕ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 ℚ), fatorTamagawa E v

/-- Redução boa em `v` ⇒ fator `1`. -/
theorem fatorTamagawa_of_good (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ))
    (hg : ((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).HasGoodReduction
      (v.adicCompletionIntegers ℚ)) : fatorTamagawa E v = 1 := by
  let _ := Classical.decEq (v.adicCompletion ℚ)
  exact tamagawaLocal_of_good _ _ hg

/-- Se a redução é boa fora de um conjunto finito `S` de primos, `∏_p c_p = ∏_{p ∈ S} c_p`. -/
theorem tamagawa_eq_prod (E : WeierstrassCurve ℚ) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v ∉ S, ((E.baseChange (v.adicCompletion ℚ)).minimal
      (v.adicCompletionIntegers ℚ)).HasGoodReduction (v.adicCompletionIntegers ℚ)) :
    tamagawa E = ∏ v ∈ S, fatorTamagawa E v := by
  refine finprod_eq_prod_of_mulSupport_subset _ fun v hv => ?_
  by_contra hvS
  exact hv (fatorTamagawa_of_good E v (hS v hvS))

end TamagawaGlobal

/-! ## O grupo de Tate–Shafarevich -/

section Sha

open Classical

variable (E : WeierstrassCurve ℚ)

/-- `E(F̄)`, para um corpo `F` de característica 0. -/
abbrev PontosBar (F : Type*) [Field F] [Algebra ℚ F] :=
  (E.toAffine.baseChange (AlgebraicClosure F)).Point

/-- Um elemento de `G_F = Gal(F̄/F)` como automorfismo de `F̄`. -/
abbrev gal {F : Type*} [Field F] (σ : absoluteGaloisGroup F) :
    AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := σ

/-- A ação de Galois de `G_F` sobre `E(F̄)`. -/
noncomputable def acao {F : Type*} [Field F] [Algebra ℚ F] (σ : absoluteGaloisGroup F) :
    PontosBar E F →+ PontosBar E F :=
  WeierstrassCurve.Affine.Point.map ((gal σ).restrictScalars ℚ).toAlgHom

/-- **Cociclos contínuos** `G_ℚ → E(ℚ̄)`: localmente constantes (o módulo é discreto) e
`f(στ) = f(σ) + σ·f(τ)`. -/
noncomputable def cociclos : AddSubgroup (absoluteGaloisGroup ℚ → PontosBar E ℚ) where
  carrier := {f | IsLocallyConstant f ∧ ∀ σ τ, f (σ * τ) = f σ + acao E σ (f τ)}
  add_mem' := by
    rintro f g ⟨hf, hf'⟩ ⟨hg, hg'⟩
    refine ⟨hf.add hg, fun σ τ => ?_⟩
    simp only [Pi.add_apply, hf', hg', map_add]
    abel
  zero_mem' := ⟨IsLocallyConstant.zero, fun σ τ => by simp⟩
  neg_mem' := by
    rintro f ⟨hf, hf'⟩
    refine ⟨hf.neg, fun σ τ => ?_⟩
    simp only [Pi.neg_apply, hf', map_neg]
    abel

/-- **Cobordos**: `f(σ) = σ·m − m`. -/
noncomputable def cobordos : AddSubgroup (cociclos E) where
  carrier := {f | ∃ m : PontosBar E ℚ, ∀ σ, (f : absoluteGaloisGroup ℚ → PontosBar E ℚ) σ =
    acao E σ m - m}
  add_mem' := by
    rintro f g ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, fun σ => ?_⟩
    simp only [AddSubgroup.coe_add, Pi.add_apply, hm, hn, map_add]
    abel
  zero_mem' := ⟨0, fun σ => by simp⟩
  neg_mem' := by
    rintro f ⟨m, hm⟩
    refine ⟨-m, fun σ => ?_⟩
    simp only [AddSubgroup.coe_neg, Pi.neg_apply, hm, map_neg]
    abel

/-- `H¹(G_ℚ, E(ℚ̄))` (cohomologia de Galois contínua). -/
abbrev H1 := cociclos E ⧸ cobordos E

/-- A restrição `G_F → G_ℚ` dada por um mergulho `ι : ℚ̄ → F̄` (`ℚ̄/ℚ` é normal). -/
noncomputable def res {F : Type*} [Field F] [Algebra ℚ F]
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure F) (σ : absoluteGaloisGroup F) :
    absoluteGaloisGroup ℚ :=
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure F) := ι.toRingHom.toAlgebra
  haveI := IsScalarTower.of_algHom ι
  AlgEquiv.restrictNormal ((gal σ).restrictScalars ℚ) (AlgebraicClosure ℚ)

/-- `ι ∘ res(σ) = σ ∘ ι`. -/
theorem res_comm {F : Type*} [Field F] [Algebra ℚ F]
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure F) (σ : absoluteGaloisGroup F)
    (x : AlgebraicClosure ℚ) :
    ι (gal (res ι σ) x) = gal σ (ι x) := by
  let _ : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure F) := ι.toRingHom.toAlgebra
  have := IsScalarTower.of_algHom ι
  exact AlgEquiv.restrictNormal_commutes ((gal σ).restrictScalars ℚ) (AlgebraicClosure ℚ) x

/-- Compatibilidade: `ι_*(res(σ)·P) = σ·ι_*(P)`. -/
theorem map_acao {F : Type*} [Field F] [Algebra ℚ F]
    (ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure F) (σ : absoluteGaloisGroup F)
    (P : PontosBar E ℚ) :
    WeierstrassCurve.Affine.Point.map ι (acao E (res ι σ) P) =
      acao E σ (WeierstrassCurve.Affine.Point.map ι P) := by
  have h : ι.comp ((gal (res ι σ)).restrictScalars ℚ).toAlgHom =
      ((gal σ).restrictScalars ℚ).toAlgHom.comp ι := by
    ext x
    exact res_comm ι σ x
  simp only [acao, WeierstrassCurve.Affine.Point.map_map, h]

/-- `f` (uma cocadeia de `G_ℚ`) fica trivial em `G_F`, para todo mergulho `ℚ̄ → F̄`. -/
def trivialEm (F : Type*) [Field F] [Algebra ℚ F] (f : absoluteGaloisGroup ℚ → PontosBar E ℚ) :
    Prop :=
  ∀ ι : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure F, ∃ m : PontosBar E F,
    ∀ σ : absoluteGaloisGroup F, WeierstrassCurve.Affine.Point.map ι (f (res ι σ)) = acao E σ m - m

open IsDedekindDomain NumberField in
/-- Trivial em todas as places de `ℚ`: a real e todas as `p`-ádicas. -/
def LocalmenteTrivial (f : absoluteGaloisGroup ℚ → PontosBar E ℚ) : Prop :=
  trivialEm E ℝ f ∧ ∀ v : HeightOneSpectrum (𝓞 ℚ), trivialEm E (v.adicCompletion ℚ) f

theorem trivialEm_add {F : Type*} [Field F] [Algebra ℚ F]
    {f g : absoluteGaloisGroup ℚ → PontosBar E ℚ} (hf : trivialEm E F f) (hg : trivialEm E F g) :
    trivialEm E F (f + g) := by
  intro ι
  obtain ⟨m, hm⟩ := hf ι
  obtain ⟨n, hn⟩ := hg ι
  refine ⟨m + n, fun σ => ?_⟩
  simp only [Pi.add_apply, map_add, hm, hn]
  abel

theorem trivialEm_zero {F : Type*} [Field F] [Algebra ℚ F] : trivialEm E F 0 :=
  fun _ => ⟨0, fun σ => by simp⟩

theorem trivialEm_neg {F : Type*} [Field F] [Algebra ℚ F]
    {f : absoluteGaloisGroup ℚ → PontosBar E ℚ} (hf : trivialEm E F f) : trivialEm E F (-f) := by
  intro ι
  obtain ⟨m, hm⟩ := hf ι
  refine ⟨-m, fun σ => ?_⟩
  simp only [Pi.neg_apply, map_neg, hm]
  abel

/-- Os cociclos localmente triviais. -/
noncomputable def shaZ : AddSubgroup (cociclos E) where
  carrier := {f | LocalmenteTrivial E f}
  add_mem' := fun hf hg => ⟨trivialEm_add E hf.1 hg.1, fun v => trivialEm_add E (hf.2 v) (hg.2 v)⟩
  zero_mem' := ⟨trivialEm_zero E, fun _ => trivialEm_zero E⟩
  neg_mem' := fun hf => ⟨trivialEm_neg E hf.1, fun v => trivialEm_neg E (hf.2 v)⟩

/-- **O grupo de Tate–Shafarevich** `Ш(E/ℚ) ⊆ H¹(G_ℚ, E(ℚ̄))`: as classes que morrem em toda
place. -/
noncomputable def sha : AddSubgroup (H1 E) :=
  (shaZ E).map (QuotientAddGroup.mk' (cobordos E))

/-- Teste: **os cobordos são localmente triviais** (logo `Ш ≅ shaZ / cobordos`). -/
theorem cobordo_localmenteTrivial : cobordos E ≤ shaZ E := by
  rintro f ⟨m, hm⟩
  have key : ∀ (F : Type) [Field F] [Algebra ℚ F],
      trivialEm E F (f : absoluteGaloisGroup ℚ → PontosBar E ℚ) := by
    intro F _ _ ι
    refine ⟨WeierstrassCurve.Affine.Point.map ι m, fun σ => ?_⟩
    rw [hm, map_sub, map_acao]
  exact ⟨key ℝ, fun v => key _⟩

end Sha

/-! ## A fórmula refinada e o modelo completo -/

section Formula

open ATK.L4Base

/-- **A fórmula refinada de BSD** para `E/ℚ`: `Ш(E)` é finito e
`L^{(r)}(E, 1) / r! = Ω_E · Reg_E · ∏_p c_p · #Ш(E) / #E(ℚ)_tors²`. -/
def FormulaRefinada (E : WeierstrassCurve ℚ) : Prop :=
  Finite (sha E) ∧ ∃ Lc : LFunctionContinued E,
    coefLider Lc = ((periodo E * regulador E * tamagawa E * Nat.card (sha E) /
      (ordemTorsao E : ℝ) ^ 2 : ℝ) : ℂ)

/-- **O modelo completo**: postos e fórmula refinada genuínos (`ATK.LigacaoBSD.modeloPosto`). -/
noncomputable def modeloCompleto : ATK.Conditional.BSD.BSDModel.{0} :=
  ATK.LigacaoBSD.modeloPosto fun E => FormulaRefinada E.1

/-- O enunciado completo de BSD sobre os objetos da Mathlib: a parte do posto (Clay) e a fórmula
refinada para toda curva elíptica sobre `ℚ`. -/
def ClayBSDCompleto : Prop :=
  ATK.LigacaoBSD.ClayBSD ∧ ∀ E : WeierstrassCurve ℚ, E.IsElliptic → FormulaRefinada E

/-- **Fidelidade**: sob modularidade e Mordell–Weil (hipóteses explícitas), o portão `BSDFull` do
modelo completo é exatamente o enunciado completo. -/
theorem bsdFull_iff (hMod : ATK.LigacaoBSD.Modularidade) (hMW : ATK.LigacaoBSD.MordellWeil) :
    ATK.Conditional.BSD.BSDFull modeloCompleto ↔ ClayBSDCompleto := by
  unfold ATK.Conditional.BSD.BSDFull ClayBSDCompleto
  rw [show ATK.Conditional.BSD.BSDRank modeloCompleto ↔ ATK.LigacaoBSD.ClayBSD from
    ATK.LigacaoBSD.posto_iff hMod hMW _]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun E hE => h2 ⟨E, hE⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun E => h2 E.1 E.2⟩

/-- A mesma fidelidade com Mordell–Weil **fraco** no lugar de Mordell–Weil
(`ATK.BSDInvariantes.mordellWeil_of_fraco`). -/
theorem bsdFull_iff_fraco (hMod : ATK.LigacaoBSD.Modularidade) (hW : MordellWeilFraco) :
    ATK.Conditional.BSD.BSDFull modeloCompleto ↔ ClayBSDCompleto :=
  bsdFull_iff hMod (mordellWeil_of_fraco hW)

/-- A obrigação O7 no modelo completo é, literalmente, a fórmula refinada para toda `E/ℚ`. -/
theorem refinedOpen_iff :
    ATK.Conditional.BSD.RefinedOpen modeloCompleto ↔
      ∀ E : WeierstrassCurve ℚ, E.IsElliptic → FormulaRefinada E :=
  ⟨fun h E hE => h ⟨E, hE⟩, fun h E => h E.1 E.2⟩

/-- **Teste (`y² = x³ − x`)**: com torção de ordem 4 e `Reg = 1`, a fórmula refinada é
`L^{(r)}(E,1)/r! = Ω · ∏ c_p · #Ш / 16` com `Ш` finito. -/
theorem formula_E32_iff :
    FormulaRefinada E32 ↔ Finite (sha E32) ∧ ∃ Lc : LFunctionContinued E32,
      coefLider Lc = ((periodo E32 * tamagawa E32 * Nat.card (sha E32) / 16 : ℝ) : ℂ) := by
  unfold FormulaRefinada
  rw [regulador_E32, ordemTorsao_E32]
  norm_num

/-- Se além disso `L(E, 1) ≠ 0` (o que a parte do posto de BSD exige para esta curva), o lado
esquerdo é `L(E, 1)`. -/
theorem formula_E32_iff_of_ne_zero (Lc : LFunctionContinued E32) (h : Lc.L 1 ≠ 0) :
    FormulaRefinada E32 ↔ Finite (sha E32) ∧
      Lc.L 1 = ((periodo E32 * tamagawa E32 * Nat.card (sha E32) / 16 : ℝ) : ℂ) := by
  rw [formula_E32_iff]
  constructor
  · rintro ⟨hf, Lc', hL⟩
    rw [Subsingleton.elim Lc' Lc, coefLider_of_ne_zero Lc h] at hL
    exact ⟨hf, hL⟩
  · rintro ⟨hf, hL⟩
    exact ⟨hf, Lc, by rw [coefLider_of_ne_zero Lc h]; exact hL⟩

/-- Em `y² = x³ − x` (posto 0), as instâncias de B6 (posto analítico ≤ 1) e de O6 (posto analítico
≥ 2) no modelo completo dizem juntas exatamente que o posto analítico é 0. -/
theorem pontes_E32_iff :
    ((modeloCompleto.analyticRank ⟨E32, E32_eliptica⟩ ≤ 1 →
        modeloCompleto.rank ⟨E32, E32_eliptica⟩ = modeloCompleto.analyticRank ⟨E32, E32_eliptica⟩) ∧
      (2 ≤ modeloCompleto.analyticRank ⟨E32, E32_eliptica⟩ →
        modeloCompleto.rank ⟨E32, E32_eliptica⟩ = modeloCompleto.analyticRank ⟨E32, E32_eliptica⟩)) ↔
      modeloCompleto.analyticRank ⟨E32, E32_eliptica⟩ = 0 := by
  have hr : modeloCompleto.rank ⟨E32, E32_eliptica⟩ = 0 := by
    change (ATK.LigacaoBSD.postoMW E32).toNat = 0
    rw [E32, ATK.LigacaoBSDTestes.posto_curva32]; rfl
  rw [hr]
  omega

end Formula

end ATK.BSDRefinada

#print axioms ATK.BSDRefinada.reducao_equacao
#print axioms ATK.BSDRefinada.tamagawaLocal_of_good
#print axioms ATK.BSDRefinada.fatorTamagawa_of_good
#print axioms ATK.BSDRefinada.tamagawa_eq_prod
#print axioms ATK.BSDRefinada.res_comm
#print axioms ATK.BSDRefinada.map_acao
#print axioms ATK.BSDRefinada.trivialEm_add
#print axioms ATK.BSDRefinada.trivialEm_zero
#print axioms ATK.BSDRefinada.trivialEm_neg
#print axioms ATK.BSDRefinada.cobordo_localmenteTrivial
#print axioms ATK.BSDRefinada.bsdFull_iff
#print axioms ATK.BSDRefinada.bsdFull_iff_fraco
#print axioms ATK.BSDRefinada.refinedOpen_iff
#print axioms ATK.BSDRefinada.formula_E32_iff
#print axioms ATK.BSDRefinada.formula_E32_iff_of_ne_zero
#print axioms ATK.BSDRefinada.pontes_E32_iff
