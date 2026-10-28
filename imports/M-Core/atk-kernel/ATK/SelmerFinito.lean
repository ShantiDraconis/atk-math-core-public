import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# ATK — Finitude do grupo de Selmer `K⟮S, n⟯` de um corpo de números

A Mathlib define o grupo de Selmer `K⟮S, n⟯ ⊆ K*/K*ⁿ` de um domínio de Dedekind
(`IsDedekindDomain.selmerGroup`) e deixa como TODO a sua finitude para corpos globais. Este arquivo
prova a finitude para corpos de números:

* `count_spanSingleton`: a ordem de `v` no ideal fracionário `(x)` é `−v(x)` (ponte entre
  `FractionalIdeal.count` e `valuationOfNeZero`);
* `valuationOfNeZeroMod_eq_one_iff`, `mem_selmer_iff`: `[x] ∈ K⟮S, n⟯` sse `n ∣ v(x)` para `v ∉ S`;
* `existe_raiz`: se `n ∣ v(x)` para todo `v`, então `(x) = Iⁿ`;
* `finito_selmer_vazio`: `K⟮∅, n⟯` é finito se `Cl(R)` e `Rˣ/Rˣⁿ` são finitos (a classe de `I`
  determina `[x]` a menos de unidades);
* `finito_selmer`: `K⟮S, n⟯` é finito para `S` finito (valuações em `S` com núcleo `K⟮∅, n⟯`);
* **`selmer_finito`**: para `K` corpo de números, `S` finito e `n > 0`, `K⟮S, n⟯` é finito — pelo
  teorema do número de classes (`NumberField.RingOfIntegers.instFintypeClassGroup`) e pelo teorema
  das unidades de Dirichlet (`Monoid.FG (𝓞 K)ˣ`).

É o ingrediente aritmético do teorema de Mordell–Weil fraco sobre corpos de números.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors NumberField

namespace ATK.SelmerFinito

section Dedekind

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem count_spanSingleton (v : HeightOneSpectrum R) (x : Kˣ) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (x : K)) =
      -Multiplicative.toAdd (v.valuationOfNeZero x) := by
  classical
  have hd : algebraMap R K ((IsLocalization.sec R⁰ (x : K)).2 : R) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (IsLocalization.sec R⁰ (x : K)).2.2
  have hI : FractionalIdeal.spanSingleton R⁰ (x : K) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact x.ne_zero
  have hspec := IsLocalization.sec_spec R⁰ (x : K)
  have haJ : FractionalIdeal.spanSingleton R⁰ (x : K) =
      FractionalIdeal.spanSingleton R⁰ ((algebraMap R K) (IsLocalization.sec R⁰ (x : K)).2)⁻¹ *
        ↑(Ideal.span {(IsLocalization.sec R⁰ (x : K)).1} : Ideal R) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    rw [← hspec]
    field_simp
  rw [FractionalIdeal.count_well_defined K v hI haJ]
  simp only [valuationOfNeZero, MonoidHom.coe_mk, OneHom.coe_mk, valuationOfNeZeroToFun,
    toAdd_ofAdd]
  ring

theorem valuationOfNeZeroMod_eq_one_iff (v : HeightOneSpectrum R) (n : ℕ) (x : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk x) = 1 ↔
      (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x) := by
  rw [← Int.mem_zmultiples_iff]
  erw [valuationOfNeZeroMod, MonoidHom.comp_apply, ← QuotientGroup.coe_mk',
    QuotientGroup.map_mk' (G := Kˣ) (N := MonoidHom.range (powMonoidHom n))]
  show (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative
      (Multiplicative.ofAdd (QuotientAddGroup.mk (s := AddSubgroup.zmultiples (n : ℤ))
        (Multiplicative.toAdd (v.valuationOfNeZero x)))) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff, ofAdd_eq_one, QuotientAddGroup.eq_zero_iff]


/-- **Raiz `n`-ésima do ideal principal**: se todas as valuações de `x` são divisíveis por `n`, então
`(x) = Iⁿ` para um ideal fracionário `I ≠ 0`. -/
theorem existe_raiz {n : ℕ} (hn : 0 < n) (x : Kˣ)
    (hx : ∀ v : HeightOneSpectrum R, (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x)) :
    ∃ I : FractionalIdeal R⁰ K, I ≠ 0 ∧ I ^ n = FractionalIdeal.spanSingleton R⁰ (x : K) := by
  set X := FractionalIdeal.spanSingleton R⁰ (x : K) with hX
  have hX0 : X ≠ 0 := by
    rw [hX, Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact x.ne_zero
  have hdiv : ∀ v, (n : ℤ) ∣ FractionalIdeal.count K v X := by
    intro v; rw [hX, count_spanSingleton]; exact (hx v).neg_right
  set e : HeightOneSpectrum R → ℤ := fun v => FractionalIdeal.count K v X / n with he
  have hfin : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, e v = 0 := by
    filter_upwards [FractionalIdeal.finite_factors X] with v hv
    simp [e, hv]
  have hsupp : (Function.mulSupport fun v : HeightOneSpectrum R =>
      (v.asIdeal : FractionalIdeal R⁰ K) ^ e v).Finite := by
    refine (Filter.eventually_cofinite.mp hfin).subset ?_
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    show ¬e v = 0
    intro he0
    apply hv
    rw [he0, zpow_zero]
  set I := ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ e v with hI
  have hIn : I ^ n = X := by
    rw [hI, finprod_pow hsupp]
    conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hX0]
    apply finprod_congr
    intro v
    rw [← zpow_natCast, ← zpow_mul, he, Int.ediv_mul_cancel (hdiv v)]
  refine ⟨I, ?_, hIn⟩
  intro h0
  rw [h0, zero_pow hn.ne'] at hIn
  exact hX0 hIn.symm

/-- **Finitude por fibras**: se `Φ : G → C` (`C` finito) tem fibras contidas em transladados de um
conjunto finito `T`, então `G` é finito. -/
theorem finito_por_fibras {G C : Type*} [Group G] [Finite C] (Φ : G → C) {T : Set G}
    (hT : T.Finite) (h : ∀ x y, Φ x = Φ y → x⁻¹ * y ∈ T) : Finite G := by
  classical
  let r : C → G := fun c => if hc : ∃ x, Φ x = c then hc.choose else 1
  have hcov : (Set.univ : Set G) ⊆ ⋃ c : C, (fun t => r c * t) '' T := by
    intro y _
    refine Set.mem_iUnion.mpr ⟨Φ y, (r (Φ y))⁻¹ * y, ?_, by simp⟩
    have hc : ∃ x, Φ x = Φ y := ⟨y, rfl⟩
    have hr : r (Φ y) = hc.choose := by simp only [r, hc, dite_true]
    rw [hr]
    exact h _ _ hc.choose_spec
  exact Set.finite_univ_iff.mp ((Set.finite_iUnion fun c => hT.image _).subset hcov)


set_option quotPrecheck false in
local notation K "/ˣ" n => Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range

/-- `K⟮S, n⟯`, o grupo de Selmer da Mathlib. -/
local notation K "⟮" S "," n "⟯" => @selmerGroup _ _ _ K _ _ _ S n

theorem mem_selmer_iff {S : Set (HeightOneSpectrum R)} {n : ℕ} (x : Kˣ) :
    (QuotientGroup.mk x : K /ˣ n) ∈ K⟮S,n⟯ ↔
      ∀ v ∉ S, (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x) := by
  constructor
  · intro h v hv
    exact (valuationOfNeZeroMod_eq_one_iff v n x).mp (h v hv)
  · intro h v hv
    exact (valuationOfNeZeroMod_eq_one_iff v n x).mpr (h v hv)

/-- A imagem de `Rˣ` em `K⟮∅, n⟯` é finita se `Rˣ/Rˣⁿ` é finito. -/
theorem finito_imagem_unidades {n : ℕ} [Fact (0 < n)]
    [Finite (Rˣ ⧸ (powMonoidHom n : Rˣ →* Rˣ).range)] :
    (Set.range (selmerGroup.fromUnit (R := R) (K := K) (n := n))).Finite := by
  have : Finite (selmerGroup.fromUnit (R := R) (K := K) (n := n)).range :=
    Finite.of_equiv _ ((QuotientGroup.quotientMulEquivOfEq
      (selmerGroup.fromUnit_ker (R := R) (K := K) (n := n))).symm.trans
        (QuotientGroup.quotientKerEquivRange _)).toEquiv
  rw [← MonoidHom.coe_range]
  exact Set.toFinite _

/-- **`K⟮∅, n⟯` é finito** se o grupo de classes e `Rˣ/Rˣⁿ` são finitos (`n > 0`): a classe da raiz
`n`-ésima do ideal `(x)` determina `[x]` a menos da imagem de `Rˣ`. -/
theorem finito_selmer_vazio {n : ℕ} (hn : 0 < n) [Finite (ClassGroup R)]
    [Finite (Rˣ ⧸ (powMonoidHom n : Rˣ →* Rˣ).range)] :
    Finite (K⟮(∅ : Set (HeightOneSpectrum R)),n⟯) := by
  classical
  have : Fact (0 < n) := ⟨hn⟩
  have hrep : ∀ z : K⟮(∅ : Set (HeightOneSpectrum R)),n⟯, ∃ (x : Kˣ) (I : FractionalIdeal R⁰ K),
      (QuotientGroup.mk x : K /ˣ n) = z ∧ I ≠ 0 ∧ I ^ n = FractionalIdeal.spanSingleton R⁰ (x : K) := by
    intro z
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (z : K /ˣ n)
    have hz : (QuotientGroup.mk x : K /ˣ n) ∈ K⟮(∅ : Set (HeightOneSpectrum R)),n⟯ := by
      rw [hx]; exact z.2
    have hdiv := (mem_selmer_iff x).mp hz
    obtain ⟨I, hI0, hI⟩ := existe_raiz hn x (fun v => hdiv v (Set.notMem_empty v))
    exact ⟨x, I, hx, hI0, hI⟩
  choose X I hX hI0 hI using hrep
  refine finito_por_fibras (fun z => ClassGroup.mk K (Units.mk0 (I z) (hI0 z)))
    (finito_imagem_unidades (R := R) (K := K) (n := n)) ?_
  intro z₁ z₂ hz
  have h1 : (ClassGroup.mk K (Units.mk0 (I z₁) (hI0 z₁)))⁻¹ *
      ClassGroup.mk K (Units.mk0 (I z₂) (hI0 z₂)) = 1 := by
    rw [hz, inv_mul_cancel]
  rw [← map_inv, ← map_mul, ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨c, hc⟩ := h1
  have hc' : (I z₁)⁻¹ * I z₂ = FractionalIdeal.spanSingleton R⁰ c := by
    rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_spanSingleton, ← hc]
    simp
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [FractionalIdeal.spanSingleton_zero] at hc'
    rcases mul_eq_zero.mp hc' with h | h
    · exact hI0 z₁ (inv_eq_zero.mp h)
    · exact hI0 z₂ h
  have hI₂ : I z₂ = FractionalIdeal.spanSingleton R⁰ c * I z₁ := by
    rw [← hc', mul_comm, ← mul_assoc, mul_inv_cancel₀ (hI0 z₁), one_mul]
  have hpow : FractionalIdeal.spanSingleton R⁰ ((X z₂ : Kˣ) : K) =
      FractionalIdeal.spanSingleton R⁰ (c ^ n * (X z₁ : K)) := by
    rw [← hI z₂, hI₂, mul_pow, hI z₁, FractionalIdeal.spanSingleton_pow,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
  obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp hpow
  rw [Units.smul_def, Algebra.smul_def] at hu
  have hu0 : algebraMap R K (u : R) ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero u.ne_zero))
  have hX2 : ((X z₂ : Kˣ) : K) = c ^ n * (X z₁ : K) / algebraMap R K (u : R) := by
    rw [eq_div_iff hu0, mul_comm, hu]
  refine ⟨u⁻¹, ?_⟩
  apply Subtype.ext
  show (QuotientGroup.mk (Units.map (algebraMap R K).toMonoidHom u⁻¹) : K /ˣ n) = _
  rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hX z₁, ← hX z₂, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul, QuotientGroup.eq]
  refine ⟨Units.mk0 c hc0, ?_⟩
  ext
  simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
    Units.val_mul, Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, map_inv]
  rw [hX2]
  have hx1 : ((X z₁ : Kˣ) : K) ≠ 0 := (X z₁).ne_zero
  field_simp
  simp


/-- **`K⟮S, n⟯` é finito** para `S` finito, se o grupo de classes e `Rˣ/Rˣⁿ` são finitos (`n > 0`):
as valuações em `S` dão um homomorfismo para o grupo finito `(ℤ/n)^S`, cujo núcleo é `K⟮∅, n⟯`. -/
theorem finito_selmer {S : Set (HeightOneSpectrum R)} (hS : S.Finite) {n : ℕ} (hn : 0 < n)
    [Finite (ClassGroup R)] [Finite (Rˣ ⧸ (powMonoidHom n : Rˣ →* Rˣ).range)] :
    Finite (K⟮S,n⟯) := by
  have : NeZero n := ⟨hn.ne'⟩
  have : Finite S := hS.to_subtype
  have h0 : Finite (K⟮(∅ : Set (HeightOneSpectrum R)),n⟯) := finito_selmer_vazio hn
  refine finito_por_fibras (selmerGroup.valuation (R := R) (K := K) (S := S) (n := n))
    (T := ((selmerGroup.valuation (R := R) (K := K) (S := S) (n := n)).ker : Set _)) ?_ ?_
  · have hfin : (Set.range fun w : K⟮(∅ : Set (HeightOneSpectrum R)),n⟯ =>
        (w : K /ˣ n)).Finite := Set.finite_range _
    refine (hfin.preimage (Subtype.val_injective.injOn)).subset ?_
    intro z hz
    rw [SetLike.mem_coe, selmerGroup.valuation_ker_eq, Subgroup.mem_subgroupOf] at hz
    exact ⟨⟨_, hz⟩, rfl⟩
  · intro x y hxy
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]

end Dedekind

/-! ## Corpos de números -/

section CorpoNumeros

variable (K : Type*) [Field K] [NumberField K]

instance finito_unidades_mod {n : ℕ} [NeZero n] :
    Finite ((𝓞 K)ˣ ⧸ (powMonoidHom n : (𝓞 K)ˣ →* (𝓞 K)ˣ).range) := by
  have : Group.FG (𝓞 K)ˣ := Group.fg_iff_monoid_fg.mpr inferInstance
  exact Subgroup.finiteIndex_iff_finite_quotient.mp
    (Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 K)ˣ (NeZero.ne n))

/-- **Finitude do grupo de Selmer** `K⟮S, n⟯` de um corpo de números, para `S` finito e `n > 0`
(o TODO "proofs of finiteness for global fields" de `Mathlib.RingTheory.DedekindDomain.SelmerGroup`,
no caso dos corpos de números): pelo teorema do número de classes e pelo teorema das unidades de
Dirichlet. -/
theorem selmer_finito {S : Set (HeightOneSpectrum (𝓞 K))} (hS : S.Finite) {n : ℕ} (hn : 0 < n) :
    Finite (@selmerGroup (𝓞 K) _ _ K _ _ _ S n) := by
  have : NeZero n := ⟨hn.ne'⟩
  exact finito_selmer hS hn

end CorpoNumeros

end ATK.SelmerFinito

#print axioms ATK.SelmerFinito.count_spanSingleton
#print axioms ATK.SelmerFinito.valuationOfNeZeroMod_eq_one_iff
#print axioms ATK.SelmerFinito.existe_raiz
#print axioms ATK.SelmerFinito.finito_por_fibras
#print axioms ATK.SelmerFinito.mem_selmer_iff
#print axioms ATK.SelmerFinito.finito_imagem_unidades
#print axioms ATK.SelmerFinito.finito_selmer_vazio
#print axioms ATK.SelmerFinito.finito_selmer
#print axioms ATK.SelmerFinito.selmer_finito
