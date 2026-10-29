import Mathlib

/-!
# ATK — "horizon prime": o que pode ser defendido no kernel

A ideia "existe um primo em algum lugar do infinito que normaliza" tem três versões precisas.
Todas estão verificadas aqui; nenhuma prova uma conjectura do milênio.

1. **Horizonte em ℕ.** Não existe um último primo (`no_last_prime`). "A partir de um horizonte H, todo
   primo tem a propriedade Q" equivale a "só finitos primos falham" (`hasHorizon_iff_finite`).

2. **O primo no infinito da teoria dos números (lugar arquimediano).** Pelo teorema de Ostrowski, os
   valores absolutos de ℚ são os p-ádicos e um único outro, o usual, chamado "primo no infinito"
   (`ostrowski`, `infinity_is_not_a_finite_prime`, `exactly_one_place_at_infinity`). Ele é exatamente o que
   NORMALIZA a fórmula do produto: |x|·∏_p |x|_p = 1 (`product_formula_rat`). Exemplo: para x = 6, os primos
   finitos dão 1/6 e o primo no infinito dá 6 (`finite_primes_alone`, `normalization_example`).

3. **Primo hiperfinito (análise não standard).** Na ultrapotência ℕ* = ℕ^ℕ/U existe um primo maior que todo
   número natural: a classe da sequência 2, 3, 5, 7, … (`horizonPrime_isPrime`, `horizonPrime_beyond`).
   Mas toda propriedade que ele tem vale para infinitos primos comuns (`horizon_transfer`): ele não sabe
   nada que os primos finitos não saibam. Por isso não pode, sozinho, resolver uma conjectura.

4. **O primo no infinito em ζ.** O fator local de ζ no primo infinito é Γ_ℝ(s) = π^(−s/2)Γ(s/2); com ele,
   Λ(s) = Γ_ℝ(s)ζ(s) satisfaz Λ(1 − s) = Λ(s) (`completed_zeta_symmetric`). É essa normalização que põe a
   reta crítica Re s = 1/2 no centro da simetria. A simetria é teorema; a RH continua aberta.

O que NÃO é defensável: que um primo "normalize" os infinitos encontrados em Navier–Stokes (itens 19–21).
Aqueles vêm de mudança de escala contínua (λ ∈ ℝ), não de aritmética; a normalização correta ali é por
normas críticas invariantes por escala (teoria de dados pequenos de Fujita–Kato), e dados grandes seguem
abertos.
-/

namespace ATK.Horizon

open Filter NumberField

/-! ## 1. Horizonte em ℕ -/

/-- Não existe último primo: acima de qualquer horizonte há outro primo. -/
theorem no_last_prime (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
  Nat.exists_infinite_primes n

/-- `Q` tem horizonte: a partir de `H`, todo primo satisfaz `Q`. -/
def HasHorizon (Q : ℕ → Prop) : Prop :=
  ∃ H : ℕ, ∀ p, p.Prime → H < p → Q p

/-- Ter horizonte é exatamente ter só finitas exceções entre os primos. -/
theorem hasHorizon_iff_finite (Q : ℕ → Prop) :
    HasHorizon Q ↔ {p | p.Prime ∧ ¬ Q p}.Finite := by
  constructor
  · rintro ⟨H, hH⟩
    apply (Set.finite_Iic H).subset
    rintro p ⟨hp, hq⟩
    rw [Set.mem_Iic]
    by_contra hlt
    exact hq (hH p hp (not_le.mp hlt))
  · intro hfin
    obtain ⟨H, hH⟩ := hfin.bddAbove
    refine ⟨H, fun p hp hHp => ?_⟩
    by_contra hq
    exact absurd (hH (show p ∈ {p | p.Prime ∧ ¬ Q p} from ⟨hp, hq⟩)) (not_le.mpr hHp)

/-! ## 2. O primo no infinito (lugar arquimediano) -/

/-- Ostrowski: todo valor absoluto não trivial de ℚ é o usual ("∞") ou um p-ádico. -/
theorem ostrowski (f : AbsoluteValue ℚ ℝ) (hf : f.IsNontrivial) :
    f ≈ Rat.AbsoluteValue.real ∨ ∃! p, ∃ (_ : Fact p.Prime), f ≈ Rat.AbsoluteValue.padic p :=
  Rat.AbsoluteValue.equiv_real_or_padic f hf

/-- O primo no infinito não é nenhum primo finito. -/
theorem infinity_is_not_a_finite_prime (p : ℕ) [Fact p.Prime] :
    ¬ Rat.AbsoluteValue.real.IsEquiv (Rat.AbsoluteValue.padic p) :=
  Rat.AbsoluteValue.not_real_isEquiv_padic p

/-- ℚ tem exatamente um lugar no infinito, e ele é o valor absoluto usual. -/
theorem exactly_one_place_at_infinity :
    Nonempty (Unique (InfinitePlace ℚ)) ∧ ∀ (v : InfinitePlace ℚ) (x : ℚ), v x = |(x : ℝ)| :=
  ⟨⟨inferInstance⟩, fun v x => by simp⟩

/-- Fórmula do produto para ℚ: o primo no infinito normaliza os primos finitos. -/
theorem product_formula_rat (x : ℚ) (hx : x ≠ 0) :
    |(x : ℝ)| * ∏ᶠ w : FinitePlace ℚ, w x = 1 := by
  have h := NumberField.prod_abs_eq_one hx
  have hm : (Rat.infinitePlace).mult = 1 := by
    unfold NumberField.InfinitePlace.mult
    exact if_pos Rat.isReal_infinitePlace
  have hu : ∀ w : InfinitePlace ℚ, w = Rat.infinitePlace := fun w => Subsingleton.elim _ _
  have hprod : (∏ w : InfinitePlace ℚ, w x ^ w.mult) = |(x : ℝ)| := by
    rw [Fintype.prod_unique, hu default, hm, pow_one]
    simp
  rw [hprod] at h
  exact h

/-- Para x = 6, só os primos finitos dão 1/6: sem o primo no infinito não há normalização. -/
theorem finite_primes_alone : padicNorm 2 (6 : ℚ) * padicNorm 3 (6 : ℚ) = 6⁻¹ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have a22 : padicNorm 2 (2 : ℚ) = 2⁻¹ := by simpa using padicNorm.padicNorm_p_of_prime (p := 2)
  have a33 : padicNorm 3 (3 : ℚ) = 3⁻¹ := by simpa using padicNorm.padicNorm_p_of_prime (p := 3)
  have a23 : padicNorm 2 (3 : ℚ) = 1 := by
    simpa using padicNorm.padicNorm_of_prime_of_ne (p := 2) (q := 3) (by norm_num)
  have a32 : padicNorm 3 (2 : ℚ) = 1 := by
    simpa using padicNorm.padicNorm_of_prime_of_ne (p := 3) (q := 2) (by norm_num)
  have e : (6 : ℚ) = 2 * 3 := by norm_num
  rw [e, padicNorm.mul, padicNorm.mul, a22, a33, a23, a32]
  norm_num

/-- Com o primo no infinito (|6| = 6) o produto fecha em 1. -/
theorem normalization_example : |(6 : ℚ)| * (padicNorm 2 (6 : ℚ) * padicNorm 3 (6 : ℚ)) = 1 := by
  rw [finite_primes_alone]
  norm_num

/-! ## 3. Primo hiperfinito (análise não standard) -/

/-- ℕ* = sequências de naturais módulo um ultrafiltro livre (o hiperfiltro). -/
abbrev StarNat : Type := Germ ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ) ℕ

/-- O "horizon prime": a classe da sequência dos primos 2, 3, 5, 7, 11, … -/
noncomputable def horizonPrime : StarNat := ((fun n : ℕ => Nat.nth Nat.Prime n) : StarNat)

/-- Ele é primo (no sentido de ℕ*). -/
theorem horizonPrime_isPrime : Germ.LiftPred Nat.Prime horizonPrime :=
  Germ.liftPred_coe.2 (Eventually.of_forall fun n => Nat.prime_nth_prime n)

/-- Ele é maior que todo número natural: está "além do horizonte". -/
theorem horizonPrime_beyond (m : ℕ) : (m : StarNat) < horizonPrime := by
  have h : ∀ᶠ n in (atTop : Filter ℕ), m < Nat.nth Nat.Prime n :=
    (eventually_ge_atTop m).mono fun n hn => by
      have := Nat.add_two_le_nth_prime n
      omega
  have h' : ∀ᶠ n in ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ), m < Nat.nth Nat.Prime n :=
    h.filter_mono Nat.hyperfilter_le_atTop
  exact Germ.coe_lt.2 h'

/-- Transferência: toda propriedade do horizon prime vale para infinitos primos comuns.
Logo ele não traz informação nova sobre os primos finitos. -/
theorem horizon_transfer (Q : ℕ → Prop) (h : Germ.LiftPred Q horizonPrime) :
    {p | p.Prime ∧ Q p}.Infinite := by
  have hs : ∀ᶠ n in ((hyperfilter ℕ : Ultrafilter ℕ) : Filter ℕ), Q (Nat.nth Nat.Prime n) :=
    Germ.liftPred_coe.1 h
  have hinf : {n | Q (Nat.nth Nat.Prime n)}.Infinite := fun hfin =>
    notMem_hyperfilter_of_finite hfin hs
  have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have himg : (Nat.nth Nat.Prime '' {n | Q (Nat.nth Nat.Prime n)}).Infinite :=
    (Set.infinite_image_iff (fun _ _ _ _ hab => hmono.injective hab)).2 hinf
  refine Set.Infinite.mono ?_ himg
  rintro _ ⟨n, hn, rfl⟩
  exact ⟨Nat.prime_nth_prime n, hn⟩

/-! ## 4. O primo no infinito em ζ: o fator Γ_ℝ torna a equação funcional exata -/

/-- ζ(s) = Λ(s) / Γ_ℝ(s), com Γ_ℝ(s) = π^(−s/2)·Γ(s/2) o fator local no primo infinito. -/
theorem zeta_eq_completed_div_infinite_factor {s : ℂ} (hs : s ≠ 0) :
    riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s :=
  riemannZeta_def_of_ne_zero hs

/-- Com o fator do primo no infinito incluído, Λ(1 − s) = Λ(s): simetria em torno da reta crítica
Re s = 1/2. (A simetria é teorema; que os zeros estejam NA reta é a hipótese de Riemann, aberta.) -/
theorem completed_zeta_symmetric (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

end ATK.Horizon

#print axioms ATK.Horizon.no_last_prime
#print axioms ATK.Horizon.hasHorizon_iff_finite
#print axioms ATK.Horizon.ostrowski
#print axioms ATK.Horizon.infinity_is_not_a_finite_prime
#print axioms ATK.Horizon.exactly_one_place_at_infinity
#print axioms ATK.Horizon.product_formula_rat
#print axioms ATK.Horizon.finite_primes_alone
#print axioms ATK.Horizon.normalization_example
#print axioms ATK.Horizon.horizonPrime_isPrime
#print axioms ATK.Horizon.horizonPrime_beyond
#print axioms ATK.Horizon.horizon_transfer
#print axioms ATK.Horizon.zeta_eq_completed_div_infinite_factor
#print axioms ATK.Horizon.completed_zeta_symmetric
