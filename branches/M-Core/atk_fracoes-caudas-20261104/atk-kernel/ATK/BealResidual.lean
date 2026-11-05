import ATK.BealReduction
import ATK.BealPartial

/-!
# ATK — O domínio residual exato de Beal, incondicionalmente

Combinando a redução primitiva (`ATK.BealReduction`) com os casos FLT(3)/FLT(4) da Mathlib
(`ATK.BealPartial`), o kernel prova que **Beal é equivalente** a excluir apenas as soluções

* com `a, b` coprimos (logo dois a dois coprimas), e
* cujo `g = mdc(x, y, z)` **não** é divisível por 3 **nem** por 4.

Nenhuma ponte (nem FLT geral) é usada. Este é o conjunto residual exato que a obrigação O2 ainda
precisa excluir; nada aqui o exclui.
-/

namespace ATK.BealResidual

open ATK.Conditional.Beal ATK.BealReduction ATK.BealPartial

/-- Exclusão residual: primitiva e com `3 ∤ mdc(x,y,z)`, `4 ∤ mdc(x,y,z)`. -/
def ExclusaoResidual : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    ¬ 3 ∣ Nat.gcd x (Nat.gcd y z) → ¬ 4 ∣ Nat.gcd x (Nat.gcd y z) →
    Nat.Coprime a b → a ^ x + b ^ y ≠ c ^ z

/-- Sem solução quando 3 ou 4 divide `mdc(x, y, z)` (forma direta). -/
theorem sem_solucao_mdc {a b c x y z : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 3 ∣ Nat.gcd x (Nat.gcd y z) ∨ 4 ∣ Nat.gcd x (Nat.gcd y z)) :
    a ^ x + b ^ y ≠ c ^ z := by
  have hx : ∀ d, d ∣ Nat.gcd x (Nat.gcd y z) → d ∣ x := fun d hd => hd.trans (Nat.gcd_dvd_left _ _)
  have hy : ∀ d, d ∣ Nat.gcd x (Nat.gcd y z) → d ∣ y :=
    fun d hd => hd.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))
  have hz : ∀ d, d ∣ Nat.gcd x (Nat.gcd y z) → d ∣ z :=
    fun d hd => hd.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
  rcases h with h | h
  · exact sem_solucao_de_flt_divisor fermatLastTheoremThree (hx 3 h) (hy 3 h) (hz 3 h) ha hb hc
  · exact sem_solucao_de_flt_divisor fermatLastTheoremFour (hx 4 h) (hy 4 h) (hz 4 h) ha hb hc

/-- **Beal ⟺ exclusão residual** (incondicional, sem pontes). -/
theorem beal_iff_residual : BealConjecture ↔ ExclusaoResidual := by
  rw [beal_iff_primitive]
  constructor
  · intro h a b c x y z ha hb hc hx hy hz _ _ hab
    exact h a b c x y z ha hb hc hx hy hz hab
  · intro h a b c x y z ha hb hc hx hy hz hab
    by_cases h34 : 3 ∣ Nat.gcd x (Nat.gcd y z) ∨ 4 ∣ Nat.gcd x (Nat.gcd y z)
    · exact sem_solucao_mdc ha hb hc h34
    · have h34' := not_or.mp h34
      exact h a b c x y z ha hb hc hx hy hz h34'.1 h34'.2 hab

/-- Forma dois a dois coprima do residual. -/
def ExclusaoResidualPairwise : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    ¬ 3 ∣ Nat.gcd x (Nat.gcd y z) → ¬ 4 ∣ Nat.gcd x (Nat.gcd y z) →
    Nat.Coprime a b → Nat.Coprime a c → Nat.Coprime b c → a ^ x + b ^ y ≠ c ^ z

theorem residual_iff_pairwise : ExclusaoResidual ↔ ExclusaoResidualPairwise := by
  constructor
  · intro h a b c x y z ha hb hc hx hy hz h3 h4 hab _ _
    exact h a b c x y z ha hb hc hx hy hz h3 h4 hab
  · intro h a b c x y z ha hb hc hx hy hz h3 h4 hab heq
    exact h a b c x y z ha hb hc hx hy hz h3 h4 hab
      (coprime_ac_de_ab (by omega) (by omega) heq hab)
      (coprime_bc_de_ab (by omega) (by omega) heq hab) heq

/-- **Beal ⟺ nenhuma solução dois a dois coprima com `3 ∤ g`, `4 ∤ g`** (`g = mdc(x,y,z)`). -/
theorem beal_iff_residual_pairwise : BealConjecture ↔ ExclusaoResidualPairwise :=
  beal_iff_residual.trans residual_iff_pairwise

/-- Teste: `(10, 14, 22)` tem `mdc = 2` e está no residual (não é coberto por FLT(3)/FLT(4)). -/
theorem exemplo_residual : ¬ 3 ∣ Nat.gcd 10 (Nat.gcd 14 22) ∧ ¬ 4 ∣ Nat.gcd 10 (Nat.gcd 14 22) := by
  decide

end ATK.BealResidual

#print axioms ATK.BealResidual.sem_solucao_mdc
#print axioms ATK.BealResidual.beal_iff_residual
#print axioms ATK.BealResidual.residual_iff_pairwise
#print axioms ATK.BealResidual.beal_iff_residual_pairwise
#print axioms ATK.BealResidual.exemplo_residual
