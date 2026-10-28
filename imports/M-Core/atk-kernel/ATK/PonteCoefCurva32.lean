/-
ATK — Ponte P2 para `y² = x³ − x`: da cota de Hasse à cota `|aₙ| ≤ n`.

A ponte P2 de `ATK.AtaqueBSD` (`CotaCoef E`: `|aₙ| ≤ n`) é reduzida aqui ao **conteúdo
definicional** da função L da Mathlib — que os fatores locais são os padrão — usando a cota de
Hasse provada em `ATK.BaseHasseCurva32`:

* `traco p = −Σ_{x ∈ 𝔽_p} χ(x³ − x)` (`= p + 1 − #E(𝔽_p)`) e `hecke a p k`, os coeficientes de
  `1/(1 − aT + pT²)` (`c₀ = 1`, `c₁ = a`, `c_{k+2} = a c_{k+1} − p c_k`);
* **`invariante`**: `c_{k+1}² − a c_{k+1} c_k + p c_k² = p^{k+1}` (a forma quadrática do
  Frobenius é multiplicada por `p` a cada passo);
* **`cota_forma`**: `(4p − a²) c_k² ≤ 4 p^{k+1}`;
* **`cota_hecke`**: para `p ≥ 5`, `a² ≤ 4p` e `a² ≠ 4p`, `|c_k| ≤ p^k`; **`cota_hecke_zero`**:
  com `a = 0`, idem para todo `p ≥ 1`;
* **`traco_tres`**: `a₃ = 0`; **`traco_sq_ne`**: `a_p² ≠ 4p` para `p` primo; com
  **`hasse_curva32`**: **`cota_local`** — `|c_k(a_p, p)| ≤ p^k` para todo primo ímpar `p`;
* `FatoresPadrao` (**ponte P2a, definicional**): `a_{2^k} = 0` (redução aditiva em 2) e
  `a_{p^k} = c_k(a_p, p)` para `p` ímpar, nos coeficientes `WeierstrassCurve.LFunction` da Mathlib;
* **`cotaCoef_de_fatores`**: `FatoresPadrao ⇒ CotaCoef E` (multiplicatividade do produto de Euler);
* **`bsd_posto_curva32_P1`**: BSD (posto) para `y² = x³ − x` módulo P1 (modularidade) e P2a.

P2a não tem conteúdo matemático novo — é o desdobramento das definições da Mathlib (modelo
minimal em `ℤ_p`, redução, contagem de pontos, produto de Euler) — e fica como próximo passo.
-/
import ATK.AtaqueBSD
import ATK.BaseHasseCurva32
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum.Prime

open ATK.LigacaoBSD ATK.LigacaoBSDTestes ATK.AtaqueBSD ATK.BaseHasseCurva32

namespace ATK.PonteCoefCurva32

/-! ### A recursão de Hecke -/

/-- Coeficientes de `1/(1 − aT + pT²)`. -/
def hecke (a p : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => a
  | k + 2 => a * hecke a p (k + 1) - p * hecke a p k

/-- **Invariante**: `c_{k+1}² − a c_{k+1} c_k + p c_k² = p^{k+1}`. -/
theorem invariante (a p : ℤ) (k : ℕ) :
    hecke a p (k + 1) ^ 2 - a * hecke a p (k + 1) * hecke a p k + p * hecke a p k ^ 2 =
      p ^ (k + 1) := by
  induction k with
  | zero =>
    show a ^ 2 - a * a * 1 + p * 1 ^ 2 = p ^ (0 + 1)
    ring
  | succ k ih =>
    show (a * hecke a p (k + 1) - p * hecke a p k) ^ 2 -
        a * (a * hecke a p (k + 1) - p * hecke a p k) * hecke a p (k + 1) +
        p * hecke a p (k + 1) ^ 2 = p ^ (k + 1 + 1)
    rw [pow_succ]
    linear_combination p * ih

/-- **`(4p − a²) c_k² ≤ 4 p^{k+1}`.** -/
theorem cota_forma (a p : ℤ) (k : ℕ) :
    (4 * p - a ^ 2) * hecke a p k ^ 2 ≤ 4 * p ^ (k + 1) := by
  rcases k with _ | k
  · simp [hecke]
    nlinarith [sq_nonneg a]
  · have h := invariante a p k
    have e : 4 * p ^ (k + 1 + 1) =
        (2 * p * hecke a p k - a * hecke a p (k + 1)) ^ 2 +
          (4 * p - a ^ 2) * hecke a p (k + 1) ^ 2 := by
      rw [pow_succ]
      linear_combination (-4 * p) * h
    rw [e]
    nlinarith [sq_nonneg (2 * p * hecke a p k - a * hecke a p (k + 1))]

/-- **`|c_k| ≤ p^k`** para `p ≥ 5`, `a² ≤ 4p`, `a² ≠ 4p`. -/
theorem cota_hecke {a p : ℤ} (hp5 : 5 ≤ p) (ha : a ^ 2 ≤ 4 * p) (hne : a ^ 2 ≠ 4 * p) (k : ℕ) :
    |hecke a p k| ≤ p ^ k := by
  have hp0 : (0 : ℤ) ≤ p := by linarith
  have h1 : 1 ≤ 4 * p - a ^ 2 := by
    have : a ^ 2 < 4 * p := lt_of_le_of_ne ha hne
    linarith
  have hsq : hecke a p k ^ 2 ≤ (p ^ k) ^ 2 := by
    rcases k with _ | _ | j
    · simp [hecke]
    · show a ^ 2 ≤ (p ^ 1) ^ 2
      rw [pow_one]
      nlinarith
    · have hf := cota_forma a p (j + 2)
      have hc : hecke a p (j + 2) ^ 2 ≤ 4 * p ^ (j + 2 + 1) := by
        nlinarith [sq_nonneg (hecke a p (j + 2))]
      have hpj : 4 ≤ p ^ (j + 1) := by
        have : p ≤ p ^ (j + 1) := le_self_pow₀ (by linarith) (Nat.succ_ne_zero j)
        linarith
      have e : (p ^ (j + 2)) ^ 2 = p ^ (j + 2 + 1) * p ^ (j + 1) := by ring
      rw [e]
      have hpos : 0 ≤ p ^ (j + 2 + 1) := pow_nonneg hp0 _
      nlinarith
  have := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (pow_nonneg hp0 k)] at this

/-- Com `a = 0`: `|c_k| ≤ p^k` para todo `p ≥ 1`. -/
theorem cota_hecke_zero {p : ℤ} (hp1 : 1 ≤ p) (k : ℕ) : |hecke 0 p k| ≤ p ^ k := by
  have hp0 : (0 : ℤ) ≤ p := by linarith
  have hf := cota_forma 0 p k
  have h4 : hecke 0 p k ^ 2 ≤ p ^ k := by
    have : 4 * p * hecke 0 p k ^ 2 ≤ 4 * p * p ^ k := by
      rw [show 4 * p * p ^ k = 4 * p ^ (k + 1) by ring]
      simpa using hf
    have hp4 : 0 < 4 * p := by linarith
    exact le_of_mul_le_mul_left this hp4
  have hpk : p ^ k ≤ (p ^ k) ^ 2 := by
    have : 1 ≤ p ^ k := one_le_pow₀ hp1
    nlinarith
  have := sq_le_sq.mp (h4.trans hpk)
  rwa [abs_of_nonneg (pow_nonneg hp0 k)] at this

/-! ### O traço de Frobenius da curva -/

/-- `a_p = −Σ_{x ∈ 𝔽_p} χ(x³ − x)`. -/
noncomputable def traco (p : ℕ) [Fact p.Prime] : ℤ :=
  -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - x)

/-- `a₃ = 0` (em `𝔽₃`, `x³ = x`). -/
theorem traco_tres : @traco 3 ⟨Nat.prime_three⟩ = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  unfold traco
  have h : ∀ x : ZMod 3, x ^ 3 - x = 0 := fun x => by rw [ZMod.pow_card, sub_self]
  simp [h]

/-- **`a_p² ≠ 4p`** para `p` primo. -/
theorem sq_ne_quatro_p {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (a : ℤ) : a ^ 2 ≠ 4 * (p : ℤ) := by
  intro h
  have hn : a.natAbs ^ 2 = 4 * p := by
    have : ((a.natAbs ^ 2 : ℕ) : ℤ) = ((4 * p : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs]
      exact h
    exact_mod_cast this
  have h1 : p ∣ a.natAbs ^ 2 := ⟨4, by rw [hn]; ring⟩
  have h2 : p ∣ a.natAbs := hp.dvd_of_dvd_pow h1
  obtain ⟨m, hm⟩ := h2
  rw [hm] at hn
  have h3 : p * (p * m ^ 2) = p * 4 := by
    calc p * (p * m ^ 2) = (p * m) ^ 2 := by ring
      _ = 4 * p := hn
      _ = p * 4 := by ring
  have h4 : p * m ^ 2 = 4 := Nat.eq_of_mul_eq_mul_left hp.pos h3
  have h5 : p ∣ 4 := ⟨m ^ 2, h4.symm⟩
  have := Nat.le_of_dvd (by norm_num) h5
  omega

/-- **Cota local**: `|c_k(a_p, p)| ≤ p^k` para todo primo ímpar `p`. -/
theorem cota_local (p : ℕ) [hp : Fact p.Prime] (h2 : p ≠ 2) (k : ℕ) :
    |hecke (traco p) p k| ≤ (p : ℤ) ^ k := by
  have hpr := hp.out
  rcases Nat.lt_or_ge p 5 with hlt | hge
  · -- `p = 3`
    have h3 : p = 3 := by
      have := hpr.two_le
      interval_cases p
      · exact absurd rfl h2
      · rfl
      · exact absurd hpr (by norm_num)
    subst h3
    have ht : traco 3 = 0 := traco_tres
    rw [ht]
    exact cota_hecke_zero (by norm_num) k
  · have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact h2
    have hH := hasse_curva32 (F := ZMod p) hF
    rw [ZMod.card] at hH
    have ha : traco p ^ 2 ≤ 4 * (p : ℤ) := by
      unfold traco
      rw [neg_sq]
      exact hH
    exact cota_hecke (by exact_mod_cast hge) ha (sq_ne_quatro_p hpr hge _) k

/-! ### A ponte definicional P2a e a cota `|aₙ| ≤ n` -/

/-- **Ponte P2a**: os coeficientes da função L da Mathlib para `y² = x³ − x` são os padrão. -/
def FatoresPadrao : Prop :=
  (∀ k : ℕ, 1 ≤ k → ATK.CongruentCurve.E.LFunction (2 ^ k) = 0) ∧
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ k : ℕ,
    ATK.CongruentCurve.E.LFunction (p ^ k) = hecke (traco p) p k

/-- A função L da Mathlib é multiplicativa. -/
theorem lfun_mult (W : WeierstrassCurve ℚ) : W.LFunction.IsMultiplicative := by
  unfold WeierstrassCurve.LFunction
  exact ArithmeticFunction.isMultiplicative_eulerProduct _ fun _ => fator_multiplicativo _ _

/-- Sob P2a, `|a_{p^k}| ≤ p^k` para todo primo `p` e `k ≥ 1`. -/
theorem cota_pot (hF : FatoresPadrao) {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k) :
    |ATK.CongruentCurve.E.LFunction (p ^ k)| ≤ (p : ℤ) ^ k := by
  by_cases h2 : p = 2
  · subst h2
    rw [hF.1 k hk, abs_zero]
    positivity
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [hF.2 p h2 k]
    exact cota_local p h2 k

/-- **`FatoresPadrao ⇒ |aₙ| ≤ n`.** -/
theorem cota_inteira (hF : FatoresPadrao) (n : ℕ) :
    |ATK.CongruentCurve.E.LFunction n| ≤ (n : ℤ) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp
  · have hn0 : n ≠ 0 := hn.ne'
    rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _ (lfun_mult _) hn0]
    unfold Finsupp.prod
    rw [Finset.abs_prod]
    calc ∏ p ∈ n.factorization.support,
          |ATK.CongruentCurve.E.LFunction (p ^ n.factorization p)|
        ≤ ∏ p ∈ n.factorization.support, (p : ℤ) ^ n.factorization p := by
          refine Finset.prod_le_prod₀ (fun p _ => abs_nonneg _) (fun p hp => ?_)
          have hpr : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
          have hk : 1 ≤ n.factorization p := Nat.one_le_iff_ne_zero.mpr
            (Finsupp.mem_support_iff.mp hp)
          exact cota_pot hF hpr hk
      _ = (n : ℤ) := by
          have := Nat.prod_factorization_pow_eq_self hn0
          unfold Finsupp.prod at this
          exact_mod_cast this

/-- **`FatoresPadrao ⇒ CotaCoef E`** (a ponte P2 de `ATK.AtaqueBSD`). -/
theorem cotaCoef_de_fatores (hF : FatoresPadrao) : CotaCoef ATK.CongruentCurve.E := by
  intro n
  rw [coef, Complex.norm_intCast]
  exact_mod_cast cota_inteira hF n

/-- **BSD (posto) para `y² = x³ − x` módulo P1 (modularidade) e P2a (definicional).** -/
theorem bsd_posto_curva32_P1 (hM : PonteModular ATK.CongruentCurve.E c32 1)
    (hF : FatoresPadrao) {G : ℂ → ℂ} (hG : Continuacao ATK.CongruentCurve.E G) :
    G 1 ≠ 0 ∧ analyticOrderAt G 1 = postoMW ATK.CongruentCurve.E :=
  bsd_posto_curva32 hM (cotaCoef_de_fatores hF) hG

end ATK.PonteCoefCurva32

#print axioms ATK.PonteCoefCurva32.invariante
#print axioms ATK.PonteCoefCurva32.cota_forma
#print axioms ATK.PonteCoefCurva32.cota_hecke
#print axioms ATK.PonteCoefCurva32.cota_hecke_zero
#print axioms ATK.PonteCoefCurva32.traco_tres
#print axioms ATK.PonteCoefCurva32.sq_ne_quatro_p
#print axioms ATK.PonteCoefCurva32.cota_local
#print axioms ATK.PonteCoefCurva32.lfun_mult
#print axioms ATK.PonteCoefCurva32.cota_pot
#print axioms ATK.PonteCoefCurva32.cota_inteira
#print axioms ATK.PonteCoefCurva32.cotaCoef_de_fatores
#print axioms ATK.PonteCoefCurva32.bsd_posto_curva32_P1
