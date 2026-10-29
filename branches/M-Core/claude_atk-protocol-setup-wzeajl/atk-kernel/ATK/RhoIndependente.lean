/-
ATK-RH — Independência linear da família ρ_m(x) = {1/(mx)} − (1/m){1/x}, m ≥ 2.

Resultado: a família é linearmente independente, e a prova usa só aritmética de
piso.  Fato central (teorema `rho_eq_step`): em (0,1], ρ_m(x) = {⌊1/x⌋/m}, ou seja,
cada ρ_m é uma função escada cujos degraus são os intervalos (1/(k+1), 1/k].
Logo uma combinação finita F = Σ c_m ρ_m é constante igual a S_k := Σ c_m {k/m} em
cada degrau, e F = 0 em um ponto de cada degrau já força c = 0 (`coeffs_eq_zero`).

Nenhum `sorry`, nenhum axioma novo.  Não há nada aqui sobre a hipótese de Riemann:
a estimativa angular (captura de χ pelo espaço gerado) continua em aberto.
-/
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace ATK.RhoIndependente

open Finset Int

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- O gerador ρ_m. -/
noncomputable def rho (m : ℕ) (x : K) : K :=
  fract (1 / (m * x)) - (1 / m) * fract (1 / x)

/-- O valor de Σ c_m ρ_m no degrau de índice k. -/
noncomputable def stepVal (I : Finset ℕ) (c : ℕ → K) (k : ℕ) : K :=
  ∑ m ∈ I, c m * fract ((k : K) / m)

/-- Soma dos coeficientes dos índices que dividem k. -/
noncomputable def divSum (I : Finset ℕ) (c : ℕ → K) (k : ℕ) : K :=
  ∑ m ∈ I, if m ∣ k then c m else 0

/-! ### Estrutura de escada -/

/-- Em x > 0, ρ_m(x) = {⌊1/x⌋ / m}. -/
theorem rho_eq_step (m : ℕ) (hm : 1 ≤ m) {x : K} (hx : 0 < x) :
    rho m x = fract (((⌊1 / x⌋ : ℤ) : K) / m) := by
  have hm' : (m : K) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  have hx' : x ≠ 0 := hx.ne'
  have h1 : 1 / (m * x) = (1 / x) / m := by field_simp
  have e1 : fract ((1 / x) / m) = (1 / x) / m - ((⌊1 / x⌋ / (m : ℤ) : ℤ) : K) := by
    rw [fract, floor_div_natCast]
  have e2 : fract (((⌊1 / x⌋ : ℤ) : K) / m)
      = ((⌊1 / x⌋ : ℤ) : K) / m - ((⌊1 / x⌋ / (m : ℤ) : ℤ) : K) := by
    rw [fract, floor_div_natCast, floor_intCast]
  have e3 : fract (1 / x) = 1 / x - ((⌊1 / x⌋ : ℤ) : K) := rfl
  unfold rho
  rw [h1, e1, e3, e2]
  ring

/-- Nos pontos 1/k, k ≥ 1, ρ_m vale {k/m}. -/
theorem rho_inv_nat (m k : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    rho m (1 / (k : K)) = fract ((k : K) / m) := by
  have hk' : (0 : K) < k := by exact_mod_cast hk
  rw [rho_eq_step m hm (by positivity)]
  rw [one_div_one_div, floor_natCast, Int.cast_natCast]

/-- A combinação Σ c_m ρ_m é constante em cada degrau (1/(k+1), 1/k]: vale `stepVal` em ⌊1/x⌋₊. -/
theorem sum_rho_eq_stepVal (I : Finset ℕ) (c : ℕ → K) (hI : ∀ m ∈ I, 1 ≤ m)
    {x : K} (hx0 : 0 < x) :
    ∑ m ∈ I, c m * rho m x = stepVal I c ⌊1 / x⌋₊ := by
  unfold stepVal
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [rho_eq_step m (hI m hm) hx0]
  have ht : (0 : K) ≤ 1 / x := by positivity
  rw [← Int.natCast_floor_eq_floor ht, Int.cast_natCast]

/-- Cada ρ_m é limitado: −1/m < ρ_m(x) < 1.  Em particular ρ_m ∈ L²(0,1). -/
theorem rho_bounds (m : ℕ) (hm : 1 ≤ m) (x : K) :
    -(1 / m) < rho m x ∧ rho m x < 1 := by
  have hmK : (0 : K) < m := by exact_mod_cast hm
  have h1 := fract_nonneg (1 / (m * x))
  have h2 := fract_lt_one (1 / (m * x))
  have h3 := fract_nonneg (1 / x)
  have h4 := fract_lt_one (1 / x)
  have h5 : 0 < 1 / (m : K) := by positivity
  have h6 : (1 / (m : K)) * fract (1 / x) < 1 / m * 1 := by
    exact mul_lt_mul_of_pos_left h4 h5
  have h7 : 0 ≤ (1 / (m : K)) * fract (1 / x) := by positivity
  have h8 : 1 / (m : K) ≤ 1 := by rw [div_le_one hmK]; exact_mod_cast hm
  unfold rho
  constructor <;> nlinarith

/-! ### O salto entre degraus consecutivos -/

/-- {(n+1)/m} − {n/m} = 1/m − [m ∣ n+1], para m ≥ 2. -/
theorem fract_succ_div_sub (m n : ℕ) (hm : 2 ≤ m) :
    fract (((n + 1 : ℕ) : K) / m) - fract ((n : K) / m)
      = 1 / m - (if m ∣ n + 1 then 1 else 0) := by
  have hm0 : 0 < m := by omega
  have hmK : (0 : K) < m := by exact_mod_cast hm0
  rw [fract_div_natCast_eq_div_natCast_mod, fract_div_natCast_eq_div_natCast_mod]
  have hmod : (n + 1) % m = (n % m + 1) % m := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt (a := 1) (by omega)]
  have hr : n % m < m := Nat.mod_lt n hm0
  by_cases h : n % m + 1 < m
  · -- sem acarreto: (n+1) % m = n % m + 1, e m ∤ n+1
    have h2 : (n + 1) % m = n % m + 1 := by rw [hmod, Nat.mod_eq_of_lt h]
    have hnd : ¬ m ∣ n + 1 := by
      rw [Nat.dvd_iff_mod_eq_zero, h2]; omega
    rw [if_neg hnd, h2]
    push_cast
    field_simp
    ring
  · -- acarreto: n % m = m − 1, (n+1) % m = 0, m ∣ n+1
    have h3 : n % m + 1 = m := by omega
    have h2 : (n + 1) % m = 0 := by rw [hmod, h3, Nat.mod_self]
    have hd : m ∣ n + 1 := Nat.dvd_of_mod_eq_zero h2
    rw [if_pos hd, h2]
    have hcast : ((n % m : ℕ) : K) = (m : K) - 1 := by
      have : n % m = m - 1 := by omega
      rw [this, Nat.cast_sub (by omega)]
      simp
    rw [hcast]
    push_cast
    field_simp
    ring

/-- stepVal (n+1) − stepVal n = A − divSum (n+1), com A = Σ c_m / m. -/
theorem stepVal_succ_sub (I : Finset ℕ) (c : ℕ → K) (hI : ∀ m ∈ I, 2 ≤ m) (n : ℕ) :
    stepVal I c (n + 1) - stepVal I c n
      = (∑ m ∈ I, c m / m) - divSum I c (n + 1) := by
  unfold stepVal divSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have := fract_succ_div_sub (K := K) m n (hI m hm)
  rw [← mul_sub, this]
  split_ifs <;> ring

/-! ### Teorema principal -/

/-- Se Σ c_m {k/m} = 0 para todo k, então todos os c_m (m ∈ I, m ≥ 2) são zero. -/
theorem coeffs_eq_zero_of_stepVal (I : Finset ℕ) (c : ℕ → K) (hI : ∀ m ∈ I, 2 ≤ m)
    (h : ∀ k : ℕ, stepVal I c k = 0) : ∀ m ∈ I, c m = 0 := by
  -- divSum (n+1) = A para todo n
  have hA : ∀ n : ℕ, divSum I c (n + 1) = ∑ m ∈ I, c m / m := by
    intro n
    have := stepVal_succ_sub I c hI n
    rw [h (n + 1), h n] at this
    linarith
  -- divSum 1 = 0, porque nenhum m ≥ 2 divide 1
  have h1 : divSum I c 1 = 0 := by
    unfold divSum
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [if_neg]
    intro hd
    have := Nat.le_of_dvd one_pos hd
    have := hI m hm
    omega
  have hA0 : ∑ m ∈ I, c m / m = 0 := by rw [← hA 0]; exact h1
  have hdiv : ∀ k : ℕ, 1 ≤ k → divSum I c k = 0 := by
    intro k hk
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [hA n, hA0]
  -- indução forte em m
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hpos : 1 ≤ m := by have := hI m hm; omega
    have hd := hdiv m hpos
    unfold divSum at hd
    rw [Finset.sum_eq_single m] at hd
    · simpa using hd
    · intro m' hm' hne
      by_cases hdm : m' ∣ m
      · rw [if_pos hdm]
        have hlt : m' < m := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdm) hne
        exact ih m' hlt hm'
      · rw [if_neg hdm]
    · intro habs; exact absurd hm habs

/-- Versão pontual: se Σ c_m ρ_m(x) = 0 em todo x ∈ (0,1], então c = 0 em I. -/
theorem coeffs_eq_zero (I : Finset ℕ) (c : ℕ → K) (hI : ∀ m ∈ I, 2 ≤ m)
    (h : ∀ x : K, 0 < x → x ≤ 1 → ∑ m ∈ I, c m * rho m x = 0) : ∀ m ∈ I, c m = 0 := by
  apply coeffs_eq_zero_of_stepVal I c hI
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · unfold stepVal; simp
  · have hk' : (0 : K) < k := by exact_mod_cast hk
    have := h (1 / (k : K)) (by positivity) (by
      rw [div_le_one hk']; exact_mod_cast hk)
    rw [← this]
    unfold stepVal
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [rho_inv_nat m k (by have := hI m hm; omega) hk]

/-- Basta anular nos pontos 1/k, k ≥ 1. -/
theorem coeffs_eq_zero_of_points (I : Finset ℕ) (c : ℕ → K) (hI : ∀ m ∈ I, 2 ≤ m)
    (h : ∀ k : ℕ, 1 ≤ k → ∑ m ∈ I, c m * rho m (1 / (k : K)) = 0) : ∀ m ∈ I, c m = 0 := by
  apply coeffs_eq_zero_of_stepVal I c hI
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · unfold stepVal; simp
  · rw [← h k hk]
    unfold stepVal
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [rho_inv_nat m k (by have := hI m hm; omega) hk]

/-! ### Independência linear no sentido da Mathlib -/

/-- ρ_m como função em (0,1], indexada por m ≥ 2. -/
noncomputable def rhoFun (m : {m : ℕ // 2 ≤ m}) : Set.Ioc (0 : K) 1 → K :=
  fun x => rho m.1 x.1

/-- A família {ρ_m : m ≥ 2} é linearmente independente no espaço das funções (0,1] → K. -/
theorem linearIndependent_rho : LinearIndependent K (rhoFun (K := K)) := by
  rw [linearIndependent_iff']
  intro s g hsum i hi
  -- transporta para um Finset de ℕ e coeficientes c : ℕ → K
  classical
  let I : Finset ℕ := s.image Subtype.val
  let c : ℕ → K := fun m => if h : 2 ≤ m then g ⟨m, h⟩ else 0
  have hI : ∀ m ∈ I, 2 ≤ m := by
    intro m hm
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hm
    exact j.2
  have hc : ∀ x : K, 0 < x → x ≤ 1 → ∑ m ∈ I, c m * rho m x = 0 := by
    intro x hx0 hx1
    have := congrFun hsum ⟨x, hx0, hx1⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [← this]
    rw [Finset.sum_image (fun a _ b _ hab => Subtype.ext hab)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [c, rhoFun, j.2]
  have := coeffs_eq_zero I c hI hc i.1 (Finset.mem_image_of_mem _ hi)
  simpa [c, i.2] using this

/-- Instância em ℝ, que é o caso do espaço de Nyman–Beurling. -/
theorem linearIndependent_rho_real : LinearIndependent ℝ (rhoFun (K := ℝ)) :=
  linearIndependent_rho

end ATK.RhoIndependente

#print axioms ATK.RhoIndependente.rho_eq_step
#print axioms ATK.RhoIndependente.rho_bounds
#print axioms ATK.RhoIndependente.coeffs_eq_zero
#print axioms ATK.RhoIndependente.linearIndependent_rho
#print axioms ATK.RhoIndependente.linearIndependent_rho_real
#print axioms ATK.RhoIndependente.rho_inv_nat
#print axioms ATK.RhoIndependente.sum_rho_eq_stepVal
#print axioms ATK.RhoIndependente.fract_succ_div_sub
#print axioms ATK.RhoIndependente.stepVal_succ_sub
#print axioms ATK.RhoIndependente.coeffs_eq_zero_of_stepVal
#print axioms ATK.RhoIndependente.coeffs_eq_zero_of_points
