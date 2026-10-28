/-
ATK.Base (N3, parte contínua) — Poincaré em `L²(Tᵈ)` e o mergulho das soluções de Galerkin.

A Mathlib tem a base de Hilbert de Fourier `mFourierBasis` de `L²(Tᵈ)` e a identidade de Parseval
(`hasSum_sq_mFourierCoeff`).  Sobre ela:

* **`media_eq`**: o coeficiente `f̂₀` é a média `∫ f`;
* `EmH1 f`: `Σ_k |k|² |f̂_k|² < ∞` (o espaço `H¹(Tᵈ)` lido em Fourier);
* **`poincare`**: se `f̂₀ = 0` e `f ∈ H¹`, então `∫ |f|² ≤ Σ_k |k|² |f̂_k|²`, isto é
  `‖f‖²_{L²} ≤ (2π)⁻² ‖∇f‖²_{L²}` — a desigualdade de Poincaré no toro;
* **`coeff_trig`**, **`energia_trig`**: o polinômio trigonométrico `Σ_{k∈K} c_k e^{2πik·x}` tem
  coeficientes `c_k` (zero fora de `K`) e `∫ |·|² = Σ_{k∈K} |c_k|²`;
* **`galerkin_L2`**: um estado de Galerkin `x` (de `ATK.BaseGalerkinGlobal`) é o campo
  `u = (u₁, u₂, u₃)` de `L²(T³)³` com `Σᵢ ∫ |uᵢ|² = ‖x‖²`;
* **`galerkin_L2_decaimento`**: as soluções globais de Galerkin de média nula têm energia
  contínua `Σᵢ ∫ |uᵢ(t)|² ≤ e^{−8π²νt} ‖x₀‖²`.

Liga as camadas N2b/N3a ao espaço de energia contínuo.  Compacidade (Aubin–Lions) e a passagem
ao limite de Leray continuam como N4–N5.
-/
import ATK.BaseGalerkinDecaimento
import Mathlib.Analysis.Fourier.AddCircleMulti

open MeasureTheory UnitAddTorus Finset Set
open scoped ComplexConjugate

noncomputable section

namespace ATK.BaseToroPoincare

open ATK.BaseGalerkinNS ATK.BaseGalerkinGlobal ATK.BaseGalerkinDecaimento

variable {d : Type*} [Fintype d]

/-- A mesma medida de Haar (massa 1) usada na Mathlib para a série de Fourier no toro. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

/-- `|k|² = Σᵢ kᵢ²`. -/
def nq (k : d → ℤ) : ℝ := ∑ i, ((k i : ℤ) : ℝ) ^ 2

theorem one_le_nq {k : d → ℤ} (hk : k ≠ 0) : 1 ≤ nq k := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
  have hi' : k i ≠ 0 := hi
  have h1 : (1 : ℤ) ≤ k i ^ 2 := by
    have := Int.one_le_abs hi'
    nlinarith [sq_abs (k i), abs_nonneg (k i)]
  have h1' : (1 : ℝ) ≤ ((k i : ℤ) : ℝ) ^ 2 := by exact_mod_cast h1
  exact h1'.trans (Finset.single_le_sum (f := fun j => ((k j : ℤ) : ℝ) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i))

/-- **`f̂₀` é a média.** -/
theorem media_eq (f : UnitAddTorus d → ℂ) : mFourierCoeff f 0 = ∫ t, f t := by
  simp [mFourierCoeff, mFourier_zero]

/-- `f ∈ H¹(Tᵈ)`, lido em Fourier. -/
def EmH1 (f : L²(UnitAddTorus d)) : Prop :=
  Summable fun k : d → ℤ => nq k * ‖mFourierCoeff f k‖ ^ 2

/-- **Desigualdade de Poincaré no toro**: para `f` de média nula em `H¹`,
`∫ |f|² ≤ Σ_k |k|² |f̂_k|²`. -/
theorem poincare (f : L²(UnitAddTorus d)) (h0 : mFourierCoeff f 0 = 0) (hf : EmH1 f) :
    ∫ t, ‖f t‖ ^ 2 ≤ ∑' k, nq k * ‖mFourierCoeff f k‖ ^ 2 := by
  refine hasSum_le (fun k => ?_) (hasSum_sq_mFourierCoeff f) hf.hasSum
  by_cases hk : k = 0
  · subst hk
    rw [h0, norm_zero]
    simp
  · have h1 := one_le_nq hk
    have h2 := sq_nonneg ‖mFourierCoeff f k‖
    nlinarith

/-- Forma com a constante: `‖f‖²_{L²} ≤ (2π)⁻² · Σ_k |2πk|² |f̂_k|²`. -/
theorem poincare_2pi (f : L²(UnitAddTorus d)) (h0 : mFourierCoeff f 0 = 0) (hf : EmH1 f) :
    ∫ t, ‖f t‖ ^ 2 ≤ (4 * Real.pi ^ 2)⁻¹ *
      ∑' k, 4 * Real.pi ^ 2 * nq k * ‖mFourierCoeff f k‖ ^ 2 := by
  have hp : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
  rw [show (fun k : d → ℤ => 4 * Real.pi ^ 2 * nq k * ‖mFourierCoeff f k‖ ^ 2) =
      fun k => 4 * Real.pi ^ 2 * (nq k * ‖mFourierCoeff f k‖ ^ 2) by funext k; ring,
    tsum_mul_left, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
  exact poincare f h0 hf

/-! ### Polinômios trigonométricos -/

/-- `Σ_{k∈K} c_k e^{2πik·x}` em `L²(Tᵈ)`. -/
def trig (K : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) : L²(UnitAddTorus d) :=
  ∑ k ∈ K, c k • mFourierLp 2 k

/-- **Coeficientes de um polinômio trigonométrico.** -/
theorem coeff_trig (K : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (j : d → ℤ) :
    mFourierCoeff (trig K c) j = if j ∈ K then c j else 0 := by
  classical
  rw [← mFourierBasis_repr, HilbertBasis.repr_apply_apply, coe_mFourierBasis, trig, inner_sum]
  simp_rw [inner_smul_right, orthonormal_iff_ite.mp orthonormal_mFourier, mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq]

/-- **Energia de um polinômio trigonométrico**: `∫ |Σ c_k e_k|² = Σ_{k∈K} |c_k|²`. -/
theorem energia_trig (K : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) :
    ∫ t, ‖trig K c t‖ ^ 2 = ∑ k ∈ K, ‖c k‖ ^ 2 := by
  have h := hasSum_sq_mFourierCoeff (trig K c)
  simp_rw [coeff_trig] at h
  have e : ∑ k ∈ K, ‖if k ∈ K then c k else 0‖ ^ 2 = ∑ k ∈ K, ‖c k‖ ^ 2 :=
    Finset.sum_congr rfl fun k hk => by rw [if_pos hk]
  have h' : HasSum (fun k : d → ℤ => ‖if k ∈ K then c k else 0‖ ^ 2) (∑ k ∈ K, ‖c k‖ ^ 2) := by
    rw [← e]
    exact hasSum_sum_of_ne_finset_zero fun k hk => by simp [hk]
  exact h.unique h'

/-! ### O mergulho de Galerkin em `L²(T³)³` -/

/-- Componente `i` do campo de Galerkin como função de `L²(T³)`. -/
def campoL2 (K : Finset Modo) (x : Est K) (i : Fin 3) : L²(UnitAddTorus (Fin 3)) :=
  trig K fun k => toCampo K x k i

/-- **Energia contínua = energia de Galerkin**: `Σᵢ ∫ |uᵢ|² = ‖x‖²`. -/
theorem galerkin_L2 (K : Finset Modo) (x : Est K) :
    ∑ i : Fin 3, ∫ t, ‖campoL2 K x i t‖ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [campoL2, energia_trig]
  rw [Finset.sum_comm, norm_sq_eq]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nsq_re]

/-- **Decaimento da energia contínua** das soluções globais de Galerkin de média nula. -/
theorem galerkin_L2_decaimento {K : Finset Modo} (hK : Simetrico K) (h0 : (0 : Modo) ∉ K)
    {ν : ℝ} (hν : 0 ≤ ν) {x₀ : Est K} (hx₀ : x₀ ∈ adm K) {T : ℝ} (hT : 0 ≤ T) :
    ∃ u : ℝ → Est K, u 0 = x₀ ∧
      (∀ t ∈ Icc 0 T, u t ∈ adm K ∧ HasDerivWithinAt u (campoE K ν (u t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, ∑ i : Fin 3, ∫ s, ‖campoL2 K (u t) i s‖ ^ 2 ≤
        Real.exp (-(8 * Real.pi ^ 2 * ν) * t) * ‖x₀‖ ^ 2 := by
  obtain ⟨u, hu0, hu, hdec⟩ := galerkin_global_decaimento hK h0 hν hx₀ hT
  refine ⟨u, hu0, hu, fun t ht => ?_⟩
  rw [galerkin_L2]
  have h := hdec t ht
  have hn : 0 ≤ ‖u t‖ := norm_nonneg _
  have e : Real.exp (-(8 * Real.pi ^ 2 * ν) * t) =
      Real.exp (-(4 * Real.pi ^ 2 * ν) * t) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e, ← mul_pow]
  exact pow_le_pow_left₀ hn h 2

end ATK.BaseToroPoincare

#print axioms ATK.BaseToroPoincare.one_le_nq
#print axioms ATK.BaseToroPoincare.media_eq
#print axioms ATK.BaseToroPoincare.poincare
#print axioms ATK.BaseToroPoincare.poincare_2pi
#print axioms ATK.BaseToroPoincare.coeff_trig
#print axioms ATK.BaseToroPoincare.energia_trig
#print axioms ATK.BaseToroPoincare.galerkin_L2
#print axioms ATK.BaseToroPoincare.galerkin_L2_decaimento
