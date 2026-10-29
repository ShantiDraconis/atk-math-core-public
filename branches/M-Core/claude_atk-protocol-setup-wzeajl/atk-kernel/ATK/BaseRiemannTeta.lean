/-
ATK.Base (R3) — Fórmula integral de Riemann para Ξ, a partir da teta de Jacobi.

Continua `ATK.BaseRiemannXi`.  A Mathlib define `Λ₀ = completedRiemannZeta₀` como transformada de
Mellin de uma versão modificada do núcleo teta `θ(x) = Σ_{n ∈ ℤ} e^{−π n² x}` (um *FE-pair*).
Aqui essa transformada é dobrada sobre `(1, ∞)` pela equação funcional de θ, e chega-se à fórmula
de Riemann (1859):

* **`Λ₀_eq_caudas`** (abstrato, para todo FE-pair fraco): `Λ₀(s) = M[cauda f](s) + ε·M[cauda g](k − s)`,
  onde `cauda f = 𝟙_{(1,∞)}(f − f₀)`;
* **`hasSum_psi`**, **`psi_pos`**: `ψ(x) = (θ(x) − 1)/2 = Σ_{n ≥ 1} e^{−π n² x} > 0`;
* **`completedRiemannZeta₀_integral`**:
  `Λ₀(s) = ∫_{(1,∞)} ψ(x) (x^{s/2 − 1} + x^{(1−s)/2 − 1}) dx` para todo `s ∈ ℂ`;
* **`completedRiemannZeta₀_critica`**: na reta crítica,
  `Λ₀(1/2 + it) = 2 ∫_{(1,∞)} ψ(x) x^{−3/4} cos((t/2) log x) dx` (real);
* **`Xi_riemann`**: `Ξ(t) = 1/2 − (t² + 1/4) ∫_{(1,∞)} ψ(x) x^{−3/4} cos((t/2) log x) dx`.

Esta é a representação sobre a qual se constrói o teorema de Hardy (camada R4).
-/
import ATK.BaseRiemannXi

open Complex Set MeasureTheory
open scoped Real

namespace ATK.BaseRiemannTeta

open ATK.BaseRiemannXi HurwitzZeta

/-! ### Parte abstrata: dobrar a transformada de Mellin de `f_modif` -/

/-- Cauda `𝟙_{(1,∞)} (f − f₀)` de um FE-pair. -/
noncomputable def cauda (P : WeakFEPair ℂ) : ℝ → ℂ := (Ioi 1).indicator fun x => P.f x - P.f₀

theorem f_modif_eq (P : WeakFEPair ℂ) {x : ℝ} (hx : 0 < x) :
    P.f_modif x = cauda P x + P.ε • ((x : ℂ) ^ (-(P.k : ℂ)) • cauda P.symm x⁻¹) := by
  rcases lt_trichotomy x 1 with h1 | rfl | h1
  · have hinv : 1 < x⁻¹ := (one_lt_inv₀ hx).mpr h1
    have hFE := P.hf_modif_FE x⁻¹ (inv_pos.mpr hx)
    rw [one_div, inv_inv] at hFE
    rw [hFE, cauda, indicator_of_notMem (notMem_Ioi.mpr h1.le), zero_add, cauda,
      indicator_of_mem (mem_Ioi.mpr hinv)]
    simp only [WeakFEPair.g_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr hinv),
      indicator_of_notMem (notMem_Ioo_of_ge hinv.le), add_zero, WeakFEPair.symm, smul_eq_mul]
    rw [Real.inv_rpow hx.le, ofReal_inv, ofReal_cpow hx.le, cpow_neg]
    ring
  · simp [WeakFEPair.f_modif, cauda]
  · have hinv : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
    rw [WeakFEPair.f_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr h1),
      indicator_of_notMem (notMem_Ioo_of_ge h1.le), add_zero, cauda, cauda,
      indicator_of_mem (mem_Ioi.mpr h1), indicator_of_notMem (notMem_Ioi.mpr hinv.le)]
    simp

theorem mellinConvergent_f_modif (P : WeakFEPair ℂ) (s : ℂ) : MellinConvergent P.f_modif s :=
  (P.isStrongFEPair_toStrongFEPair.hasMellin s).1

/-- A cauda tem transformada de Mellin convergente em todo `s`. -/
theorem mellinConvergent_cauda (P : WeakFEPair ℂ) (s : ℂ) : MellinConvergent (cauda P) s := by
  have h := (mellinConvergent_f_modif P s).indicator (measurableSet_Ioi (a := (1 : ℝ)))
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  by_cases h1 : 1 < x
  · simp only [indicator_of_mem (mem_Ioi.mpr h1), cauda, WeakFEPair.f_modif, Pi.add_apply,
      indicator_of_notMem (notMem_Ioo_of_ge h1.le), add_zero]
  · simp only [indicator_of_notMem (notMem_Ioi.mpr (not_lt.mp h1)), cauda, smul_zero]

/-- **Dobra de Mellin**: `Λ₀(s) = M[cauda f](s) + ε · M[cauda g](k − s)`. -/
theorem Λ₀_eq_caudas (P : WeakFEPair ℂ) (s : ℂ) :
    P.Λ₀ s = mellin (cauda P) s + P.ε * mellin (cauda P.symm) (P.k - s) := by
  have hA := mellinConvergent_cauda P s
  set B : ℝ → ℂ := fun x => P.ε • ((x : ℂ) ^ (-(P.k : ℂ)) • cauda P.symm x⁻¹) with hB
  have hEq : EqOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • P.f_modif t)
      (fun t => (t : ℂ) ^ (s - 1) • cauda P t + (t : ℂ) ^ (s - 1) • B t) (Ioi 0) := by
    intro t ht
    simp only [hB, f_modif_eq P ht, smul_add]
  have hBc : MellinConvergent B s := by
    have h := (mellinConvergent_f_modif P s).sub hA
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, hB, f_modif_eq P ht, smul_add, add_sub_cancel_left]
  rw [WeakFEPair.Λ₀, mellin, setIntegral_congr_fun measurableSet_Ioi hEq, integral_add hA hBc]
  change mellin (cauda P) s + mellin B s = _
  rw [hB, mellin_const_smul, mellin_cpow_smul, mellin_comp_inv, smul_eq_mul]
  congr 3
  ring

/-! ### O núcleo teta -/

/-- Cauda de teta: `ψ(x) = (θ(x) − 1)/2`. -/
noncomputable def psi (x : ℝ) : ℝ := (evenKernel 0 x - 1) / 2

/-- **`ψ(x) = Σ_{n ≥ 1} e^{−π n² x}`.** -/
theorem hasSum_psi {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => Real.exp (-π * (n + 1) ^ 2 * x)) (psi x) := by
  have h := (hasSum_nat_cosKernel₀ 0 hx).div_const 2
  have e : cosKernel ((0 : ℝ) : UnitAddCircle) x = evenKernel 0 x := by
    rw [evenKernel_eq_cosKernel_of_zero]
    rfl
  rw [e] at h
  refine h.congr_fun fun n => ?_
  simp

theorem psi_pos {x : ℝ} (hx : 0 < x) : 0 < psi x :=
  lt_of_lt_of_le (Real.exp_pos _) (le_hasSum (hasSum_psi hx) 0 fun _ _ => (Real.exp_pos _).le)

local notation "P₀" => hurwitzEvenFEPair 0

theorem cauda_P₀ (x : ℝ) : cauda P₀ x = (Ioi 1).indicator (fun y => ((2 * psi y : ℝ) : ℂ)) x := by
  unfold cauda
  congr 1
  funext y
  simp only [hurwitzEvenFEPair, Function.comp_apply, ite_true, psi]
  push_cast
  ring

theorem mellin_cauda_P₀ (w : ℂ) :
    mellin (cauda P₀) w = ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (w - 1) * ((2 * psi x : ℝ) : ℂ) := by
  rw [mellin]
  have e : EqOn (fun t : ℝ => (t : ℂ) ^ (w - 1) • cauda P₀ t)
      ((Ioi 1).indicator fun x : ℝ => (x : ℂ) ^ (w - 1) * ((2 * psi x : ℝ) : ℂ)) (Ioi 0) := by
    intro t _
    by_cases h1 : 1 < t
    · simp only [cauda_P₀, indicator_of_mem (mem_Ioi.mpr h1), smul_eq_mul]
    · simp only [cauda_P₀, indicator_of_notMem (notMem_Ioi.mpr (not_lt.mp h1)), smul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi e, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]

theorem integrableOn_psi (w : ℂ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (w - 1) * ((2 * psi x : ℝ) : ℂ)) (Ioi 1) := by
  have h := (mellinConvergent_cauda P₀ w).mono_set (Ioi_subset_Ioi zero_le_one)
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [cauda_P₀, indicator_of_mem hx, smul_eq_mul]

/-- `Λ₀(s) = (M[cauda](s/2) + M[cauda](1/2 − s/2)) / 2`. -/
theorem completedRiemannZeta₀_eq_caudas (s : ℂ) :
    completedRiemannZeta₀ s = (mellin (cauda P₀) (s / 2) + mellin (cauda P₀) (1 / 2 - s / 2)) / 2 := by
  have hε : (hurwitzEvenFEPair 0).ε = 1 := rfl
  have hk : (hurwitzEvenFEPair 0).k = 1 / 2 := rfl
  rw [completedRiemannZeta₀, completedHurwitzZetaEven₀, Λ₀_eq_caudas, hurwitzEvenFEPair_zero_symm,
    hε, hk, one_mul]
  push_cast
  ring_nf

/-- **Fórmula de Riemann (forma complexa)**:
`Λ₀(s) = ∫_{(1,∞)} ψ(x) (x^{s/2 − 1} + x^{(1−s)/2 − 1}) dx`. -/
theorem completedRiemannZeta₀_integral (s : ℂ) :
    completedRiemannZeta₀ s =
      ∫ x in Ioi (1 : ℝ), (psi x : ℂ) * ((x : ℂ) ^ (s / 2 - 1) + (x : ℂ) ^ ((1 - s) / 2 - 1)) := by
  rw [completedRiemannZeta₀_eq_caudas, mellin_cauda_P₀, mellin_cauda_P₀,
    ← integral_add (integrableOn_psi _) (integrableOn_psi _), ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  have e : (1 : ℂ) / 2 - s / 2 = (1 - s) / 2 := by ring
  simp only [e]
  push_cast
  ring

/-- `x^{a + ib} + x^{a − ib} = 2 x^a cos(b log x)` para `x > 0`. -/
theorem cpow_add_cpow_conj {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    (x : ℂ) ^ ((a : ℂ) + b * I) + (x : ℂ) ^ ((a : ℂ) - b * I) =
      ((2 * x ^ a * Real.cos (b * Real.log x) : ℝ) : ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [cpow_def_of_ne_zero hx0, cpow_def_of_ne_zero hx0, ← ofReal_log hx.le,
    Real.rpow_def_of_pos hx]
  push_cast
  rw [show (2 : ℂ) * cexp (↑(Real.log x) * ↑a) * Complex.cos (↑b * ↑(Real.log x)) =
      cexp (↑(Real.log x) * ↑a) * (2 * Complex.cos (↑b * ↑(Real.log x))) by ring,
    Complex.two_cos, mul_add (cexp _), ← Complex.exp_add, ← Complex.exp_add]
  congr 1 <;> congr 1 <;> ring

/-- **Λ₀ na reta crítica**: `Λ₀(1/2 + it) = 2 ∫_{(1,∞)} ψ(x) x^{−3/4} cos((t/2) log x) dx`. -/
theorem completedRiemannZeta₀_critica (t : ℝ) :
    completedRiemannZeta₀ (1 / 2 + t * I) =
      ((2 * ∫ x in Ioi (1 : ℝ), psi x * x ^ (-(3 / 4 : ℝ)) * Real.cos (t / 2 * Real.log x) : ℝ) : ℂ) := by
  rw [completedRiemannZeta₀_integral, ofReal_mul, ← integral_complex_ofReal, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
  have e1 : (1 / 2 + (t : ℂ) * I) / 2 - 1 = ((-(3 / 4 : ℝ) : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  have e2 : (1 - (1 / 2 + (t : ℂ) * I)) / 2 - 1 = ((-(3 / 4 : ℝ) : ℝ) : ℂ) - ((t / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [e1, e2, cpow_add_cpow_conj hx0]
  push_cast
  ring

/-- **Fórmula de Riemann para Ξ**:
`Ξ(t) = 1/2 − (t² + 1/4) ∫_{(1,∞)} ψ(x) x^{−3/4} cos((t/2) log x) dx`. -/
theorem Xi_riemann (t : ℝ) :
    Xi t = 1 / 2 - (t ^ 2 + 1 / 4) *
      ∫ x in Ioi (1 : ℝ), psi x * x ^ (-(3 / 4 : ℝ)) * Real.cos (t / 2 * Real.log x) := by
  set J := ∫ x in Ioi (1 : ℝ), psi x * x ^ (-(3 / 4 : ℝ)) * Real.cos (t / 2 * Real.log x)
  have h : riemannXi (1 / 2 + t * I) = ((1 / 2 - (t ^ 2 + 1 / 4) * J : ℝ) : ℂ) := by
    rw [riemannXi, completedRiemannZeta₀_critica]
    push_cast
    linear_combination ((t : ℂ) ^ 2 * (J : ℂ)) * I_sq
  unfold Xi
  rw [h, ofReal_re]

end ATK.BaseRiemannTeta

#print axioms ATK.BaseRiemannTeta.f_modif_eq
#print axioms ATK.BaseRiemannTeta.mellinConvergent_f_modif
#print axioms ATK.BaseRiemannTeta.mellinConvergent_cauda
#print axioms ATK.BaseRiemannTeta.Λ₀_eq_caudas
#print axioms ATK.BaseRiemannTeta.hasSum_psi
#print axioms ATK.BaseRiemannTeta.psi_pos
#print axioms ATK.BaseRiemannTeta.cauda_P₀
#print axioms ATK.BaseRiemannTeta.mellin_cauda_P₀
#print axioms ATK.BaseRiemannTeta.integrableOn_psi
#print axioms ATK.BaseRiemannTeta.completedRiemannZeta₀_eq_caudas
#print axioms ATK.BaseRiemannTeta.completedRiemannZeta₀_integral
#print axioms ATK.BaseRiemannTeta.cpow_add_cpow_conj
#print axioms ATK.BaseRiemannTeta.completedRiemannZeta₀_critica
#print axioms ATK.BaseRiemannTeta.Xi_riemann
