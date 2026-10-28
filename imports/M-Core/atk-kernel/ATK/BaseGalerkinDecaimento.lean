/-
ATK.Base (N3, parte discreta) — Poincaré em Fourier e decaimento exponencial de Galerkin.

Continua `ATK.BaseGalerkinGlobal`.  Em média nula (`0 ∉ K`), todo modo tem `|k|² ≥ 1`, logo
`λ_k = 4π²|k|² ≥ 4π²` (desigualdade de Poincaré no toro, lida em Fourier), e a dissipação de
Navier–Stokes domina a energia:

* **`decaimento_exponencial`** (abstrato): se `⟪F v, v⟫ ≤ −c ‖v‖²` ao longo da trajetória, então
  `‖u(t)‖ ≤ e^{−ct} ‖u(0)‖`;
* **`lam_ge`**: `k ≠ 0 ⇒ λ_k ≥ 4π²` (Poincaré discreto);
* **`norm_sq_eq`**: `‖x‖² = Σ_{k∈K} |x̂_k|²` (Parseval no espaço de estados);
* **`campoE_dissipa_forte`**: em `adm K` com `0 ∉ K`, `⟪V(u), u⟫ ≤ −4π²ν ‖u‖²`;
* **`galerkin_decaimento`**: as soluções globais de Galerkin de média nula satisfazem
  `‖u(t)‖ ≤ e^{−4π²νt} ‖u(0)‖`.

É a estimativa uniforme em `K` que alimenta a compacidade (N4) e a passagem ao limite (N5).
-/
import ATK.BaseGalerkinGlobal

open Finset Complex ComplexConjugate Set
open scoped RealInnerProductSpace

namespace ATK.BaseGalerkinDecaimento

open ATK.BaseGalerkinNS ATK.BaseGalerkinGlobal

/-! ### Decaimento exponencial abstrato -/

/-- **Decaimento exponencial**: se `⟪F v, v⟫ ≤ −c‖v‖²` em um conjunto que contém a trajetória,
então `‖u(t)‖ ≤ e^{−ct}‖u(0)‖` em `[0, T]`. -/
theorem decaimento_exponencial {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {F : H → H} {S : Set H} {c : ℝ} (hF : ∀ v ∈ S, ⟪F v, v⟫ ≤ -c * ‖v‖ ^ 2)
    {u : ℝ → H} {T : ℝ} (hS : ∀ t ∈ Icc 0 T, u t ∈ S)
    (hu : ∀ t ∈ Icc 0 T, HasDerivWithinAt u (F (u t)) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, ‖u t‖ ≤ Real.exp (-c * t) * ‖u 0‖ := by
  set g : ℝ → ℝ := fun s => Real.exp (2 * c * s) * ‖u s‖ ^ 2 with hg
  set g' : ℝ → ℝ := fun s =>
    Real.exp (2 * c * s) * (2 * c * 1) * ‖u s‖ ^ 2 + Real.exp (2 * c * s) * (2 * ⟪u s, F (u s)⟫)
  have hD : ∀ t ∈ Icc 0 T, HasDerivWithinAt g (g' t) (Icc 0 T) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => Real.exp (2 * c * s)) (Real.exp (2 * c * t) * (2 * c * 1)) t :=
      ((hasDerivAt_id t).const_mul (2 * c)).exp
    exact h1.hasDerivWithinAt.mul (hu t ht).norm_sq
  have hanti : AntitoneOn g (Icc 0 T) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := g') (convex_Icc 0 T)
      (fun t ht => (hD t ht).continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
    · exact (hD t (interior_subset ht)).mono interior_subset
    · have ht' := interior_subset ht
      have hd := hF (u t) (hS t ht')
      rw [real_inner_comm] at hd
      have he := Real.exp_pos (2 * c * t)
      have : 2 * c * 1 * ‖u t‖ ^ 2 + 2 * ⟪u t, F (u t)⟫ ≤ 0 := by linarith
      calc g' t = Real.exp (2 * c * t) * (2 * c * 1 * ‖u t‖ ^ 2 + 2 * ⟪u t, F (u t)⟫) := by
              simp only [g']; ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he.le this
  intro t ht
  have hT : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, le_trans ht.1 ht.2⟩
  have h := hanti hT ht ht.1
  simp only [hg, mul_zero, Real.exp_zero, one_mul] at h
  -- h : exp(2ct) ‖u t‖² ≤ ‖u 0‖²
  have he : Real.exp (-c * t) ^ 2 * Real.exp (2 * c * t) = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add,
      show ((2 : ℕ) : ℝ) * (-c * t) + 2 * c * t = 0 by push_cast; ring, Real.exp_zero]
  have hsq : ‖u t‖ ^ 2 ≤ (Real.exp (-c * t) * ‖u 0‖) ^ 2 := by
    have hpos : 0 ≤ Real.exp (-c * t) ^ 2 := sq_nonneg _
    calc ‖u t‖ ^ 2 = Real.exp (-c * t) ^ 2 * (Real.exp (2 * c * t) * ‖u t‖ ^ 2) := by
            rw [← mul_assoc, he, one_mul]
      _ ≤ Real.exp (-c * t) ^ 2 * ‖u 0‖ ^ 2 := mul_le_mul_of_nonneg_left h hpos
      _ = (Real.exp (-c * t) * ‖u 0‖) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mp hsq

/-! ### Poincaré discreto -/

/-- **Poincaré em Fourier**: `k ≠ 0 ⇒ λ_k = 4π²|k|² ≥ 4π²`. -/
theorem lam_ge {k : Modo} (hk : k ≠ 0) : 4 * Real.pi ^ 2 ≤ lam k := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
  have hi' : k i ≠ 0 := hi
  have h1 : (1 : ℤ) ≤ k i ^ 2 := by
    have := Int.one_le_abs hi'
    nlinarith [sq_abs (k i), abs_nonneg (k i)]
  have h1' : (1 : ℝ) ≤ ((k i : ℤ) : ℝ) ^ 2 := by exact_mod_cast h1
  have hs : ((k i : ℤ) : ℝ) ^ 2 ≤ ∑ j, ((k j : ℤ) : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun j => ((k j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  unfold lam
  have hp : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  nlinarith

/-- `Re ⟨a, ā⟩ = Σ |aᵢ|²`. -/
theorem nsq_re (a : Vec) : (nsq a).re = ∑ i, ‖a i‖ ^ 2 := by
  unfold nsq dot cj
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- **Parseval**: `‖x‖² = Σ_{k∈K} |x̂_k|²`. -/
theorem norm_sq_eq (K : Finset Modo) (x : Est K) :
    ‖x‖ ^ 2 = ∑ k ∈ K, (nsq (toCampo K x k)).re := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, ← Finset.sum_coe_sort K]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nsq_re]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toCampo_apply_mem K x k.2 i]

/-- **Dissipação forte**: em média nula, `⟪V(u), u⟫ ≤ −4π²ν‖u‖²`. -/
theorem campoE_dissipa_forte {K : Finset Modo} (hK : Simetrico K) (h0 : (0 : Modo) ∉ K)
    {ν : ℝ} (hν : 0 ≤ ν) {x : Est K} (hx : x ∈ adm K) :
    ⟪campoE K ν x, x⟫ ≤ -(4 * Real.pi ^ 2 * ν) * ‖x‖ ^ 2 := by
  rw [inner_campoE hK ν hx, norm_sq_eq]
  have h : 4 * Real.pi ^ 2 * ν * ∑ k ∈ K, (nsq (toCampo K x k)).re ≤
      ∑ k ∈ K, ν * lam k * (nsq (toCampo K x k)).re := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk0 : k ≠ 0 := fun h => h0 (h ▸ hk)
    have hl := lam_ge hk0
    have hn := nsq_re_nonneg (toCampo K x k)
    have hνn : 0 ≤ ν * (nsq (toCampo K x k)).re := mul_nonneg hν hn
    nlinarith
  linarith

/-- **Decaimento exponencial de Galerkin**: toda solução admissível de média nula satisfaz
`‖u(t)‖ ≤ e^{−4π²νt}‖u(0)‖`. -/
theorem galerkin_decaimento {K : Finset Modo} (hK : Simetrico K) (h0 : (0 : Modo) ∉ K)
    {ν : ℝ} (hν : 0 ≤ ν) {u : ℝ → Est K} {T : ℝ}
    (hu : ∀ t ∈ Icc 0 T, u t ∈ adm K ∧ HasDerivWithinAt u (campoE K ν (u t)) (Icc 0 T) t) :
    ∀ t ∈ Icc 0 T, ‖u t‖ ≤ Real.exp (-(4 * Real.pi ^ 2 * ν) * t) * ‖u 0‖ :=
  decaimento_exponencial (S := adm K) (fun _ hv => campoE_dissipa_forte hK h0 hν hv)
    (fun t ht => (hu t ht).1) (fun t ht => (hu t ht).2)

/-- **Existência global com decaimento**: para dado inicial admissível de média nula, existe
solução de Galerkin em `[0, T]` com `‖u(t)‖ ≤ e^{−4π²νt}‖u(0)‖`. -/
theorem galerkin_global_decaimento {K : Finset Modo} (hK : Simetrico K) (h0 : (0 : Modo) ∉ K)
    {ν : ℝ} (hν : 0 ≤ ν) {x₀ : Est K} (hx₀ : x₀ ∈ adm K) {T : ℝ} (hT : 0 ≤ T) :
    ∃ u : ℝ → Est K, u 0 = x₀ ∧
      (∀ t ∈ Icc 0 T, u t ∈ adm K ∧ HasDerivWithinAt u (campoE K ν (u t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, ‖u t‖ ≤ Real.exp (-(4 * Real.pi ^ 2 * ν) * t) * ‖x₀‖ := by
  obtain ⟨u, hu0, hu, -⟩ := galerkin_global hK hν hx₀ hT
  refine ⟨u, hu0, hu, fun t ht => ?_⟩
  have h := galerkin_decaimento hK h0 hν hu t ht
  rwa [hu0] at h

end ATK.BaseGalerkinDecaimento

#print axioms ATK.BaseGalerkinDecaimento.decaimento_exponencial
#print axioms ATK.BaseGalerkinDecaimento.lam_ge
#print axioms ATK.BaseGalerkinDecaimento.nsq_re
#print axioms ATK.BaseGalerkinDecaimento.norm_sq_eq
#print axioms ATK.BaseGalerkinDecaimento.campoE_dissipa_forte
#print axioms ATK.BaseGalerkinDecaimento.galerkin_decaimento
#print axioms ATK.BaseGalerkinDecaimento.galerkin_global_decaimento
