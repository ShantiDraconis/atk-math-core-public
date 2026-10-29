import ATK.ATKI
import ATK.BaezDuarteBridge

/-!
# ATK-I — Ponte de Bagchi: `D∞ = 0` (família do texto) ⟹ Hipótese de Riemann

A família do texto ATK-I (`ATK.ATKI.wTexto`, `ATK.ATKI.gTexto`) é a do teorema 1 de Bagchi
(2006, arXiv:math/0607733): pesos `1/(n(n+1))` e geradores `γ_q(n) = {n/q}`, `q ≥ 2`.

Este arquivo prova no kernel, **sem hipóteses**:

  `rh_of_texto : (⨅ N, Defeito wTexto gTexto N) = 0 → RiemannHypothesis`

com `RiemannHypothesis` da Mathlib. Argumento (isometria de Bagchi):

1. `{t/q} = ({⌊t⌋/q}) + {t}/q`, logo `ρ_q(x) − ρ_1(x)/q = {⌊1/x⌋/q}` para `x > 0`
   (`rho_sub`), com `ρ_k(x) = {1/(kx)}` a família de Báez-Duarte.
2. Para cada `c` do texto, os coeficientes `c' = (−Σ c_m/(m+2), c_0, …, c_{N−1})` dão o resíduo
   de Báez-Duarte `χ − Σ c'_k ρ_{k+1}`, que vale `0` em `(1, ∞)` e é constante
   `1 − Σ c_m γ_{m+2}(n)` em `(1/(n+1), 1/n]`.
3. Logo `‖χ − Σ c'_k ρ_{k+1}‖²_{L²(0,∞)} = Σ_n (1 − Σ c_m γ_{m+2}(n))²/(n(n+1))`
   (`residualSq_coefBD`): a distância do texto é uma distância de Báez-Duarte.
4. `D^{BD}_{N+1} ≤ D^{texto}_N` (`DN_succ_le`); com `D∞ = 0` vem `D^{BD}_N → 0`, e a ponte B1
   já provada (`ATK.BaezDuarteBridge.baezDuarteCriterion`) dá RH.

O que **não** está aqui: a recíproca (RH ⟹ `D∞ = 0`, direção de necessidade) e, claro, a prova de
que `D∞ = 0`. `D∞ = 0` continua sendo um problema aberto equivalente a RH.
-/

open Set MeasureTheory Filter Topology

namespace ATK.ATKIBagchi

open ATK.ATKI ATK.Conditional.Riemann ATK.RiemannConcrete ATK.RiemannFaithful ATK.BaezDuarteBridge

noncomputable section

/-! ## 1. Parte fracionária de `t/q` -/

/-- `{t/q} = ((⌊t⌋ mod q) + {t})/q`. -/
theorem fract_div_nat (t : ℝ) {q : ℕ} (hq : 0 < q) :
    Int.fract (t / q) = ((((⌊t⌋ % (q : ℤ)) : ℤ) : ℝ) + Int.fract t) / q := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have h0 : (0 : ℤ) ≤ ⌊t⌋ % (q : ℤ) := Int.emod_nonneg _ hqz.ne'
  have h1 : ⌊t⌋ % (q : ℤ) + 1 ≤ q := Int.add_one_le_iff.mpr (Int.emod_lt_of_pos _ hqz)
  have h0r : (0 : ℝ) ≤ (((⌊t⌋ % (q : ℤ)) : ℤ) : ℝ) := by exact_mod_cast h0
  have h1r : (((⌊t⌋ % (q : ℤ)) : ℤ) : ℝ) + 1 ≤ q := by exact_mod_cast h1
  have hdec : (⌊t⌋ : ℝ) = (q : ℝ) * (((⌊t⌋ / (q : ℤ)) : ℤ) : ℝ) + (((⌊t⌋ % (q : ℤ)) : ℤ) : ℝ) := by
    have hz : ⌊t⌋ = (q : ℤ) * (⌊t⌋ / (q : ℤ)) + ⌊t⌋ % (q : ℤ) := by
      first
      | (have := Int.emod_def ⌊t⌋ (q : ℤ); linarith)
      | exact (Int.mul_ediv_add_emod ⌊t⌋ (q : ℤ)).symm
      | (have := Int.emod_add_ediv ⌊t⌋ (q : ℤ); linarith)
    exact_mod_cast hz
  rw [Int.fract_eq_iff]
  refine ⟨div_nonneg (by linarith [Int.fract_nonneg t]) hq'.le, ?_, ⌊t⌋ / (q : ℤ), ?_⟩
  · rw [div_lt_one hq']
    linarith [Int.fract_lt_one t]
  · rw [← sub_div, div_eq_iff hq'.ne', ← Int.self_sub_floor, hdec]
    ring

/-- `ρ_q(x) − ρ_1(x)/q = (⌊1/x⌋ mod q)/q`. -/
theorem rho_sub (q : ℕ) (hq : 0 < q) {x : ℝ} (_hx : 0 < x) :
    rho q x - rho 1 x / q = (((⌊1 / x⌋ % (q : ℤ)) : ℤ) : ℝ) / q := by
  have h1 : 1 / ((q : ℝ) * x) = 1 / x / q := by rw [div_div, mul_comm]
  have h2 : rho 1 x = Int.fract (1 / x) := by simp [rho]
  rw [h2]
  unfold rho
  rw [h1, fract_div_nat _ hq]
  ring

/-! ## 2. As faixas `(1/(k+2), 1/(k+1)]` -/

/-- A faixa onde `⌊1/x⌋ = k + 1`. -/
def faixa (k : ℕ) : Set ℝ := Ioc (1 / ((k : ℝ) + 2)) (1 / ((k : ℝ) + 1))

theorem faixa_meas (k : ℕ) : MeasurableSet (faixa k) := measurableSet_Ioc

theorem faixa_pos {k : ℕ} {x : ℝ} (h : x ∈ faixa k) : 0 < x := by
  have hk : (0 : ℝ) < 1 / ((k : ℝ) + 2) := by positivity
  simp only [faixa, mem_Ioc] at h
  linarith [h.1]

theorem mem_faixa_iff {x : ℝ} (hx : 0 < x) (k : ℕ) : x ∈ faixa k ↔ ⌊1 / x⌋ = (k : ℤ) + 1 := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  simp only [faixa, mem_Ioc]
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(le_one_div hx hk1).mp h2, ?_⟩
    have := (one_div_lt hk2 hx).mp h1
    linarith
  · rintro ⟨h1, h2⟩
    exact ⟨(one_div_lt hk2 hx).mpr (by linarith), (le_one_div hx hk1).mpr h1⟩

theorem iUnion_faixa : ⋃ k, faixa k = Ioc (0 : ℝ) 1 := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩
    have hx := faixa_pos hk
    simp only [faixa, mem_Ioc] at hk
    refine ⟨hx, hk.2.trans ?_⟩
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  · rintro ⟨hx0, hx1⟩
    have hge : (1 : ℝ) ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith
    have hfl : (1 : ℤ) ≤ ⌊1 / x⌋ := Int.le_floor.mpr (by exact_mod_cast hge)
    refine ⟨(⌊1 / x⌋ - 1).toNat, ?_⟩
    rw [mem_faixa_iff hx0, Int.toNat_of_nonneg (by omega)]
    ring

theorem faixa_disjoint : Pairwise (Function.onFun Disjoint faixa) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun x hi hj => hij ?_
  have hx := faixa_pos hi
  rw [mem_faixa_iff hx] at hi hj
  have : (i : ℤ) = j := by linarith
  exact_mod_cast this

/-! ## 3. Os coeficientes de Báez-Duarte de um vetor do texto -/

/-- `c' = (−Σ c_m/(m+2), c_0, …, c_{N−1})`. -/
def coefBD {N : ℕ} (c : Fin N → ℝ) : Fin (N + 1) → ℝ :=
  Fin.cons (α := fun _ => ℝ) (-(∑ i : Fin N, c i / (((i : ℕ) : ℝ) + 2))) c

theorem coefBD_zero {N : ℕ} (c : Fin N → ℝ) :
    coefBD c 0 = -(∑ i : Fin N, c i / (((i : ℕ) : ℝ) + 2)) := by
  unfold coefBD
  exact Fin.cons_zero _ _

theorem coefBD_succ {N : ℕ} (c : Fin N → ℝ) (i : Fin N) : coefBD c i.succ = c i := by
  unfold coefBD
  exact Fin.cons_succ _ _ _

/-- A constante da cauda de `c'` é zero. -/
theorem tailS_coefBD {N : ℕ} (c : Fin N → ℝ) : tailS (coefBD c) = 0 := by
  unfold tailS
  rw [Fin.sum_univ_succ, coefBD_zero]
  simp only [coefBD_succ, Fin.val_zero, Fin.val_succ, Nat.cast_zero, zero_add, div_one,
    Nat.cast_add, Nat.cast_one]
  rw [neg_add_eq_zero]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- O resíduo de Báez-Duarte de `c'`, para `x > 0`. -/
theorem res_coefBD {N : ℕ} (c : Fin N → ℝ) {x : ℝ} (hx : 0 < x) :
    res (coefBD c) x = chi x -
      ∑ i : Fin N, c i * ((((⌊1 / x⌋ % (((i : ℕ) : ℤ) + 2)) : ℤ) : ℝ) / (((i : ℕ) : ℝ) + 2)) := by
  have hterm : ∀ i : Fin N, coefBD c i.succ * rho ((i.succ : ℕ) + 1) x =
      c i * (rho 1 x / (((i : ℕ) : ℝ) + 2)) +
        c i * ((((⌊1 / x⌋ % (((i : ℕ) : ℤ) + 2)) : ℤ) : ℝ) / (((i : ℕ) : ℝ) + 2)) := by
    intro i
    have h := rho_sub ((i : ℕ) + 2) (by omega) hx
    push_cast at h
    rw [coefBD_succ, Fin.val_succ]
    show c i * rho ((i : ℕ) + 2) x = _
    linear_combination (c i) * h
  have hs : ∑ i : Fin N, c i * (rho 1 x / (((i : ℕ) : ℝ) + 2)) =
      (∑ i : Fin N, c i / (((i : ℕ) : ℝ) + 2)) * rho 1 x := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  unfold res
  rw [Fin.sum_univ_succ]
  simp only [hterm]
  rw [Finset.sum_add_distrib, hs, coefBD_zero]
  simp only [Fin.val_zero, zero_add]
  ring

/-- Na faixa `k`, o resíduo é a constante `1 − Σ c_m γ_{m+2}(k+1)` do texto. -/
theorem res_on_faixa {N : ℕ} (c : Fin N → ℝ) {k : ℕ} {x : ℝ} (hx : x ∈ faixa k) :
    res (coefBD c) x = 1 - ∑ i : Fin N, c i * gTexto i k := by
  have hx0 := faixa_pos hx
  have hfl : ⌊1 / x⌋ = (k : ℤ) + 1 := (mem_faixa_iff hx0 k).mp hx
  have hIoc : x ∈ Ioc (0 : ℝ) 1 := by
    rw [← iUnion_faixa]
    exact mem_iUnion.mpr ⟨k, hx⟩
  have hg : ∀ i : Fin N,
      (((((k : ℤ) + 1) % (((i : ℕ) : ℤ) + 2)) : ℤ) : ℝ) / (((i : ℕ) : ℝ) + 2) = gTexto i k := by
    intro i
    have h1 : (((k + 1) % ((i : ℕ) + 2) : ℕ) : ℤ) = ((k : ℤ) + 1) % (((i : ℕ) : ℤ) + 2) := by
      exact_mod_cast Int.natCast_mod (k + 1) ((i : ℕ) + 2)
    unfold gTexto
    rw [← h1, Int.cast_natCast]
  rw [res_coefBD c hx0, chi_of_mem hIoc, hfl]
  simp only [hg]

/-! ## 4. A isometria: a distância do texto é uma distância de Báez-Duarte -/

theorem integral_faixa {N : ℕ} (c : Fin N → ℝ) (k : ℕ) :
    ∫ x in faixa k, res (coefBD c) x ^ 2 = wTexto k * (1 - ∑ i : Fin N, c i * gTexto i k) ^ 2 := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hle : 1 / ((k : ℝ) + 2) ≤ 1 / ((k : ℝ) + 1) := one_div_le_one_div_of_le hk1 (by linarith)
  have hw : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) = wTexto k := by
    unfold wTexto
    rw [div_sub_div _ _ hk1.ne' hk2.ne']
    congr 1
    ring
  have hcongr : ∫ x in faixa k, res (coefBD c) x ^ 2 =
      ∫ _ in faixa k, (1 - ∑ i : Fin N, c i * gTexto i k) ^ 2 :=
    setIntegral_congr_fun (faixa_meas k) fun x hx => by simp only [res_on_faixa c hx]
  rw [hcongr]
  unfold faixa
  rw [← intervalIntegral.integral_of_le hle, intervalIntegral.integral_const, smul_eq_mul, hw]

theorem integral_Ioc_coefBD {N : ℕ} (c : Fin N → ℝ) :
    ∫ x in Ioc (0 : ℝ) 1, res (coefBD c) x ^ 2 =
      ∑' k, wTexto k * (1 - ∑ i : Fin N, c i * gTexto i k) ^ 2 := by
  have hint : IntegrableOn (fun x => res (coefBD c) x ^ 2) (⋃ k, faixa k) := by
    rw [iUnion_faixa]
    exact (integrable_res_sq (coefBD c)).mono_set Ioc_subset_Ioi_self
  rw [← iUnion_faixa, integral_iUnion faixa_meas faixa_disjoint hint]
  exact tsum_congr (integral_faixa c)

/-- **Isometria de Bagchi**: `‖χ − Σ c'_k ρ_{k+1}‖² = Σ_k w_k (1 − Σ c_m g_m(k))²`. -/
theorem residualSq_coefBD {N : ℕ} (c : Fin N → ℝ) :
    residualSq (N + 1) (coefBD c) =
      ∑' k, wTexto k * (1 - ∑ i : Fin N, c i * gTexto i k) ^ 2 := by
  rw [residualSq_eq_res, ← integral_Ioc_coefBD c, ← Ioc_union_Ioi_eq_Ioi zero_le_one,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((integrable_res_sq (coefBD c)).mono_set Ioc_subset_Ioi_self)
      ((integrable_res_sq (coefBD c)).mono_set (Ioi_subset_Ioi zero_le_one)),
    integral_tail_sq, tailS_coefBD]
  ring

/-! ## 5. A ponte -/

/-- `D^{BD}_{N+1} ≤ D^{texto}_N`. -/
theorem DN_succ_le (N : ℕ) : DN (N + 1) ≤ Defeito wTexto gTexto N := by
  unfold Defeito
  refine le_ciInf fun c => ?_
  rw [← residualSq_coefBD c]
  exact DN_le_residualSq (N + 1) (coefBD c)

/-- Se o defeito do texto vai a zero, o `D_N` de Báez-Duarte vai a zero. -/
theorem tendsto_DN_of_texto (h : Tendsto (Defeito wTexto gTexto) atTop (𝓝 0)) :
    Tendsto DN atTop (𝓝 0) := by
  have h1 : Tendsto (fun N => DN (N + 1)) atTop (𝓝 0) :=
    squeeze_zero (fun N => DN_nonneg (N + 1)) DN_succ_le h
  exact (tendsto_add_atTop_iff_nat 1).mp h1

/-- **Ponte de Bagchi no kernel**: `D∞ = 0` na família do texto ⟹ Hipótese de Riemann. -/
theorem rh_of_texto (h : (⨅ N, Defeito wTexto gTexto N) = 0) : RiemannHypothesis := by
  have hT := texto_converge
  rw [h] at hT
  exact baezDuarteCriterion (tendsto_DN_of_texto hT)

/-- A mesma ponte na forma `∀ ε > 0, ∃ N, D N < ε`. -/
theorem rh_of_texto_eps (h : ∀ ε > 0, ∃ N, Defeito wTexto gTexto N < ε) : RiemannHypothesis :=
  rh_of_texto ((defeito_limite_zero_iff wTexto_nonneg).mpr h)

/-- Contrapositiva: se RH é falsa, o `D∞` do texto é estritamente positivo. -/
theorem texto_pos_of_not_rh (h : ¬ RiemannHypothesis) : 0 < ⨅ N, Defeito wTexto gTexto N := by
  have h0 : 0 ≤ ⨅ N, Defeito wTexto gTexto N := le_ciInf (defeito_nonneg wTexto_nonneg)
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd (rh_of_texto heq.symm) h

end

end ATK.ATKIBagchi

#print axioms ATK.ATKIBagchi.fract_div_nat
#print axioms ATK.ATKIBagchi.rho_sub
#print axioms ATK.ATKIBagchi.faixa_meas
#print axioms ATK.ATKIBagchi.faixa_pos
#print axioms ATK.ATKIBagchi.mem_faixa_iff
#print axioms ATK.ATKIBagchi.iUnion_faixa
#print axioms ATK.ATKIBagchi.faixa_disjoint
#print axioms ATK.ATKIBagchi.coefBD_zero
#print axioms ATK.ATKIBagchi.coefBD_succ
#print axioms ATK.ATKIBagchi.tailS_coefBD
#print axioms ATK.ATKIBagchi.res_coefBD
#print axioms ATK.ATKIBagchi.res_on_faixa
#print axioms ATK.ATKIBagchi.integral_faixa
#print axioms ATK.ATKIBagchi.integral_Ioc_coefBD
#print axioms ATK.ATKIBagchi.residualSq_coefBD
#print axioms ATK.ATKIBagchi.DN_succ_le
#print axioms ATK.ATKIBagchi.tendsto_DN_of_texto
#print axioms ATK.ATKIBagchi.rh_of_texto
#print axioms ATK.ATKIBagchi.rh_of_texto_eps
#print axioms ATK.ATKIBagchi.texto_pos_of_not_rh
