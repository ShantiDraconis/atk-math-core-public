import Mathlib

/-!
# ATK — Laguerre: `p + c·p'` preserva raízes reais, e o fluxo do calor discreto em polinômios

O núcleo polinomial do teorema de de Bruijn (o semigrupo `e^{−λD²}`, `λ ≥ 0`, preserva a classe de
Laguerre–Pólya) — sem as passagens ao limite (Hurwitz), que ficam `BUILD_PENDING`.

* `RealRooted p`: `p` tem tantas raízes reais (com multiplicidade) quanto o grau (`⟺ Splits`,
  `realRooted_iff_splits`).
* `realRooted_of_card`: para polinômios reais, `#raízes ≥ grau − 1` já basta (o fator restante teria grau 1).
* **Laguerre** (`realRooted_add_C_mul_derivative`): `p` com raízes reais ⇒ `p + c·p'` com raízes reais, para
  todo `c ∈ ℝ`. Prova: Rolle para `e^{x/c}p(x)` (cuja derivada é `e^{x/c}(p + cp')(x)/c`) entre raízes
  consecutivas, multiplicidades `m − 1` nas raízes de `p`, e contagem como em `Polynomial.card_roots_le_derivative`.
* `realRooted_sub_derivative2`: `p − λp''` (`λ ≥ 0`) tem raízes reais, pois `1 − λD² = (1 − √λD)(1 + √λD)`;
  iterando (`realRooted_iter`), **`(1 − (t/N)D²)^N p` tem raízes reais para `t ≥ 0`** — o análogo discreto de
  `H_t = e^{−t∂²}H₀` (`ATK.DBN.calor`).
* `calor_direto_falha`: o sentido oposto não preserva: `X²` tem raízes reais e `(1 + D²)X² = X² + 2` não tem.
-/

open Polynomial

namespace ATK.Laguerre

/-- `p` tem só raízes reais: o número de raízes reais (com multiplicidade) é o grau. -/
def RealRooted (p : ℝ[X]) : Prop := Multiset.card p.roots = p.natDegree

theorem realRooted_iff_splits (p : ℝ[X]) : RealRooted p ↔ p.Splits := splits_iff_card_roots.symm

/-- Para polinômios reais, `#raízes + 1 ≥ grau` já implica raízes reais. -/
theorem realRooted_of_card {p : ℝ[X]} (h : p.natDegree ≤ Multiset.card p.roots + 1) : RealRooted p := by
  obtain ⟨q, _, hdeg, hroots⟩ := exists_prod_multiset_X_sub_C_mul p
  have hq : q.natDegree = 0 := by
    by_contra hne
    have h1 : q.natDegree = 1 := by omega
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp at h1
    have hd : q.degree = 1 := by
      rw [degree_eq_natDegree hq0, h1]
      rfl
    obtain ⟨x, hx⟩ := exists_root_of_degree_eq_one hd
    have hmem : x ∈ q.roots := (mem_roots hq0).mpr hx
    rw [hroots] at hmem
    simp at hmem
  unfold RealRooted
  omega

/-- **Laguerre**: se `p` tem só raízes reais, `p + c·p'` também, para todo `c` real. -/
theorem realRooted_add_C_mul_derivative {p : ℝ[X]} (hp : RealRooted p) (c : ℝ) :
    RealRooted (p + C c * derivative p) := by
  classical
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using hp
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [RealRooted]
  set q := p + C c * derivative p with hq
  have hdeg : q.natDegree = p.natDegree := by
    rcases eq_or_ne p.natDegree 0 with h0 | h0
    · rw [hq, derivative_of_natDegree_zero h0, mul_zero, add_zero]
    · exact natDegree_add_eq_left_of_natDegree_lt
        (lt_of_le_of_lt (natDegree_C_mul_le _ _) (natDegree_derivative_lt h0))
  have hq0 : q ≠ 0 := by
    rcases eq_or_ne p.natDegree 0 with h0 | h0
    · rw [hq, derivative_of_natDegree_zero h0, mul_zero, add_zero]
      exact hp0
    · intro h
      rw [h, natDegree_zero] at hdeg
      exact h0 hdeg.symm
  -- multiplicidades: uma raiz de multiplicidade `m` de `p` é raiz de multiplicidade `≥ m − 1` de `q`
  have hmult : ∀ x, p.rootMultiplicity x - 1 ≤ q.rootMultiplicity x := by
    intro x
    rw [le_rootMultiplicity_iff hq0]
    have h1 := pow_rootMultiplicity_dvd p x
    have h2 := pow_sub_one_dvd_derivative_of_pow_dvd h1
    have h3 : (X - C x) ^ (p.rootMultiplicity x - 1) ∣ p := (pow_dvd_pow _ (Nat.sub_le _ _)).trans h1
    exact h3.add (h2.mul_left _)
  -- entrelaçamento: entre raízes consecutivas de `p` há uma raiz de `q` (Rolle para `e^{x/c}p(x)`)
  have hinter : p.roots.toFinset.card ≤ (q.roots.toFinset \ p.roots.toFinset).card + 1 := by
    refine Finset.card_le_sdiff_of_interleaved fun x hx y hy hxy _ => ?_
    rw [Multiset.mem_toFinset, mem_roots hp0] at hx hy
    have hderiv : ∀ t, HasDerivAt (fun t => Real.exp (t / c) * p.eval t)
        (Real.exp (t / c) / c * q.eval t) t := by
      intro t
      have h1 : HasDerivAt (fun t => Real.exp (t / c)) (Real.exp (t / c) * (1 / c)) t := by
        have := ((hasDerivAt_id t).div_const c).exp
        simpa using this
      have h2 := h1.mul (p.hasDerivAt t)
      convert h2 using 1
      simp only [hq, eval_add, eval_mul, eval_C]
      field_simp
    have hfc : ContinuousOn (fun t => Real.exp (t / c) * p.eval t) (Set.Icc x y) :=
      (Continuous.continuousOn (by fun_prop))
    have hfI : (fun t => Real.exp (t / c) * p.eval t) x = (fun t => Real.exp (t / c) * p.eval t) y := by
      simp only [hx.eq_zero, hy.eq_zero, mul_zero]
    obtain ⟨z, hz, hz0⟩ := exists_hasDerivAt_eq_zero hxy hfc hfI (fun t _ => hderiv t)
    refine ⟨z, ?_, hz.1, hz.2⟩
    rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot]
    have hne : Real.exp (z / c) / c ≠ 0 := div_ne_zero (Real.exp_pos _).ne' hc
    exact (mul_eq_zero.mp hz0).resolve_left hne
  apply realRooted_of_card
  rw [hdeg, ← hp]
  calc Multiset.card p.roots = ∑ x ∈ p.roots.toFinset, p.roots.count x :=
        (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x ∈ p.roots.toFinset, (p.roots.count x - 1 + 1) :=
        (Eq.symm <| Finset.sum_congr rfl fun _ hx => tsub_add_cancel_of_le <|
          Nat.succ_le_iff.2 <| Multiset.count_pos.2 <| Multiset.mem_toFinset.1 hx)
    _ = (∑ x ∈ p.roots.toFinset, (p.rootMultiplicity x - 1)) + p.roots.toFinset.card := by
        simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones, count_roots]
    _ ≤ (∑ x ∈ p.roots.toFinset, q.rootMultiplicity x) +
          ((q.roots.toFinset \ p.roots.toFinset).card + 1) :=
        add_le_add (Finset.sum_le_sum fun x _ => hmult x) hinter
    _ ≤ (∑ x ∈ p.roots.toFinset, q.roots.count x) +
          ((∑ x ∈ q.roots.toFinset \ p.roots.toFinset, q.roots.count x) + 1) := by
        simp only [← count_roots, Finset.card_eq_sum_ones]
        gcongr with x hx
        rw [Nat.succ_le_iff, Multiset.count_pos, ← Multiset.mem_toFinset]
        exact (Finset.mem_sdiff.1 hx).1
    _ = Multiset.card q.roots + 1 := by
        rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union,
          ← Multiset.toFinset_sum_count_eq, ← Finset.sum_subset Finset.subset_union_right]
        intro x _ hx₂
        simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx₂

/-- **`p − λp''` tem raízes reais** (`λ ≥ 0`): `1 − λD² = (1 + √λD)(1 − √λD)`. -/
theorem realRooted_sub_derivative2 {p : ℝ[X]} (hp : RealRooted p) {l : ℝ} (hl : 0 ≤ l) :
    RealRooted (p - C l * derivative (derivative p)) := by
  have h1 := realRooted_add_C_mul_derivative hp (-Real.sqrt l)
  have h2 := realRooted_add_C_mul_derivative h1 (Real.sqrt l)
  have hs : C (Real.sqrt l) * C (Real.sqrt l) = C l := by
    rw [← C_mul, Real.mul_self_sqrt hl]
  have e : p + C (-Real.sqrt l) * derivative p + C (Real.sqrt l) *
      derivative (p + C (-Real.sqrt l) * derivative p) = p - C l * derivative (derivative p) := by
    rw [derivative_add, derivative_C_mul, map_neg]
    linear_combination (-(derivative (derivative p))) * hs
  rw [← e]
  exact h2

/-- O passo do fluxo do calor discreto, `f ↦ f − λf''`. -/
noncomputable def passoCalor (l : ℝ) (f : ℝ[X]) : ℝ[X] := f - C l * derivative (derivative f)

/-- **`(1 − λD²)^N p` tem raízes reais** (`λ ≥ 0`); com `λ = t/N`, o análogo discreto de `e^{−tD²}`. -/
theorem realRooted_iter {p : ℝ[X]} (hp : RealRooted p) {l : ℝ} (hl : 0 ≤ l) (N : ℕ) :
    RealRooted ((passoCalor l)^[N] p) := by
  induction N with
  | zero => simpa using hp
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    exact realRooted_sub_derivative2 ih hl

/-- O fluxo direto não preserva: `X²` tem raízes reais, `(1 + D²)X² = X² + 2` não tem. -/
theorem calor_direto_falha :
    RealRooted (X ^ 2) ∧ ¬ RealRooted (X ^ 2 - C (-1) * derivative (derivative (X ^ 2))) := by
  constructor
  · simp [RealRooted]
  · have e : (X ^ 2 - C (-1) * derivative (derivative (X ^ 2)) : ℝ[X]) = X ^ 2 + C 2 := by
      simp only [derivative_X_pow, map_neg, derivative_mul, derivative_C, zero_mul, zero_add]
      norm_num
    rw [e]
    intro h
    have hdeg : (X ^ 2 + C 2 : ℝ[X]).natDegree = 2 := natDegree_X_pow_add_C
    have hne : (X ^ 2 + C 2 : ℝ[X]) ≠ 0 := by
      intro h0
      rw [h0, natDegree_zero] at hdeg
      exact absurd hdeg (by norm_num)
    have hr : (X ^ 2 + C 2 : ℝ[X]).roots = 0 := by
      refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
      rw [mem_roots hne, IsRoot, eval_add, eval_pow, eval_X, eval_C] at hx
      nlinarith [sq_nonneg x]
    unfold RealRooted at h
    rw [hr, hdeg] at h
    simp at h

end ATK.Laguerre

#print axioms ATK.Laguerre.realRooted_iff_splits
#print axioms ATK.Laguerre.realRooted_of_card
#print axioms ATK.Laguerre.realRooted_add_C_mul_derivative
#print axioms ATK.Laguerre.realRooted_sub_derivative2
#print axioms ATK.Laguerre.realRooted_iter
#print axioms ATK.Laguerre.calor_direto_falha
