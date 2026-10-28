import ATK.ProdutoresTN

/-!
# ATK — Polinômios de Jensen de `Ξ`: HR ⇒ todos hiperbólicos (Pólya), e Turán sob HR

Para `γ(k) = k!·aₖ` (os `aₖ` de `ATK.XiTP.aXi`; o fator 8 da normalização usual não muda as raízes), o polinômio
de Jensen de grau `d` e deslocamento `n` é `J^{d,n}(X) = Σ_{j≤d} C(d,j)γ(n+j)X^j` (`jensen`).

* `realRooted_jensen_of_genero0`: se `B(w) = a₀∏(1 + αⱼw)` coeficiente a coeficiente (`αⱼ ≥ 0`), **todos os
  `J^{d,n}` têm só raízes reais**. Prova: `Q_K = a₀∏_{i<K}(1 + αᵢD)X^d` tem raízes reais (Laguerre, rodada 12),
  `Q_K → Σ_k aₖ d^{(k)}X^{d−k}` (Hurwitz para polinômios), `J^{d,0}` é o reverso desse limite
  (`jensen_eq_reverse`, `realRooted_reverse`) e `Dⁿ J^{d+n,0} = (d+n)^{(n)}·J^{d,n}` (`iterate_derivative_jensen`).
* **`rh_jensen`: HR ⇒ todo `J^{d,n}` de `Ξ` é hiperbólico** (a direção de Pólya, 1927).
* **`turan_de_rh`**: sob HR, `γ(n)γ(n+2) ≤ γ(n+1)²` (`d = 2`). Junto com `ATK.XiMom.aXi_cota_superior`
  (incondicional, Cauchy–Schwarz), isso cerca `a_{n+1}²` por cima e por baixo.

A volta (todos os `J^{d,n}` hiperbólicos ⇒ HR) precisa de Hurwitz para funções inteiras: `BUILD_PENDING`. Os
resultados incondicionais conhecidos — Turán para todo `n` (Csordas–Norfolk–Varga 1986) e, para cada `d`, todos os
`n` suficientemente grandes (Griffin–Ono–Rolen–Zagier 2019) — não estão formalizados aqui. A hiperbolicidade de
todos os `J^{d,n}` é HR: `OPEN_MATH`.
-/

open Polynomial Filter Topology Finset
open scoped Nat

namespace ATK.JensenPolya

open ATK.Laguerre ATK.PolyaCalor ATK.Edrei ATK.XiTP ATK.XiCresc

/-! ## 1. Operações que preservam raízes reais -/

theorem realRooted_derivative {p : ℝ[X]} (hp : RealRooted p) : RealRooted (derivative p) := by
  apply realRooted_of_card
  have h1 := natDegree_derivative_le p
  have h2 := card_roots_le_derivative p
  unfold RealRooted at hp
  omega

theorem realRooted_iterate_derivative {p : ℝ[X]} (hp : RealRooted p) (n : ℕ) :
    RealRooted (derivative^[n] p) := by
  induction n with
  | zero => simpa using hp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact realRooted_derivative ih

theorem realRooted_C_mul {p : ℝ[X]} {c : ℝ} (hc : c ≠ 0) : RealRooted (C c * p) ↔ RealRooted p := by
  unfold RealRooted
  rw [roots_C_mul _ hc, natDegree_C_mul hc]

theorem splits_reverse_X_sub_C (r : ℝ) : (X - C r : ℝ[X]).reverse.Splits := by
  have hX : (X : ℝ[X]).reverse = 1 := by
    have h := reverse_X_mul (1 : ℝ[X])
    rw [mul_one] at h
    rw [h, ← C_1, reverse_C]
  have e : (X - C r : ℝ[X]).reverse = C (-r) * X + 1 := by
    rw [sub_eq_add_neg, ← C_neg, reverse_add_C, natDegree_X, pow_one, hX]
    ring
  rw [e]
  rcases eq_or_ne r 0 with rfl | hr
  · simp only [neg_zero, map_zero, zero_mul, zero_add]
    exact Splits.one
  · have e2 : C (-r) * X + 1 = C (-r) * (X + C (-r⁻¹)) := by
      rw [mul_add, ← C_mul, neg_mul_neg, mul_inv_cancel₀ hr, C_1]
    rw [e2]
    exact (Splits.X_add_C _).C_mul _

theorem splits_reverse {p : ℝ[X]} (hp : p.Splits) : p.reverse.Splits := by
  rw [hp.eq_prod_roots, reverse_mul_of_domain, reverse_C]
  refine Splits.C_mul ?_ _
  induction p.roots using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    rw [← C_1, reverse_C]
    exact Splits.C 1
  | cons r s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain]
    exact (splits_reverse_X_sub_C r).mul ih

/-- O reverso de um polinômio com só raízes reais tem só raízes reais. -/
theorem realRooted_reverse {p : ℝ[X]} (hp : RealRooted p) : RealRooted p.reverse :=
  (realRooted_iff_splits _).mpr (splits_reverse ((realRooted_iff_splits _).mp hp))

/-! ## 2. `Q_K = a₀∏_{i<K}(1 + αᵢD)X^d` e o limite -/

/-- `Q_K` pela recursão de Laguerre. -/
noncomputable def QK (a0 : ℝ) (α : ℕ → ℝ) (d : ℕ) : ℕ → ℝ[X]
  | 0 => C a0 * X ^ d
  | K + 1 => QK a0 α d K + C (α K) * derivative (QK a0 α d K)

theorem realRooted_QK (a0 : ℝ) (α : ℕ → ℝ) (d K : ℕ) : RealRooted (QK a0 α d K) := by
  induction K with
  | zero => exact (realRooted_iff_splits _).mpr (Splits.C_mul_X_pow a0 d)
  | succ K ih => exact realRooted_add_C_mul_derivative ih _

theorem prodCoef_zero_idx (a0 : ℝ) (α : ℕ → ℝ) : ∀ K, prodCoef a0 α K 0 = a0
  | 0 => by simp [prodCoef]
  | K + 1 => by simp [prodCoef, prodCoef_zero_idx a0 α K]

theorem coeff_QK (a0 : ℝ) (α : ℕ → ℝ) (d : ℕ) : ∀ K m, (QK a0 α d K).coeff m =
    if m ≤ d then prodCoef a0 α K (d - m) * (d.descFactorial (d - m) : ℝ) else 0
  | 0, m => by
    simp only [QK, coeff_C_mul_X_pow, prodCoef]
    by_cases h : m = d
    · subst h
      simp
    · by_cases h2 : m ≤ d
      · rw [if_neg h, if_pos h2, if_neg (by omega)]
        ring
      · rw [if_neg h, if_neg h2]
  | K + 1, m => by
    simp only [QK, coeff_add, coeff_C_mul, coeff_derivative, coeff_QK a0 α d K m,
      coeff_QK a0 α d K (m + 1)]
    rcases lt_trichotomy m d with h | h | h
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega),
        show m + k + 1 - m = k + 1 by omega, show m + k + 1 - (m + 1) = k by omega]
      simp only [prodCoef, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      rw [Nat.descFactorial_succ, show m + k + 1 - k = m + 1 by omega]
      push_cast
      ring
    · subst h
      rw [if_pos le_rfl, if_neg (by omega), if_pos le_rfl, Nat.sub_self]
      simp [prodCoef]
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      ring

theorem natDegree_QK {a0 : ℝ} (ha0 : a0 ≠ 0) (α : ℕ → ℝ) (d K : ℕ) : (QK a0 α d K).natDegree = d := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [coeff_QK, if_neg (by omega)]
  · rw [coeff_QK, if_pos le_rfl, Nat.sub_self, prodCoef_zero_idx]
    simpa using ha0

/-- O limite `Σ_k aₖ d^{(k)} X^{d−k}`. -/
noncomputable def QL (a : ℕ → ℝ) (d : ℕ) : ℝ[X] :=
  ∑ k ∈ range (d + 1), C (a k * (d.descFactorial k : ℝ)) * X ^ (d - k)

theorem coeff_QL (a : ℕ → ℝ) (d m : ℕ) :
    (QL a d).coeff m = if m ≤ d then a (d - m) * (d.descFactorial (d - m) : ℝ) else 0 := by
  unfold QL
  rw [finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  split_ifs with hm
  · rw [Finset.sum_eq_single (d - m)]
    · rw [if_pos (by omega)]
    · intro k hk hne
      rw [if_neg]
      intro h
      apply hne
      simp only [mem_range] at hk
      omega
    · intro h
      simp only [mem_range] at h
      omega
  · apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg]
    simp only [mem_range] at hk
    omega

theorem natDegree_QL {a : ℕ → ℝ} (ha0 : a 0 ≠ 0) (d : ℕ) : (QL a d).natDegree = d := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro m hm
    rw [coeff_QL, if_neg (by omega)]
  · rw [coeff_QL, if_pos le_rfl, Nat.sub_self]
    simpa using ha0

/-- `Q_K → QL` coeficiente a coeficiente, e o limite tem só raízes reais. -/
theorem realRooted_QL {a α : ℕ → ℝ} (ha0 : a 0 ≠ 0)
    (hlim : ∀ n, Tendsto (fun N => prodCoef (a 0) α N n) atTop (𝓝 (a n))) (d : ℕ) :
    RealRooted (QL a d) := by
  refine realRooted_of_tendsto (f := fun K => QK (a 0) α d K) (n := d)
    (fun K => realRooted_QK _ _ _ K) (fun K => natDegree_QK ha0 α d K) (fun m => ?_) ?_
  · simp only [coeff_QK, coeff_QL]
    split_ifs
    · exact (hlim _).mul_const _
    · exact tendsto_const_nhds
  · rw [coeff_QL, if_pos le_rfl, Nat.sub_self]
    simpa using ha0

/-! ## 3. Polinômios de Jensen -/

/-- **`J^{d,n}_γ(X) = Σ_{j≤d} C(d,j)γ(n+j)X^j`.** -/
noncomputable def jensen (γ : ℕ → ℝ) (d n : ℕ) : ℝ[X] :=
  ∑ j ∈ range (d + 1), C ((d.choose j : ℝ) * γ (n + j)) * X ^ j

theorem coeff_jensen (γ : ℕ → ℝ) (d n m : ℕ) :
    (jensen γ d n).coeff m = if m ≤ d then (d.choose m : ℝ) * γ (n + m) else 0 := by
  unfold jensen
  rw [finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp

/-- `J^{d,0}` (para `γ(k) = k!aₖ`) é o reverso de `QL`. -/
theorem jensen_eq_reverse {a : ℕ → ℝ} (ha0 : a 0 ≠ 0) (d : ℕ) :
    jensen (fun k => (k ! : ℝ) * a k) d 0 = (QL a d).reverse := by
  ext m
  rw [coeff_reverse, natDegree_QL ha0, coeff_jensen, coeff_QL]
  by_cases hm : m ≤ d
  · rw [revAt_le hm, if_pos hm, if_pos (by omega), show d - (d - m) = m by omega, zero_add,
      Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  · rw [revAt_eq_self_of_lt (by omega), if_neg hm, if_neg hm]

/-- `(i+n)^{(n)}·C(d+n, i+n) = (d+n)^{(n)}·C(d, i)`. -/
theorem desc_choose (d n i : ℕ) (hi : i ≤ d) :
    (i + n).descFactorial n * (d + n).choose (i + n) = (d + n).descFactorial n * d.choose i := by
  have h1 : (i + n).descFactorial n * i ! = (i + n)! := by
    have := Nat.factorial_mul_descFactorial (show n ≤ i + n by omega)
    rw [show i + n - n = i by omega] at this
    rw [mul_comm]
    exact this
  have h2 : (d + n).choose (i + n) * (i + n)! * (d - i)! = (d + n)! := by
    have := Nat.choose_mul_factorial_mul_factorial (show i + n ≤ d + n by omega)
    rwa [show d + n - (i + n) = d - i by omega] at this
  have h3 : d.choose i * i ! * (d - i)! = d ! := Nat.choose_mul_factorial_mul_factorial hi
  have h4 : (d + n).descFactorial n * d ! = (d + n)! := by
    have := Nat.factorial_mul_descFactorial (show n ≤ d + n by omega)
    rw [show d + n - n = d by omega] at this
    rw [mul_comm]
    exact this
  apply Nat.eq_of_mul_eq_mul_right (show 0 < i ! * (d - i)! by positivity)
  calc (i + n).descFactorial n * (d + n).choose (i + n) * (i ! * (d - i)!)
      = ((i + n).descFactorial n * i !) * ((d + n).choose (i + n) * (d - i)!) := by ring
    _ = (i + n)! * ((d + n).choose (i + n) * (d - i)!) := by rw [h1]
    _ = (d + n)! := by rw [← h2]; ring
    _ = (d + n).descFactorial n * d ! := h4.symm
    _ = (d + n).descFactorial n * (d.choose i * i ! * (d - i)!) := by rw [h3]
    _ = _ := by ring

/-- `Dⁿ J^{d+n,0} = (d+n)^{(n)}·J^{d,n}`. -/
theorem iterate_derivative_jensen (γ : ℕ → ℝ) (d n : ℕ) :
    derivative^[n] (jensen γ (d + n) 0) = C (((d + n).descFactorial n : ℕ) : ℝ) * jensen γ d n := by
  ext i
  rw [coeff_iterate_derivative, coeff_C_mul, coeff_jensen, coeff_jensen]
  by_cases hi : i ≤ d
  · rw [if_pos (by omega), if_pos hi, nsmul_eq_mul, zero_add,
      show γ (i + n) = γ (n + i) by rw [add_comm]]
    have key := congrArg (Nat.cast : ℕ → ℝ) (desc_choose d n i hi)
    push_cast at key
    linear_combination γ (n + i) * key
  · rw [if_neg (by omega), if_neg hi]
    simp

/-- **Se `B = a₀∏(1 + αⱼw)` coeficiente a coeficiente, todo `J^{d,n}` (de `γ(k) = k!aₖ`) tem só raízes
reais.** -/
theorem realRooted_jensen_of_genero0 {a α : ℕ → ℝ} (ha0 : a 0 ≠ 0)
    (hlim : ∀ n, Tendsto (fun N => prodCoef (a 0) α N n) atTop (𝓝 (a n))) (d n : ℕ) :
    RealRooted (jensen (fun k => (k ! : ℝ) * a k) d n) := by
  have h0 : RealRooted (jensen (fun k => (k ! : ℝ) * a k) (d + n) 0) := by
    rw [jensen_eq_reverse ha0]
    exact realRooted_reverse (realRooted_QL ha0 hlim (d + n))
  have h1 := realRooted_iterate_derivative h0 n
  rw [iterate_derivative_jensen] at h1
  have hne : (((d + n).descFactorial n : ℕ) : ℝ) ≠ 0 := by
    have : (d + n).descFactorial n ≠ 0 := fun h => by
      rw [Nat.descFactorial_eq_zero_iff_lt] at h
      omega
    exact_mod_cast this
  exact (realRooted_C_mul hne).mp h1

/-- `γ(k) = k!·aₖ` para `Ξ`. -/
noncomputable def γXi (k : ℕ) : ℝ := (k ! : ℝ) * aXi k

/-- **Pólya (direção ⇒): HR ⇒ todo polinômio de Jensen `J^{d,n}` de `Ξ` tem só raízes reais.** -/
theorem rh_jensen (h : RiemannHypothesis) (d n : ℕ) : RealRooted (jensen γXi d n) := by
  obtain ⟨α, _, _, hlim⟩ := rh_iff_genero0.mp h
  exact realRooted_jensen_of_genero0 aXi_zero_pos.ne' hlim d n

/-- **Turán sob HR**: `γ(n)γ(n+2) ≤ γ(n+1)²` (`J^{2,n}` hiperbólico). -/
theorem turan_de_rh (h : RiemannHypothesis) (n : ℕ) : γXi n * γXi (n + 2) ≤ γXi (n + 1) ^ 2 := by
  have hr := rh_jensen h 2 n
  have hpos : 0 < γXi (n + 2) := mul_pos (by positivity) (ATK.XiMom.aXi_pos _)
  have hdeg : (jensen γXi 2 n).natDegree = 2 := by
    refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro m hm
      rw [coeff_jensen, if_neg (by omega)]
    · rw [coeff_jensen, if_pos le_rfl]
      simpa using hpos.ne'
  have hcard : 0 < Multiset.card (jensen γXi 2 n).roots := by
    unfold RealRooted at hr
    omega
  obtain ⟨x, hx⟩ := Multiset.card_pos_iff_exists_mem.mp hcard
  have hne : jensen γXi 2 n ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdeg
    omega
  have hev := ((mem_roots hne).mp hx).eq_zero
  simp only [jensen, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add] at hev
  try simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X] at hev
  norm_num at hev
  have e : (γXi (n + 2) * x + γXi (n + 1)) ^ 2 = γXi (n + 1) ^ 2 - γXi n * γXi (n + 2) := by
    linear_combination γXi (n + 2) * hev
  nlinarith [sq_nonneg (γXi (n + 2) * x + γXi (n + 1))]

end ATK.JensenPolya

#print axioms ATK.JensenPolya.realRooted_derivative
#print axioms ATK.JensenPolya.realRooted_iterate_derivative
#print axioms ATK.JensenPolya.realRooted_C_mul
#print axioms ATK.JensenPolya.splits_reverse_X_sub_C
#print axioms ATK.JensenPolya.splits_reverse
#print axioms ATK.JensenPolya.realRooted_reverse
#print axioms ATK.JensenPolya.realRooted_QK
#print axioms ATK.JensenPolya.prodCoef_zero_idx
#print axioms ATK.JensenPolya.coeff_QK
#print axioms ATK.JensenPolya.natDegree_QK
#print axioms ATK.JensenPolya.coeff_QL
#print axioms ATK.JensenPolya.natDegree_QL
#print axioms ATK.JensenPolya.realRooted_QL
#print axioms ATK.JensenPolya.coeff_jensen
#print axioms ATK.JensenPolya.jensen_eq_reverse
#print axioms ATK.JensenPolya.desc_choose
#print axioms ATK.JensenPolya.iterate_derivative_jensen
#print axioms ATK.JensenPolya.realRooted_jensen_of_genero0
#print axioms ATK.JensenPolya.rh_jensen
#print axioms ATK.JensenPolya.turan_de_rh
