import ATK.LaguerrePolya

/-!
# ATK — Pólya–de Bruijn para polinômios: `e^{−λD²}` preserva raízes reais (`λ ≥ 0`)

Completa `ATK/LaguerrePolya.lean` com a passagem ao limite:

* **Cota de Hurwitz** (`norm_eval_ge`): se `p ∈ ℝ[X]` tem só raízes reais, `|p(z)| ≥ |a|·|Im z|ⁿ` em `ℂ`.
* **Hurwitz para polinômios** (`realRooted_of_tendsto`): um limite coeficiente a coeficiente de polinômios de grau
  `n` com só raízes reais, cujo coeficiente `n` do limite é `≠ 0`, tem só raízes reais (um zero não real `z₀` do
  limite daria `0 < |a||Im z₀|ⁿ ≤ |f_N(z₀)| → 0`).
* `iter_passoCalor`: `(1 − λD²)^N p = Σ_m C(N,m)(−λ)^m D^{2m}p` (binômio em `Module.End`);
  `tendsto_choose_div_pow`: `C(N,m)/N^m → 1/m!`; `tendsto_iter_calor`: `(1 − (λ/N)D²)^N p → e^{−λD²}p`
  coeficiente a coeficiente, com `e^{−λD²}p = Σ_m (−λ)^m/m!·D^{2m}p` (`calorExato`, soma finita).
* **`realRooted_calorExato`**: `p` com só raízes reais e `λ ≥ 0` ⇒ `e^{−λD²}p` com só raízes reais (Pólya 1913;
  é o caso polinomial do fechamento para cima de de Bruijn, `ATK.DBN`).

Para `H_t` falta (`BUILD_PENDING`) aproximar `H₀` por polinômios com raízes reais (o que já pressupõe HR) e o
teorema de Hurwitz para funções inteiras; nada disto prova HR.
-/

open Polynomial Filter Topology Finset

namespace ATK.PolyaCalor

open ATK.Laguerre

/-! ## 1. Hurwitz para polinômios -/

theorem aux_prod (z : ℂ) (s : Multiset ℝ) :
    |z.im| ^ Multiset.card s ≤ ‖(((s.map fun a => X - C a).prod).map (algebraMap ℝ ℂ)).eval z‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul, eval_mul, norm_mul,
      Multiset.card_cons, pow_succ']
    have h1 : |z.im| ≤ ‖((X - C r).map (algebraMap ℝ ℂ)).eval z‖ := by
      have := Complex.abs_im_le_norm (z - (r : ℂ))
      simpa using this
    exact mul_le_mul h1 ih (by positivity) (norm_nonneg _)

/-- **Cota de Hurwitz**: `|p(z)| ≥ |a|·|Im z|ⁿ` se `p` tem só raízes reais. -/
theorem norm_eval_ge {p : ℝ[X]} (hp : RealRooted p) (z : ℂ) :
    |p.leadingCoeff| * |z.im| ^ p.natDegree ≤ ‖(p.map (algebraMap ℝ ℂ)).eval z‖ := by
  have hfac : C p.leadingCoeff * (p.roots.map fun a => X - C a).prod = p :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C hp
  have h := aux_prod z p.roots
  rw [hp] at h
  conv_rhs => rw [← hfac]
  rw [Polynomial.map_mul, eval_mul, norm_mul, map_C, eval_C]
  have e : ‖(algebraMap ℝ ℂ) p.leadingCoeff‖ = |p.leadingCoeff| := by simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- **Hurwitz para polinômios**: limites coeficiente a coeficiente de polinômios de grau `n` com só raízes
reais, com coeficiente `n` do limite `≠ 0`, têm só raízes reais. -/
theorem realRooted_of_tendsto {f : ℕ → ℝ[X]} {g : ℝ[X]} {n : ℕ}
    (hf : ∀ N, RealRooted (f N)) (hdeg : ∀ N, (f N).natDegree = n)
    (hlim : ∀ k, Tendsto (fun N => (f N).coeff k) atTop (𝓝 (g.coeff k)))
    (hg : g.coeff n ≠ 0) : RealRooted g := by
  have hgk : ∀ k, n < k → g.coeff k = 0 := by
    intro k hk
    have h0 : ∀ N, (f N).coeff k = 0 := fun N =>
      coeff_eq_zero_of_natDegree_lt (by rw [hdeg N]; exact hk)
    have h1 := hlim k
    simp only [h0] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  have hgdeg : g.natDegree = n :=
    natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr hgk) hg
  by_contra hnot
  obtain ⟨q, hq, hcard, hqroots⟩ := exists_prod_multiset_X_sub_C_mul g
  have hcle := card_roots' g
  have hq1 : 0 < q.natDegree := by
    unfold RealRooted at hnot
    omega
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hq1
  have hdq : 0 < (q.map (algebraMap ℝ ℂ)).degree := by
    rw [degree_map]
    exact natDegree_pos_iff_degree_pos.mp hq1
  obtain ⟨z₀, hz₀⟩ := Complex.exists_root hdq
  have him : z₀.im ≠ 0 := by
    intro h0
    have hz : z₀ = algebraMap ℝ ℂ z₀.re := Complex.ext (by simp) (by simp [h0])
    rw [hz, IsRoot.def, eval_map, eval₂_at_apply, map_eq_zero] at hz₀
    have hmem : z₀.re ∈ q.roots := (mem_roots hq0).mpr hz₀
    rw [hqroots] at hmem
    simp at hmem
  have hgz : (g.map (algebraMap ℝ ℂ)).eval z₀ = 0 := by
    rw [← hq, Polynomial.map_mul, eval_mul, hz₀.eq_zero, mul_zero]
  have e : ∀ h : ℝ[X], h.natDegree ≤ n → (h.map (algebraMap ℝ ℂ)).eval z₀ =
      ∑ i ∈ range (n + 1), algebraMap ℝ ℂ (h.coeff i) * z₀ ^ i := by
    intro h hh
    rw [eval_eq_sum_range' (n := n + 1) (by rw [natDegree_map]; omega)]
    simp only [coeff_map]
  have hconv : Tendsto (fun N => ((f N).map (algebraMap ℝ ℂ)).eval z₀) atTop
      (𝓝 ((g.map (algebraMap ℝ ℂ)).eval z₀)) := by
    rw [funext fun N => e (f N) (hdeg N).le, e g hgdeg.le]
    refine tendsto_finset_sum _ fun i _ => ?_
    exact (((continuous_algebraMap ℝ ℂ).tendsto _).comp (hlim i)).mul_const _
  have hlow : ∀ N, |(f N).coeff n| * |z₀.im| ^ n ≤ ‖((f N).map (algebraMap ℝ ℂ)).eval z₀‖ := by
    intro N
    have h := norm_eval_ge (hf N) z₀
    rwa [leadingCoeff, hdeg N] at h
  have hL : Tendsto (fun N => |(f N).coeff n| * |z₀.im| ^ n) atTop (𝓝 (|g.coeff n| * |z₀.im| ^ n)) :=
    ((hlim n).abs).mul_const _
  have hR : Tendsto (fun N => ‖((f N).map (algebraMap ℝ ℂ)).eval z₀‖) atTop (𝓝 0) := by
    have h := hconv.norm
    rwa [hgz, norm_zero] at h
  have hle := le_of_tendsto_of_tendsto' hL hR hlow
  have hpos : 0 < |g.coeff n| * |z₀.im| ^ n :=
    mul_pos (abs_pos.mpr hg) (pow_pos (abs_pos.mpr him) n)
  linarith

/-! ## 2. `(1 − λD²)^N` e `e^{−λD²}` -/

theorem natDegree_passoCalor (l : ℝ) (f : ℝ[X]) : (passoCalor l f).natDegree = f.natDegree := by
  unfold passoCalor
  rcases eq_or_ne f.natDegree 0 with h0 | h0
  · rw [derivative_of_natDegree_zero h0, derivative_zero, mul_zero, sub_zero]
  · apply natDegree_sub_eq_left_of_natDegree_lt
    calc (C l * derivative (derivative f)).natDegree ≤ (derivative (derivative f)).natDegree :=
          natDegree_C_mul_le _ _
      _ ≤ (derivative f).natDegree := (natDegree_derivative_le _).trans (Nat.sub_le _ _)
      _ < f.natDegree := natDegree_derivative_lt h0

theorem coeff_natDegree_passoCalor (l : ℝ) (f : ℝ[X]) :
    (passoCalor l f).coeff f.natDegree = f.coeff f.natDegree := by
  unfold passoCalor
  rw [coeff_sub, coeff_C_mul, coeff_derivative, coeff_derivative,
    coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < f.natDegree + 1 + 1)]
  simp

theorem natDegree_iter (l : ℝ) (p : ℝ[X]) (N : ℕ) : ((passoCalor l)^[N] p).natDegree = p.natDegree := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply', natDegree_passoCalor, ih]

theorem coeff_iter (l : ℝ) (p : ℝ[X]) (N : ℕ) :
    ((passoCalor l)^[N] p).coeff p.natDegree = p.coeff p.natDegree := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply']
    have h := coeff_natDegree_passoCalor l ((passoCalor l)^[N] p)
    rw [natDegree_iter] at h
    rw [h, ih]

/-- **`(1 − λD²)^N p = Σ_{m ≤ N} C(N,m)(−λ)^m D^{2m}p`.** -/
theorem iter_passoCalor (l : ℝ) (p : ℝ[X]) (N : ℕ) :
    (passoCalor l)^[N] p =
      ∑ m ∈ range (N + 1), ((N.choose m : ℝ) * (-l) ^ m) • derivative^[2 * m] p := by
  let D : Module.End ℝ ℝ[X] := derivative
  have hstep : passoCalor l = ⇑(((-l) • D ^ 2 + 1 : Module.End ℝ ℝ[X])) := by
    funext f
    show f - C l * derivative (derivative f) = ((-l) • D ^ 2 + 1 : Module.End ℝ ℝ[X]) f
    rw [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, pow_two, Module.End.mul_apply,
      C_mul', neg_smul]
    abel
  rw [hstep, ← Module.End.coe_pow, (Commute.one_right _).add_pow, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_pow, mul_one, _root_.smul_pow, ← pow_mul, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.natCast_apply, map_nsmul, Module.End.pow_apply]
  module

/-- `C(N,m)/N^m → 1/m!`. -/
theorem tendsto_choose_div_pow (m : ℕ) :
    Tendsto (fun N : ℕ => (N.choose m : ℝ) / (N : ℝ) ^ m) atTop (𝓝 (1 / m.factorial)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : Tendsto (fun N : ℕ => (1 - (m : ℝ) / N) / (m + 1)) atTop (𝓝 (1 / (m + 1))) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_const_div_atTop_nhds_zero_nat (m : ℝ))
      simpa using this.div_const ((m : ℝ) + 1)
    have h2 := ih.mul h1
    have e : (1 : ℝ) / m.factorial * (1 / (m + 1)) = 1 / (m + 1).factorial := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp
    rw [e] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop m] with N hN
    have hc := Nat.choose_succ_right_eq N m
    have hc' : (N.choose (m + 1) : ℝ) * (m + 1) = N.choose m * ((N : ℝ) - m) := by
      have := congrArg (Nat.cast : ℕ → ℝ) hc
      push_cast [Nat.cast_sub hN.le] at this
      linarith
    have hN0 : (N : ℝ) ≠ 0 := by
      have : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
      exact this.ne'
    have key : (N.choose (m + 1) : ℝ) = N.choose m * ((N : ℝ) - m) / (m + 1) := by
      rw [eq_div_iff (by positivity)]
      exact hc'
    rw [key]
    field_simp
    ring

/-- **`e^{−λD²}p = Σ_{m ≤ n} (−λ)^m/m!·D^{2m}p`** (`n` o grau; os termos com `2m > n` são zero). -/
noncomputable def calorExato (l : ℝ) (p : ℝ[X]) : ℝ[X] :=
  ∑ m ∈ range (p.natDegree + 1), ((-l) ^ m / m.factorial) • derivative^[2 * m] p

theorem calorExato_zero (p : ℝ[X]) : calorExato 0 p = p := by
  rw [calorExato, Finset.sum_range_succ']
  simp

/-- **`(1 − (λ/N)D²)^N p → e^{−λD²}p`** coeficiente a coeficiente. -/
theorem tendsto_iter_calor (l : ℝ) (p : ℝ[X]) (k : ℕ) :
    Tendsto (fun N : ℕ => ((passoCalor (l / N))^[N] p).coeff k) atTop (𝓝 ((calorExato l p).coeff k)) := by
  set n := p.natDegree with hn
  have hfin : ∀ N : ℕ, n ≤ N → (passoCalor (l / N))^[N] p =
      ∑ m ∈ range (n + 1), ((N.choose m : ℝ) * (-(l / N)) ^ m) • derivative^[2 * m] p := by
    intro N hN
    rw [iter_passoCalor]
    symm
    apply Finset.sum_subset (range_subset_range.mpr (by omega))
    intro m hm hmn
    simp only [mem_range, not_lt] at hm hmn
    rw [iterate_derivative_eq_zero (by omega), smul_zero]
  have hcoef : ∀ m, Tendsto (fun N : ℕ => (N.choose m : ℝ) * (-(l / N)) ^ m) atTop
      (𝓝 ((-l) ^ m / m.factorial)) := by
    intro m
    have h := (tendsto_choose_div_pow m).const_mul ((-l) ^ m)
    rw [show (-l) ^ m * (1 / (m.factorial : ℝ)) = (-l) ^ m / m.factorial by ring] at h
    refine h.congr' (Eventually.of_forall fun N => ?_)
    show (-l) ^ m * ((N.choose m : ℝ) / (N : ℝ) ^ m) = (N.choose m : ℝ) * (-(l / N)) ^ m
    rw [← neg_div, div_pow]
    ring
  have hEv : ∀ᶠ N : ℕ in atTop, ((passoCalor (l / N))^[N] p).coeff k =
      ∑ m ∈ range (n + 1), ((N.choose m : ℝ) * (-(l / N)) ^ m) * (derivative^[2 * m] p).coeff k := by
    filter_upwards [eventually_ge_atTop n] with N hN
    rw [hfin N hN, finset_sum_coeff]
    simp only [coeff_smul, smul_eq_mul]
  have hT : Tendsto (fun N : ℕ => ∑ m ∈ range (n + 1),
      ((N.choose m : ℝ) * (-(l / N)) ^ m) * (derivative^[2 * m] p).coeff k) atTop
      (𝓝 (∑ m ∈ range (n + 1), (-l) ^ m / m.factorial * (derivative^[2 * m] p).coeff k)) :=
    tendsto_finset_sum _ fun m _ => (hcoef m).mul_const _
  have hcal : (calorExato l p).coeff k =
      ∑ m ∈ range (n + 1), (-l) ^ m / m.factorial * (derivative^[2 * m] p).coeff k := by
    rw [calorExato, finset_sum_coeff]
    simp only [coeff_smul, smul_eq_mul]
    rfl
  rw [hcal]
  exact hT.congr' (hEv.mono fun N h => h.symm)

/-- **Pólya–de Bruijn para polinômios**: `p` com só raízes reais e `λ ≥ 0` ⇒ `e^{−λD²}p` com só raízes
reais. -/
theorem realRooted_calorExato {p : ℝ[X]} (hp : RealRooted p) {l : ℝ} (hl : 0 ≤ l) :
    RealRooted (calorExato l p) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [calorExato, RealRooted]
  refine realRooted_of_tendsto (f := fun N : ℕ => (passoCalor (l / N))^[N] p) (n := p.natDegree)
    (fun N => realRooted_iter hp (div_nonneg hl (Nat.cast_nonneg N)) N)
    (fun N => natDegree_iter _ p N) (tendsto_iter_calor l p) ?_
  have h := tendsto_iter_calor l p p.natDegree
  simp only [coeff_iter] at h
  rw [← tendsto_nhds_unique tendsto_const_nhds h]
  exact leadingCoeff_ne_zero.mpr hp0

end ATK.PolyaCalor

#print axioms ATK.PolyaCalor.aux_prod
#print axioms ATK.PolyaCalor.norm_eval_ge
#print axioms ATK.PolyaCalor.realRooted_of_tendsto
#print axioms ATK.PolyaCalor.natDegree_passoCalor
#print axioms ATK.PolyaCalor.coeff_natDegree_passoCalor
#print axioms ATK.PolyaCalor.natDegree_iter
#print axioms ATK.PolyaCalor.coeff_iter
#print axioms ATK.PolyaCalor.iter_passoCalor
#print axioms ATK.PolyaCalor.tendsto_choose_div_pow
#print axioms ATK.PolyaCalor.calorExato_zero
#print axioms ATK.PolyaCalor.tendsto_iter_calor
#print axioms ATK.PolyaCalor.realRooted_calorExato
