import ATK.Cert.Intervalo

/-!
# Funções transcendentes certificadas: `e^{iθ}`, `log n`, `√n` (fase 2)

* `tayI`: a soma de Taylor `Σ_{k<n} (iθ)^k/k!` em aritmética racional exata; `mem_expIRect`:
  `e^{iθ}` está no retângulo `T ± 2|θ|^n/n!` se `|θ|/(n+1) ≤ 1/2` (`Complex.exp_bound'`).
* `mem_expIAuto`: `e^{iθ}` para `θ` real num intervalo, com redução por `2kπ` usando
  `3,14159265358979323846 < π < 3,14159265358979323847` (Mathlib) e a cota de Lipschitz
  `|e^{ix} − e^{iy}| ≤ |x − y|`.
* `mem_logI`: `log n = Σ_{j<n} [log(j+1) − log j]`, cada parcela pela série de `atanh` com resto
  geométrico.
* `mem_sqrtI`: `√n` a partir de um certificado racional `lo² ≤ n ≤ hi²`.
-/

open Complex Real Filter Topology

namespace ATK.Cert

/-! ### Taylor de `e^{iθ}` em racionais -/

/-- `((Σ_{k<n} (iθ)^k/k!), (iθ)^n/n!)` como pares (re, im) racionais. -/
def tayI : ℕ → ℚ → (ℚ × ℚ) × (ℚ × ℚ)
  | 0, _ => ((0, 0), (1, 0))
  | n + 1, m =>
    let r := tayI n m
    ((r.1.1 + r.2.1, r.1.2 + r.2.2), (-(r.2.2 * m) / (n + 1), r.2.1 * m / (n + 1)))

theorem tayI_spec (n : ℕ) (m : ℚ) :
    (((tayI n m).1.1 : ℂ) + ((tayI n m).1.2 : ℂ) * I =
        ∑ k ∈ Finset.range n, (I * (m : ℂ)) ^ k / (k.factorial : ℂ)) ∧
      (((tayI n m).2.1 : ℂ) + ((tayI n m).2.2 : ℂ) * I = (I * (m : ℂ)) ^ n / (n.factorial : ℂ)) := by
  induction n with
  | zero => simp [tayI]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [tayI]
    constructor
    · rw [Finset.sum_range_succ, ← h1, ← h2]; push_cast; ring
    · rw [pow_succ, Nat.factorial_succ]
      push_cast
      have hf : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      rw [show (I * (m : ℂ)) ^ n * (I * m) / (((n : ℂ) + 1) * (n.factorial : ℂ)) =
          ((I * (m : ℂ)) ^ n / (n.factorial : ℂ)) * (I * m) / ((n : ℂ) + 1) by field_simp]
      rw [← h2]
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring

/-- Retângulo para `e^{im}`, `m` racional: centro de Taylor `± 2|m|^n/n!`. -/
def expIRect (n : ℕ) (m : ℚ) : IC :=
  IC.widen (IC.pt (tayI n m).1.1 (tayI n m).1.2) (|m| ^ n / n.factorial * 2)

theorem mem_expIRect {n : ℕ} {m : ℚ} (h : |m| / (n + 1) ≤ 1 / 2) :
    IC.mem (Complex.exp (I * (m : ℂ))) (expIRect n m) := by
  unfold expIRect
  refine IC.mem_widen_of_norm (IC.mem_pt _ _) ?_
  rw [(tayI_spec n m).1]
  have hnorm : ‖I * (m : ℂ)‖ = |(m : ℝ)| := by simp
  have hx : ‖I * (m : ℂ)‖ / (n.succ : ℝ) ≤ 1 / 2 := by
    rw [hnorm]
    have : (|m| / (n + 1) : ℚ) ≤ 1 / 2 := h
    have h' : (((|m| / (n + 1) : ℚ)) : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    simpa [Nat.succ_eq_add_one] using h'
  have hb := Complex.exp_bound' hx
  rw [hnorm] at hb
  refine hb.trans (le_of_eq ?_)
  push_cast
  ring

/-- `|e^{ix} − e^{iy}| ≤ |x − y|`. -/
theorem norm_expI_sub_le (x y : ℝ) :
    ‖Complex.exp (I * x) - Complex.exp (I * y)‖ ≤ |x - y| := by
  have e : Complex.exp (I * x) - Complex.exp (I * y) =
      Complex.exp (I * y) * (Complex.exp (I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
  rw [e, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have := Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y)
  simpa using this

/-! ### `e^{iθ}` com `θ` num intervalo -/

/-- `π` com 20 casas: `πlo < π < πlo + 10^{-20}`. -/
def piLo : ℚ := 314159265358979323846 / 10 ^ 20

theorem piLo_lt : (piLo : ℝ) < π := by
  have := Real.pi_gt_d20; unfold piLo; push_cast; linarith

theorem lt_piLo_add : π < (piLo : ℝ) + 1 / 10 ^ 20 := by
  have := Real.pi_lt_d20; unfold piLo; push_cast; linarith

/-- Redução: `k = round(meio/2π)`, `m` = meio reduzido (arredondado), `e` = meia largura + erros. -/
def redK (Θ : IR) : ℤ := ⌊(Θ.lo + Θ.hi) / 2 / (2 * piLo) + 1 / 2⌋

def redM (p : ℕ) (Θ : IR) : ℚ :=
  (⌊((Θ.lo + Θ.hi) / 2 - 2 * redK Θ * piLo) * 2 ^ p⌋ : ℚ) / 2 ^ p

def redE (p : ℕ) (Θ : IR) : ℚ :=
  (Θ.hi - Θ.lo) / 2 + |(Θ.lo + Θ.hi) / 2 - 2 * redK Θ * piLo - redM p Θ| + 2 * |(redK Θ : ℚ)| / 10 ^ 20

/-- O retângulo final para `e^{iθ}`. -/
def expIAuto (n p : ℕ) (Θ : IR) : IC := IC.widen (expIRect n (redM p Θ)) (redE p Θ)

/-- Condição verificável: Taylor converge no ponto reduzido. -/
def expIAuto_ok (n p : ℕ) (Θ : IR) : Bool := decide (|redM p Θ| / (n + 1) ≤ 1 / 2)

theorem mem_expIAuto {n p : ℕ} {Θ : IR} {θ : ℝ} (hok : expIAuto_ok n p Θ = true)
    (hθ : IR.mem θ Θ) : IC.mem (Complex.exp (I * θ)) (expIAuto n p Θ) := by
  unfold expIAuto_ok at hok
  have hm : |redM p Θ| / (n + 1) ≤ 1 / 2 := of_decide_eq_true hok
  have hper : Complex.exp (I * θ) =
      Complex.exp (I * ((θ - 2 * ((redK Θ : ℤ) : ℝ) * π : ℝ) : ℂ)) := by
    have : I * ((θ - 2 * ((redK Θ : ℤ) : ℝ) * π : ℝ) : ℂ) =
        I * θ - ((redK Θ : ℤ) : ℂ) * (2 * π * I) := by push_cast; ring
    rw [this, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]
  unfold expIAuto
  rw [hper]
  refine IC.mem_widen_of_norm (mem_expIRect hm) ?_
  refine (norm_expI_sub_le _ _).trans ?_
  obtain ⟨h1, h2⟩ := hθ
  have hpi1 := piLo_lt
  have hpi2 := lt_piLo_add
  have hE : ((redE p Θ : ℚ) : ℝ) = ((Θ.hi : ℝ) - Θ.lo) / 2 +
      |((Θ.lo : ℝ) + Θ.hi) / 2 - 2 * ((redK Θ : ℤ) : ℝ) * (piLo : ℝ) - (redM p Θ : ℝ)| +
      2 * |((redK Θ : ℤ) : ℝ)| / 10 ^ 20 := by
    unfold redE; push_cast; ring_nf
  rw [hE]
  set K : ℝ := ((redK Θ : ℤ) : ℝ)
  set M : ℝ := (redM p Θ : ℝ)
  set L : ℝ := (Θ.lo : ℝ)
  set H : ℝ := (Θ.hi : ℝ)
  set P : ℝ := (piLo : ℝ)
  have hA : |θ - (L + H) / 2| ≤ (H - L) / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hB : |2 * K * π - 2 * K * P| ≤ 2 * |K| / 10 ^ 20 := by
    have e : 2 * K * π - 2 * K * P = 2 * K * (π - P) := by ring
    rw [e, abs_mul, abs_mul, abs_two]
    have hd : |π - P| ≤ 1 / 10 ^ 20 := abs_le.mpr ⟨by linarith, by linarith⟩
    have : (0 : ℝ) ≤ 2 * |K| := by positivity
    calc 2 * |K| * |π - P| ≤ 2 * |K| * (1 / 10 ^ 20) := mul_le_mul_of_nonneg_left hd this
      _ = 2 * |K| / 10 ^ 20 := by ring
  have hT : |(θ - 2 * K * π) - M| ≤
      |θ - (L + H) / 2| + |(L + H) / 2 - 2 * K * P - M| + |2 * K * π - 2 * K * P| := by
    have e : (θ - 2 * K * π) - M =
        ((θ - (L + H) / 2) + ((L + H) / 2 - 2 * K * P - M)) - (2 * K * π - 2 * K * P) := by ring
    rw [e]
    have := abs_sub ((θ - (L + H) / 2) + ((L + H) / 2 - 2 * K * P - M)) (2 * K * π - 2 * K * P)
    have := abs_add_le (θ - (L + H) / 2) ((L + H) / 2 - 2 * K * P - M)
    linarith
  linarith

/-! ### `log n` pela série de `atanh` -/

/-- `Σ_{k<K} 2x^{2k+1}/(2k+1)`. -/
def atS (K : ℕ) (x : ℚ) : ℚ := ∑ k ∈ Finset.range K, 2 * x ^ (2 * k + 1) / (2 * k + 1)

/-- Intervalo para `log(j+1) − log j`, `j ≥ 1`. -/
def dLog (K j : ℕ) : IR :=
  let x : ℚ := 1 / (2 * j + 1)
  ⟨atS K x, atS K x + 2 * x ^ (2 * K + 1) / ((2 * K + 1) * (1 - x ^ 2))⟩

theorem atS_cast (K : ℕ) (q : ℚ) :
    ((atS K q : ℚ) : ℝ) = ∑ k ∈ Finset.range K, 2 * (1 / (2 * (k : ℝ) + 1)) * (q : ℝ) ^ (2 * k + 1) := by
  unfold atS; push_cast; refine Finset.sum_congr rfl fun k _ => ?_; ring

theorem mem_dLog (K : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    IR.mem (Real.log (j + 1) - Real.log j) (dLog K j) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  set q : ℚ := 1 / (2 * j + 1) with hq
  have hqx : (q : ℝ) = 1 / (2 * (j : ℝ) + 1) := by rw [hq]; push_cast; ring
  have hx0 : (0 : ℝ) < q := by rw [hqx]; positivity
  have hx1 : (q : ℝ) < 1 := by rw [hqx, div_lt_one (by positivity)]; linarith
  have habs : |(q : ℝ)| < 1 := by rw [abs_of_pos hx0]; exact hx1
  have hS := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hval : Real.log (1 + (q : ℝ)) - Real.log (1 - (q : ℝ)) = Real.log (j + 1) - Real.log j := by
    rw [hqx]
    have h1 : 1 + 1 / (2 * (j : ℝ) + 1) = (2 * (j + 1)) / (2 * j + 1) := by field_simp; ring
    have h2 : 1 - 1 / (2 * (j : ℝ) + 1) = (2 * j) / (2 * j + 1) := by field_simp; ring
    rw [h1, h2, Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by positivity)]
    ring
  rw [hval] at hS
  set f : ℕ → ℝ := fun k => 2 * (1 / (2 * k + 1)) * (q : ℝ) ^ (2 * k + 1) with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => by positivity
  have hpart : ((atS K q : ℚ) : ℝ) = ∑ k ∈ Finset.range K, f k := by rw [atS_cast]
  have hbound : (((2 * q ^ (2 * K + 1) / ((2 * K + 1) * (1 - q ^ 2)) : ℚ)) : ℝ) =
      2 * (q : ℝ) ^ (2 * K + 1) / ((2 * K + 1) * (1 - (q : ℝ) ^ 2)) := by push_cast; ring
  have htail : ∑' k, f (k + K) ≤ 2 * (q : ℝ) ^ (2 * K + 1) / ((2 * K + 1) * (1 - (q : ℝ) ^ 2)) := by
    have hx2 : (q : ℝ) ^ 2 < 1 := by nlinarith
    have hgeo : HasSum (fun k : ℕ => 2 * (q : ℝ) ^ (2 * K + 1) / (2 * K + 1) * ((q : ℝ) ^ 2) ^ k)
        (2 * (q : ℝ) ^ (2 * K + 1) / (2 * K + 1) * (1 - (q : ℝ) ^ 2)⁻¹) :=
      (hasSum_geometric_of_lt_one (by positivity) hx2).mul_left _
    have hle : ∀ k, f (k + K) ≤ 2 * (q : ℝ) ^ (2 * K + 1) / (2 * K + 1) * ((q : ℝ) ^ 2) ^ k := by
      intro k
      simp only [hf]
      have hp : (q : ℝ) ^ (2 * (k + K) + 1) = (q : ℝ) ^ (2 * K + 1) * ((q : ℝ) ^ 2) ^ k := by
        rw [← pow_mul, ← pow_add]; congr 1; ring
      push_cast
      rw [hp]
      have hden : (2 * K + 1 : ℝ) ≤ 2 * ((k : ℝ) + K) + 1 := by
        have : (0 : ℝ) ≤ k := k.cast_nonneg; linarith
      have hpos : 0 ≤ (q : ℝ) ^ (2 * K + 1) * ((q : ℝ) ^ 2) ^ k := by positivity
      rw [show 2 * (q : ℝ) ^ (2 * K + 1) / (2 * K + 1) * ((q : ℝ) ^ 2) ^ k =
        2 * (1 / (2 * K + 1)) * ((q : ℝ) ^ (2 * K + 1) * ((q : ℝ) ^ 2) ^ k) by ring]
      gcongr
    have := (hS.summable.comp_injective (add_left_injective K)).tsum_le_tsum hle hgeo.summable
    rw [hgeo.tsum_eq] at this
    refine this.trans (le_of_eq ?_)
    field_simp
  unfold dLog IR.mem
  dsimp only
  rw [← hq]
  constructor
  · rw [hpart]; exact sum_le_hasSum (Finset.range K) (fun k _ => hf0 k) hS
  · have hsplit := hS.summable.sum_add_tsum_nat_add K
    rw [hS.tsum_eq] at hsplit
    rw [Rat.cast_add, hbound, hpart, ← hsplit]
    linarith

/-- `log n` como soma telescópica de `dLog`. -/
def logI (K : ℕ) : ℕ → IR
  | 0 => ⟨0, 0⟩
  | 1 => ⟨0, 0⟩
  | j + 2 => IR.add (logI K (j + 1)) (dLog K (j + 1))

theorem mem_logI (K : ℕ) : ∀ n : ℕ, 1 ≤ n → IR.mem (Real.log n) (logI K n)
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp [logI, IR.mem]
  | j + 2, _ => by
    have ih := mem_logI K (j + 1) (by omega)
    have hd := mem_dLog K (j := j + 1) (by omega)
    have e : Real.log ((j + 2 : ℕ) : ℝ) =
        Real.log ((j + 1 : ℕ) : ℝ) + (Real.log ((j + 1 : ℕ) + 1) - Real.log ((j + 1 : ℕ) : ℝ)) := by
      push_cast; ring_nf
    rw [e]
    simp only [logI]
    exact IR.mem_add ih (by push_cast at hd ⊢; exact hd)

/-! ### `√n` por certificado -/

/-- Verificação `0 ≤ lo`, `lo² ≤ n ≤ hi²`, `0 ≤ hi`. -/
def sqrtOk (n : ℕ) (lo hi : ℚ) : Bool := decide (0 ≤ lo ∧ lo ^ 2 ≤ n ∧ (n : ℚ) ≤ hi ^ 2 ∧ 0 ≤ hi)

theorem mem_sqrtI {n : ℕ} {lo hi : ℚ} (h : sqrtOk n lo hi = true) :
    IR.mem (Real.sqrt n) ⟨lo, hi⟩ := by
  unfold sqrtOk at h
  obtain ⟨h0, h1, h2, h3⟩ := of_decide_eq_true h
  have h0' : (0 : ℝ) ≤ lo := by exact_mod_cast h0
  have h1' : ((lo : ℝ)) ^ 2 ≤ n := by exact_mod_cast h1
  have h2' : (n : ℝ) ≤ (hi : ℝ) ^ 2 := by exact_mod_cast h2
  have h3' : (0 : ℝ) ≤ hi := by exact_mod_cast h3
  constructor
  · exact Real.le_sqrt_of_sq_le h1'
  · exact Real.sqrt_le_iff.mpr ⟨h3', h2'⟩

end ATK.Cert

#print axioms ATK.Cert.tayI_spec
#print axioms ATK.Cert.mem_expIRect
#print axioms ATK.Cert.norm_expI_sub_le
#print axioms ATK.Cert.mem_expIAuto
#print axioms ATK.Cert.mem_dLog
#print axioms ATK.Cert.mem_logI
#print axioms ATK.Cert.mem_sqrtI
#print axioms ATK.Cert.piLo_lt
#print axioms ATK.Cert.lt_piLo_add
#print axioms ATK.Cert.atS_cast
