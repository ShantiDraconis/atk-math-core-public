import ATK.ASWReciproca

/-!
# ATK — Edrei para funções inteiras (sem Nevanlinna)

**Teorema (`edrei_inteira`)**: se `a : ℕ → ℝ` são os coeficientes de uma função inteira `F(z) = Σ aₙzⁿ`
(`Inteira a`: `Σ|aₙ|Rⁿ < ∞` para todo `R`), `a₀ > 0` e a matriz de Toeplitz `T(a)` é totalmente não
negativa, então **todo zero complexo de `F` é real e negativo**.

É a direção difícil do teorema de Aissen–Schoenberg–Whitney–Edrei para funções inteiras. A prova de Edrei
(1953) usa teoria de Nevanlinna; aqui ela é substituída por um argumento de descida nos coeficientes de
`B = 1/F(−x)`, que estende `ATK/ASWReciproca.lean`:

1. `cc_de_tn_ser`: TN de `T(a)` ⇒ menores de colunas iniciais de `T(b)` `≥ 0` (Jacobi nas seções finitas).
2. `ev_mul_inv`: onde `Σ b_k x^k` converge absolutamente, `F(−x)·B(x) = 1` (produto de Cauchy).
3. Se `F(w) = 0`: `b_k > 0` (`b_pos_ser`), a razão `b_{k+1}/b_k ↓ L` com `L·|w| ≥ 1` (`raio_ser`), e
   `F(−1/L) = 0` por convergência dominada (`raiz_ser`, teorema de Tannery).
4. `F = (1 + Lz)·G` com `G` inteira (`divLin`, `inteira_divLin`, `ev_divLin`) e `1/G(−x) = (1 − Lx)B`
   de novo com menores de colunas iniciais `≥ 0` (`cc_remove`).
5. Descida (`descida`): se `w` não é real negativo, cada passo tira um zero real de módulo `≤ |w|` e baixa
   `b₁` de pelo menos `1/(a₀|w|)`; como `b₁ ≥ 0`, absurdo.

A recíproca (`tn_de_limite`): limites coeficiente a coeficiente de polinômios com zeros reais `≤ 0` dão
`T(a)` TN — em particular produtos de gênero 0 (`tn_genero0`).
-/

open Matrix Finset Filter Topology

namespace ATK.Edrei

open ATK.ToeplitzTN (toep)
open ATK.ASWRec

/-! ## 1. Funções inteiras como sequências de coeficientes -/

/-- `a` são os coeficientes de uma função inteira: `Σ|aₙ|Rⁿ < ∞` para todo `R ≥ 0`. -/
def Inteira (a : ℕ → ℝ) : Prop := ∀ R : ℝ, 0 ≤ R → Summable fun n => |a n| * R ^ n

/-- `F(z) = Σ aₙ zⁿ`. -/
noncomputable def ev (a : ℕ → ℝ) (z : ℂ) : ℂ := ∑' n, (a n : ℂ) * z ^ n

theorem summable_norm_ev {a : ℕ → ℝ} (ha : Inteira a) (z : ℂ) :
    Summable fun n => ‖(a n : ℂ) * z ^ n‖ := by
  refine (ha ‖z‖ (norm_nonneg z)).congr fun n => ?_
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]

theorem ev_zero (a : ℕ → ℝ) : ev a 0 = a 0 := by
  unfold ev
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

/-! ## 2. Transferência para séries -/

/-- `F(−x)` como série formal. -/
noncomputable def qser (a : ℕ → ℝ) : PowerSeries ℝ := PowerSeries.mk fun n => (-1 : ℝ) ^ n * a n

/-- **Transferência (Jacobi), séries**: `T(a)` TN e `a₀ > 0` ⇒ menores de colunas iniciais de
`T(coef 1/F(−x))` `≥ 0`. -/
theorem cc_de_tn_ser {a : ℕ → ℝ} (hP : (toep a).IsTotallyNonneg) (h0 : 0 < a 0)
    {B : PowerSeries ℝ} (hB : qser a * B = 1) : CCTN (fun k => PowerSeries.coeff k B) := by
  classical
  intro r R hR
  set m : ℕ := (Finset.univ.sup fun s => R s) + 1 with hm
  have hRlt : ∀ s, R s < r + m := by
    intro s
    have := Finset.le_sup (f := fun s => R s) (Finset.mem_univ s)
    omega
  set R' : Fin r → Fin (r + m) := fun s => ⟨R s, hRlt s⟩ with hR'def
  have hR' : StrictMono R' := fun a b hab => by
    show R a < R b
    exact hR hab
  set T : Finset (Fin (r + m)) := (Finset.univ.image R')ᶜ with hT
  have hTc : T.card = m := by
    rw [hT, Finset.card_compl, Finset.card_image_of_injective _ hR'.injective, Finset.card_univ,
      Fintype.card_fin, Fintype.card_fin]
    omega
  set Rc := T.orderEmbOfFin hTc with hRcdef
  have hRc : StrictMono Rc := Rc.strictMono
  have hc : ∀ x, x ∈ Set.range Rc ↔ x ∉ Set.range R' := by
    intro x
    rw [hRcdef, Finset.range_orderEmbOfFin]
    simp [hT]
  set G := sec (r + m) (fun k => PowerSeries.coeff k (qser a)) with hG
  set Xm := sec (r + m) (fun k => PowerSeries.coeff k B) with hX
  have hGX : G * Xm = 1 := by rw [hG, hX, sec_mul, hB, sec_one]
  have hJ := jacobi_init r m G Xm hGX R' Rc hR' hRc hc
  have hA : (Matrix.of fun i j : Fin (r + m) => (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) * G i j) =
      sec (r + m) a := by
    ext i j
    simp only [Matrix.of_apply, hG, sec, toep, qser, PowerSeries.coeff_mk]
    split_ifs with h
    · rw [← mul_assoc, ← pow_add, show (i : ℕ) + (j : ℕ) + ((i : ℕ) - (j : ℕ)) = 2 * (i : ℕ) by omega,
        pow_mul]
      norm_num
    · ring
  rw [hA] at hJ
  have hdetA : 0 < (sec (r + m) a).det := by
    rw [Matrix.det_of_isLowerTriangular _ ?_]
    · apply Finset.prod_pos
      intro i _
      simp [sec, toep, h0]
    · intro i j hij
      have hij' : (i : ℕ) < (j : ℕ) := hij
      simp only [sec, toep]
      rw [if_neg (by omega)]
  have hminor : 0 ≤ ((sec (r + m) a).submatrix (Fin.natAdd r) Rc).det := by
    have e : (sec (r + m) a).submatrix (Fin.natAdd r) Rc =
        (toep a).submatrix (fun t : Fin m => r + (t : ℕ)) (fun u => (Rc u : ℕ)) := by
      ext t u
      simp [sec]
    rw [e]
    refine hP (fun a b hab => ?_) (fun a b hab => hRc hab)
    have : (a : ℕ) < b := hab
    show r + (a : ℕ) < r + (b : ℕ)
    omega
  have hsub : Xm.submatrix R' (Fin.castAdd m) =
      (toep fun k => PowerSeries.coeff k B).submatrix R (fun c : Fin r => (c : ℕ)) := by
    ext s c
    simp [hX, sec, hR'def]
  rw [hsub] at hJ
  by_contra hneg
  push_neg at hneg
  have := mul_neg_of_neg_of_pos hneg hdetA
  linarith

/-- A recorrência `F(−x)·B = 1` nos coeficientes. -/
def RecS (a b : ℕ → ℝ) : Prop :=
  ∀ N, ∑ i ∈ Finset.range (N + 1), (-1) ^ i * a i * b (N - i) = if N = 0 then 1 else 0

theorem recS_of_inv {a : ℕ → ℝ} {B : PowerSeries ℝ} (hB : qser a * B = 1) :
    RecS a (fun k => PowerSeries.coeff k B) := by
  intro N
  have h := congrArg (PowerSeries.coeff N) hB
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i c => PowerSeries.coeff i (qser a) * PowerSeries.coeff c B)] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [qser, PowerSeries.coeff_mk]

theorem b0_eq {a b : ℕ → ℝ} (hrec : RecS a b) (h0 : 0 < a 0) : b 0 = (a 0)⁻¹ := by
  have h := hrec 0
  rw [Finset.sum_range_one, if_pos rfl] at h
  norm_num at h
  field_simp
  linarith

/-- **`F(−x)·B(x) = 1`** onde `Σ b_k x^k` converge absolutamente. -/
theorem ev_mul_inv {a b : ℕ → ℝ} (ha : Inteira a) (hrec : RecS a b) {x : ℂ}
    (hb : Summable fun k => ‖(b k : ℂ) * x ^ k‖) :
    ev a (-x) * ∑' k, (b k : ℂ) * x ^ k = 1 := by
  unfold ev
  have h1 : Summable fun n => ‖(a n : ℂ) * (-x) ^ n‖ := summable_norm_ev ha (-x)
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm h1 hb]
  have e : ∀ n, ∑ k ∈ Finset.range (n + 1), (a k : ℂ) * (-x) ^ k * ((b (n - k) : ℂ) * x ^ (n - k)) =
      ((if n = 0 then 1 else 0 : ℝ) : ℂ) * x ^ n := by
    intro n
    rw [← hrec n]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [neg_pow, ← pow_sub_mul_pow x hk']
    ring
  simp_rw [e]
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-! ## 3. Positividade, razão, raio e uma raiz real -/

theorem b_pos_ser {a b : ℕ → ℝ} (ha : Inteira a) (hrec : RecS a b) (h0 : 0 < a 0) (hcc : CCTN b)
    {w : ℂ} (hw : ev a w = 0) (k : ℕ) : 0 < b k := by
  classical
  have hb0 : 0 < b 0 := by rw [b0_eq hrec h0]; exact inv_pos.mpr h0
  by_contra hk
  have hz : ∃ k, b k = 0 := ⟨k, le_antisymm (not_lt.mp hk) (cc_nonneg hcc k)⟩
  have hk0z : b (Nat.find hz) = 0 := Nat.find_spec hz
  have hk0pos : 1 ≤ Nat.find hz := by
    by_contra h
    have : Nat.find hz = 0 := by omega
    rw [this] at hk0z
    linarith
  have hprev : 0 < b (Nat.find hz - 1) := by
    have h1 : b (Nat.find hz - 1) ≠ 0 := Nat.find_min hz (by omega)
    exact lt_of_le_of_ne (cc_nonneg hcc _) (Ne.symm h1)
  have hzero : ∀ j, Nat.find hz ≤ j → b j = 0 := by
    intro j hj
    rcases Nat.eq_or_lt_of_le hj with h | h
    · rw [← h]; exact hk0z
    · exact cc_zero_prop hcc hk0pos hk0z hprev h
  have hsum : Summable fun k => ‖(b k : ℂ) * (-w) ^ k‖ := by
    refine summable_of_ne_finset_zero (s := Finset.range (Nat.find hz)) fun j hj => ?_
    rw [hzero j (by simpa using hj)]
    simp
  have := ev_mul_inv ha hrec hsum
  rw [neg_neg, hw, zero_mul] at this
  exact zero_ne_one this

theorem ratio_antitone {b : ℕ → ℝ} (hcc : CCTN b) (hpos : ∀ k, 0 < b k) :
    Antitone (fun k => b (k + 1) / b k) := by
  refine antitone_nat_of_succ_le fun k => ?_
  show b (k + 2) / b (k + 1) ≤ b (k + 1) / b k
  rw [div_le_div_iff₀ (hpos _) (hpos _)]
  have := cc_log_concave hcc k
  nlinarith [this]

theorem ev_ne_zero_at_zero {a : ℕ → ℝ} (h0 : 0 < a 0) {w : ℂ} (hw : ev a w = 0) : w ≠ 0 := by
  rintro rfl
  rw [ev_zero] at hw
  exact (ne_of_gt h0) (by exact_mod_cast hw)

/-- **Raio**: se `F(w) = 0`, a razão limite satisfaz `L·|w| ≥ 1`. -/
theorem raio_ser {a b : ℕ → ℝ} (ha : Inteira a) (hrec : RecS a b) (h0 : 0 < a 0)
    (hpos : ∀ k, 0 < b k) {L : ℝ} (hlim : Tendsto (fun k => b (k + 1) / b k) atTop (𝓝 L))
    {w : ℂ} (hw : ev a w = 0) : 1 ≤ L * ‖w‖ := by
  have hw0 : w ≠ 0 := ev_ne_zero_at_zero h0 hw
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  by_contra h
  push_neg at h
  have hsum : Summable fun k => ‖(b k : ℂ) * (-w) ^ k‖ := by
    refine summable_of_ratio_test_tendsto_lt_one h (Eventually.of_forall fun n => ?_) ?_
    · rw [norm_ne_zero_iff]
      exact mul_ne_zero (by exact_mod_cast (hpos n).ne') (pow_ne_zero _ (neg_ne_zero.mpr hw0))
    · refine (hlim.mul_const ‖w‖).congr fun n => ?_
      simp only [norm_mul, norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hpos _), abs_norm]
      field_simp
      ring
  have := ev_mul_inv ha hrec hsum
  rw [neg_neg, hw, zero_mul] at this
  exact zero_ne_one this

theorem pow_mul_le {b : ℕ → ℝ} (hpos : ∀ k, 0 < b k) {L : ℝ} (hL : 0 ≤ L)
    (hge : ∀ k, L ≤ b (k + 1) / b k) (m j : ℕ) : L ^ j * b m ≤ b (m + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : L * b (m + j) ≤ b (m + j + 1) := by
      have := hge (m + j)
      rwa [le_div_iff₀ (hpos _)] at this
    calc L ^ (j + 1) * b m = L * (L ^ j * b m) := by ring
      _ ≤ L * b (m + j) := mul_le_mul_of_nonneg_left ih hL
      _ ≤ b (m + j + 1) := h1
      _ = b (m + (j + 1)) := by rw [Nat.add_assoc]

/-- **Uma raiz real** (Tannery): `Σ (−1)^i aᵢ L^{−i} = 0`, i.e. `F(−1/L) = 0`. -/
theorem raiz_ser {a b : ℕ → ℝ} (ha : Inteira a) (hrec : RecS a b) (hpos : ∀ k, 0 < b k)
    {L : ℝ} (hL : 0 < L) (hlim : Tendsto (fun k => b (k + 1) / b k) atTop (𝓝 L))
    (hge : ∀ k, L ≤ b (k + 1) / b k) :
    ∑' i, (-1) ^ i * a i * L⁻¹ ^ i = 0 := by
  classical
  set f : ℕ → ℕ → ℝ := fun M i => if i ≤ M then (-1) ^ i * a i * (b (M - i) / b M) else 0 with hf
  have hsum0 : ∀ M, 1 ≤ M → ∑' i, f M i = 0 := by
    intro M hM
    rw [tsum_eq_sum (s := Finset.range (M + 1)) fun i hi => by
      simp only [hf]
      rw [if_neg (by simp at hi; omega)]]
    have h := hrec M
    rw [if_neg (by omega)] at h
    have e : ∑ i ∈ Finset.range (M + 1), f M i =
        (∑ i ∈ Finset.range (M + 1), (-1) ^ i * a i * b (M - i)) / b M := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [hf]
      rw [if_pos (by simp at hi; omega)]
      ring
    rw [e, h, zero_div]
  have hlimi : ∀ i, Tendsto (fun M => f M i) atTop (𝓝 ((-1) ^ i * a i * L⁻¹ ^ i)) := by
    intro i
    have h1 : Tendsto (fun M => b (M + i) / b M) atTop (𝓝 (L ^ i)) := ratio_pow hpos hlim i
    have h2 : Tendsto (fun M => (b (M + i) / b M)⁻¹) atTop (𝓝 ((L ^ i)⁻¹)) :=
      h1.inv₀ (pow_ne_zero _ hL.ne')
    have h3 : Tendsto (fun M => (b (M - i + i) / b (M - i))⁻¹) atTop (𝓝 ((L ^ i)⁻¹)) :=
      h2.comp (tendsto_sub_atTop_nat i)
    have h4 : Tendsto (fun M => (-1) ^ i * a i * (b (M - i + i) / b (M - i))⁻¹) atTop
        (𝓝 ((-1) ^ i * a i * (L ^ i)⁻¹)) := h3.const_mul _
    rw [inv_pow]
    refine h4.congr' ?_
    filter_upwards [eventually_ge_atTop i] with M hM
    simp only [hf, if_pos hM, Nat.sub_add_cancel hM, inv_div]
  have hbound : ∀ M i, ‖f M i‖ ≤ |a i| * L⁻¹ ^ i := by
    intro M i
    simp only [hf]
    split_ifs with h
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos (div_pos (hpos _) (hpos _))]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have := pow_mul_le hpos hL.le hge (M - i) i
      rw [Nat.sub_add_cancel h] at this
      rw [div_le_iff₀ (hpos _)]
      calc b (M - i) = L⁻¹ ^ i * (L ^ i * b (M - i)) := by
            rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hL.ne', one_pow, one_mul]
        _ ≤ L⁻¹ ^ i * b M := mul_le_mul_of_nonneg_left this (pow_nonneg (inv_nonneg.mpr hL.le) _)
    · rw [norm_zero]
      positivity
  have hT := tendsto_tsum_of_dominated_convergence (ha L⁻¹ (inv_nonneg.mpr hL.le)) hlimi
    (Eventually.of_forall hbound)
  have hT0 : Tendsto (fun M => ∑' i, f M i) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop 1] with M hM
      exact (hsum0 M hM).symm)
  exact tendsto_nhds_unique hT hT0

/-! ## 4. Remoção do fator `1 + Lz` -/

/-- `G = F/(1 + Lz)`: `c'_0 = c_0`, `c'_{n+1} = c_{n+1} − L·c'_n`. -/
def divLin (c : ℕ → ℝ) (L : ℝ) : ℕ → ℝ
  | 0 => c 0
  | n + 1 => c (n + 1) - L * divLin c L n

theorem divLin_partial (c : ℕ → ℝ) {L : ℝ} (hL : L ≠ 0) (n : ℕ) :
    divLin c L n * (-L⁻¹) ^ n = ∑ j ∈ Finset.range (n + 1), c j * (-L⁻¹) ^ j := by
  induction n with
  | zero => simp [divLin]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h1 : -L * (-L⁻¹) = 1 := by field_simp
    calc divLin c L (n + 1) * (-L⁻¹) ^ (n + 1)
        = c (n + 1) * (-L⁻¹) ^ (n + 1) + divLin c L n * (-L⁻¹) ^ n * (-L * (-L⁻¹)) := by
          simp only [divLin]
          ring
      _ = _ := by rw [h1, mul_one]; ring

/-- `G = F/(1 + Lz)` é inteira quando `F(−1/L) = 0` (cauda de uma série inteira). -/
theorem inteira_divLin {c : ℕ → ℝ} (hc : Inteira c) {L : ℝ} (hL : 0 < L)
    (hroot : ∑' j, c j * (-L⁻¹) ^ j = 0) : Inteira (divLin c L) := by
  intro R hR
  set y : ℝ := -L⁻¹ with hy
  have hay : |y| = L⁻¹ := by rw [hy, abs_neg, abs_of_pos (inv_pos.mpr hL)]
  have hsy : Summable fun j => c j * y ^ j := by
    refine Summable.of_norm ((hc L⁻¹ (inv_nonneg.mpr hL.le)).congr fun j => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, hay]
  set T : ℝ := 2 * R + L⁻¹ with hT
  have hTpos : 0 < T := by positivity
  have hLT : 1 ≤ L * T := by
    rw [hT, mul_add, mul_inv_cancel₀ hL.ne']
    nlinarith
  have hLT0 : 0 < L * T := by positivity
  set K : ℝ := ∑' j, |c j| * T ^ j with hK
  have hsT := hc T hTpos.le
  clear_value y T K
  have hbound : ∀ n, |divLin c L n| * R ^ n ≤ K / (L * T) * (R / T) ^ n := by
    intro n
    have h1 : divLin c L n * y ^ n = -∑' j, c (j + (n + 1)) * y ^ (j + (n + 1)) := by
      rw [hy, divLin_partial c hL.ne' n, ← hy]
      have := hsy.sum_add_tsum_nat_add (n + 1)
      rw [hroot] at this
      linarith
    have hs' : Summable fun j => |c (j + (n + 1))| * T ^ (j + (n + 1)) :=
      (summable_nat_add_iff (f := fun m => |c m| * T ^ m) (n + 1)).mpr hsT
    have hq0 : 0 ≤ (L * T)⁻¹ := inv_nonneg.mpr hLT0.le
    have hq1 : (L * T)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hLT
    have hterm : ∀ j, ‖c (j + (n + 1)) * y ^ (j + (n + 1))‖ ≤
        (L * T)⁻¹ ^ (n + 1) * (|c (j + (n + 1))| * T ^ (j + (n + 1))) := by
      intro j
      rw [Real.norm_eq_abs, abs_mul, abs_pow, hay]
      have e : L⁻¹ ^ (j + (n + 1)) = (L * T)⁻¹ ^ (j + (n + 1)) * T ^ (j + (n + 1)) := by
        rw [← mul_pow]
        congr 1
        field_simp
      rw [e]
      have hle : (L * T)⁻¹ ^ (j + (n + 1)) ≤ (L * T)⁻¹ ^ (n + 1) :=
        pow_le_pow_of_le_one hq0 hq1 (by omega)
      have := abs_nonneg (c (j + (n + 1)))
      have := pow_nonneg hTpos.le (j + (n + 1))
      calc |c (j + (n + 1))| * ((L * T)⁻¹ ^ (j + (n + 1)) * T ^ (j + (n + 1)))
          = (L * T)⁻¹ ^ (j + (n + 1)) * (|c (j + (n + 1))| * T ^ (j + (n + 1))) := by ring
        _ ≤ (L * T)⁻¹ ^ (n + 1) * (|c (j + (n + 1))| * T ^ (j + (n + 1))) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
    have hnorm : Summable fun j => ‖c (j + (n + 1)) * y ^ (j + (n + 1))‖ :=
      Summable.of_nonneg_of_le (fun j => norm_nonneg _) hterm (hs'.mul_left _)
    have htail : ∑' j, |c (j + (n + 1))| * T ^ (j + (n + 1)) ≤ K := by
      have := hsT.sum_add_tsum_nat_add (n + 1)
      have hnn : 0 ≤ ∑ i ∈ Finset.range (n + 1), |c i| * T ^ i :=
        Finset.sum_nonneg fun i _ => by positivity
      rw [hK]
      linarith
    have h2 : |∑' j, c (j + (n + 1)) * y ^ (j + (n + 1))| ≤ (L * T)⁻¹ ^ (n + 1) * K := by
      calc |∑' j, c (j + (n + 1)) * y ^ (j + (n + 1))|
          = ‖∑' j, c (j + (n + 1)) * y ^ (j + (n + 1))‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' j, ‖c (j + (n + 1)) * y ^ (j + (n + 1))‖ := norm_tsum_le_tsum_norm hnorm
        _ ≤ ∑' j, (L * T)⁻¹ ^ (n + 1) * (|c (j + (n + 1))| * T ^ (j + (n + 1))) :=
          Summable.tsum_le_tsum hterm hnorm (hs'.mul_left _)
        _ = (L * T)⁻¹ ^ (n + 1) * ∑' j, |c (j + (n + 1))| * T ^ (j + (n + 1)) := tsum_mul_left
        _ ≤ (L * T)⁻¹ ^ (n + 1) * K := mul_le_mul_of_nonneg_left htail (pow_nonneg hq0 _)
    have h3 : |divLin c L n| * L⁻¹ ^ n ≤ (L * T)⁻¹ ^ (n + 1) * K := by
      have := congrArg abs h1
      rw [abs_mul, abs_pow, hay, abs_neg] at this
      rw [this]
      exact h2
    have hLn : 0 < L ^ n := pow_pos hL n
    have h4 : |divLin c L n| ≤ (L * T)⁻¹ ^ (n + 1) * K * L ^ n := by
      have e : |divLin c L n| = |divLin c L n| * L⁻¹ ^ n * L ^ n := by
        rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ hL.ne', one_pow, mul_one]
      rw [e]
      exact mul_le_mul_of_nonneg_right h3 hLn.le
    calc |divLin c L n| * R ^ n ≤ (L * T)⁻¹ ^ (n + 1) * K * L ^ n * R ^ n :=
          mul_le_mul_of_nonneg_right h4 (pow_nonneg hR _)
      _ = K / (L * T) * (R / T) ^ n := by
          have hLi : L⁻¹ ^ n * L ^ n = 1 := by rw [← mul_pow, inv_mul_cancel₀ hL.ne', one_pow]
          linear_combination (K * L⁻¹ * T⁻¹ ^ (n + 1) * R ^ n) * hLi
  have hgeo : Summable fun n => K / (L * T) * (R / T) ^ n := by
    refine (summable_geometric_of_lt_one (div_nonneg hR hTpos.le) ?_).mul_left _
    rw [div_lt_one hTpos, hT]
    have := inv_pos.mpr hL
    linarith
  exact Summable.of_nonneg_of_le (fun n => by positivity) hbound hgeo

theorem ev_divLin {c : ℕ → ℝ} (hc : Inteira c) {L : ℝ} (hd : Inteira (divLin c L)) (z : ℂ) :
    ev c z = (1 + (L : ℂ) * z) * ev (divLin c L) z := by
  set d := divLin c L with hdd
  have hcd : ∀ n, c (n + 1) = d (n + 1) + L * d n := by
    intro n
    simp only [hdd, divLin]
    ring
  have hsd : Summable fun n => (d n : ℂ) * z ^ n := (summable_norm_ev hd z).of_norm
  have hsc : Summable fun n => (c n : ℂ) * z ^ n := (summable_norm_ev hc z).of_norm
  have hS : ∑' n, (d n : ℂ) * z ^ n = (d 0 : ℂ) * z ^ 0 + ∑' n, (d (n + 1) : ℂ) * z ^ (n + 1) :=
    hsd.tsum_eq_zero_add
  have e : ∀ n, (c (n + 1) : ℂ) * z ^ (n + 1) =
      (d (n + 1) : ℂ) * z ^ (n + 1) + (L : ℂ) * z * ((d n : ℂ) * z ^ n) := by
    intro n
    rw [hcd n]
    push_cast
    ring
  unfold ev
  calc ∑' n, (c n : ℂ) * z ^ n = (c 0 : ℂ) * z ^ 0 + ∑' n, (c (n + 1) : ℂ) * z ^ (n + 1) :=
        hsc.tsum_eq_zero_add
    _ = (d 0 : ℂ) * z ^ 0 + (∑' n, (d (n + 1) : ℂ) * z ^ (n + 1) +
          (L : ℂ) * z * ∑' n, (d n : ℂ) * z ^ n) := by
        simp_rw [e]
        rw [Summable.tsum_add ((summable_nat_add_iff (f := fun n => (d n : ℂ) * z ^ n) 1).mpr hsd)
          (hsd.mul_left _), tsum_mul_left]
        rfl
    _ = (1 + (L : ℂ) * z) * ∑' n, (d n : ℂ) * z ^ n := by
        rw [hS]
        ring

theorem coeff_bL (B : PowerSeries ℝ) (L : ℝ) (k : ℕ) :
    PowerSeries.coeff k ((1 - PowerSeries.C L * PowerSeries.X) * B) =
      bL (fun k => PowerSeries.coeff k B) L k := by
  rw [sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul]
  cases k with
  | zero => simp [bL, PowerSeries.coeff_zero_X_mul]
  | succ k =>
    rw [PowerSeries.coeff_succ_X_mul]
    simp [bL]

theorem qser_divLin (c : ℕ → ℝ) (L : ℝ) :
    qser c = (1 - PowerSeries.C L * PowerSeries.X) * qser (divLin c L) := by
  ext n
  rw [sub_mul, one_mul, mul_assoc, map_sub, PowerSeries.coeff_C_mul]
  cases n with
  | zero => simp [qser, divLin, PowerSeries.coeff_zero_X_mul]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul]
    simp only [qser, PowerSeries.coeff_mk, divLin]
    ring

/-! ## 5. A descida e o teorema -/

/-- Estado da descida: `G` inteira com `G(0) = a₀`, `G(w) = 0`, `G(−x)·B = 1`, `B` com menores de
colunas iniciais `≥ 0`. -/
def Estado (a0 : ℝ) (w : ℂ) (c : ℕ → ℝ) (B : PowerSeries ℝ) : Prop :=
  Inteira c ∧ c 0 = a0 ∧ ev c w = 0 ∧ qser c * B = 1 ∧ CCTN (fun k => PowerSeries.coeff k B)

/-- **Um passo**: tira um zero real `−1/L` (com `L|w| ≥ 1`) e baixa `b₁` de pelo menos `1/(a₀|w|)`. -/
theorem passo {a0 : ℝ} (ha0 : 0 < a0) {w : ℂ} (hw : ¬ (w.im = 0 ∧ w.re < 0)) {c : ℕ → ℝ}
    {B : PowerSeries ℝ} (h : Estado a0 w c B) :
    ∃ c' B', Estado a0 w c' B' ∧ PowerSeries.coeff 1 B' + (a0 * ‖w‖)⁻¹ ≤ PowerSeries.coeff 1 B := by
  obtain ⟨hc, hc0, hcw, hB, hcc⟩ := h
  have h0 : 0 < c 0 := hc0 ▸ ha0
  have hrec := recS_of_inv hB
  have hpos := b_pos_ser hc hrec h0 hcc hcw
  have hanti := ratio_antitone hcc hpos
  obtain ⟨L, hL0, hlim⟩ := ratio_tendsto hcc hpos
  have hge : ∀ k, L ≤ PowerSeries.coeff (k + 1) B / PowerSeries.coeff k B :=
    fun k => hanti.le_of_tendsto hlim k
  have hrad := raio_ser hc hrec h0 hpos hlim hcw
  have hw0 := ev_ne_zero_at_zero h0 hcw
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hL : 0 < L := by
    rcases hL0.lt_or_eq with h | h
    · exact h
    · rw [← h, zero_mul] at hrad
      linarith
  have hroot0 := raiz_ser hc hrec hpos hL hlim hge
  have hroot : ∑' j, c j * (-L⁻¹) ^ j = 0 := by
    rw [← hroot0]
    congr 1
    ext j
    rw [neg_pow]
    ring
  have hd := inteira_divLin hc hL hroot
  refine ⟨divLin c L, (1 - PowerSeries.C L * PowerSeries.X) * B, ⟨hd, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [divLin, hc0]
  · have he := ev_divLin hc hd w
    rw [hcw] at he
    have hne : (1 + (L : ℂ) * w) ≠ 0 := by
      intro h1
      apply hw
      have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      have hw' : w = ((-L⁻¹ : ℝ) : ℂ) := by
        push_cast
        field_simp
        linear_combination h1
      rw [hw']
      simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
      exact neg_neg_of_pos (inv_pos.mpr hL)
    exact (mul_eq_zero.mp he.symm).resolve_left hne
  · rw [qser_divLin c L] at hB
    calc qser (divLin c L) * ((1 - PowerSeries.C L * PowerSeries.X) * B)
        = ((1 - PowerSeries.C L * PowerSeries.X) * qser (divLin c L)) * B := by ring
      _ = 1 := hB
  · have e : (fun k => PowerSeries.coeff k ((1 - PowerSeries.C L * PowerSeries.X) * B)) =
        bL (fun k => PowerSeries.coeff k B) L := funext (coeff_bL B L)
    rw [e]
    exact cc_remove hcc hpos hlim
  · rw [coeff_bL]
    simp only [bL, one_ne_zero, if_false, Nat.sub_self]
    have hb0 : PowerSeries.coeff 0 B = a0⁻¹ := by rw [b0_eq hrec h0, hc0]
    rw [hb0]
    have h1 : 1 / ‖w‖ ≤ L := (div_le_iff₀ hnw).mpr hrad
    have h2 : (a0 * ‖w‖)⁻¹ = a0⁻¹ * (1 / ‖w‖) := by rw [mul_inv, one_div]
    rw [h2]
    have := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr ha0.le)
    linarith

theorem descida {a0 : ℝ} (ha0 : 0 < a0) {w : ℂ} (hw : ¬ (w.im = 0 ∧ w.re < 0)) {c : ℕ → ℝ}
    {B : PowerSeries ℝ} (h : Estado a0 w c B) (k : ℕ) :
    ∃ c' B', Estado a0 w c' B' ∧
      PowerSeries.coeff 1 B' + k * (a0 * ‖w‖)⁻¹ ≤ PowerSeries.coeff 1 B := by
  induction k with
  | zero => exact ⟨c, B, h, by simp⟩
  | succ k ih =>
    obtain ⟨c', B', h', hle⟩ := ih
    obtain ⟨c'', B'', h'', hle'⟩ := passo ha0 hw h'
    refine ⟨c'', B'', h'', ?_⟩
    push_cast
    linarith

/-- **Edrei para funções inteiras (sem Nevanlinna)**: `F = Σ aₙzⁿ` inteira, `a₀ > 0` e `T(a)` TN ⇒
todo zero de `F` é real e negativo. -/
theorem edrei_inteira {a : ℕ → ℝ} (ha : Inteira a) (h0 : 0 < a 0) (hTN : (toep a).IsTotallyNonneg)
    {w : ℂ} (hw : ev a w = 0) : w.im = 0 ∧ w.re < 0 := by
  by_contra hneg
  set B : PowerSeries ℝ := (qser a)⁻¹ with hBdef
  have hB : qser a * B = 1 := PowerSeries.mul_inv_cancel _ (by simp [qser, h0.ne'])
  have hst : Estado (a 0) w a B := ⟨ha, rfl, hw, hB, cc_de_tn_ser hTN h0 hB⟩
  have hw0 := ev_ne_zero_at_zero h0 hw
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hq : 0 < (a 0 * ‖w‖)⁻¹ := by positivity
  obtain ⟨k, hk⟩ := exists_nat_gt (PowerSeries.coeff 1 B / (a 0 * ‖w‖)⁻¹)
  obtain ⟨c', B', h', hle⟩ := descida h0 hneg hst k
  have hnn : 0 ≤ PowerSeries.coeff 1 B' := cc_nonneg h'.2.2.2.2 1
  have h1 := (div_lt_iff₀ hq).mp hk
  linarith

/-! ## 6. A recíproca: limites de polinômios com zeros reais `≤ 0` -/

/-- TN é fechada por limites entrada a entrada. -/
theorem tn_closed {A : ℕ → Matrix ℕ ℕ ℝ} {A' : Matrix ℕ ℕ ℝ} (h : ∀ N, (A N).IsTotallyNonneg)
    (hl : ∀ i j, Tendsto (fun N => A N i j) atTop (𝓝 (A' i j))) : A'.IsTotallyNonneg := by
  intro n rows cols hr hc
  have hconv : Tendsto (fun N => (A N).submatrix rows cols) atTop (𝓝 (A'.submatrix rows cols)) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hl (rows i) (cols j)
  have := ((continuous_id.matrix_det).tendsto _).comp hconv
  exact ge_of_tendsto' this fun N => h N hr hc

/-- **(⇐)**: se `a` é limite coeficiente a coeficiente de polinômios com zeros reais `≤ 0` e líder `≥ 0`,
`T(a)` é TN. -/
theorem tn_de_limite {a : ℕ → ℝ} {P : ℕ → Polynomial ℝ}
    (hP : ∀ N, Multiset.card (P N).roots = (P N).natDegree ∧ (∀ x ∈ (P N).roots, x ≤ 0) ∧
      0 ≤ (P N).leadingCoeff)
    (hlim : ∀ n, Tendsto (fun N => (P N).coeff n) atTop (𝓝 (a n))) : (toep a).IsTotallyNonneg := by
  refine tn_closed (A := fun N => toep (P N).coeff)
    (fun N => ATK.ToeplitzTN.tn_de_raizes (hP N).1 (hP N).2.1 (hP N).2.2) fun i j => ?_
  simp only [toep]
  split_ifs
  · exact hlim _
  · exact tendsto_const_nhds

/-! ## 7. Produtos de gênero 0: `a₀∏(1 + αⱼz)`, `αⱼ ≥ 0`, `Σαⱼ < ∞` -/

/-- Coeficientes de `a₀∏_{j<N}(1 + αⱼz)`. -/
def prodCoef (a0 : ℝ) (α : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => fun n => if n = 0 then a0 else 0
  | N + 1 => fun n => prodCoef a0 α N n + α N * (if n = 0 then 0 else prodCoef a0 α N (n - 1))

theorem tn_smul_seq {a : ℕ → ℝ} (h : (toep a).IsTotallyNonneg) {s : ℝ} (hs : 0 ≤ s) :
    (toep fun n => s * a n).IsTotallyNonneg := by
  intro k rows cols hr hc
  have e : (toep fun n => s * a n).submatrix rows cols = s • (toep a).submatrix rows cols := by
    ext i j
    simp only [toep, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [e, Matrix.det_smul]
  exact mul_nonneg (pow_nonneg hs _) (h hr hc)

/-- Multiplicar por `1 + αz` (`α ≥ 0`) preserva TN. -/
theorem tn_mul_one_add {a : ℕ → ℝ} (h : (toep a).IsTotallyNonneg) {α : ℝ} (hα : 0 ≤ α) :
    (toep fun n => a n + α * (if n = 0 then 0 else a (n - 1))).IsTotallyNonneg := by
  rcases hα.lt_or_eq with hp | h0
  · have e : (fun n => a n + α * (if n = 0 then 0 else a (n - 1))) =
        fun n => α * ATK.ToeplitzTN.mulLin a α⁻¹ n := by
      funext n
      simp only [ATK.ToeplitzTN.mulLin]
      rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    rw [e]
    exact tn_smul_seq (ATK.ToeplitzTN.tn_mulLin h (inv_nonneg.mpr hp.le)) hp.le
  · subst h0
    simpa using h

theorem tn_prodCoef {a0 : ℝ} (ha0 : 0 ≤ a0) {α : ℕ → ℝ} (hα : ∀ j, 0 ≤ α j) (N : ℕ) :
    (toep (prodCoef a0 α N)).IsTotallyNonneg := by
  induction N with
  | zero =>
    have e : prodCoef a0 α 0 = (Polynomial.C a0).coeff := by
      funext n
      simp [prodCoef, Polynomial.coeff_C]
    rw [e, ATK.ToeplitzTN.toep_C]
    exact Matrix.IsTotallyNonneg.one.smul ha0
  | succ N ih => exact tn_mul_one_add ih (hα N)

theorem prodCoef_nonneg {a0 : ℝ} (ha0 : 0 ≤ a0) {α : ℕ → ℝ} (hα : ∀ j, 0 ≤ α j) (N n : ℕ) :
    0 ≤ prodCoef a0 α N n := by
  induction N generalizing n with
  | zero =>
    simp only [prodCoef]
    split_ifs <;> linarith
  | succ N ih =>
    simp only [prodCoef]
    have := ih n
    have := hα N
    split_ifs
    · linarith
    · have := ih (n - 1)
      nlinarith

theorem prodCoef_mono {a0 : ℝ} (ha0 : 0 ≤ a0) {α : ℕ → ℝ} (hα : ∀ j, 0 ≤ α j) (n : ℕ) :
    Monotone fun N => prodCoef a0 α N n := by
  refine monotone_nat_of_le_succ fun N => ?_
  show prodCoef a0 α N n ≤ prodCoef a0 α N n + α N * (if n = 0 then 0 else prodCoef a0 α N (n - 1))
  have := hα N
  have := prodCoef_nonneg ha0 hα N (n - 1)
  split_ifs
  · linarith
  · nlinarith

theorem prodCoef_le {a0 : ℝ} (ha0 : 0 ≤ a0) {α : ℕ → ℝ} (hα : ∀ j, 0 ≤ α j) (N n : ℕ) :
    prodCoef a0 α N n ≤ a0 * (∑ j ∈ Finset.range N, α j) ^ n := by
  induction N generalizing n with
  | zero =>
    simp only [prodCoef, Finset.range_zero, Finset.sum_empty]
    split_ifs with h
    · subst h; simp
    · rw [zero_pow h, mul_zero]
  | succ N ih =>
    simp only [prodCoef]
    set s := ∑ j ∈ Finset.range N, α j with hs
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => hα j
    rw [Finset.sum_range_succ, ← hs]
    have hαN := hα N
    split_ifs with h
    · subst h
      have := ih 0
      simp only [pow_zero, mul_one] at this ⊢
      linarith
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have h1 := ih (m + 1)
      have h2 := ih m
      simp only [Nat.add_sub_cancel] at h2 ⊢
      have h3 : s ^ m ≤ (s + α N) ^ m := pow_le_pow_left₀ hs0 (by linarith) m
      calc prodCoef a0 α N (m + 1) + α N * prodCoef a0 α N m
          ≤ a0 * s ^ (m + 1) + α N * (a0 * s ^ m) := by nlinarith
        _ = a0 * s ^ m * (s + α N) := by ring
        _ ≤ a0 * (s + α N) ^ m * (s + α N) := by
            apply mul_le_mul_of_nonneg_right _ (by linarith)
            exact mul_le_mul_of_nonneg_left h3 ha0
        _ = a0 * (s + α N) ^ (m + 1) := by ring

/-- Os coeficientes do produto infinito `a₀∏(1 + αⱼz)`: limite monótono das somas parciais. -/
noncomputable def coefGenero0 (a0 : ℝ) (α : ℕ → ℝ) (n : ℕ) : ℝ := ⨆ N, prodCoef a0 α N n

theorem tendsto_prodCoef {a0 : ℝ} (ha0 : 0 ≤ a0) {α : ℕ → ℝ} (hα : ∀ j, 0 ≤ α j) (hs : Summable α)
    (n : ℕ) : Tendsto (fun N => prodCoef a0 α N n) atTop (𝓝 (coefGenero0 a0 α n)) := by
  refine tendsto_atTop_ciSup (prodCoef_mono ha0 hα n) ⟨a0 * (∑' j, α j) ^ n, ?_⟩
  rintro _ ⟨N, rfl⟩
  refine (prodCoef_le ha0 hα N n).trans (mul_le_mul_of_nonneg_left ?_ ha0)
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => hα j)
    (hs.sum_le_tsum _ fun j _ => hα j) n

/-- **Edrei (⇐) para produtos de gênero 0**: `αⱼ ≥ 0`, `Σαⱼ < ∞`, `a₀ ≥ 0` ⇒ `T(coef a₀∏(1 + αⱼz))` é TN. -/
theorem tn_genero0 {a0 : ℝ} (ha0 : 0 ≤ a0) {α : ℕ → ℝ} (hα : ∀ j, 0 ≤ α j) (hs : Summable α) :
    (toep (coefGenero0 a0 α)).IsTotallyNonneg := by
  refine tn_closed (A := fun N => toep (prodCoef a0 α N)) (tn_prodCoef ha0 hα) fun i j => ?_
  simp only [toep]
  split_ifs
  · exact tendsto_prodCoef ha0 hα hs _
  · exact tendsto_const_nhds

end ATK.Edrei

#print axioms ATK.Edrei.summable_norm_ev
#print axioms ATK.Edrei.ev_zero
#print axioms ATK.Edrei.cc_de_tn_ser
#print axioms ATK.Edrei.recS_of_inv
#print axioms ATK.Edrei.b0_eq
#print axioms ATK.Edrei.ev_mul_inv
#print axioms ATK.Edrei.b_pos_ser
#print axioms ATK.Edrei.ratio_antitone
#print axioms ATK.Edrei.ev_ne_zero_at_zero
#print axioms ATK.Edrei.raio_ser
#print axioms ATK.Edrei.pow_mul_le
#print axioms ATK.Edrei.raiz_ser
#print axioms ATK.Edrei.divLin_partial
#print axioms ATK.Edrei.inteira_divLin
#print axioms ATK.Edrei.ev_divLin
#print axioms ATK.Edrei.coeff_bL
#print axioms ATK.Edrei.qser_divLin
#print axioms ATK.Edrei.passo
#print axioms ATK.Edrei.descida
#print axioms ATK.Edrei.edrei_inteira
#print axioms ATK.Edrei.tn_closed
#print axioms ATK.Edrei.tn_de_limite
#print axioms ATK.Edrei.tn_smul_seq
#print axioms ATK.Edrei.tn_mul_one_add
#print axioms ATK.Edrei.tn_prodCoef
#print axioms ATK.Edrei.prodCoef_nonneg
#print axioms ATK.Edrei.prodCoef_mono
#print axioms ATK.Edrei.prodCoef_le
#print axioms ATK.Edrei.tendsto_prodCoef
#print axioms ATK.Edrei.tn_genero0
