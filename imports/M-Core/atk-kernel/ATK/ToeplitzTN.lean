import ATK.JensenTuran

/-!
# ATK — Positividade total de Toeplitz (Aissen–Schoenberg–Whitney–Edrei) para polinômios

Fecha, na forma polinomial, o critério correto do erro E8 (`TP∞(aₙ)`, não `TP∞(γₙ)`), usando a
definição `Matrix.IsTotallyNonneg` do Mathlib (todos os menores, linhas e colunas estritamente crescentes)
para a matriz de Toeplitz triangular infinita `T(a)_{ij} = a_{i−j}`.

* **ASW (⇐), qualquer grau**: se `p = c·∏(X + rᵢ)` com `c ≥ 0`, `rᵢ ≥ 0` — isto é, `p` tem só zeros reais
  `≤ 0` e coeficiente líder `≥ 0` — então `T(coef p)` é totalmente não negativa (`tn_de_raizes`), e em
  particular todo menor de Toeplitz `D_{r,m} ≥ 0` (`Dmin_nonneg_de_raizes`). A prova: multiplicar por
  `X + r` soma colunas vizinhas (`toep_mulLin`); por multilinearidade o menor vira soma de menores de `T(a)`
  com colunas não decrescentes (`det_expand`), cada um `≥ 0` ou nulo (`tn_mulLin`).
* **ASW (⇒) em grau 2**: para `a₀, a₂ > 0`, `T(a₀,a₁,a₂)` é totalmente não negativa **⟺ `a₁ ≥ 0` e
  `a₁² ≥ 4a₀a₂`** ⟺ `a₀ + a₁x + a₂x² = a₂(x + r₁)(x + r₂)` com `rᵢ ≥ 0` (`tn_grau_dois_iff`,
  `fatora_iff`). A recíproca usa os menores tridiagonais `D_r = a₁D_{r−1} − a₀a₂D_{r−2}` (`D_rec`) e
  mostra, sem trigonometria, que com `a₁² < 4a₀a₂` algum `D_r < 0` (`algum_D_neg`).
* Exemplo: `Θ = 1 + x + x²` (zeros não reais) tem `D₃ = −1` (`um_x_x2`).

O que **não** está aqui: a recíproca em grau `≥ 3` (ASW 1952 usa a identidade de Jacobi para a inversa e o
teorema de Pringsheim) e o teorema de Edrei para séries infinitas (teoria de Nevanlinna).
-/

open Matrix Polynomial Finset

namespace ATK.ToeplitzTN

/-! ## 1. A matriz de Toeplitz e o fator linear -/

/-- `T(a)_{ij} = a_{i−j}` (`0` se `i < j`). -/
def toep (a : ℕ → ℝ) : Matrix ℕ ℕ ℝ := fun i j => if j ≤ i then a (i - j) else 0

/-- Coeficientes de `a(X)·(X + r)`: `b_n = r a_n + a_{n−1}`. -/
def mulLin (a : ℕ → ℝ) (r : ℝ) (n : ℕ) : ℝ := r * a n + if n = 0 then 0 else a (n - 1)

theorem toep_mulLin (a : ℕ → ℝ) (r : ℝ) (i j : ℕ) :
    toep (mulLin a r) i j = r * toep a i j + toep a i (j + 1) := by
  unfold toep mulLin
  by_cases h1 : j + 1 ≤ i
  · have h2 : j ≤ i := by omega
    have h3 : i - j ≠ 0 := by omega
    rw [if_pos h2, if_pos h2, if_pos h1, if_neg h3, show i - j - 1 = i - (j + 1) by omega]
  · rw [if_neg h1]
    by_cases h2 : j ≤ i
    · have h3 : i - j = 0 := by omega
      simp [h2, h3]
    · simp [h2]

/-- **Expansão multilinear**: o menor de `(r·col_j + col_{j+1})` é a soma dos menores com colunas
`cols j + βⱼ`, `βⱼ ∈ {0, 1}`, pesados por `r^{#zeros}`. -/
theorem det_expand {n : ℕ} (A : Matrix ℕ ℕ ℝ) (rows cols : Fin n → ℕ) (r : ℝ) :
    (Matrix.of fun i j : Fin n => r * A (rows i) (cols j) + A (rows i) (cols j + 1)).det =
      ∑ β : Fin n → Fin 2, (∏ i, (![r, 1] : Fin 2 → ℝ) (β i)) *
        (A.submatrix rows fun j => cols j + (β j : ℕ)).det := by
  rw [det_apply']
  simp_rw [det_apply', Matrix.submatrix_apply, Matrix.of_apply]
  have h1 : ∀ σ : Equiv.Perm (Fin n),
      ∏ i, (r * A (rows (σ i)) (cols i) + A (rows (σ i)) (cols i + 1)) =
        ∑ β : Fin n → Fin 2, (∏ i, (![r, 1] : Fin 2 → ℝ) (β i)) *
          ∏ i, A (rows (σ i)) (cols i + (β i : ℕ)) := by
    intro σ
    have e : ∀ i, r * A (rows (σ i)) (cols i) + A (rows (σ i)) (cols i + 1) =
        ∑ b : Fin 2, (![r, 1] : Fin 2 → ℝ) b * A (rows (σ i)) (cols i + (b : ℕ)) := by
      intro i; simp [Fin.sum_univ_two]
    rw [Finset.prod_congr rfl fun i _ => e i, Fintype.prod_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.prod_mul_distrib]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun σ _ => ?_
  ring

theorem coef_nonneg {r : ℝ} (hr : 0 ≤ r) (b : Fin 2) : 0 ≤ (![r, 1] : Fin 2 → ℝ) b := by
  fin_cases b <;> simp [hr]

/-- **Multiplicar por `X + r` (`r ≥ 0`) preserva a positividade total.** -/
theorem tn_mulLin {a : ℕ → ℝ} (ha : (toep a).IsTotallyNonneg) {r : ℝ} (hr : 0 ≤ r) :
    (toep (mulLin a r)).IsTotallyNonneg := by
  intro n rows cols hrows hcols
  have hM : (toep (mulLin a r)).submatrix rows cols =
      Matrix.of fun i j => r * toep a (rows i) (cols j) + toep a (rows i) (cols j + 1) := by
    ext i j; simp [toep_mulLin]
  rw [hM, det_expand]
  refine Finset.sum_nonneg fun β _ => mul_nonneg (Finset.prod_nonneg fun i _ => coef_nonneg hr _) ?_
  have hmono : Monotone fun j => cols j + (β j : ℕ) := by
    intro i j hij
    rcases hij.lt_or_eq with h | h
    · have h1 := hcols h
      have h2 : (β i : ℕ) < 2 := (β i).isLt
      simp only
      omega
    · rw [h]
  by_cases hinj : Function.Injective fun j => cols j + (β j : ℕ)
  · exact ha hrows (hmono.strictMono_of_injective hinj)
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨i, j, hij, hne⟩ := hinj
    rw [Matrix.det_zero_of_column_eq hne fun k => by simp only [Matrix.submatrix_apply]; rw [hij]]

/-! ## 2. ASW (⇐): zeros reais `≤ 0` ⇒ `T(coef p)` totalmente não negativa -/

theorem coeff_mul_lin (p : ℝ[X]) (r : ℝ) : (p * (X + C r)).coeff = mulLin p.coeff r := by
  funext n
  unfold mulLin
  rw [mul_add, coeff_add, coeff_mul_C]
  rcases n with _ | n
  · simp
    ring
  · rw [coeff_mul_X]
    simp
    ring

theorem toep_C (c : ℝ) : toep (C c).coeff = c • (1 : Matrix ℕ ℕ ℝ) := by
  ext i j
  simp only [toep, coeff_C, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp
  · by_cases h2 : j ≤ i
    · rw [if_pos h2, if_neg (by omega), if_neg h]; simp
    · rw [if_neg h2, if_neg h]; simp

/-- **`c ≥ 0`, `rᵢ ≥ 0` ⇒ `T(coef(c·∏(X + rᵢ)))` é totalmente não negativa.** -/
theorem tn_prod (c : ℝ) (hc : 0 ≤ c) (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x) :
    (toep (C c * (s.map fun x => X + C x).prod).coeff).IsTotallyNonneg := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, mul_one]
    rw [toep_C]
    exact Matrix.IsTotallyNonneg.one.smul hc
  | cons x s ih =>
    have hx : 0 ≤ x := hs x (Multiset.mem_cons_self x s)
    have hs' : ∀ y ∈ s, 0 ≤ y := fun y hy => hs y (Multiset.mem_cons_of_mem hy)
    have e : C c * ((x ::ₘ s).map fun x => X + C x).prod =
        (C c * (s.map fun x => X + C x).prod) * (X + C x) := by
      rw [Multiset.map_cons, Multiset.prod_cons]; ring
    rw [e, coeff_mul_lin]
    exact tn_mulLin (ih hs') hx

/-- **ASW (⇐)**: se todas as raízes de `p` são reais (`#raízes = grau`) e `≤ 0`, e o coeficiente líder é
`≥ 0`, então a matriz de Toeplitz dos coeficientes é totalmente não negativa. -/
theorem tn_de_raizes {p : ℝ[X]} (hroots : Multiset.card p.roots = p.natDegree)
    (hneg : ∀ x ∈ p.roots, x ≤ 0) (hlc : 0 ≤ p.leadingCoeff) : (toep p.coeff).IsTotallyNonneg := by
  have h := C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  have e : (p.roots.map fun a => X - C a) = (p.roots.map Neg.neg).map fun x => X + C x := by
    rw [Multiset.map_map]
    congr 1
    funext a
    simp [sub_eq_add_neg]
  rw [← h, e]
  refine tn_prod _ hlc _ fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
  have := hneg a ha
  linarith

/-- Os menores de Toeplitz `D_{r,m} = det[a_{m+i−j}]` são menores de `T(a)`. -/
theorem Dmin_eq_submatrix (a : ℕ → ℝ) (r m : ℕ) :
    ATK.ClosedMath.Jensen.Dmin a r m =
      ((toep a).submatrix (fun i : Fin r => m + (i : ℕ)) fun j : Fin r => (j : ℕ)).det := by
  unfold ATK.ClosedMath.Jensen.Dmin
  congr 1
  ext i j
  simp only [Matrix.of_apply, Matrix.submatrix_apply, toep, ATK.ClosedMath.Jensen.ext]
  by_cases h : (j : ℕ) ≤ m + (i : ℕ)
  · have h0 : (0 : ℤ) ≤ (m : ℤ) + ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) := by omega
    have e : (m : ℤ) + ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) = ((m + (i : ℕ) - (j : ℕ) : ℕ) : ℤ) := by omega
    rw [if_pos h0, if_pos h, e, Int.toNat_natCast]
  · have h0 : ¬ (0 : ℤ) ≤ (m : ℤ) + ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) := by omega
    rw [if_neg h0, if_neg h]

theorem Dmin_nonneg_of_tn {a : ℕ → ℝ} (h : (toep a).IsTotallyNonneg) (r m : ℕ) :
    0 ≤ ATK.ClosedMath.Jensen.Dmin a r m := by
  rw [Dmin_eq_submatrix]
  refine h (fun i j hij => ?_) Fin.val_strictMono
  have : (i : ℕ) < j := hij
  show m + (i : ℕ) < m + (j : ℕ)
  omega

/-- **Critério correto de E8, direção (⇐)**: zeros reais `≤ 0` ⇒ todo `D_{r,m}(aₙ) ≥ 0`. -/
theorem Dmin_nonneg_de_raizes {p : ℝ[X]} (hroots : Multiset.card p.roots = p.natDegree)
    (hneg : ∀ x ∈ p.roots, x ≤ 0) (hlc : 0 ≤ p.leadingCoeff) (r m : ℕ) :
    0 ≤ ATK.ClosedMath.Jensen.Dmin p.coeff r m :=
  Dmin_nonneg_of_tn (tn_de_raizes hroots hneg hlc) r m

/-- **`(1 + X)³`**: `T(1,3,3,1)` é totalmente não negativa (todos os menores, não só os 2×2). -/
theorem tn_binomio_cubo : (toep ((X + C (1 : ℝ)) ^ 3).coeff).IsTotallyNonneg := by
  have e : (X + C (1 : ℝ)) ^ 3 = C 1 * (({1, 1, 1} : Multiset ℝ).map fun x => X + C x).prod := by
    simp; ring
  rw [e]
  exact tn_prod 1 zero_le_one _ (by simp)

/-! ## 3. ASW (⇒) em grau 2: os menores tridiagonais -/

/-- Entradas tridiagonais: `a₁` na diagonal, `a₂` abaixo, `a₀` acima. -/
def tri (a0 a1 a2 : ℝ) (i j : ℕ) : ℝ :=
  if i = j then a1 else if i = j + 1 then a2 else if j = i + 1 then a0 else 0

theorem tri_succ (a0 a1 a2 : ℝ) (i j : ℕ) : tri a0 a1 a2 (i + 1) (j + 1) = tri a0 a1 a2 i j := by
  unfold tri
  simp only [add_left_inj]

/-- `D_r = det[tri(i,j)]_{i,j<r}`. -/
noncomputable def Dtri (a0 a1 a2 : ℝ) (r : ℕ) : ℝ :=
  (Matrix.of fun i j : Fin r => tri a0 a1 a2 i j).det

theorem Dtri_zero (a0 a1 a2 : ℝ) : Dtri a0 a1 a2 0 = 1 := by
  unfold Dtri; exact Matrix.det_isEmpty

theorem Dtri_one (a0 a1 a2 : ℝ) : Dtri a0 a1 a2 1 = a1 := by
  unfold Dtri; rw [Matrix.det_unique]; simp [tri]

theorem Dtri_shift (a0 a1 a2 : ℝ) (r : ℕ) :
    (Matrix.of fun i j : Fin (r + 1) => tri a0 a1 a2 i j).submatrix Fin.succ Fin.succ =
      Matrix.of fun i j : Fin r => tri a0 a1 a2 i j := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Fin.val_succ, tri_succ]

/-- **Recorrência**: `D_{r+2} = a₁D_{r+1} − a₀a₂D_r`. -/
theorem D_rec (a0 a1 a2 : ℝ) (r : ℕ) :
    Dtri a0 a1 a2 (r + 2) = a1 * Dtri a0 a1 a2 (r + 1) - a0 * a2 * Dtri a0 a1 a2 r := by
  unfold Dtri
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hrest : ∑ j : Fin r, (-1 : ℝ) ^ ((j.succ.succ : Fin (r + 2)) : ℕ) *
      (Matrix.of fun i j : Fin (r + 2) => tri a0 a1 a2 i j) 0 j.succ.succ *
      ((Matrix.of fun i j : Fin (r + 2) => tri a0 a1 a2 i j).submatrix Fin.succ
        (j.succ.succ).succAbove).det = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    have : tri a0 a1 a2 ((0 : Fin (r + 2)) : ℕ) ((j.succ.succ : Fin (r + 2)) : ℕ) = 0 := by
      simp only [Fin.val_zero, Fin.val_succ, tri]
      split_ifs <;> first | rfl | (exfalso; omega)
    simp only [Matrix.of_apply, this, mul_zero, zero_mul]
  rw [hrest, add_zero]
  -- termo j = 0
  have h0 : (Matrix.of fun i j : Fin (r + 2) => tri a0 a1 a2 i j).submatrix Fin.succ
      (0 : Fin (r + 2)).succAbove = Matrix.of fun i j : Fin (r + 1) => tri a0 a1 a2 i j := by
    rw [Fin.succAbove_zero]; exact Dtri_shift a0 a1 a2 (r + 1)
  -- termo j = 1: expandir pela coluna 0
  set B := (Matrix.of fun i j : Fin (r + 2) => tri a0 a1 a2 i j).submatrix Fin.succ
      (Fin.succ (0 : Fin (r + 1))).succAbove with hB
  have hB0 : ∀ i : Fin (r + 1), B i 0 = if (i : ℕ) = 0 then a2 else 0 := by
    intro i
    rw [hB, Matrix.submatrix_apply, Matrix.of_apply, Fin.succ_zero_eq_one, Fin.one_succAbove_zero]
    simp only [Fin.val_succ, Fin.val_zero, tri]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hBs : B.submatrix (0 : Fin (r + 1)).succAbove Fin.succ =
      Matrix.of fun i j : Fin r => tri a0 a1 a2 i j := by
    ext i j
    rw [hB, Matrix.submatrix_apply, Matrix.submatrix_apply, Matrix.of_apply, Matrix.of_apply,
      Fin.succAbove_zero, Fin.succ_succAbove_succ, Fin.succAbove_zero]
    simp only [Fin.val_succ, tri_succ]
  have hdetB : B.det = a2 * (Matrix.of fun i j : Fin r => tri a0 a1 a2 i j).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have hz : ∑ i : Fin r, (-1 : ℝ) ^ ((i.succ : Fin (r + 1)) : ℕ) * B i.succ 0 *
        (B.submatrix (i.succ).succAbove Fin.succ).det = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hB0]; simp
    rw [hz, add_zero, hB0, hBs]
    simp
  have e01 : (Matrix.of fun i j : Fin (r + 2) => tri a0 a1 a2 i j) 0 (Fin.succ (0 : Fin (r + 1))) = a0 := by
    simp [tri]
  have e00 : (Matrix.of fun i j : Fin (r + 2) => tri a0 a1 a2 i j) 0 0 = a1 := by
    simp [tri]
  rw [h0, e00, e01, hdetB]
  simp
  ring

/-- `D_r` com `a₀ = a₁ = a₂ = 1` (`Θ = 1 + x + x²`): `D₃ = −1`. -/
theorem um_x_x2 : Dtri 1 1 1 3 = -1 := by
  rw [D_rec, D_rec, Dtri_one, Dtri_zero]; norm_num

/-! ### A recíproca: `a₁² < 4a₀a₂` força um `D_r < 0` -/

/-- Recorrência de Chebyshev `x_{r+2} = 2c·x_{r+1} − x_r`, `x₀ = 1`, `x₁ = 2c`, com `0 ≤ c < 1`:
algum `x_r < 0`. (Sem trigonometria: o invariante `x_{r+1}² − 2c x_{r+1}x_r + x_r² = 1` dá
`x_r + x_{r+1} ≥ 1` e `x_r ≤ 1/(1−c)` enquanto todos forem `≥ 0`; a soma telescópica
`2(1−c)Σ_{k≤N}x_k ≤ x₁ + x_N` contradiz `Σ_{k≤2N} x_k ≥ N`.) -/
theorem cheb_neg {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (x : ℕ → ℝ) (h0 : x 0 = 1) (h1 : x 1 = 2 * c)
    (hrec : ∀ r, x (r + 2) = 2 * c * x (r + 1) - x r) : ∃ r, x r < 0 := by
  by_contra hall
  push Not at hall
  -- invariante
  have hQ : ∀ r, x (r + 1) ^ 2 - 2 * c * x (r + 1) * x r + x r ^ 2 = 1 := by
    intro r
    induction r with
    | zero => rw [h0, h1]; ring
    | succ r ih => rw [hrec r]; linear_combination ih
  have hpar : ∀ r, 1 ≤ x r + x (r + 1) := by
    intro r
    have q := hQ r
    have a := hall r
    have b := hall (r + 1)
    nlinarith [mul_nonneg (mul_nonneg hc0 b) a]
  set M : ℝ := 1 / (1 - c) with hM
  have h1c : 0 < 1 - c := by linarith
  have hM1 : 1 ≤ M := by rw [hM, le_div_iff₀ h1c]; linarith
  have hbd : ∀ r, x r ≤ M := by
    intro r
    have q := hQ r
    have a := hall r
    have b := hall (r + 1)
    have hsq : (1 - c) * x r ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x (r + 1) - x r)]
    have hsq' : x r ^ 2 ≤ M := by rw [hM, le_div_iff₀ h1c]; linarith
    by_contra hcon
    push Not at hcon
    nlinarith
  -- soma telescópica
  have htel : ∀ N, 2 * (1 - c) * (∑ k ∈ Finset.range N, x (k + 1)) = x 1 - x 0 + x N - x (N + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have := hrec N
      linarith
  have hsum_le : ∀ N, (∑ k ∈ Finset.range N, x (k + 1)) ≤ M / (1 - c) := by
    intro N
    have := htel N
    have a := hall (N + 1)
    have b := hbd N
    have c1 : x 1 ≤ M := hbd 1
    rw [le_div_iff₀ h1c]
    nlinarith [h0]
  have hsum_ge : ∀ N : ℕ, (N : ℝ) ≤ ∑ k ∈ Finset.range (2 * N), x (k + 1) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ]
      have := hpar (2 * N + 1)
      push_cast
      linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (M / (1 - c))
  have := hsum_ge N
  have := hsum_le (2 * N)
  linarith

/-- **Com `a₀, a₂ > 0`, `a₁ ≥ 0` e `a₁² < 4a₀a₂`, algum menor tridiagonal é negativo.** -/
theorem algum_D_neg {a0 a1 a2 : ℝ} (h0 : 0 < a0) (h2 : 0 < a2) (h1 : 0 ≤ a1)
    (hd : a1 ^ 2 < 4 * a0 * a2) : ∃ r, Dtri a0 a1 a2 r < 0 := by
  set s := Real.sqrt (a0 * a2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (mul_pos h0 h2)
  have hs2 : s ^ 2 = a0 * a2 := Real.sq_sqrt (mul_pos h0 h2).le
  set c := a1 / (2 * s) with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c < 1 := by
    rw [hc, div_lt_one (by positivity)]
    nlinarith
  have hx0 : Dtri a0 a1 a2 0 / s ^ 0 = 1 := by rw [Dtri_zero]; simp
  have hx1 : Dtri a0 a1 a2 1 / s ^ 1 = 2 * c := by
    rw [Dtri_one, hc, pow_one]; field_simp
  have hxr : ∀ r : ℕ, Dtri a0 a1 a2 (r + 2) / s ^ (r + 2) =
      2 * c * (Dtri a0 a1 a2 (r + 1) / s ^ (r + 1)) - Dtri a0 a1 a2 r / s ^ r := by
    intro r
    rw [D_rec, show a0 * a2 = s ^ 2 from hs2.symm, hc]
    field_simp
    ring
  obtain ⟨r, hr⟩ := cheb_neg hc0 hc1 (fun r => Dtri a0 a1 a2 r / s ^ r) hx0 hx1 hxr
  refine ⟨r, ?_⟩
  by_contra hge
  push Not at hge
  have : 0 ≤ Dtri a0 a1 a2 r / s ^ r := div_nonneg hge (pow_pos hs0 r).le
  exact absurd hr (not_lt.mpr this)

/-! ### O enunciado em grau 2 -/

/-- `(a₀, a₁, a₂, 0, 0, …)`. -/
def seq3 (a0 a1 a2 : ℝ) (n : ℕ) : ℝ := if n = 0 then a0 else if n = 1 then a1 else if n = 2 then a2 else 0

theorem tri_eq_toep (a0 a1 a2 : ℝ) (i j : ℕ) : toep (seq3 a0 a1 a2) (i + 1) j = tri a0 a1 a2 i j := by
  unfold toep seq3 tri
  by_cases hj : j ≤ i + 1
  · rw [if_pos hj]
    split_ifs <;> first | rfl | omega
  · rw [if_neg hj]
    split_ifs <;> first | rfl | omega

theorem Dtri_nonneg_of_tn {a0 a1 a2 : ℝ} (h : (toep (seq3 a0 a1 a2)).IsTotallyNonneg) (r : ℕ) :
    0 ≤ Dtri a0 a1 a2 r := by
  have e : (Matrix.of fun i j : Fin r => tri a0 a1 a2 i j) =
      (toep (seq3 a0 a1 a2)).submatrix (fun i : Fin r => (i : ℕ) + 1) fun j : Fin r => (j : ℕ) := by
    ext i j; rw [Matrix.of_apply, Matrix.submatrix_apply, tri_eq_toep]
  unfold Dtri
  rw [e]
  refine h (fun i j hij => ?_) Fin.val_strictMono
  have : (i : ℕ) < j := hij
  show (i : ℕ) + 1 < (j : ℕ) + 1
  omega

/-- **Fatoração**: `a₁ ≥ 0 ∧ a₁² ≥ 4a₀a₂ ⟺ a₀ + a₁x + a₂x² = a₂(x + r₁)(x + r₂)` com `r₁, r₂ ≥ 0`
(para `a₀ ≥ 0`, `a₂ > 0`): só zeros reais `≤ 0`. -/
theorem fatora_iff {a0 a1 a2 : ℝ} (h0 : 0 ≤ a0) (h2 : 0 < a2) :
    (0 ≤ a1 ∧ 4 * a0 * a2 ≤ a1 ^ 2) ↔
      ∃ r1 r2 : ℝ, 0 ≤ r1 ∧ 0 ≤ r2 ∧ a1 = a2 * (r1 + r2) ∧ a0 = a2 * (r1 * r2) := by
  constructor
  · rintro ⟨h1, hd⟩
    set q := Real.sqrt (a1 ^ 2 - 4 * a0 * a2) with hq
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hq2 : q ^ 2 = a1 ^ 2 - 4 * a0 * a2 := Real.sq_sqrt (by linarith)
    have hqa : q ≤ a1 := by
      rw [hq]; apply Real.sqrt_le_iff.mpr; constructor
      · exact h1
      · nlinarith [mul_nonneg h0 h2.le]
    refine ⟨(a1 - q) / (2 * a2), (a1 + q) / (2 * a2), by apply div_nonneg <;> linarith,
      by apply div_nonneg <;> linarith, ?_, ?_⟩
    · field_simp; ring
    · field_simp; nlinarith [hq2]
  · rintro ⟨r1, r2, hr1, hr2, e1, e0⟩
    refine ⟨by rw [e1]; positivity, ?_⟩
    rw [e1, e0]
    nlinarith [sq_nonneg (r1 - r2), h2.le, mul_pos h2 h2]

theorem seq3_eq_coeff {a2 r1 r2 : ℝ} :
    seq3 (a2 * (r1 * r2)) (a2 * (r1 + r2)) a2 = (C a2 * (({r1, r2} : Multiset ℝ).map
      fun x => X + C x).prod).coeff := by
  have e : C a2 * (({r1, r2} : Multiset ℝ).map fun x => X + C x).prod =
      C a2 * X ^ 2 + C (a2 * (r1 + r2)) * X + C (a2 * (r1 * r2)) := by
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.prod_cons, Multiset.prod_singleton, C_mul, C_add]
    ring
  rw [e]
  funext n
  unfold seq3
  rcases n with _ | _ | _ | n
  · simp
  · simp
  · simp
  · simp

/-- **ASW em grau 2**: para `a₀, a₂ > 0`, `T(a₀, a₁, a₂)` é totalmente não negativa
**⟺ `a₁ ≥ 0` e `a₁² ≥ 4a₀a₂`** (⟺ zeros reais `≤ 0`, `fatora_iff`). -/
theorem tn_grau_dois_iff {a0 a1 a2 : ℝ} (h0 : 0 < a0) (h2 : 0 < a2) :
    (toep (seq3 a0 a1 a2)).IsTotallyNonneg ↔ (0 ≤ a1 ∧ 4 * a0 * a2 ≤ a1 ^ 2) := by
  constructor
  · intro h
    have h1 : 0 ≤ a1 := by
      have := h.nonneg 1 0
      simpa [toep, seq3] using this
    refine ⟨h1, ?_⟩
    by_contra hd
    push Not at hd
    obtain ⟨r, hr⟩ := algum_D_neg h0 h2 h1 hd
    linarith [Dtri_nonneg_of_tn h r]
  · intro hc
    obtain ⟨r1, r2, hr1, hr2, e1, e0⟩ := (fatora_iff h0.le h2).mp hc
    rw [e1, e0, seq3_eq_coeff]
    refine tn_prod a2 h2.le _ fun x hx => ?_
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption

/-- **`Θ = 1 + x + x²` não é `TP∞`** (zeros não reais): `D₃ = −1 < 0`. -/
theorem um_x_x2_nao_tn : ¬ (toep (seq3 1 1 1)).IsTotallyNonneg := by
  intro h
  have := Dtri_nonneg_of_tn h 3
  rw [um_x_x2] at this
  norm_num at this

end ATK.ToeplitzTN

-- Auditoria de axiomas (kernel)
#print axioms ATK.ToeplitzTN.toep_mulLin
#print axioms ATK.ToeplitzTN.det_expand
#print axioms ATK.ToeplitzTN.coef_nonneg
#print axioms ATK.ToeplitzTN.tn_mulLin
#print axioms ATK.ToeplitzTN.coeff_mul_lin
#print axioms ATK.ToeplitzTN.toep_C
#print axioms ATK.ToeplitzTN.tn_prod
#print axioms ATK.ToeplitzTN.tn_de_raizes
#print axioms ATK.ToeplitzTN.Dmin_eq_submatrix
#print axioms ATK.ToeplitzTN.Dmin_nonneg_of_tn
#print axioms ATK.ToeplitzTN.Dmin_nonneg_de_raizes
#print axioms ATK.ToeplitzTN.tn_binomio_cubo
#print axioms ATK.ToeplitzTN.tri_succ
#print axioms ATK.ToeplitzTN.Dtri_zero
#print axioms ATK.ToeplitzTN.Dtri_one
#print axioms ATK.ToeplitzTN.Dtri_shift
#print axioms ATK.ToeplitzTN.D_rec
#print axioms ATK.ToeplitzTN.um_x_x2
#print axioms ATK.ToeplitzTN.cheb_neg
#print axioms ATK.ToeplitzTN.algum_D_neg
#print axioms ATK.ToeplitzTN.tri_eq_toep
#print axioms ATK.ToeplitzTN.Dtri_nonneg_of_tn
#print axioms ATK.ToeplitzTN.fatora_iff
#print axioms ATK.ToeplitzTN.seq3_eq_coeff
#print axioms ATK.ToeplitzTN.tn_grau_dois_iff
#print axioms ATK.ToeplitzTN.um_x_x2_nao_tn
