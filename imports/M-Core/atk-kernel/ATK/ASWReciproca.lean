import ATK.ToeplitzTN

/-!
# ATK — A recíproca de Aissen–Schoenberg–Whitney para polinômios

**Teorema (ASW 1952, polinômios)**: para `p ∈ ℝ[X]` com `p(0) > 0`, a matriz de Toeplitz `T(coef p)` é
totalmente não negativa **⟺** `p` só tem zeros reais `≤ 0` e coeficiente líder `≥ 0` (`asw_iff`).
A direção (⇐) está em `ATK/ToeplitzTN.lean`; aqui está a (⇒), com o que falta no Mathlib:

1. **Colunas unitárias** (`det_unit_cols`): uma matriz com colunas `e_{ρ_s}` nas posições `π_s` tem
   determinante `(−1)^{Σ(π_s + ρ_s)}` vezes o menor complementar (Laplace iterado).
2. **Identidade de Jacobi** para menores complementares da inversa, na forma sem sinal com `D = diag((−1)^i)`
   (`jacobi_init`): se `G·X = 1` e `A = DGD`, então `det X[R, 0..r−1] · det A = det A[r.., Rᶜ]`.
3. **Seções de Toeplitz** (`sec_mul`): `T_N(u)·T_N(v) = T_N(u·v)`; com `B = 1/p(−x)` isto liga os
   coeficientes `b` à inversa e dá `T(coef p)` TN ⇒ todos os menores de `T(b)` com colunas iniciais `≥ 0`
   (`cc_de_tn`).
4. **Uma raiz real** (sem Pringsheim): `b_k > 0` (`b_pos`: sem zeros internos e `B` não é polinômio),
   `b_{k+1}/b_k` decrescente (log-concavidade, `cc_log_concave`) com limite `L` (`ratio_tendsto`), e a
   recorrência `p(−x)B = 1` passa ao limite: `L > 0` e `p(−1/L) = 0` (`raiz_real`).
5. **Remoção do fator** (`cc_remove`): os menores de `(1 − Lx)B` com colunas iniciais são limites de menores
   `(r+1)×(r+1)` de `B` (operações de coluna `opCol`, escala da última linha, continuidade do determinante).
6. **Indução no grau** (`asw_rec`): `p = (x + 1/L)·q`, `q(−x)·(1/L − x)B = 1`; daí `asw_reciproca`,
   `asw_iff` e `asw_fatora` (`p = c·∏(x − xᵢ)`, `xᵢ ≤ 0`).

O que **não** está aqui: o teorema de Edrei (séries infinitas, teoria de Nevanlinna) e a fatoração de
Hadamard de `Θ`.
-/

open Matrix Polynomial Finset Filter Topology

namespace ATK.ASWRec

open ATK.ToeplitzTN (toep)

/-! ## 1. Colunas unitárias -/

/-- O único `z` com `p.succAbove z = x` (para `x ≠ p`). -/
noncomputable def preAbove {n : ℕ} (p x : Fin (n + 1)) (h : x ≠ p) : Fin n :=
  Classical.choose (Fin.exists_succAbove_eq h)

theorem succAbove_preAbove {n : ℕ} (p x : Fin (n + 1)) (h : x ≠ p) :
    p.succAbove (preAbove p x h) = x :=
  Classical.choose_spec (Fin.exists_succAbove_eq h)

theorem val_succAbove_of_lt {n : ℕ} (p : Fin (n + 1)) (z : Fin n) (h : p < p.succAbove z) :
    ((p.succAbove z : Fin (n + 1)) : ℕ) = (z : ℕ) + 1 := by
  by_cases hz : z.castSucc < p
  · rw [Fin.succAbove_of_castSucc_lt p z hz] at h
    exact absurd h (not_lt.mpr hz.le)
  · rw [Fin.succAbove_of_le_castSucc p z (not_lt.mp hz)]
    simp

theorem neg_one_pow_even_sum {a b : ℕ} (h : Even (a + b)) : ((-1 : ℝ)) ^ a = (-1) ^ b := by
  have h2 : ((-1 : ℝ)) ^ (a + b) = 1 := h.neg_one_pow
  have h3 : ((-1 : ℝ)) ^ b * (-1) ^ b = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  calc ((-1 : ℝ)) ^ a = (-1) ^ a * ((-1) ^ b * (-1) ^ b) := by rw [h3, mul_one]
    _ = (-1) ^ (a + b) * (-1) ^ b := by rw [pow_add]; ring
    _ = (-1) ^ b := by rw [h2, one_mul]

/-- **Lema das colunas unitárias**: se a coluna `π_s` de `M` é o vetor unitário `e_{ρ_s}` (`s < r`), então
`det M = (−1)^{Σ_s(π_s + ρ_s)} · det M[ρᶜ, πᶜ]`. -/
theorem det_unit_cols (r : ℕ) : ∀ (m n : ℕ), r + m = n → ∀ (M : Matrix (Fin n) (Fin n) ℝ)
    (π ρ : Fin r → Fin n) (πc ρc : Fin m → Fin n),
    StrictMono π → StrictMono ρ → StrictMono πc → StrictMono ρc →
    (∀ x, x ∈ Set.range πc ↔ x ∉ Set.range π) → (∀ x, x ∈ Set.range ρc ↔ x ∉ Set.range ρ) →
    (∀ s i, M i (π s) = if i = ρ s then 1 else 0) →
    M.det = (-1) ^ (∑ s, ((π s : ℕ) + (ρ s : ℕ))) * (M.submatrix ρc πc).det := by
  induction r with
  | zero =>
    intro m n hn M π ρ πc ρc _ _ hπc hρc cπ cρ _
    obtain rfl : m = n := by omega
    have e1 : πc = id := by
      rw [← StrictMono.range_inj_of_wellFoundedLT hπc strictMono_id]
      ext x
      simp only [Set.range_id, Set.mem_univ, iff_true]
      exact (cπ x).mpr (by rintro ⟨s, -⟩; exact s.elim0)
    have e2 : ρc = id := by
      rw [← StrictMono.range_inj_of_wellFoundedLT hρc strictMono_id]
      ext x
      simp only [Set.range_id, Set.mem_univ, iff_true]
      exact (cρ x).mpr (by rintro ⟨s, -⟩; exact s.elim0)
    rw [e1, e2, Matrix.submatrix_id_id]
    simp
  | succ r ih =>
    intro m n hn M π ρ πc ρc hπ hρ hπc hρc cπ cρ hM
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hdet : M.det = (-1) ^ ((ρ 0 : ℕ) + (π 0 : ℕ)) *
        (M.submatrix (ρ 0).succAbove (π 0).succAbove).det := by
      rw [Matrix.det_succ_column M (π 0), Finset.sum_eq_single (ρ 0)]
      · rw [hM 0 (ρ 0), if_pos rfl, mul_one]
      · intro i _ hi
        rw [hM 0 i, if_neg hi]
        simp
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hπne : ∀ s : Fin r, π s.succ ≠ π 0 := fun s h => (Fin.succ_ne_zero s) (hπ.injective h)
    have hρne : ∀ s : Fin r, ρ s.succ ≠ ρ 0 := fun s h => (Fin.succ_ne_zero s) (hρ.injective h)
    have hπc0 : ∀ t, πc t ≠ π 0 := fun t h => ((cπ (πc t)).mp ⟨t, rfl⟩) ⟨0, h.symm⟩
    have hρc0 : ∀ t, ρc t ≠ ρ 0 := fun t h => ((cρ (ρc t)).mp ⟨t, rfl⟩) ⟨0, h.symm⟩
    set π' : Fin r → Fin n' := fun s => preAbove (π 0) (π s.succ) (hπne s) with hπ'
    set ρ' : Fin r → Fin n' := fun s => preAbove (ρ 0) (ρ s.succ) (hρne s) with hρ'
    set πc' : Fin m → Fin n' := fun t => preAbove (π 0) (πc t) (hπc0 t) with hπc'
    set ρc' : Fin m → Fin n' := fun t => preAbove (ρ 0) (ρc t) (hρc0 t) with hρc'
    have sπ : ∀ s, (π 0).succAbove (π' s) = π s.succ := fun s => succAbove_preAbove _ _ _
    have sρ : ∀ s, (ρ 0).succAbove (ρ' s) = ρ s.succ := fun s => succAbove_preAbove _ _ _
    have sπc : ∀ t, (π 0).succAbove (πc' t) = πc t := fun t => succAbove_preAbove _ _ _
    have sρc : ∀ t, (ρ 0).succAbove (ρc' t) = ρc t := fun t => succAbove_preAbove _ _ _
    have mono : ∀ {k : ℕ} (p : Fin (n' + 1)) (f : Fin k → Fin n') (g : Fin k → Fin (n' + 1)),
        (∀ s, p.succAbove (f s) = g s) → StrictMono g → StrictMono f := by
      intro k p f g hfg hg a b hab
      have := hg hab
      rw [← hfg a, ← hfg b] at this
      exact (Fin.strictMono_succAbove p).lt_iff_lt.mp this
    have hπ'm : StrictMono π' :=
      mono (π 0) π' (fun s => π s.succ) sπ fun a b hab => hπ (Fin.succ_lt_succ_iff.mpr hab)
    have hρ'm : StrictMono ρ' :=
      mono (ρ 0) ρ' (fun s => ρ s.succ) sρ fun a b hab => hρ (Fin.succ_lt_succ_iff.mpr hab)
    have hπc'm : StrictMono πc' := mono (π 0) πc' πc sπc hπc
    have hρc'm : StrictMono ρc' := mono (ρ 0) ρc' ρc sρc hρc
    have cπ' : ∀ x, x ∈ Set.range πc' ↔ x ∉ Set.range π' := by
      intro x
      constructor
      · rintro ⟨t, rfl⟩ ⟨s, hs⟩
        have h1 := congrArg (π 0).succAbove hs
        rw [sπ, sπc] at h1
        exact ((cπ (πc t)).mp ⟨t, rfl⟩) ⟨s.succ, h1⟩
      · intro hx
        have hy : (π 0).succAbove x ∉ Set.range π := by
          rintro ⟨s, hs⟩
          cases s using Fin.cases with
          | zero => exact Fin.succAbove_ne (π 0) x hs.symm
          | succ s =>
            exact hx ⟨s, Fin.succAbove_right_injective (by rw [sπ]; exact hs)⟩
        obtain ⟨t, ht⟩ := (cπ _).mpr hy
        exact ⟨t, Fin.succAbove_right_injective (by rw [sπc]; exact ht)⟩
    have cρ' : ∀ x, x ∈ Set.range ρc' ↔ x ∉ Set.range ρ' := by
      intro x
      constructor
      · rintro ⟨t, rfl⟩ ⟨s, hs⟩
        have h1 := congrArg (ρ 0).succAbove hs
        rw [sρ, sρc] at h1
        exact ((cρ (ρc t)).mp ⟨t, rfl⟩) ⟨s.succ, h1⟩
      · intro hx
        have hy : (ρ 0).succAbove x ∉ Set.range ρ := by
          rintro ⟨s, hs⟩
          cases s using Fin.cases with
          | zero => exact Fin.succAbove_ne (ρ 0) x hs.symm
          | succ s =>
            exact hx ⟨s, Fin.succAbove_right_injective (by rw [sρ]; exact hs)⟩
        obtain ⟨t, ht⟩ := (cρ _).mpr hy
        exact ⟨t, Fin.succAbove_right_injective (by rw [sρc]; exact ht)⟩
    set M' := M.submatrix (ρ 0).succAbove (π 0).succAbove with hM'def
    have hM' : ∀ s i, M' i (π' s) = if i = ρ' s then 1 else 0 := by
      intro s i
      simp only [hM'def, Matrix.submatrix_apply, sπ]
      rw [hM s.succ]
      have : ((ρ 0).succAbove i = ρ s.succ) ↔ (i = ρ' s) := by
        rw [← sρ s]; exact Fin.succAbove_right_injective.eq_iff
      simp only [this]
    have hih := ih m n' (by omega) M' π' ρ' πc' ρc' hπ'm hρ'm hπc'm hρc'm cπ' cρ' hM'
    have hsub : M'.submatrix ρc' πc' = M.submatrix ρc πc := by
      ext t u
      simp only [hM'def, Matrix.submatrix_apply, sρc, sπc]
    rw [hsub] at hih
    have hvπ : ∀ s : Fin r, ((π s.succ : Fin (n' + 1)) : ℕ) = (π' s : ℕ) + 1 := by
      intro s
      rw [← sπ s]
      exact val_succAbove_of_lt _ _ (by rw [sπ s]; exact hπ (Fin.succ_pos s))
    have hvρ : ∀ s : Fin r, ((ρ s.succ : Fin (n' + 1)) : ℕ) = (ρ' s : ℕ) + 1 := by
      intro s
      rw [← sρ s]
      exact val_succAbove_of_lt _ _ (by rw [sρ s]; exact hρ (Fin.succ_pos s))
    have hsum : ∑ s : Fin (r + 1), ((π s : ℕ) + (ρ s : ℕ)) =
        ((π 0 : ℕ) + (ρ 0 : ℕ)) + ((∑ s : Fin r, ((π' s : ℕ) + (ρ' s : ℕ))) + 2 * r) := by
      rw [Fin.sum_univ_succ]
      congr 1
      simp only [hvπ, hvρ]
      rw [Finset.sum_congr rfl (fun s _ => show (π' s : ℕ) + 1 + ((ρ' s : ℕ) + 1) =
        ((π' s : ℕ) + (ρ' s : ℕ)) + 2 by ring), Finset.sum_add_distrib]
      simp [mul_comm]
    rw [hdet, hih, hsum]
    have h2 : ((-1 : ℝ)) ^ (2 * r) = 1 := by rw [pow_mul]; norm_num
    rw [pow_add ((-1 : ℝ)) ((π 0 : ℕ) + (ρ 0 : ℕ)),
      pow_add ((-1 : ℝ)) (∑ s : Fin r, ((π' s : ℕ) + (ρ' s : ℕ))) (2 * r), h2,
      add_comm ((π 0 : ℕ)) (ρ 0 : ℕ)]
    ring

/-! ## 2. A identidade de Jacobi (forma sem sinal) -/

theorem range_castAdd_iff {r m : ℕ} (x : Fin (r + m)) :
    x ∈ Set.range (Fin.natAdd r : Fin m → Fin (r + m)) ↔ x ∉ Set.range (Fin.castAdd m : Fin r → Fin (r + m)) := by
  constructor
  · rintro ⟨t, rfl⟩ ⟨s, hs⟩
    have := congrArg Fin.val hs
    simp at this
    omega
  · intro hx
    have hr : r ≤ (x : ℕ) := by
      by_contra h
      exact hx ⟨⟨x, by omega⟩, Fin.ext (by simp)⟩
    exact ⟨⟨(x : ℕ) - r, by omega⟩, Fin.ext (by simp; omega)⟩

theorem sum_partition {n r m : ℕ} (R : Fin r → Fin n) (Rc : Fin m → Fin n) (hR : Function.Injective R)
    (hRc : Function.Injective Rc) (hc : ∀ x, x ∈ Set.range Rc ↔ x ∉ Set.range R) (f : Fin n → ℕ) :
    ∑ x, f x = ∑ s, f (R s) + ∑ t, f (Rc t) := by
  classical
  have hu : (Finset.univ : Finset (Fin n)) = Finset.univ.image R ∪ Finset.univ.image Rc := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, true_and, true_iff]
    by_cases h : x ∈ Set.range R
    · exact Or.inl h
    · exact Or.inr ((hc x).mpr h)
  have hd : Disjoint (Finset.univ.image R) (Finset.univ.image Rc) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx1 hx2
    exact ((hc x).mp hx2) hx1
  rw [hu, Finset.sum_union hd, Finset.sum_image fun a _ b _ h => hR h,
    Finset.sum_image fun a _ b _ h => hRc h]

theorem det_conj_sign {k : ℕ} (d1 d2 : Fin k → ℝ) (Mx : Matrix (Fin k) (Fin k) ℝ) :
    (Matrix.of fun i j => d1 i * d2 j * Mx i j).det = (∏ i, d1 i) * (∏ j, d2 j) * Mx.det := by
  have e : (Matrix.of fun i j => d1 i * d2 j * Mx i j) =
      Matrix.diagonal d1 * Mx * Matrix.diagonal d2 := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  ring

/-- **Jacobi (colunas iniciais, sem sinal)**: se `G·X = 1` e `A = DGD` (`D = diag((−1)^i)`), então
`det X[R, {0..r−1}] · det A = det A[{r..}, Rᶜ]`. -/
theorem jacobi_init (r m : ℕ) (G X : Matrix (Fin (r + m)) (Fin (r + m)) ℝ) (hGX : G * X = 1)
    (R : Fin r → Fin (r + m)) (Rc : Fin m → Fin (r + m)) (hR : StrictMono R) (hRc : StrictMono Rc)
    (hc : ∀ x, x ∈ Set.range Rc ↔ x ∉ Set.range R) :
    (X.submatrix R (Fin.castAdd m)).det *
        (Matrix.of fun i j : Fin (r + m) => (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) * G i j).det =
      ((Matrix.of fun i j : Fin (r + m) => (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) * G i j).submatrix
        (Fin.natAdd r) Rc).det := by
  classical
  -- W: colunas de X nas posições R, unitárias nas posições Rᶜ
  set W : Matrix (Fin (r + m)) (Fin (r + m)) ℝ := fun i q =>
    if h : ∃ s, R s = q then X i (Fin.castAdd m h.choose) else if i = q then 1 else 0 with hWdef
  have hWR : ∀ s i, W i (R s) = X i (Fin.castAdd m s) := by
    intro s i
    have h : ∃ s', R s' = R s := ⟨s, rfl⟩
    simp only [hWdef, dif_pos h]
    rw [hR.injective h.choose_spec]
  have hWc : ∀ t i, W i (Rc t) = if i = Rc t then 1 else 0 := by
    intro t i
    have h : ¬ ∃ s, R s = Rc t := fun ⟨s, hs⟩ => ((hc (Rc t)).mp ⟨t, rfl⟩) ⟨s, hs⟩
    simp only [hWdef, dif_neg h]
  have cR : ∀ x, x ∈ Set.range R ↔ x ∉ Set.range Rc := by
    intro x
    constructor
    · intro h1 h2; exact ((hc x).mp h2) h1
    · intro h1; by_contra h2; exact h1 ((hc x).mpr h2)
  have hW := det_unit_cols m r (r + m) (by omega) W Rc Rc R R hRc hRc hR hR cR cR hWc
  have hWsub : W.submatrix R R = X.submatrix R (Fin.castAdd m) := by
    ext s s'
    simp only [Matrix.submatrix_apply, hWR]
  have hs1 : ((-1 : ℝ)) ^ (∑ t, ((Rc t : ℕ) + (Rc t : ℕ))) = 1 := by
    rw [Finset.sum_add_distrib]
    exact Even.neg_one_pow ⟨_, rfl⟩
  rw [hs1, one_mul, hWsub] at hW
  -- Z = G·W
  have hZR : ∀ s i, (G * W) i (R s) = if i = Fin.castAdd m s then 1 else 0 := by
    intro s i
    simp only [Matrix.mul_apply, hWR]
    rw [← Matrix.mul_apply, hGX, Matrix.one_apply]
  have hZc : ∀ t i, (G * W) i (Rc t) = G i (Rc t) := by
    intro t i
    simp only [Matrix.mul_apply, hWc, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    simp
  have hZ := det_unit_cols r m (r + m) rfl (G * W) R (Fin.castAdd m) Rc (Fin.natAdd r) hR
    (Fin.strictMono_castAdd m) hRc (Fin.strictMono_natAdd r) hc range_castAdd_iff hZR
  have hZsub : (G * W).submatrix (Fin.natAdd r) Rc = G.submatrix (Fin.natAdd r) Rc := by
    ext t u
    simp only [Matrix.submatrix_apply, hZc]
  rw [hZsub, Matrix.det_mul, hW] at hZ
  -- A = DGD
  have hA : (Matrix.of fun i j : Fin (r + m) => (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) * G i j).det = G.det := by
    have := det_conj_sign (fun i : Fin (r + m) => (-1 : ℝ) ^ (i : ℕ)) (fun j => (-1 : ℝ) ^ (j : ℕ)) G
    have e : (Matrix.of fun i j : Fin (r + m) => (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) * G i j) =
        Matrix.of fun (i j : Fin (r + m)) => (-1 : ℝ) ^ (i : ℕ) * (-1) ^ (j : ℕ) * G i j := by
      ext i j; simp [pow_add]
    rw [e, this, ← Finset.prod_mul_distrib]
    simp [← pow_add, ← two_mul, pow_mul]
  have hAs : ((Matrix.of fun i j : Fin (r + m) => (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) * G i j).submatrix
      (Fin.natAdd r) Rc).det = (-1) ^ (∑ t : Fin m, ((Fin.natAdd r t : Fin (r + m)) : ℕ)) *
        (-1) ^ (∑ u : Fin m, (Rc u : ℕ)) * (G.submatrix (Fin.natAdd r) Rc).det := by
    have := det_conj_sign (fun t : Fin m => (-1 : ℝ) ^ ((Fin.natAdd r t : Fin (r + m)) : ℕ))
      (fun u => (-1 : ℝ) ^ (Rc u : ℕ)) (G.submatrix (Fin.natAdd r) Rc)
    have e : ((Matrix.of fun i j : Fin (r + m) => (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) * G i j).submatrix
        (Fin.natAdd r) Rc) = Matrix.of fun t u => (-1 : ℝ) ^ ((Fin.natAdd r t : Fin (r + m)) : ℕ) *
          (-1) ^ (Rc u : ℕ) * (G.submatrix (Fin.natAdd r) Rc) t u := by
      ext t u; simp [pow_add]
    rw [e, this, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  rw [hA, hAs]
  -- paridade
  have hpart1 := sum_partition R Rc hR.injective hRc.injective hc (fun x => (x : ℕ))
  have hpart2 : ∑ x : Fin (r + m), (x : ℕ) = ∑ s : Fin r, ((Fin.castAdd m s : Fin (r + m)) : ℕ) +
      ∑ t : Fin m, ((Fin.natAdd r t : Fin (r + m)) : ℕ) := Fin.sum_univ_add _
  have hev : Even ((∑ s, ((R s : ℕ) + ((Fin.castAdd m s : Fin (r + m)) : ℕ))) +
      ((∑ t : Fin m, ((Fin.natAdd r t : Fin (r + m)) : ℕ)) + ∑ u, (Rc u : ℕ))) := by
    rw [Finset.sum_add_distrib]
    have : (∑ s, (R s : ℕ)) + (∑ s : Fin r, ((Fin.castAdd m s : Fin (r + m)) : ℕ)) +
        ((∑ t : Fin m, ((Fin.natAdd r t : Fin (r + m)) : ℕ)) + ∑ u, (Rc u : ℕ)) =
        (∑ x : Fin (r + m), (x : ℕ)) + (∑ x : Fin (r + m), (x : ℕ)) := by
      omega
    rw [this]
    exact ⟨_, rfl⟩
  have hsg := neg_one_pow_even_sum hev
  rw [← pow_add, ← hsg]
  linarith [hZ]

/-! ## 3. Seções de Toeplitz e a transferência -/

/-- Seção `N × N` de `T(u)`. -/
def sec (N : ℕ) (u : ℕ → ℝ) : Matrix (Fin N) (Fin N) ℝ := fun i j => toep u i j

/-- **Seções multiplicam**: `T_N(φ)·T_N(ψ) = T_N(φψ)` (coeficientes de séries formais). -/
theorem sec_mul (N : ℕ) (φ ψ : PowerSeries ℝ) :
    sec N (fun k => PowerSeries.coeff k φ) * sec N (fun k => PowerSeries.coeff k ψ) =
      sec N (fun k => PowerSeries.coeff k (φ * ψ)) := by
  ext i j
  simp only [Matrix.mul_apply, sec, toep]
  set F : ℕ → ℝ := fun k => (if k ≤ (i : ℕ) then PowerSeries.coeff ((i : ℕ) - k) φ else 0) *
    (if (j : ℕ) ≤ k then PowerSeries.coeff (k - (j : ℕ)) ψ else 0) with hF
  have hsum : ∑ x : Fin N, (if (x : ℕ) ≤ (i : ℕ) then PowerSeries.coeff ((i : ℕ) - (x : ℕ)) φ else 0) *
      (if (j : ℕ) ≤ (x : ℕ) then PowerSeries.coeff ((x : ℕ) - (j : ℕ)) ψ else 0) =
      ∑ k ∈ Finset.range N, F k := (Finset.sum_range F).symm
  rw [hsum]
  by_cases hji : (j : ℕ) ≤ (i : ℕ)
  · rw [if_pos hji, mul_comm φ ψ, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun a b => PowerSeries.coeff a ψ * PowerSeries.coeff b φ)]
    have hsub : Finset.Ico (j : ℕ) ((i : ℕ) + 1) ⊆ Finset.range N := by
      intro k hk
      simp only [Finset.mem_Ico, Finset.mem_range] at hk ⊢
      have := i.isLt
      omega
    have hzero : ∀ k ∈ Finset.range N, k ∉ Finset.Ico (j : ℕ) ((i : ℕ) + 1) → F k = 0 := by
      intro k _ hk
      simp only [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
      simp only [hF]
      rcases hk with hk | hk
      · rw [if_neg (by omega : ¬ (j : ℕ) ≤ k), mul_zero]
      · rw [if_neg (by omega : ¬ k ≤ (i : ℕ)), zero_mul]
    rw [← Finset.sum_subset hsub hzero, Finset.sum_Ico_eq_sum_range,
      show (i : ℕ) + 1 - (j : ℕ) = ((i : ℕ) - (j : ℕ)).succ by omega]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t ≤ (i : ℕ) - (j : ℕ) := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    simp only [hF]
    rw [if_pos (by omega), if_pos (by omega), show (i : ℕ) - ((j : ℕ) + t) = (i : ℕ) - (j : ℕ) - t by omega,
      show (j : ℕ) + t - (j : ℕ) = t by omega]
    ring
  · rw [if_neg hji]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [hF]
    split_ifs with h1 h2 <;> first | (exfalso; omega) | ring

theorem sec_one (N : ℕ) : sec N (fun k => PowerSeries.coeff k (1 : PowerSeries ℝ)) = 1 := by
  ext i j
  simp only [sec, toep, PowerSeries.coeff_one, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    rw [if_neg hij]
    split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

/-- Coeficientes de `p(−x)`. -/
theorem coeff_comp_neg_X (P : ℝ[X]) (k : ℕ) : (P.comp (-X)).coeff k = (-1) ^ k * P.coeff k := by
  have : (-X : ℝ[X]) = C (-1) * X := by simp
  rw [this, comp_C_mul_X_coeff]
  ring

/-- **Menores de colunas iniciais** de `T(b)` não negativos. -/
def CCTN (b : ℕ → ℝ) : Prop :=
  ∀ (r : ℕ) (R : Fin r → ℕ), StrictMono R → 0 ≤ ((toep b).submatrix R fun c : Fin r => (c : ℕ)).det

/-- **Transferência (Jacobi)**: `T(coef p)` TN e `p(0) > 0` ⇒ os menores de colunas iniciais de
`T(coef 1/p(−x))` são `≥ 0`. -/
theorem cc_de_tn {P : ℝ[X]} (hP : (toep P.coeff).IsTotallyNonneg) (h0 : 0 < P.coeff 0)
    {B : PowerSeries ℝ} (hB : ((P.comp (-X) : ℝ[X]) : PowerSeries ℝ) * B = 1) :
    CCTN (fun k => PowerSeries.coeff k B) := by
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
  set G := sec (r + m) (fun k => PowerSeries.coeff k ((P.comp (-X) : ℝ[X]) : PowerSeries ℝ)) with hG
  set Xm := sec (r + m) (fun k => PowerSeries.coeff k B) with hX
  have hGX : G * Xm = 1 := by rw [hG, hX, sec_mul, hB, sec_one]
  have hJ := jacobi_init r m G Xm hGX R' Rc hR' hRc hc
  have hA : (Matrix.of fun i j : Fin (r + m) => (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) * G i j) =
      sec (r + m) P.coeff := by
    ext i j
    simp only [Matrix.of_apply, hG, sec, toep, Polynomial.coeff_coe, coeff_comp_neg_X]
    split_ifs with h
    · rw [← mul_assoc, ← pow_add, show (i : ℕ) + (j : ℕ) + ((i : ℕ) - (j : ℕ)) = 2 * (i : ℕ) by omega,
        pow_mul]
      norm_num
    · ring
  rw [hA] at hJ
  have hdetA : 0 < (sec (r + m) P.coeff).det := by
    rw [Matrix.det_of_isLowerTriangular _ ?_]
    · apply Finset.prod_pos
      intro i _
      simp [sec, toep, h0]
    · intro i j hij
      have hij' : (i : ℕ) < (j : ℕ) := hij
      simp only [sec, toep]
      rw [if_neg (by omega)]
  have hminor : 0 ≤ ((sec (r + m) P.coeff).submatrix (Fin.natAdd r) Rc).det := by
    have e : (sec (r + m) P.coeff).submatrix (Fin.natAdd r) Rc =
        (toep P.coeff).submatrix (fun t : Fin m => r + (t : ℕ)) (fun u => (Rc u : ℕ)) := by
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

/-! ## 4. Uma raiz real -/

/-- A recorrência `p(−x)·B = 1` nos coeficientes. -/
def Rec (P : ℝ[X]) (b : ℕ → ℝ) : Prop :=
  ∀ N, ∑ i ∈ Finset.range (N + 1), (-1) ^ i * P.coeff i * b (N - i) = if N = 0 then 1 else 0

theorem rec_of_inv {P : ℝ[X]} {B : PowerSeries ℝ}
    (hB : ((P.comp (-X) : ℝ[X]) : PowerSeries ℝ) * B = 1) : Rec P (fun k => PowerSeries.coeff k B) := by
  intro N
  have h := congrArg (PowerSeries.coeff N) hB
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_one, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a c => PowerSeries.coeff a ((P.comp (-X) : ℝ[X]) : PowerSeries ℝ) * PowerSeries.coeff c B)] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.coeff_coe, coeff_comp_neg_X]

theorem toep_zero_col (b : ℕ → ℝ) (k : ℕ) : toep b k 0 = b k := by
  simp [toep]

theorem toep_one_col (b : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) : toep b k 1 = b (k - 1) := by
  simp [toep, hk]

theorem cc_nonneg {b : ℕ → ℝ} (h : CCTN b) (k : ℕ) : 0 ≤ b k := by
  have := h 1 ![k] (Fin.strictMono_iff_lt_succ.mpr fun i => i.elim0)
  rw [Matrix.det_fin_one] at this
  simpa [toep] using this

theorem cc_minor2 {b : ℕ → ℝ} (h : CCTN b) {k j : ℕ} (hkj : k < j) :
    0 ≤ toep b k 0 * toep b j 1 - toep b k 1 * toep b j 0 := by
  have hm : StrictMono ![k, j] := Fin.strictMono_iff_lt_succ.mpr fun i => by
    fin_cases i
    simpa using hkj
  have := h 2 ![k, j] hm
  rw [Matrix.det_fin_two] at this
  simpa using this

/-- Log-concavidade: `b_k b_{k+2} ≤ b_{k+1}²`. -/
theorem cc_log_concave {b : ℕ → ℝ} (h : CCTN b) (k : ℕ) : b k * b (k + 2) ≤ b (k + 1) ^ 2 := by
  have := cc_minor2 h (show k + 1 < k + 2 by omega)
  rw [toep_zero_col, toep_zero_col, toep_one_col b (by omega), toep_one_col b (by omega),
    show k + 2 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega] at this
  nlinarith [this]

/-- Sem zeros internos: `b_k = 0`, `b_{k−1} > 0` ⇒ `b_j = 0` para `j > k`. -/
theorem cc_zero_prop {b : ℕ → ℝ} (h : CCTN b) {k : ℕ} (hk : 1 ≤ k) (hbk : b k = 0)
    (hprev : 0 < b (k - 1)) {j : ℕ} (hj : k < j) : b j = 0 := by
  have := cc_minor2 h hj
  rw [toep_zero_col, toep_zero_col, toep_one_col b hk, toep_one_col b (by omega), hbk] at this
  have hbj := cc_nonneg h j
  by_contra hne
  have hpos : 0 < b j := lt_of_le_of_ne hbj (Ne.symm hne)
  have := mul_pos hprev hpos
  linarith

theorem coeff_natDegree_ne_zero {P : ℝ[X]} (h0 : 0 < P.coeff 0) : P.coeff P.natDegree ≠ 0 := by
  have hP : P ≠ 0 := fun h => by rw [h] at h0; simp at h0
  exact leadingCoeff_ne_zero.mpr hP

/-- **Positividade**: `b_k > 0` para todo `k` (grau `≥ 1`). -/
theorem b_pos {P : ℝ[X]} {b : ℕ → ℝ} (hrec : Rec P b) (h0 : 0 < P.coeff 0) (hdeg : 1 ≤ P.natDegree)
    (hcc : CCTN b) (k : ℕ) : 0 < b k := by
  classical
  have hb0 : 0 < b 0 := by
    have h := hrec 0
    rw [Finset.sum_range_one, if_pos rfl] at h
    norm_num at h
    by_contra hle
    push_neg at hle
    have := mul_nonpos_of_nonneg_of_nonpos h0.le hle
    linarith
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
  have hzero : ∀ j, Nat.find hz - 1 < j → b j = 0 := by
    intro j hj
    rcases Nat.eq_or_lt_of_le (show Nat.find hz ≤ j by omega) with h | h
    · rw [← h]; exact hk0z
    · exact cc_zero_prop hcc hk0pos hk0z hprev h
  have h := hrec (P.natDegree + (Nat.find hz - 1))
  rw [if_neg (by omega), Finset.sum_eq_single P.natDegree] at h
  · rw [show P.natDegree + (Nat.find hz - 1) - P.natDegree = Nat.find hz - 1 by omega] at h
    have : (-1 : ℝ) ^ P.natDegree * P.coeff P.natDegree * b (Nat.find hz - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (coeff_natDegree_ne_zero h0)) hprev.ne'
    exact this h
  · intro i _ hin
    rcases lt_or_gt_of_ne hin with hlt | hgt
    · rw [hzero _ (by omega), mul_zero]
    · rw [coeff_eq_zero_of_natDegree_lt hgt]; ring
  · intro hn
    exact absurd (Finset.mem_range.mpr (by omega)) hn

/-- A razão `b_{k+1}/b_k` decresce e converge a `L ≥ 0`. -/
theorem ratio_tendsto {b : ℕ → ℝ} (hcc : CCTN b) (hpos : ∀ k, 0 < b k) :
    ∃ L, 0 ≤ L ∧ Tendsto (fun k => b (k + 1) / b k) atTop (𝓝 L) := by
  have hanti : Antitone (fun k => b (k + 1) / b k) := by
    refine antitone_nat_of_succ_le fun k => ?_
    show b (k + 2) / b (k + 1) ≤ b (k + 1) / b k
    rw [div_le_div_iff₀ (hpos _) (hpos _)]
    have := cc_log_concave hcc k
    nlinarith [this]
  have hbdd : BddBelow (Set.range fun k => b (k + 1) / b k) :=
    ⟨0, by rintro _ ⟨k, rfl⟩; exact (div_pos (hpos _) (hpos _)).le⟩
  exact ⟨_, le_ciInf fun k => (div_pos (hpos _) (hpos _)).le, tendsto_atTop_ciInf hanti hbdd⟩

/-- `b_{M+j}/b_M → L^j`. -/
theorem ratio_pow {b : ℕ → ℝ} (hpos : ∀ k, 0 < b k) {L : ℝ}
    (hlim : Tendsto (fun k => b (k + 1) / b k) atTop (𝓝 L)) (j : ℕ) :
    Tendsto (fun M => b (M + j) / b M) atTop (𝓝 (L ^ j)) := by
  induction j with
  | zero =>
    simp only [add_zero, pow_zero]
    exact tendsto_const_nhds.congr fun M => (div_self (hpos M).ne').symm
  | succ j ih =>
    have h2 : Tendsto (fun M => b (M + j + 1) / b (M + j)) atTop (𝓝 L) :=
      hlim.comp (tendsto_add_atTop_nat j)
    rw [pow_succ]
    refine (ih.mul h2).congr fun M => ?_
    rw [show M + (j + 1) = M + j + 1 by ring]
    field_simp [(hpos (M + j)).ne', (hpos M).ne']

/-- **Uma raiz real** (sem Pringsheim): `L > 0` e `p(−1/L) = 0`. -/
theorem raiz_real {P : ℝ[X]} {b : ℕ → ℝ} (hrec : Rec P b) (h0 : 0 < P.coeff 0) (hdeg : 1 ≤ P.natDegree)
    (hpos : ∀ k, 0 < b k) {L : ℝ} (hL0 : 0 ≤ L) (hlim : Tendsto (fun k => b (k + 1) / b k) atTop (𝓝 L)) :
    0 < L ∧ P.IsRoot (-L⁻¹) := by
  have hsum0 : ∀ M, ∑ i ∈ Finset.range (P.natDegree + 1),
      (-1) ^ i * P.coeff i * (b (M + (P.natDegree - i)) / b M) = 0 := by
    intro M
    have h := hrec (M + P.natDegree)
    rw [if_neg (by omega)] at h
    have hsub : Finset.range (P.natDegree + 1) ⊆ Finset.range (M + P.natDegree + 1) :=
      Finset.range_subset_range.mpr (by omega)
    rw [← Finset.sum_subset hsub ?_] at h
    · have e : ∑ i ∈ Finset.range (P.natDegree + 1),
          (-1) ^ i * P.coeff i * (b (M + (P.natDegree - i)) / b M) =
          (∑ i ∈ Finset.range (P.natDegree + 1), (-1) ^ i * P.coeff i * b (M + P.natDegree - i)) / b M := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i hi => ?_
        have := Finset.mem_range.mp hi
        rw [show M + (P.natDegree - i) = M + P.natDegree - i by omega]
        ring
      rw [e, h, zero_div]
    · intro i _ hi
      have : P.natDegree < i := by simp at hi; omega
      rw [coeff_eq_zero_of_natDegree_lt this]
      ring
  have hlimsum : Tendsto (fun M => ∑ i ∈ Finset.range (P.natDegree + 1),
      (-1) ^ i * P.coeff i * (b (M + (P.natDegree - i)) / b M)) atTop
      (𝓝 (∑ i ∈ Finset.range (P.natDegree + 1), (-1) ^ i * P.coeff i * L ^ (P.natDegree - i))) :=
    tendsto_finset_sum _ fun i _ => (ratio_pow hpos hlim (P.natDegree - i)).const_mul _
  have hS : ∑ i ∈ Finset.range (P.natDegree + 1), (-1) ^ i * P.coeff i * L ^ (P.natDegree - i) = 0 :=
    tendsto_nhds_unique hlimsum (tendsto_const_nhds.congr fun M => (hsum0 M).symm)
  have hLpos : 0 < L := by
    rcases hL0.lt_or_eq with h | h
    · exact h
    exfalso
    rw [← h, Finset.sum_eq_single P.natDegree] at hS
    · rw [Nat.sub_self, pow_zero, mul_one] at hS
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (coeff_natDegree_ne_zero h0) hS
    · intro i hi hin
      have := Finset.mem_range.mp hi
      rw [zero_pow (by omega)]
      ring
    · intro hn
      exact absurd (Finset.mem_range.mpr (by omega)) hn
  refine ⟨hLpos, ?_⟩
  rw [IsRoot, eval_eq_sum_range]
  have e : L ^ P.natDegree * ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (-L⁻¹) ^ i =
      ∑ i ∈ Finset.range (P.natDegree + 1), (-1) ^ i * P.coeff i * L ^ (P.natDegree - i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ P.natDegree := by have := Finset.mem_range.mp hi; omega
    rw [← pow_sub_mul_pow L hi', neg_pow, inv_pow]
    have hLi : L ^ i ≠ 0 := pow_ne_zero _ hLpos.ne'
    calc L ^ (P.natDegree - i) * L ^ i * (P.coeff i * ((-1) ^ i * (L ^ i)⁻¹))
        = (-1) ^ i * P.coeff i * L ^ (P.natDegree - i) * (L ^ i * (L ^ i)⁻¹) := by ring
      _ = (-1) ^ i * P.coeff i * L ^ (P.natDegree - i) := by rw [mul_inv_cancel₀ hLi, mul_one]
  rw [hS] at e
  exact (mul_eq_zero.mp e).resolve_left (pow_ne_zero _ hLpos.ne')

/-! ## 5. Remoção do fator -/

/-- `(1 − Lx)·B`: `b′_k = b_k − L b_{k−1}`. -/
def bL (b : ℕ → ℝ) (L : ℝ) (k : ℕ) : ℝ := b k - if k = 0 then 0 else L * b (k - 1)

theorem toep_bL (b : ℕ → ℝ) (L : ℝ) (i c : ℕ) :
    toep b i c - L * toep b i (c + 1) = toep (bL b L) i c := by
  simp only [toep, bL]
  by_cases h1 : c + 1 ≤ i
  · rw [if_pos h1, if_pos (show c ≤ i by omega), if_pos (show c ≤ i by omega),
      if_neg (show i - c ≠ 0 by omega), show i - (c + 1) = i - c - 1 by omega]
  · by_cases h2 : c ≤ i
    · have : c = i := by omega
      subst this
      rw [if_neg h1, if_pos le_rfl, if_pos le_rfl, Nat.sub_self, if_pos rfl]
      ring
    · rw [if_neg h1, if_neg h2, if_neg h2]
      ring

/-- Operações de coluna `col_c ← col_c − L·col_{c+1}`. -/
def opCol (n : ℕ) (L : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun c' c => if c' = c then 1 else if (c' : ℕ) = c + 1 then -L else 0

theorem det_opCol (n : ℕ) (L : ℝ) : (opCol n L).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ ?_]
  · simp [opCol]
  · intro i j hij
    have hij' : (i : ℕ) < (j : ℕ) := hij
    simp only [opCol]
    rw [if_neg (fun h => by rw [h] at hij'; omega), if_neg (by omega)]

theorem mul_opCol_apply {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ) (L : ℝ) (i : Fin k) (c : Fin n) :
    (A * opCol n L) i c = A i c - if h : (c : ℕ) + 1 < n then L * A i ⟨c + 1, h⟩ else 0 := by
  simp only [Matrix.mul_apply, opCol]
  have e : ∀ c' : Fin n, A i c' * (if c' = c then 1 else if (c' : ℕ) = c + 1 then -L else 0) =
      (if c' = c then A i c' else 0) + (if (c' : ℕ) = c + 1 then -L * A i c' else 0) := by
    intro c'
    by_cases h1 : c' = c
    · subst h1
      simp
    · rw [if_neg h1, if_neg h1, zero_add]
      split_ifs <;> ring
  rw [Finset.sum_congr rfl fun c' _ => e c', Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(c : ℕ) + 1, h⟩]
    · simp only [if_true]
      ring
    · intro c' _ hc'
      rw [if_neg (fun h' => hc' (Fin.ext h'))]
    · simp
  · rw [Finset.sum_eq_zero fun c' _ => by rw [if_neg (by have := c'.isLt; omega)]]
    ring

/-- **Remoção do fator**: se os menores de colunas iniciais de `T(b)` são `≥ 0`, `b > 0` e
`b_{k+1}/b_k → L`, então o mesmo vale para `b′ = (1 − Lx)·b`. Cada menor de `T(b′)` é o limite de
menores `(r+1)×(r+1)` de `T(b)` (linhas `R ∪ {M + J + r}`) após operações de coluna e escala. -/
theorem cc_remove {b : ℕ → ℝ} (hcc : CCTN b) (hpos : ∀ k, 0 < b k) {L : ℝ}
    (hlim : Tendsto (fun k => b (k + 1) / b k) atTop (𝓝 L)) : CCTN (bL b L) := by
  classical
  intro r R hR
  set J : ℕ := (Finset.univ.sup fun s => R s) + 1 with hJ
  have hRJ : ∀ s, R s < J := fun s => by
    have := Finset.le_sup (f := fun s => R s) (Finset.mem_univ s)
    omega
  set rows : ℕ → Fin (r + 1) → ℕ := fun M i => if h : (i : ℕ) < r then R ⟨i, h⟩ else M + J + r
    with hrows
  have hrowsm : ∀ M, StrictMono (rows M) := by
    intro M a c hac
    have hac' : (a : ℕ) < c := hac
    simp only [hrows]
    by_cases hc : (c : ℕ) < r
    · rw [dif_pos (by omega), dif_pos hc]
      exact hR (show (⟨a, by omega⟩ : Fin r) < ⟨c, hc⟩ from hac')
    · rw [dif_neg hc]
      by_cases ha : (a : ℕ) < r
      · rw [dif_pos ha]
        have := hRJ ⟨a, ha⟩
        omega
      · exfalso
        have := c.isLt
        omega
  set A : ℕ → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ :=
    fun M => (toep b).submatrix (rows M) (fun c => (c : ℕ)) with hA
  set W : ℕ → Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := fun M => Matrix.of fun i c =>
    (if (i : ℕ) < r then 1 else (b (M + J))⁻¹) * (A M * opCol (r + 1) L) i c with hW
  have hWnn : ∀ M, 0 ≤ (W M).det := by
    intro M
    simp only [hW]
    rw [Matrix.det_mul_column, Matrix.det_mul, det_opCol, mul_one]
    apply mul_nonneg
    · apply Finset.prod_nonneg
      intro i _
      split_ifs
      · norm_num
      · exact (inv_pos.mpr (hpos _)).le
    · exact hcc (r + 1) (rows M) (hrowsm M)
  set Winf : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ := Matrix.of fun i c =>
    if (i : ℕ) < r then (A 0 * opCol (r + 1) L) i c else if (c : ℕ) < r then 0 else 1 with hWinf
  have hrow_const : ∀ M (i : Fin (r + 1)), (i : ℕ) < r → ∀ c,
      (A M * opCol (r + 1) L) i c = (A 0 * opCol (r + 1) L) i c := by
    intro M i hi c
    rw [mul_opCol_apply, mul_opCol_apply]
    simp only [hA, Matrix.submatrix_apply, hrows, dif_pos hi]
  have hconv : Tendsto W atTop (𝓝 Winf) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun c => ?_
    simp only [hW, hWinf, Matrix.of_apply]
    by_cases hi : (i : ℕ) < r
    · simp only [if_pos hi, one_mul]
      exact tendsto_const_nhds.congr fun M => (hrow_const M i hi c).symm
    · simp only [if_neg hi, mul_opCol_apply]
      have hAi : ∀ M (c' : Fin (r + 1)), A M i c' = b (M + J + (r - c')) := by
        intro M c'
        have := c'.isLt
        simp only [hA, Matrix.submatrix_apply, hrows, dif_neg hi, toep]
        rw [if_pos (by omega), show M + J + r - c' = M + J + (r - c') by omega]
      by_cases hc : (c : ℕ) < r
      · have hc1 : (c : ℕ) + 1 < r + 1 := by omega
        simp only [if_pos hc, dif_pos hc1]
        obtain ⟨j, hj⟩ : ∃ j, r - (c : ℕ) = j + 1 := ⟨r - c - 1, by omega⟩
        have hj2 : r - ((c : ℕ) + 1) = j := by omega
        simp only [hAi, hj, hj2]
        have h1 := (ratio_pow hpos hlim (j + 1)).comp (tendsto_add_atTop_nat J)
        have h2 := (ratio_pow hpos hlim j).comp (tendsto_add_atTop_nat J)
        have h3 := h1.sub (h2.const_mul L)
        have e0 : L ^ (j + 1) - L * L ^ j = 0 := by ring
        rw [e0] at h3
        refine h3.congr fun M => ?_
        simp only [Function.comp]
        ring
      · rw [if_neg hc]
        have hcr : (c : ℕ) = r := by have := c.isLt; omega
        simp only [hAi, hcr, Nat.sub_self, add_zero, lt_self_iff_false, ↓reduceDIte, sub_zero]
        exact tendsto_const_nhds.congr fun M => (inv_mul_cancel₀ (hpos _).ne').symm
  have hdetinf : Winf.det = ((toep (bL b L)).submatrix R fun c : Fin r => (c : ℕ)).det := by
    rw [Matrix.det_succ_row Winf (Fin.last r), Finset.sum_eq_single (Fin.last r)]
    · have hsub : Winf.submatrix (Fin.last r).succAbove (Fin.last r).succAbove =
          (toep (bL b L)).submatrix R fun c : Fin r => (c : ℕ) := by
        ext s c
        rw [Fin.succAbove_last]
        simp only [Matrix.submatrix_apply, hWinf, Matrix.of_apply, Fin.coe_castSucc, if_pos s.isLt]
        rw [mul_opCol_apply]
        simp only [Fin.coe_castSucc]
        rw [dif_pos (show (c : ℕ) + 1 < r + 1 by omega)]
        simp only [hA, hrows, Matrix.submatrix_apply, Fin.coe_castSucc, dif_pos s.isLt, Fin.eta]
        exact toep_bL b L (R s) c
      have hl : Winf (Fin.last r) (Fin.last r) = 1 := by simp [hWinf]
      rw [hsub, hl, Fin.val_last, Even.neg_one_pow ⟨r, rfl⟩]
      ring
    · intro c _ hc
      have hcr : (c : ℕ) < r := by
        have := c.isLt
        have : (c : ℕ) ≠ r := fun h => hc (Fin.ext (by simp [h]))
        omega
      have : Winf (Fin.last r) c = 0 := by simp [hWinf, hcr]
      rw [this]
      ring
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hlimdet : Tendsto (fun M => (W M).det) atTop (𝓝 Winf.det) :=
    ((continuous_id.matrix_det).tendsto Winf).comp hconv
  rw [← hdetinf]
  exact ge_of_tendsto' hlimdet hWnn

/-! ## 6. Indução no grau e o teorema -/

theorem cc_smul {b : ℕ → ℝ} (h : CCTN b) {c : ℝ} (hc : 0 ≤ c) : CCTN (fun k => c * b k) := by
  intro r R hR
  have e : (toep fun k => c * b k).submatrix R (fun j : Fin r => (j : ℕ)) =
      c • (toep b).submatrix R (fun j : Fin r => (j : ℕ)) := by
    ext i j
    simp only [toep, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [e, Matrix.det_smul]
  exact mul_nonneg (pow_nonneg hc _) (h r R hR)

/-- **Indução no grau**: `p(0) > 0`, `p(−x)·B = 1` e os menores de colunas iniciais de `T(coef B)`
`≥ 0` ⇒ `p` tem `deg p` zeros reais, todos `≤ 0`, e coeficiente líder `≥ 0`. -/
theorem asw_rec : ∀ (n : ℕ) (P : ℝ[X]), P.natDegree = n → 0 < P.coeff 0 → ∀ B : PowerSeries ℝ,
    ((P.comp (-X) : ℝ[X]) : PowerSeries ℝ) * B = 1 → CCTN (fun k => PowerSeries.coeff k B) →
    Multiset.card P.roots = P.natDegree ∧ (∀ x ∈ P.roots, x ≤ 0) ∧ 0 ≤ P.leadingCoeff := by
  intro n
  induction n with
  | zero =>
    intro P hn h0 B _ _
    have hP : P = C (P.coeff 0) := eq_C_of_natDegree_eq_zero hn
    refine ⟨?_, ?_, ?_⟩
    · rw [hn, hP, roots_C]
      simp
    · intro x hx
      rw [hP, roots_C] at hx
      simp at hx
    · rw [leadingCoeff, hn]
      exact h0.le
  | succ n ih =>
    intro P hn h0 B hB hcc
    have hrec := rec_of_inv hB
    have hdeg : 1 ≤ P.natDegree := by omega
    have hpos := b_pos hrec h0 hdeg hcc
    obtain ⟨L, hL0, hlim⟩ := ratio_tendsto hcc hpos
    obtain ⟨hLpos, hroot⟩ := raiz_real hrec h0 hdeg hpos hL0 hlim
    set a : ℝ := -L⁻¹ with ha
    set Q := P /ₘ (X - C a) with hQ
    have hPQ : (X - C a) * Q = P := mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hP0 : P ≠ 0 := fun h => by rw [h] at h0; simp at h0
    have hQn : Q.natDegree = n := by
      rw [hQ, natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C, hn]
      omega
    have hQ0 : 0 < Q.coeff 0 := by
      have h := congrArg (fun p => p.coeff 0) hPQ
      simp only [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero] at h
      rw [ha, zero_sub, neg_neg] at h
      have hLi : 0 < L⁻¹ := inv_pos.mpr hLpos
      by_contra hle
      push_neg at hle
      have := mul_nonpos_of_nonneg_of_nonpos hLi.le hle
      linarith
    have hpoly : C L⁻¹ * Q.comp (-X) = P.comp (-X) + X * Q.comp (-X) := by
      rw [← hPQ, mul_comp_neg_X, sub_comp, X_comp, C_comp, ha, C_neg]
      ring
    set B2 : PowerSeries ℝ := PowerSeries.C L⁻¹ * B - PowerSeries.X * B with hB2
    have hB2' : ((Q.comp (-X) : ℝ[X]) : PowerSeries ℝ) * B2 = 1 := by
      have e := congrArg (fun p : ℝ[X] => (p : PowerSeries ℝ)) hpoly
      simp only [Polynomial.coe_mul, Polynomial.coe_add, Polynomial.coe_C, Polynomial.coe_X] at e
      calc ((Q.comp (-X) : ℝ[X]) : PowerSeries ℝ) * B2
          = (PowerSeries.C L⁻¹ * ((Q.comp (-X) : ℝ[X]) : PowerSeries ℝ) -
              PowerSeries.X * ((Q.comp (-X) : ℝ[X]) : PowerSeries ℝ)) * B := by
            rw [hB2]
            ring
        _ = ((P.comp (-X) : ℝ[X]) : PowerSeries ℝ) * B := by
            rw [e]
            ring
        _ = 1 := hB
    have hcoef : (fun k => PowerSeries.coeff k B2) =
        fun k => L⁻¹ * bL (fun k => PowerSeries.coeff k B) L k := by
      funext k
      rw [hB2, map_sub, PowerSeries.coeff_C_mul]
      cases k with
      | zero =>
        rw [PowerSeries.coeff_zero_X_mul]
        simp [bL]
      | succ k =>
        rw [PowerSeries.coeff_succ_X_mul]
        simp only [bL, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hLpos.ne', one_mul]
    have hcc2 : CCTN (fun k => PowerSeries.coeff k B2) := by
      rw [hcoef]
      exact cc_smul (cc_remove hcc hpos hlim) (inv_pos.mpr hLpos).le
    obtain ⟨h1, h2, h3⟩ := ih Q hQn hQ0 B2 hB2' hcc2
    have hroots : P.roots = a ::ₘ Q.roots := by
      rw [← hPQ, roots_mul (by rw [hPQ]; exact hP0), roots_X_sub_C, Multiset.singleton_add]
    refine ⟨?_, ?_, ?_⟩
    · rw [hroots, Multiset.card_cons, h1, hQn, hn]
    · intro x hx
      rw [hroots, Multiset.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [ha]
        exact neg_nonpos.mpr (inv_pos.mpr hLpos).le
      · exact h2 x hx
    · rw [← hPQ, leadingCoeff_monic_mul (monic_X_sub_C a)]
      exact h3

/-- **Recíproca de Aissen–Schoenberg–Whitney (polinômios)**: `p(0) > 0` e `T(coef p)` TN ⇒ `p` só tem
zeros reais `≤ 0` (contados com multiplicidade, `deg p` deles) e coeficiente líder `≥ 0`. -/
theorem asw_reciproca {P : ℝ[X]} (h0 : 0 < P.coeff 0) (hP : (toep P.coeff).IsTotallyNonneg) :
    Multiset.card P.roots = P.natDegree ∧ (∀ x ∈ P.roots, x ≤ 0) ∧ 0 ≤ P.leadingCoeff := by
  set B : PowerSeries ℝ := (((P.comp (-X) : ℝ[X]) : PowerSeries ℝ))⁻¹ with hBdef
  have hB : ((P.comp (-X) : ℝ[X]) : PowerSeries ℝ) * B = 1 := by
    apply PowerSeries.mul_inv_cancel
    rw [Polynomial.constantCoeff_coe, coeff_comp_neg_X]
    simp [h0.ne']
  exact asw_rec _ P rfl h0 B hB (cc_de_tn hP h0 hB)

/-- **Teorema de Aissen–Schoenberg–Whitney para polinômios** (as duas direções): para `p(0) > 0`,
`T(coef p)` é totalmente não negativa **⟺** `p` só tem zeros reais `≤ 0` e coeficiente líder `≥ 0`. -/
theorem asw_iff {P : ℝ[X]} (h0 : 0 < P.coeff 0) :
    (toep P.coeff).IsTotallyNonneg ↔
      (Multiset.card P.roots = P.natDegree ∧ (∀ x ∈ P.roots, x ≤ 0) ∧ 0 ≤ P.leadingCoeff) :=
  ⟨asw_reciproca h0, fun ⟨h1, h2, h3⟩ => ATK.ToeplitzTN.tn_de_raizes h1 h2 h3⟩

/-- **Forma fatorada**: `p(0) > 0` e `T(coef p)` TN ⇒ `p = c·∏(x − xᵢ)` com todos os `xᵢ ≤ 0` reais. -/
theorem asw_fatora {P : ℝ[X]} (h0 : 0 < P.coeff 0) (hP : (toep P.coeff).IsTotallyNonneg) :
    C P.leadingCoeff * (P.roots.map fun x => X - C x).prod = P ∧ ∀ x ∈ P.roots, x ≤ 0 := by
  obtain ⟨h1, h2, _⟩ := asw_reciproca h0 hP
  exact ⟨C_leadingCoeff_mul_prod_multiset_X_sub_C h1, h2⟩

end ATK.ASWRec

#print axioms ATK.ASWRec.succAbove_preAbove
#print axioms ATK.ASWRec.val_succAbove_of_lt
#print axioms ATK.ASWRec.neg_one_pow_even_sum
#print axioms ATK.ASWRec.det_unit_cols
#print axioms ATK.ASWRec.range_castAdd_iff
#print axioms ATK.ASWRec.sum_partition
#print axioms ATK.ASWRec.det_conj_sign
#print axioms ATK.ASWRec.jacobi_init
#print axioms ATK.ASWRec.sec_mul
#print axioms ATK.ASWRec.sec_one
#print axioms ATK.ASWRec.coeff_comp_neg_X
#print axioms ATK.ASWRec.cc_de_tn
#print axioms ATK.ASWRec.rec_of_inv
#print axioms ATK.ASWRec.toep_zero_col
#print axioms ATK.ASWRec.toep_one_col
#print axioms ATK.ASWRec.cc_nonneg
#print axioms ATK.ASWRec.cc_minor2
#print axioms ATK.ASWRec.cc_log_concave
#print axioms ATK.ASWRec.cc_zero_prop
#print axioms ATK.ASWRec.coeff_natDegree_ne_zero
#print axioms ATK.ASWRec.b_pos
#print axioms ATK.ASWRec.ratio_tendsto
#print axioms ATK.ASWRec.ratio_pow
#print axioms ATK.ASWRec.raiz_real
#print axioms ATK.ASWRec.toep_bL
#print axioms ATK.ASWRec.det_opCol
#print axioms ATK.ASWRec.mul_opCol_apply
#print axioms ATK.ASWRec.cc_remove
#print axioms ATK.ASWRec.cc_smul
#print axioms ATK.ASWRec.asw_rec
#print axioms ATK.ASWRec.asw_reciproca
#print axioms ATK.ASWRec.asw_iff
#print axioms ATK.ASWRec.asw_fatora
