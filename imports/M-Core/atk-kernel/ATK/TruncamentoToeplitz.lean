import ATK.TuranDispersao

/-!
# ATK — Truncamento de Toeplitz: `P(N)`, `Q(N+1)`, o nível da primeira falha e o fluxo

`T(a)_{ij} = a_{i−j}`. `P(a, N)`: todo menor de `T(a)` com índices `≤ N` é `≥ 0` (positividade total do
truncamento `T_N`, `P_iff_trunc`). `Q(a, N)`: os menores com índices `≤ N` **que usam a linha ou a coluna
`N`**.

* `P(N+1) ⟺ P(N) ∧ Q(N+1)` (`P_succ_iff`); `TN(T(a)) ⟺ ∀N, P(N)` (`tn_iff_P`); `P(0) ⟺ a₀ ≥ 0`;
* **indução** (`inducao`): `a₀ ≥ 0` e `P(N) ⇒ Q(N+1)` para todo `N` dão TN;
* **primeira falha** (`nivel_unico`): se `T(a)` não é TN e `a₀ ≥ 0`, existe **um único** `N` com
  `P(N) ∧ ¬P(N+1)`, e nele falha `Q(N+1)` (`primeira_falha`);
* para `Ξ`: `RH ⟺ ∀N, P(N)` ⟺ `∀N, Q(N+1)` (`rh_iff_P`, `rh_iff_Q`); **`P(1)` é incondicional**
  (`P1_Xi`); **`P(2)` vale sob o lema de Csordas** (`P2_Xi_de_csordas`, BUILD_PENDING); logo um zero
  fora da reta força um nível de falha `N ≥ 1`, e `N ≥ 2` com um menor negativo de **ordem `≥ 3`** sob
  Csordas (`nivel_de_zero_fora`, `ordem_ge_tres_de_csordas`);
* o menor `3×3` contíguo é `a₁³ − 2a₀a₁a₂ + a₀²a₃` (`menor3`); o defeito de ordem 2 nos momentos é
  `a₁² − a₀a₂ = (6m₁² − m₀m₂)/24` para `aₙ = mₙ/(2n)!` (`defeito_momentos`);
* **fluxo** `bₙ(τ) = aₙe^{−τn(n−1)}`: `D₂(b(τ))ₙ = e^{−2τ(n+1)n}(a_{n+1}² − e^{−2τ}aₙa_{n+2})`
  (`D2_fluxo`), crescente em `τ` (`defeito_monotono`). **Volta válida**: positividade para **todo**
  `τ > 0` dá positividade em `τ = 0` (`volta_valida`, e para TN inteira, `volta_valida_tn`). **Volta
  ingênua inválida**: um único `τ > 0` não basta (`volta_ingenua_invalida`, `a = (1, 1, 2, 1, …)`).
-/

open Matrix Filter Topology Set

namespace ATK.TruncToep

open ATK.ToeplitzTN (toep)

/-- `P(a, N)`: os menores de `T(a)` com índices `≤ N` são `≥ 0`. -/
def P (a : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ ⦃r : ℕ⦄ ⦃I J : Fin r → ℕ⦄, StrictMono I → StrictMono J → (∀ p, I p ≤ N) → (∀ q, J q ≤ N) →
    0 ≤ ((toep a).submatrix I J).det

/-- `Q(a, N)`: os menores com índices `≤ N` que usam a linha ou a coluna `N`. -/
def Q (a : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ ⦃r : ℕ⦄ ⦃I J : Fin r → ℕ⦄, StrictMono I → StrictMono J → (∀ p, I p ≤ N) → (∀ q, J q ≤ N) →
    ((∃ p, I p = N) ∨ (∃ q, J q = N)) → 0 ≤ ((toep a).submatrix I J).det

/-- O truncamento `T_N`, matriz `(N+1) × (N+1)`. -/
def trunc (a : ℕ → ℝ) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  (toep a).submatrix Fin.val Fin.val

variable {a : ℕ → ℝ}

theorem P_mono {N M : ℕ} (h : N ≤ M) (hP : P a M) : P a N :=
  fun _ _ _ hI hJ hIN hJN => hP hI hJ (fun p => (hIN p).trans h) (fun q => (hJN q).trans h)

/-- **`P(N+1) ⟺ P(N) ∧ Q(N+1)`.** -/
theorem P_succ_iff (N : ℕ) : P a (N + 1) ↔ P a N ∧ Q a (N + 1) := by
  constructor
  · intro h
    exact ⟨P_mono (Nat.le_succ N) h, fun _ _ _ hI hJ hIN hJN _ => h hI hJ hIN hJN⟩
  · rintro ⟨hP, hQ⟩ r I J hI hJ hIN hJN
    by_cases hu : (∃ p, I p = N + 1) ∨ (∃ q, J q = N + 1)
    · exact hQ hI hJ hIN hJN hu
    · push Not at hu
      exact hP hI hJ (fun p => by have := hIN p; have := hu.1 p; omega)
        (fun q => by have := hJN q; have := hu.2 q; omega)

/-- `P(N)` é a positividade total do truncamento `T_N`. -/
theorem P_iff_trunc (N : ℕ) : P a N ↔ (trunc a N).IsTotallyNonneg := by
  constructor
  · intro h r rows cols hr hc
    have := h (Fin.val_strictMono.comp hr) (Fin.val_strictMono.comp hc)
      (fun p => Nat.lt_succ_iff.mp (rows p).isLt) (fun q => Nat.lt_succ_iff.mp (cols q).isLt)
    simpa [trunc, Matrix.submatrix_submatrix] using this
  · intro h r I J hI hJ hIN hJN
    let rows : Fin r → Fin (N + 1) := fun p => ⟨I p, Nat.lt_succ_of_le (hIN p)⟩
    let cols : Fin r → Fin (N + 1) := fun q => ⟨J q, Nat.lt_succ_of_le (hJN q)⟩
    have hr : StrictMono rows := fun x y hxy => by
      show (⟨I x, _⟩ : Fin (N + 1)) < ⟨I y, _⟩
      exact Fin.mk_lt_mk.mpr (hI hxy)
    have hc : StrictMono cols := fun x y hxy => by
      show (⟨J x, _⟩ : Fin (N + 1)) < ⟨J y, _⟩
      exact Fin.mk_lt_mk.mpr (hJ hxy)
    exact h hr hc

/-- **`TN(T(a)) ⟺ ∀ N, P(N)`.** -/
theorem tn_iff_P : (toep a).IsTotallyNonneg ↔ ∀ N, P a N := by
  constructor
  · intro h N r I J hI hJ _ _
    exact h hI hJ
  · intro h r rows cols hr hc
    refine h (∑ p, rows p + ∑ q, cols q) hr hc (fun p => ?_) (fun q => ?_)
    · exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)).trans
        (Nat.le_add_right _ _)
    · exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)).trans
        (Nat.le_add_left _ _)

theorem toep_diag (i : ℕ) : toep a i i = a 0 := by simp [toep]

theorem toep_sub {i j : ℕ} (h : j ≤ i) : toep a i j = a (i - j) := by simp [toep, h]

theorem toep_acima {i j : ℕ} (h : i < j) : toep a i j = 0 := by
  simp [toep, Nat.not_le.mpr h]

/-- **`P(0) ⟺ a₀ ≥ 0`.** -/
theorem P_zero_iff : P a 0 ↔ 0 ≤ a 0 := by
  constructor
  · intro h
    have := h (r := 1) (I := ![0]) (J := ![0]) (Subsingleton.strictMono _) (Subsingleton.strictMono _)
      (fun _ => by simp) (fun _ => by simp)
    rw [Matrix.det_fin_one] at this
    simpa [toep, Matrix.submatrix_apply] using this
  · intro h0 r I J hI hJ hIN hJN
    rcases r with _ | _ | r
    · simp
    · rw [Matrix.det_fin_one]
      simp only [submatrix_apply]
      have h1 : I 0 = 0 := Nat.le_zero.mp (hIN 0)
      have h2 : J 0 = 0 := Nat.le_zero.mp (hJN 0)
      rw [h1, h2, toep_diag]
      exact h0
    · exfalso
      have := hI (show (0 : Fin (r + 2)) < 1 from by simp)
      have := hIN 1
      omega

/-- **Indução**: `a₀ ≥ 0` e `P(N) ⇒ Q(N+1)` para todo `N` ⇒ TN. -/
theorem inducao (h0 : 0 ≤ a 0) (hstep : ∀ N, P a N → Q a (N + 1)) : (toep a).IsTotallyNonneg := by
  rw [tn_iff_P]
  intro N
  induction N with
  | zero => exact P_zero_iff.mpr h0
  | succ N ih => exact (P_succ_iff N).mpr ⟨ih, hstep N ih⟩

/-- **O nível da primeira falha é único.** -/
theorem nivel_unico (h0 : 0 ≤ a 0) (hn : ¬ (toep a).IsTotallyNonneg) :
    ∃! N, P a N ∧ ¬ P a (N + 1) := by
  classical
  rw [tn_iff_P] at hn
  push Not at hn
  have hex : ∃ N, ¬ P a N := hn
  set N0 := Nat.find hex with hN0
  have hN0spec : ¬ P a N0 := Nat.find_spec hex
  have hN0ne : N0 ≠ 0 := by
    intro h
    rw [h] at hN0spec
    exact hN0spec (P_zero_iff.mpr h0)
  obtain ⟨N, hN⟩ : ∃ N, N0 = N + 1 := ⟨N0 - 1, by omega⟩
  have hPN : P a N := by
    by_contra hc
    have := Nat.find_min' hex hc
    omega
  refine ⟨N, ⟨hPN, hN ▸ hN0spec⟩, ?_⟩
  rintro M ⟨hPM, hnPM⟩
  rcases lt_trichotomy M N with hlt | heq | hgt
  · exact absurd (P_mono (by omega) hPN) hnPM
  · exact heq
  · exact absurd (P_mono (by omega) hPM) (hN ▸ hN0spec)

/-- No nível da primeira falha, falha `Q(N+1)`: há um menor negativo que usa o índice `N + 1`. -/
theorem primeira_falha (h0 : 0 ≤ a 0) (hn : ¬ (toep a).IsTotallyNonneg) :
    ∃ N, P a N ∧ ¬ Q a (N + 1) := by
  obtain ⟨N, ⟨hP, hnP⟩, _⟩ := nivel_unico h0 hn
  exact ⟨N, hP, fun hQ => hnP ((P_succ_iff N).mpr ⟨hP, hQ⟩)⟩

/-! ## O menor `3×3` e o defeito de ordem 2 -/

/-- O menor contíguo `3×3` (linhas `1,2,3`, colunas `0,1,2`): `a₁³ − 2a₀a₁a₂ + a₀²a₃`. -/
theorem menor3 (a : ℕ → ℝ) :
    ((toep a).submatrix ![1, 2, 3] ![0, 1, 2]).det = a 1 ^ 3 - 2 * a 0 * a 1 * a 2 + a 0 ^ 2 * a 3 := by
  rw [Matrix.det_fin_three]
  simp [toep]
  ring

/-- `a₁² − a₀a₂ = (6m₁² − m₀m₂)/24` para `aₙ = mₙ/(2n)!`. -/
theorem defeito_momentos (m : ℕ → ℝ) :
    (m 1 / (Nat.factorial 2 : ℝ)) ^ 2 - m 0 / (Nat.factorial 0 : ℝ) * (m 2 / (Nat.factorial 4 : ℝ)) =
      (6 * m 1 ^ 2 - m 0 * m 2) / 24 := by
  simp [Nat.factorial]
  ring

/-! ## Para `Ξ` -/

open ATK.XiTP (aXi aXi_zero_pos)

theorem rh_iff_P : RiemannHypothesis ↔ ∀ N, P aXi N := ATK.XiCresc.rh_iff_tn.trans tn_iff_P

theorem rh_iff_Q : RiemannHypothesis ↔ ∀ N, Q aXi (N + 1) := by
  constructor
  · intro h N
    exact ((P_succ_iff N).mp (rh_iff_P.mp h (N + 1))).2
  · intro h
    exact ATK.XiCresc.rh_iff_tn.mpr (inducao aXi_zero_pos.le fun N _ => h N)

/-- **`P(1)` é incondicional** para `Ξ`: os menores com índices `≤ 1` são `a₀, a₁, 0, a₀²`. -/
theorem P1_de_pos {a : ℕ → ℝ} (h0 : 0 ≤ a 0) (h1 : 0 ≤ a 1) : P a 1 := by
  intro r I J hI hJ hIN hJN
  have hent : ∀ i j, i ≤ 1 → j ≤ 1 → 0 ≤ toep a i j := by
    intro i j hi hj
    by_cases h : j ≤ i
    · rw [toep_sub h]
      interval_cases i <;> interval_cases j <;> simp_all
    · rw [toep_acima (Nat.lt_of_not_le h)]
  rcases r with _ | _ | _ | r
  · simp
  · rw [Matrix.det_fin_one]; exact hent _ _ (hIN 0) (hJN 0)
  · have hI0 : I 0 = 0 := by
      have := hI (show (0 : Fin 2) < 1 by decide); have := hIN 1; omega
    have hI1 : I 1 = 1 := by
      have := hI (show (0 : Fin 2) < 1 by decide); have := hIN 1; omega
    have hJ0 : J 0 = 0 := by
      have := hJ (show (0 : Fin 2) < 1 by decide); have := hJN 1; omega
    have hJ1 : J 1 = 1 := by
      have := hJ (show (0 : Fin 2) < 1 by decide); have := hJN 1; omega
    rw [Matrix.det_fin_two]
    simp only [submatrix_apply, hI0, hI1, hJ0, hJ1, toep_diag, toep_acima (show 0 < 1 by norm_num)]
    nlinarith
  · exfalso
    have h01 := hI (show (⟨0, by omega⟩ : Fin (r + 3)) < ⟨1, by omega⟩ from Fin.mk_lt_mk.mpr (by omega))
    have h12 := hI (show (⟨1, by omega⟩ : Fin (r + 3)) < ⟨2, by omega⟩ from Fin.mk_lt_mk.mpr (by omega))
    have := hIN ⟨2, by omega⟩
    omega

theorem P1_Xi : P aXi 1 := P1_de_pos (ATK.XiMom.aXi_pos 0).le (ATK.XiMom.aXi_pos 1).le

/-- PF₂ e entradas `≥ 0` ⇒ `P(2)` (o único menor `3×3` com índices `≤ 2` é triangular: `a₀³`). -/
theorem P2_de_pf2 {a : ℕ → ℝ} (hpos : ∀ n, 0 ≤ a n)
    (hpf2 : ∀ I J : Fin 2 → ℕ, StrictMono I → StrictMono J → 0 ≤ ((toep a).submatrix I J).det) :
    P a 2 := by
  intro r I J hI hJ hIN hJN
  have hent : ∀ i j, 0 ≤ toep a i j := by
    intro i j
    by_cases h : j ≤ i
    · rw [toep_sub h]; exact hpos _
    · rw [toep_acima (Nat.lt_of_not_le h)]
  rcases r with _ | _ | _ | _ | r
  · simp
  · rw [Matrix.det_fin_one]; exact hent _ _
  · exact hpf2 I J hI hJ
  · have hI0 : I 0 = 0 := by
      have := hI (show (0 : Fin 3) < 1 by decide); have := hI (show (1 : Fin 3) < 2 by decide)
      have := hIN 2; omega
    have hI1 : I 1 = 1 := by
      have := hI (show (0 : Fin 3) < 1 by decide); have := hI (show (1 : Fin 3) < 2 by decide)
      have := hIN 2; omega
    have hI2 : I 2 = 2 := by
      have := hI (show (0 : Fin 3) < 1 by decide); have := hI (show (1 : Fin 3) < 2 by decide)
      have := hIN 2; omega
    have hJ0 : J 0 = 0 := by
      have := hJ (show (0 : Fin 3) < 1 by decide); have := hJ (show (1 : Fin 3) < 2 by decide)
      have := hJN 2; omega
    have hJ1 : J 1 = 1 := by
      have := hJ (show (0 : Fin 3) < 1 by decide); have := hJ (show (1 : Fin 3) < 2 by decide)
      have := hJN 2; omega
    have hJ2 : J 2 = 2 := by
      have := hJ (show (0 : Fin 3) < 1 by decide); have := hJ (show (1 : Fin 3) < 2 by decide)
      have := hJN 2; omega
    rw [Matrix.det_fin_three]
    simp only [submatrix_apply, hI0, hI1, hI2, hJ0, hJ1, hJ2, toep_diag,
      toep_acima (show 0 < 1 by norm_num), toep_acima (show 0 < 2 by norm_num),
      toep_acima (show 1 < 2 by norm_num)]
    have := hpos 0
    have : 0 ≤ a 0 ^ 3 := by positivity
    nlinarith
  · exfalso
    have h01 := hI (show (⟨0, by omega⟩ : Fin (r + 4)) < ⟨1, by omega⟩ from Fin.mk_lt_mk.mpr (by omega))
    have h12 := hI (show (⟨1, by omega⟩ : Fin (r + 4)) < ⟨2, by omega⟩ from Fin.mk_lt_mk.mpr (by omega))
    have h23 := hI (show (⟨2, by omega⟩ : Fin (r + 4)) < ⟨3, by omega⟩ from Fin.mk_lt_mk.mpr (by omega))
    have := hIN ⟨3, by omega⟩
    omega

/-- O lema de Csordas (BUILD_PENDING): `ψ_Φ = −Φ′/(uΦ)` crescente em `(0, ∞)`. -/
def Csordas : Prop :=
  MonotoneOn (fun u => -ATK.TuranDisp.Phid u / (u * ATK.XiPhi.Phi u)) (Ioi 0)

/-- **`P(2)` para `Ξ`, sob o lema de Csordas.** -/
theorem P2_Xi_de_csordas (hψ : Csordas) : P aXi 2 :=
  P2_de_pf2 (fun n => (ATK.XiMom.aXi_pos n).le) (ATK.TuranDisp.pf2_de_csordas hψ)

/-- **Um zero fora da reta tem um nível de falha único `N ≥ 1`.** -/
theorem nivel_de_zero_fora (h : ¬ RiemannHypothesis) :
    ∃! N, P aXi N ∧ ¬ P aXi (N + 1) := by
  rw [ATK.XiCresc.rh_iff_tn] at h
  exact nivel_unico aXi_zero_pos.le h

theorem nivel_ge_um {N : ℕ} (h : P aXi N ∧ ¬ P aXi (N + 1)) : 1 ≤ N := by
  by_contra h0
  have : N = 0 := by omega
  subst this
  exact h.2 P1_Xi

theorem nivel_ge_dois_de_csordas (hψ : Csordas) {N : ℕ} (h : P aXi N ∧ ¬ P aXi (N + 1)) : 2 ≤ N := by
  by_contra h0
  have := nivel_ge_um h
  have : N = 1 := by omega
  subst this
  exact h.2 (P2_Xi_de_csordas hψ)

/-- **Sob Csordas, um zero fora da reta força um menor de Toeplitz negativo de ordem `≥ 3`.** -/
theorem ordem_ge_tres_de_csordas (hψ : Csordas) (h : ¬ RiemannHypothesis) :
    ∃ r, 3 ≤ r ∧ ∃ I J : Fin r → ℕ, StrictMono I ∧ StrictMono J ∧
      ((toep aXi).submatrix I J).det < 0 := by
  rw [ATK.XiCresc.rh_iff_tn] at h
  unfold Matrix.IsTotallyNonneg at h
  push Not at h
  obtain ⟨r, I, J, hI, hJ, hneg⟩ := h
  refine ⟨r, ?_, I, J, hI, hJ, hneg⟩
  by_contra hr
  rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
  · rw [Matrix.det_isEmpty] at hneg; linarith
  · rw [Matrix.det_fin_one] at hneg
    simp only [submatrix_apply] at hneg
    by_cases hji : J 0 ≤ I 0
    · rw [toep_sub hji] at hneg; linarith [ATK.XiMom.aXi_pos (I 0 - J 0)]
    · rw [toep_acima (Nat.lt_of_not_le hji)] at hneg; linarith
  · linarith [ATK.TuranDisp.pf2_de_csordas hψ I J hI hJ]

/-! ## O fluxo `bₙ(τ) = aₙ e^{−τn(n−1)}` -/

noncomputable def fluxo (a : ℕ → ℝ) (τ : ℝ) (n : ℕ) : ℝ :=
  a n * Real.exp (-τ * n * ((n : ℝ) - 1))

/-- Defeito de ordem 2: `a_{n+1}² − aₙ a_{n+2}`. -/
def D2 (a : ℕ → ℝ) (n : ℕ) : ℝ := a (n + 1) ^ 2 - a n * a (n + 2)

theorem fluxo_zero (a : ℕ → ℝ) : fluxo a 0 = a := by
  funext n; simp [fluxo]

/-- **`D₂(b(τ))ₙ = e^{−2τ(n+1)n}·(a_{n+1}² − e^{−2τ}aₙa_{n+2})`.** -/
theorem D2_fluxo (a : ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    D2 (fluxo a τ) n = Real.exp (-2 * τ * ((n : ℝ) + 1) * n) *
      (a (n + 1) ^ 2 - Real.exp (-2 * τ) * (a n * a (n + 2))) := by
  unfold D2 fluxo
  push_cast
  have e1 : Real.exp (-τ * ((n : ℝ) + 1) * ((n : ℝ) + 1 - 1)) ^ 2 =
      Real.exp (-2 * τ * ((n : ℝ) + 1) * n) := by
    rw [sq, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (-τ * (n : ℝ) * ((n : ℝ) - 1)) * Real.exp (-τ * ((n : ℝ) + 2) * ((n : ℝ) + 2 - 1)) =
      Real.exp (-2 * τ * ((n : ℝ) + 1) * n) * Real.exp (-2 * τ) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  calc (a (n + 1) * Real.exp (-τ * ((n : ℝ) + 1) * ((n : ℝ) + 1 - 1))) ^ 2 -
        a n * Real.exp (-τ * (n : ℝ) * ((n : ℝ) - 1)) *
          (a (n + 2) * Real.exp (-τ * ((n : ℝ) + 2) * ((n : ℝ) + 2 - 1)))
      = a (n + 1) ^ 2 * Real.exp (-τ * ((n : ℝ) + 1) * ((n : ℝ) + 1 - 1)) ^ 2 -
          a n * a (n + 2) * (Real.exp (-τ * (n : ℝ) * ((n : ℝ) - 1)) *
            Real.exp (-τ * ((n : ℝ) + 2) * ((n : ℝ) + 2 - 1))) := by ring
    _ = _ := by rw [e1, e2]; ring

/-- O defeito normalizado cresce com `τ` quando `aₙa_{n+2} ≥ 0`. -/
theorem defeito_monotono {a : ℕ → ℝ} {n : ℕ} (hp : 0 ≤ a n * a (n + 2)) {τ τ' : ℝ} (h : τ ≤ τ') :
    a (n + 1) ^ 2 - Real.exp (-2 * τ) * (a n * a (n + 2)) ≤
      a (n + 1) ^ 2 - Real.exp (-2 * τ') * (a n * a (n + 2)) := by
  have : Real.exp (-2 * τ') ≤ Real.exp (-2 * τ) := Real.exp_le_exp.mpr (by linarith)
  nlinarith

/-- **Volta válida**: `D₂ ≥ 0` para **todo** `τ > 0` ⇒ `D₂ ≥ 0` em `τ = 0`. -/
theorem volta_valida {a : ℕ → ℝ} {n : ℕ} (h : ∀ τ > 0, 0 ≤ D2 (fluxo a τ) n) : 0 ≤ D2 a n := by
  have hb : ∀ τ > 0, Real.exp (-2 * τ) * (a n * a (n + 2)) ≤ a (n + 1) ^ 2 := by
    intro τ hτ
    have := h τ hτ
    rw [D2_fluxo] at this
    have hpos := Real.exp_pos (-2 * τ * ((n : ℝ) + 1) * n)
    have := (mul_nonneg_iff_of_pos_left hpos).mp this
    linarith
  have ht : Tendsto (fun τ : ℝ => Real.exp (-2 * τ) * (a n * a (n + 2))) (𝓝[>] 0)
      (𝓝 (Real.exp (-2 * 0) * (a n * a (n + 2)))) := by
    refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul continuous_const).tendsto 0
  have hle : Real.exp (-2 * 0) * (a n * a (n + 2)) ≤ a (n + 1) ^ 2 :=
    le_of_tendsto ht (eventually_nhdsWithin_of_forall fun τ hτ => hb τ hτ)
  simp at hle
  unfold D2
  linarith

/-- **Volta válida para TN inteira**: `T(b(τ))` TN para todo `τ > 0` ⇒ `T(a)` TN. -/
theorem volta_valida_tn {a : ℕ → ℝ} (h : ∀ τ > 0, (toep (fluxo a τ)).IsTotallyNonneg) :
    (toep a).IsTotallyNonneg := by
  have hτ : ∀ N : ℕ, (0 : ℝ) < 1 / ((N : ℝ) + 1) := fun N => by positivity
  refine ATK.Edrei.tn_closed (A := fun N => toep (fluxo a (1 / ((N : ℝ) + 1)))) (fun N => h _ (hτ N))
    fun i j => ?_
  simp only [toep]
  split_ifs
  · have hc : Continuous fun τ : ℝ => fluxo a τ (i - j) := by
      unfold fluxo; fun_prop
    have := (hc.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    rw [fluxo_zero] at this
    exact this
  · exact tendsto_const_nhds

/-- **Volta ingênua inválida**: com `a = (1, 1, 2, 1, …)`, `D₂(b(1))₀ > 0` mas `D₂(a)₀ = −1`. -/
theorem volta_ingenua_invalida :
    ∃ a : ℕ → ℝ, 0 < D2 (fluxo a 1) 0 ∧ D2 a 0 < 0 := by
  refine ⟨fun n => if n = 2 then 2 else 1, ?_, ?_⟩
  · rw [D2_fluxo]
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, one_mul]
    norm_num
    have h2 : (2 : ℝ) < Real.exp 2 := by
      have := Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num); linarith
    have : Real.exp (-2) = (Real.exp 2)⁻¹ := by rw [Real.exp_neg]
    rw [this]
    have hp := Real.exp_pos 2
    rw [inv_mul_lt_iff₀ hp]
    linarith
  · unfold D2; norm_num

end ATK.TruncToep

#print axioms ATK.TruncToep.P_mono
#print axioms ATK.TruncToep.P_succ_iff
#print axioms ATK.TruncToep.P_iff_trunc
#print axioms ATK.TruncToep.tn_iff_P
#print axioms ATK.TruncToep.toep_diag
#print axioms ATK.TruncToep.toep_sub
#print axioms ATK.TruncToep.toep_acima
#print axioms ATK.TruncToep.P_zero_iff
#print axioms ATK.TruncToep.inducao
#print axioms ATK.TruncToep.nivel_unico
#print axioms ATK.TruncToep.primeira_falha
#print axioms ATK.TruncToep.menor3
#print axioms ATK.TruncToep.defeito_momentos
#print axioms ATK.TruncToep.rh_iff_P
#print axioms ATK.TruncToep.rh_iff_Q
#print axioms ATK.TruncToep.P1_de_pos
#print axioms ATK.TruncToep.P1_Xi
#print axioms ATK.TruncToep.P2_de_pf2
#print axioms ATK.TruncToep.P2_Xi_de_csordas
#print axioms ATK.TruncToep.nivel_de_zero_fora
#print axioms ATK.TruncToep.nivel_ge_um
#print axioms ATK.TruncToep.nivel_ge_dois_de_csordas
#print axioms ATK.TruncToep.ordem_ge_tres_de_csordas
#print axioms ATK.TruncToep.fluxo_zero
#print axioms ATK.TruncToep.D2_fluxo
#print axioms ATK.TruncToep.defeito_monotono
#print axioms ATK.TruncToep.volta_valida
#print axioms ATK.TruncToep.volta_valida_tn
#print axioms ATK.TruncToep.volta_ingenua_invalida
