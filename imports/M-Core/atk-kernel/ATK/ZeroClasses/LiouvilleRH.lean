import ATK.ZeroClasses.TetaExpoente

/-!
# A função de Liouville: `Σ λ(n)n^{−s} = ζ(2s)/ζ(s)`, `Θ`, RH e a conjectura de Pólya (rodada 99)

Com `λ(n) = (−1)^{Ω(n)}` (`ArithmeticFunction.liouville` da Mathlib) e `L(N) = Σ_{n ≤ N} λ(n)` (`Lv`):

* §1 **`LSeries_lam_mul_zeta`**: `L(λ, s) ζ(s) = ζ(2s)` em `Re s > 1`, pelos produtos de Euler. `λ` é completamente
  multiplicativa com `λ(p) = −1`, e `(1 + p^{−s})⁻¹(1 − p^{−s})⁻¹ = (1 − p^{−2s})⁻¹`.
* §2–3 **Landau**: `GA L(s) = ζ(2s)F(s)` (`GA_Lv_eq`, `F = 1/ζ`), holomorfa no disco `|s − 2| < 2 − θ` para
  `θ ≥ ½`. Uma cota de um lado `L(N) ≤ A(N + 1)^θ + K` (ou `≥ −…`) dá `ζ ≠ 0` em `Re s > θ`
  (`semZeros_of_liouville_le`, `_ge`): divide-se a extensão por `ζ(2s)`, que não se anula em `Re s > ½`.
* §4 **RH e Pólya**:
  * `rh_of_liouville_le`, `_ge`: um lado de `L(x) = O(x^{½+ε})` já dá RH;
  * `rh_of_liouville_limitada_cima`, `_baixo`: `L` limitada de um lado dá RH;
  * **`rh_of_polya`**: `L(N) ≤ 0` para `N ≥ 2` (a conjectura de Pólya, falsa: Haselgrove 1958) implicaria RH;
  * `liouville_omega_mais`, `_menos`: `L(x) = Ω±(x^θ)` para `½ ≤ θ < Θ`.
* §5–6 **A recíproca** (`liouville_of_semZeros`, pela soma de Perron genérica da rodada 57 e `‖ζ(2v)‖ ≤ ζ(1 + ε/2)`):
  * **`semZeros_iff_liouville`**;
  * `Teta_le_iff_liouville_le`, `_ge`;
  * **`rh_iff_liouville`**: RH ⟺ `L(x) = O(x^{½+ε})`, e o mesmo de um lado só (`rh_iff_liouville_le`, `_ge`).
* §7 **Abaixo de `½`, sem hipóteses** (`liouville_nao_O`, `liouville_omega_abs`): `L(x) ≠ O(x^θ)` para `θ < ½`. Se
  valesse, `(2s − 1)L(λ, s) = ζ₁(2s)F(s)` no disco `|s − 2| < 2` (identidade analítica). Em `s = ½` o lado esquerdo
  é `0` e o direito é `ζ₁(1)F(½) ≠ 0`.
* §8 **`Teta_eq_liouville`**: `Θ = inf{θ : |L(N)| ≤ N^θ para N grande}`, e `rh_iff_expoente_liouville`.

Classificação: **reformulação** (RH e `Θ` pela função de Liouville; Landau, Pólya 1919 — tudo clássico, aqui
formalizado) e **consequência** (`Ω(x^θ)` para `θ < ½`). Os lados de cima/baixo de `L` separadamente, abaixo de `½`,
não estão aqui: o de cima é a questão de Pólya, e não decorre só do polo. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.LiouvilleRH

open ATK.ZeroClasses.QuasiRH (SemZeros)
open ATK.RHLogZeta (F F_eq)

/-! ## 1. A série de Dirichlet de `λ` -/

/-- `λ(n)` como número complexo. -/
noncomputable def lam (n : ℕ) : ℂ := (ArithmeticFunction.liouville n : ℂ)

theorem norm_lam_le (n : ℕ) : ‖lam n‖ ≤ 1 := by
  unfold lam
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [ArithmeticFunction.liouville_apply hn]
    push_cast
    simp

theorem lam_prime {p : ℕ} (hp : p.Prime) : lam p = -1 := by
  unfold lam
  rw [ArithmeticFunction.liouville_apply hp.ne_zero, ArithmeticFunction.cardFactors_apply_prime hp]
  push_cast
  ring

/-- `n ↦ λ(n) n^{−s}` é completamente multiplicativa (`s ≠ 0`). -/
noncomputable def lamHom {s : ℂ} (hs : s ≠ 0) : ℕ →*₀ ℂ where
  toFun n := lam n * (n : ℂ) ^ (-s)
  map_zero' := by simp [lam, hs]
  map_one' := by simp [lam, ArithmeticFunction.liouville_apply_one]
  map_mul' m n := by
    simp only [lam, ArithmeticFunction.liouville_apply_mul, Int.cast_mul, Nat.cast_mul]
    rw [show ((m : ℂ) * (n : ℂ)) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) by
      simpa only [ofReal_natCast] using mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg (-s)]
    ring

theorem summable_lamHom {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n => ‖lamHom (ne_zero_of_one_lt_re hs) n‖) := by
  refine (summable_riemannZetaSummand hs).of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  simp only [lamHom, riemannZetaSummandHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_lam_le n)

theorem tsum_lamHom {s : ℂ} (hs : 1 < s.re) :
    ∑' n, lamHom (ne_zero_of_one_lt_re hs) n = LSeries lam s := by
  simp only [lamHom, cpow_neg, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, LSeries,
    LSeries.term_of_ne_zero' (ne_zero_of_one_lt_re hs), div_eq_mul_inv]

/-- **`L(λ, s) ζ(s) = ζ(2s)`** para `Re s > 1`, pelos produtos de Euler. -/
theorem LSeries_lam_mul_zeta {s : ℂ} (hs : 1 < s.re) :
    LSeries lam s * riemannZeta s = riemannZeta (2 * s) := by
  have h2s : 1 < (2 * s).re := by simp; linarith
  have h1 := EulerProduct.eulerProduct_completely_multiplicative_hasProd (summable_lamHom hs)
  rw [tsum_lamHom hs] at h1
  have h2 := riemannZeta_eulerProduct_hasProd hs
  have h3 := riemannZeta_eulerProduct_hasProd h2s
  have h12 := h1.mul h2
  refine h12.unique ?_
  convert h3 using 1
  funext p
  simp only [lamHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, lam_prime p.prop]
  rw [show -(2 * s) = (2 : ℕ) * (-s) by push_cast; ring, cpow_nat_mul, ← mul_inv]
  congr 1
  ring

theorem LSeriesSummable_lam {s : ℂ} (hs : 1 < s.re) : LSeriesSummable lam s :=
  LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_lam_le n) hs

/-- **`L(λ, s) = ζ(2s)/ζ(s)`**, na forma `ζ(2s) F(s)` com `F = 1/ζ`. -/
theorem LSeries_lam {s : ℂ} (hs : 1 < s.re) : LSeries lam s = riemannZeta (2 * s) * F s := by
  have hs1 : s ≠ 1 := fun h => by rw [h, one_re] at hs; exact lt_irrefl 1 hs
  have hz := riemannZeta_ne_zero_of_one_lt_re hs
  rw [F_eq hs1, ← LSeries_lam_mul_zeta hs]
  field_simp

/-! ## 2. A soma `L(N) = Σ_{n ≤ N} λ(n)` -/

open ATK.ZeroClasses.VonKoch (GA)

/-- `L(N) = Σ_{n ≤ N} λ(n)` (a função somatória de Liouville). -/
noncomputable def Lv (N : ℕ) : ℝ := ∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.liouville n : ℝ)

theorem abs_liouville_le (n : ℕ) : |(ArithmeticFunction.liouville n : ℝ)| ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [ArithmeticFunction.liouville_apply hn]
    push_cast
    simp

theorem abs_Lv_le (N : ℕ) : |Lv N| ≤ N + 1 := by
  unfold Lv
  calc |∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.liouville n : ℝ)|
      ≤ ∑ n ∈ Finset.range (N + 1), |(ArithmeticFunction.liouville n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range (N + 1), (1 : ℝ) := Finset.sum_le_sum fun n _ => abs_liouville_le n
    _ = N + 1 := by simp

theorem Lv_zero : Lv 0 = 0 := by simp [Lv]

theorem Lv_one : Lv 1 = 1 := by simp [Lv, Finset.sum_range_succ, ArithmeticFunction.liouville_apply_one]

theorem Lv_succ_eq (n : ℕ) : ((Lv (n + 1) : ℝ) : ℂ) = ∑ k ∈ Finset.range (n + 1), lam (k + 1) := by
  unfold Lv lam
  rw [Finset.sum_range_succ']
  push_cast
  simp

theorem GA_Lv_eq {s : ℂ} (hs : 1 < s.re) : GA Lv s = riemannZeta (2 * s) * F s := by
  rw [ATK.ZeroClasses.Unilateral.GA_eq_LSeries' (θ := 1) (C := 1) zero_le_one
    (fun N => by rw [Real.rpow_one, one_mul]; exact abs_Lv_le N) Lv_succ_eq hs (LSeriesSummable_lam hs),
    LSeries_lam hs]

/-! ## 3. Landau: um lado de `L(x)` dá `ζ ≠ 0` -/

theorem re_gt_of_mem_ball {θ : ℝ} {s : ℂ} (hs : s ∈ ball (2 : ℂ) (2 - θ)) : θ < s.re := by
  rw [mem_ball, dist_eq_norm] at hs
  have h := Complex.abs_re_le_norm (s - 2)
  simp only [sub_re, re_ofNat] at h
  have := neg_abs_le (s.re - 2)
  linarith

theorem differentiableAt_zeta_dois {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fun s => riemannZeta (2 * s)) s := by
  have h2s : 2 * s ≠ 1 := fun h => by
    have := congrArg re h
    simp at this
    linarith
  exact (differentiableAt_riemannZeta h2s).comp s (differentiableAt_id.const_mul 2)

theorem zeta_dois_ne_zero {s : ℂ} (hs : 1 / 2 < s.re) : riemannZeta (2 * s) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)

theorem differentiableOn_H {θ : ℝ} (hθ : 1 / 2 ≤ θ) :
    DifferentiableOn ℂ (fun s => riemannZeta (2 * s) * F s) (ball (2 : ℂ) (2 - θ)) := by
  intro s hs
  have hre := re_gt_of_mem_ball hs
  exact ((differentiableAt_zeta_dois (by linarith)).mul
    ((ATK.ZeroClasses.Unilateral.differentiableOn_F (by linarith) s hs).differentiableAt
      (isOpen_ball.mem_nhds hs))).differentiableWithinAt

/-- Uma extensão holomorfa de `ζ(2s)/ζ(s)` a `Re s > θ ≥ ½` dá `ζ ≠ 0` em `Re s > θ`. -/
theorem semZeros_of_ext_liouville {θ : ℝ} (hθ : 1 / 2 ≤ θ) {G : ℂ → ℂ}
    (hG : ∀ s : ℂ, θ < s.re → DifferentiableAt ℂ G s)
    (hGE : ∀ s : ℂ, 1 < s.re → G s = riemannZeta (2 * s) * F s) : SemZeros θ := by
  refine ATK.ZeroClasses.Unilateral.semZeros_of_ext_mertens (G := fun s => G s / riemannZeta (2 * s))
    (fun s hs => (hG s hs).div (differentiableAt_zeta_dois (by linarith)) (zeta_dois_ne_zero (by linarith)))
    fun s hs => ?_
  rw [hGE s hs]
  field_simp [zeta_dois_ne_zero (show 1 / 2 < s.re by linarith)]

/-- **`L(N) ≤ A(N + 1)^θ + K` ⟹ `ζ ≠ 0` em `Re s > θ`** (`½ ≤ θ < 1`). -/
theorem semZeros_of_liouville_le {θ A K : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ N : ℕ, Lv N ≤ A * ((N : ℝ) + 1) ^ θ + K) : SemZeros θ := by
  obtain ⟨G, hG, hGA⟩ := ATK.ZeroClasses.Unilateral.extensao (a := Lv) (C := 1) (by linarith) hθ1
    (fun N => by rw [one_mul]; exact abs_Lv_le N) h (differentiableOn_H hθ) (fun s hs => GA_Lv_eq hs)
  exact semZeros_of_ext_liouville hθ hG fun s hs => (hGA s hs).trans (GA_Lv_eq hs)

/-- **`L(N) ≥ −A(N + 1)^θ − K` ⟹ `ζ ≠ 0` em `Re s > θ`** (`½ ≤ θ < 1`). -/
theorem semZeros_of_liouville_ge {θ A K : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1)
    (h : ∀ N : ℕ, -(A * ((N : ℝ) + 1) ^ θ) - K ≤ Lv N) : SemZeros θ := by
  obtain ⟨G, hG, hGA⟩ := ATK.ZeroClasses.Unilateral.extensao (a := fun N => -Lv N) (C := 1) (A := A) (K := K)
    (by linarith) hθ1 (fun N => by rw [abs_neg, one_mul]; exact abs_Lv_le N) (fun N => by have := h N; linarith)
    (H := fun s => -(riemannZeta (2 * s) * F s)) (differentiableOn_H hθ).neg
    (fun s hs => by rw [ATK.ZeroClasses.Unilateral.GA_neg, GA_Lv_eq hs])
  refine semZeros_of_ext_liouville hθ (G := fun s => -G s) (fun s hs => (hG s hs).neg) fun s hs => ?_
  rw [hGA s hs, ATK.ZeroClasses.Unilateral.GA_neg, GA_Lv_eq hs, neg_neg]

/-! ## 4. `Θ`, RH e a conjectura de Pólya -/

open ATK.ZeroClasses.BDTheta (Teta Teta_le_um)

/-- **`L(x) ≤ A x^{θ+ε} + K` para todo `ε > 0` ⟹ `Θ ≤ θ`** (`½ ≤ θ`). -/
theorem Teta_le_of_liouville_le {θ : ℝ} (hθ : 1 / 2 ≤ θ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ A K : ℝ, ∀ N : ℕ, Lv N ≤ A * ((N : ℝ) + 1) ^ (θ + ε) + K) : Teta ≤ θ :=
  ATK.ZeroClasses.Unilateral.Teta_le_of_unilateral hθ fun ε hε h1 => by
    obtain ⟨A, K, hAK⟩ := h ε hε
    exact semZeros_of_liouville_le (by linarith) h1 hAK

/-- **`L(x) ≥ −A x^{θ+ε} − K` para todo `ε > 0` ⟹ `Θ ≤ θ`** (`½ ≤ θ`). -/
theorem Teta_le_of_liouville_ge {θ : ℝ} (hθ : 1 / 2 ≤ θ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ A K : ℝ, ∀ N : ℕ, -(A * ((N : ℝ) + 1) ^ (θ + ε)) - K ≤ Lv N) : Teta ≤ θ :=
  ATK.ZeroClasses.Unilateral.Teta_le_of_unilateral hθ fun ε hε h1 => by
    obtain ⟨A, K, hAK⟩ := h ε hε
    exact semZeros_of_liouville_ge (by linarith) h1 hAK

/-- **`L(x) ≤ A x^{½+ε} + K` para todo `ε > 0` ⟹ RH.** -/
theorem rh_of_liouville_le
    (h : ∀ ε : ℝ, 0 < ε → ∃ A K : ℝ, ∀ N : ℕ, Lv N ≤ A * ((N : ℝ) + 1) ^ (1 / 2 + ε) + K) :
    RiemannHypothesis :=
  ATK.ZeroClasses.PiUnilateral.rh_iff_Teta_le.mpr (Teta_le_of_liouville_le le_rfl h)

/-- **`L(x) ≥ −A x^{½+ε} − K` para todo `ε > 0` ⟹ RH.** -/
theorem rh_of_liouville_ge
    (h : ∀ ε : ℝ, 0 < ε → ∃ A K : ℝ, ∀ N : ℕ, -(A * ((N : ℝ) + 1) ^ (1 / 2 + ε)) - K ≤ Lv N) :
    RiemannHypothesis :=
  ATK.ZeroClasses.PiUnilateral.rh_iff_Teta_le.mpr (Teta_le_of_liouville_ge le_rfl h)

/-- **`L(N)` limitada por cima ⟹ RH.** -/
theorem rh_of_liouville_limitada_cima (h : ∃ K : ℝ, ∀ N : ℕ, Lv N ≤ K) : RiemannHypothesis := by
  obtain ⟨K, hK⟩ := h
  exact rh_of_liouville_le fun _ _ => ⟨0, K, fun N => by rw [zero_mul, zero_add]; exact hK N⟩

/-- **`L(N)` limitada por baixo ⟹ RH.** -/
theorem rh_of_liouville_limitada_baixo (h : ∃ K : ℝ, ∀ N : ℕ, -K ≤ Lv N) : RiemannHypothesis := by
  obtain ⟨K, hK⟩ := h
  exact rh_of_liouville_ge fun _ _ => ⟨0, K, fun N => by rw [zero_mul, neg_zero, zero_sub]; exact hK N⟩

/-- **A conjectura de Pólya implica RH** (Pólya 1919): se `L(N) ≤ 0` para todo `N ≥ 2`, vale RH. (A conjectura é
falsa — Haselgrove 1958; o primeiro contraexemplo é `N = 906 150 257`, Tanaka 1980 —, mas a implicação é o teorema.) -/
theorem rh_of_polya (h : ∀ N : ℕ, 2 ≤ N → Lv N ≤ 0) : RiemannHypothesis := by
  refine rh_of_liouville_limitada_cima ⟨1, fun N => ?_⟩
  rcases lt_or_ge N 2 with hN | hN
  · interval_cases N
    · rw [Lv_zero]; norm_num
    · rw [Lv_one]
  · linarith [h N hN]

/-- **`L(x) = Ω₊(x^θ)` para `½ ≤ θ < Θ`**. -/
theorem liouville_omega_mais {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hlt : θ < Teta) (A K : ℝ) :
    ∃ N : ℕ, A * ((N : ℝ) + 1) ^ θ + K < Lv N := by
  by_contra hne
  push Not at hne
  exact ATK.ZeroClasses.Unilateral.nao_semZeros hlt
    (semZeros_of_liouville_le hθ (hlt.trans_le Teta_le_um) hne)

/-- **`L(x) = Ω₋(x^θ)` para `½ ≤ θ < Θ`**. -/
theorem liouville_omega_menos {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hlt : θ < Teta) (A K : ℝ) :
    ∃ N : ℕ, Lv N < -(A * ((N : ℝ) + 1) ^ θ) - K := by
  by_contra hne
  push Not at hne
  exact ATK.ZeroClasses.Unilateral.nao_semZeros hlt
    (semZeros_of_liouville_ge hθ (hlt.trans_le Teta_le_um) hne)

/-! ## 5. A recíproca: `ζ ≠ 0` em `Re s > θ` ⟹ `L(x) = O(x^{θ+ε})` -/

/-- `‖ζ(w)‖ ≤ Σ (n + 1)^{−σ₀}` em `Re w ≥ σ₀ > 1`, uniformemente. -/
theorem norm_zeta_le_unif {σ₀ : ℝ} (h1 : 1 < σ₀) {w : ℂ} (hw : σ₀ ≤ w.re) :
    ‖riemannZeta w‖ ≤ ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ σ₀)⁻¹ := by
  have hs : Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ σ₀)⁻¹ :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr h1)
  have hterm : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ w‖ ≤ (((n + 1 : ℕ) : ℝ) ^ σ₀)⁻¹ := by
    intro n
    have e : (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e, norm_div, norm_one, norm_natCast_cpow_of_pos (Nat.succ_pos n), one_div]
    have hb : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow_of_exponent_le hb hw)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by linarith)]
  have hsn : Summable fun n : ℕ => ‖1 / ((n : ℂ) + 1) ^ w‖ :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hterm hs)

theorem Lv_eq_sum (σ : ℝ) (N : ℕ) :
    ((Lv N : ℝ) : ℂ) = ∑ n ∈ Finset.range (N + 1), LSeries.term lam (σ : ℂ) n * (((n : ℝ) ^ σ : ℝ) : ℂ) := by
  unfold Lv
  push_cast
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [ATK.ZeroClasses.VonKochRH.term_mul_rpow lam σ hn]
    rfl

/-- **`ζ ≠ 0` em `Re s > θ` ⟹ `L(N) = O((N + 1)^{θ+ε})`** (`½ ≤ θ < 1`). -/
theorem liouville_of_semZeros {θ : ℝ} (hZ : SemZeros θ) (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |Lv N| ≤ C * ((N : ℝ) + 1) ^ (θ + ε) := by
  refine ATK.ZeroClasses.QuasiRH.reduz fun ε hε hε1 => ?_
  obtain ⟨CF, hCF0, hCF⟩ := ATK.ZeroClasses.QuasiRH.norm_F_le hZ hθ hθ1 (δ := ε / 4) (η := ε / 2 / 16)
    (by linarith) (by linarith) (by linarith)
  set Z := ∑' n : ℕ, (((n + 1 : ℕ) : ℝ) ^ (1 + ε / 2))⁻¹ with hZdef
  have hZ0 : 0 ≤ Z := tsum_nonneg fun _ => by positivity
  have hZb : ∀ v : ℂ, θ + ε / 4 ≤ v.re → ‖riemannZeta (2 * v)‖ ≤ Z := fun v hv =>
    norm_zeta_le_unif (by linarith) (by simp; linarith)
  have hΦd : ∀ v : ℂ, θ < v.re → DifferentiableAt ℂ (fun v => riemannZeta (2 * v) * F v) v := fun v hv =>
    (differentiableAt_zeta_dois (by linarith)).mul (ATK.ZeroClasses.QuasiRH.differentiableAt_F hZ hv)
  have hΦL : ∀ v : ℂ, 1 < v.re → LSeries lam v = (fun v => riemannZeta (2 * v) * F v) v := fun v hv =>
    LSeries_lam hv
  obtain ⟨B, hB⟩ := ATK.ZeroClasses.QuasiRH.somas_limitadas_gen norm_lam_le
    (Φ := fun v => riemannZeta (2 * v) * F v) (θ := θ) (ε := ε / 2) (δ := ε / 4) (CF := Z * CF) hθ
    (by linarith) (by linarith) (by linarith) hΦd hΦL (mul_nonneg hZ0 hCF0.le) (fun v hv => by
      rw [norm_mul, mul_assoc]
      exact mul_le_mul (hZb v (by linarith)) (hCF v (by linarith)) (norm_nonneg _) hZ0)
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = θ + ε / 2 + ε / 4 := ⟨_, rfl⟩
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  have hBσ : ∀ N : ℕ, ‖∑ n ∈ Finset.range (N + 1), LSeries.term lam (σ : ℂ) n‖ ≤ B := by
    intro N; rw [hσ]; exact hB N
  refine ⟨2 * B, fun N => ?_⟩
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hBσ 0)
  have hn := congrArg norm (Lv_eq_sum σ N)
  rw [Complex.norm_real, Real.norm_eq_abs] at hn
  have h1 : |Lv N| ≤ 2 * B * (N : ℝ) ^ σ := by
    rw [hn]; exact ATK.ZeroClasses.VonKochRH.abel_cota hσ0 hBσ N
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have hN0 := (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  calc (N : ℝ) ^ σ ≤ ((N : ℝ) + 1) ^ σ := Real.rpow_le_rpow hN0 (by linarith) hσ0.le
    _ ≤ ((N : ℝ) + 1) ^ (θ + ε) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by rw [hσ]; linarith)

/-! ## 6. As equivalências -/

open ATK.ZeroClasses.BDTheta (Teta_le_iff)

/-- **`ζ ≠ 0` em `Re s > θ` ⟺ `L(x) = O(x^{θ+ε})` para todo `ε > 0`** (`½ ≤ θ < 1`). -/
theorem semZeros_iff_liouville {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    SemZeros θ ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |Lv N| ≤ C * ((N : ℝ) + 1) ^ (θ + ε) := by
  refine ⟨fun hZ => liouville_of_semZeros hZ hθ hθ1, fun h => ?_⟩
  refine (Teta_le_iff hθ).mp (Teta_le_of_liouville_le hθ fun ε hε => ?_)
  obtain ⟨C, hC⟩ := h ε hε
  exact ⟨C, 0, fun N => by rw [add_zero]; exact (le_abs_self _).trans (hC N)⟩

/-- **`Θ ≤ θ` ⟺ `L(x) ≤ A x^{θ+ε} + K`** para todo `ε > 0` (`½ ≤ θ < 1`). -/
theorem Teta_le_iff_liouville_le {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    Teta ≤ θ ↔ ∀ ε : ℝ, 0 < ε → ∃ A K : ℝ, ∀ N : ℕ, Lv N ≤ A * ((N : ℝ) + 1) ^ (θ + ε) + K := by
  refine ⟨fun hT ε hε => ?_, Teta_le_of_liouville_le hθ⟩
  obtain ⟨C, hC⟩ := liouville_of_semZeros ((Teta_le_iff hθ).mp hT) hθ hθ1 ε hε
  exact ⟨C, 0, fun N => by rw [add_zero]; exact (le_abs_self _).trans (hC N)⟩

/-- **`Θ ≤ θ` ⟺ `L(x) ≥ −A x^{θ+ε} − K`** para todo `ε > 0` (`½ ≤ θ < 1`). -/
theorem Teta_le_iff_liouville_ge {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    Teta ≤ θ ↔ ∀ ε : ℝ, 0 < ε → ∃ A K : ℝ, ∀ N : ℕ, -(A * ((N : ℝ) + 1) ^ (θ + ε)) - K ≤ Lv N := by
  refine ⟨fun hT ε hε => ?_, Teta_le_of_liouville_ge hθ⟩
  obtain ⟨C, hC⟩ := liouville_of_semZeros ((Teta_le_iff hθ).mp hT) hθ hθ1 ε hε
  exact ⟨C, 0, fun N => by rw [sub_zero]; exact neg_le_of_abs_le (hC N)⟩

/-- **RH ⟺ `L(x) = O(x^{½+ε})`** para todo `ε > 0`. -/
theorem rh_iff_liouville : RiemannHypothesis ↔
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, |Lv N| ≤ C * ((N : ℝ) + 1) ^ (1 / 2 + ε) :=
  ATK.ZeroClasses.QuasiRH.semZeros_meio_iff.symm.trans (semZeros_iff_liouville le_rfl (by norm_num))

/-- **RH ⟺ `L(x) ≤ A x^{½+ε} + K`** para todo `ε > 0` (um lado só). -/
theorem rh_iff_liouville_le : RiemannHypothesis ↔
    ∀ ε : ℝ, 0 < ε → ∃ A K : ℝ, ∀ N : ℕ, Lv N ≤ A * ((N : ℝ) + 1) ^ (1 / 2 + ε) + K :=
  ATK.ZeroClasses.PiUnilateral.rh_iff_Teta_le.trans (Teta_le_iff_liouville_le le_rfl (by norm_num))

/-- **RH ⟺ `L(x) ≥ −A x^{½+ε} − K`** para todo `ε > 0` (um lado só). -/
theorem rh_iff_liouville_ge : RiemannHypothesis ↔
    ∀ ε : ℝ, 0 < ε → ∃ A K : ℝ, ∀ N : ℕ, -(A * ((N : ℝ) + 1) ^ (1 / 2 + ε)) - K ≤ Lv N :=
  ATK.ZeroClasses.PiUnilateral.rh_iff_Teta_le.trans (Teta_le_iff_liouville_ge le_rfl (by norm_num))

/-! ## 7. Abaixo de `½`: o polo de `ζ(2s)` em `s = ½` -/

open ATK.RHLogZeta (zeta₁_eq)

/-- **`L(x) ≠ O(x^θ)` para `0 ≤ θ < ½`, sem hipóteses**: se `|L(N)| ≤ C(N + 1)^θ`, a série `Σ λ(n)n^{−s}` seria
holomorfa em `Re s > θ`, logo `(2s − 1)L(λ, s) = ζ₁(2s)F(s)` no disco `|s − 2| < 2` — e em `s = ½` o lado esquerdo
é `0` e o direito é `ζ₁(1)F(½) ≠ 0`. -/
theorem liouville_nao_O {θ C : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2)
    (hC : ∀ N : ℕ, |Lv N| ≤ C * ((N : ℝ) + 1) ^ θ) : False := by
  set V : Set ℂ := ball (2 : ℂ) 2 ∩ {s : ℂ | θ < s.re} with hV
  have hVo : IsOpen V := isOpen_ball.inter (isOpen_lt continuous_const continuous_re)
  have hVc : IsPreconnected V := (convex_ball (2 : ℂ) 2).inter (convex_halfSpace_re_gt θ) |>.isPreconnected
  set φ : ℂ → ℂ := fun s => (2 * s - 1) * GA Lv s - riemannZeta₁ (2 * s) * F s with hφ
  have hFd : DifferentiableOn ℂ F (ball (2 : ℂ) 2) := by
    have := ATK.ZeroClasses.Unilateral.differentiableOn_F (θ := 0) le_rfl
    rwa [sub_zero] at this
  have hφd : DifferentiableOn ℂ φ V := by
    intro s hs
    have hG := ATK.ZeroClasses.VonKoch.differentiableAt_GA hθ0 hC hs.2
    have hZ : DifferentiableAt ℂ (fun s => riemannZeta₁ (2 * s)) s :=
      (differentiable_riemannZeta₁ _).comp s (differentiableAt_id.const_mul 2)
    have hF := (hFd s hs.1).differentiableAt (isOpen_ball.mem_nhds hs.1)
    exact ((((differentiableAt_id.const_mul 2).sub_const 1).mul hG).sub (hZ.mul hF)).differentiableWithinAt
  have h2 : (2 : ℂ) ∈ V := ⟨mem_ball_self (by norm_num), by simp; linarith⟩
  have hev : φ =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [hmem] with s hs
    have h2s : 2 * s ≠ 1 := fun h => by
      have := congrArg re h
      simp at this
      linarith
    simp only [hφ, Pi.zero_apply]
    rw [GA_Lv_eq hs, zeta₁_eq h2s]
    ring
  have hzero := (hφd.analyticOnNhd hVo).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hVc h2 hev
  have hmeio : (1 / 2 : ℂ) ∈ V := by
    refine ⟨?_, by simp; linarith⟩
    rw [mem_ball, dist_eq_norm]
    norm_num
  have h := hzero hmeio
  simp only [hφ] at h
  have h1 : (2 : ℂ) * (1 / 2) = 1 := by norm_num
  rw [h1, sub_self, zero_mul, zero_sub] at h
  have h' : -(riemannZeta₁ 1 * F (1 / 2)) = 0 := h
  have hz1 : riemannZeta₁ 1 ≠ 0 := ATK.ZeroClasses.Unilateral.zeta₁_ne_zero_bola (by
    rw [mem_ball, dist_eq_norm]; norm_num)
  have hzm : riemannZeta₁ (1 / 2) ≠ 0 := ATK.ZeroClasses.Unilateral.zeta₁_ne_zero_bola (by
    rw [mem_ball, dist_eq_norm]; norm_num)
  have hF : F (1 / 2) ≠ 0 := by
    unfold F
    exact div_ne_zero (by norm_num) hzm
  exact mul_ne_zero hz1 hF (neg_eq_zero.mp h')

/-- **`|L(x)| = Ω(x^θ)` para `0 ≤ θ < ½`**: para todo `K`, `|L(N)| > (N + 1)^θ + K` para algum `N`. -/
theorem liouville_omega_abs {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (K : ℝ) :
    ∃ N : ℕ, ((N : ℝ) + 1) ^ θ + K < |Lv N| := by
  by_contra hne
  push Not at hne
  refine liouville_nao_O (C := 1 + |K|) hθ0 hθ fun N => ?_
  have hp : 1 ≤ ((N : ℝ) + 1) ^ θ := Real.one_le_rpow (by linarith [N.cast_nonneg (α := ℝ)]) hθ0
  have := hne N
  nlinarith [abs_nonneg K, le_abs_self K]

/-! ## 8. `Θ` como expoente exato de `|L(x)|` -/

open ATK.ZeroClasses.TetaExpoente (Expoentes Teta_eq_of mem_of_Teta freq_of_omega)
open ATK.ZeroClasses.BDTheta (meio_le_Teta rh_iff_Teta)

/-- **`Θ = inf{θ : |L(N)| ≤ N^θ para N grande}`** — sem hipóteses. -/
theorem Teta_eq_liouville : Teta = sInf (Expoentes fun N => |Lv N|) := by
  refine Teta_eq_of (mem_of_Teta (fun t ht1 ht2 hT ε hε => ?_) ⟨1, 0, Eventually.of_forall fun N => ?_⟩)
    fun θ hθ => ?_
  · obtain ⟨C, hC⟩ := liouville_of_semZeros ((Teta_le_iff ht1).mp hT) ht1 ht2 ε hε
    exact ⟨C, 0, Eventually.of_forall fun N => by rw [add_zero]; exact hC N⟩
  · rw [ATK.ZeroClasses.TetaExpoente.pot_um, one_mul, add_zero]
    exact abs_Lv_le N
  · set θ' := max θ 0 with hθ'
    have hθ'0 : 0 ≤ θ' := le_max_right _ _
    refine freq_of_omega hθ'0 (fun K => ?_) (le_max_left θ 0)
    rcases lt_or_ge θ' (1 / 2) with h | h
    · exact liouville_omega_abs hθ'0 h K
    · obtain ⟨N, hN⟩ := liouville_omega_mais h (max_lt hθ (by linarith [meio_le_Teta])) 1 K
      exact ⟨N, by linarith [le_abs_self (Lv N)]⟩

/-- **RH ⟺ o expoente de `|L(N)|` é `½`**. -/
theorem rh_iff_expoente_liouville : RiemannHypothesis ↔ sInf (Expoentes fun N => |Lv N|) = 1 / 2 := by
  rw [rh_iff_Teta, Teta_eq_liouville]

end ATK.ZeroClasses.LiouvilleRH

#print axioms ATK.ZeroClasses.LiouvilleRH.norm_lam_le
#print axioms ATK.ZeroClasses.LiouvilleRH.lam_prime
#print axioms ATK.ZeroClasses.LiouvilleRH.summable_lamHom
#print axioms ATK.ZeroClasses.LiouvilleRH.tsum_lamHom
#print axioms ATK.ZeroClasses.LiouvilleRH.LSeries_lam_mul_zeta
#print axioms ATK.ZeroClasses.LiouvilleRH.LSeriesSummable_lam
#print axioms ATK.ZeroClasses.LiouvilleRH.LSeries_lam
#print axioms ATK.ZeroClasses.LiouvilleRH.abs_liouville_le
#print axioms ATK.ZeroClasses.LiouvilleRH.abs_Lv_le
#print axioms ATK.ZeroClasses.LiouvilleRH.Lv_zero
#print axioms ATK.ZeroClasses.LiouvilleRH.Lv_one
#print axioms ATK.ZeroClasses.LiouvilleRH.Lv_succ_eq
#print axioms ATK.ZeroClasses.LiouvilleRH.GA_Lv_eq
#print axioms ATK.ZeroClasses.LiouvilleRH.re_gt_of_mem_ball
#print axioms ATK.ZeroClasses.LiouvilleRH.differentiableAt_zeta_dois
#print axioms ATK.ZeroClasses.LiouvilleRH.zeta_dois_ne_zero
#print axioms ATK.ZeroClasses.LiouvilleRH.differentiableOn_H
#print axioms ATK.ZeroClasses.LiouvilleRH.semZeros_of_ext_liouville
#print axioms ATK.ZeroClasses.LiouvilleRH.semZeros_of_liouville_le
#print axioms ATK.ZeroClasses.LiouvilleRH.semZeros_of_liouville_ge
#print axioms ATK.ZeroClasses.LiouvilleRH.Teta_le_of_liouville_le
#print axioms ATK.ZeroClasses.LiouvilleRH.Teta_le_of_liouville_ge
#print axioms ATK.ZeroClasses.LiouvilleRH.rh_of_liouville_le
#print axioms ATK.ZeroClasses.LiouvilleRH.rh_of_liouville_ge
#print axioms ATK.ZeroClasses.LiouvilleRH.rh_of_liouville_limitada_cima
#print axioms ATK.ZeroClasses.LiouvilleRH.rh_of_liouville_limitada_baixo
#print axioms ATK.ZeroClasses.LiouvilleRH.rh_of_polya
#print axioms ATK.ZeroClasses.LiouvilleRH.liouville_omega_mais
#print axioms ATK.ZeroClasses.LiouvilleRH.liouville_omega_menos
#print axioms ATK.ZeroClasses.LiouvilleRH.norm_zeta_le_unif
#print axioms ATK.ZeroClasses.LiouvilleRH.Lv_eq_sum
#print axioms ATK.ZeroClasses.LiouvilleRH.liouville_of_semZeros
#print axioms ATK.ZeroClasses.LiouvilleRH.semZeros_iff_liouville
#print axioms ATK.ZeroClasses.LiouvilleRH.Teta_le_iff_liouville_le
#print axioms ATK.ZeroClasses.LiouvilleRH.Teta_le_iff_liouville_ge
#print axioms ATK.ZeroClasses.LiouvilleRH.rh_iff_liouville
#print axioms ATK.ZeroClasses.LiouvilleRH.rh_iff_liouville_le
#print axioms ATK.ZeroClasses.LiouvilleRH.rh_iff_liouville_ge
#print axioms ATK.ZeroClasses.LiouvilleRH.liouville_nao_O
#print axioms ATK.ZeroClasses.LiouvilleRH.liouville_omega_abs
#print axioms ATK.ZeroClasses.LiouvilleRH.Teta_eq_liouville
#print axioms ATK.ZeroClasses.LiouvilleRH.rh_iff_expoente_liouville
