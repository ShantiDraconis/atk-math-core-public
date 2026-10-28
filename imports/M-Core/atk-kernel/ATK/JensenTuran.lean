import ATK.Hexagrama

/-!
# ATK — Polinômios de Jensen, Turán, Toeplitz e momentos (a rota de Jensen–Pólya)

Variável quadrática `x = (s − ½)²` e `Θ(x) = ξ(½ + √x) = Σ aₙ xⁿ`.

* **`ξ` inteira** (`xiE`): `ξ(s) = s(s−1)/2 · Λ₀(s) + ½` (sem o valor-lixo do Mathlib em `0` e `1`);
  `ξ(1 − s) = ξ(s)` e **zeros de `ξ` = zeros não triviais de `ζ`** (`xiE_zero_iff`), usando
  `ζ ≠ 0` em `Re s ≥ 1` (Mathlib).
* **HR ⟺ `(ρ − ½)²` real e negativo** para todo zero (`rh_iff_quadrado`), e
  **HR ⟺ todos os zeros de `Θ` são reais negativos** (`rh_iff_Theta`) — a forma de Laguerre–Pólya.
* **Normalização de Jensen** `γₙ = n!·aₙ`: `γ_{k+1}² ≥ γ_kγ_{k+2} ⟺ (k+1)a_{k+1}² ≥ (k+2)a_ka_{k+2}`.
* **Jensen grau 2**: `γ_k + 2γ_{k+1}X + γ_{k+2}X²` só tem raízes reais ⟺ Turán (`jensen_grau2`).
* **Discriminante cúbico**: `Δ = A⁴∏(rᵢ − rⱼ)²`; raízes reais ⇒ `Δ ≥ 0`; par conjugado ⇒ `Δ < 0`;
  para `J₃` normalizado, `Δ = 27[4(γ₁² − γ₀γ₂)(γ₂² − γ₁γ₃) − (γ₁γ₂ − γ₀γ₃)²]` (Turán de ordem 3).
* **Toeplitz**: `D_{2,k+1} = γ_{k+1}² − γ_kγ_{k+2}`; menores 2×2 ≥ 0 ⟺ Turán.
* **Momentos**: para uma medida positiva, `M_{n+1}² ≤ M_nM_{n+2}` (log-**convexidade**, sempre);
  com `γₙ = C qⁿ n! Mₙ/(2n)!`, **Turán ⟺ `(2n+1)MₙM_{n+2} ≤ (2n+3)M_{n+1}²`**: um Cauchy–Schwarz
  **reverso** com folga `(2n+3)/(2n+1)`. A medida `¾δ₀ + ¼δ₂` mostra que a log-convexidade **não**
  implica Turán (`cs_nao_implica_turan`).

O que **não** está aqui (não está no Mathlib, ou é equivalente a HR): o teorema de Jensen–Pólya
(LP ⟺ todos os `J_{d,n}` hiperbólicos), Aissen–Schoenberg–Whitney–Edrei, a positividade total de
todos os menores e, portanto, HR.
-/

open Complex Finset MeasureTheory

namespace ATK.ClosedMath.Jensen

open ATK.ZetaSimetria ATK.CEZ

/-! ## 1. HR na variável quadrática -/

theorem quadrado_re_im (ρ : ℂ) :
    ((ρ - 1 / 2) ^ 2).im = 2 * (ρ.re - 1 / 2) * ρ.im ∧
      ((ρ - 1 / 2) ^ 2).re = (ρ.re - 1 / 2) ^ 2 - ρ.im ^ 2 := by
  constructor
  · simp [sq]; ring
  · simp [sq]

/-- **HR ⟺ `(ρ − ½)²` é real e negativo para todo zero não trivial.** -/
theorem rh_iff_quadrado : RiemannHypothesis ↔
    ∀ ρ ∈ Z, ((ρ - 1 / 2) ^ 2).im = 0 ∧ ((ρ - 1 / 2) ^ 2).re < 0 := by
  rw [rh_iff_externa_vazia]
  constructor
  · intro h ρ hρ
    have hre : ρ.re = 1 / 2 := by
      by_contra hne
      have hm : ρ ∈ ZE := ⟨hρ, hne⟩
      rw [h] at hm
      exact hm
    have him := im_ne_zero_of_mem_Z hρ
    obtain ⟨e1, e2⟩ := quadrado_re_im ρ
    rw [e1, e2, hre]
    refine ⟨by ring, ?_⟩
    have := pow_pos (abs_pos.mpr him) 2
    rw [sq_abs] at this
    linarith
  · intro h
    ext ρ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hρ, hne⟩
    have h1 := (h ρ hρ).1
    rw [(quadrado_re_im ρ).1] at h1
    have him := im_ne_zero_of_mem_Z hρ
    apply hne
    rcases mul_eq_zero.mp h1 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · norm_num at h3
      · linarith
    · exact absurd h2 him

/-! ## 2. `ξ` inteira e seus zeros -/

/-- `ξ(s) = s(s−1)/2 · Λ₀(s) + ½`: inteira, `ξ(0) = ξ(1) = ½`. -/
noncomputable def xiE (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2

theorem xiE_eq_xi {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : xiE s = ATK.ClosedMath.xi s := by
  unfold xiE ATK.ClosedMath.xi
  rw [completedRiemannZeta_eq]
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

theorem xiE_um_menos (s : ℂ) : xiE (1 - s) = xiE s := by
  unfold xiE
  rw [completedRiemannZeta₀_one_sub]
  ring

theorem xiE_zero_val : xiE 0 = 1 / 2 := by simp [xiE]

theorem xiE_one_val : xiE 1 = 1 / 2 := by simp [xiE]

theorem xiE_ne_zero_of_one_le_re {s : ℂ} (h : 1 ≤ s.re) : xiE s ≠ 0 := by
  by_cases hs1 : s = 1
  · rw [hs1, xiE_one_val]; norm_num
  have h0 : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by rintro rfl; simp at h0
  rw [xiE_eq_xi hs0 hs1, Ne, ATK.ClosedMath.xi_zero_iff h0 hs1]
  exact riemannZeta_ne_zero_of_one_le_re h

theorem xiE_ne_zero_of_re_nonpos {s : ℂ} (h : s.re ≤ 0) : xiE s ≠ 0 := by
  rw [← xiE_um_menos]
  apply xiE_ne_zero_of_one_le_re
  simp only [sub_re, one_re]
  linarith

/-- **Os zeros de `ξ` são exatamente os zeros não triviais de `ζ`.** -/
theorem xiE_zero_iff (s : ℂ) : xiE s = 0 ↔ s ∈ Z := by
  constructor
  · intro h
    have h0 : 0 < s.re := by
      by_contra h'
      exact xiE_ne_zero_of_re_nonpos (not_lt.mp h') h
    have h1 : s.re < 1 := by
      by_contra h'
      exact xiE_ne_zero_of_one_le_re (not_lt.mp h') h
    have hs0 : s ≠ 0 := by rintro rfl; simp at h0
    have hs1 : s ≠ 1 := by rintro rfl; simp at h1
    rw [xiE_eq_xi hs0 hs1, ATK.ClosedMath.xi_zero_iff h0 hs1] at h
    exact ⟨h, h0, h1⟩
  · rintro ⟨hz, h0, h1⟩
    have hs0 : s ≠ 0 := by rintro rfl; simp at h0
    have hs1 : s ≠ 1 := by rintro rfl; simp at h1
    rw [xiE_eq_xi hs0 hs1, ATK.ClosedMath.xi_zero_iff h0 hs1]
    exact hz

/-! ## 3. `Θ(x) = ξ(½ + √x)` e HR na forma de Laguerre–Pólya -/

/-- `ξ(½ + w)` é par em `w`. -/
theorem xiE_par (w : ℂ) : xiE (1 / 2 - w) = xiE (1 / 2 + w) := by
  rw [← xiE_um_menos]
  congr 1
  ring

/-- `Θ(x) = ξ(½ + √x)` (bem definida pela paridade). -/
noncomputable def Theta (x : ℂ) : ℂ := xiE (1 / 2 + x ^ ((2 : ℂ)⁻¹))

theorem raiz_sq (x : ℂ) : (x ^ ((2 : ℂ)⁻¹)) ^ 2 = x := Complex.cpow_ofNat_inv_pow x 2

theorem Theta_quadrado (w : ℂ) : Theta (w ^ 2) = xiE (1 / 2 + w) := by
  unfold Theta
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (raiz_sq (w ^ 2)) with h | h
  · rw [h]
  · rw [h, ← sub_eq_add_neg, xiE_par]

/-- **HR ⟺ todos os zeros de `Θ` são reais e negativos.** -/
theorem rh_iff_Theta : RiemannHypothesis ↔ ∀ x : ℂ, Theta x = 0 → x.im = 0 ∧ x.re < 0 := by
  rw [rh_iff_quadrado]
  constructor
  · intro h x hx
    have hρ : (1 / 2 + x ^ ((2 : ℂ)⁻¹)) ∈ Z := (xiE_zero_iff _).mp hx
    have := h _ hρ
    rwa [show (1 / 2 + x ^ ((2 : ℂ)⁻¹) - 1 / 2) = x ^ ((2 : ℂ)⁻¹) by ring, raiz_sq] at this
  · intro h ρ hρ
    apply h
    rw [Theta_quadrado, show (1 / 2 : ℂ) + (ρ - 1 / 2) = ρ by ring]
    exact (xiE_zero_iff ρ).mpr hρ

/-! ## 4. Normalização de Jensen e Turán -/

/-- `γₙ = n!·aₙ`. -/
noncomputable def gam (a : ℕ → ℝ) (n : ℕ) : ℝ := (n.factorial : ℝ) * a n

/-- **Turán normalizado**: `γ_kγ_{k+2} ≤ γ_{k+1}² ⟺ (k+2)a_ka_{k+2} ≤ (k+1)a_{k+1}²`. -/
theorem turan_normalizacao (a : ℕ → ℝ) (k : ℕ) :
    gam a k * gam a (k + 2) ≤ gam a (k + 1) ^ 2 ↔
      ((k : ℝ) + 2) * a k * a (k + 2) ≤ ((k : ℝ) + 1) * a (k + 1) ^ 2 := by
  unfold gam
  have e1 : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * k.factorial := by
    push_cast [Nat.factorial_succ]; ring
  have e2 : ((k + 2).factorial : ℝ) = ((k : ℝ) + 2) * ((k : ℝ) + 1) * k.factorial := by
    push_cast [Nat.factorial_succ]; ring
  rw [e1, e2]
  have hpos : 0 < ((k : ℝ) + 1) * (k.factorial : ℝ) ^ 2 := by
    have := Nat.factorial_pos k
    positivity
  have key : (((k : ℝ) + 1) * k.factorial * a (k + 1)) ^ 2 -
      k.factorial * a k * (((k : ℝ) + 2) * ((k : ℝ) + 1) * k.factorial * a (k + 2)) =
      (((k : ℝ) + 1) * (k.factorial : ℝ) ^ 2) *
        (((k : ℝ) + 1) * a (k + 1) ^ 2 - ((k : ℝ) + 2) * a k * a (k + 2)) := by ring
  rw [← sub_nonneg, key, mul_nonneg_iff_of_pos_left hpos, sub_nonneg]

/-- **Jensen de grau 2**: `g₂z² + 2g₁z + g₀` (`g₂ ≠ 0`) só tem raízes reais ⟺ `g₀g₂ ≤ g₁²`. -/
theorem jensen_grau2 {g0 g1 g2 : ℝ} (h2 : g2 ≠ 0) :
    (∀ z : ℂ, (g2 : ℂ) * z ^ 2 + 2 * g1 * z + g0 = 0 → z.im = 0) ↔ g0 * g2 ≤ g1 ^ 2 := by
  constructor
  · intro h
    by_contra hlt
    have hD : 0 < g0 * g2 - g1 ^ 2 := by linarith [not_le.mp hlt]
    set s := Real.sqrt (g0 * g2 - g1 ^ 2) with hs_def
    have hs : s ^ 2 = g0 * g2 - g1 ^ 2 := Real.sq_sqrt hD.le
    have hs0 : 0 < s := Real.sqrt_pos.mpr hD
    have h2' : (g2 : ℂ) ≠ 0 := by exact_mod_cast h2
    have hsC : (s : ℂ) ^ 2 = (g0 : ℂ) * g2 - (g1 : ℂ) ^ 2 := by exact_mod_cast hs
    have hfr : (g2 : ℂ) * ((-(g1 : ℂ) + (s : ℂ) * I) / g2) ^ 2 +
        2 * g1 * ((-(g1 : ℂ) + (s : ℂ) * I) / g2) + g0 =
        ((-(g1 : ℂ) + (s : ℂ) * I) ^ 2 + 2 * g1 * (-(g1 : ℂ) + (s : ℂ) * I) + g0 * g2) / g2 := by
      field_simp
    have hnum : (-(g1 : ℂ) + (s : ℂ) * I) ^ 2 + 2 * g1 * (-(g1 : ℂ) + (s : ℂ) * I) + g0 * g2 = 0 := by
      linear_combination (-(1 : ℂ)) * hsC + (s : ℂ) ^ 2 * I_sq
    have hz : (g2 : ℂ) * ((-(g1 : ℂ) + (s : ℂ) * I) / g2) ^ 2 +
        2 * g1 * ((-(g1 : ℂ) + (s : ℂ) * I) / g2) + g0 = 0 := by
      rw [hfr, hnum, zero_div]
    have him := h _ hz
    have : ((-(g1 : ℂ) + (s : ℂ) * I) / g2).im = s / g2 := by
      simp [div_ofReal_im]
    rw [this] at him
    rcases div_eq_zero_iff.mp him with h' | h'
    · linarith
    · exact h2 h'
  · intro h z hz
    have hre : g2 * (z.re ^ 2 - z.im ^ 2) + 2 * g1 * z.re + g0 = 0 := by
      have := congrArg Complex.re hz
      simp [sq] at this
      linarith
    have him : z.im * (2 * (g2 * z.re + g1)) = 0 := by
      have := congrArg Complex.im hz
      simp [sq] at this
      linarith
    by_contra hy
    have hx : g2 * z.re + g1 = 0 := by
      rcases mul_eq_zero.mp him with h' | h'
      · exact absurd h' hy
      · linarith
    have key : g2 ^ 2 * z.im ^ 2 = g0 * g2 - g1 ^ 2 := by
      linear_combination (-g2) * hre + (g2 * z.re + g1) * hx
    have : 0 < g2 ^ 2 * z.im ^ 2 := by positivity
    linarith

/-- `J_{2,k}(X) = γ_k + 2γ_{k+1}X + γ_{k+2}X²` é hiperbólico ⟺ `γ_kγ_{k+2} ≤ γ_{k+1}²`. -/
theorem jensen2_iff_turan (γ : ℕ → ℝ) (k : ℕ) (hk : γ (k + 2) ≠ 0) :
    (∀ z : ℂ, (γ (k + 2) : ℂ) * z ^ 2 + 2 * γ (k + 1) * z + γ k = 0 → z.im = 0) ↔
      γ k * γ (k + 2) ≤ γ (k + 1) ^ 2 :=
  jensen_grau2 hk

/-! ## 5. Discriminante cúbico e Turán de ordem 3 -/

/-- Discriminante de `AX³ + BX² + CX + D`. -/
def disc3 {R : Type*} [CommRing R] (A B C D : R) : R :=
  B ^ 2 * C ^ 2 - 4 * A * C ^ 3 - 4 * B ^ 3 * D - 27 * A ^ 2 * D ^ 2 + 18 * A * B * C * D

/-- `Δ = A⁴ ∏_{i<j} (rᵢ − rⱼ)²` para `A(X − r₁)(X − r₂)(X − r₃)`. -/
theorem disc3_raizes {R : Type*} [CommRing R] (A r1 r2 r3 : R) :
    disc3 A (-A * (r1 + r2 + r3)) (A * (r1 * r2 + r1 * r3 + r2 * r3)) (-A * r1 * r2 * r3) =
      A ^ 4 * ((r1 - r2) * (r1 - r3) * (r2 - r3)) ^ 2 := by
  unfold disc3; ring

/-- Raízes reais ⇒ `Δ ≥ 0`. -/
theorem disc3_real_nonneg (A r1 r2 r3 : ℝ) :
    0 ≤ disc3 A (-A * (r1 + r2 + r3)) (A * (r1 * r2 + r1 * r3 + r2 * r3)) (-A * r1 * r2 * r3) := by
  rw [disc3_raizes]; positivity

/-- Uma raiz real `r` e um par conjugado `u ± iv` (`v ≠ 0`) ⇒ `Δ = −4A⁴v²((r−u)²+v²)² < 0`. -/
theorem disc3_conjugado (A r u v : ℝ) (hA : A ≠ 0) (hv : v ≠ 0) :
    (A : ℂ) ^ 4 * ((r - (u + v * I)) * (r - (u - v * I)) * ((u + v * I) - (u - v * I))) ^ 2 =
        ((-4 * A ^ 4 * v ^ 2 * ((r - u) ^ 2 + v ^ 2) ^ 2 : ℝ) : ℂ) ∧
      -4 * A ^ 4 * v ^ 2 * ((r - u) ^ 2 + v ^ 2) ^ 2 < 0 := by
  constructor
  · have h1 : ((r : ℂ) - (u + v * I)) * (r - (u - v * I)) = (((r - u) ^ 2 + v ^ 2 : ℝ) : ℂ) := by
      push_cast
      linear_combination (-(v : ℂ) ^ 2) * I_sq
    have h2 : ((u : ℂ) + v * I) - (u - v * I) = 2 * v * I := by ring
    rw [h1, h2]
    push_cast
    linear_combination (4 * (A : ℂ) ^ 4 * (v : ℂ) ^ 2 * (((r : ℂ) - u) ^ 2 + (v : ℂ) ^ 2) ^ 2) * I_sq
  · have : 0 < A ^ 4 * v ^ 2 * ((r - u) ^ 2 + v ^ 2) ^ 2 := by
      have : 0 < (r - u) ^ 2 + v ^ 2 := by positivity
      positivity
    linarith

/-- `J₃` normalizado `γ₃X³ + 3γ₂X² + 3γ₁X + γ₀`:
`Δ = 27[4(γ₁² − γ₀γ₂)(γ₂² − γ₁γ₃) − (γ₁γ₂ − γ₀γ₃)²]`. -/
theorem disc3_jensen (g0 g1 g2 g3 : ℝ) :
    disc3 g3 (3 * g2) (3 * g1) g0 =
      27 * (4 * (g1 ^ 2 - g0 * g2) * (g2 ^ 2 - g1 * g3) - (g1 * g2 - g0 * g3) ^ 2) := by
  unfold disc3; ring

/-- **Turán de ordem 3**: se `J₃` tem três raízes reais, então
`(γ₁γ₂ − γ₀γ₃)² ≤ 4(γ₁² − γ₀γ₂)(γ₂² − γ₁γ₃)`. -/
theorem turan3 {g0 g1 g2 g3 r1 r2 r3 : ℝ}
    (hB : 3 * g2 = -g3 * (r1 + r2 + r3)) (hC : 3 * g1 = g3 * (r1 * r2 + r1 * r3 + r2 * r3))
    (hD : g0 = -g3 * r1 * r2 * r3) :
    (g1 * g2 - g0 * g3) ^ 2 ≤ 4 * (g1 ^ 2 - g0 * g2) * (g2 ^ 2 - g1 * g3) := by
  have h := disc3_real_nonneg g3 r1 r2 r3
  rw [← hB, ← hC, ← hD, disc3_jensen] at h
  linarith

/-! ## 6. Menores de Toeplitz -/

/-- Sequência estendida por zero aos índices negativos. -/
noncomputable def ext (γ : ℕ → ℝ) (n : ℤ) : ℝ := if 0 ≤ n then γ n.toNat else 0

theorem ext_of_eq (γ : ℕ → ℝ) {n : ℤ} {m : ℕ} (h : n = m) : ext γ n = γ m := by
  subst h; simp [ext]

/-- `D_{r,k} = det[γ_{k+i−j}]_{i,j<r}`. -/
noncomputable def Dmin (γ : ℕ → ℝ) (r : ℕ) (k : ℤ) : ℝ :=
  (Matrix.of fun i j : Fin r => ext γ (k + (i : ℕ) - (j : ℕ))).det

theorem Dmin_um (γ : ℕ → ℝ) (k : ℕ) : Dmin γ 1 k = γ k := by
  unfold Dmin
  rw [Matrix.det_unique]
  simp only [Matrix.of_apply]
  exact ext_of_eq γ (by simp)

/-- **Menor 2×2**: `D_{2,k+1} = γ_{k+1}² − γ_kγ_{k+2}`. -/
theorem Dmin_dois (γ : ℕ → ℝ) (k : ℕ) : Dmin γ 2 ((k : ℤ) + 1) = γ (k + 1) ^ 2 - γ k * γ (k + 2) := by
  unfold Dmin
  rw [Matrix.det_fin_two]
  have e00 : ext γ (((k : ℤ) + 1) + (((0 : Fin 2) : ℕ) : ℤ) - (((0 : Fin 2) : ℕ) : ℤ)) = γ (k + 1) :=
    ext_of_eq γ (by simp)
  have e11 : ext γ (((k : ℤ) + 1) + (((1 : Fin 2) : ℕ) : ℤ) - (((1 : Fin 2) : ℕ) : ℤ)) = γ (k + 1) :=
    ext_of_eq γ (by simp)
  have e01 : ext γ (((k : ℤ) + 1) + (((0 : Fin 2) : ℕ) : ℤ) - (((1 : Fin 2) : ℕ) : ℤ)) = γ k :=
    ext_of_eq γ (by simp)
  have e10 : ext γ (((k : ℤ) + 1) + (((1 : Fin 2) : ℕ) : ℤ) - (((0 : Fin 2) : ℕ) : ℤ)) = γ (k + 2) :=
    ext_of_eq γ (by simp; ring)
  simp only [Matrix.of_apply, e00, e11, e01, e10]
  ring

/-- **Menores 2×2 de Toeplitz ≥ 0 ⟺ Turán.** -/
theorem toeplitz2_iff_turan (γ : ℕ → ℝ) :
    (∀ k : ℕ, 0 ≤ Dmin γ 2 ((k : ℤ) + 1)) ↔ ∀ k : ℕ, γ k * γ (k + 2) ≤ γ (k + 1) ^ 2 := by
  simp only [Dmin_dois, sub_nonneg]

/-! ## 7. Momentos: log-convexidade (sempre) × Turán (o que falta) -/

/-- Momentos pares `Mₙ = ∫ u^{2n} dμ`. -/
noncomputable def M (μ : Measure ℝ) (n : ℕ) : ℝ := ∫ u, u ^ (2 * n) ∂μ

/-- **Cauchy–Schwarz**: `M_{n+1}² ≤ MₙM_{n+2}` para toda medida positiva (log-convexidade). -/
theorem momentos_logconvexos (μ : Measure ℝ) (n : ℕ)
    (h0 : Integrable (fun u : ℝ => u ^ (2 * n)) μ)
    (h1 : Integrable (fun u : ℝ => u ^ (2 * (n + 1))) μ)
    (h2 : Integrable (fun u : ℝ => u ^ (2 * (n + 2))) μ) :
    M μ (n + 1) ^ 2 ≤ M μ n * M μ (n + 2) := by
  have key : ∀ t : ℝ, 0 ≤ M μ n * (t * t) + 2 * M μ (n + 1) * t + M μ (n + 2) := by
    intro t
    have hq : (fun u : ℝ => u ^ (2 * n) * (t + u ^ 2) ^ 2) =
        fun u => (t * t) * u ^ (2 * n) + (2 * t) * u ^ (2 * (n + 1)) + u ^ (2 * (n + 2)) := by
      funext u; ring
    have hint : ∫ u, u ^ (2 * n) * (t + u ^ 2) ^ 2 ∂μ =
        M μ n * (t * t) + 2 * M μ (n + 1) * t + M μ (n + 2) := by
      have i1 : Integrable (fun u : ℝ => (t * t) * u ^ (2 * n) + (2 * t) * u ^ (2 * (n + 1))) μ :=
        (h0.const_mul _).add (h1.const_mul _)
      rw [hq, integral_add i1 h2, integral_add (h0.const_mul _) (h1.const_mul _), integral_const_mul,
        integral_const_mul]
      unfold M
      ring
    rw [← hint]
    apply integral_nonneg
    intro u
    have : 0 ≤ u ^ (2 * n) := by rw [pow_mul]; positivity
    exact mul_nonneg this (sq_nonneg _)
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

/-- Coeficientes de Jensen a partir dos momentos: `γₙ = C qⁿ n! Mₙ/(2n)!`
(para `ξ`: `aₙ = 8·4ⁿ Mₙ/(2n)!`, `Mₙ = ∫₀^∞ u^{2n} Φ(u) du`). -/
noncomputable def gamM (C q : ℝ) (Mm : ℕ → ℝ) (n : ℕ) : ℝ :=
  C * q ^ n * (n.factorial : ℝ) * Mm n / ((2 * n).factorial : ℝ)

/-- **Turán ⟺ Cauchy–Schwarz reverso**: `γₙγ_{n+2} ≤ γ_{n+1}² ⟺ (2n+1)MₙM_{n+2} ≤ (2n+3)M_{n+1}²`. -/
theorem turan_iff_momentos (C q : ℝ) (hC : 0 < C) (hq : 0 < q) (Mm : ℕ → ℝ) (n : ℕ) :
    gamM C q Mm n * gamM C q Mm (n + 2) ≤ gamM C q Mm (n + 1) ^ 2 ↔
      (2 * (n : ℝ) + 1) * (Mm n * Mm (n + 2)) ≤ (2 * (n : ℝ) + 3) * Mm (n + 1) ^ 2 := by
  have fa1 : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * n.factorial := by
    push_cast [Nat.factorial_succ]; ring
  have fa2 : ((n + 2).factorial : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) * n.factorial := by
    push_cast [Nat.factorial_succ]; ring
  have fb1 : ((2 * (n + 1)).factorial : ℝ) = (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1) *
      (2 * n).factorial := by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
    push_cast [Nat.factorial_succ]; ring
  have fb2 : ((2 * (n + 2)).factorial : ℝ) = (2 * (n : ℝ) + 4) * (2 * (n : ℝ) + 3) *
      (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1) * (2 * n).factorial := by
    rw [show 2 * (n + 2) = 2 * n + 1 + 1 + 1 + 1 by ring]
    push_cast [Nat.factorial_succ]; ring
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hf2 : (0 : ℝ) < (2 * n).factorial := by exact_mod_cast Nat.factorial_pos _
  set c := C * q ^ n * (n.factorial : ℝ) / ((2 * n).factorial : ℝ) with hc
  have hcpos : 0 < c := by positivity
  have g0 : gamM C q Mm n = c * Mm n := by
    unfold gamM; rw [hc]; field_simp
  have g1 : gamM C q Mm (n + 1) = c * (q / (2 * (2 * (n : ℝ) + 1))) * Mm (n + 1) := by
    unfold gamM; rw [hc, fa1, fb1]; field_simp; ring
  have g2 : gamM C q Mm (n + 2) =
      c * (q ^ 2 / (4 * (2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3))) * Mm (n + 2) := by
    unfold gamM; rw [hc, fa2, fb2]; field_simp; ring
  have key : gamM C q Mm (n + 1) ^ 2 - gamM C q Mm n * gamM C q Mm (n + 2) =
      (c ^ 2 * q ^ 2 / (4 * (2 * (n : ℝ) + 1) ^ 2 * (2 * (n : ℝ) + 3))) *
        ((2 * (n : ℝ) + 3) * Mm (n + 1) ^ 2 - (2 * (n : ℝ) + 1) * (Mm n * Mm (n + 2))) := by
    rw [g0, g1, g2]; field_simp; ring
  have hpos : 0 < c ^ 2 * q ^ 2 / (4 * (2 * (n : ℝ) + 1) ^ 2 * (2 * (n : ℝ) + 3)) := by positivity
  rw [← sub_nonneg, key, mul_nonneg_iff_of_pos_left hpos, sub_nonneg]

/-- **Sanduíche**: para momentos de uma medida positiva, Turán (normalizado) equivale a
`M_{n+1}² ≤ MₙM_{n+2} ≤ ((2n+3)/(2n+1)) M_{n+1}²` — o lado esquerdo é grátis, o direito é o
conteúdo. -/
theorem sanduiche (μ : Measure ℝ) (C q : ℝ) (hC : 0 < C) (hq : 0 < q) (n : ℕ)
    (h0 : Integrable (fun u : ℝ => u ^ (2 * n)) μ)
    (h1 : Integrable (fun u : ℝ => u ^ (2 * (n + 1))) μ)
    (h2 : Integrable (fun u : ℝ => u ^ (2 * (n + 2))) μ) :
    M μ (n + 1) ^ 2 ≤ M μ n * M μ (n + 2) ∧
      (gamM C q (M μ) n * gamM C q (M μ) (n + 2) ≤ gamM C q (M μ) (n + 1) ^ 2 ↔
        (2 * (n : ℝ) + 1) * (M μ n * M μ (n + 2)) ≤ (2 * (n : ℝ) + 3) * M μ (n + 1) ^ 2) :=
  ⟨momentos_logconvexos μ n h0 h1 h2, turan_iff_momentos C q hC hq (M μ) n⟩

/-- A medida `¾δ₀ + ¼δ₂`. -/
noncomputable def muCE : Measure ℝ :=
  (3 / 4 : ENNReal) • Measure.dirac 0 + (1 / 4 : ENNReal) • Measure.dirac 2

theorem M_muCE (n : ℕ) : M muCE n = 3 / 4 * (0 : ℝ) ^ (2 * n) + 1 / 4 * (2 : ℝ) ^ (2 * n) := by
  unfold M muCE
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac]
  · simp [ENNReal.toReal_div]
  · exact (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by simp) (by simp))
  · exact (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by simp) (by simp))

/-- **Log-convexidade não implica Turán**: em `¾δ₀ + ¼δ₂`, `M = (1, 1, 4)`;
`M₁² = 1 ≤ 4 = M₀M₂`, mas `1·M₀M₂ = 4 > 3 = 3·M₁²`. -/
theorem cs_nao_implica_turan :
    M muCE 1 ^ 2 ≤ M muCE 0 * M muCE 2 ∧
      ¬ ((2 * ((0 : ℕ) : ℝ) + 1) * (M muCE 0 * M muCE 2) ≤ (2 * ((0 : ℕ) : ℝ) + 3) * M muCE 1 ^ 2) := by
  simp only [M_muCE]
  norm_num

/-! ## 8. Positividade total: `a` × `γ = n!·a` -/

theorem ext_neg (γ : ℕ → ℝ) {n : ℤ} (h : n < 0) : ext γ n = 0 := by
  simp [ext, not_le.mpr h]

/-- Menor 3×3 em `k = 1`: `D_{3,1} = γ₁³ − 2γ₀γ₁γ₂ + γ₀²γ₃`. -/
theorem Dmin_tres_um (γ : ℕ → ℝ) :
    Dmin γ 3 1 = γ 1 ^ 3 - 2 * γ 0 * γ 1 * γ 2 + γ 0 ^ 2 * γ 3 := by
  unfold Dmin
  rw [Matrix.det_fin_three]
  have v0 : ((0 : Fin 3) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 3) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 3) : ℕ) = 2 := rfl
  simp only [Matrix.of_apply, v0, v1, v2]
  rw [ext_of_eq γ (n := (1 : ℤ) + ((0 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) (m := 1) (by norm_num),
    ext_of_eq γ (n := (1 : ℤ) + ((0 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) (m := 0) (by norm_num),
    ext_neg γ (n := (1 : ℤ) + ((0 : ℕ) : ℤ) - ((2 : ℕ) : ℤ)) (by norm_num),
    ext_of_eq γ (n := (1 : ℤ) + ((1 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) (m := 2) (by norm_num),
    ext_of_eq γ (n := (1 : ℤ) + ((1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) (m := 1) (by norm_num),
    ext_of_eq γ (n := (1 : ℤ) + ((1 : ℕ) : ℤ) - ((2 : ℕ) : ℤ)) (m := 0) (by norm_num),
    ext_of_eq γ (n := (1 : ℤ) + ((2 : ℕ) : ℤ) - ((0 : ℕ) : ℤ)) (m := 3) (by norm_num),
    ext_of_eq γ (n := (1 : ℤ) + ((2 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) (m := 2) (by norm_num),
    ext_of_eq γ (n := (1 : ℤ) + ((2 : ℕ) : ℤ) - ((2 : ℕ) : ℤ)) (m := 1) (by norm_num)]
  ring

/-- **Positividade total não passa de `a` para `γ = n!·a`**: para `(1 + X)³`, `a = (1,3,3,1)` (só
zeros reais negativos, sequência de Pólya–frequência) tem `D_{3,1}(a) = 10 > 0`, mas
`γ = (1,3,6,6)` tem `D_{3,1}(γ) = −3 < 0`. O alvo correto de Aissen–Schoenberg–Whitney–Edrei é a
sequência dos coeficientes de Taylor `aₙ` de `Θ`, não `γₙ`. -/
theorem tp_a_nao_passa_gamma :
    Dmin (fun n => ((Nat.choose 3 n : ℕ) : ℝ)) 3 1 = 10 ∧
      Dmin (gam fun n => ((Nat.choose 3 n : ℕ) : ℝ)) 3 1 = -3 := by
  rw [Dmin_tres_um, Dmin_tres_um]
  simp [gam, Nat.choose, Nat.factorial]
  norm_num

end ATK.ClosedMath.Jensen

-- Auditoria de axiomas (kernel)
#print axioms ATK.ClosedMath.Jensen.quadrado_re_im
#print axioms ATK.ClosedMath.Jensen.rh_iff_quadrado
#print axioms ATK.ClosedMath.Jensen.xiE_eq_xi
#print axioms ATK.ClosedMath.Jensen.xiE_um_menos
#print axioms ATK.ClosedMath.Jensen.xiE_zero_val
#print axioms ATK.ClosedMath.Jensen.xiE_one_val
#print axioms ATK.ClosedMath.Jensen.xiE_ne_zero_of_one_le_re
#print axioms ATK.ClosedMath.Jensen.xiE_ne_zero_of_re_nonpos
#print axioms ATK.ClosedMath.Jensen.xiE_zero_iff
#print axioms ATK.ClosedMath.Jensen.xiE_par
#print axioms ATK.ClosedMath.Jensen.raiz_sq
#print axioms ATK.ClosedMath.Jensen.Theta_quadrado
#print axioms ATK.ClosedMath.Jensen.rh_iff_Theta
#print axioms ATK.ClosedMath.Jensen.turan_normalizacao
#print axioms ATK.ClosedMath.Jensen.jensen_grau2
#print axioms ATK.ClosedMath.Jensen.jensen2_iff_turan
#print axioms ATK.ClosedMath.Jensen.disc3_raizes
#print axioms ATK.ClosedMath.Jensen.disc3_real_nonneg
#print axioms ATK.ClosedMath.Jensen.disc3_conjugado
#print axioms ATK.ClosedMath.Jensen.disc3_jensen
#print axioms ATK.ClosedMath.Jensen.turan3
#print axioms ATK.ClosedMath.Jensen.ext_of_eq
#print axioms ATK.ClosedMath.Jensen.Dmin_um
#print axioms ATK.ClosedMath.Jensen.Dmin_dois
#print axioms ATK.ClosedMath.Jensen.toeplitz2_iff_turan
#print axioms ATK.ClosedMath.Jensen.momentos_logconvexos
#print axioms ATK.ClosedMath.Jensen.turan_iff_momentos
#print axioms ATK.ClosedMath.Jensen.sanduiche
#print axioms ATK.ClosedMath.Jensen.M_muCE
#print axioms ATK.ClosedMath.Jensen.cs_nao_implica_turan
#print axioms ATK.ClosedMath.Jensen.ext_neg
#print axioms ATK.ClosedMath.Jensen.Dmin_tres_um
#print axioms ATK.ClosedMath.Jensen.tp_a_nao_passa_gamma
