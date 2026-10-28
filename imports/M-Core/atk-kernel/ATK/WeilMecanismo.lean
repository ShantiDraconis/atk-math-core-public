import Mathlib

/-!
# ATK — O mecanismo de Weil (índice de Hodge ⇒ hipótese de Riemann para curvas) e a ponte de Hilbert–Pólya

**Weil (1948), forma abstrata.** Numa superfície `C × C` (curva `C` de gênero `g` sobre `𝔽_q`), com as
classes `f₁ = pt × C`, `f₂ = C × pt`, a diagonal `Δ` e o gráfico `Γ` do Frobenius, as interseções são
`f₁² = f₂² = 0`, `f₁·f₂ = 1`, `Δ·fᵢ = 1`, `Γ·f₁ = 1`, `Γ·f₂ = q`, `Δ² = 2 − 2g`, `Γ² = q(2 − 2g)` e
`Δ·Γ = N = #C(𝔽_q)`. O **teorema do índice de Hodge** (`D·H = 0 ⇒ D² ≤ 0`, `H = f₁ + f₂`) dá a
desigualdade de **Castelnuovo–Severi** `D² ≤ 2(D·f₁)(D·f₂)` (`castelnuovo_severi`) e daí a **cota de Weil**
`(N − q − 1)² ≤ 4g²q`, i.e. `|N − q − 1| ≤ 2g√q` (`cota_weil`, `cota_weil_abs`) — a hipótese de Riemann
para `C`.

Aqui tudo é **álgebra linear sobre uma forma bilinear simétrica qualquer**: os números de interseção e o
índice de Hodge entram como hipóteses. O que este arquivo isola é exatamente o nó que falta para `Spec ℤ`:
não se conhece uma "superfície" `Spec ℤ × Spec ℤ` com forma de interseção e índice de Hodge — o análogo
aritmético é a positividade de Weil, equivalente a HR e **`OPEN_MATH`**.

**Hilbert–Pólya** (`rh_de_operador`): se cada zero não trivial `ρ` dá um autovalor `(ρ − 1/2)/i` de um
operador simétrico num espaço com produto interno, vale HR (autovalores de operadores simétricos são reais).
Sem uma construção *natural* do operador, a existência é só uma reformulação; o operador é `OPEN_MATH`.
-/

open LinearMap

namespace ATK.Weil

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Castelnuovo–Severi** a partir do índice de Hodge: se `f₁² = f₂² = 0`, `f₁·f₂ = 1` e todo `x` com
`x·(f₁ + f₂) = 0` tem `x² ≤ 0`, então `D² ≤ 2(D·f₁)(D·f₂)`. -/
theorem castelnuovo_severi (β : LinearMap.BilinForm ℝ V) (hβ : β.IsSymm) (f₁ f₂ : V)
    (h11 : β f₁ f₁ = 0) (h22 : β f₂ f₂ = 0) (h12 : β f₁ f₂ = 1)
    (hodge : ∀ x, β x (f₁ + f₂) = 0 → β x x ≤ 0) (D : V) :
    β D D ≤ 2 * (β D f₁ * β D f₂) := by
  have h21 : β f₂ f₁ = 1 := by rw [← hβ.eq, h12]
  set a := β D f₂ with ha
  set b := β D f₁ with hb
  set D' := D - a • f₁ - b • f₂ with hD'
  have hD'1 : β D' f₁ = 0 := by
    simp only [hD', map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, h11, h21]
    rw [← hb]
    ring
  have hD'2 : β D' f₂ = 0 := by
    simp only [hD', map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, h22, h12]
    rw [← ha]
    ring
  have hH : β D' (f₁ + f₂) = 0 := by rw [map_add, hD'1, hD'2, add_zero]
  have hle := hodge D' hH
  have hDf1 : β f₁ D = b := by rw [← hβ.eq]
  have hDf2 : β f₂ D = a := by rw [← hβ.eq]
  have e : β D' D' = β D D - 2 * (b * a) := by
    simp only [hD', map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      h11, h22, h12, h21, hDf1, hDf2]
    rw [← ha, ← hb]
    ring
  rw [e] at hle
  linarith

/-- **Cota de Weil (hipótese de Riemann para curvas), forma quadrada**: com os números de interseção de
`C × C`, o índice de Hodge dá `(N − q − 1)² ≤ 4g²q`. -/
theorem cota_weil (β : LinearMap.BilinForm ℝ V) (hβ : β.IsSymm) (f₁ f₂ Δ Γ : V) (q g N : ℝ)
    (hg : 0 ≤ g)
    (h11 : β f₁ f₁ = 0) (h22 : β f₂ f₂ = 0) (h12 : β f₁ f₂ = 1)
    (hΔ1 : β Δ f₁ = 1) (hΔ2 : β Δ f₂ = 1) (hΓ1 : β Γ f₁ = 1) (hΓ2 : β Γ f₂ = q)
    (hΔΔ : β Δ Δ = 2 - 2 * g) (hΓΓ : β Γ Γ = q * (2 - 2 * g)) (hΔΓ : β Δ Γ = N)
    (hodge : ∀ x, β x (f₁ + f₂) = 0 → β x x ≤ 0) :
    (N - q - 1) ^ 2 ≤ 4 * g ^ 2 * q := by
  have hΓΔ : β Γ Δ = N := by rw [← hβ.eq, hΔΓ]
  have hQ : ∀ m n : ℝ, 0 ≤ g * m ^ 2 + (q + 1 - N) * m * n + g * q * n ^ 2 := by
    intro m n
    have h := castelnuovo_severi β hβ f₁ f₂ h11 h22 h12 hodge (m • Δ + n • Γ)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hΔ1, hΔ2, hΓ1, hΓ2, hΔΔ, hΓΓ, hΔΓ, hΓΔ] at h
    nlinarith [h]
  rcases hg.lt_or_eq with hgp | hg0
  · have h := hQ (-(q + 1 - N)) (2 * g)
    have : 0 ≤ g * (4 * g ^ 2 * q - (q + 1 - N) ^ 2) := by nlinarith [h]
    have h2 := (mul_nonneg_iff_of_pos_left hgp).mp this
    nlinarith [h2]
  · subst hg0
    have h := hQ 1 (-(q + 1 - N))
    nlinarith [h, sq_nonneg (q + 1 - N)]

/-- **`|N − q − 1| ≤ 2g√q`.** -/
theorem cota_weil_abs (β : LinearMap.BilinForm ℝ V) (hβ : β.IsSymm) (f₁ f₂ Δ Γ : V) (q g N : ℝ)
    (hq : 0 ≤ q) (hg : 0 ≤ g)
    (h11 : β f₁ f₁ = 0) (h22 : β f₂ f₂ = 0) (h12 : β f₁ f₂ = 1)
    (hΔ1 : β Δ f₁ = 1) (hΔ2 : β Δ f₂ = 1) (hΓ1 : β Γ f₁ = 1) (hΓ2 : β Γ f₂ = q)
    (hΔΔ : β Δ Δ = 2 - 2 * g) (hΓΓ : β Γ Γ = q * (2 - 2 * g)) (hΔΓ : β Δ Γ = N)
    (hodge : ∀ x, β x (f₁ + f₂) = 0 → β x x ≤ 0) :
    |N - q - 1| ≤ 2 * g * Real.sqrt q := by
  have h := cota_weil β hβ f₁ f₂ Δ Γ q g N hg h11 h22 h12 hΔ1 hΔ2 hΓ1 hΓ2 hΔΔ hΓΓ hΔΓ hodge
  have e : 4 * g ^ 2 * q = (2 * g * Real.sqrt q) ^ 2 := by
    rw [show (2 * g * Real.sqrt q) ^ 2 = 4 * g ^ 2 * Real.sqrt q ^ 2 by ring, Real.sq_sqrt hq]
  rw [e] at h
  exact abs_le_of_sq_le_sq h (by positivity)

/-- A matriz de Gram de `(f₁, f₂, Δ, Γ)` com `g = 0`, `q = 1`, `N = 5`. -/
def gramFalso : Matrix (Fin 4) (Fin 4) ℝ := !![0, 1, 1, 1; 1, 0, 1, 1; 1, 1, 2, 5; 1, 1, 5, 2]

/-- **Sem o índice de Hodge a cota falha**: existe uma forma bilinear simétrica em `ℝ⁴` com exatamente os
números de interseção de `C × C` para `g = 0`, `q = 1`, `N = 5`, e `(N − q − 1)² = 9 > 0 = 4g²q`. A
positividade (índice de Hodge) é o ingrediente — não a aritmética das interseções. -/
theorem hodge_necessario : ∃ (β : LinearMap.BilinForm ℝ (Fin 4 → ℝ)) (f₁ f₂ Δ Γ : Fin 4 → ℝ),
    β.IsSymm ∧ β f₁ f₁ = 0 ∧ β f₂ f₂ = 0 ∧ β f₁ f₂ = 1 ∧ β Δ f₁ = 1 ∧ β Δ f₂ = 1 ∧ β Γ f₁ = 1 ∧
    β Γ f₂ = 1 ∧ β Δ Δ = 2 - 2 * 0 ∧ β Γ Γ = 1 * (2 - 2 * 0) ∧ β Δ Γ = 5 ∧
    ¬ ((5 : ℝ) - 1 - 1) ^ 2 ≤ 4 * 0 ^ 2 * 1 := by
  refine ⟨Matrix.toBilin' gramFalso, Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1,
    ?_, ?_⟩
  · refine LinearMap.BilinForm.isSymm_def.mpr fun x y => ?_
    simp only [Matrix.toBilin'_apply, Fin.sum_univ_four, gramFalso, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.vecHead]
    ring
  · simp only [Matrix.toBilin'_single, gramFalso]
    norm_num

end ATK.Weil

namespace ATK.HilbertPolya

/-- **Ponte de Hilbert–Pólya**: se para cada zero não trivial `ρ` de `ζ` o número `(ρ − 1/2)/i` é autovalor de
um operador simétrico `T` num espaço com produto interno complexo, vale HR. -/
theorem rh_de_operador {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hspec : ∀ ρ : ℂ, riemannZeta ρ = 0 → (¬∃ n : ℕ, ρ = -2 * (n + 1)) → ρ ≠ 1 →
      Module.End.HasEigenvalue T ((ρ - 1 / 2) / Complex.I)) :
    RiemannHypothesis := by
  intro ρ hz hnt h1
  have hμ := hT.conj_eigenvalue_eq_self (hspec ρ hz hnt h1)
  have him := congrArg Complex.im hμ
  rw [Complex.conj_im] at him
  have h0 : ((ρ - 1 / 2) / Complex.I).im = 0 := by linarith
  have e : (ρ - 1 / 2) / Complex.I = -Complex.I * (ρ - 1 / 2) := by
    rw [div_eq_mul_inv, Complex.inv_I]
    ring
  rw [e] at h0
  simp only [neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_re,
    Complex.sub_im, zero_mul, one_mul, zero_add] at h0
  norm_num at h0
  linarith

end ATK.HilbertPolya

#print axioms ATK.Weil.castelnuovo_severi
#print axioms ATK.Weil.cota_weil
#print axioms ATK.Weil.cota_weil_abs
#print axioms ATK.Weil.hodge_necessario
#print axioms ATK.HilbertPolya.rh_de_operador
