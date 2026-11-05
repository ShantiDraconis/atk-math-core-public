import ATK.Hexagrama
import ATK.ClosedMathGeometrias
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# ATK — Geometria extra, contraexemplos e erros registrados

* **K₆** (o hexagrama `½ ± d ± it, ½ ± it`): as coordenadas `x = d(1,−1,−1,1,0,0)` e
  `y = t(1,1,−1,−1,1,−1)` dos seis pontos têm soma `0`, `|x|² = 4d²`, `|y|² = 6t²`, `⟨x,y⟩ = 0`; o
  laplaciano `L = 6I − J` de `K₆` tem `vᵀLv = Σ_{i<j}(vᵢ − vⱼ)²`, `Lv = 6v − (Σv)𝟙`, autovalores só
  `0` (constantes) e `6` (soma zero); `xᵀLx = 24d²`, `yᵀLy = 36t²`; rotação preserva `d² + t²` e o
  retângulo do quarteto tem área `4|dt|`.
* **Métricas induzidas** `(E, F, G)`: helicoide `(1, 0, 1+σ²)`, cilindro parabólico `(1+4σ², 0, 1)`,
  sela `(1+4σ², −4σt, 1+4t²)`, hiperboloide `(cosh²t, 0, cosh 2t)`, todas com `EG − F² > 0`.
* **Jensen com `aₙ` (contraexemplo)**: `Θ = 1 + 2x + 2x²` tem zeros não reais, mas todos os
  polinômios de Jensen montados com `aₙ` são hiperbólicos (discriminante `4N > 0`); com
  `γₙ = n!aₙ = (1, 2, 4)`, `J_{3,0} = 1 + 6X + 12X²` não tem raiz real — só a normalização `γₙ` detecta.
* **Família de cruzamento** (8af24fb4): sem `γ ≠ 0` as afirmações falham — `λ ≠ 0, γ = 0` dá zeros
  **duplos** `½ ± λ`, e `λ = γ = 0` dá um zero **quádruplo** em `½`.
* **"HR ⇏ O1"** (425e4bc1) é mal posto: provar `¬(HR → Q)` provaria HR (`nao_implica_prova_rh`).
* **Fourier no toro**: `e_{m,n}(x,y) = e^{i(mx+ny)}/(2π)` é ortonormal em `[0,2π]²`.
* **Energia cinética gaussiana**: para `ψ = (α/π)^{1/4} e^{−αx²/2}`, `ψ′ = −αxψ`, `∫ψ² = 1` e
  `½∫(ψ′)² = α/4`.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace ATK.GeometriaExtra

/-! ## 1. K₆ -/

/-- Partes reais dos seis pontos. -/
def xv (d : ℝ) : Fin 6 → ℝ := ![d, -d, -d, d, 0, 0]
/-- Partes imaginárias dos seis pontos. -/
def yv (t : ℝ) : Fin 6 → ℝ := ![t, t, -t, -t, t, -t]

theorem pontos_coord (d t : ℝ) (i : Fin 6) :
    (ATK.ClosedMath.Hexagrama.pontos d t i).re = xv d i ∧
      (ATK.ClosedMath.Hexagrama.pontos d t i).im = yv t i := by
  fin_cases i <;> simp [ATK.ClosedMath.Hexagrama.pontos, xv, yv]

theorem K6_somas (d t : ℝ) :
    ∑ i, xv d i = 0 ∧ ∑ i, yv t i = 0 ∧ ∑ i, xv d i ^ 2 = 4 * d ^ 2 ∧ ∑ i, yv t i ^ 2 = 6 * t ^ 2 ∧
      ∑ i, xv d i * yv t i = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Fin.sum_univ_six, xv, yv] <;> ring

/-- Laplaciano de `K₆`: `L = 6I − J`. -/
def L6 : Matrix (Fin 6) (Fin 6) ℝ := Matrix.of fun i j => if i = j then 5 else -1

theorem L6_mulVec (v : Fin 6 → ℝ) (i : Fin 6) : (L6.mulVec v) i = 6 * v i - ∑ j, v j := by
  simp only [L6, Matrix.mulVec, dotProduct, Matrix.of_apply]
  fin_cases i <;> simp [Fin.sum_univ_six] <;> ring

/-- **`vᵀLv = Σ_{i<j}(vᵢ − vⱼ)²`** (aqui como `½ Σ_{i,j}`). -/
theorem forma_L6 (v : Fin 6 → ℝ) :
    ∑ i, v i * (L6.mulVec v) i = (∑ i, ∑ j, (v i - v j) ^ 2) / 2 := by
  simp only [L6_mulVec, Fin.sum_univ_six]
  ring

/-- **Espectro de `K₆`**: autovalores só `0` e `6`. -/
theorem L6_autovalores {v : Fin 6 → ℝ} {μ : ℝ} (hv : v ≠ 0) (h : L6.mulVec v = μ • v) :
    μ = 0 ∨ μ = 6 := by
  by_cases h6 : μ = 6
  · exact Or.inr h6
  left
  set s := ∑ j, v j with hs
  have hi : ∀ i, (6 - μ) * v i = s := by
    intro i
    have := congrFun h i
    rw [L6_mulVec, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have h6' : 6 - μ ≠ 0 := sub_ne_zero.mpr (Ne.symm h6)
  have hc : ∀ i, v i = s / (6 - μ) := fun i => by rw [eq_div_iff h6', mul_comm]; exact hi i
  have hsum : s = 6 * (s / (6 - μ)) := by
    conv_lhs => rw [hs]
    simp only [Fin.sum_univ_six, hc]; ring
  have hs0 : s ≠ 0 := by
    intro h0
    apply hv
    funext i
    rw [hc i, h0, zero_div, Pi.zero_apply]
  have h2 : s * (6 - μ) = 6 * s := by
    have := congrArg (fun z => z * (6 - μ)) hsum
    rw [this, mul_assoc, div_mul_cancel₀ _ h6']
  have : s * μ = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hs0
  · exact h

theorem L6_constante (c : ℝ) : L6.mulVec (fun _ => c) = 0 := by
  funext i; rw [L6_mulVec]; simp

theorem L6_soma_zero {v : Fin 6 → ℝ} (hv : ∑ j, v j = 0) : L6.mulVec v = (6 : ℝ) • v := by
  funext i; rw [L6_mulVec, hv]; simp

/-- **`xᵀLx = 24d²`, `yᵀLy = 36t²`** (a energia `24d² + 36t²` de `Hexagrama.energia_pontos`). -/
theorem energias_L6 (d t : ℝ) :
    ∑ i, xv d i * (L6.mulVec (xv d)) i = 24 * d ^ 2 ∧ ∑ i, yv t i * (L6.mulVec (yv t)) i = 36 * t ^ 2 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := K6_somas d t
  constructor
  · simp only [L6_mulVec, h1, sub_zero]
    have : ∑ i, xv d i * (6 * xv d i) = 6 * ∑ i, xv d i ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, h3]; ring
  · simp only [L6_mulVec, h2, sub_zero]
    have : ∑ i, yv t i * (6 * yv t i) = 6 * ∑ i, yv t i ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, h4]; ring

/-- Rotação preserva `d² + t²`. -/
theorem rotacao (d t α : ℝ) :
    (d * Real.cos α - t * Real.sin α) ^ 2 + (d * Real.sin α + t * Real.cos α) ^ 2 = d ^ 2 + t ^ 2 := by
  have := Real.cos_sq_add_sin_sq α
  nlinarith [this]

/-- O retângulo do quarteto `½ ± d ± it` tem lados `2|d|`, `2|t|` e área `4|dt|`. -/
theorem area_quarteto (d t : ℝ) :
    dist ((1 / 2 : ℂ) + d + t * I) ((1 / 2 : ℂ) - d + t * I) *
      dist ((1 / 2 : ℂ) + d + t * I) ((1 / 2 : ℂ) + d - t * I) = 4 * |d * t| := by
  rw [dist_eq_norm, dist_eq_norm]
  have e1 : (1 / 2 : ℂ) + d + t * I - ((1 / 2 : ℂ) - d + t * I) = ((2 * d : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 / 2 : ℂ) + d + t * I - ((1 / 2 : ℂ) + d - t * I) = ((2 * t : ℝ) : ℂ) * I := by push_cast; ring
  rw [e1, e2, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
  norm_num
  ring

/-- Os geradores `R(d,t) = (−d,t)`, `C(d,t) = (d,−t)` de `ℤ/2 × ℤ/2`. -/
theorem klein_geradores (d t : ℝ) :
    ((-(-d), t) = (d, t)) ∧ ((d, -(-t)) = (d, t)) ∧ ((-d, -t) = (-(d), -(t))) := by
  simp

/-! ## 2. Métricas induzidas -/

/-- **Helicoide** `(σ cos t, σ sin t, t)`: `E = 1`, `F = 0`, `G = 1 + σ²`. -/
theorem metrica_helicoide (σ t : ℝ) :
    (HasDerivAt (fun σ => σ * Real.cos t) (Real.cos t) σ ∧ HasDerivAt (fun σ => σ * Real.sin t) (Real.sin t) σ) ∧
    (HasDerivAt (fun t => σ * Real.cos t) (-σ * Real.sin t) t ∧
      HasDerivAt (fun t => σ * Real.sin t) (σ * Real.cos t) t) ∧
    Real.cos t ^ 2 + Real.sin t ^ 2 + 0 ^ 2 = 1 ∧
    Real.cos t * (-σ * Real.sin t) + Real.sin t * (σ * Real.cos t) + 0 * 1 = 0 ∧
    (-σ * Real.sin t) ^ 2 + (σ * Real.cos t) ^ 2 + 1 ^ 2 = 1 + σ ^ 2 ∧
    0 < 1 * (1 + σ ^ 2) - 0 ^ 2 := by
  have hc := Real.cos_sq_add_sin_sq t
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, by linarith, by ring, by nlinarith, by nlinarith [sq_nonneg σ]⟩
  · simpa using (hasDerivAt_id σ).mul_const (Real.cos t)
  · simpa using (hasDerivAt_id σ).mul_const (Real.sin t)
  · have := (Real.hasDerivAt_cos t).const_mul σ; convert this using 1; ring
  · exact (Real.hasDerivAt_sin t).const_mul σ

/-- **Cilindro parabólico** `(σ, t, σ²)`: `E = 1 + 4σ²`, `F = 0`, `G = 1`. -/
theorem metrica_cilindro (σ : ℝ) :
    HasDerivAt (fun σ : ℝ => σ ^ 2) (2 * σ) σ ∧
    1 ^ 2 + 0 ^ 2 + (2 * σ) ^ 2 = 1 + 4 * σ ^ 2 ∧ 1 * 0 + 0 * 1 + 2 * σ * 0 = 0 ∧
    0 ^ 2 + 1 ^ 2 + 0 ^ 2 = 1 ∧ 0 < (1 + 4 * σ ^ 2) * 1 - 0 ^ 2 := by
  refine ⟨by simpa using hasDerivAt_pow 2 σ, by ring, by ring, by ring, by nlinarith [sq_nonneg σ]⟩

/-- **Sela** `(σ, t, σ² − t²)`: `E = 1 + 4σ²`, `F = −4σt`, `G = 1 + 4t²`, `EG − F² = 1 + 4σ² + 4t²`. -/
theorem metrica_sela (σ t : ℝ) :
    HasDerivAt (fun σ : ℝ => σ ^ 2 - t ^ 2) (2 * σ) σ ∧ HasDerivAt (fun t : ℝ => σ ^ 2 - t ^ 2) (-(2 * t)) t ∧
    1 ^ 2 + 0 ^ 2 + (2 * σ) ^ 2 = 1 + 4 * σ ^ 2 ∧ 1 * 0 + 0 * 1 + 2 * σ * (-(2 * t)) = -4 * σ * t ∧
    0 ^ 2 + 1 ^ 2 + (-(2 * t)) ^ 2 = 1 + 4 * t ^ 2 ∧
    (1 + 4 * σ ^ 2) * (1 + 4 * t ^ 2) - (-4 * σ * t) ^ 2 = 1 + 4 * σ ^ 2 + 4 * t ^ 2 ∧
    0 < (1 + 4 * σ ^ 2) * (1 + 4 * t ^ 2) - (-4 * σ * t) ^ 2 := by
  refine ⟨by simpa using (hasDerivAt_pow 2 σ).sub_const (t ^ 2), ?_, by ring, by ring, by ring, by ring, ?_⟩
  · simpa using ((hasDerivAt_pow 2 t).const_sub (σ ^ 2))
  · nlinarith [sq_nonneg σ, sq_nonneg t]

/-- **Hiperboloide** `(cosh t cos σ, cosh t sin σ, sinh t)`: `E = cosh²t`, `F = 0`, `G = cosh 2t`. -/
theorem metrica_hiperboloide (σ t : ℝ) :
    (Real.cosh t * Real.sin σ) ^ 2 + (Real.cosh t * Real.cos σ) ^ 2 + 0 ^ 2 = Real.cosh t ^ 2 ∧
    (-(Real.cosh t * Real.sin σ)) * (Real.sinh t * Real.cos σ) +
      (Real.cosh t * Real.cos σ) * (Real.sinh t * Real.sin σ) + 0 * Real.cosh t = 0 ∧
    (Real.sinh t * Real.cos σ) ^ 2 + (Real.sinh t * Real.sin σ) ^ 2 + Real.cosh t ^ 2 = Real.cosh (2 * t) ∧
    0 < Real.cosh t ^ 2 * Real.cosh (2 * t) - 0 ^ 2 := by
  have hc := Real.cos_sq_add_sin_sq σ
  have h2 : Real.cosh (2 * t) = Real.sinh t ^ 2 + Real.cosh t ^ 2 := by
    rw [Real.cosh_two_mul]; ring
  refine ⟨by nlinarith, by ring, by rw [h2]; nlinarith, ?_⟩
  have h1 := Real.cosh_pos t
  have h3 := Real.cosh_pos (2 * t)
  nlinarith [mul_pos (pow_pos h1 2) h3]

theorem derivadas_hiperboloide (σ t : ℝ) :
    HasDerivAt (fun σ => Real.cosh t * Real.cos σ) (-(Real.cosh t * Real.sin σ)) σ ∧
    HasDerivAt (fun σ => Real.cosh t * Real.sin σ) (Real.cosh t * Real.cos σ) σ ∧
    HasDerivAt (fun t => Real.cosh t * Real.cos σ) (Real.sinh t * Real.cos σ) t ∧
    HasDerivAt (fun t => Real.cosh t * Real.sin σ) (Real.sinh t * Real.sin σ) t ∧
    HasDerivAt Real.sinh (Real.cosh t) t := by
  refine ⟨?_, (Real.hasDerivAt_sin σ).const_mul _, (Real.hasDerivAt_cosh t).mul_const _,
    (Real.hasDerivAt_cosh t).mul_const _, Real.hasDerivAt_sinh t⟩
  have := (Real.hasDerivAt_cos σ).const_mul (Real.cosh t); convert this using 1; ring

/-! ## 3. Jensen montado com `aₙ`: contraexemplo -/

/-- `Θ(x) = 1 + 2x + 2x²` tem o zero não real `(−1 + i)/2`. -/
theorem Theta_nao_real : (1 : ℂ) + 2 * ((-1 + I) / 2) + 2 * ((-1 + I) / 2) ^ 2 = 0 ∧
    ((-1 + I) / 2 : ℂ).im ≠ 0 := by
  constructor
  · ring_nf; rw [I_sq]; ring
  · simp

/-- Com `a = (1, 2, 2)`, `J_{N,0}(X) = 1 + 2NX + N(N−1)X²` tem discriminante `4N > 0`: duas raízes
reais distintas para `N ≥ 2` (e `J_{N,k}`, `k ≥ 1`, tem grau `≤ 1`). -/
theorem jensen_a_hiperbolico {N : ℕ} (hN : 2 ≤ N) :
    discrim ((N : ℝ) * (N - 1)) (2 * N) 1 = 4 * N ∧
    ∃ x₁ x₂ : ℝ, x₁ ≠ x₂ ∧ (N : ℝ) * (N - 1) * x₁ ^ 2 + 2 * N * x₁ + 1 = 0 ∧
      (N : ℝ) * (N - 1) * x₂ ^ 2 + 2 * N * x₂ + 1 = 0 := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hd : discrim ((N : ℝ) * (N - 1)) (2 * N) 1 = 4 * N := by unfold discrim; ring
  refine ⟨hd, ?_⟩
  have ha : (N : ℝ) * (N - 1) ≠ 0 := by
    apply mul_ne_zero <;> linarith
  set s := Real.sqrt (4 * N) with hs
  have hss : discrim ((N : ℝ) * (N - 1)) (2 * N) 1 = s * s := by
    rw [hd, hs, Real.mul_self_sqrt (by positivity)]
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  refine ⟨(-(2 * N) + s) / (2 * ((N : ℝ) * (N - 1))), (-(2 * N) - s) / (2 * ((N : ℝ) * (N - 1))), ?_, ?_, ?_⟩
  · intro h
    have h2 : (2 * ((N : ℝ) * (N - 1))) ≠ 0 := mul_ne_zero two_ne_zero ha
    rw [div_left_inj' h2] at h
    linarith
  · have := (quadratic_eq_zero_iff ha hss ((-(2 * N) + s) / (2 * ((N : ℝ) * (N - 1))))).mpr (Or.inl rfl)
    rw [← this]; ring
  · have := (quadratic_eq_zero_iff ha hss ((-(2 * N) - s) / (2 * ((N : ℝ) * (N - 1))))).mpr (Or.inr rfl)
    rw [← this]; ring

/-- Com `γ = (1, 2, 4)`, `J_{3,0}(X) = 1 + 6X + 12X²` **não** tem raiz real. -/
theorem jensen_gamma_detecta (x : ℝ) : 1 + 6 * x + 12 * x ^ 2 ≠ 0 := by
  nlinarith [sq_nonneg (x + 1 / 4)]

/-! ## 4. A família de cruzamento sem `γ ≠ 0` -/

/-- Com `γ = 0` e `λ ≠ 0`, `½ + λ` é zero **duplo** (não simples). -/
theorem cruzamento_gamma_zero {l : ℝ} (hl : l ≠ 0) :
    (ATK.ClosedMath.Gpoly l 0).rootMultiplicity ((1 / 2 : ℂ) + (l : ℂ)) = 2 := by
  classical
  rw [← Polynomial.count_roots, ATK.ClosedMath.Gpoly_roots]
  have h3 : ((1 / 2 : ℂ) + (l : ℂ)) ≠ 1 / 2 - l := by
    intro h; have := congrArg Complex.re h; simp at this; exact hl (by linarith)
  have h3' : (2⁻¹ : ℂ) + l ≠ 2⁻¹ - l := by simpa [one_div] using h3
  simp [ATK.ClosedMath.raizes, h3']

/-- Com `λ = γ = 0`, `½` é zero **quádruplo** (não dois zeros duplos distintos). -/
theorem cruzamento_tudo_zero : (ATK.ClosedMath.Gpoly 0 0).rootMultiplicity (1 / 2 : ℂ) = 4 := by
  classical
  rw [← Polynomial.count_roots, ATK.ClosedMath.Gpoly_roots]
  simp [ATK.ClosedMath.raizes]

/-! ## 5. "HR ⇏ O1" é mal posto -/

/-- Provar `¬(HR → Q)` (para qualquer `Q`) provaria HR. -/
theorem nao_implica_prova_rh (Q : Prop) (h : ¬ (RiemannHypothesis → Q)) : RiemannHypothesis ∧ ¬ Q := by
  by_contra h'
  apply h
  intro hRH
  by_contra hQ
  exact h' ⟨hRH, hQ⟩

/-! ## 6. Fourier no toro -/

theorem integral_exp_int (k : ℤ) :
    ∫ x in (0 : ℝ)..(2 * π), Complex.exp (k * I * x) = if k = 0 then (2 * π : ℂ) else 0 := by
  split_ifs with hk
  · subst hk; simp
  · have hc : (k : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) I_ne_zero
    have h := integral_exp_mul_complex (a := 0) (b := 2 * π) hc
    have e : (fun x : ℝ => Complex.exp ((k : ℂ) * I * x)) = fun x : ℝ => Complex.exp ((k : ℂ) * I * (x : ℂ)) := rfl
    rw [e, h]
    have h2 : Complex.exp ((k : ℂ) * I * ((2 * π : ℝ) : ℂ)) = 1 := by
      rw [show (k : ℂ) * I * ((2 * π : ℝ) : ℂ) = (k : ℂ) * (2 * π * I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [h2]
    simp

/-- `e_{m,n}(x,y) = e^{i(mx+ny)}/(2π)`. -/
noncomputable def efun (m n : ℤ) (x y : ℝ) : ℂ := Complex.exp (I * (m * x + n * y)) / (2 * π)

theorem efun_prod (m n m' n' : ℤ) (x y : ℝ) :
    efun m n x y * (starRingEnd ℂ) (efun m' n' x y) =
      Complex.exp (((m - m' : ℤ) : ℂ) * I * x) * Complex.exp (((n - n' : ℤ) : ℂ) * I * y) / (4 * π ^ 2) := by
  unfold efun
  have c1 : (starRingEnd ℂ) (2 * (π : ℂ)) = 2 * π := by
    rw [map_mul, Complex.conj_ofReal, map_ofNat]
  have c2 : (starRingEnd ℂ) (I * ((m' : ℂ) * x + n' * y)) = -(I * ((m' : ℂ) * x + n' * y)) := by
    simp [map_mul, map_add, Complex.conj_I, Complex.conj_ofReal]
  rw [map_div₀, ← Complex.exp_conj, c1, c2, div_mul_div_comm, ← Complex.exp_add, ← Complex.exp_add]
  have e1 : I * ((m : ℂ) * x + n * y) + -(I * ((m' : ℂ) * x + n' * y)) =
      ((m - m' : ℤ) : ℂ) * I * x + ((n - n' : ℤ) : ℂ) * I * y := by push_cast; ring
  have e2 : (2 * (π : ℂ)) * (2 * π) = 4 * π ^ 2 := by ring
  rw [e1, e2]

/-- **`e_{m,n}` é ortonormal em `[0,2π]²`.** -/
theorem fourier_toro (m n m' n' : ℤ) :
    ∫ x in (0 : ℝ)..(2 * π), ∫ y in (0 : ℝ)..(2 * π), efun m n x y * (starRingEnd ℂ) (efun m' n' x y) =
      if m = m' ∧ n = n' then 1 else 0 := by
  simp_rw [efun_prod, div_eq_mul_inv]
  simp_rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const]
  rw [integral_exp_int, integral_exp_int]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases h1 : m = m' <;> by_cases h2 : n = n' <;> simp [h1, h2, sub_eq_zero] <;> (field_simp; ring)

/-! ## 7. Energia cinética gaussiana -/

/-- `ψ(x) = (α/π)^{1/4} e^{−αx²/2}`. -/
noncomputable def psi (α x : ℝ) : ℝ := (α / π) ^ (1 / 4 : ℝ) * Real.exp (-(α * x ^ 2) / 2)

theorem psi_sq (α x : ℝ) (hα : 0 < α) : psi α x ^ 2 = Real.sqrt (α / π) * Real.exp (-α * x ^ 2) := by
  unfold psi
  have h1 : ((α / π) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (α / π) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.sqrt_eq_rpow]; norm_num
  have h2 : Real.exp (-(α * x ^ 2) / 2) ^ 2 = Real.exp (-α * x ^ 2) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [mul_pow, h1, h2]

theorem deriv_psi (α x : ℝ) : HasDerivAt (psi α) (-(α * x) * psi α x) x := by
  unfold psi
  have h : HasDerivAt (fun x : ℝ => -(α * x ^ 2) / 2) (-(α * x)) x := by
    have := ((hasDerivAt_pow 2 x).const_mul α).neg.div_const 2
    convert this using 1; push_cast; ring
  have := (h.exp).const_mul ((α / π) ^ (1 / 4 : ℝ))
  convert this using 1; ring

/-- **`∫ψ² = 1`.** -/
theorem psi_normalizada {α : ℝ} (hα : 0 < α) : ∫ x, psi α x ^ 2 = 1 := by
  simp_rw [psi_sq _ _ hα]
  rw [integral_const_mul, integral_gaussian]
  rw [← Real.sqrt_mul (by positivity)]
  rw [show α / π * (π / α) = 1 by field_simp]
  simp

/-- `∫ x² e^{−αx²} = √π/(2α^{3/2})`, via a integral Gama em `(0, ∞)` e paridade. -/
theorem momento_dois {α : ℝ} (hα : 0 < α) :
    ∫ x, x ^ 2 * Real.exp (-α * x ^ 2) = Real.sqrt π / (2 * α * Real.sqrt α) := by
  have hev : (fun x : ℝ => x ^ 2 * Real.exp (-α * x ^ 2)) =
      fun x => (fun y : ℝ => y ^ (2 : ℝ) * Real.exp (-α * y ^ (2 : ℝ))) |x| := by
    funext x
    simp only [Real.rpow_two, sq_abs]
  rw [hev, integral_comp_abs (f := fun y : ℝ => y ^ (2 : ℝ) * Real.exp (-α * y ^ (2 : ℝ))),
    _root_.integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hα]
  have hG : Real.Gamma ((2 + 1) / 2) = Real.sqrt π / 2 := by
    rw [show ((2 : ℝ) + 1) / 2 = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  rw [hG]
  have hr : α ^ (-((2 : ℝ) + 1) / 2) = 1 / (α * Real.sqrt α) := by
    rw [show -((2 : ℝ) + 1) / 2 = -(1 + 1 / 2) by norm_num, Real.rpow_neg hα.le,
      Real.rpow_add hα, Real.rpow_one, ← Real.sqrt_eq_rpow]
    field_simp
  rw [hr]
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  field_simp

/-- **Energia cinética `½∫(ψ′)² = α/4`.** -/
theorem energia_cinetica {α : ℝ} (hα : 0 < α) : 1 / 2 * ∫ x, (-(α * x) * psi α x) ^ 2 = α / 4 := by
  have e : (fun x => (-(α * x) * psi α x) ^ 2) =
      fun x => α ^ 2 * Real.sqrt (α / π) * (x ^ 2 * Real.exp (-α * x ^ 2)) := by
    funext x
    rw [mul_pow, psi_sq _ _ hα]
    ring
  rw [e, integral_const_mul, momento_dois hα]
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  rw [Real.sqrt_div hα.le]
  field_simp
  norm_num

end ATK.GeometriaExtra

-- Auditoria de axiomas (kernel)
#print axioms ATK.GeometriaExtra.pontos_coord
#print axioms ATK.GeometriaExtra.K6_somas
#print axioms ATK.GeometriaExtra.L6_mulVec
#print axioms ATK.GeometriaExtra.forma_L6
#print axioms ATK.GeometriaExtra.L6_autovalores
#print axioms ATK.GeometriaExtra.L6_constante
#print axioms ATK.GeometriaExtra.L6_soma_zero
#print axioms ATK.GeometriaExtra.energias_L6
#print axioms ATK.GeometriaExtra.rotacao
#print axioms ATK.GeometriaExtra.area_quarteto
#print axioms ATK.GeometriaExtra.klein_geradores
#print axioms ATK.GeometriaExtra.metrica_helicoide
#print axioms ATK.GeometriaExtra.metrica_cilindro
#print axioms ATK.GeometriaExtra.metrica_sela
#print axioms ATK.GeometriaExtra.metrica_hiperboloide
#print axioms ATK.GeometriaExtra.derivadas_hiperboloide
#print axioms ATK.GeometriaExtra.Theta_nao_real
#print axioms ATK.GeometriaExtra.jensen_a_hiperbolico
#print axioms ATK.GeometriaExtra.jensen_gamma_detecta
#print axioms ATK.GeometriaExtra.cruzamento_gamma_zero
#print axioms ATK.GeometriaExtra.cruzamento_tudo_zero
#print axioms ATK.GeometriaExtra.nao_implica_prova_rh
#print axioms ATK.GeometriaExtra.integral_exp_int
#print axioms ATK.GeometriaExtra.efun_prod
#print axioms ATK.GeometriaExtra.fourier_toro
#print axioms ATK.GeometriaExtra.psi_sq
#print axioms ATK.GeometriaExtra.deriv_psi
#print axioms ATK.GeometriaExtra.psi_normalizada
#print axioms ATK.GeometriaExtra.momento_dois
#print axioms ATK.GeometriaExtra.energia_cinetica
