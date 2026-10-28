import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# ATK — Os modelos finitos das sete linhas, certificados

Os cálculos "exatos no modelo" dos textos anexados, verificados no kernel. Cada valor pertence ao
modelo indicado — **nenhum** é uma constante das conjecturas (ver `MODELOS_TERMINAIS.md`).

* **RH (Gram 2×2)**: `G = [[2,1],[1,2]]`, `det G = 3`, `G⁻¹`, `c = G⁻¹b = (1/3, −1/6)`, `Gc = b`,
  `bᵀG⁻¹b = 1/6`, **`D₂ = 5/6`**; `D₂ = 5/6 ⟺ b₁² − b₁b₂ + b₂² = 1/4`; `1/6 ≤ ‖b‖² ≤ 1/2`.
  (O `D₂` real de Báez-Duarte é `0,28996…`: o modelo **não** é a sequência concreta.)
* **NS**: margem `5/12`, absorção `X ≤ (12/5)F`, robustez `ε < 5/24`, derivada da amplificação
  `144/25`, Riccati com `C = 1/5`, `y₀ = 1`: `y(t) ≤ 1/(1 − 2t/5)` (valores `5`, `25`).
* **YM**: `H = diag(0,1,2)`: gap `1` (quociente de Rayleigh), `Z(log 2) = 7/4`, `⟨E⟩ = 4/7`,
  `Var E = 26/49`, decaimento `≤ e^{−2t}`, integral `a²/2 + b²/4 ∈ [1/4, 1/2]`.
* **BSD (matriz)**: `H = [[2,1],[1,3]]`: `det 5`, `tr 5`, inversa, polinômio `λ² − 5λ + 5`,
  positividade, `Q ≥ ((5−√5)/2)‖v‖²`, `h₂₂ = (R + h₁₂²)/h₁₁`, perturbação `|ΔR| ≤ 7ε + 2ε²`,
  robustez `−1−√6 < ε < −1+√6`.
* **Hodge (álgebra linear do mapa de ciclos)**: `Mc = α` no modelo; posto + nulidade; sobrejetiva
  ⟺ posto `= d`; sobrejetiva ⇒ `d ≤ m`; soluções `= c₀ + ker`.
* **P ≠ NP**: `(nᵏ)ˡ = n^{kl}`, `(2n)¹² = 4096 n¹²`, composição de cotas polinomiais.
* **Geometria**: volumes exatos das bolas unitárias `π²/2` (4D), `8π²/15` (5D), `64π⁵/10395` (11D);
  cubo inscrito em 11D `∈ (0,00383; 0,00384)` (corrige `0,003815`); cone `∫₀¹ t^{d−1} = 1/d`;
  gap do toro plano `|k|² ≥ 1`.
* **Infinitesimais formais**: `(1+2ε)(1−3ε) = 1 − ε − 6ε²`; `(1−ε)Σ_{i<n} εⁱ = 1 − εⁿ`.
-/

open Matrix Real MeasureTheory Set

namespace ATK.ModelosSete

/-! ## RH — o modelo de Gram 2×2 -/

/-- Matriz de Gram do modelo. -/
def G : Matrix (Fin 2) (Fin 2) ℚ := !![2, 1; 1, 2]
/-- Sua inversa. -/
def Ginv : Matrix (Fin 2) (Fin 2) ℚ := !![2 / 3, -1 / 3; -1 / 3, 2 / 3]
/-- Vetor de produtos internos do modelo. -/
def bvec : Fin 2 → ℚ := ![1 / 2, 0]

theorem G_det : G.det = 3 := by rw [G, Matrix.det_fin_two_of]; norm_num

theorem G_mul_Ginv : G * Ginv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [G, Ginv, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem coeficientes : Ginv *ᵥ bvec = ![1 / 3, -1 / 6] := by
  ext i; fin_cases i <;> simp [Ginv, bvec, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- Resíduo linear zero: `G c = b`. -/
theorem residuo_linear : G *ᵥ ![1 / 3, -1 / 6] = bvec := by
  ext i; fin_cases i <;> simp [G, bvec, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- Energia projetada `bᵀG⁻¹b = 1/6`. -/
theorem energia_projetada : bvec ⬝ᵥ (Ginv *ᵥ bvec) = 1 / 6 := by
  rw [coeficientes]; simp [bvec, dotProduct, Fin.sum_univ_two]; norm_num

/-- **`D₂ = 5/6` no modelo.** -/
theorem D2_modelo : 1 - bvec ⬝ᵥ (Ginv *ᵥ bvec) = 5 / 6 := by rw [energia_projetada]; norm_num

theorem D2_formula (b₁ b₂ : ℚ) :
    1 - ![b₁, b₂] ⬝ᵥ (Ginv *ᵥ ![b₁, b₂]) = 1 - 2 / 3 * (b₁ ^ 2 - b₁ * b₂ + b₂ ^ 2) := by
  simp [Ginv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]; ring

/-- `D₂ = 5/6 ⟺ b₁² − b₁b₂ + b₂² = 1/4` (a família de vetores compatíveis). -/
theorem D2_iff (b₁ b₂ : ℚ) :
    1 - ![b₁, b₂] ⬝ᵥ (Ginv *ᵥ ![b₁, b₂]) = 5 / 6 ↔ b₁ ^ 2 - b₁ * b₂ + b₂ ^ 2 = 1 / 4 := by
  rw [D2_formula]; constructor <;> intro h <;> linarith

/-- Na família compatível, `1/6 ≤ b₁² + b₂² ≤ 1/2`. -/
theorem norma_b {b₁ b₂ : ℝ} (h : b₁ ^ 2 - b₁ * b₂ + b₂ ^ 2 = 1 / 4) :
    1 / 6 ≤ b₁ ^ 2 + b₂ ^ 2 ∧ b₁ ^ 2 + b₂ ^ 2 ≤ 1 / 2 := by
  constructor <;> nlinarith [sq_nonneg (b₁ - b₂), sq_nonneg (b₁ + b₂)]

/-! ## Navier–Stokes — o modelo de absorção -/

theorem margem_modelo : (1 : ℝ) - 1 / 4 - 1 / 3 = 5 / 12 := by norm_num

theorem absorcao_modelo {X F : ℝ} (h : X ≤ (1 / 4 + 1 / 3) * X + F) : X ≤ 12 / 5 * F := by
  linarith

/-- Robustez: aumentar as duas constantes em `ε` mantém a absorção ⟺ `ε < 5/24`. -/
theorem robustez_absorcao (ε : ℝ) : 1 / 4 + ε + (1 / 3 + ε) < 1 ↔ ε < 5 / 24 := by
  constructor <;> intro h <;> linarith

/-- Derivada da amplificação `A(s) = 1/(5/12 − s)` em `0`: `(12/5)² = 144/25`. -/
theorem amplificacao_deriv : HasDerivAt (fun s : ℝ => 1 / (5 / 12 - s)) (144 / 25) 0 := by
  have h := ((hasDerivAt_id (0 : ℝ)).const_sub (5 / 12 : ℝ)).inv (by norm_num)
  simp only [id, one_div] at h ⊢
  convert h using 1
  norm_num

/-- A cota de Riccati do modelo (`C = 1/5`, `y₀ = 1`) é a solução exata de `B' = (2/5)B²`, que
explode em `t = 5/2`; a comparação `y ≤ B` é `ATK.NavierStokes.riccati_upper_bound`. -/
theorem riccati_solucao {t : ℝ} (ht : t < 5 / 2) :
    HasDerivAt (fun s : ℝ => 1 / (1 - 2 / 5 * s)) (2 / 5 * (1 / (1 - 2 / 5 * t)) ^ 2) t := by
  have hne : (1 : ℝ) - 2 / 5 * t ≠ 0 := by intro h; linarith
  have h := (((hasDerivAt_id t).const_mul (2 / 5 : ℝ)).const_sub (1 : ℝ)).inv hne
  simp only [id, one_div] at h ⊢
  convert h using 1
  field_simp

theorem riccati_valores :
    (1 : ℝ) / (1 - 2 / 5 * 2) = 5 ∧ (1 : ℝ) / (1 - 2 / 5 * (12 / 5)) = 25 := by norm_num

/-! ## Yang–Mills — o Hamiltoniano `diag(0,1,2)` -/

/-- Forma quadrática de `H = diag(0,1,2)`. -/
def QH (ψ : Fin 3 → ℝ) : ℝ := 0 * ψ 0 ^ 2 + 1 * ψ 1 ^ 2 + 2 * ψ 2 ^ 2
/-- Norma ao quadrado. -/
def nrm (ψ : Fin 3 → ℝ) : ℝ := ψ 0 ^ 2 + ψ 1 ^ 2 + ψ 2 ^ 2

/-- **Gap do modelo**: para `ψ ⊥ vácuo`, `‖ψ‖² ≤ ⟨ψ,Hψ⟩ ≤ 2‖ψ‖²`. -/
theorem gap_modelo (ψ : Fin 3 → ℝ) (h0 : ψ 0 = 0) : nrm ψ ≤ QH ψ ∧ QH ψ ≤ 2 * nrm ψ := by
  unfold nrm QH; rw [h0]; constructor <;> nlinarith [sq_nonneg (ψ 1), sq_nonneg (ψ 2)]

/-- O gap `1` é atingido em `e₁`. -/
theorem gap_atingido : QH ![0, 1, 0] = 1 ∧ nrm ![0, 1, 0] = 1 := by
  simp [QH, nrm]

theorem exp_neg_log_dois : Real.exp (-Real.log 2) = 1 / 2 := by
  rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

theorem exp_neg_dois_log_dois : Real.exp (-(2 * Real.log 2)) = 1 / 4 := by
  rw [show 2 * Real.log 2 = Real.log 4 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num]
  rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num

/-- **Função de partição** `Z(log 2) = 7/4`. -/
theorem particao : 1 + Real.exp (-Real.log 2) + Real.exp (-(2 * Real.log 2)) = 7 / 4 := by
  rw [exp_neg_log_dois, exp_neg_dois_log_dois]; norm_num

/-- **Energia média** `4/7` e **variância** `26/49`. -/
theorem energia_variancia :
    (0 * 1 + 1 * Real.exp (-Real.log 2) + 2 * Real.exp (-(2 * Real.log 2))) / (7 / 4) = 4 / 7 ∧
      (0 * 1 + 1 * Real.exp (-Real.log 2) + 4 * Real.exp (-(2 * Real.log 2))) / (7 / 4) -
        (4 / 7) ^ 2 = 26 / 49 := by
  rw [exp_neg_log_dois, exp_neg_dois_log_dois]; norm_num

/-- **Decaimento**: `‖e^{−tH}ψ‖² ≤ e^{−2t}‖ψ‖²` para `ψ = (0, a, b)`. -/
theorem decaimento (a b : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-2 * t) * a ^ 2 + Real.exp (-4 * t) * b ^ 2 ≤ Real.exp (-2 * t) * (a ^ 2 + b ^ 2) := by
  have : Real.exp (-4 * t) ≤ Real.exp (-2 * t) := Real.exp_le_exp.2 (by linarith)
  nlinarith [sq_nonneg b]

/-- Integral do decaimento normalizado: `a²/2 + b²/4 ∈ [1/4, 1/2]` quando `a² + b² = 1`. -/
theorem integral_limites {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) :
    1 / 4 ≤ a ^ 2 / 2 + b ^ 2 / 4 ∧ a ^ 2 / 2 + b ^ 2 / 4 ≤ 1 / 2 := by
  constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]

theorem integral_exp_dois : ∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) = 1 / 2 := by
  rw [integral_exp_mul_Ioi (by norm_num) 0]; norm_num

theorem integral_exp_quatro : ∫ t in Ioi (0 : ℝ), Real.exp (-4 * t) = 1 / 4 := by
  rw [integral_exp_mul_Ioi (by norm_num) 0]; norm_num

/-! ## BSD — a matriz de alturas do modelo -/

/-- Matriz de alturas do modelo. -/
def Hb : Matrix (Fin 2) (Fin 2) ℚ := !![2, 1; 1, 3]

theorem Hb_det : Hb.det = 5 := by rw [Hb, Matrix.det_fin_two_of]; norm_num

theorem Hb_traco : Hb.trace = 5 := by
  simp [Hb, Matrix.trace, Fin.sum_univ_two]; norm_num

theorem Hb_inversa : Hb * !![3 / 5, -1 / 5; -1 / 5, 2 / 5] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Hb, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- Polinômio característico `λ² − 5λ + 5`. -/
theorem Hb_caracteristico (l : ℚ) : (Hb - l • 1).det = l ^ 2 - 5 * l + 5 := by
  rw [Matrix.det_fin_two]; simp [Hb]; ring

theorem forma_quadratica (x y : ℝ) :
    2 * x ^ 2 + 2 * x * y + 3 * y ^ 2 = 2 * (x + y / 2) ^ 2 + 5 / 2 * y ^ 2 := by ring

/-- **Positividade**. -/
theorem Hb_positiva {x y : ℝ} (h : x ≠ 0 ∨ y ≠ 0) : 0 < 2 * x ^ 2 + 2 * x * y + 3 * y ^ 2 := by
  rw [forma_quadratica]
  rcases h with h | h
  · by_cases hy : y = 0
    · subst hy; have : 0 < x ^ 2 := by positivity
      nlinarith
    · have : 0 < y ^ 2 := by positivity
      nlinarith [sq_nonneg (x + y / 2)]
  · have : 0 < y ^ 2 := by positivity
    nlinarith [sq_nonneg (x + y / 2)]

/-- **Menor autovalor**: `Q(x,y) ≥ ((5 − √5)/2)(x² + y²)`. -/
theorem Hb_autovalor_min (x y : ℝ) :
    (5 - Real.sqrt 5) / 2 * (x ^ 2 + y ^ 2) ≤ 2 * x ^ 2 + 2 * x * y + 3 * y ^ 2 := by
  set l := (5 - Real.sqrt 5) / 2 with hl
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt 5 < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs1 : 1 < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hl2 : 0 < 2 - l := by rw [hl]; linarith
  have hprod : (2 - l) * (3 - l) = 1 := by rw [hl]; nlinarith
  have key : (2 - l) * ((2 - l) * x ^ 2 + 2 * x * y + (3 - l) * y ^ 2) =
      ((2 - l) * x + y) ^ 2 := by nlinarith
  have hnn : 0 ≤ (2 - l) * x ^ 2 + 2 * x * y + (3 - l) * y ^ 2 := by
    by_contra hc; push Not at hc
    have : (2 - l) * ((2 - l) * x ^ 2 + 2 * x * y + (3 - l) * y ^ 2) < 0 :=
      mul_neg_of_pos_of_neg hl2 hc
    nlinarith [sq_nonneg ((2 - l) * x + y)]
  nlinarith

/-- `h₂₂ = (R + h₁₂²)/h₁₁`. -/
theorem h22_iff {h11 h12 h22 R : ℝ} (h : h11 ≠ 0) :
    h11 * h22 - h12 ^ 2 = R ↔ h22 = (R + h12 ^ 2) / h11 := by
  rw [eq_div_iff h]; constructor <;> intro e <;> linarith

/-- Perturbação do determinante. -/
theorem perturbacao (e11 e12 e22 : ℝ) :
    (2 + e11) * (3 + e22) - (1 + e12) ^ 2 - 5 = 3 * e11 + 2 * e22 - 2 * e12 + e11 * e22 - e12 ^ 2 := by
  ring

/-- **Tolerância**: entradas com erro `≤ ε` ⇒ `|ΔR| ≤ 7ε + 2ε²`. -/
theorem perturbacao_cota {e11 e12 e22 ε : ℝ} (h1 : |e11| ≤ ε) (h2 : |e12| ≤ ε) (h3 : |e22| ≤ ε) :
    |(2 + e11) * (3 + e22) - (1 + e12) ^ 2 - 5| ≤ 7 * ε + 2 * ε ^ 2 := by
  rw [perturbacao]
  have a1 : |e11 * e22| ≤ ε ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul h1 h3 (abs_nonneg _) ((abs_nonneg _).trans h1)
  have a2 : |e12 ^ 2| ≤ ε ^ 2 := by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  calc |3 * e11 + 2 * e22 - 2 * e12 + e11 * e22 - e12 ^ 2|
      ≤ |3 * e11| + |2 * e22| + |2 * e12| + |e11 * e22| + |e12 ^ 2| := by
        have := abs_add_le (3 * e11 + 2 * e22 - 2 * e12 + e11 * e22) (-(e12 ^ 2))
        have := abs_add_le (3 * e11 + 2 * e22 - 2 * e12) (e11 * e22)
        have := abs_sub (3 * e11 + 2 * e22) (2 * e12)
        have := abs_add_le (3 * e11) (2 * e22)
        rw [abs_neg] at *
        simp only [sub_eq_add_neg] at *
        linarith
    _ ≤ 3 * ε + 2 * ε + 2 * ε + ε ^ 2 + ε ^ 2 := by
        have t1 : |3 * e11| = 3 * |e11| := by rw [abs_mul]; norm_num
        have t2 : |2 * e22| = 2 * |e22| := by rw [abs_mul]; norm_num
        have t3 : |2 * e12| = 2 * |e12| := by rw [abs_mul]; norm_num
        rw [t1, t2, t3]; linarith
    _ = 7 * ε + 2 * ε ^ 2 := by ring

/-- **Robustez**: `5 − 2ε − ε² > 0 ⟺ −1 − √6 < ε < −1 + √6`. -/
theorem robustez_regulador (ε : ℝ) :
    0 < 5 - 2 * ε - ε ^ 2 ↔ -1 - Real.sqrt 6 < ε ∧ ε < -1 + Real.sqrt 6 := by
  have e : 5 - 2 * ε - ε ^ 2 = 6 - (ε + 1) ^ 2 := by ring
  rw [e, sub_pos, Real.sq_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-! ## Hodge — a álgebra linear do mapa de ciclos -/

/-- No modelo: `M c = α` com `M = [[2,1],[1,3]]`, `α = (1,2)`, `c = (1/5, 3/5)`. -/
theorem hodge_modelo : Hb *ᵥ ![1 / 5, 3 / 5] = ![1, 2] := by
  ext i; fin_cases i <;> simp [Hb, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

section Hodge
set_option linter.unusedSectionVars false
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Posto + nulidade `= m`. -/
theorem posto_nulidade (f : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.ker f) = Module.finrank K V :=
  LinearMap.finrank_range_add_finrank_ker f

/-- Sobrejetiva ⟺ posto `= d` (déficit zero). -/
theorem sobrejetiva_iff (f : V →ₗ[K] W) :
    Function.Surjective f ↔ Module.finrank K (LinearMap.range f) = Module.finrank K W := by
  rw [← LinearMap.range_eq_top]
  constructor
  · intro h; rw [h, finrank_top]
  · intro h; exact Submodule.eq_top_of_finrank_eq h

/-- Para cobrir todas as classes é preciso `d ≤ m`. -/
theorem precisa_m_ge_d (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    Module.finrank K W ≤ Module.finrank K V := by
  rw [← (sobrejetiva_iff f).1 hf]; exact LinearMap.finrank_range_le f

/-- Todas as soluções: `c₀ + ker M`. -/
theorem solucoes_afins (f : V →ₗ[K] W) {c₀ : V} {α : W} (h₀ : f c₀ = α) (c : V) :
    f c = α ↔ c - c₀ ∈ LinearMap.ker f := by
  rw [LinearMap.mem_ker, map_sub, h₀, sub_eq_zero]

end Hodge

/-! ## P ≠ NP — composição de cotas -/

theorem composicao_expoente (n k l : ℕ) : (n ^ k) ^ l = n ^ (k * l) := (pow_mul n k l).symm

theorem duplicacao (n : ℕ) : (2 * n) ^ 12 = 4096 * n ^ 12 := by ring

/-- Composição de cotas polinomiais: `g(f(n)) ≤ D·Cˡ·n^{kl}`. -/
theorem composicao_cota {f g : ℕ → ℕ} {C D k l : ℕ} (hg : Monotone g)
    (hf : ∀ n, f n ≤ C * n ^ k) (hgb : ∀ m, g m ≤ D * m ^ l) (n : ℕ) :
    g (f n) ≤ D * C ^ l * n ^ (k * l) := by
  calc g (f n) ≤ g (C * n ^ k) := hg (hf n)
    _ ≤ D * (C * n ^ k) ^ l := hgb _
    _ = D * C ^ l * n ^ (k * l) := by rw [mul_pow, ← pow_mul]; ring

theorem busca_cauda : 2 ^ 11 - 1000 = 1048 ∧ (1048 : ℚ) / 2048 = 131 / 256 := by norm_num

/-! ## Geometria em 4, 5 e 11 dimensões -/

theorem volume_bola_4 :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1) = ENNReal.ofReal (π ^ 2 / 2) := by
  rw [InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)]
  simp [Nat.factorial]

theorem volume_bola_5 :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 5)) 1) = ENNReal.ofReal (8 * π ^ 2 / 15) := by
  rw [InnerProductSpace.volume_ball_of_dim_odd (k := 2) (by simp)]
  simp [Nat.doubleFactorial]
  ring_nf

theorem volume_bola_11 :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 11)) 1) = ENNReal.ofReal (64 * π ^ 5 / 10395) := by
  rw [InnerProductSpace.volume_ball_of_dim_odd (k := 5) (by simp)]
  simp [Nat.doubleFactorial]
  ring_nf

theorem cubo_inscrito_4 : (2 / Real.sqrt 4) ^ 4 = 1 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num

/-- Cubo inscrito na bola unitária de dimensão 11: volume `∈ (0,00383; 0,00384)`. -/
theorem cubo_inscrito_11 :
    (0.00383 : ℝ) < (2 / Real.sqrt 11) ^ 11 ∧ (2 / Real.sqrt 11) ^ 11 < 0.00384 := by
  set s := Real.sqrt 11 with hsdef
  have hs2 : s ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by norm_num)
  have h1 : (3.31662 : ℝ) < s := by rw [hsdef, Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : s < 3.31663 := by rw [hsdef, Real.sqrt_lt' (by norm_num)]; norm_num
  have e : (2 / s) ^ 11 = 2048 / (161051 * s) := by
    rw [div_pow]
    have : s ^ 11 = (s ^ 2) ^ 5 * s := by ring
    rw [this, hs2]; norm_num
  rw [e]
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

/-- **Cone**: `∫₀¹ t^{d−1} dt = 1/d` (volume do cone = base/d). -/
theorem cone (d : ℕ) (hd : 1 ≤ d) : ∫ t in (0 : ℝ)..1, t ^ (d - 1) = 1 / d := by
  rw [integral_pow]
  have hc : ((d - 1 : ℕ) : ℝ) + 1 = d := by rw [Nat.cast_sub hd]; simp
  have hd0 : d - 1 + 1 = d := by omega
  rw [hd0, zero_pow (by omega : d ≠ 0)]
  push_cast [Nat.cast_sub hd]
  simp

theorem casca : (1 : ℝ) - 0.9 ^ 4 = 0.3439 ∧ (1 : ℝ) - 0.9 ^ 5 = 0.40951 := by norm_num

/-- **Gap do toro plano**: todo modo `k ≠ 0` tem `|k|² ≥ 1`. -/
theorem gap_toro {d : ℕ} (k : Fin d → ℤ) (hk : k ≠ 0) : 1 ≤ ∑ i, k i ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra h; push Not at h; exact hk (funext h)
  have h1 : 1 ≤ k i ^ 2 := by
    have : 0 < k i ^ 2 := by positivity
    omega
  exact h1.trans (Finset.single_le_sum (fun j _ => sq_nonneg (k j)) (Finset.mem_univ i))

/-! ## Infinitesimais formais -/

theorem serie_formal {R : Type*} [CommRing R] (ε : R) :
    (1 + 2 * ε) * (1 - 3 * ε) = 1 - ε - 6 * ε ^ 2 := by ring

theorem geometrica_truncada {R : Type*} [CommRing R] (ε : R) (n : ℕ) :
    (1 - ε) * ∑ i ∈ Finset.range n, ε ^ i = 1 - ε ^ n := mul_neg_geom_sum ε n

end ATK.ModelosSete

#print axioms ATK.ModelosSete.G_det
#print axioms ATK.ModelosSete.G_mul_Ginv
#print axioms ATK.ModelosSete.coeficientes
#print axioms ATK.ModelosSete.residuo_linear
#print axioms ATK.ModelosSete.energia_projetada
#print axioms ATK.ModelosSete.D2_modelo
#print axioms ATK.ModelosSete.D2_formula
#print axioms ATK.ModelosSete.D2_iff
#print axioms ATK.ModelosSete.norma_b
#print axioms ATK.ModelosSete.margem_modelo
#print axioms ATK.ModelosSete.absorcao_modelo
#print axioms ATK.ModelosSete.robustez_absorcao
#print axioms ATK.ModelosSete.amplificacao_deriv
#print axioms ATK.ModelosSete.riccati_solucao
#print axioms ATK.ModelosSete.riccati_valores
#print axioms ATK.ModelosSete.gap_modelo
#print axioms ATK.ModelosSete.gap_atingido
#print axioms ATK.ModelosSete.exp_neg_log_dois
#print axioms ATK.ModelosSete.exp_neg_dois_log_dois
#print axioms ATK.ModelosSete.particao
#print axioms ATK.ModelosSete.energia_variancia
#print axioms ATK.ModelosSete.decaimento
#print axioms ATK.ModelosSete.integral_limites
#print axioms ATK.ModelosSete.integral_exp_dois
#print axioms ATK.ModelosSete.integral_exp_quatro
#print axioms ATK.ModelosSete.Hb_det
#print axioms ATK.ModelosSete.Hb_traco
#print axioms ATK.ModelosSete.Hb_inversa
#print axioms ATK.ModelosSete.Hb_caracteristico
#print axioms ATK.ModelosSete.forma_quadratica
#print axioms ATK.ModelosSete.Hb_positiva
#print axioms ATK.ModelosSete.Hb_autovalor_min
#print axioms ATK.ModelosSete.h22_iff
#print axioms ATK.ModelosSete.perturbacao
#print axioms ATK.ModelosSete.perturbacao_cota
#print axioms ATK.ModelosSete.robustez_regulador
#print axioms ATK.ModelosSete.hodge_modelo
#print axioms ATK.ModelosSete.posto_nulidade
#print axioms ATK.ModelosSete.sobrejetiva_iff
#print axioms ATK.ModelosSete.precisa_m_ge_d
#print axioms ATK.ModelosSete.solucoes_afins
#print axioms ATK.ModelosSete.composicao_expoente
#print axioms ATK.ModelosSete.duplicacao
#print axioms ATK.ModelosSete.composicao_cota
#print axioms ATK.ModelosSete.busca_cauda
#print axioms ATK.ModelosSete.volume_bola_4
#print axioms ATK.ModelosSete.volume_bola_5
#print axioms ATK.ModelosSete.volume_bola_11
#print axioms ATK.ModelosSete.cubo_inscrito_4
#print axioms ATK.ModelosSete.cubo_inscrito_11
#print axioms ATK.ModelosSete.cone
#print axioms ATK.ModelosSete.casca
#print axioms ATK.ModelosSete.gap_toro
#print axioms ATK.ModelosSete.serie_formal
#print axioms ATK.ModelosSete.geometrica_truncada
