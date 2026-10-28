import ATK.XiMomentos
import ATK.PolyaCalor

/-!
# ATK — Interface dos produtores de positividade total (Grupo 3) e as suas ressalvas

* **A interface** `ArithmeticTotalPositiveKernel` (núcleo, identidade com `T(aₙ)` de `Ξ`, positividade total de todos
  os menores): `nonempty_iff_rh` — **existe uma instância ⟺ HR**. A estrutura é exatamente HR, nem mais fraca nem
  mais forte; uma instância incondicional seria uma prova de HR (`OPEN_MATH`).
* **Ressalvas, com contraexemplos no kernel**:
  * `gram_vacuo`: toda matriz é `Aᵢⱼ = ⟨uᵢ, vⱼ⟩` — uma "representação de Gram" `bᵢ₋ⱼ = ⟨uᵢ, vⱼ⟩` sozinha não
    carrega informação;
  * `psd_nao_tn`: uma matriz de Gram (semidefinida positiva) pode não ser totalmente não negativa;
  * `hankel_nao_toeplitz`: os momentos de `μ = (3/2)δ₀ + ½δ₁` têm Hankel positiva, mas `bₙ = mₙ/(2n)!` tem um menor de
    Toeplitz `3 × 3` igual a `−7/2880 < 0` — Hankel (M2) não dá Toeplitz (M3).
* **Núcleos TN conhecidos** (sem afirmar que representam `Ξ`): `tn_exp` — `T(γⁿ/n!)` (`e^{γz}`, `γ ≥ 0`) é TN, como
  limite de `(1 + γz/N)^N` (`prodCoef_const`); junto com `∏(1 + αⱼz)` (rodadas 10–11) e os limites (`tn_closed`), é
  a parte "suficiente" de Edrei para funções inteiras.

* **As pontes de fechamento propostas**: `rh_de_aproximacoes_tn` (limites de matrizes TN que convergem para `T(aₙ)`
  dão HR) e `rh_iff_fatores_positivos` — **existir `c_{N,k} ≥ 0` com `a₀e_n(c_N) → aₙ` é equivalente a HR**. Fechar
  esse nó é provar HR; não é um passo intermediário mais fácil.

Ficam `BUILD_PENDING`: Cauchy–Binet / Lindström–Gessel–Viennot (não estão no Mathlib), o fator `1/(1 − βz)`, a
positividade total estrita do núcleo de Hankel dos momentos (Andréief + Vandermonde generalizado).
-/

open Filter Topology Matrix

namespace ATK.ProdTN

open ATK.Edrei ATK.XiTP ATK.XiCresc
open ATK.ToeplitzTN (toep)

/-! ## 1. A interface -/

/-- **O produtor terminal** (interface proposta): um núcleo igual à matriz de Toeplitz dos coeficientes de `Ξ` com
todos os menores `≥ 0`. -/
structure ArithmeticTotalPositiveKernel where
  kernel : ℕ → ℕ → ℝ
  coefficient_identity : ∀ i j, kernel i j = toep aXi i j
  total_nonnegative : ∀ (r : ℕ) (I J : Fin r → ℕ), StrictMono I → StrictMono J →
    0 ≤ (Matrix.of fun p q => kernel (I p) (J q)).det

/-- Uma instância dá HR. -/
theorem rh_of_kernel (K : ArithmeticTotalPositiveKernel) : RiemannHypothesis := by
  refine rh_de_tn fun r I J hI hJ => ?_
  have h := K.total_nonnegative r I J hI hJ
  have e : (Matrix.of fun p q => K.kernel (I p) (J q)) = (toep aXi).submatrix I J := by
    ext p q
    simp [K.coefficient_identity]
  rwa [e] at h

/-- HR dá uma instância. -/
noncomputable def kernel_of_rh (h : RiemannHypothesis) : ArithmeticTotalPositiveKernel where
  kernel := toep aXi
  coefficient_identity _ _ := rfl
  total_nonnegative r I J hI hJ := tn_de_rh h hI hJ

/-- **A interface é exatamente HR**: `Nonempty ArithmeticTotalPositiveKernel ⟺ RiemannHypothesis`. -/
theorem nonempty_iff_rh : Nonempty ArithmeticTotalPositiveKernel ↔ RiemannHypothesis :=
  ⟨fun ⟨K⟩ => rh_of_kernel K, fun h => ⟨kernel_of_rh h⟩⟩

/-! ## 2. Ressalvas -/

/-- **Toda matriz é uma "matriz de Gram" bilinear**: `Aᵢⱼ = ⟨uᵢ, vⱼ⟩` com `uᵢ` = linhas, `vⱼ` = base canônica. -/
theorem gram_vacuo {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) :
    ∃ u v : Fin r → (Fin r → ℝ), ∀ i j, A i j = u i ⬝ᵥ v j :=
  ⟨fun i => A i, fun j => Pi.single j 1, fun i j => by simp [dotProduct_single]⟩

/-- A matriz de Gram de `(1, 0)` e `(−1, 1)`. -/
def gramEx : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 2]

/-- **Gram (semidefinida positiva) não implica TN**: `gramEx` é `BᵀB`, mas tem uma entrada `−1`. -/
theorem psd_nao_tn : gramEx.PosSemidef ∧ ¬ gramEx.IsTotallyNonneg := by
  constructor
  · have e : gramEx = (!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᴴ * !![1, -1; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [gramEx, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
    rw [e]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  · intro h
    have := h.nonneg 0 1
    simp [gramEx] at this
    linarith

/-- Momentos de `μ = (3/2)δ₀ + ½δ₁`: `mₙ = (3/2)·0^{2n} + ½`. -/
noncomputable def momEx (n : ℕ) : ℝ := 3 / 2 * (0 : ℝ) ^ (2 * n) + 1 / 2

/-- Hankel positiva para `momEx`: `Σcᵢcⱼm_{i+j} = (3/2)(Σcᵢ0^{2i})² + ½(Σcᵢ)² ≥ 0`. -/
theorem hankel_momEx (N : ℕ) (c : ℕ → ℝ) :
    0 ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, c i * c j * momEx (i + j) := by
  have hpt : ∀ i j, c i * c j * momEx (i + j) =
      3 / 2 * ((c i * (0 : ℝ) ^ (2 * i)) * (c j * (0 : ℝ) ^ (2 * j))) + 1 / 2 * (c i * c j) := by
    intro i j
    unfold momEx
    rw [show 2 * (i + j) = 2 * i + 2 * j by ring, pow_add]
    ring
  simp_rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  have h1 := mul_self_nonneg (∑ i ∈ Finset.range N, c i * (0 : ℝ) ^ (2 * i))
  have h2 := mul_self_nonneg (∑ i ∈ Finset.range N, c i)
  nlinarith

/-- Os coeficientes `bₙ = mₙ/(2n)!` de `μ = (3/2)δ₀ + ½δ₁`. -/
noncomputable def bEx (n : ℕ) : ℝ := momEx n / (2 * n).factorial

/-- **Hankel não dá Toeplitz**: o menor de `T(bEx)` nas linhas `1, 2, 3` e colunas `0, 1, 2` é `−7/2880`. -/
theorem hankel_nao_toeplitz :
    ((toep bEx).submatrix ![1, 2, 3] ![0, 1, 2]).det = -7 / 2880 ∧ ¬ (toep bEx).IsTotallyNonneg := by
  have hd : ((toep bEx).submatrix ![1, 2, 3] ![0, 1, 2]).det = -7 / 2880 := by
    rw [Matrix.det_fin_three]
    simp [toep, bEx, momEx, Nat.factorial]
    norm_num
  refine ⟨hd, fun h => ?_⟩
  have hr : StrictMono (![1, 2, 3] : Fin 3 → ℕ) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [Fin.lt_def]
  have hc : StrictMono (![0, 1, 2] : Fin 3 → ℕ) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [Fin.lt_def]
  have := h hr hc
  rw [hd] at this
  norm_num at this

/-! ## 3. Um núcleo TN conhecido: `e^{γz}` -/

/-- `(1 + cz)^N` pela recursão de `prodCoef`: coeficientes `C(N,n)cⁿ`. -/
theorem prodCoef_const (c : ℝ) : ∀ N n, prodCoef 1 (fun _ => c) N n = (N.choose n : ℝ) * c ^ n
  | 0, n => by
    cases n <;> simp [prodCoef]
  | N + 1, 0 => by
    simp only [prodCoef, if_true, mul_zero, add_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero,
      mul_one]
    have := prodCoef_const c N 0
    simpa using this
  | N + 1, k + 1 => by
    simp only [prodCoef, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [prodCoef_const c N (k + 1), prodCoef_const c N k, Nat.choose_succ_succ', Nat.cast_add, pow_succ]
    ring

/-- **`e^{γz}` é PF∞**: `T(γⁿ/n!)` é TN para `γ ≥ 0` (limite de `(1 + γz/N)^N`). -/
theorem tn_exp {γ : ℝ} (hγ : 0 ≤ γ) : (toep fun n => γ ^ n / n.factorial).IsTotallyNonneg := by
  refine tn_closed (A := fun N => toep (prodCoef 1 (fun _ => γ / N) N))
    (fun N => tn_prodCoef zero_le_one (fun _ => div_nonneg hγ (Nat.cast_nonneg N)) N) fun i j => ?_
  simp only [toep]
  split_ifs
  · have h := (ATK.PolyaCalor.tendsto_choose_div_pow (i - j)).const_mul (γ ^ (i - j))
    rw [show γ ^ (i - j) * (1 / ((i - j).factorial : ℝ)) = γ ^ (i - j) / (i - j).factorial by ring] at h
    refine h.congr fun N => ?_
    rw [prodCoef_const, div_pow]
    ring
  · exact tendsto_const_nhds

/-! ## 4. As pontes de fechamento propostas — e por que fechá-las é HR -/

/-- **Fechamento por aproximações TN**: se `T⁽ᴺ⁾` são TN e `T⁽ᴺ⁾ᵢⱼ → a_{i−j}` (os coeficientes de `Ξ`), vale HR. -/
theorem rh_de_aproximacoes_tn {A : ℕ → Matrix ℕ ℕ ℝ} (hA : ∀ N, (A N).IsTotallyNonneg)
    (hl : ∀ i j, Tendsto (fun N => A N i j) atTop (𝓝 (toep aXi i j))) : RiemannHypothesis :=
  rh_de_tn (tn_closed hA hl)

/-- **O "nó decisivo" é HR**: existe um arranjo `c_{N,k} ≥ 0` com `a₀·e_n(c_{N,0}, …, c_{N,N−1}) → aₙ` para todo `n`
**se e só se** vale HR. (`prodCoef a₀ c N n = a₀·e_n` dos primeiros `N` parâmetros.) -/
theorem rh_iff_fatores_positivos : RiemannHypothesis ↔
    ∃ c : ℕ → ℕ → ℝ, (∀ N k, 0 ≤ c N k) ∧
      ∀ n, Tendsto (fun N => prodCoef (aXi 0) (c N) N n) atTop (𝓝 (aXi n)) := by
  constructor
  · intro h
    obtain ⟨α, hα, _, hlim⟩ := rh_iff_genero0.mp h
    exact ⟨fun _ => α, fun _ k => hα k, hlim⟩
  · rintro ⟨c, hc, hlim⟩
    refine rh_de_aproximacoes_tn (A := fun N => toep (prodCoef (aXi 0) (c N) N))
      (fun N => tn_prodCoef aXi_zero_pos.le (hc N) N) fun i j => ?_
    simp only [toep]
    split_ifs
    · exact hlim _
    · exact tendsto_const_nhds

end ATK.ProdTN

#print axioms ATK.ProdTN.rh_of_kernel
#print axioms ATK.ProdTN.kernel_of_rh
#print axioms ATK.ProdTN.nonempty_iff_rh
#print axioms ATK.ProdTN.gram_vacuo
#print axioms ATK.ProdTN.psd_nao_tn
#print axioms ATK.ProdTN.hankel_momEx
#print axioms ATK.ProdTN.hankel_nao_toeplitz
#print axioms ATK.ProdTN.prodCoef_const
#print axioms ATK.ProdTN.tn_exp
#print axioms ATK.ProdTN.rh_de_aproximacoes_tn
#print axioms ATK.ProdTN.rh_iff_fatores_positivos
