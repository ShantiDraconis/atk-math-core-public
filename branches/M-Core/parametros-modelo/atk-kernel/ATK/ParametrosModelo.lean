import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# ATK — Parâmetros, modelos e habitantes auxiliares: conferência no kernel

Os nove textos de 15/10/2026 (valores estruturados, preenchimento de parâmetros, derivações, letras e
operadores, valores canônicos, gramática, inventário de provas, habitantes) propõem valores exatos de
modelos e alguns lemas em Lean, todos marcados como "não compilados". Este arquivo confere tudo o
que é enunciado matemático preciso nesses textos. Duas afirmações estão **erradas** e são refutadas
aqui, com a versão correta provada:

* a "lei universal de todas as junções" tem o sinal do termo em `A` trocado:
  `comutador_lei` prova a lei certa e `lei_do_texto_falsa` dá o contraexemplo;
* "em Beal, `mdc(A,B) = mdc(A,C) = mdc(B,C) = mdc(A,B,C)`" é falso: `beal_mdc_texto_falso` usa
  `4³ + 4³ = 2⁷`, com `mdc(4,4) = 4 ≠ 2 = mdc(4,2)`. O correto é que os três pares têm os
  mesmos divisores primos (`beal_primos_comuns`).

Uma observação de método sobre o "teorema central de anulação" (H5): as suas hipóteses já equivalem à
conclusão (`anulacao_iff`). Ele não reduz nenhum problema; aplicá-lo a um defeito original exige
provar exatamente `d ≡ 0`.

Tudo aqui é `EXACT_MODEL`: propriedades dos modelos e lemas lógicos. Nenhum enunciado terminal é
tocado (0/7).
-/

open Real Matrix
open scoped goldenRatio

namespace ATK.ParametrosModelo

/-! ## 1. Valores estruturados (texto "estrutura de valores únicos") -/

/-- Um parâmetro com valor, domínio e propriedade certificada. -/
structure Parametro where
  Carrier : Type
  value : Carrier
  Valid : Carrier → Prop
  certified : Valid value

/-- Uma transformação entre parâmetros que preserva a validade. -/
structure MapaParametro (A B : Parametro) where
  map : A.Carrier → B.Carrier
  preserves : ∀ x, A.Valid x → B.Valid (map x)

/-- A composição preserva a validade. -/
def MapaParametro.comp {A B C : Parametro} (f : MapaParametro A B) (g : MapaParametro B C) :
    MapaParametro A C where
  map := g.map ∘ f.map
  preserves := fun x hx => g.preserves (f.map x) (f.preserves x hx)

theorem comp_map {A B C : Parametro} (f : MapaParametro A B) (g : MapaParametro B C) (x) :
    (f.comp g).map x = g.map (f.map x) := rfl

/-- O parâmetro `φ`, com `φ² = φ + 1` certificado. -/
noncomputable def parametroPhi : Parametro := ⟨ℝ, φ, fun x => x ^ 2 = x + 1, goldenRatio_sq⟩

/-! ## 2. Habitantes H1–H5 e o fechamento -/

/-- H1: substituição. -/
theorem h1_substituicao {X Y : Type*} (f : X → Y) {x y : X} (h : x = y) : f x = f y := by
  cases h
  rfl

/-- H2: composição de propriedades preservadas. -/
theorem h2_composicao {X Y Z : Type*} (P : X → Prop) (Q : Y → Prop) (R : Z → Prop) (f : X → Y)
    (g : Y → Z) (hf : ∀ x, P x → Q (f x)) (hg : ∀ y, Q y → R (g y)) :
    ∀ x, P x → R (g (f x)) :=
  fun x hx => hg (f x) (hf x hx)

/-- H3: transporte de iterações, `F ∘ T = U ∘ F ⇒ F ∘ Tⁿ = Uⁿ ∘ F`. -/
theorem h3_iteracoes {X Y : Type*} (T : X → X) (U : Y → Y) (F : X → Y)
    (h : ∀ x, F (T x) = U (F x)) : ∀ n x, F (T^[n] x) = U^[n] (F x) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    rw [Function.iterate_succ_apply', h, ih, ← Function.iterate_succ_apply' U]

/-- H4: contração ao longo da órbita, `d(Tⁿx) ≤ qⁿ d(x)`. -/
theorem h4_contracao {X : Type*} (T : X → X) (d : X → ℝ) {q : ℝ} (hq0 : 0 ≤ q)
    (hT : ∀ x, d (T x) ≤ q * d x) : ∀ n x, d (T^[n] x) ≤ q ^ n * d x := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [Function.iterate_succ_apply']
    calc d (T (T^[n] x)) ≤ q * d (T^[n] x) := hT _
      _ ≤ q * (q ^ n * d x) := mul_le_mul_of_nonneg_left (ih x) hq0
      _ = q ^ (n + 1) * d x := by ring

/-- H4 (limite): `d(Tⁿx) → 0` se `0 ≤ d` e `q < 1`. -/
theorem h4_limite {X : Type*} (T : X → X) (d : X → ℝ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hd : ∀ x, 0 ≤ d x) (hT : ∀ x, d (T x) ≤ q * d x) (x : X) :
    Filter.Tendsto (fun n => d (T^[n] x)) Filter.atTop (nhds 0) := by
  have hlim : Filter.Tendsto (fun n : ℕ => q ^ n * d x) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (d x)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => hd _)
    (fun n => h4_contracao T d hq0 hT n x)

/-- H5: anulação por invariância e contração. -/
theorem h5_anulacao {X : Type*} (T : X → X) (d : X → ℝ) {q : ℝ} (hq1 : q < 1)
    (hd : ∀ x, 0 ≤ d x) (hinv : ∀ x, d (T x) = d x) (hT : ∀ x, d (T x) ≤ q * d x) :
    ∀ x, d x = 0 := by
  intro x
  have h1 := hT x
  rw [hinv] at h1
  have h2 := hd x
  nlinarith

/-- **As hipóteses de H5 equivalem à conclusão**: o teorema não reduz nada. -/
theorem anulacao_iff {X : Type*} (T : X → X) (d : X → ℝ) {q : ℝ} (hq1 : q < 1)
    (hd : ∀ x, 0 ≤ d x) :
    ((∀ x, d (T x) = d x) ∧ (∀ x, d (T x) ≤ q * d x)) ↔ ∀ x, d x = 0 := by
  constructor
  · rintro ⟨hinv, hT⟩
    exact h5_anulacao T d hq1 hd hinv hT
  · intro h0
    refine ⟨fun x => by rw [h0, h0], fun x => by rw [h0, h0, mul_zero]⟩

/-- O fechamento lógico: habitantes e pontes dão as sete proposições. -/
theorem fechamento (P K : Fin 7 → Prop) (habitantes : ∀ i, K i) (pontes : ∀ i, K i → P i) :
    ∀ i, P i :=
  fun i => pontes i (habitantes i)

/-! ## 3. Gramática: escopo dos quantificadores -/

/-- `∀x ∃y, x = y` vale e `∃y ∀x, x = y` não, em `Bool`. -/
theorem escopo_quantificadores :
    (∀ x : Bool, ∃ y : Bool, x = y) ∧ ¬ (∃ y : Bool, ∀ x : Bool, x = y) := by
  decide

/-! ## 4. Os operadores `A`, `M`, `S` e a lei das junções -/

/-- `A = [[0, −1], [1, 0]]`. -/
def opA : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]
/-- `M = [[1, 0], [0, −1]]`. -/
def opM : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]
/-- `S = [[0, 1], [1, 0]]`. -/
def opS : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

theorem tabela_operadores :
    opA * opA = -1 ∧ opM * opM = 1 ∧ opS * opS = 1 ∧ opA * opM = opS ∧ opM * opA = -opS ∧
      opM * opS = -opA ∧ opS * opM = opA ∧ opS * opA = opM ∧ opA * opS = -opM := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;> simp [opA, opM, opS, Matrix.mul_apply]

/-- O operador de uma letra, `O = g I + a A + b M + c S = [[g + b, c − a], [a + c, g − b]]`. -/
def operador (g a b c : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![g + b, c - a; a + c, g - b]

theorem operador_soma (g a b c : ℤ) :
    operador g a b c = !![g, 0; 0, g] + a • opA + b • opM + c • opS := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [operador, opA, opM, opS] <;> ring

/-- **A lei correta das junções**:
`[Oᵢ, Oⱼ] = 2(cᵢbⱼ − bᵢcⱼ)A + 2(cᵢaⱼ − aᵢcⱼ)M + 2(aᵢbⱼ − bᵢaⱼ)S`. -/
theorem comutador_lei (g a b c g' a' b' c' : ℤ) :
    operador g a b c * operador g' a' b' c' - operador g' a' b' c' * operador g a b c =
      (2 * (c * b' - b * c')) • opA + (2 * (c * a' - a * c')) • opM +
        (2 * (a * b' - b * a')) • opS := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [operador, opA, opM, opS, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **A lei do texto está errada** (sinal do termo em `A`): com `O = M` e `O' = S`, o comutador é
`−2A`, e o texto daria `+2A`. -/
theorem lei_do_texto_falsa :
    operador 0 0 1 0 * operador 0 0 0 1 - operador 0 0 0 1 * operador 0 0 1 0 ≠
      (2 * (1 * 1 - 0 * 0)) • opA + (2 * (0 * 0 - 0 * 0)) • opM +
        (2 * (0 * 0 - 1 * 0)) • opS := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [operador, opA, opM, opS, Matrix.mul_apply, Fin.sum_univ_two] at this

/-- O traço de todo comutador é zero e o determinante é multiplicativo. -/
theorem traco_det (X Y : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix.trace (X * Y - Y * X) = 0 ∧ (X * Y).det = X.det * Y.det := by
  refine ⟨?_, Matrix.det_mul X Y⟩
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- O exemplo do texto: `O_א = O(1; 1, 1, 1)`, `O_ב = O(2; 0, 2, 2)` e o seu comutador. -/
theorem exemplo_alef_bet :
    operador 1 1 1 1 = !![2, 0; 2, 0] ∧ operador 2 0 2 2 = !![4, 2; 2, 0] ∧
      operador 1 1 1 1 * operador 2 0 2 2 = !![8, 4; 8, 4] ∧
      operador 2 0 2 2 * operador 1 1 1 1 = !![12, 0; 4, 0] ∧
      operador 1 1 1 1 * operador 2 0 2 2 - operador 2 0 2 2 * operador 1 1 1 1 =
        !![-4, 4; 4, 4] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [operador, opA, opM, opS, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## 5. Contagens dos sistemas de símbolos -/

/-- Gematria padrão das 22 letras. -/
def gematria : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 200,
  300, 400]

theorem contagens :
    gematria.length = 22 ∧ gematria.sum = 1495 ∧ (List.range 25).sum = 300 ∧
      Nat.choose 22 2 = 231 ∧ Nat.choose 24 2 = 276 ∧ 22 * 24 = 528 ∧
      231 + 276 + 528 = Nat.choose 46 2 ∧ Nat.choose 46 2 = 1035 ∧ 2 ^ 6 = 64 := by
  decide

/-! ## 6. Riemann: o modelo de Gram -/

/-- `G = [[2, 1], [1, 2]]`. -/
def gram : Matrix (Fin 2) (Fin 2) ℚ := !![2, 1; 1, 2]

theorem gram_valores :
    gram.det = 3 ∧ Matrix.trace gram = 4 ∧
      gram * ((1 / 3 : ℚ) • !![2, -1; -1, 2]) = 1 ∧
      (∀ l : ℚ, (2 - l) * (2 - l) - 1 = 0 ↔ l = 1 ∨ l = 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [gram, Matrix.det_fin_two_of]; norm_num
  · rw [gram, Matrix.trace_fin_two_of]; norm_num
  · ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [gram, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · intro l
    constructor
    · intro h
      have : (l - 1) * (l - 3) = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h1
      · left; linarith
      · right; linarith
    · rintro (rfl | rfl) <;> norm_num

/-- O defeito do exemplo: `b = (1/2, 1/3)`, `bᵀG⁻¹b = 7/54`, `D = 1 − 7/54 = 47/54`. -/
theorem gram_defeito :
    let b : Fin 2 → ℚ := ![1 / 2, 1 / 3]
    let Ginv : Matrix (Fin 2) (Fin 2) ℚ := (1 / 3 : ℚ) • !![2, -1; -1, 2]
    Ginv *ᵥ b = ![2 / 9, 1 / 18] ∧ b ⬝ᵥ (Ginv *ᵥ b) = 7 / 54 ∧ 1 - b ⬝ᵥ (Ginv *ᵥ b) = 47 / 54 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; norm_num
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; norm_num

/-! ## 7. P vs NP: a fórmula de teste -/

/-- `F = (x₁ ∨ x₂) ∧ (¬x₁ ∨ x₃)`. -/
def formula (v : Bool × Bool × Bool) : Bool := (v.1 || v.2.1) && (!v.1 || v.2.2)

/-- `F` é satisfatível, `(1, 0, 1)` a satisfaz, e tem exatamente 4 das 8 atribuições. -/
theorem formula_contagem :
    formula (true, false, true) = true ∧
      (Finset.univ.filter fun v => formula v = true).card = 4 ∧
      Fintype.card (Bool × Bool × Bool) = 8 := by
  decide

/-! ## 8. Navier–Stokes: a margem auxiliar -/

theorem margem_ns :
    (1 : ℚ) - 1 / 4 - 1 / 3 = 5 / 12 ∧ (1 : ℚ) / 4 + 1 / 3 = 7 / 12 ∧ (12 : ℚ) / 5 * (1 / 5) = 12 / 25 := by
  norm_num

/-- `X ≤ c_B X + c_T X + C` com `c_B + c_T = 7/12` dá `X ≤ (12/5) C`. -/
theorem cota_ns {X C : ℝ} (h : X ≤ 1 / 4 * X + 1 / 3 * X + C) : X ≤ 12 / 5 * C := by
  linarith

/-- O modelo `u(t) = 8 e^{−t log 2}`: `u(n) = 8/2ⁿ`, `u' = −(log 2) u < 0`. -/
theorem modelo_decaimento (t : ℝ) :
    HasDerivAt (fun s => 8 * exp (-(log 2) * s)) (-(log 2) * (8 * exp (-(log 2) * t))) t ∧
      -(log 2) * (8 * exp (-(log 2) * t)) < 0 := by
  constructor
  · have h := (((hasDerivAt_id' t).const_mul (-(log 2))).exp).const_mul 8
    convert h using 1
    ring
  · have : 0 < log 2 := log_pos (by norm_num)
    have : 0 < exp (-(log 2) * t) := exp_pos _
    nlinarith

theorem modelo_decaimento_inteiros (n : ℕ) : 8 * exp (-(log 2) * n) = 8 / 2 ^ n := by
  rw [show -(log 2) * (n : ℝ) = -((n : ℝ) * log 2) by ring, exp_neg, ← log_rpow (by norm_num),
    exp_log (by positivity), rpow_natCast]
  ring

/-! ## 9. Yang–Mills: o laplaciano do ciclo de 10 vértices -/

/-- Equação de autovetor do laplaciano de ciclo: para `v j = cos(θ j)`,
`2 v j − v (j−1) − v (j+1) = (2 − 2 cos θ) v j`. -/
theorem autovetor_ciclo (θ : ℝ) (j : ℤ) :
    2 * cos (θ * j) - cos (θ * (j - 1)) - cos (θ * (j + 1)) = (2 - 2 * cos θ) * cos (θ * j) := by
  have h1 : θ * (j - 1) = θ * j - θ := by ring
  have h2 : θ * (j + 1) = θ * j + θ := by ring
  rw [h1, h2, cos_sub, cos_add]
  ring

/-- Os autovalores `2 − 2cos(kπ/5)`, `k = 1, …, 5`, em forma fechada, e o gap `(3 − √5)/2 > 0`. -/
theorem espectro_ciclo :
    2 - 2 * cos (π / 5) = (3 - √5) / 2 ∧ 2 - 2 * cos (2 * π / 5) = (5 - √5) / 2 ∧
      2 - 2 * cos (3 * π / 5) = (3 + √5) / 2 ∧ 2 - 2 * cos (4 * π / 5) = (5 + √5) / 2 ∧
      2 - 2 * cos (5 * π / 5) = 4 ∧ 0 < (3 - √5) / 2 := by
  have h5 : √5 ^ 2 = 5 := sq_sqrt (by norm_num)
  have c1 := cos_pi_div_five
  have c2 : cos (2 * π / 5) = (√5 - 1) / 4 := by
    rw [show 2 * π / 5 = 2 * (π / 5) by ring, cos_two_mul, c1]
    nlinarith [h5]
  have c3 : cos (3 * π / 5) = -((√5 - 1) / 4) := by
    rw [show 3 * π / 5 = π - 2 * π / 5 by ring, cos_pi_sub, c2]
  have c4 : cos (4 * π / 5) = -((1 + √5) / 4) := by
    rw [show 4 * π / 5 = π - π / 5 by ring, cos_pi_sub, c1]
  refine ⟨by rw [c1]; ring, by rw [c2]; ring, by rw [c3]; ring, by rw [c4]; ring, ?_, ?_⟩
  · rw [show 5 * π / 5 = π by ring, cos_pi]; norm_num
  · have : √5 < 3 := by
      rw [show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
      exact sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith

/-! ## 10. BSD: a matriz de emparelhamento do modelo -/

/-- `H = [[2, 1], [1, 3]]`: `tr = det = 5`, autovalores `(5 ± √5)/2`, positiva definida. -/
theorem bsd_modelo :
    (!![2, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℚ).det = 5 ∧
      Matrix.trace (!![2, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℚ) = 5 ∧
      ((5 + √5) / 2) ^ 2 - 5 * ((5 + √5) / 2) + 5 = 0 ∧
      ((5 - √5) / 2) ^ 2 - 5 * ((5 - √5) / 2) + 5 = 0 ∧
      0 < (5 - √5) / 2 := by
  have h5 : √5 ^ 2 = 5 := sq_sqrt (by norm_num)
  refine ⟨?_, ?_, by nlinarith [h5], by nlinarith [h5], ?_⟩
  · rw [Matrix.det_fin_two_of]; norm_num
  · rw [Matrix.trace_fin_two_of]; norm_num
  · have : √5 < 5 := by
      rw [show (5 : ℝ) = √25 by rw [show (25 : ℝ) = 5 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
      exact sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith

/-! ## 11. Hodge: a decomposição linear do modelo -/

theorem hodge_modelo :
    (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℚ) *ᵥ ![2, 1] = ![3, 1] ∧
      (!![1, 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℚ).det = -2 := by
  refine ⟨?_, ?_⟩
  · ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  · rw [Matrix.det_fin_two_of]; norm_num

/-! ## 12. Beal: divisores comuns e o exemplo -/

/-- O correto: um primo que divide duas das bases divide a terceira. -/
theorem beal_primos_comuns {A B C x y z p : ℕ} (hp : p.Prime) (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (h : A ^ x + B ^ y = C ^ z) :
    (p ∣ A ∧ p ∣ B → p ∣ C) ∧ (p ∣ A ∧ p ∣ C → p ∣ B) ∧ (p ∣ B ∧ p ∣ C → p ∣ A) := by
  refine ⟨fun ⟨ha, hb⟩ => ?_, fun ⟨ha, hc⟩ => ?_, fun ⟨hb, hc⟩ => ?_⟩
  · have : p ∣ C ^ z := h ▸ dvd_add (dvd_pow ha hx.ne') (dvd_pow hb hy.ne')
    exact hp.dvd_of_dvd_pow this
  · have h1 : p ∣ C ^ z := dvd_pow hc hz.ne'
    have h2 : p ∣ A ^ x := dvd_pow ha hx.ne'
    have : p ∣ B ^ y := (Nat.dvd_add_right h2).mp (h ▸ h1)
    exact hp.dvd_of_dvd_pow this
  · have h1 : p ∣ C ^ z := dvd_pow hc hz.ne'
    have h2 : p ∣ B ^ y := dvd_pow hb hy.ne'
    have : p ∣ A ^ x := (Nat.dvd_add_left h2).mp (h ▸ h1)
    exact hp.dvd_of_dvd_pow this

/-- **A afirmação do texto é falsa**: `4³ + 4³ = 2⁷`, expoentes `> 2`, e `mdc(4,4) = 4 ≠ 2 =
mdc(4,2)`. -/
theorem beal_mdc_texto_falso :
    (4 : ℕ) ^ 3 + 4 ^ 3 = 2 ^ 7 ∧ Nat.gcd 4 4 ≠ Nat.gcd 4 2 ∧
      ¬ (∀ A B C x y z : ℕ, 2 < x → 2 < y → 2 < z → A ^ x + B ^ y = C ^ z →
        Nat.gcd A B = Nat.gcd A C) := by
  refine ⟨by norm_num, by decide, fun h => ?_⟩
  have := h 4 4 2 3 3 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact absurd this (by decide)

/-- O exemplo `2³ + 2³ = 2⁴`, `mdc = 2`, e o aumento da valuação: `v₂(8) = 3`, `v₂(16) = 4`. -/
theorem beal_exemplo :
    (2 : ℕ) ^ 3 + 2 ^ 3 = 2 ^ 4 ∧ Nat.gcd 2 (Nat.gcd 2 2) = 2 ∧
      padicValNat 2 (2 ^ 3) = 3 ∧ padicValNat 2 (2 ^ 3 + 2 ^ 3) = 4 := by
  refine ⟨by norm_num, by decide, padicValNat.prime_pow 3, ?_⟩
  rw [show (2 : ℕ) ^ 3 + 2 ^ 3 = 2 ^ 4 by norm_num]
  exact padicValNat.prime_pow 4

/-! ## 13. Razão áurea e a contração do modelo -/

theorem razao_aurea : φ ^ 2 = φ + 1 ∧ 1 / φ = φ - 1 ∧ φ ^ 3 = 2 * φ + 1 := by
  have h := goldenRatio_sq
  have hpos := goldenRatio_pos
  refine ⟨h, ?_, ?_⟩
  · rw [div_eq_iff hpos.ne']
    linear_combination -h
  · linear_combination (φ + 1) * h

theorem contracao_modelo :
    (1 / 2 : ℚ) ^ 6 = 1 / 64 ∧ (1 : ℚ) - 1 / 64 = 63 / 64 ∧ (8 : ℚ) * (1 / 2) ^ 3 = 1 ∧
      (8 : ℚ) * (1 / 2) ^ 6 = 1 / 8 := by
  norm_num

end ATK.ParametrosModelo

#print axioms ATK.ParametrosModelo.comp_map
#print axioms ATK.ParametrosModelo.h1_substituicao
#print axioms ATK.ParametrosModelo.h2_composicao
#print axioms ATK.ParametrosModelo.h3_iteracoes
#print axioms ATK.ParametrosModelo.h4_contracao
#print axioms ATK.ParametrosModelo.h4_limite
#print axioms ATK.ParametrosModelo.h5_anulacao
#print axioms ATK.ParametrosModelo.anulacao_iff
#print axioms ATK.ParametrosModelo.fechamento
#print axioms ATK.ParametrosModelo.escopo_quantificadores
#print axioms ATK.ParametrosModelo.tabela_operadores
#print axioms ATK.ParametrosModelo.operador_soma
#print axioms ATK.ParametrosModelo.comutador_lei
#print axioms ATK.ParametrosModelo.lei_do_texto_falsa
#print axioms ATK.ParametrosModelo.traco_det
#print axioms ATK.ParametrosModelo.exemplo_alef_bet
#print axioms ATK.ParametrosModelo.contagens
#print axioms ATK.ParametrosModelo.gram_valores
#print axioms ATK.ParametrosModelo.gram_defeito
#print axioms ATK.ParametrosModelo.formula_contagem
#print axioms ATK.ParametrosModelo.margem_ns
#print axioms ATK.ParametrosModelo.cota_ns
#print axioms ATK.ParametrosModelo.modelo_decaimento
#print axioms ATK.ParametrosModelo.modelo_decaimento_inteiros
#print axioms ATK.ParametrosModelo.autovetor_ciclo
#print axioms ATK.ParametrosModelo.espectro_ciclo
#print axioms ATK.ParametrosModelo.bsd_modelo
#print axioms ATK.ParametrosModelo.hodge_modelo
#print axioms ATK.ParametrosModelo.beal_primos_comuns
#print axioms ATK.ParametrosModelo.beal_mdc_texto_falso
#print axioms ATK.ParametrosModelo.beal_exemplo
#print axioms ATK.ParametrosModelo.razao_aurea
#print axioms ATK.ParametrosModelo.contracao_modelo
