import ATK.ZeroClasses.Escalas

/-!
# ATK-ZERO-CLASSES — o encontro: matrizes, composições, colisões e certificados

Rodada 21. O pedido: cruzar todos os dados e achar **exatamente onde** os zeros não triviais fora da linha se
encontram no mundo hipotético. O kernel responde em quatro partes; nada aqui supõe RH nem `¬RH`, e o mundo
hipotético entra **só como hipótese** (`HFora`).

**1. Matriz, soma, diferença, produto** (`det_zeta`, `xi_bilateral`, `det_B`, `cruzamento`, `criterio_SD`).
`A(w) = [[Re w, −Im w], [Im w, Re w]]` tem `det A = |w|²` e representa a multiplicação (`matA_mul`). Com
`s₋ = 1 − s̄₊`, `ξ(s₋) = conj ξ(s₊)`, e então `(|S|² + |D|²)/4 = det A(ξ(s₊)) = ξ(s₊)ξ(s₋) = |ξ(s₊)|²`
(`S = ξ(s₊) + ξ(s₋)`, `D = ξ(s₊) − ξ(s₋)`); na faixa, `S = D = 0 ⟺ ζ(s₊) = 0`. São **quatro escritas do mesmo
número**, não quatro evidências; e a simetria sozinha não obriga zero (`simetria_nao_obriga`: `3 + 4i`).

**2. Zero coletivo ≠ zero individual** (`zero_coletivo`, `zero_coletivo_zeta`, `dois_pontos`,
`coletivo_sem_individual`, `composicao_funcional`). `(ζ3 − ζ4)ζ2 + (ζ4 − ζ2)ζ3 + (ζ2 − ζ3)ζ4 = 0` com pesos não
nulos e nenhum `ζ(k)` nulo; `exp` nunca se anula e ainda assim admite cancelamento; a equação funcional é uma
composição identicamente nula. Também: `ζ(−½) ≠ 0`, `ζ(qₙ) ≠ 0` para `qₙ = −1/(2n+1) + i·10¹⁰⁰`, e
`ζ(−2·10¹⁰⁰⁰) = 0` (zero **trivial** gigante).

**3. Colisão: possível em família, impossível para `ζ` fixa** (`Fcol_zero_iff`, `colisao_dupla`,
`logderiv_Fcol`, `logderiv_limite`, `colisao_atk`, `sem_colisao`, `atk_finitos`, `estabilizacao`).
`F_δ(s) = (s − c)² − δ²` tem zeros `c ± δ` que colidem num zero duplo, e `F′/F = 1/(s − ρ₊) + 1/(s − ρ₋) →
2/(s − c)`. Para `ζ`, **nenhuma sequência de pontos distintos `sₙ → c` é eventualmente feita de zeros**
(`sem_colisao`, inclusive `c = 1`): a sequência ATK `½ + 1/(2n+1) + it` só toca zeros para finitos `n`, em cada
altura `t`. A "estabilização" `|ζ(ρ+u)|²/u² → |ζ′(ρ)|² > 0` no primeiro zero certificado é a assinatura de um
zero **simples na linha**, não de uma colisão (`estabilizacao_primeiro_zero`).

**4. Onde exatamente — o certificado** (`certificado_existencia`, `certificado_exclusao`, `certificado_refuta`,
`certificado_robusto`, `fora_simples_iff_certificado`). Um disco com `‖1 − f′/c‖ ≤ ½` e `‖f(z₀)/c‖ ≤ r/2` contém
**exatamente um** zero, simples. Logo: **existe zero simples fora da linha ⟺ existe um disco fora da linha com
esse certificado**; e todo zero simples fora da linha é certificado por **qualquer** dado de precisão finita
suficiente (centro a menos de `r/4`, inclinação a menos de `|ζ′(ρ)|/8`). O mundo hipotético, se for o real, é
**verificável por uma conta finita**; o que nenhuma conta finita faz é provar que ele é falso (isso é RH).

**5. O encontro no mundo hipotético** (`primeiro_fora`, `altura_unica`, `encontro_hipotetico`,
`candidato_gigante`). Sob `HFora` existe um **primeiro** zero fora da linha `ρ* = β + iγ*` (menor altura
positiva), `γ*` é **único**, e com as hipóteses de Platt–Trudgian e Bellotti–Trudgian–Yang: `γ* > 3·10¹²`, `β` na
janela, o quarteto `ρ*, 1 − ρ̄*, ρ̄*, 1 − ρ*` são zeros, e o par `ρ*, 1 − ρ̄*` encontra-se no ponto `½ + iγ*`
da linha. **Esse é o ponto exato de encontro: `½ + iγ*`.** O valor de `γ*` não é determinado por nenhum dado
disponível — só sabemos `γ* > H`; uma cota superior seria uma refutação de RH. O candidato
`ρ = ½ + 1/(2·10¹⁰⁰⁰ + 1) + i·10¹⁰⁰` está na janela (nada o exclui), e seu estado é `ζ(ρ) = 0 ⟺ S = D = 0`:
**não calculado** (a soma de Riemann–Siegel nessa altura tem `≈ 4·10⁴⁹` termos).
-/

open Complex ComplexConjugate Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.Encontro

open ATK.ZeroClasses ATK.ZeroClasses.Zeta ATK.ZeroClasses.Hipotetico ATK.BaseRiemannXi
open ATK.ZeroCert (z0 rr)

/-! ## 1. A matriz da multiplicação; soma e diferença dos espelhos -/

/-- Matriz real `[[Re w, −Im w], [Im w, Re w]]` da multiplicação por `w`. -/
def matA (w : ℂ) : Matrix (Fin 2) (Fin 2) ℝ := !![w.re, -w.im; w.im, w.re]

theorem det_matA (w : ℂ) : (matA w).det = normSq w := by
  rw [matA, Matrix.det_fin_two_of, normSq_apply]; ring

theorem det_matA_eq_zero_iff (w : ℂ) : (matA w).det = 0 ↔ w = 0 := by
  rw [det_matA, normSq_eq_zero]

/-- A multiplicação complexa **é** o produto de matrizes. -/
theorem matA_mul (w v : ℂ) : matA (w * v) = matA w * matA v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matA, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- `det A(s) = |ζ(s)|²`, e `A(s)` é singular **exatamente** nos zeros de `ζ`. -/
theorem det_zeta (s : ℂ) : (matA (riemannZeta s)).det = ‖riemannZeta s‖ ^ 2 ∧
    ((matA (riemannZeta s)).det = 0 ↔ riemannZeta s = 0) :=
  ⟨by rw [det_matA, Complex.sq_norm], det_matA_eq_zero_iff _⟩

/-- `ξ(1 − s̄) = conj ξ(s)`. -/
theorem xi_espelho (s : ℂ) : riemannXi (1 - conj s) = conj (riemannXi s) := by
  rw [riemannXi_one_sub, riemannXi_conj]

theorem espelho_coord (u t : ℝ) :
    1 - conj ((1 / 2 : ℂ) + u + t * I) = (1 / 2 : ℂ) - u + t * I := by
  apply Complex.ext <;> simp <;> ring

/-- **Bilateralidade**: `ξ(½ − u + it) = conj ξ(½ + u + it)`; `|ξ|` é par em `u`. -/
theorem xi_bilateral (u t : ℝ) :
    riemannXi ((1 / 2 : ℂ) - u + t * I) = conj (riemannXi ((1 / 2 : ℂ) + u + t * I)) ∧
      ‖riemannXi ((1 / 2 : ℂ) - u + t * I)‖ = ‖riemannXi ((1 / 2 : ℂ) + u + t * I)‖ := by
  have h : riemannXi ((1 / 2 : ℂ) - u + t * I) = conj (riemannXi ((1 / 2 : ℂ) + u + t * I)) := by
    rw [← espelho_coord, xi_espelho]
  exact ⟨h, by rw [h, Complex.norm_conj]⟩

/-- **A matriz diagonal** `B = diag(ξ(s), ξ(1 − s̄))` tem `det B = |ξ(s)|²`. -/
theorem det_B (s : ℂ) :
    (Matrix.diagonal ![riemannXi s, riemannXi (1 - conj s)]).det = (normSq (riemannXi s) : ℂ) := by
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp [xi_espelho, Complex.mul_conj]

/-- **Soma e diferença**: `|a + ā|² + |a − ā|² = 4|a|²`. -/
theorem soma_diferenca (a : ℂ) : ‖a + conj a‖ ^ 2 + ‖a - conj a‖ ^ 2 = 4 * ‖a‖ ^ 2 := by
  simp only [Complex.sq_norm, normSq_apply, add_re, add_im, sub_re, sub_im, conj_re, conj_im]; ring

theorem SD_zero_iff (a : ℂ) : (a + conj a = 0 ∧ a - conj a = 0) ↔ a = 0 := by
  constructor
  · rintro ⟨h1, h2⟩; linear_combination (h1 + h2) / 2
  · rintro rfl; simp

/-- **O cruzamento unificado**: `(|S|² + |D|²)/4 = det A(ξ(s₊)) = |ξ(s₊)|²` e `ξ(s₊)·ξ(s₋) = det A(ξ(s₊))`,
com `s₋ = 1 − s̄₊`. Quatro escritas do **mesmo** número. -/
theorem cruzamento (s : ℂ) :
    (‖riemannXi s + riemannXi (1 - conj s)‖ ^ 2 + ‖riemannXi s - riemannXi (1 - conj s)‖ ^ 2) / 4 =
        (matA (riemannXi s)).det ∧
      (matA (riemannXi s)).det = ‖riemannXi s‖ ^ 2 ∧
      riemannXi s * riemannXi (1 - conj s) = (((matA (riemannXi s)).det : ℝ) : ℂ) := by
  have hd : (matA (riemannXi s)).det = ‖riemannXi s‖ ^ 2 := by rw [det_matA, Complex.sq_norm]
  refine ⟨?_, hd, ?_⟩
  · rw [xi_espelho, soma_diferenca, hd]; ring
  · rw [xi_espelho, Complex.mul_conj, det_matA]

/-- **Critério `S = D = 0`** na faixa: `S = D = 0 ⟺ ζ(s₊) = 0`. -/
theorem criterio_SD {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    (riemannXi s + riemannXi (1 - conj s) = 0 ∧ riemannXi s - riemannXi (1 - conj s) = 0) ↔
      riemannZeta s = 0 := by
  have hs1 : s ≠ 1 := by intro h; rw [h, one_re] at h1; exact lt_irrefl _ h1
  rw [xi_espelho, SD_zero_iff, riemannXi_eq_zero_iff h0 hs1]

/-- **A simetria não obriga zero**: `a = 3 + 4i` satisfaz a identidade (`36 + 64 = 100`) e `a ≠ 0`. -/
theorem simetria_nao_obriga : ∃ a : ℂ, a ≠ 0 ∧ ‖a + conj a‖ ^ 2 + ‖a - conj a‖ ^ 2 = 100 := by
  refine ⟨3 + 4 * I, ?_, ?_⟩
  · intro h; have := congrArg Complex.re h; norm_num at this
  · rw [soma_diferenca, Complex.sq_norm, normSq_apply]; norm_num

/-! ## 2. Zero coletivo não é zero individual -/

/-- **Zero coletivo**: para quaisquer três valores, `(b − c)a + (c − a)b + (a − b)c = 0`. -/
theorem zero_coletivo (a b c : ℂ) : (b - c) * a + (c - a) * b + (a - b) * c = 0 := by ring

/-- O exemplo `ζ(2), ζ(3), ζ(4)`: a composição é **exatamente** nula, um peso é não nulo e nenhum valor é zero. -/
theorem zero_coletivo_zeta :
    (riemannZeta 3 - riemannZeta 4) * riemannZeta 2 + (riemannZeta 4 - riemannZeta 2) * riemannZeta 3 +
        (riemannZeta 2 - riemannZeta 3) * riemannZeta 4 = 0 ∧
      riemannZeta 4 - riemannZeta 2 ≠ 0 ∧
      riemannZeta 2 ≠ 0 ∧ riemannZeta 3 ≠ 0 ∧ riemannZeta 4 ≠ 0 := by
  refine ⟨zero_coletivo _ _ _, ?_, ?_, ?_, ?_⟩
  · rw [riemannZeta_two, riemannZeta_four]
    intro h
    have h' : ((π ^ 4 / 90 - π ^ 2 / 6 : ℝ) : ℂ) = 0 := by push_cast; exact h
    have h'' : π ^ 4 / 90 - π ^ 2 / 6 = 0 := by exact_mod_cast h'
    have hp := Real.pi_pos
    have hlt := Real.pi_lt_d2
    have hq : 0 < 15 - π ^ 2 := by nlinarith
    nlinarith [mul_pos hq (by positivity : (0 : ℝ) < π ^ 2)]
  all_goals exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)

/-- **Cancelamento de dois pontos** com peso dependente dos valores: sempre exato, nunca informativo. -/
theorem dois_pontos (f : ℂ → ℂ) (s₁ s₂ : ℂ) (h : f s₂ ≠ 0) : f s₁ + (-(f s₁ / f s₂)) * f s₂ = 0 := by
  field_simp; ring

/-- **Zero coletivo sem zero individual**: `exp` nunca se anula e `e⁰ + (−e⁻¹)·e¹ = 0`. -/
theorem coletivo_sem_individual : (∀ z, exp z ≠ 0) ∧ ∃ w : ℂ, w ≠ 0 ∧ exp 0 + w * exp 1 = 0 := by
  refine ⟨exp_ne_zero, -(exp 1)⁻¹, by simp [exp_ne_zero], ?_⟩
  rw [exp_zero, neg_mul, inv_mul_cancel₀ (exp_ne_zero 1)]; ring

/-- **A equação funcional é uma composição identicamente nula**: `ζ(1 − s) − χ̃(s)ζ(s) = 0`. -/
theorem composicao_funcional {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs1 : s ≠ 1) :
    riemannZeta (1 - s) - 2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * riemannZeta s = 0 := by
  rw [riemannZeta_one_sub hs hs1, sub_self]

/-- Fora da faixa e fora dos pares negativos, `ζ` não se anula. -/
theorem nao_zero {s : ℂ} (ht : ¬ ATK.ZetaSimetria.Trivial s) (hre : s.re ≤ 0 ∨ 1 ≤ s.re) :
    riemannZeta s ≠ 0 := by
  intro hz
  obtain ⟨-, h0, h1⟩ := (ATK.ZetaSimetria.mem_Z_iff_nao_trivial s).mpr ⟨hz, ht⟩
  rcases hre with h | h <;> linarith

/-- No semiplano `Re ≤ 0`, fora do eixo real, `ζ` não se anula. -/
theorem semiplano_esquerdo (x y : ℝ) (hx : x ≤ 0) (hy : y ≠ 0) : riemannZeta (x + y * I) ≠ 0 := by
  refine nao_zero ?_ (Or.inl (by simpa using hx))
  rintro ⟨n, hn⟩
  have := congrArg Complex.im hn
  simp at this
  exact hy this

/-- **`ζ(−½) ≠ 0`**: `−½` não é zero trivial. -/
theorem zeta_menos_meio : riemannZeta (-1 / 2) ≠ 0 := by
  refine nao_zero ?_ (Or.inl (by norm_num))
  rintro ⟨n, hn⟩
  have := congrArg Complex.re hn
  norm_num at this
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- **A sequência `qₙ = −1/(2n+1) + i·10¹⁰⁰` não contém zeros.** -/
theorem q_nao_zero (n : ℕ) : riemannZeta ((-(1 / (2 * n + 1)) : ℝ) + ((10 : ℝ) ^ 100 : ℝ) * I) ≠ 0 :=
  semiplano_esquerdo _ _ (by have : (0 : ℝ) < 1 / (2 * n + 1) := by positivity
                             linarith) (by positivity)

/-- **Zero trivial gigante**: `ζ(−2·10¹⁰⁰⁰) = 0`. -/
theorem zero_trivial_gigante : riemannZeta (-2 * 10 ^ 1000) = 0 := by
  have h := riemannZeta_neg_two_mul_nat_add_one (10 ^ 1000 - 1)
  have e : (((10 ^ 1000 - 1 : ℕ) : ℂ) + 1) = 10 ^ 1000 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]; push_cast; ring
  rwa [e] at h

/-! ## 3. Colisão: possível em família, impossível para `ζ` fixa -/

/-- Modelo de colisão `F_δ(s) = (s − c)² − δ²`. -/
def Fcol (δ c s : ℂ) : ℂ := (s - c) ^ 2 - δ ^ 2

theorem Fcol_fatora (δ c s : ℂ) : Fcol δ c s = (s - (c + δ)) * (s - (c - δ)) := by unfold Fcol; ring

theorem Fcol_zero_iff (δ c s : ℂ) : Fcol δ c s = 0 ↔ s = c + δ ∨ s = c - δ := by
  rw [Fcol_fatora, mul_eq_zero, sub_eq_zero, sub_eq_zero]

theorem hasDerivAt_Fcol (δ c s : ℂ) : HasDerivAt (Fcol δ c) (2 * (s - c)) s := by
  have h : HasDerivAt (fun x => (x - c) ^ 2 - δ ^ 2) (2 * (s - c)) s := by
    simpa using (((hasDerivAt_id' s).sub_const c).pow 2).sub_const (δ ^ 2)
  exact h

/-- **Colisão**: em `δ = 0` os zeros `c ± δ` fundem-se num zero duplo (`F(c) = F′(c) = 0`). -/
theorem colisao_dupla (c : ℂ) :
    Fcol 0 c c = 0 ∧ deriv (Fcol 0 c) c = 0 ∧ ∀ s, Fcol 0 c s = (s - c) ^ 2 :=
  ⟨by simp [Fcol], by rw [(hasDerivAt_Fcol 0 c c).deriv]; ring, fun s => by simp [Fcol]⟩

/-- **Derivada logarítmica**: `F′/F = 1/(s − ρ₊) + 1/(s − ρ₋)`. -/
theorem logderiv_Fcol {δ c s : ℂ} (hp : s ≠ c + δ) (hm : s ≠ c - δ) :
    2 * (s - c) / Fcol δ c s = 1 / (s - (c + δ)) + 1 / (s - (c - δ)) := by
  have a := sub_ne_zero.mpr hp
  have b := sub_ne_zero.mpr hm
  rw [Fcol_fatora]; field_simp; ring

/-- **Os dois polos simples fundem-se num polo de resíduo 2**: `1/(s − ρ₊) + 1/(s − ρ₋) → 2/(s − c)`. -/
theorem logderiv_limite {c s : ℂ} (hs : s ≠ c) :
    Tendsto (fun δ : ℂ => 1 / (s - (c + δ)) + 1 / (s - (c - δ))) (𝓝 0) (𝓝 (2 / (s - c))) := by
  have hc : s - c ≠ 0 := sub_ne_zero.mpr hs
  have h : ContinuousAt (fun δ : ℂ => 1 / (s - (c + δ)) + 1 / (s - (c - δ))) 0 := by
    apply ContinuousAt.add <;> apply ContinuousAt.div continuousAt_const (by fun_prop) (by simpa using hc)
  convert h.tendsto using 2
  simp only [add_zero, sub_zero]; ring

/-- Ponto da sequência ATK na altura `t`: `½ + 1/(2n+1) + it`. -/
noncomputable def pATK (t : ℝ) (n : ℕ) : ℂ := ((1 / 2 + 1 / (2 * n + 1) : ℝ) : ℂ) + t * I

/-- O ponto de encontro geométrico `½ + it`. -/
noncomputable def cT (t : ℝ) : ℂ := ((1 / 2 : ℝ) : ℂ) + t * I

theorem pATK_re (t : ℝ) (n : ℕ) : (pATK t n).re = 1 / 2 + 1 / (2 * n + 1) := by
  simp only [pATK, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]; ring

theorem pATK_ne (t : ℝ) (n : ℕ) : pATK t n ≠ cT t := by
  intro h
  have := congrArg Complex.re h
  rw [pATK_re] at this
  simp [cT] at this
  have : (0 : ℝ) < 1 / (2 * n + 1) := by positivity
  linarith

theorem tendsto_pATK (t : ℝ) : Tendsto (pATK t) atTop (𝓝 (cT t)) := by
  have hf : Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
  have h1 : Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ) + 1)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hf
  have h2 : Tendsto (fun n : ℕ => (((1 / 2 + 1 / (2 * n + 1) : ℝ)) : ℂ) + t * I) atTop
      (𝓝 ((((1 / 2 + 0 : ℝ)) : ℂ) + t * I)) :=
    ((Complex.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.add h1)).add_const _
  rw [add_zero] at h2
  exact h2

/-- **A família ATK de colisão**: `F_{1/(2n+1)}` tem o zero `½ + 1/(2n+1) + it` fora da linha, e esses zeros
convergem ao ponto de encontro `½ + it`. -/
theorem colisao_atk (t : ℝ) :
    (∀ n : ℕ, Fcol ((1 / (2 * n + 1) : ℝ) : ℂ) (cT t) (pATK t n) = 0 ∧ (pATK t n).re ≠ 1 / 2) ∧
      Tendsto (pATK t) atTop (𝓝 (cT t)) := by
  refine ⟨fun n => ⟨?_, ?_⟩, tendsto_pATK t⟩
  · rw [Fcol_zero_iff]; left
    simp only [pATK, cT]; push_cast; ring
  · rw [pATK_re]
    have : (0 : ℝ) < 1 / (2 * n + 1) := by positivity
    linarith

/-- **`ζ` não admite colisão**: se `sₙ → c` com `sₙ ≠ c`, então `ζ(sₙ) ≠ 0` para `n` grande (vale também em
`c = 1`, o polo). -/
theorem sem_colisao {s : ℕ → ℂ} {c : ℂ} (hs : Tendsto s atTop (𝓝 c)) (hne : ∀ n, s n ≠ c) :
    ∀ᶠ n in atTop, riemannZeta (s n) ≠ 0 := by
  have hev := nao_acumulacao_iff.mp (sem_acumulacao_zeta c)
  have hs' : Tendsto s atTop (𝓝[≠] c) := tendsto_nhdsWithin_iff.mpr ⟨hs, Eventually.of_forall hne⟩
  exact hs'.eventually hev

/-- **Em cada altura `t`, a sequência ATK só toca zeros de `ζ` para finitos `n`.** -/
theorem atk_finitos (t : ℝ) : {n : ℕ | riemannZeta (pATK t n) = 0}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (sem_colisao (tendsto_pATK t) (pATK_ne t))
  refine (Set.finite_lt_nat N).subset fun n hn => ?_
  by_contra hc
  exact hN n (not_lt.mp hc) hn

/-- **Estabilização** (genérico): num zero `f(ρ) = 0` com `f′(ρ) = f′`, `|f(ρ+u)|²/u² → |f′|²` (`u` real). -/
theorem estabilizacao {f : ℂ → ℂ} {f' ρ : ℂ} (hf : HasDerivAt f f' ρ) (h0 : f ρ = 0) :
    Tendsto (fun u : ℝ => ‖f (ρ + u)‖ ^ 2 / u ^ 2) (𝓝[≠] 0) (𝓝 (‖f'‖ ^ 2)) := by
  have h1 : HasDerivAt (fun z : ℂ => f (ρ + z)) f' ((0 : ℝ) : ℂ) :=
    HasDerivAt.comp_const_add ρ _ (by simpa using hf)
  have h2 : HasDerivAt (fun u : ℝ => f (ρ + u)) f' 0 := h1.comp_ofReal
  have h3 := hasDerivAt_iff_tendsto_slope_zero.mp h2
  have h4 := ((continuous_norm.tendsto f').comp h3).pow 2
  refine h4.congr fun u => ?_
  simp [h0, mul_pow, div_eq_inv_mul]

/-- **A estabilização no primeiro zero certificado**: `|ζ(ρ₁+u)|²/u² → |ζ′(ρ₁)|² > 0`,
`|ξ(ρ₁+u)|²/u² → |ξ′(ρ₁)|²`, e `|ξ(ρ₁ − u)| = |ξ(ρ₁ + u)|` (bilateral). Assinatura de zero **simples na linha**. -/
theorem estabilizacao_primeiro_zero : ∃ ρ ∈ ATK.ZetaSimetria.Z, ρ.re = 1 / 2 ∧
    ρ ∈ closedBall z0 ((rr : ℚ) : ℝ) ∧ 0 < ‖deriv riemannZeta ρ‖ ^ 2 ∧
    Tendsto (fun u : ℝ => ‖riemannZeta (ρ + u)‖ ^ 2 / u ^ 2) (𝓝[≠] 0) (𝓝 (‖deriv riemannZeta ρ‖ ^ 2)) ∧
    Tendsto (fun u : ℝ => ‖riemannXi (ρ + u)‖ ^ 2 / u ^ 2) (𝓝[≠] 0) (𝓝 (‖deriv riemannXi ρ‖ ^ 2)) ∧
    ∀ u : ℝ, ‖riemannXi (ρ - u)‖ = ‖riemannXi (ρ + u)‖ := by
  obtain ⟨ρ, hρ, hre, hB, hd⟩ := ATK.ZeroClasses.Escalas.primeiro_zero_simples
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, one_re] at hre; norm_num at hre
  have hx0 : riemannXi ρ = 0 := (riemannXi_eq_zero_iff hρ.2.1 hρ1).mpr hρ.1
  refine ⟨ρ, hρ, hre, hB, by positivity, ?_, ?_, fun u => ?_⟩
  · exact estabilizacao (differentiableAt_riemannZeta hρ1).hasDerivAt hρ.1
  · exact estabilizacao (differentiable_riemannXi ρ).hasDerivAt hx0
  · have e : ρ - u = 1 - conj (ρ + u) := by
      apply Complex.ext <;> simp [hre] <;> ring
    rw [e, xi_espelho, Complex.norm_conj]

/-! ## 4. Onde exatamente: os certificados -/

/-- **Certificado de existência** (contração): se `‖1 − f′/c‖ ≤ ½` no disco `B(z₀, r)` e `‖f(z₀)/c‖ ≤ r/2`,
então `f` tem **exatamente um** zero em `B(z₀, r)`, e ele é simples. -/
theorem certificado_existencia {f : ℂ → ℂ} {z0 c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hc : c ≠ 0)
    (hd : ∀ z ∈ closedBall z0 r, DifferentiableAt ℂ f z)
    (hder : ∀ z ∈ closedBall z0 r, ‖1 - deriv f z / c‖ ≤ 1 / 2)
    (h0 : ‖f z0 / c‖ ≤ r / 2) :
    ∃ ρ ∈ closedBall z0 r, f ρ = 0 ∧ deriv f ρ ≠ 0 ∧ ∀ w ∈ closedBall z0 r, f w = 0 → w = ρ := by
  set g : ℂ → ℂ := fun z => z - f z / c with hg
  set B := closedBall z0 r with hBdef
  have hgd : ∀ z ∈ B, HasDerivAt g (1 - deriv f z / c) z := fun z hz =>
    (hasDerivAt_id z).sub ((hd z hz).hasDerivAt.div_const c)
  have lip : LipschitzOnWith (1 / 2) g B := by
    apply (convex_closedBall z0 r).lipschitzOnWith_of_nnnorm_deriv_le
    · intro u hu; exact (hgd u hu).differentiableAt
    · intro u hu
      rw [← NNReal.coe_le_coe, coe_nnnorm, (hgd u hu).deriv]
      simpa using hder u hu
  have hz0 : z0 ∈ B := mem_closedBall_self hr
  have maps : MapsTo g B B := by
    intro z hz
    have hl := lip.dist_le_mul z hz z0 hz0
    have h1 : dist (g z0) z0 ≤ r / 2 := by
      rw [dist_eq_norm]
      have e : g z0 - z0 = -(f z0 / c) := by simp [hg]
      rw [e, norm_neg]; exact h0
    rw [hBdef, mem_closedBall] at hz ⊢
    calc dist (g z) z0 ≤ dist (g z) (g z0) + dist (g z0) z0 := dist_triangle _ _ _
      _ ≤ (1 / 2 : NNReal) * dist z z0 + r / 2 := add_le_add hl h1
      _ ≤ (1 / 2 : ℝ) * r + r / 2 := by push_cast; gcongr
      _ = r := by ring
  have fixo : ∀ z, g z = z ↔ f z = 0 := by
    intro z
    simp only [hg]
    constructor
    · intro h
      have : f z / c = 0 := by linear_combination -h
      exact (div_eq_zero_iff.mp this).resolve_right hc
    · intro h; rw [h]; simp
  have hK : ContractingWith (1 / 2) (maps.restrict g B B) :=
    ⟨by rw [← NNReal.coe_lt_coe]; norm_num, lip.mapsToRestrict maps⟩
  obtain ⟨y, hyB, hyfix, -⟩ := hK.exists_fixedPoint' isClosed_closedBall.isComplete maps hz0
    (edist_ne_top _ _)
  have hy0 : f y = 0 := (fixo y).mp hyfix
  refine ⟨y, hyB, hy0, fun hd0 => ?_, fun w hw hw0 => ?_⟩
  · have := hder y hyB
    rw [hd0, zero_div, sub_zero, norm_one] at this
    norm_num at this
  · have hwf := (fixo w).mpr hw0
    have hl := lip.dist_le_mul w hw y hyB
    rw [hwf, show g y = y from hyfix] at hl
    have : dist w y = 0 := by
      have := dist_nonneg (x := w) (y := y)
      push_cast at hl
      linarith
    exact dist_eq_zero.mp this

/-- **Certificado de exclusão**: se `‖f′‖ ≤ M` no disco e `M·r < ‖f(z₀)‖`, o disco não tem zeros. -/
theorem certificado_exclusao {f : ℂ → ℂ} {z0 : ℂ} {r M : ℝ}
    (hd : ∀ z ∈ closedBall z0 r, DifferentiableAt ℂ f z) (hb : ∀ z ∈ closedBall z0 r, ‖deriv f z‖ ≤ M)
    (hM : M * r < ‖f z0‖) : ∀ z ∈ closedBall z0 r, f z ≠ 0 := by
  intro z hz h0
  have hr : 0 ≤ r := le_trans dist_nonneg hz
  have hz0 : z0 ∈ closedBall z0 r := mem_closedBall_self hr
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hb z0 hz0)
  have hmv := (convex_closedBall z0 r).norm_image_sub_le_of_norm_deriv_le hd hb hz0 hz
  rw [h0, zero_sub, norm_neg] at hmv
  have hzr : ‖z - z0‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hz
  nlinarith

/-- Um disco **inteiramente fora da linha**, dentro da faixa. -/
def DiscoFora (z0 : ℂ) (r : ℝ) : Prop := r < |z0.re - 1 / 2| ∧ r < z0.re ∧ r < 1 - z0.re

theorem discoFora_pontos {z0 z : ℂ} {r : ℝ} (hD : DiscoFora z0 r) (hz : z ∈ closedBall z0 r) :
    0 < z.re ∧ z.re < 1 ∧ z.re ≠ 1 / 2 := by
  have h : |z.re - z0.re| ≤ r := by
    have := Complex.abs_re_le_norm (z - z0)
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [sub_re] at this
    linarith
  obtain ⟨h1, h2, h3⟩ := hD
  rw [abs_le] at h
  refine ⟨by linarith, by linarith, fun he => ?_⟩
  have : |z0.re - 1 / 2| ≤ r := by rw [abs_le]; constructor <;> linarith
  linarith

/-- **Certificado fora da linha ⟹ zero simples fora da linha** (e portanto `¬RH`). -/
theorem certificado_refuta {z0 c : ℂ} {r : ℝ} (hr : 0 ≤ r) (hc : c ≠ 0) (hD : DiscoFora z0 r)
    (hder : ∀ z ∈ closedBall z0 r, ‖1 - deriv riemannZeta z / c‖ ≤ 1 / 2)
    (h0 : ‖riemannZeta z0 / c‖ ≤ r / 2) :
    (∃ ρ ∈ closedBall z0 r, ForaCritico ρ ∧ deriv riemannZeta ρ ≠ 0) ∧ ¬ RiemannHypothesis := by
  have hd : ∀ z ∈ closedBall z0 r, DifferentiableAt ℂ riemannZeta z := fun z hz =>
    differentiableAt_riemannZeta fun h => by
      have := (discoFora_pontos hD hz).2.1
      rw [h, one_re] at this
      exact lt_irrefl _ this
  obtain ⟨ρ, hρB, hρ0, hρd, -⟩ := certificado_existencia hr hc hd hder h0
  obtain ⟨a, b, e⟩ := discoFora_pontos hD hρB
  exact ⟨⟨ρ, hρB, ⟨⟨hρ0, a, b⟩, e⟩, hρd⟩, hFora_iff.mp ⟨ρ, hρ0, a, b, e⟩⟩

/-- **Robustez**: todo zero simples fora da linha é certificado por **qualquer** dado de precisão finita
suficiente — centro `z₀` a menos de `r/4` e inclinação `c` a menos de `|ζ′(ρ)|/8`, para todo `r < r₀`. -/
theorem certificado_robusto {ρ : ℂ} (hρ : ForaCritico ρ) (hs : deriv riemannZeta ρ ≠ 0) :
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ → ∀ z0 c : ℂ, ‖z0 - ρ‖ ≤ r / 4 →
      ‖c - deriv riemannZeta ρ‖ ≤ ‖deriv riemannZeta ρ‖ / 8 →
      c ≠ 0 ∧ DiscoFora z0 r ∧ (∀ z ∈ closedBall z0 r, ‖1 - deriv riemannZeta z / c‖ ≤ 1 / 2) ∧
        ‖riemannZeta z0 / c‖ ≤ r / 2 := by
  set c' := deriv riemannZeta ρ with hc'
  set a := ‖c'‖ with ha
  have hapos : 0 < a := norm_pos_iff.mpr hs
  have hρ0 : 0 < ρ.re := hρ.1.2.1
  have hρ1' : ρ.re < 1 := hρ.1.2.2
  have hρh : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hρ.2)
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, one_re] at hρ1'; exact lt_irrefl _ hρ1'
  have hcont : ContinuousAt (deriv riemannZeta) ρ :=
    ((analyticOn_riemannZeta ρ hρ1).deriv).continuousAt
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.mp hcont (a / 8) (by positivity)
  set m := min |ρ.re - 1 / 2| (min ρ.re (1 - ρ.re)) with hm
  have hm0 : 0 < m := lt_min hρh (lt_min hρ0 (by linarith))
  have hm1 : m ≤ |ρ.re - 1 / 2| := min_le_left _ _
  have hm2 : m ≤ ρ.re := (min_le_right _ _).trans (min_le_left _ _)
  have hm3 : m ≤ 1 - ρ.re := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨min (δ / 2) (m / 2), lt_min (by linarith) (by linarith), fun r hr hr0 z0 c hz0 hc => ?_⟩
  have hrδ : r < δ / 2 := lt_of_lt_of_le hr0 (min_le_left _ _)
  have hrm : r < m / 2 := lt_of_lt_of_le hr0 (min_le_right _ _)
  -- |c| ≥ 7a/8
  have hcn : 7 * a / 8 ≤ ‖c‖ := by
    have := norm_sub_norm_le c' c
    rw [norm_sub_rev] at this
    linarith
  have hcpos : 0 < ‖c‖ := by linarith
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  -- derivada perto de ρ
  have hder_near : ∀ z, ‖z - ρ‖ < δ → ‖deriv riemannZeta z - c'‖ < a / 8 := by
    intro z hz
    have := hball (x := z) (by rwa [dist_eq_norm])
    rwa [dist_eq_norm] at this
  have hre0 : |z0.re - ρ.re| ≤ r / 4 := by
    have := Complex.abs_re_le_norm (z0 - ρ); rw [sub_re] at this; linarith
  refine ⟨hc0, ⟨?_, ?_, ?_⟩, fun z hz => ?_, ?_⟩
  · have := abs_sub_abs_le_abs_sub (ρ.re - 1 / 2) (z0.re - 1 / 2)
    rw [show ρ.re - 1 / 2 - (z0.re - 1 / 2) = -(z0.re - ρ.re) by ring, abs_neg] at this
    linarith
  · rw [abs_le] at hre0; linarith
  · rw [abs_le] at hre0; linarith
  · have hzr : ‖z - z0‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hz
    have hzρ : ‖z - ρ‖ < δ := by
      calc ‖z - ρ‖ = ‖(z - z0) + (z0 - ρ)‖ := by ring_nf
        _ ≤ ‖z - z0‖ + ‖z0 - ρ‖ := norm_add_le _ _
        _ < δ := by linarith
    have h1 := hder_near z hzρ
    have e : 1 - deriv riemannZeta z / c = (c - deriv riemannZeta z) / c := by field_simp
    rw [e, norm_div, div_le_iff₀ hcpos]
    have h2 : ‖c - deriv riemannZeta z‖ ≤ ‖c - c'‖ + ‖deriv riemannZeta z - c'‖ := by
      calc ‖c - deriv riemannZeta z‖ = ‖(c - c') - (deriv riemannZeta z - c')‖ := by ring_nf
        _ ≤ ‖c - c'‖ + ‖deriv riemannZeta z - c'‖ := norm_sub_le _ _
    nlinarith
  · -- valor no centro: teorema do valor médio no disco B(ρ, r/4)
    have hsub : ∀ z ∈ closedBall ρ (r / 4), ‖z - ρ‖ < δ := fun z hz => by
      rw [mem_closedBall, dist_eq_norm] at hz; linarith
    have hdiff : ∀ z ∈ closedBall ρ (r / 4), DifferentiableAt ℂ riemannZeta z := by
      intro z hz
      refine differentiableAt_riemannZeta fun h => ?_
      rw [mem_closedBall, dist_eq_norm, h] at hz
      have := Complex.abs_re_le_norm (1 - ρ)
      rw [sub_re, one_re] at this
      have := abs_of_pos (show (0 : ℝ) < 1 - ρ.re by linarith)
      linarith
    have hbound : ∀ z ∈ closedBall ρ (r / 4), ‖deriv riemannZeta z‖ ≤ 9 * a / 8 := by
      intro z hz
      have := hder_near z (hsub z hz)
      have h3 := norm_sub_norm_le (deriv riemannZeta z) c'
      linarith
    have hρB : ρ ∈ closedBall ρ (r / 4) := mem_closedBall_self (by linarith)
    have hz0B : z0 ∈ closedBall ρ (r / 4) := by rwa [mem_closedBall, dist_eq_norm]
    have hmv := (convex_closedBall ρ (r / 4)).norm_image_sub_le_of_norm_deriv_le hdiff hbound hρB hz0B
    rw [hρ.1.1, sub_zero] at hmv
    rw [norm_div, div_le_iff₀ hcpos]
    nlinarith

/-- **O critério exato**: existe zero **simples** fora da linha ⟺ existe um disco fora da linha com o certificado
de contração. -/
theorem fora_simples_iff_certificado :
    (∃ ρ, ForaCritico ρ ∧ deriv riemannZeta ρ ≠ 0) ↔
      ∃ z0 c : ℂ, ∃ r : ℝ, 0 ≤ r ∧ c ≠ 0 ∧ DiscoFora z0 r ∧
        (∀ z ∈ closedBall z0 r, ‖1 - deriv riemannZeta z / c‖ ≤ 1 / 2) ∧ ‖riemannZeta z0 / c‖ ≤ r / 2 := by
  constructor
  · rintro ⟨ρ, hρ, hs⟩
    obtain ⟨r₀, hr₀, H⟩ := certificado_robusto hρ hs
    obtain ⟨hc, hD, hder, h0⟩ := H (r₀ / 2) (by linarith) (by linarith) ρ (deriv riemannZeta ρ)
      (by simp; linarith) (by simp; positivity)
    exact ⟨ρ, _, r₀ / 2, by linarith, hc, hD, hder, h0⟩
  · rintro ⟨z0, c, r, hr, hc, hD, hder, h0⟩
    obtain ⟨⟨ρ, -, hρ, hs⟩, -⟩ := certificado_refuta hr hc hD hder h0
    exact ⟨ρ, hρ, hs⟩

/-! ## 5. O encontro no mundo hipotético -/

/-- `ρ` é o **primeiro** zero fora da linha: menor altura positiva. -/
def PrimeiroFora (ρ : ℂ) : Prop :=
  ForaCritico ρ ∧ 0 < ρ.im ∧ ∀ ρ', ForaCritico ρ' → 0 < ρ'.im → ρ.im ≤ ρ'.im

/-- **No mundo hipotético existe um primeiro zero fora da linha.** -/
theorem primeiro_fora (H : HFora) : ∃ ρ, PrimeiroFora ρ := by
  obtain ⟨ρ0, h0⟩ := hFora_iff_fora.mp H
  have hpos : ∃ ρ1, ForaCritico ρ1 ∧ 0 < ρ1.im := by
    rcases lt_or_gt_of_ne (ATK.ZetaSimetria.im_ne_zero_of_mem_Z h0.1) with hn | hp
    · refine ⟨conj ρ0, ⟨ATK.ZetaSimetria.espelho_mem_Z h0.1, by simpa using h0.2⟩, by simpa using hn⟩
    · exact ⟨ρ0, h0, hp⟩
  obtain ⟨ρ1, h1, h1p⟩ := hpos
  set S := {ρ | ForaCritico ρ ∧ |ρ.im| ≤ ρ1.im} ∩ {ρ | 0 < ρ.im} with hS
  have hfin : S.Finite := (finitos_abaixo ρ1.im).subset inter_subset_left
  have hne : S.Nonempty := ⟨ρ1, ⟨h1, by rw [abs_of_pos h1p]⟩, h1p⟩
  obtain ⟨ρ, ⟨⟨hρ, hρle⟩, hρp⟩, hmin⟩ := Set.exists_min_image S Complex.im hfin hne
  refine ⟨ρ, hρ, hρp, fun ρ' h' hp' => ?_⟩
  by_cases hc : |ρ'.im| ≤ ρ1.im
  · exact hmin ρ' ⟨⟨h', hc⟩, hp'⟩
  · push Not at hc
    rw [abs_of_pos hp'] at hc
    rw [abs_of_pos hρp] at hρle
    linarith

/-- **A altura do primeiro encontro é única.** -/
theorem altura_unica {ρ ρ' : ℂ} (h : PrimeiroFora ρ) (h' : PrimeiroFora ρ') : ρ.im = ρ'.im :=
  le_antisymm (h.2.2 ρ' h'.1 h'.2.1) (h'.2.2 ρ h.1 h.2.1)

/-- **O encontro no mundo hipotético**, cruzando o kernel com a literatura (hipóteses nomeadas
`VerificadoAte H` — Platt–Trudgian — e `RegiaoClassica R` — Bellotti–Trudgian–Yang). O primeiro zero fora da
linha `ρ* = β + iγ*` tem: `γ*` único, `γ* > H`, `β` na janela, o quarteto inteiro de zeros, o par `ρ*, 1 − ρ̄*`
com ponto médio **`½ + iγ*`** na linha, e abaixo de `γ*` nenhum zero fora da linha. -/
theorem encontro_hipotetico {Hv R : ℝ} (hV : ATK.ZeroClasses.Escalas.VerificadoAte Hv) (hH : 3 ≤ Hv)
    (hR : ATK.ZeroClasses.Escalas.RegiaoClassica R) (H : HFora) :
    ∃ ρ, PrimeiroFora ρ ∧ Hv < ρ.im ∧ 1 / (R * Real.log ρ.im) < ρ.re ∧
      ρ.re < 1 - 1 / (R * Real.log ρ.im) ∧
      ForaCritico (ATK.ZetaSimetria.torcao ρ) ∧ ForaCritico (conj ρ) ∧ ForaCritico (1 - ρ) ∧
      (ρ + ATK.ZetaSimetria.torcao ρ) / 2 = (1 / 2 : ℂ) + ρ.im * I ∧
      (∀ ρ', PrimeiroFora ρ' → ρ'.im = ρ.im) ∧
      (∀ ρ', ForaCritico ρ' → 0 < ρ'.im → ¬ ρ'.im < ρ.im) := by
  obtain ⟨ρ, hP⟩ := primeiro_fora H
  obtain ⟨hρ, hp, hmin⟩ := hP
  obtain ⟨hγ, hβ1, hβ2⟩ := ATK.ZeroClasses.Escalas.janela hV hH hR hρ
  rw [abs_of_pos hp] at hγ hβ1 hβ2
  refine ⟨ρ, ⟨hρ, hp, hmin⟩, hγ, hβ1, hβ2, ATK.ZeroClasses.MundoFora.torcao_fora hρ,
    ⟨ATK.ZetaSimetria.espelho_mem_Z hρ.1, by simpa using hρ.2⟩, ⟨ATK.ZetaSimetria.tensao_mem_Z hρ.1, ?_⟩,
    ?_, fun ρ' h' => altura_unica h' ⟨hρ, hp, hmin⟩, fun ρ' h' hp' hlt => absurd (hmin ρ' h' hp') (not_le.mpr hlt)⟩
  · show (ATK.ZetaSimetria.tensao ρ).re ≠ 1 / 2
    rw [ATK.ZetaSimetria.re_tensao]
    intro h; exact hρ.2 (by linarith)
  · apply Complex.ext <;> simp [ATK.ZetaSimetria.torcao]

/-- `δ` da reta ATK `n = 10¹⁰⁰⁰ − 1` é `1/(2·10¹⁰⁰⁰ + 1)`. -/
theorem delta_gigante :
    ATK.ZeroClasses.Construcao.delta (10 ^ 1000 - 1) = 1 / (2 * 10 ^ 1000 + 1) := by
  unfold ATK.ZeroClasses.Construcao.delta
  rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num))]
  push_cast; ring_nf

/-- O candidato gigante `ρ = ½ + 1/(2·10¹⁰⁰⁰ + 1) + i·10¹⁰⁰`. -/
noncomputable def rhoGig : ℂ := ((1 / 2 + 1 / (2 * 10 ^ 1000 + 1) : ℝ) : ℂ) + ((10 : ℝ) ^ 100 : ℝ) * I

/-- **O candidato gigante**: fora da linha, na faixa, acima de `H`, **dentro** da janela de 2026 (nada conhecido o
exclui), e seu estado é `ζ(ρ) = 0 ⟺ det A(ξ(ρ)) = 0 ⟺ S = D = 0` — **não calculado**. -/
theorem candidato_gigante :
    rhoGig.re ≠ 1 / 2 ∧ 0 < rhoGig.re ∧ rhoGig.re < 1 ∧ (3000175332800 : ℝ) < rhoGig.im ∧
      1 / (4.896 * Real.log rhoGig.im) < rhoGig.re ∧ rhoGig.re < 1 - 1 / (4.896 * Real.log rhoGig.im) ∧
      (riemannZeta rhoGig = 0 ↔ (matA (riemannXi rhoGig)).det = 0) ∧
      (riemannZeta rhoGig = 0 ↔ (riemannXi rhoGig + riemannXi (1 - conj rhoGig) = 0 ∧
        riemannXi rhoGig - riemannXi (1 - conj rhoGig) = 0)) := by
  have hre : rhoGig.re = 1 / 2 + ATK.ZeroClasses.Construcao.delta (10 ^ 1000 - 1) := by
    rw [delta_gigante]; simp only [rhoGig, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im]; ring
  have him : rhoGig.im = (10 : ℝ) ^ 100 := by
    simp only [rhoGig, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]; ring
  have hd := ATK.ZeroClasses.Construcao.delta_pos (10 ^ 1000 - 1)
  have hd3 := ATK.ZeroClasses.Construcao.delta_le (10 ^ 1000 - 1)
  have hH : (3000175332800 : ℝ) < rhoGig.im := by rw [him]; norm_num
  have hw := ATK.ZeroClasses.Escalas.retas_atk_acima_de_H hH (10 ^ 1000 - 1)
  have h0 : 0 < rhoGig.re := by rw [hre]; linarith
  have h1 : rhoGig.re < 1 := by rw [hre]; linarith
  have hs : riemannXi rhoGig = 0 ↔ riemannZeta rhoGig = 0 :=
    riemannXi_eq_zero_iff h0 (by intro h; rw [h, one_re] at h1; exact lt_irrefl _ h1)
  refine ⟨by rw [hre]; linarith, h0, h1, hH, by rw [← hre] at hw; exact hw.1, by rw [← hre] at hw; exact hw.2,
    ?_, (criterio_SD h0 h1).symm⟩
  rw [det_matA_eq_zero_iff, hs]

end ATK.ZeroClasses.Encontro

#print axioms ATK.ZeroClasses.Encontro.det_matA
#print axioms ATK.ZeroClasses.Encontro.det_matA_eq_zero_iff
#print axioms ATK.ZeroClasses.Encontro.matA_mul
#print axioms ATK.ZeroClasses.Encontro.det_zeta
#print axioms ATK.ZeroClasses.Encontro.xi_espelho
#print axioms ATK.ZeroClasses.Encontro.espelho_coord
#print axioms ATK.ZeroClasses.Encontro.xi_bilateral
#print axioms ATK.ZeroClasses.Encontro.det_B
#print axioms ATK.ZeroClasses.Encontro.soma_diferenca
#print axioms ATK.ZeroClasses.Encontro.SD_zero_iff
#print axioms ATK.ZeroClasses.Encontro.cruzamento
#print axioms ATK.ZeroClasses.Encontro.criterio_SD
#print axioms ATK.ZeroClasses.Encontro.simetria_nao_obriga
#print axioms ATK.ZeroClasses.Encontro.zero_coletivo
#print axioms ATK.ZeroClasses.Encontro.zero_coletivo_zeta
#print axioms ATK.ZeroClasses.Encontro.dois_pontos
#print axioms ATK.ZeroClasses.Encontro.coletivo_sem_individual
#print axioms ATK.ZeroClasses.Encontro.composicao_funcional
#print axioms ATK.ZeroClasses.Encontro.nao_zero
#print axioms ATK.ZeroClasses.Encontro.semiplano_esquerdo
#print axioms ATK.ZeroClasses.Encontro.zeta_menos_meio
#print axioms ATK.ZeroClasses.Encontro.q_nao_zero
#print axioms ATK.ZeroClasses.Encontro.zero_trivial_gigante
#print axioms ATK.ZeroClasses.Encontro.Fcol_fatora
#print axioms ATK.ZeroClasses.Encontro.Fcol_zero_iff
#print axioms ATK.ZeroClasses.Encontro.hasDerivAt_Fcol
#print axioms ATK.ZeroClasses.Encontro.colisao_dupla
#print axioms ATK.ZeroClasses.Encontro.logderiv_Fcol
#print axioms ATK.ZeroClasses.Encontro.logderiv_limite
#print axioms ATK.ZeroClasses.Encontro.pATK_re
#print axioms ATK.ZeroClasses.Encontro.pATK_ne
#print axioms ATK.ZeroClasses.Encontro.tendsto_pATK
#print axioms ATK.ZeroClasses.Encontro.colisao_atk
#print axioms ATK.ZeroClasses.Encontro.sem_colisao
#print axioms ATK.ZeroClasses.Encontro.atk_finitos
#print axioms ATK.ZeroClasses.Encontro.estabilizacao
#print axioms ATK.ZeroClasses.Encontro.estabilizacao_primeiro_zero
#print axioms ATK.ZeroClasses.Encontro.certificado_existencia
#print axioms ATK.ZeroClasses.Encontro.certificado_exclusao
#print axioms ATK.ZeroClasses.Encontro.discoFora_pontos
#print axioms ATK.ZeroClasses.Encontro.certificado_refuta
#print axioms ATK.ZeroClasses.Encontro.certificado_robusto
#print axioms ATK.ZeroClasses.Encontro.fora_simples_iff_certificado
#print axioms ATK.ZeroClasses.Encontro.primeiro_fora
#print axioms ATK.ZeroClasses.Encontro.altura_unica
#print axioms ATK.ZeroClasses.Encontro.encontro_hipotetico
#print axioms ATK.ZeroClasses.Encontro.delta_gigante
#print axioms ATK.ZeroClasses.Encontro.candidato_gigante
