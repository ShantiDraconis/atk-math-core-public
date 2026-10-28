import ATK.ATKIAlgebra
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# ATK-I — aplicações às sete conjecturas: o que a álgebra relacional prova de fato

Cada bloco formaliza a parte **demonstrável** dos textos ATK-I sobre um problema. Nenhum fecha
uma conjectura; cada um isola a obrigação terminal que continua aberta.

* **RH** (família do texto, Bagchi): `Σ_N (D_N − D_{N+1}) = D_0 − D∞`, `D_0 = 1`; logo
  "a soma dos ganhos esgota o defeito inicial" ⟹ RH. Aberto: provar que esgota.
* **Yang–Mills**: coercividade `⟪ψ, Hψ⟫ ≥ δ‖ψ‖²` em `Ω^⊥` ⟹ todo autovalor em `Ω^⊥` é `≥ δ`;
  gaps positivos podem sumir no limite (`1/(n+1) → 0`). Aberto: construir `H` em 4D.
* **Navier–Stokes**: absorção (`c < 1`) ⟹ `Y' ≤ 2CY` ⟹ Grönwall `Y(t) ≤ Y(0)e^{2Ct}`.
  Aberto: provar a absorção para Navier–Stokes 3D sem supor regularidade.
* **BSD**: defeito inteiro `< 1` ⟹ igualdade; cotas `≤ 2` e `≥ 2` fecham o posto; regulador do
  exemplo `det !![2,1;1,3] = 5`. Aberto: as cotas para toda curva.
* **Hodge**: certificado `2z₁ + 3z₂ = α`; transição racional `D(t) = 10(1 − t)`; lei de contração
  `f(q(t)) − α = (1 − t)(f(q₀) − α)` — que **pressupõe** a solução exata. Aberto: os ciclos.
* **P vs NP**: `∀N ∃m, m > N` vale e `∃m ∀N, m > N` não; busca exaustiva `2ⁿ`; erro `1/(n+1) → 0`
  sem nunca ser `0`. Aberto: excluir todo algoritmo polinomial.
-/

open Filter Topology Finset

namespace ATK.ATKIAplicacoes

open ATK.ATKI

noncomputable section

/-! ## RH: a série telescópica dos ganhos -/

/-- `Σ_N (D_N − D_{N+1}) = D_0 − D∞` na família do texto. -/
theorem telescopica :
    HasSum (fun N => Defeito wTexto gTexto N - Defeito wTexto gTexto (N + 1))
      (Defeito wTexto gTexto 0 - ⨅ N, Defeito wTexto gTexto N) := by
  have hnn : ∀ N, 0 ≤ Defeito wTexto gTexto N - Defeito wTexto gTexto (N + 1) :=
    fun N => sub_nonneg.mpr (texto_antitone (Nat.le_succ N))
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have h : (fun n => ∑ i ∈ range n,
      (Defeito wTexto gTexto i - Defeito wTexto gTexto (i + 1))) =
      fun n => Defeito wTexto gTexto 0 - Defeito wTexto gTexto n := by
    funext n
    exact Finset.sum_range_sub' (Defeito wTexto gTexto) n
  rw [h]
  exact tendsto_const_nhds.sub texto_converge

/-- `1/(k+1) − 1/(k+2) = w_k`. -/
theorem peso_telescopico (k : ℕ) : 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 2) = wTexto k := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  unfold wTexto
  rw [div_sub_div _ _ hk1.ne' hk2.ne']
  congr 1
  ring

/-- Os pesos somam 1: `Σ 1/((k+1)(k+2)) = 1`. -/
theorem soma_pesos : HasSum wTexto 1 := by
  have h : ∀ n : ℕ, ∑ i ∈ range n, wTexto i = 1 - 1 / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, ← peso_telescopico n]
      push_cast
      ring
  rw [hasSum_iff_tendsto_nat_of_nonneg wTexto_nonneg, funext h]
  have hl := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using hl

/-- `D_0 = 1`: sem geradores, a distância de `1` a `0` é `Σ w_k = 1`. -/
theorem defeito_texto_zero : Defeito wTexto gTexto 0 = 1 := by
  unfold Defeito
  simp only [Fin.sum_univ_zero, sub_zero, one_pow, mul_one]
  rw [ciInf_const]
  exact soma_pesos.tsum_eq

/-- Se a soma dos ganhos esgota o defeito inicial, vale RH (via Bagchi). -/
theorem rh_de_telescopica
    (h : ∑' N, (Defeito wTexto gTexto N - Defeito wTexto gTexto (N + 1)) =
      Defeito wTexto gTexto 0) : RiemannHypothesis := by
  rw [telescopica.tsum_eq] at h
  exact ATK.ATKIBagchi.rh_of_texto (by linarith)

/-- A forma do texto: `Σ_N (D_N − D_{N+1}) = 1 ⟹ RH`. -/
theorem rh_de_ganhos
    (h : ∑' N, (Defeito wTexto gTexto N - Defeito wTexto gTexto (N + 1)) = 1) :
    RiemannHypothesis :=
  rh_de_telescopica (by rw [defeito_texto_zero]; exact h)

/-! ## Yang–Mills: coercividade dá gap -/

open scoped InnerProductSpace in
/-- Se `⟪ψ, Hψ⟫ ≥ δ‖ψ‖²` para todo `ψ ⊥ Ω`, todo autovalor com autovetor em `Ω^⊥` é `≥ δ`. -/
theorem gap_de_coercividade {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →ₗ[ℝ] E) (Ω : E) {δ : ℝ}
    (hc : ∀ ψ : E, ⟪Ω, ψ⟫_ℝ = 0 → δ * ‖ψ‖ ^ 2 ≤ ⟪ψ, H ψ⟫_ℝ)
    {ψ : E} {lam : ℝ} (hψ : ψ ≠ 0) (hΩ : ⟪Ω, ψ⟫_ℝ = 0) (hev : H ψ = lam • ψ) : δ ≤ lam := by
  have h := hc ψ hΩ
  rw [hev, real_inner_smul_right, real_inner_self_eq_norm_sq] at h
  exact le_of_mul_le_mul_right h (pow_pos (norm_pos_iff.mpr hψ) 2)

/-- Gaps positivos podem sumir no limite: `Δ_n = 1/(n+1) > 0` e `Δ_n → 0`. -/
theorem gaps_positivos_somem :
    (∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  ⟨fun _ => by positivity, tendsto_one_div_add_atTop_nhds_zero_nat⟩

/-! ## Navier–Stokes: absorção e Grönwall -/

/-- Absorção: `Y'/2 + νZ ≤ cνZ + CY` com `c < 1`, `ν > 0`, `Z ≥ 0` ⟹ `Y' ≤ 2CY`. -/
theorem absorcao {y' z y c ν C : ℝ} (hc : c < 1) (hν : 0 < ν) (hz : 0 ≤ z)
    (h : y' / 2 + ν * z ≤ c * ν * z + C * y) : y' ≤ 2 * C * y := by
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hc.le) hν.le) hz]

/-- Grönwall: `Y' ≤ 2CY` ⟹ `Y(t) ≤ Y(0) e^{2Ct}` para `t ≥ 0`. -/
theorem gronwall_simples {Y Y' : ℝ → ℝ} {C : ℝ} (hY : ∀ t, HasDerivAt Y (Y' t) t)
    (h : ∀ t, Y' t ≤ 2 * C * Y t) {t : ℝ} (ht : 0 ≤ t) :
    Y t ≤ Y 0 * Real.exp (2 * C * t) := by
  have hg : ∀ s, HasDerivAt (fun s => Y s * Real.exp (s * -(2 * C)))
      (Y' s * Real.exp (s * -(2 * C)) + Y s * (Real.exp (s * -(2 * C)) * -(2 * C))) s :=
    fun s => (hY s).mul (hasDerivAt_mul_const (-(2 * C))).exp
  have hanti : Antitone (fun s => Y s * Real.exp (s * -(2 * C))) := by
    apply antitone_of_deriv_nonpos (fun s => (hg s).differentiableAt)
    intro s
    rw [(hg s).deriv]
    have he := Real.exp_pos (s * -(2 * C))
    have h1 := mul_le_mul_of_nonneg_left (h s) he.le
    nlinarith
  have h0 := hanti ht
  simp only [zero_mul, Real.exp_zero, mul_one] at h0
  have hE : Real.exp (t * -(2 * C)) * Real.exp (2 * C * t) = 1 := by
    rw [← Real.exp_add, show t * -(2 * C) + 2 * C * t = 0 by ring, Real.exp_zero]
  calc Y t = Y t * Real.exp (t * -(2 * C)) * Real.exp (2 * C * t) := by
        rw [mul_assoc (Y t), hE, mul_one]
    _ ≤ Y 0 * Real.exp (2 * C * t) := mul_le_mul_of_nonneg_right h0 (Real.exp_pos _).le

/-- Regularidade condicional: absorção uniforme ⟹ `Y` não explode em tempo finito. -/
theorem ns_condicional {Y Y' Z : ℝ → ℝ} {c ν C : ℝ} (hY : ∀ t, HasDerivAt Y (Y' t) t)
    (hc : c < 1) (hν : 0 < ν) (hZ : ∀ t, 0 ≤ Z t)
    (habs : ∀ t, Y' t / 2 + ν * Z t ≤ c * ν * Z t + C * Y t) {t : ℝ} (ht : 0 ≤ t) :
    Y t ≤ Y 0 * Real.exp (2 * C * t) :=
  gronwall_simples hY (fun s => absorcao hc hν (hZ s) (habs s)) ht

/-- Os valores do texto: `δ = 1 − 1/4 − 1/3 = 5/12 > 0`. -/
theorem margem_exemplo : (1 : ℝ) - 1 / 4 - 1 / 3 = 5 / 12 ∧ (0 : ℝ) < 5 / 12 := by
  constructor <;> norm_num

/-! ## BSD: fechamento por defeito inteiro -/

/-- Defeito de posto `< 1` ⟹ postos iguais. -/
theorem fechamento_inteiro {a b : ℕ} (h : |(a : ℝ) - b| < 1) : a = b := by
  have h' : |((a : ℤ) - b : ℤ)| < 1 := by exact_mod_cast h
  have := Int.abs_lt_one_iff.mp h'
  omega

/-- Cotas certificadas fecham: `r_alg, r_an ∈ [2, 2]` ⟹ `r_alg = r_an`. -/
theorem cotas_fecham {ra rn : ℕ} (h1 : ra ≤ 2) (h2 : 2 ≤ ra) (h3 : rn ≤ 2) (h4 : 2 ≤ rn) :
    ra = rn := by
  omega

/-- O regulador do exemplo: `det !![2, 1; 1, 3] = 5`. -/
theorem regulador_exemplo : Matrix.det !![(2 : ℚ), 1; 1, 3] = 5 := by
  rw [Matrix.det_fin_two_of]
  norm_num

/-- E `h₂₂` é determinado: `2h − 1 = 5 ⟹ h = 3`. -/
theorem regulador_h22 (h : ℚ) (hh : 2 * h - 1 * 1 = 5) : h = 3 := by linarith

/-! ## Hodge: certificado racional e lei de contração -/

/-- `2z₁ + 3z₂ = α` com `z₁ = (1,0,1)`, `z₂ = (0,1,1)`, `α = (2,3,5)`. -/
theorem hodge_certificado :
    (2 : ℚ) • ![(1 : ℚ), 0, 1] + (3 : ℚ) • ![(0 : ℚ), 1, 1] = ![2, 3, 5] := by
  ext i
  fin_cases i <;> simp <;> norm_num

/-- A transição racional `q(t) = (2t, 3t, 0)`: defeito total `10(1 − t)` em `[0, 1]`. -/
theorem hodge_transicao {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |2 * t - 2| + |3 * t - 3| + |5 * t - 5| = 10 * (1 - t) := by
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  ring

/-- Lei de contração: se `f(q*) = α`, então `f((1−t)q₀ + t q*) − α = (1 − t)(f(q₀) − α)`.
Ela **pressupõe** a solução exata `q*`; não a constrói. -/
theorem contracao_relacional {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) {q0 qs : V} {α : W} (h : f qs = α) (t : K) :
    f ((1 - t) • q0 + t • qs) - α = (1 - t) • (f q0 - α) := by
  rw [map_add, map_smul, map_smul, h]
  simp only [smul_sub, sub_smul, one_smul]
  abel

/-! ## P vs NP: quantificadores e aproximação finita -/

/-- `∀N ∃m, m > N` vale; `∃m ∀N, m > N` não: trocar a ordem muda a afirmação. -/
theorem quantificadores : (∀ N : ℕ, ∃ m : ℕ, m > N) ∧ ¬ ∃ m : ℕ, ∀ N : ℕ, m > N :=
  ⟨fun N => ⟨N + 1, Nat.lt_succ_self N⟩, fun ⟨m, hm⟩ => lt_irrefl m (hm m)⟩

/-- Busca exaustiva: `2ⁿ` atribuições de `n` variáveis. -/
theorem busca_exaustiva (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by simp

/-- Aproximação finita é trivial: para cada `N` a própria linguagem serve de tabela. Por isso
"`∀ N, ∃ A_N`" não caracteriza `P`. -/
theorem aproximacao_finita_trivial {α : Type*} (L : α → Bool) (tam : α → ℕ) :
    ∀ N, ∃ A : α → Bool, ∀ x, tam x ≤ N → A x = L x :=
  fun _ => ⟨L, fun _ _ => rfl⟩

/-- Erro `1/(n+1)`: nunca é zero, mas tende a zero. Convergência não é igualdade exata. -/
theorem erro_tende_sem_zerar :
    (∀ n : ℕ, 1 / ((n : ℝ) + 1) ≠ 0) ∧ Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  ⟨fun _ => by positivity, tendsto_one_div_add_atTop_nhds_zero_nat⟩

/-! ## O navio do texto (valores ilustrativos) -/

theorem reynolds : (8 : ℝ) * 200 / (1 / 10 ^ 6) = 16 * 10 ^ 8 := by norm_num

theorem pressao_dinamica : (1 / 2 : ℝ) * 1025 * 8 ^ 2 = 32800 := by norm_num

end

end ATK.ATKIAplicacoes

#print axioms ATK.ATKIAplicacoes.telescopica
#print axioms ATK.ATKIAplicacoes.peso_telescopico
#print axioms ATK.ATKIAplicacoes.soma_pesos
#print axioms ATK.ATKIAplicacoes.defeito_texto_zero
#print axioms ATK.ATKIAplicacoes.rh_de_telescopica
#print axioms ATK.ATKIAplicacoes.rh_de_ganhos
#print axioms ATK.ATKIAplicacoes.gap_de_coercividade
#print axioms ATK.ATKIAplicacoes.gaps_positivos_somem
#print axioms ATK.ATKIAplicacoes.absorcao
#print axioms ATK.ATKIAplicacoes.gronwall_simples
#print axioms ATK.ATKIAplicacoes.ns_condicional
#print axioms ATK.ATKIAplicacoes.margem_exemplo
#print axioms ATK.ATKIAplicacoes.fechamento_inteiro
#print axioms ATK.ATKIAplicacoes.cotas_fecham
#print axioms ATK.ATKIAplicacoes.regulador_exemplo
#print axioms ATK.ATKIAplicacoes.regulador_h22
#print axioms ATK.ATKIAplicacoes.hodge_certificado
#print axioms ATK.ATKIAplicacoes.hodge_transicao
#print axioms ATK.ATKIAplicacoes.contracao_relacional
#print axioms ATK.ATKIAplicacoes.quantificadores
#print axioms ATK.ATKIAplicacoes.busca_exaustiva
#print axioms ATK.ATKIAplicacoes.aproximacao_finita_trivial
#print axioms ATK.ATKIAplicacoes.erro_tende_sem_zerar
#print axioms ATK.ATKIAplicacoes.reynolds
#print axioms ATK.ATKIAplicacoes.pressao_dinamica
