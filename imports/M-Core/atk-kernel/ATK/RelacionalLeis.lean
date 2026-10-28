/-
ATK-I — Nível I completo: leis algébricas, potências, transição, pré-ordem, quociente,
três estados, equação universal das sete relações e infinitésimos.

Complementa `ATK.RelacionalI` (pares, d, 𝒫, 𝒞, transporte) com o restante do texto
"ATK-I — Estrutura matemática completa da lógica relacional":

* §3  `K²` é anel comutativo sob ⊕, ⊗ (assoc., comut., distributividade, 𝟎 = R(0,0), 𝟏 = R(1,1));
* §4  `𝒯` (diagonal) é um **subanel**: as relações verdadeiras formam subestrutura algébrica;
* §5–6 `d(−R) = d(R)`; `d(R ⊗ S) ≤ |c| d(R) + |b| d(S)` (forma exata do texto);
* §7  **`d(Rⁿ) = d(R) · |Σ aʲ bⁿ⁻¹⁻ʲ|`** (exata); `R(2,1)³ = R(8,1)`, `d = 7`;
      a potência não preserva: `R(−1,1)² = R(1,1)`;
* §8  ≽ é pré-ordem total, **não** antissimétrica (`d R(0,1) = d R(2,3) = 1`);
* §9  `R ∼ S ⟺ d R = d S` é equivalência; `ℛ(ℝ)/∼ ≃ [0,∞)` via d; ⊕ **não** passa ao quociente;
* §10 transição `T_t(a,b) = ((1−t)a + tb, b)`: `d(T_t R) = |1−t| d(R)`, contração em [0,1],
      `T_1 R = R(b,b)`, estabilidade, composição **`T_t ∘ T_s = T_{s+t−st}`**;
      `T_t ∈ 𝒫 ⟺ t ≠ 1`; `T_1` torna toda relação verdadeira (normalização ≠ certificado);
* §12 hiper-reais (Mathlib): `R(ε,0)` tem defeito `ε > 0` menor que todo real positivo,
      não é verdadeira, e a parte padrão do defeito é 0 — **defeito infinitesimal ≠ zero**;
* §13 três estados TRUE / APPROX / FAR com tolerância τ (APPROX nunca é TRUE);
* §14 **equação universal**: `Σ wᵢ(aᵢ − bᵢ)² = 0 ⟺ ∀ i, aᵢ = bᵢ` (wᵢ > 0), em particular para 7;
      e o fechamento artificial: aplicando `T_1` a cada relação, a soma vira 0 sem provar nada.

Estado: ALGEBRA_GREEN; aplicação às sete conjecturas OPEN; certificados terminais 0/7.
-/
import ATK.RelacionalI
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace ATK.RelacionalLeis

open ATK.RelacionalI Finset

section Anel

variable {K : Type*} [NormedField K]

/-! ### §3 Leis algébricas -/

theorem oplus_eq_add (R S : Relacao K) : oplus R S = R + S := rfl

theorem otimes_eq_mul (R S : Relacao K) : otimes R S = R * S := rfl

theorem oplus_assoc (R S U : Relacao K) : oplus (oplus R S) U = oplus R (oplus S U) :=
  add_assoc R S U

theorem oplus_comm (R S : Relacao K) : oplus R S = oplus S R := add_comm R S

theorem otimes_assoc (R S U : Relacao K) : otimes (otimes R S) U = otimes R (otimes S U) :=
  mul_assoc R S U

theorem otimes_comm (R S : Relacao K) : otimes R S = otimes S R := mul_comm R S

/-- Distributividade `R ⊗ (S ⊕ T) = (R ⊗ S) ⊕ (R ⊗ T)`. -/
theorem otimes_oplus (R S U : Relacao K) :
    otimes R (oplus S U) = oplus (otimes R S) (otimes R U) := mul_add R S U

/-- `𝟎 = R(0,0)` é neutro de ⊕. -/
theorem oplus_zero (R : Relacao K) : oplus R (0, 0) = R := add_zero R

/-- `𝟏 = R(1,1)` é neutro de ⊗. -/
theorem otimes_one (R : Relacao K) : otimes R (1, 1) = R := mul_one R

/-! ### §4 𝒯 é subanel -/

/-- As relações verdadeiras como subanel de `K × K`. -/
def verdadeiras : Subring (K × K) where
  carrier := {R | Verdadeira R}
  mul_mem' := fun {R S} hR hS => verdadeira_otimes hR hS
  one_mem' := rfl
  add_mem' := fun {R S} hR hS => verdadeira_oplus hR hS
  zero_mem' := rfl
  neg_mem' := fun {R} hR => by
    show (-R).1 = (-R).2
    simp only [Prod.fst_neg, Prod.snd_neg]
    exact congrArg Neg.neg hR

theorem mem_verdadeiras (R : Relacao K) : R ∈ verdadeiras ↔ Verdadeira R := Iff.rfl

theorem exemplo_verdadeiras : Verdadeira ((1 : K), (1 : K)) ∧ ¬ Verdadeira ((0 : K), (1 : K)) :=
  ⟨rfl, fun h => zero_ne_one h⟩

/-! ### §5–6 Defeito -/

theorem d_neg (R : Relacao K) : d (-R) = d R := by
  unfold d
  simp only [Prod.fst_neg, Prod.snd_neg]
  rw [neg_sub_neg, norm_sub_rev]

/-- Forma do texto: `ac − bd = (a − b)c + b(c − d)`. -/
theorem d_otimes_le_texto (R S : Relacao K) : d (otimes R S) ≤ ‖S.1‖ * d R + ‖R.2‖ * d S := by
  unfold d otimes
  have e : R.1 * S.1 - R.2 * S.2 = (R.1 - R.2) * S.1 + R.2 * (S.1 - S.2) := by ring
  rw [e]
  calc ‖(R.1 - R.2) * S.1 + R.2 * (S.1 - S.2)‖
      ≤ ‖(R.1 - R.2) * S.1‖ + ‖R.2 * (S.1 - S.2)‖ := norm_add_le _ _
    _ = ‖S.1‖ * ‖R.1 - R.2‖ + ‖R.2‖ * ‖S.1 - S.2‖ := by rw [norm_mul, norm_mul, mul_comm]

/-! ### §7 Potências -/

/-- `R(a,b)ⁿ = R(aⁿ, bⁿ)`. -/
def pot (R : Relacao K) (n : ℕ) : Relacao K := (R.1 ^ n, R.2 ^ n)

/-- **Lei exata das potências**: `d(Rⁿ) = d(R) · ‖Σ_{j<n} aʲ b^{n−1−j}‖`. -/
theorem d_pot (R : Relacao K) (n : ℕ) :
    d (pot R n) = d R * ‖∑ j ∈ range n, R.1 ^ j * R.2 ^ (n - 1 - j)‖ := by
  unfold d pot
  rw [← geom_sum₂_mul, norm_mul, mul_comm]

theorem verdadeira_pot {R : Relacao K} (hR : Verdadeira R) (n : ℕ) : Verdadeira (pot R n) := by
  unfold Verdadeira pot at *
  rw [hR]

/-- Exemplo do texto: `R(2,1)³ = R(8,1)` e `d = 7 = 1·(4 + 2 + 1)`. -/
theorem exemplo_pot : pot ((2 : ℝ), (1 : ℝ)) 3 = (8, 1) ∧ d (pot ((2 : ℝ), (1 : ℝ)) 3) = 7 := by
  refine ⟨by norm_num [pot], ?_⟩
  norm_num [d, pot]

/-- A potência pode eliminar um defeito sem que a relação original seja verdadeira:
`R(−1,1)² = R(1,1)`.  Logo `R ↦ R²` não está em 𝒫. -/
theorem potencia_nao_preserva : ¬ PreservaEquiv (fun R : Relacao ℝ => pot R 2) := by
  intro h
  have h1 : Verdadeira (pot ((-1 : ℝ), (1 : ℝ)) 2) := by
    unfold Verdadeira pot; norm_num
  have h2 := (h (-1, 1)).mp h1
  unfold Verdadeira at h2
  norm_num at h2

end Anel

/-! ### §8–9 Pré-ordem e quociente -/

/-- ≽ não é antissimétrica: `d R(0,1) = d R(2,3) = 1` com `R(0,1) ≠ R(2,3)`. -/
theorem prox_nao_antissimetrica :
    Prox ((0 : ℝ), (1 : ℝ)) ((2 : ℝ), (3 : ℝ)) ∧ Prox ((2 : ℝ), (3 : ℝ)) ((0 : ℝ), (1 : ℝ)) ∧
      ((0 : ℝ), (1 : ℝ)) ≠ ((2 : ℝ), (3 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Prox d; norm_num
  · unfold Prox d; norm_num
  · intro h; have := congrArg Prod.fst h; norm_num at this

/-- `R ∼ S ⟺ d R = d S`. -/
def MesmoDefeito {K : Type*} [NormedField K] (R S : Relacao K) : Prop := d R = d S

theorem mesmoDefeito_equivalence {K : Type*} [NormedField K] :
    Equivalence (MesmoDefeito (K := K)) :=
  ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- O quociente `ℛ(ℝ)/∼` é identificado com `[0, ∞)` pelo defeito: imagem exata. -/
theorem imagem_defeito : Set.range (d : Relacao ℝ → ℝ) = Set.Ici 0 := by
  ext r
  constructor
  · rintro ⟨R, rfl⟩; exact d_nonneg R
  · intro hr
    refine ⟨(r, 0), ?_⟩
    unfold d
    simp [abs_of_nonneg (show (0 : ℝ) ≤ r from hr)]

/-- ⊕ **não** passa ao quociente: `R(1,0) ∼ R(0,1)`, mas somando `R(1,0)` os defeitos são 2 e 0. -/
theorem oplus_nao_compativel :
    ∃ R R' S : Relacao ℝ, MesmoDefeito R R' ∧ ¬ MesmoDefeito (oplus R S) (oplus R' S) := by
  refine ⟨(1, 0), (0, 1), (1, 0), ?_, ?_⟩
  · unfold MesmoDefeito d; norm_num
  · unfold MesmoDefeito d oplus; norm_num

/-! ### §10 Transição -/

section Transicao

variable {K : Type*} [NormedField K]

/-- `T_t(R(a,b)) = R((1−t)a + tb, b)`. -/
def transicao (t : K) (R : Relacao K) : Relacao K := ((1 - t) * R.1 + t * R.2, R.2)

theorem d_transicao (t : K) (R : Relacao K) : d (transicao t R) = ‖1 - t‖ * d R := by
  unfold d transicao
  have e : (1 - t) * R.1 + t * R.2 - R.2 = (1 - t) * (R.1 - R.2) := by ring
  rw [e, norm_mul]

/-- Lei de fechamento: `T_1(R(a,b)) = R(b,b)`. -/
theorem transicao_um (R : Relacao K) : transicao 1 R = (R.2, R.2) := by
  unfold transicao
  simp

/-- Lei de estabilidade: `T_t(R(a,a)) = R(a,a)`. -/
theorem transicao_estavel (t a : K) : transicao t (a, a) = (a, a) := by
  unfold transicao
  ext <;> simp <;> ring

/-- **Lei de composição**: `T_t ∘ T_s = T_{s+t−st}`. -/
theorem transicao_comp (s t : K) (R : Relacao K) :
    transicao t (transicao s R) = transicao (s + t - s * t) R := by
  unfold transicao
  ext <;> simp <;> ring

theorem transicao_preserva {t : K} (ht : t ≠ 1) : PreservaEquiv (transicao t) := by
  intro R
  unfold Verdadeira transicao
  simp only
  have h1 : (1 - t) ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  constructor
  · intro h
    have : (1 - t) * (R.1 - R.2) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h2 | h2
    · exact absurd h2 h1
    · exact sub_eq_zero.mp h2
  · intro h; rw [h]; ring

/-- **Normalização**: `T_1` torna qualquer relação verdadeira. -/
theorem normalizacao_fecha_tudo (R : Relacao K) : Verdadeira (transicao 1 R) := by
  rw [transicao_um]; rfl

/-- … e portanto `T_1 ∉ 𝒫`: a normalização não serve de certificado. -/
theorem normalizacao_nao_certifica : ¬ PreservaEquiv (transicao (1 : K)) := by
  intro h
  have := (h (1, 0)).mp (normalizacao_fecha_tudo _)
  exact one_ne_zero this

end Transicao

/-- Lei de contração em ℝ: `t ∈ [0,1]` ⇒ `d(T_t R) = (1−t) d(R) ≤ d(R)`. -/
theorem transicao_contrai {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : Contrai (transicao t) := by
  intro R
  rw [d_transicao]
  have : ‖1 - t‖ = 1 - t := by rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [this]
  have hd := d_nonneg R
  nlinarith

/-! ### §13 Três estados -/

/-- Estado operacional com tolerância τ. -/
inductive Estado3
  | verdadeiro
  | aprox
  | longe
  deriving DecidableEq, Repr

/-- `TRUE` se `d = 0`, `APPROX` se `0 < d ≤ τ`, `FAR` se `d > τ`. -/
noncomputable def estado {K : Type*} [NormedField K] (τ : ℝ) (R : Relacao K) : Estado3 := by
  classical
  exact if d R = 0 then .verdadeiro else if d R ≤ τ then .aprox else .longe

theorem estado_verdadeiro_iff {K : Type*} [NormedField K] (τ : ℝ) (R : Relacao K) :
    estado τ R = .verdadeiro ↔ Verdadeira R := by
  classical
  rw [← d_eq_zero_iff]
  unfold estado
  by_cases h : d R = 0
  · simp [h]
  · by_cases h2 : d R ≤ τ <;> simp [h, h2]

/-- `APPROX` é proximidade, não verdade. -/
theorem estado_aprox_nao_verdadeiro {K : Type*} [NormedField K] (τ : ℝ) (R : Relacao K)
    (h : estado τ R = .aprox) : ¬ Verdadeira R := by
  intro hv
  rw [(estado_verdadeiro_iff τ R).mpr hv] at h
  cases h

/-- Laboratório do texto: `R(0,1)` com τ = 0,25 está em `FAR`. -/
theorem exemplo_laboratorio : estado (1 / 4) ((0 : ℝ), (1 : ℝ)) = .longe := by
  have hd : d ((0 : ℝ), (1 : ℝ)) = 1 := by unfold d; norm_num
  unfold estado
  rw [hd]
  norm_num

/-! ### §14 Equação universal -/

/-- `𝓕 = Σ wᵢ (aᵢ − bᵢ)²`. -/
def F {ι : Type*} [Fintype ι] (w a b : ι → ℝ) : ℝ := ∑ i, w i * (a i - b i) ^ 2

/-- **Teorema de fechamento simultâneo**: com pesos `wᵢ > 0`, `𝓕 = 0 ⟺ ∀ i, aᵢ = bᵢ`. -/
theorem fechamento_simultaneo {ι : Type*} [Fintype ι] (w a b : ι → ℝ) (hw : ∀ i, 0 < w i) :
    F w a b = 0 ↔ ∀ i, a i = b i := by
  unfold F
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hw i).le (sq_nonneg _))]
  constructor
  · intro h i
    have := h i (mem_univ i)
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 (hw i).ne'
    · exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1)
  · intro h i _
    rw [h i, sub_self]; ring

/-- O caso das sete relações. -/
theorem fechamento_sete (w a b : Fin 7 → ℝ) (hw : ∀ i, 0 < w i) :
    F w a b = 0 ↔ ∀ i, a i = b i :=
  fechamento_simultaneo w a b hw

/-- Com algum `wᵢ ≤ 0` o teorema falha: pesos positivos são necessários. -/
theorem pesos_necessarios :
    ∃ (w a b : Fin 7 → ℝ), F w a b = 0 ∧ ¬ ∀ i, a i = b i := by
  refine ⟨fun _ => 0, fun _ => 1, fun _ => 0, by simp [F], fun h => ?_⟩
  have := h 0
  norm_num at this

/-- **Fechamento artificial**: aplicando a normalização `T_1` a cada relação, `𝓕 = 0` para
quaisquer dados — por isso `𝓕 = 0` só certifica quando os defeitos são fiéis ao enunciado. -/
theorem fechamento_artificial {ι : Type*} [Fintype ι] (w a b : ι → ℝ) :
    F w (fun i => (transicao 1 (a i, b i)).1) b = 0 := by
  unfold F
  refine Finset.sum_eq_zero fun i _ => ?_
  show w i * ((transicao 1 (a i, b i)).1 - b i) ^ 2 = 0
  rw [transicao_um]
  simp

/-! ### §12 Infinitésimos (hiper-reais da Mathlib) -/

/-- Defeito em corpo ordenado: `|a − b|`. -/
def dOrd {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (R : K × K) : K :=
  |R.1 - R.2|

/-- `R(ε, 0)`: defeito exatamente `ε`, positivo, **menor que todo real positivo**, e a relação
é falsa. -/
theorem defeito_infinitesimal :
    dOrd (Hyperreal.epsilon, (0 : ℝ*)) = Hyperreal.epsilon ∧
      0 < dOrd (Hyperreal.epsilon, (0 : ℝ*)) ∧
      (∀ r : ℝ, 0 < r → dOrd (Hyperreal.epsilon, (0 : ℝ*)) < (r : ℝ*)) ∧
      Hyperreal.epsilon ≠ (0 : ℝ*) := by
  have h : dOrd (Hyperreal.epsilon, (0 : ℝ*)) = Hyperreal.epsilon := by
    unfold dOrd
    simp only [sub_zero]
    exact abs_of_pos Hyperreal.epsilon_pos
  refine ⟨h, ?_, ?_, Hyperreal.epsilon_ne_zero⟩
  · rw [h]; exact Hyperreal.epsilon_pos
  · intro r hr; rw [h]; exact Hyperreal.epsilon_lt_of_pos hr

/-- **Defeito infinitesimal ≠ defeito zero**: a parte padrão do defeito de `R(ε,0)` é 0, mas o
defeito não é 0 — a passagem à parte padrão perde a informação infinitesimal. -/
theorem parte_padrao_perde :
    ArchimedeanClass.stdPart (dOrd (Hyperreal.epsilon, (0 : ℝ*))) = 0 ∧
      dOrd (Hyperreal.epsilon, (0 : ℝ*)) ≠ 0 := by
  obtain ⟨h, hpos, -, -⟩ := defeito_infinitesimal
  refine ⟨?_, hpos.ne'⟩
  rw [h]
  exact Hyperreal.stdPart_epsilon

end ATK.RelacionalLeis

#print axioms ATK.RelacionalLeis.oplus_eq_add
#print axioms ATK.RelacionalLeis.otimes_eq_mul
#print axioms ATK.RelacionalLeis.oplus_assoc
#print axioms ATK.RelacionalLeis.oplus_comm
#print axioms ATK.RelacionalLeis.otimes_assoc
#print axioms ATK.RelacionalLeis.otimes_comm
#print axioms ATK.RelacionalLeis.otimes_oplus
#print axioms ATK.RelacionalLeis.oplus_zero
#print axioms ATK.RelacionalLeis.otimes_one
#print axioms ATK.RelacionalLeis.mem_verdadeiras
#print axioms ATK.RelacionalLeis.exemplo_verdadeiras
#print axioms ATK.RelacionalLeis.d_neg
#print axioms ATK.RelacionalLeis.d_otimes_le_texto
#print axioms ATK.RelacionalLeis.d_pot
#print axioms ATK.RelacionalLeis.verdadeira_pot
#print axioms ATK.RelacionalLeis.exemplo_pot
#print axioms ATK.RelacionalLeis.potencia_nao_preserva
#print axioms ATK.RelacionalLeis.prox_nao_antissimetrica
#print axioms ATK.RelacionalLeis.mesmoDefeito_equivalence
#print axioms ATK.RelacionalLeis.imagem_defeito
#print axioms ATK.RelacionalLeis.oplus_nao_compativel
#print axioms ATK.RelacionalLeis.d_transicao
#print axioms ATK.RelacionalLeis.transicao_um
#print axioms ATK.RelacionalLeis.transicao_estavel
#print axioms ATK.RelacionalLeis.transicao_comp
#print axioms ATK.RelacionalLeis.transicao_preserva
#print axioms ATK.RelacionalLeis.normalizacao_fecha_tudo
#print axioms ATK.RelacionalLeis.normalizacao_nao_certifica
#print axioms ATK.RelacionalLeis.transicao_contrai
#print axioms ATK.RelacionalLeis.estado_verdadeiro_iff
#print axioms ATK.RelacionalLeis.estado_aprox_nao_verdadeiro
#print axioms ATK.RelacionalLeis.exemplo_laboratorio
#print axioms ATK.RelacionalLeis.fechamento_simultaneo
#print axioms ATK.RelacionalLeis.fechamento_sete
#print axioms ATK.RelacionalLeis.pesos_necessarios
#print axioms ATK.RelacionalLeis.fechamento_artificial
#print axioms ATK.RelacionalLeis.defeito_infinitesimal
#print axioms ATK.RelacionalLeis.parte_padrao_perde
