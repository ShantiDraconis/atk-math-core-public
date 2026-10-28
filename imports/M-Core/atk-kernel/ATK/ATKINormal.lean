import ATK.ATKIBagchi
import Mathlib.Analysis.Real.Hyperreal

/-!
# ATK-I — pares relacionais, ordem de proximidade e normalização da igualdade

Formaliza a álgebra proposta nos textos ATK-I para o objeto `(a = b)`:

* `Par`: o objeto `(a = b)` (não a sua verdade); `trio = E(a,b) = (a, b, a − b)`;
* `vale R ↔ a = b`, `defeito R = |a − b|`, `vale ↔ defeito = 0`; ligação com `RelNum`;
* escala `k·(a = b) = (ka = kb)` e potência `(a = b)ⁿ = (aⁿ = bⁿ)`;
* ordem de proximidade `R ⪰ S ↔ defeito R ≤ defeito S`: pré-ordem total, **não** antissimétrica;
  as relações que valem estão no topo;
* o cálculo `(0 = 1)·3 ⪰ (2 = 1)³`, isto é `(0 = 3) ⪰ (8 = 1)` (defeitos 3 ≤ 7): **vale**;
  pela diferença `a − b` (`−3 ≥ 1`), componente a componente, e com infinitésimo hiper-real
  (`−3ε ≥ (2 − ε)³`): **não vale** — o resultado depende da ordem escolhida;
* normalização `T_t(a = b) = ((1 − t)a + tb = b)`: `T₀ = id`, `T_s ∘ T_t = T_{s+t−st}`,
  `T₁ ∘ T₁ = T₁`, `defeito (T_t R) = |1 − t| · defeito R`, `T₁ R` sempre vale, `T_t` fixa as
  relações que valem e preserva a ordem de proximidade; `D_x(R) = defeito R/(1 + x) → 0`.

O que a normalização **não** faz (`normalizacao_nao_e_prova`, `vale_T_iff`, `normalizar_D`):
`T₁(0 = 1) = (1 = 1)` vale embora `(0 = 1)` não valha; para `t ≠ 1`, `T_t` não muda a verdade;
e `T₁(D = 0) = (0 = 0)` para **todo** `D`, logo normalizar `(D∞ = 0)` não informa o valor de `D∞`.
Já `(D∞ = 0)` **valer** implica RH (`vale_D_infinito_RH`, pela ponte de Bagchi).
-/

open Filter Topology

namespace ATK.ATKINormal

/-- O par relacional `(a = b)`: o objeto, não a sua verdade. -/
structure Par where
  a : ℝ
  b : ℝ

namespace Par

/-- `E(a,b) = (a, b, a − b)`. -/
def trio (R : Par) : ℝ × ℝ × ℝ := (R.a, R.b, R.a - R.b)

/-- A relação vale: `a = b`. -/
def vale (R : Par) : Prop := R.a = R.b

/-- Defeito `|a − b|`. -/
noncomputable def defeito (R : Par) : ℝ := |R.a - R.b|

def escala (k : ℝ) (R : Par) : Par := ⟨k * R.a, k * R.b⟩

def pot (n : ℕ) (R : Par) : Par := ⟨R.a ^ n, R.b ^ n⟩

/-- Ordem de proximidade: `R ⪰ S` quando `R` está pelo menos tão perto de valer quanto `S`. -/
def maisProximo (R S : Par) : Prop := R.defeito ≤ S.defeito

/-- Normalização `T_t(a = b) = ((1 − t)a + tb = b)`. -/
def T (t : ℝ) (R : Par) : Par := ⟨(1 - t) * R.a + t * R.b, R.b⟩

/-- O par como número relacional do ATK-I. -/
def paraRelNum (R : Par) : ATK.ATKI.RelNum := ⟨R.a, .eq, R.b⟩

/-! ## Verdade e defeito -/

theorem defeito_nonneg (R : Par) : 0 ≤ R.defeito := abs_nonneg _

theorem vale_iff_defeito (R : Par) : R.vale ↔ R.defeito = 0 := by
  unfold vale defeito
  rw [abs_eq_zero, sub_eq_zero]

theorem paraRelNum_holds (R : Par) : (paraRelNum R).holds ↔ R.vale := Iff.rfl

/-! ## Ordem de proximidade -/

theorem maisProximo_refl (R : Par) : maisProximo R R := le_refl _

theorem maisProximo_trans {R S U : Par} (h1 : maisProximo R S) (h2 : maisProximo S U) :
    maisProximo R U := le_trans h1 h2

theorem maisProximo_total (R S : Par) : maisProximo R S ∨ maisProximo S R := le_total _ _

/-- Não é antissimétrica: `(0 = 1)` e `(1 = 0)` têm o mesmo defeito e são objetos diferentes. -/
theorem nao_antissimetrica :
    maisProximo ⟨0, 1⟩ ⟨1, 0⟩ ∧ maisProximo ⟨1, 0⟩ ⟨0, 1⟩ ∧ (⟨0, 1⟩ : Par) ≠ ⟨1, 0⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · simp [maisProximo, defeito]
  · simp [maisProximo, defeito]
  · intro h
    have := congrArg Par.a h
    norm_num at this

/-- As relações que valem estão no topo. -/
theorem vale_topo {R : Par} (h : R.vale) (S : Par) : maisProximo R S := by
  unfold maisProximo
  rw [(vale_iff_defeito R).mp h]
  exact defeito_nonneg S

/-! ## Escala, potência e o cálculo `(0 = 1)·3 ⪰ (2 = 1)³` -/

theorem defeito_escala (k : ℝ) (R : Par) : (escala k R).defeito = |k| * R.defeito := by
  show |k * R.a - k * R.b| = |k| * |R.a - R.b|
  rw [← mul_sub, abs_mul]

theorem exemplo_escala : escala 3 ⟨0, 1⟩ = ⟨0, 3⟩ := by
  norm_num [escala]

theorem exemplo_pot : pot 3 ⟨2, 1⟩ = ⟨8, 1⟩ := by
  norm_num [pot]

theorem defeito_0_3 : (⟨0, 3⟩ : Par).defeito = 3 := by
  show |(0 : ℝ) - 3| = 3
  rw [abs_of_neg (by norm_num)]
  norm_num

theorem defeito_8_1 : (⟨8, 1⟩ : Par).defeito = 7 := by
  show |(8 : ℝ) - 1| = 7
  rw [abs_of_pos (by norm_num)]
  norm_num

/-- **`(0 = 1)·3 ⪰ (2 = 1)³`** na ordem de proximidade: `(0 = 3) ⪰ (8 = 1)`, pois `3 ≤ 7`. -/
theorem exemplo_proximidade : maisProximo (escala 3 ⟨0, 1⟩) (pot 3 ⟨2, 1⟩) := by
  rw [exemplo_escala, exemplo_pot]
  unfold maisProximo
  rw [defeito_0_3, defeito_8_1]
  norm_num

/-- Pela diferença `a − b`, a mesma desigualdade é falsa: `−3 ≥ 1` não vale. -/
theorem pela_diferenca_falsa : ¬ ((0 - 1 : ℝ) * 3 ≥ (2 - 1) ^ 3) := by norm_num

/-- Componente a componente em `E(a,b)`, também é falsa (primeira componente: `0 ≥ 8`). -/
theorem por_componentes_falsa :
    ¬ ((escala 3 ⟨0, 1⟩).trio.1 ≥ (pot 3 ⟨2, 1⟩).trio.1) := by
  rw [exemplo_escala, exemplo_pot]
  norm_num [trio]

/-- Com o infinitésimo hiper-real `ε`, pela diferença: `−3ε ≥ (2 − ε)³` é falsa
(equivale a `ε³ − 6ε² + 9ε − 8 ≥ 0`). -/
theorem infinitesimal_falsa :
    ¬ (-3 * Hyperreal.epsilon ≥ (2 - Hyperreal.epsilon) ^ 3) := by
  have h0 : (0 : Hyperreal) < Hyperreal.epsilon := Hyperreal.epsilon_pos
  have h1 : Hyperreal.epsilon < 1 := by
    have h := Hyperreal.epsilon_lt_of_pos (show (0 : ℝ) < 1 from one_pos)
    simpa using h
  intro h
  nlinarith [mul_nonneg (sq_nonneg (Hyperreal.epsilon - 1))
    (by linarith : (0 : Hyperreal) ≤ 4 - Hyperreal.epsilon)]

/-! ## Normalização -/

theorem T_zero (R : Par) : T 0 R = R := by
  obtain ⟨a, b⟩ := R
  show (⟨(1 - 0) * a + 0 * b, b⟩ : Par) = ⟨a, b⟩
  congr 1
  ring

theorem T_comp (s t : ℝ) (R : Par) : T s (T t R) = T (s + t - s * t) R := by
  show (⟨(1 - s) * ((1 - t) * R.a + t * R.b) + s * R.b, R.b⟩ : Par) =
    ⟨(1 - (s + t - s * t)) * R.a + (s + t - s * t) * R.b, R.b⟩
  congr 1
  ring

theorem T_idem (R : Par) : T 1 (T 1 R) = T 1 R := by
  rw [T_comp]
  norm_num

/-- `T₁ R` sempre vale. -/
theorem T_vale (R : Par) : (T 1 R).vale := by
  show (1 - 1) * R.a + 1 * R.b = R.b
  ring

theorem defeito_T (t : ℝ) (R : Par) : (T t R).defeito = |1 - t| * R.defeito := by
  show |(1 - t) * R.a + t * R.b - R.b| = |1 - t| * |R.a - R.b|
  rw [← abs_mul]
  congr 1
  ring

theorem defeito_T_le_one {t : ℝ} (ht : t ≤ 1) (R : Par) :
    (T t R).defeito = (1 - t) * R.defeito := by
  rw [defeito_T, abs_of_nonneg (by linarith)]

/-- Estabilidade: `T_t` fixa as relações que já valem. -/
theorem T_estavel {R : Par} (h : R.vale) (t : ℝ) : T t R = R := by
  obtain ⟨a, b⟩ := R
  have hab : a = b := h
  subst hab
  show (⟨(1 - t) * a + t * a, a⟩ : Par) = ⟨a, a⟩
  congr 1
  ring

/-- A normalização preserva a ordem de proximidade. -/
theorem T_mono {R S : Par} (h : maisProximo R S) (t : ℝ) : maisProximo (T t R) (T t S) := by
  unfold maisProximo at *
  rw [defeito_T, defeito_T]
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- Para `t ≠ 1`, a normalização não muda a verdade. -/
theorem vale_T_iff {t : ℝ} (ht : t ≠ 1) (R : Par) : (T t R).vale ↔ R.vale := by
  rw [vale_iff_defeito, vale_iff_defeito, defeito_T, mul_eq_zero]
  have hne : |1 - t| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm ht))
  exact ⟨fun h => h.resolve_left hne, Or.inr⟩

/-- **Normalizar não é provar**: `(0 = 1)` não vale, mas `T₁(0 = 1) = (1 = 1)` vale. -/
theorem normalizacao_nao_e_prova : ¬ (⟨0, 1⟩ : Par).vale ∧ (T 1 ⟨0, 1⟩).vale :=
  ⟨by norm_num [vale], T_vale _⟩

/-- `T₁(D = 0) = (0 = 0)` para todo `D`: o resultado não depende de `D`. -/
theorem normalizar_D (D : ℝ) : T 1 ⟨D, 0⟩ = ⟨0, 0⟩ := by
  show (⟨(1 - 1) * D + 1 * 0, 0⟩ : Par) = ⟨0, 0⟩
  congr 1
  ring

/-! ## Infinito e infinitésimo: `D_x(R) = defeito R/(1 + x) → 0` -/

theorem Dx_tendsto (R : Par) :
    Tendsto (fun x : ℝ => R.defeito / (1 + x)) atTop (𝓝 0) :=
  Tendsto.div_atTop tendsto_const_nhds
    (tendsto_atTop_mono (fun x => by show x ≤ 1 + x; linarith) tendsto_id)

/-- `t(x) = x/(1 + x)`. -/
noncomputable def tx (x : ℝ) : ℝ := x / (1 + x)

theorem defeito_T_tx {x : ℝ} (hx : 0 ≤ x) : (T (tx x) ⟨0, 1⟩).defeito = 1 / (1 + x) := by
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have he : (1 - tx x) * 0 + tx x * 1 - 1 = -(1 / (1 + x)) := by
    unfold tx
    first
    | (field_simp; ring)
    | field_simp
    | ring
  show |(1 - tx x) * 0 + tx x * 1 - 1| = 1 / (1 + x)
  rw [he, abs_neg, abs_of_pos (by positivity)]

/-- O desvio de `T_{t(x)}(0 = 1)` vai a zero quando `x → ∞`. -/
theorem T_tx_tendsto : Tendsto (fun x : ℝ => (T (tx x) ⟨0, 1⟩).defeito) atTop (𝓝 0) := by
  have hb : Tendsto (fun x : ℝ => 1 / (1 + x)) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds
      (tendsto_atTop_mono (fun x => by show x ≤ 1 + x; linarith) tendsto_id)
  refine hb.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact (defeito_T_tx hx).symm

/-! ## O número `(D∞ = 0)` -/

/-- O número relacional `(D∞ = 0)` da família do texto. -/
noncomputable def numeroD : Par := ⟨⨅ N, ATK.ATKI.Defeito ATK.ATKI.wTexto ATK.ATKI.gTexto N, 0⟩

/-- Se `(D∞ = 0)` **vale**, a Hipótese de Riemann vale (ponte de Bagchi). -/
theorem vale_D_infinito_RH (h : numeroD.vale) : RiemannHypothesis :=
  ATK.ATKIBagchi.rh_of_texto h

/-- Normalizar `(D∞ = 0)` dá `(0 = 0)`, seja qual for `D∞`. -/
theorem normalizar_numeroD : T 1 numeroD = ⟨0, 0⟩ := normalizar_D _

end Par

end ATK.ATKINormal

#print axioms ATK.ATKINormal.Par.defeito_nonneg
#print axioms ATK.ATKINormal.Par.vale_iff_defeito
#print axioms ATK.ATKINormal.Par.paraRelNum_holds
#print axioms ATK.ATKINormal.Par.maisProximo_refl
#print axioms ATK.ATKINormal.Par.maisProximo_trans
#print axioms ATK.ATKINormal.Par.maisProximo_total
#print axioms ATK.ATKINormal.Par.nao_antissimetrica
#print axioms ATK.ATKINormal.Par.vale_topo
#print axioms ATK.ATKINormal.Par.defeito_escala
#print axioms ATK.ATKINormal.Par.exemplo_escala
#print axioms ATK.ATKINormal.Par.exemplo_pot
#print axioms ATK.ATKINormal.Par.defeito_0_3
#print axioms ATK.ATKINormal.Par.defeito_8_1
#print axioms ATK.ATKINormal.Par.exemplo_proximidade
#print axioms ATK.ATKINormal.Par.pela_diferenca_falsa
#print axioms ATK.ATKINormal.Par.por_componentes_falsa
#print axioms ATK.ATKINormal.Par.infinitesimal_falsa
#print axioms ATK.ATKINormal.Par.T_zero
#print axioms ATK.ATKINormal.Par.T_comp
#print axioms ATK.ATKINormal.Par.T_idem
#print axioms ATK.ATKINormal.Par.T_vale
#print axioms ATK.ATKINormal.Par.defeito_T
#print axioms ATK.ATKINormal.Par.defeito_T_le_one
#print axioms ATK.ATKINormal.Par.T_estavel
#print axioms ATK.ATKINormal.Par.T_mono
#print axioms ATK.ATKINormal.Par.vale_T_iff
#print axioms ATK.ATKINormal.Par.normalizacao_nao_e_prova
#print axioms ATK.ATKINormal.Par.normalizar_D
#print axioms ATK.ATKINormal.Par.Dx_tendsto
#print axioms ATK.ATKINormal.Par.defeito_T_tx
#print axioms ATK.ATKINormal.Par.T_tx_tendsto
#print axioms ATK.ATKINormal.Par.vale_D_infinito_RH
#print axioms ATK.ATKINormal.Par.normalizar_numeroD
