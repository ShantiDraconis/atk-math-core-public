import ATK.ATKI
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Teste: a estrutura ATK-I decide algum enunciado?

`EstruturaATKI P` reúne o que a estrutura ATK-I fornece sobre uma proposição `P`: o ciclo dos
estados volta, o ciclo relacional volta, o ciclo de quatro passos volta, De Morgan vale, existe um
certificado e existe um defeito fiel, não negativo, decrescente e convergente.

Resultados:

* `estrutura_vale`: `EstruturaATKI P` vale para **toda** proposição `P`, verdadeira ou falsa;
* `estrutura_nao_implica`: logo a estrutura não implica `P` (com `P := False`);
* `estrutura_RH_e_negacao`: vale para `RiemannHypothesis` e para `¬ RiemannHypothesis`;
* `todo_iff`: o estado `Todo` de um certificado existe exatamente quando `P` vale;
* `ultimo_passo_iff`: para **qualquer** parâmetro `d` com `T ↔ d = 0`, o último passo do
  fechamento por defeito (a cota `d ≤ εₙ → 0`) é equivalente a `T`;
* `ultimo_passo_RH`: com o parâmetro trivial, o último passo é equivalente a RH.

O parâmetro decide onde fica o último passo, não se ele some: o que sobra é sempre equivalente ao
alvo.
-/

namespace ATK.ATKITeste

open Filter Topology ATK.ATKI

noncomputable section

/-- O que a estrutura ATK-I fornece sobre uma proposição `P`. -/
structure EstruturaATKI (P : Prop) : Prop where
  ciclo_estado : Estado.inv (Estado.inv (interpretarP P)) = interpretarP P
  ciclo_relacional : ∀ x : RelNum, RelNum.neg (RelNum.neg x) = x
  ciclo_quatro :
    RelNum.neg (RelNum.scale (1 / 2) (RelNum.neg (RelNum.scale 2 RelNum.N0))) = RelNum.N0
  de_morgan : ∀ a b : Estado,
    Estado.inv (Estado.otimes a b) = Estado.oplus (Estado.inv a) (Estado.inv b)
  certificado : Nonempty (Cert P)
  defeito_fiel : ∃ d : ℕ → ℝ, ∃ L : ℝ,
    (∀ n, 0 ≤ d n) ∧ Antitone d ∧ Tendsto d atTop (𝓝 L) ∧ (P ↔ L = 0)

/-- A estrutura vale para **toda** proposição, verdadeira ou falsa. -/
theorem estrutura_vale (P : Prop) : EstruturaATKI P := by
  classical
  refine ⟨Estado.inv_inv _, RelNum.neg_neg, RelNum.ciclo_quatro, Estado.de_morgan_otimes,
    ⟨Cert.aberto⟩, ?_⟩
  by_cases h : P
  · exact ⟨fun _ => 0, 0, fun _ => le_rfl, antitone_const, tendsto_const_nhds,
      iff_of_true h rfl⟩
  · exact ⟨fun _ => 1, 1, fun _ => zero_le_one, antitone_const, tendsto_const_nhds,
      iff_of_false h one_ne_zero⟩

/-- A estrutura não implica a proposição: ela vale para `False`. -/
theorem estrutura_nao_implica : ¬ ∀ P : Prop, EstruturaATKI P → P :=
  fun h => h False (estrutura_vale False)

/-- A estrutura vale igualmente para RH e para a sua negação. -/
theorem estrutura_RH_e_negacao :
    EstruturaATKI RiemannHypothesis ∧ EstruturaATKI (¬ RiemannHypothesis) :=
  ⟨estrutura_vale _, estrutura_vale _⟩

/-- `Todo` na interpretação é exatamente a verdade de `P`. -/
theorem interpretarP_todo_iff (P : Prop) : interpretarP P = .todo ↔ P := by
  classical
  unfold interpretarP
  by_cases h : P <;> simp [h]

/-- Um certificado com estado `Todo` existe exatamente quando `P` vale. -/
theorem todo_iff (P : Prop) : (∃ c : Cert P, c.estado = .todo) ↔ P :=
  ⟨fun ⟨_, h⟩ => Cert.sound_todo h, fun h => ⟨.provado h, rfl⟩⟩

/-- **O último passo é equivalente ao alvo**, qualquer que seja o parâmetro `d`. -/
theorem ultimo_passo_iff {T : Prop} {d : ℝ} (ponte : T ↔ d = 0) (h0 : 0 ≤ d) :
    (∃ ε : ℕ → ℝ, (∀ n, d ≤ ε n) ∧ Tendsto ε atTop (𝓝 0)) ↔ T := by
  constructor
  · rintro ⟨ε, hd, hε⟩
    exact fechamento_por_defeito ponte h0 hd hε
  · intro hT
    exact ⟨fun _ => 0, fun _ => (ponte.mp hT).le, tendsto_const_nhds⟩

/-- O parâmetro trivial: `0` se `T` vale, `1` se não. -/
def dTrivial (T : Prop) : ℝ := by
  classical
  exact if T then 0 else 1

theorem dTrivial_ponte (T : Prop) : T ↔ dTrivial T = 0 := by
  classical
  unfold dTrivial
  by_cases h : T <;> simp [h]

theorem dTrivial_nonneg (T : Prop) : 0 ≤ dTrivial T := by
  classical
  unfold dTrivial
  split_ifs <;> norm_num

/-- Com o parâmetro trivial, o último passo do fechamento de RH é equivalente a RH. -/
theorem ultimo_passo_RH :
    (∃ ε : ℕ → ℝ, (∀ n, dTrivial RiemannHypothesis ≤ ε n) ∧ Tendsto ε atTop (𝓝 0)) ↔
      RiemannHypothesis :=
  ultimo_passo_iff (dTrivial_ponte _) (dTrivial_nonneg _)

end

end ATK.ATKITeste

#print axioms ATK.ATKITeste.estrutura_vale
#print axioms ATK.ATKITeste.estrutura_nao_implica
#print axioms ATK.ATKITeste.estrutura_RH_e_negacao
#print axioms ATK.ATKITeste.interpretarP_todo_iff
#print axioms ATK.ATKITeste.todo_iff
#print axioms ATK.ATKITeste.ultimo_passo_iff
#print axioms ATK.ATKITeste.dTrivial_ponte
#print axioms ATK.ATKITeste.dTrivial_nonneg
#print axioms ATK.ATKITeste.ultimo_passo_RH
