import ATK.Indeterminacy
import ATK.IMath.Certificates.Core

/-!
# ATK — I-Mathematics no kernel: os 15 certificados e a ponte com o `I` do ATK

Fonte: `ShantiDraconis/meta-mathematics-indeterminate-I`, commit `919fc81` (núcleo congelado em
`b8b1da78`), `src/IMath/**`. Os arquivos estão em `ATK/IMath/**` sem mudança de conteúdo; só os
`import IMath.…` viraram `import ATK.IMath.…`. A fonte original usa Lean/Mathlib `v4.12.0`; aqui
compilam em `v4.34.1`.

**Os 15 certificados** (`C01`–`C15`) entram como apelidos, para que o auditor do kernel confira
`#print axioms` de **todos** — o arquivo original imprime só 8.

**Duas definições de `I`, compatíveis.** O IMath usa `Phi3 α` (finito, `∞`, indeterminado com a
expressão de origem) e divide `a/0 = ∞` (`a ≠ 0`), `0/0 = I`. O ATK (`ATK.Indeterminacy`) usa
`RI = Option ℝ` com `I = none` absorvente e `x/0 = I` para todo `x`. A projeção
`proj : Phi3 ℝ → RI` (finito ↦ finito; `∞` e indeterminados ↦ `I`) é:

* compatível com a soma: `proj (x ⊕ y) = proj x + proj y` para **todos** `x, y` (`pi_absorbingAdd`);
* compatível com a divisão de finitos: `proj (a ÷ b) = a ⊘ b` (`pi_idiv`);
* invariante pelo colapso (`pi_collapse`) e sobrejetiva (`pi_surjective`).

Logo `RI` é o quociente de `Phi3 ℝ` que identifica `∞` com `I`; o núcleo dessa identificação é
exatamente o que distingue os dois modelos (`pi_eq_I_iff`, `modelos_diferem_em_um_sobre_zero`).
Nenhum dos dois declara axiomas: ambos são extensões conservadoras, ao contrário dos sistemas
`PAX`/`K_I` refutados em `ATK.IAlgebra`.
-/

namespace ATK.IMathPonte

open IMath IMath.Phi3

/-! ## Os 15 certificados -/

alias C01 := IMath.Certificates.C01_I_is_indeterminate
alias C02 := IMath.Certificates.C02_I_is_not_infinity
alias C03 := IMath.Certificates.C03_I_is_not_finite
alias C04 := IMath.Certificates.C04_real_embedding_injective
alias C05 := IMath.Certificates.C05_complex_embedding_injective
alias C06 := IMath.Certificates.C06_zero_over_zero_is_I
alias C07 := IMath.Certificates.C07_infinity_over_infinity_retains_provenance
alias C08 := IMath.Certificates.C08_collapse_is_idempotent
alias C09 := IMath.Certificates.C09_absorbing_addition_refutes_right_cancellation
alias C10 := IMath.Certificates.C10_refinement_transitive
alias C11 := IMath.Certificates.C11_contextual_zero_over_zero_germs_differ
alias C12 := IMath.Certificates.C12_x_over_x_resolves_to_one
alias C13 := IMath.Certificates.C13_x_squared_over_x_resolves_to_zero
alias C14 := IMath.Certificates.C14_same_substitution_form_different_resolutions
alias C15 := IMath.Certificates.C15_determined_geometry_embedding_injective

/-! ## A ponte `proj : Phi3 ℝ → RI` -/

/-- Esquece a diferença entre `∞` e os indeterminados. -/
def proj : Phi3 ℝ → ATK.Indeterminacy.RI
  | .finite a => some a
  | .infinity => none
  | .indeterminate _ => none

theorem pi_finite (a : ℝ) : proj (.finite a) = ATK.Indeterminacy.ι a := rfl

theorem pi_I : proj (Phi3.I (α := ℝ)) = ATK.Indeterminacy.I := rfl

theorem pi_infinity : proj (.infinity : Phi3 ℝ) = ATK.Indeterminacy.I := rfl

/-- O que `proj` identifica: exatamente `∞` e os indeterminados. -/
theorem pi_eq_I_iff (x : Phi3 ℝ) :
    proj x = ATK.Indeterminacy.I ↔ x = .infinity ∨ ∃ e, x = .indeterminate e := by
  cases x with
  | finite a => simp [proj, ATK.Indeterminacy.I]
  | infinity => simp [proj, ATK.Indeterminacy.I]
  | indeterminate e => simp [proj, ATK.Indeterminacy.I]

theorem pi_surjective : Function.Surjective proj := by
  intro r
  cases r with
  | none => exact ⟨.infinity, rfl⟩
  | some a => exact ⟨.finite a, rfl⟩

/-- **Soma**: a soma absorvente do IMath vira a soma absorvente do ATK, em todos os casos. -/
theorem pi_absorbingAdd (x y : Phi3 ℝ) :
    proj (absorbingAdd x y) = ATK.Indeterminacy.addI (proj x) (proj y) := by
  cases x <;> cases y <;> rfl

/-- **Divisão de finitos**: `proj (a ÷ b) = a ⊘ b`, inclusive `0/0` e `a/0`. -/
theorem pi_idiv (a b : ℝ) :
    proj (idiv (.finite a) (.finite b)) =
      ATK.Indeterminacy.divI (ATK.Indeterminacy.ι a) (ATK.Indeterminacy.ι b) := by
  by_cases hb : b = 0
  · subst hb
    by_cases ha : a = 0
    · subst ha
      simp [idiv, proj, ATK.Indeterminacy.divI, ATK.Indeterminacy.ι]
    · simp [idiv, ha, proj, ATK.Indeterminacy.divI, ATK.Indeterminacy.ι]
  · simp [idiv, hb, proj, ATK.Indeterminacy.divI, ATK.Indeterminacy.ι]

/-- O colapso do IMath não muda a projeção. -/
theorem pi_collapse (x : Phi3 ℝ) : proj (collapse x) = proj x := by
  cases x <;> rfl

/-- Os dois modelos diferem exatamente onde `proj` identifica: em `Phi3`, `1/0 = ∞ ≠ I`; em `RI`,
`1 ⊘ 0 = I`. -/
theorem modelos_diferem_em_um_sobre_zero :
    idiv (.finite (1 : ℝ)) (.finite 0) = .infinity ∧
      (.infinity : Phi3 ℝ) ≠ Phi3.I ∧
      ATK.Indeterminacy.divI (ATK.Indeterminacy.ι 1) (ATK.Indeterminacy.ι 0) =
        ATK.Indeterminacy.I := by
  refine ⟨finite_ne_zero_idiv_zero one_ne_zero, fun h => I_ne_infinity h.symm, ?_⟩
  simp [ATK.Indeterminacy.divI, ATK.Indeterminacy.ι, ATK.Indeterminacy.I]

end ATK.IMathPonte

#print axioms ATK.IMathPonte.C01
#print axioms ATK.IMathPonte.C02
#print axioms ATK.IMathPonte.C03
#print axioms ATK.IMathPonte.C04
#print axioms ATK.IMathPonte.C05
#print axioms ATK.IMathPonte.C06
#print axioms ATK.IMathPonte.C07
#print axioms ATK.IMathPonte.C08
#print axioms ATK.IMathPonte.C09
#print axioms ATK.IMathPonte.C10
#print axioms ATK.IMathPonte.C11
#print axioms ATK.IMathPonte.C12
#print axioms ATK.IMathPonte.C13
#print axioms ATK.IMathPonte.C14
#print axioms ATK.IMathPonte.C15
#print axioms ATK.IMathPonte.pi_finite
#print axioms ATK.IMathPonte.pi_I
#print axioms ATK.IMathPonte.pi_infinity
#print axioms ATK.IMathPonte.pi_eq_I_iff
#print axioms ATK.IMathPonte.pi_surjective
#print axioms ATK.IMathPonte.pi_absorbingAdd
#print axioms ATK.IMathPonte.pi_idiv
#print axioms ATK.IMathPonte.pi_collapse
#print axioms ATK.IMathPonte.modelos_diferem_em_um_sobre_zero
