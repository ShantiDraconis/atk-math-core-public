import ATK.ModeloPNP
import ATK.Externo.FCComplexidade

/-!
# ATK — Integração com o formal-conjectures: o enunciado de P ≠ NP

Dois enunciados de P ≠ NP sobre as máquinas `Turing.FinTM2` da Mathlib, escritos de forma
independente:

* **ATK** (`ATK.LigacaoPNP.PneNP`): linguagens `Set (List Bool)`, entrada **crua** na fita,
  pares `⟨w, c⟩` com bits duplicados e separador `01`;
* **formal-conjectures** (`ATK.FC.ComplexityTheory.P ≠ NP`, cópia em `ATK.Externo.FCComplexidade`):
  problemas `List Bool → Bool`, entrada codificada bit a bit como `[true, b, false]`, pares com
  um bloco autodelimitado.

Este arquivo prova, no kernel:

* `caract`/`lang`: a bijeção entre linguagens e problemas de decisão;
* `emP_iff`, `emNP_iff`: `L ∈ P_ATK ⟺ caract L ∈ P_FC` e o mesmo para NP;
* **`pneNP_iff_fc`: `PneNP ⟺ P_FC ≠ NP_FC`**,

sob a hipótese `Transcodificadores`: quatro máquinas `FinTM2` de tempo polinomial que convertem
entre as duas codificações (crua → FC, FC → crua, par FC → par ATK, palavra → par FC).
Construí-las é engenharia de máquinas, **não** matemática aberta; é o próximo marco desta ligação.

Nada aqui decide P vs NP. **CLOSED_MATH continua false.**
-/

namespace ATK.IntegracaoFCPNP

open Turing Computability ATK.LigacaoPNP ATK.FC ATK.FC.BitstringEncoding ATK.FC.ComplexityTheory

/-! ## Linguagens e problemas de decisão -/

/-- A função característica de uma linguagem (decisão clássica). -/
noncomputable def caract (L : Linguagem) : DecisionProblem :=
  fun w => @decide (w ∈ L) (Classical.dec _)

/-- A linguagem de um problema de decisão. -/
def lang (f : DecisionProblem) : Linguagem := {w | f w = true}

theorem caract_eq_true (L : Linguagem) (w : Palavra) : caract L w = true ↔ w ∈ L := by
  unfold caract
  exact @decide_eq_true_iff _ (Classical.dec _)

theorem caract_lang (f : DecisionProblem) : caract (lang f) = f := by
  funext w
  rw [Bool.eq_iff_iff, caract_eq_true]
  rfl

theorem lang_caract (L : Linguagem) : lang (caract L) = L := by
  ext w
  exact caract_eq_true L w

/-! ## As codificações -/

/-- A codificação do formal-conjectures para palavras: cada bit `b` vira `[true, b, false]`. -/
def encFC : Palavra → List Bool := (BitstringEncoding.toEncoding (α := List Bool)).encode

/-- A codificação do formal-conjectures para pares de palavras. -/
def encFCPar : Palavra × Palavra → List Bool :=
  (BitstringEncoding.toEncoding (α := Palavra × Palavra)).encode

/-- Para `Bool`, as duas codificações coincidem: `[b]`. -/
theorem encBool_eq : (BitstringEncoding.toEncoding (α := Bool)).encode = encodeBool := rfl

/-- Exemplo: a palavra `[b]` é codificada como `[true, b, false]` no formal-conjectures. -/
example (b : Bool) : encFC [b] = [true, b, false] := rfl

/-- O segundo componente do par do ATK: pula pares de bits iguais e devolve o que vem depois do
separador `01`. -/
def cer : List Bool → List Bool
  | a :: b :: r => if a = b then cer r else r
  | _ => []

theorem cer_par (w c : Palavra) : cer (par w c) = c := by
  induction w with
  | nil => simp [par, cer]
  | cons b w ih =>
    simp only [par, List.flatMap_cons, List.cons_append, List.nil_append,
      List.append_assoc] at ih ⊢
    rw [cer]
    simp [ih]

/-- Separa uma palavra do ATK nos dois componentes do par. -/
def separa (u : List Bool) : Palavra × Palavra := (ATK.ModeloPNP.dec u, cer u)

theorem separa_par (w c : Palavra) : separa (par w c) = (w, c) := by
  simp [separa, ATK.ModeloPNP.dec_par, cer_par]

/-! ## A hipótese: quatro transcodificadores -/

/-- Quatro máquinas `FinTM2` de tempo polinomial entre as codificações do ATK e do
formal-conjectures. -/
structure Transcodificadores : Prop where
  /-- palavra crua ↦ codificação FC -/
  crua_fc : Nonempty (TM2ComputableInPolyTime cod encFC id)
  /-- codificação FC ↦ palavra crua -/
  fc_crua : Nonempty (TM2ComputableInPolyTime encFC cod id)
  /-- par na codificação FC ↦ par `⟨w, c⟩` do ATK -/
  par_fc : Nonempty (TM2ComputableInPolyTime encFCPar cod (fun p => par p.1 p.2))
  /-- palavra do ATK ↦ seus dois componentes, na codificação FC de pares -/
  separa_fc : Nonempty (TM2ComputableInPolyTime cod encFCPar separa)

/-! ## P e NP coincidem pelas duas definições -/

theorem emP_iff (T : Transcodificadores) (L : Linguagem) : EmP L ↔ caract L ∈ P := by
  constructor
  · rintro ⟨χ, hχ, ⟨M⟩⟩
    obtain ⟨T2⟩ := T.fc_crua
    have hχeq : χ = caract L := by
      funext w
      rw [Bool.eq_iff_iff, caract_eq_true]
      exact (hχ w).symm
    subst hχeq
    exact ⟨ATK.ComposicaoTM2.comp T2 M⟩
  · rintro ⟨M⟩
    obtain ⟨T1⟩ := T.crua_fc
    exact ⟨caract L, fun w => (caract_eq_true L w).symm, ⟨ATK.ComposicaoTM2.comp T1 M⟩⟩

theorem emNP_iff (T : Transcodificadores) (L : Linguagem) : EmNP L ↔ caract L ∈ NP := by
  constructor
  · rintro ⟨V, ⟨χ, hχ, ⟨MV⟩⟩, q, hq⟩
    obtain ⟨T3⟩ := T.par_fc
    refine ⟨q, fun p => χ (par p.1 p.2), ⟨ATK.ComposicaoTM2.comp T3 MV⟩, fun x => ?_⟩
    rw [caract_eq_true, hq x]
    exact exists_congr fun c => and_congr Iff.rfl (hχ (par x c))
  · rintro ⟨p, R, ⟨MR⟩, hR⟩
    obtain ⟨T4⟩ := T.separa_fc
    refine ⟨{u | R (separa u) = true},
      ⟨R ∘ separa, fun u => Iff.rfl, ⟨ATK.ComposicaoTM2.comp T4 MR⟩⟩, p, fun w => ?_⟩
    rw [← caract_eq_true, hR w]
    refine exists_congr fun c => and_congr Iff.rfl ?_
    show R (w, c) = true ↔ R (separa (par w c)) = true
    rw [separa_par]

/-- **Os dois enunciados de P ≠ NP são equivalentes**, dados os transcodificadores. -/
theorem pneNP_iff_fc (T : Transcodificadores) : PneNP ↔ P ≠ NP := by
  unfold PneNP
  apply not_congr
  constructor
  · intro h
    ext f
    rw [← caract_lang f, ← emP_iff T, ← emNP_iff T]
    exact Set.ext_iff.mp h (lang f)
  · intro h
    ext L
    show EmP L ↔ EmNP L
    rw [emP_iff T, emNP_iff T, h]

end ATK.IntegracaoFCPNP

#print axioms ATK.IntegracaoFCPNP.caract_eq_true
#print axioms ATK.IntegracaoFCPNP.caract_lang
#print axioms ATK.IntegracaoFCPNP.lang_caract
#print axioms ATK.IntegracaoFCPNP.encBool_eq
#print axioms ATK.IntegracaoFCPNP.cer_par
#print axioms ATK.IntegracaoFCPNP.separa_par
#print axioms ATK.IntegracaoFCPNP.emP_iff
#print axioms ATK.IntegracaoFCPNP.emNP_iff
#print axioms ATK.IntegracaoFCPNP.pneNP_iff_fc
