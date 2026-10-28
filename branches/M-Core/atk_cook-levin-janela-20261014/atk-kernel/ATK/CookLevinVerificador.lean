import ATK.CookLevinRestricao
import ATK.CookLevinInicio
import ATK.LigacaoPNP
import ATK.ComposicaoTM2
import Mathlib.Data.Set.Finite.Lattice

/-!
# ATK — Cook–Levin, marco CL3d: a fórmula de um verificador NP

Junta as peças CL1–CL3c para uma máquina de pilhas qualquer (só os alfabetos de entrada e de saída
precisam ser finitos, como numa `FinTM2`):

* `formulaV`: restringe os alfabetos aos símbolos que aparecem (CL3b), monta o tableau (CL2) com
  a linha inicial de certificado livre (CL3c) e a aceitação;
* **`formulaV_correta`**: `formulaV` é satisfatível ⇔ existe certificado `c` com `|c| ≤ m` que leva a
  máquina, em `T` passos, a parar com `y` no topo da pilha de saída;
* **`verificador_tableau`**: para um verificador `V` em tempo polinomial (uma
  `TM2ComputableInPolyTime cod encodeBool χ`), `formulaW V m w` é satisfatível ⇔
  `∃ c, |c| ≤ m ∧ χ (par w c) = true`.

É a correção matemática da redução de Cook–Levin. **Falta CL4**: a fórmula precisa ser escrita em
`ℕ` (`codCNF`) por uma `FinTM2` em tempo polinomial — só então `L ≤p SAT`. Contador da ponte segue
1/8. **CLOSED_MATH continua false.**
-/

namespace ATK.CookLevinVerificador

open Turing Function ATK.CookLevinJanela ATK.CookLevinTableau ATK.CookLevinRestricao ATK.CookLevinInicio
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Máquina genérica -/

section Generico

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ : Type} [Fintype Λ]
  {σ : Type} [Fintype σ] (M : Λ → TM2.Stmt Γ Λ σ) (k₀ k₁ : K) [Finite (Γ k₀)] [Finite (Γ k₁)]

/-- Os símbolos que importam: entrada, saída e o que a máquina empilha. -/
def R : ∀ k, Set (Γ k) := fun k => {a | k = k₀ ∨ k = k₁ ∨ ∃ l, a ∈ pushSet (M l) k}

theorem R_finite (k : K) : (R M k₀ k₁ k).Finite := by
  by_cases h0 : k = k₀
  · subst h0; exact Set.toFinite _
  by_cases h1 : k = k₁
  · subst h1; exact Set.toFinite _
  refine (Set.finite_iUnion fun l => pushSet_finite (M l) k).subset ?_
  rintro a (h | h | ⟨l, hl⟩)
  · exact absurd h h0
  · exact absurd h h1
  · exact Set.mem_iUnion.mpr ⟨l, hl⟩

instance instFintypeR (k : K) : Fintype ↥(R M k₀ k₁ k) := (R_finite M k₀ k₁ k).fintype

theorem pushSet_R (l : Λ) (k : K) : pushSet (M l) k ⊆ R M k₀ k₁ k :=
  fun _ ha => Or.inr (Or.inr ⟨l, ha⟩)

/-- A máquina restrita. -/
def Mr : Λ → TM2.Stmt (fun k => ↥(R M k₀ k₁ k)) Λ σ := restr M (pushSet_R M k₀ k₁)

/-- Bits de entrada e símbolo de aceitação, no alfabeto restrito. -/
def gR (g : Bool → Γ k₀) : Bool → ↥(R M k₀ k₁ k₀) := fun b => ⟨g b, Or.inl rfl⟩
def yR (y : Γ k₁) : ↥(R M k₀ k₁ k₁) := ⟨y, Or.inr (Or.inl rfl)⟩

variable (g : Bool → Γ k₀) (y : Γ k₁) (pre : List Bool) (m T : ℕ) (main : Λ) (s₀ : σ)

/-- O número de células por pilha: cabe tudo durante os `T` passos. -/
def Scel : ℕ :=
  pre.length + m + (T + 1) * pushMax (Mr M k₀ k₁) + profMax (Mr M k₀ k₁) + 1

/-- **A fórmula do verificador.** -/
def formulaV : Fm (Var K (fun k => ↥(R M k₀ k₁ k)) Λ σ) :=
  formula (Mr M k₀ k₁) T (Scel M k₀ k₁ pre m T)
    (iniF k₀ (pre.map (gR M k₀ k₁ g)) (gR M k₀ k₁ g) m main s₀ (Scel M k₀ k₁ pre m T)) k₁ (yR M k₀ k₁ y)

/-- A configuração inicial restrita de um certificado. -/
abbrev cfgR (c : List Bool) : TM2.Cfg (fun k => ↥(R M k₀ k₁ k)) Λ σ :=
  cfgIni (Γ := fun k => ↥(R M k₀ k₁ k)) k₀ (pre.map (gR M k₀ k₁ g)) (gR M k₀ k₁ g) main s₀ c

theorem valC_cfgR (c : List Bool) :
    valC (cfgR M k₀ k₁ g pre main s₀ c) = cfgIni k₀ (pre.map g) g main s₀ c := by
  simp only [cfgR, valC, cfgIni, TM2.Cfg.mk.injEq, true_and]
  funext k
  by_cases hk : k = k₀
  · subst hk
    simp only [valS, update_self, List.map_append, List.map_map]
    rfl
  · simp [valS, update_of_ne hk]

/-- **A fórmula do verificador é fiel.** -/
theorem formulaV_correta :
    (∃ τ, Sat τ (formulaV M k₀ k₁ g y pre m T main s₀)) ↔
      ∃ c : List Bool, c.length ≤ m ∧
        (run M (cfgIni k₀ (pre.map g) g main s₀ c) T).l = none ∧
        ((run M (cfgIni k₀ (pre.map g) g main s₀ c) T).stk k₁)[0]? = some y := by
  have hS : (pre.map (gR M k₀ k₁ g)).length + m < Scel M k₀ k₁ pre m T := by
    simp only [List.length_map, Scel]; omega
  rw [formulaV, tableau_correto (M := Mr M k₀ k₁) (I := Ini k₀ (pre.map (gR M k₀ k₁ g)) (gR M k₀ k₁ g) m main s₀)
    (by simp only [Scel]; omega) (by simp only [Scel]; omega) ?_ (fun τ hL hI => ini_dec hS hL hI)
    (fun C ⟨c, hc, hC⟩ τ h => by subst hC; exact ini_sat hc hS h)]
  · constructor
    · rintro ⟨C, ⟨c, hc, rfl⟩, hl, hy⟩
      have e := run_restr M (pushSet_R M k₀ k₁) (cfgR M k₀ k₁ g pre main s₀ c) T
      rw [valC_cfgR] at e
      refine ⟨c, hc, ?_, ?_⟩
      · rw [← e]; exact hl
      · rw [← e]
        simp only [valC, valS, List.getElem?_map]
        rw [show (Mr M k₀ k₁) = restr M (pushSet_R M k₀ k₁) from rfl] at hy
        rw [hy]
        rfl
    · rintro ⟨c, hc, hl, hy⟩
      have e := run_restr M (pushSet_R M k₀ k₁) (cfgR M k₀ k₁ g pre main s₀ c) T
      rw [valC_cfgR] at e
      refine ⟨_, ⟨c, hc, rfl⟩, ?_, ?_⟩
      · have := congrArg TM2.Cfg.l e
        simp only [valC] at this
        rw [show (Mr M k₀ k₁) = restr M (pushSet_R M k₀ k₁) from rfl, this, hl]
      · have := congrArg (fun C => (C.stk k₁)[0]?) e
        simp only [valC, valS, List.getElem?_map] at this
        rw [hy] at this
        rw [show (Mr M k₀ k₁) = restr M (pushSet_R M k₀ k₁) from rfl]
        cases h : ((run (restr M (pushSet_R M k₀ k₁))
            (cfgR M k₀ k₁ g pre main s₀ c) T).stk k₁)[0]? with
        | none => rw [h] at this; simp at this
        | some a =>
          rw [h] at this
          simp only [Option.map_some, Option.some.injEq] at this
          rw [Option.some.injEq]
          exact Subtype.ext this
  · rintro C ⟨c, hc, hC⟩ t ht k
    have h1 : t * pushMax (Mr M k₀ k₁) ≤ T * pushMax (Mr M k₀ k₁) := Nat.mul_le_mul_right _ ht
    have h3 := run_len (Mr M k₀ k₁) C k t
    have h2 : (C.stk k).length ≤ pre.length + m := by
      subst hC
      by_cases hk : k = k₀
      · subst hk; rw [cfgIni_k₀]; simp; omega
      · rw [cfgIni_ne hk]; simp
    have h4 : Scel M k₀ k₁ pre m T =
        pre.length + m + (T + 1) * pushMax (Mr M k₀ k₁) + profMax (Mr M k₀ k₁) + 1 := rfl
    have h5 : (T + 1) * pushMax (Mr M k₀ k₁) = T * pushMax (Mr M k₀ k₁) + pushMax (Mr M k₀ k₁) :=
      Nat.succ_mul _ _
    omega

end Generico

/-! ### Execução e `EvalsTo` -/

section Execucao

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (M : Λ → TM2.Stmt Γ Λ σ)

theorem iter_none (n : ℕ) : (flip bind (TM2.step M))^[n] none = none := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih

theorem run_de_iter : ∀ (n : ℕ) (a b : TM2.Cfg Γ Λ σ),
    (flip bind (TM2.step M))^[n] (some a) = some b → run M a n = b
  | 0, a, b, h => by simpa [run] using h
  | n + 1, a, b, h => by
    rw [Function.iterate_succ_apply] at h
    change (flip bind (TM2.step M))^[n] (TM2.step M a) = some b at h
    cases hs : TM2.step M a with
    | none => rw [hs, iter_none] at h; exact absurd h (by simp)
    | some a' =>
      rw [hs] at h
      have := run_de_iter n a' b h
      simp only [run, Function.iterate_succ_apply]
      have hp : passo M a = a' := by simp [passo, hs]
      rw [hp]
      exact this

theorem run_parada (b : TM2.Cfg Γ Λ σ) (hb : b.l = none) : ∀ t, run M b t = b
  | 0 => rfl
  | t + 1 => by
    obtain ⟨l, v, S⟩ := b
    simp only at hb
    subst hb
    rw [run_succ, run_parada _ rfl t, passo_none]

/-- Se a execução chega a uma configuração parada em `n ≤ T` passos, `run M a T` é ela. -/
theorem run_de_evals {a b : TM2.Cfg Γ Λ σ} {n T : ℕ}
    (h : (flip bind (TM2.step M))^[n] (some a) = some b) (hb : b.l = none) (hn : n ≤ T) :
    run M a T = b := by
  have e : run M a T = run M (run M a n) (T - n) := by
    simp only [run]
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hn]
  rw [e, run_de_iter M n a b h, run_parada M b hb]

end Execucao

/-! ### O verificador de uma linguagem NP -/

section Verificador

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

open ATK.LigacaoPNP Computability StateTransition

variable {χ : Palavra → Bool} (V : TM2ComputableInPolyTime cod encodeBool χ)

/-- O prefixo de `par w c` (bits de `w` duplicados e o separador). -/
def pre (w : Palavra) : List Bool := (w.flatMap fun b => [b, b]) ++ [false, true]

theorem par_eq (w c : Palavra) : par w c = pre w ++ c := rfl

instance finSaida : Finite (V.tm.Γ V.tm.k₁) := Finite.of_equiv _ V.outputAlphabet.symm

/-- O número de passos do tableau para a palavra `w` e certificados até `m`. -/
def Tw (m : ℕ) (w : Palavra) : ℕ := V.time.eval ((pre w).length + m)

/-- **A fórmula de Cook–Levin de `w`** (sobre variáveis abstratas). -/
def formulaW (m : ℕ) (w : Palavra) :=
  formulaV V.tm.m V.tm.k₀ V.tm.k₁ V.inputAlphabet.symm (V.outputAlphabet.symm true) (pre w) m
    (Tw V m w) V.tm.main V.tm.initialState

theorem initList_eq (w c : Palavra) :
    initList V.tm ((par w c).map V.inputAlphabet.invFun) =
      cfgIni V.tm.k₀ ((pre w).map V.inputAlphabet.symm) V.inputAlphabet.symm V.tm.main
        V.tm.initialState c := by
  simp only [initList, cfgIni, par_eq, List.map_append]
  congr 1
  funext k
  by_cases hk : k = V.tm.k₀
  · subst hk; simp
  · simp [hk]

/-- **O tableau do verificador.** A fórmula de `w` é satisfatível se e só se algum certificado
de comprimento `≤ m` faz o verificador aceitar `par w c`. -/
theorem verificador_tableau (m : ℕ) (w : Palavra) :
    (∃ τ, Sat τ (formulaW V m w)) ↔ ∃ c : Palavra, c.length ≤ m ∧ χ (par w c) = true := by
  rw [formulaW, formulaV_correta]
  refine exists_congr fun c => and_congr_right fun hc => ?_
  have ev := V.outputsFun (par w c)
  have hT : ev.steps ≤ Tw V m w := by
    refine ev.steps_le_m.trans (ATK.ComposicaoTM2.eval_mono _ ?_)
    simp only [cod, id, par_eq, List.length_append]
    omega
  have hev := ev.evals_in_steps
  simp only [cod, id, encodeBool] at hev
  have hrun := run_de_evals V.tm.m (a := initList V.tm ((par w c).map V.inputAlphabet.invFun))
    (b := haltList V.tm [V.outputAlphabet.invFun (χ (par w c))]) (n := ev.steps) (T := Tw V m w)
    hev rfl hT
  rw [initList_eq] at hrun
  rw [hrun]
  have hk : (haltList V.tm [V.outputAlphabet.invFun (χ (par w c))]).stk V.tm.k₁ =
      [V.outputAlphabet.invFun (χ (par w c))] := by simp [haltList]
  rw [hk]
  simp only [haltList, List.getElem?_cons_zero, Option.some.injEq, true_and]
  constructor
  · intro h
    have := congrArg V.outputAlphabet h
    simpa using this
  · intro h
    rw [h]
    rfl

end Verificador

end

end ATK.CookLevinVerificador

#print axioms ATK.CookLevinVerificador.R
#print axioms ATK.CookLevinVerificador.R_finite
#print axioms ATK.CookLevinVerificador.instFintypeR
#print axioms ATK.CookLevinVerificador.pushSet_R
#print axioms ATK.CookLevinVerificador.Mr
#print axioms ATK.CookLevinVerificador.gR
#print axioms ATK.CookLevinVerificador.yR
#print axioms ATK.CookLevinVerificador.Scel
#print axioms ATK.CookLevinVerificador.formulaV
#print axioms ATK.CookLevinVerificador.cfgR
#print axioms ATK.CookLevinVerificador.valC_cfgR
#print axioms ATK.CookLevinVerificador.formulaV_correta
#print axioms ATK.CookLevinVerificador.iter_none
#print axioms ATK.CookLevinVerificador.run_de_iter
#print axioms ATK.CookLevinVerificador.run_parada
#print axioms ATK.CookLevinVerificador.run_de_evals
#print axioms ATK.CookLevinVerificador.pre
#print axioms ATK.CookLevinVerificador.par_eq
#print axioms ATK.CookLevinVerificador.finSaida
#print axioms ATK.CookLevinVerificador.Tw
#print axioms ATK.CookLevinVerificador.formulaW
#print axioms ATK.CookLevinVerificador.initList_eq
#print axioms ATK.CookLevinVerificador.verificador_tableau
