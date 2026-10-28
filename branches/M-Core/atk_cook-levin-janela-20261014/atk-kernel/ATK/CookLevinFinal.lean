import ATK.CookLevinPrograma

/-!
# ATK — Cook–Levin, marco CL5: SAT é NP-completo no modelo genuíno

Para cada verificador `V : TM2ComputableInPolyTime cod encodeBool χ` e polinômio `q`:

* `progCL V q`: o programa de laços (`aritP` e o molde `formulaT` da fórmula de Cook–Levin);
* **`progCL_out`**: a sua saída é exatamente `fCL V q w`;
* **`progCL_custo`**: o custo é `≤ B(|w|)` para um polinômio `B`;
* **`fCL_computavel`**: `fCL V q` é `TM2ComputableInPolyTime cod cod` (pelo compilador `Gerador`);
* **`cookLevin`**: `CookLevin modeloPNP SAT` — SAT ∈ NP e toda linguagem de NP se reduz a SAT.

Só com `propext`, `Classical.choice`, `Quot.sound`. **CLOSED_MATH continua false** (a ponte B4 é
uma das obrigações; P ≠ NP continua em aberto).
-/

namespace ATK.CookLevinFinal

set_option linter.unusedSectionVars false

open Turing Function ATK.Gerador ATK.CookLevinMolde ATK.CookLevinPrograma ATK.CookLevinTableau
  ATK.CookLevinReducao ATK.CookLevinVerificador ATK.LigacaoPNP ATK.ModeloPNP Computability
  ATK.CookLevinJanela
open scoped Classical

noncomputable section

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable {χ : Palavra → Bool} (V : TM2ComputableInPolyTime cod encodeBool χ) (q : Polynomial ℕ)

/-- A máquina restrita do verificador. -/
abbrev Mv := Mr V.tm.m V.tm.k₀ V.tm.k₁
abbrev Dv : ℕ := profMax (Mv V)
abbrev Pv : ℕ := pushMax (Mv V)
abbrev Cv : ℕ := Dv V + Pv V + 1

/-- O molde da fórmula do verificador. -/
def moldeV : FT (Var V.tm.K (fun k => ↥(R V.tm.m V.tm.k₀ V.tm.k₁ k)) V.tm.Λ V.tm.σ) (Rg (Cv V)) :=
  formulaT (Mv V) V.tm.k₀ V.tm.k₁ (gR V.tm.m V.tm.k₀ V.tm.k₁ V.inputAlphabet.symm)
    (yR V.tm.m V.tm.k₀ V.tm.k₁ (V.outputAlphabet.symm true)) V.tm.main V.tm.initialState

/-- **O programa da redução de Cook–Levin.** -/
def progCL : Prog (Rg (Cv V)) :=
  .seq (aritP (coefs q) (coefs V.time) (Pv V) (Dv V)) (comp (moldeV V))

theorem pre_length (w : Palavra) : (pre w).length = 2 * w.length + 2 := by
  simp only [pre, List.length_append, dobro_length]
  rfl

theorem regOK (w : Palavra) :
    RegOK (Mv V) w (run w (aritP (C := Cv V) (coefs q) (coefs V.time) (Pv V) (Dv V)) s0).regs := by
  obtain ⟨-, v, hsm⟩ := run_aritP (C := Cv V) w (coefs q) (coefs V.time) (Pv V) (Dv V)
  refine ⟨v.N, v.E2, by rw [v.X, v.E2, v.Mq], by rw [v.T1, v.TT], ?_, hsm, ?_⟩
  · rw [v.TP, v.SS, v.X]; omega
  · rw [v.SS]
    have : Pv V ≤ Pv V * (horn (2 * w.length + 2 + horn w.length (coefs q)) (coefs V.time) + 1) :=
      Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have e1 : Dv V = profMax (Mv V) := rfl
    have e2 : Pv V = pushMax (Mv V) := rfl
    omega

/-- **A saída do programa é a redução.** -/
theorem progCL_out (w : Palavra) : (run w (progCL V q) s0).out = fCL V q w := by
  obtain ⟨a1, v, -⟩ := run_aritP (C := Cv V) w (coefs q) (coefs V.time) (Pv V) (Dv V)
  have hok := (comp_ok cod3 w (moldeV V) idxR (wf_formulaT (Mv V) _ _ _ _ _ _)
    (run w (aritP (C := Cv V) (coefs q) (coefs V.time) (Pv V) (Dv V)) s0)).1
  rw [progCL, run_seqP, hok, a1, List.nil_append, moldeV,
    sem_formulaT (Mv V) _ _ _ _ _ _ w _ (by simp [Cv]) (regOK V q w), fmOutV_cod3]
  simp only [fCL, formulaW, formulaV]
  rw [v.TT, v.SS, v.Mq]
  simp only [horn_coefs]
  have hT : Tw V (q.eval w.length) w = V.time.eval (2 * w.length + 2 + q.eval w.length) := by
    simp [Tw, pre_length]
  have hS : Scel V.tm.m V.tm.k₀ V.tm.k₁ (pre w) (q.eval w.length)
      (V.time.eval (2 * w.length + 2 + q.eval w.length)) =
      2 * w.length + 2 + q.eval w.length +
        (Pv V * (V.time.eval (2 * w.length + 2 + q.eval w.length) + 1) + (Dv V + 1)) := by
    rw [Scel, pre_length]
    ring
  try rw [hT]
  rw [hS]
  rfl

/-! ### Custo polinomial -/

/-- O limite de todos os contadores, em função de `n = |w|`. -/
def Vn (n : ℕ) : ℕ :=
  2 * n + 2 + q.eval n + (Pv V * (V.time.eval (2 * n + 2 + q.eval n) + 1) + (Dv V + 1)) +
    V.time.eval (2 * n + 2 + q.eval n) + 1

/-- O limite do custo, em função de `V`. -/
def K1 (B : ℕ) : ℕ :=
  (5 * B + 3) * 7 + 3 + Ecost (coefs q) B + Ecost (coefs V.time) B + Pv V * (5 * B + 3) +
    (Dv V + 1) + Cv V * (5 * B + 3 + Cv V) + cb (moldeV V) B

theorem progCL_custo (w : Palavra) : cost w (progCL V q) s0 ≤ K1 V q (Vn V q w.length) := by
  have hV : 2 * w.length + 2 + horn w.length (coefs q) +
      (Pv V * (horn (2 * w.length + 2 + horn w.length (coefs q)) (coefs V.time) + 1) + (Dv V + 1)) +
      horn (2 * w.length + 2 + horn w.length (coefs q)) (coefs V.time) + 1 ≤ Vn V q w.length := by
    simp only [horn_coefs, Vn]; exact le_rfl
  have c1 := cost_aritP (C := Cv V) w (coefs q) (coefs V.time) (Pv V) (Dv V) _ hV
  have c2 := (comp_cost cod3 w (Vn V q w.length) (by simp only [Vn]; omega) (moldeV V) idxR
    (wf_formulaT (Mv V) _ _ _ _ _ _) _ (regs_le_V w (coefs q) (coefs V.time) (Pv V) (Dv V) _ hV)).1
  rw [progCL, cost_seqP]
  unfold K1
  omega

open Polynomial in
/-- `Ecost` como polinômio. -/
def EcostP (cs : List ℕ) : Polynomial ℕ :=
  C 5 + C cs.length * (C cs.sum * (C 5 * X ^ cs.length + C 3) + C 19 * X ^ cs.length + C 9) +
    X ^ cs.length

open Polynomial in
/-- `K1` como polinômio. -/
def K1P : Polynomial ℕ :=
  (C 5 * X + C 3) * C 7 + C 3 + EcostP (coefs q) + EcostP (coefs V.time) +
    C (Pv V) * (C 5 * X + C 3) + C (Dv V + 1) + C (Cv V) * (C 5 * X + C 3 + C (Cv V)) +
    cbP (moldeV V)

open Polynomial in
/-- `Vn` como polinômio. -/
def VnP : Polynomial ℕ :=
  (C 2 * X + C 2 + q) + (C (Pv V) * (V.time.comp (C 2 * X + C 2 + q) + 1) + C (Dv V + 1)) +
    V.time.comp (C 2 * X + C 2 + q) + 1

theorem eval_EcostP (cs : List ℕ) (B : ℕ) : (EcostP cs).eval B = Ecost cs B := by
  simp only [EcostP, Ecost, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]

theorem eval_K1P (B : ℕ) : (K1P V q).eval B = K1 V q B := by
  simp [K1P, K1, eval_EcostP, eval_cbP]

theorem eval_VnP (n : ℕ) : (VnP V q).eval n = Vn V q n := by
  simp [VnP, Vn, Polynomial.eval_comp]

/-- **A redução de Cook–Levin é computável por uma `FinTM2` em tempo polinomial.** -/
theorem fCL_computavel : Nonempty (TM2ComputableInPolyTime cod cod (fCL V q)) := by
  have h := computavel_nonempty (progCL V q) ((K1P V q).comp (VnP V q)) (fun w => by
    rw [Polynomial.eval_comp, eval_VnP, eval_K1P]; exact progCL_custo V q w)
  have hf : (fun w => (run w (progCL V q) s0).out) = fCL V q := funext (progCL_out V q)
  rw [hf] at h
  exact h

end

/-- **Cook–Levin.** SAT é NP-completo no modelo genuíno de P vs NP (`modeloPNP`): SAT ∈ NP e toda
linguagem de NP se reduz a SAT por uma `FinTM2` em tempo polinomial. -/
theorem cookLevin : ATK.Conditional.PvsNP.CookLevin modeloPNP SAT :=
  cookLevin_de_computavel fun _ V q => fCL_computavel V q


end ATK.CookLevinFinal

#print axioms ATK.CookLevinFinal.Mv
#print axioms ATK.CookLevinFinal.Dv
#print axioms ATK.CookLevinFinal.Pv
#print axioms ATK.CookLevinFinal.Cv
#print axioms ATK.CookLevinFinal.moldeV
#print axioms ATK.CookLevinFinal.progCL
#print axioms ATK.CookLevinFinal.pre_length
#print axioms ATK.CookLevinFinal.regOK
#print axioms ATK.CookLevinFinal.progCL_out
#print axioms ATK.CookLevinFinal.Vn
#print axioms ATK.CookLevinFinal.K1
#print axioms ATK.CookLevinFinal.progCL_custo
#print axioms ATK.CookLevinFinal.EcostP
#print axioms ATK.CookLevinFinal.K1P
#print axioms ATK.CookLevinFinal.VnP
#print axioms ATK.CookLevinFinal.eval_EcostP
#print axioms ATK.CookLevinFinal.eval_K1P
#print axioms ATK.CookLevinFinal.eval_VnP
#print axioms ATK.CookLevinFinal.fCL_computavel
#print axioms ATK.CookLevinFinal.cookLevin
