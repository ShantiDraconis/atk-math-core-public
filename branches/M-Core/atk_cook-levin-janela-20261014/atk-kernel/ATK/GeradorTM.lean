import ATK.Gerador
import Mathlib.Computability.TuringMachine.Computable

/-!
# ATK — Cook–Levin, marco CL4b-3: todo programa de laços é uma `FinTM2` em tempo polinomial

* `codigo p`: o programa montado, seguido da cópia da saída (a pilha de trabalho invertida vai
  para a pilha de saída) e da limpeza de contadores e entrada;
* `maq p`: a `FinTM2` desse código;
* `roda`: da configuração inicial de `w` à configuração final com `(run w p s0).out` na saída,
  em no máximo `(|R| + 2) · cost w p s0 + |R| + |w| + 3` passos;
* **`computavel`**: se `cost w p s0 ≤ B(|w|)` para um polinômio `B`, então
  `w ↦ (run w p s0).out` é `TM2ComputableInPolyTime`.

**Nada aqui prova Cook–Levin. CLOSED_MATH continua false.**
-/

namespace ATK.Gerador

set_option linter.unusedSectionVars false

open Turing Function

noncomputable section

variable {R : Type} [DecidableEq R]

/-- Estado inicial: contadores zerados, saída vazia. -/
def s0 : St R := ⟨fun _ => 0, []⟩

/-! ### Crescimento da saída e dos contadores -/

/-- Medida que cresce no máximo um por passo: tamanho da saída mais (talvez) um contador. -/
def mu (o : Option R) (s : St R) : ℕ := s.out.length + o.elim 0 s.regs

theorem run_le (w : List Bool) (o : Option R) :
    ∀ (p : Prog R) (s : St R), mu o (run w p s) ≤ mu o s + cost w p s
  | .skip, s => by simp [run, cost]
  | .out b, s => by simp [run, cost, mu]; omega
  | .inc r', s => by
    simp only [run, cost, mu]
    rcases o with _ | r
    · simp
    · by_cases h : r = r'
      · subst h; simp; omega
      · simp [update_of_ne h]
  | .dec r', s => by
    simp only [run, cost, mu]
    rcases o with _ | r
    · simp
    · by_cases h : r = r'
      · subst h; simp; omega
      · simp [update_of_ne h]
  | .clr r', s => by
    simp only [run, cost, mu]
    rcases o with _ | r
    · simp
    · by_cases h : r = r'
      · subst h; simp; omega
      · simp [update_of_ne h]
  | .seq p q, s => by
    have h1 := run_le w o p s
    have h2 := run_le w o q (run w p s)
    simp only [run, cost]
    omega
  | .loop r' p, s => by
    have it : ∀ n s', mu o ((run w p)^[n] s') ≤ mu o s' + costIt (cost w p) (run w p) n s' := by
      intro n
      induction n with
      | zero => intro s'; simp [costIt]
      | succ n ih =>
        intro s'
        have := run_le w o p s'
        have := ih (run w p s')
        simp only [iterate_succ_apply, costIt]
        omega
    have := it (s.regs r') s
    simp only [run, cost]
    omega
  | .forIn p₀ p₁, s => by
    have it : ∀ (bs : List Bool) s', mu o (bs.foldl (fun s b => if b then run w p₁ s else
        run w p₀ s) s') ≤ mu o s' + costIn (cost w p₀) (cost w p₁) (run w p₀) (run w p₁) bs s' := by
      intro bs
      induction bs with
      | nil => intro s'; simp [costIn]
      | cons b bs ih =>
        intro s'
        cases b with
        | false =>
          have := run_le w o p₀ s'
          have := ih (run w p₀ s')
          simp only [List.foldl_cons, Bool.false_eq_true, ↓reduceIte, costIn]
          omega
        | true =>
          have := run_le w o p₁ s'
          have := ih (run w p₁ s')
          simp only [List.foldl_cons, ↓reduceIte, costIn]
          omega
    have := it w s
    simp only [run, cost]
    omega

theorem out_le (w : List Bool) (p : Prog R) : (run w p s0).out.length ≤ cost w p s0 := by
  have := run_le w none p s0
  simpa [mu, s0] using this

theorem regs_le (w : List Bool) (p : Prog R) (r : R) : (run w p s0).regs r ≤ cost w p s0 := by
  have := run_le w (some r) p s0
  simp only [mu, Option.elim] at this
  have h0 : (s0 : St R).out.length = 0 ∧ (s0 : St R).regs r = 0 := ⟨rfl, rfl⟩
  omega

/-! ### O código completo e a máquina -/

variable [Fintype R]

/-- Os contadores em lista. -/
def regsL (R : Type) [Fintype R] : List R := (Finset.univ : Finset R).toList

theorem length_regsL : (regsL R).length = Fintype.card R := by simp [regsL]

/-- O código completo de `p`. -/
def codigo (p : Prog R) : List (Ins (Pk R (depth p))) :=
  asm (depth p) p 0 0 ++ [.mv Pk.wrk Pk.outp] ++ (regsL R).map (fun r => .clr (Pk.reg r)) ++
    [.clr Pk.inp, .halt]

/-- A máquina de `p`. -/
abbrev maq (p : Prog R) : FinTM2 where
  K := Pk R (depth p)
  k₀ := Pk.inp
  k₁ := Pk.outp
  Γ := fun _ => Bool
  Λ := Fin ((codigo p).length + 1)
  main := lab (codigo p).length 0
  σ := Bool
  initialState := false
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := prog (codigo p)

theorem Loc.self {κ : Type} (code : List (Ins κ)) : Loc code 0 code := fun i hi => by
  simp [List.getElem?_eq_getElem hi]

theorem halt_ok {κ : Type} [DecidableEq κ] {code : List (Ins κ)} {a : ℕ}
    (h : code[a]? = some .halt) (v : Bool) (S : κ → List Bool) :
    Reach (TM2.step (prog code)) (cfg code a v S) ⟨none, false, S⟩ 1 :=
  Reach.one (by rw [step_at h]; simp [stmt, TM2.stepAux])

/-- Limpar uma lista de contadores em sequência. -/
theorem clrs_ok {D : ℕ} {code : List (Ins (Pk R D))} :
    ∀ (rs : List R) (a : ℕ) (S : Pk R D → List Bool) (v : Bool),
      (∀ i (h : i < rs.length), code[a + i]? = some (.clr (Pk.reg rs[i]))) →
      ∃ v', Reach (TM2.step (prog code)) (cfg code a v S)
        (cfg code (a + rs.length) v' (fun k => if ∃ r ∈ rs, k = Pk.reg r then [] else S k))
        ((rs.map fun r => (S (Pk.reg r)).length + 1).sum)
  | [], a, S, v, _ => ⟨v, by simpa using Reach.refl _⟩
  | r :: rs, a, S, v, h => by
    have h0 : code[a]? = some (.clr (Pk.reg r)) := by
      have := h 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at this
      exact this
    have r1 := clr_ok h0 (S (Pk.reg r)) v S rfl
    obtain ⟨v', r2⟩ := clrs_ok rs (a + 1) (update S (Pk.reg r) []) false fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    refine ⟨v', ?_⟩
    have e : (fun k => if ∃ r' ∈ rs, k = Pk.reg r' then [] else update S (Pk.reg r) [] k) =
        (fun k => if ∃ r' ∈ r :: rs, k = Pk.reg r' then [] else S k) := by
      funext k
      by_cases hk : k = Pk.reg r
      · subst hk; simp
      · by_cases hk' : ∃ r' ∈ rs, k = Pk.reg r'
        · have : ∃ r' ∈ r :: rs, k = Pk.reg r' := by
            obtain ⟨r', hr', e⟩ := hk'; exact ⟨r', List.mem_cons_of_mem _ hr', e⟩
          simp only [hk', this, ↓reduceIte]
        · have : ¬ ∃ r' ∈ r :: rs, k = Pk.reg r' := by
            rintro ⟨r', hr', e⟩
            rcases List.mem_cons.mp hr' with rfl | hr'
            · exact hk e
            · exact hk' ⟨r', hr', e⟩
          simp only [hk', this, ↓reduceIte, update_of_ne hk]
    rw [e] at r2
    have ea : a + 1 + rs.length = a + (r :: rs).length := by simp; omega
    rw [ea] at r2
    have hle : ((rs.map fun r' => ((update S (Pk.reg r) []) (Pk.reg r')).length + 1).sum) ≤
        ((rs.map fun r' => (S (Pk.reg r')).length + 1).sum) := by
      apply List.sum_le_sum
      intro r' _
      by_cases hr : r' = r
      · subst hr; simp
      · simp [update_of_ne (show Pk.reg r' ≠ (Pk.reg r : Pk R D) by simpa using hr)]
    refine (r1.trans r2).mono ?_
    simp only [List.map_cons, List.sum_cons]
    omega

theorem sum_le_card (w : List Bool) (p : Prog R) (S : Pk R (depth p) → List Bool)
    (hS : ∀ r, (S (Pk.reg r)).length ≤ cost w p s0) :
    ((regsL R).map fun r => (S (Pk.reg r)).length + 1).sum ≤
      Fintype.card R * (cost w p s0 + 1) := by
  have := List.sum_le_length_nsmul ((regsL R).map fun r => (S (Pk.reg r)).length + 1)
    (cost w p s0 + 1) (by
      intro x hx
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp hx
      have := hS r; omega)
  simpa [length_regsL] using this

/-- As pilhas iniciais. -/
def S0 (D : ℕ) (w : List Bool) : Pk R D → List Bool := update (fun _ => []) Pk.inp w

theorem inv_S0 (D : ℕ) (w : List Bool) : Inv 0 w (S0 (R := R) D w) :=
  ⟨by simp [S0], by simp [S0], by simp [S0], fun r => by simp [S0],
    fun i _ => ⟨by simp [S0], by simp [S0]⟩⟩

theorem stOf_S0 (D : ℕ) (w : List Bool) : stOf (S0 (R := R) D w) = s0 := by
  simp [stOf, S0, s0]

theorem mem_regsL (r : R) : r ∈ regsL R := by simp [regsL]

/-- A execução completa, para qualquer código que contenha o programa e o epílogo. -/
theorem roda_gen (p : Prog R) (w : List Bool) (code : List (Ins (Pk R (depth p))))
    (hL : Loc code 0 (asm (depth p) p 0 0 ++ [.mv Pk.wrk Pk.outp] ++
      (regsL R).map (fun r => .clr (Pk.reg r)) ++ [.clr Pk.inp, .halt])) :
    Reach (TM2.step (prog code)) (cfg code 0 false (S0 (depth p) w))
      ⟨none, false, update (fun _ => []) Pk.outp (run w p s0).out⟩
      ((Fintype.card R + 2) * cost w p s0 + Fintype.card R + w.length + 3) := by
  -- o programa
  obtain ⟨v1, r1⟩ := asm_ok code w p 0 0 (S0 (depth p) w) false hL.left.left.left (by simp)
    (inv_S0 (depth p) w)
  rw [stOf_S0] at r1
  simp only [Nat.zero_add] at r1
  -- cópia da saída
  set S1 := put (S0 (depth p) w) (run w p s0) with hS1
  have c1 : code[size p]? = some (.mv Pk.wrk Pk.outp) := by
    simpa using hL.left.left.right.atE (i := 0) (b := size p) (by simp) (by simp [length_asm])
  have r2 := mv_ok (s := Pk.wrk) (d := Pk.outp) (by simp) c1 (S1 Pk.wrk) v1 S1 rfl
  set S2 := update (update S1 Pk.wrk []) Pk.outp ((S1 Pk.wrk).reverse ++ S1 Pk.outp) with hS2
  -- limpeza dos contadores
  obtain ⟨v3, r3⟩ := clrs_ok (code := code) (regsL R) (size p + 1) S2 false fun i hi => by
    have := hL.left.right.atE (i := i) (b := size p + 1 + i) (by simpa using hi)
      (by simp [length_asm])
    simpa using this
  set S3 : Pk R (depth p) → List Bool :=
    fun k => if ∃ r ∈ regsL R, k = Pk.reg r then [] else S2 k with hS3
  -- limpeza da entrada
  have c4 : code[size p + 1 + (regsL R).length]? = some (.clr Pk.inp) := by
    simpa using hL.right.atE (i := 0) (b := size p + 1 + (regsL R).length) (by simp)
      (by simp [length_asm]; omega)
  have r4 := clr_ok c4 (S3 Pk.inp) v3 S3 rfl
  have c5 : code[size p + 1 + (regsL R).length + 1]? = some .halt := by
    simpa using hL.right.atE (i := 1) (b := size p + 1 + (regsL R).length + 1) (by simp)
      (by simp [length_asm]; omega)
  have r5 := halt_ok c5 false (update S3 Pk.inp [])
  have tot := (((r1.trans r2).trans r3).trans r4).trans r5
  -- pilhas finais
  have eF : update S3 Pk.inp [] = update (fun _ => []) Pk.outp (run w p s0).out := by
    funext k
    rcases k with b | r | i | i
    · cases b <;> simp [hS3, hS2, hS1, put, S0]
    · simp [hS3, mem_regsL]
    · simp [hS3, hS2, hS1, put, S0]
    · simp [hS3, hS2, hS1, put, S0]
  rw [eF] at tot
  refine tot.mono ?_
  -- custo
  have hout : (S1 Pk.wrk).length ≤ cost w p s0 := by
    simpa [hS1, put] using out_le w p
  have hsum := sum_le_card w p S2 (fun r => by
    simpa [hS2, hS1, put] using regs_le w p r)
  have hinp : (S3 Pk.inp).length = w.length := by simp [hS3, hS2, hS1, put, S0]
  rw [hinp]
  have e1 : (Fintype.card R + 2) * cost w p s0 =
      Fintype.card R * cost w p s0 + 2 * cost w p s0 := by ring
  have e2 : Fintype.card R * (cost w p s0 + 1) =
      Fintype.card R * cost w p s0 + Fintype.card R := by ring
  rw [e2] at hsum
  rw [e1]
  omega

/-- **A execução completa** da máquina de `p`. -/
theorem roda (p : Prog R) (w : List Bool) :
    Reach (TM2.step (prog (codigo p))) (cfg (codigo p) 0 false (S0 (depth p) w))
      ⟨none, false, update (fun _ => []) Pk.outp (run w p s0).out⟩
      ((Fintype.card R + 2) * cost w p s0 + Fintype.card R + w.length + 3) :=
  roda_gen p w (codigo p) (Loc.self _)

theorem initList_maq (p : Prog R) (w : List Bool) :
    initList (maq p) w = cfg (codigo p) 0 false (S0 (depth p) w) := by
  simp only [initList, cfg, maq]
  congr 1
  funext k
  by_cases hk : k = Pk.inp
  · subst hk; simp [S0]
  · simp [S0, hk]

theorem haltList_maq (p : Prog R) (l : List Bool) :
    haltList (maq p) l = ⟨none, false, update (fun _ => []) Pk.outp l⟩ := by
  simp only [haltList, maq]
  congr 1
  funext k
  by_cases hk : k = Pk.outp
  · subst hk; simp
  · simp [hk]

/-- **Todo programa de custo polinomial é uma `FinTM2` em tempo polinomial.** -/
def computavel (p : Prog R) (B : Polynomial ℕ) (hB : ∀ w, cost w p s0 ≤ B.eval w.length) :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id (fun w => (run w p s0).out) where
  tm := maq p
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C (Fintype.card R + 2) * B + Polynomial.X +
    Polynomial.C (Fintype.card R + 3)
  outputsFun w := by
    have hr := roda p w
    have hk := (Classical.choose_spec hr).1
    have he := (Classical.choose_spec hr).2
    have hin : List.map (Equiv.refl Bool).invFun (id w) = w := by simp
    have hout : List.map (Equiv.refl Bool).invFun (id (run w p s0).out) = (run w p s0).out := by
      simp
    refine ⟨⟨Classical.choose hr, ?_⟩, ?_⟩
    · rw [hin, hout, initList_maq, Option.map_some, haltList_maq]
      exact he
    · have := hB w
      simp only [id, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      refine hk.trans ?_
      have : (Fintype.card R + 2) * cost w p s0 ≤ (Fintype.card R + 2) * B.eval w.length :=
        Nat.mul_le_mul_left _ this
      omega

theorem computavel_nonempty (p : Prog R) (B : Polynomial ℕ)
    (hB : ∀ w, cost w p s0 ≤ B.eval w.length) :
    Nonempty (TM2ComputableInPolyTime (id : List Bool → List Bool) id
      (fun w => (run w p s0).out)) :=
  ⟨computavel p B hB⟩

end

end ATK.Gerador

#print axioms ATK.Gerador.s0
#print axioms ATK.Gerador.mu
#print axioms ATK.Gerador.run_le
#print axioms ATK.Gerador.out_le
#print axioms ATK.Gerador.regs_le
#print axioms ATK.Gerador.regsL
#print axioms ATK.Gerador.length_regsL
#print axioms ATK.Gerador.codigo
#print axioms ATK.Gerador.maq
#print axioms ATK.Gerador.Loc.self
#print axioms ATK.Gerador.halt_ok
#print axioms ATK.Gerador.clrs_ok
#print axioms ATK.Gerador.sum_le_card
#print axioms ATK.Gerador.S0
#print axioms ATK.Gerador.inv_S0
#print axioms ATK.Gerador.stOf_S0
#print axioms ATK.Gerador.mem_regsL
#print axioms ATK.Gerador.roda_gen
#print axioms ATK.Gerador.roda
#print axioms ATK.Gerador.initList_maq
#print axioms ATK.Gerador.haltList_maq
#print axioms ATK.Gerador.computavel
#print axioms ATK.Gerador.computavel_nonempty
