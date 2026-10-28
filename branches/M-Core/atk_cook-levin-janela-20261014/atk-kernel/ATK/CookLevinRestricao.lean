import ATK.CookLevinTableau
import Mathlib.Data.Set.Finite.Range

/-!
# ATK — Cook–Levin, marco CL3b: alfabetos finitos

Uma `FinTM2` só exige alfabeto finito na pilha de entrada; as outras pilhas podem ter alfabetos
infinitos. O tableau (CL2–CL3) precisa de alfabetos finitos. Mas uma máquina só escreve símbolos
`f v` dos seus `push`, com `v` no conjunto finito de estados: os símbolos que aparecem formam um
conjunto finito.

* `pushSet q k`: os símbolos que a instrução `q` pode empilhar em `k`; é finito (`pushSet_finite`);
* `tr q`: a mesma instrução sobre os alfabetos restritos `R k ⊇ pushSet`;
* **`run_tr`**: a máquina restrita roda exatamente como a original (`valC` esquece a restrição).

**Nada aqui prova Cook–Levin. CLOSED_MATH continua false.**
-/

namespace ATK.CookLevinRestricao

open Turing Function ATK.CookLevinTableau

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Os símbolos que uma instrução pode empilhar em cada pilha. -/
def pushSet : TM2.Stmt Γ Λ σ → ∀ k, Set (Γ k)
  | .push k' f q => fun k => {a | ∃ (h : k' = k) (v : σ), h ▸ f v = a} ∪ pushSet q k
  | .peek _ _ q => pushSet q
  | .pop _ _ q => pushSet q
  | .load _ q => pushSet q
  | .branch _ q₁ q₂ => fun k => pushSet q₁ k ∪ pushSet q₂ k
  | .goto _ => fun _ => ∅
  | .halt => fun _ => ∅

theorem pushSet_finite [Finite σ] : ∀ (q : TM2.Stmt Γ Λ σ) (k : K), (pushSet q k).Finite
  | .push k' f q, k => by
    refine Set.Finite.union ?_ (pushSet_finite q k)
    by_cases hk : k' = k
    · subst hk
      refine (Set.finite_range f).subset ?_
      rintro a ⟨h, v, rfl⟩
      exact ⟨v, rfl⟩
    · convert Set.finite_empty
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h, -⟩
      exact hk h
  | .peek _ _ q, k => pushSet_finite q k
  | .pop _ _ q, k => pushSet_finite q k
  | .load _ q, k => pushSet_finite q k
  | .branch _ q₁ q₂, k => (pushSet_finite q₁ k).union (pushSet_finite q₂ k)
  | .goto _, _ => Set.finite_empty
  | .halt, _ => Set.finite_empty

variable (R : ∀ k, Set (Γ k))

/-- A instrução sobre os alfabetos restritos. -/
def tr : (q : TM2.Stmt Γ Λ σ) → (∀ k, pushSet q k ⊆ R k) → TM2.Stmt (fun k => ↥(R k)) Λ σ
  | .push k f q, h => .push k (fun v => ⟨f v, h k (Or.inl ⟨rfl, v, rfl⟩)⟩)
      (tr q fun j => Set.subset_union_right.trans (h j))
  | .peek k f q, h => .peek k (fun v o => f v (o.map Subtype.val)) (tr q h)
  | .pop k f q, h => .pop k (fun v o => f v (o.map Subtype.val)) (tr q h)
  | .load a q, h => .load a (tr q h)
  | .branch f q₁ q₂, h => .branch f (tr q₁ fun j => Set.subset_union_left.trans (h j))
      (tr q₂ fun j => Set.subset_union_right.trans (h j))
  | .goto f, _ => .goto f
  | .halt, _ => .halt

variable {R}

/-- Esquecer a restrição nas pilhas. -/
def valS (S : ∀ k, List ↥(R k)) : ∀ k, List (Γ k) := fun k => (S k).map Subtype.val

/-- Esquecer a restrição numa configuração. -/
def valC (c : TM2.Cfg (fun k => ↥(R k)) Λ σ) : TM2.Cfg Γ Λ σ := ⟨c.l, c.var, valS c.stk⟩

theorem valS_update (S : ∀ k, List ↥(R k)) (k : K) (L : List ↥(R k)) :
    valS (update S k L) = update (valS S) k (L.map Subtype.val) := by
  funext j
  by_cases hj : j = k
  · subst hj; simp [valS]
  · simp [valS, update_of_ne hj]

theorem stepAux_tr : ∀ (q : TM2.Stmt Γ Λ σ) (h : ∀ k, pushSet q k ⊆ R k) (v : σ)
    (S : ∀ k, List ↥(R k)), valC (TM2.stepAux (tr R q h) v S) = TM2.stepAux q v (valS S)
  | .push k f q, h, v, S => by
    simp only [tr, TM2.stepAux]
    rw [stepAux_tr q _ v _, valS_update]
    rfl
  | .peek k f q, h, v, S => by
    simp only [tr, TM2.stepAux]
    rw [stepAux_tr q h _ _]
    simp only [valS, List.head?_map]
  | .pop k f q, h, v, S => by
    simp only [tr, TM2.stepAux]
    rw [stepAux_tr q h _ _, valS_update]
    simp only [valS, List.head?_map, List.map_tail]
  | .load a q, h, v, S => by
    simp only [tr, TM2.stepAux]
    exact stepAux_tr q h _ S
  | .branch f q₁ q₂, h, v, S => by
    simp only [tr, TM2.stepAux]
    cases f v
    · exact stepAux_tr q₂ _ v S
    · exact stepAux_tr q₁ _ v S
  | .goto f, _, v, S => rfl
  | .halt, _, v, S => rfl

variable (M : Λ → TM2.Stmt Γ Λ σ) (hR : ∀ l k, pushSet (M l) k ⊆ R k)

/-- A máquina restrita. -/
def restr : Λ → TM2.Stmt (fun k => ↥(R k)) Λ σ := fun l => tr R (M l) (hR l)

theorem step_restr (c : TM2.Cfg (fun k => ↥(R k)) Λ σ) :
    (TM2.step (restr M hR) c).map valC = TM2.step M (valC c) := by
  obtain ⟨_ | l, v, S⟩ := c
  · rfl
  · simp only [TM2.step, Option.map_some, restr]
    rw [stepAux_tr]
    rfl

theorem passo_restr (c : TM2.Cfg (fun k => ↥(R k)) Λ σ) :
    valC (passo (restr M hR) c) = passo M (valC c) := by
  have h := step_restr M hR c
  simp only [passo]
  cases hs : TM2.step (restr M hR) c with
  | none =>
    rw [hs] at h
    simp only [Option.map_none] at h
    rw [← h]
    rfl
  | some c' =>
    rw [hs] at h
    simp only [Option.map_some] at h
    rw [← h]
    rfl

/-- **A máquina restrita roda como a original.** -/
theorem run_restr (c : TM2.Cfg (fun k => ↥(R k)) Λ σ) :
    ∀ t, valC (run (restr M hR) c t) = run M (valC c) t
  | 0 => rfl
  | t + 1 => by
    rw [run_succ, run_succ, passo_restr, run_restr c t]

end ATK.CookLevinRestricao

#print axioms ATK.CookLevinRestricao.pushSet
#print axioms ATK.CookLevinRestricao.pushSet_finite
#print axioms ATK.CookLevinRestricao.tr
#print axioms ATK.CookLevinRestricao.valS
#print axioms ATK.CookLevinRestricao.valC
#print axioms ATK.CookLevinRestricao.valS_update
#print axioms ATK.CookLevinRestricao.stepAux_tr
#print axioms ATK.CookLevinRestricao.restr
#print axioms ATK.CookLevinRestricao.step_restr
#print axioms ATK.CookLevinRestricao.passo_restr
#print axioms ATK.CookLevinRestricao.run_restr
