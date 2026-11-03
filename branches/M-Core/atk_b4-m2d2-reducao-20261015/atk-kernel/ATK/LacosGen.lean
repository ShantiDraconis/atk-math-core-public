import ATK.LacosLp
import ATK.CookLevinReducao

/-!
# ATK — Ponte B4, marco M2d (parte 2b): geradores de cláusulas

Uma camada entre os programas de laço (`ATK.Lacos.Lp`) e as fórmulas do tableau:

* `Term`: índices (registrador, constante, soma); `VarT`, `LitT`, `ClaT`: variáveis, literais e
  cláusulas do tableau com índices simbólicos;
* `ClaT.cmd`: o programa que emite `codClausula` da cláusula renomeada (`nome`);
* `Gen`: geradores (cláusula, sequência, laço `forU`), com `Gen.cmd` (programa) e `Gen.clas`
  (a lista de cláusulas gerada);
* **`Gen.out`**: a saída do programa é exatamente `codCNF (renomeia (g.clas w E))`;
* `Gen.lp`: o programa é um programa de laço (`Lp`), logo tem custo polinomial.

Nada aqui decide P vs NP. **CLOSED_MATH continua false.**
-/

set_option autoImplicit false

namespace ATK.LacosGen

open ATK.Compilador ATK.Lacos ATK.CookLevinTableau ATK.CookLevinReducao ATK.ModeloPNP Function

variable {R : ℕ}

/-! ### Termos -/

inductive Term (R : ℕ) where
  | reg (r : Fin R)
  | const (c : ℕ)
  | add (a b : Term R)

namespace Term

def eval (E : Env R) : Term R → ℕ
  | reg r => E r
  | const c => c
  | add a b => a.eval E + b.eval E

def reads : Term R → Finset (Fin R)
  | reg r => {r}
  | const _ => ∅
  | add a b => a.reads ∪ b.reads

/-- Emite `s` repetido `eval` vezes. -/
def cmd (s : List Bool) : Term R → Cmd R
  | reg r => .emitU r s
  | const c => .emit (List.replicate c s).flatten
  | add a b => .seq (a.cmd s) (b.cmd s)

theorem env (w : List Bool) (s : List Bool) : ∀ (τ : Term R) (E : Env R),
    (sem w (τ.cmd s) E).1 = E
  | reg _, _ => rfl
  | const _, _ => rfl
  | add a b, E => by simp only [cmd, sem]; rw [env w s a, env w s b]

theorem out (w : List Bool) (s : List Bool) : ∀ (τ : Term R) (E : Env R),
    (sem w (τ.cmd s) E).2 = (List.replicate (τ.eval E) s).flatten
  | reg _, _ => rfl
  | const _, _ => rfl
  | add a b, E => by
    simp only [cmd, sem, eval]
    rw [out w s a, env w s a, out w s b, List.replicate_add, List.flatten_append]

theorem lp {W : Finset (Fin R)} (s : List Bool) : ∀ (τ : Term R), (∀ r ∈ τ.reads, r ∉ W) →
    Lp W (τ.cmd s)
  | reg r, h => Lp.emitU s (h r (by simp [reads]))
  | const _, _ => Lp.emit W _
  | add a b, h => Lp.seq (lp s a fun r hr => h r (by simp [reads, hr]))
    (lp s b fun r hr => h r (by simp [reads, hr]))

theorem eval_congr {W : Finset (Fin R)} : ∀ (τ : Term R), (∀ r ∈ τ.reads, r ∉ W) →
    ∀ {E E' : Env R}, (∀ r, r ∉ W → E r = E' r) → τ.eval E = τ.eval E'
  | reg r, h, E, E', hE => hE r (h r (by simp [reads]))
  | const _, _, _, _, _ => rfl
  | add a b, h, E, E', hE => by
    simp only [eval]
    rw [eval_congr a (fun r hr => h r (by simp [reads, hr])) hE,
      eval_congr b (fun r hr => h r (by simp [reads, hr])) hE]

end Term

/-! ### Variáveis, literais e cláusulas com índices simbólicos -/

variable {K : Type} [Fintype K]

inductive VarT (R : ℕ) (K : Type) where
  | x (t : Term R) (k : K) (i j : Term R)
  | y (t j : Term R)
  | z (t j : Term R)

namespace VarT

def eval (E : Env R) : VarT R K → Var K
  | x t k i j => .x (t.eval E) k (i.eval E) (j.eval E)
  | y t j => .y (t.eval E) (j.eval E)
  | z t j => .z (t.eval E) (j.eval E)

def reads : VarT R K → Finset (Fin R)
  | x t _ i j => t.reads ∪ i.reads ∪ j.reads
  | y t j => t.reads ∪ j.reads
  | z t j => t.reads ∪ j.reads

/-- `unario n` codificado em `simb`: `n` vezes `[false, true]` e depois `[false, false]`. -/
def un (τ : Term R) : Cmd R := .seq (τ.cmd [false, true]) (.emit [false, false])

theorem un_out (w : List Bool) (τ : Term R) (E : Env R) :
    (sem w (un τ) E).2 = (unario (τ.eval E)).flatMap simb := by
  simp only [un, sem, Term.out, unario, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    simb, List.append_nil]
  congr 1
  induction τ.eval E with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih, simb]

theorem un_env (w : List Bool) (τ : Term R) (E : Env R) : (sem w (un τ) E).1 = E := by
  simp only [un, sem, Term.env]

theorem un_lp {W : Finset (Fin R)} {τ : Term R} (h : ∀ r ∈ τ.reads, r ∉ W) : Lp W (un τ) :=
  Lp.seq (Term.lp _ τ h) (Lp.emit W _)

/-- Emite `(cadeia (eval v)).flatMap simb`. -/
noncomputable def cmd : VarT R K → Cmd R
  | x t k i j => .seq (.emit [false, true, false, true]) (.seq (un t)
      (.seq (.emit ((unario (κ k)).flatMap simb)) (.seq (un i) (.seq (un j) (.emit [false, true])))))
  | y t j => .seq (.emit [false, true, false, false]) (.seq (un t) (.seq (un j) (.emit [false, true])))
  | z t j => .seq (.emit [false, false, false, true]) (.seq (un t) (.seq (un j) (.emit [false, true])))

theorem cmd_env (w : List Bool) : ∀ (v : VarT R K) (E : Env R), (sem w v.cmd E).1 = E
  | x _ _ _ _, E => by simp only [cmd, sem, un_env]
  | y _ _, E => by simp only [cmd, sem, un_env]
  | z _ _, E => by simp only [cmd, sem, un_env]

theorem cmd_out (w : List Bool) : ∀ (v : VarT R K) (E : Env R),
    (sem w v.cmd E).2 = (cadeia (v.eval E)).flatMap simb
  | x t k i j, E => by
    simp only [cmd, sem, un_env, un_out, eval, cadeia, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, simb, List.append_assoc, List.cons_append, List.nil_append]
  | y t j, E => by
    simp only [cmd, sem, un_env, un_out, eval, cadeia, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, simb, List.append_assoc, List.cons_append, List.nil_append]
  | z t j, E => by
    simp only [cmd, sem, un_env, un_out, eval, cadeia, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, simb, List.append_assoc, List.cons_append, List.nil_append]

theorem cmd_lp {W : Finset (Fin R)} : ∀ (v : VarT R K), (∀ r ∈ v.reads, r ∉ W) → Lp W v.cmd
  | x t _ i j, h => by
    simp only [reads, Finset.mem_union] at h
    exact Lp.seq (Lp.emit W _) (Lp.seq (un_lp fun r hr => h r (by simp [hr]))
      (Lp.seq (Lp.emit W _) (Lp.seq (un_lp fun r hr => h r (by simp [hr]))
        (Lp.seq (un_lp fun r hr => h r (by simp [hr])) (Lp.emit W _)))))
  | y t j, h => by
    simp only [reads, Finset.mem_union] at h
    exact Lp.seq (Lp.emit W _) (Lp.seq (un_lp fun r hr => h r (by simp [hr]))
      (Lp.seq (un_lp fun r hr => h r (by simp [hr])) (Lp.emit W _)))
  | z t j, h => by
    simp only [reads, Finset.mem_union] at h
    exact Lp.seq (Lp.emit W _) (Lp.seq (un_lp fun r hr => h r (by simp [hr]))
      (Lp.seq (un_lp fun r hr => h r (by simp [hr])) (Lp.emit W _)))

theorem eval_congr {W : Finset (Fin R)} : ∀ (v : VarT R K), (∀ r ∈ v.reads, r ∉ W) →
    ∀ {E E' : Env R}, (∀ r, r ∉ W → E r = E' r) → v.eval E = v.eval E'
  | x t _ i j, h, E, E', hE => by
    simp only [reads, Finset.mem_union] at h
    simp only [eval]
    rw [Term.eval_congr t (fun r hr => h r (by simp [hr])) hE,
      Term.eval_congr i (fun r hr => h r (by simp [hr])) hE,
      Term.eval_congr j (fun r hr => h r (by simp [hr])) hE]
  | y t j, h, E, E', hE => by
    simp only [reads, Finset.mem_union] at h
    simp only [eval]
    rw [Term.eval_congr t (fun r hr => h r (by simp [hr])) hE,
      Term.eval_congr j (fun r hr => h r (by simp [hr])) hE]
  | z t j, h, E, E', hE => by
    simp only [reads, Finset.mem_union] at h
    simp only [eval]
    rw [Term.eval_congr t (fun r hr => h r (by simp [hr])) hE,
      Term.eval_congr j (fun r hr => h r (by simp [hr])) hE]

end VarT

/-- Literal simbólico. -/
abbrev LitT (R : ℕ) (K : Type) := VarT R K × Bool
/-- Cláusula simbólica. -/
abbrev ClaT (R : ℕ) (K : Type) := List (LitT R K)

namespace LitT

def eval (E : Env R) (ℓ : LitT R K) : Lit K := (ℓ.1.eval E, ℓ.2)

noncomputable def cmd (ℓ : LitT R K) : Cmd R :=
  .seq (.emit (simb ℓ.2)) (.seq ℓ.1.cmd (.emit [true, false]))

theorem cmd_env (w : List Bool) (ℓ : LitT R K) (E : Env R) : (sem w ℓ.cmd E).1 = E := by
  simp only [cmd, sem, VarT.cmd_env]

theorem cmd_out (w : List Bool) (ℓ : LitT R K) (E : Env R) :
    (sem w ℓ.cmd E).2 = codLiteral (nome (ℓ.1.eval E), ℓ.2) := by
  simp only [cmd, sem, VarT.cmd_env, VarT.cmd_out, codLiteral, bits_nome, eval, List.append_assoc]

theorem cmd_lp {W : Finset (Fin R)} (ℓ : LitT R K) (h : ∀ r ∈ ℓ.1.reads, r ∉ W) : Lp W ℓ.cmd :=
  Lp.seq (Lp.emit W _) (Lp.seq (VarT.cmd_lp _ h) (Lp.emit W _))

end LitT

/-- Sequência de comandos. -/
def seqC : List (Cmd R) → Cmd R
  | [] => .emit []
  | c :: cs => .seq c (seqC cs)

theorem seqC_lp {W : Finset (Fin R)} : ∀ {cs : List (Cmd R)}, (∀ c ∈ cs, Lp W c) → Lp W (seqC cs)
  | [], _ => Lp.emit W _
  | c :: cs, h => Lp.seq (h c (by simp)) (seqC_lp fun c' hc' => h c' (by simp [hc']))

namespace ClaT

def eval (E : Env R) (C : ClaT R K) : Cla K := C.map (LitT.eval E)

def reads (C : ClaT R K) : Finset (Fin R) := C.foldr (fun ℓ s => ℓ.1.reads ∪ s) ∅

theorem mem_reads {C : ClaT R K} {ℓ : LitT R K} (hℓ : ℓ ∈ C) : ℓ.1.reads ⊆ C.reads := by
  induction C with
  | nil => simp at hℓ
  | cons ℓ' C ih =>
    simp only [reads, List.foldr_cons]
    rcases List.mem_cons.mp hℓ with rfl | h
    · exact Finset.subset_union_left
    · exact (ih h).trans Finset.subset_union_right

noncomputable def cmd (C : ClaT R K) : Cmd R :=
  .seq (seqC (C.map LitT.cmd)) (.emit [true, true])

theorem seq_env (w : List Bool) : ∀ (C : ClaT R K) (E : Env R),
    (sem w (seqC (C.map LitT.cmd)) E).1 = E
  | [], E => rfl
  | ℓ :: C, E => by simp only [List.map_cons, seqC, sem, LitT.cmd_env]; exact seq_env w C E

theorem seq_out (w : List Bool) : ∀ (C : ClaT R K) (E : Env R),
    (sem w (seqC (C.map LitT.cmd)) E).2 =
      ((C.eval E).map fun ℓ => (nome ℓ.1, ℓ.2)).flatMap codLiteral
  | [], E => by simp [seqC, sem, eval]
  | ℓ :: C, E => by
    simp only [List.map_cons, seqC, sem, LitT.cmd_env, LitT.cmd_out, eval, List.flatMap_cons]
    rw [seq_out w C E]
    rfl

theorem cmd_env (w : List Bool) (C : ClaT R K) (E : Env R) : (sem w C.cmd E).1 = E := by
  simp only [cmd, sem, seq_env]

/-- **Uma cláusula**: o programa emite `codCNF (renomeia [C.eval E])`. -/
theorem cmd_out (w : List Bool) (C : ClaT R K) (E : Env R) :
    (sem w C.cmd E).2 = codCNF (renomeia [C.eval E]) := by
  simp only [cmd, sem, seq_env, seq_out, codCNF, renomeia, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, codClausula, List.append_nil]

theorem cmd_lp {W : Finset (Fin R)} (C : ClaT R K) (h : ∀ r ∈ C.reads, r ∉ W) : Lp W C.cmd :=
  Lp.seq (seqC_lp fun c hc => by
    obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hc
    exact LitT.cmd_lp ℓ fun r hr => h r (mem_reads hℓ hr)) (Lp.emit W _)

theorem eval_congr {W : Finset (Fin R)} (C : ClaT R K) (h : ∀ r ∈ C.reads, r ∉ W)
    {E E' : Env R} (hE : ∀ r, r ∉ W → E r = E' r) : C.eval E = C.eval E' := by
  simp only [eval]
  refine List.map_congr_left fun ℓ hℓ => ?_
  simp only [LitT.eval]
  rw [VarT.eval_congr ℓ.1 (fun r hr => h r (mem_reads hℓ hr)) hE]

end ClaT

/-! ### Geradores -/

/-- As cláusulas de um laço sobre os bits `L`: o corpo `f₀`/`f₁` com o contador `c` valendo a
posição (o ambiente é atualizado com `c + 1` a cada bit). -/
def clasBitsAux {R : ℕ} {α : Type} (f₀ f₁ : Env R → List α) (c : Fin R) :
    List Bool → Env R → List α
  | [], _ => []
  | b :: L, E => (if b then f₁ E else f₀ E) ++ clasBitsAux f₀ f₁ c L (update E c (E c + 1))

theorem clasBitsAux_congr {R : ℕ} {α : Type} (f₀ f₁ : Env R → List α) (c : Fin R)
    (S : Finset (Fin R)) (hcS : c ∉ S)
    (h₀ : ∀ E E' : Env R, (∀ r, r ∉ S → E r = E' r) → f₀ E = f₀ E')
    (h₁ : ∀ E E' : Env R, (∀ r, r ∉ S → E r = E' r) → f₁ E = f₁ E') :
    ∀ (L : List Bool) (E E' : Env R), (∀ r, r ∉ S → E r = E' r) →
      clasBitsAux f₀ f₁ c L E = clasBitsAux f₀ f₁ c L E'
  | [], _, _, _ => rfl
  | b :: L, E, E', hE => by
    simp only [clasBitsAux]
    have hc : E c = E' c := hE c hcS
    have hb : (if b then f₁ E else f₀ E) = (if b then f₁ E' else f₀ E') := by
      cases b
      · exact h₀ E E' hE
      · exact h₁ E E' hE
    rw [hb]
    congr 1
    refine clasBitsAux_congr f₀ f₁ c S hcS h₀ h₁ L _ _ fun r hr => ?_
    by_cases hrc : r = c
    · subst hrc; simp [hc]
    · rw [update_of_ne hrc, update_of_ne hrc]; exact hE r hr

inductive Gen (R : ℕ) (K : Type) where
  | cla (C : ClaT R K)
  | nil
  | seq (g₁ g₂ : Gen R K)
  | forU (x y : Fin R) (g : Gen R K)
  /-- Laço sobre os bits da entrada, com contador de posição `c`. -/
  | bits (c : Fin R) (g₀ g₁ : Gen R K)

namespace Gen

noncomputable def cmd : Gen R K → Cmd R
  | cla C => C.cmd
  | nil => .emit []
  | seq g₁ g₂ => .seq g₁.cmd g₂.cmd
  | forU x y g => .forU x y g.cmd
  | bits c g₀ g₁ => .seq (.zero c) (.forBits (.seq g₀.cmd (.inc c)) (.seq g₁.cmd (.inc c)))

/-- As cláusulas geradas, com o ambiente `E`. -/
def clas (w : List Bool) (E : Env R) : Gen R K → List (Cla K)
  | cla C => [C.eval E]
  | nil => []
  | seq g₁ g₂ => g₁.clas w E ++ g₂.clas w E
  | forU x y g => (List.range (E x)).flatMap fun k => g.clas w (update E y k)
  | bits c g₀ g₁ => clasBitsAux (g₀.clas w) (g₁.clas w) c w (update E c 0)

/-- Boa formação relativa ao conjunto `W` dos contadores escritos. -/
def ok (W : Finset (Fin R)) : Gen R K → Prop
  | cla C => ∀ r ∈ C.reads, r ∉ W
  | nil => True
  | seq g₁ g₂ => g₁.ok W ∧ g₂.ok W
  | forU x y g => x ∉ W ∧ y ∈ W ∧ g.ok (W.erase y)
  | bits c g₀ g₁ => c ∈ W ∧ g₀.ok (W.erase c) ∧ g₁.ok (W.erase c)

theorem lp {W : Finset (Fin R)} : ∀ (g : Gen R K), g.ok W → Lp W g.cmd
  | cla C, h => ClaT.cmd_lp C h
  | nil, _ => Lp.emit W _
  | seq g₁ g₂, h => Lp.seq (lp g₁ h.1) (lp g₂ h.2)
  | forU x y g, h => Lp.forU h.1 h.2.1 (lp g h.2.2)
  | bits c g₀ g₁, h => Lp.bitsC h.1 (lp g₀ h.2.1) (lp g₁ h.2.2)

theorem clas_congr (w : List Bool) {W : Finset (Fin R)} : ∀ (g : Gen R K), g.ok W → ∀ {E E' : Env R},
    (∀ r, r ∉ W → E r = E' r) → g.clas w E = g.clas w E'
  | cla C, h, E, E', hE => by simp only [clas]; rw [ClaT.eval_congr C h hE]
  | nil, _, _, _, _ => rfl
  | seq g₁ g₂, h, E, E', hE => by
    simp only [clas]
    rw [clas_congr w g₁ h.1 hE, clas_congr w g₂ h.2 hE]
  | forU x y g, h, E, E', hE => by
    simp only [clas]
    rw [hE x h.1]
    refine List.flatMap_congr fun k _ => clas_congr w g h.2.2 fun r hr => ?_
    by_cases hry : r = y
    · subst hry; simp
    · rw [update_of_ne hry, update_of_ne hry]
      exact hE r fun h' => hr (Finset.mem_erase.mpr ⟨hry, h'⟩)
  | bits c g₀ g₁, h, E, E', hE => by
    simp only [clas]
    refine clasBitsAux_congr _ _ c (W.erase c) (by simp)
      (fun E E' hh => clas_congr w g₀ h.2.1 hh) (fun E E' hh => clas_congr w g₁ h.2.2 hh) w _ _
      fun r hr => ?_
    by_cases hrc : r = c
    · subst hrc; simp
    · rw [update_of_ne hrc, update_of_ne hrc]
      exact hE r fun h' => hr (Finset.mem_erase.mpr ⟨hrc, h'⟩)

/-- **A saída de um gerador** é `codCNF (renomeia (g.clas w E))`. -/
theorem out (w : List Bool) {W : Finset (Fin R)} : ∀ (g : Gen R K), g.ok W → ∀ (E : Env R),
    (sem w g.cmd E).2 = codCNF (renomeia (g.clas w E))
  | cla C, _, E => ClaT.cmd_out w C E
  | nil, _, _ => by simp [cmd, sem, clas, codCNF, renomeia]
  | seq g₁ g₂, h, E => by
    simp only [cmd, clas]
    rw [Lp.out_seq w (lp g₁ h.1) (lp g₂ h.2), out w g₁ h.1, out w g₂ h.2]
    simp only [renomeia, codCNF, List.map_append, List.flatMap_append]
  | forU x y g, h, E => by
    simp only [cmd, clas]
    rw [Lp.out_forU w h.2.1 (lp g h.2.2)]
    simp only [renomeia, codCNF, List.map_flatMap, List.flatMap_assoc]
    refine List.flatMap_congr fun k _ => ?_
    rw [out w g h.2.2]
    rfl
  | bits c g₀ g₁, h, E => by
    simp only [cmd, clas]
    have hcS : c ∉ W.erase c := by simp
    have step₀ : ∀ E' : Env R, sem w (.seq g₀.cmd (.inc c)) E' =
        (update (sem w g₀.cmd E').1 c (E' c + 1), codCNF (renomeia (g₀.clas w E'))) := fun E' => by
      rw [Lacos.sem_body w (W.erase c) c hcS (fun E r hr => (lp g₀ h.2.1).env w E hr) E',
        out w g₀ h.2.1 E']
    have step₁ : ∀ E' : Env R, sem w (.seq g₁.cmd (.inc c)) E' =
        (update (sem w g₁.cmd E').1 c (E' c + 1), codCNF (renomeia (g₁.clas w E'))) := fun E' => by
      rw [Lacos.sem_body w (W.erase c) c hcS (fun E r hr => (lp g₁ h.2.2).env w E hr) E',
        out w g₁ h.2.2 E']
    have key : ∀ (L : List Bool) (E' : Env R),
        (semBits (sem w (.seq g₀.cmd (.inc c))) (sem w (.seq g₁.cmd (.inc c))) L E').2 =
          codCNF (renomeia (clasBitsAux (g₀.clas w) (g₁.clas w) c L E')) := by
      intro L
      induction L with
      | nil => intro E'; simp [semBits, clasBitsAux, codCNF, renomeia]
      | cons b L ih =>
        intro E'
        have hag₀ : clasBitsAux (g₀.clas w) (g₁.clas w) c L (update (sem w g₀.cmd E').1 c (E' c + 1)) =
            clasBitsAux (g₀.clas w) (g₁.clas w) c L (update E' c (E' c + 1)) := by
          refine clasBitsAux_congr _ _ c (W.erase c) hcS
            (fun E E' hh => clas_congr w g₀ h.2.1 hh) (fun E E' hh => clas_congr w g₁ h.2.2 hh) L _ _
            fun r hr => ?_
          by_cases hrc : r = c
          · subst hrc; simp
          · rw [update_of_ne hrc, update_of_ne hrc]
            exact (lp g₀ h.2.1).env w E' fun h' => hr h'
        have hag₁ : clasBitsAux (g₀.clas w) (g₁.clas w) c L (update (sem w g₁.cmd E').1 c (E' c + 1)) =
            clasBitsAux (g₀.clas w) (g₁.clas w) c L (update E' c (E' c + 1)) := by
          refine clasBitsAux_congr _ _ c (W.erase c) hcS
            (fun E E' hh => clas_congr w g₀ h.2.1 hh) (fun E E' hh => clas_congr w g₁ h.2.2 hh) L _ _
            fun r hr => ?_
          by_cases hrc : r = c
          · subst hrc; simp
          · rw [update_of_ne hrc, update_of_ne hrc]
            exact (lp g₁ h.2.2).env w E' fun h' => hr h'
        cases b
        · simp only [semBits, clasBitsAux, Bool.false_eq_true, ↓reduceIte]
          rw [step₀ E']
          dsimp only
          rw [ih, hag₀]
          simp only [renomeia, codCNF, List.map_append, List.flatMap_append]
        · simp only [semBits, clasBitsAux, ↓reduceIte]
          rw [step₁ E']
          dsimp only
          rw [ih, hag₁]
          simp only [renomeia, codCNF, List.map_append, List.flatMap_append]
    exact key w (update E c 0)

/-- Sequência de geradores. -/
def seqL : List (Gen R K) → Gen R K
  | [] => nil
  | g :: gs => seq g (seqL gs)

theorem clas_seqL (w : List Bool) (E : Env R) : ∀ (gs : List (Gen R K)),
    (seqL gs).clas w E = gs.flatMap (clas w E ·)
  | [] => rfl
  | g :: gs => by simp only [seqL, clas, List.flatMap_cons]; rw [clas_seqL w E gs]

theorem ok_seqL {W : Finset (Fin R)} : ∀ (gs : List (Gen R K)), (∀ g ∈ gs, g.ok W) →
    (seqL gs).ok W
  | [], _ => trivial
  | g :: gs, h => ⟨h g (by simp), ok_seqL gs fun g' hg' => h g' (by simp [hg'])⟩

/-- Lista de cláusulas simbólicas. -/
def clasL (Cs : List (ClaT R K)) : Gen R K := seqL (Cs.map cla)

theorem clas_clasL (w : List Bool) (E : Env R) (Cs : List (ClaT R K)) :
    (clasL Cs).clas w E = Cs.map (ClaT.eval E) := by
  simp only [clasL, clas_seqL, List.flatMap_map, clas]
  induction Cs with
  | nil => rfl
  | cons C Cs ih => simp [List.flatMap_cons, ih]

theorem ok_clasL {W : Finset (Fin R)} (Cs : List (ClaT R K)) (h : ∀ C ∈ Cs, ∀ r ∈ C.reads, r ∉ W) :
    (clasL Cs).ok W :=
  ok_seqL _ fun g hg => by
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hg
    exact h C hC

end Gen

end ATK.LacosGen
