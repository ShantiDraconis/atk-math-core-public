import ATK.LacosGen

/-!
# ATK — Ponte B4, marco M2d (parte 2c): o tableau como gerador de cláusulas

Para um tableau `A : Tab K Γ Λ σ`, geradores (`ATK.LacosGen.Gen`) cujas cláusulas são
**exatamente** as famílias (E), (R), (P), (A) e as partes de (I) do tableau, quando os
registradores guardam `T`, `T + 1`, `H`, `H − c` (`c ≤ c₀`), `P`, `Q`, `H − P − Q`.

Nada aqui decide P vs NP. **CLOSED_MATH continua false.**
-/

set_option autoImplicit false

namespace ATK.CookLevinGen

open ATK.Compilador ATK.Lacos ATK.LacosGen ATK.CookLevinTableau ATK.CookLevinReducao
  ATK.CookLevinBase Turing Turing.TM2 Function

/-! ### Lemas de listas -/

theorem range_filter_lt (m : ℕ) : ∀ n, m ≤ n →
    (List.range n).filter (fun j => decide (j < m)) = List.range m
  | 0, h => by
    have : m = 0 := by omega
    subst this; rfl
  | n + 1, h => by
    rw [List.range_succ, List.filter_append]
    rcases Nat.lt_or_ge n m with h1 | h1
    · have hm : m = n + 1 := by omega
      subst hm
      rw [List.filter_eq_self.mpr (fun j hj => by simp at hj ⊢; omega)]
      simp [List.range_succ]
    · rw [range_filter_lt m n h1]
      simp [h1]

theorem range_filter_add_lt (c : ℕ) {H : ℕ} (hc : c ≤ H) :
    (List.range H).filter (fun j => decide (c + j < H)) = List.range (H - c) := by
  rw [← range_filter_lt (H - c) H (Nat.sub_le _ _)]
  refine List.filter_congr fun j _ => ?_
  simp only [decide_eq_decide]
  omega

theorem noMaximo_range {K : Type} (g : ℕ → Var K) : ∀ L : ℕ,
    noMaximo ((List.range L).map g) =
      (List.range L).flatMap fun a =>
        ((List.range L).filter (fun b => decide (a < b))).map fun b => [(g a, false), (g b, false)]
  | 0 => rfl
  | L + 1 => by
    have ih := noMaximo_range (g ∘ Nat.succ) L
    rw [List.range_succ_eq_map, List.map_cons, noMaximo]
    simp only [List.map_map]
    rw [ih, List.flatMap_cons, List.flatMap_map]
    congr 1
    · simp [List.filter_cons, List.filter_map, Function.comp_def]
    · refine List.flatMap_congr fun a _ => ?_
      simp [List.filter_cons, List.filter_map, Function.comp_def, Nat.succ_lt_succ_iff]

theorem flatMap_triples {α β γ δ : Type} (la : List α) (lb : List β) (lc : List γ)
    (F : α → β → γ → List δ) :
    (la.flatMap fun a => lb.flatMap fun b => lc.flatMap fun c => F a b c) =
      (la.flatMap fun a => lb.flatMap fun b => lc.map fun c => (a, b, c)).flatMap
        fun q => F q.1 q.2.1 q.2.2 := by
  simp only [List.flatMap_assoc, List.flatMap_map]

/-! ### O gerador "exatamente um" -/

section tab

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} {Λ σ : Type} (A : Tab K Γ Λ σ)
  {R : ℕ} {w : List Bool}

/-- `umSo` das variáveis `v 0, …, v (L-1)`. -/
def umSoG (L : ℕ) (v : ℕ → VarT R K) : Gen R K :=
  Gen.clasL (((List.range L).map fun j => (v j, true)) ::
    ((List.range L).flatMap fun a =>
      ((List.range L).filter (fun b => decide (a < b))).map fun b => [(v a, false), (v b, false)]))

theorem clas_umSoG (L : ℕ) (v : ℕ → VarT R K) (E : Env R) :
    (umSoG L v).clas w E = umSo ((List.range L).map fun j => (v j).eval E) := by
  rw [umSoG, Gen.clas_clasL, umSo, noMaximo_range]
  simp only [List.map_cons, ClaT.eval, List.map_map, List.map_flatMap, peloMenos]
  rfl

/-! ### (E) -/

/-- Registradores usados pelos geradores do tableau. -/
structure Regs (R : ℕ) where
  T : Fin R
  T1 : Fin R
  P : Fin R
  Q : Fin R
  H2 : Fin R
  hb : ℕ → Fin R
  rt : Fin R
  ri : Fin R
  rj : Fin R

variable (ρ : Regs R)

/-- `Var.x` com tempo `t` (termo), pilha `k`, célula `i` (termo) e valor `j` (termo). -/
abbrev vx (t : Term R) (k : K) (i j : Term R) : VarT R K := .x t k i j

noncomputable def genE (c₀ : ℕ) : Gen R K :=
  .forU ρ.T1 ρ.rt (Gen.seqL
    ([umSoG A.labs.length fun j => .y (.reg ρ.rt) (.const j),
      umSoG A.sts.length fun j => .z (.reg ρ.rt) (.const j)] ++
     (Tab.ks (K := K)).map fun k =>
      .forU (ρ.hb c₀) ρ.ri (umSoG (A.vals k).length fun j => vx (.reg ρ.rt) k (.reg ρ.ri) (.const j))))

/-- Hipóteses sobre o ambiente: os registradores de parâmetros guardam `T`, `T+1`, `H − c`, …
e os contadores são distintos de tudo. -/
structure Vals (E : Env R) (c₀ T H P Q : ℕ) : Prop where
  hT : E ρ.T = T
  hT1 : E ρ.T1 = T + 1
  hP : E ρ.P = P
  hQ : E ρ.Q = Q
  hH2 : E ρ.H2 = H - P - Q
  hhb : ∀ c, c ≤ c₀ → E (ρ.hb c) = H - c₀ + c
  hH : c₀ ≤ H
  hPQ : P + Q ≤ H - c₀

/-- Os contadores são distintos dos parâmetros e entre si. -/
structure Dist (c₀ : ℕ) : Prop where
  tT : ρ.rt ≠ ρ.T
  tT1 : ρ.rt ≠ ρ.T1
  tP : ρ.rt ≠ ρ.P
  tQ : ρ.rt ≠ ρ.Q
  tH2 : ρ.rt ≠ ρ.H2
  thb : ∀ c, c ≤ c₀ → ρ.rt ≠ ρ.hb c
  iT : ρ.ri ≠ ρ.T
  iT1 : ρ.ri ≠ ρ.T1
  iP : ρ.ri ≠ ρ.P
  iQ : ρ.ri ≠ ρ.Q
  iH2 : ρ.ri ≠ ρ.H2
  ihb : ∀ c, c ≤ c₀ → ρ.ri ≠ ρ.hb c
  jT : ρ.rj ≠ ρ.T
  jT1 : ρ.rj ≠ ρ.T1
  jP : ρ.rj ≠ ρ.P
  jQ : ρ.rj ≠ ρ.Q
  jH2 : ρ.rj ≠ ρ.H2
  jhb : ∀ c, c ≤ c₀ → ρ.rj ≠ ρ.hb c
  ti : ρ.rt ≠ ρ.ri
  tj : ρ.rt ≠ ρ.rj
  ij : ρ.ri ≠ ρ.rj

variable {ρ}

theorem Vals.update_t {E : Env R} {c₀ T H P Q : ℕ} (h : Vals ρ E c₀ T H P Q) (hd : Dist ρ c₀)
    (t : ℕ) : Vals ρ (update E ρ.rt t) c₀ T H P Q where
  hT := by rw [update_of_ne hd.tT.symm, h.hT]
  hT1 := by rw [update_of_ne hd.tT1.symm, h.hT1]
  hP := by rw [update_of_ne hd.tP.symm, h.hP]
  hQ := by rw [update_of_ne hd.tQ.symm, h.hQ]
  hH2 := by rw [update_of_ne hd.tH2.symm, h.hH2]
  hhb := fun c hc => by rw [update_of_ne (hd.thb c hc).symm, h.hhb c hc]
  hH := h.hH
  hPQ := h.hPQ

theorem Vals.update_i {E : Env R} {c₀ T H P Q : ℕ} (h : Vals ρ E c₀ T H P Q) (hd : Dist ρ c₀)
    (i : ℕ) : Vals ρ (update E ρ.ri i) c₀ T H P Q where
  hT := by rw [update_of_ne hd.iT.symm, h.hT]
  hT1 := by rw [update_of_ne hd.iT1.symm, h.hT1]
  hP := by rw [update_of_ne hd.iP.symm, h.hP]
  hQ := by rw [update_of_ne hd.iQ.symm, h.hQ]
  hH2 := by rw [update_of_ne hd.iH2.symm, h.hH2]
  hhb := fun c hc => by rw [update_of_ne (hd.ihb c hc).symm, h.hhb c hc]
  hH := h.hH
  hPQ := h.hPQ

theorem Vals.update_j {E : Env R} {c₀ T H P Q : ℕ} (h : Vals ρ E c₀ T H P Q) (hd : Dist ρ c₀)
    (j : ℕ) : Vals ρ (update E ρ.rj j) c₀ T H P Q where
  hT := by rw [update_of_ne hd.jT.symm, h.hT]
  hT1 := by rw [update_of_ne hd.jT1.symm, h.hT1]
  hP := by rw [update_of_ne hd.jP.symm, h.hP]
  hQ := by rw [update_of_ne hd.jQ.symm, h.hQ]
  hH2 := by rw [update_of_ne hd.jH2.symm, h.hH2]
  hhb := fun c hc => by rw [update_of_ne (hd.jhb c hc).symm, h.hhb c hc]
  hH := h.hH
  hPQ := h.hPQ

theorem Vals.H {E : Env R} {c₀ T H P Q : ℕ} (h : Vals ρ E c₀ T H P Q) : E (ρ.hb c₀) = H := by
  rw [h.hhb c₀ le_rfl]
  have := h.hH
  omega

/-- **(E)**: o gerador produz exatamente `A.fE T H`. -/
theorem clas_genE {E : Env R} {c₀ T H P Q : ℕ} (h : Vals ρ E c₀ T H P Q) (hd : Dist ρ c₀) :
    (genE A ρ c₀).clas w E = A.fE T H := by
  simp only [genE, Gen.clas, Tab.fE, h.hT1]
  refine List.flatMap_congr fun t _ => ?_
  rw [Gen.clas_seqL]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_map,
    List.flatMap_append, List.map_cons, List.map_nil, List.append_assoc]
  have hv := h.update_t hd t
  congr 1
  · rw [clas_umSoG]
    simp only [Tab.rotulos, VarT.eval, Term.eval, update_self]
  congr 1
  · rw [clas_umSoG]
    simp only [Tab.estados, VarT.eval, Term.eval, update_self]
  refine List.flatMap_congr fun k _ => ?_
  simp only [Gen.clas, hv.H]
  refine List.flatMap_congr fun i _ => ?_
  rw [clas_umSoG]
  simp only [Tab.celulas, VarT.eval, Term.eval, update_self, update_of_ne hd.ti]

/-! ### (P) e (A) -/

/-- O índice do rótulo `none` (parada). -/
noncomputable def jn : ℕ := ix A.labs none

variable (ρ) in
noncomputable def genP (c₀ : ℕ) : Gen R K :=
  .forU ρ.T ρ.rt (Gen.seqL
    ([Gen.cla [(.y (.reg ρ.rt) (.const (jn A)), false),
        (.y (.add (.reg ρ.rt) (.const 1)) (.const (jn A)), true)],
      Gen.clasL ((List.range A.sts.length).map fun jv =>
        [(.y (.reg ρ.rt) (.const (jn A)), false), (.z (.reg ρ.rt) (.const jv), false),
          (.z (.add (.reg ρ.rt) (.const 1)) (.const jv), true)])] ++
     (Tab.ks (K := K)).map fun k =>
      .forU (ρ.hb c₀) ρ.ri (Gen.clasL ((List.range (A.vals k).length).map fun a =>
        [(.y (.reg ρ.rt) (.const (jn A)), false),
          (vx (.reg ρ.rt) k (.reg ρ.ri) (.const a), false),
          (vx (.add (.reg ρ.rt) (.const 1)) k (.reg ρ.ri) (.const a), true)]))))

theorem clas_genP {E : Env R} {c₀ T H P Q : ℕ} (h : Vals ρ E c₀ T H P Q) (hd : Dist ρ c₀) :
    (genP A ρ c₀).clas w E = A.fP T H := by
  simp only [genP, Gen.clas, Tab.fP, h.hT]
  refine List.flatMap_congr fun t _ => ?_
  rw [Gen.clas_seqL]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.flatMap_map,
    List.flatMap_append, List.append_assoc, Gen.clas, Gen.clas_clasL, ClaT.eval, List.map_cons,
    List.map_nil, LitT.eval, VarT.eval, Term.eval, update_self, List.map_map, jn]
  have hv := h.update_t hd t
  congr 1
  congr 1
  · refine List.map_congr_left fun jv _ => ?_
    simp [ClaT.eval, LitT.eval, VarT.eval, Term.eval]
  refine List.flatMap_congr fun k _ => ?_
  simp only [Gen.clas, hv.H, Gen.clas_clasL, List.map_map]
  refine List.flatMap_congr fun i _ => List.map_congr_left fun a _ => ?_
  simp [ClaT.eval, LitT.eval, VarT.eval, Term.eval, update_of_ne hd.ti]

variable (ρ) in
noncomputable def genA (acc : Γ A.k₁) : Gen R K :=
  Gen.clasL [[(.y (.reg ρ.T) (.const (jn A)), true)],
    [(vx (.reg ρ.T) A.k₁ (.const 0) (.const (ix (A.vals A.k₁) (some acc))), true)]]

theorem clas_genA {E : Env R} {c₀ T H P Q : ℕ} (h : Vals ρ E c₀ T H P Q) (acc : Γ A.k₁) :
    (genA A ρ acc).clas w E = A.fA T acc := by
  simp only [genA, Gen.clas_clasL, Tab.fA, ClaT.eval, List.map_cons, List.map_nil, LitT.eval,
    VarT.eval, Term.eval, h.hT, jn]


/-! ### (R): antecedentes e consequentes -/

variable (ρ) in
/-- Os antecedentes, com o tempo no registrador `rt`. -/
noncomputable def antesT (jl jv : ℕ) (p : A.Pat) : ClaT R K :=
  (.y (.reg ρ.rt) (.const jl), false) :: (.z (.reg ρ.rt) (.const jv), false) ::
    (Tab.ks (K := K)).flatMap fun k => (List.finRange A.d).map fun i =>
      (vx (.reg ρ.rt) k (.const i.val) (.const (p k i).val), false)

theorem eval_antesT (jl jv : ℕ) (p : A.Pat) {E : Env R} {t : ℕ} (ht : E ρ.rt = t) :
    (antesT A ρ jl jv p).eval E = A.antes t jl jv p := by
  simp only [antesT, ClaT.eval, Tab.antes, List.map_cons, List.map_flatMap, List.map_map,
    LitT.eval, VarT.eval, Term.eval, ht, Function.comp_def]

/-- O índice de `none` na pilha `k`. -/
noncomputable def jnone (k : K) : ℕ := ix (A.vals k) none

variable (ρ) in
/-- Os consequentes de uma linha `r`, cada cláusula prefixada por `pre`. -/
noncomputable def conseqG (c₀ : ℕ) (pre : ClaT R K) (r : Cfg Γ Λ σ) : Gen R K :=
  Gen.seq (Gen.clasL [pre ++ [(.y (.add (.reg ρ.rt) (.const 1)) (.const (ix A.labs r.l)), true)],
      pre ++ [(.z (.add (.reg ρ.rt) (.const 1)) (.const (ix A.sts r.var)), true)]])
    (Gen.seqL ((Tab.ks (K := K)).map fun k =>
      Gen.seq (Gen.clasL ((List.range (r.stk k).length).map fun i =>
          pre ++ [(vx (.add (.reg ρ.rt) (.const 1)) k (.const i)
            (.const (ix (A.vals k) (r.stk k)[i]?)), true)]))
        (if A.d ≤ (r.stk k).length then
          Gen.forU (ρ.hb (c₀ - (r.stk k).length)) ρ.rj (Gen.clasL
            ((List.range (A.vals k).length).map fun a =>
              pre ++ [(vx (.reg ρ.rt) k (.add (.const A.d) (.reg ρ.rj)) (.const a), false),
                (vx (.add (.reg ρ.rt) (.const 1)) k (.add (.const (r.stk k).length) (.reg ρ.rj))
                  (.const a), true)]))
        else
          Gen.seq (Gen.forU (ρ.hb (c₀ - A.d)) ρ.rj (Gen.clasL
            ((List.range (A.vals k).length).map fun a =>
              pre ++ [(vx (.reg ρ.rt) k (.add (.const A.d) (.reg ρ.rj)) (.const a), false),
                (vx (.add (.reg ρ.rt) (.const 1)) k (.add (.const (r.stk k).length) (.reg ρ.rj))
                  (.const a), true)])))
          (Gen.clasL ((List.range (A.d - (r.stk k).length)).map fun j' =>
            pre ++ [(vx (.add (.reg ρ.rt) (.const 1)) k
              (.add (.reg (ρ.hb (c₀ - A.d))) (.const ((r.stk k).length + j'))) (.const (jnone A k)),
              true)])))))

theorem eval_append_single {E : Env R} (pre : ClaT R K) (ℓ : LitT R K) :
    ClaT.eval E (pre ++ [ℓ]) = pre.eval E ++ [ℓ.eval E] := by
  simp [ClaT.eval]

theorem eval_append {E : Env R} (pre l : ClaT R K) :
    ClaT.eval E (pre ++ l) = pre.eval E ++ l.eval E := by
  simp [ClaT.eval]

/-- **Consequentes**: `conseqG` gera exatamente `(A.conseq H t r).map (preC ++ ·)`. -/
theorem clas_conseqG {E : Env R} {c₀ T H P Q : ℕ} (h : Vals ρ E c₀ T H P Q) (hd : Dist ρ c₀)
    (hdc : A.d ≤ c₀) {t : ℕ} (ht : E ρ.rt = t) (pre : ClaT R K) (hpre : ∀ r ∈ pre.reads, r ≠ ρ.rj)
    (r : Cfg Γ Λ σ) (hlen : ∀ k, (r.stk k).length ≤ c₀) :
    (conseqG A ρ c₀ pre r).clas w E = (A.conseq H t r).map (pre.eval E ++ ·) := by
  have hpreE : ∀ j, pre.eval (update E ρ.rj j) = pre.eval E := fun j =>
    ClaT.eval_congr (W := {ρ.rj}) pre (fun r hr => by simpa using hpre r hr)
      (fun r hr => update_of_ne (by simpa using hr) j E)
  simp only [conseqG, Gen.clas, Tab.conseq, List.map_cons, List.map_append, List.map_flatMap,
    Gen.clas_seqL, List.flatMap_map, Gen.clas_clasL, eval_append_single, LitT.eval, VarT.eval,
    Term.eval, ht, List.map_nil, List.map_map, List.cons_append, List.nil_append]
  congr 1
  congr 1
  refine List.flatMap_congr fun k _ => ?_
  congr 1
  · refine List.map_congr_left fun i _ => ?_
    simp [eval_append_single, LitT.eval, VarT.eval, Term.eval, ht]
  rw [range_filter_add_lt _ ((hlen k).trans h.hH)]
  split_ifs with hdl
  · simp only [Gen.clas, h.hhb _ (Nat.sub_le _ _), Gen.clas_clasL, List.map_map, List.map_flatMap]
    have e1 : H - c₀ + (c₀ - (r.stk k).length) = H - (r.stk k).length := by
      have := hlen k; have := h.hH; omega
    rw [e1]
    refine List.flatMap_congr fun j hj => ?_
    have hj' : j < H - (r.stk k).length := List.mem_range.mp hj
    rw [if_pos (by omega), List.map_map]
    refine List.map_congr_left fun a _ => ?_
    simp only [Function.comp_apply, eval_append, hpreE]
    simp [ClaT.eval, LitT.eval, VarT.eval, Term.eval, ht, update_of_ne hd.tj]
  · simp only [Gen.clas, h.hhb _ (Nat.sub_le _ _), Gen.clas_clasL, List.map_map, List.map_flatMap]
    have e1 : H - c₀ + (c₀ - A.d) = H - A.d := by have := h.hH; omega
    have e2 : H - (r.stk k).length = (H - A.d) + (A.d - (r.stk k).length) := by
      have := h.hH; omega
    rw [e1, e2, List.range_add, List.flatMap_append, List.flatMap_map]
    congr 1
    · refine List.flatMap_congr fun j hj => ?_
      have hj' : j < H - A.d := List.mem_range.mp hj
      rw [if_pos (by omega), List.map_map]
      refine List.map_congr_left fun a _ => ?_
      simp only [Function.comp_apply, eval_append, hpreE]
      simp [ClaT.eval, LitT.eval, VarT.eval, Term.eval, ht, update_of_ne hd.tj]
    · rw [← List.flatMap_singleton' (List.map _ _), List.flatMap_map]
      refine List.flatMap_congr fun j' _ => ?_
      rw [if_neg (by omega)]
      simp [eval_append_single, LitT.eval, VarT.eval, Term.eval, ht, h.hhb _ (Nat.sub_le _ _), e1,
        jnone, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]


/-- Os triplos `(jl, jv, p)`. -/
noncomputable def triplos : List (ℕ × ℕ × A.Pat) :=
  (List.range A.labs.length).flatMap fun jl => (List.range A.sts.length).flatMap fun jv =>
    A.pats.map fun p => (jl, jv, p)

variable (ρ) in
/-- Um triplo `(jl, jv, p)`: as transições a partir do rótulo `jl`, estado `jv`, padrão `p`. -/
noncomputable def triploG (c₀ : ℕ) (q : ℕ × ℕ × A.Pat) : Gen R K :=
  match A.labs[q.1]?, A.sts[q.2.1]? with
  | some (some l), some v =>
      conseqG A ρ c₀ (antesT A ρ q.1 q.2.1 q.2.2) (stepAux (A.M l) v (A.janela q.2.2))
  | _, _ => Gen.nil

variable (ρ) in
noncomputable def genR (c₀ : ℕ) : Gen R K :=
  .forU ρ.T ρ.rt (Gen.seqL ((triplos A).map (triploG A ρ c₀)))

theorem reads_subset {C : ClaT R K} {S : Finset (Fin R)} (h : ∀ ℓ ∈ C, ℓ.1.reads ⊆ S) :
    C.reads ⊆ S := by
  induction C with
  | nil => simp [ClaT.reads]
  | cons ℓ C ih =>
    simp only [ClaT.reads, List.foldr_cons]
    exact Finset.union_subset (h ℓ (by simp)) (ih fun ℓ' h' => h ℓ' (by simp [h']))

theorem reads_antesT (jl jv : ℕ) (p : A.Pat) : (antesT A ρ jl jv p).reads ⊆ {ρ.rt} := by
  refine reads_subset fun ℓ hℓ => ?_
  simp only [antesT, List.mem_cons, List.mem_flatMap, List.mem_map] at hℓ
  rcases hℓ with rfl | rfl | ⟨k, -, i, -, rfl⟩ <;> simp [VarT.reads, Term.reads]

/-- **(R)**: o gerador produz exatamente `A.fR T H`. -/
theorem clas_genR {E : Env R} {c₀ T H P Q : ℕ} (h : Vals ρ E c₀ T H P Q) (hd : Dist ρ c₀)
    (hdc : A.d ≤ c₀)
    (hlen : ∀ l v (p : A.Pat) k, ((stepAux (A.M l) v (A.janela p)).stk k).length ≤ c₀) :
    (genR A ρ c₀).clas w E = A.fR T H := by
  simp only [genR, Gen.clas, Tab.fR, h.hT]
  refine List.flatMap_congr fun t _ => ?_
  rw [Gen.clas_seqL, List.flatMap_map, flatMap_triples, triplos]
  refine List.flatMap_congr fun q _ => ?_
  have hv := h.update_t hd t
  simp only [triploG]
  rcases hl : A.labs[q.1]? with _ | (_ | l) <;> rcases hs : A.sts[q.2.1]? with _ | v <;>
    simp only [Gen.clas]
  rw [clas_conseqG A hv hd hdc (update_self ..) _ ?_ _ (fun k => hlen l v q.2.2 k),
    eval_antesT A _ _ _ (update_self ..)]
  intro r hr
  have := reads_antesT A q.1 q.2.1 q.2.2 hr
  simp only [Finset.mem_singleton] at this
  rw [this]
  exact hd.tj


/-! ### (I): a linha inicial -/

/-- O índice do rótulo e do estado iniciais. -/
noncomputable def jl0 : ℕ := ix A.labs (some A.l₀)
noncomputable def jv0 : ℕ := ix A.sts A.v₀

variable (ρ) in
/-- (I), parte 1: rótulo, estado e as pilhas fora da entrada. -/
noncomputable def genI1 (c₀ : ℕ) : Gen R K :=
  Gen.seq (Gen.clasL [[(.y (.const 0) (.const (jl0 A)), true)], [(.z (.const 0) (.const (jv0 A)), true)]])
    (Gen.seqL (((Tab.ks (K := K)).filter (· ≠ A.k₀)).map fun k =>
      .forU (ρ.hb c₀) ρ.ri (Gen.cla [(vx (.const 0) k (.reg ρ.ri) (.const (jnone A k)), true)])))

open Classical in
/-- Os valores de célula que **não** são candidatos a certificado (nem vazios). -/
noncomputable def jsLivres (cands : List (Γ A.k₀)) : List ℕ :=
  (List.range (A.vals A.k₀).length).filter fun j =>
    (A.vals A.k₀).getD j none ∉ none :: cands.map some

variable (ρ) in
/-- (I), parte 3: as `Q` células livres (índice `P + i`). -/
noncomputable def genI2 (cands : List (Γ A.k₀)) : Gen R K :=
  .forU ρ.Q ρ.ri (Gen.clasL
    (((jsLivres A cands).map fun j => [(vx (.const 0) A.k₀ (.add (.reg ρ.P) (.reg ρ.ri)) (.const j), false)]) ++
     [[(vx (.const 0) A.k₀ (.add (.reg ρ.P) (.reg ρ.ri)) (.const (jnone A A.k₀)), false),
       (vx (.const 0) A.k₀ (.add (.reg ρ.P) (.add (.reg ρ.ri) (.const 1))) (.const (jnone A A.k₀)), true)]]))

variable (ρ) in
/-- (I), parte 4: o resto da pilha de entrada vazio (índice `P + Q + i`). -/
noncomputable def genI3 : Gen R K :=
  .forU ρ.H2 ρ.ri (Gen.cla
    [(vx (.const 0) A.k₀ (.add (.reg ρ.P) (.add (.reg ρ.Q) (.reg ρ.ri))) (.const (jnone A A.k₀)), true)])

/-- As cláusulas da entrada `w` (duplicada), a partir da célula `i₀`. -/
noncomputable def preClas (enc : Bool → Γ A.k₀) : ℕ → List Bool → List (Cla K)
  | _, [] => []
  | i₀, b :: bs =>
    [[(.x 0 A.k₀ i₀ (ix (A.vals A.k₀) (some (enc b))), true)],
     [(.x 0 A.k₀ (i₀ + 1) (ix (A.vals A.k₀) (some (enc b))), true)]] ++ preClas enc (i₀ + 2) bs

variable (ρ) in
/-- (I), parte 2b: as duas células do separador, depois do bloco de bits (`ri = 2|w|`). -/
noncomputable def genSep (enc : Bool → Γ A.k₀) : Gen R K :=
  Gen.clasL [[(vx (.const 0) A.k₀ (.reg ρ.ri) (.const (ix (A.vals A.k₀) (some (enc false)))), true)],
    [(vx (.const 0) A.k₀ (.add (.reg ρ.ri) (.const 1)) (.const (ix (A.vals A.k₀) (some (enc true)))), true)]]

/-- A célula `i` da linha inicial na pilha de entrada. -/
noncomputable def F0 (i : ℕ) (o : Option (Γ A.k₀)) : List (Cla K) :=
  [[(.x 0 A.k₀ i (ix (A.vals A.k₀) o), true)]]

theorem preClas_spec (enc : Bool → Γ A.k₀) : ∀ (w : List Bool) (i₀ : ℕ) (rest : List (Γ A.k₀)),
    (List.range (2 * w.length + rest.length)).flatMap
        (fun i => F0 A (i₀ + i) ((w.flatMap fun b => [enc b, enc b]) ++ rest)[i]?) =
      preClas A enc i₀ w ++ (List.range rest.length).flatMap fun i => F0 A (i₀ + 2 * w.length + i) rest[i]?
  | [], i₀, rest => by simp [preClas]
  | b :: bs, i₀, rest => by
    have ih := preClas_spec enc bs (i₀ + 2) rest
    rw [List.length_cons, show 2 * (bs.length + 1) + rest.length = 2 + (2 * bs.length + rest.length)
      by ring, List.range_add, List.flatMap_append, List.flatMap_map]
    have h2 : (List.range 2).flatMap
        (fun i => F0 A (i₀ + i) (((b :: bs).flatMap fun b => [enc b, enc b]) ++ rest)[i]?) =
        [[(.x 0 A.k₀ i₀ (ix (A.vals A.k₀) (some (enc b))), true)],
         [(.x 0 A.k₀ (i₀ + 1) (ix (A.vals A.k₀) (some (enc b))), true)]] := by
      simp [F0, List.range_succ_eq_map]
    have h3 : (List.range (2 * bs.length + rest.length)).flatMap
        (fun i => F0 A (i₀ + (2 + i)) (((b :: bs).flatMap fun b => [enc b, enc b]) ++ rest)[2 + i]?) =
        preClas A enc (i₀ + 2) bs ++
          (List.range rest.length).flatMap fun i => F0 A (i₀ + 2 + 2 * bs.length + i) rest[i]? := by
      rw [← ih]
      refine List.flatMap_congr fun i _ => ?_
      rw [show i₀ + (2 + i) = i₀ + 2 + i by ring]
      simp only [List.flatMap_cons, List.cons_append, show 2 + i = i + 1 + 1 by ring,
        List.getElem?_cons_succ, List.nil_append]
    rw [h2, h3]
    simp only [preClas, List.cons_append, List.nil_append]
    congr 3
    refine List.flatMap_congr fun i _ => ?_
    congr 2
    ring

theorem length_pre (enc : Bool → Γ A.k₀) (w : List Bool) :
    ((((w.flatMap fun b => [b, b]) ++ [false, true]).map enc)).length = 2 * w.length + 2 := by
  simp only [List.length_map, List.length_append, List.length_cons, List.length_nil]
  induction w with
  | nil => simp
  | cons b w ih => simp only [List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢; omega

open Classical in
/-- A célula `i` da linha inicial na pilha de entrada (a função dentro de `Tab.fI`). -/
noncomputable def fIcell (pre cands : List (Γ A.k₀)) (Q H i : ℕ) : List (Cla K) :=
  if i < pre.length then [[(.x 0 A.k₀ i (ix (A.vals A.k₀) pre[i]?), true)]]
  else if i < pre.length + Q then
    ((List.range (A.vals A.k₀).length).filter (fun j =>
        (A.vals A.k₀).getD j none ∉ none :: cands.map some)).map
      (fun j => [(.x 0 A.k₀ i j, false)]) ++
    (if i + 1 < H then
      [[(.x 0 A.k₀ i (ix (A.vals A.k₀) none), false),
        (.x 0 A.k₀ (i + 1) (ix (A.vals A.k₀) none), true)]] else [])
  else [[(.x 0 A.k₀ i (ix (A.vals A.k₀) none), true)]]

theorem fI_eq (pre cands : List (Γ A.k₀)) (Q H : ℕ) :
    A.fI pre cands Q H =
      [[(.y 0 (jl0 A), true)], [(.z 0 (jv0 A), true)]] ++
      ((Tab.ks (K := K)).filter (· ≠ A.k₀)).flatMap (fun k =>
        (List.range H).map fun i => [(.x 0 k i (jnone A k), true)]) ++
      (List.range H).flatMap (fIcell A pre cands Q H) := rfl

theorem fIcell_lt (pre cands : List (Γ A.k₀)) (Q H : ℕ) {i : ℕ} (hi : i < pre.length) :
    fIcell A pre cands Q H i = F0 A i pre[i]? := by
  simp [fIcell, hi, F0]

theorem fIcell_mid (pre cands : List (Γ A.k₀)) (Q H : ℕ) {i : ℕ} (hi : pre.length ≤ i)
    (hi' : i < pre.length + Q) (hH : i + 1 < H) :
    fIcell A pre cands Q H i =
      ((jsLivres A cands).map fun j => [(.x 0 A.k₀ i j, false)]) ++
        [[(.x 0 A.k₀ i (jnone A A.k₀), false), (.x 0 A.k₀ (i + 1) (jnone A A.k₀), true)]] := by
  simp [fIcell, not_lt.mpr hi, hi', hH, jsLivres, jnone]

theorem fIcell_hi (pre cands : List (Γ A.k₀)) (Q H : ℕ) {i : ℕ} (hi : pre.length + Q ≤ i) :
    fIcell A pre cands Q H i = [[(.x 0 A.k₀ i (jnone A A.k₀), true)]] := by
  simp [fIcell, not_lt.mpr hi, not_lt.mpr (by omega : pre.length ≤ i), jnone]

/-- **(I)** como concatenação das partes, com `pre = (w.flatMap dup ++ [false, true]).map enc`. -/
theorem fI_split (enc : Bool → Γ A.k₀) (cands : List (Γ A.k₀)) (w : List Bool) {Q H : ℕ}
    (hH : 2 * w.length + 2 + Q < H) :
    A.fI (((w.flatMap fun b => [b, b]) ++ [false, true]).map enc) cands Q H =
      [[(.y 0 (jl0 A), true)], [(.z 0 (jv0 A), true)]] ++
      ((Tab.ks (K := K)).filter (· ≠ A.k₀)).flatMap (fun k =>
        (List.range H).map fun i => [(.x 0 k i (jnone A k), true)]) ++
      (preClas A enc 0 w ++
        [[(.x 0 A.k₀ (2 * w.length) (ix (A.vals A.k₀) (some (enc false))), true)],
         [(.x 0 A.k₀ (2 * w.length + 1) (ix (A.vals A.k₀) (some (enc true))), true)]]) ++
      ((List.range Q).flatMap fun i =>
        ((jsLivres A cands).map fun j => [(.x 0 A.k₀ (2 * w.length + 2 + i) j, false)]) ++
          [[(.x 0 A.k₀ (2 * w.length + 2 + i) (jnone A A.k₀), false),
            (.x 0 A.k₀ (2 * w.length + 2 + i + 1) (jnone A A.k₀), true)]]) ++
      ((List.range (H - (2 * w.length + 2) - Q)).flatMap fun i =>
        [[(.x 0 A.k₀ (2 * w.length + 2 + Q + i) (jnone A A.k₀), true)]]) := by
  have hlen := length_pre A enc w
  set pre := (((w.flatMap fun b => [b, b]) ++ [false, true]).map enc) with hpre
  set P := 2 * w.length + 2 with hP
  have hr : List.range H = List.range P ++ (List.range Q).map (P + ·) ++
      (List.range (H - P - Q)).map (P + Q + ·) := by
    rw [← List.range_add, ← List.range_add]
    congr 1
    omega
  rw [fI_eq, hr, List.flatMap_append, List.flatMap_append, List.flatMap_map, List.flatMap_map]
  have h1 : (List.range P).flatMap (fIcell A pre cands Q H) =
      preClas A enc 0 w ++
        [[(.x 0 A.k₀ (2 * w.length) (ix (A.vals A.k₀) (some (enc false))), true)],
         [(.x 0 A.k₀ (2 * w.length + 1) (ix (A.vals A.k₀) (some (enc true))), true)]] := by
    rw [List.flatMap_congr fun i hi => fIcell_lt A pre cands Q H (by
      rw [hlen]; exact List.mem_range.mp hi)]
    have := preClas_spec A enc w 0 [enc false, enc true]
    simp only [Nat.zero_add, List.length_cons, List.length_nil, Nat.reduceAdd] at this
    simp only [hpre, hP, List.map_append, List.map_flatMap, List.map_cons, List.map_nil]
    rw [this]
    simp [F0, List.range_succ_eq_map]
  have h2 : (List.range Q).flatMap (fun i => fIcell A pre cands Q H (P + i)) =
      (List.range Q).flatMap fun i =>
        ((jsLivres A cands).map fun j => [(.x 0 A.k₀ (P + i) j, false)]) ++
          [[(.x 0 A.k₀ (P + i) (jnone A A.k₀), false), (.x 0 A.k₀ (P + i + 1) (jnone A A.k₀), true)]] :=
    List.flatMap_congr fun i hi => fIcell_mid A pre cands Q H (by rw [hlen]; omega)
      (by rw [hlen]; have := List.mem_range.mp hi; omega) (by have := List.mem_range.mp hi; omega)
  have h3 : (List.range (H - P - Q)).flatMap (fun i => fIcell A pre cands Q H (P + Q + i)) =
      (List.range (H - P - Q)).flatMap fun i => [[(.x 0 A.k₀ (P + Q + i) (jnone A A.k₀), true)]] :=
    List.flatMap_congr fun i _ => fIcell_hi A pre cands Q H (by rw [hlen]; omega)
  rw [h1, h2, h3]
  simp only [List.append_assoc]

end tab

end ATK.CookLevinGen
