import ATK.GeradorTM

/-!
# ATK — Cook–Levin, marco CL4b-4a: moldes de fórmula compilados para laços

Uma fórmula CNF cujas variáveis são escritas como `0^a 1 0^t 1 0^p 1` é descrita por um *molde*
`FT V R`:

* `cl lits`: uma cláusula, cada literal com variável `v g` (`g` = valores dos contadores), sinal,
  índice fixo `a` e termos unários `t`, `p` (soma de contadores mais constante);
* `cat`, `nil`: concatenação;
* `rng r i body`: para `i < g r`, o molde `body` com o contador `i` valendo `i`;
* `bits i b₀ b₁`: para cada bit da entrada (posição em `i`), `b₀` ou `b₁`.

`sem` é a fórmula do molde, `comp` o programa de laços. **`comp_ok`**: o programa escreve
exatamente a codificação da fórmula, sem alterar os contadores fora dos índices (`WF`).

**Nada aqui prova Cook–Levin. CLOSED_MATH continua false.**
-/

namespace ATK.Gerador

set_option linter.unusedSectionVars false

open Function

variable {R : Type} [DecidableEq R]

/-! ### Saídas auxiliares -/

/-- Escrever uma lista fixa de bits. -/
def outs (l : List Bool) : Prog R := l.foldr (fun b p => .seq (.out b) p) .skip

theorem run_outs (w : List Bool) : ∀ (l : List Bool) (s : St R),
    run w (outs l) s = ⟨s.regs, s.out ++ l⟩
  | [], s => by simp [outs, run]
  | b :: l, s => by
    have := run_outs w l ⟨s.regs, s.out ++ [b]⟩
    simp only [outs, List.foldr_cons, run] at this ⊢
    rw [this]
    simp

/-- Sequência de programas. -/
def seqs (ps : List (Prog R)) : Prog R := ps.foldr .seq .skip

/-- Programas puros (só escrevem) em sequência. -/
theorem run_seqs_puro {α : Type} (w : List Bool) (f : α → (R → ℕ) → List Bool) (P : α → Prog R)
    (hP : ∀ x s, run w (P x) s = ⟨s.regs, s.out ++ f x s.regs⟩) :
    ∀ (xs : List α) (s : St R), run w (seqs (xs.map P)) s = ⟨s.regs, s.out ++ xs.flatMap (f · s.regs)⟩
  | [], s => by simp [seqs, run]
  | x :: xs, s => by
    have := run_seqs_puro w f P hP xs ⟨s.regs, s.out ++ f x s.regs⟩
    simp only [seqs, List.map_cons, List.foldr_cons, run] at this ⊢
    rw [hP x s, this]
    simp

/-- `[false, b]`. -/
def sb (b : Bool) : List Bool := [false, b]

/-- `0^n 1` com cada bit `c` escrito como `[false, c]`. -/
def unS (n : ℕ) : List Bool := List.replicate (2 * n) false ++ [false, true]

/-- Termo unário: soma de contadores mais constante. -/
abbrev UT (R : Type) := List R × ℕ

/-- Valor de um termo. -/
def val (u : UT R) (g : R → ℕ) : ℕ := (u.1.map g).sum + u.2

/-- Escrever `unS` de um contador. -/
def dup (r : R) : Prog R := .loop r (.seq (.out false) (.out false))

theorem run_dup (w : List Bool) (r : R) (s : St R) :
    run w (dup r) s = ⟨s.regs, s.out ++ List.replicate (2 * s.regs r) false⟩ := by
  have it : ∀ n (s' : St R), s'.regs = s.regs →
      (run w (.seq (.out false) (.out false)))^[n] s' =
        ⟨s.regs, s'.out ++ List.replicate (2 * n) false⟩ := by
    intro n
    induction n with
    | zero => intro s' h; cases s'; simp_all
    | succ n ih =>
      intro s' h
      rw [iterate_succ_apply, ih _ (by simp [run, h])]
      simp only [run, St.mk.injEq, true_and]
      rw [show 2 * (n + 1) = 2 + 2 * n by ring, List.replicate_add]
      simp
  exact it _ s rfl

/-- Escrever `unS (val u g)`. -/
def emitU (u : UT R) : Prog R :=
  .seq (seqs (u.1.map dup)) (outs (List.replicate (2 * u.2) false ++ [false, true]))

theorem flatMap_rep (g : R → ℕ) : ∀ rs : List R,
    rs.flatMap (fun r => List.replicate (2 * g r) false) = List.replicate (2 * (rs.map g).sum) false
  | [] => by simp
  | r :: rs => by
    rw [List.flatMap_cons, flatMap_rep g rs, List.map_cons, List.sum_cons, Nat.mul_add,
      List.replicate_append_replicate]

theorem run_emitU (w : List Bool) (u : UT R) (s : St R) :
    run w (emitU u) s = ⟨s.regs, s.out ++ unS (val u s.regs)⟩ := by
  simp only [emitU, run]
  rw [run_seqs_puro w (fun r g => List.replicate (2 * g r) false) dup (fun r s => run_dup w r s),
    run_outs, flatMap_rep]
  simp only [unS, val, Nat.mul_add, ← List.replicate_append_replicate, List.append_assoc]

/-! ### Literais e moldes -/

/-- Saída de um literal: sinal, `0^a 1`, `0^t 1`, `0^p 1`, fim de literal. -/
def litOut (b : Bool) (a t p : ℕ) : List Bool := sb b ++ unS a ++ unS t ++ unS p ++ [true, false]

/-- Molde de literal. -/
structure LT (V R : Type) where
  v : (R → ℕ) → V
  b : Bool
  a : ℕ
  tt : UT R
  pt : UT R

/-- O programa de um literal. -/
def litP {V : Type} (l : LT V R) : Prog R :=
  .seq (outs (sb l.b ++ unS l.a)) (.seq (emitU l.tt) (.seq (emitU l.pt) (outs [true, false])))

theorem run_litP {V : Type} (w : List Bool) (l : LT V R) (s : St R) :
    run w (litP l) s = ⟨s.regs, s.out ++ litOut l.b l.a (val l.tt s.regs) (val l.pt s.regs)⟩ := by
  simp only [litP, run, run_outs, run_emitU, litOut, List.append_assoc]

section Moldes

variable {V : Type} (cod3 : V → ℕ × ℕ × ℕ)

/-- Saída de um literal sobre variáveis. -/
def litOutV (ℓ : V × Bool) : List Bool := litOut ℓ.2 (cod3 ℓ.1).1 (cod3 ℓ.1).2.1 (cod3 ℓ.1).2.2

/-- Saída de uma cláusula. -/
def clOutV (C : List (V × Bool)) : List Bool := C.flatMap (litOutV cod3) ++ [true, true]

/-- Saída de uma fórmula. -/
def fmOutV (φ : List (List (V × Bool))) : List Bool := φ.flatMap (clOutV cod3)

/-- Moldes de fórmula. -/
inductive FT (V R : Type) where
  | nil
  | cl (lits : List (LT V R))
  | cat (a b : FT V R)
  | rng (r i : R) (body : FT V R)
  | bits (i : R) (b₀ b₁ : FT V R)

/-- A fórmula de um molde. -/
def sem (w : List Bool) : FT V R → (R → ℕ) → List (List (V × Bool))
  | .nil, _ => []
  | .cl lits, g => [lits.map fun l => (l.v g, l.b)]
  | .cat a b, g => sem w a g ++ sem w b g
  | .rng r i body, g => (List.range (g r)).flatMap fun k => sem w body (update g i k)
  | .bits i b₀ b₁, g => w.zipIdx.flatMap fun x =>
      if x.1 then sem w b₁ (update g i x.2) else sem w b₀ (update g i x.2)

/-- O programa de um molde. -/
def comp : FT V R → Prog R
  | .nil => .skip
  | .cl lits => .seq (seqs (lits.map litP)) (outs [true, true])
  | .cat a b => .seq (comp a) (comp b)
  | .rng r i body => .seq (.clr i) (.loop r (.seq (comp body) (.inc i)))
  | .bits i b₀ b₁ => .seq (.clr i) (.forIn (.seq (comp b₀) (.inc i)) (.seq (comp b₁) (.inc i)))

/-- `f` não depende dos contadores em `sc`. -/
def Insens {α : Type} (sc : R → Prop) (f : (R → ℕ) → α) : Prop :=
  ∀ g g', (∀ r, ¬ sc r → g r = g' r) → f g = f g'

/-- Boa formação: os índices (`sc`) não são lidos fora dos seus laços. -/
def WF : FT V R → (R → Prop) → Prop
  | .nil, _ => True
  | .cl lits, sc => ∀ l ∈ lits, (∀ r ∈ l.tt.1 ++ l.pt.1, ¬ sc r) ∧ Insens sc l.v ∧
      ∀ g, cod3 (l.v g) = (l.a, val l.tt g, val l.pt g)
  | .cat a b, sc => WF a sc ∧ WF b sc
  | .rng r i body, sc => ¬ sc r ∧ sc i ∧ WF body (fun x => sc x ∧ x ≠ i)
  | .bits i b₀ b₁, sc => sc i ∧ WF b₀ (fun x => sc x ∧ x ≠ i) ∧ WF b₁ (fun x => sc x ∧ x ≠ i)

theorem fmOutV_append (φ ψ : List (List (V × Bool))) :
    fmOutV cod3 (φ ++ ψ) = fmOutV cod3 φ ++ fmOutV cod3 ψ := by
  simp [fmOutV]

theorem sem_insens (w : List Bool) :
    ∀ (ft : FT V R) (sc : R → Prop), WF cod3 ft sc → Insens sc (sem w ft)
  | .nil, _, _ => fun _ _ _ => rfl
  | .cl lits, sc, h => fun g g' hg => by
    simp only [sem, List.cons.injEq, and_true]
    apply List.map_congr_left
    intro l hl
    rw [(h l hl).2.1 g g' hg]
  | .cat a b, sc, h => fun g g' hg => by
    simp only [sem]
    rw [sem_insens w a sc h.1 g g' hg, sem_insens w b sc h.2 g g' hg]
  | .rng r i body, sc, h => fun g g' hg => by
    obtain ⟨hr, hi, hb⟩ := h
    simp only [sem]
    rw [hg r hr]
    congr 1
    funext k
    apply sem_insens w body _ hb
    intro x hx
    by_cases hxi : x = i
    · subst hxi; simp
    · simp only [update_of_ne hxi]
      exact hg x fun hsc => hx ⟨hsc, hxi⟩
  | .bits i b₀ b₁, sc, h => fun g g' hg => by
    obtain ⟨hi, h0, h1⟩ := h
    simp only [sem]
    congr 1
    funext x
    have hh : ∀ k, ∀ y, ¬ (sc y ∧ y ≠ i) → update g i k y = update g' i k y := by
      intro k y hy
      by_cases hyi : y = i
      · subst hyi; simp
      · simp only [update_of_ne hyi]
        exact hg y fun hsc => hy ⟨hsc, hyi⟩
    split_ifs
    · exact sem_insens w b₁ _ h1 _ _ (hh x.2)
    · exact sem_insens w b₀ _ h0 _ _ (hh x.2)

/-- **O programa de um molde escreve a sua fórmula.** -/
theorem comp_ok (w : List Bool) :
    ∀ (ft : FT V R) (sc : R → Prop), WF cod3 ft sc → ∀ s : St R,
      (run w (comp ft) s).out = s.out ++ fmOutV cod3 (sem w ft s.regs) ∧
      ∀ r, ¬ sc r → (run w (comp ft) s).regs r = s.regs r
  | .nil, _, _, s => by simp [comp, run, sem, fmOutV]
  | .cl lits, sc, h, s => by
    have e := run_seqs_puro w (fun l g => litOut l.b l.a (val l.tt g) (val l.pt g)) litP
      (fun l s => run_litP w l s) lits s
    have hrun : run w (comp (.cl lits)) s = ⟨s.regs, s.out ++ lits.flatMap (fun l =>
        litOut l.b l.a (val l.tt s.regs) (val l.pt s.regs)) ++ [true, true]⟩ := by
      simp only [comp, run, e, run_outs]
    rw [hrun]
    refine ⟨?_, fun _ _ => rfl⟩
    simp only [sem, fmOutV, clOutV, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.flatMap_map, List.append_assoc]
    congr 2
    apply List.flatMap_congr
    intro l hl
    simp only [litOutV, (h l hl).2.2 s.regs]
  | .cat a b, sc, h, s => by
    obtain ⟨ha1, ha2⟩ := comp_ok w a sc h.1 s
    obtain ⟨hb1, hb2⟩ := comp_ok w b sc h.2 (run w (comp a) s)
    refine ⟨?_, fun r hr => (hb2 r hr).trans (ha2 r hr)⟩
    simp only [comp, run, sem, fmOutV_append]
    rw [hb1, ha1, sem_insens cod3 w b sc h.2 (run w (comp a) s).regs s.regs ha2]
    simp
  | .rng r i body, sc, h, s => by
    obtain ⟨hr, hi, hb⟩ := h
    have hri : r ≠ i := fun e => hr (e ▸ hi)
    have key : ∀ k, ((run w (.seq (comp body) (.inc i)))^[k] ⟨update s.regs i 0, s.out⟩).regs i = k ∧
        (∀ x, ¬ sc x → ((run w (.seq (comp body) (.inc i)))^[k]
          ⟨update s.regs i 0, s.out⟩).regs x = s.regs x) ∧
        ((run w (.seq (comp body) (.inc i)))^[k] ⟨update s.regs i 0, s.out⟩).out =
          s.out ++ fmOutV cod3 ((List.range k).flatMap fun k' => sem w body (update s.regs i k')) := by
      intro k
      induction k with
      | zero =>
        refine ⟨by simp, fun x hx => ?_, by simp [fmOutV]⟩
        have hxi : x ≠ i := fun e => hx (e ▸ hi)
        simp [update_of_ne hxi]
      | succ k ih =>
        obtain ⟨e1, e2, e3⟩ := ih
        rw [iterate_succ_apply']
        set X := (run w (.seq (comp body) (.inc i)))^[k] ⟨update s.regs i 0, s.out⟩
        obtain ⟨c1, c2⟩ := comp_ok w body _ hb X
        have hins : sem w body X.regs = sem w body (update s.regs i k) := by
          apply sem_insens cod3 w body _ hb
          intro x hx
          by_cases hxi : x = i
          · subst hxi; simp [e1]
          · have : ¬ sc x := fun hsc => hx ⟨hsc, hxi⟩
            simp [update_of_ne hxi, e2 x this]
        have ci : (run w (comp body) X).regs i = k := by
          rw [c2 i (by simp), e1]
        simp only [run]
        refine ⟨by simp [ci], fun x hx => ?_, ?_⟩
        · have hxi : x ≠ i := fun e => hx (e ▸ hi)
          simp only [update_of_ne hxi]
          rw [c2 x (fun h => hx h.1), e2 x hx]
        · rw [c1, e3, hins, List.range_succ, List.flatMap_append, fmOutV_append]
          simp
    obtain ⟨k1, k2, k3⟩ := key (s.regs r)
    have hloop : run w (comp (.rng r i body)) s =
        (run w (.seq (comp body) (.inc i)))^[s.regs r] ⟨update s.regs i 0, s.out⟩ := by
      simp only [comp, run]
      rw [update_of_ne hri]
    rw [hloop]
    exact ⟨k3, k2⟩
  | .bits i b₀ b₁, sc, h, s => by
    obtain ⟨hi, h0, h1⟩ := h
    have ok0 := comp_ok w b₀ _ h0
    have ok1 := comp_ok w b₁ _ h1
    let F : St R → Bool → St R := fun s b =>
      if b then run w (.seq (comp b₁) (.inc i)) s else run w (.seq (comp b₀) (.inc i)) s
    have key : ∀ (l : List Bool) (j : ℕ) (X : St R), X.regs i = j →
        (∀ x, ¬ sc x → X.regs x = s.regs x) →
        (l.foldl F X).regs i = j + l.length ∧
        (∀ x, ¬ sc x → (l.foldl F X).regs x = s.regs x) ∧
        (l.foldl F X).out = X.out ++ fmOutV cod3 ((l.zipIdx j).flatMap fun x =>
          if x.1 then sem w b₁ (update s.regs i x.2) else sem w b₀ (update s.regs i x.2)) := by
      intro l
      induction l with
      | nil => intro j X e1 e2; exact ⟨by simp [e1], e2, by simp [fmOutV]⟩
      | cons b l ih =>
        intro j X e1 e2
        have step : ∀ (bd : FT V R), WF cod3 bd (fun x => sc x ∧ x ≠ i) →
            (∀ s : St R, (run w (comp bd) s).out = s.out ++ fmOutV cod3 (sem w bd s.regs) ∧
              ∀ r, ¬ (sc r ∧ r ≠ i) → (run w (comp bd) s).regs r = s.regs r) →
            (run w (.seq (comp bd) (.inc i)) X).regs i = j + 1 ∧
            (∀ x, ¬ sc x → (run w (.seq (comp bd) (.inc i)) X).regs x = s.regs x) ∧
            (run w (.seq (comp bd) (.inc i)) X).out =
              X.out ++ fmOutV cod3 (sem w bd (update s.regs i j)) := by
          intro bd hbd hok
          obtain ⟨c1, c2⟩ := hok X
          have hins : sem w bd X.regs = sem w bd (update s.regs i j) := by
            apply sem_insens cod3 w bd _ hbd
            intro x hx
            by_cases hxi : x = i
            · subst hxi; simp [e1]
            · have : ¬ sc x := fun hsc => hx ⟨hsc, hxi⟩
              simp [update_of_ne hxi, e2 x this]
          simp only [run]
          refine ⟨by simp [c2 i (by simp), e1], fun x hx => ?_, by simp [c1, hins]⟩
          have hxi : x ≠ i := fun e => hx (e ▸ hi)
          simp only [update_of_ne hxi]
          rw [c2 x (fun h => hx h.1), e2 x hx]
        obtain ⟨t1, t2, t3⟩ := step (if b then b₁ else b₀) (by cases b <;> simp [h0, h1])
          (by cases b <;> assumption)
        have hF : F X b = run w (.seq (comp (if b then b₁ else b₀)) (.inc i)) X := by
          cases b <;> rfl
        obtain ⟨u1, u2, u3⟩ := ih (j + 1) (F X b) (by rw [hF, t1]) (by rw [hF]; exact t2)
        simp only [List.foldl_cons, List.length_cons, List.zipIdx_cons, List.flatMap_cons,
          fmOutV_append]
        refine ⟨by rw [u1]; omega, u2, ?_⟩
        rw [u3, hF, t3]
        cases b <;> simp
    have hrun : run w (comp (.bits i b₀ b₁)) s = w.foldl F ⟨update s.regs i 0, s.out⟩ := rfl
    obtain ⟨k1, k2, k3⟩ := key w 0 ⟨update s.regs i 0, s.out⟩ (by simp) (fun x hx => by
      have hxi : x ≠ i := fun e => hx (e ▸ hi)
      simp [update_of_ne hxi])
    rw [hrun]
    exact ⟨k3, k2⟩

/-! ### Custo -/

theorem cost_seq (w : List Bool) (p q : Prog R) (s : St R) :
    cost w (.seq p q) s = cost w p s + cost w q (run w p s) := rfl
theorem cost_loop (w : List Bool) (r : R) (p : Prog R) (s : St R) :
    cost w (.loop r p) s = 2 * (s.regs r + 1) + 1 + costIt (cost w p) (run w p) (s.regs r) s := rfl
theorem cost_forIn (w : List Bool) (p₀ p₁ : Prog R) (s : St R) :
    cost w (.forIn p₀ p₁) s = 2 * (w.length + 1) + 1 +
      costIn (cost w p₀) (cost w p₁) (run w p₀) (run w p₁) w s := rfl
theorem cost_clr (w : List Bool) (r : R) (s : St R) : cost w (.clr r) s = s.regs r + 1 := rfl
theorem cost_inc (w : List Bool) (r : R) (s : St R) : cost w (.inc r) s = 1 := rfl
theorem costIt_succ {α : Type} (c : α → ℕ) (f : α → α) (n : ℕ) (x : α) :
    costIt c f (n + 1) x = c x + 2 + costIt c f n (f x) := rfl
theorem costIn_cons {α : Type} (c₀ c₁ : α → ℕ) (f₀ f₁ : α → α) (b : Bool) (bs : List Bool) (x : α) :
    costIn c₀ c₁ f₀ f₁ (b :: bs) x =
      (if b then c₁ x else c₀ x) + 2 + costIn c₀ c₁ f₀ f₁ bs (if b then f₁ x else f₀ x) := rfl

theorem cost_outs (w : List Bool) : ∀ (l : List Bool) (s : St R), cost w (outs l) s = l.length
  | [], s => by simp [outs, cost]
  | b :: l, s => by
    simp only [outs, List.foldr_cons, cost, List.length_cons]
    have := cost_outs w l ⟨s.regs, s.out ++ [b]⟩
    simp only [outs] at this
    simp only [run]
    rw [this]
    omega

theorem costIt_const {α : Type} (c : α → ℕ) (f : α → α) (k : ℕ) (hc : ∀ x, c x = k) :
    ∀ n x, costIt c f n x = n * (k + 2)
  | 0, x => by simp [costIt]
  | n + 1, x => by
    simp only [costIt, hc, costIt_const c f k hc n (f x)]
    ring

theorem cost_dup (w : List Bool) (r : R) (s : St R) : cost w (dup r) s = 6 * s.regs r + 3 := by
  simp only [dup, cost]
  rw [costIt_const _ _ 2 (fun x => by simp [cost])]
  ring

theorem cost_seqs_le {α : Type} (w : List Bool) (f : α → (R → ℕ) → List Bool) (P : α → Prog R)
    (hP : ∀ x s, run w (P x) s = ⟨s.regs, s.out ++ f x s.regs⟩) (c : α → ℕ) :
    ∀ (xs : List α) (s : St R), (∀ x ∈ xs, ∀ s' : St R, s'.regs = s.regs → cost w (P x) s' ≤ c x) →
      cost w (seqs (xs.map P)) s ≤ (xs.map c).sum
  | [], s, _ => by simp [seqs, cost]
  | x :: xs, s, h => by
    simp only [seqs, List.map_cons, List.foldr_cons, cost, List.sum_cons]
    have h1 := h x (List.mem_cons_self ..) s rfl
    have h2 := cost_seqs_le w f P hP c xs (run w (P x) s) (fun y hy s' hs' =>
      h y (List.mem_cons_of_mem _ hy) s' (by rw [hs', hP]))
    simp only [seqs] at h2
    omega

theorem cost_emitU_le (w : List Bool) (u : UT R) (s : St R) (B : ℕ) (hB : ∀ r, s.regs r ≤ B) :
    cost w (emitU u) s ≤ u.1.length * (6 * B + 3) + 2 * u.2 + 2 := by
  simp only [emitU, cost]
  have h1 := cost_seqs_le w (fun r g => List.replicate (2 * g r) false) dup
    (fun r s => run_dup w r s) (fun _ => 6 * B + 3) u.1 s (fun r _ s' hs' => by
      rw [cost_dup, hs']; have := hB r; omega)
  rw [cost_outs]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil] at h1 ⊢
  omega

/-- Limite do custo de um literal. -/
def litC {V : Type} (l : LT V R) (B : ℕ) : ℕ :=
  2 * l.a + 4 + (l.tt.1.length * (6 * B + 3) + 2 * l.tt.2 + 2) +
    (l.pt.1.length * (6 * B + 3) + 2 * l.pt.2 + 2) + 2

theorem cost_litP_le {V : Type} (w : List Bool) (l : LT V R) (s : St R) (B : ℕ)
    (hB : ∀ r, s.regs r ≤ B) : cost w (litP l) s ≤ litC l B := by
  simp only [litP, cost, run_outs, run_emitU, cost_outs]
  have h1 := cost_emitU_le w l.tt ⟨s.regs, s.out ++ (sb l.b ++ unS l.a)⟩ B hB
  have h2 := cost_emitU_le w l.pt ⟨s.regs, (s.out ++ (sb l.b ++ unS l.a)) ++
    unS (val l.tt s.regs)⟩ B hB
  simp only [litC, sb, unS, List.length_append, List.length_cons, List.length_replicate,
    List.length_nil] at h1 h2 ⊢
  omega

section CustoMoldes

variable {V : Type}

/-- Limite do custo de um molde, com contadores e entrada `≤ B`. -/
def cb : FT V R → ℕ → ℕ
  | .nil, _ => 0
  | .cl lits, B => (lits.map (litC · B)).sum + 2
  | .cat a b, B => cb a B + cb b B
  | .rng _ _ body, B => 3 * B + 4 + B * (cb body B + 3)
  | .bits _ b₀ b₁, B => 3 * B + 4 + B * (cb b₀ B + cb b₁ B + 3)

variable (cod3 : V → ℕ × ℕ × ℕ)

/-- **Custo dos moldes.** Com contadores e entrada limitados por `B`, o programa de um molde custa
no máximo `cb ft B` passos e mantém os contadores `≤ B`. -/
theorem comp_cost (w : List Bool) (B : ℕ) (hw : w.length ≤ B) :
    ∀ (ft : FT V R) (sc : R → Prop), WF cod3 ft sc → ∀ s : St R, (∀ r, s.regs r ≤ B) →
      cost w (comp ft) s ≤ cb ft B ∧ ∀ r, (run w (comp ft) s).regs r ≤ B
  | .nil, _, _, s, hB => by simp [comp, cost, cb, run, hB]
  | .cl lits, sc, h, s, hB => by
    have e := run_seqs_puro w (fun l g => litOut l.b l.a (val l.tt g) (val l.pt g)) litP
      (fun l s => run_litP w l s) lits s
    have c1 := cost_seqs_le w (fun l g => litOut l.b l.a (val l.tt g) (val l.pt g)) litP
      (fun l s => run_litP w l s) (litC · B) lits s (fun l _ s' hs' =>
        cost_litP_le w l s' B (by rw [hs']; exact hB))
    simp only [comp, cost, cb, run, e, run_outs, cost_outs]
    refine ⟨by simp; omega, hB⟩
  | .cat a b, sc, h, s, hB => by
    obtain ⟨a1, a2⟩ := comp_cost w B hw a sc h.1 s hB
    obtain ⟨b1, b2⟩ := comp_cost w B hw b sc h.2 (run w (comp a) s) a2
    simp only [comp, cost, cb, run]
    exact ⟨by omega, b2⟩
  | .rng r i body, sc, h, s, hB => by
    obtain ⟨hr, hi, hb⟩ := h
    have hri : r ≠ i := fun e => hr (e ▸ hi)
    have it : ∀ n (X : St R), (∀ r', X.regs r' ≤ B) → X.regs i + n ≤ B →
        costIt (cost w (.seq (comp body) (.inc i))) (run w (.seq (comp body) (.inc i))) n X ≤
          n * (cb body B + 3) ∧
        ∀ r', ((run w (.seq (comp body) (.inc i)))^[n] X).regs r' ≤ B := by
      intro n
      induction n with
      | zero => intro X hX _; simp [costIt, hX]
      | succ n ih =>
        intro X hX hXi
        obtain ⟨d1, d2⟩ := comp_cost w B hw body _ hb X hX
        have fi := (comp_ok cod3 w body _ hb X).2 i (by simp)
        have hY : ∀ r', (run w (.seq (comp body) (.inc i)) X).regs r' ≤ B := by
          intro r'
          simp only [run]
          by_cases h' : r' = i
          · subst h'; simp; omega
          · simp [update_of_ne h', d2 r']
        have hYi : (run w (.seq (comp body) (.inc i)) X).regs i = X.regs i + 1 := by
          simp [run, fi]
        obtain ⟨e1, e2⟩ := ih _ hY (by rw [hYi]; omega)
        refine ⟨?_, by rw [iterate_succ_apply]; exact e2⟩
        rw [costIt_succ, cost_seq, cost_inc, Nat.succ_mul]
        omega
    have hs1 : ∀ r', (update s.regs i 0) r' ≤ B := by
      intro r'; by_cases h' : r' = i
      · subst h'; simp
      · simp [update_of_ne h', hB r']
    obtain ⟨t1, t2⟩ := it (s.regs r) ⟨update s.regs i 0, s.out⟩ hs1 (by simp [hB r])
    have hrun : run w (comp (.rng r i body)) s =
        (run w (.seq (comp body) (.inc i)))^[s.regs r] ⟨update s.regs i 0, s.out⟩ := by
      simp only [comp, run]
      rw [update_of_ne hri]
    have hcost : cost w (comp (.rng r i body)) s = s.regs i + 1 + (2 * (s.regs r + 1) + 1 +
        costIt (cost w (.seq (comp body) (.inc i))) (run w (.seq (comp body) (.inc i)))
          (s.regs r) ⟨update s.regs i 0, s.out⟩) := by
      show cost w (.seq (.clr i) (.loop r (.seq (comp body) (.inc i)))) s = _
      rw [cost_seq, cost_clr, cost_loop]
      simp only [run, update_of_ne hri]
    rw [hcost, hrun]
    simp only [cb]
    refine ⟨?_, t2⟩
    have := hB i
    have := hB r
    have : s.regs r * (cb body B + 3) ≤ B * (cb body B + 3) := Nat.mul_le_mul_right _ (hB r)
    omega
  | .bits i b₀ b₁, sc, h, s, hB => by
    obtain ⟨hi, h0, h1⟩ := h
    have cc0 := comp_cost w B hw b₀ _ h0
    have cc1 := comp_cost w B hw b₁ _ h1
    have it : ∀ (l : List Bool) (X : St R), (∀ r', X.regs r' ≤ B) → X.regs i + l.length ≤ B →
        costIn (cost w (.seq (comp b₀) (.inc i))) (cost w (.seq (comp b₁) (.inc i)))
          (run w (.seq (comp b₀) (.inc i))) (run w (.seq (comp b₁) (.inc i))) l X ≤
          l.length * (cb b₀ B + cb b₁ B + 3) ∧
        ∀ r', (l.foldl (fun s b => if b then run w (.seq (comp b₁) (.inc i)) s else
          run w (.seq (comp b₀) (.inc i)) s) X).regs r' ≤ B := by
      intro l
      induction l with
      | nil => intro X hX _; simp [costIn, hX]
      | cons b l ih =>
        intro X hX hXi
        have one : ∀ (bd : FT V R), WF cod3 bd (fun x => sc x ∧ x ≠ i) →
            (cost w (comp bd) X ≤ cb bd B ∧ ∀ r, (run w (comp bd) X).regs r ≤ B) →
            (∀ r', (run w (.seq (comp bd) (.inc i)) X).regs r' ≤ B) ∧
            (run w (.seq (comp bd) (.inc i)) X).regs i = X.regs i + 1 := by
          intro bd hbd ⟨_, d2⟩
          have fi := (comp_ok cod3 w bd _ hbd X).2 i (by simp)
          refine ⟨fun r' => ?_, by simp [run, fi]⟩
          simp only [run]
          by_cases h' : r' = i
          · subst h'; simp [fi]; simp at hXi; omega
          · simp [update_of_ne h', d2 r']
        cases b with
        | false =>
          obtain ⟨y1, y2⟩ := one b₀ h0 (cc0 X hX)
          obtain ⟨e1, e2⟩ := ih _ y1 (by rw [y2]; simp at hXi; omega)
          refine ⟨?_, by simpa using e2⟩
          have := (cc0 X hX).1
          rw [costIn_cons]
          simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
          rw [cost_seq, cost_inc, Nat.succ_mul]
          omega
        | true =>
          obtain ⟨y1, y2⟩ := one b₁ h1 (cc1 X hX)
          obtain ⟨e1, e2⟩ := ih _ y1 (by rw [y2]; simp at hXi; omega)
          refine ⟨?_, by simpa using e2⟩
          have := (cc1 X hX).1
          rw [costIn_cons]
          simp only [↓reduceIte, List.length_cons]
          rw [cost_seq, cost_inc, Nat.succ_mul]
          omega
    have hs1 : ∀ r', (update s.regs i 0) r' ≤ B := by
      intro r'; by_cases h' : r' = i
      · subst h'; simp
      · simp [update_of_ne h', hB r']
    obtain ⟨t1, t2⟩ := it w ⟨update s.regs i 0, s.out⟩ hs1 (by simp [hw])
    have hcost : cost w (comp (.bits i b₀ b₁)) s = s.regs i + 1 + (2 * (w.length + 1) + 1 +
        costIn (cost w (.seq (comp b₀) (.inc i))) (cost w (.seq (comp b₁) (.inc i)))
          (run w (.seq (comp b₀) (.inc i))) (run w (.seq (comp b₁) (.inc i))) w
          ⟨update s.regs i 0, s.out⟩) := by
      show cost w (.seq (.clr i) (.forIn (.seq (comp b₀) (.inc i)) (.seq (comp b₁) (.inc i)))) s = _
      rw [cost_seq, cost_clr, cost_forIn]
      rfl
    have hrun : run w (comp (.bits i b₀ b₁)) s = w.foldl (fun s b => if b then
        run w (.seq (comp b₁) (.inc i)) s else run w (.seq (comp b₀) (.inc i)) s)
          ⟨update s.regs i 0, s.out⟩ := rfl
    rw [hcost, hrun]
    simp only [cb]
    refine ⟨?_, t2⟩
    have := hB i
    have : w.length * (cb b₀ B + cb b₁ B + 3) ≤ B * (cb b₀ B + cb b₁ B + 3) :=
      Nat.mul_le_mul_right _ hw
    omega

open Polynomial in
/-- `litC` como polinômio em `B`. -/
noncomputable def litCP (l : LT V R) : Polynomial ℕ :=
  C (2 * l.a + 4 + 3 * l.tt.1.length + 2 * l.tt.2 + 2 + 3 * l.pt.1.length + 2 * l.pt.2 + 2 + 2) +
    C (6 * (l.tt.1.length + l.pt.1.length)) * X

open Polynomial in
/-- `cb` como polinômio em `B`. -/
noncomputable def cbP : FT V R → Polynomial ℕ
  | .nil => 0
  | .cl lits => (lits.map litCP).sum + 2
  | .cat a b => cbP a + cbP b
  | .rng _ _ body => 3 * X + 4 + X * (cbP body + 3)
  | .bits _ b₀ b₁ => 3 * X + 4 + X * (cbP b₀ + cbP b₁ + 3)

theorem eval_litCP (l : LT V R) (B : ℕ) : (litCP l).eval B = litC l B := by
  simp only [litCP, litC, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X]
  ring

theorem eval_cbP (B : ℕ) : ∀ ft : FT V R, (cbP ft).eval B = cb ft B
  | .nil => by simp [cbP, cb]
  | .cl lits => by
    have e : ∀ ls : List (LT V R), (ls.map litCP).sum.eval B = (ls.map (litC · B)).sum := by
      intro ls
      induction ls with
      | nil => simp
      | cons l ls ih => simp [Polynomial.eval_add, eval_litCP, ih]
    simp only [cbP, cb, Polynomial.eval_add, e]
    simp
  | .cat a b => by simp [cbP, cb, eval_cbP B a, eval_cbP B b]
  | .rng _ _ body => by simp [cbP, cb, eval_cbP B body]
  | .bits _ b₀ b₁ => by simp [cbP, cb, eval_cbP B b₀, eval_cbP B b₁]

end CustoMoldes

end Moldes

end ATK.Gerador

#print axioms ATK.Gerador.outs
#print axioms ATK.Gerador.run_outs
#print axioms ATK.Gerador.seqs
#print axioms ATK.Gerador.run_seqs_puro
#print axioms ATK.Gerador.sb
#print axioms ATK.Gerador.unS
#print axioms ATK.Gerador.UT
#print axioms ATK.Gerador.val
#print axioms ATK.Gerador.dup
#print axioms ATK.Gerador.run_dup
#print axioms ATK.Gerador.emitU
#print axioms ATK.Gerador.flatMap_rep
#print axioms ATK.Gerador.run_emitU
#print axioms ATK.Gerador.litOut
#print axioms ATK.Gerador.LT
#print axioms ATK.Gerador.litP
#print axioms ATK.Gerador.run_litP
#print axioms ATK.Gerador.litOutV
#print axioms ATK.Gerador.clOutV
#print axioms ATK.Gerador.fmOutV
#print axioms ATK.Gerador.FT
#print axioms ATK.Gerador.sem
#print axioms ATK.Gerador.comp
#print axioms ATK.Gerador.Insens
#print axioms ATK.Gerador.WF
#print axioms ATK.Gerador.fmOutV_append
#print axioms ATK.Gerador.sem_insens
#print axioms ATK.Gerador.comp_ok
#print axioms ATK.Gerador.cost_seq
#print axioms ATK.Gerador.cost_loop
#print axioms ATK.Gerador.cost_forIn
#print axioms ATK.Gerador.cost_clr
#print axioms ATK.Gerador.cost_inc
#print axioms ATK.Gerador.costIt_succ
#print axioms ATK.Gerador.costIn_cons
#print axioms ATK.Gerador.cost_outs
#print axioms ATK.Gerador.costIt_const
#print axioms ATK.Gerador.cost_dup
#print axioms ATK.Gerador.cost_seqs_le
#print axioms ATK.Gerador.cost_emitU_le
#print axioms ATK.Gerador.litC
#print axioms ATK.Gerador.cost_litP_le
#print axioms ATK.Gerador.cb
#print axioms ATK.Gerador.comp_cost
#print axioms ATK.Gerador.eval_litCP
#print axioms ATK.Gerador.eval_cbP
