import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Fintype.Sum

/-!
# ATK — Cook–Levin, marco CL4b-1: uma linguagem de laços compilada para máquina de pilhas

Para escrever a fórmula de Cook–Levin por uma `FinTM2`, em vez de uma máquina feita à mão, uma
linguagem pequena:

* `Prog R`: `out b` (escreve um bit), `inc`/`dec`/`clr` (contadores unários `r : R`), `seq`,
  `loop r p` (repete `p` tantas vezes quanto o valor de `r` no início), `forIn p₀ p₁` (para cada bit
  da entrada, `p₀` ou `p₁`);
* `run w p`: a semântica (registros e saída); `cost w p`: o número de passos da máquina;
* `asm`: o montador (endereços absolutos); `prog`: a máquina de pilhas (`TM2`) de um código;
* **`asm_ok`**: rodar o código montado de `p` leva, em no máximo `cost w p s` passos, do estado `s`
  ao estado `run w p s`.

**Nada aqui prova Cook–Levin. CLOSED_MATH continua false.**
-/

namespace ATK.Gerador

set_option linter.unusedSectionVars false

open Turing Function

/-! ### A linguagem -/

/-- Programas com contadores `R`. -/
inductive Prog (R : Type) where
  | skip
  | out (b : Bool)
  | inc (r : R)
  | dec (r : R)
  | clr (r : R)
  | seq (p q : Prog R)
  | loop (r : R) (p : Prog R)
  | forIn (p₀ p₁ : Prog R)

/-- Estado: valores dos contadores e a saída escrita. -/
structure St (R : Type) where
  regs : R → ℕ
  out : List Bool

variable {R : Type} [DecidableEq R]

/-- Semântica, com a entrada `w`. -/
def run (w : List Bool) : Prog R → St R → St R
  | .skip, s => s
  | .out b, s => ⟨s.regs, s.out ++ [b]⟩
  | .inc r, s => ⟨update s.regs r (s.regs r + 1), s.out⟩
  | .dec r, s => ⟨update s.regs r (s.regs r - 1), s.out⟩
  | .clr r, s => ⟨update s.regs r 0, s.out⟩
  | .seq p q, s => run w q (run w p s)
  | .loop r p, s => (run w p)^[s.regs r] s
  | .forIn p₀ p₁, s => w.foldl (fun s b => if b then run w p₁ s else run w p₀ s) s

/-- Custo de iterar `n` vezes um corpo de custo `c` e efeito `f` (mais 2 passos por volta). -/
def costIt {α : Type} (c : α → ℕ) (f : α → α) : ℕ → α → ℕ
  | 0, _ => 0
  | n + 1, s => c s + 2 + costIt c f n (f s)

/-- Custo de percorrer os bits `bs`. -/
def costIn {α : Type} (c₀ c₁ : α → ℕ) (f₀ f₁ : α → α) : List Bool → α → ℕ
  | [], _ => 0
  | b :: bs, s => (if b then c₁ s else c₀ s) + 2 + costIn c₀ c₁ f₀ f₁ bs (if b then f₁ s else f₀ s)

/-- O número de passos da máquina. -/
def cost (w : List Bool) : Prog R → St R → ℕ
  | .skip, _ => 0
  | .out _, _ => 1
  | .inc _, _ => 1
  | .dec _, _ => 1
  | .clr r, s => s.regs r + 1
  | .seq p q, s => cost w p s + cost w q (run w p s)
  | .loop r p, s => 2 * (s.regs r + 1) + 1 + costIt (cost w p) (run w p) (s.regs r) s
  | .forIn p₀ p₁, s => 2 * (w.length + 1) + 1 +
      costIn (cost w p₀) (cost w p₁) (run w p₀) (run w p₁) w s

/-- Tamanho do código montado. -/
def size : Prog R → ℕ
  | .skip => 0
  | .out _ => 1
  | .inc _ => 1
  | .dec _ => 1
  | .clr _ => 1
  | .seq p q => size p + size q
  | .loop _ p => size p + 4
  | .forIn p₀ p₁ => size p₀ + size p₁ + 5

/-- Profundidade de laços aninhados. -/
def depth : Prog R → ℕ
  | .seq p q => max (depth p) (depth q)
  | .loop _ p => depth p + 1
  | .forIn p₀ p₁ => max (depth p₀) (depth p₁) + 1
  | _ => 0

/-! ### As pilhas da máquina -/

/-- Pilhas fixas: entrada, saída, trabalho (saída invertida), temporárias. -/
inductive Base where
  | inp | outp | wrk | tu | tb
  deriving DecidableEq

instance : Fintype Base :=
  ⟨{.inp, .outp, .wrk, .tu, .tb}, by intro x; cases x <;> simp⟩

/-- As pilhas: fixas, contadores, e uma pilha escondida (unária e de bits) por nível de laço. -/
abbrev Pk (R : Type) (D : ℕ) := Base ⊕ R ⊕ Fin (D + 1) ⊕ Fin (D + 1)

namespace Pk
variable {D : ℕ}
abbrev inp : Pk R D := .inl .inp
abbrev outp : Pk R D := .inl .outp
abbrev wrk : Pk R D := .inl .wrk
abbrev tu : Pk R D := .inl .tu
abbrev tb : Pk R D := .inl .tb
abbrev reg (r : R) : Pk R D := .inr (.inl r)
abbrev hu (i : Fin (D + 1)) : Pk R D := .inr (.inr (.inl i))
abbrev hb (i : Fin (D + 1)) : Pk R D := .inr (.inr (.inr i))
end Pk

/-- O nível `ℓ` como índice de pilha escondida. -/
def nv (D ℓ : ℕ) : Fin (D + 1) := ⟨min ℓ D, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-! ### Instruções e montador -/

/-- Instruções da máquina; cada uma é um rótulo da `TM2` e roda em um passo por volta. -/
inductive Ins (κ : Type) where
  | push (k : κ) (b : Bool)
  | pop1 (k : κ)
  | clr (k : κ)
  | mv (s d : κ)
  | mv2 (s d₁ d₂ : κ)
  | jmp (a : ℕ)
  | lhead (h : κ) (e : ℕ)
  | ihead (h : κ) (a₁ e : ℕ)
  | halt

/-- O montador: código de `p` a partir do endereço `a`, no nível `ℓ`. -/
def asm (D : ℕ) : Prog R → ℕ → ℕ → List (Ins (Pk R D))
  | .skip, _, _ => []
  | .out b, _, _ => [.push Pk.wrk b]
  | .inc r, _, _ => [.push (Pk.reg r) true]
  | .dec r, _, _ => [.pop1 (Pk.reg r)]
  | .clr r, _, _ => [.clr (Pk.reg r)]
  | .seq p q, a, ℓ => asm D p a ℓ ++ asm D q (a + size p) ℓ
  | .loop r p, a, ℓ =>
      [.mv2 (Pk.reg r) Pk.tu (Pk.hu (nv D ℓ)), .mv Pk.tu (Pk.reg r),
        .lhead (Pk.hu (nv D ℓ)) (a + 4 + size p)] ++ asm D p (a + 3) (ℓ + 1) ++ [.jmp (a + 2)]
  | .forIn p₀ p₁, a, ℓ =>
      [.mv Pk.inp Pk.tb, .mv2 Pk.tb Pk.inp (Pk.hb (nv D ℓ)),
        .ihead (Pk.hb (nv D ℓ)) (a + 4 + size p₀) (a + 5 + size p₀ + size p₁)] ++
        asm D p₀ (a + 3) (ℓ + 1) ++ [.jmp (a + 2)] ++ asm D p₁ (a + 4 + size p₀) (ℓ + 1) ++
        [.jmp (a + 2)]

omit [DecidableEq R] in
theorem length_asm (D : ℕ) : ∀ (p : Prog R) (a ℓ : ℕ), (asm D p a ℓ).length = size p
  | .skip, _, _ => rfl
  | .out _, _, _ => rfl
  | .inc _, _, _ => rfl
  | .dec _, _, _ => rfl
  | .clr _, _, _ => rfl
  | .seq p q, a, ℓ => by simp [asm, size, length_asm D p, length_asm D q]
  | .loop _ p, a, ℓ => by simp [asm, size, length_asm D p]
  | .forIn p₀ p₁, a, ℓ => by simp [asm, size, length_asm D p₀, length_asm D p₁]; omega

/-! ### A máquina de um código -/

/-- Rótulos: endereços `0..N`. -/
def lab (N a : ℕ) : Fin (N + 1) := ⟨min a N, Nat.lt_succ_of_le (min_le_right _ _)⟩

variable {κ : Type} [DecidableEq κ]

/-- A instrução no endereço `a` como instrução `TM2` (estado: um bit). -/
def stmt (N a : ℕ) : Ins κ → TM2.Stmt (fun _ : κ => Bool) (Fin (N + 1)) Bool
  | .push k b => .push k (fun _ => b) (.goto fun _ => lab N (a + 1))
  | .pop1 k => .pop k (fun v _ => v) (.goto fun _ => lab N (a + 1))
  | .clr k => .peek k (fun _ o => o.isSome)
      (.branch id (.pop k (fun v _ => v) (.goto fun _ => lab N a)) (.goto fun _ => lab N (a + 1)))
  | .mv s d => .peek s (fun _ o => o.isSome)
      (.branch id (.pop s (fun _ o => o.getD false) (.push d id (.goto fun _ => lab N a)))
        (.goto fun _ => lab N (a + 1)))
  | .mv2 s d₁ d₂ => .peek s (fun _ o => o.isSome)
      (.branch id (.pop s (fun _ o => o.getD false) (.push d₁ id (.push d₂ id
        (.goto fun _ => lab N a)))) (.goto fun _ => lab N (a + 1)))
  | .jmp t => .goto fun _ => lab N t
  | .lhead h e => .peek h (fun _ o => o.isSome)
      (.branch id (.pop h (fun v _ => v) (.goto fun _ => lab N (a + 1))) (.goto fun _ => lab N e))
  | .ihead h a₁ e => .peek h (fun _ o => o.isSome)
      (.branch id (.pop h (fun _ o => o.getD false)
        (.branch id (.goto fun _ => lab N a₁) (.goto fun _ => lab N (a + 1))))
        (.goto fun _ => lab N e))
  | .halt => .load (fun _ => false) .halt

/-- O programa `TM2` de um código. -/
def prog (code : List (Ins κ)) : Fin (code.length + 1) → TM2.Stmt (fun _ : κ => Bool)
    (Fin (code.length + 1)) Bool :=
  fun a => match code[a.val]? with
    | some i => stmt code.length a.val i
    | none => .load (fun _ => false) .halt

/-- Configuração no endereço `a`. -/
def cfg (code : List (Ins κ)) (a : ℕ) (v : Bool) (S : κ → List Bool) :
    TM2.Cfg (fun _ : κ => Bool) (Fin (code.length + 1)) Bool :=
  ⟨some (lab code.length a), v, S⟩

/-- Alcançar em no máximo `n` passos. -/
def Reach {α : Type*} (f : α → Option α) (c c' : α) (n : ℕ) : Prop :=
  ∃ k ≤ n, (flip bind f)^[k] (some c) = some c'

namespace Reach
variable {α : Type*} {f : α → Option α}

theorem refl (c : α) : Reach f c c 0 := ⟨0, le_refl _, rfl⟩

theorem mono {c c' : α} {n m : ℕ} (h : Reach f c c' n) (hnm : n ≤ m) : Reach f c c' m :=
  let ⟨k, hk, he⟩ := h; ⟨k, hk.trans hnm, he⟩

theorem trans {c c' c'' : α} {n m : ℕ} (h1 : Reach f c c' n) (h2 : Reach f c' c'' m) :
    Reach f c c'' (n + m) := by
  obtain ⟨k1, hk1, e1⟩ := h1
  obtain ⟨k2, hk2, e2⟩ := h2
  exact ⟨k2 + k1, by omega, by rw [iterate_add_apply, e1, e2]⟩

theorem one {c c' : α} (h : f c = some c') : Reach f c c' 1 := ⟨1, le_refl _, h⟩

theorem cons {c c' c'' : α} {n : ℕ} (h : f c = some c') (h2 : Reach f c' c'' n) :
    Reach f c c'' (n + 1) :=
  ((one h).trans h2).mono (by omega)

end Reach

/-! ### Um passo por instrução -/

variable {code : List (Ins κ)}

theorem lab_val {N a : ℕ} (h : a ≤ N) : (lab N a).val = a := by simp [lab, h]

theorem step_at {a : ℕ} {i : Ins κ} (h : code[a]? = some i) (v : Bool) (S : κ → List Bool) :
    TM2.step (prog code) (cfg code a v S) = some (TM2.stepAux (stmt code.length a i) v S) := by
  have ha : a < code.length := by
    by_contra h'
    rw [List.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)
  simp only [cfg, TM2.step, prog, lab_val ha.le, h]

theorem push_ok {a : ℕ} {k : κ} {b : Bool} (h : code[a]? = some (.push k b)) (v : Bool)
    (S : κ → List Bool) :
    Reach (TM2.step (prog code)) (cfg code a v S) (cfg code (a + 1) v (update S k (b :: S k))) 1 :=
  Reach.one (by rw [step_at h]; simp [stmt, TM2.stepAux, cfg])

theorem pop1_ok {a : ℕ} {k : κ} (h : code[a]? = some (.pop1 k)) (v : Bool)
    (S : κ → List Bool) :
    Reach (TM2.step (prog code)) (cfg code a v S) (cfg code (a + 1) v (update S k (S k).tail)) 1 :=
  Reach.one (by rw [step_at h]; simp [stmt, TM2.stepAux, cfg])

theorem jmp_ok {a t : ℕ} (h : code[a]? = some (.jmp t)) (v : Bool) (S : κ → List Bool) :
    Reach (TM2.step (prog code)) (cfg code a v S) (cfg code t v S) 1 :=
  Reach.one (by rw [step_at h]; simp [stmt, TM2.stepAux, cfg])

theorem clr_ok {a : ℕ} {k : κ} (h : code[a]? = some (.clr k)) :
    ∀ (l : List Bool) (v : Bool) (S : κ → List Bool), S k = l →
    Reach (TM2.step (prog code)) (cfg code a v S) (cfg code (a + 1) false (update S k []))
      (l.length + 1)
  | [], v, S, hS => by
    have e : update S k [] = S := by rw [← hS, update_eq_self]
    rw [e]
    exact Reach.one (by rw [step_at h]; simp [stmt, TM2.stepAux, cfg, hS])
  | x :: l, v, S, hS => by
    have := clr_ok h l true (update S k l) (by simp)
    simp only [update_idem] at this
    refine Reach.cons ?_ this
    rw [step_at h]
    simp [stmt, TM2.stepAux, cfg, hS]

theorem mv_ok {a : ℕ} {s d : κ} (hsd : s ≠ d) (h : code[a]? = some (.mv s d)) :
    ∀ (l : List Bool) (v : Bool) (S : κ → List Bool), S s = l →
    Reach (TM2.step (prog code)) (cfg code a v S)
      (cfg code (a + 1) false (update (update S s []) d (l.reverse ++ S d))) (l.length + 1)
  | [], v, S, hS => by
    have e : update (update S s []) d (([] : List Bool).reverse ++ S d) = S := by
      funext k
      by_cases hk : k = d
      · subst hk; simp
      · by_cases hk' : k = s
        · subst hk'; simp [hk, hS]
        · simp [hk, hk']
    rw [e]
    exact Reach.one (by rw [step_at h]; simp [stmt, TM2.stepAux, cfg, hS])
  | x :: l, v, S, hS => by
    have := mv_ok hsd h l x (update (update S s l) d (x :: S d))
      (by simp [update_of_ne hsd])
    have e : update (update (update (update S s l) d (x :: S d)) s []) d
        (l.reverse ++ update (update S s l) d (x :: S d) d) =
        update (update S s []) d ((x :: l).reverse ++ S d) := by
      funext k
      by_cases hk : k = d
      · subst hk; simp
      · by_cases hk' : k = s
        · subst hk'; simp [hk]
        · simp [hk, hk']
    rw [e] at this
    refine (Reach.cons ?_ this).mono (by simp)
    rw [step_at h]
    simp [stmt, TM2.stepAux, cfg, hS, update_of_ne (Ne.symm hsd)]

theorem mv2_ok {a : ℕ} {s d₁ d₂ : κ} (h1 : s ≠ d₁) (h2 : s ≠ d₂) (h12 : d₁ ≠ d₂)
    (h : code[a]? = some (.mv2 s d₁ d₂)) :
    ∀ (l : List Bool) (v : Bool) (S : κ → List Bool), S s = l →
    Reach (TM2.step (prog code)) (cfg code a v S)
      (cfg code (a + 1) false (update (update (update S s []) d₁ (l.reverse ++ S d₁)) d₂
        (l.reverse ++ S d₂))) (l.length + 1)
  | [], v, S, hS => by
    have e : update (update (update S s []) d₁ (([] : List Bool).reverse ++ S d₁)) d₂
        (([] : List Bool).reverse ++ S d₂) = S := by
      funext k
      by_cases hk : k = d₂
      · subst hk; simp
      · by_cases hk1 : k = d₁
        · subst hk1; simp [hk]
        · by_cases hk' : k = s
          · subst hk'; simp [hk, hk1, hS]
          · simp [hk, hk1, hk']
    rw [e]
    exact Reach.one (by rw [step_at h]; simp [stmt, TM2.stepAux, cfg, hS])
  | x :: l, v, S, hS => by
    have := mv2_ok h1 h2 h12 h l x
      (update (update (update S s l) d₁ (x :: S d₁)) d₂ (x :: S d₂))
      (by simp [update_of_ne h1, update_of_ne h2])
    have e : update (update (update (update (update (update S s l) d₁ (x :: S d₁)) d₂
        (x :: S d₂)) s []) d₁ (l.reverse ++ update (update (update S s l) d₁ (x :: S d₁)) d₂
        (x :: S d₂) d₁)) d₂ (l.reverse ++ update (update (update S s l) d₁ (x :: S d₁)) d₂
        (x :: S d₂) d₂) =
        update (update (update S s []) d₁ ((x :: l).reverse ++ S d₁)) d₂
          ((x :: l).reverse ++ S d₂) := by
      funext k
      by_cases hk : k = d₂
      · subst hk; simp
      · by_cases hk1 : k = d₁
        · subst hk1; simp [hk]
        · by_cases hk' : k = s
          · subst hk'; simp [hk, hk1]
          · simp [hk, hk1, hk']
    rw [e] at this
    refine (Reach.cons ?_ this).mono (by simp)
    rw [step_at h]
    have q1 : update S s l d₁ = S d₁ := update_of_ne (Ne.symm h1) _ _
    have q2 : update S s l d₂ = S d₂ := update_of_ne (Ne.symm h2) _ _
    have q3 : update (update S s l) d₁ (x :: S d₁) d₂ = S d₂ := by
      rw [update_of_ne (Ne.symm h12), q2]
    simp [stmt, TM2.stepAux, cfg, hS, q1, q3]

theorem lhead_nil {a e : ℕ} {hk : κ} (h : code[a]? = some (.lhead hk e)) (v : Bool)
    (S : κ → List Bool) (hS : S hk = []) :
    Reach (TM2.step (prog code)) (cfg code a v S) (cfg code e false S) 1 :=
  Reach.one (by rw [step_at h]; simp [stmt, TM2.stepAux, cfg, hS])

theorem lhead_cons {a e : ℕ} {hk : κ} (h : code[a]? = some (.lhead hk e)) (v : Bool)
    (S : κ → List Bool) (x : Bool) (l : List Bool) (hS : S hk = x :: l) :
    Reach (TM2.step (prog code)) (cfg code a v S) (cfg code (a + 1) true (update S hk l)) 1 :=
  Reach.one (by rw [step_at h]; simp [stmt, TM2.stepAux, cfg, hS])

theorem ihead_nil {a a₁ e : ℕ} {hk : κ} (h : code[a]? = some (.ihead hk a₁ e)) (v : Bool)
    (S : κ → List Bool) (hS : S hk = []) :
    Reach (TM2.step (prog code)) (cfg code a v S) (cfg code e false S) 1 :=
  Reach.one (by rw [step_at h]; simp [stmt, TM2.stepAux, cfg, hS])

theorem ihead_cons {a a₁ e : ℕ} {hk : κ} (h : code[a]? = some (.ihead hk a₁ e)) (v : Bool)
    (S : κ → List Bool) (b : Bool) (l : List Bool) (hS : S hk = b :: l) :
    Reach (TM2.step (prog code)) (cfg code a v S)
      (cfg code (if b then a₁ else a + 1) b (update S hk l)) 1 :=
  Reach.one (by rw [step_at h]; cases b <;> simp [stmt, TM2.stepAux, cfg, hS])

/-! ### O estado nas pilhas -/

section Estado

variable {D : ℕ}

/-- O estado lido das pilhas: contadores (comprimentos) e saída (pilha de trabalho invertida). -/
def stOf (S : Pk R D → List Bool) : St R := ⟨fun r => (S (Pk.reg r)).length, (S Pk.wrk).reverse⟩

/-- As pilhas com o estado `s` escrito nos contadores e na saída. -/
def put (S : Pk R D → List Bool) (s : St R) : Pk R D → List Bool
  | .inr (.inl r) => List.replicate (s.regs r) true
  | .inl .wrk => s.out.reverse
  | .inl .inp => S Pk.inp
  | .inl .outp => S Pk.outp
  | .inl .tu => S Pk.tu
  | .inl .tb => S Pk.tb
  | .inr (.inr k) => S (.inr (.inr k))

/-- O invariante entre instruções, no nível `ℓ`. -/
structure Inv (ℓ : ℕ) (w : List Bool) (S : Pk R D → List Bool) : Prop where
  inp : S Pk.inp = w
  tu : S Pk.tu = []
  tb : S Pk.tb = []
  regs : ∀ r, S (Pk.reg r) = List.replicate (S (Pk.reg r)).length true
  hid : ∀ i : Fin (D + 1), ℓ ≤ i.val → S (Pk.hu i) = [] ∧ S (Pk.hb i) = []

theorem put_stOf {ℓ : ℕ} {w : List Bool} {S : Pk R D → List Bool} (h : Inv ℓ w S) :
    put S (stOf S) = S := by
  funext k
  rcases k with b | r | i | i
  · cases b <;> simp [put, stOf]
  · exact (h.regs r).symm
  · rfl
  · rfl

theorem stOf_put (S : Pk R D → List Bool) (s : St R) : stOf (put S s) = s := by
  cases s; simp [stOf, put]

theorem put_put (S : Pk R D → List Bool) (s s' : St R) : put (put S s) s' = put S s' := by
  funext k
  rcases k with b | r | i | i
  · cases b <;> rfl
  · rfl
  · rfl
  · rfl

theorem inv_put {ℓ : ℕ} {w : List Bool} {S : Pk R D → List Bool} (h : Inv ℓ w S) (s : St R) :
    Inv ℓ w (put S s) :=
  ⟨h.inp, h.tu, h.tb, fun r => by simp [put], fun i hi => h.hid i hi⟩

theorem put_upd_hu (S : Pk R D → List Bool) (s : St R) (i : Fin (D + 1)) (l : List Bool) :
    put (update S (Pk.hu i) l) s = update (put S s) (Pk.hu i) l := by
  funext k
  rcases k with b | r | j | j
  · cases b <;> simp [put]
  · simp [put]
  · by_cases hj : j = i
    · subst hj; simp [put]
    · simp [put, hj]
  · simp [put]

theorem put_upd_hb (S : Pk R D → List Bool) (s : St R) (i : Fin (D + 1)) (l : List Bool) :
    put (update S (Pk.hb i) l) s = update (put S s) (Pk.hb i) l := by
  funext k
  rcases k with b | r | j | j
  · cases b <;> simp [put]
  · simp [put]
  · simp [put]
  · by_cases hj : j = i
    · subst hj; simp [put]
    · simp [put, hj]

theorem stOf_upd_hu (S : Pk R D → List Bool) (i : Fin (D + 1)) (l : List Bool) :
    stOf (update S (Pk.hu i) l) = stOf S := by
  simp [stOf]

theorem stOf_upd_hb (S : Pk R D → List Bool) (i : Fin (D + 1)) (l : List Bool) :
    stOf (update S (Pk.hb i) l) = stOf S := by
  simp [stOf]

theorem inv_upd_hu {ℓ : ℕ} {w : List Bool} {S : Pk R D → List Bool} (h : Inv ℓ w S)
    (i : Fin (D + 1)) (hi : i.val = ℓ) (l : List Bool) : Inv (ℓ + 1) w (update S (Pk.hu i) l) := by
  refine ⟨by simp [h.inp], by simp [h.tu], by simp [h.tb], fun r => by simpa using h.regs r,
    fun j hj => ?_⟩
  have hne : j ≠ i := by intro e; subst e; omega
  simp [hne, (h.hid j (by omega)).1, (h.hid j (by omega)).2]

theorem inv_upd_hb {ℓ : ℕ} {w : List Bool} {S : Pk R D → List Bool} (h : Inv ℓ w S)
    (i : Fin (D + 1)) (hi : i.val = ℓ) (l : List Bool) : Inv (ℓ + 1) w (update S (Pk.hb i) l) := by
  refine ⟨by simp [h.inp], by simp [h.tu], by simp [h.tb], fun r => by simpa using h.regs r,
    fun j hj => ?_⟩
  have hne : j ≠ i := by intro e; subst e; omega
  simp [hne, (h.hid j (by omega)).1, (h.hid j (by omega)).2]

/-- O código `P` está no endereço `a`. -/
def Loc (code : List (Ins κ)) (a : ℕ) (P : List (Ins κ)) : Prop :=
  ∀ i (h : i < P.length), code[a + i]? = some P[i]

theorem Loc.left {code : List (Ins κ)} {a : ℕ} {P Q : List (Ins κ)} (h : Loc code a (P ++ Q)) :
    Loc code a P := fun i hi => by
  have := h i (by simp; omega)
  rwa [List.getElem_append_left hi] at this

theorem Loc.right {code : List (Ins κ)} {a : ℕ} {P Q : List (Ins κ)} (h : Loc code a (P ++ Q)) :
    Loc code (a + P.length) Q := fun i hi => by
  have := h (P.length + i) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa [Nat.add_assoc] using this

theorem Loc.at {code : List (Ins κ)} {a : ℕ} {P : List (Ins κ)} (h : Loc code a P) {i : ℕ}
    (hi : i < P.length) : code[a + i]? = some P[i] := h i hi

theorem Loc.atE {code : List (Ins κ)} {a : ℕ} {P : List (Ins κ)} (h : Loc code a P) {i b : ℕ}
    (hi : i < P.length) (hb : a + i = b) : code[b]? = some P[i] := hb ▸ h i hi

theorem Loc.shift {code : List (Ins κ)} {a b : ℕ} {P : List (Ins κ)} (h : Loc code a P)
    (e : a = b) : Loc code b P := e ▸ h

theorem put_out {ℓ : ℕ} {w : List Bool} {S : Pk R D → List Bool} (h : Inv ℓ w S) (b : Bool) :
    put S ⟨(stOf S).regs, (stOf S).out ++ [b]⟩ = update S Pk.wrk (b :: S Pk.wrk) := by
  funext k
  rcases k with c | r | j | j
  · cases c <;> simp [put, stOf]
  · simpa [put, stOf] using (h.regs r).symm
  · rfl
  · rfl

theorem put_reg {ℓ : ℕ} {w : List Bool} {S : Pk R D → List Bool} (h : Inv ℓ w S) (r : R) (m : ℕ) :
    put S ⟨update (stOf S).regs r m, (stOf S).out⟩ = update S (Pk.reg r) (List.replicate m true) := by
  funext k
  rcases k with c | r' | j | j
  · cases c <;> simp [put, stOf]
  · by_cases hr : r' = r
    · subst hr; simp [put]
    · simpa [put, stOf, hr] using (h.regs r').symm
  · rfl
  · rfl

end Estado

/-! ### Correção do montador -/

section Correcao

variable {D : ℕ}

theorem depth_le_left {ℓ : ℕ} {p q : Prog R} (h : ℓ + depth (.seq p q) ≤ D) : ℓ + depth p ≤ D :=
  (Nat.add_le_add_left (le_max_left _ _) ℓ).trans h

theorem depth_le_right {ℓ : ℕ} {p q : Prog R} (h : ℓ + depth (.seq p q) ≤ D) : ℓ + depth q ≤ D :=
  (Nat.add_le_add_left (le_max_right _ _) ℓ).trans h

/-- **Correção do montador.** O código de `p` leva, em no máximo `cost w p s` passos, do estado
`s` (lido das pilhas) ao estado `run w p s`, sem tocar a entrada nem as pilhas dos laços externos. -/
theorem asm_ok (code : List (Ins (Pk R D))) (w : List Bool) :
    ∀ (p : Prog R) (a ℓ : ℕ) (S : Pk R D → List Bool) (v : Bool),
      Loc code a (asm D p a ℓ) → ℓ + depth p ≤ D → Inv ℓ w S →
      ∃ v', Reach (TM2.step (prog code)) (cfg code a v S)
        (cfg code (a + size p) v' (put S (run w p (stOf S)))) (cost w p (stOf S))
  | .skip, a, ℓ, S, v, _, _, h => ⟨v, by simpa [size, run, cost, put_stOf h] using Reach.refl _⟩
  | .out b, a, ℓ, S, v, hL, _, h => by
    have hc : code[a]? = some (.push Pk.wrk b) := by simpa [asm] using hL.at (i := 0) (by simp [asm])
    refine ⟨v, ?_⟩
    simp only [run, size, cost]
    rw [put_out h b]
    exact push_ok hc v S
  | .inc r, a, ℓ, S, v, hL, _, h => by
    have hc : code[a]? = some (.push (Pk.reg r) true) := by
      simpa [asm] using hL.at (i := 0) (by simp [asm])
    obtain ⟨n, hn⟩ : ∃ n, S (Pk.reg r) = List.replicate n true := ⟨_, h.regs r⟩
    refine ⟨v, ?_⟩
    simp only [run, size, cost]
    rw [put_reg h]
    have e : (stOf S).regs r + 1 = n + 1 := by simp [stOf, hn]
    rw [e, List.replicate_succ, ← hn]
    exact push_ok hc v S
  | .dec r, a, ℓ, S, v, hL, _, h => by
    have hc : code[a]? = some (.pop1 (Pk.reg r)) := by
      simpa [asm] using hL.at (i := 0) (by simp [asm])
    obtain ⟨n, hn⟩ : ∃ n, S (Pk.reg r) = List.replicate n true := ⟨_, h.regs r⟩
    refine ⟨v, ?_⟩
    simp only [run, size, cost]
    rw [put_reg h]
    have e : (stOf S).regs r - 1 = n - 1 := by simp [stOf, hn]
    rw [e, ← List.tail_replicate, ← hn]
    exact pop1_ok hc v S
  | .clr r, a, ℓ, S, v, hL, _, h => by
    have hc : code[a]? = some (.clr (Pk.reg r)) := by
      simpa [asm] using hL.at (i := 0) (by simp [asm])
    refine ⟨false, ?_⟩
    simp only [run, size, cost]
    rw [put_reg h, List.replicate_zero]
    exact clr_ok hc _ v S rfl
  | .seq p q, a, ℓ, S, v, hL, hd, h => by
    simp only [asm] at hL
    obtain ⟨v1, h1⟩ := asm_ok code w p a ℓ S v hL.left (depth_le_left hd) h
    have hL2 := hL.right
    rw [length_asm] at hL2
    obtain ⟨v2, h2⟩ := asm_ok code w q (a + size p) ℓ _ v1 hL2 (depth_le_right hd) (inv_put h _)
    refine ⟨v2, ?_⟩
    rw [stOf_put, put_put] at h2
    simpa [size, run, cost, Nat.add_assoc] using h1.trans h2
  | .loop r p, a, ℓ, S, v, hL, hd, h => by
    simp only [depth] at hd
    have hiv : (nv D ℓ).val = ℓ := by simp [nv]; omega
    simp only [asm] at hL
    have c0 : code[a]? = some (.mv2 (Pk.reg r) Pk.tu (Pk.hu (nv D ℓ))) := by
      simpa using hL.left.left.at (i := 0) (by simp)
    have c1 : code[a + 1]? = some (.mv Pk.tu (Pk.reg r)) := by
      simpa using hL.left.left.at (i := 1) (by simp)
    have c2 : code[a + 2]? = some (.lhead (Pk.hu (nv D ℓ)) (a + 4 + size p)) := by
      simpa using hL.left.left.at (i := 2) (by simp)
    have hLb : Loc code (a + 3) (asm D p (a + 3) (ℓ + 1)) :=
      hL.left.right.shift (by simp)
    have cj : code[a + 3 + size p]? = some (.jmp (a + 2)) := by
      simpa using hL.right.atE (i := 0) (by simp) (by simp [length_asm]; omega)
    obtain ⟨n, hn⟩ : ∃ n, S (Pk.reg r) = List.replicate n true := ⟨_, h.regs r⟩
    have hrn : (stOf S).regs r = n := by simp [stOf, hn]
    have hhu := (h.hid (nv D ℓ) (by omega)).1
    -- o laço: invariante
    have inv : ∀ (j : ℕ) (s' : St R) (v0 : Bool), ∃ v', Reach (TM2.step (prog code))
        (cfg code (a + 2) v0 (update (put S s') (Pk.hu (nv D ℓ)) (List.replicate j true)))
        (cfg code (a + 4 + size p) v' (put S ((run w p)^[j] s')))
        (costIt (cost w p) (run w p) j s' + 1) := by
      intro j
      induction j with
      | zero =>
        intro s' v0
        have e : update (put S s') (Pk.hu (nv D ℓ)) (List.replicate 0 true) = put S s' := by
          rw [List.replicate_zero]
          exact update_eq_self_iff.mpr hhu.symm
        rw [e]
        exact ⟨false, by simpa [costIt] using lhead_nil c2 v0 (put S s') hhu⟩
      | succ j ih =>
        intro s' v0
        have r1 := lhead_cons c2 v0
          (update (put S s') (Pk.hu (nv D ℓ)) (List.replicate (j + 1) true)) true
          (List.replicate j true) (by simp [List.replicate_succ])
        rw [update_idem] at r1
        have hT := inv_upd_hu (inv_put h s') (nv D ℓ) hiv (List.replicate j true)
        obtain ⟨v1, r2⟩ := asm_ok code w p (a + 3) (ℓ + 1) _ true hLb (by omega) hT
        rw [stOf_upd_hu, stOf_put, put_upd_hu, put_put] at r2
        have r3 := jmp_ok cj v1 (update (put S (run w p s')) (Pk.hu (nv D ℓ))
          (List.replicate j true))
        obtain ⟨v2, r4⟩ := ih (run w p s') v1
        refine ⟨v2, ?_⟩
        rw [iterate_succ_apply]
        exact (((r1.trans r2).trans r3).trans r4).mono (by simp [costIt]; omega)
    -- cópia do contador
    set S1 := update (update (update S (Pk.reg r) []) Pk.tu (List.replicate n true))
      (Pk.hu (nv D ℓ)) (List.replicate n true) with hS1
    have s1 : Reach (TM2.step (prog code)) (cfg code a v S) (cfg code (a + 1) false S1) (n + 1) := by
      have := mv2_ok (s := Pk.reg r) (d₁ := Pk.tu) (d₂ := Pk.hu (nv D ℓ)) (by simp) (by simp)
        (by simp) c0 (S (Pk.reg r)) v S rfl
      rw [hn] at this
      simpa [h.tu, hhu, hS1] using this
    have s2 := mv_ok (s := Pk.tu) (d := Pk.reg r) (by simp) c1 (List.replicate n true) false S1
      (by simp [hS1])
    have eS2 : update (update S1 Pk.tu []) (Pk.reg r) ((List.replicate n true).reverse ++
        S1 (Pk.reg r)) = update (put S (stOf S)) (Pk.hu (nv D ℓ)) (List.replicate n true) := by
      rw [put_stOf h]
      funext k
      by_cases k1 : k = Pk.hu (nv D ℓ)
      · subst k1; simp [hS1]
      · by_cases k2 : k = Pk.reg r
        · subst k2; simp [hS1, hn]
        · by_cases k3 : k = Pk.tu
          · subst k3; simp [hS1, h.tu]
          · simp [hS1, k1, k2, k3]
    rw [eS2] at s2
    obtain ⟨v', rl⟩ := inv n (stOf S) false
    refine ⟨v', ?_⟩
    have tot := (s1.trans s2).trans rl
    simp only [run, size, cost, hrn]
    have e4 : a + (size p + 4) = a + 4 + size p := by omega
    rw [e4]
    refine tot.mono ?_
    simp
    omega
  | .forIn p₀ p₁, a, ℓ, S, v, hL, hd, h => by
    simp only [depth] at hd
    have hiv : (nv D ℓ).val = ℓ := by simp [nv]; omega
    have hd0 : ℓ + 1 + depth p₀ ≤ D := by have := le_max_left (depth p₀) (depth p₁); omega
    have hd1 : ℓ + 1 + depth p₁ ≤ D := by have := le_max_right (depth p₀) (depth p₁); omega
    simp only [asm] at hL
    have c0 : code[a]? = some (.mv Pk.inp Pk.tb) := by
      simpa using hL.left.left.left.left.at (i := 0) (by simp)
    have c1 : code[a + 1]? = some (.mv2 Pk.tb Pk.inp (Pk.hb (nv D ℓ))) := by
      simpa using hL.left.left.left.left.at (i := 1) (by simp)
    have c2 : code[a + 2]? = some (.ihead (Pk.hb (nv D ℓ)) (a + 4 + size p₀)
        (a + 5 + size p₀ + size p₁)) := by
      simpa using hL.left.left.left.left.at (i := 2) (by simp)
    have hL0 : Loc code (a + 3) (asm D p₀ (a + 3) (ℓ + 1)) :=
      hL.left.left.left.right.shift (by simp)
    have cj0 : code[a + 3 + size p₀]? = some (.jmp (a + 2)) := by
      simpa using hL.left.left.right.atE (i := 0) (by simp) (by simp [length_asm]; omega)
    have hL1 : Loc code (a + 4 + size p₀) (asm D p₁ (a + 4 + size p₀) (ℓ + 1)) :=
      hL.left.right.shift (by simp [length_asm]; omega)
    have cj1 : code[a + 4 + size p₀ + size p₁]? = some (.jmp (a + 2)) := by
      simpa using hL.right.atE (i := 0) (by simp) (by simp [length_asm]; omega)
    have hhb := (h.hid (nv D ℓ) (by omega)).2
    -- invariante sobre os bits restantes
    have inv : ∀ (bs : List Bool) (s' : St R) (v0 : Bool), ∃ v', Reach (TM2.step (prog code))
        (cfg code (a + 2) v0 (update (put S s') (Pk.hb (nv D ℓ)) bs))
        (cfg code (a + 5 + size p₀ + size p₁) v'
          (put S (bs.foldl (fun s b => if b then run w p₁ s else run w p₀ s) s')))
        (costIn (cost w p₀) (cost w p₁) (run w p₀) (run w p₁) bs s' + 1) := by
      intro bs
      induction bs with
      | nil =>
        intro s' v0
        have e : update (put S s') (Pk.hb (nv D ℓ)) [] = put S s' :=
          update_eq_self_iff.mpr hhb.symm
        rw [e]
        exact ⟨false, by simpa [costIn] using ihead_nil c2 v0 (put S s') hhb⟩
      | cons b bs ih =>
        intro s' v0
        have r1 := ihead_cons c2 v0 (update (put S s') (Pk.hb (nv D ℓ)) (b :: bs)) b bs
          (by simp)
        rw [update_idem] at r1
        have hT := inv_upd_hb (inv_put h s') (nv D ℓ) hiv bs
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at r1
          obtain ⟨v1, r2⟩ := asm_ok code w p₀ (a + 3) (ℓ + 1) _ false hL0 hd0 hT
          rw [stOf_upd_hb, stOf_put, put_upd_hb, put_put] at r2
          have r3 := jmp_ok cj0 v1 (update (put S (run w p₀ s')) (Pk.hb (nv D ℓ)) bs)
          obtain ⟨v2, r4⟩ := ih (run w p₀ s') v1
          refine ⟨v2, ?_⟩
          simp only [List.foldl_cons, Bool.false_eq_true, ↓reduceIte]
          exact (((r1.trans r2).trans r3).trans r4).mono (by simp [costIn]; omega)
        | true =>
          simp only [↓reduceIte] at r1
          obtain ⟨v1, r2⟩ := asm_ok code w p₁ (a + 4 + size p₀) (ℓ + 1) _ true hL1 hd1 hT
          rw [stOf_upd_hb, stOf_put, put_upd_hb, put_put] at r2
          have r3 := jmp_ok cj1 v1 (update (put S (run w p₁ s')) (Pk.hb (nv D ℓ)) bs)
          obtain ⟨v2, r4⟩ := ih (run w p₁ s') v1
          refine ⟨v2, ?_⟩
          simp only [List.foldl_cons, ↓reduceIte]
          exact (((r1.trans r2).trans r3).trans r4).mono (by simp [costIn]; omega)
    -- cópia da entrada
    set S1 := update (update S Pk.inp []) Pk.tb w.reverse with hS1
    have s1 : Reach (TM2.step (prog code)) (cfg code a v S) (cfg code (a + 1) false S1)
        (w.length + 1) := by
      have := mv_ok (s := Pk.inp) (d := Pk.tb) (by simp) c0 w v S h.inp
      simpa [h.tb, hS1] using this
    have s2 := mv2_ok (s := Pk.tb) (d₁ := Pk.inp) (d₂ := Pk.hb (nv D ℓ)) (by simp) (by simp)
      (by simp) c1 w.reverse false S1 (by simp [hS1])
    have eS2 : update (update (update S1 Pk.tb []) Pk.inp (w.reverse.reverse ++ S1 Pk.inp))
        (Pk.hb (nv D ℓ)) (w.reverse.reverse ++ S1 (Pk.hb (nv D ℓ))) =
        update (put S (stOf S)) (Pk.hb (nv D ℓ)) w := by
      rw [put_stOf h]
      funext k
      by_cases k1 : k = Pk.hb (nv D ℓ)
      · subst k1; simp [hS1, hhb]
      · by_cases k2 : k = Pk.inp
        · subst k2; simp [hS1, h.inp]
        · by_cases k3 : k = Pk.tb
          · subst k3; simp [hS1, h.tb]
          · simp [hS1, k1, k2, k3]
    rw [eS2] at s2
    obtain ⟨v', rl⟩ := inv w (stOf S) false
    refine ⟨v', ?_⟩
    have tot := (s1.trans s2).trans rl
    simp only [run, size, cost]
    have e5 : a + (size p₀ + size p₁ + 5) = a + 5 + size p₀ + size p₁ := by omega
    rw [e5]
    refine tot.mono ?_
    simp
    omega

end Correcao

end ATK.Gerador

#print axioms ATK.Gerador.Prog
#print axioms ATK.Gerador.St
#print axioms ATK.Gerador.run
#print axioms ATK.Gerador.costIt
#print axioms ATK.Gerador.costIn
#print axioms ATK.Gerador.cost
#print axioms ATK.Gerador.size
#print axioms ATK.Gerador.depth
#print axioms ATK.Gerador.Base
#print axioms ATK.Gerador.Pk
#print axioms ATK.Gerador.Pk.inp
#print axioms ATK.Gerador.Pk.outp
#print axioms ATK.Gerador.Pk.wrk
#print axioms ATK.Gerador.Pk.tu
#print axioms ATK.Gerador.Pk.tb
#print axioms ATK.Gerador.Pk.reg
#print axioms ATK.Gerador.Pk.hu
#print axioms ATK.Gerador.Pk.hb
#print axioms ATK.Gerador.nv
#print axioms ATK.Gerador.Ins
#print axioms ATK.Gerador.asm
#print axioms ATK.Gerador.length_asm
#print axioms ATK.Gerador.lab
#print axioms ATK.Gerador.stmt
#print axioms ATK.Gerador.prog
#print axioms ATK.Gerador.cfg
#print axioms ATK.Gerador.Reach
#print axioms ATK.Gerador.Reach.refl
#print axioms ATK.Gerador.Reach.mono
#print axioms ATK.Gerador.Reach.trans
#print axioms ATK.Gerador.Reach.one
#print axioms ATK.Gerador.Reach.cons
#print axioms ATK.Gerador.lab_val
#print axioms ATK.Gerador.step_at
#print axioms ATK.Gerador.push_ok
#print axioms ATK.Gerador.pop1_ok
#print axioms ATK.Gerador.jmp_ok
#print axioms ATK.Gerador.clr_ok
#print axioms ATK.Gerador.mv_ok
#print axioms ATK.Gerador.mv2_ok
#print axioms ATK.Gerador.lhead_nil
#print axioms ATK.Gerador.lhead_cons
#print axioms ATK.Gerador.ihead_nil
#print axioms ATK.Gerador.ihead_cons
#print axioms ATK.Gerador.stOf
#print axioms ATK.Gerador.put
#print axioms ATK.Gerador.Inv
#print axioms ATK.Gerador.put_stOf
#print axioms ATK.Gerador.stOf_put
#print axioms ATK.Gerador.put_put
#print axioms ATK.Gerador.inv_put
#print axioms ATK.Gerador.put_upd_hu
#print axioms ATK.Gerador.put_upd_hb
#print axioms ATK.Gerador.stOf_upd_hu
#print axioms ATK.Gerador.stOf_upd_hb
#print axioms ATK.Gerador.inv_upd_hu
#print axioms ATK.Gerador.inv_upd_hb
#print axioms ATK.Gerador.Loc
#print axioms ATK.Gerador.Loc.left
#print axioms ATK.Gerador.Loc.right
#print axioms ATK.Gerador.Loc.at
#print axioms ATK.Gerador.Loc.atE
#print axioms ATK.Gerador.Loc.shift
#print axioms ATK.Gerador.put_out
#print axioms ATK.Gerador.put_reg
#print axioms ATK.Gerador.depth_le_left
#print axioms ATK.Gerador.depth_le_right
#print axioms ATK.Gerador.asm_ok
