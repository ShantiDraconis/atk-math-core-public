import ATK.SatNPSemantica

/-!
# ATK — SAT ∈ NP, a máquina: o verificador `verif` como `Turing.FinTM2` em tempo polinomial

Pilhas: `inp` (entrada/saída, bits), `T` (auxiliar de inversão), `X` (fórmula), `C`
(certificado), `D` (parte varrida do certificado, para restaurar), `I` (índice do literal
corrente, bit mais significativo no topo) e `J` (parte desempilhada de `I`, para restaurar), as
seis últimas de símbolos de dois bits.

Fase 0 (`rx`, `tx`, `rc`, `tc`): lê `⟨x, c⟩` e deixa `X = syms x`, `C = syms c` (se `|x|` for
ímpar, rejeita). Fase 1 (`st`, `ix`, consulta `en`/`cm`/`sk`/`rj`, limpeza `cj`/`ci`/`rd`):
avalia a fórmula como `evalStart`; cada literal consulta o certificado. Saída: `oc`; rejeição
por fórmula malformada: `dx`/`di`/`dc`; por `|x|` ímpar: `dk`/`dt`.
-/

namespace ATK.SatNPMaquina

open ATK.SatNPSemantica

open Turing Computability StateTransition Function

/-! ### Pilhas, rótulos e estado -/

inductive K | inp | T | X | C | D | I | J
  deriving DecidableEq

instance : Fintype K :=
  ⟨{.inp, .T, .X, .C, .D, .I, .J}, fun x => by cases x <;> simp⟩

/-- Alfabetos: bits na entrada, símbolos nas demais. -/
@[reducible] def Γ : K → Type
  | .inp => Bool
  | _ => Sym

inductive Lab | rx | tx | rc | tc | st | ix | en | cm | sk | rj | cj | ci | rd | oc | dx | di | dc
    | dk | dt
  deriving DecidableEq

instance : Fintype Lab :=
  ⟨{.rx, .tx, .rc, .tc, .st, .ix, .en, .cm, .sk, .rj, .cj, .ci, .rd, .oc, .dx, .di, .dc, .dk, .dt},
    fun x => by cases x <;> simp⟩

structure Est where
  b1 : Option Bool
  pend : Option Bool
  sy : Option Sym
  u : Option Sym
  fr : Bool
  cs : Bool
  al : Bool
  p : Bool
  v : Bool
  res : Bool
  deriving DecidableEq

instance : Fintype Est :=
  Fintype.ofEquiv
    (Option Bool × Option Bool × Option Sym × Option Sym × Bool × Bool × Bool × Bool × Bool × Bool)
    { toFun := fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1,
        t.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2⟩
      invFun := fun s => (s.b1, s.pend, s.sy, s.u, s.fr, s.cs, s.al, s.p, s.v, s.res)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Estado inicial (e final). -/
def init : Est := ⟨none, none, none, none, false, false, false, false, false, false⟩

/-- Estados canônicos da fase 1. -/
def E (fr cs al p v res : Bool) : Est := ⟨none, none, none, none, fr, cs, al, p, v, res⟩

/-- Estado da fase 0 com um bit pendente. -/
def S0 (q : Option Bool) : Est := ⟨none, q, none, none, false, false, false, false, false, false⟩

abbrev St := Turing.TM2.Stmt Γ Lab Est

open Turing.TM2.Stmt

/-! ### O programa -/

def Prx : St :=
  pop .inp (fun s o => {s with b1 := o})
   (branch (fun s => s.b1.isSome)
     (pop .inp (fun s o => {s with sy := o.map fun b => (s.b1.getD false, b)})
       (branch (fun s => s.sy.isSome)
         (branch (fun s => (s.sy.getD sL).1 == (s.sy.getD sL).2)
           (branch (fun s => s.pend.isSome)
             (push .T (fun s => (s.pend.getD false, (s.sy.getD sL).1))
               (load (fun _ => S0 none) (goto fun _ => .rx)))
             (load (fun s => S0 (some (s.sy.getD sL).1)) (goto fun _ => .rx)))
           (branch (fun s => s.pend.isSome)
             (load (fun _ => init) (goto fun _ => .dk))
             (load (fun _ => init) (goto fun _ => .tx))))
         (branch (fun s => s.pend.isSome)
           (load (fun _ => init) (goto fun _ => .dk))
           (load (fun _ => init) (goto fun _ => .tx)))))
     (branch (fun s => s.pend.isSome)
       (load (fun _ => init) (goto fun _ => .dk))
       (load (fun _ => init) (goto fun _ => .tx))))

def Ptx : St :=
  pop .T (fun s o => {s with sy := o})
    (branch (fun s => s.sy.isSome)
      (push .X (fun s => s.sy.getD sL) (load (fun _ => init) (goto fun _ => .tx)))
      (goto fun _ => .rc))

def Prc : St :=
  pop .inp (fun s o => {s with b1 := o})
    (branch (fun s => s.b1.isSome)
      (pop .inp (fun s o => {s with sy := o.map fun b => (s.b1.getD false, b)})
        (branch (fun s => s.sy.isSome)
          (push .T (fun s => s.sy.getD sL) (load (fun _ => init) (goto fun _ => .rc)))
          (load (fun _ => init) (goto fun _ => .tc))))
      (goto fun _ => .tc))

def Ptc : St :=
  pop .T (fun s o => {s with sy := o})
    (branch (fun s => s.sy.isSome)
      (push .C (fun s => s.sy.getD sL) (load (fun _ => init) (goto fun _ => .tc)))
      (load (fun _ => E true false true false false false) (goto fun _ => .st)))

def Pst : St :=
  pop .X (fun s o => {s with sy := o})
    (branch (fun s => s.sy.isSome)
      (branch (fun s => decide (s.sy.getD sL = sC))
        (load (fun s => E true false (s.al && s.cs) false false false) (goto fun _ => .st))
        (branch (fun s => (s.sy.getD sL).1)
          (load (fun _ => init) (goto fun _ => .dx))
          (load (fun s => E s.fr s.cs s.al (s.sy.getD sL).2 false false) (goto fun _ => .ix))))
      (load (fun s => E s.fr s.cs s.al false false (s.fr && s.al)) (goto fun _ => .oc)))

def Pix : St :=
  pop .X (fun s o => {s with sy := o})
    (branch (fun s => s.sy.isSome)
      (branch (fun s => decide (s.sy.getD sL = sC))
        (load (fun _ => init) (goto fun _ => .dx))
        (branch (fun s => (s.sy.getD sL).1)
          (peek .I (fun s o => {s with u := o})
            (branch (fun s => s.u.all (· = (false, true)))
              (load (fun s => E s.fr s.cs s.al s.p false false) (goto fun _ => .en))
              (load (fun _ => init) (goto fun _ => .dx))))
          (push .I (fun s => s.sy.getD sL)
            (load (fun s => E s.fr s.cs s.al s.p false false) (goto fun _ => .ix)))))
      (load (fun _ => init) (goto fun _ => .dx)))

def Pen : St :=
  pop .C (fun s o => {s with sy := o})
    (branch (fun s => s.sy.isSome)
      (push .D (fun s => s.sy.getD sL)
        (branch (fun s => decide (s.sy.getD sL = sL))
          (peek .I (fun s o => {s with u := o})
            (branch (fun s => s.u.isSome)
              (load (fun s => E s.fr s.cs s.al s.p s.v s.res) (goto fun _ => .en))
              (load (fun s => E s.fr s.cs s.al s.p s.v false) (goto fun _ => .cj))))
          (load (fun s => E s.fr s.cs s.al s.p (s.sy.getD sL).2 s.res) (goto fun _ => .cm))))
      (load (fun s => E s.fr s.cs s.al s.p s.v false) (goto fun _ => .cj)))

def Pcm : St :=
  pop .C (fun s o => {s with sy := o})
    (branch (fun s => s.sy.isSome)
      (push .D (fun s => s.sy.getD sL)
        (branch (fun s => decide (s.sy.getD sL = sL))
          (peek .I (fun s o => {s with u := o})
            (branch (fun s => s.u.isSome)
              (load (fun s => E s.fr s.cs s.al s.p s.v s.res) (goto fun _ => .rj))
              (load (fun s => E s.fr s.cs s.al s.p s.v s.v) (goto fun _ => .cj))))
          (pop .I (fun s o => {s with u := o})
            (branch (fun s => s.u.isSome)
              (push .J (fun s => s.u.getD sL)
                (branch (fun s => decide (s.u = s.sy))
                  (load (fun s => E s.fr s.cs s.al s.p s.v s.res) (goto fun _ => .cm))
                  (load (fun s => E s.fr s.cs s.al s.p s.v s.res) (goto fun _ => .sk))))
              (load (fun s => E s.fr s.cs s.al s.p s.v s.res) (goto fun _ => .sk))))))
      (peek .I (fun s o => {s with u := o})
        (branch (fun s => s.u.isSome)
          (load (fun s => E s.fr s.cs s.al s.p s.v s.res) (goto fun _ => .rj))
          (load (fun s => E s.fr s.cs s.al s.p s.v s.v) (goto fun _ => .cj)))))

def Psk : St :=
  pop .C (fun s o => {s with sy := o})
    (branch (fun s => s.sy.isSome)
      (push .D (fun s => s.sy.getD sL)
        (branch (fun s => decide (s.sy.getD sL = sL))
          (load (fun s => E s.fr s.cs s.al s.p s.v s.res) (goto fun _ => .rj))
          (load (fun s => E s.fr s.cs s.al s.p s.v s.res) (goto fun _ => .sk))))
      (goto fun _ => .rj))

def Prj : St :=
  pop .J (fun s o => {s with u := o})
    (branch (fun s => s.u.isSome)
      (push .I (fun s => s.u.getD sL)
        (load (fun s => E s.fr s.cs s.al s.p s.v s.res) (goto fun _ => .rj)))
      (goto fun _ => .en))

def Pcj : St :=
  pop .J (fun s o => {s with u := o})
    (branch (fun s => s.u.isSome)
      (load (fun s => E s.fr s.cs s.al s.p s.v s.res) (goto fun _ => .cj))
      (goto fun _ => .ci))

def Pci : St :=
  pop .I (fun s o => {s with u := o})
    (branch (fun s => s.u.isSome)
      (load (fun s => E s.fr s.cs s.al s.p s.v s.res) (goto fun _ => .ci))
      (goto fun _ => .rd))

def Prd : St :=
  pop .D (fun s o => {s with sy := o})
    (branch (fun s => s.sy.isSome)
      (push .C (fun s => s.sy.getD sL)
        (load (fun s => E s.fr s.cs s.al s.p s.v s.res) (goto fun _ => .rd)))
      (load (fun s => E false (s.cs || (s.res == s.p)) s.al false false false) (goto fun _ => .st)))

def Poc : St :=
  pop .C (fun s o => {s with sy := o})
    (branch (fun s => s.sy.isSome)
      (load (fun s => E s.fr s.cs s.al s.p s.v s.res) (goto fun _ => .oc))
      (push .inp (fun s => s.res) (load (fun _ => init) halt)))

def Pdx : St :=
  pop .X (fun s o => {s with sy := o})
    (branch (fun s => s.sy.isSome) (load (fun _ => init) (goto fun _ => .dx)) (goto fun _ => .di))

def Pdi : St :=
  pop .I (fun s o => {s with sy := o})
    (branch (fun s => s.sy.isSome) (load (fun _ => init) (goto fun _ => .di)) (goto fun _ => .dc))

def Pdc : St :=
  pop .C (fun s o => {s with sy := o})
    (branch (fun s => s.sy.isSome) (load (fun _ => init) (goto fun _ => .dc))
      (push .inp (fun _ => false) (load (fun _ => init) halt)))

def Pdk : St :=
  pop .inp (fun s o => {s with b1 := o})
    (branch (fun s => s.b1.isSome) (load (fun _ => init) (goto fun _ => .dk)) (goto fun _ => .dt))

def Pdt : St :=
  pop .T (fun s o => {s with sy := o})
    (branch (fun s => s.sy.isSome) (load (fun _ => init) (goto fun _ => .dt))
      (push .inp (fun _ => false) (load (fun _ => init) halt)))

def prog : Lab → St
  | .rx => Prx | .tx => Ptx | .rc => Prc | .tc => Ptc | .st => Pst | .ix => Pix | .en => Pen
  | .cm => Pcm | .sk => Psk | .rj => Prj | .cj => Pcj | .ci => Pci | .rd => Prd | .oc => Poc
  | .dx => Pdx | .di => Pdi | .dc => Pdc | .dk => Pdk | .dt => Pdt

/-- **A máquina verificadora.** -/
abbrev verifTM : FinTM2 where
  K := K
  k₀ := .inp
  k₁ := .inp
  Γ := Γ
  Λ := Lab
  main := .rx
  σ := Est
  initialState := init
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := prog

/-! ### Configurações -/

structure Pil where
  inp : List Bool
  T : List Sym
  X : List Sym
  C : List Sym
  D : List Sym
  I : List Sym
  J : List Sym

def stk (P : Pil) : (k : K) → List (Γ k)
  | .inp => P.inp
  | .T => P.T
  | .X => P.X
  | .C => P.C
  | .D => P.D
  | .I => P.I
  | .J => P.J

abbrev Cfg := Turing.TM2.Cfg Γ Lab Est

def cfg (l : Lab) (s : Est) (P : Pil) : Cfg := ⟨some l, s, stk P⟩

abbrev step := Turing.TM2.step prog

@[simp] theorem stk_inp (P : Pil) : stk P .inp = P.inp := rfl
@[simp] theorem stk_T (P : Pil) : stk P .T = P.T := rfl
@[simp] theorem stk_X (P : Pil) : stk P .X = P.X := rfl
@[simp] theorem stk_C (P : Pil) : stk P .C = P.C := rfl
@[simp] theorem stk_D (P : Pil) : stk P .D = P.D := rfl
@[simp] theorem stk_I (P : Pil) : stk P .I = P.I := rfl
@[simp] theorem stk_J (P : Pil) : stk P .J = P.J := rfl

@[simp] theorem upd_inp (P : Pil) (l : List Bool) :
    update (stk P) K.inp l = stk {P with inp := l} := by
  funext k; cases k <;> rfl
@[simp] theorem upd_T (P : Pil) (l : List Sym) : update (stk P) K.T l = stk {P with T := l} := by
  funext k; cases k <;> rfl
@[simp] theorem upd_X (P : Pil) (l : List Sym) : update (stk P) K.X l = stk {P with X := l} := by
  funext k; cases k <;> rfl
@[simp] theorem upd_C (P : Pil) (l : List Sym) : update (stk P) K.C l = stk {P with C := l} := by
  funext k; cases k <;> rfl
@[simp] theorem upd_D (P : Pil) (l : List Sym) : update (stk P) K.D l = stk {P with D := l} := by
  funext k; cases k <;> rfl
@[simp] theorem upd_I (P : Pil) (l : List Sym) : update (stk P) K.I l = stk {P with I := l} := by
  funext k; cases k <;> rfl
@[simp] theorem upd_J (P : Pil) (l : List Sym) : update (stk P) K.J l = stk {P with J := l} := by
  funext k; cases k <;> rfl

end ATK.SatNPMaquina


namespace ATK.SatNPMaquina

open ATK.SatNPSemantica
open Turing Computability StateTransition Function ATK.LigacaoPNP ATK.ModeloPNP

/-! ### Passos (um por rótulo e caso) -/

section Passos
variable (inp : List Bool) (T X C D I J : List Sym)

local macro "passo" : tactic =>
  `(tactic| simp [step, cfg, prog, Prx, Ptx, Prc, Ptc, Pst, Pix, Pen, Pcm, Psk, Prj, Pcj, Pci, Prd,
      Poc, Pdx, Pdi, Pdc, Pdk, Pdt, Turing.TM2.stepAux, S0, E, init, sL, sC])

/-! Fase 0 -/

theorem rx_nil (q : Option Bool) :
    step (cfg .rx (S0 q) ⟨[], T, X, C, D, I, J⟩) =
      some (cfg (if q.isSome then .dk else .tx) init ⟨[], T, X, C, D, I, J⟩) := by
  cases q <;> passo

theorem rx_one (q : Option Bool) (a : Bool) :
    step (cfg .rx (S0 q) ⟨[a], T, X, C, D, I, J⟩) =
      some (cfg (if q.isSome then .dk else .tx) init ⟨[], T, X, C, D, I, J⟩) := by
  cases q <;> passo

theorem rx_eq_none (a : Bool) (r : List Bool) :
    step (cfg .rx (S0 none) ⟨a :: a :: r, T, X, C, D, I, J⟩) =
      some (cfg .rx (S0 (some a)) ⟨r, T, X, C, D, I, J⟩) := by passo

theorem rx_eq_some (q a : Bool) (r : List Bool) :
    step (cfg .rx (S0 (some q)) ⟨a :: a :: r, T, X, C, D, I, J⟩) =
      some (cfg .rx (S0 none) ⟨r, (q, a) :: T, X, C, D, I, J⟩) := by passo

theorem rx_neq (q : Option Bool) (a b : Bool) (r : List Bool) (h : a ≠ b) :
    step (cfg .rx (S0 q) ⟨a :: b :: r, T, X, C, D, I, J⟩) =
      some (cfg (if q.isSome then .dk else .tx) init ⟨r, T, X, C, D, I, J⟩) := by
  cases a <;> cases b <;> simp at h <;> cases q <;> passo

theorem tx_cons (t : Sym) :
    step (cfg .tx init ⟨inp, t :: T, X, C, D, I, J⟩) =
      some (cfg .tx init ⟨inp, T, t :: X, C, D, I, J⟩) := by passo

theorem tx_nil : step (cfg .tx init ⟨inp, [], X, C, D, I, J⟩) =
    some (cfg .rc init ⟨inp, [], X, C, D, I, J⟩) := by passo

theorem rc_nil : step (cfg .rc init ⟨[], T, X, C, D, I, J⟩) =
    some (cfg .tc init ⟨[], T, X, C, D, I, J⟩) := by passo

theorem rc_one (a : Bool) : step (cfg .rc init ⟨[a], T, X, C, D, I, J⟩) =
    some (cfg .tc init ⟨[], T, X, C, D, I, J⟩) := by passo

theorem rc_cons (a b : Bool) (r : List Bool) :
    step (cfg .rc init ⟨a :: b :: r, T, X, C, D, I, J⟩) =
      some (cfg .rc init ⟨r, (a, b) :: T, X, C, D, I, J⟩) := by passo

theorem tc_cons (t : Sym) :
    step (cfg .tc init ⟨inp, t :: T, X, C, D, I, J⟩) =
      some (cfg .tc init ⟨inp, T, X, t :: C, D, I, J⟩) := by passo

theorem tc_nil : step (cfg .tc init ⟨inp, [], X, C, D, I, J⟩) =
    some (cfg .st (E true false true false false false) ⟨inp, [], X, C, D, I, J⟩) := by passo


/-! Fase 1 -/

variable (fr cs al p v res : Bool)

/-- Configuração final: só a saída `[b]`. -/
def fim (b : Bool) : Cfg := ⟨none, init, stk ⟨[b], [], [], [], [], [], []⟩⟩

theorem st_nil : step (cfg .st (E fr cs al p v res) ⟨inp, T, [], C, D, I, J⟩) =
    some (cfg .oc (E fr cs al false false (fr && al)) ⟨inp, T, [], C, D, I, J⟩) := by passo

theorem st_sC : step (cfg .st (E fr cs al p v res) ⟨inp, T, sC :: X, C, D, I, J⟩) =
    some (cfg .st (E true false (al && cs) false false false) ⟨inp, T, X, C, D, I, J⟩) := by passo

theorem st_bad (s : Sym) (h1 : s ≠ sC) (h2 : s.1 = true) :
    step (cfg .st (E fr cs al p v res) ⟨inp, T, s :: X, C, D, I, J⟩) =
      some (cfg .dx init ⟨inp, T, X, C, D, I, J⟩) := by
  rcases s with ⟨a, b⟩; simp only at h2; subst h2; cases b
  · passo
  · simp [sC] at h1

theorem st_lit (b : Bool) :
    step (cfg .st (E fr cs al p v res) ⟨inp, T, (false, b) :: X, C, D, I, J⟩) =
      some (cfg .ix (E fr cs al b false false) ⟨inp, T, X, C, D, I, J⟩) := by passo

theorem ix_nil : step (cfg .ix (E fr cs al p v res) ⟨inp, T, [], C, D, I, J⟩) =
    some (cfg .dx init ⟨inp, T, [], C, D, I, J⟩) := by passo

theorem ix_sC : step (cfg .ix (E fr cs al p v res) ⟨inp, T, sC :: X, C, D, I, J⟩) =
    some (cfg .dx init ⟨inp, T, X, C, D, I, J⟩) := by passo

theorem ix_fim_ok (h : I.head?.all (· = (false, true)) = true) :
    step (cfg .ix (E fr cs al p v res) ⟨inp, T, sL :: X, C, D, I, J⟩) =
      some (cfg .en (E fr cs al p false false) ⟨inp, T, X, C, D, I, J⟩) := by
  passo; simpa using h

theorem ix_fim_bad (h : I.head?.all (· = (false, true)) = false) :
    step (cfg .ix (E fr cs al p v res) ⟨inp, T, sL :: X, C, D, I, J⟩) =
      some (cfg .dx init ⟨inp, T, X, C, D, I, J⟩) := by
  passo; simpa using h

theorem ix_bit (b : Bool) :
    step (cfg .ix (E fr cs al p v res) ⟨inp, T, (false, b) :: X, C, D, I, J⟩) =
      some (cfg .ix (E fr cs al p false false) ⟨inp, T, X, C, D, (false, b) :: I, J⟩) := by passo

theorem en_nil : step (cfg .en (E fr cs al p v res) ⟨inp, T, X, [], D, I, J⟩) =
    some (cfg .cj (E fr cs al p v false) ⟨inp, T, X, [], D, I, J⟩) := by passo

theorem en_sL_vazio (C : List Sym) :
    step (cfg .en (E fr cs al p v res) ⟨inp, T, X, sL :: C, D, [], J⟩) =
      some (cfg .cj (E fr cs al p v false) ⟨inp, T, X, C, sL :: D, [], J⟩) := by passo

theorem en_sL_cheio (C : List Sym) (u : Sym) (I : List Sym) :
    step (cfg .en (E fr cs al p v res) ⟨inp, T, X, sL :: C, D, u :: I, J⟩) =
      some (cfg .en (E fr cs al p v res) ⟨inp, T, X, C, sL :: D, u :: I, J⟩) := by passo

theorem en_sym (s : Sym) (C : List Sym) (h : s ≠ sL) :
    step (cfg .en (E fr cs al p v res) ⟨inp, T, X, s :: C, D, I, J⟩) =
      some (cfg .cm (E fr cs al p s.2 res) ⟨inp, T, X, C, s :: D, I, J⟩) := by
  rcases s with ⟨a, b⟩; cases a <;> cases b <;> simp [sL] at h <;> passo

theorem cm_nil_vazio : step (cfg .cm (E fr cs al p v res) ⟨inp, T, X, [], D, [], J⟩) =
    some (cfg .cj (E fr cs al p v v) ⟨inp, T, X, [], D, [], J⟩) := by passo

theorem cm_nil_cheio (u : Sym) (I : List Sym) :
    step (cfg .cm (E fr cs al p v res) ⟨inp, T, X, [], D, u :: I, J⟩) =
      some (cfg .rj (E fr cs al p v res) ⟨inp, T, X, [], D, u :: I, J⟩) := by passo

theorem cm_sL_vazio (C : List Sym) :
    step (cfg .cm (E fr cs al p v res) ⟨inp, T, X, sL :: C, D, [], J⟩) =
      some (cfg .cj (E fr cs al p v v) ⟨inp, T, X, C, sL :: D, [], J⟩) := by passo

theorem cm_sL_cheio (C : List Sym) (u : Sym) (I : List Sym) :
    step (cfg .cm (E fr cs al p v res) ⟨inp, T, X, sL :: C, D, u :: I, J⟩) =
      some (cfg .rj (E fr cs al p v res) ⟨inp, T, X, C, sL :: D, u :: I, J⟩) := by passo

theorem cm_sym_vazio (t : Sym) (C : List Sym) (h : t ≠ sL) :
    step (cfg .cm (E fr cs al p v res) ⟨inp, T, X, t :: C, D, [], J⟩) =
      some (cfg .sk (E fr cs al p v res) ⟨inp, T, X, C, t :: D, [], J⟩) := by
  rcases t with ⟨a, b⟩; cases a <;> cases b <;> simp [sL] at h <;> passo

theorem cm_sym_igual (t : Sym) (C : List Sym) (I : List Sym) (h : t ≠ sL) :
    step (cfg .cm (E fr cs al p v res) ⟨inp, T, X, t :: C, D, t :: I, J⟩) =
      some (cfg .cm (E fr cs al p v res) ⟨inp, T, X, C, t :: D, I, t :: J⟩) := by
  rcases t with ⟨a, b⟩; cases a <;> cases b <;> simp [sL] at h <;> passo

theorem cm_sym_dif (t u : Sym) (C : List Sym) (I : List Sym) (h : t ≠ sL) (hu : u ≠ t) :
    step (cfg .cm (E fr cs al p v res) ⟨inp, T, X, t :: C, D, u :: I, J⟩) =
      some (cfg .sk (E fr cs al p v res) ⟨inp, T, X, C, t :: D, I, u :: J⟩) := by
  rcases t with ⟨a, b⟩; rcases u with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> simp [sL] at h hu <;> passo

theorem sk_nil : step (cfg .sk (E fr cs al p v res) ⟨inp, T, X, [], D, I, J⟩) =
    some (cfg .rj (E fr cs al p v res) ⟨inp, T, X, [], D, I, J⟩) := by passo

theorem sk_sL (C : List Sym) : step (cfg .sk (E fr cs al p v res) ⟨inp, T, X, sL :: C, D, I, J⟩) =
    some (cfg .rj (E fr cs al p v res) ⟨inp, T, X, C, sL :: D, I, J⟩) := by passo

theorem sk_sym (t : Sym) (C : List Sym) (h : t ≠ sL) :
    step (cfg .sk (E fr cs al p v res) ⟨inp, T, X, t :: C, D, I, J⟩) =
      some (cfg .sk (E fr cs al p v res) ⟨inp, T, X, C, t :: D, I, J⟩) := by
  rcases t with ⟨a, b⟩; cases a <;> cases b <;> simp [sL] at h <;> passo

theorem rj_cons (u : Sym) (J : List Sym) :
    step (cfg .rj (E fr cs al p v res) ⟨inp, T, X, C, D, I, u :: J⟩) =
      some (cfg .rj (E fr cs al p v res) ⟨inp, T, X, C, D, u :: I, J⟩) := by passo

theorem rj_nil : step (cfg .rj (E fr cs al p v res) ⟨inp, T, X, C, D, I, []⟩) =
    some (cfg .en (E fr cs al p v res) ⟨inp, T, X, C, D, I, []⟩) := by passo

theorem cj_cons (u : Sym) (J : List Sym) :
    step (cfg .cj (E fr cs al p v res) ⟨inp, T, X, C, D, I, u :: J⟩) =
      some (cfg .cj (E fr cs al p v res) ⟨inp, T, X, C, D, I, J⟩) := by passo

theorem cj_nil : step (cfg .cj (E fr cs al p v res) ⟨inp, T, X, C, D, I, []⟩) =
    some (cfg .ci (E fr cs al p v res) ⟨inp, T, X, C, D, I, []⟩) := by passo

theorem ci_cons (u : Sym) (I : List Sym) :
    step (cfg .ci (E fr cs al p v res) ⟨inp, T, X, C, D, u :: I, J⟩) =
      some (cfg .ci (E fr cs al p v res) ⟨inp, T, X, C, D, I, J⟩) := by passo

theorem ci_nil : step (cfg .ci (E fr cs al p v res) ⟨inp, T, X, C, D, [], J⟩) =
    some (cfg .rd (E fr cs al p v res) ⟨inp, T, X, C, D, [], J⟩) := by passo

theorem rd_cons (d : Sym) (D : List Sym) :
    step (cfg .rd (E fr cs al p v res) ⟨inp, T, X, C, d :: D, I, J⟩) =
      some (cfg .rd (E fr cs al p v res) ⟨inp, T, X, d :: C, D, I, J⟩) := by passo

theorem rd_nil : step (cfg .rd (E fr cs al p v res) ⟨inp, T, X, C, [], I, J⟩) =
    some (cfg .st (E false (cs || (res == p)) al false false false) ⟨inp, T, X, C, [], I, J⟩) := by
  passo

theorem oc_cons (t : Sym) (C : List Sym) :
    step (cfg .oc (E fr cs al p v res) ⟨inp, T, X, t :: C, D, I, J⟩) =
      some (cfg .oc (E fr cs al p v res) ⟨inp, T, X, C, D, I, J⟩) := by passo

theorem oc_nil : step (cfg .oc (E fr cs al p v res) ⟨[], [], [], [], [], [], []⟩) = some (fim res) := by
  passo; rfl

theorem dx_cons (t : Sym) : step (cfg .dx init ⟨inp, T, t :: X, C, D, I, J⟩) =
    some (cfg .dx init ⟨inp, T, X, C, D, I, J⟩) := by passo

theorem dx_nil : step (cfg .dx init ⟨inp, T, [], C, D, I, J⟩) =
    some (cfg .di init ⟨inp, T, [], C, D, I, J⟩) := by passo

theorem di_cons (t : Sym) : step (cfg .di init ⟨inp, T, X, C, D, t :: I, J⟩) =
    some (cfg .di init ⟨inp, T, X, C, D, I, J⟩) := by passo

theorem di_nil : step (cfg .di init ⟨inp, T, X, C, D, [], J⟩) =
    some (cfg .dc init ⟨inp, T, X, C, D, [], J⟩) := by passo

theorem dc_cons (t : Sym) : step (cfg .dc init ⟨inp, T, X, t :: C, D, I, J⟩) =
    some (cfg .dc init ⟨inp, T, X, C, D, I, J⟩) := by passo

theorem dc_nil : step (cfg .dc init ⟨[], [], [], [], [], [], []⟩) = some (fim false) := by
  passo; rfl

theorem dk_cons (a : Bool) (r : List Bool) : step (cfg .dk init ⟨a :: r, T, X, C, D, I, J⟩) =
    some (cfg .dk init ⟨r, T, X, C, D, I, J⟩) := by passo

theorem dk_nil : step (cfg .dk init ⟨[], T, X, C, D, I, J⟩) =
    some (cfg .dt init ⟨[], T, X, C, D, I, J⟩) := by passo

theorem dt_cons (t : Sym) : step (cfg .dt init ⟨inp, t :: T, X, C, D, I, J⟩) =
    some (cfg .dt init ⟨inp, T, X, C, D, I, J⟩) := by passo

theorem dt_nil : step (cfg .dt init ⟨[], [], [], [], [], [], []⟩) = some (fim false) := by
  passo; rfl

end Passos


/-! ### Alcance em até `n` passos -/

/-- `c` alcança `c'` em no máximo `n` passos. -/
def Reach (c c' : Cfg) (n : ℕ) : Prop := ∃ k ≤ n, (flip bind step)^[k] (some c) = some c'

theorem Reach.refl (c : Cfg) : Reach c c 0 := ⟨0, le_refl _, rfl⟩

theorem Reach.mono {c c' : Cfg} {n m : ℕ} (h : Reach c c' n) (hnm : n ≤ m) : Reach c c' m :=
  let ⟨k, hk, he⟩ := h; ⟨k, hk.trans hnm, he⟩

theorem Reach.trans {c c' c'' : Cfg} {n m : ℕ} (h1 : Reach c c' n) (h2 : Reach c' c'' m) :
    Reach c c'' (n + m) := by
  obtain ⟨k1, hk1, e1⟩ := h1
  obtain ⟨k2, hk2, e2⟩ := h2
  exact ⟨k2 + k1, by omega, by rw [iterate_add_apply, e1, e2]⟩

theorem Reach.one {c c' : Cfg} (h : step c = some c') : Reach c c' 1 := ⟨1, le_refl _, h⟩

theorem Reach.cons {c c' c'' : Cfg} {n : ℕ} (h : step c = some c') (h2 : Reach c' c'' n) :
    Reach c c'' (n + 1) :=
  ((Reach.one h).trans h2).mono (by omega)

/-! ### Fase 0 -/

theorem run_rx (X C D I J : List Sym) : ∀ (y : List Bool) (q : Option Bool) (T : List Sym),
    Reach (cfg .rx (S0 q) ⟨y, T, X, C, D, I, J⟩)
      (cfg (if (q.toList ++ dec y).length % 2 = 0 then .tx else .dk) init
        ⟨decC y, (syms (q.toList ++ dec y)).reverse ++ T, X, C, D, I, J⟩) (y.length + 1)
  | [], q, T => by
    refine (Reach.one ?_).mono (by simp)
    rw [rx_nil]; cases q <;> simp [dec, decC, syms]
  | [a], q, T => by
    refine (Reach.one ?_).mono (by simp)
    rw [rx_one]; cases q <;> simp [dec, decC, syms]
  | a :: b :: r, q, T => by
    by_cases hab : a = b
    · subst hab
      cases q with
      | none =>
        have ih := run_rx X C D I J r (some a) T
        have h := (Reach.cons (rx_eq_none T X C D I J a r) ih).mono
          (show r.length + 1 + 1 ≤ (a :: a :: r).length + 1 by simp)
        have e1 : dec (a :: a :: r) = a :: dec r := by simp [dec]
        have e2 : decC (a :: a :: r) = decC r := by simp [decC]
        rw [e1, e2]
        exact h
      | some q0 =>
        have ih := run_rx X C D I J r none ((q0, a) :: T)
        have h := (Reach.cons (rx_eq_some T X C D I J q0 a r) ih).mono
          (show r.length + 1 + 1 ≤ (a :: a :: r).length + 1 by simp)
        have e1 : dec (a :: a :: r) = a :: dec r := by simp [dec]
        have e2 : decC (a :: a :: r) = decC r := by simp [decC]
        have e3 : ((some q0).toList ++ (a :: dec r)).length % 2 = ((none : Option Bool).toList ++ dec r).length % 2 := by
          simp; omega
        have e4 : (syms ((some q0).toList ++ (a :: dec r))).reverse ++ T =
            (syms (none.toList ++ dec r)).reverse ++ (q0, a) :: T := by simp [syms]
        rw [e1, e2, e3, e4]
        exact h
    · refine (Reach.one ?_).mono (by simp)
      rw [rx_neq T X C D I J q a b r hab]; cases q <;> simp [dec, decC, hab, syms]

theorem run_tx (inp : List Bool) (C D I J : List Sym) : ∀ (T X : List Sym),
    Reach (cfg .tx init ⟨inp, T, X, C, D, I, J⟩) (cfg .rc init ⟨inp, [], T.reverse ++ X, C, D, I, J⟩)
      (T.length + 1)
  | [], X => (Reach.one (tx_nil inp X C D I J)).mono (by simp)
  | t :: T, X => by
    simpa using Reach.cons (tx_cons inp T X C D I J t) (run_tx inp C D I J T (t :: X))

theorem run_rc (X C D I J : List Sym) : ∀ (y : List Bool) (T : List Sym),
    Reach (cfg .rc init ⟨y, T, X, C, D, I, J⟩) (cfg .tc init ⟨[], (syms y).reverse ++ T, X, C, D, I, J⟩)
      (y.length + 1)
  | [], T => (Reach.one (rc_nil T X C D I J)).mono (by simp)
  | [a], T => (Reach.one (rc_one T X C D I J a)).mono (by simp)
  | a :: b :: r, T => by
    have h := Reach.cons (rc_cons T X C D I J a b r) (run_rc X C D I J r ((a, b) :: T))
    have h2 := h.mono (show r.length + 1 + 1 ≤ (a :: b :: r).length + 1 by simp)
    simpa [syms] using h2

theorem run_tc (X D I J : List Sym) : ∀ (T C : List Sym),
    Reach (cfg .tc init ⟨[], T, X, C, D, I, J⟩)
      (cfg .st (E true false true false false false) ⟨[], [], X, T.reverse ++ C, D, I, J⟩)
      (T.length + 1)
  | [], C => (Reach.one (tc_nil [] X C D I J)).mono (by simp)
  | t :: T, C => by
    have h := Reach.cons (tc_cons [] T X C D I J t) (run_tc X D I J T (t :: C))
    simpa using h

/-! ### Esvaziamentos -/

theorem run_dk (T X C D I J : List Sym) : ∀ r : List Bool,
    Reach (cfg .dk init ⟨r, T, X, C, D, I, J⟩) (cfg .dt init ⟨[], T, X, C, D, I, J⟩) (r.length + 1)
  | [] => (Reach.one (dk_nil T X C D I J)).mono (by simp)
  | a :: r => by simpa using Reach.cons (dk_cons T X C D I J a r) (run_dk T X C D I J r)

theorem run_dt : ∀ T : List Sym, Reach (cfg .dt init ⟨[], T, [], [], [], [], []⟩) (fim false) (T.length + 1)
  | [] => (Reach.one dt_nil).mono (by simp)
  | t :: T => by simpa using Reach.cons (dt_cons [] T [] [] [] [] [] t) (run_dt T)

theorem run_dx (C I : List Sym) : ∀ X : List Sym,
    Reach (cfg .dx init ⟨[], [], X, C, [], I, []⟩) (cfg .di init ⟨[], [], [], C, [], I, []⟩) (X.length + 1)
  | [] => (Reach.one (dx_nil [] [] C [] I [])).mono (by simp)
  | t :: X => by simpa using Reach.cons (dx_cons [] [] X C [] I [] t) (run_dx C I X)

theorem run_di (C : List Sym) : ∀ I : List Sym,
    Reach (cfg .di init ⟨[], [], [], C, [], I, []⟩) (cfg .dc init ⟨[], [], [], C, [], [], []⟩) (I.length + 1)
  | [] => (Reach.one (di_nil [] [] [] C [] [])).mono (by simp)
  | t :: I => by simpa using Reach.cons (di_cons [] [] [] C [] I [] t) (run_di C I)

theorem run_dc : ∀ C : List Sym, Reach (cfg .dc init ⟨[], [], [], C, [], [], []⟩) (fim false) (C.length + 1)
  | [] => (Reach.one dc_nil).mono (by simp)
  | t :: C => by simpa using Reach.cons (dc_cons [] [] [] C [] [] [] t) (run_dc C)

/-- Rejeição na fase 1: esvazia `X`, `I`, `C` e devolve `false`. -/
theorem run_rejeita (X C I : List Sym) :
    Reach (cfg .dx init ⟨[], [], X, C, [], I, []⟩) (fim false) (X.length + I.length + C.length + 3) :=
  (((run_dx C I X).trans (run_di C I)).trans (run_dc C)).mono (by omega)

theorem run_oc (fr cs al p v res : Bool) : ∀ C : List Sym,
    Reach (cfg .oc (E fr cs al p v res) ⟨[], [], [], C, [], [], []⟩) (fim res) (C.length + 1)
  | [] => (Reach.one (oc_nil fr cs al p v res)).mono (by simp)
  | t :: C => by
    simpa using Reach.cons (oc_cons [] [] [] [] [] [] fr cs al p v res t C) (run_oc fr cs al p v res C)


/-! ### A consulta ao certificado -/

section Consulta
variable (X : List Sym) (fr cs al p v res : Bool)

theorem run_rj (C D : List Sym) : ∀ (J I : List Sym),
    Reach (cfg .rj (E fr cs al p v res) ⟨[], [], X, C, D, I, J⟩)
      (cfg .en (E fr cs al p v res) ⟨[], [], X, C, D, J.reverse ++ I, []⟩) (J.length + 1)
  | [], I => (Reach.one (rj_nil [] [] X C D I fr cs al p v res)).mono (by simp)
  | u :: J, I => by
    simpa using Reach.cons (rj_cons [] [] X C D I fr cs al p v res u J) (run_rj C D J (u :: I))

theorem run_sk (I J : List Sym) : ∀ (C D : List Sym), ∃ D' : List Sym,
    D'.reverse ++ (seg C).2 = D.reverse ++ C ∧
    Reach (cfg .sk (E fr cs al p v res) ⟨[], [], X, C, D, I, J⟩)
      (cfg .rj (E fr cs al p v res) ⟨[], [], X, (seg C).2, D', I, J⟩) (C.length + 1)
  | [], D => ⟨D, by simp [seg], (Reach.one (sk_nil [] [] X D I J fr cs al p v res)).mono (by simp)⟩
  | t :: C, D => by
    by_cases ht : t = sL
    · subst ht
      refine ⟨sL :: D, by simp [seg], ?_⟩
      simpa [seg] using (Reach.one (sk_sL [] [] X D I J fr cs al p v res C)).mono
        (show 1 ≤ (sL :: C).length + 1 by simp)
    · obtain ⟨D', hD, hr⟩ := run_sk I J C (t :: D)
      refine ⟨D', by simpa [seg, ht] using hD, ?_⟩
      have h := Reach.cons (sk_sym [] [] X D I J fr cs al p v res t C ht) hr
      simpa [seg, ht] using h

theorem run_cm_igual : ∀ (C D I J : List Sym), (seg C).1 = I → ∃ D' J' : List Sym,
    D'.reverse ++ (seg C).2 = D.reverse ++ C ∧ J'.length = J.length + I.length ∧
    Reach (cfg .cm (E fr cs al p v res) ⟨[], [], X, C, D, I, J⟩)
      (cfg .cj (E fr cs al p v v) ⟨[], [], X, (seg C).2, D', [], J'⟩) (C.length + 1)
  | [], D, I, J, h => by
    simp only [seg] at h; subst h
    exact ⟨D, J, by simp [seg], by simp,
      (Reach.one (cm_nil_vazio [] [] X D J fr cs al p v res)).mono (by simp)⟩
  | t :: C, D, I, J, h => by
    by_cases ht : t = sL
    · subst ht
      simp only [seg, ↓reduceIte] at h; subst h
      refine ⟨sL :: D, J, by simp [seg], by simp, ?_⟩
      simpa [seg] using (Reach.one (cm_sL_vazio [] [] X D J fr cs al p v res C)).mono
        (show 1 ≤ (sL :: C).length + 1 by simp)
    · simp only [seg, ht, ↓reduceIte] at h; subst h
      obtain ⟨D', J', hD, hJ, hr⟩ := run_cm_igual C (t :: D) (seg C).1 (t :: J) rfl
      refine ⟨D', J', by simpa [seg, ht] using hD, by simp at hJ ⊢; omega, ?_⟩
      have h := Reach.cons (cm_sym_igual [] [] X D J fr cs al p v res t C (seg C).1 ht) hr
      simpa [seg, ht] using h

theorem run_cm_dif : ∀ (C D I J : List Sym), (seg C).1 ≠ I → ∃ D' : List Sym,
    D'.reverse ++ (seg C).2 = D.reverse ++ C ∧
    Reach (cfg .cm (E fr cs al p v res) ⟨[], [], X, C, D, I, J⟩)
      (cfg .en (E fr cs al p v res) ⟨[], [], X, (seg C).2, D', J.reverse ++ I, []⟩)
      (C.length + J.length + I.length + 2)
  | [], D, I, J, h => by
    obtain ⟨u, I', rfl⟩ : ∃ u I', I = u :: I' := by
      cases I with
      | nil => simp [seg] at h
      | cons u I' => exact ⟨u, I', rfl⟩
    refine ⟨D, by simp [seg], ?_⟩
    have h1 := Reach.cons (cm_nil_cheio [] [] X D J fr cs al p v res u I')
      (run_rj X fr cs al p v res [] D J (u :: I'))
    simpa [seg] using h1.mono (by simp)
  | t :: C, D, I, J, h => by
    by_cases ht : t = sL
    · subst ht
      obtain ⟨u, I', rfl⟩ : ∃ u I', I = u :: I' := by
        cases I with
        | nil => simp [seg] at h
        | cons u I' => exact ⟨u, I', rfl⟩
      refine ⟨sL :: D, by simp [seg], ?_⟩
      have h1 := Reach.cons (cm_sL_cheio [] [] X D J fr cs al p v res C u I')
        (run_rj X fr cs al p v res C (sL :: D) J (u :: I'))
      simpa [seg] using h1.mono (by simp; omega)
    · cases I with
      | nil =>
        obtain ⟨D', hD, hr⟩ := run_sk X fr cs al p v res [] J C (t :: D)
        refine ⟨D', by simpa [seg, ht] using hD, ?_⟩
        have h1 := Reach.cons (cm_sym_vazio [] [] X D J fr cs al p v res t C ht)
          (hr.trans (run_rj X fr cs al p v res (seg C).2 D' J []))
        simpa [seg, ht] using h1.mono (by simp; omega)
      | cons u I' =>
        by_cases hu : u = t
        · subst hu
          have h' : (seg C).1 ≠ I' := by
            intro he; apply h; simp [seg, ht, he]
          obtain ⟨D', hD, hr⟩ := run_cm_dif C (u :: D) I' (u :: J) h'
          refine ⟨D', by simpa [seg, ht] using hD, ?_⟩
          have h1 := Reach.cons (cm_sym_igual [] [] X D J fr cs al p v res u C I' ht) hr
          simpa [seg, ht] using h1.mono (by simp; omega)
        · obtain ⟨D', hD, hr⟩ := run_sk X fr cs al p v res I' (u :: J) C (t :: D)
          refine ⟨D', by simpa [seg, ht] using hD, ?_⟩
          have h1 := Reach.cons (cm_sym_dif [] [] X D J fr cs al p v res t u C I' ht hu)
            (hr.trans (run_rj X fr cs al p v res (seg C).2 D' (u :: J) I'))
          simpa [seg, ht] using h1.mono (by simp; omega)

end Consulta


section Consulta2
variable (X : List Sym) (fr cs al p : Bool)

theorem run_en : ∀ (n : ℕ) (C D I : List Sym) (v res : Bool), C.length ≤ n →
    ∃ (C' D' I' J' : List Sym) (v' : Bool),
      D'.reverse ++ C' = D.reverse ++ C ∧ I'.length + J'.length = I.length ∧
      Reach (cfg .en (E fr cs al p v res) ⟨[], [], X, C, D, I, []⟩)
        (cfg .cj (E fr cs al p v' (lookup I C)) ⟨[], [], X, C', D', I', J'⟩)
        ((C.length + 1) * (C.length + I.length + 3))
  | n, [], D, I, v, res, _ => by
    refine ⟨[], D, I, [], v, by simp, by simp, ?_⟩
    have h := (Reach.one (en_nil [] [] X D I [] fr cs al p v res)).mono
      (show 1 ≤ ([] : List Sym).length.succ * (([] : List Sym).length + I.length + 3) by simp)
    simpa [lookup] using h
  | 0, _ :: _, _, _, _, _, hn => by simp at hn
  | n + 1, s :: r, D, I, v, res, hn => by
    simp only [List.length_cons] at hn
    by_cases hs : s = sL
    · subst hs
      cases I with
      | nil =>
        refine ⟨r, sL :: D, [], [], v, by simp, by simp, ?_⟩
        have h := (Reach.one (en_sL_vazio [] [] X D [] fr cs al p v res r)).mono
          (show 1 ≤ ((sL :: r).length + 1) * ((sL :: r).length + ([] : List Sym).length + 3) by
            simp; nlinarith)
        rw [lookup]; simpa [seg] using h
      | cons u I' =>
        obtain ⟨C', D', I'', J', v', hD, hI, hr⟩ := run_en n r (sL :: D) (u :: I') v res (by omega)
        refine ⟨C', D', I'', J', v', by simpa using hD, hI, ?_⟩
        have h := Reach.cons (en_sL_cheio [] [] X D [] fr cs al p v res r u I') hr
        have hl : lookup (u :: I') (sL :: r) = lookup (u :: I') r := by
          rw [lookup]; simp [seg]
        rw [hl]
        refine h.mono ?_
        simp only [List.length_cons]
        nlinarith
    · by_cases hm : (seg r).1 = I
      · obtain ⟨D', J', hD, hJ, hr⟩ := run_cm_igual X fr cs al p s.2 res r (s :: D) I [] hm
        refine ⟨(seg r).2, D', [], J', s.2, by simpa using hD, by simp [hJ], ?_⟩
        have h := Reach.cons (en_sym [] [] X D I [] fr cs al p v res s r hs) hr
        have hl : lookup I (s :: r) = s.2 := by
          rw [lookup]; simp [seg, hs, hm]
        rw [hl]
        refine h.mono ?_
        simp only [List.length_cons]
        nlinarith
      · obtain ⟨D1, hD1, hr1⟩ := run_cm_dif X fr cs al p s.2 res r (s :: D) I [] hm
        have hlen : (seg r).2.length ≤ r.length := seg_snd_length_le r
        obtain ⟨C', D', I', J', v', hD, hI, hr⟩ :=
          run_en n (seg r).2 D1 I s.2 res (by omega)
        refine ⟨C', D', I', J', v', by rw [hD, hD1]; simp, hI, ?_⟩
        have h := Reach.cons (en_sym [] [] X D I [] fr cs al p v res s r hs)
          (hr1.trans (by simpa using hr))
        have hl : lookup I (s :: r) = lookup I (seg r).2 := by
          rw [lookup]; simp [seg, hs, hm]
        rw [hl]
        refine h.mono ?_
        simp only [List.length_cons, List.length_nil]
        have h1 : ((seg r).2.length + 1) * ((seg r).2.length + I.length + 3) ≤
            (r.length + 1) * (r.length + I.length + 3) :=
          Nat.mul_le_mul (by omega) (by omega)
        nlinarith

theorem run_cj (C D I : List Sym) (v res : Bool) : ∀ J : List Sym,
    Reach (cfg .cj (E fr cs al p v res) ⟨[], [], X, C, D, I, J⟩)
      (cfg .ci (E fr cs al p v res) ⟨[], [], X, C, D, I, []⟩) (J.length + 1)
  | [] => (Reach.one (cj_nil [] [] X C D I fr cs al p v res)).mono (by simp)
  | u :: J => by simpa using Reach.cons (cj_cons [] [] X C D I fr cs al p v res u J) (run_cj C D I v res J)

theorem run_ci (C D : List Sym) (v res : Bool) : ∀ I : List Sym,
    Reach (cfg .ci (E fr cs al p v res) ⟨[], [], X, C, D, I, []⟩)
      (cfg .rd (E fr cs al p v res) ⟨[], [], X, C, D, [], []⟩) (I.length + 1)
  | [] => (Reach.one (ci_nil [] [] X C D [] fr cs al p v res)).mono (by simp)
  | u :: I => by simpa using Reach.cons (ci_cons [] [] X C D [] fr cs al p v res u I) (run_ci C D v res I)

theorem run_rd (v res : Bool) : ∀ (D C : List Sym),
    Reach (cfg .rd (E fr cs al p v res) ⟨[], [], X, C, D, [], []⟩)
      (cfg .st (E false (cs || (res == p)) al false false false) ⟨[], [], X, D.reverse ++ C, [], [], []⟩)
      (D.length + 1)
  | [], C => (Reach.one (rd_nil [] [] X C [] [] fr cs al p v res)).mono (by simp)
  | d :: D, C => by
    simpa using Reach.cons (rd_cons [] [] X C [] [] fr cs al p v res d D) (run_rd v res D (d :: C))

/-- **Um literal inteiro**: do fim do índice à consulta e à restauração do certificado. -/
theorem run_lit (C I : List Sym) (v res : Bool) (h : I.head?.all (· = (false, true)) = true) :
    Reach (cfg .ix (E fr cs al p v res) ⟨[], [], sL :: X, C, [], I, []⟩)
      (cfg .st (E false (cs || (lookup I C == p)) al false false false) ⟨[], [], X, C, [], [], []⟩)
      (1 + (C.length + 1) * (C.length + I.length + 3) + (I.length + 2) + (C.length + 1)) := by
  obtain ⟨C', D', I', J', v', hD, hI, hr⟩ := run_en X fr cs al p C.length C [] I false false le_rfl
  have hDl : D'.length ≤ C.length := by
    have := congrArg List.length hD; simp at this; omega
  have h1 := ((((Reach.one (ix_fim_ok [] [] X C [] I [] fr cs al p v res h)).trans hr).trans
    (run_cj X fr cs al p C' D' I' v' (lookup I C) J')).trans
    (run_ci X fr cs al p C' D' v' (lookup I C) I')).trans (run_rd X fr cs al p v' (lookup I C) D' C')
  simp only [List.reverse_nil, List.nil_append] at hD
  rw [hD] at h1
  exact h1.mono (by omega)

end Consulta2


/-! ### A fase 1 inteira -/

/-- Custo por símbolo da fórmula (um literal com consulta, no pior caso). -/
def Q (M : ℕ) : ℕ := (M + 1) * (2 * M + 3) + 3 * M + 6

theorem Q_ge (M : ℕ) : 3 * M + 6 ≤ Q M := by unfold Q; omega

theorem run_fase1 (C : List Sym) (M : ℕ) (hC : C.length ≤ M) : ∀ X : List Sym,
    (∀ fr cs al, X.length ≤ M →
      Reach (cfg .st (E fr cs al false false false) ⟨[], [], X, C, [], [], []⟩)
        (fim (evalStart C fr cs al X)) ((X.length + 1) * Q M)) ∧
    (∀ p I fr cs al, I.length + X.length ≤ M →
      Reach (cfg .ix (E fr cs al p false false) ⟨[], [], X, C, [], I, []⟩)
        (fim (evalIdx C p I cs al X)) ((X.length + 1) * Q M))
  | [] => by
    have hQ := Q_ge M
    refine ⟨fun fr cs al _ => ?_, fun p I fr cs al hI => ?_⟩
    · have h := Reach.cons (st_nil [] [] C [] [] [] fr cs al false false false)
        (run_oc fr cs al false false (fr && al) C)
      rw [evalStart]
      exact h.mono (by simp; omega)
    · have h := Reach.cons (ix_nil [] [] C [] I [] fr cs al p false false) (run_rejeita [] C I)
      rw [evalIdx]
      exact h.mono (by simp at hI ⊢; omega)
  | s :: X => by
    obtain ⟨ih1, ih2⟩ := run_fase1 C M hC X
    have hQ := Q_ge M
    refine ⟨fun fr cs al hX => ?_, fun p I fr cs al hI => ?_⟩
    · simp only [List.length_cons] at hX
      rcases s with ⟨a, b⟩
      cases a
      · -- início de literal
        have h := Reach.cons (st_lit [] [] X C [] [] [] fr cs al false false false b)
          (ih2 b [] fr cs al (by simp; omega))
        have he : evalStart C fr cs al ((false, b) :: X) = evalIdx C b [] cs al X := by
          rw [evalStart]; simp [sC]
        rw [he]
        exact h.mono (by simp; nlinarith)
      · cases b
        · -- `sL` no início: malformado
          have h := Reach.cons (st_bad [] [] X C [] [] [] fr cs al false false false (true, false)
            (by simp [sC]) rfl) (run_rejeita X C [])
          have he : evalStart C fr cs al ((true, false) :: X) = false := by
            rw [evalStart]; simp [sC]
          rw [he]
          exact h.mono (by simp; nlinarith)
        · -- fim de cláusula
          have h := Reach.cons (st_sC [] [] X C [] [] [] fr cs al false false false)
            (ih1 true false (al && cs) (by omega))
          have he : evalStart C fr cs al ((true, true) :: X) =
              evalStart C true false (al && cs) X := by
            rw [evalStart]; simp [sC]
          rw [he]
          exact h.mono (by simp; nlinarith)
    · simp only [List.length_cons] at hI
      rcases s with ⟨a, b⟩
      cases a
      · -- bit do índice
        have h := Reach.cons (ix_bit [] [] X C [] I [] fr cs al p false false b)
          (ih2 p ((false, b) :: I) fr cs al (by simp; omega))
        have he : evalIdx C p I cs al ((false, b) :: X) = evalIdx C p ((false, b) :: I) cs al X := by
          rw [evalIdx]; simp [sC]
        rw [he]
        exact h.mono (by simp; nlinarith)
      · cases b
        · -- fim do literal
          by_cases hc : I.head?.all (· = (false, true)) = true
          · have hl := run_lit X fr cs al p C I false false hc
            have h := hl.trans (ih1 false (cs || (lookup I C == p)) al (by omega))
            have he : evalIdx C p I cs al ((true, false) :: X) =
                evalStart C false (cs || (lookup I C == p)) al X := by
              rw [evalIdx]; simp [sC, hc]
            rw [he]
            refine h.mono ?_
            have hm : (C.length + 1) * (C.length + I.length + 3) ≤ (M + 1) * (2 * M + 3) :=
              Nat.mul_le_mul (by omega) (by omega)
            simp only [List.length_cons]
            unfold Q at hQ ⊢
            nlinarith
          · have hc' : I.head?.all (· = (false, true)) = false := by simpa using hc
            have h := Reach.cons (ix_fim_bad [] [] X C [] I [] fr cs al p false false hc')
              (run_rejeita X C I)
            have he : evalIdx C p I cs al ((true, false) :: X) = false := by
              rw [evalIdx]; simp [sC, hc']
            rw [he]
            exact h.mono (by simp; nlinarith)
        · -- `sC` dentro do literal: malformado
          have h := Reach.cons (ix_sC [] [] X C [] I [] fr cs al p false false) (run_rejeita X C I)
          have he : evalIdx C p I cs al ((true, true) :: X) = false := by
            rw [evalIdx]; simp [sC]
          rw [he]
          exact h.mono (by simp; nlinarith)


/-! ### A execução completa e a cota polinomial -/

theorem decC_length_le : ∀ y : List Bool, (decC y).length ≤ y.length
  | a :: b :: r => by
    simp only [decC]
    split_ifs
    · have := decC_length_le r; simp; omega
    · simp only [List.length_cons]; omega
  | [a] => by simp [decC]
  | [] => by simp [decC]

theorem syms_length_le : ∀ l : List Bool, (syms l).length ≤ l.length
  | a :: b :: r => by have := syms_length_le r; simp [syms]; omega
  | [a] => by simp [syms]
  | [] => by simp [syms]

theorem initList_v (y : List Bool) : initList verifTM y = cfg .rx (S0 none) ⟨y, [], [], [], [], [], []⟩ := by
  simp only [initList, cfg, verifTM]
  congr 1
  funext k
  cases k <;> rfl

theorem haltList_v (b : Bool) : haltList verifTM [b] = fim b := by
  simp only [haltList, fim, verifTM]
  congr 1
  funext k
  cases k <;> rfl

theorem run_total (y : List Bool) :
    Reach (cfg .rx (S0 none) ⟨y, [], [], [], [], [], []⟩) (fim (verif y)) (2 * (y.length + 2) ^ 3) := by
  set n := y.length with hn
  have hdec := dec_length_le y
  have hdecC := decC_length_le y
  have hX := syms_length_le (dec y)
  have hC := syms_length_le (decC y)
  have h0 := run_rx [] [] [] [] [] y none []
  simp only [Option.toList_none, List.nil_append, List.append_nil] at h0
  by_cases hev : (dec y).length % 2 = 0
  · simp only [hev, ↓reduceIte] at h0
    have h1 := run_tx (decC y) [] [] [] [] (syms (dec y)).reverse []
    have h2 := run_rc (syms (dec y)) [] [] [] [] (decC y) []
    have h3 := run_tc (syms (dec y)) [] [] [] (syms (decC y)).reverse []
    have h4 := (run_fase1 (syms (decC y)) n (by omega) (syms (dec y))).1 true false true (by omega)
    simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at h1 h2 h3
    have hv : verif y = evalStart (syms (decC y)) true false true (syms (dec y)) := by
      simp [verif, hev]
    rw [hv]
    refine ((((h0.trans h1).trans h2).trans h3).trans h4).mono ?_
    have hQ : (syms (dec y)).length * Q n + Q n ≤ (n + 1) * Q n := by
      have := Nat.mul_le_mul_right (Q n) (show (syms (dec y)).length ≤ n by omega)
      nlinarith
    unfold Q at hQ ⊢
    nlinarith
  · simp only [hev, ↓reduceIte] at h0
    have h1 := run_dk (syms (dec y)).reverse [] [] [] [] [] (decC y)
    have h2 := run_dt (syms (dec y)).reverse
    have hv : verif y = false := by simp [verif, hev]
    rw [hv]
    refine ((h0.trans h1).trans h2).mono ?_
    simp only [List.length_reverse]
    have h4 : 4 * (n + 2) ≤ (n + 2) ^ 3 := by
      have h : 4 ≤ (n + 2) ^ 2 := by nlinarith
      calc 4 * (n + 2) ≤ (n + 2) ^ 2 * (n + 2) := Nat.mul_le_mul_right _ h
        _ = (n + 2) ^ 3 := by ring
    omega

/-- **O verificador de SAT roda em tempo polinomial** (`2 (n + 2)³` passos). -/
noncomputable def verifComputavel : TM2ComputableInPolyTime cod encodeBool verif where
  tm := verifTM
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 2 * (Polynomial.X + 2) ^ 3
  outputsFun y := by
    have hr := run_total y
    have hk := (Classical.choose_spec hr).1
    have he := (Classical.choose_spec hr).2
    have hin : List.map (Equiv.refl Bool).invFun (cod y) = y := by simp [cod]
    have hout : List.map (Equiv.refl Bool).invFun (encodeBool (verif y)) = [verif y] := by
      simp [encodeBool]
    refine ⟨⟨Classical.choose hr, ?_⟩, ?_⟩
    · rw [hin, hout, initList_v, Option.map_some, haltList_v]
      exact he
    · simp only [cod, id, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_ofNat]
      exact hk

/-- **SAT ∈ NP** sobre `Turing.FinTM2`: o verificador `verif` em tempo polinomial e certificados
de tamanho `≤ |x|`. -/
theorem sat_em_NP : SAT ∈ classeNP := sat_em_NP_de verifComputavel

end ATK.SatNPMaquina

#print axioms ATK.SatNPMaquina.rx_nil
#print axioms ATK.SatNPMaquina.rx_one
#print axioms ATK.SatNPMaquina.rx_eq_none
#print axioms ATK.SatNPMaquina.rx_eq_some
#print axioms ATK.SatNPMaquina.rx_neq
#print axioms ATK.SatNPMaquina.tx_cons
#print axioms ATK.SatNPMaquina.tx_nil
#print axioms ATK.SatNPMaquina.rc_nil
#print axioms ATK.SatNPMaquina.rc_one
#print axioms ATK.SatNPMaquina.rc_cons
#print axioms ATK.SatNPMaquina.tc_cons
#print axioms ATK.SatNPMaquina.tc_nil
#print axioms ATK.SatNPMaquina.st_nil
#print axioms ATK.SatNPMaquina.st_sC
#print axioms ATK.SatNPMaquina.st_bad
#print axioms ATK.SatNPMaquina.st_lit
#print axioms ATK.SatNPMaquina.ix_nil
#print axioms ATK.SatNPMaquina.ix_sC
#print axioms ATK.SatNPMaquina.ix_fim_ok
#print axioms ATK.SatNPMaquina.ix_fim_bad
#print axioms ATK.SatNPMaquina.ix_bit
#print axioms ATK.SatNPMaquina.en_nil
#print axioms ATK.SatNPMaquina.en_sL_vazio
#print axioms ATK.SatNPMaquina.en_sL_cheio
#print axioms ATK.SatNPMaquina.en_sym
#print axioms ATK.SatNPMaquina.cm_nil_vazio
#print axioms ATK.SatNPMaquina.cm_nil_cheio
#print axioms ATK.SatNPMaquina.cm_sL_vazio
#print axioms ATK.SatNPMaquina.cm_sL_cheio
#print axioms ATK.SatNPMaquina.cm_sym_vazio
#print axioms ATK.SatNPMaquina.cm_sym_igual
#print axioms ATK.SatNPMaquina.cm_sym_dif
#print axioms ATK.SatNPMaquina.sk_nil
#print axioms ATK.SatNPMaquina.sk_sL
#print axioms ATK.SatNPMaquina.sk_sym
#print axioms ATK.SatNPMaquina.rj_cons
#print axioms ATK.SatNPMaquina.rj_nil
#print axioms ATK.SatNPMaquina.cj_cons
#print axioms ATK.SatNPMaquina.cj_nil
#print axioms ATK.SatNPMaquina.ci_cons
#print axioms ATK.SatNPMaquina.ci_nil
#print axioms ATK.SatNPMaquina.rd_cons
#print axioms ATK.SatNPMaquina.rd_nil
#print axioms ATK.SatNPMaquina.oc_cons
#print axioms ATK.SatNPMaquina.oc_nil
#print axioms ATK.SatNPMaquina.dx_cons
#print axioms ATK.SatNPMaquina.dx_nil
#print axioms ATK.SatNPMaquina.di_cons
#print axioms ATK.SatNPMaquina.di_nil
#print axioms ATK.SatNPMaquina.dc_cons
#print axioms ATK.SatNPMaquina.dc_nil
#print axioms ATK.SatNPMaquina.dk_cons
#print axioms ATK.SatNPMaquina.dk_nil
#print axioms ATK.SatNPMaquina.dt_cons
#print axioms ATK.SatNPMaquina.dt_nil
#print axioms ATK.SatNPMaquina.Reach.refl
#print axioms ATK.SatNPMaquina.Reach.mono
#print axioms ATK.SatNPMaquina.Reach.trans
#print axioms ATK.SatNPMaquina.Reach.one
#print axioms ATK.SatNPMaquina.Reach.cons
#print axioms ATK.SatNPMaquina.run_rx
#print axioms ATK.SatNPMaquina.run_tx
#print axioms ATK.SatNPMaquina.run_rc
#print axioms ATK.SatNPMaquina.run_tc
#print axioms ATK.SatNPMaquina.run_dk
#print axioms ATK.SatNPMaquina.run_dt
#print axioms ATK.SatNPMaquina.run_dx
#print axioms ATK.SatNPMaquina.run_di
#print axioms ATK.SatNPMaquina.run_dc
#print axioms ATK.SatNPMaquina.run_rejeita
#print axioms ATK.SatNPMaquina.run_oc
#print axioms ATK.SatNPMaquina.run_rj
#print axioms ATK.SatNPMaquina.run_sk
#print axioms ATK.SatNPMaquina.run_cm_igual
#print axioms ATK.SatNPMaquina.run_cm_dif
#print axioms ATK.SatNPMaquina.run_en
#print axioms ATK.SatNPMaquina.run_cj
#print axioms ATK.SatNPMaquina.run_ci
#print axioms ATK.SatNPMaquina.run_rd
#print axioms ATK.SatNPMaquina.run_lit
#print axioms ATK.SatNPMaquina.Q_ge
#print axioms ATK.SatNPMaquina.run_fase1
#print axioms ATK.SatNPMaquina.decC_length_le
#print axioms ATK.SatNPMaquina.syms_length_le
#print axioms ATK.SatNPMaquina.initList_v
#print axioms ATK.SatNPMaquina.haltList_v
#print axioms ATK.SatNPMaquina.run_total
#print axioms ATK.SatNPMaquina.verifComputavel
#print axioms ATK.SatNPMaquina.sat_em_NP
