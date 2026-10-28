import ATK.IntegracaoFCPNP

/-!
# ATK — Os quatro transcodificadores entre as codificações do ATK e do formal-conjectures

Constrói quatro máquinas `Turing.FinTM2`, com prova de correção e de tempo **linear**:

1. `cruaFC` : palavra crua `w` ↦ `encFC w` (cada bit `b` vira `[true, b, false]`);
2. `fcCrua` : `encFC w` ↦ `w`;
3. `parFC`  : `encFCPar (w, c)` ↦ `par w c` (bits de `w` duplicados, separador `01`, depois `c`);
4. `separaFC` : `u` ↦ `encFCPar (dec u, cer u)`.

Todas usam duas pilhas sobre `Bool` (`false` = entrada/saída, `true` = auxiliar), como o
decodificador `ATK.ModeloPNP.decTM`: uma fase de leitura empilha a saída na auxiliar, e a fase
final a devolve à pilha principal.

Com elas, `transcodificadores : Transcodificadores`, e portanto

* **`pneNP_iff_fc_incondicional : PneNP ↔ P_FC ≠ NP_FC`** — o enunciado de P ≠ NP do ATK e o do
  formal-conjectures (Google DeepMind) são equivalentes, **sem hipóteses**.

Nada aqui decide P vs NP. **CLOSED_MATH continua false.**
-/

namespace ATK.TranscodificadoresFC

open Turing Computability Function ATK.LigacaoPNP ATK.ModeloPNP ATK.IntegracaoFCPNP
  ATK.FC.BitstringEncoding
open Turing.TM2.Stmt

/-! ## As codificações, por extenso -/

theorem encFC_nil : encFC [] = [] := rfl

theorem encFC_cons (b : Bool) (w : Palavra) : encFC (b :: w) = true :: b :: false :: encFC w :=
  rfl

theorem length_encFC : ∀ w : Palavra, (encFC w).length = 3 * w.length
  | [] => rfl
  | b :: w => by rw [encFC_cons]; simp only [List.length_cons, length_encFC w]; ring

theorem encFCPar_eq (w c : Palavra) : encFCPar (w, c) = delimit (encFC w) ++ encFC c := rfl

theorem delimit_encFC_nil : delimit (encFC []) = [false] := rfl

theorem delimit_encFC_cons (b : Bool) (w : Palavra) :
    delimit (encFC (b :: w)) = true :: true :: true :: b :: true :: false :: delimit (encFC w) := by
  rw [encFC_cons]
  rfl

/-- Os dois bits duplicados do par do ATK. -/
def dup (w : Palavra) : Palavra := w.flatMap fun b => [b, b]

theorem dup_nil : dup [] = [] := rfl

theorem dup_cons (b : Bool) (w : Palavra) : dup (b :: w) = b :: b :: dup w := rfl

theorem par_eq (w c : Palavra) : par w c = dup w ++ false :: true :: c := by
  simp [par, dup]

abbrev σT := Option Bool × Option Bool

/-! ## Máquina 1: palavra crua ↦ `encFC` -/

namespace M1

abbrev St := Turing.TM2.Stmt (fun _ : Bool => Bool) (Fin 2) σT

/-- Lê um bit `b` e empilha `true, b, false` na auxiliar. -/
def passo0 : St :=
  pop false (fun s o => (o, s.2))
    (branch (fun s => s.1.isSome)
      (push true (fun _ => true) (push true (fun s => s.1.getD false) (push true (fun _ => false)
        (load (fun _ => (none, none)) (goto fun _ => 0)))))
      (load (fun _ => (none, none)) (goto fun _ => 1)))

/-- Devolve a auxiliar para a saída. -/
def passo1 : St :=
  pop true (fun _ o => (o, none))
    (branch (fun s => s.1.isSome)
      (push false (fun s => s.1.getD false) (load (fun _ => (none, none)) (goto fun _ => 1)))
      halt)

def prog : Fin 2 → St
  | 0 => passo0
  | 1 => passo1

abbrev tm : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ _ := Bool
  Λ := Fin 2
  main := 0
  σ := σT
  initialState := (none, none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := prog

abbrev Cfg := Turing.TM2.Cfg (fun _ : Bool => Bool) (Fin 2) σT

def cfg (l : Fin 2) (x A : List Bool) : Cfg := ⟨some l, (none, none), pil x A⟩

abbrev step := Turing.TM2.step prog

theorem s0_cons (b r A) : step (cfg 0 (b :: r) A) = some (cfg 0 r (false :: b :: true :: A)) := by
  simp [cfg, step, prog, passo0, Turing.TM2.stepAux, pil_false, upd_false, pil_true, upd_true]

theorem s0_nil (A) : step (cfg 0 [] A) = some (cfg 1 [] A) := by
  simp [cfg, step, prog, passo0, Turing.TM2.stepAux, pil_false, upd_false]

theorem s1_cons (B a A) : step (cfg 1 B (a :: A)) = some (cfg 1 (a :: B) A) := by
  simp [cfg, step, prog, passo1, Turing.TM2.stepAux, pil_true, upd_true, pil_false, upd_false]

theorem s1_nil (B) : step (cfg 1 B []) = some ⟨none, (none, none), pil B []⟩ := by
  simp [cfg, step, prog, passo1, Turing.TM2.stepAux, pil_true, upd_true]

theorem one {c c' : Cfg} (h : step c = some c') : flip bind step (some c) = some c' := h

theorem run1 : ∀ (A B : List Bool),
    (flip bind step)^[A.length + 1] (some (cfg 1 B A)) =
      some ⟨none, (none, none), pil (A.reverse ++ B) []⟩
  | [], B => by rw [List.length_nil, zero_add, iterate_one]; exact s1_nil B
  | a :: A, B => by
    rw [List.length_cons, iterate_succ_apply, one (s1_cons B a A), run1 A (a :: B)]
    simp

theorem run0 : ∀ (x A : List Bool),
    (flip bind step)^[x.length + 1] (some (cfg 0 x A)) =
      some (cfg 1 [] ((encFC x).reverse ++ A))
  | [], A => by
    rw [List.length_nil, zero_add, iterate_one]
    exact s0_nil A
  | b :: r, A => by
    rw [List.length_cons, iterate_succ_apply, one (s0_cons b r A), run0 r]
    simp [encFC_cons]

theorem initList_eq (x : List Bool) : initList tm x = cfg 0 x [] := by
  simp only [initList, cfg, tm]
  congr 1
  funext k
  cases k <;> (simp [pil]; try rfl)

theorem haltList_eq (y : List Bool) :
    haltList tm y = (⟨none, (none, none), pil y []⟩ : Cfg) := by
  simp only [haltList, tm]
  congr 1
  funext k
  cases k <;> (simp [pil]; try rfl)

/-- **Palavra crua ↦ `encFC`**, em tempo `4n + 2`. -/
noncomputable def computavel : TM2ComputableInPolyTime cod encFC id where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 4 * Polynomial.X + 2
  outputsFun x := by
    have hin : List.map (Equiv.refl Bool).invFun (cod x) = x := by simp [cod]
    have hout : List.map (Equiv.refl Bool).invFun (encFC (id x)) = encFC x := by simp
    refine ⟨⟨(x.length + 1) + ((encFC x).length + 1), ?_⟩, ?_⟩
    · rw [hin, hout, initList_eq, Option.map_some, haltList_eq]
      show (flip bind step)^[(x.length + 1) + ((encFC x).length + 1)] (some (cfg 0 x [])) = _
      rw [add_comm, iterate_add_apply, run0 x [], List.append_nil]
      have := run1 (encFC x).reverse []
      rw [List.length_reverse, List.reverse_reverse, List.append_nil] at this
      rw [this]
      rfl
    · change (x.length + 1) + ((encFC x).length + 1) ≤
        Polynomial.eval (cod x).length (4 * Polynomial.X + 2)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat, length_encFC, cod, id]
      omega

end M1

/-! ## Máquina 2: `encFC` ↦ palavra crua -/

namespace M2

abbrev St := Turing.TM2.Stmt (fun _ : Bool => Bool) (Fin 2) σT

/-- Lê um bloco `true, b, false` e empilha `b` na auxiliar. -/
def passo0 : St :=
  pop false (fun s o => (o, s.2))
    (branch (fun s => s.1.isSome)
      (pop false (fun s o => (s.1, o)) (push true (fun s => s.2.getD false)
        (pop false (fun s _ => s) (load (fun _ => (none, none)) (goto fun _ => 0)))))
      (load (fun _ => (none, none)) (goto fun _ => 1)))

def prog : Fin 2 → St
  | 0 => passo0
  | 1 => M1.passo1

abbrev tm : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ _ := Bool
  Λ := Fin 2
  main := 0
  σ := σT
  initialState := (none, none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := prog

abbrev Cfg := Turing.TM2.Cfg (fun _ : Bool => Bool) (Fin 2) σT

def cfg (l : Fin 2) (x A : List Bool) : Cfg := ⟨some l, (none, none), pil x A⟩

abbrev step := Turing.TM2.step prog

theorem s0_cons (b rest A) :
    step (cfg 0 (true :: b :: false :: rest) A) = some (cfg 0 rest (b :: A)) := by
  simp [cfg, step, prog, passo0, Turing.TM2.stepAux, pil_false, upd_false, pil_true, upd_true]

theorem s0_nil (A) : step (cfg 0 [] A) = some (cfg 1 [] A) := by
  simp [cfg, step, prog, passo0, Turing.TM2.stepAux, pil_false, upd_false]

theorem s1_cons (B a A) : step (cfg 1 B (a :: A)) = some (cfg 1 (a :: B) A) := by
  simp [cfg, step, prog, M1.passo1, Turing.TM2.stepAux, pil_true, upd_true, pil_false, upd_false]

theorem s1_nil (B) : step (cfg 1 B []) = some ⟨none, (none, none), pil B []⟩ := by
  simp [cfg, step, prog, M1.passo1, Turing.TM2.stepAux, pil_true, upd_true]

theorem one {c c' : Cfg} (h : step c = some c') : flip bind step (some c) = some c' := h

theorem run1 : ∀ (A B : List Bool),
    (flip bind step)^[A.length + 1] (some (cfg 1 B A)) =
      some ⟨none, (none, none), pil (A.reverse ++ B) []⟩
  | [], B => by rw [List.length_nil, zero_add, iterate_one]; exact s1_nil B
  | a :: A, B => by
    rw [List.length_cons, iterate_succ_apply, one (s1_cons B a A), run1 A (a :: B)]
    simp

theorem run0 : ∀ (w A : List Bool),
    (flip bind step)^[w.length + 1] (some (cfg 0 (encFC w) A)) =
      some (cfg 1 [] (w.reverse ++ A))
  | [], A => by
    rw [List.length_nil, zero_add, iterate_one, encFC_nil]
    exact s0_nil A
  | b :: w, A => by
    rw [List.length_cons, iterate_succ_apply, encFC_cons, one (s0_cons b (encFC w) A), run0 w]
    simp

theorem initList_eq (x : List Bool) : initList tm x = cfg 0 x [] := by
  simp only [initList, cfg, tm]
  congr 1
  funext k
  cases k <;> (simp [pil]; try rfl)

theorem haltList_eq (y : List Bool) :
    haltList tm y = (⟨none, (none, none), pil y []⟩ : Cfg) := by
  simp only [haltList, tm]
  congr 1
  funext k
  cases k <;> (simp [pil]; try rfl)

/-- **`encFC` ↦ palavra crua**, em tempo `2n + 2` (entrada de tamanho `3n`). -/
noncomputable def computavel : TM2ComputableInPolyTime encFC cod id where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 2
  outputsFun x := by
    have hin : List.map (Equiv.refl Bool).invFun (encFC x) = encFC x := by simp
    have hout : List.map (Equiv.refl Bool).invFun (cod (id x)) = x := by simp [cod]
    refine ⟨⟨(x.reverse.length + 1) + (x.length + 1), ?_⟩, ?_⟩
    · rw [hin, hout, initList_eq, Option.map_some, haltList_eq]
      show (flip bind step)^[(x.reverse.length + 1) + (x.length + 1)]
        (some (cfg 0 (encFC x) [])) = _
      rw [iterate_add_apply, run0 x [], List.append_nil, run1 x.reverse [],
        List.reverse_reverse, List.append_nil]
      rfl
    · change (x.reverse.length + 1) + (x.length + 1) ≤
        Polynomial.eval (encFC x).length (Polynomial.X + 2)
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat, length_encFC,
        List.length_reverse]
      omega

end M2

/-! ## Máquina 3: `encFCPar (w, c)` ↦ `par w c` -/

namespace M3

abbrev St := Turing.TM2.Stmt (fun _ : Bool => Bool) (Fin 3) σT

/-- Lê um bloco de 6 símbolos `t t t b t f` e empilha `b, b`; no terminador `f`, empilha o
separador `0, 1` e passa a ler `c`. -/
def passo0 : St :=
  pop false (fun s o => (o, s.2))
    (branch (fun s => decide (s.1 = some true))
      (pop false (fun s _ => s) (pop false (fun s _ => s) (pop false (fun s o => (s.1, o))
        (pop false (fun s _ => s) (pop false (fun s _ => s)
          (push true (fun s => s.2.getD false) (push true (fun s => s.2.getD false)
            (load (fun _ => (none, none)) (goto fun _ => 0)))))))))
      (push true (fun _ => false) (push true (fun _ => true)
        (load (fun _ => (none, none)) (goto fun _ => 1)))))

/-- Lê um bloco `true, b, false` de `c` e empilha `b`. -/
def passo1 : St :=
  pop false (fun s o => (o, s.2))
    (branch (fun s => s.1.isSome)
      (pop false (fun s o => (s.1, o)) (push true (fun s => s.2.getD false)
        (pop false (fun s _ => s) (load (fun _ => (none, none)) (goto fun _ => 1)))))
      (load (fun _ => (none, none)) (goto fun _ => 2)))

/-- Devolve a auxiliar para a saída. -/
def passo2 : St :=
  pop true (fun _ o => (o, none))
    (branch (fun s => s.1.isSome)
      (push false (fun s => s.1.getD false) (load (fun _ => (none, none)) (goto fun _ => 2)))
      halt)

def prog : Fin 3 → St
  | 0 => passo0
  | 1 => passo1
  | 2 => passo2

abbrev tm : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := σT
  initialState := (none, none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := prog

abbrev Cfg := Turing.TM2.Cfg (fun _ : Bool => Bool) (Fin 3) σT

def cfg (l : Fin 3) (x A : List Bool) : Cfg := ⟨some l, (none, none), pil x A⟩

abbrev step := Turing.TM2.step prog

theorem s0_grp (b rest A) :
    step (cfg 0 (true :: true :: true :: b :: true :: false :: rest) A) =
      some (cfg 0 rest (b :: b :: A)) := by
  simp [cfg, step, prog, passo0, Turing.TM2.stepAux, pil_false, upd_false, pil_true, upd_true]

theorem s0_end (rest A) : step (cfg 0 (false :: rest) A) = some (cfg 1 rest (true :: false :: A)) := by
  simp [cfg, step, prog, passo0, Turing.TM2.stepAux, pil_false, upd_false, pil_true, upd_true]

theorem s1_cons (b rest A) :
    step (cfg 1 (true :: b :: false :: rest) A) = some (cfg 1 rest (b :: A)) := by
  simp [cfg, step, prog, passo1, Turing.TM2.stepAux, pil_false, upd_false, pil_true, upd_true]

theorem s1_nil (A) : step (cfg 1 [] A) = some (cfg 2 [] A) := by
  simp [cfg, step, prog, passo1, Turing.TM2.stepAux, pil_false, upd_false]

theorem s2_cons (B a A) : step (cfg 2 B (a :: A)) = some (cfg 2 (a :: B) A) := by
  simp [cfg, step, prog, passo2, Turing.TM2.stepAux, pil_true, upd_true, pil_false, upd_false]

theorem s2_nil (B) : step (cfg 2 B []) = some ⟨none, (none, none), pil B []⟩ := by
  simp [cfg, step, prog, passo2, Turing.TM2.stepAux, pil_true, upd_true]

theorem one {c c' : Cfg} (h : step c = some c') : flip bind step (some c) = some c' := h

theorem run2 : ∀ (A B : List Bool),
    (flip bind step)^[A.length + 1] (some (cfg 2 B A)) =
      some ⟨none, (none, none), pil (A.reverse ++ B) []⟩
  | [], B => by rw [List.length_nil, zero_add, iterate_one]; exact s2_nil B
  | a :: A, B => by
    rw [List.length_cons, iterate_succ_apply, one (s2_cons B a A), run2 A (a :: B)]
    simp

theorem run1 : ∀ (c A : List Bool),
    (flip bind step)^[c.length + 1] (some (cfg 1 (encFC c) A)) =
      some (cfg 2 [] (c.reverse ++ A))
  | [], A => by
    rw [List.length_nil, zero_add, iterate_one, encFC_nil]
    exact s1_nil A
  | b :: c, A => by
    rw [List.length_cons, iterate_succ_apply, encFC_cons, one (s1_cons b (encFC c) A), run1 c]
    simp

theorem run0 : ∀ (w R A : List Bool),
    (flip bind step)^[w.length + 1] (some (cfg 0 (delimit (encFC w) ++ R) A)) =
      some (cfg 1 R (true :: false :: ((dup w).reverse ++ A)))
  | [], R, A => by
    rw [List.length_nil, zero_add, iterate_one, delimit_encFC_nil, List.singleton_append,
      one (s0_end R A)]
    rfl
  | b :: w, R, A => by
    rw [List.length_cons, iterate_succ_apply, delimit_encFC_cons]
    simp only [List.cons_append]
    rw [one (s0_grp b (delimit (encFC w) ++ R) A), run0 w R (b :: b :: A), dup_cons]
    simp

theorem initList_eq (x : List Bool) : initList tm x = cfg 0 x [] := by
  simp only [initList, cfg, tm]
  congr 1
  funext k
  cases k <;> (simp [pil]; try rfl)

theorem haltList_eq (y : List Bool) :
    haltList tm y = (⟨none, (none, none), pil y []⟩ : Cfg) := by
  simp only [haltList, tm]
  congr 1
  funext k
  cases k <;> (simp [pil]; try rfl)

theorem length_dup (w : Palavra) : (dup w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [dup_cons]; simp only [List.length_cons, ih]; ring

/-- **`encFCPar (w, c)` ↦ `par w c`**, em tempo linear. -/
noncomputable def computavel :
    TM2ComputableInPolyTime encFCPar cod (fun p : Palavra × Palavra => par p.1 p.2) where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 4
  outputsFun p := by
    obtain ⟨w, c⟩ := p
    have hin : List.map (Equiv.refl Bool).invFun (encFCPar (w, c)) =
        delimit (encFC w) ++ encFC c := by simp [encFCPar_eq]
    have hout : List.map (Equiv.refl Bool).invFun (cod (par (w, c).1 (w, c).2)) =
        dup w ++ false :: true :: c := by simp [cod, par_eq]
    refine ⟨⟨((c.reverse ++ true :: false :: (dup w).reverse).length + 1) +
      ((c.length + 1) + (w.length + 1)), ?_⟩, ?_⟩
    · rw [hin, hout, initList_eq, Option.map_some, haltList_eq]
      show (flip bind step)^[((c.reverse ++ true :: false :: (dup w).reverse).length + 1) +
        ((c.length + 1) + (w.length + 1))] (some (cfg 0 (delimit (encFC w) ++ encFC c) [])) = _
      rw [iterate_add_apply _ ((c.reverse ++ true :: false :: (dup w).reverse).length + 1),
        iterate_add_apply _ (c.length + 1) (w.length + 1), run0 w (encFC c) [], List.append_nil,
        run1 c (true :: false :: (dup w).reverse), run2 _ []]
      simp
      rfl
    · change ((c.reverse ++ true :: false :: (dup w).reverse).length + 1) +
        ((c.length + 1) + (w.length + 1)) ≤
        Polynomial.eval (encFCPar (w, c)).length (Polynomial.X + 4)
      simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat, encFCPar_eq,
        List.length_append, length_delimit, length_encFC, List.length_reverse,
        List.length_cons, length_dup]
      omega

end M3

/-! ## Máquina 4: `u` ↦ `encFCPar (dec u, cer u)` -/

namespace M4

abbrev St := Turing.TM2.Stmt (fun _ : Bool => Bool) (Fin 3) σT

/-- Lê um par `a b`: se `a = b`, empilha o bloco `t t t a t f`; se `a ≠ b`, empilha o terminador
e passa a copiar o resto; se a entrada acaba, empilha o terminador e termina. -/
def passo0 : St :=
  pop false (fun s o => (o, s.2))
    (branch (fun s => s.1.isSome)
      (pop false (fun s o => (s.1, o))
        (branch (fun s => s.2.isSome)
          (branch (fun s => decide (s.1 = s.2))
            (push true (fun _ => true) (push true (fun _ => true) (push true (fun _ => true)
              (push true (fun s => s.1.getD false) (push true (fun _ => true)
                (push true (fun _ => false) (load (fun _ => (none, none)) (goto fun _ => 0))))))))
            (push true (fun _ => false) (load (fun _ => (none, none)) (goto fun _ => 1))))
          (push true (fun _ => false) (load (fun _ => (none, none)) (goto fun _ => 2)))))
      (push true (fun _ => false) (load (fun _ => (none, none)) (goto fun _ => 2))))

/-- Copia o resto da entrada como blocos `true, b, false`. -/
def passo1 : St :=
  pop false (fun s o => (o, s.2))
    (branch (fun s => s.1.isSome)
      (push true (fun _ => true) (push true (fun s => s.1.getD false) (push true (fun _ => false)
        (load (fun _ => (none, none)) (goto fun _ => 1)))))
      (load (fun _ => (none, none)) (goto fun _ => 2)))

def prog : Fin 3 → St
  | 0 => passo0
  | 1 => passo1
  | 2 => M3.passo2

abbrev tm : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ _ := Bool
  Λ := Fin 3
  main := 0
  σ := σT
  initialState := (none, none)
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := prog

abbrev Cfg := Turing.TM2.Cfg (fun _ : Bool => Bool) (Fin 3) σT

def cfg (l : Fin 3) (x A : List Bool) : Cfg := ⟨some l, (none, none), pil x A⟩

abbrev step := Turing.TM2.step prog

theorem s0_eq (a r A) :
    step (cfg 0 (a :: a :: r) A) =
      some (cfg 0 r (false :: true :: a :: true :: true :: true :: A)) := by
  simp [cfg, step, prog, passo0, Turing.TM2.stepAux, pil_false, upd_false, pil_true, upd_true]

theorem s0_ne (a b r A) (h : a ≠ b) : step (cfg 0 (a :: b :: r) A) = some (cfg 1 r (false :: A)) := by
  simp [cfg, step, prog, passo0, Turing.TM2.stepAux, pil_false, upd_false, pil_true, upd_true, h]

theorem s0_one (a A) : step (cfg 0 [a] A) = some (cfg 2 [] (false :: A)) := by
  simp [cfg, step, prog, passo0, Turing.TM2.stepAux, pil_false, upd_false, pil_true, upd_true]

theorem s0_nil (A) : step (cfg 0 [] A) = some (cfg 2 [] (false :: A)) := by
  simp [cfg, step, prog, passo0, Turing.TM2.stepAux, pil_false, upd_false, pil_true, upd_true]

theorem s1_cons (b r A) : step (cfg 1 (b :: r) A) = some (cfg 1 r (false :: b :: true :: A)) := by
  simp [cfg, step, prog, passo1, Turing.TM2.stepAux, pil_false, upd_false, pil_true, upd_true]

theorem s1_nil (A) : step (cfg 1 [] A) = some (cfg 2 [] A) := by
  simp [cfg, step, prog, passo1, Turing.TM2.stepAux, pil_false, upd_false]

theorem s2_cons (B a A) : step (cfg 2 B (a :: A)) = some (cfg 2 (a :: B) A) := by
  simp [cfg, step, prog, M3.passo2, Turing.TM2.stepAux, pil_true, upd_true, pil_false, upd_false]

theorem s2_nil (B) : step (cfg 2 B []) = some ⟨none, (none, none), pil B []⟩ := by
  simp [cfg, step, prog, M3.passo2, Turing.TM2.stepAux, pil_true, upd_true]

theorem one {c c' : Cfg} (h : step c = some c') : flip bind step (some c) = some c' := h

theorem run2 : ∀ (A B : List Bool),
    (flip bind step)^[A.length + 1] (some (cfg 2 B A)) =
      some ⟨none, (none, none), pil (A.reverse ++ B) []⟩
  | [], B => by rw [List.length_nil, zero_add, iterate_one]; exact s2_nil B
  | a :: A, B => by
    rw [List.length_cons, iterate_succ_apply, one (s2_cons B a A), run2 A (a :: B)]
    simp

theorem run1 : ∀ (r A : List Bool),
    (flip bind step)^[r.length + 1] (some (cfg 1 r A)) =
      some (cfg 2 [] ((encFC r).reverse ++ A))
  | [], A => by
    rw [List.length_nil, zero_add, iterate_one]
    exact s1_nil A
  | b :: r, A => by
    rw [List.length_cons, iterate_succ_apply, one (s1_cons b r A), run1 r]
    simp [encFC_cons]

theorem separa_eq (a : List Bool) (b : Bool) :
    encFCPar (separa (b :: b :: a)) = true :: true :: true :: b :: true :: false ::
      encFCPar (separa a) := by
  simp only [separa, encFCPar_eq, dec, cer, ite_true, delimit_encFC_cons, List.cons_append]

theorem run0 : ∀ (u A : List Bool),
    (flip bind step)^[kPar u] (some (cfg 0 u A)) =
      some (cfg 2 [] ((encFCPar (separa u)).reverse ++ A))
  | a :: b :: r, A => by
    by_cases h : a = b
    · subst h
      simp only [kPar, ite_true]
      rw [iterate_succ_apply, one (s0_eq a r A), run0 r, separa_eq r a]
      simp
    · simp only [kPar, h, ite_false]
      rw [show r.length + 2 = r.length + 1 + 1 from rfl, iterate_succ_apply,
        one (s0_ne a b r A h), run1 r (false :: A)]
      simp [separa, dec, cer, h, encFCPar_eq, delimit_encFC_nil]
  | [a], A => by
    simp only [kPar, iterate_one]
    rw [one (s0_one a A)]
    simp [separa, dec, cer, encFCPar_eq, encFC_nil, delimit]
  | [], A => by
    simp only [kPar, iterate_one]
    rw [one (s0_nil A)]
    simp [separa, dec, cer, encFCPar_eq, encFC_nil, delimit]

theorem length_separa : ∀ u : List Bool, (encFCPar (separa u)).length ≤ 3 * u.length + 1
  | a :: b :: r => by
    by_cases h : a = b
    · subst h
      rw [separa_eq r a]
      have := length_separa r
      simp only [List.length_cons]
      omega
    · simp only [separa, dec, cer, h, ite_false, encFCPar_eq, delimit_encFC_nil,
        List.length_append, length_encFC, List.length_cons, List.length_nil]
      omega
  | [a] => by simp [separa, dec, cer, encFCPar_eq, encFC_nil]
  | [] => by simp [separa, dec, cer, encFCPar_eq, encFC_nil]

theorem initList_eq (x : List Bool) : initList tm x = cfg 0 x [] := by
  simp only [initList, cfg, tm]
  congr 1
  funext k
  cases k <;> (simp [pil]; try rfl)

theorem haltList_eq (y : List Bool) :
    haltList tm y = (⟨none, (none, none), pil y []⟩ : Cfg) := by
  simp only [haltList, tm]
  congr 1
  funext k
  cases k <;> (simp [pil]; try rfl)

/-- **`u` ↦ `encFCPar (dec u, cer u)`**, em tempo `4n + 3`. -/
noncomputable def computavel : TM2ComputableInPolyTime cod encFCPar separa where
  tm := tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 4 * Polynomial.X + 3
  outputsFun u := by
    have hin : List.map (Equiv.refl Bool).invFun (cod u) = u := by simp [cod]
    have hout : List.map (Equiv.refl Bool).invFun (encFCPar (separa u)) =
        encFCPar (separa u) := by simp
    refine ⟨⟨((encFCPar (separa u)).reverse.length + 1) + kPar u, ?_⟩, ?_⟩
    · rw [hin, hout, initList_eq, Option.map_some, haltList_eq]
      show (flip bind step)^[((encFCPar (separa u)).reverse.length + 1) + kPar u]
        (some (cfg 0 u [])) = _
      rw [iterate_add_apply, run0 u [], List.append_nil, run2 _ [], List.reverse_reverse,
        List.append_nil]
      rfl
    · have h1 := kPar_le u
      have h2 := length_separa u
      change ((encFCPar (separa u)).reverse.length + 1) + kPar u ≤
        Polynomial.eval (cod u).length (4 * Polynomial.X + 3)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_ofNat, List.length_reverse, cod, id]
      omega

end M4

/-! ## Os transcodificadores e a equivalência incondicional -/

/-- **As quatro máquinas existem.** -/
theorem transcodificadores : Transcodificadores :=
  ⟨⟨M1.computavel⟩, ⟨M2.computavel⟩, ⟨M3.computavel⟩, ⟨M4.computavel⟩⟩

/-- `L ∈ P` (ATK) ⟺ `caract L ∈ P` (formal-conjectures), sem hipóteses. -/
theorem emP_iff_fc (L : Linguagem) : EmP L ↔ caract L ∈ ATK.FC.ComplexityTheory.P :=
  emP_iff transcodificadores L

/-- `L ∈ NP` (ATK) ⟺ `caract L ∈ NP` (formal-conjectures), sem hipóteses. -/
theorem emNP_iff_fc (L : Linguagem) : EmNP L ↔ caract L ∈ ATK.FC.ComplexityTheory.NP :=
  emNP_iff transcodificadores L

/-- **O enunciado de P ≠ NP do ATK equivale ao do formal-conjectures, sem hipóteses.** -/
theorem pneNP_iff_fc_incondicional :
    PneNP ↔ ATK.FC.ComplexityTheory.P ≠ ATK.FC.ComplexityTheory.NP :=
  pneNP_iff_fc transcodificadores

end ATK.TranscodificadoresFC

#print axioms ATK.TranscodificadoresFC.length_encFC
#print axioms ATK.TranscodificadoresFC.par_eq
#print axioms ATK.TranscodificadoresFC.M1.run0
#print axioms ATK.TranscodificadoresFC.M1.run1
#print axioms ATK.TranscodificadoresFC.M2.run0
#print axioms ATK.TranscodificadoresFC.M3.run0
#print axioms ATK.TranscodificadoresFC.M3.run1
#print axioms ATK.TranscodificadoresFC.M4.run0
#print axioms ATK.TranscodificadoresFC.M4.length_separa
#print axioms ATK.TranscodificadoresFC.transcodificadores
#print axioms ATK.TranscodificadoresFC.emP_iff_fc
#print axioms ATK.TranscodificadoresFC.emNP_iff_fc
#print axioms ATK.TranscodificadoresFC.pneNP_iff_fc_incondicional
