import ATK.CookLevinJanela
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-!
# ATK — Cook–Levin, marcos CL2–CL3: o tableau e a sua correção

Para uma máquina de pilhas `M : Λ → TM2.Stmt Γ Λ σ` com rótulos, estados, pilhas e alfabetos finitos,
este módulo escreve a execução de `T` passos como uma fórmula CNF (o *tableau*) e prova que ela é
fiel:

* variáveis `lab t o`, `st t v`, `cel t k p a` — no instante `t`, o rótulo é `o`, o estado é `v`,
  a célula `p` (contada do topo) da pilha `k` é `a` (`none` = abaixo do fundo);
* `clsLinha t S` — cada uma dessas grandezas tem exatamente um valor;
* `clsTrans t S` — o passo `t → t+1`. Pela janela (marco CL1), o passo só depende do rótulo, do
  estado e das `D = profMax M` células do topo de cada pilha: um *caso* é um elemento do tipo
  finito `Caso M`, e cada caso dá cláusulas de tamanho fixo; o resto da pilha desce ou sobe em
  bloco (`cel t k (p' - |r| + D) a → cel (t+1) k p' a`). A configuração parada se repete.
* **`tableau_correto`**: a fórmula `estrutura ++ ini ++ aceita` é satisfatível se e só se alguma
  configuração inicial permitida por `ini` leva, em `T` passos, a uma parada com `y` no topo da
  pilha `k₁`.

A fórmula aqui é sobre um tipo abstrato de variáveis; a codificação em `ℕ` e a máquina que a escreve
são os marcos seguintes (CL4). **Nada aqui prova Cook–Levin. CLOSED_MATH continua false.**
-/

namespace ATK.CookLevinTableau

set_option linter.unusedSectionVars false

open Turing Function ATK.CookLevinJanela

noncomputable section

/-! ### CNF sobre um tipo qualquer de variáveis -/

/-- Cláusula e fórmula sobre variáveis `V`. -/
abbrev Cl (V : Type*) := List (V × Bool)
abbrev Fm (V : Type*) := List (Cl V)

variable {V : Type*}

/-- `τ` satisfaz `φ`: cada cláusula tem um literal verdadeiro. -/
def Sat (τ : V → Bool) (φ : Fm V) : Prop := ∀ C ∈ φ, ∃ ℓ ∈ C, τ ℓ.1 = ℓ.2

theorem sat_nil (τ : V → Bool) : Sat τ [] := by simp [Sat]

theorem sat_append {τ : V → Bool} {φ ψ : Fm V} : Sat τ (φ ++ ψ) ↔ Sat τ φ ∧ Sat τ ψ := by
  simp only [Sat, List.mem_append]
  constructor
  · intro h; exact ⟨fun C hC => h C (Or.inl hC), fun C hC => h C (Or.inr hC)⟩
  · rintro ⟨h1, h2⟩ C (hC | hC)
    · exact h1 C hC
    · exact h2 C hC

theorem sat_cons {τ : V → Bool} {C : Cl V} {φ : Fm V} :
    Sat τ (C :: φ) ↔ (∃ ℓ ∈ C, τ ℓ.1 = ℓ.2) ∧ Sat τ φ := by
  simp [Sat]

theorem sat_flatMap {α : Type*} {τ : V → Bool} {l : List α} {f : α → Fm V} :
    Sat τ (l.flatMap f) ↔ ∀ x ∈ l, Sat τ (f x) := by
  simp only [Sat, List.mem_flatMap]
  constructor
  · intro h x hx C hC; exact h C ⟨x, hx, hC⟩
  · rintro h C ⟨x, hx, hC⟩; exact h x hx C hC

theorem sat_map {α : Type*} {τ : V → Bool} {l : List α} {f : α → Cl V} :
    Sat τ (l.map f) ↔ ∀ x ∈ l, ∃ ℓ ∈ f x, τ ℓ.1 = ℓ.2 := by
  simp only [Sat, List.mem_map]
  constructor
  · intro h x hx; exact h (f x) ⟨x, hx, rfl⟩
  · rintro h C ⟨x, hx, rfl⟩; exact h x hx

theorem sat_singleton {τ : V → Bool} {C : Cl V} : Sat τ [C] ↔ ∃ ℓ ∈ C, τ ℓ.1 = ℓ.2 := by
  simp [Sat]

/-- A cláusula `P₁ ∧ … ∧ Pₙ → ℓ`. -/
def imp (P : List V) (ℓ : V × Bool) : Cl V := P.map (fun x => (x, false)) ++ [ℓ]

theorem cl_imp {τ : V → Bool} {P : List V} {ℓ : V × Bool} :
    (∃ m ∈ imp P ℓ, τ m.1 = m.2) ↔ ((∀ x ∈ P, τ x = true) → τ ℓ.1 = ℓ.2) := by
  simp only [imp, List.mem_append, List.mem_map, List.mem_singleton]
  constructor
  · rintro ⟨m, hm | rfl, h⟩ hP
    · obtain ⟨x, hx, rfl⟩ := hm
      simp only at h
      rw [hP x hx] at h
      exact absurd h (by decide)
    · exact h
  · intro h
    by_cases hP : ∀ x ∈ P, τ x = true
    · exact ⟨ℓ, Or.inr rfl, h hP⟩
    · push Not at hP
      obtain ⟨x, hx, hne⟩ := hP
      exact ⟨(x, false), Or.inl ⟨x, hx, rfl⟩, by simpa using hne⟩

/-- Todos os elementos de um tipo finito, em lista. -/
def todos (α : Type*) [Fintype α] : List α := (Finset.univ : Finset α).toList

theorem mem_todos {α : Type*} [Fintype α] (x : α) : x ∈ todos α :=
  Finset.mem_toList.mpr (Finset.mem_univ x)

/-- Exatamente um dos `f x` é verdadeiro. -/
def umDe {α : Type*} [Fintype α] [DecidableEq α] (f : α → V) : Fm V :=
  (todos α).map (fun x => (f x, true)) ::
    (todos α).flatMap fun x => ((todos α).filter (· ≠ x)).map fun y => [(f x, false), (f y, false)]

theorem sat_umDe {α : Type*} [Fintype α] [DecidableEq α] {τ : V → Bool} {f : α → V} :
    Sat τ (umDe f) ↔ ∃ x, ∀ y, τ (f y) = decide (y = x) := by
  simp only [umDe, sat_cons, sat_flatMap, sat_map, List.mem_map, List.mem_filter, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨⟨ℓ, ⟨x, -, rfl⟩, hx⟩, h⟩
    refine ⟨x, fun y => ?_⟩
    by_cases hy : y = x
    · subst hy; simpa using hx
    · obtain ⟨m, hm, hm'⟩ := h x (mem_todos x) y ⟨mem_todos y, by simpa using hy⟩
      rcases hm with rfl | rfl
      · simp only at hm' hx; rw [hm'] at hx; exact absurd hx (by decide)
      · simpa [hy] using hm'
  · rintro ⟨x, hx⟩
    refine ⟨⟨(f x, true), ⟨x, mem_todos x, rfl⟩, by simp [hx]⟩, fun a _ b hb => ?_⟩
    have hb' : b ≠ a := by simpa using hb.2
    by_cases ha : a = x
    · subst ha
      exact ⟨(f b, false), Or.inr rfl, by simp [hx, hb']⟩
    · exact ⟨(f a, false), Or.inl rfl, by simp [hx, ha]⟩

theorem umDe_det {α : Type*} [Fintype α] [DecidableEq α] {τ : V → Bool} {f : α → V}
    (h : Sat τ (umDe f)) {x : α} (hx : τ (f x) = true) : ∀ y, τ (f y) = decide (y = x) := by
  obtain ⟨x₀, h₀⟩ := sat_umDe.mp h
  have : x = x₀ := by simpa [h₀ x] using hx
  subst this
  exact h₀

/-! ### A máquina e o passo com parada absorvente -/

/-- Variáveis do tableau. -/
inductive Var (K : Type) (Γ : K → Type) (Λ σ : Type) where
  | lab (t : ℕ) (o : Option Λ)
  | st (t : ℕ) (v : σ)
  | cel (t : ℕ) (k : K) (p : ℕ) (a : Option (Γ k))

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ : Type} {σ : Type}

/-- O passo, com a configuração parada absorvente. -/
def passo (M : Λ → TM2.Stmt Γ Λ σ) (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ σ :=
  (TM2.step M c).getD c

/-- A execução de `t` passos. -/
def run (M : Λ → TM2.Stmt Γ Λ σ) (C : TM2.Cfg Γ Λ σ) (t : ℕ) : TM2.Cfg Γ Λ σ :=
  (passo M)^[t] C

theorem run_succ (M : Λ → TM2.Stmt Γ Λ σ) (C : TM2.Cfg Γ Λ σ) (t : ℕ) :
    run M C (t + 1) = passo M (run M C t) := by
  simp only [run, Function.iterate_succ_apply']

theorem passo_none (M : Λ → TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    passo M ⟨none, v, S⟩ = ⟨none, v, S⟩ := rfl

/-- A janela de profundidade `D` lida célula a célula. -/
def winOf (D : ℕ) (S : ∀ k, List (Γ k)) : ∀ k, Fin D → Option (Γ k) :=
  fun k i => (S k)[i.val]?

/-- As pilhas descritas por células (o prefixo até o primeiro `none`). -/
def janC {D : ℕ} (W : ∀ k, Fin D → Option (Γ k)) : ∀ k, List (Γ k) :=
  fun k => (List.ofFn (W k)).filterMap id

theorem filterMap_ofFn_getElem_opt {α : Type*} :
    ∀ (D : ℕ) (l : List α), (List.ofFn fun i : Fin D => l[i.val]?).filterMap id = l.take D
  | 0, l => by simp
  | D + 1, [] => by
    rw [List.ofFn_succ]
    have := filterMap_ofFn_getElem_opt D ([] : List α)
    simp
  | D + 1, a :: l => by
    rw [List.ofFn_succ]
    have := filterMap_ofFn_getElem_opt D l
    simp only [Fin.val_zero, List.getElem?_cons_zero, Fin.val_succ, List.getElem?_cons_succ,
      List.filterMap_cons, List.take_succ_cons]
    exact congrArg (List.cons a) this

theorem janC_winOf (D : ℕ) (S : ∀ k, List (Γ k)) : janC (winOf D S) = jan D S := by
  funext k
  exact filterMap_ofFn_getElem_opt D (S k)

/-- **O passo em células.** Um passo de uma configuração em curso é o passo sobre a janela, com o
resto de cada pilha deslocado. -/
theorem passo_some [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ) (l : Λ) (v : σ) (S : ∀ k, List (Γ k)) :
    passo M ⟨some l, v, S⟩ =
      ⟨(TM2.stepAux (M l) v (janC (winOf (profMax M) S))).l,
        (TM2.stepAux (M l) v (janC (winOf (profMax M) S))).var,
        fun k => (TM2.stepAux (M l) v (janC (winOf (profMax M) S))).stk k ++
          (S k).drop (profMax M)⟩ := by
  simp only [passo, step_janela, Option.getD_some, janC_winOf]

theorem getElem_opt_append_drop {α : Type*} (r s : List α) (D p : ℕ) :
    (r ++ s.drop D)[p]? = if p < r.length then r[p]? else s[p - r.length + D]? := by
  split_ifs with h
  · exact List.getElem?_append_left h
  · rw [List.getElem?_append_right (by omega), List.getElem?_drop]
    congr 1
    omega

/-! ### Crescimento das pilhas -/

/-- Número máximo de `push` num ramo de uma instrução. -/
def npush : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => npush q + 1
  | .peek _ _ q => npush q
  | .pop _ _ q => npush q
  | .load _ q => npush q
  | .branch _ q₁ q₂ => max (npush q₁) (npush q₂)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_len : ∀ (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) (k : K),
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + npush q
  | .push k' f q, v, S, k => by
    have := stepAux_len q v (update S k' (f v :: S k')) k
    simp only [TM2.stepAux, npush]
    by_cases hk : k = k'
    · subst hk; simp only [update_self, List.length_cons] at this; omega
    · simp only [update_of_ne hk] at this; omega
  | .peek k' f q, v, S, k => by
    have := stepAux_len q (f v (S k').head?) S k
    simp only [TM2.stepAux, npush]; omega
  | .pop k' f q, v, S, k => by
    have := stepAux_len q (f v (S k').head?) (update S k' (S k').tail) k
    simp only [TM2.stepAux, npush]
    by_cases hk : k = k'
    · subst hk; simp only [update_self, List.length_tail] at this; omega
    · simp only [update_of_ne hk] at this; omega
  | .load a q, v, S, k => by
    have := stepAux_len q (a v) S k
    simp only [TM2.stepAux, npush]; omega
  | .branch f q₁ q₂, v, S, k => by
    have h1 := stepAux_len q₁ v S k
    have h2 := stepAux_len q₂ v S k
    simp only [TM2.stepAux, npush]
    cases f v
    · simp only [Bool.cond_false]; omega
    · simp only [Bool.cond_true]; omega
  | .goto _, _, _, _ => by simp [TM2.stepAux]
  | .halt, _, _, _ => by simp [TM2.stepAux]

/-- Máximo de `push` por passo de um programa com rótulos finitos. -/
def pushMax [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ) : ℕ :=
  Finset.univ.sup fun l => npush (M l)

theorem passo_len [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ) (C : TM2.Cfg Γ Λ σ) (k : K) :
    ((passo M C).stk k).length ≤ (C.stk k).length + pushMax M := by
  obtain ⟨_ | l, v, S⟩ := C
  · simp [passo_none]
  · have h1 := stepAux_len (M l) v S k
    have h2 : npush (M l) ≤ pushMax M :=
      Finset.le_sup (f := fun l => npush (M l)) (Finset.mem_univ l)
    simp only [passo, TM2.step, Option.getD_some]
    omega

/-- **Crescimento linear.** Em `t` passos cada pilha cresce no máximo `t · pushMax M`. -/
theorem run_len [Fintype Λ] (M : Λ → TM2.Stmt Γ Λ σ) (C : TM2.Cfg Γ Λ σ) (k : K) :
    ∀ t, ((run M C t).stk k).length ≤ (C.stk k).length + t * pushMax M
  | 0 => by simp [run]
  | t + 1 => by
    rw [run_succ]
    have := passo_len M (run M C t) k
    have := run_len M C k t
    rw [Nat.succ_mul]
    omega

/-! ### As cláusulas -/

variable [Fintype K] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [Fintype Λ] [DecidableEq Λ]
  [Fintype σ] [DecidableEq σ] (M : Λ → TM2.Stmt Γ Λ σ)

/-- Um caso do passo: rótulo, estado e as `D` células do topo de cada pilha. -/
abbrev Caso := Λ × σ × (∀ k, Fin (profMax M) → Option (Γ k))

/-- Exatamente um valor por grandeza, no instante `t`, para as células `p < S`. -/
def clsLinha (t S : ℕ) : Fm (Var K Γ Λ σ) :=
  umDe (fun o => Var.lab t o) ++ umDe (fun v => Var.st t v) ++
    (todos K).flatMap fun k => (List.range S).flatMap fun p => umDe (fun a => Var.cel t k p a)

/-- As premissas de um caso no instante `t`. -/
def prem (t : ℕ) (c : Caso M) : List (Var K Γ Λ σ) :=
  Var.lab t (some c.1) :: Var.st t c.2.1 ::
    (todos K).flatMap fun k => (todos (Fin (profMax M))).map fun i => Var.cel t k i.val (c.2.2 k i)

/-- O resultado do passo sobre a janela de um caso. -/
def res (c : Caso M) : TM2.Cfg Γ Λ σ := TM2.stepAux (M c.1) c.2.1 (janC c.2.2)

/-- As cláusulas de um caso: rótulo, estado e células do instante `t+1`. -/
def clsCaso (t S : ℕ) (c : Caso M) : Fm (Var K Γ Λ σ) :=
  imp (prem M t c) (Var.lab (t + 1) (res M c).l, true) ::
  imp (prem M t c) (Var.st (t + 1) (res M c).var, true) ::
  (todos K).flatMap fun k => (List.range S).flatMap fun p' =>
    if p' < ((res M c).stk k).length then
      [imp (prem M t c) (Var.cel (t + 1) k p' ((res M c).stk k)[p']?, true)]
    else if p' - ((res M c).stk k).length + profMax M < S then
      (todos (Option (Γ k))).map fun a =>
        imp (Var.cel t k (p' - ((res M c).stk k).length + profMax M) a :: prem M t c)
          (Var.cel (t + 1) k p' a, true)
    else [imp (prem M t c) (Var.cel (t + 1) k p' none, true)]

/-- A configuração parada se repete. -/
def clsPara (t S : ℕ) : Fm (Var K Γ Λ σ) :=
  imp [Var.lab t none] (Var.lab (t + 1) none, true) ::
    ((todos σ).map fun v => imp [Var.lab t none, Var.st t v] (Var.st (t + 1) v, true)) ++
    (todos K).flatMap fun k => (List.range S).flatMap fun p => (todos (Option (Γ k))).map fun a =>
      imp [Var.lab t none, Var.cel t k p a] (Var.cel (t + 1) k p a, true)

/-- O passo `t → t+1`. -/
def clsTrans (t S : ℕ) : Fm (Var K Γ Λ σ) :=
  clsPara t S ++ (todos (Caso M)).flatMap (clsCaso M t S)

/-- A estrutura do tableau: linhas `0..T` e passos `0..T-1`. -/
def estrutura (T S : ℕ) : Fm (Var K Γ Λ σ) :=
  (List.range (T + 1)).flatMap (fun t => clsLinha t S) ++
    (List.range T).flatMap fun t => clsTrans M t S

/-- A aceitação: no instante `T` a máquina parou com `y` no topo da pilha `k₁`. -/
def aceita (T : ℕ) (k₁ : K) (y : Γ k₁) : Fm (Var K Γ Λ σ) :=
  [[(Var.lab T none, true)], [(Var.cel T k₁ 0 (some y), true)]]

/-- A fórmula completa. -/
def formula (T S : ℕ) (ini : Fm (Var K Γ Λ σ)) (k₁ : K) (y : Γ k₁) : Fm (Var K Γ Λ σ) :=
  estrutura M T S ++ ini ++ aceita T k₁ y

/-! ### Linhas -/

/-- A linha `t` da valoração `τ` descreve a configuração `C` (células `p < S`). -/
def Linha (τ : Var K Γ Λ σ → Bool) (t S : ℕ) (C : TM2.Cfg Γ Λ σ) : Prop :=
  (∀ o, τ (Var.lab t o) = decide (o = C.l)) ∧ (∀ v, τ (Var.st t v) = decide (v = C.var)) ∧
    ∀ k, ∀ p < S, ∀ a, τ (Var.cel t k p a) = decide (a = (C.stk k)[p]?)

variable {M}

theorem Linha.sat {τ : Var K Γ Λ σ → Bool} {t S : ℕ} {C : TM2.Cfg Γ Λ σ}
    (h : Linha τ t S C) : Sat τ (clsLinha (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) t S) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [clsLinha, sat_append, sat_flatMap, List.mem_range]
  exact ⟨⟨sat_umDe.mpr ⟨C.l, h1⟩, sat_umDe.mpr ⟨C.var, h2⟩⟩,
    fun k _ p hp => sat_umDe.mpr ⟨_, h3 k p hp⟩⟩

theorem sat_clsLinha {τ : Var K Γ Λ σ → Bool} {t S : ℕ} :
    Sat τ (clsLinha (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) t S) ↔
      Sat τ (umDe fun o => Var.lab (K := K) (Γ := Γ) (σ := σ) t o) ∧
      Sat τ (umDe fun v => Var.st (K := K) (Γ := Γ) (Λ := Λ) t v) ∧
      ∀ k, ∀ p < S, Sat τ (umDe fun a => Var.cel (Λ := Λ) (σ := σ) t k p a) := by
  simp only [clsLinha, sat_append, sat_flatMap, List.mem_range, and_assoc]
  exact and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h k p hp => h k (mem_todos k) p hp,
    fun h k _ p hp => h k p hp⟩)

/-- Uma linha satisfeita é determinada pelos valores verdadeiros. -/
theorem Linha.de {τ : Var K Γ Λ σ → Bool} {t S : ℕ} {C : TM2.Cfg Γ Λ σ}
    (h : Sat τ (clsLinha (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) t S))
    (hl : τ (Var.lab t C.l) = true) (hv : τ (Var.st t C.var) = true)
    (hc : ∀ k, ∀ p < S, τ (Var.cel t k p (C.stk k)[p]?) = true) : Linha τ t S C := by
  obtain ⟨h1, h2, h3⟩ := sat_clsLinha.mp h
  exact ⟨umDe_det h1 hl, umDe_det h2 hv, fun k p hp => umDe_det (h3 k p hp) (hc k p hp)⟩

/-- A valoração genuína de uma sequência de configurações. -/
def gen (r : ℕ → TM2.Cfg Γ Λ σ) : Var K Γ Λ σ → Bool
  | .lab t o => decide (o = (r t).l)
  | .st t v => decide (v = (r t).var)
  | .cel t k p a => decide (a = ((r t).stk k)[p]?)

theorem linha_gen (r : ℕ → TM2.Cfg Γ Λ σ) (t S : ℕ) : Linha (gen r) t S (r t) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ _ => rfl⟩

/-! ### O passo em células -/

theorem passo_cel (l : Λ) (v : σ) (Stk : ∀ k, List (Γ k)) :
    (passo M ⟨some l, v, Stk⟩).l = (res M (l, v, winOf (profMax M) Stk)).l ∧
    (passo M ⟨some l, v, Stk⟩).var = (res M (l, v, winOf (profMax M) Stk)).var ∧
    ∀ k p', ((passo M ⟨some l, v, Stk⟩).stk k)[p']? =
      if p' < ((res M (l, v, winOf (profMax M) Stk)).stk k).length then
        ((res M (l, v, winOf (profMax M) Stk)).stk k)[p']?
      else (Stk k)[p' - ((res M (l, v, winOf (profMax M) Stk)).stk k).length + profMax M]? := by
  rw [passo_some]
  exact ⟨rfl, rfl, fun k p' => getElem_opt_append_drop _ _ _ _⟩

theorem prem_verdadeira {τ : Var K Γ Λ σ → Bool} {t S : ℕ} {C : TM2.Cfg Γ Λ σ}
    (h : Linha τ t S C) (hD : profMax M ≤ S) {l : Λ} (hl : C.l = some l) :
    ∀ x ∈ prem M t (l, C.var, winOf (profMax M) C.stk), τ x = true := by
  intro x hx
  simp only [prem, List.mem_cons, List.mem_flatMap, List.mem_map] at hx
  rcases hx with rfl | rfl | ⟨k, -, i, -, rfl⟩
  · rw [h.1]; simp [hl]
  · rw [h.2.1]; simp
  · rw [h.2.2 k i.val (by omega)]; simp [winOf]

theorem prem_caso {τ : Var K Γ Λ σ → Bool} {t S : ℕ} {C : TM2.Cfg Γ Λ σ}
    (h : Linha τ t S C) (hD : profMax M ≤ S) {c : Caso M}
    (hc : ∀ x ∈ prem M t c, τ x = true) :
    C.l = some c.1 ∧ C.var = c.2.1 ∧ c.2.2 = winOf (profMax M) C.stk := by
  obtain ⟨l, v, W⟩ := c
  have h1 := hc _ (List.mem_cons_self ..)
  have h2 := hc _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  rw [h.1] at h1
  rw [h.2.1] at h2
  refine ⟨(of_decide_eq_true h1).symm, (of_decide_eq_true h2).symm, ?_⟩
  funext k i
  have h3 := hc (Var.cel t k i.val (W k i)) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_flatMap.mpr ⟨k, mem_todos k, List.mem_map.mpr ⟨i, mem_todos i, rfl⟩⟩)))
  rw [h.2.2 k i.val (by omega)] at h3
  exact of_decide_eq_true h3

/-! ### As cláusulas de transição -/

theorem sat_clsTrans {τ : Var K Γ Λ σ → Bool} {t S : ℕ} :
    Sat τ (clsTrans M t S) ↔
      Sat τ (clsPara (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) t S) ∧ ∀ c, Sat τ (clsCaso M t S c) := by
  simp only [clsTrans, sat_append, sat_flatMap]
  exact and_congr Iff.rfl ⟨fun h c => h c (mem_todos c), fun h c _ => h c⟩

theorem sat_clsPara {τ : Var K Γ Λ σ → Bool} {t S : ℕ} :
    Sat τ (clsPara (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) t S) ↔
      (τ (Var.lab t none) = true →
        τ (Var.lab (t + 1) none) = true ∧
        (∀ v, τ (Var.st t v) = true → τ (Var.st (t + 1) v) = true) ∧
        ∀ k, ∀ p < S, ∀ a, τ (Var.cel t k p a) = true → τ (Var.cel (t + 1) k p a) = true) := by
  simp only [clsPara, sat_cons, sat_append, sat_map, sat_flatMap, cl_imp, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩ hn
    exact ⟨h1 hn, fun v hv => h2 v (mem_todos v) ⟨hn, hv⟩,
      fun k p hp a ha => h3 k (mem_todos k) p hp a (mem_todos a) ⟨hn, ha⟩⟩
  · intro h
    exact ⟨⟨fun hn => (h hn).1, fun v _ hv => (h hv.1).2.1 v hv.2⟩,
      fun k _ p hp a _ ha => (h ha.1).2.2 k p hp a ha.2⟩

/-- As cláusulas de um caso valem quando a premissa do caso falha. -/
theorem clsCaso_guarda {τ : Var K Γ Λ σ → Bool} {t S : ℕ} {c : Caso M}
    (h : ¬ ∀ x ∈ prem M t c, τ x = true) : Sat τ (clsCaso M t S c) := by
  have g : ∀ (L : List (Var K Γ Λ σ)) (ℓ : Var K Γ Λ σ × Bool), (∀ x ∈ prem M t c, x ∈ L) →
      ∃ m ∈ imp L ℓ, τ m.1 = m.2 := fun L ℓ hL =>
    cl_imp.mpr fun hP => absurd (fun x hx => hP x (hL x hx)) h
  have g0 := fun ℓ => g (prem M t c) ℓ (fun _ hx => hx)
  simp only [clsCaso, sat_cons, sat_flatMap]
  refine ⟨g0 _, g0 _, fun k _ p' _ => ?_⟩
  split_ifs
  · exact sat_singleton.mpr (g0 _)
  · exact sat_map.mpr fun a _ => g _ _ fun x hx => List.mem_cons_of_mem _ hx
  · exact sat_singleton.mpr (g0 _)

/-- **Correção do passo (ida).** Se as linhas `t` e `t+1` descrevem `C` e `passo M C`, as
cláusulas de transição valem. -/
theorem trans_sat {τ : Var K Γ Λ σ → Bool} {t S : ℕ} {C : TM2.Cfg Γ Λ σ}
    (h0 : Linha τ t S C) (h1 : Linha τ (t + 1) S (passo M C)) (hD : profMax M ≤ S)
    (hC : ∀ k, (C.stk k).length ≤ S) : Sat τ (clsTrans M t S) := by
  rw [sat_clsTrans]
  constructor
  · rw [sat_clsPara]
    intro hn
    obtain ⟨Cl, Cv, Cs⟩ := C
    rw [h0.1] at hn
    have hCl : Cl = none := (of_decide_eq_true hn).symm
    subst hCl
    rw [passo_none] at h1
    refine ⟨by rw [h1.1]; simp, fun v hv => ?_, fun k p hp a ha => ?_⟩
    · rw [h0.2.1] at hv; rw [h1.2.1]; exact hv
    · rw [h0.2.2 k p hp] at ha; rw [h1.2.2 k p hp]; exact ha
  · intro c
    by_cases hP : ∀ x ∈ prem M t c, τ x = true
    swap
    · exact clsCaso_guarda hP
    obtain ⟨hl, hv, hW⟩ := prem_caso h0 hD hP
    obtain ⟨l, v, W⟩ := c
    obtain ⟨Cl, Cv, Cs⟩ := C
    simp only at hl hv hW
    subst hl hv hW
    obtain ⟨el, ev, ec⟩ := passo_cel (M := M) l Cv Cs
    simp only [clsCaso, sat_cons, sat_flatMap, List.mem_range, cl_imp]
    refine ⟨fun _ => ?_, fun _ => ?_, fun k _ p' hp' => ?_⟩
    · rw [h1.1, el]; simp
    · rw [h1.2.1, ev]; simp
    · have e := ec k p'
      split_ifs with h₁ h₂
      · rw [sat_singleton, cl_imp]
        intro _
        rw [h1.2.2 k p' hp', e]
        simp [h₁]
      · rw [sat_map]
        intro a _
        rw [cl_imp]
        intro hx
        have ha := hx _ (List.mem_cons_self ..)
        rw [h0.2.2 k _ h₂] at ha
        rw [h1.2.2 k p' hp', e]
        simp only [h₁, ↓reduceIte]
        exact ha
      · rw [sat_singleton, cl_imp]
        intro _
        rw [h1.2.2 k p' hp', e]
        simp only [h₁, ↓reduceIte]
        have hCk := hC k
        have : (Cs k)[p' - ((res M (l, Cv, winOf (profMax M) Cs)).stk k).length +
            profMax M]? = none := List.getElem?_eq_none (by simp only at hCk; omega)
        simp [this]

/-- **Correção do passo (volta).** Se a linha `t` descreve `C` e as cláusulas valem, a linha
`t+1` descreve `passo M C`. -/
theorem trans_det {τ : Var K Γ Λ σ → Bool} {t S : ℕ} {C : TM2.Cfg Γ Λ σ}
    (h0 : Linha τ t S C) (hT : Sat τ (clsTrans M t S))
    (hL : Sat τ (clsLinha (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) (t + 1) S))
    (hD : profMax M ≤ S) (hC : ∀ k, (C.stk k).length ≤ S) : Linha τ (t + 1) S (passo M C) := by
  rw [sat_clsTrans] at hT
  obtain ⟨hPara, hCaso⟩ := hT
  obtain ⟨Cl, Cv, Cs⟩ := C
  cases Cl with
  | none =>
    rw [passo_none]
    have hn : τ (Var.lab t none) = true := by rw [h0.1]; simp
    obtain ⟨p1, p2, p3⟩ := sat_clsPara.mp hPara hn
    refine Linha.de hL p1 (p2 _ (by rw [h0.2.1]; simp)) fun k p hp => p3 k p hp _ ?_
    rw [h0.2.2 k p hp]; simp
  | some l =>
    have hP := prem_verdadeira h0 hD (l := l) rfl
    have hc := hCaso (l, Cv, winOf (profMax M) Cs)
    obtain ⟨el, ev, ec⟩ := passo_cel (M := M) l Cv Cs
    simp only [clsCaso, sat_cons, sat_flatMap, List.mem_range, cl_imp] at hc
    obtain ⟨c1, c2, c3⟩ := hc
    refine Linha.de hL (by rw [el]; exact c1 hP) (by rw [ev]; exact c2 hP) fun k p' hp' => ?_
    have c4 := c3 k (mem_todos k) p' hp'
    rw [ec k p']
    split_ifs at c4 ⊢ with h₁ h₂
    · rw [sat_singleton, cl_imp] at c4
      exact c4 hP
    · rw [sat_map] at c4
      refine cl_imp.mp (c4 _ (mem_todos _)) fun x hx => ?_
      rcases List.mem_cons.mp hx with rfl | hx
      · rw [h0.2.2 k _ h₂]; simp
      · exact hP x hx
    · rw [sat_singleton, cl_imp] at c4
      have hCk := hC k
      have : (Cs k)[p' - ((res M (l, Cv, winOf (profMax M) Cs)).stk k).length +
          profMax M]? = none := List.getElem?_eq_none (by simp only at hCk; omega)
      rw [this]
      exact c4 hP

/-! ### O tableau é fiel -/

theorem sat_estrutura {τ : Var K Γ Λ σ → Bool} {T S : ℕ} :
    Sat τ (estrutura M T S) ↔
      (∀ t ≤ T, Sat τ (clsLinha (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) t S)) ∧
        ∀ t < T, Sat τ (clsTrans M t S) := by
  simp only [estrutura, sat_append, sat_flatMap, List.mem_range, Nat.lt_succ_iff]

theorem sat_aceita {τ : Var K Γ Λ σ → Bool} {T : ℕ} {k₁ : K} {y : Γ k₁} :
    Sat τ (aceita T k₁ y) ↔ τ (Var.lab T none) = true ∧ τ (Var.cel T k₁ 0 (some y)) = true := by
  simp [aceita, Sat]

/-- **O tableau é fiel (CL3).** Se as pilhas cabem em `S` células durante os `T` passos e a parte
inicial `ini` descreve exatamente as configurações de `I`, a fórmula é satisfatível se e só se
alguma configuração de `I` para em `T` passos com `y` no topo da pilha `k₁`. -/
theorem tableau_correto {T S : ℕ} {ini : Fm (Var K Γ Λ σ)} {k₁ : K} {y : Γ k₁}
    {I : Set (TM2.Cfg Γ Λ σ)} (hD : profMax M ≤ S) (hS0 : 0 < S)
    (hS : ∀ C ∈ I, ∀ t ≤ T, ∀ k, ((run M C t).stk k).length ≤ S)
    (hI1 : ∀ τ, Sat τ (clsLinha (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) 0 S) → Sat τ ini →
      ∃ C ∈ I, Linha τ 0 S C)
    (hI2 : ∀ C ∈ I, ∀ τ, Linha τ 0 S C → Sat τ ini) :
    (∃ τ, Sat τ (formula M T S ini k₁ y)) ↔
      ∃ C ∈ I, (run M C T).l = none ∧ ((run M C T).stk k₁)[0]? = some y := by
  simp only [formula, sat_append, sat_estrutura, sat_aceita]
  constructor
  · rintro ⟨τ, ⟨⟨hL, hT⟩, hini⟩, ha1, ha2⟩
    obtain ⟨C, hC, h0⟩ := hI1 τ (hL 0 (Nat.zero_le _)) hini
    have key : ∀ t ≤ T, Linha τ t S (run M C t) := by
      intro t ht
      induction t with
      | zero => exact h0
      | succ t ih =>
        rw [run_succ]
        exact trans_det (ih (by omega)) (hT t (by omega)) (hL (t + 1) ht) hD
          (hS C hC t (by omega))
    have hk := key T le_rfl
    refine ⟨C, hC, ?_, ?_⟩
    · rw [hk.1] at ha1; exact (of_decide_eq_true ha1).symm
    · rw [hk.2.2 k₁ 0 hS0] at ha2; exact (of_decide_eq_true ha2).symm
  · rintro ⟨C, hC, hl, hy⟩
    refine ⟨gen (run M C), ⟨⟨fun t _ => (linha_gen _ t S).sat, fun t ht => ?_⟩,
      hI2 C hC _ (linha_gen _ 0 S)⟩, ?_, ?_⟩
    · have h1 := linha_gen (run M C) (t + 1) S
      rw [run_succ] at h1
      exact trans_sat (linha_gen _ t S) h1 hD (hS C hC t (by omega))
    · simp [gen, hl]
    · simp [gen, hy]

end

end ATK.CookLevinTableau

#print axioms ATK.CookLevinTableau.Cl
#print axioms ATK.CookLevinTableau.Fm
#print axioms ATK.CookLevinTableau.Sat
#print axioms ATK.CookLevinTableau.sat_nil
#print axioms ATK.CookLevinTableau.sat_append
#print axioms ATK.CookLevinTableau.sat_cons
#print axioms ATK.CookLevinTableau.sat_flatMap
#print axioms ATK.CookLevinTableau.sat_map
#print axioms ATK.CookLevinTableau.sat_singleton
#print axioms ATK.CookLevinTableau.imp
#print axioms ATK.CookLevinTableau.cl_imp
#print axioms ATK.CookLevinTableau.todos
#print axioms ATK.CookLevinTableau.mem_todos
#print axioms ATK.CookLevinTableau.umDe
#print axioms ATK.CookLevinTableau.sat_umDe
#print axioms ATK.CookLevinTableau.umDe_det
#print axioms ATK.CookLevinTableau.Var
#print axioms ATK.CookLevinTableau.passo
#print axioms ATK.CookLevinTableau.run
#print axioms ATK.CookLevinTableau.run_succ
#print axioms ATK.CookLevinTableau.passo_none
#print axioms ATK.CookLevinTableau.winOf
#print axioms ATK.CookLevinTableau.janC
#print axioms ATK.CookLevinTableau.filterMap_ofFn_getElem_opt
#print axioms ATK.CookLevinTableau.janC_winOf
#print axioms ATK.CookLevinTableau.passo_some
#print axioms ATK.CookLevinTableau.getElem_opt_append_drop
#print axioms ATK.CookLevinTableau.npush
#print axioms ATK.CookLevinTableau.stepAux_len
#print axioms ATK.CookLevinTableau.pushMax
#print axioms ATK.CookLevinTableau.passo_len
#print axioms ATK.CookLevinTableau.run_len
#print axioms ATK.CookLevinTableau.Caso
#print axioms ATK.CookLevinTableau.clsLinha
#print axioms ATK.CookLevinTableau.prem
#print axioms ATK.CookLevinTableau.res
#print axioms ATK.CookLevinTableau.clsCaso
#print axioms ATK.CookLevinTableau.clsPara
#print axioms ATK.CookLevinTableau.clsTrans
#print axioms ATK.CookLevinTableau.estrutura
#print axioms ATK.CookLevinTableau.aceita
#print axioms ATK.CookLevinTableau.formula
#print axioms ATK.CookLevinTableau.Linha
#print axioms ATK.CookLevinTableau.Linha.sat
#print axioms ATK.CookLevinTableau.sat_clsLinha
#print axioms ATK.CookLevinTableau.Linha.de
#print axioms ATK.CookLevinTableau.gen
#print axioms ATK.CookLevinTableau.linha_gen
#print axioms ATK.CookLevinTableau.passo_cel
#print axioms ATK.CookLevinTableau.prem_verdadeira
#print axioms ATK.CookLevinTableau.prem_caso
#print axioms ATK.CookLevinTableau.sat_clsTrans
#print axioms ATK.CookLevinTableau.sat_clsPara
#print axioms ATK.CookLevinTableau.clsCaso_guarda
#print axioms ATK.CookLevinTableau.trans_sat
#print axioms ATK.CookLevinTableau.trans_det
#print axioms ATK.CookLevinTableau.sat_estrutura
#print axioms ATK.CookLevinTableau.sat_aceita
#print axioms ATK.CookLevinTableau.tableau_correto
