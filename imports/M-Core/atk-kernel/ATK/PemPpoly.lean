import ATK.CircuitoCamadas
import ATK.CookLevinBase
import ATK.AtaquePvsNP

/-!
# ATK — Ponte `P ⊆ P/poly` provada (Savage 1972) para as máquinas `Turing.FinTM2` da Mathlib

`AtaquePvsNP.PemPpoly` era uma ponte publicada (hipótese com nome). Aqui ela é provada: toda
linguagem de `classeP` (função característica computável em tempo polinomial por uma
`Turing.FinTM2`) tem circuitos de tamanho polinomial no modelo de `ATK.Shannon`.

A prova é o tableau determinístico em camadas (`ATK.CircuitoCamadas`):

* uma linha codifica uma configuração em "um-quente": rótulo, estado e, para cada pilha `k` e
  altura `i < H`, o símbolo da célula (ou vazio), com símbolos no conjunto finito `S k` (o
  alfabeto de entrada e os símbolos que o programa empurra; `CookLevinBase.simbolos_finite`);
* cada bit da linha seguinte é uma disjunção, sobre os **padrões** (rótulo, estado, janelas das
  `d` primeiras células de cada pilha), do padrão que casa com o bit calculado pelo passo sobre a
  janela (`CookLevinBase.stepAux_topo`, lema de moldura) — fórmulas de tamanho constante;
* a linha inicial depende de um bit de entrada por célula; a saída lê o topo da pilha de saída;
* tamanho total `O(T(n) · (n + T(n)))`, polinomial.

Resultado: `pemPpoly : AtaquePvsNP.PemPpoly` e, com ele,
`p_ne_np_de_naoPpoly : NPnaoEmPpoly → PneNP` sem pontes.
-/

namespace ATK.PemPpoly

open Turing ATK.CircuitoCamadas ATK.CircuitoCamadas.Form ATK.CookLevinBase ATK.Shannon
  ATK.LigacaoPNP ATK.AtaquePvsNP

open Classical

/-! ## Fórmulas: mudança de variáveis -/

namespace FormM

variable {ι κ : Type*}

/-- Renomeia as variáveis. -/
def map (f : ι → κ) : Form ι → Form κ
  | .var i => .var (f i)
  | .tt => .tt
  | .ff => .ff
  | .e a b => .e (map f a) (map f b)
  | .ou a b => .ou (map f a) (map f b)
  | .nao a => .nao (map f a)

theorem eval_map (f : ι → κ) (ρ : κ → Bool) :
    ∀ φ : Form ι, (map f φ).eval ρ = φ.eval (ρ ∘ f)
  | .var _ => rfl
  | .tt => rfl
  | .ff => rfl
  | .e a b => by simp [map, eval, eval_map f ρ a, eval_map f ρ b]
  | .ou a b => by simp [map, eval, eval_map f ρ a, eval_map f ρ b]
  | .nao a => by simp [map, eval, eval_map f ρ a]

theorem tam_map (f : ι → κ) : ∀ φ : Form ι, (map f φ).tam = φ.tam
  | .var _ => rfl
  | .tt => rfl
  | .ff => rfl
  | .e a b => by simp [map, tam, tam_map f a, tam_map f b]
  | .ou a b => by simp [map, tam, tam_map f a, tam_map f b]
  | .nao a => by simp [map, tam, tam_map f a]

end FormM

/-! ## A máquina -/

section Maquina

variable (tm : FinTM2)

instance instFintypeK : Fintype tm.K := tm.kFin
instance instFintypeΛ : Fintype tm.Λ := tm.ΛFin
instance instFintypeσ : Fintype tm.σ := tm.σFin
instance instFintypeΓ₀ : Fintype (tm.Γ tm.k₀) := tm.Γk₀Fin

/-- Janela de leitura: a maior profundidade de leitura do programa. -/
noncomputable def jan : ℕ := Finset.univ.sup fun l => prof (tm.m l)

/-- Maior número de empilhamentos por passo. -/
noncomputable def cres : ℕ := Finset.univ.sup fun l => emp (tm.m l)

theorem prof_le (l : tm.Λ) : prof (tm.m l) ≤ jan tm :=
  Finset.le_sup (f := fun l => prof (tm.m l)) (Finset.mem_univ l)

theorem emp_le (l : tm.Λ) : emp (tm.m l) ≤ cres tm :=
  Finset.le_sup (f := fun l => emp (tm.m l)) (Finset.mem_univ l)

/-- Símbolos relevantes: os da pilha de entrada e os empurrados pelo programa. -/
def simb : Set (Σ k, tm.Γ k) :=
  (⋃ l, simbolos (tm.m l)) ∪ Set.range (fun x : tm.Γ tm.k₀ => (⟨tm.k₀, x⟩ : Σ k, tm.Γ k))

theorem simb_finite : (simb tm).Finite := by
  haveI : Finite tm.σ := Finite.of_fintype _
  exact (Set.finite_iUnion fun l => simbolos_finite (tm.m l)).union (Set.finite_range _)

/-- Símbolos relevantes da pilha `k`. -/
def S (k : tm.K) : Set (tm.Γ k) := {x | (⟨k, x⟩ : Σ k, tm.Γ k) ∈ simb tm}

theorem S_finite (k : tm.K) : (S tm k).Finite :=
  (simb_finite tm).preimage (fun _ _ _ _ h => by simpa using h)

noncomputable instance instFintypeS (k : tm.K) : Fintype (S tm k) := (S_finite tm k).fintype

/-- Configuração válida: pilhas de altura `≤ H` com símbolos relevantes. -/
def Ok (H : ℕ) (c : tm.Cfg) : Prop :=
  ∀ k, (c.stk k).length ≤ H ∧ ∀ x ∈ c.stk k, x ∈ S tm k

/-! ### Linhas -/

/-- Os bits de uma linha (altura `H = Hb + 1`). -/
abbrev Bit (Hb : ℕ) := Option tm.Λ ⊕ tm.σ ⊕ (Σ k : tm.K, Fin (Hb + 1) × Option (S tm k))

/-- A célula `i` (reduzida módulo `H`) da pilha `k` com valor `o`. -/
def cel {Hb : ℕ} (k : tm.K) (i : ℕ) (o : Option (S tm k)) : Bit tm Hb :=
  .inr (.inr ⟨k, ⟨i % (Hb + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩, o⟩)

/-- Codificação um-quente de uma configuração. -/
noncomputable def codif (Hb : ℕ) (c : tm.Cfg) : Bit tm Hb → Bool
  | .inl l => decide (c.l = l)
  | .inr (.inl s) => decide (c.var = s)
  | .inr (.inr ⟨k, i, o⟩) => decide ((c.stk k)[i.1]? = o.map Subtype.val)

theorem codif_cel {Hb : ℕ} (c : tm.Cfg) (k : tm.K) {i : ℕ} (hi : i < Hb + 1)
    (o : Option (S tm k)) :
    codif tm Hb c (cel tm k i o) = decide ((c.stk k)[i]? = o.map Subtype.val) := by
  simp [cel, codif, Nat.mod_eq_of_lt hi]

/-! ### Padrões -/

/-- Janela de uma pilha: até `d` símbolos relevantes. -/
abbrev Jan (d : ℕ) (k : tm.K) := Σ j : Fin (d + 1), (Fin j → S tm k)

/-- Padrão: rótulo, estado e janelas. -/
abbrev Pat (d : ℕ) := Option tm.Λ × tm.σ × (∀ k, Jan tm d k)

/-- A janela como lista. -/
def win {d : ℕ} (p : Pat tm d) (k : tm.K) : List (tm.Γ k) :=
  List.ofFn fun i : Fin (p.2.2 k).1 => ((p.2.2 k).2 i).1

/-- O passo sobre os dados de um padrão (parada fica parada). -/
noncomputable def novo (l : Option tm.Λ) (s : tm.σ) (W : ∀ k, List (tm.Γ k)) :
    Option tm.Λ × tm.σ × (∀ k, List (tm.Γ k)) :=
  match l with
  | none => (none, s, W)
  | some lb => ((TM2.stepAux (tm.m lb) s W).l, (TM2.stepAux (tm.m lb) s W).var,
      (TM2.stepAux (tm.m lb) s W).stk)

end Maquina

/-! ## O casamento de padrões -/

section Casa

variable (tm : FinTM2) (Hb : ℕ)

/-- Valor esperado da célula `i` da janela `W`. -/
def celW {d : ℕ} {k : tm.K} (W : Jan tm d k) (i : ℕ) : Option (S tm k) :=
  if h : i < W.1 then some (W.2 ⟨i, h⟩) else none

theorem celW_val {d : ℕ} (p : Pat tm d) (k : tm.K) (i : ℕ) :
    (celW tm (p.2.2 k) i).map Subtype.val = (win tm p k)[i]? := by
  unfold celW win
  split_ifs with h
  · simp [List.getElem?_ofFn, h]
  · simp [List.getElem?_ofFn, h]

theorem length_win {d : ℕ} (p : Pat tm d) (k : tm.K) : (win tm p k).length ≤ d := by
  simp only [win, List.length_ofFn]; have := (p.2.2 k).1.2; omega

/-- Fórmula de casamento do padrão `p`. -/
noncomputable def casa {d : ℕ} (p : Pat tm d) : Form (Bit tm Hb) :=
  eL ([.var (.inl p.1), .var (.inr (.inl p.2.1))] ++
    (Finset.univ : Finset tm.K).toList.flatMap fun k =>
      (List.range d).map fun i => .var (cel tm (Hb := Hb) k i (celW tm (p.2.2 k) i)))

theorem casa_iff {d : ℕ} (hd : d ≤ Hb) (c : tm.Cfg) (p : Pat tm d) :
    (casa tm Hb p).eval (codif tm Hb c) = true ↔
      p.1 = c.l ∧ p.2.1 = c.var ∧ ∀ k, win tm p k = (c.stk k).take d := by
  rw [casa, eval_eL]
  simp only [List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_range,
    Finset.mem_toList, Finset.mem_univ, true_and, List.not_mem_nil, or_false]
  constructor
  · intro h
    have h1 := h _ (Or.inl (Or.inl rfl))
    have h2 := h _ (Or.inl (Or.inr rfl))
    simp only [eval, codif, decide_eq_true_eq] at h1 h2
    refine ⟨h1.symm, h2.symm, fun k => ?_⟩
    apply List.ext_getElem?
    intro i
    by_cases hi : i < d
    · have h3 := h _ (Or.inr ⟨k, i, hi, rfl⟩)
      simp only [eval] at h3
      rw [codif_cel tm c k (by omega), decide_eq_true_eq, celW_val] at h3
      rw [List.getElem?_take, if_pos hi, h3]
    · rw [List.getElem?_take, if_neg hi, List.getElem?_eq_none]
      have := length_win tm p k; omega
  · rintro ⟨h1, h2, h3⟩ φ hφ
    rcases hφ with (rfl | rfl) | ⟨k, i, hi, rfl⟩
    · simp [eval, codif, h1]
    · simp [eval, codif, h2]
    · simp only [eval]
      rw [codif_cel tm c k (by omega), decide_eq_true_eq, celW_val, h3 k, List.getElem?_take,
        if_pos hi]

/-- O padrão de uma configuração válida. -/
noncomputable def patOf {d : ℕ} (c : tm.Cfg) (hc : ∀ k, ∀ x ∈ c.stk k, x ∈ S tm k) : Pat tm d :=
  (c.l, c.var, fun k => ⟨⟨((c.stk k).take d).length, by
    have := List.length_take_le d (c.stk k); omega⟩,
    fun i => ⟨((c.stk k).take d)[i.1], hc k _ (List.mem_of_mem_take (List.getElem_mem _))⟩⟩)

theorem win_patOf {d : ℕ} (c : tm.Cfg) (hc : ∀ k, ∀ x ∈ c.stk k, x ∈ S tm k) (k : tm.K) :
    win tm (patOf tm (d := d) c hc) k = (c.stk k).take d := by
  simp only [win, patOf]
  exact List.ofFn_getElem

/-- Uma disjunção de casamentos vale o corpo comum dos padrões que casam. -/
theorem ouL_casa {d : ℕ} {ρ : Bit tm Hb → Bool} (P : List (Pat tm d))
    (B : Pat tm d → Form (Bit tm Hb)) (v : Bool)
    (hex : ∃ p ∈ P, (casa tm Hb p).eval ρ = true)
    (hall : ∀ p ∈ P, (casa tm Hb p).eval ρ = true → (B p).eval ρ = v) :
    (ouL (P.map fun p => .e (casa tm Hb p) (B p))).eval ρ = v := by
  cases v with
  | true =>
    obtain ⟨p, hp, hc⟩ := hex
    rw [eval_ouL]
    exact ⟨_, List.mem_map_of_mem hp, by simp [eval, hc, hall p hp hc]⟩
  | false =>
    by_contra hne
    rw [Bool.not_eq_false, eval_ouL] at hne
    obtain ⟨φ, hφ, h⟩ := hne
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hφ
    simp only [eval, Bool.and_eq_true] at h
    rw [hall p hp h.1] at h
    exact Bool.false_ne_true h.2

end Casa

/-! ## O passo -/

section Passo

variable (tm : FinTM2) (Hb : ℕ)

/-- **Moldura do passo acolchoado**: o novo rótulo, estado e topo saem de `novo` aplicado às
janelas; o resto de cada pilha desce intacto. -/
theorem passoA_novo (c : tm.Cfg) :
    (passoA tm.m c).l = (novo tm c.l c.var fun k => (c.stk k).take (jan tm)).1 ∧
    (passoA tm.m c).var = (novo tm c.l c.var fun k => (c.stk k).take (jan tm)).2.1 ∧
    ∀ k, (passoA tm.m c).stk k =
      (novo tm c.l c.var fun k => (c.stk k).take (jan tm)).2.2 k ++ (c.stk k).drop (jan tm) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => simp [passoA, novo, TM2.step]
  | some lb =>
    have h := stepAux_topo (tm.m lb) v S (prof_le tm lb)
    simp only [passoA, novo, TM2.step, Option.getD_some]
    rw [h]
    exact ⟨rfl, rfl, fun k => rfl⟩

theorem getElem?_append_drop {α : Type*} (W L : List α) (d i : ℕ) :
    (W ++ L.drop d)[i]? = if i < W.length then W[i]? else L[d + i - W.length]? := by
  split_ifs with hi
  · exact List.getElem?_append_left hi
  · rw [List.getElem?_append_right (by omega), List.getElem?_drop]
    congr 1; omega

/-- Corpo da célula `(k, i, o)` para um padrão. -/
noncomputable def corpo (p : Pat tm (jan tm)) (k : tm.K) (i : ℕ) (o : Option (S tm k)) :
    Form (Bit tm Hb) :=
  if i < ((novo tm p.1 p.2.1 (win tm p)).2.2 k).length then
    const (decide (((novo tm p.1 p.2.1 (win tm p)).2.2 k)[i]? = o.map Subtype.val))
  else if jan tm + i - ((novo tm p.1 p.2.1 (win tm p)).2.2 k).length < Hb + 1 then
    .var (cel tm k (jan tm + i - ((novo tm p.1 p.2.1 (win tm p)).2.2 k).length) o)
  else const (decide (o = none))

/-- Os padrões. -/
noncomputable def pats : List (Pat tm (jan tm)) := (Finset.univ : Finset (Pat tm (jan tm))).toList

/-- Fórmula de cada bit da linha seguinte. -/
noncomputable def pasF : Bit tm Hb → Form (Bit tm Hb)
  | .inl l => ouL ((pats tm).map fun p =>
      .e (casa tm Hb p) (const (decide ((novo tm p.1 p.2.1 (win tm p)).1 = l))))
  | .inr (.inl s) => ouL ((pats tm).map fun p =>
      .e (casa tm Hb p) (const (decide ((novo tm p.1 p.2.1 (win tm p)).2.1 = s))))
  | .inr (.inr ⟨k, i, o⟩) => ouL ((pats tm).map fun p =>
      .e (casa tm Hb p) (corpo tm Hb p k i.1 o))

/-- **Correção do passo**: as fórmulas calculam a codificação da configuração seguinte. -/
theorem pasF_correto (hd : jan tm ≤ Hb) (c : tm.Cfg) (hc : Ok tm (Hb + 1) c)
    (r : Bit tm Hb) : (pasF tm Hb r).eval (codif tm Hb c) = codif tm Hb (passoA tm.m c) r := by
  have hS : ∀ k, ∀ x ∈ c.stk k, x ∈ S tm k := fun k => (hc k).2
  have hex : ∃ p ∈ pats tm, (casa tm Hb p).eval (codif tm Hb c) = true :=
    ⟨patOf tm c hS, by simp [pats], (casa_iff tm Hb hd c _).mpr
      ⟨rfl, rfl, win_patOf tm c hS⟩⟩
  have hdados : ∀ p : Pat tm (jan tm), (casa tm Hb p).eval (codif tm Hb c) = true →
      novo tm p.1 p.2.1 (win tm p) = novo tm c.l c.var fun k => (c.stk k).take (jan tm) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := (casa_iff tm Hb hd c p).mp hp
    rw [h1, h2, funext h3]
  obtain ⟨n1, n2, n3⟩ := passoA_novo tm c
  rcases r with l | s | ⟨k, i, o⟩
  · refine ouL_casa tm Hb _ _ _ hex fun p _ hp => ?_
    rw [eval_const, hdados p hp, ← n1]; rfl
  · refine ouL_casa tm Hb _ _ _ hex fun p _ hp => ?_
    rw [eval_const, hdados p hp, ← n2]; rfl
  · refine ouL_casa tm Hb _ _ _ hex fun p _ hp => ?_
    simp only [corpo, hdados p hp]
    show _ = decide (((passoA tm.m c).stk k)[i.1]? = o.map Subtype.val)
    rw [n3 k, getElem?_append_drop]
    split_ifs with hi hsrc
    · rw [eval_const]
    · simp only [eval]
      rw [codif_cel tm c k hsrc]
    · rw [eval_const]
      have hlen := (hc k).1
      rw [List.getElem?_eq_none (by omega)]
      cases o <;> simp

end Passo

/-! ## Linha inicial e saída -/

section Bordas

variable (tm : FinTM2) (Hb : ℕ)

/-- A entrada na pilha `k₀`. -/
def ent (A : tm.Γ tm.k₀ ≃ Bool) {n : ℕ} (x : Fin n → Bool) : List (tm.Γ tm.k₀) :=
  List.ofFn fun i => A.symm (x i)

/-- Fórmulas da linha inicial: cada célula depende de no máximo um bit da entrada. -/
noncomputable def iniF (A : tm.Γ tm.k₀ ≃ Bool) (n : ℕ) (r : Bit tm Hb) : Form (Fin n) :=
  match r with
  | .inr (.inr ⟨_, i, _⟩) =>
    if h : i.1 < n then
      .ou (.e (.var ⟨i.1, h⟩)
          (const (codif tm Hb (initList tm (ent tm A fun _ : Fin n => true)) r)))
        (.e (.nao (.var ⟨i.1, h⟩))
          (const (codif tm Hb (initList tm (ent tm A fun _ : Fin n => false)) r)))
    else const (codif tm Hb (initList tm (ent tm A fun _ : Fin n => false)) r)
  | _ => const (codif tm Hb (initList tm (ent tm A fun _ : Fin n => false)) r)

theorem initList_stk (s s' : List (tm.Γ tm.k₀)) (k : tm.K) (i : ℕ) (h : s[i]? = s'[i]?) :
    ((initList tm s).stk k)[i]? = ((initList tm s').stk k)[i]? := by
  by_cases hk : k = tm.k₀
  · subst hk; simpa [initList] using h
  · simp [initList, hk]

theorem iniF_correto (A : tm.Γ tm.k₀ ≃ Bool) {n : ℕ} (x : Fin n → Bool) (r : Bit tm Hb) :
    (iniF tm Hb A n r).eval x = codif tm Hb (initList tm (ent tm A x)) r := by
  rcases r with l | s | ⟨k, i, o⟩
  · simp only [iniF, eval_const, codif, initList]; exact decide_eq_decide.mpr Iff.rfl
  · simp only [iniF, eval_const, codif, initList]; exact decide_eq_decide.mpr Iff.rfl
  · simp only [iniF]
    split_ifs with h
    · have key : ∀ b, x ⟨i.1, h⟩ = b →
          codif tm Hb (initList tm (ent tm A fun _ : Fin n => b)) (.inr (.inr ⟨k, i, o⟩)) =
            codif tm Hb (initList tm (ent tm A x)) (.inr (.inr ⟨k, i, o⟩)) := by
        intro b hb
        simp only [codif]
        rw [initList_stk tm _ (ent tm A x) k i.1 (by simp [ent, List.getElem?_ofFn, h, hb])]
      cases hx : x ⟨i.1, h⟩
      · simp only [eval, eval_const, hx, Bool.false_and, Bool.not_false, Bool.true_and,
          Bool.false_or]
        exact key false hx
      · simp only [eval, eval_const, hx, Bool.true_and, Bool.or_eq_true, Bool.not_true,
          Bool.false_and, Bool.or_false]
        exact key true hx
    · rw [eval_const]
      simp only [codif]
      rw [initList_stk tm _ (ent tm A x) k i.1 (by simp [ent, List.getElem?_ofFn, h])]

/-- Fórmula de saída: o topo da pilha de saída decodifica para `true`. -/
noncomputable def saiF (B' : tm.Γ tm.k₁ ≃ Bool) : Form (Bit tm Hb) :=
  ouL ((((Finset.univ : Finset (S tm tm.k₁)).toList.filter fun o => B' o.1)).map fun o =>
    .var (cel tm tm.k₁ 0 (some o)))

theorem saiF_correto (B' : tm.Γ tm.k₁ ≃ Bool) (b : Bool) (hb : B'.symm b ∈ S tm tm.k₁) :
    (saiF tm Hb B').eval (codif tm Hb (haltList tm [B'.symm b])) = b := by
  have hcel : ∀ o : S tm tm.k₁, codif tm Hb (haltList tm [B'.symm b]) (cel tm tm.k₁ 0 (some o)) =
      decide (B'.symm b = o.1) := by
    intro o
    rw [codif_cel tm _ _ (Nat.succ_pos _)]
    simp [haltList]
  cases b with
  | true =>
    rw [saiF, eval_ouL]
    refine ⟨.var (cel tm tm.k₁ 0 (some ⟨B'.symm true, hb⟩)), ?_, ?_⟩
    · refine List.mem_map.mpr ⟨⟨B'.symm true, hb⟩, ?_, rfl⟩
      simp
    · simp only [eval, hcel, decide_true]
  | false =>
    by_contra hne
    rw [Bool.not_eq_false, saiF, eval_ouL] at hne
    obtain ⟨φ, hφ, hv⟩ := hne
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hφ
    simp only [List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and] at ho
    simp only [eval, hcel, decide_eq_true_eq] at hv
    rw [← hv] at ho
    simp at ho

end Bordas

/-! ## A execução -/

section Execucao

variable (tm : FinTM2)

/-- **Invariante**: altura `≤ n + cres · t` e símbolos relevantes. -/
theorem ok_iter (c₀ : TM2.Cfg tm.Γ tm.Λ tm.σ) {n : ℕ}
    (h0 : ∀ k, (c₀.stk k).length ≤ n ∧ ∀ y ∈ c₀.stk k, y ∈ S tm k) :
    ∀ t, ∀ k, (((passoA tm.m)^[t] c₀).stk k).length ≤ n + cres tm * t ∧
      ∀ y ∈ ((passoA tm.m)^[t] c₀).stk k, y ∈ S tm k
  | 0, k => by simpa using h0 k
  | t + 1, k => by
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := ok_iter c₀ h0 t k
    generalize (passoA tm.m)^[t] c₀ = c at h1 h2
    rcases c with ⟨l, v, S'⟩
    rcases l with _ | lb
    · rw [passoA_parada tm.m _ rfl]
      exact ⟨by nlinarith, h2⟩
    · change ((TM2.stepAux (tm.m lb) v S').stk k).length ≤ _ ∧
        ∀ y ∈ (TM2.stepAux (tm.m lb) v S').stk k, y ∈ S tm k
      refine ⟨?_, fun y hy => ?_⟩
      · have := length_stepAux_le (tm.m lb) v S' k
        have := emp_le tm lb
        simp only at h1
        nlinarith
      · rcases mem_stepAux (tm.m lb) v S' k y hy with h | h
        · exact h2 y h
        · exact Or.inl (Set.mem_iUnion.mpr ⟨lb, h⟩)

theorem ok_ini (A : tm.Γ tm.k₀ ≃ Bool) {n : ℕ} (x : Fin n → Bool) (k : tm.K) :
    ((initList tm (ent tm A x)).stk k).length ≤ n ∧
      ∀ y ∈ (initList tm (ent tm A x)).stk k, y ∈ S tm k := by
  by_cases hk : k = tm.k₀
  · subst hk
    simp only [initList, dite_true]
    refine ⟨by simp [ent], fun y _ => ?_⟩
    exact Or.inr ⟨y, rfl⟩
  · simp [initList, hk]

/-- As linhas calculadas pelas fórmulas são as codificações da execução. -/
theorem linhas {Hb : ℕ} (hd : jan tm ≤ Hb) (c₀ : TM2.Cfg tm.Γ tm.Λ tm.σ) {n T : ℕ}
    (h0 : ∀ k, (c₀.stk k).length ≤ n ∧ ∀ y ∈ c₀.stk k, y ∈ S tm k)
    (hH : n + cres tm * T ≤ Hb + 1) :
    ∀ t ≤ T, (fun ρ r => (pasF tm Hb r).eval ρ)^[t] (codif tm Hb c₀) =
      codif tm Hb ((passoA tm.m)^[t] c₀)
  | 0, _ => rfl
  | t + 1, ht => by
    rw [Function.iterate_succ_apply', linhas hd c₀ h0 hH t (by omega),
      Function.iterate_succ_apply']
    funext r
    refine pasF_correto tm Hb hd _ (fun k => ⟨?_, (ok_iter tm c₀ h0 t k).2⟩) r
    have := (ok_iter tm c₀ h0 t k).1
    have : cres tm * t ≤ cres tm * T := Nat.mul_le_mul_left _ (by omega)
    omega

end Execucao

/-! ## Tamanho das fórmulas -/

section Tamanhos

variable (tm : FinTM2) (Hb : ℕ)

theorem tam_eL_vars {ι : Type*} : ∀ L : List (Form ι), (∀ φ ∈ L, φ.tam = 0) →
    (eL L).tam = L.length + 1
  | [], _ => rfl
  | φ :: L, h => by
    simp only [eL, tam, List.length_cons]
    rw [h φ (List.mem_cons_self ..), tam_eL_vars L fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)]
    ring

theorem tam_casa (p : Pat tm (jan tm)) :
    (casa tm Hb p).tam = Fintype.card tm.K * jan tm + 3 := by
  rw [casa, tam_eL_vars]
  · simp only [List.length_append, List.length_cons, List.length_nil, List.length_flatMap,
      List.length_map, List.length_range, List.map_const', List.sum_replicate, smul_eq_mul,
      Finset.length_toList, Finset.card_univ]
    ring
  · intro φ hφ
    simp only [List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_range,
      List.not_mem_nil, or_false] at hφ
    rcases hφ with (rfl | rfl) | ⟨_, _, _, _, rfl⟩ <;> rfl

theorem tam_ouL_le {ι : Type*} (L : List (Form ι)) (c : ℕ) (h : ∀ φ ∈ L, φ.tam ≤ c) :
    (ouL L).tam ≤ L.length * (c + 1) + 1 := by
  rw [tam_ouL]
  have := List.sum_le_length_nsmul (L.map fun φ => φ.tam + 1) (c + 1) (by
    intro x hx
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hx
    have := h φ hφ; omega)
  simp only [List.length_map, smul_eq_mul] at this
  omega

/-- Cota uniforme para as fórmulas de passo. -/
noncomputable def cP : ℕ := (pats tm).length * (Fintype.card tm.K * jan tm + 6) + 1

theorem tam_pasF (r : Bit tm Hb) : (pasF tm Hb r).tam ≤ cP tm := by
  have hc : ∀ p : Pat tm (jan tm), ∀ b : Form (Bit tm Hb), b.tam ≤ 1 →
      (Form.e (casa tm Hb p) b).tam ≤ Fintype.card tm.K * jan tm + 5 := by
    intro p b hb
    simp only [tam, tam_casa]
    omega
  rcases r with l | s | ⟨k, i, o⟩ <;> simp only [pasF] <;>
  · refine (tam_ouL_le _ (Fintype.card tm.K * jan tm + 5) ?_).trans
      (le_of_eq (by simp only [List.length_map, cP]; try ring))
    intro φ hφ
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hφ
    apply hc
    first
    | exact (tam_const _).le
    | (simp only [corpo]; split_ifs <;> simp [tam, tam_const])

theorem tam_iniF (A : tm.Γ tm.k₀ ≃ Bool) (n : ℕ) (r : Bit tm Hb) : (iniF tm Hb A n r).tam ≤ 6 := by
  rcases r with l | s | ⟨k, i, o⟩
  · simp [iniF, tam_const]
  · simp [iniF, tam_const]
  · simp only [iniF]
    split_ifs <;> simp [tam, tam_const]

theorem tam_saiF (B' : tm.Γ tm.k₁ ≃ Bool) :
    (saiF tm Hb B').tam ≤ Fintype.card (S tm tm.k₁) + 1 := by
  rw [saiF, tam_ouL]
  have hz : ∀ x ∈ (((Finset.univ : Finset (S tm tm.k₁)).toList.filter fun o => B' o.1).map
      fun o => (Form.var (cel tm (Hb := Hb) tm.k₁ 0 (some o)) : Form (Bit tm Hb))),
      x.tam + 1 = 1 := by
    intro x hx
    obtain ⟨o, -, rfl⟩ := List.mem_map.mp hx
    rfl
  rw [List.map_congr_left hz]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one, List.length_map]
  have := List.length_filter_le (fun o : S tm tm.k₁ => B' o.1) (Finset.univ : Finset _).toList
  simp only [Finset.length_toList, Finset.card_univ] at this
  omega

theorem custo_le {ι : Type*} {B : ℕ} (F : Fin B → Form ι) (c : ℕ) (h : ∀ b, (F b).tam ≤ c) :
    custo (List.ofFn F) ≤ B * (c + 1) := by
  rw [custo, List.length_ofFn, List.map_ofFn, List.sum_ofFn]
  have : ∑ b, (Form.tam ∘ F) b ≤ ∑ _b : Fin B, c := Finset.sum_le_sum fun b _ => h b
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  rw [Nat.mul_succ]
  omega

/-- Constante do número de bits por unidade de altura. -/
noncomputable def cB : ℕ :=
  Fintype.card (Option tm.Λ) + Fintype.card tm.σ + ∑ k, (Fintype.card (S tm k) + 1)

theorem card_bit : Fintype.card (Bit tm Hb) ≤ cB tm * (Hb + 1) := by
  simp only [Bit, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_option, cB]
  have h1 : ∑ k, (Hb + 1) * (Fintype.card (S tm k) + 1) =
      (Hb + 1) * ∑ k, (Fintype.card (S tm k) + 1) := by rw [Finset.mul_sum]
  rw [h1]
  nlinarith [Nat.zero_le (∑ k, (Fintype.card (S tm k) + 1)), Nat.zero_le (Fintype.card tm.Λ),
    Nat.zero_le (Fintype.card tm.σ)]

end Tamanhos

/-! ## O circuito de uma máquina -/

section Principal

variable {χ : Palavra → Bool}
  (M : TM2ComputableInPolyTime LigacaoPNP.cod Computability.encodeBool χ)

/-- Altura do tableau para entradas de tamanho `n`. -/
noncomputable def altura (n : ℕ) : ℕ := n + cres M.tm * M.time.eval n + jan M.tm

/-- O número de portas do circuito. -/
noncomputable def tamanho (n : ℕ) : ℕ :=
  custo (List.ofFn fun b => iniF M.tm (altura M n) M.inputAlphabet n
      ((Fintype.equivFin (Bit M.tm (altura M n))).symm b)) +
    M.time.eval n * custo (List.ofFn fun b => FormM.map (Fintype.equivFin (Bit M.tm (altura M n)))
      (pasF M.tm (altura M n) ((Fintype.equivFin (Bit M.tm (altura M n))).symm b))) +
    ((FormM.map (Fintype.equivFin (Bit M.tm (altura M n)))
      (saiF M.tm (altura M n) M.outputAlphabet)).tam + 1)

/-- **Simulação**: a fatia de tamanho `n` tem circuito com `tamanho M n` portas. -/
theorem circuito_M (n : ℕ) :
    TemCircuito (fun x : Fin n → Bool => χ (List.ofFn x)) (tamanho M n) := by
  set Hb := altura M n with hHb
  set T := M.time.eval n with hT
  set e := Fintype.equivFin (Bit M.tm Hb) with he
  have hd : jan M.tm ≤ Hb := by simp only [hHb, altura]; omega
  have hH : n + cres M.tm * T ≤ Hb + 1 := by simp only [hHb, altura, hT]; omega
  have h := temCircuito_camadas (n := n) (T := T)
    (fun b => iniF M.tm Hb M.inputAlphabet n (e.symm b))
    (fun b => FormM.map e (pasF M.tm Hb (e.symm b)))
    (FormM.map e (saiF M.tm Hb M.outputAlphabet))
  have hfun : (fun x : Fin n → Bool => χ (List.ofFn x)) = fun x =>
      (FormM.map e (saiF M.tm Hb M.outputAlphabet)).eval
        ((fun r b => (FormM.map e (pasF M.tm Hb (e.symm b))).eval r)^[T]
          (fun b => (iniF M.tm Hb M.inputAlphabet n (e.symm b)).eval x)) := by
    funext x
    set c₀ : TM2.Cfg M.tm.Γ M.tm.Λ M.tm.σ := initList M.tm (ent M.tm M.inputAlphabet x) with hc₀
    have h0 : ∀ k, (c₀.stk k).length ≤ n ∧ ∀ y ∈ c₀.stk k, y ∈ S M.tm k :=
      ok_ini M.tm M.inputAlphabet x
    -- linhas indexadas por `Fin B`
    have hrows : ∀ t, (fun r b => (FormM.map e (pasF M.tm Hb (e.symm b))).eval r)^[t]
        (fun b => (iniF M.tm Hb M.inputAlphabet n (e.symm b)).eval x) =
        ((fun ρ r => (pasF M.tm Hb r).eval ρ)^[t] (codif M.tm Hb c₀)) ∘ e.symm := by
      intro t
      induction t with
      | zero =>
        funext b
        simp only [Function.iterate_zero, id, Function.comp]
        exact iniF_correto M.tm Hb M.inputAlphabet x _
      | succ t ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
        funext b
        simp only [Function.comp, FormM.eval_map]
        congr 1
        funext r
        simp
    rw [hrows, FormM.eval_map, linhas M.tm hd c₀ h0 hH T le_rfl]
    -- a execução para em `T` passos com a saída `χ w`
    have hout := M.outputsFun (List.ofFn x)
    have hlen : (LigacaoPNP.cod (List.ofFn x)).length = n := by simp [LigacaoPNP.cod]
    have hin : List.map M.inputAlphabet.invFun (LigacaoPNP.cod (List.ofFn x)) =
        ent M.tm M.inputAlphabet x := by
      simp [LigacaoPNP.cod, ent, List.map_ofFn, Function.comp_def]
    rw [hlen, hin] at hout
    have hfim : (passoA M.tm.m)^[T] c₀ =
        haltList M.tm [M.outputAlphabet.symm (χ (List.ofFn x))] := by
      have hev := hout.evals_in_steps
      simp only [Computability.encodeBool] at hev
      exact acolchoada_de_evals M.tm.m c₀ _ rfl _ T hout.steps_le_m hev
    have hmem : M.outputAlphabet.symm (χ (List.ofFn x)) ∈ S M.tm M.tm.k₁ := by
      have := (ok_iter M.tm c₀ h0 T M.tm.k₁).2
      rw [hfim] at this
      exact this _ (by simp [haltList])
    have hcomp : (codif M.tm Hb ((passoA M.tm.m)^[T] c₀) ∘ e.symm) ∘ e =
        codif M.tm Hb ((passoA M.tm.m)^[T] c₀) := by
      funext r; simp
    rw [hcomp, hfim, saiF_correto M.tm Hb M.outputAlphabet _ hmem]
  rw [hfun]
  exact h

end Principal

/-! ## Cota polinomial e a ponte -/

/-- `K (n+1)^m ≤ n^k + k` para algum `k`. -/
theorem poli (K m : ℕ) : ∃ k, ∀ n, K * (n + 1) ^ m ≤ n ^ k + k := by
  refine ⟨K * (K * 2 ^ m + 1) ^ m + m + 1, fun n => ?_⟩
  rcases Nat.lt_or_ge n (K * 2 ^ m + 1) with h | h
  · have h1 : (n + 1) ^ m ≤ (K * 2 ^ m + 1) ^ m := Nat.pow_le_pow_left h m
    have h2 := Nat.mul_le_mul_left K h1
    omega
  · have hn1 : 1 ≤ n := le_trans (Nat.le_add_left 1 _) h
    have h2 : (n + 1) ^ m ≤ (2 * n) ^ m := Nat.pow_le_pow_left (by omega) m
    rw [mul_pow] at h2
    have h3 : K * 2 ^ m * n ^ m ≤ n * n ^ m := Nat.mul_le_mul_right _ (by omega)
    have h5 : n ^ (m + 1) ≤ n ^ (K * (K * 2 ^ m + 1) ^ m + m + 1) :=
      Nat.pow_le_pow_right hn1 (by omega)
    calc K * (n + 1) ^ m ≤ K * (2 ^ m * n ^ m) := Nat.mul_le_mul_left K h2
      _ = K * 2 ^ m * n ^ m := by ring
      _ ≤ n * n ^ m := h3
      _ = n ^ (m + 1) := by ring
      _ ≤ _ := h5
      _ ≤ _ := Nat.le_add_right _ _

section Final

variable {χ : Palavra → Bool}
  (M : TM2ComputableInPolyTime LigacaoPNP.cod Computability.encodeBool χ)

/-- Constante da cota de tamanho. -/
noncomputable def Kc : ℕ :=
  7 * (cB M.tm * (1 + cres M.tm * M.time.eval 1 + jan M.tm)) +
    M.time.eval 1 * (cB M.tm * (1 + cres M.tm * M.time.eval 1 + jan M.tm)) * (cP M.tm + 1) +
    (Fintype.card (S M.tm M.tm.k₁) + 2)

/-- **Tamanho polinomial**: `tamanho M n ≤ Kc · (n+1)^(2 grau + 2)`. -/
theorem tamanho_le (n : ℕ) :
    tamanho M n ≤ Kc M * ((n + 1) ^ (M.time.natDegree + 1)) ^ 2 := by
  unfold tamanho
  set Hb := altura M n with hHb
  set T := M.time.eval n with hT
  set B := Fintype.card (Bit M.tm Hb) with hBdef
  generalize Fintype.equivFin (Bit M.tm Hb) = e
  set a := M.time.eval 1
  set D := M.time.natDegree
  set P := (n + 1) ^ (D + 1) with hP
  have hP1 : 1 ≤ P := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have hNP : n + 1 ≤ P := by
    rw [hP]; calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  have hTP : T ≤ a * P := by
    have h1 := cota M.time n
    have h2 : (n + 1) ^ D ≤ P := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
    calc T ≤ a * (n + 1) ^ D := h1
      _ ≤ a * P := Nat.mul_le_mul_left _ h2
  have hH : Hb + 1 ≤ (1 + cres M.tm * a + jan M.tm) * P := by
    simp only [hHb, altura]
    have h1 : cres M.tm * T ≤ cres M.tm * (a * P) := Nat.mul_le_mul_left _ hTP
    have h2 : jan M.tm ≤ jan M.tm * P := Nat.le_mul_of_pos_right _ hP1
    nlinarith
  have hB : B ≤ cB M.tm * (1 + cres M.tm * a + jan M.tm) * P := by
    have := card_bit M.tm Hb
    calc B ≤ cB M.tm * (Hb + 1) := this
      _ ≤ cB M.tm * ((1 + cres M.tm * a + jan M.tm) * P) := Nat.mul_le_mul_left _ hH
      _ = _ := by ring
  have c1 : custo (List.ofFn fun b => iniF M.tm Hb M.inputAlphabet n (e.symm b)) ≤ B * 7 :=
    custo_le _ 6 fun b => tam_iniF M.tm Hb M.inputAlphabet n _
  have c2 : custo (List.ofFn fun b => FormM.map e (pasF M.tm Hb (e.symm b))) ≤
      B * (cP M.tm + 1) :=
    custo_le _ (cP M.tm) fun b => by rw [FormM.tam_map]; exact tam_pasF M.tm Hb _
  have c3 : (FormM.map e (saiF M.tm Hb M.outputAlphabet)).tam ≤
      Fintype.card (S M.tm M.tm.k₁) + 1 := by
    rw [FormM.tam_map]; exact tam_saiF M.tm Hb _
  have hsum : custo (List.ofFn fun b => iniF M.tm Hb M.inputAlphabet n (e.symm b)) +
      T * custo (List.ofFn fun b => FormM.map e (pasF M.tm Hb (e.symm b))) +
      ((FormM.map e (saiF M.tm Hb M.outputAlphabet)).tam + 1) ≤
      B * 7 + T * (B * (cP M.tm + 1)) + (Fintype.card (S M.tm M.tm.k₁) + 2) := by
    have := Nat.mul_le_mul_left T c2
    omega
  set β := cB M.tm * (1 + cres M.tm * a + jan M.tm)
  have e1 : B * 7 ≤ 7 * β * P ^ 2 := by
    have : B * 7 ≤ β * P * 7 := Nat.mul_le_mul_right _ hB
    have hP2 : P ≤ P ^ 2 := by nlinarith
    nlinarith
  have e2 : T * (B * (cP M.tm + 1)) ≤ a * β * (cP M.tm + 1) * P ^ 2 := by
    have h1 : T * (B * (cP M.tm + 1)) ≤ (a * P) * ((β * P) * (cP M.tm + 1)) :=
      Nat.mul_le_mul hTP (Nat.mul_le_mul_right _ hB)
    calc T * (B * (cP M.tm + 1)) ≤ (a * P) * ((β * P) * (cP M.tm + 1)) := h1
      _ = _ := by ring
  have e3 : Fintype.card (S M.tm M.tm.k₁) + 2 ≤ (Fintype.card (S M.tm M.tm.k₁) + 2) * P ^ 2 :=
    Nat.le_mul_of_pos_right _ (by positivity)
  calc _ ≤ _ := hsum
    _ ≤ 7 * β * P ^ 2 + a * β * (cP M.tm + 1) * P ^ 2 +
        (Fintype.card (S M.tm M.tm.k₁) + 2) * P ^ 2 := by omega
    _ = Kc M * P ^ 2 := by simp only [Kc]; ring

theorem tamanho_poli : ∃ k, ∀ n, tamanho M n ≤ n ^ k + k := by
  obtain ⟨k, hk⟩ := poli (Kc M) (2 * (M.time.natDegree + 1))
  refine ⟨k, fun n => (tamanho_le M n).trans ?_⟩
  rw [← pow_mul, mul_comm (M.time.natDegree + 1) 2]
  exact hk n

end Final

/-- **Ponte `P ⊆ P/poly` provada** (Savage 1972): toda linguagem de `P` (máquinas `FinTM2` da
Mathlib em tempo polinomial) tem circuitos de tamanho polinomial. -/
theorem pemPpoly : PemPpoly := by
  intro L hL
  obtain ⟨χ, hχ, ⟨M⟩⟩ := hL
  obtain ⟨k, hk⟩ := tamanho_poli M
  refine ⟨k, fun n => ?_⟩
  have hf : fatia L n = fun x : Fin n → Bool => χ (List.ofFn x) := by
    funext x
    simp only [fatia]
    by_cases h : χ (List.ofFn x) = true
    · simp [(hχ _).mpr h, h]
    · have : List.ofFn x ∉ L := fun hm => h ((hχ _).mp hm)
      simp only [this, decide_false]
      cases hc : χ (List.ofFn x)
      · rfl
      · exact absurd hc h
  rw [hf]
  exact temCircuito_mono (hk n) (circuito_M M n)

/-- **`NP ⊄ P/poly ⇒ P ≠ NP`**, sem pontes. -/
theorem p_ne_np_de_naoPpoly (h : NPnaoEmPpoly) : PneNP := p_ne_np_de_ppoly pemPpoly h

/-- **Cotas superpolinomiais para uma linguagem de NP ⇒ P ≠ NP**, sem pontes. -/
theorem p_ne_np_de_cotas_sem_ponte {L : Linguagem} (hL : L ∈ classeNP)
    (h : ∀ k : ℕ, CotaInferior L fun n => n ^ k + k) : PneNP :=
  p_ne_np_de_cotas pemPpoly hL h

end ATK.PemPpoly

#print axioms ATK.PemPpoly.FormM.eval_map
#print axioms ATK.PemPpoly.FormM.tam_map
#print axioms ATK.PemPpoly.prof_le
#print axioms ATK.PemPpoly.emp_le
#print axioms ATK.PemPpoly.simb_finite
#print axioms ATK.PemPpoly.S_finite
#print axioms ATK.PemPpoly.codif_cel
#print axioms ATK.PemPpoly.celW_val
#print axioms ATK.PemPpoly.length_win
#print axioms ATK.PemPpoly.casa_iff
#print axioms ATK.PemPpoly.win_patOf
#print axioms ATK.PemPpoly.ouL_casa
#print axioms ATK.PemPpoly.passoA_novo
#print axioms ATK.PemPpoly.getElem?_append_drop
#print axioms ATK.PemPpoly.pasF_correto
#print axioms ATK.PemPpoly.initList_stk
#print axioms ATK.PemPpoly.iniF_correto
#print axioms ATK.PemPpoly.saiF_correto
#print axioms ATK.PemPpoly.ok_iter
#print axioms ATK.PemPpoly.ok_ini
#print axioms ATK.PemPpoly.linhas
#print axioms ATK.PemPpoly.tam_eL_vars
#print axioms ATK.PemPpoly.tam_casa
#print axioms ATK.PemPpoly.tam_ouL_le
#print axioms ATK.PemPpoly.tam_pasF
#print axioms ATK.PemPpoly.tam_iniF
#print axioms ATK.PemPpoly.tam_saiF
#print axioms ATK.PemPpoly.custo_le
#print axioms ATK.PemPpoly.card_bit
#print axioms ATK.PemPpoly.circuito_M
#print axioms ATK.PemPpoly.poli
#print axioms ATK.PemPpoly.tamanho_le
#print axioms ATK.PemPpoly.tamanho_poli
#print axioms ATK.PemPpoly.pemPpoly
#print axioms ATK.PemPpoly.p_ne_np_de_naoPpoly
#print axioms ATK.PemPpoly.p_ne_np_de_cotas_sem_ponte
