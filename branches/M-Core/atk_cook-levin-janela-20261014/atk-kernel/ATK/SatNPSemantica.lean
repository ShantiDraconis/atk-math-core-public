import ATK.ModeloPNP

/-!
# ATK — SAT ∈ NP, parte semântica (ponte B4, metade "SAT ∈ NP")

O verificador lê `y = ⟨x, c⟩` em símbolos de dois bits (`00`, `01`, `10` = fim de literal,
`11` = fim de cláusula). O certificado `c` é uma lista de segmentos separados por `10`; cada
segmento é `valor · índice` (o índice escrito do bit mais significativo para o menos
significativo). A valoração lida do certificado é `τ_c(i)` = valor do primeiro segmento com o
índice de `i` (padrão `false`).

Este arquivo define a função que a máquina vai calcular (`verif`, espelho exato da máquina) e
prova a sua semântica:

* `verif_par_iff`: `verif ⟨x, c⟩ = true ⟺ ∃ φ, x = codCNF φ ∧ Satisfaz τ_c φ`;
* `certificado`: para `φ` satisfeita por `τ`, um certificado `c` com `|c| ≤ |codCNF φ|` e
  `τ_c = τ` nas variáveis de `φ`.

A máquina `FinTM2` que calcula `verif` em tempo polinomial está em `ATK.SatNPMaquina`.
-/

namespace ATK.SatNPSemantica

open ATK.LigacaoPNP ATK.ModeloPNP Turing Computability

/-! ### Símbolos -/

/-- Símbolo de dois bits. -/
abbrev Sym := Bool × Bool

/-- Fim de literal / de segmento (`10`). -/
def sL : Sym := (true, false)

/-- Fim de cláusula (`11`). -/
def sC : Sym := (true, true)

/-- Leitura em símbolos de dois bits (um bit final ímpar é descartado). -/
def syms : List Bool → List Sym
  | a :: b :: r => (a, b) :: syms r
  | _ => []

/-- O segundo componente de um par `⟨x, c⟩`: o que vem depois do separador. -/
def decC : List Bool → List Bool
  | a :: b :: r => if a = b then decC r else r
  | _ => []

theorem decC_par (w c : Palavra) : decC (par w c) = c := by
  induction w with
  | nil => simp [par, decC]
  | cons b w ih =>
    simp only [par, List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc] at ih ⊢
    rw [decC]; simp [ih]

/-! ### Segmentos do certificado e consulta -/

/-- Primeiro segmento (até `sL`, exclusive) e o resto depois de `sL`. -/
def seg : List Sym → List Sym × List Sym
  | [] => ([], [])
  | s :: r => if s = sL then ([], r) else (s :: (seg r).1, (seg r).2)

theorem seg_snd_length_le : ∀ C : List Sym, (seg C).2.length ≤ C.length
  | [] => le_refl _
  | s :: r => by
    unfold seg
    split_ifs
    · simp
    · simp only [List.length_cons]; have := seg_snd_length_le r; omega

theorem seg_snd_length_lt (s : Sym) (r : List Sym) : (seg (s :: r)).2.length < (s :: r).length := by
  unfold seg
  split_ifs
  · simp
  · simp only [List.length_cons]; have := seg_snd_length_le r; omega

/-- Consulta: valor do primeiro segmento de `C` cujo índice (cauda) é `I`; `false` se nenhum. -/
def lookup (I : List Sym) : List Sym → Bool
  | [] => false
  | s :: r =>
    if (seg (s :: r)).1.tail = I then ((seg (s :: r)).1.head?.map Prod.snd).getD false
    else lookup I (seg (s :: r)).2
termination_by C => C.length
decreasing_by exact seg_snd_length_lt s r

/-! ### A avaliação (espelho da máquina) -/

mutual
/-- No início de um literal ou de uma cláusula. `fresh`: nenhum literal desde o último `sC`;
`cs`: a cláusula corrente já tem literal verdadeiro; `all`: todas as cláusulas fechadas até aqui
são satisfeitas. -/
def evalStart (C : List Sym) : Bool → Bool → Bool → List Sym → Bool
  | fresh, _, all, [] => fresh && all
  | _, cs, all, s :: X =>
    if s = sC then evalStart C true false (all && cs) X
    else if s.1 then false
    else evalIdx C s.2 [] cs all X

/-- Lendo o índice de um literal de polaridade `p`; `I` = símbolos lidos (o último no topo). -/
def evalIdx (C : List Sym) (p : Bool) : List Sym → Bool → Bool → List Sym → Bool
  | _, _, _, [] => false
  | I, cs, all, s :: X =>
    if s = sC then false
    else if s.1 then
      (if I.head?.all (· = (false, true)) then evalStart C false (cs || (lookup I C == p)) all X
       else false)
    else evalIdx C p (s :: I) cs all X
end

/-- **A função calculada pelo verificador.** -/
def verif (y : List Bool) : Bool :=
  (dec y).length % 2 == 0 && evalStart (syms (decC y)) true false true (syms (dec y))

/-! ### Codificação de fórmulas em símbolos -/

/-- Símbolos do índice de uma variável, na ordem de `codLiteral` (bit menos significativo
primeiro). -/
def bitsSym (i : ℕ) : List Sym := i.bits.map fun b => (false, b)

def encLit (ℓ : Literal) : List Sym := (false, ℓ.2) :: bitsSym ℓ.1 ++ [sL]

def encClause (K : Clausula) : List Sym := K.flatMap encLit ++ [sC]

def encCNF (φ : CNF) : List Sym := φ.flatMap encClause

theorem syms_cons_cons (a b : Bool) (r : List Bool) : syms (a :: b :: r) = (a, b) :: syms r := rfl

theorem syms_flatMap_simb (l : List Bool) (r : List Bool) :
    syms (l.flatMap simb ++ r) = l.map (fun b => (false, b)) ++ syms r := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.flatMap_cons, simb, List.cons_append, List.nil_append,
      List.map_cons] at ih ⊢
    rw [syms_cons_cons, ih]

theorem syms_codLiteral (ℓ : Literal) (r : List Bool) :
    syms (codLiteral ℓ ++ r) = encLit ℓ ++ syms r := by
  simp only [codLiteral, simb, List.cons_append, List.nil_append, List.append_assoc]
  rw [syms_cons_cons, syms_flatMap_simb]
  simp [encLit, bitsSym, sL, syms]

theorem syms_codClausula (K : Clausula) (r : List Bool) :
    syms (codClausula K ++ r) = encClause K ++ syms r := by
  unfold codClausula encClause
  induction K with
  | nil => simp [syms, sC]
  | cons ℓ K ih =>
    simp only [List.flatMap_cons, List.append_assoc] at ih ⊢
    rw [syms_codLiteral, ih]

theorem syms_codCNF (φ : CNF) : syms (codCNF φ) = encCNF φ := by
  unfold codCNF encCNF
  induction φ with
  | nil => simp [syms]
  | cons K φ ih =>
    simp only [List.flatMap_cons]
    rw [syms_codClausula, ih]

theorem codCNF_length_even (φ : CNF) : (codCNF φ).length % 2 = 0 := by
  have hl : ∀ ℓ : Literal, (codLiteral ℓ).length % 2 = 0 := by
    intro ℓ
    simp only [codLiteral, simb, List.length_append, List.length_cons, List.length_nil,
      List.length_flatMap, List.map_const', List.sum_replicate, smul_eq_mul]
    omega
  have hc : ∀ K : Clausula, (codClausula K).length % 2 = 0 := by
    intro K
    simp only [codClausula, List.length_append, List.length_flatMap, List.length_cons,
      List.length_nil]
    induction K with
    | nil => simp
    | cons ℓ K ih => simp only [List.map_cons, List.sum_cons]; have := hl ℓ; omega
  simp only [codCNF, List.length_flatMap]
  induction φ with
  | nil => simp
  | cons K φ ih => simp only [List.map_cons, List.sum_cons]; have := hc K; omega

/-! ### Índices binários -/

/-- Inversa de `Nat.bits` (bit menos significativo primeiro). -/
def ofBits : List Bool → ℕ
  | [] => 0
  | b :: l => 2 * ofBits l + (if b then 1 else 0)

theorem ofBits_bits (n : ℕ) : ofBits n.bits = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp [ofBits]
    · have hlt : n / 2 < n := Nat.div_lt_self hpos (by norm_num)
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have hne : n / 2 ≠ 0 := by omega
        have hn : n = 2 * (n / 2) := by omega
        rw [hn, Nat.bit0_bits _ hne, ofBits, ih _ hlt]
        simp
      · have hn : n = 2 * (n / 2) + 1 := by omega
        rw [hn, Nat.bit1_bits, ofBits, ih _ hlt]
        simp

theorem bits_injective : Function.Injective Nat.bits := fun m n h => by
  rw [← ofBits_bits m, ← ofBits_bits n, h]

/-- Representação canônica: vazia ou terminando em `true`. -/
def Canon (l : List Bool) : Prop := l.getLast? = none ∨ l.getLast? = some true

theorem bits_canon (n : ℕ) : Canon n.bits := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; left; simp
    · have hlt : n / 2 < n := Nat.div_lt_self hpos (by norm_num)
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · have hne : n / 2 ≠ 0 := by omega
        have hn : n = 2 * (n / 2) := by omega
        rw [hn, Nat.bit0_bits _ hne]
        have hb : (n / 2).bits ≠ [] := by
          intro hb; apply hne; rw [← ofBits_bits (n / 2), hb]; rfl
        rcases ih _ hlt with h1 | h1
        · exact absurd (List.getLast?_eq_none_iff.mp h1) hb
        · right; rw [List.getLast?_cons, h1]; rfl
      · have hn : n = 2 * (n / 2) + 1 := by omega
        rw [hn, Nat.bit1_bits]
        rcases ih _ hlt with h1 | h1
        · right; rw [List.getLast?_cons, h1]; rfl
        · right; rw [List.getLast?_cons, h1]; rfl

theorem bits_ofBits : ∀ l : List Bool, Canon l → (ofBits l).bits = l
  | [], _ => by simp [ofBits]
  | b :: l, hc => by
    by_cases hl : l = []
    · subst hl
      have hb : b = true := by
        rcases hc with h | h <;> simp at h; exact h
      subst hb; simp [ofBits]
    · have hcl : Canon l := by
        rcases hc with h | h
        · simp at h
        · right; rw [List.getLast?_cons] at h
          rcases hg : l.getLast? with _ | x
          · exact absurd (List.getLast?_eq_none_iff.mp hg) hl
          · rw [hg] at h; simpa using h
      have ih := bits_ofBits l hcl
      have hne : ofBits l ≠ 0 := by intro h0; apply hl; rw [← ih, h0]; simp
      cases b
      · simp only [ofBits, Bool.false_eq_true, ite_false, add_zero]
        rw [Nat.bit0_bits _ hne, ih]
      · simp only [ofBits, ite_true]
        rw [Nat.bit1_bits, ih]

/-! ### A consulta do certificado -/

/-- Índice como fica na pilha da máquina: o bit mais significativo no topo. -/
def idxSym (i : ℕ) : List Sym := (bitsSym i).reverse

/-- A valoração lida do certificado (em símbolos). -/
def tau (C : List Sym) (i : ℕ) : Bool := lookup (idxSym i) C

/-- Valor de uma cláusula sob o certificado. -/
def clauseVal (C : List Sym) (K : Clausula) : Bool := K.any fun ℓ => lookup (idxSym ℓ.1) C == ℓ.2

theorem satisfaz_iff (C : List Sym) (φ : CNF) :
    Satisfaz (tau C) φ ↔ φ.all (clauseVal C) = true := by
  simp only [Satisfaz, List.all_eq_true, clauseVal, List.any_eq_true, beq_iff_eq, tau]

/-! ### Completude: a avaliação sobre fórmulas codificadas -/

theorem evalStart_sC (C : List Sym) (fresh cs all : Bool) (X : List Sym) :
    evalStart C fresh cs all (sC :: X) = evalStart C true false (all && cs) X := by
  rw [evalStart]; simp

theorem evalIdx_bits (C : List Sym) (p : Bool) (X : List Sym) :
    ∀ (l : List Bool) (I : List Sym) (cs all : Bool),
      evalIdx C p I cs all (l.map (fun b => (false, b)) ++ sL :: X) =
        (if ((l.map (fun b => (false, b))).reverse ++ I).head?.all (· = (false, true)) then
          evalStart C false (cs || (lookup ((l.map (fun b => (false, b))).reverse ++ I) C == p)) all X
        else false)
  | [], I, cs, all => by
    rw [List.map_nil, List.nil_append, evalIdx]
    have h1 : sL ≠ sC := by decide
    have h2 : sL.1 = true := rfl
    simp only [h1, h2, ↓reduceIte, List.reverse_nil, List.nil_append]
    rfl
  | b :: l, I, cs, all => by
    rw [List.map_cons, List.cons_append, evalIdx]
    simp only [sC, Prod.mk.injEq, Bool.false_eq_true, false_and, ite_false]
    rw [evalIdx_bits C p X l ((false, b) :: I) cs all]
    simp

theorem bitsSym_reverse_head (i : ℕ) :
    ((bitsSym i).reverse).head?.all (· = (false, true)) = true := by
  rw [List.head?_reverse, bitsSym, List.getLast?_map]
  rcases bits_canon i with h | h <;> simp [h]

theorem evalStart_encLit (C : List Sym) (ℓ : Literal) (fresh cs all : Bool) (X : List Sym) :
    evalStart C fresh cs all (encLit ℓ ++ X) =
      evalStart C false (cs || (lookup (idxSym ℓ.1) C == ℓ.2)) all X := by
  simp only [encLit, List.cons_append, List.append_assoc, List.nil_append]
  rw [evalStart]
  simp only [sC, Prod.mk.injEq, Bool.false_eq_true, false_and, ite_false]
  rw [bitsSym, evalIdx_bits]
  have h := bitsSym_reverse_head ℓ.1
  simp only [bitsSym] at h
  simp only [List.append_nil, h, ↓reduceIte]
  rfl

theorem evalStart_encClause (C : List Sym) (all : Bool) (X : List Sym) :
    ∀ (K : Clausula) (fresh cs : Bool),
      evalStart C fresh cs all (encClause K ++ X) =
        evalStart C true false (all && (cs || clauseVal C K)) X
  | [], fresh, cs => by
    simp [encClause, evalStart_sC, clauseVal]
  | ℓ :: K, fresh, cs => by
    have h : encClause (ℓ :: K) ++ X = encLit ℓ ++ (encClause K ++ X) := by
      simp [encClause]
    rw [h, evalStart_encLit, evalStart_encClause C all X K]
    simp [clauseVal, Bool.or_assoc]

theorem evalStart_encCNF (C : List Sym) :
    ∀ (φ : CNF) (all : Bool), evalStart C true false all (encCNF φ) = (all && φ.all (clauseVal C))
  | [], all => by simp [encCNF, evalStart]
  | K :: φ, all => by
    have h : encCNF (K :: φ) = encClause K ++ encCNF φ := by simp [encCNF]
    rw [h, evalStart_encClause, evalStart_encCNF C φ]
    simp [Bool.and_assoc]

theorem verif_codCNF (φ : CNF) (c : List Bool) :
    verif (par (codCNF φ) c) = φ.all (clauseVal (syms c)) := by
  simp [verif, dec_par, decC_par, codCNF_length_even, syms_codCNF, evalStart_encCNF]

/-! ### Correção: o que o verificador aceita é uma fórmula codificada satisfeita -/

theorem eval_all_false (C : List Sym) : ∀ X : List Sym,
    (∀ fresh cs, evalStart C fresh cs false X = false) ∧
      (∀ p I cs, evalIdx C p I cs false X = false)
  | [] => ⟨fun fresh cs => by simp [evalStart], fun p I cs => by simp [evalIdx]⟩
  | s :: X => by
    have ih := eval_all_false C X
    refine ⟨fun fresh cs => ?_, fun p I cs => ?_⟩
    · rw [evalStart]
      split_ifs
      · simpa using ih.1 true false
      · rfl
      · exact ih.2 s.2 [] cs
    · rw [evalIdx]
      split_ifs
      · rfl
      · exact ih.1 false _
      · rfl
      · exact ih.2 p (s :: I) cs

theorem sym_eq_of_fst (s : Sym) (h : s.1 = false) : s = (false, s.2) := by
  rcases s with ⟨a, b⟩; simp_all

theorem sym_eq_sL (s : Sym) (h1 : s ≠ sC) (h2 : s.1 = true) : s = sL := by
  rcases s with ⟨a, b⟩; simp_all [sC, sL]

theorem canon_of_head (l : List Bool) :
    ((l.map (fun b => (false, b))).reverse ++ []).head?.all (· = (false, true)) = true → Canon l := by
  rw [List.append_nil, List.head?_reverse, List.getLast?_map]
  rcases h : l.getLast? with _ | b
  · intro; left; exact h
  · intro hb; right; simp at hb; rw [h, hb]

theorem eval_sound (C : List Sym) : ∀ X : List Sym,
    (∀ all, evalStart C true false all X = true →
      ∃ φ : CNF, X = encCNF φ ∧ all = true ∧ φ.all (clauseVal C) = true) ∧
    (∀ cs all, evalStart C false cs all X = true →
      ∃ (K : Clausula) (φ : CNF), X = K.flatMap encLit ++ sC :: encCNF φ ∧ all = true ∧
        (cs || clauseVal C K) = true ∧ φ.all (clauseVal C) = true) ∧
    (∀ p I cs all, evalIdx C p I cs all X = true →
      ∃ (l : List Bool) (K : Clausula) (φ : CNF),
        X = l.map (fun b => (false, b)) ++ sL :: (K.flatMap encLit ++ sC :: encCNF φ) ∧
        ((l.map (fun b => (false, b))).reverse ++ I).head?.all (· = (false, true)) = true ∧
        all = true ∧
        (cs || (lookup ((l.map (fun b => (false, b))).reverse ++ I) C == p) || clauseVal C K) = true ∧
        φ.all (clauseVal C) = true)
  | [] => by
    refine ⟨fun all h => ⟨[], rfl, by simpa [evalStart] using h, rfl⟩, fun cs all h => ?_,
      fun p I cs all h => ?_⟩
    · simp [evalStart] at h
    · simp [evalIdx] at h
  | s :: X => by
    obtain ⟨ih1, ih2, ih3⟩ := eval_sound C X
    -- o literal que começa com `s` (polaridade `s.2`) e cujo índice é `l`
    have lit : ∀ (l : List Bool), Canon l →
        ∃ ℓ : Literal, ℓ.2 = s.2 ∧ bitsSym ℓ.1 = l.map (fun b => (false, b)) ∧
          idxSym ℓ.1 = (l.map (fun b => (false, b))).reverse := fun l hl =>
      ⟨(ofBits l, s.2), rfl, by simp [bitsSym, bits_ofBits l hl], by
        simp [idxSym, bitsSym, bits_ofBits l hl]⟩
    refine ⟨fun all h => ?_, fun cs all h => ?_, fun p I cs all h => ?_⟩
    · rw [evalStart] at h
      split_ifs at h with h1 h2
      · simp [(eval_all_false C X).1] at h
      · obtain ⟨l, K, φ, hX, hc, ha, hv, hφ⟩ := ih3 s.2 [] false all h
        obtain ⟨ℓ, hℓ2, hb, hi⟩ := lit l (canon_of_head l hc)
        refine ⟨(ℓ :: K) :: φ, ?_, ha, ?_⟩
        · rw [sym_eq_of_fst s (by simpa using h2), hX]
          simp [encCNF, encClause, encLit, hb, hℓ2]
        · simp only [List.all_cons, Bool.and_eq_true]
          refine ⟨?_, hφ⟩
          simp only [clauseVal, List.any_cons, hi, hℓ2]
          simpa [clauseVal] using hv
    · rw [evalStart] at h
      split_ifs at h with h1 h2
      · obtain ⟨φ, hX, ha, hφ⟩ := ih1 _ h
        simp only [Bool.and_eq_true] at ha
        refine ⟨[], φ, ?_, ha.1, by simp [clauseVal, ha.2], hφ⟩
        rw [h1, hX]; simp
      · obtain ⟨l, K, φ, hX, hc, ha, hv, hφ⟩ := ih3 s.2 [] cs all h
        obtain ⟨ℓ, hℓ2, hb, hi⟩ := lit l (canon_of_head l hc)
        refine ⟨ℓ :: K, φ, ?_, ha, ?_, hφ⟩
        · rw [sym_eq_of_fst s (by simpa using h2), hX]
          simp [encLit, hb, hℓ2]
        · simp only [clauseVal, List.any_cons, hi, hℓ2]
          simpa [clauseVal, Bool.or_assoc] using hv
    · rw [evalIdx] at h
      split_ifs at h with h1 h2 h3
      · obtain ⟨K, φ, hX, ha, hv, hφ⟩ := ih2 _ _ h
        refine ⟨[], K, φ, ?_, by simpa using h3, ha, by simpa using hv, hφ⟩
        rw [sym_eq_sL s h1 h2, hX]; simp
      · obtain ⟨l, K, φ, hX, hc, ha, hv, hφ⟩ := ih3 p (s :: I) cs all h
        have hs := sym_eq_of_fst s (by simpa using h2)
        refine ⟨s.2 :: l, K, φ, ?_, ?_, ha, ?_, hφ⟩
        · rw [hX]; conv_lhs => rw [hs]
          simp
        · rw [hs] at hc; simpa using hc
        · rw [hs] at hv; simpa using hv

/-- Leitura inversa de `syms` em listas de comprimento par. -/
def unsyms (l : List Sym) : List Bool := l.flatMap fun s => [s.1, s.2]

theorem unsyms_syms : ∀ x : List Bool, x.length % 2 = 0 → unsyms (syms x) = x
  | [] , _ => rfl
  | [a], h => by simp at h
  | a :: b :: r, h => by
    simp only [List.length_cons] at h
    simp [syms, unsyms] at *
    exact unsyms_syms r (by omega)

theorem syms_inj {x y : List Bool} (hx : x.length % 2 = 0) (hy : y.length % 2 = 0)
    (h : syms x = syms y) : x = y := by
  rw [← unsyms_syms x hx, ← unsyms_syms y hy, h]

/-- **Correção do verificador.** -/
theorem verif_par_sound (x c : Palavra) (h : verif (par x c) = true) :
    ∃ φ : CNF, x = codCNF φ ∧ Satisfaz (tau (syms c)) φ := by
  simp only [verif, dec_par, decC_par, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨φ, hX, -, hφ⟩ := (eval_sound (syms c) (syms x)).1 true h.2
  refine ⟨φ, syms_inj h.1 (codCNF_length_even φ) (by rw [hX, syms_codCNF]), ?_⟩
  exact (satisfaz_iff _ _).mpr hφ

/-! ### O certificado -/

/-- Segmento do certificado para a variável `i`: valor `τ i`, índice (bit mais significativo
primeiro) e fim `10`. -/
def codSeg (τ : ℕ → Bool) (i : ℕ) : List Bool :=
  simb (τ i) ++ i.bits.reverse.flatMap simb ++ [true, false]

/-- **O certificado**: um segmento por ocorrência de literal. -/
def cert (τ : ℕ → Bool) (φ : CNF) : List Bool := φ.flatten.flatMap fun ℓ => codSeg τ ℓ.1

/-- O segmento em símbolos. -/
def encSeg (τ : ℕ → Bool) (i : ℕ) : List Sym := (false, τ i) :: idxSym i ++ [sL]

theorem syms_codSeg (τ : ℕ → Bool) (i : ℕ) (r : List Bool) :
    syms (codSeg τ i ++ r) = encSeg τ i ++ syms r := by
  simp only [codSeg, simb, List.cons_append, List.nil_append, List.append_assoc]
  rw [syms_cons_cons, syms_flatMap_simb]
  simp [encSeg, idxSym, bitsSym, List.map_reverse, sL, syms]

theorem syms_cert (τ : ℕ → Bool) (φ : CNF) :
    syms (cert τ φ) = φ.flatten.flatMap fun ℓ => encSeg τ ℓ.1 := by
  unfold cert
  induction φ.flatten with
  | nil => simp [syms]
  | cons ℓ L ih =>
    simp only [List.flatMap_cons]
    rw [syms_codSeg, ih]

theorem seg_append (r : List Sym) :
    ∀ l : List Sym, (∀ s ∈ l, s.1 = false) → seg (l ++ sL :: r) = (l, r)
  | [], _ => by simp [seg]
  | s :: l, h => by
    have hs : s ≠ sL := by
      intro hs; have := h s (by simp); rw [hs] at this; simp [sL] at this
    simp only [List.cons_append, seg, hs, ↓reduceIte]
    rw [seg_append r l (fun t ht => h t (by simp [ht]))]

theorem idxSym_injective : Function.Injective idxSym := by
  intro m n h
  simp only [idxSym, bitsSym, List.reverse_inj] at h
  exact bits_injective (List.map_injective_iff.mpr (fun a b hab => by simpa using hab) h)

theorem lookup_encSegs (τ : ℕ → Bool) :
    ∀ (L : List Literal) (i : ℕ), i ∈ L.map Prod.fst →
      lookup (idxSym i) (L.flatMap fun ℓ => encSeg τ ℓ.1) = τ i
  | [], i, h => by simp at h
  | ℓ :: L, i, h => by
    have hform : (ℓ :: L).flatMap (fun ℓ => encSeg τ ℓ.1) =
        (false, τ ℓ.1) :: (idxSym ℓ.1 ++ sL :: L.flatMap fun ℓ => encSeg τ ℓ.1) := by
      simp [encSeg]
    have hseg : seg ((false, τ ℓ.1) :: (idxSym ℓ.1 ++ sL :: L.flatMap fun ℓ => encSeg τ ℓ.1)) =
        ((false, τ ℓ.1) :: idxSym ℓ.1, L.flatMap fun ℓ => encSeg τ ℓ.1) := by
      have := seg_append (L.flatMap fun ℓ => encSeg τ ℓ.1) ((false, τ ℓ.1) :: idxSym ℓ.1)
        (by intro s hs; simp only [List.mem_cons] at hs
            rcases hs with rfl | hs
            · rfl
            · simp only [idxSym, bitsSym, List.mem_reverse, List.mem_map] at hs
              obtain ⟨b, -, rfl⟩ := hs; rfl)
      simpa using this
    rw [hform, lookup, hseg]
    simp only [List.tail_cons, List.head?_cons, Option.map_some, Option.getD_some]
    by_cases hi : idxSym ℓ.1 = idxSym i
    · have he := idxSym_injective hi
      subst he
      simp
    · simp only [hi, ↓reduceIte]
      have hne : i ≠ ℓ.1 := fun he => hi (by rw [he])
      simp only [List.map_cons, List.mem_cons, hne, false_or] at h
      exact lookup_encSegs τ L i h

theorem codSeg_length (τ : ℕ → Bool) (ℓ : Literal) :
    (codSeg τ ℓ.1).length = (codLiteral ℓ).length := by
  simp [codSeg, codLiteral, simb, List.length_flatMap]

theorem cert_length (τ : ℕ → Bool) (φ : CNF) : (cert τ φ).length ≤ (codCNF φ).length := by
  unfold cert codCNF
  induction φ with
  | nil => simp
  | cons K φ ih =>
    simp only [List.flatten_cons, List.flatMap_append, List.length_append, List.flatMap_cons]
    have hK : (K.flatMap fun ℓ => codSeg τ ℓ.1).length ≤ (codClausula K).length := by
      unfold codClausula
      simp only [List.length_append, List.length_flatMap, codSeg_length]
      omega
    omega

/-- **SAT em termos do verificador**: `x ∈ SAT` ⟺ algum certificado de tamanho `≤ |x|` faz o
verificador aceitar `⟨x, c⟩`. -/
theorem sat_iff_verif (x : Palavra) :
    x ∈ SAT ↔ ∃ c : Palavra, c.length ≤ x.length ∧ verif (par x c) = true := by
  constructor
  · rintro ⟨φ, rfl, τ, hτ⟩
    refine ⟨cert τ φ, cert_length τ φ, ?_⟩
    rw [verif_codCNF, ← satisfaz_iff]
    intro K hK
    obtain ⟨ℓ, hℓ, hv⟩ := hτ K hK
    refine ⟨ℓ, hℓ, ?_⟩
    rw [tau, syms_cert, lookup_encSegs τ φ.flatten ℓ.1 (List.mem_map.mpr
      ⟨ℓ, List.mem_flatten.mpr ⟨K, hK, hℓ⟩, rfl⟩), hv]
  · rintro ⟨c, -, h⟩
    obtain ⟨φ, rfl, hφ⟩ := verif_par_sound x c h
    exact ⟨φ, rfl, _, hφ⟩

/-- **SAT ∈ NP, dado o verificador em tempo polinomial.** A máquina está em `ATK.SatNPMaquina`. -/
theorem sat_em_NP_de (M : TM2ComputableInPolyTime cod encodeBool verif) : SAT ∈ classeNP :=
  ⟨{y | verif y = true}, ⟨verif, fun _ => Iff.rfl, ⟨M⟩⟩, Polynomial.X, fun w => by
    simpa using sat_iff_verif w⟩

end ATK.SatNPSemantica

#print axioms ATK.SatNPSemantica.decC_par
#print axioms ATK.SatNPSemantica.seg_snd_length_le
#print axioms ATK.SatNPSemantica.seg_snd_length_lt
#print axioms ATK.SatNPSemantica.syms_cons_cons
#print axioms ATK.SatNPSemantica.syms_flatMap_simb
#print axioms ATK.SatNPSemantica.syms_codLiteral
#print axioms ATK.SatNPSemantica.syms_codClausula
#print axioms ATK.SatNPSemantica.syms_codCNF
#print axioms ATK.SatNPSemantica.codCNF_length_even
#print axioms ATK.SatNPSemantica.ofBits_bits
#print axioms ATK.SatNPSemantica.bits_injective
#print axioms ATK.SatNPSemantica.bits_canon
#print axioms ATK.SatNPSemantica.bits_ofBits
#print axioms ATK.SatNPSemantica.satisfaz_iff
#print axioms ATK.SatNPSemantica.evalStart_sC
#print axioms ATK.SatNPSemantica.evalIdx_bits
#print axioms ATK.SatNPSemantica.bitsSym_reverse_head
#print axioms ATK.SatNPSemantica.evalStart_encLit
#print axioms ATK.SatNPSemantica.evalStart_encClause
#print axioms ATK.SatNPSemantica.evalStart_encCNF
#print axioms ATK.SatNPSemantica.verif_codCNF
#print axioms ATK.SatNPSemantica.eval_all_false
#print axioms ATK.SatNPSemantica.sym_eq_of_fst
#print axioms ATK.SatNPSemantica.sym_eq_sL
#print axioms ATK.SatNPSemantica.canon_of_head
#print axioms ATK.SatNPSemantica.eval_sound
#print axioms ATK.SatNPSemantica.unsyms_syms
#print axioms ATK.SatNPSemantica.syms_inj
#print axioms ATK.SatNPSemantica.verif_par_sound
#print axioms ATK.SatNPSemantica.syms_codSeg
#print axioms ATK.SatNPSemantica.syms_cert
#print axioms ATK.SatNPSemantica.seg_append
#print axioms ATK.SatNPSemantica.idxSym_injective
#print axioms ATK.SatNPSemantica.lookup_encSegs
#print axioms ATK.SatNPSemantica.codSeg_length
#print axioms ATK.SatNPSemantica.cert_length
#print axioms ATK.SatNPSemantica.sat_iff_verif
#print axioms ATK.SatNPSemantica.sat_em_NP_de
