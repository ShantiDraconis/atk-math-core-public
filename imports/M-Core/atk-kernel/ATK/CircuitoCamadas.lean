import ATK.Shannon

/-!
# ATK — Circuitos em camadas (base para a ponte `P ⊆ P/poly`)

Ferramenta genérica sobre o modelo de circuitos de `ATK.Shannon` (lista sequencial de portas E,
OU, NÃO; cada porta acrescenta um fio):

* `Form ι`: fórmulas booleanas sobre variáveis em `ι`, com avaliação `eval` e custo `tam`;
* `comp`: compilação de uma fórmula em portas a partir do comprimento atual (`avalia_comp`);
* `bloco`: compila uma lista de fórmulas e copia os resultados para os últimos fios
  (`avalia_bloco`);
* `temCircuito_lista`: toda lista de portas dá um circuito do modelo de `Shannon` com o mesmo
  número de portas (referências fora do alcance leem `false`, então podem ser truncadas);
* **`temCircuito_camadas`**: se uma linha inicial é dada por fórmulas na entrada, cada linha
  seguinte por fórmulas na anterior e a saída por uma fórmula na última, a função resultante tem
  circuito com `custo(inicial) + T · custo(passo) + custo(saída)` portas.

É o esqueleto da simulação de máquinas de Turing por circuitos (Savage 1972).
-/

namespace ATK.CircuitoCamadas

open ATK.Shannon

/-- Fórmulas booleanas sobre variáveis em `ι`. -/
inductive Form (ι : Type*) where
  | var : ι → Form ι
  | tt : Form ι
  | ff : Form ι
  | e : Form ι → Form ι → Form ι
  | ou : Form ι → Form ι → Form ι
  | nao : Form ι → Form ι

namespace Form

variable {ι κ : Type*}

/-- Avaliação. -/
def eval (ρ : ι → Bool) : Form ι → Bool
  | var i => ρ i
  | tt => true
  | ff => false
  | e a b => a.eval ρ && b.eval ρ
  | ou a b => a.eval ρ || b.eval ρ
  | nao a => !a.eval ρ

/-- Número de portas da compilação. -/
def tam : Form ι → ℕ
  | var _ => 0
  | tt => 1
  | ff => 1
  | e a b => a.tam + b.tam + 1
  | ou a b => a.tam + b.tam + 1
  | nao a => a.tam + 1

/-- Disjunção de uma lista. -/
def ouL : List (Form ι) → Form ι
  | [] => ff
  | φ :: φs => ou φ (ouL φs)

/-- Conjunção de uma lista. -/
def eL : List (Form ι) → Form ι
  | [] => tt
  | φ :: φs => e φ (eL φs)

/-- Constante. -/
def const (b : Bool) : Form ι := if b then tt else ff

theorem eval_const (ρ : ι → Bool) (b : Bool) : (const b).eval ρ = b := by
  cases b <;> rfl

theorem tam_const (b : Bool) : (const b : Form ι).tam = 1 := by
  cases b <;> rfl

theorem eval_ouL (ρ : ι → Bool) :
    ∀ φs : List (Form ι), (ouL φs).eval ρ = true ↔ ∃ φ ∈ φs, φ.eval ρ = true
  | [] => by simp [ouL, eval]
  | φ :: φs => by
    simp only [ouL, eval, Bool.or_eq_true, eval_ouL ρ φs, List.mem_cons]
    constructor
    · rintro (h | ⟨ψ, hψ, h⟩)
      · exact ⟨φ, Or.inl rfl, h⟩
      · exact ⟨ψ, Or.inr hψ, h⟩
    · rintro ⟨ψ, rfl | hψ, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨ψ, hψ, h⟩

theorem eval_eL (ρ : ι → Bool) :
    ∀ φs : List (Form ι), (eL φs).eval ρ = true ↔ ∀ φ ∈ φs, φ.eval ρ = true
  | [] => by simp [eL, eval]
  | φ :: φs => by
    simp only [eL, eval, Bool.and_eq_true, eval_eL ρ φs, List.mem_cons]
    constructor
    · rintro ⟨h1, h2⟩ ψ (rfl | hψ)
      · exact h1
      · exact h2 ψ hψ
    · intro h
      exact ⟨h φ (Or.inl rfl), fun ψ hψ => h ψ (Or.inr hψ)⟩

theorem tam_ouL : ∀ φs : List (Form ι), (ouL φs).tam = (φs.map fun φ => φ.tam + 1).sum + 1
  | [] => rfl
  | φ :: φs => by
    simp only [ouL, tam, tam_ouL φs, List.map_cons, List.sum_cons]
    ring

theorem tam_eL : ∀ φs : List (Form ι), (eL φs).tam = (φs.map fun φ => φ.tam + 1).sum + 1
  | [] => rfl
  | φ :: φs => by
    simp only [eL, tam, tam_eL φs, List.map_cons, List.sum_cons]
    ring

end Form

open Form

/-- Uma porta: operação e dois fios (índices absolutos). -/
abbrev Porta := Op × ℕ × ℕ

/-- Compila `φ` a partir do comprimento atual `L`; a variável `i` está no fio `idx i`.
Devolve as portas e o fio do resultado. -/
def comp {ι : Type*} (idx : ι → ℕ) : ℕ → Form ι → List Porta × ℕ
  | _, .var i => ([], idx i)
  | L, .tt => ([(.nao, L, L)], L)
  | L, .ff => ([(.e, L, L)], L)
  | L, .e a b =>
    ((comp idx L a).1 ++ (comp idx (L + a.tam) b).1 ++
      [(.e, (comp idx L a).2, (comp idx (L + a.tam) b).2)], L + a.tam + b.tam)
  | L, .ou a b =>
    ((comp idx L a).1 ++ (comp idx (L + a.tam) b).1 ++
      [(.ou, (comp idx L a).2, (comp idx (L + a.tam) b).2)], L + a.tam + b.tam)
  | L, .nao a => ((comp idx L a).1 ++ [(.nao, (comp idx L a).2, (comp idx L a).2)], L + a.tam)

theorem avalia_append (G H : List Porta) (v : List Bool) :
    avalia (G ++ H) v = avalia H (avalia G v) := by
  simp [avalia, List.foldl_append]

theorem avalia_um (g : Porta) (v : List Bool) :
    avalia [g] v = v ++ [g.1.ap (v.getD g.2.1 false) (v.getD g.2.2 false)] := rfl

theorem avalia_nil (v : List Bool) : avalia [] v = v := rfl

theorem avalia_length : ∀ (G : List Porta) (v : List Bool), (avalia G v).length = v.length + G.length
  | [], v => by simp [avalia_nil]
  | g :: gs, v => by
    have e : g :: gs = [g] ++ gs := rfl
    rw [e, avalia_append, avalia_length gs, avalia_um]
    simp; ring

theorem getD_esq {u w : List Bool} {i : ℕ} (h : i < u.length) :
    (u ++ w).getD i false = u.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_fim (u : List Bool) : u.getD u.length false = false := by
  simp [List.getD_eq_getElem?_getD]

/-- **Semântica da compilação.** -/
theorem avalia_comp {ι : Type*} (idx : ι → ℕ) :
    ∀ (φ : Form ι) (v : List Bool), (∀ i, idx i < v.length) →
      ∃ w : List Bool, avalia (comp idx v.length φ).1 v = v ++ w ∧ w.length = φ.tam ∧
        (comp idx v.length φ).2 < v.length + φ.tam ∧
        (v ++ w).getD (comp idx v.length φ).2 false = φ.eval (fun i => v.getD (idx i) false)
  | .var i, v, h => ⟨[], by simp [comp, avalia_nil], rfl, by simpa [comp, tam] using h i,
      by simp [comp, eval]⟩
  | .tt, v, h => ⟨[true], by simp [comp, avalia_um, Op.ap, getD_fim], rfl, by simp [comp, tam],
      by simp [comp, eval, List.getD_eq_getElem?_getD]⟩
  | .ff, v, h => ⟨[false], by simp [comp, avalia_um, Op.ap, getD_fim], rfl, by simp [comp, tam],
      by simp [comp, eval, List.getD_eq_getElem?_getD]⟩
  | .e a b, v, h => by
    obtain ⟨wa, ha1, ha2, ha3, ha4⟩ := avalia_comp idx a v h
    have hlen : (v ++ wa).length = v.length + a.tam := by simp [ha2]
    obtain ⟨wb, hb1, hb2, hb3, hb4⟩ := avalia_comp idx b (v ++ wa) (fun i => by
      have := h i; rw [hlen]; omega)
    rw [hlen] at hb1 hb3 hb4
    have hρ : (fun i => (v ++ wa).getD (idx i) false) = fun i => v.getD (idx i) false :=
      funext fun i => getD_esq (h i)
    rw [hρ] at hb4
    have hra : (v ++ wa ++ wb).getD (comp idx v.length a).2 false = a.eval
        (fun i => v.getD (idx i) false) := by
      rw [getD_esq (by rw [hlen]; exact ha3), ha4]
    refine ⟨wa ++ wb ++ [a.eval (fun i => v.getD (idx i) false) &&
      b.eval (fun i => v.getD (idx i) false)], ?_, ?_, ?_, ?_⟩
    · simp only [comp]
      rw [avalia_append, avalia_append, ha1, hb1, avalia_um, hra, hb4]
      simp [Op.ap, List.append_assoc]
    · simp [ha2, hb2, tam]; try ring
    · simp only [comp, tam]; omega
    · simp only [comp, eval]
      have : v.length + a.tam + b.tam = (v ++ wa ++ wb).length := by simp [ha2, hb2]; ring
      rw [this, ← List.append_assoc, ← List.append_assoc]
      simp [List.getD_eq_getElem?_getD]
  | .ou a b, v, h => by
    obtain ⟨wa, ha1, ha2, ha3, ha4⟩ := avalia_comp idx a v h
    have hlen : (v ++ wa).length = v.length + a.tam := by simp [ha2]
    obtain ⟨wb, hb1, hb2, hb3, hb4⟩ := avalia_comp idx b (v ++ wa) (fun i => by
      have := h i; rw [hlen]; omega)
    rw [hlen] at hb1 hb3 hb4
    have hρ : (fun i => (v ++ wa).getD (idx i) false) = fun i => v.getD (idx i) false :=
      funext fun i => getD_esq (h i)
    rw [hρ] at hb4
    have hra : (v ++ wa ++ wb).getD (comp idx v.length a).2 false = a.eval
        (fun i => v.getD (idx i) false) := by
      rw [getD_esq (by rw [hlen]; exact ha3), ha4]
    refine ⟨wa ++ wb ++ [a.eval (fun i => v.getD (idx i) false) ||
      b.eval (fun i => v.getD (idx i) false)], ?_, ?_, ?_, ?_⟩
    · simp only [comp]
      rw [avalia_append, avalia_append, ha1, hb1, avalia_um, hra, hb4]
      simp [Op.ap, List.append_assoc]
    · simp [ha2, hb2, tam]; try ring
    · simp only [comp, tam]; omega
    · simp only [comp, eval]
      have : v.length + a.tam + b.tam = (v ++ wa ++ wb).length := by simp [ha2, hb2]; ring
      rw [this, ← List.append_assoc, ← List.append_assoc]
      simp [List.getD_eq_getElem?_getD]
  | .nao a, v, h => by
    obtain ⟨wa, ha1, ha2, ha3, ha4⟩ := avalia_comp idx a v h
    have hlen : (v ++ wa).length = v.length + a.tam := by simp [ha2]
    refine ⟨wa ++ [!a.eval (fun i => v.getD (idx i) false)], ?_, ?_, ?_, ?_⟩
    · simp only [comp]
      rw [avalia_append, ha1, avalia_um, ha4]
      simp [Op.ap, List.append_assoc]
    · simp [ha2, tam]
    · simp only [comp, tam]; omega
    · simp only [comp, eval]
      rw [← hlen, ← List.append_assoc]
      simp [List.getD_eq_getElem?_getD]

theorem comp_length {ι : Type*} (idx : ι → ℕ) :
    ∀ (L : ℕ) (φ : Form ι), (comp idx L φ).1.length = φ.tam
  | _, .var _ => rfl
  | _, .tt => rfl
  | _, .ff => rfl
  | L, .e a b => by
    simp [comp, tam, comp_length idx L a, comp_length idx (L + a.tam) b]; try omega
  | L, .ou a b => by
    simp [comp, tam, comp_length idx L a, comp_length idx (L + a.tam) b]; try omega
  | L, .nao a => by simp [comp, tam, comp_length idx L a]

/-! ## Blocos -/

/-- Compila uma lista de fórmulas em sequência. -/
def compL {ι : Type*} (idx : ι → ℕ) : ℕ → List (Form ι) → List Porta × List ℕ
  | _, [] => ([], [])
  | L, φ :: φs => ((comp idx L φ).1 ++ (compL idx (L + φ.tam) φs).1,
      (comp idx L φ).2 :: (compL idx (L + φ.tam) φs).2)

/-- Custo de um bloco. -/
def custo {ι : Type*} (φs : List (Form ι)) : ℕ := (φs.map Form.tam).sum + φs.length

/-- Bloco: compila e copia os resultados para os últimos fios. -/
def bloco {ι : Type*} (idx : ι → ℕ) (L : ℕ) (φs : List (Form ι)) : List Porta :=
  (compL idx L φs).1 ++ (compL idx L φs).2.map fun r => (Op.ou, r, r)

theorem avalia_copias :
    ∀ (rs : List ℕ) (u : List Bool), (∀ r ∈ rs, r < u.length) →
      avalia (rs.map fun r => (Op.ou, r, r)) u = u ++ rs.map fun r => u.getD r false
  | [], u, _ => by simp [avalia_nil]
  | r :: rs, u, h => by
    have h1 := h r (List.mem_cons_self ..)
    rw [List.map_cons, show (Op.ou, r, r) :: List.map (fun r => (Op.ou, r, r)) rs =
      [(Op.ou, r, r)] ++ List.map (fun r => (Op.ou, r, r)) rs from rfl, avalia_append, avalia_um]
    rw [avalia_copias rs _ (fun r' hr' => by
      have := h r' (List.mem_cons_of_mem _ hr'); simp; omega)]
    simp only [Op.ap, Bool.or_self, List.map_cons, List.append_assoc, List.cons_append,
      List.nil_append]
    congr 2
    refine List.map_congr_left fun r' hr' => ?_
    exact getD_esq (h r' (List.mem_cons_of_mem _ hr'))

theorem avalia_compL {ι : Type*} (idx : ι → ℕ) :
    ∀ (φs : List (Form ι)) (v : List Bool), (∀ i, idx i < v.length) →
      ∃ w : List Bool, avalia (compL idx v.length φs).1 v = v ++ w ∧
        w.length = (φs.map Form.tam).sum ∧
        (∀ r ∈ (compL idx v.length φs).2, r < (v ++ w).length) ∧
        (compL idx v.length φs).2.map (fun r => (v ++ w).getD r false) =
          φs.map fun φ => φ.eval (fun i => v.getD (idx i) false)
  | [], v, _ => ⟨[], by simp [compL, avalia_nil], rfl, by simp [compL], by simp [compL]⟩
  | φ :: φs, v, h => by
    obtain ⟨w1, h1, h2, h3, h4⟩ := avalia_comp idx φ v h
    have hlen : (v ++ w1).length = v.length + φ.tam := by simp [h2]
    obtain ⟨w2, g1, g2, g3, g4⟩ := avalia_compL idx φs (v ++ w1) (fun i => by
      have := h i; rw [hlen]; omega)
    rw [hlen] at g1 g3 g4
    have hρ : (fun i => (v ++ w1).getD (idx i) false) = fun i => v.getD (idx i) false :=
      funext fun i => getD_esq (h i)
    rw [hρ] at g4
    refine ⟨w1 ++ w2, ?_, ?_, ?_, ?_⟩
    · simp only [compL]
      rw [avalia_append, h1, g1, List.append_assoc]
    · simp [h2, g2]; try ring
    · intro r hr
      simp only [compL, List.mem_cons] at hr
      rcases hr with rfl | hr
      · simp; omega
      · have := g3 r hr; simpa [List.append_assoc] using this
    · simp only [compL, List.map_cons]
      rw [← List.append_assoc, getD_esq (by simp; omega), h4]
      congr 1
      try (rw [← g4]; simp [List.append_assoc])

/-- **Semântica do bloco**: os últimos fios são os valores das fórmulas. -/
theorem avalia_bloco {ι : Type*} (idx : ι → ℕ) (φs : List (Form ι)) (v : List Bool)
    (h : ∀ i, idx i < v.length) :
    ∃ w : List Bool, avalia (bloco idx v.length φs) v =
      v ++ w ++ φs.map (fun φ => φ.eval (fun i => v.getD (idx i) false)) ∧
      w.length = (φs.map Form.tam).sum := by
  obtain ⟨w, h1, h2, h3, h4⟩ := avalia_compL idx φs v h
  refine ⟨w, ?_, h2⟩
  rw [bloco, avalia_append, h1, avalia_copias _ _ h3, h4]

theorem compL_length {ι : Type*} (idx : ι → ℕ) :
    ∀ (L : ℕ) (φs : List (Form ι)), (compL idx L φs).1.length = (φs.map Form.tam).sum ∧
      (compL idx L φs).2.length = φs.length
  | _, [] => by simp [compL]
  | L, φ :: φs => by
    have := compL_length idx (L + φ.tam) φs
    simp [compL, comp_length, this.1, this.2]

theorem bloco_length {ι : Type*} (idx : ι → ℕ) (L : ℕ) (φs : List (Form ι)) :
    (bloco idx L φs).length = custo φs := by
  simp [bloco, custo, (compL_length idx L φs).1, (compL_length idx L φs).2]

/-! ## Camadas -/

/-- A linha atual nos últimos `B` fios. -/
def idxLinha (B L : ℕ) (b : Fin B) : ℕ := L - B + b

/-- `T` blocos de passo. -/
def iter (B : ℕ) (pas : List (Form (Fin B))) : ℕ → ℕ → List Porta
  | 0, _ => []
  | t + 1, L => bloco (idxLinha B L) L pas ++ iter B pas t (L + custo pas)

theorem iter_length (B : ℕ) (pas : List (Form (Fin B))) :
    ∀ (t L : ℕ), (iter B pas t L).length = t * custo pas
  | 0, _ => by simp [iter]
  | t + 1, L => by
    rw [iter, List.length_append, bloco_length, iter_length B pas t]; ring

theorem getD_linha {u : List Bool} {B : ℕ} (row : Fin B → Bool) (b : Fin B) :
    (u ++ List.ofFn row).getD ((u ++ List.ofFn row).length - B + b) false = row b := by
  simp only [List.length_append, List.length_ofFn, Nat.add_sub_cancel, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem?_ofFn]
  simp

theorem avalia_iter {B : ℕ} (pas : Fin B → Form (Fin B)) :
    ∀ (t : ℕ) (u : List Bool) (row : Fin B → Bool),
      ∃ w : List Bool, avalia (iter B (List.ofFn pas) t (u ++ List.ofFn row).length)
        (u ++ List.ofFn row) =
        w ++ List.ofFn ((fun r b => (pas b).eval r)^[t] row)
  | 0, u, row => ⟨u, by simp [iter, avalia_nil]⟩
  | t + 1, u, row => by
    have hidx : ∀ b, idxLinha B (u ++ List.ofFn row).length b < (u ++ List.ofFn row).length := by
      intro b; simp [idxLinha]; try omega
    obtain ⟨w, h1, h2⟩ := avalia_bloco _ (List.ofFn pas) _ hidx
    have hrow : (fun i => (u ++ List.ofFn row).getD (idxLinha B (u ++ List.ofFn row).length i)
        false) = row := funext fun b => by
      simp only [idxLinha]; exact getD_linha row b
    rw [hrow] at h1
    have hmap : (List.ofFn pas).map (fun φ => φ.eval row) =
        List.ofFn (fun b => (pas b).eval row) := by simp [List.map_ofFn, Function.comp_def]
    rw [hmap] at h1
    have hL : (u ++ List.ofFn row).length + custo (List.ofFn pas) =
        (u ++ List.ofFn row ++ w ++ List.ofFn (fun b => (pas b).eval row)).length := by
      simp [custo, h2, List.map_ofFn]; try ring
    obtain ⟨w', h'⟩ := avalia_iter pas t (u ++ List.ofFn row ++ w)
      (fun b => (pas b).eval row)
    refine ⟨w', ?_⟩
    rw [iter, avalia_append, h1, hL, h']
    congr 2
    try rw [Function.iterate_succ_apply]

/-! ## Do gabarito ao circuito de `Shannon` -/

/-- Truncamento das referências (fios fora do alcance leem `false`). -/
def trunca : ℕ → List Porta → List Porta
  | _, [] => []
  | L, g :: gs => (g.1, min g.2.1 L, min g.2.2 L) :: trunca (L + 1) gs

theorem getD_min (v : List Bool) (r : ℕ) :
    v.getD (min r v.length) false = v.getD r false := by
  rcases le_or_gt v.length r with h | h
  · rw [min_eq_right h, getD_fim]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  · rw [min_eq_left h.le]

theorem avalia_trunca :
    ∀ (G : List Porta) (v : List Bool), avalia (trunca v.length G) v = avalia G v
  | [], v => rfl
  | g :: gs, v => by
    have e1 : trunca v.length (g :: gs) = [(g.1, min g.2.1 v.length, min g.2.2 v.length)] ++
        trunca (v.length + 1) gs := rfl
    have e2 : g :: gs = [g] ++ gs := rfl
    rw [e1, e2, avalia_append, avalia_append, avalia_um, avalia_um]
    simp only [getD_min]
    have := avalia_trunca gs (v ++ [g.1.ap (v.getD g.2.1 false) (v.getD g.2.2 false)])
    simpa using this

theorem trunca_length : ∀ (L : ℕ) (G : List Porta), (trunca L G).length = G.length
  | _, [] => rfl
  | L, _ :: gs => by simp [trunca, trunca_length (L + 1) gs]

theorem trunca_getElem :
    ∀ (L : ℕ) (G : List Porta) (j : ℕ) (hj : j < G.length),
      (trunca L G)[j]'(by rw [trunca_length]; exact hj) =
        (G[j].1, min G[j].2.1 (L + j), min G[j].2.2 (L + j))
  | L, g :: gs, 0, _ => by simp [trunca]
  | L, g :: gs, j + 1, hj => by
    simp only [trunca, List.getElem_cons_succ]
    rw [trunca_getElem (L + 1) gs j (by simpa using hj)]
    simp [Nat.add_assoc, Nat.add_comm 1 j]

/-- **Toda lista de portas é um circuito** com o mesmo número de portas. -/
theorem temCircuito_lista {n : ℕ} (G : List Porta) (f : (Fin n → Bool) → Bool)
    (hf : ∀ x, (avalia G (List.ofFn x)).getLastD false = f x) : TemCircuito f G.length := by
  refine ⟨G.length, le_rfl, fun j => (G[j].1,
    ⟨min G[j].2.1 (n + j), by have := j.2; omega⟩,
    ⟨min G[j].2.2 (n + j), by have := j.2; omega⟩), ?_⟩
  funext x
  rw [Circuito.computa, ← hf x]
  congr 1
  have hl : (List.ofFn x).length = n := List.length_ofFn
  rw [← avalia_trunca G (List.ofFn x), hl]
  congr 1
  apply List.ext_getElem
  · simp [trunca_length]
  · intro j h1 h2
    simp only [List.getElem_ofFn]
    rw [trunca_getElem n G j (by simpa using h1)]
    rfl

/-- O circuito em camadas. -/
def circuito (n B T : ℕ) (ini : Fin B → Form (Fin n)) (pas : Fin B → Form (Fin B))
    (sai : Form (Fin B)) : List Porta :=
  bloco (fun i : Fin n => (i : ℕ)) n (List.ofFn ini) ++
    iter B (List.ofFn pas) T (n + custo (List.ofFn ini)) ++
    bloco (idxLinha B (n + custo (List.ofFn ini) + T * custo (List.ofFn pas)))
      (n + custo (List.ofFn ini) + T * custo (List.ofFn pas)) [sai]

/-- **Circuitos em camadas**: linha inicial por fórmulas na entrada, `T` passos por fórmulas na
linha anterior, saída por uma fórmula na última linha. -/
theorem temCircuito_camadas {n B T : ℕ} (ini : Fin B → Form (Fin n))
    (pas : Fin B → Form (Fin B)) (sai : Form (Fin B)) :
    TemCircuito (fun x => sai.eval ((fun r b => (pas b).eval r)^[T]
        (fun b => (ini b).eval x)))
      (custo (List.ofFn ini) + T * custo (List.ofFn pas) + (sai.tam + 1)) := by
  have hlen : (circuito n B T ini pas sai).length =
      custo (List.ofFn ini) + T * custo (List.ofFn pas) + (sai.tam + 1) := by
    simp [circuito, bloco_length, iter_length, custo]; try ring
  rw [← hlen]
  refine temCircuito_lista _ _ fun x => ?_
  have hx : (List.ofFn x).length = n := List.length_ofFn
  -- bloco inicial
  obtain ⟨w0, h0, h0'⟩ := avalia_bloco (fun i : Fin n => (i : ℕ)) (List.ofFn ini) (List.ofFn x)
    (fun i => by rw [hx]; exact i.2)
  have hρ0 : (fun i : Fin n => (List.ofFn x).getD (i : ℕ) false) = x := funext fun i => by
    simp [List.getD_eq_getElem?_getD]
  rw [hρ0, hx] at h0
  have hm0 : (List.ofFn ini).map (fun φ => φ.eval x) = List.ofFn (fun b => (ini b).eval x) := by
    simp [List.map_ofFn, Function.comp_def]
  rw [hm0] at h0
  have hL1 : n + custo (List.ofFn ini) =
      (List.ofFn x ++ w0 ++ List.ofFn (fun b => (ini b).eval x)).length := by
    simp [custo, h0', hx, List.map_ofFn]; try ring
  obtain ⟨w1, h1⟩ := avalia_iter pas T (List.ofFn x ++ w0) (fun b => (ini b).eval x)
  set row := (fun r b => (pas b).eval r)^[T] (fun b => (ini b).eval x) with hrow
  have hL2 : n + custo (List.ofFn ini) + T * custo (List.ofFn pas) =
      (w1 ++ List.ofFn row).length := by
    have := congrArg List.length h1
    rw [avalia_length, iter_length] at this
    rw [← this, ← hL1]
    try simp [List.append_assoc]
  have hidx : ∀ b, idxLinha B (w1 ++ List.ofFn row).length b < (w1 ++ List.ofFn row).length := by
    intro b; simp [idxLinha]; try omega
  obtain ⟨w2, h2, -⟩ := avalia_bloco _ [sai] _ hidx
  have hρ2 : (fun i => (w1 ++ List.ofFn row).getD (idxLinha B (w1 ++ List.ofFn row).length i)
      false) = row := funext fun b => by simp only [idxLinha]; exact getD_linha row b
  rw [hρ2] at h2
  rw [circuito, avalia_append, avalia_append, h0, hL2, hL1, h1, h2]
  simp

end ATK.CircuitoCamadas

#print axioms ATK.CircuitoCamadas.Form.eval_const
#print axioms ATK.CircuitoCamadas.Form.tam_const
#print axioms ATK.CircuitoCamadas.Form.eval_ouL
#print axioms ATK.CircuitoCamadas.Form.eval_eL
#print axioms ATK.CircuitoCamadas.Form.tam_ouL
#print axioms ATK.CircuitoCamadas.Form.tam_eL
#print axioms ATK.CircuitoCamadas.avalia_append
#print axioms ATK.CircuitoCamadas.avalia_um
#print axioms ATK.CircuitoCamadas.avalia_nil
#print axioms ATK.CircuitoCamadas.avalia_length
#print axioms ATK.CircuitoCamadas.getD_esq
#print axioms ATK.CircuitoCamadas.getD_fim
#print axioms ATK.CircuitoCamadas.avalia_comp
#print axioms ATK.CircuitoCamadas.comp_length
#print axioms ATK.CircuitoCamadas.avalia_copias
#print axioms ATK.CircuitoCamadas.avalia_compL
#print axioms ATK.CircuitoCamadas.avalia_bloco
#print axioms ATK.CircuitoCamadas.compL_length
#print axioms ATK.CircuitoCamadas.bloco_length
#print axioms ATK.CircuitoCamadas.iter_length
#print axioms ATK.CircuitoCamadas.getD_linha
#print axioms ATK.CircuitoCamadas.avalia_iter
#print axioms ATK.CircuitoCamadas.getD_min
#print axioms ATK.CircuitoCamadas.avalia_trunca
#print axioms ATK.CircuitoCamadas.trunca_length
#print axioms ATK.CircuitoCamadas.trunca_getElem
#print axioms ATK.CircuitoCamadas.temCircuito_lista
#print axioms ATK.CircuitoCamadas.temCircuito_camadas
