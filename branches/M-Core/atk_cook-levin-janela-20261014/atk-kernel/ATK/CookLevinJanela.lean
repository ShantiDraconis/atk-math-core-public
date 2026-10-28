import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Finset.Lattice.Fold

/-!
# ATK — Cook–Levin, marco CL1: um passo de máquina de pilhas é local (a janela)

Para a outra metade da ponte B4 (`∀ L ∈ NP, L ≤p SAT`), a execução de um verificador `FinTM2`
precisa virar uma fórmula CNF (o *tableau*). O primeiro fato necessário é que **um passo só lê e
só altera o topo das pilhas**, até uma profundidade fixa que depende só da instrução:

* `prof q`: o número de leituras (`pop`/`peek`) da instrução `q` no pior ramo;
* **`stepAux_janela`**: `stepAux q v S` é o resultado de `stepAux q v` sobre as janelas
  `take (prof q)` das pilhas, com o resto `drop (prof q)` de cada pilha intacto embaixo;
* `stepAux_concorda`: duas configurações com as mesmas janelas dão o mesmo rótulo, o mesmo estado e
  as mesmas janelas novas.

Com isso o passo vira uma tabela finita: (rótulo, estado, janelas) ↦ (rótulo, estado, janelas
novas), e o resto das pilhas é copiado. É o que permite escrever o passo com cláusulas de tamanho
fixo no tableau (marco CL2).

Nada aqui prova Cook–Levin; é a primeira peça. **CLOSED_MATH continua false.**
-/

namespace ATK.CookLevinJanela

open Turing Function

variable {K : Type*} [DecidableEq K] {Γ : K → Type*} {Λ : Type*} {σ : Type*}

/-- Profundidade de leitura de uma instrução: `pop`/`peek` no pior ramo. -/
def prof : Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => prof q
  | .peek _ _ q => prof q + 1
  | .pop _ _ q => prof q + 1
  | .load _ q => prof q
  | .branch _ q₁ q₂ => max (prof q₁) (prof q₂)
  | .goto _ => 0
  | .halt => 0

/-- As janelas de profundidade `d` das pilhas. -/
def jan (d : ℕ) (S : ∀ k, List (Γ k)) : ∀ k, List (Γ k) := fun k => (S k).take d

theorem take_cons_succ {α : Type*} (a : α) (l : List α) (d : ℕ) :
    (a :: l).take (d + 1) = a :: l.take d := rfl

theorem take_of_take {α : Type*} {l l' : List α} {n m : ℕ} (h : l.take m = l'.take m)
    (hnm : n ≤ m) : l.take n = l'.take n := by
  have := congrArg (List.take n) h
  simpa [List.take_take, Nat.min_eq_left hnm] using this

theorem head_eq {α : Type*} {l l' : List α} (h : l.take 1 = l'.take 1) : l.head? = l'.head? := by
  cases l <;> cases l' <;> simp_all

theorem tail_take_succ {α : Type*} (l : List α) (n : ℕ) : l.tail.take n = (l.take (n + 1)).tail := by
  cases l <;> simp

theorem drop_tail {α : Type*} (l : List α) (n : ℕ) : l.tail.drop n = l.drop (n + 1) := by
  cases l <;> simp

/-- Lema auxiliar de listas: `drop n l = drop n (take d l) ++ drop d l` para `n ≤ d`. -/
theorem drop_eq_drop_take_append {α : Type*} (l : List α) {n d : ℕ} (h : n ≤ d) :
    l.drop n = (l.take d).drop n ++ l.drop d := by
  rw [List.drop_take]
  conv_lhs => rw [← List.take_append_drop (d - n) (l.drop n)]
  rw [List.drop_drop]
  congr 2
  omega

/-- **Localidade, forma fraca.** Se as pilhas concordam até a profundidade `prof q`, o passo dá o
mesmo rótulo e o mesmo estado, e cada pilha nova é um mesmo prefixo `P` seguido da pilha antiga sem
os seus `n ≤ prof q` primeiros símbolos. -/
theorem stepAux_concorda : ∀ (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (S S' : ∀ k, List (Γ k)),
    (∀ k, (S k).take (prof q) = (S' k).take (prof q)) →
    (TM2.stepAux q v S).l = (TM2.stepAux q v S').l ∧
    (TM2.stepAux q v S).var = (TM2.stepAux q v S').var ∧
    ∀ k, ∃ (P : List (Γ k)) (n : ℕ), n ≤ prof q ∧
      (TM2.stepAux q v S).stk k = P ++ (S k).drop n ∧
      (TM2.stepAux q v S').stk k = P ++ (S' k).drop n
  | .push k f q, v, S, S', h => by
    have h1 : ∀ j, (update S k (f v :: S k) j).take (prof q) =
        (update S' k (f v :: S' k) j).take (prof q) := by
      intro j
      by_cases hj : j = k
      · subst hj
        simp only [update_self]
        have hj := h j
        simp only [prof] at hj
        cases hp : prof q with
        | zero => simp
        | succ d =>
          rw [take_cons_succ, take_cons_succ, take_of_take hj (n := d) (by omega)]
      · simp only [update_of_ne hj]; exact h j
    obtain ⟨hl, hv, hs⟩ := stepAux_concorda q v _ _ h1
    simp only [TM2.stepAux]
    refine ⟨hl, hv, fun j => ?_⟩
    obtain ⟨P, n, hn, e1, e2⟩ := hs j
    by_cases hj : j = k
    · subst hj
      simp only [update_self] at e1 e2
      cases n with
      | zero =>
        exact ⟨P ++ [f v], 0, Nat.zero_le _, by simpa using e1, by simpa using e2⟩
      | succ n =>
        exact ⟨P, n, by simp only [prof]; omega, by simpa using e1, by simpa using e2⟩
    · simp only [update_of_ne hj] at e1 e2
      exact ⟨P, n, by simpa [prof] using hn, e1, e2⟩
  | .peek k f q, v, S, S', h => by
    have h1 : ∀ j, (S j).take (prof q) = (S' j).take (prof q) := fun j =>
      take_of_take (h j) (by simp [prof])
    have hhead : (S k).head? = (S' k).head? := head_eq (take_of_take (h k) (by simp [prof]))
    obtain ⟨hl, hv, hs⟩ := stepAux_concorda q (f v (S k).head?) S S' h1
    simp only [TM2.stepAux]
    rw [← hhead]
    refine ⟨hl, hv, fun j => ?_⟩
    obtain ⟨P, n, hn, e1, e2⟩ := hs j
    exact ⟨P, n, by simp only [prof]; omega, e1, e2⟩
  | .pop k f q, v, S, S', h => by
    have hhead : (S k).head? = (S' k).head? := head_eq (take_of_take (h k) (by simp [prof]))
    have h1 : ∀ j, (update S k (S k).tail j).take (prof q) =
        (update S' k (S' k).tail j).take (prof q) := by
      intro j
      by_cases hj : j = k
      · subst hj
        simp only [update_self, tail_take_succ]
        have hj := h j
        simp only [prof] at hj
        rw [hj]
      · simp only [update_of_ne hj]; exact take_of_take (h j) (by simp [prof])
    obtain ⟨hl, hv, hs⟩ := stepAux_concorda q (f v (S k).head?) _ _ h1
    simp only [TM2.stepAux]
    rw [← hhead]
    refine ⟨hl, hv, fun j => ?_⟩
    obtain ⟨P, n, hn, e1, e2⟩ := hs j
    by_cases hj : j = k
    · subst hj
      simp only [update_self, drop_tail] at e1 e2
      exact ⟨P, n + 1, by simp only [prof]; omega, e1, e2⟩
    · simp only [update_of_ne hj] at e1 e2
      exact ⟨P, n, by simp only [prof]; omega, e1, e2⟩
  | .load a q, v, S, S', h => by
    obtain ⟨hl, hv, hs⟩ := stepAux_concorda q (a v) S S' (fun k => by simpa [prof] using h k)
    simp only [TM2.stepAux]
    exact ⟨hl, hv, fun j => by simpa [prof] using hs j⟩
  | .branch f q₁ q₂, v, S, S', h => by
    simp only [TM2.stepAux]
    cases hf : f v
    · obtain ⟨hl, hv, hs⟩ := stepAux_concorda q₂ v S S' fun j =>
        take_of_take (h j) (by simp [prof])
      refine ⟨by simpa using hl, by simpa using hv, fun j => ?_⟩
      obtain ⟨P, n, hn, e1, e2⟩ := hs j
      exact ⟨P, n, by simp only [prof]; omega, by simpa using e1, by simpa using e2⟩
    · obtain ⟨hl, hv, hs⟩ := stepAux_concorda q₁ v S S' fun j =>
        take_of_take (h j) (by simp [prof])
      refine ⟨by simpa using hl, by simpa using hv, fun j => ?_⟩
      obtain ⟨P, n, hn, e1, e2⟩ := hs j
      exact ⟨P, n, by simp only [prof]; omega, by simpa using e1, by simpa using e2⟩
  | .goto f, v, S, S', _ => ⟨rfl, rfl, fun k => ⟨[], 0, le_refl _, by simp [TM2.stepAux],
      by simp [TM2.stepAux]⟩⟩
  | .halt, v, S, S', _ => ⟨rfl, rfl, fun k => ⟨[], 0, le_refl _, by simp [TM2.stepAux],
      by simp [TM2.stepAux]⟩⟩

/-- **A janela, profundidade qualquer.** Para `d ≥ prof q`, um passo é o passo sobre as janelas
`take d` das pilhas, com o resto `drop d` de cada pilha intacto embaixo. -/
theorem stepAux_janela_de (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) {d : ℕ}
    (hd : prof q ≤ d) :
    TM2.stepAux q v S =
      ⟨(TM2.stepAux q v (jan d S)).l, (TM2.stepAux q v (jan d S)).var,
        fun k => (TM2.stepAux q v (jan d S)).stk k ++ (S k).drop d⟩ := by
  obtain ⟨hl, hv, hs⟩ := stepAux_concorda q v S (jan d S) (fun k => by
    simp [jan, List.take_take, Nat.min_eq_left hd])
  rcases hstep : TM2.stepAux q v S with ⟨l, var, stk⟩
  rw [hstep] at hl hv hs
  simp only at hl hv
  congr 1
  funext k
  obtain ⟨P, n, hn, e1, e2⟩ := hs k
  simp only at e1
  rw [e1, e2, List.append_assoc]
  dsimp only [jan]
  rw [← drop_eq_drop_take_append (S k) (le_trans hn hd)]

/-- **A janela.** Um passo é o passo sobre as janelas `take (prof q)` das pilhas, com o resto de
cada pilha (`drop (prof q)`) intacto embaixo. -/
theorem stepAux_janela (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    TM2.stepAux q v S =
      ⟨(TM2.stepAux q v (jan (prof q) S)).l, (TM2.stepAux q v (jan (prof q) S)).var,
        fun k => (TM2.stepAux q v (jan (prof q) S)).stk k ++ (S k).drop (prof q)⟩ :=
  stepAux_janela_de q v S le_rfl

/-- Profundidade uniforme de um programa com rótulos finitos. -/
def profMax [Fintype Λ] (M : Λ → Turing.TM2.Stmt Γ Λ σ) : ℕ :=
  Finset.univ.sup fun l => prof (M l)

omit [DecidableEq K] in
theorem prof_le_profMax [Fintype Λ] (M : Λ → Turing.TM2.Stmt Γ Λ σ) (l : Λ) :
    prof (M l) ≤ profMax M :=
  Finset.le_sup (f := fun l => prof (M l)) (Finset.mem_univ l)

/-- **A janela da máquina.** Para um programa com rótulos finitos há uma profundidade `D` única
(`profMax M`) tal que cada passo de `TM2.step M` é determinado pelo rótulo, pelo estado e pelas
janelas de profundidade `D`, e copia o resto das pilhas. -/
theorem step_janela [Fintype Λ] (M : Λ → Turing.TM2.Stmt Γ Λ σ) (l : Λ) (v : σ)
    (S : ∀ k, List (Γ k)) :
    TM2.step M ⟨some l, v, S⟩ =
      some ⟨(TM2.stepAux (M l) v (jan (profMax M) S)).l,
        (TM2.stepAux (M l) v (jan (profMax M) S)).var,
        fun k => (TM2.stepAux (M l) v (jan (profMax M) S)).stk k ++ (S k).drop (profMax M)⟩ := by
  simp only [TM2.step]
  rw [stepAux_janela_de (M l) v S (prof_le_profMax M l)]

/-- A configuração parada não dá passo. -/
theorem step_parada (M : Λ → Turing.TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    TM2.step M ⟨none, v, S⟩ = none := rfl

end ATK.CookLevinJanela

#print axioms ATK.CookLevinJanela.prof
#print axioms ATK.CookLevinJanela.jan
#print axioms ATK.CookLevinJanela.take_cons_succ
#print axioms ATK.CookLevinJanela.take_of_take
#print axioms ATK.CookLevinJanela.head_eq
#print axioms ATK.CookLevinJanela.tail_take_succ
#print axioms ATK.CookLevinJanela.drop_tail
#print axioms ATK.CookLevinJanela.drop_eq_drop_take_append
#print axioms ATK.CookLevinJanela.stepAux_concorda
#print axioms ATK.CookLevinJanela.stepAux_janela_de
#print axioms ATK.CookLevinJanela.stepAux_janela
#print axioms ATK.CookLevinJanela.profMax
#print axioms ATK.CookLevinJanela.prof_le_profMax
#print axioms ATK.CookLevinJanela.step_janela
#print axioms ATK.CookLevinJanela.step_parada
