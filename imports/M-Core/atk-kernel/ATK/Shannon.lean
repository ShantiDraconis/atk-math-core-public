import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# ATK — P vs NP: o teorema de contagem de Shannon (funções booleanas difíceis existem)

Modelo: circuitos booleanos como programas lineares — `s` portas `∧`, `∨`, `¬`, cada uma lendo dois
fios anteriores (entradas ou portas já calculadas); a saída é o último fio.

* `card_circuito`: há exatamente `(3(n+s)²)^s` descrições de circuitos com `n` entradas e `s` portas;
* `existe_funcao_dificil`: se `(s+1)(3(n+s)²+1)^s < 2^(2^n)`, alguma função de `n` bits **não** tem
  circuito com `≤ s` portas;
* `shannon`: para `n ≥ 4`, existe função de `n` bits sem circuito com `≤ 2^n/(8n)` portas
  (complexidade **exponencial**);
* `familia_fora_de_Ppoly`: existe uma família `fₙ` que, para todo `k`, eventualmente não tem circuito
  com `≤ n^k` portas — uma família fora de `P/poly`.

A lacuna O4 (`P ≠ NP`) fica isolada com precisão: Shannon garante que famílias fora de `P/poly`
existem (quase todas as funções o são), mas a prova é por contagem e não exibe nenhuma. Basta exibir
**uma** família em `NP` fora de `P/poly` (o lane já prova `NP ⊄ P/poly ⇒ P ≠ NP` no seu modelo:
`ATK.PvsNP.p_ne_np_of_np_not_subset_ppoly`). As barreiras conhecidas (relativização, provas naturais,
algebrização) dizem que essa função não pode ser obtida por contagem nem por diagonalização simples.
-/

open Filter

namespace ATK.Shannon

/-- Portas: E, OU, NÃO (NÃO ignora a segunda entrada). -/
inductive Op
  | e
  | ou
  | nao
  deriving DecidableEq

instance : Fintype Op where
  elems := {Op.e, Op.ou, Op.nao}
  complete := fun x => by cases x <;> simp

theorem card_op : Fintype.card Op = 3 := rfl

def Op.ap : Op → Bool → Bool → Bool
  | e, a, b => a && b
  | ou, a, b => a || b
  | nao, a, _ => !a

/-- Circuito com `n` entradas e `s` portas: a porta `i` é `(op, fio₁, fio₂)`. -/
abbrev Circuito (n s : ℕ) := Fin s → Op × Fin (n + s) × Fin (n + s)

/-- Avaliação sequencial: cada porta acrescenta um fio (referência inexistente lê `false`). -/
def avalia (G : List (Op × ℕ × ℕ)) (v0 : List Bool) : List Bool :=
  G.foldl (fun v g => v ++ [g.1.ap (v.getD g.2.1 false) (v.getD g.2.2 false)]) v0

/-- A função calculada: o último fio. -/
def Circuito.computa {n s : ℕ} (C : Circuito n s) (x : Fin n → Bool) : Bool :=
  (avalia (List.ofFn fun i => ((C i).1, ((C i).2.1 : ℕ), ((C i).2.2 : ℕ))) (List.ofFn x)).getLastD
    false

/-- `f` tem circuito com no máximo `s` portas. -/
def TemCircuito {n : ℕ} (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ s' ≤ s, ∃ C : Circuito n s', C.computa = f

theorem temCircuito_mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s t : ℕ} (h : s ≤ t)
    (hf : TemCircuito f s) : TemCircuito f t := by
  obtain ⟨s', hs', C, hC⟩ := hf
  exact ⟨s', le_trans hs' h, C, hC⟩

theorem card_circuito (n s : ℕ) : Fintype.card (Circuito n s) = (3 * (n + s) ^ 2) ^ s := by
  simp only [Circuito, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, card_op]
  ring

theorem card_funcoes (n : ℕ) : Fintype.card ((Fin n → Bool) → Bool) = 2 ^ (2 ^ n) := by
  simp [Fintype.card_bool, Fintype.card_fin]

/-- **Contagem de Shannon.** -/
theorem existe_funcao_dificil {n s : ℕ} (h : (s + 1) * (3 * (n + s) ^ 2 + 1) ^ s < 2 ^ (2 ^ n)) :
    ∃ f : (Fin n → Bool) → Bool, ¬ TemCircuito f s := by
  by_contra hall
  have hall' : ∀ f : (Fin n → Bool) → Bool, TemCircuito f s := fun f => by
    by_contra hf; exact hall ⟨f, hf⟩
  let F : (Σ i : Fin (s + 1), Circuito n i) → ((Fin n → Bool) → Bool) := fun p => p.2.computa
  have hsurj : Function.Surjective F := by
    intro f
    obtain ⟨s', hs', C, hC⟩ := hall' f
    exact ⟨⟨⟨s', by omega⟩, C⟩, hC⟩
  have hcard := Fintype.card_le_of_surjective F hsurj
  rw [Fintype.card_sigma, card_funcoes] at hcard
  simp only [card_circuito] at hcard
  have hb : ∀ i : Fin (s + 1), (3 * (n + (i : ℕ)) ^ 2) ^ (i : ℕ) ≤ (3 * (n + s) ^ 2 + 1) ^ s := by
    intro i
    have hi : (i : ℕ) ≤ s := Nat.lt_succ_iff.mp i.isLt
    have h1 : (n + (i : ℕ)) ^ 2 ≤ (n + s) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    calc (3 * (n + (i : ℕ)) ^ 2) ^ (i : ℕ) ≤ (3 * (n + s) ^ 2 + 1) ^ (i : ℕ) :=
          Nat.pow_le_pow_left (Nat.le_succ_of_le (Nat.mul_le_mul_left 3 h1)) _
      _ ≤ (3 * (n + s) ^ 2 + 1) ^ s := Nat.pow_le_pow_right (by omega) hi
  have hsum : ∑ i : Fin (s + 1), (3 * (n + (i : ℕ)) ^ 2) ^ (i : ℕ) ≤
      (s + 1) * (3 * (n + s) ^ 2 + 1) ^ s := by
    calc _ ≤ ∑ _i : Fin (s + 1), (3 * (n + s) ^ 2 + 1) ^ s := Finset.sum_le_sum fun i _ => hb i
      _ = _ := by simp
  omega

theorem dois_n_mais_um_le (n : ℕ) (hn : 3 ≤ n) : 2 * n + 1 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]; omega

/-- **Shannon**: para `n ≥ 4` existe função de `n` bits sem circuito com `≤ 2^n/(8n)` portas. -/
theorem shannon (n : ℕ) (hn : 4 ≤ n) : ∃ f : (Fin n → Bool) → Bool, ¬ TemCircuito f (2 ^ n / (8 * n)) := by
  apply existe_funcao_dificil
  set s := 2 ^ n / (8 * n) with hs
  have hN := dois_n_mais_um_le n (by omega)
  have h8 : s * (8 * n) ≤ 2 ^ n := Nat.div_mul_le_self _ _
  generalize hNdef : 2 ^ n = N at hN h8
  have hP : 8 * (n * s) ≤ N := by nlinarith
  have hsP : s ≤ n * s := Nat.le_mul_of_pos_left s (by omega)
  have h32 : 32 * s ≤ N := by nlinarith
  have hs1 : s + 1 ≤ N := by omega
  have hns : n + s ≤ N := by omega
  have hsq : (n + s) ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hns 2
  have hN1 : 1 ≤ N := by omega
  have hbase : 3 * (n + s) ^ 2 + 1 ≤ 4 * N ^ 2 := by nlinarith
  have h4 : 4 * N ^ 2 = 2 ^ (2 * n + 2) := by rw [← hNdef]; ring
  have hexp : n + (2 * n + 2) * s < N := by nlinarith
  calc (s + 1) * (3 * (n + s) ^ 2 + 1) ^ s ≤ N * (4 * N ^ 2) ^ s :=
        Nat.mul_le_mul hs1 (Nat.pow_le_pow_left hbase s)
    _ = 2 ^ (n + (2 * n + 2) * s) := by rw [h4, ← hNdef, ← pow_mul, ← pow_add]
    _ < 2 ^ N := Nat.pow_lt_pow_right (by norm_num) hexp

/-- `8 n^(k+1) < 2^n` para `n` grande. -/
theorem eventualmente_pol_lt_exp (k : ℕ) : ∀ᶠ n : ℕ in atTop, 8 * n ^ (k + 1) < 2 ^ n := by
  have h := tendsto_pow_const_div_const_pow_of_one_lt (k + 1) (by norm_num : (1 : ℝ) < 2)
  have h' := h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  filter_upwards [h'] with n hn
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_lt_iff₀ h2] at hn
  have : (8 * n ^ (k + 1) : ℝ) < 2 ^ n := by linarith
  exact_mod_cast this

/-- **Existe uma família de funções fora de `P/poly`**: para todo `k`, eventualmente `fₙ` não tem
circuito com `≤ n^k` portas. -/
theorem familia_fora_de_Ppoly :
    ∃ f : ∀ n : ℕ, (Fin n → Bool) → Bool, ∀ k : ℕ, ∀ᶠ n in atTop, ¬ TemCircuito (f n) (n ^ k) := by
  classical
  let f : ∀ n : ℕ, (Fin n → Bool) → Bool := fun n =>
    if hn : 4 ≤ n then Classical.choose (shannon n hn) else fun _ => false
  refine ⟨f, fun k => ?_⟩
  filter_upwards [eventualmente_pol_lt_exp k, eventually_ge_atTop 4] with n hn h4
  have hf : ¬ TemCircuito (f n) (2 ^ n / (8 * n)) := by
    simp only [f, h4, ↓reduceDIte]
    exact Classical.choose_spec (shannon n h4)
  intro hk
  apply hf
  refine temCircuito_mono ?_ hk
  rw [Nat.le_div_iff_mul_le (by omega)]
  calc n ^ k * (8 * n) = 8 * n ^ (k + 1) := by ring
    _ ≤ 2 ^ n := hn.le

end ATK.Shannon

#print axioms ATK.Shannon.card_op
#print axioms ATK.Shannon.temCircuito_mono
#print axioms ATK.Shannon.card_circuito
#print axioms ATK.Shannon.card_funcoes
#print axioms ATK.Shannon.existe_funcao_dificil
#print axioms ATK.Shannon.dois_n_mais_um_le
#print axioms ATK.Shannon.shannon
#print axioms ATK.Shannon.eventualmente_pol_lt_exp
#print axioms ATK.Shannon.familia_fora_de_Ppoly
