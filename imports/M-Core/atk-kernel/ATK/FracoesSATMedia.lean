import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# ATK — `7/8` para toda fórmula 3-CNF (rodada 104)

Completa a frente P vs NP da rodada 103 (`ATK.Fracoes.SAT`, que tinha `7/8` para uma cláusula só):

* `card_padrao_oito`: para variáveis distintas `x₀, x₁, x₂` e qualquer padrão `t ∈ {0,1}³`, exatamente `2ⁿ/8`
  atribuições `v : Fin n → Bool` têm `(v x₀, v x₁, v x₂) = t` (as 8 classes são trocadas entre si pela
  inversão de bits, `inverte`, que é involução);
* `card_satisfaz`: uma 3-cláusula com variáveis distintas é satisfeita por `7·2ⁿ/8` atribuições;
* **`media_sete_oitavos`**: para `m` cláusulas, `Σ_v #sat(v) · 8 = 7 m 2ⁿ` — a média é exatamente `7m/8`;
* **`existe_sete_oitavos`** (Johnson 1974): existe `v` que satisfaz pelo menos `7/8` das cláusulas.

Håstad (2001): para todo `ε > 0`, garantir `7/8 + ε` em tempo polinomial implica `P = NP` (ponte, não
formalizada). Classificação: **consequência** (clássica). P vs NP continua `OPEN_MATH`.
-/

open Finset

namespace ATK.Fracoes.SATMedia

variable {n : ℕ}

/-- O padrão de `v` nas três variáveis `x`. -/
def padrao (x : Fin 3 → Fin n) (v : Fin n → Bool) : Fin 3 → Bool := fun l => v (x l)

/-- Inversão dos bits marcados por `d`. -/
def inverte (d v : Fin n → Bool) : Fin n → Bool := fun m => xor (v m) (d m)

theorem inverte_inverte (d v : Fin n → Bool) : inverte d (inverte d v) = v := by
  funext m
  simp only [inverte]
  cases v m <;> cases d m <;> rfl

/-- Os bits onde os padrões `t` e `t'` diferem. -/
def dif (x : Fin 3 → Fin n) (t t' : Fin 3 → Bool) : Fin n → Bool :=
  fun m => decide (∃ l, x l = m ∧ t l ≠ t' l)

theorem dif_symm (x : Fin 3 → Fin n) (t t' : Fin 3 → Bool) : dif x t t' = dif x t' t := by
  funext m
  simp only [dif, ne_comm]

theorem padrao_inverte {x : Fin 3 → Fin n} (hx : Function.Injective x) {t t' : Fin 3 → Bool}
    {v : Fin n → Bool} (h : padrao x v = t) : padrao x (inverte (dif x t t') v) = t' := by
  funext l
  have hv : v (x l) = t l := congrFun h l
  have hd : dif x t t' (x l) = decide (t l ≠ t' l) := by
    unfold dif
    refine decide_eq_decide.mpr ⟨fun ⟨l', hl', hne⟩ => ?_, fun hne => ⟨l, rfl, hne⟩⟩
    rw [hx hl'] at hne
    exact hne
  simp only [padrao, inverte, hv, hd]
  cases t l <;> cases t' l <;> rfl

theorem card_padrao {x : Fin 3 → Fin n} (hx : Function.Injective x) (t t' : Fin 3 → Bool) :
    (univ.filter (fun v => padrao x v = t)).card = (univ.filter (fun v => padrao x v = t')).card := by
  refine Finset.card_nbij' (inverte (dif x t t')) (inverte (dif x t t')) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    exact padrao_inverte hx hv
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    rw [dif_symm]
    exact padrao_inverte hx hv
  · intro v _
    exact inverte_inverte _ _
  · intro v _
    exact inverte_inverte _ _

/-- **Cada um dos 8 padrões tem `2ⁿ/8` atribuições.** -/
theorem card_padrao_oito {x : Fin 3 → Fin n} (hx : Function.Injective x) (t : Fin 3 → Bool) :
    8 * (univ.filter (fun v => padrao x v = t)).card = 2 ^ n := by
  have hsum := Finset.card_eq_sum_card_fiberwise (f := padrao x) (s := (univ : Finset (Fin n → Bool)))
    (t := (univ : Finset (Fin 3 → Bool))) (fun _ _ => mem_univ _)
  rw [Finset.sum_congr rfl (fun t' _ => card_padrao hx t' t), Finset.sum_const, Finset.card_univ,
    Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_fin, Nat.nsmul_eq_mul] at hsum
  norm_num at hsum
  omega

/-- **Uma 3-cláusula com variáveis distintas é satisfeita por `7·2ⁿ/8` atribuições.** -/
theorem card_satisfaz {x : Fin 3 → Fin n} (hx : Function.Injective x) (s : Fin 3 → Bool) :
    8 * (univ.filter (fun v : Fin n → Bool => ∃ l, v (x l) = s l)).card = 7 * 2 ^ n := by
  have hc : univ.filter (fun v : Fin n → Bool => ¬ ∃ l, v (x l) = s l) =
      univ.filter (fun v => padrao x v = fun l => !(s l)) := by
    ext v
    simp only [mem_filter, mem_univ, true_and, not_exists, padrao, funext_iff]
    refine forall_congr' fun l => ?_
    cases v (x l) <;> cases s l <;> simp
  have h1 := card_padrao_oito hx (fun l => !(s l))
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin n → Bool))) (fun v => ∃ l, v (x l) = s l)
  rw [hc, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h2
  omega

variable {m : ℕ} (vars : Fin m → Fin 3 → Fin n) (sgn : Fin m → Fin 3 → Bool)

/-- Número de cláusulas satisfeitas por `v`. -/
def numSat (v : Fin n → Bool) : ℕ := (univ.filter (fun c => ∃ l, v (vars c l) = sgn c l)).card

/-- **A média é exatamente `7/8`**: `8 · Σ_v #sat(v) = 7 m 2ⁿ`. -/
theorem media_sete_oitavos (hinj : ∀ c, Function.Injective (vars c)) :
    8 * ∑ v : Fin n → Bool, numSat vars sgn v = 7 * m * 2 ^ n := by
  have e : ∑ v : Fin n → Bool, numSat vars sgn v =
      ∑ c : Fin m, (univ.filter (fun v : Fin n → Bool => ∃ l, v (vars c l) = sgn c l)).card := by
    simp only [numSat, Finset.card_filter]
    exact Finset.sum_comm
  rw [e, Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun c _ => card_satisfaz (hinj c) (sgn c)), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  ring

/-- **Johnson (7/8)**: existe uma atribuição que satisfaz pelo menos `7/8` das cláusulas. -/
theorem existe_sete_oitavos (hinj : ∀ c, Function.Injective (vars c)) :
    ∃ v : Fin n → Bool, 7 * m ≤ 8 * numSat vars sgn v := by
  by_contra h
  simp only [not_exists, not_le] at h
  have hlt : ∑ v : Fin n → Bool, 8 * numSat vars sgn v < ∑ _v : Fin n → Bool, 7 * m :=
    Finset.sum_lt_sum_of_nonempty univ_nonempty fun v _ => h v
  rw [← Finset.mul_sum, media_sete_oitavos vars sgn hinj, Finset.sum_const, Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.nsmul_eq_mul] at hlt
  rw [mul_comm] at hlt
  exact lt_irrefl _ hlt

end ATK.Fracoes.SATMedia

#print axioms ATK.Fracoes.SATMedia.inverte_inverte
#print axioms ATK.Fracoes.SATMedia.dif_symm
#print axioms ATK.Fracoes.SATMedia.padrao_inverte
#print axioms ATK.Fracoes.SATMedia.card_padrao
#print axioms ATK.Fracoes.SATMedia.card_padrao_oito
#print axioms ATK.Fracoes.SATMedia.card_satisfaz
#print axioms ATK.Fracoes.SATMedia.media_sete_oitavos
#print axioms ATK.Fracoes.SATMedia.existe_sete_oitavos
