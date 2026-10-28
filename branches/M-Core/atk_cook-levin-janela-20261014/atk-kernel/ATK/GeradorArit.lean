import ATK.GeradorForm
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# ATK — Cook–Levin, marco CL4b-4b: aritmética unária nos contadores

* `addTo a b`: `b += a`; `mulTo a x b`: `b += a · x`;
* `evalP cs x acc pow tmp`: `acc := Σ cs[i] · x^i` (potências crescentes), com custo
  `≤ |cs| · (C · (5 Y + 3) + 19 Y + 9) + 5` onde `Y = (x + 1)^|cs|` e `C = Σ cs`;
* `evalP_poly`: para os coeficientes de um polinômio `q`, `acc := q.eval x`.

**Nada aqui prova Cook–Levin. CLOSED_MATH continua false.**
-/

namespace ATK.Gerador

set_option linter.unusedSectionVars false

open Function

variable {R : Type} [DecidableEq R]

/-- `b += a`. -/
def addTo (a b : R) : Prog R := .loop a (.inc b)

theorem run_addTo (w : List Bool) {a b : R} (hab : a ≠ b) (s : St R) :
    run w (addTo a b) s = ⟨update s.regs b (s.regs b + s.regs a), s.out⟩ := by
  have it : ∀ n (s' : St R), (run w (.inc b))^[n] s' = ⟨update s'.regs b (s'.regs b + n), s'.out⟩ := by
    intro n
    induction n with
    | zero => intro s'; simp
    | succ n ih =>
      intro s'
      rw [iterate_succ_apply, ih]
      simp only [run, St.mk.injEq, and_true]
      funext r
      by_cases hr : r = b
      · subst hr; simp; omega
      · simp [update_of_ne hr]
  simp only [addTo, run]
  exact it _ s

theorem cost_addTo (w : List Bool) (a b : R) (s : St R) : cost w (addTo a b) s = 5 * s.regs a + 3 := by
  simp only [addTo, cost_loop]
  rw [costIt_const (cost w (.inc b)) _ 1 (fun _ => rfl)]
  ring

/-- `b += a · x`. -/
def mulTo (a x b : R) : Prog R := .loop a (addTo x b)

theorem run_mulTo (w : List Bool) {a x b : R} (_hab : a ≠ b) (hxb : x ≠ b) (s : St R) :
    run w (mulTo a x b) s = ⟨update s.regs b (s.regs b + s.regs a * s.regs x), s.out⟩ := by
  have it : ∀ n (s' : St R), s'.regs x = s.regs x →
      (run w (addTo x b))^[n] s' = ⟨update s'.regs b (s'.regs b + n * s.regs x), s'.out⟩ := by
    intro n
    induction n with
    | zero => intro s' _; simp
    | succ n ih =>
      intro s' hs'
      rw [iterate_succ_apply, ih _ (by rw [run_addTo w hxb]; simp [update_of_ne hxb, hs'])]
      rw [run_addTo w hxb]
      simp only [St.mk.injEq, and_true]
      funext r
      by_cases hr : r = b
      · subst hr; simp [hs']; ring
      · simp [update_of_ne hr]
  simp only [mulTo, run]
  exact it _ s rfl

theorem cost_mulTo (w : List Bool) {a x b : R} (hab : a ≠ b) (hxb : x ≠ b) (s : St R) :
    cost w (mulTo a x b) s = 5 * s.regs a * s.regs x + 7 * s.regs a + 3 := by
  have it : ∀ n (s' : St R), s'.regs x = s.regs x →
      costIt (cost w (addTo x b)) (run w (addTo x b)) n s' = n * (5 * s.regs x + 5) := by
    intro n
    induction n with
    | zero => intro s' _; simp [costIt]
    | succ n ih =>
      intro s' hs'
      rw [costIt_succ, ih _ (by rw [run_addTo w hxb]; simp [update_of_ne hxb, hs']), cost_addTo, hs']
      ring
  simp only [mulTo, cost_loop]
  rw [it _ s rfl]
  ring

/-- `acc += c · pow`. -/
def addMul (c : ℕ) (pow acc : R) : Prog R := seqs (List.replicate c (addTo pow acc))

theorem run_addMul (w : List Bool) {pow acc : R} (h : pow ≠ acc) :
    ∀ (c : ℕ) (s : St R),
      run w (addMul c pow acc) s = ⟨update s.regs acc (s.regs acc + c * s.regs pow), s.out⟩
  | 0, s => by simp [addMul, seqs, run]
  | c + 1, s => by
    simp only [addMul, List.replicate_succ, seqs, List.foldr_cons, run]
    have := run_addMul w h c (run w (addTo pow acc) s)
    simp only [addMul, seqs] at this
    rw [this, run_addTo w h]
    simp only [St.mk.injEq, and_true]
    funext r
    by_cases hr : r = acc
    · subst hr; simp [update_of_ne h]; ring
    · simp [update_of_ne hr]

theorem cost_addMul (w : List Bool) {pow acc : R} (h : pow ≠ acc) :
    ∀ (c : ℕ) (s : St R), cost w (addMul c pow acc) s = c * (5 * s.regs pow + 3)
  | 0, s => by simp [addMul, seqs, cost]
  | c + 1, s => by
    simp only [addMul, List.replicate_succ, seqs, List.foldr_cons, cost_seq]
    have := cost_addMul w h c (run w (addTo pow acc) s)
    simp only [addMul, seqs] at this
    rw [this, cost_addTo, run_addTo w h]
    simp [update_of_ne h]
    ring

/-- `pow := pow · x`, usando `tmp` (zerado no fim). -/
def mulP (x pow tmp : R) : Prog R :=
  .seq (.clr tmp) (.seq (mulTo pow x tmp) (.seq (.clr pow) (.seq (addTo tmp pow) (.clr tmp))))

theorem run_mulP (w : List Bool) {x pow tmp : R} (h1 : x ≠ pow) (h2 : x ≠ tmp) (h3 : pow ≠ tmp)
    (s : St R) :
    run w (mulP x pow tmp) s =
      ⟨update (update s.regs pow (s.regs pow * s.regs x)) tmp 0, s.out⟩ := by
  simp only [mulP, run]
  rw [run_mulTo w h3 h2]
  simp only
  rw [run_addTo w (Ne.symm h3)]
  simp only [St.mk.injEq, and_true]
  funext r
  by_cases hr : r = tmp
  · subst hr; simp
  · by_cases hp : r = pow
    · subst hp; simp [hr, update_of_ne h2, update_of_ne h3.symm]
    · simp [hr, hp, update_of_ne h3, update_of_ne (Ne.symm h3)]

theorem cost_mulP (w : List Bool) {x pow tmp : R} (h1 : x ≠ pow) (h2 : x ≠ tmp) (h3 : pow ≠ tmp)
    (s : St R) :
    cost w (mulP x pow tmp) s = 11 * s.regs pow * s.regs x + 8 * s.regs pow + s.regs tmp + 9 := by
  simp only [mulP, cost_seq, cost_clr]
  rw [cost_mulTo w h3 h2]
  simp only [run]
  rw [run_mulTo w h3 h2]
  simp only
  rw [cost_addTo]
  simp only [run]
  rw [run_addTo w (Ne.symm h3)]
  simp [update_of_ne h3, update_of_ne (Ne.symm h3), update_of_ne h2]
  ring

/-- Um passo da avaliação: `acc += c · pow`, `pow := pow · x`. -/
def passoP (c : ℕ) (x acc pow tmp : R) : Prog R := .seq (addMul c pow acc) (mulP x pow tmp)

/-- `Σ cs[i] · x^i`, pela regra de Horner. -/
def horn (x : ℕ) : List ℕ → ℕ
  | [] => 0
  | c :: cs => c + x * horn x cs

theorem horn_range (x : ℕ) (f : ℕ → ℕ) :
    ∀ n, horn x ((List.range n).map f) = ∑ i ∈ Finset.range n, f i * x ^ i
  | 0 => by simp [horn]
  | n + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, horn,
      Finset.sum_range_succ', horn_range x (f ∘ Nat.succ) n, Finset.mul_sum]
    simp only [Function.comp, pow_zero, Nat.mul_one, pow_succ]
    rw [Nat.add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- **Avaliação de polinômio** pelas potências crescentes. -/
def evalP (cs : List ℕ) (x acc pow tmp : R) : Prog R :=
  .seq (.clr acc) (.seq (.clr pow) (.seq (.clr tmp) (.seq (.inc pow)
    (.seq (seqs (cs.map fun c => passoP c x acc pow tmp)) (.clr pow)))))

section Avaliacao

variable {x acc pow tmp : R} (hxa : x ≠ acc) (hxp : x ≠ pow) (hxt : x ≠ tmp) (hap : acc ≠ pow)
  (hat : acc ≠ tmp) (hpt : pow ≠ tmp)
include hxa hxp hxt hap hat hpt

theorem run_passos (w : List Bool) :
    ∀ (cs : List ℕ) (s : St R), s.regs tmp = 0 →
      run w (seqs (cs.map fun c => passoP c x acc pow tmp)) s =
        ⟨update (update s.regs acc (s.regs acc + s.regs pow * horn (s.regs x) cs))
          pow (s.regs pow * s.regs x ^ cs.length), s.out⟩
  | [], s, _ => by
    simp only [List.map_nil, seqs, List.foldr_nil, run, horn, List.length_nil,
      Nat.mul_zero, Nat.add_zero, pow_zero, Nat.mul_one, update_eq_self]
  | c :: cs, s, ht => by
    simp only [List.map_cons, seqs, List.foldr_cons, run]
    have h1 : run w (passoP c x acc pow tmp) s =
        ⟨update (update s.regs acc (s.regs acc + c * s.regs pow)) pow
          (s.regs pow * s.regs x), s.out⟩ := by
      simp only [passoP, run]
      rw [run_addMul w hap.symm, run_mulP w hxp hxt hpt]
      simp only [St.mk.injEq, and_true]
      funext r
      by_cases hr : r = tmp
      · subst hr; simp [update_of_ne (Ne.symm hpt), update_of_ne (Ne.symm hat), ht]
      · simp [hr, update_of_ne hap.symm, update_of_ne hxa, update_of_ne hxp]
    have hx1 : (run w (passoP c x acc pow tmp) s).regs x = s.regs x := by
      rw [h1]; simp [update_of_ne hxa, update_of_ne hxp]
    have := run_passos w cs (run w (passoP c x acc pow tmp) s) (by
      rw [h1]; simp [update_of_ne (Ne.symm hpt), update_of_ne (Ne.symm hat), ht])
    simp only [seqs] at this
    rw [this, hx1, h1]
    simp only [St.mk.injEq, and_true]
    funext r
    by_cases hr : r = pow
    · subst hr; simp [update_of_ne hap, pow_succ]; ring
    · by_cases ha : r = acc
      · subst ha
        simp [hr, update_of_ne hap.symm, update_of_ne hap, horn]
        ring
      · simp [hr, ha]

theorem cost_passos (w : List Bool) (Y : ℕ) :
    ∀ (cs : List ℕ) (s : St R), s.regs tmp = 0 → s.regs pow * (s.regs x + 1) ^ cs.length ≤ Y →
      cost w (seqs (cs.map fun c => passoP c x acc pow tmp)) s ≤
        cs.length * (cs.sum * (5 * Y + 3) + 19 * Y + 9)
  | [], s, _, _ => by simp [seqs, cost]
  | c :: cs, s, ht, hY => by
    simp only [List.map_cons, seqs, List.foldr_cons, cost_seq]
    have h1 : run w (passoP c x acc pow tmp) s =
        ⟨update (update s.regs acc (s.regs acc + c * s.regs pow)) pow
          (s.regs pow * s.regs x), s.out⟩ := by
      simp only [passoP, run]
      rw [run_addMul w hap.symm, run_mulP w hxp hxt hpt]
      simp only [St.mk.injEq, and_true]
      funext r
      by_cases hr : r = tmp
      · subst hr; simp [update_of_ne (Ne.symm hpt), update_of_ne (Ne.symm hat), ht]
      · simp [hr, update_of_ne hap.symm, update_of_ne hxa, update_of_ne hxp]
    have hc1 : cost w (passoP c x acc pow tmp) s =
        c * (5 * s.regs pow + 3) + (11 * s.regs pow * s.regs x + 8 * s.regs pow + 0 + 9) := by
      simp only [passoP, cost_seq]
      rw [cost_addMul w hap.symm, cost_mulP w hxp hxt hpt, run_addMul w hap.symm]
      simp [update_of_ne (Ne.symm hat), update_of_ne hap.symm, update_of_ne hxa, ht]
    have hpowle : s.regs pow ≤ Y := by
      refine le_trans ?_ hY
      exact Nat.le_mul_of_pos_right _ (pow_pos (Nat.succ_pos _) _)
    have hpx : s.regs pow * s.regs x ≤ Y := by
      refine le_trans ?_ hY
      rw [List.length_cons, pow_succ]
      calc s.regs pow * s.regs x ≤ s.regs pow * (s.regs x + 1) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ s.regs pow * ((s.regs x + 1) ^ cs.length * (s.regs x + 1)) := by
          apply Nat.mul_le_mul_left
          exact Nat.le_mul_of_pos_left _ (pow_pos (Nat.succ_pos _) _)
    have hnext := cost_passos w Y cs (run w (passoP c x acc pow tmp) s)
      (by rw [h1]; simp [update_of_ne (Ne.symm hpt), update_of_ne (Ne.symm hat), ht])
      (by
        rw [h1]
        simp only [update_self, update_of_ne hxp, update_of_ne hxa]
        refine le_trans ?_ hY
        rw [List.length_cons, pow_succ, Nat.mul_assoc]
        apply Nat.mul_le_mul_left
        rw [Nat.mul_comm]
        exact Nat.mul_le_mul_left _ (by omega))
    simp only [seqs] at hnext
    rw [hc1]
    simp only [List.length_cons, List.sum_cons]
    have e0 : 8 * s.regs pow ≤ 8 * Y := Nat.mul_le_mul_left _ hpowle
    have e1 : c * (5 * s.regs pow + 3) ≤ c * (5 * Y + 3) := Nat.mul_le_mul_left _ (by omega)
    have e2 : 11 * s.regs pow * s.regs x ≤ 11 * Y := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hpx
    have e3 : cs.length * (cs.sum * (5 * Y + 3) + 19 * Y + 9) ≤
        cs.length * ((c + cs.sum) * (5 * Y + 3) + 19 * Y + 9) := by
      apply Nat.mul_le_mul_left
      have : cs.sum * (5 * Y + 3) ≤ (c + cs.sum) * (5 * Y + 3) := Nat.mul_le_mul_right _ (by omega)
      omega
    have e4 : c * (5 * Y + 3) ≤ (c + cs.sum) * (5 * Y + 3) := Nat.mul_le_mul_right _ (by omega)
    calc _ ≤ (c + cs.sum) * (5 * Y + 3) + (11 * Y + 8 * Y + 0 + 9) +
          cs.length * ((c + cs.sum) * (5 * Y + 3) + 19 * Y + 9) := by omega
      _ = (cs.length + 1) * ((c + cs.sum) * (5 * Y + 3) + 19 * Y + 9) := by ring

theorem run_evalP (w : List Bool) (cs : List ℕ) (s : St R) :
    run w (evalP cs x acc pow tmp) s =
      ⟨update (update (update s.regs acc (horn (s.regs x) cs)) pow 0) tmp 0, s.out⟩ := by
  simp only [evalP, run]
  rw [run_passos hxa hxp hxt hap hat hpt w cs _ (by simp [update_of_ne hpt.symm])]
  have hp1 : update (update (update s.regs acc 0) pow 0) tmp 0 pow = 0 := by
    rw [update_of_ne hpt]; simp
  simp only [St.mk.injEq, and_true]
  funext r
  by_cases hr : r = pow
  · subst hr; simp [update_of_ne hpt]
  · by_cases ht : r = tmp
    · subst ht; simp [hr, update_of_ne hpt.symm, update_of_ne hat.symm]
    · by_cases ha : r = acc
      · subst ha; simp [hr, ht, update_of_ne hap, update_of_ne hat, update_of_ne hxa,
          update_of_ne hxp, update_of_ne hxt, hp1]
      · simp [hr, ht, ha]

theorem cost_evalP (w : List Bool) (cs : List ℕ) (s : St R) :
    cost w (evalP cs x acc pow tmp) s ≤
      s.regs acc + s.regs pow + s.regs tmp + 5 +
        cs.length * (cs.sum * (5 * (s.regs x + 1) ^ cs.length + 3) +
          19 * (s.regs x + 1) ^ cs.length + 9) + (s.regs x + 1) ^ cs.length := by
  simp only [evalP, cost_seq, cost_clr, cost_inc]
  have hc := cost_passos hxa hxp hxt hap hat hpt w ((s.regs x + 1) ^ cs.length) cs
    (run w (.inc pow) (run w (.clr tmp) (run w (.clr pow) (run w (.clr acc) s))))
    (by simp [run, update_of_ne hpt.symm])
    (by simp [run, update_of_ne hxp, update_of_ne hxt, update_of_ne hxa, update_of_ne hpt])
  rw [run_passos hxa hxp hxt hap hat hpt w cs _ (by simp [run, update_of_ne hpt.symm])]
  simp only [run, update_self, update_of_ne hpt, update_of_ne hap.symm] at hc ⊢
  have hxn : (s.regs x) ^ cs.length ≤ (s.regs x + 1) ^ cs.length :=
    Nat.pow_le_pow_left (by omega) _
  simp [update_of_ne hxp, update_of_ne hxt, update_of_ne hxa, update_of_ne hpt,
    update_of_ne hap.symm, update_of_ne hap, update_of_ne hpt.symm, update_of_ne hat.symm] at hc ⊢
  omega

end Avaliacao

/-- Os coeficientes de um polinômio em lista. -/
noncomputable def coefs (q : Polynomial ℕ) : List ℕ := (List.range (q.natDegree + 1)).map q.coeff

theorem horn_coefs (q : Polynomial ℕ) (x : ℕ) : horn x (coefs q) = q.eval x := by
  rw [coefs, horn_range, Polynomial.eval_eq_sum_range]

end ATK.Gerador

#print axioms ATK.Gerador.addTo
#print axioms ATK.Gerador.run_addTo
#print axioms ATK.Gerador.cost_addTo
#print axioms ATK.Gerador.mulTo
#print axioms ATK.Gerador.run_mulTo
#print axioms ATK.Gerador.cost_mulTo
#print axioms ATK.Gerador.addMul
#print axioms ATK.Gerador.run_addMul
#print axioms ATK.Gerador.cost_addMul
#print axioms ATK.Gerador.mulP
#print axioms ATK.Gerador.run_mulP
#print axioms ATK.Gerador.cost_mulP
#print axioms ATK.Gerador.passoP
#print axioms ATK.Gerador.horn
#print axioms ATK.Gerador.horn_range
#print axioms ATK.Gerador.evalP
#print axioms ATK.Gerador.run_passos
#print axioms ATK.Gerador.cost_passos
#print axioms ATK.Gerador.run_evalP
#print axioms ATK.Gerador.cost_evalP
#print axioms ATK.Gerador.horn_coefs
