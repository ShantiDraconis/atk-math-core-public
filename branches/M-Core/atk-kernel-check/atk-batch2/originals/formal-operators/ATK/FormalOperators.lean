import ATK.KernelGates

/-!
ATK: unconditional elementary inhabitants and operators.
These theorems are NOT the seven open conjectures.
-/
namespace ATK.Formal

-- Logic: witnesses, conjunction, and semantic preservation.
theorem inhabited_to_exists {α : Sort u} (a : α) : Nonempty α := ⟨a⟩
theorem compose_proofs {P Q R : Prop} (pq : P → Q) (qr : Q → R) : P → R :=
  fun p => qr (pq p)
theorem conjunction_commutes {P Q : Prop} : P ∧ Q → Q ∧ P :=
  fun h => ⟨h.2, h.1⟩

-- Arithmetic: natural-number order and well-founded descent.
theorem zero_le_all (n : Nat) : 0 ≤ n := Nat.zero_le n
theorem successor_strict (n : Nat) : n < n + 1 := Nat.lt_succ_self n
theorem no_decrease_at_zero (f : Nat → Nat) : ¬ (∀ n, f n < n) := by
  intro h
  exact Nat.not_lt_zero (f 0) (h 0)

-- Algebra: additive structure of integers.
theorem add_zero_int (x : Int) : x + 0 = x := add_zero x
theorem add_comm_int (x y : Int) : x + y = y + x := add_comm x y
theorem add_assoc_int (x y z : Int) : (x + y) + z = x + (y + z) :=
  add_assoc x y z

-- Geometry: a concrete 2D point and translation operators.
structure Point2 where
  x : Int
  y : Int
  deriving DecidableEq, Repr

def translate (p v : Point2) : Point2 := ⟨p.x + v.x, p.y + v.y⟩
def origin : Point2 := ⟨0, 0⟩
theorem translate_origin (p : Point2) : translate p origin = p := by
  cases p with
  | mk x y =>
    simp [translate, origin]

theorem translate_comp (p v w : Point2) :
    translate (translate p v) w =
    translate p (translate v w) := by
  cases p with
  | mk px py =>
    cases v with
    | mk vx vy =>
      cases w with
      | mk wx wy =>
        simp [translate, Int.add_assoc]

-- Computational semantics: concrete evaluation of Boolean expressions.
inductive Expr where
  | lit : Bool → Expr
  | neg : Expr → Expr
  | conj : Expr → Expr → Expr
  deriving Repr

def eval : Expr → Bool
  | .lit b => b
  | .neg e => !(eval e)
  | .conj a b => eval a && eval b

theorem eval_literal (b : Bool) : eval (.lit b) = b := rfl
theorem eval_conj (a b : Expr) :
    eval (.conj a b) = (eval a && eval b) := rfl
theorem eval_neg (a : Expr) : eval (.neg a) = !(eval a) := rfl

-- A bridge may be used only after both the concrete material and the
-- independently established implication are supplied.
theorem terminal_application {Material Target : Prop}
    (inhabitant : Material) (bridge : Material → Target) : Target :=
  bridge inhabitant

end ATK.Formal
