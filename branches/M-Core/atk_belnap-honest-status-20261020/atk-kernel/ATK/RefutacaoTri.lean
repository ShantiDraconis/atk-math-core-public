import ATK.ClosedMath

/-!
# ATK — Refutation of the "Tri" three-state trick

This file permanently documents, as checked theorems (not just a comment someone can skip past),
why a three-constructor type

```
inductive Tri (P : Prop) : Type
| t  : P → Tri P
| f  : ¬P → Tri P
| tf : P → ¬P → Tri P
```

does **not** give `OPEN_MATH`/`BRIDGE`/`CLOSED_MATH` a genuine third "true and false
simultaneously" state. Constructing `Tri.tf h1 h2` requires a term `h1 : P` and a term
`h2 : ¬P` at the same time. Since `¬P` unfolds to `P → False`, the application `h2 h1` is
already a term of type `False` — and `False.elim` proves anything whatsoever (the principle of
explosion). So `Tri.tf` is not a stable third value; it is a detector of inconsistency in the
ambient axioms. If it were ever inhabited for a real, consistent mathematical proposition `P`,
the news would be that the background theory (Mathlib / the logic Lean checks against) is
inconsistent — not that `P` has an interesting third truth value.

If genuine disagreement between different research branches needs tracking (one branch's
human-reviewed model judged faithful, another branch finding the same parametric instance
vacuous — see `ATK.ClosedMath.ns_toy_model_vacuous` / `pnp_toy_model_vacuous` for exactly this
failure mode), use `ATK.StatusHonesto`'s `Evidencia`/`ValorBelnap` instead: two independent
booleans recording what was *reported*, never a literal `P`/`¬P` pair.
-/

namespace ATK.RefutacaoTri

/-- The three-state type someone might be tempted to use. Defining it is harmless; the point of
this file is that its third constructor can never be inhabited for a consistent `P`. -/
inductive Tri (P : Prop) : Type where
  | t : P → Tri P
  | f : ¬P → Tri P
  | tf : P → ¬P → Tri P

/-- Constructing the `tf` case already requires a contradiction. -/
theorem tf_requires_false {P : Prop} (h1 : P) (h2 : ¬P) : False := h2 h1

/-- From that contradiction, anything follows — `tf` cannot carry information about `P`,
because it only exists when every proposition is simultaneously provable. -/
theorem tf_explodes {P Q : Prop} (h1 : P) (h2 : ¬P) : Q := (tf_requires_false h1 h2).elim

/-- The same fact, phrased as "there is no way to case on `Tri.tf` without already having
`False` in hand". -/
theorem tri_tf_case_gives_false {P : Prop} : (∃ h1 : P, ∃ _h2 : ¬P, True) → False :=
  fun ⟨h1, h2, _⟩ => tf_requires_false h1 h2

/-- Concretely, for any model `M`: `SevenStatements M` and its negation can never both be
inhabited. This is exactly why a `ClosedMath_Tri`-style "true/false coexisting" label for
`CLOSED_MATH` can never be built from real witnesses — only from a bug or an outright
inconsistency. -/
theorem sevenStatements_tf_would_explode {M : ATK.ClosedMath.Models}
    (h1 : ATK.ClosedMath.SevenStatements M) (h2 : ¬ ATK.ClosedMath.SevenStatements M) :
    False :=
  tf_requires_false h1 h2

end ATK.RefutacaoTri

#print axioms ATK.RefutacaoTri.tf_requires_false
#print axioms ATK.RefutacaoTri.tf_explodes
#print axioms ATK.RefutacaoTri.tri_tf_case_gives_false
#print axioms ATK.RefutacaoTri.sevenStatements_tf_would_explode
