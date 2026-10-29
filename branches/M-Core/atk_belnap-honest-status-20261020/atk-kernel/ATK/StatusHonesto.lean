/-!
# ATK — Honest cross-branch evidence tracking (Belnap–Dunn four values)

Different attack branches on the same obligation or bridge can report conflicting claims about
it (one branch's human-reviewed model judged faithful, another branch finding the same
parametric instance vacuous — see `ATK.ClosedMath.ns_toy_model_vacuous` /
`pnp_toy_model_vacuous`). This file tracks that disagreement as **data**: two independent
booleans recording what was reported, never a literal proof of `P` and a literal proof of `¬P`.
It therefore can never collapse to `False` the way the naive "three-valued `Prop`" approach does
(see `ATK.RefutacaoTri`).

`ambos` ("both") means two sources disagreed, not that the claim itself has some third truth
value. A claim with no proof either way is `nenhum` ("none"), not `ambos` — missing a proof is
not evidence *against* a statement, and conflating "incomplete" with "contradicted" is exactly
the kind of imprecision this file exists to prevent.
-/

namespace ATK.StatusHonesto

/-- Four-valued evidence status (Belnap–Dunn). Never derived from a `Prop`/`¬Prop` pair. -/
inductive ValorBelnap where
  | verdadeiro
  | falso
  | ambos
  | nenhum
  deriving DecidableEq, Repr

/-- One source's report about one claim. `temAFavor`/`temContra` are plain booleans — flags
about what was *reported*, never proof terms. A `prova` field, when present, names the actual
Lean theorem backing a `temAFavor := true` report; a report with no such theorem is evidence,
not a certificate. -/
structure Evidencia where
  camada : String
  claim : String
  temAFavor : Bool
  temContra : Bool
  fonte : String
  prova : Option String := none
  deriving Repr

def Evidencia.valor (e : Evidencia) : ValorBelnap :=
  match e.temAFavor, e.temContra with
  | true, false => .verdadeiro
  | false, true => .falso
  | true, true => .ambos
  | false, false => .nenhum

/-- Combining reports from several sources **about the same claim**: favorable if *any* matching
source reported favorable evidence, contrary if *any* matching source reported contrary
evidence. `es` is filtered to `e.claim = claim` first — otherwise a favorable report about one
claim and a contrary report about an unrelated claim would wrongly combine into `ambos` for a
claim neither source said anything about. -/
def combinar (claim : String) (es : List Evidencia) : ValorBelnap :=
  let relevantes := es.filter (·.claim == claim)
  Evidencia.valor
    { camada := "", claim := claim, fonte := "",
      temAFavor := relevantes.any (·.temAFavor), temContra := relevantes.any (·.temContra) }

end ATK.StatusHonesto
