namespace MCore.YangMills.A1

/-!
Decomposition of the A1 `OPEN_BRIDGE` into its five sub-bridges, classified
per the frontier protocol's four terminal states. This file is deliberately
independent of `Mathlib`/`Hardening`/`PositiveControl`: it is bookkeeping
data, not a proof about `A1ScientificWitness` itself, and its own build
must never become a place to quietly relabel a `blockingOpen` node.

Terminal states:
- `proved`: discharged inside this repository, from first principles.
- `externalClassical reference`: discharged by a named classical theorem,
  not reproved here. Citing this status without a real `reference` string
  is itself a NO-PLACEBO violation.
- `blockingOpen`: no witness exists anywhere; this is the genuine frontier.
- `refuted`: the sub-bridge as stated is false (countermodel found).
-/

inductive BridgeStatus where
  | proved
  | externalClassical (reference : String)
  | blockingOpen
  | refuted
  deriving DecidableEq, Repr

structure SubBridge where
  name : String
  field : String
  status : BridgeStatus
  note : String
  deriving DecidableEq, Repr

/-- `A1ScientificWitness`'s five fields, decomposed. `toy_a1_scientific_witness`
(`PositiveControl.lean`) discharges every field's *type* for a degenerate
one-point, zero-estimate instance — that is a satisfiability check, not a
classical or proved discharge of the physical statement, so it is recorded in
each `note`, never as the `status` itself. -/
def a1Decomposition : List SubBridge :=
  [ { name := "B1"
      field := "MeasureInvariance"
      status := .externalClassical
        "Haar-measure invariance under gauge translation for compact lattice gauge theories (Osterwalder-Seiler, Comm. Math. Phys. 42 (1975) 281)"
      note := "toy_a1_scientific_witness discharges only the one-point, trivial-gauge-group instance; the physical instance (Haar product measure over a compact gauge group) is not yet formalized in this repository." }
  , { name := "B2"
      field := "ObservableInvariance"
      status := .externalClassical
        "Wilson-loop/plaquette-trace observables are gauge invariant by construction (standard lattice gauge theory)"
      note := "toy_a1_scientific_witness discharges only the trivial constant-observable instance." }
  , { name := "B3"
      field := "ReflectionPositivityData"
      status := .externalClassical
        "Reflection positivity for compact lattice gauge theories (Osterwalder-Seiler, Comm. Math. Phys. 42 (1975) 281)"
      note := "toy_a1_scientific_witness discharges only a degenerate single-test instance; the physical OS positivity argument is not yet formalized here." }
  , { name := "B4"
      field := "PositiveTransferData"
      status := .externalClassical
        "GNS/transfer-operator reconstruction from reflection positivity (Osterwalder-Schrader, Comm. Math. Phys. 31 (1973) 83 and 42 (1975) 281)"
      note := "toy_a1_scientific_witness discharges only the trivial zero-operator instance." }
  , { name := "B5"
      field := "UniformRegulatorControl"
      status := .blockingOpen
      note := "The uniform (cutoff -> 0, volume -> infinity) mass-gap bound is exactly the unresolved Yang-Mills existence-and-mass-gap statement. pointwise_cutoff_volume_positive_not_uniform (UniformityFirewalls.lean) proves pointwise control at each fixed cutoff/volume can never by itself supply this; toy_a1_scientific_witness's zero estimate is uniform only because it carries no gap." }
  ]

theorem a1_decomposition_count : a1Decomposition.length = 5 := by rfl

/-- The only sub-bridge without a witness or a named classical reference is
`UniformRegulatorControl`. If this ever fails after an edit to
`a1Decomposition`, either a real sub-bridge was closed (update the note and
keep this theorem honest) or a `blockingOpen` node was quietly relabeled
(reject the edit). -/
theorem a1_exactly_one_blocking_node :
    (a1Decomposition.filter (fun b => decide (b.status = .blockingOpen))).length = 1 := by
  decide

theorem a1_blocking_node_is_uniformity :
    ∀ b ∈ a1Decomposition, b.status = .blockingOpen → b.field = "UniformRegulatorControl" := by
  decide

end MCore.YangMills.A1
