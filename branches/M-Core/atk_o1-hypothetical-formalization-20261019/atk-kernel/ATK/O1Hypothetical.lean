import ATK.RiemannConcrete
import ATK.ObrigacoesMinimas

/-!
# O1: hypothesis-preserving semantics and temporal audit

This module does not prove the Riemann Hypothesis. It proves only logical
transports from an explicit hypothesis about the actual repository DN.
No custom axioms, sorry, or changes to the target definitions.
-/

open Filter Topology
open ATK.Conditional.Riemann

namespace ATK.O1Hypothetical

/-- Mathematical object: the actual infimum of the repository's DN. -/
def TerminalLimit : Prop := (⨅ N, DN N) = 0

/-- Semantic equivalence of the terminal and convergence formulations. -/
theorem terminal_iff_convergence :
    TerminalLimit ↔ Tendsto DN atTop (𝓝 0) := by
  exact ATK.RiemannConcrete.O1_iff_iInf_zero.symm

/-- Conditional RH, retaining the exact mathematical premise. -/
theorem rh_of_terminal (h : TerminalLimit) : RiemannHypothesis := by
  exact ATK.ObrigacoesMinimas.rh_obrigacao_suficiente
    (terminal_iff_convergence.mp h)

/-- A sufficient bound is logically stronger than the terminal premise. -/
theorem terminal_of_original_bound (h : UniformLogBound) : TerminalLimit := by
  exact terminal_iff_convergence.mpr
    (ATK.ObrigacoesMinimas.O1_implica_minima h)

/-- Conditional conjunction does not discharge its premise. -/
theorem closure_contract :
    TerminalLimit → (Tendsto DN atTop (𝓝 0) ∧ RiemannHypothesis) := by
  intro h
  exact ⟨terminal_iff_convergence.mp h, rh_of_terminal h⟩

end ATK.O1Hypothetical

#print axioms ATK.O1Hypothetical.terminal_iff_convergence
#print axioms ATK.O1Hypothetical.rh_of_terminal
#print axioms ATK.O1Hypothetical.terminal_of_original_bound
#print axioms ATK.O1Hypothetical.closure_contract
