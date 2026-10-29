import MCore.RH.NB.QuantitativeUpperBound

namespace Riemann.frozen

open MCore.RH.NB

/-- Pinned scoped reuse of the GREEN theorem at 5c66f8dc.
    This does not state or prove RiemannHypothesis. -/
theorem vanishing_upper_bound_thm
    (D : NBHilbertData)
    (rho : D.GeneratorFamily)
    (h : D.VanishingUpperBound rho) :
    D.DNLimit rho = 0 :=
  D.DNLimit_eq_zero_of_vanishingUpperBound rho h

#print axioms vanishing_upper_bound_thm

end Riemann.frozen
