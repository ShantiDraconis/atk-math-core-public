import Riemann.frozen.vanishing_upper_bound_green_5c66f8dc

namespace Riemann.scoped

open MCore.RH.NB

theorem FINAL_PROOF
    (D : NBHilbertData)
    (rho : D.GeneratorFamily)
    (h : D.VanishingUpperBound rho) :
    D.DNLimit rho = 0 :=
  Riemann.frozen.vanishing_upper_bound_thm D rho h

theorem FINAL_SCOPED_CLAIM
    (D : NBHilbertData)
    (rho : D.GeneratorFamily)
    (h : D.VanishingUpperBound rho) :
    D.DNLimit rho = 0 :=
  FINAL_PROOF D rho h

#print axioms FINAL_PROOF
#print axioms FINAL_SCOPED_CLAIM

end Riemann.scoped
