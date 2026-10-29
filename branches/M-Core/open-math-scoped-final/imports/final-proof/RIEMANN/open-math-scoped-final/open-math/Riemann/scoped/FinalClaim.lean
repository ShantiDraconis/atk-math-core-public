import Riemann.scoped.FinalProof

namespace Riemann.scoped

open MCore.RH.NB

theorem FINAL_CLAIM
    (D : NBHilbertData)
    (rho : D.GeneratorFamily)
    (h : D.VanishingUpperBound rho) :
    D.DNLimit rho = 0 :=
  FINAL_PROOF D rho h

#print axioms FINAL_CLAIM

end Riemann.scoped
