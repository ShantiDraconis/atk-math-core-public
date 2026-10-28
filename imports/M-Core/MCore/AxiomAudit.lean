import MCore

/-!
K15 axiom audit targets.

This file deliberately contains no new axioms.  The executable CI gate prints
Lean's actual axiom dependencies for the project declarations below; CI then
compares those names with the explicit foundational allowlist.
-/

#print axioms MCore.no_open
#print axioms MCore.no_promotion
#print axioms MCore.audit_illegal_promotions
#print axioms MCore.blocked_necessary
#print axioms MCore.amplitude_unbounded
#print axioms MCore.no_fixed_delta_gap
#print axioms MCore.no_path_independent_extension
#print axioms MCore.explicit_no_common_extension
#print axioms MCore.rhoStarScaleLaw_holds
#print axioms MCore.certifiedObligations_iff_zeroTotal
