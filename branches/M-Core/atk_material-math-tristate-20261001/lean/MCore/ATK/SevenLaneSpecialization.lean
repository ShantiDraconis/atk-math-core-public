import MCore.ATK.UniversalProducerTheorem

namespace MCore.ATK.UniversalProducer

open MCore.ATK.StructuralDefect

/--
Explicit seven-field view of the dependent universal inhabitant bundle.

The fields remain problem-specific dependent types; this structure does not
identify the mathematical inhabitants across lanes.
-/
structure SevenInhabitantBundle (K : UniversalProducerKernel) where
  riemann : (K.lane .riemann).Inhabitant
  pnp : (K.lane .pnp).Inhabitant
  yangMills : (K.lane .yangMills).Inhabitant
  navierStokes : (K.lane .navierStokes).Inhabitant
  bsd : (K.lane .bsd).Inhabitant
  hodge : (K.lane .hodge).Inhabitant
  beal : (K.lane .beal).Inhabitant

/-- Explicit seven-field view of the universal final certificate root. -/
structure SevenCertificateBundle (K : UniversalProducerKernel) where
  riemann : (K.lane .riemann).Certificate
  pnp : (K.lane .pnp).Certificate
  yangMills : (K.lane .yangMills).Certificate
  navierStokes : (K.lane .navierStokes).Certificate
  bsd : (K.lane .bsd).Certificate
  hodge : (K.lane .hodge).Certificate
  beal : (K.lane .beal).Certificate

/-- Expand the dependent inhabitant family into seven named fields. -/
def UniversalInhabitantBundle.toSeven
    {K : UniversalProducerKernel}
    (B : UniversalInhabitantBundle K) :
    SevenInhabitantBundle K where
  riemann := B.inhabitant .riemann
  pnp := B.inhabitant .pnp
  yangMills := B.inhabitant .yangMills
  navierStokes := B.inhabitant .navierStokes
  bsd := B.inhabitant .bsd
  hodge := B.inhabitant .hodge
  beal := B.inhabitant .beal

/-- Reassemble the seven named inhabitant fields into the dependent family. -/
def SevenInhabitantBundle.toUniversal
    {K : UniversalProducerKernel}
    (B : SevenInhabitantBundle K) :
    UniversalInhabitantBundle K where
  inhabitant := fun p =>
    match p with
    | .riemann => B.riemann
    | .pnp => B.pnp
    | .yangMills => B.yangMills
    | .navierStokes => B.navierStokes
    | .bsd => B.bsd
    | .hodge => B.hodge
    | .beal => B.beal

/-- Expand the dependent final root into seven named certificate fields. -/
def UniversalFinalRoot.toSeven
    {K : UniversalProducerKernel}
    (R : UniversalFinalRoot K) :
    SevenCertificateBundle K where
  riemann := R.certificate .riemann
  pnp := R.certificate .pnp
  yangMills := R.certificate .yangMills
  navierStokes := R.certificate .navierStokes
  bsd := R.certificate .bsd
  hodge := R.certificate .hodge
  beal := R.certificate .beal

/-- Reassemble named certificate fields into the dependent universal root. -/
def SevenCertificateBundle.toUniversal
    {K : UniversalProducerKernel}
    (B : SevenCertificateBundle K) :
    UniversalFinalRoot K where
  certificate := fun p =>
    match p with
    | .riemann => B.riemann
    | .pnp => B.pnp
    | .yangMills => B.yangMills
    | .navierStokes => B.navierStokes
    | .bsd => B.bsd
    | .hodge => B.hodge
    | .beal => B.beal

/-- Build all seven exact inhabitants from the already-materialized kernel. -/
def buildSevenInhabitants
    (K : UniversalProducerKernel)
    (S : UniversalSeed K) :
    SevenInhabitantBundle K :=
  (buildInhabitantBundle K S).toSeven

/-- Build all seven exact lane certificates from the same seeds. -/
def buildSevenCertificates
    (K : UniversalProducerKernel)
    (S : UniversalSeed K) :
    SevenCertificateBundle K :=
  (buildFinalRoot K S).toSeven

/--
Strict version starting from fixed terminal specifications and exact
materializers.  The target types are fixed before the materializers are
supplied, so the seven-field bundle cannot weaken a terminal obligation.
-/
def resolveExactSevenInhabitants
    (S : UniversalProblemSpec)
    (M : UniversalExactMaterialization S)
    (seed : UniversalProblemSeed S) :
    SevenInhabitantBundle (S.materialize M) :=
  (resolveExactUniversalProblem S M seed).toSeven

/-- Every explicit seven-inhabitant bundle projects to each exact lane. -/
theorem seven_inhabitant_no_escape_riemann
    {K : UniversalProducerKernel}
    (B : SevenInhabitantBundle K) :
    (K.lane .riemann).Inhabitant := B.riemann

theorem seven_inhabitant_no_escape_pnp
    {K : UniversalProducerKernel}
    (B : SevenInhabitantBundle K) :
    (K.lane .pnp).Inhabitant := B.pnp

theorem seven_inhabitant_no_escape_yangMills
    {K : UniversalProducerKernel}
    (B : SevenInhabitantBundle K) :
    (K.lane .yangMills).Inhabitant := B.yangMills

theorem seven_inhabitant_no_escape_navierStokes
    {K : UniversalProducerKernel}
    (B : SevenInhabitantBundle K) :
    (K.lane .navierStokes).Inhabitant := B.navierStokes

theorem seven_inhabitant_no_escape_bsd
    {K : UniversalProducerKernel}
    (B : SevenInhabitantBundle K) :
    (K.lane .bsd).Inhabitant := B.bsd

theorem seven_inhabitant_no_escape_hodge
    {K : UniversalProducerKernel}
    (B : SevenInhabitantBundle K) :
    (K.lane .hodge).Inhabitant := B.hodge

theorem seven_inhabitant_no_escape_beal
    {K : UniversalProducerKernel}
    (B : SevenInhabitantBundle K) :
    (K.lane .beal).Inhabitant := B.beal

/--
External issuance from the explicit seven-field final root.

The external authority/format remains a separate interface; mathematical
construction and issuance are not conflated.
-/
def issueSevenExternalCertificate
    (K : UniversalProducerKernel)
    (B : SevenCertificateBundle K)
    (E : ExternalCertificateInterface K) :
    E.ExternalCertificate :=
  E.issue B.toUniversal

/--
Direct seven-lane closure theorem after exact materialization.

This theorem is constructive: it returns the seven actual inhabitant terms.
Its required input M is precisely the seven problem-specific OPEN_MATH
extraction obligations.
-/
theorem exact_seven_lane_resolution
    (S : UniversalProblemSpec)
    (M : UniversalExactMaterialization S)
    (seed : UniversalProblemSeed S) :
    Nonempty (SevenInhabitantBundle (S.materialize M)) :=
  ⟨resolveExactSevenInhabitants S M seed⟩

#print axioms MCore.ATK.UniversalProducer.resolveExactSevenInhabitants
#print axioms MCore.ATK.UniversalProducer.buildSevenCertificates
#print axioms MCore.ATK.UniversalProducer.issueSevenExternalCertificate
#print axioms MCore.ATK.UniversalProducer.exact_seven_lane_resolution
#print axioms MCore.ATK.UniversalProducer.seven_inhabitant_no_escape_pnp

end MCore.ATK.UniversalProducer
