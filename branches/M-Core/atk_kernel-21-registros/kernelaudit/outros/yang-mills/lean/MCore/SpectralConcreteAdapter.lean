import MCore.SpectralCore
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace MCore

/-- Concrete analytic realization kept separate from K14's dependency-light
interface.  It records only the structure needed to map a genuine Hilbert-space
model into the existing certified chain. -/
structure ConcreteHilbertAdapter
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) where
  HilbertState : Type
  toAbstract : HilbertState → D.State
  physical : HilbertState → Prop
  vacuumOrthogonal : HilbertState → Prop
  inDomain : HilbertState → Prop
  hamiltonian : HilbertState → HilbertState
  rate : D.Scale
  ratePositive : G.positive rate
  mapsPhysical : ∀ psi, physical psi → D.physical (toAbstract psi)
  mapsOrthogonal : ∀ psi, vacuumOrthogonal psi → D.orthogonalToVacuum (toAbstract psi)
  mapsDomain : ∀ psi, inDomain psi → H.domain (toAbstract psi)
  intertwines : ∀ (psi) (hd : inDomain psi),
    toAbstract (hamiltonian psi) = H.act (toAbstract psi) (mapsDomain psi hd)
  spectralLowerBound : ∀ psi,
    physical psi → vacuumOrthogonal psi → inDomain psi →
      G.gapBound rate (toAbstract psi) (toAbstract (hamiltonian psi))

/-- Everything after a concrete spectral lower bound is mechanical. -/
theorem concrete_adapter_mass_gap
    {D : K14PhysicalHilbertData}
    {H : K14HamiltonianOperator D}
    {G : K14GapScale D}
    (A : ConcreteHilbertAdapter D H G)
    (surjectivePhysical : ∀ psi : D.State,
      D.physical psi → D.orthogonalToVacuum psi → H.domain psi →
      ∃ phi : A.HilbertState,
        A.toAbstract phi = psi ∧ A.physical phi ∧
        A.vacuumOrthogonal phi ∧ A.inDomain phi) :
    K14MassGap D H G A.rate := by
  refine ⟨A.ratePositive, ?_⟩
  intro psi hdom hp ho
  obtain ⟨phi, hphi, hpp, hop, hdp⟩ := surjectivePhysical psi hp ho hdom
  subst psi
  have hgap := A.spectralLowerBound phi hpp hop hdp
  rw [A.intertwines phi hdp] at hgap
  exact hgap

/-- The remaining scientific edge is deliberately explicit: construct a
concrete adapter and prove coverage/density of the physical vacuum-orthogonal
domain. -/
def ConcreteSpectralOpenBridge
    (D : K14PhysicalHilbertData)
    (H : K14HamiltonianOperator D)
    (G : K14GapScale D) : Prop :=
  ∃ A : ConcreteHilbertAdapter D H G,
    ∀ psi : D.State,
      D.physical psi → D.orthogonalToVacuum psi → H.domain psi →
      ∃ phi : A.HilbertState,
        A.toAbstract phi = psi ∧ A.physical phi ∧
        A.vacuumOrthogonal phi ∧ A.inDomain phi

end MCore
