import Mathlib
import MCore.FinalFail.SevenProblemSignatures
import MCore.FinalFail.UniversalTerminalClosure

namespace MCore.FinalFail.SevenTerminalParameterLaw

/-!
# Seven terminal parameter law

This file separates two levels which must not be conflated:

1. **Logical closure laws** proved here without any conjectural axiom.
2. **Material inhabitants** of the seven open problems, represented by model fields.

The theorems below say exactly what certifies or refutes each terminal predicate
*once the mathematical model has been instantiated*.  They do **not** construct
a Riemann zero theorem, a Yang--Mills mass gap, a Navier--Stokes global solution,
an algebraic Hodge cycle, BSD, a P != NP lower bound, or a Beal proof.
-/

universe u v

/-- The four terminal closure geometries used by the seven lanes. -/
inductive TerminalMode where
  | zero
  | positiveGap
  | globalExclusion
  | realization
  deriving DecidableEq, Repr

/-- Structural classification only; it contains no proof of a conjecture. -/
def terminalModeOf : ProblemId → TerminalMode
  | .riemann => .zero
  | .bsd => .zero
  | .yangMills => .positiveGap
  | .beal => .positiveGap
  | .navierStokes => .globalExclusion
  | .pVsNP => .globalExclusion
  | .hodge => .realization

theorem terminalMode_total (p : ProblemId) :
    ∃ m : TerminalMode, terminalModeOf p = m :=
  ⟨terminalModeOf p, rfl⟩

/-! ## Generic certification/refutation law -/

/-- Universal certification of a terminal predicate. -/
def Certifies {X : Type u} (P : X → Prop) : Prop :=
  ∀ x, P x

/-- A material counterexample to a universal terminal predicate. -/
def Refutes {X : Type u} (P : X → Prop) : Prop :=
  ∃ x, ¬ P x

/-- One counterexample always destroys universal certification. -/
theorem refutes_not_certifies {X : Type u} {P : X → Prop}
    (h : Refutes P) : ¬ Certifies P := by
  rintro hcert
  rcases h with ⟨x, hx⟩
  exact hx (hcert x)

/-- Classically, failure of a universal terminal certification is exactly the
existence of a counterexample. -/
theorem not_certifies_iff_refutes {X : Type u} (P : X → Prop) :
    ¬ Certifies P ↔ Refutes P := by
  classical
  simp [Certifies, Refutes]

/-! ## Riemann: vanishing of critical-line defect -/

structure RiemannModel where
  Zero : Type u
  nontrivialZero : Zero → Prop
  re : Zero → ℝ

noncomputable def riemannDefect (M : RiemannModel) (z : M.Zero) : ℝ :=
  M.re z - ((1 : ℝ) / 2)

def RiemannCertifies (M : RiemannModel) : Prop :=
  ∀ z, M.nontrivialZero z → riemannDefect M z = 0

def RiemannRefutes (M : RiemannModel) : Prop :=
  ∃ z, M.nontrivialZero z ∧ riemannDefect M z ≠ 0

theorem riemann_defect_zero_iff_critical_line
    (M : RiemannModel) (z : M.Zero) :
    riemannDefect M z = 0 ↔ M.re z = ((1 : ℝ) / 2) := by
  unfold riemannDefect
  exact sub_eq_zero

theorem not_riemannCertifies_iff_riemannRefutes (M : RiemannModel) :
    ¬ RiemannCertifies M ↔ RiemannRefutes M := by
  classical
  simp [RiemannCertifies, RiemannRefutes]

theorem riemann_cert_refute_disjoint (M : RiemannModel) :
    ¬ (RiemannCertifies M ∧ RiemannRefutes M) := by
  rintro ⟨hc, z, hz, hne⟩
  exact hne (hc z hz)

/-! ## Yang--Mills: strictly positive uniform spectral gap -/

structure YangMillsModel where
  State : Type u
  excited : State → Prop
  gap : State → ℝ

/-- Certification means one positive constant works uniformly for every
physical excited state represented by the model. -/
def YangMillsCertifies (M : YangMillsModel) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ s, M.excited s → m ≤ M.gap s

/-- Refutation of the positive-gap predicate means gaps can be found below
*every* positive proposed lower bound. -/
def YangMillsRefutes (M : YangMillsModel) : Prop :=
  ∀ m : ℝ, 0 < m → ∃ s, M.excited s ∧ M.gap s < m

theorem not_yangMillsCertifies_iff_yangMillsRefutes (M : YangMillsModel) :
    ¬ YangMillsCertifies M ↔ YangMillsRefutes M := by
  classical
  simp [YangMillsCertifies, YangMillsRefutes, not_le]

theorem yangMills_cert_refute_disjoint (M : YangMillsModel) :
    ¬ (YangMillsCertifies M ∧ YangMillsRefutes M) := by
  rintro ⟨⟨m, hm, hgap⟩, href⟩
  rcases href m hm with ⟨s, hs, hlt⟩
  exact (not_lt_of_ge (hgap s hs)) hlt

/-! ## Navier--Stokes: global smooth continuation versus a finite obstruction -/

structure NavierStokesModel where
  InitialData : Type u
  admissible : InitialData → Prop
  globalSmooth : InitialData → Prop

def NavierStokesCertifies (M : NavierStokesModel) : Prop :=
  ∀ u₀, M.admissible u₀ → M.globalSmooth u₀

def NavierStokesRefutes (M : NavierStokesModel) : Prop :=
  ∃ u₀, M.admissible u₀ ∧ ¬ M.globalSmooth u₀

theorem not_navierStokesCertifies_iff_navierStokesRefutes
    (M : NavierStokesModel) :
    ¬ NavierStokesCertifies M ↔ NavierStokesRefutes M := by
  classical
  simp [NavierStokesCertifies, NavierStokesRefutes]

theorem navierStokes_cert_refute_disjoint (M : NavierStokesModel) :
    ¬ (NavierStokesCertifies M ∧ NavierStokesRefutes M) := by
  rintro ⟨hc, u₀, hu, hbad⟩
  exact hbad (hc u₀ hu)

/-! ## Hodge: every eligible class has an algebraic realization -/

structure HodgeModel where
  Class : Type u
  Cycle : Type v
  eligible : Class → Prop
  realizes : Cycle → Class → Prop

def HodgeCertifies (M : HodgeModel) : Prop :=
  ∀ α, M.eligible α → ∃ Z, M.realizes Z α

def HodgeRefutes (M : HodgeModel) : Prop :=
  ∃ α, M.eligible α ∧ ∀ Z, ¬ M.realizes Z α

theorem not_hodgeCertifies_iff_hodgeRefutes (M : HodgeModel) :
    ¬ HodgeCertifies M ↔ HodgeRefutes M := by
  classical
  simp [HodgeCertifies, HodgeRefutes]

theorem hodge_cert_refute_disjoint (M : HodgeModel) :
    ¬ (HodgeCertifies M ∧ HodgeRefutes M) := by
  rintro ⟨hc, α, hα, hnone⟩
  rcases hc α hα with ⟨Z, hZ⟩
  exact hnone Z hZ

/-! ## BSD: rank equality plus the refined formula -/

structure BSDModel where
  Curve : Type u
  algebraicRank : Curve → ℕ
  analyticRank : Curve → ℕ
  refinedFormula : Curve → Prop

def bsdRankDefect (M : BSDModel) (E : M.Curve) : ℤ :=
  (M.algebraicRank E : ℤ) - (M.analyticRank E : ℤ)

def BSDCertifies (M : BSDModel) : Prop :=
  ∀ E, bsdRankDefect M E = 0 ∧ M.refinedFormula E

def BSDRefutes (M : BSDModel) : Prop :=
  ∃ E, bsdRankDefect M E ≠ 0 ∨ ¬ M.refinedFormula E

theorem bsd_rank_defect_zero_iff (M : BSDModel) (E : M.Curve) :
    bsdRankDefect M E = 0 ↔ M.algebraicRank E = M.analyticRank E := by
  unfold bsdRankDefect
  omega

theorem not_bsdCertifies_iff_bsdRefutes (M : BSDModel) :
    ¬ BSDCertifies M ↔ BSDRefutes M := by
  classical
  constructor
  · intro h
    by_contra href
    apply h
    intro E
    constructor
    · by_contra hd
      exact href ⟨E, Or.inl hd⟩
    · by_contra hf
      exact href ⟨E, Or.inr hf⟩
  · rintro ⟨E, href⟩ hcert
    rcases hcert E with ⟨hrank, hrefined⟩
    exact href.elim (fun h => h hrank) (fun h => h hrefined)

theorem bsd_cert_refute_disjoint (M : BSDModel) :
    ¬ (BSDCertifies M ∧ BSDRefutes M) := by
  rintro ⟨hc, E, href⟩
  rcases hc E with ⟨hrank, hrefined⟩
  exact href.elim (fun h => h hrank) (fun h => h hrefined)

/-! ## P versus NP: exclusion of every polynomial SAT decider -/

structure PvsNPModel where
  Machine : Type u
  polynomialSATDecider : Machine → Prop

def PvsNPCertifies (M : PvsNPModel) : Prop :=
  ∀ machine, ¬ M.polynomialSATDecider machine

def PvsNPRefutes (M : PvsNPModel) : Prop :=
  ∃ machine, M.polynomialSATDecider machine

theorem not_pVsNPCertifies_iff_pVsNPRefutes (M : PvsNPModel) :
    ¬ PvsNPCertifies M ↔ PvsNPRefutes M := by
  classical
  simp [PvsNPCertifies, PvsNPRefutes]

theorem pVsNP_cert_refute_disjoint (M : PvsNPModel) :
    ¬ (PvsNPCertifies M ∧ PvsNPRefutes M) := by
  rintro ⟨hc, machine, hm⟩
  exact hc machine hm

/-! ## Beal: exclusion of primitive admissible solutions -/

structure BealModel where
  Candidate : Type u
  admissibleEquation : Candidate → Prop
  commonGCD : Candidate → ℕ

def bealDefect (M : BealModel) (c : M.Candidate) : ℕ :=
  M.commonGCD c - 1

def BealCertifies (M : BealModel) : Prop :=
  ∀ c, M.admissibleEquation c → 1 < M.commonGCD c

def BealRefutes (M : BealModel) : Prop :=
  ∃ c, M.admissibleEquation c ∧ M.commonGCD c ≤ 1

theorem not_bealCertifies_iff_bealRefutes (M : BealModel) :
    ¬ BealCertifies M ↔ BealRefutes M := by
  classical
  simp [BealCertifies, BealRefutes, not_lt]

theorem beal_cert_refute_disjoint (M : BealModel) :
    ¬ (BealCertifies M ∧ BealRefutes M) := by
  rintro ⟨hc, c, hcand, hle⟩
  exact (not_lt_of_ge hle) (hc c hcand)

/-! ## Global seven-lane theorem -/

structure SevenModels where
  riemann : RiemannModel
  yangMills : YangMillsModel
  navierStokes : NavierStokesModel
  hodge : HodgeModel
  bsd : BSDModel
  pVsNP : PvsNPModel
  beal : BealModel

def GlobalCertifies (M : SevenModels) : Prop :=
  RiemannCertifies M.riemann ∧
  YangMillsCertifies M.yangMills ∧
  NavierStokesCertifies M.navierStokes ∧
  HodgeCertifies M.hodge ∧
  BSDCertifies M.bsd ∧
  PvsNPCertifies M.pVsNP ∧
  BealCertifies M.beal

def GlobalRefutes (M : SevenModels) : Prop :=
  RiemannRefutes M.riemann ∨
  YangMillsRefutes M.yangMills ∨
  NavierStokesRefutes M.navierStokes ∨
  HodgeRefutes M.hodge ∨
  BSDRefutes M.bsd ∨
  PvsNPRefutes M.pVsNP ∨
  BealRefutes M.beal

/-- The global root is refuted exactly when at least one of the seven terminal
predicates has a material counterexample.  The proof is deliberately explicit,
so no simplifier behavior hides the seven producer cuts. -/
theorem not_globalCertifies_iff_globalRefutes (M : SevenModels) :
    ¬ GlobalCertifies M ↔ GlobalRefutes M := by
  classical
  constructor
  · intro hglobal
    by_cases hr : RiemannCertifies M.riemann
    · by_cases hy : YangMillsCertifies M.yangMills
      · by_cases hn : NavierStokesCertifies M.navierStokes
        · by_cases hh : HodgeCertifies M.hodge
          · by_cases hd : BSDCertifies M.bsd
            · by_cases hp : PvsNPCertifies M.pVsNP
              · by_cases hb : BealCertifies M.beal
                · exact False.elim (hglobal ⟨hr, hy, hn, hh, hd, hp, hb⟩)
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    ((not_bealCertifies_iff_bealRefutes M.beal).1 hb))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ((not_pVsNPCertifies_iff_pVsNPRefutes M.pVsNP).1 hp))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ((not_bsdCertifies_iff_bsdRefutes M.bsd).1 hd)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl
              ((not_hodgeCertifies_iff_hodgeRefutes M.hodge).1 hh))))
        · exact Or.inr (Or.inr (Or.inl
            ((not_navierStokesCertifies_iff_navierStokesRefutes M.navierStokes).1 hn)))
      · exact Or.inr (Or.inl
          ((not_yangMillsCertifies_iff_yangMillsRefutes M.yangMills).1 hy))
    · exact Or.inl ((not_riemannCertifies_iff_riemannRefutes M.riemann).1 hr)
  · intro href hcert
    rcases hcert with ⟨hr, hy, hn, hh, hd, hp, hb⟩
    rcases href with hR | hY | hN | hH | hD | hP | hB
    · exact ((not_riemannCertifies_iff_riemannRefutes M.riemann).2 hR) hr
    · exact ((not_yangMillsCertifies_iff_yangMillsRefutes M.yangMills).2 hY) hy
    · exact ((not_navierStokesCertifies_iff_navierStokesRefutes M.navierStokes).2 hN) hn
    · exact ((not_hodgeCertifies_iff_hodgeRefutes M.hodge).2 hH) hh
    · exact ((not_bsdCertifies_iff_bsdRefutes M.bsd).2 hD) hd
    · exact ((not_pVsNPCertifies_iff_pVsNPRefutes M.pVsNP).2 hP) hp
    · exact ((not_bealCertifies_iff_bealRefutes M.beal).2 hB) hb

/-- A global certificate projects to every lane. -/
theorem global_projects_all (M : SevenModels) (h : GlobalCertifies M) :
    RiemannCertifies M.riemann ∧
    YangMillsCertifies M.yangMills ∧
    NavierStokesCertifies M.navierStokes ∧
    HodgeCertifies M.hodge ∧
    BSDCertifies M.bsd ∧
    PvsNPCertifies M.pVsNP ∧
    BealCertifies M.beal :=
  h

/-- No aggregate wrapper can certify the global root while one terminal lane is
materially refuted. -/
theorem global_cert_refute_disjoint (M : SevenModels) :
    ¬ (GlobalCertifies M ∧ GlobalRefutes M) := by
  intro h
  exact (not_globalCertifies_iff_globalRefutes M).2 h.2 h.1

/-- Bridge into the existing fail-closed universal bundle. -/
def toUniversalTerminalInhabitants (M : SevenModels)
    (h : GlobalCertifies M) :
    MCore.FinalFail.Universal.TerminalInhabitants
      (RiemannCertifies M.riemann)
      (BealCertifies M.beal)
      (PvsNPCertifies M.pVsNP)
      (NavierStokesCertifies M.navierStokes)
      (HodgeCertifies M.hodge)
      (BSDCertifies M.bsd)
      (YangMillsCertifies M.yangMills) := by
  rcases h with ⟨hr, hy, hn, hh, hd, hp, hb⟩
  exact ⟨hr, hb, hp, hn, hh, hd, hy⟩

end MCore.FinalFail.SevenTerminalParameterLaw
