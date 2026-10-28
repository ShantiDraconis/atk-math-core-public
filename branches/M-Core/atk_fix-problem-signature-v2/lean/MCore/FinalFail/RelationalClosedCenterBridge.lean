import MCore.FinalFail.RelationalCenterBridge

namespace MCore.FinalFail

/--
The four relational arrows are total on their source types.
This is the exact amount of data needed to induce maps between the
existence propositions Nonempty Start, Nonempty Center and Nonempty Finish.
-/
structure RelationalTotality (H : RelationalHardAtom) where
  start_to_center_total :
    ∀ s : H.Start, ∃ c : H.Center, H.start_to_center s c
  center_to_start_total :
    ∀ c : H.Center, ∃ s : H.Start, H.center_to_start c s
  center_to_finish_total :
    ∀ c : H.Center, ∃ f : H.Finish, H.center_to_finish c f
  finish_to_center_total :
    ∀ f : H.Finish, ∃ c : H.Center, H.finish_to_center f c

/--
Single-valuedness is a separate strengthening. It is not required merely to
obtain ClosedCenterHard at the proposition/existence level.
-/
structure RelationalSingleValued (H : RelationalHardAtom) where
  start_to_center_unique :
    ∀ s : H.Start, ∀ c₁ c₂ : H.Center,
      H.start_to_center s c₁ → H.start_to_center s c₂ → c₁ = c₂
  center_to_start_unique :
    ∀ c : H.Center, ∀ s₁ s₂ : H.Start,
      H.center_to_start c s₁ → H.center_to_start c s₂ → s₁ = s₂
  center_to_finish_unique :
    ∀ c : H.Center, ∀ f₁ f₂ : H.Finish,
      H.center_to_finish c f₁ → H.center_to_finish c f₂ → f₁ = f₂
  finish_to_center_unique :
    ∀ f : H.Finish, ∀ c₁ c₂ : H.Center,
      H.finish_to_center f c₁ → H.finish_to_center f c₂ → c₁ = c₂

namespace RelationalTotality

/--
Total relational arrows induce the existing ClosedCenterHard architecture on
existence propositions. No global choice function and no single-valuedness
hypothesis is needed because each implication consumes one concrete witness
and destructs one corresponding existential locally.
-/
def toClosedCenterHard
    {H : RelationalHardAtom}
    (T : RelationalTotality H) :
    ClosedCenterHard
      (Nonempty H.Start)
      (Nonempty H.Center)
      (Nonempty H.Finish) where
  start_to_center := by
    rintro ⟨s⟩
    rcases T.start_to_center_total s with ⟨c, _⟩
    exact ⟨c⟩
  center_to_start := by
    rintro ⟨c⟩
    rcases T.center_to_start_total c with ⟨s, _⟩
    exact ⟨s⟩
  center_to_finish := by
    rintro ⟨c⟩
    rcases T.center_to_finish_total c with ⟨f, _⟩
    exact ⟨f⟩
  finish_to_center := by
    rintro ⟨f⟩
    rcases T.finish_to_center_total f with ⟨c, _⟩
    exact ⟨c⟩

/--
The induced proposition-level closed center does not erase branch multiplicity.
FailAt remains a separate property of a concrete center and can coexist with
the induced ClosedCenterHard object.
-/
theorem closedCenterHard_coexists_with_failAt
    {H : RelationalHardAtom}
    (T : RelationalTotality H)
    (c : H.Center)
    (hFail : H.FailAt c) :
    Nonempty
        (ClosedCenterHard
          (Nonempty H.Start)
          (Nonempty H.Center)
          (Nonempty H.Finish)) ∧
      H.FailAt c := by
  exact ⟨⟨T.toClosedCenterHard⟩, hFail⟩

end RelationalTotality

/--
If the scientific application needs actual underlying functions rather than
only proposition-level existence implications, those functions must be
provided explicitly together with relation fidelity. This avoids smuggling a
choice oracle into the core.
-/
structure RelationalFunctionalWitness (H : RelationalHardAtom) where
  startToCenter : H.Start → H.Center
  centerToStart : H.Center → H.Start
  centerToFinish : H.Center → H.Finish
  finishToCenter : H.Finish → H.Center
  startToCenter_spec :
    ∀ s : H.Start, H.start_to_center s (startToCenter s)
  centerToStart_spec :
    ∀ c : H.Center, H.center_to_start c (centerToStart c)
  centerToFinish_spec :
    ∀ c : H.Center, H.center_to_finish c (centerToFinish c)
  finishToCenter_spec :
    ∀ f : H.Finish, H.finish_to_center f (finishToCenter f)

/-- Every explicit functional witness supplies relational totality. -/
def RelationalFunctionalWitness.toTotality
    {H : RelationalHardAtom}
    (F : RelationalFunctionalWitness H) :
    RelationalTotality H where
  start_to_center_total := fun s => ⟨F.startToCenter s, F.startToCenter_spec s⟩
  center_to_start_total := fun c => ⟨F.centerToStart c, F.centerToStart_spec c⟩
  center_to_finish_total := fun c => ⟨F.centerToFinish c, F.centerToFinish_spec c⟩
  finish_to_center_total := fun f => ⟨F.finishToCenter f, F.finishToCenter_spec f⟩

/-- Therefore an explicit function-level realization induces ClosedCenterHard
without using Classical.choice. -/
def RelationalFunctionalWitness.toClosedCenterHard
    {H : RelationalHardAtom}
    (F : RelationalFunctionalWitness H) :
    ClosedCenterHard
      (Nonempty H.Start)
      (Nonempty H.Center)
      (Nonempty H.Finish) :=
  F.toTotality.toClosedCenterHard

#print axioms MCore.FinalFail.RelationalTotality.toClosedCenterHard
#print axioms MCore.FinalFail.RelationalTotality.closedCenterHard_coexists_with_failAt
#print axioms MCore.FinalFail.RelationalFunctionalWitness.toTotality
#print axioms MCore.FinalFail.RelationalFunctionalWitness.toClosedCenterHard

end MCore.FinalFail
