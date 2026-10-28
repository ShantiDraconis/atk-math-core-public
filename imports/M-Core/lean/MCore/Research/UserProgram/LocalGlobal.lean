import Mathlib

namespace MCore.Research.UserProgram

structure Framework where
  X : Type
  Local : Type
  Global : Type
  loc : X → Local
  glob : X → Global

def Reconstructs (F : Framework) (bridge : F.Local → F.Global) : Prop :=
  ∀ x, bridge (F.loc x) = F.glob x

def HasBridge (F : Framework) : Prop :=
  ∃ bridge : F.Local → F.Global, Reconstructs F bridge

def Gap (F : Framework) : Prop := ¬ HasBridge F

theorem gap_iff_no_reconstruction (F : Framework) :
    Gap F ↔ ¬ ∃ bridge : F.Local → F.Global, ∀ x, bridge (F.loc x) = F.glob x := by
  rfl

theorem hasBridge_not_gap {F : Framework} (h : HasBridge F) : ¬ Gap F := by
  exact fun hg => hg h

end MCore.Research.UserProgram
