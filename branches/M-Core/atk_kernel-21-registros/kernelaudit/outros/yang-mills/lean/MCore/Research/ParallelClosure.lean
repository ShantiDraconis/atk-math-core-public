namespace MCore.Research

structure ExactResidual (Parent Child : Prop) where
  forward : Parent → Child
  backward : Child → Parent

structure ParallelAttack (Goal : Prop) where
  Residual : Prop
  exact : ExactResidual Goal Residual

theorem return_to_primary {Goal : Prop} (a : ParallelAttack Goal)
    (h : a.Residual) : Goal := a.exact.backward h

end MCore.Research
