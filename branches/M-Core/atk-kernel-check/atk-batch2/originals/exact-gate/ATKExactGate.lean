/- Independent, propositional audit gate. No claim that any open conjecture is proved. -/
namespace ATK
structure Lane (Target : Prop) where
  material : Prop
  witness : material
  sound : material → Target

theorem lane_closes {P : Prop} (l : Lane P) : P := l.sound l.witness

theorem seven_close
  {R NS YM BSD H B PNP : Prop}
  (r : Lane R) (ns : Lane NS) (ym : Lane YM)
  (bsd : Lane BSD) (h : Lane H) (b : Lane B)
  (pnp : Lane PNP) :
  R ∧ NS ∧ YM ∧ BSD ∧ H ∧ B ∧ PNP := by
  exact ⟨lane_closes r, lane_closes ns, lane_closes ym,
    lane_closes bsd, lane_closes h, lane_closes b, lane_closes pnp⟩

/- Example of why a generic inhabited wrapper does not prove an arbitrary P. -/
structure WeakClosure where
  premise : Prop
  evidence : premise

theorem weakClosure_inhabited : Nonempty WeakClosure :=
  ⟨⟨True, True.intro⟩⟩
end ATK
