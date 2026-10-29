/-!
# ATK terminal-proof interfaces (seven lanes)

This file is a *proposition-level specification*, not a claim of the seven
open mathematical conjectures. No axioms, sorry, admit, or synthetic witnesses
are introduced. Existing certified files remain unchanged.

A terminal certificate is constructible only from actual proofs of the seven
material propositions, provided as parameters by the caller.
-/

namespace ATK.Terminal

universe u

structure SevenEndpoints where
  beal : Prop
  hodge : Prop
  yangMills : Prop
  riemann : Prop
  pNeNP : Prop
  bsd : Prop
  navierStokes : Prop

def MaterialComplete (E : SevenEndpoints) : Prop :=
  E.beal ∧ E.hodge ∧ E.yangMills ∧ E.riemann ∧
  E.pNeNP ∧ E.bsd ∧ E.navierStokes

structure TerminalProofs (E : SevenEndpoints) where
  beal : E.beal
  hodge : E.hodge
  yangMills : E.yangMills
  riemann : E.riemann
  pNeNP : E.pNeNP
  bsd : E.bsd
  navierStokes : E.navierStokes

theorem terminalProofs_iff_materialComplete (E : SevenEndpoints) :
    Nonempty (TerminalProofs E) ↔ MaterialComplete E := by
  constructor
  · rintro ⟨h⟩
    exact ⟨h.beal, h.hodge, h.yangMills, h.riemann,
      h.pNeNP, h.bsd, h.navierStokes⟩
  · rintro ⟨hb, hh, hy, hr, hp, hbsd, hns⟩
    exact ⟨⟨hb, hh, hy, hr, hp, hbsd, hns⟩⟩

theorem close_from_material
    (E : SevenEndpoints)
    (hb : E.beal) (hh : E.hodge) (hy : E.yangMills)
    (hr : E.riemann) (hp : E.pNeNP) (hbsd : E.bsd)
    (hns : E.navierStokes) : MaterialComplete E :=
  ⟨hb, hh, hy, hr, hp, hbsd, hns⟩

end ATK.Terminal
