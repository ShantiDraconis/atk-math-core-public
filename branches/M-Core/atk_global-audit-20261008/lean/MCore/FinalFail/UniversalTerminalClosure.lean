import MCore.FinalFail.DirectProducerCuts

namespace MCore.FinalFail.Universal

/-!
# Universal terminal closure law

This module formalizes the only admissible global composition rule for the seven
terminal lanes: a universal root is inhabited exactly when every terminal
proposition is inhabited.  It deliberately contains no mathematical producer
for any lane.

The point is fail-closed bookkeeping at the kernel level:
* packing all seven terminal inhabitants yields the universal bundle;
* every universal bundle projects back to each terminal inhabitant;
* componentwise strengthening maps a bundle forward;
* therefore no wrapper, renamed hypothesis, or aggregate certificate can bypass
  a missing terminal inhabitant.
-/

structure TerminalInhabitants
    (Riemann Beal PvsNP NavierStokes Hodge BSD YangMills : Prop) : Prop where
  riemann : Riemann
  beal : Beal
  pVsNP : PvsNP
  navierStokes : NavierStokes
  hodge : Hodge
  bsd : BSD
  yangMills : YangMills

def AllSeven
    (Riemann Beal PvsNP NavierStokes Hodge BSD YangMills : Prop) : Prop :=
  Riemann ∧ Beal ∧ PvsNP ∧ NavierStokes ∧ Hodge ∧ BSD ∧ YangMills

theorem terminalInhabitants_iff_allSeven
    (Riemann Beal PvsNP NavierStokes Hodge BSD YangMills : Prop) :
    TerminalInhabitants Riemann Beal PvsNP NavierStokes Hodge BSD YangMills ↔
      AllSeven Riemann Beal PvsNP NavierStokes Hodge BSD YangMills := by
  constructor
  · intro h
    exact ⟨h.riemann, h.beal, h.pVsNP, h.navierStokes, h.hodge, h.bsd, h.yangMills⟩
  · rintro ⟨hr, hb, hp, hn, hh, hd, hy⟩
    exact ⟨hr, hb, hp, hn, hh, hd, hy⟩

def map
    {Riemann Beal PvsNP NavierStokes Hodge BSD YangMills : Prop}
    {Riemann' Beal' PvsNP' NavierStokes' Hodge' BSD' YangMills' : Prop}
    (fR : Riemann → Riemann')
    (fB : Beal → Beal')
    (fP : PvsNP → PvsNP')
    (fN : NavierStokes → NavierStokes')
    (fH : Hodge → Hodge')
    (fD : BSD → BSD')
    (fY : YangMills → YangMills')
    (h : TerminalInhabitants Riemann Beal PvsNP NavierStokes Hodge BSD YangMills) :
    TerminalInhabitants Riemann' Beal' PvsNP' NavierStokes' Hodge' BSD' YangMills' :=
  ⟨fR h.riemann, fB h.beal, fP h.pVsNP, fN h.navierStokes,
   fH h.hodge, fD h.bsd, fY h.yangMills⟩

theorem no_escape_riemann
    {Riemann Beal PvsNP NavierStokes Hodge BSD YangMills : Prop}
    (h : TerminalInhabitants Riemann Beal PvsNP NavierStokes Hodge BSD YangMills) :
    Riemann := h.riemann

theorem no_escape_beal
    {Riemann Beal PvsNP NavierStokes Hodge BSD YangMills : Prop}
    (h : TerminalInhabitants Riemann Beal PvsNP NavierStokes Hodge BSD YangMills) :
    Beal := h.beal

theorem no_escape_pVsNP
    {Riemann Beal PvsNP NavierStokes Hodge BSD YangMills : Prop}
    (h : TerminalInhabitants Riemann Beal PvsNP NavierStokes Hodge BSD YangMills) :
    PvsNP := h.pVsNP

theorem no_escape_navierStokes
    {Riemann Beal PvsNP NavierStokes Hodge BSD YangMills : Prop}
    (h : TerminalInhabitants Riemann Beal PvsNP NavierStokes Hodge BSD YangMills) :
    NavierStokes := h.navierStokes

theorem no_escape_hodge
    {Riemann Beal PvsNP NavierStokes Hodge BSD YangMills : Prop}
    (h : TerminalInhabitants Riemann Beal PvsNP NavierStokes Hodge BSD YangMills) :
    Hodge := h.hodge

theorem no_escape_bsd
    {Riemann Beal PvsNP NavierStokes Hodge BSD YangMills : Prop}
    (h : TerminalInhabitants Riemann Beal PvsNP NavierStokes Hodge BSD YangMills) :
    BSD := h.bsd

theorem no_escape_yangMills
    {Riemann Beal PvsNP NavierStokes Hodge BSD YangMills : Prop}
    (h : TerminalInhabitants Riemann Beal PvsNP NavierStokes Hodge BSD YangMills) :
    YangMills := h.yangMills

/-- The universal aggregation layer has exactly seven direct producer cuts. -/
theorem universal_cut_cardinality :
    MCore.FinalFail.Semantic.directProducerCutCount = 7 :=
  MCore.FinalFail.Semantic.directProducerCutCount_eq_seven

/-- At the audited frontier, aggregation itself produces none of the seven
material inhabitants. -/
theorem universal_aggregation_is_fail_closed :
    MCore.FinalFail.Semantic.producedDirectCount = 0 ∧
    MCore.FinalFail.Semantic.openDirectCount = 7 := by
  exact ⟨MCore.FinalFail.Semantic.producedDirectCount_eq_zero,
    MCore.FinalFail.Semantic.openDirectCount_eq_seven⟩

end MCore.FinalFail.Universal
