import Mathlib.Order.Basic

/-!
# Condicional — Birch e Swinnerton-Dyer

A Mathlib tem curvas de Weierstrass, mas não a função L de E nem o posto de Mordell–Weil;
o enunciado é relativo a um `BSDModel` (fidelidade: PARAMÉTRICA).

Forma condicional:

  `GrossZagierKolyvagin M → RankOpen M → RefinedOpen M → BSDFull M`

* `GrossZagierKolyvagin` (PONTE; Gross–Zagier 1986, Kolyvagin 1988–89, modularidade
  Wiles/BCDT 2001): posto analítico ≤ 1 ⇒ posto = posto analítico.
* `RankOpen` (ABERTA): o mesmo para posto analítico ≥ 2.
* `RefinedOpen` (ABERTA): Ш finito e a fórmula do termo líder, para toda E/ℚ.
  O `ATK.BSD.sha_recovery` só isola #Ш **supondo** essa fórmula.

O terminal do `m-core-bsd` exige ligar dados genuínos de curvas elípticas antes; este
arquivo deixa essa ligação explícita como os campos do modelo.
-/

namespace ATK.Conditional.BSD

universe u

/-- Interface: curvas elípticas sobre ℚ com posto algébrico e analítico. -/
structure BSDModel where
  Curve : Type u
  /-- posto de Mordell–Weil de E(ℚ) -/
  rank : Curve → ℕ
  /-- ord_{s=1} L(E, s) -/
  analyticRank : Curve → ℕ
  /-- Ш(E) finito e L^{(r)}(E,1)/r! = Ω · Reg · ∏ c_p · #Ш / #tors² -/
  RefinedFormula : Curve → Prop

/-- Parte de posto do enunciado. -/
def BSDRank (M : BSDModel.{u}) : Prop :=
  ∀ E, M.analyticRank E = M.rank E

/-- Enunciado-alvo completo (posto + fórmula refinada). -/
def BSDFull (M : BSDModel.{u}) : Prop :=
  BSDRank M ∧ ∀ E, M.RefinedFormula E

/-- PONTE: Gross–Zagier–Kolyvagin. -/
def GrossZagierKolyvagin (M : BSDModel.{u}) : Prop :=
  ∀ E, M.analyticRank E ≤ 1 → M.rank E = M.analyticRank E

/-- HIPÓTESE ABERTA: posto analítico ≥ 2. -/
def RankOpen (M : BSDModel.{u}) : Prop :=
  ∀ E, 2 ≤ M.analyticRank E → M.rank E = M.analyticRank E

/-- HIPÓTESE ABERTA: fórmula refinada. -/
def RefinedOpen (M : BSDModel.{u}) : Prop :=
  ∀ E, M.RefinedFormula E

theorem bsd_rank_conditional {M : BSDModel.{u}}
    (hBridge : GrossZagierKolyvagin M) (hOpen : RankOpen M) : BSDRank M := by
  intro E
  by_cases h : M.analyticRank E ≤ 1
  · exact (hBridge E h).symm
  · exact (hOpen E (by omega)).symm

/-- **Condicional BSD.** -/
theorem bsd_conditional {M : BSDModel.{u}}
    (hBridge : GrossZagierKolyvagin M) (hRank : RankOpen M) (hRefined : RefinedOpen M) :
    BSDFull M :=
  ⟨bsd_rank_conditional hBridge hRank, hRefined⟩

end ATK.Conditional.BSD

#print axioms ATK.Conditional.BSD.bsd_rank_conditional
#print axioms ATK.Conditional.BSD.bsd_conditional
