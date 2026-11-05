import ATK.FechamentoO1

/-!
# `D_∞ = inf_N D_N`: o limite de Báez-Duarte como número

`D_N` é decrescente e limitada por baixo (`ATK.RiemannConcrete.DN_antitone`, `DN_nonneg`), então
converge para `D_∞ = ⨅ N, D_N` (`ATK.RiemannConcrete.DN_tendsto_iInf`). Este arquivo dá nome a
`D_∞` e junta o que o kernel já sabe sobre ele:

* `dInf_nonneg`, `dInf_le_one`: `0 ≤ D_∞ ≤ 1`;
* `tendsto_dInf`, `dInf_eq_zero_iff`: `D_N → D_∞`, e `D_N → 0 ⟺ D_∞ = 0`;
* `piso_no_limite`: um zero `ρ` com `1/2 < Re ρ < 1` dá `m(ρ)² ≤ D_∞` (a condensação passa ao
  limite), e `dInf_pos_of_zeroFora`: **um zero fora da linha força `D_∞ > 0`**;
* `rh_of_dInf_eq_zero`: `D_∞ = 0 → RH` (B1, provada);
* `rh_iff_dInf_eq_zero`: **com `NecessidadeRH` como hipótese**, `RH ⟺ D_∞ = 0`.

`NecessidadeRH` tem a força de RH quando combinada com B1; aqui ela é hipótese, não axioma. Nada
neste arquivo prova RH nem a refuta.
-/

open Filter Topology
open ATK.Conditional.Riemann ATK.ForaDaLinha ATK.FechamentoO1 ATK.BaezDuarteBridge

namespace ATK.DInfinito

/-- `D_∞ = inf_N D_N`. -/
noncomputable def dInf : ℝ := ⨅ N, DN N

theorem dInf_nonneg : 0 ≤ dInf := le_ciInf DN_nonneg

theorem dInf_le_one : dInf ≤ 1 :=
  (ciInf_le ⟨0, by rintro _ ⟨N, rfl⟩; exact DN_nonneg N⟩ 0).trans (ATK.RiemannConcrete.DN_le_one 0)

theorem tendsto_dInf : Tendsto DN atTop (𝓝 dInf) := ATK.RiemannConcrete.DN_tendsto_iInf

theorem dInf_eq_zero_iff : Tendsto DN atTop (𝓝 0) ↔ dInf = 0 :=
  ATK.RiemannConcrete.O1_iff_iInf_zero

/-- **A condensação passa ao limite**: `m(ρ)² ≤ D_∞`. -/
theorem piso_no_limite {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    m ρ ^ 2 ≤ dInf :=
  le_ciInf (piso_DN hz h0 h1)

/-- **Um zero fora da linha força `D_∞ > 0`.** -/
theorem dInf_pos_of_zeroFora (ρ : ZeroFora) : 0 < dInf := by
  obtain ⟨μ, hμ, h⟩ := condensacao ρ
  exact hμ.trans_le (le_ciInf h)

/-- Contrapositiva: `D_∞ = 0` não deixa zero fora da linha. -/
theorem rh_of_dInf_eq_zero (h : dInf = 0) : RiemannHypothesis :=
  baezDuarteCriterion (dInf_eq_zero_iff.mpr h)

/-- **Com a necessidade como hipótese**: `RH ⟺ D_∞ = 0`. -/
theorem rh_iff_dInf_eq_zero (h : NecessidadeRH) : RiemannHypothesis ↔ dInf = 0 :=
  (rh_iff_DN h).trans dInf_eq_zero_iff

end ATK.DInfinito

#print axioms ATK.DInfinito.dInf_nonneg
#print axioms ATK.DInfinito.dInf_le_one
#print axioms ATK.DInfinito.tendsto_dInf
#print axioms ATK.DInfinito.dInf_eq_zero_iff
#print axioms ATK.DInfinito.piso_no_limite
#print axioms ATK.DInfinito.dInf_pos_of_zeroFora
#print axioms ATK.DInfinito.rh_of_dInf_eq_zero
#print axioms ATK.DInfinito.rh_iff_dInf_eq_zero
