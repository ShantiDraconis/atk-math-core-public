import MCore.RH.NB.Nesting

namespace MCore.RH.NB
namespace NBHilbertData

variable (D : NBHilbertData)

theorem dN_antitone_of_le (rho : D.GeneratorFamily) {N M : ℕ} (hNM : N ≤ M) :
    D.dN rho M ≤ D.dN rho N := by
  unfold dN
  let vN : D.V rho M :=
    ⟨(D.P rho N D.chi : D.H), D.V_mono_of_le rho hNM (D.P_mem rho N D.chi)⟩
  have hmin := D.P_minimal rho M D.chi
  have hb : BddBelow (Set.range (fun v : D.V rho M => ‖D.chi - (v : D.H)‖)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨v, rfl⟩
    exact norm_nonneg _
  have hle : (⨅ v : D.V rho M, ‖D.chi - (v : D.H)‖) ≤ ‖D.chi - (vN : D.H)‖ := by
    exact ciInf_le hb vN
  calc
    ‖D.chi - (D.P rho M D.chi : D.H)‖ =
        (⨅ v : D.V rho M, ‖D.chi - (v : D.H)‖) := hmin
    _ ≤ ‖D.chi - (vN : D.H)‖ := hle
    _ = ‖D.chi - (D.P rho N D.chi : D.H)‖ := by rfl

theorem DN_antitone_of_le (rho : D.GeneratorFamily) {N M : ℕ} (hNM : N ≤ M) :
    D.DN rho M ≤ D.DN rho N := by
  unfold DN
  have hnonnegM : 0 ≤ D.dN rho M := D.dN_nonneg rho M
  have hnonnegN : 0 ≤ D.dN rho N := D.dN_nonneg rho N
  have hmono : D.dN rho M ≤ D.dN rho N := D.dN_antitone_of_le rho hNM
  nlinarith

theorem DN_antitone (rho : D.GeneratorFamily) :
    Antitone (D.DN rho) := by
  intro N M hNM
  exact D.DN_antitone_of_le rho hNM

end NBHilbertData
end MCore.RH.NB
