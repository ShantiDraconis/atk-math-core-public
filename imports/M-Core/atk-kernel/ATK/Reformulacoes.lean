import ATK.NecessidadeRH
import ATK.GramBaezDuarte

/-!
# ATK-RH — Reformulações de uma linha (via `rh_iff_DN`)

* **`rh_iff_forma_quadratica`**: HR ⟺ `bᵀG_N⁻¹b → 1` (pois `D_N = 1 − bᵀG_N⁻¹b`).
* **`rh_iff_residuo`**: HR ⟺ `∀ ε > 0, ∃ N, ∃ c, ‖χ − Σ c_k ρ_k‖² < ε`.
* **`rh_iff_certificados`**: HR ⟺ para todo `j` existe um resíduo `≤ 2⁻ʲ` (uma família de
  certificados finitos; cada um é uma conta, a família inteira é HR).
-/

open Filter Topology Matrix

namespace ATK.Reformulacoes

open ATK.Conditional.Riemann (DN residualSq DN_nonneg)

theorem rh_iff_forma_quadratica :
    RiemannHypothesis ↔ Tendsto (fun N => ATK.GramBaezDuarte.b N ⬝ᵥ
      ((ATK.GramBaezDuarte.G N)⁻¹ *ᵥ ATK.GramBaezDuarte.b N)) atTop (𝓝 1) := by
  rw [ATK.NecessidadeRH.rh_iff_DN]
  have e : ∀ N, ATK.GramBaezDuarte.b N ⬝ᵥ ((ATK.GramBaezDuarte.G N)⁻¹ *ᵥ ATK.GramBaezDuarte.b N) =
      1 - DN N := fun N => by rw [ATK.GramBaezDuarte.DN_eq_gram]; ring
  simp_rw [e]
  constructor
  · intro h; simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  · intro h; simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h

theorem rh_iff_residuo :
    RiemannHypothesis ↔ ∀ ε > 0, ∃ N : ℕ, ∃ c : Fin N → ℝ, residualSq N c < ε := by
  rw [ATK.NecessidadeRH.rh_iff_iInf_DN]
  have hbdd : BddBelow (Set.range DN) := ⟨0, by rintro _ ⟨N, rfl⟩; exact DN_nonneg N⟩
  constructor
  · intro h ε hε
    have h1 : ⨅ N, DN N < ε := by rw [h]; exact hε
    obtain ⟨N, hN⟩ := exists_lt_of_ciInf_lt h1
    have hbddc : BddBelow (Set.range (residualSq N)) :=
      ⟨0, by rintro _ ⟨c, rfl⟩; exact ATK.RiemannConcrete.residualSq_nonneg N c⟩
    obtain ⟨c, hc⟩ := exists_lt_of_ciInf_lt (show ⨅ c, residualSq N c < ε from hN)
    exact ⟨N, c, hc⟩
  · intro h
    apply le_antisymm _ (le_ciInf DN_nonneg)
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨N, c, hc⟩ := h ε hε
    have := (ciInf_le hbdd N).trans (ATK.RiemannConcrete.DN_le_residualSq N c)
    linarith

theorem rh_iff_certificados :
    RiemannHypothesis ↔ ∀ j : ℕ, ∃ N : ℕ, ∃ c : Fin N → ℝ, residualSq N c ≤ (1 / 2 : ℝ) ^ j := by
  rw [rh_iff_residuo]
  constructor
  · intro h j
    obtain ⟨N, c, hc⟩ := h ((1 / 2 : ℝ) ^ j) (by positivity)
    exact ⟨N, c, hc.le⟩
  · intro h ε hε
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
    obtain ⟨N, c, hc⟩ := h j
    exact ⟨N, c, lt_of_le_of_lt hc hj⟩

end ATK.Reformulacoes

-- Auditoria de axiomas (kernel)
#print axioms ATK.Reformulacoes.rh_iff_forma_quadratica
#print axioms ATK.Reformulacoes.rh_iff_residuo
#print axioms ATK.Reformulacoes.rh_iff_certificados
