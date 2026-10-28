import ATK.ZeroClasses.JensenLocal

/-!
# O produto canônico dos zeros de `ζ` converge, e `HadamardXi` vira uma identidade (rodada 31)

Com `Σ_ρ m_ρ/|ρ|² < ∞` (`JensenLocal.soma_ordem_inv_quadrado`), o produto canônico de gênero 1

  `P(s) = ∏_ρ ((1 − s/ρ) e^{s/ρ})^{m_ρ}`

converge **incondicionalmente** para todo `s`:

* `E1 z = (1 − z) e^z`, `E1_sub_one_le`: `‖E1 z − 1‖ ≤ 3‖z‖²` para `‖z‖ ≤ 1`
  (`norm_exp_sub_one_sub_id_le`, `norm_exp_sub_one_le` da Mathlib);
* `ZM`: os zeros com multiplicidade (`Σ ρ : ATK.ZetaSimetria.Z, Fin m_ρ`); `summable_ZM`: `Σ_{(ρ,j)} 1/|ρ|² < ∞`;
* **`canonico_converge`**: `∏_{(ρ,j)} E1(s/ρ)` é multiplicável (`Complex.multipliable_one_add_of_summable`);
  `Pcan s` é o seu valor;
* **`produtos_simetricos`**: os produtos parciais simétricos de `HadamardXi` (`|Im ρ| ≤ T`, com multiplicidade)
  convergem para `Pcan s` quando `T → ∞`;
* **`hadamardXi_iff`**: `HadamardXi ⟺ ∃ A B, ∀ s, ξ(s) = e^{A + Bs} · Pcan(s)`.

A parte de convergência do teorema de Hadamard para `ξ` está provada; falta a identidade (que `ξ/P` é
`e^{A + Bs}`, a parte de ordem 1 / Borel–Carathéodory): BUILD_PENDING.

Classificação (rodada 31): **ferramenta** — reduz `HadamardXi` (`ATK.FechamentoO1`) a uma identidade. RH segue
OPEN_MATH.
-/

open Complex Set Filter Topology
open scoped Real

namespace ATK.ZeroClasses.Canonico



/-- Os zeros da faixa com multiplicidade: pares `(ρ, j)` com `j < m_ρ`. -/
abbrev ZM := Σ ρ : ATK.ZetaSimetria.Z, Fin (analyticOrderNatAt riemannZeta (ρ : ℂ))

/-- O fator de Weierstrass de gênero 1. -/
noncomputable def E1 (z : ℂ) : ℂ := (1 - z) * cexp z

theorem E1_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖E1 z - 1‖ ≤ 3 * ‖z‖ ^ 2 := by
  have e : E1 z - 1 = (cexp z - 1 - z) - z * (cexp z - 1) := by unfold E1; ring
  rw [e]
  have h1 := Complex.norm_exp_sub_one_sub_id_le hz
  have h2 := Complex.norm_exp_sub_one_le hz
  calc _ ≤ ‖cexp z - 1 - z‖ + ‖z * (cexp z - 1)‖ := norm_sub_le _ _
    _ ≤ ‖z‖ ^ 2 + ‖z‖ * (2 * ‖z‖) := by
        rw [norm_mul]
        gcongr
    _ = 3 * ‖z‖ ^ 2 := by ring

/-- **`Σ_{(ρ, j)} 1/|ρ|² < ∞`**. -/
theorem summable_ZM : Summable (fun p : ZM => 1 / ‖((p.1 : ATK.ZetaSimetria.Z) : ℂ)‖ ^ 2) := by
  rw [summable_sigma_of_nonneg (fun p => by positivity)]
  refine ⟨fun x => Summable.of_finite, ?_⟩
  convert ATK.ZeroClasses.JensenLocal.soma_ordem_inv_quadrado using 1
  funext x
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem norma_quociente (s : ℂ) (p : ZM) :
    ‖s‖ ^ 2 * (1 / ‖((p.1 : ATK.ZetaSimetria.Z) : ℂ)‖ ^ 2) = ‖s / ((p.1 : ATK.ZetaSimetria.Z) : ℂ)‖ ^ 2 := by
  rw [norm_div, div_pow]
  ring

/-- **O produto canônico converge** (incondicionalmente) em todo `s`. -/
theorem canonico_converge (s : ℂ) : Multipliable (fun p : ZM => E1 (s / ((p.1 : ATK.ZetaSimetria.Z) : ℂ))) := by
  have hg : Summable (fun p : ZM => ‖s‖ ^ 2 * (1 / ‖((p.1 : ATK.ZetaSimetria.Z) : ℂ)‖ ^ 2)) :=
    summable_ZM.mul_left _
  have hev : ∀ᶠ p : ZM in cofinite, ‖s / ((p.1 : ATK.ZetaSimetria.Z) : ℂ)‖ ≤ 1 := by
    filter_upwards [hg.tendsto_cofinite_zero.eventually (ge_mem_nhds one_pos)] with p hp
    rw [norma_quociente] at hp
    nlinarith [norm_nonneg (s / ((p.1 : ATK.ZetaSimetria.Z) : ℂ))]
  have hsum : Summable (fun p : ZM => E1 (s / ((p.1 : ATK.ZetaSimetria.Z) : ℂ)) - 1) := by
    refine (hg.mul_left 3).of_norm_bounded_eventually ?_
    filter_upwards [hev] with p hp
    rw [norma_quociente]
    exact E1_sub_one_le hp
  have := Complex.multipliable_one_add_of_summable hsum
  simpa using this

/-- O produto canônico `P(s) = ∏_{(ρ, j)} (1 − s/ρ) e^{s/ρ}`. -/
noncomputable def Pcan (s : ℂ) : ℂ := ∏' p : ZM, E1 (s / ((p.1 : ATK.ZetaSimetria.Z) : ℂ))

open Classical in
/-- Os conjuntos `|Im ρ| ≤ T` com multiplicidade, em `ZM`. -/
noncomputable def simT (T : ℝ) : Finset ZM :=
  ((ATK.FechamentoO1.zerosSim_finito T).toFinset.subtype (· ∈ ATK.ZetaSimetria.Z)).sigma fun _ => Finset.univ

theorem prod_sim_eq (s : ℂ) (T : ℝ) :
    ∏ ρ ∈ (ATK.FechamentoO1.zerosSim_finito T).toFinset,
        ((1 - s / ρ) * cexp (s / ρ)) ^ analyticOrderNatAt riemannZeta ρ =
      ∏ p ∈ simT T, E1 (s / ((p.1 : ATK.ZetaSimetria.Z) : ℂ)) := by
  classical
  unfold simT
  rw [Finset.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, E1]
  rw [Finset.prod_subtype_eq_prod_filter
    (f := fun ρ : ℂ => ((1 - s / ρ) * cexp (s / ρ)) ^ analyticOrderNatAt riemannZeta ρ),
    Finset.filter_true_of_mem]
  intro ρ hρ
  exact ((Set.Finite.mem_toFinset _).mp hρ).1

theorem simT_tendsto : Tendsto simT atTop atTop := by
  classical
  apply Filter.tendsto_atTop_finset_of_monotone
  · intro T T' h p hp
    unfold simT at hp ⊢
    rw [Finset.mem_sigma, Finset.mem_subtype, Set.Finite.mem_toFinset] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans h⟩, hp.2⟩
  · intro p
    refine ⟨|((p.1 : ATK.ZetaSimetria.Z) : ℂ).im|, ?_⟩
    unfold simT
    rw [Finset.mem_sigma, Finset.mem_subtype, Set.Finite.mem_toFinset]
    exact ⟨⟨p.1.2, le_rfl⟩, Finset.mem_univ _⟩

/-- **Os produtos parciais simétricos de `HadamardXi` convergem para `Pcan s`**. -/
theorem produtos_simetricos (s : ℂ) :
    Tendsto (fun T : ℝ => ∏ ρ ∈ (ATK.FechamentoO1.zerosSim_finito T).toFinset,
      ((1 - s / ρ) * cexp (s / ρ)) ^ analyticOrderNatAt riemannZeta ρ) atTop (𝓝 (Pcan s)) := by
  have h : Tendsto (fun F : Finset ZM => ∏ p ∈ F, E1 (s / ((p.1 : ATK.ZetaSimetria.Z) : ℂ))) atTop (𝓝 (Pcan s)) :=
    (canonico_converge s).hasProd
  exact (h.comp simT_tendsto).congr fun T => (prod_sim_eq s T).symm

/-- **`HadamardXi ⟺ ξ = e^{A + Bs} · P`**: só falta a identidade. -/
theorem hadamardXi_iff : ATK.FechamentoO1.HadamardXi ↔
    ∃ A B : ℂ, ∀ s : ℂ, ATK.FechamentoO1.xi s = cexp (A + B * s) * Pcan s := by
  constructor
  · rintro ⟨A, B, h⟩
    exact ⟨A, B, fun s => tendsto_nhds_unique (h s) ((produtos_simetricos s).const_mul _)⟩
  · rintro ⟨A, B, h⟩
    refine ⟨A, B, fun s => ?_⟩
    rw [h s]
    exact (produtos_simetricos s).const_mul _

end ATK.ZeroClasses.Canonico

#print axioms ATK.ZeroClasses.Canonico.E1_sub_one_le
#print axioms ATK.ZeroClasses.Canonico.summable_ZM
#print axioms ATK.ZeroClasses.Canonico.norma_quociente
#print axioms ATK.ZeroClasses.Canonico.canonico_converge
#print axioms ATK.ZeroClasses.Canonico.prod_sim_eq
#print axioms ATK.ZeroClasses.Canonico.simT_tendsto
#print axioms ATK.ZeroClasses.Canonico.produtos_simetricos
#print axioms ATK.ZeroClasses.Canonico.hadamardXi_iff
