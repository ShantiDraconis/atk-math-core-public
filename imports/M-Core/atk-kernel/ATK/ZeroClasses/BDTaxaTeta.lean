import ATK.ZeroClasses.BDSemPotencia

/-!
# `Θ` como o início das taxas de potência de `D_N(σ)` (rodada 85)

Com as rodadas 76 e 83, "ter taxa de potência" em `σ` é exatamente estar à direita de `Θ`:

  **`ComTaxa σ ⟺ Θ < σ`** para `0 < σ < 1`   (`comTaxa_iff`),

com `ComTaxa σ := ∃ κ > 0, TaxaDN σ κ`. A ida é a rodada 83 (`taxaDN_pos`); a volta é a rodada 76 (`taxa_Teta`, com
`κ = 2(σ − Θ)`). Daí:
* **`Teta_eq_sInf`**: se `Θ < 1`, `Θ = inf{σ ∈ (0, 1) : D_N(σ) ≪ N^{−κ} para algum κ > 0}`;
* `comTaxa_mono`: `ComTaxa` sobe com `σ`;
* **`rh_iff_comTaxa`**: RH ⟺ `D_N(σ)` tem taxa de potência para todo `σ ∈ (½, 1)`;
* **`rh_iff_comTaxa_perto`**: RH ⟺ para todo `ε > 0` há `σ ∈ (½, ½ + ε)` com taxa de potência.

A taxa só importa quanto ao sinal. O valor exato `κ = 2(σ − Θ)` (Q2(iii)) não é necessário para medir `Θ`.

Classificação (rodada 85): **reformulação**. RH continua OPEN_MATH.
-/

open Set Filter Topology

namespace ATK.ZeroClasses.BDTaxaTeta

open ATK.ZeroClasses.BDTheta (Teta meio_le_Teta Teta_le_um rh_iff_Teta TaxaDN taxa_Teta)
open ATK.ZeroClasses.BDTaxaPiso (taxaDN_pos taxaDN_mono)

/-- `D_N(σ)` tem alguma taxa de potência positiva. -/
def ComTaxa (σ : ℝ) : Prop := ∃ κ : ℝ, 0 < κ ∧ TaxaDN σ κ

/-- **`ComTaxa σ ⟺ Θ < σ`** para `0 < σ < 1`. -/
theorem comTaxa_iff {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) : ComTaxa σ ↔ Teta < σ :=
  ⟨fun ⟨_, hκ, h⟩ => taxaDN_pos hσ0 hσ1 hκ h,
   fun h => ⟨2 * (σ - Teta), by linarith, taxa_Teta h hσ1⟩⟩

/-- `ComTaxa` sobe com `σ`. -/
theorem comTaxa_mono {σ σ' : ℝ} (hσ0 : 0 < σ) (hσσ : σ ≤ σ') (hσ1 : σ' < 1) (h : ComTaxa σ) : ComTaxa σ' :=
  let ⟨κ, hκ, hT⟩ := h
  ⟨κ, hκ, taxaDN_mono hσ0 hσσ hσ1 hT⟩

/-- **`Θ = inf{σ ∈ (0, 1) : ComTaxa σ}`** (se `Θ < 1`). -/
theorem Teta_eq_sInf (hT1 : Teta < 1) : Teta = sInf {σ : ℝ | σ ∈ Ioo (0 : ℝ) 1 ∧ ComTaxa σ} := by
  have hT0 : 0 < Teta := by linarith [meio_le_Teta]
  have e : {σ : ℝ | σ ∈ Ioo (0 : ℝ) 1 ∧ ComTaxa σ} = Ioo Teta 1 := by
    ext σ
    constructor
    · rintro ⟨⟨h0, h1⟩, h⟩
      exact ⟨(comTaxa_iff h0 h1).mp h, h1⟩
    · rintro ⟨h0, h1⟩
      exact ⟨⟨by linarith, h1⟩, (comTaxa_iff (by linarith) h1).mpr h0⟩
  rw [e, csInf_Ioo hT1]

/-- **RH ⟺ `D_N(σ)` tem taxa de potência para todo `σ ∈ (½, 1)`**. -/
theorem rh_iff_comTaxa : RiemannHypothesis ↔ ∀ σ : ℝ, 1 / 2 < σ → σ < 1 → ComTaxa σ := by
  constructor
  · intro hRH σ hσ hσ1
    exact (comTaxa_iff (by linarith) hσ1).mpr (by rw [rh_iff_Teta.mp hRH]; exact hσ)
  · intro h
    apply rh_iff_Teta.mpr
    refine le_antisymm ?_ meio_le_Teta
    by_contra hc
    push Not at hc
    set σ : ℝ := (1 / 2 + min Teta 1) / 2 with hσ
    have hm : 1 / 2 < min Teta 1 := lt_min hc (by norm_num)
    have hσ1 : σ < 1 := by have := min_le_right Teta 1; rw [hσ]; linarith
    have hσT : σ < Teta := by have := min_le_left Teta 1; rw [hσ]; linarith
    have := (comTaxa_iff (by rw [hσ]; linarith) hσ1).mp (h σ (by rw [hσ]; linarith) hσ1)
    linarith

/-- **RH ⟺ há taxa de potência arbitrariamente perto de `½`**. -/
theorem rh_iff_comTaxa_perto :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 / 2 + ε ∧ σ < 1 ∧ ComTaxa σ := by
  constructor
  · intro hRH ε hε
    set σ : ℝ := 1 / 2 + min (ε / 2) (1 / 4) with hσ
    have hm : 0 < min (ε / 2) (1 / 4) := lt_min (by linarith) (by norm_num)
    have h1 : min (ε / 2) (1 / 4) ≤ ε / 2 := min_le_left _ _
    have h2 : min (ε / 2) (1 / 4) ≤ 1 / 4 := min_le_right _ _
    exact ⟨σ, by rw [hσ]; linarith, by rw [hσ]; linarith, by rw [hσ]; linarith,
      (rh_iff_comTaxa.mp hRH) σ (by rw [hσ]; linarith) (by rw [hσ]; linarith)⟩
  · intro h
    apply rh_iff_comTaxa.mpr
    intro σ hσ hσ1
    obtain ⟨σ₀, h0, h1, h2, hc⟩ := h (σ - 1 / 2) (by linarith)
    exact comTaxa_mono (by linarith) (by linarith) hσ1 hc

end ATK.ZeroClasses.BDTaxaTeta

#print axioms ATK.ZeroClasses.BDTaxaTeta.comTaxa_iff
#print axioms ATK.ZeroClasses.BDTaxaTeta.comTaxa_mono
#print axioms ATK.ZeroClasses.BDTaxaTeta.Teta_eq_sInf
#print axioms ATK.ZeroClasses.BDTaxaTeta.rh_iff_comTaxa
#print axioms ATK.ZeroClasses.BDTaxaTeta.rh_iff_comTaxa_perto
