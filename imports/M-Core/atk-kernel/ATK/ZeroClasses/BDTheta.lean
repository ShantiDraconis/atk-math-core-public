import ATK.ZeroClasses.BDTaxa

/-!
# O expoente `Θ = sup Re ρ` e três instrumentos que o medem (rodada 76)

Define `Θ = inf{θ ≥ ½ : ζ ≠ 0 em Re s > θ}` (`Teta`) e junta as rodadas 57 e 59–75 numa só grandeza:

* `meio_le_Teta`, `Teta_le_um`, `semZeros_Teta`: `½ ≤ Θ ≤ 1` e `ζ ≠ 0` em `Re s > Θ`; `re_le_Teta`: todo zero tem
  `Re ρ ≤ Θ`; `existe_zero`: se `½ ≤ θ < Θ`, há zero com `Re ρ > θ` (logo `Θ = max(½, sup Re ρ)`);
* **`rh_iff_Teta`**: **RH ⟺ Θ = ½**;
* **os três instrumentos** (`Teta_le_iff_psi`, `Teta_le_iff_mertens`, `Teta_le_iff_DNσ`): para `½ ≤ θ < 1`,
  `Θ ≤ θ ⟺ ψ(x) − x ≪ x^{θ+ε} ⟺ M(x) ≪ x^{θ+ε} ⟺ inf_N D_N(σ) = 0 para todo σ ∈ (θ, 1)`;
* **a taxa** (`TaxaDN σ κ`: `D_N(σ) ≪ N^{−δ}` para todo `δ < κ`): `taxa_Teta`: `TaxaDN σ (2(σ − Θ))` em
  `Θ < σ < 1` (rodada 75); `piso_abaixo`, `nao_taxa_abaixo`: abaixo de `Θ`, `inf_N D_N(σ) > 0` e nenhuma taxa
  positiva;
* **`rh_iff_taxa`**: RH ⟺ `TaxaDN σ (2σ − 1)` para todo `σ ∈ (½, 1)`;
* **`PisoPonderado`** (a questão Q2(iii), **OPEN_MATH**): `TaxaDN σ κ ⟹ κ ≤ 2(σ − Θ)` para `Θ ≤ σ < 1`; e
  `rh_iff_taxa_de_piso`: **se** o piso valer, então RH ⟺ `TaxaDN σ₀ (2σ₀ − 1)` para **um único** `σ₀ ∈ (½, 1)`.

Nada aqui diz qual é o valor de `Θ`: todos os enunciados valem para qualquer valor. `Θ = ½` é RH (OPEN_MATH);
`Θ < 1` (um semiplano sem zeros) também é OPEN_MATH.

Classificação (rodada 76): **reformulação** (organiza as caracterizações de `Θ`). RH continua OPEN_MATH.
-/

open Complex Set Filter Topology
open scoped Real

namespace ATK.ZeroClasses.BDTheta

open ATK.ZeroClasses.QuasiRH (SemZeros semZeros_meio_iff semZeros_iff_psi semZeros_iff_mertens)
open ATK.ZeroClasses.BDPonderado (DNσ DNσ_nonneg semZeros_of_DNσ piso_DNσ)
open ATK.ZeroClasses.BDTaxa (DNσ_taxa semZeros_iff_DNσ)

/-! ## 1. `Θ` -/

/-- Os `θ ≥ ½` com `ζ ≠ 0` em `Re s > θ`. -/
def Admissivel : Set ℝ := {θ | 1 / 2 ≤ θ ∧ SemZeros θ}

/-- **`Θ = inf{θ ≥ ½ : ζ ≠ 0 em Re s > θ}`**. -/
noncomputable def Teta : ℝ := sInf Admissivel

theorem semZeros_mono {θ θ' : ℝ} (h : SemZeros θ) (hle : θ ≤ θ') : SemZeros θ' :=
  fun s hs => h s (lt_of_le_of_lt hle hs)

theorem semZeros_um : SemZeros 1 := fun _ hs => riemannZeta_ne_zero_of_one_le_re hs.le

theorem um_mem : (1 : ℝ) ∈ Admissivel := ⟨by norm_num, semZeros_um⟩

theorem bdd : BddBelow Admissivel := ⟨1 / 2, fun _ h => h.1⟩

theorem meio_le_Teta : 1 / 2 ≤ Teta := le_csInf ⟨1, um_mem⟩ fun _ h => h.1

theorem Teta_le_um : Teta ≤ 1 := csInf_le bdd um_mem

/-- `ζ ≠ 0` em `Re s > Θ`. -/
theorem semZeros_Teta : SemZeros Teta := by
  intro s hs
  obtain ⟨θ, hθ, hθs⟩ := exists_lt_of_csInf_lt ⟨1, um_mem⟩ hs
  exact hθ.2 s hθs

/-- **`Θ ≤ θ ⟺ ζ ≠ 0 em Re s > θ`**, para `θ ≥ ½`. -/
theorem Teta_le_iff {θ : ℝ} (hθ : 1 / 2 ≤ θ) : Teta ≤ θ ↔ SemZeros θ :=
  ⟨fun h => semZeros_mono semZeros_Teta h, fun h => csInf_le bdd ⟨hθ, h⟩⟩

/-- Todo zero de `ζ` tem `Re ρ ≤ Θ`. -/
theorem re_le_Teta {ρ : ℂ} (hρ : riemannZeta ρ = 0) : ρ.re ≤ Teta := by
  by_contra h
  exact semZeros_Teta ρ (not_le.mp h) hρ

/-- Se `½ ≤ θ < Θ`, há um zero com `Re ρ > θ`. -/
theorem existe_zero {θ : ℝ} (hθ : 1 / 2 ≤ θ) (h : θ < Teta) : ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ θ < ρ.re := by
  by_contra hne
  push Not at hne
  have hZ : SemZeros θ := fun s hs hz => absurd (hne s hz) (not_le.mpr hs)
  exact absurd ((Teta_le_iff hθ).mpr hZ) (not_le.mpr h)

/-- **RH ⟺ Θ = ½**. -/
theorem rh_iff_Teta : RiemannHypothesis ↔ Teta = 1 / 2 := by
  rw [← semZeros_meio_iff, ← Teta_le_iff le_rfl]
  exact ⟨fun h => le_antisymm h meio_le_Teta, fun h => h.le⟩

/-! ## 2. Três instrumentos, uma grandeza -/

/-- `Θ ≤ θ ⟺ ψ(x) − x ≪ x^{θ+ε}` (rodada 57). -/
theorem Teta_le_iff_psi {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    Teta ≤ θ ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ,
      |Chebyshev.psi N - N| ≤ C * ((N : ℝ) + 1) ^ (θ + ε) :=
  (Teta_le_iff hθ).trans (semZeros_iff_psi hθ hθ1)

/-- `Θ ≤ θ ⟺ M(x) ≪ x^{θ+ε}` (rodada 57). -/
theorem Teta_le_iff_mertens {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    Teta ≤ θ ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ,
      |ATK.ZeroClasses.Mertens.M N| ≤ C * ((N : ℝ) + 1) ^ (θ + ε) :=
  (Teta_le_iff hθ).trans (semZeros_iff_mertens hθ hθ1)

/-- `Θ ≤ θ ⟺ inf_N D_N(σ) = 0` para todo `σ ∈ (θ, 1)` (rodadas 59 e 75). -/
theorem Teta_le_iff_DNσ {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    Teta ≤ θ ↔ ∀ σ : ℝ, θ < σ → σ < 1 → ⨅ N, DNσ σ N = 0 :=
  (Teta_le_iff hθ).trans (semZeros_iff_DNσ hθ hθ1)

/-! ## 3. A taxa de `D_N(σ)` -/

/-- `D_N(σ) ≪ N^{−δ}` para todo `δ < κ`. -/
def TaxaDN (σ κ : ℝ) : Prop := ∀ δ : ℝ, δ < κ → ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N → DNσ σ N ≤ K * (N : ℝ) ^ (-δ)

theorem taxa_mono {σ κ κ' : ℝ} (h : TaxaDN σ κ) (hle : κ' ≤ κ) : TaxaDN σ κ' :=
  fun δ hδ => h δ (lt_of_lt_of_le hδ hle)

/-- **`κ(σ) ≥ 2(σ − Θ)`**: `TaxaDN σ (2(σ − Θ))` para `Θ < σ < 1`. -/
theorem taxa_Teta {σ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) : TaxaDN σ (2 * (σ - Teta)) := by
  intro δ hδ
  have hm0 := le_max_right δ 0
  have hmδ := le_max_left δ 0
  have hmax : max δ 0 < 2 * (σ - Teta) := max_lt hδ (by linarith)
  set δ' : ℝ := (max δ 0 / 2 + (σ - Teta)) / 2 with hδ'
  obtain ⟨K, hK0, hK⟩ := DNσ_taxa semZeros_Teta meio_le_Teta (by linarith) hσ1 (δ := δ')
    (by rw [hδ']; linarith) (by rw [hδ']; linarith)
  refine ⟨K, fun N hN => (hK N hN).trans ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hexp : -(2 * δ') ≤ -δ := by
    rcases le_total δ 0 with h | h
    · rw [hδ']; linarith
    · have hm : max δ 0 = δ := max_eq_left h
      rw [hδ', hm]
      linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 hexp) hK0

/-- **Abaixo de `Θ`**: `inf_N D_N(σ) > 0` para `0 < σ < Θ`. -/
theorem piso_abaixo {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ < Teta) : 0 < ⨅ N, DNσ σ N := by
  rcases lt_or_ge σ (1 / 2) with h | h
  · exact piso_DNσ hσ0 h
  · have hge : 0 ≤ ⨅ N, DNσ σ N := Real.iInf_nonneg fun N => DNσ_nonneg σ N
    rcases hge.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have hσ1 : σ < 1 := lt_of_lt_of_le hσ Teta_le_um
      have hZ := semZeros_of_DNσ hσ0 hσ1 h'.symm
      have := (Teta_le_iff h).mpr hZ
      linarith

/-- Abaixo de `Θ`, nenhuma taxa positiva. -/
theorem nao_taxa_abaixo {σ κ : ℝ} (hσ0 : 0 < σ) (hσ : σ < Teta) (hκ : 0 < κ) : ¬ TaxaDN σ κ := by
  intro h
  have hpos := piso_abaixo hσ0 hσ
  obtain ⟨K, hK⟩ := h (κ / 2) (by linarith)
  have hg : Tendsto (fun N : ℕ => K * (N : ℝ) ^ (-(κ / 2))) atTop (𝓝 0) := by
    have h0 := (tendsto_rpow_neg_atTop (y := κ / 2) (by linarith)).comp tendsto_natCast_atTop_atTop
    simpa using h0.const_mul K
  have hbdd : BddBelow (Set.range (DNσ σ)) := ⟨0, fun _ ⟨N, hN⟩ => hN ▸ DNσ_nonneg σ N⟩
  have hle : ⨅ N, DNσ σ N ≤ 0 := by
    refine ge_of_tendsto hg ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact (ciInf_le hbdd N).trans (hK N hN)
  linarith

/-- **RH ⟺ `TaxaDN σ (2σ − 1)` para todo `σ ∈ (½, 1)`**. -/
theorem rh_iff_taxa : RiemannHypothesis ↔ ∀ σ : ℝ, 1 / 2 < σ → σ < 1 → TaxaDN σ (2 * σ - 1) := by
  rw [rh_iff_Teta]
  constructor
  · intro hT σ hσ hσ1
    have := taxa_Teta (σ := σ) (by rw [hT]; exact hσ) hσ1
    rw [hT] at this
    exact taxa_mono this (by linarith)
  · intro h
    by_contra hne
    have hgt : 1 / 2 < Teta := lt_of_le_of_ne meio_le_Teta (Ne.symm hne)
    have hT1 := Teta_le_um
    exact nao_taxa_abaixo (σ := (1 / 2 + Teta) / 2) (by linarith) (by linarith) (κ := 2 * ((1 / 2 + Teta) / 2) - 1)
      (by linarith) (h _ (by linarith) (by linarith))

/-! ## 4. A questão aberta Q2(iii) -/

/-- **O piso ponderado** (Q2(iii), **OPEN_MATH**): para `Θ ≤ σ < 1`, nenhuma taxa acima de `2(σ − Θ)`. -/
def PisoPonderado : Prop := ∀ σ : ℝ, Teta ≤ σ → σ < 1 → ∀ κ : ℝ, TaxaDN σ κ → κ ≤ 2 * (σ - Teta)

/-- **Se o piso valer**, RH se decide num único `σ₀ ∈ (½, 1)`: RH ⟺ `TaxaDN σ₀ (2σ₀ − 1)`. -/
theorem rh_iff_taxa_de_piso (hP : PisoPonderado) {σ₀ : ℝ} (h0 : 1 / 2 < σ₀) (h1 : σ₀ < 1) :
    RiemannHypothesis ↔ TaxaDN σ₀ (2 * σ₀ - 1) := by
  constructor
  · intro hRH
    exact (rh_iff_taxa.mp hRH) σ₀ h0 h1
  · intro h
    rw [rh_iff_Teta]
    rcases lt_or_ge σ₀ Teta with hlt | hge
    · exact absurd h (nao_taxa_abaixo (by linarith) hlt (by linarith))
    · have := hP σ₀ hge h1 _ h
      linarith [meio_le_Teta]

end ATK.ZeroClasses.BDTheta

#print axioms ATK.ZeroClasses.BDTheta.semZeros_mono
#print axioms ATK.ZeroClasses.BDTheta.semZeros_um
#print axioms ATK.ZeroClasses.BDTheta.um_mem
#print axioms ATK.ZeroClasses.BDTheta.bdd
#print axioms ATK.ZeroClasses.BDTheta.meio_le_Teta
#print axioms ATK.ZeroClasses.BDTheta.Teta_le_um
#print axioms ATK.ZeroClasses.BDTheta.semZeros_Teta
#print axioms ATK.ZeroClasses.BDTheta.Teta_le_iff
#print axioms ATK.ZeroClasses.BDTheta.re_le_Teta
#print axioms ATK.ZeroClasses.BDTheta.existe_zero
#print axioms ATK.ZeroClasses.BDTheta.rh_iff_Teta
#print axioms ATK.ZeroClasses.BDTheta.Teta_le_iff_psi
#print axioms ATK.ZeroClasses.BDTheta.Teta_le_iff_mertens
#print axioms ATK.ZeroClasses.BDTheta.Teta_le_iff_DNσ
#print axioms ATK.ZeroClasses.BDTheta.taxa_mono
#print axioms ATK.ZeroClasses.BDTheta.taxa_Teta
#print axioms ATK.ZeroClasses.BDTheta.piso_abaixo
#print axioms ATK.ZeroClasses.BDTheta.nao_taxa_abaixo
#print axioms ATK.ZeroClasses.BDTheta.rh_iff_taxa
#print axioms ATK.ZeroClasses.BDTheta.rh_iff_taxa_de_piso
