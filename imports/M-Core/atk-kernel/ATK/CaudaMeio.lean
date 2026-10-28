import ATK.ZetaTroca
import ATK.BarreiraZero

/-!
# ATK-RH — "1/2 com cauda": as três leituras, decididas

1. **Cauda decimal infinita** (`0,4999…`, ou `0,5000…`): é o próprio `1/2`. `4/10 + Σ_{k≥0} 9/10^{k+2} = 1/2`
   (`dizima_noves`); e um número que concorda com `1/2` em todas as casas decimais é `1/2`
   (`cauda_decimal_exata`).
2. **Cauda verdadeira** `Re ρ = 1/2 + ε`, `ε ≠ 0`, num zero `ρ = 1/2 + ε + iγ`:
   * vem em par: `1/2 − ε + iγ` também é zero, e o centro do par é exatamente `1/2` (`cauda_par`);
   * refuta RH (`cauda_refuta`);
   * deixa um **piso** em `D_∞`: `0 < B ≤ D_∞`, com `B = (2|ε|)·|1−ρ⁺|²/|ρ⁺|⁴` (`cauda_piso`);
   * esse piso **some com a altura**: `B ≤ 2|ε|/γ²` (`barreira_le_cauda`). Para o produtor `D_N` excluir uma
     cauda `ε` na altura `γ`, é preciso `D_N < 2|ε|/γ²` (`deteccao_exige`).
3. **Cauda que encolhe** `ε_n → 0` ao longo de zeros distintos: as alturas vão a infinito
   (`ATK.TruncamentoZero.aproximantes_sobem`).
-/

open Complex Filter Topology

namespace ATK.CaudaMeio

open ATK.ZetaSimetria ATK.ForaDaLinha ATK.EixoDeslocado ATK.BarreiraZero ATK.ModeloParametrico
open ATK.Conditional.Riemann

/-- `0,4999… = 1/2`. -/
theorem dizima_noves : (4 : ℝ) / 10 + ∑' k : ℕ, (9 : ℝ) / 10 ^ (k + 2) = 1 / 2 := by
  have h : ∀ k : ℕ, (9 : ℝ) / 10 ^ (k + 2) = 9 / 100 * (1 / 10) ^ k := by
    intro k; rw [pow_add, one_div_pow]; field_simp; ring
  simp_rw [h]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- Um número que concorda com `1/2` em todas as casas decimais é `1/2`. -/
theorem cauda_decimal_exata {β : ℝ} (h : ∀ n : ℕ, |β - 1 / 2| ≤ (1 / 10) ^ n) : β = 1 / 2 := by
  refine exato_de_toda_tolerancia fun τ hτ => ?_
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hτ (by norm_num : (1 / 10 : ℝ) < 1)
  exact (h n).trans hn.le

/-- **A cauda vem em par**: `1/2 + ε + iγ` zero ⇒ `1/2 − ε + iγ` zero; o centro do par é `1/2`. -/
theorem cauda_par {ρ : ℂ} (hρ : ρ ∈ Z) {ε : ℝ} (hε : ρ.re = 1 / 2 + ε) :
    torcao ρ ∈ Z ∧ (torcao ρ).re = 1 / 2 - ε ∧ (torcao ρ).im = ρ.im ∧
      (ρ.re + (torcao ρ).re) / 2 = 1 / 2 := by
  refine ⟨torcao_mem_Z hρ, by rw [re_torcao, hε]; ring, im_torcao ρ, ?_⟩
  rw [re_torcao]; ring

/-- **Uma cauda não nula refuta RH.** -/
theorem cauda_refuta {ρ : ℂ} (hρ : ρ ∈ Z) {ε : ℝ} (hε : ρ.re = 1 / 2 + ε) (h0 : ε ≠ 0) :
    ¬ RiemannHypothesis := fun h => h0 (by have := re_de_rh h hρ; linarith)

/-- **O piso some com a altura**: `B(ρ) ≤ (2σ − 1)/γ²`. -/
theorem barreira_le_cauda {ρ : ℂ} (h0 : 1 / 2 < ρ.re) (hγ : ρ.im ≠ 0) :
    barreira ρ ≤ (2 * ρ.re - 1) / ρ.im ^ 2 := by
  unfold barreira
  have ha := normSq_eq_add ρ
  have hb0 : 0 ≤ normSq (1 - ρ) := normSq_nonneg _
  have hγ2 : 0 < ρ.im ^ 2 := by positivity
  have haγ : ρ.im ^ 2 ≤ normSq ρ := by rw [normSq_apply]; nlinarith [mul_self_nonneg ρ.re]
  have hapos : 0 < normSq ρ := lt_of_lt_of_le hγ2 haγ
  have ht : 0 < 2 * ρ.re - 1 := by linarith
  have hb : normSq (1 - ρ) ≤ normSq ρ := by linarith
  rw [div_le_div_iff₀ (by positivity) hγ2]
  calc (2 * ρ.re - 1) * normSq (1 - ρ) * ρ.im ^ 2
      ≤ (2 * ρ.re - 1) * normSq ρ * normSq ρ := by gcongr
    _ = (2 * ρ.re - 1) * normSq ρ ^ 2 := by ring

/-- **O piso da cauda em `D_∞`**: um zero com cauda `ε ≠ 0` na altura `γ` dá um zero `ρ⁺` com
`Re ρ⁺ = 1/2 + |ε|`, mesma altura, e `0 < B(ρ⁺) ≤ D_∞`, `B(ρ⁺) ≤ 2|ε|/γ²`. -/
theorem cauda_piso {ρ : ℂ} (hρ : ρ ∈ Z) {ε : ℝ} (hε : ρ.re = 1 / 2 + ε) (h0 : ε ≠ 0) :
    ∃ σ ∈ Z, σ.re = 1 / 2 + |ε| ∧ σ.im = ρ.im ∧ 0 < barreira σ ∧
      barreira σ ≤ ATK.DInfinito.dInf ∧ barreira σ ≤ 2 * |ε| / ρ.im ^ 2 := by
  have him := im_ne_zero_of_mem_Z hρ
  obtain ⟨σ, hσZ, hσre, hσim⟩ : ∃ σ ∈ Z, σ.re = 1 / 2 + |ε| ∧ σ.im = ρ.im := by
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · refine ⟨torcao ρ, torcao_mem_Z hρ, ?_, im_torcao ρ⟩
      rw [re_torcao, hε, abs_of_neg hneg]; ring
    · exact ⟨ρ, hρ, by rw [hε, abs_of_pos hpos], rfl⟩
  have habs : 0 < |ε| := abs_pos.mpr h0
  obtain ⟨hz, -, h1⟩ := hσZ
  have hlo : 1 / 2 < σ.re := by rw [hσre]; linarith
  refine ⟨σ, ⟨hz, by linarith, h1⟩, hσre, hσim, barreira_pos hlo h1,
    barreira_le_dInf hz hlo h1, ?_⟩
  have := barreira_le_cauda hlo (by rw [hσim]; exact him)
  rw [hσre, hσim] at this
  calc barreira σ ≤ (2 * (1 / 2 + |ε|) - 1) / ρ.im ^ 2 := this
    _ = 2 * |ε| / ρ.im ^ 2 := by ring

/-- **Para o produtor `D_N` excluir uma cauda `ε` na altura `γ`**, `D_N` tem de ficar abaixo de
`2ε/γ²`: a exclusão `D_N < B(ρ)` (`ATK.BarreiraZero.exclusao`) implica `D_N < (2σ−1)/γ²`. -/
theorem deteccao_exige {ρ : ℂ} (h0 : 1 / 2 < ρ.re) (hγ : ρ.im ≠ 0) {N : ℕ}
    (h : DN N < barreira ρ) : DN N < (2 * ρ.re - 1) / ρ.im ^ 2 :=
  h.trans_le (barreira_le_cauda h0 hγ)

end ATK.CaudaMeio

#print axioms ATK.CaudaMeio.dizima_noves
#print axioms ATK.CaudaMeio.cauda_decimal_exata
#print axioms ATK.CaudaMeio.cauda_par
#print axioms ATK.CaudaMeio.cauda_refuta
#print axioms ATK.CaudaMeio.barreira_le_cauda
#print axioms ATK.CaudaMeio.cauda_piso
#print axioms ATK.CaudaMeio.deteccao_exige
