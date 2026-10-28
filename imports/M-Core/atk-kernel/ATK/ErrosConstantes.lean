import Mathlib

/-!
# ATK — Erros da tabela de constantes (texto 7a43314b): `1/ζ(3)` e `2π²`

* **`0,831908` ("densidades aritméticas") está errado na 6ª casa.** O valor é
  `1/ζ(3) = 0,8319073726…` (densidade dos inteiros livres de cubos), cujo arredondamento a 6 casas é
  `0,831907`. Prova no kernel: `ζ(3) = Σ 1/n³` (Mathlib), soma parcial exata até `n = 60` (racional,
  `decide +kernel`) e caudas telescópicas
  `1/(2m²) + 1/(2m³) − [1/(2(m+1)²) + 1/(2(m+1)³)] ≤ 1/m³ ≤ 1/((m−1)m(m+1))`, `m ≥ 61`,
  dão `0,831907 < 1/ζ(3) < 0,8319075 < 0,831908` (`inv_zeta_tres_cotas`, `texto_0831908_errado`).
* **`19,739209` ("volume da esfera unitária") é `2π²`, mas o rótulo está errado.** `2π²` é a **área**
  (volume 3-dimensional) de `S³ ⊂ ℝ⁴`, a derivada em `r = 1` de `vol(B⁴_r) = π² r⁴/2`
  (`vol_bola_quatro`, `area_S3`); o volume da bola unitária é `π` (ℝ²), `4π/3` (ℝ³), `π²/2` (ℝ⁴).
  O número em si está certo: `19,739208 < 2π² < 19,739209` (`dois_pi_quadrado_cotas`).
-/

open Real Filter Topology MeasureTheory

namespace ATK.ErrosConstantes

/-! ## 1. `ζ(3)` como série real -/

/-- `ζ(3) = Σ_{n ≥ 1} 1/n³` (série real). -/
noncomputable def z3 : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3

theorem summable_z3 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 3 := by
  have h := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 3))
  refine h.congr fun n => ?_
  push_cast
  ring

theorem zeta_tres_eq : riemannZeta 3 = (z3 : ℂ) := by
  have h := zeta_nat_eq_tsum_of_gt_one (k := 3) (by norm_num)
  have hs : Summable fun n : ℕ => 1 / (n : ℂ) ^ 3 := by
    have : Summable fun n : ℕ => ((1 / (n : ℝ) ^ 3 : ℝ) : ℂ) :=
      Complex.summable_ofReal.mpr (Real.summable_one_div_nat_pow.mpr (by norm_num))
    refine this.congr fun n => ?_
    push_cast; ring
  push_cast at h
  rw [h, hs.tsum_eq_zero_add, z3, Complex.ofReal_tsum]
  simp

/-! ## 2. Caudas telescópicas -/

theorem tele_hasSum {u : ℕ → ℝ} (h0 : ∀ n, 0 ≤ u n - u (n + 1)) (hu : Tendsto u atTop (𝓝 0)) :
    HasSum (fun n => u n - u (n + 1)) (u 0) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg h0]
  have e : ∀ N, ∑ i ∈ Finset.range N, (u i - u (i + 1)) = u 0 - u N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; ring
  simp_rw [e]
  simpa using (tendsto_const_nhds (x := u 0)).sub hu

theorem tele_le {f u : ℕ → ℝ} (hs : Summable f) (hf : ∀ n, 0 ≤ f n)
    (hle : ∀ n, f n ≤ u n - u (n + 1)) (hu : Tendsto u atTop (𝓝 0)) : ∑' n, f n ≤ u 0 := by
  have hh := tele_hasSum (fun n => (hf n).trans (hle n)) hu
  rw [← hh.tsum_eq]
  exact hs.tsum_le_tsum hle hh.summable

theorem tele_ge {f w : ℕ → ℝ} (hs : Summable f) (h0 : ∀ n, 0 ≤ w n - w (n + 1))
    (hge : ∀ n, w n - w (n + 1) ≤ f n) (hw : Tendsto w atTop (𝓝 0)) : w 0 ≤ ∑' n, f n := by
  have hh := tele_hasSum h0 hw
  rw [← hh.tsum_eq]
  exact hh.summable.tsum_le_tsum hge hs

/-- Majorante: `u(n) = 1/(2(n+60)(n+61))`. -/
noncomputable def uM (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 60) * ((n : ℝ) + 61))

/-- Minorante: `w(n) = 1/(2(n+61)²) + 1/(2(n+61)³)`. -/
noncomputable def wM (n : ℕ) : ℝ := 1 / (2 * ((n : ℝ) + 61) ^ 2) + 1 / (2 * ((n : ℝ) + 61) ^ 3)

theorem uM_passo (n : ℕ) : 1 / ((n : ℝ) + 61) ^ 3 ≤ uM n - uM (n + 1) := by
  have key : uM n - uM (n + 1) = 1 / (((n : ℝ) + 60) * ((n : ℝ) + 61) * ((n : ℝ) + 62)) := by
    unfold uM; push_cast; field_simp; ring
  rw [key]
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem wM_passo (n : ℕ) :
    0 ≤ wM n - wM (n + 1) ∧ wM n - wM (n + 1) ≤ 1 / ((n : ℝ) + 61) ^ 3 := by
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hm : (0 : ℝ) < (n : ℝ) + 61 := by linarith
  have e1 : wM n - wM (n + 1) = (2 * ((n : ℝ) + 61) + 1) / (2 * ((n : ℝ) + 61) ^ 2 * ((n : ℝ) + 62) ^ 2) +
      (3 * ((n : ℝ) + 61) ^ 2 + 3 * ((n : ℝ) + 61) + 1) /
        (2 * ((n : ℝ) + 61) ^ 3 * ((n : ℝ) + 62) ^ 3) := by
    unfold wM; push_cast; field_simp; ring
  have e2 : 1 / ((n : ℝ) + 61) ^ 3 - (wM n - wM (n + 1)) =
      (2 * ((n : ℝ) + 61) + 1) / (2 * ((n : ℝ) + 61) ^ 3 * ((n : ℝ) + 62) ^ 3) := by
    unfold wM; push_cast; field_simp; ring
  constructor
  · rw [e1]; positivity
  · have : 0 ≤ (2 * ((n : ℝ) + 61) + 1) / (2 * ((n : ℝ) + 61) ^ 3 * ((n : ℝ) + 62) ^ 3) := by
      positivity
    linarith

theorem uM_tende : Tendsto uM atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun n => by unfold uM; positivity) (fun n => ?_)
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

theorem wM_tende : Tendsto wM atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun n => by unfold wM; positivity) (fun n => ?_)
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have h1 : 1 / (2 * ((n : ℝ) + 61) ^ 2) ≤ 1 / (2 * ((n : ℝ) + 1)) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have h2 : 1 / (2 * ((n : ℝ) + 61) ^ 3) ≤ 1 / (2 * ((n : ℝ) + 1)) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg ((n : ℝ) + 61)])
  unfold wM
  have : 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) = 1 / ((n : ℝ) + 1) := by
    field_simp; ring
  linarith

theorem summable_cauda : Summable fun n : ℕ => 1 / ((n : ℝ) + 61) ^ 3 := by
  refine ((summable_nat_add_iff 60).mpr summable_z3).congr fun n => ?_
  push_cast; ring

theorem z3_split :
    z3 = (∑ i ∈ Finset.range 60, 1 / ((i : ℝ) + 1) ^ 3) + ∑' n : ℕ, 1 / ((n : ℝ) + 61) ^ 3 := by
  unfold z3
  rw [← summable_z3.sum_add_tsum_nat_add 60]
  congr 1
  refine tsum_congr fun n => ?_
  push_cast; ring

/-- A soma parcial exata `S₆₀ = Σ_{n ≤ 60} 1/n³ ∈ ℚ`. -/
def S60 : ℚ := ∑ i ∈ Finset.range 60, 1 / ((i : ℚ) + 1) ^ 3

theorem S60_cast : (∑ i ∈ Finset.range 60, 1 / ((i : ℝ) + 1) ^ 3) = ((S60 : ℚ) : ℝ) := by
  unfold S60; push_cast; rfl

theorem cert_sup : (831907 / 10 ^ 6 : ℚ) * (S60 + 1 / 7320) < 1 := by decide +kernel

theorem cert_inf : 1 < (8319075 / 10 ^ 7 : ℚ) * (S60 + 1 / (2 * 61 ^ 2) + 1 / (2 * 61 ^ 3)) := by
  decide +kernel

theorem z3_le : z3 ≤ (S60 : ℝ) + 1 / 7320 := by
  rw [z3_split, S60_cast]
  have := tele_le summable_cauda (fun n => by positivity) uM_passo uM_tende
  have hu0 : uM 0 = 1 / 7320 := by unfold uM; norm_num
  linarith

theorem z3_ge : (S60 : ℝ) + 1 / (2 * 61 ^ 2) + 1 / (2 * 61 ^ 3) ≤ z3 := by
  rw [z3_split, S60_cast]
  have := tele_ge summable_cauda (fun n => (wM_passo n).1) (fun n => (wM_passo n).2) wM_tende
  have hw0 : wM 0 = 1 / (2 * 61 ^ 2) + 1 / (2 * 61 ^ 3) := by unfold wM; norm_num
  linarith

theorem z3_pos : 0 < z3 := by
  have h := z3_ge
  have : (0 : ℝ) ≤ (S60 : ℝ) := by
    have : (0 : ℚ) ≤ S60 := by unfold S60; positivity
    exact_mod_cast this
  linarith [show (0 : ℝ) < 1 / (2 * 61 ^ 2) by norm_num, show (0 : ℝ) < 1 / (2 * 61 ^ 3) by norm_num]

/-- **`0,831907 < 1/ζ(3) < 0,8319075`.** -/
theorem inv_zeta_tres_cotas : (831907 / 10 ^ 6 : ℝ) < 1 / z3 ∧ 1 / z3 < 8319075 / 10 ^ 7 := by
  have hp := z3_pos
  have h1 := (Rat.cast_lt (K := ℝ)).mpr cert_sup
  have h2 := (Rat.cast_lt (K := ℝ)).mpr cert_inf
  push_cast at h1 h2
  have hle := z3_le
  have hge := z3_ge
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-- **O `0,831908` do texto está errado**: `1/ζ(3) < 0,8319075 < 0,831908`, e `ζ(3)` é a série. -/
theorem texto_0831908_errado :
    riemannZeta 3 = (z3 : ℂ) ∧ 1 / z3 < 8319075 / 10 ^ 7 ∧ (8319075 / 10 ^ 7 : ℝ) < 831908 / 10 ^ 6 ∧
      (831907 / 10 ^ 6 : ℝ) < 1 / z3 :=
  ⟨zeta_tres_eq, inv_zeta_tres_cotas.2, by norm_num, inv_zeta_tres_cotas.1⟩

/-- `1,2020568 < ζ(3) < 1,2020570`. -/
theorem z3_cotas : (12020568 / 10 ^ 7 : ℝ) < z3 ∧ z3 < 12020570 / 10 ^ 7 := by
  have c1 : (12020568 / 10 ^ 7 : ℚ) < S60 + 1 / (2 * 61 ^ 2) + 1 / (2 * 61 ^ 3) := by decide +kernel
  have c2 : S60 + 1 / 7320 < (12020570 / 10 ^ 7 : ℚ) := by decide +kernel
  have d1 : ((12020568 / 10 ^ 7 : ℚ) : ℝ) < ((S60 + 1 / (2 * 61 ^ 2) + 1 / (2 * 61 ^ 3) : ℚ) : ℝ) := by
    exact_mod_cast c1
  have d2 : ((S60 + 1 / 7320 : ℚ) : ℝ) < ((12020570 / 10 ^ 7 : ℚ) : ℝ) := by exact_mod_cast c2
  push_cast at d1 d2
  exact ⟨by linarith [z3_ge], by linarith [z3_le]⟩

/-! ## 3. `2π²`: área de `S³`, não volume de bola -/

/-- `vol(B⁴_r) = (π²/2) r⁴`. -/
theorem vol_bola_quatro (r : ℝ) (hr : 0 ≤ r) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) r) = ENNReal.ofReal (π ^ 2 / 2 * r ^ 4) := by
  rw [InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)]
  simp only [finrank_euclideanSpace_fin, Nat.factorial, Nat.succ_eq_add_one, Nat.reduceAdd,
    Nat.reduceMul]
  rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  ring

/-- **Volume da bola unitária em ℝ⁴: `π²/2`** (não `2π²`). -/
theorem vol_bola_unit_quatro :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1) = ENNReal.ofReal (π ^ 2 / 2) := by
  rw [vol_bola_quatro 1 zero_le_one]; norm_num

/-- **Área de `S³`**: `d/dr (π²r⁴/2)|_{r=1} = 2π²`. -/
theorem area_S3 : HasDerivAt (fun r : ℝ => π ^ 2 / 2 * r ^ 4) (2 * π ^ 2) 1 := by
  have := (hasDerivAt_pow 4 (1 : ℝ)).const_mul (π ^ 2 / 2)
  convert this using 1
  norm_num
  ring

/-- **`19,739208 < 2π² < 19,739209`**: o número da tabela está certo. -/
theorem dois_pi_quadrado_cotas : (19739208 / 10 ^ 6 : ℝ) < 2 * π ^ 2 ∧ 2 * π ^ 2 < 19739209 / 10 ^ 6 := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  constructor <;> nlinarith

/-- **`π²/2 ≠ 2π²`** e `4π/3 ≠ 2π²`: nenhum volume de bola unitária (ℝ³, ℝ⁴) é `19,739…`. -/
theorem rotulo_errado : π ^ 2 / 2 < 2 * π ^ 2 ∧ 4 * π / 3 < 2 * π ^ 2 := by
  have h := Real.pi_gt_three
  constructor <;> nlinarith

end ATK.ErrosConstantes

-- Auditoria de axiomas (kernel)
#print axioms ATK.ErrosConstantes.summable_z3
#print axioms ATK.ErrosConstantes.zeta_tres_eq
#print axioms ATK.ErrosConstantes.tele_hasSum
#print axioms ATK.ErrosConstantes.tele_le
#print axioms ATK.ErrosConstantes.tele_ge
#print axioms ATK.ErrosConstantes.uM_passo
#print axioms ATK.ErrosConstantes.wM_passo
#print axioms ATK.ErrosConstantes.uM_tende
#print axioms ATK.ErrosConstantes.wM_tende
#print axioms ATK.ErrosConstantes.summable_cauda
#print axioms ATK.ErrosConstantes.z3_split
#print axioms ATK.ErrosConstantes.S60_cast
#print axioms ATK.ErrosConstantes.cert_sup
#print axioms ATK.ErrosConstantes.cert_inf
#print axioms ATK.ErrosConstantes.z3_le
#print axioms ATK.ErrosConstantes.z3_ge
#print axioms ATK.ErrosConstantes.z3_pos
#print axioms ATK.ErrosConstantes.inv_zeta_tres_cotas
#print axioms ATK.ErrosConstantes.texto_0831908_errado
#print axioms ATK.ErrosConstantes.z3_cotas
#print axioms ATK.ErrosConstantes.vol_bola_quatro
#print axioms ATK.ErrosConstantes.vol_bola_unit_quatro
#print axioms ATK.ErrosConstantes.area_S3
#print axioms ATK.ErrosConstantes.dois_pi_quadrado_cotas
#print axioms ATK.ErrosConstantes.rotulo_errado
