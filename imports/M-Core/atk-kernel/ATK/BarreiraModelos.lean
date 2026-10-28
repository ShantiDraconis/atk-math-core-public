import ATK.BarreiraZero
import ATK.LinhaIncognita
import ATK.Cert.Transc

/-!
# ATK-RH — Cálculo da barreira, o modelo logarítmico e o ajuste de dois pontos

**Barreira** `B(β, γ) = t·b/a²`, `t = 2β − 1`, `a = β² + γ²`, `b = (1 − β)² + γ²` (`= barreira (β + iγ)`,
`barreira_eq`):

* `∂_β B = B·(2/t + 2(β−1)/b − 4β/a)` (`deriv_beta`); `∂_γ B = 2γB·(1/b − 2/a)` (`deriv_gamma`);
* em `β = ½`: `∂_β B = 2/(γ² + ¼)` (`deriv_meio`) e `B(½ + δ, γ)/δ → 2/(γ² + ¼)` (`lim_meio`);
* `γ²·B(β, γ) → 2β − 1` quando `γ → ∞` (`lim_altura`);
* tabela (`tabela`): `B(0,6; 14,134725) ∈ (0,000998; 0,000999)`, `B(0,75; ·) ∈ (0,002489; 0,002490)`,
  `B(0,9; ·) ∈ (0,003972; 0,003973)` — todas `< 0,2967`, nenhum desses pontos é excluído.

**Identidades**: `F(s) = (s − ½)ζ(s)` zera exatamente nos zeros de `ζ` e em `½` (`F_zero_iff`), e
`F(½) = 0` com `ζ(½) ≠ 0` (`F_meio`); `Re(A/B) − ½ = (ac + bd)/(c² + d²) − ½` (`eps_formula`).

**Modelo logarítmico** `f(x) = a + C/log x` (`x > 1`, `C > 0`): `f′ = −C/(x log²x) < 0`,
`f″ = C(log x + 2)/(x² log³x) > 0`, `∫_{N₀}^{N₁} f′ = C(1/log N₁ − 1/log N₀)`, `∫_{N₀}^∞ (−f′) = C/log N₀`,
`f → a`.

**Ajuste de dois pontos** (`ajuste_negativo`): com os decimais relatados `D₂₅₆ = 0,0082337162772` e
`D₈₀₀₀ = 0,0050691202`, vale `D₂₅₆ log 256 > D₈₀₀₀ log 8000`, logo o único modelo `a + C/log N` pelos dois
pontos tem **intercepto `a ∈ (−2,92·10⁻⁵, −2,90·10⁻⁵)`, negativo** — incompatível com `D_N ≥ 0` como
lei assintótica (`sem_modelo_nao_negativo`). Isso diz algo sobre o modelo, não sobre `D_∞`.
-/

open Real Filter Topology Set MeasureTheory

namespace ATK.BarreiraModelos

/-! ## 1. A barreira como função de `(β, γ)` -/

/-- `B(β, γ) = (2β − 1)((1 − β)² + γ²)/(β² + γ²)²`. -/
noncomputable def Bf (β γ : ℝ) : ℝ := (2 * β - 1) * ((1 - β) ^ 2 + γ ^ 2) / (β ^ 2 + γ ^ 2) ^ 2

theorem barreira_eq (ρ : ℂ) : ATK.BarreiraZero.barreira ρ = Bf ρ.re ρ.im := by
  unfold ATK.BarreiraZero.barreira Bf
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  ring

theorem hasDerivAt_num (β γ : ℝ) :
    HasDerivAt (fun x : ℝ => (2 * x - 1) * ((1 - x) ^ 2 + γ ^ 2))
      (2 * ((1 - β) ^ 2 + γ ^ 2) + (2 * β - 1) * (2 * (β - 1))) β := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 β := by
    simpa using ((hasDerivAt_id' β).const_mul 2).sub_const 1
  have h2 : HasDerivAt (fun x : ℝ => (1 - x) ^ 2 + γ ^ 2) (2 * (β - 1)) β := by
    have := (((hasDerivAt_const β (1 : ℝ)).sub (hasDerivAt_id' β)).pow 2).add_const (γ ^ 2)
    convert this using 1
    simp only [Pi.sub_apply]
    ring
  convert h1.mul h2 using 1

theorem hasDerivAt_den (β γ : ℝ) :
    HasDerivAt (fun x : ℝ => (x ^ 2 + γ ^ 2) ^ 2) (2 * (β ^ 2 + γ ^ 2) * (2 * β)) β := by
  have := (((hasDerivAt_id' β).pow 2).add_const (γ ^ 2)).pow 2
  convert this using 1
  simp only [Pi.pow_apply]
  ring

/-- **`∂_β B = B·(2/t + 2(β−1)/b − 4β/a)`.** -/
theorem deriv_beta (β γ : ℝ) (ht : 2 * β - 1 ≠ 0) (hb : (1 - β) ^ 2 + γ ^ 2 ≠ 0)
    (ha : β ^ 2 + γ ^ 2 ≠ 0) :
    HasDerivAt (fun x => Bf x γ)
      (Bf β γ * (2 / (2 * β - 1) + 2 * (β - 1) / ((1 - β) ^ 2 + γ ^ 2) - 4 * β / (β ^ 2 + γ ^ 2))) β := by
  have := (hasDerivAt_num β γ).div (hasDerivAt_den β γ) (pow_ne_zero 2 ha)
  unfold Bf
  convert this using 1
  field_simp
  ring

/-- **Em `β = ½`: `∂_β B = 2/(γ² + ¼)`.** -/
theorem deriv_meio (γ : ℝ) : HasDerivAt (fun x => Bf x γ) (2 / (γ ^ 2 + 1 / 4)) (1 / 2) := by
  have ha : (1 / 2 : ℝ) ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have := (hasDerivAt_num (1 / 2) γ).div (hasDerivAt_den (1 / 2) γ) (pow_ne_zero 2 ha)
  unfold Bf
  convert this using 1
  have h4 : γ ^ 2 + 1 / 4 ≠ 0 := by positivity
  field_simp
  ring

/-- **`∂_γ B = 2γB·(1/b − 2/a)`.** -/
theorem deriv_gamma (β γ : ℝ) (hb : (1 - β) ^ 2 + γ ^ 2 ≠ 0) (ha : β ^ 2 + γ ^ 2 ≠ 0) :
    HasDerivAt (fun y => Bf β y)
      (2 * γ * Bf β γ * (1 / ((1 - β) ^ 2 + γ ^ 2) - 2 / (β ^ 2 + γ ^ 2))) γ := by
  have hn : HasDerivAt (fun y : ℝ => (2 * β - 1) * ((1 - β) ^ 2 + y ^ 2)) ((2 * β - 1) * (2 * γ)) γ := by
    have := (((hasDerivAt_id' γ).pow 2).const_add ((1 - β) ^ 2)).const_mul (2 * β - 1)
    convert this using 1
    ring
  have hd : HasDerivAt (fun y : ℝ => (β ^ 2 + y ^ 2) ^ 2) (2 * (β ^ 2 + γ ^ 2) * (2 * γ)) γ := by
    have := (((hasDerivAt_id' γ).pow 2).const_add (β ^ 2)).pow 2
    convert this using 1
    simp only [Pi.pow_apply]
    ring
  have := hn.div hd (pow_ne_zero 2 ha)
  unfold Bf
  convert this using 1
  field_simp

/-- **`B(½ + δ, γ)/δ → 2/(γ² + ¼)`** quando `δ → 0`. -/
theorem lim_meio (γ : ℝ) :
    Tendsto (fun δ : ℝ => Bf (1 / 2 + δ) γ / δ) (𝓝[≠] 0) (𝓝 (2 / (γ ^ 2 + 1 / 4))) := by
  set g : ℝ → ℝ := fun δ => 2 * ((1 / 2 - δ) ^ 2 + γ ^ 2) / ((1 / 2 + δ) ^ 2 + γ ^ 2) ^ 2 with hg
  have hcont : ContinuousAt g 0 := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    positivity
  have hg0 : g 0 = 2 / (γ ^ 2 + 1 / 4) := by
    simp only [hg]
    have h4 : γ ^ 2 + 1 / 4 ≠ 0 := by positivity
    field_simp
    ring
  have hT : Tendsto g (𝓝[≠] 0) (𝓝 (2 / (γ ^ 2 + 1 / 4))) := by
    rw [← hg0]; exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num : (-1 / 2 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1 / 2))] with δ hδ hδ'
  have hδ0 : δ ≠ 0 := hδ
  simp only [hg, Bf]
  have hpos : 0 < 1 / 2 + δ := by linarith [hδ'.1]
  have hp : ((1 / 2 + δ) ^ 2 + γ ^ 2) ≠ 0 :=
    (add_pos_of_pos_of_nonneg (pow_pos hpos 2) (sq_nonneg γ)).ne'
  field_simp
  ring

/-- **`γ² B(β, γ) → 2β − 1`** quando `γ → ∞`. -/
theorem lim_altura (β : ℝ) :
    Tendsto (fun γ : ℝ => γ ^ 2 * Bf β γ) atTop (𝓝 (2 * β - 1)) := by
  set h : ℝ → ℝ := fun v => (2 * β - 1) * ((1 + (1 - β) ^ 2 * v ^ 2) / (1 + β ^ 2 * v ^ 2) ^ 2) with hh
  have hcont : ContinuousAt h 0 := by
    refine continuousAt_const.mul (ContinuousAt.div (by fun_prop) (by fun_prop) ?_)
    simp
  have h0 : h 0 = 2 * β - 1 := by simp [hh]
  have hT : Tendsto (fun γ : ℝ => h γ⁻¹) atTop (𝓝 (2 * β - 1)) := by
    rw [← h0]; exact hcont.tendsto.comp tendsto_inv_atTop_zero
  refine hT.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with γ hγ
  simp only [hh, Bf]
  have hγ0 : γ ≠ 0 := hγ.ne'
  have h1 : β ^ 2 + γ ^ 2 ≠ 0 := by positivity
  have h2 : 1 + β ^ 2 * (γ⁻¹) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Tabela em `γ = 14,134725` e em `γ = 100`. -/
theorem tabela :
    (998 / 10 ^ 6 < Bf (3 / 5) (14134725 / 10 ^ 6) ∧ Bf (3 / 5) (14134725 / 10 ^ 6) < 999 / 10 ^ 6) ∧
    (2489 / 10 ^ 6 < Bf (3 / 4) (14134725 / 10 ^ 6) ∧ Bf (3 / 4) (14134725 / 10 ^ 6) < 2490 / 10 ^ 6) ∧
    (3972 / 10 ^ 6 < Bf (9 / 10) (14134725 / 10 ^ 6) ∧ Bf (9 / 10) (14134725 / 10 ^ 6) < 3973 / 10 ^ 6) ∧
    (199988 / 10 ^ 10 < Bf (3 / 5) 100 ∧ Bf (3 / 5) 100 < 199990 / 10 ^ 10) ∧
    (499946 / 10 ^ 10 < Bf (3 / 4) 100 ∧ Bf (3 / 4) 100 < 499948 / 10 ^ 10) := by
  unfold Bf
  norm_num

theorem tabela_abaixo :
    Bf (3 / 5) (14134725 / 10 ^ 6) < 2967 / 10 ^ 4 ∧ Bf (3 / 4) (14134725 / 10 ^ 6) < 2967 / 10 ^ 4 ∧
    Bf (9 / 10) (14134725 / 10 ^ 6) < 2967 / 10 ^ 4 := by
  obtain ⟨⟨-, h1⟩, ⟨-, h2⟩, ⟨-, h3⟩, -⟩ := tabela
  refine ⟨?_, ?_, ?_⟩ <;> linarith

/-! ## 2. `F(s) = (s − ½)ζ(s)` e `ε_N` -/

/-- `F(s) = (s − ½) ζ(s)`. -/
noncomputable def F (s : ℂ) : ℂ := (s - 1 / 2) * riemannZeta s

theorem F_zero_iff (s : ℂ) : F s = 0 ↔ riemannZeta s = 0 ∨ s = 1 / 2 := by
  unfold F
  rw [mul_eq_zero, sub_eq_zero]
  tauto

theorem F_zero_iff_of_ne {s : ℂ} (hs : s ≠ 1 / 2) : F s = 0 ↔ riemannZeta s = 0 := by
  rw [F_zero_iff]; tauto

/-- `F(½) = 0`, embora `ζ(½) ≠ 0`: o zero de `F` em `½` é artificial. -/
theorem F_meio : F (1 / 2) = 0 ∧ riemannZeta (1 / 2) ≠ 0 :=
  ⟨by simp [F], ATK.LinhaIncognita.zeta_meio_ne_zero⟩

/-- `ε = Re(A/B) − ½ = (ac + bd)/(c² + d²) − ½`. -/
theorem eps_formula (A B : ℂ) :
    (A / B).re - 1 / 2 = (A.re * B.re + A.im * B.im) / (B.re ^ 2 + B.im ^ 2) - 1 / 2 := by
  rw [Complex.div_re, Complex.normSq_apply]
  ring

/-! ## 3. O modelo logarítmico `f(x) = a + C/log x` -/

/-- `f(x) = a + C/log x`. -/
noncomputable def fLog (a C x : ℝ) : ℝ := a + C / Real.log x

theorem log_pos_of {x : ℝ} (hx : 1 < x) : 0 < Real.log x := Real.log_pos hx

theorem deriv_fLog (a C : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fLog a C) (-C / (x * Real.log x ^ 2)) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl : Real.log x ≠ 0 := (log_pos_of hx).ne'
  have := ((Real.hasDerivAt_log hx0).inv hl).const_mul C |>.const_add a
  unfold fLog
  convert this using 1
  · funext y; simp [div_eq_mul_inv]
  · field_simp

theorem deriv_fLog_neg {C : ℝ} (hC : 0 < C) {x : ℝ} (hx : 1 < x) :
    -C / (x * Real.log x ^ 2) < 0 := by
  have := log_pos_of hx
  have hx0 : 0 < x := by linarith
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

theorem deriv2_fLog (C : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun y => -C / (y * Real.log y ^ 2))
      (C * (Real.log x + 2) / (x ^ 2 * Real.log x ^ 3)) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl : Real.log x ≠ 0 := (log_pos_of hx).ne'
  have hd : HasDerivAt (fun y => y * Real.log y ^ 2) (1 * Real.log x ^ 2 + x * (2 * Real.log x * x⁻¹)) x := by
    have := (hasDerivAt_id' x).mul ((Real.hasDerivAt_log hx0).pow 2)
    convert this using 1
    simp only [Pi.pow_apply]
    ring
  have := (hasDerivAt_const x (-C)).div hd (mul_ne_zero hx0 (pow_ne_zero 2 hl))
  convert this using 1
  field_simp
  ring

theorem deriv2_fLog_pos {C : ℝ} (hC : 0 < C) {x : ℝ} (hx : 1 < x) :
    0 < C * (Real.log x + 2) / (x ^ 2 * Real.log x ^ 3) := by
  have := log_pos_of hx
  have hx0 : 0 < x := by linarith
  positivity

theorem tendsto_fLog (a C : ℝ) : Tendsto (fLog a C) atTop (𝓝 a) := by
  have h : Tendsto (fun x => C / Real.log x) atTop (𝓝 0) :=
    Real.tendsto_log_atTop.const_div_atTop C
  have := h.const_add a
  rw [add_zero] at this
  exact this

theorem continuousOn_dfLog (C : ℝ) {N₀ : ℝ} (h0 : 1 < N₀) (N₁ : ℝ) :
    ContinuousOn (fun x => -C / (x * Real.log x ^ 2)) (Icc N₀ N₁) := by
  refine ContinuousOn.div continuousOn_const ?_ ?_
  · refine continuousOn_id.mul ((Real.continuousOn_log.mono ?_).pow 2)
    intro x hx; simp only [mem_compl_iff, mem_singleton_iff]; linarith [hx.1]
  · intro x hx
    have hx1 : 1 < x := lt_of_lt_of_le h0 hx.1
    have := log_pos_of hx1
    have : 0 < x := by linarith
    positivity

/-- `∫_{N₀}^{N₁} f′ = C(1/log N₁ − 1/log N₀)`. -/
theorem integral_dfLog (a C : ℝ) {N₀ N₁ : ℝ} (h0 : 1 < N₀) (h01 : N₀ ≤ N₁) :
    ∫ x in N₀..N₁, -C / (x * Real.log x ^ 2) = C * (1 / Real.log N₁ - 1 / Real.log N₀) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fLog a C)]
  · unfold fLog; ring
  · intro x hx
    rw [uIcc_of_le h01] at hx
    exact deriv_fLog a C (lt_of_lt_of_le h0 hx.1)
  · exact (continuousOn_dfLog C h0 N₁).intervalIntegrable_of_Icc h01

/-- `∫_{N₀}^∞ (−f′) = C/log N₀`. -/
theorem integral_Ioi_dfLog {C : ℝ} (hC : 0 ≤ C) {N₀ : ℝ} (h0 : 1 < N₀) :
    ∫ x in Ioi N₀, C / (x * Real.log x ^ 2) = C / Real.log N₀ := by
  have hcont : ContinuousWithinAt (fun x => -(C / Real.log x)) (Ici N₀) N₀ := by
    have hl : Real.log N₀ ≠ 0 := (log_pos_of h0).ne'
    refine (ContinuousAt.neg (ContinuousAt.div continuousAt_const
      (Real.continuousAt_log (by linarith)) hl)).continuousWithinAt
  have hder : ∀ x ∈ Ioi N₀, HasDerivAt (fun x => -(C / Real.log x)) (C / (x * Real.log x ^ 2)) x := by
    intro x hx
    have hx1 : 1 < x := lt_trans h0 hx
    have := (deriv_fLog 0 C hx1).neg
    convert this using 1
    · funext y; simp [fLog]
    · ring
  have hpos : ∀ x ∈ Ioi N₀, 0 ≤ C / (x * Real.log x ^ 2) := by
    intro x hx
    have hx1 : 1 < x := lt_trans h0 hx
    have := log_pos_of hx1
    have : 0 < x := by linarith
    positivity
  have hlim : Tendsto (fun x => -(C / Real.log x)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_log_atTop.const_div_atTop C).neg
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hder hpos hlim]
  ring

/-! ## 4. O ajuste de dois pontos -/

/-- Pelos pontos `(L₀, D₀)`, `(L₁, D₁)` (`L = log N`), o modelo `a + C/L` tem
`a = (D₁L₁ − D₀L₀)/(L₁ − L₀)`. -/
theorem intercepto {L₀ L₁ D₀ D₁ a C : ℝ} (hL0 : 0 < L₀) (hL : L₀ < L₁)
    (h0 : D₀ = a + C / L₀) (h1 : D₁ = a + C / L₁) :
    a = (D₁ * L₁ - D₀ * L₀) / (L₁ - L₀) := by
  have hL1 : 0 < L₁ := by linarith
  have hne : L₁ - L₀ ≠ 0 := by linarith
  rw [eq_div_iff hne, h0, h1]
  field_simp
  ring

theorem intercepto_neg_iff {L₀ L₁ D₀ D₁ a C : ℝ} (hL0 : 0 < L₀) (hL : L₀ < L₁)
    (h0 : D₀ = a + C / L₀) (h1 : D₁ = a + C / L₁) :
    a < 0 ↔ D₁ * L₁ < D₀ * L₀ := by
  rw [intercepto hL0 hL h0 h1, div_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · linarith
  · intro h; right; constructor <;> linarith

/-- `D₂₅₆ = 0,0082337162772` e `D₈₀₀₀ = 0,0050691202` (decimais relatados). -/
noncomputable def D256 : ℝ := 82337162772 / 10 ^ 13
noncomputable def D8000 : ℝ := 50691202 / 10 ^ 10

theorem log5_sub_log4_bounds :
    (2231435 / 10 ^ 7 : ℝ) < Real.log 5 - Real.log 4 ∧ Real.log 5 - Real.log 4 < 2231436 / 10 ^ 7 := by
  have h := ATK.Cert.mem_dLog 6 (j := 4) (by norm_num)
  unfold ATK.Cert.dLog ATK.Cert.atS ATK.Cert.IR.mem at h
  norm_num [Finset.sum_range_succ] at h
  constructor <;> linarith [h.1, h.2]

theorem log256 : Real.log 256 = 8 * Real.log 2 := by
  rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num

theorem log8000 : Real.log 8000 = 6 * Real.log 2 + 3 * Real.log 5 := by
  rw [show (8000 : ℝ) = 2 ^ 6 * 5 ^ 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow]
  push_cast; ring

theorem log4 : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num

/-- **`D₂₅₆ log 256 > D₈₀₀₀ log 8000`.** -/
theorem produto_decresce : D8000 * Real.log 8000 < D256 * Real.log 256 := by
  rw [log8000, log256]
  have h4 := log4
  have h2a := Real.log_two_gt_d9
  have h2b := Real.log_two_lt_d9
  obtain ⟨h5a, h5b⟩ := log5_sub_log4_bounds
  unfold D256 D8000
  linarith

/-- **O ajuste de dois pontos tem intercepto negativo**, `a ∈ (−2,92·10⁻⁵, −2,90·10⁻⁵)`. -/
theorem ajuste_negativo {a C : ℝ} (h0 : D256 = a + C / Real.log 256) (h1 : D8000 = a + C / Real.log 8000) :
    a < 0 ∧ -292 / 10 ^ 7 < a ∧ a < -290 / 10 ^ 7 := by
  have hL0 : 0 < Real.log 256 := Real.log_pos (by norm_num)
  have hL : Real.log 256 < Real.log 8000 := Real.log_lt_log (by norm_num) (by norm_num)
  have ha := intercepto hL0 hL h0 h1
  refine ⟨(intercepto_neg_iff hL0 hL h0 h1).mpr produto_decresce, ?_⟩
  have hden : 0 < Real.log 8000 - Real.log 256 := by linarith
  have h4 := log4
  have h2a := Real.log_two_gt_d9
  have h2b := Real.log_two_lt_d9
  obtain ⟨h5a, h5b⟩ := log5_sub_log4_bounds
  rw [ha]
  constructor
  · rw [lt_div_iff₀ hden, log8000, log256]; unfold D256 D8000; linarith
  · rw [div_lt_iff₀ hden, log8000, log256]; unfold D256 D8000; linarith

/-- **Nenhum modelo `a + C/log N` com `a ≥ 0` passa pelos dois pontos relatados.** -/
theorem sem_modelo_nao_negativo :
    ¬ ∃ a C : ℝ, 0 ≤ a ∧ D256 = a + C / Real.log 256 ∧ D8000 = a + C / Real.log 8000 := by
  rintro ⟨a, C, ha, h0, h1⟩
  have := (ajuste_negativo h0 h1).1
  linarith

/-- E o modelo ajustado fica negativo para `N` grande. -/
theorem modelo_fica_negativo {a C : ℝ} (h0 : D256 = a + C / Real.log 256)
    (h1 : D8000 = a + C / Real.log 8000) : ∀ᶠ x in atTop, fLog a C x < 0 := by
  have ha := (ajuste_negativo h0 h1).1
  exact (tendsto_fLog a C).eventually (gt_mem_nhds ha)

end ATK.BarreiraModelos

-- Auditoria de axiomas (kernel)
#print axioms ATK.BarreiraModelos.barreira_eq
#print axioms ATK.BarreiraModelos.hasDerivAt_num
#print axioms ATK.BarreiraModelos.hasDerivAt_den
#print axioms ATK.BarreiraModelos.deriv_beta
#print axioms ATK.BarreiraModelos.deriv_meio
#print axioms ATK.BarreiraModelos.deriv_gamma
#print axioms ATK.BarreiraModelos.lim_meio
#print axioms ATK.BarreiraModelos.lim_altura
#print axioms ATK.BarreiraModelos.tabela
#print axioms ATK.BarreiraModelos.tabela_abaixo
#print axioms ATK.BarreiraModelos.F_zero_iff
#print axioms ATK.BarreiraModelos.F_zero_iff_of_ne
#print axioms ATK.BarreiraModelos.F_meio
#print axioms ATK.BarreiraModelos.eps_formula
#print axioms ATK.BarreiraModelos.log_pos_of
#print axioms ATK.BarreiraModelos.deriv_fLog
#print axioms ATK.BarreiraModelos.deriv_fLog_neg
#print axioms ATK.BarreiraModelos.deriv2_fLog
#print axioms ATK.BarreiraModelos.deriv2_fLog_pos
#print axioms ATK.BarreiraModelos.tendsto_fLog
#print axioms ATK.BarreiraModelos.continuousOn_dfLog
#print axioms ATK.BarreiraModelos.integral_dfLog
#print axioms ATK.BarreiraModelos.integral_Ioi_dfLog
#print axioms ATK.BarreiraModelos.intercepto
#print axioms ATK.BarreiraModelos.intercepto_neg_iff
#print axioms ATK.BarreiraModelos.log5_sub_log4_bounds
#print axioms ATK.BarreiraModelos.log256
#print axioms ATK.BarreiraModelos.log8000
#print axioms ATK.BarreiraModelos.log4
#print axioms ATK.BarreiraModelos.produto_decresce
#print axioms ATK.BarreiraModelos.ajuste_negativo
#print axioms ATK.BarreiraModelos.sem_modelo_nao_negativo
#print axioms ATK.BarreiraModelos.modelo_fica_negativo
