import ATK.NSFraca
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# ATK — Navier–Stokes: a formulação fraca para campos-teste de Schwartz

Camada 17 do ataque a B3. A formulação fraca `ATK.NSFraca.formulacao_fraca` vale para campos-teste
de suporte compacto; aqui ela é estendida a **rotacionais de campos de Schwartz** `Φ = rot Ψ`,
por corte `Ψ_R = χ(·/R) Ψ` (o rotacional mantém a divergência nula) e convergência dominada:

* `rot`, `div_rot` (`div rot = 0`, simetria das segundas derivadas), cotas
  `‖Dⁿ rot F‖ ≤ ‖rotL‖ ‖Dⁿ⁺¹ F‖`, `‖ΔG‖ ≤ 3 ‖D²G‖`;
* o corte `χ_R`: igual a `1` em `‖x‖ ≤ R`, derivadas limitadas uniformemente para `R ≥ 1`
  (regra de Leibniz);
* **`formulacao_fraca_rot`**: a identidade para `Φ = rot Ψ`, `Ψ` de Schwartz.

**CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff Real

namespace ATK.NSCorte

open ATK.LigacaoNS ATK.NSReducao ATK.NSFraca

/-! ### O rotacional como aplicação linear da derivada -/

/-- `L ↦ (L eⱼ)ₖ`. -/
noncomputable def cmp (j k : Fin 3) : (E3 →L[ℝ] E3) →L[ℝ] ℝ :=
  (EuclideanSpace.proj k : E3 →L[ℝ] ℝ).comp (ContinuousLinearMap.apply ℝ E3 (e j))

theorem cmp_apply (j k : Fin 3) (L : E3 →L[ℝ] E3) : cmp j k L = L (e j) k := rfl

/-- O rotacional `rot F = (∂₁F₂ − ∂₂F₁, ∂₂F₀ − ∂₀F₂, ∂₀F₁ − ∂₁F₀)` como função linear da derivada. -/
noncomputable def rotL : (E3 →L[ℝ] E3) →L[ℝ] E3 :=
  (cmp 1 2 - cmp 2 1).smulRight (e 0) + (cmp 2 0 - cmp 0 2).smulRight (e 1) +
    (cmp 0 1 - cmp 1 0).smulRight (e 2)

/-- O rotacional. -/
noncomputable def rot (F : E3 → E3) (x : E3) : E3 := rotL (fderiv ℝ F x)

theorem rotL_apply (L : E3 →L[ℝ] E3) (a : Fin 3) :
    rotL L a = if a = 0 then L (e 1) 2 - L (e 2) 1 else if a = 1 then L (e 2) 0 - L (e 0) 2
      else L (e 0) 1 - L (e 1) 0 := by
  fin_cases a <;> simp [rotL, cmp_apply, e, PiLp.single_apply]

theorem contDiff_rot {F : E3 → E3} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (rot F) :=
  rotL.contDiff.comp (hF.fderiv_right (by simp))

theorem hasCompactSupport_rot {F : E3 → E3} (hF : HasCompactSupport F) :
    HasCompactSupport (rot F) :=
  (hF.fderiv (𝕜 := ℝ)).comp_left (g := rotL) (map_zero _)

theorem dX_rot {F : E3 → E3} (hF : ContDiff ℝ ∞ F) (j : Fin 3) (x : E3) :
    dX j (rot F) x = rotL (fderiv ℝ (fderiv ℝ F) x (e j)) := by
  unfold dX rot
  have hd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have h : HasFDerivAt (fun y => rotL (fderiv ℝ F y)) (rotL.comp (fderiv ℝ (fderiv ℝ F) x)) x :=
    rotL.hasFDerivAt.comp x hd.hasFDerivAt
  rw [h.fderiv]
  rfl

/-- **`div rot = 0`** (simetria das segundas derivadas). -/
theorem div_rot {F : E3 → E3} (hF : ContDiff ℝ ∞ F) (x : E3) : div (rot F) x = 0 := by
  have hs : IsSymmSndFDerivAt ℝ F x :=
    (hF.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  unfold div
  simp only [dX_rot hF, rotL_apply]
  simp only [Fin.sum_univ_three]
  simp only [show (0 : Fin 3) ≠ 1 from by decide, show (0 : Fin 3) ≠ 2 from by decide,
    show (1 : Fin 3) ≠ 0 from by decide, show (1 : Fin 3) ≠ 2 from by decide,
    show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide, if_true, if_false]
  rw [hs (e 0) (e 1), hs (e 0) (e 2), hs (e 1) (e 2)]
  ring

/-! ### Cotas das derivadas -/

theorem norm_iteratedFDeriv_rot_le {F : E3 → E3} (hF : ContDiff ℝ ∞ F) (n : ℕ) (x : E3) :
    ‖iteratedFDeriv ℝ n (rot F) x‖ ≤ ‖rotL‖ * ‖iteratedFDeriv ℝ (n + 1) F x‖ := by
  have h := rotL.norm_iteratedFDeriv_comp_left (f := fderiv ℝ F) (x := x) (N := ∞) (n := n)
    ((hF.fderiv_right (m := ∞) (by simp)).contDiffAt) (by exact_mod_cast le_top)
  rw [norm_iteratedFDeriv_fderiv] at h
  exact h

theorem norm_dX_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (G : E3 → W) (j : Fin 3)
    (x : E3) : ‖dX j G x‖ ≤ ‖iteratedFDeriv ℝ 1 G x‖ := by
  rw [norm_iteratedFDeriv_one]
  unfold dX
  have he : ‖(e j : E3)‖ = 1 := by simp [e]
  calc ‖fderiv ℝ G x (e j)‖ ≤ ‖fderiv ℝ G x‖ * ‖(e j : E3)‖ := (fderiv ℝ G x).le_opNorm _
    _ = ‖fderiv ℝ G x‖ := by rw [he, mul_one]

theorem dX_dX_eq {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {G : E3 → W}
    (hG : ContDiff ℝ ∞ G) (i j : Fin 3) (x : E3) :
    dX i (dX j G) x = iteratedFDeriv ℝ 2 G x ![e i, e j] := by
  rw [iteratedFDeriv_two_apply]
  unfold dX
  have hd : DifferentiableAt ℝ (fderiv ℝ G) x :=
    ((hG.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) x
  have h : HasFDerivAt (fun y => fderiv ℝ G y (e j))
      ((ContinuousLinearMap.apply ℝ W (e j)).comp (fderiv ℝ (fderiv ℝ G) x)) x :=
    (ContinuousLinearMap.apply ℝ W (e j)).hasFDerivAt.comp x hd.hasFDerivAt
  rw [h.fderiv]
  rfl

theorem norm_lap_le {G : E3 → E3} (hG : ContDiff ℝ ∞ G) (x : E3) :
    ‖lap G x‖ ≤ 3 * ‖iteratedFDeriv ℝ 2 G x‖ := by
  unfold lap
  have he : ∀ j, ‖(e j : E3)‖ = 1 := fun j => by simp [e]
  calc ‖∑ j, dX j (dX j G) x‖ ≤ ∑ j, ‖dX j (dX j G) x‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, ‖iteratedFDeriv ℝ 2 G x‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [dX_dX_eq hG]
        refine ((iteratedFDeriv ℝ 2 G x).le_opNorm _).trans ?_
        simp [Fin.prod_univ_two, he]
    _ = 3 * ‖iteratedFDeriv ℝ 2 G x‖ := by simp


/-! ### O corte -/

/-- A função de corte base (= 1 em `B(0, 1)`, suporte em `B(0, 2)`). -/
noncomputable def bump0 : ContDiffBump (0 : E3) := ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- `χ_R(x) = b(x/R)`. -/
noncomputable def chi (R : ℝ) (x : E3) : ℝ := bump0 (R⁻¹ • x)

theorem chi_eq_comp (R : ℝ) :
    chi R = (⇑bump0) ∘ (R⁻¹ • ContinuousLinearMap.id ℝ E3) := by
  funext x; simp [chi]

theorem contDiff_chi (R : ℝ) : ContDiff ℝ ∞ (chi R) := by
  rw [chi_eq_comp]
  exact bump0.contDiff.comp (R⁻¹ • ContinuousLinearMap.id ℝ E3).contDiff

theorem hasCompactSupport_chi {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (chi R) :=
  bump0.hasCompactSupport.comp_smul (inv_ne_zero hR)

theorem chi_eq_one {R : ℝ} (hR : 0 < R) {x : E3} (hx : ‖x‖ ≤ R) : chi R x = 1 := by
  apply bump0.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hR).le]
  show R⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ hR, mul_one]
  exact hx

theorem exists_bound_bump0 (n : ℕ) : ∃ B, ∀ y, ‖iteratedFDeriv ℝ n bump0 y‖ ≤ B :=
  (bump0.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
    (bump0.hasCompactSupport.iteratedFDeriv n)

theorem norm_iteratedFDeriv_chi_le {R : ℝ} (hR : 1 ≤ R) (n : ℕ) {B : ℝ}
    (hB : ∀ y, ‖iteratedFDeriv ℝ n bump0 y‖ ≤ B) (x : E3) :
    ‖iteratedFDeriv ℝ n (chi R) x‖ ≤ B := by
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
  set g : E3 →L[ℝ] E3 := R⁻¹ • ContinuousLinearMap.id ℝ E3 with hg
  have hgn : ‖g‖ ≤ 1 := by
    rw [hg, norm_smul]
    refine (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (norm_nonneg _)).trans ?_
    rw [mul_one, Real.norm_of_nonneg (inv_pos.mpr hR0).le]
    exact inv_le_one_of_one_le₀ hR
  rw [chi_eq_comp, g.iteratedFDeriv_comp_right bump0.contDiff x (by exact_mod_cast le_top)]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  calc ‖(iteratedFDeriv ℝ n bump0 (g x)).compContinuousLinearMap fun _ => g‖
      ≤ ‖iteratedFDeriv ℝ n bump0 (g x)‖ * ∏ _i : Fin n, ‖g‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ B * 1 := by
        refine mul_le_mul (hB _) ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) hB0
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) hgn
    _ = B := mul_one B

/-- O campo cortado `Ψ_R = χ_R Ψ`. -/
noncomputable def corte (R : ℝ) (Ψ : E3 → E3) (x : E3) : E3 := chi R x • Ψ x

theorem contDiff_corte (R : ℝ) {Ψ : E3 → E3} (hΨ : ContDiff ℝ ∞ Ψ) : ContDiff ℝ ∞ (corte R Ψ) :=
  (contDiff_chi R).smul hΨ

theorem hasCompactSupport_corte {R : ℝ} (hR : R ≠ 0) (Ψ : E3 → E3) :
    HasCompactSupport (corte R Ψ) :=
  (hasCompactSupport_chi hR).smul_right

/-- Soma das normas das derivadas de ordem `≤ 3`. -/
noncomputable def S3 (Ψ : E3 → E3) (x : E3) : ℝ := ∑ m ∈ Finset.range 4, ‖iteratedFDeriv ℝ m Ψ x‖

theorem S3_nonneg (Ψ : E3 → E3) (x : E3) : 0 ≤ S3 Ψ x :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem le_S3 (Ψ : E3 → E3) {m : ℕ} (hm : m ≤ 3) (x : E3) :
    ‖iteratedFDeriv ℝ m Ψ x‖ ≤ S3 Ψ x := by
  unfold S3
  exact Finset.single_le_sum (f := fun m => ‖iteratedFDeriv ℝ m Ψ x‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (by omega))

/-- **Cota uniforme das derivadas do corte**: `‖Dⁿ Ψ_R‖ ≤ K S₃(Ψ)` para `n ≤ 3`, `R ≥ 1`. -/
theorem exists_bound_corte : ∃ K, 0 ≤ K ∧ ∀ {R : ℝ}, 1 ≤ R → ∀ {Ψ : E3 → E3}, ContDiff ℝ ∞ Ψ →
    ∀ {n : ℕ}, n ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ n (corte R Ψ) x‖ ≤ K * S3 Ψ x := by
  choose B hB using exists_bound_bump0
  set Bm : ℝ := ∑ i ∈ Finset.range 4, |B i| with hBm
  have hBm0 : 0 ≤ Bm := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨8 * Bm, by positivity, fun {R} hR {Ψ} hΨ {n} hn x => ?_⟩
  have hL := norm_iteratedFDeriv_smul_le (contDiff_chi R) hΨ x (n := n) (by exact_mod_cast le_top)
  refine hL.trans ?_
  have hterm : ∀ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (chi R) x‖ *
      ‖iteratedFDeriv ℝ (n - i) Ψ x‖ ≤ (n.choose i : ℝ) * Bm * S3 Ψ x := by
    intro i hi
    have hi3 : i ≤ 3 := by have := Finset.mem_range.mp hi; omega
    have h1 : ‖iteratedFDeriv ℝ i (chi R) x‖ ≤ Bm := by
      refine (norm_iteratedFDeriv_chi_le hR i (B := |B i|) (fun y => (hB i y).trans
        (le_abs_self _)) x).trans ?_
      exact Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (by omega))
    have h2 := le_S3 Ψ (m := n - i) (by omega) x
    have hc : (0 : ℝ) ≤ n.choose i := Nat.cast_nonneg _
    gcongr
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) ≤ 8 := by
    have := Nat.sum_range_choose n
    have h8 : (2 : ℝ) ^ n ≤ 8 := by
      calc (2 : ℝ) ^ n ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hn
        _ = 8 := by norm_num
    calc (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by exact_mod_cast this
      _ ≤ 8 := h8
  have := S3_nonneg Ψ x
  calc (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * Bm * S3 Ψ x ≤ 8 * Bm * S3 Ψ x := by
        gcongr
    _ = 8 * Bm * S3 Ψ x := rfl

/-- Para `R ≥ ‖x‖ + 1`, `Ψ_R = Ψ` perto de `x`. -/
theorem corte_eventuallyEq {R : ℝ} {x : E3} (hR : ‖x‖ + 1 ≤ R) (Ψ : E3 → E3) :
    corte R Ψ =ᶠ[𝓝 x] Ψ := by
  have hR0 : 0 < R := by have := norm_nonneg x; linarith
  filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
  have hy' : ‖y‖ ≤ R := by
    have h1 : ‖y‖ ≤ ‖x‖ + dist y x := by
      have := norm_le_insert' y x
      rw [dist_eq_norm]; linarith [norm_sub_rev x y]
    have h2 : dist y x < 1 := hy
    linarith
  simp [corte, chi_eq_one hR0 hy']

theorem dX_eventuallyEq {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {G₁ G₂ : E3 → W}
    {x : E3} (h : G₁ =ᶠ[𝓝 x] G₂) (j : Fin 3) : dX j G₁ =ᶠ[𝓝 x] dX j G₂ := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  simp [dX, hy]

theorem rot_eventuallyEq {G₁ G₂ : E3 → E3} {x : E3} (h : G₁ =ᶠ[𝓝 x] G₂) :
    rot G₁ =ᶠ[𝓝 x] rot G₂ := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  simp [rot, hy]

theorem lap_eq_of_eventuallyEq {G₁ G₂ : E3 → E3} {x : E3} (h : G₁ =ᶠ[𝓝 x] G₂) :
    lap G₁ x = lap G₂ x := by
  unfold lap
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (dX_eventuallyEq (dX_eventuallyEq h j) j).eq_of_nhds


/-! ### Cotas pontuais dos integrandos -/

open ATK.NSFourierBase in
theorem S3_schwartz (Ψ : SchwartzMap E3 E3) : ∃ C, 0 ≤ C ∧ ∀ x, S3 Ψ x ≤ C * (w 4 x)⁻¹ := by
  set C₀ := 2 ^ 4 * (Finset.Iic ((4 : ℕ), (3 : ℕ))).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Ψ with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  refine ⟨4 * C₀, by positivity, fun x => ?_⟩
  have hw := w_pos 4 x
  have h : ∀ m ∈ Finset.range 4, ‖iteratedFDeriv ℝ m Ψ x‖ ≤ C₀ * (w 4 x)⁻¹ := by
    intro m hm
    have hm3 : m ≤ 3 := by have := Finset.mem_range.mp hm; omega
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((4 : ℕ), (3 : ℕ)))
      (k := 4) (n := m) le_rfl hm3 Ψ x
    rw [← div_eq_mul_inv, le_div_iff₀ hw, mul_comm]
    exact this
  unfold S3
  calc ∑ m ∈ Finset.range 4, ‖iteratedFDeriv ℝ m Ψ x‖ ≤ ∑ _m ∈ Finset.range 4, C₀ * (w 4 x)⁻¹ :=
        Finset.sum_le_sum h
    _ = 4 * C₀ * (w 4 x)⁻¹ := by simp; ring

theorem continuous_S3 {Ψ : E3 → E3} (hΨ : ContDiff ℝ ∞ Ψ) : Continuous (S3 Ψ) := by
  unfold S3
  exact continuous_finsetSum _ fun m _ =>
    (hΨ.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm

theorem abs_conv_term_le (v : E3) {G : E3 → E3} (x : E3) :
    |∑ j, ∑ k, v j * v k * dX j G x k| ≤ 9 * ‖v‖ ^ 2 * ‖iteratedFDeriv ℝ 1 G x‖ := by
  have hv : ∀ i, |v i| ≤ ‖v‖ := fun i => by
    have := PiLp.norm_apply_le v i; rwa [Real.norm_eq_abs] at this
  have hd : ∀ j k, |dX j G x k| ≤ ‖iteratedFDeriv ℝ 1 G x‖ := fun j k => by
    have h1 := PiLp.norm_apply_le (dX j G x) k
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (norm_dX_le G j x)
  calc |∑ j, ∑ k, v j * v k * dX j G x k| ≤ ∑ j, ∑ k, |v j * v k * dX j G x k| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _j : Fin 3, ∑ _k : Fin 3, ‖v‖ * ‖v‖ * ‖iteratedFDeriv ℝ 1 G x‖ := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul (hv j) (hv k) (abs_nonneg _) (norm_nonneg _)) (hd j k)
          (abs_nonneg _) (by positivity)
    _ = 9 * ‖v‖ ^ 2 * ‖iteratedFDeriv ℝ 1 G x‖ := by simp; ring

/-! ### A formulação fraca para `Φ = rot Ψ`, `Ψ` de Schwartz -/

section

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}

open ATK.NSFourierBase in
/-- **Formulação fraca para rotacionais de campos de Schwartz.** -/
theorem formulacao_fraca_rot (h : SolucaoLocal ν u₀ T U P) (Ψ : SchwartzMap E3 E3) {t : ℝ}
    (ht : t ∈ Ico 0 T) :
    (∫ x, inner ℝ (U (x, t)) (rot Ψ x)) - ∫ x, inner ℝ (u₀ x) (rot Ψ x) =
      ∫ s in (0 : ℝ)..t, Bw ν U (rot Ψ) s := by
  have hΨ : ContDiff ℝ ∞ (Ψ : E3 → E3) := Ψ.smooth ⊤
  obtain ⟨K, hK0, hK⟩ := exists_bound_corte
  obtain ⟨CS, hCS0, hCS⟩ := S3_schwartz Ψ
  have hS3c := continuous_S3 hΨ
  have hS3le : ∀ x, S3 Ψ x ≤ CS := fun x => (hCS x).trans
    (mul_le_of_le_one_right hCS0 (inv_le_one_of_one_le₀ (one_le_w 4 x)))
  have hS3sq : Integrable fun x => S3 Ψ x ^ 2 := by
    refine (integrable_w_inv.const_mul (CS * CS)).mono' (hS3c.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    have h1 := hCS x
    have h2 := hS3le x
    have h0 := S3_nonneg Ψ x
    calc S3 Ψ x * S3 Ψ x ≤ CS * (CS * (w 4 x)⁻¹) := mul_le_mul h2 h1 h0 hCS0
      _ = CS * CS * (w 4 x)⁻¹ := by ring
  set R : ℕ → ℝ := fun n => (n : ℝ) + 1 with hRdef
  have hR1 : ∀ n, 1 ≤ R n := fun n => by simp [hRdef]
  have hR0 : ∀ n, R n ≠ 0 := fun n => by have := hR1 n; positivity
  set Φn : ℕ → E3 → E3 := fun n => rot (corte (R n) Ψ) with hΦn
  have hrot : 0 ≤ ‖rotL‖ := ContinuousLinearMap.opNorm_nonneg _
  have hΦnc : ∀ n, ContDiff ℝ ∞ (Φn n) := fun n => contDiff_rot (contDiff_corte _ hΨ)
  -- cotas uniformes
  have bΦ : ∀ n x, ‖Φn n x‖ ≤ ‖rotL‖ * K * S3 Ψ x := by
    intro n x
    have := norm_iteratedFDeriv_rot_le (contDiff_corte (R n) hΨ) 0 x
    rw [norm_iteratedFDeriv_zero] at this
    refine this.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hK (hR1 n) hΨ (by norm_num) x) hrot
  have bD1 : ∀ n x, ‖iteratedFDeriv ℝ 1 (Φn n) x‖ ≤ ‖rotL‖ * K * S3 Ψ x := by
    intro n x
    refine (norm_iteratedFDeriv_rot_le (contDiff_corte (R n) hΨ) 1 x).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hK (hR1 n) hΨ (by norm_num) x) hrot
  have bL : ∀ n x, ‖lap (Φn n) x‖ ≤ 3 * (‖rotL‖ * K * S3 Ψ x) := by
    intro n x
    refine (norm_lap_le (hΦnc n) x).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    refine (norm_iteratedFDeriv_rot_le (contDiff_corte (R n) hΨ) 2 x).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hK (hR1 n) hΨ (by norm_num) x) hrot
  -- convergência pontual (igualdade eventual)
  have ev : ∀ x, ∀ᶠ n in atTop, corte (R n) Ψ =ᶠ[𝓝 x] (Ψ : E3 → E3) := by
    intro x
    filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
    refine corte_eventuallyEq ?_ Ψ
    have : ‖x‖ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    simp only [hRdef]; linarith
  have evΦ : ∀ x, ∀ᶠ n in atTop, Φn n x = rot Ψ x := fun x =>
    (ev x).mono fun n hn => (rot_eventuallyEq hn).eq_of_nhds
  have evL : ∀ x, ∀ᶠ n in atTop, lap (Φn n) x = lap (rot Ψ) x := fun x =>
    (ev x).mono fun n hn => lap_eq_of_eventuallyEq (rot_eventuallyEq hn)
  have evD : ∀ x j, ∀ᶠ n in atTop, dX j (Φn n) x = dX j (rot Ψ) x := fun x j =>
    (ev x).mono fun n hn => (dX_eventuallyEq (rot_eventuallyEq hn) j).eq_of_nhds
  -- energia em `[0, t]`
  obtain ⟨CE, hCE⟩ := h.2.2.2.2.2 t (lt_of_le_of_lt le_rfl ht.2)
  have hUc : ∀ τ ∈ Icc 0 t, Continuous fun x => U (x, τ) := fun τ hτ =>
    continuous_fatia_U h.1 ⟨hτ.1, hτ.2.trans_lt ht.2⟩
  -- limite de `∫ ⟪U(τ), Φₙ⟫`
  have limA : ∀ τ ∈ Icc 0 t, Tendsto (fun n => ∫ x, inner ℝ (U (x, τ)) (Φn n x)) atTop
      (𝓝 (∫ x, inner ℝ (U (x, τ)) (rot Ψ x))) := by
    intro τ hτ
    have hE := (hCE τ hτ).1.1
    refine tendsto_integral_of_dominated_convergence
      (fun x => ‖rotL‖ * K * (‖U (x, τ)‖ ^ 2 + S3 Ψ x ^ 2)) (fun n => ?_)
      ((hE.add hS3sq).const_mul _) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · exact ((hUc τ hτ).inner (hΦnc n).continuous).aestronglyMeasurable
    · refine (norm_inner_le_norm _ _).trans ?_
      have h1 := bΦ n x
      have hS := S3_nonneg Ψ x
      have hrk : 0 ≤ ‖rotL‖ * K := mul_nonneg hrot hK0
      calc ‖U (x, τ)‖ * ‖Φn n x‖ ≤ ‖U (x, τ)‖ * (‖rotL‖ * K * S3 Ψ x) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = ‖rotL‖ * K * (‖U (x, τ)‖ * S3 Ψ x) := by ring
        _ ≤ ‖rotL‖ * K * (‖U (x, τ)‖ ^ 2 + S3 Ψ x ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hrk
            nlinarith [sq_nonneg (‖U (x, τ)‖ - S3 Ψ x), norm_nonneg (U (x, τ))]
    · exact tendsto_const_nhds.congr' ((evΦ x).mono fun n hn => by simp only [hn])
  -- limite de `Bw`
  have limB : ∀ τ ∈ Icc 0 t, Tendsto (fun n => Bw ν U (Φn n) τ) atTop
      (𝓝 (Bw ν U (rot Ψ) τ)) := by
    intro τ hτ
    have hE := (hCE τ hτ).1.1
    unfold Bw
    refine Tendsto.add (Tendsto.const_mul ν ?_) ?_
    · refine tendsto_integral_of_dominated_convergence
        (fun x => 3 * (‖rotL‖ * K) * (‖U (x, τ)‖ ^ 2 + S3 Ψ x ^ 2)) (fun n => ?_)
        ((hE.add hS3sq).const_mul _) (fun n => Eventually.of_forall fun x => ?_)
        (Eventually.of_forall fun x => ?_)
      · exact ((hUc τ hτ).inner (contDiff_lap (hΦnc n)).continuous).aestronglyMeasurable
      · refine (norm_inner_le_norm _ _).trans ?_
        have h1 := bL n x
        have hrk : 0 ≤ 3 * (‖rotL‖ * K) := by positivity
        calc ‖U (x, τ)‖ * ‖lap (Φn n) x‖ ≤ ‖U (x, τ)‖ * (3 * (‖rotL‖ * K * S3 Ψ x)) :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = 3 * (‖rotL‖ * K) * (‖U (x, τ)‖ * S3 Ψ x) := by ring
          _ ≤ 3 * (‖rotL‖ * K) * (‖U (x, τ)‖ ^ 2 + S3 Ψ x ^ 2) := by
              refine mul_le_mul_of_nonneg_left ?_ hrk
              nlinarith [sq_nonneg (‖U (x, τ)‖ - S3 Ψ x), norm_nonneg (U (x, τ)),
                S3_nonneg Ψ x]
      · exact tendsto_const_nhds.congr' ((evL x).mono fun n hn => by simp only [hn])
    · refine tendsto_integral_of_dominated_convergence
        (fun x => 9 * (‖rotL‖ * K * CS) * ‖U (x, τ)‖ ^ 2) (fun n => ?_)
        (hE.const_mul _) (fun n => Eventually.of_forall fun x => ?_)
        (Eventually.of_forall fun x => ?_)
      · have hu' : ∀ i, Continuous fun x => U (x, τ) i := fun i =>
          (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous.comp (hUc τ hτ)
        have hd' : ∀ j k, Continuous fun x => dX j (Φn n) x k := fun j k =>
          (EuclideanSpace.proj k : E3 →L[ℝ] ℝ).continuous.comp (continuous_dX (hΦnc n) j)
        exact (continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
          ((hu' j).mul (hu' k)).mul (hd' j k)).aestronglyMeasurable
      · rw [Real.norm_eq_abs]
        refine (abs_conv_term_le (U (x, τ)) x).trans ?_
        have h1 := bD1 n x
        have h2 : ‖rotL‖ * K * S3 Ψ x ≤ ‖rotL‖ * K * CS :=
          mul_le_mul_of_nonneg_left (hS3le x) (mul_nonneg hrot hK0)
        calc 9 * ‖U (x, τ)‖ ^ 2 * ‖iteratedFDeriv ℝ 1 (Φn n) x‖
            ≤ 9 * ‖U (x, τ)‖ ^ 2 * (‖rotL‖ * K * CS) :=
              mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
          _ = 9 * (‖rotL‖ * K * CS) * ‖U (x, τ)‖ ^ 2 := by ring
      · refine tendsto_const_nhds.congr' ?_
        have hall : ∀ᶠ n in atTop, ∀ j, dX j (Φn n) x = dX j (rot Ψ) x := by
          rw [eventually_all]; exact fun j => evD x j
        exact hall.mono fun n hn => by simp only [hn]
  -- a identidade para cada `n` e a passagem ao limite
  have hid : ∀ n, (∫ x, inner ℝ (U (x, t)) (Φn n x)) - ∫ x, inner ℝ (u₀ x) (Φn n x) =
      ∫ s in (0 : ℝ)..t, Bw ν U (Φn n) s := fun n =>
    formulacao_fraca h (hΦnc n) (hasCompactSupport_rot (hasCompactSupport_corte (hR0 n) _))
      (div_rot (contDiff_corte _ hΨ)) ht
  have hu0 : ∀ G : E3 → E3, ∫ x, inner ℝ (u₀ x) (G x) = ∫ x, inner ℝ (U (x, 0)) (G x) :=
    fun G => by simp_rw [h.2.2.1]
  have lim1 : Tendsto (fun n => (∫ x, inner ℝ (U (x, t)) (Φn n x)) -
      ∫ x, inner ℝ (u₀ x) (Φn n x)) atTop
      (𝓝 ((∫ x, inner ℝ (U (x, t)) (rot Ψ x)) - ∫ x, inner ℝ (u₀ x) (rot Ψ x))) := by
    simp_rw [hu0]
    exact (limA t ⟨ht.1, le_rfl⟩).sub (limA 0 ⟨le_rfl, ht.1⟩)
  -- limite do lado direito (convergência dominada em `s`)
  have hBb : ∀ n, ∀ s ∈ Icc 0 t, ‖Bw ν U (Φn n) s‖ ≤
      |ν| * (3 * (‖rotL‖ * K) * (CE + ∫ x, S3 Ψ x ^ 2)) + 9 * (‖rotL‖ * K * CS) * CE := by
    intro n s hs
    have hE := (hCE s hs).1
    unfold Bw
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine (norm_integral_le_of_norm_le (((hE.1.add hS3sq).const_mul
        (3 * (‖rotL‖ * K)))) (Eventually.of_forall fun x => ?_)).trans ?_
      · refine (norm_inner_le_norm _ _).trans ?_
        have h1 := bL n x
        have hrk : 0 ≤ 3 * (‖rotL‖ * K) := by positivity
        calc ‖U (x, s)‖ * ‖lap (Φn n) x‖ ≤ ‖U (x, s)‖ * (3 * (‖rotL‖ * K * S3 Ψ x)) :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = 3 * (‖rotL‖ * K) * (‖U (x, s)‖ * S3 Ψ x) := by ring
          _ ≤ 3 * (‖rotL‖ * K) * (‖U (x, s)‖ ^ 2 + S3 Ψ x ^ 2) := by
              refine mul_le_mul_of_nonneg_left ?_ hrk
              nlinarith [sq_nonneg (‖U (x, s)‖ - S3 Ψ x), norm_nonneg (U (x, s)),
                S3_nonneg Ψ x]
      · simp only [Pi.add_apply]
        rw [integral_const_mul, integral_add hE.1 hS3sq]
        have : 0 ≤ 3 * (‖rotL‖ * K) := by positivity
        exact mul_le_mul_of_nonneg_left (by linarith [hE.2]) this
    · refine (norm_integral_le_of_norm_le (hE.1.const_mul (9 * (‖rotL‖ * K * CS)))
        (Eventually.of_forall fun x => ?_)).trans ?_
      · rw [Real.norm_eq_abs]
        refine (abs_conv_term_le (U (x, s)) x).trans ?_
        have h1 := bD1 n x
        have h2 : ‖rotL‖ * K * S3 Ψ x ≤ ‖rotL‖ * K * CS :=
          mul_le_mul_of_nonneg_left (hS3le x) (mul_nonneg hrot hK0)
        calc 9 * ‖U (x, s)‖ ^ 2 * ‖iteratedFDeriv ℝ 1 (Φn n) x‖
            ≤ 9 * ‖U (x, s)‖ ^ 2 * (‖rotL‖ * K * CS) :=
              mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
          _ = 9 * (‖rotL‖ * K * CS) * ‖U (x, s)‖ ^ 2 := by ring
      · rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hE.2 (by positivity)
  have lim2 : Tendsto (fun n => ∫ s in (0 : ℝ)..t, Bw ν U (Φn n) s) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, Bw ν U (rot Ψ) s)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => |ν| * (3 * (‖rotL‖ * K) * (CE + ∫ x, S3 Ψ x ^ 2)) +
        9 * (‖rotL‖ * K * CS) * CE) (Eventually.of_forall fun n => ?_)
      (Eventually.of_forall fun n => Eventually.of_forall fun s hs => ?_)
      intervalIntegrable_const (Eventually.of_forall fun s hs => ?_)
    · have hc := continuousOn_Bw (ν := ν) h.1 (hΦnc n)
        (hasCompactSupport_rot (hasCompactSupport_corte (hR0 n) _)) ht
      rw [uIoc_of_le ht.1]
      exact (hc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · rw [uIoc_of_le ht.1] at hs
      exact hBb n s (Ioc_subset_Icc_self hs)
    · rw [uIoc_of_le ht.1] at hs
      exact limB s (Ioc_subset_Icc_self hs)
  have e := tendsto_nhds_unique (lim1.congr fun n => hid n) lim2
  exact e

end

end ATK.NSCorte

#print axioms ATK.NSCorte.cmp_apply
#print axioms ATK.NSCorte.rotL_apply
#print axioms ATK.NSCorte.contDiff_rot
#print axioms ATK.NSCorte.hasCompactSupport_rot
#print axioms ATK.NSCorte.dX_rot
#print axioms ATK.NSCorte.div_rot
#print axioms ATK.NSCorte.norm_iteratedFDeriv_rot_le
#print axioms ATK.NSCorte.norm_dX_le
#print axioms ATK.NSCorte.dX_dX_eq
#print axioms ATK.NSCorte.norm_lap_le
#print axioms ATK.NSCorte.chi_eq_comp
#print axioms ATK.NSCorte.contDiff_chi
#print axioms ATK.NSCorte.hasCompactSupport_chi
#print axioms ATK.NSCorte.chi_eq_one
#print axioms ATK.NSCorte.exists_bound_bump0
#print axioms ATK.NSCorte.norm_iteratedFDeriv_chi_le
#print axioms ATK.NSCorte.contDiff_corte
#print axioms ATK.NSCorte.hasCompactSupport_corte
#print axioms ATK.NSCorte.S3_nonneg
#print axioms ATK.NSCorte.le_S3
#print axioms ATK.NSCorte.exists_bound_corte
#print axioms ATK.NSCorte.corte_eventuallyEq
#print axioms ATK.NSCorte.dX_eventuallyEq
#print axioms ATK.NSCorte.rot_eventuallyEq
#print axioms ATK.NSCorte.lap_eq_of_eventuallyEq
#print axioms ATK.NSCorte.S3_schwartz
#print axioms ATK.NSCorte.continuous_S3
#print axioms ATK.NSCorte.abs_conv_term_le
#print axioms ATK.NSCorte.formulacao_fraca_rot
