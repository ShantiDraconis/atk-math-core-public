import ATK.NSFracaFourier

/-!
# ATK — Navier–Stokes: a fórmula de Duhamel para uma solução suave qualquer

Camada 20 do ataque a B3 (unicidade fraca–forte, passo U-4). A formulação fraca no lado de Fourier
(`ATK.NSFracaFourier.fraca_fourier`) só usa campos-teste fixos no tempo. Testando contra
`ψ_r = e^{−4π²ν‖ξ‖²(t−r)} G` (com `G` de suporte compacto) obtém-se a forma integrada da fórmula de
Duhamel:

`∫ ⟪b(t), m_G⟫ = ∫ ⟪e^{−4π²ν‖ξ‖²t} â₀, m_G⟫ − ∫₀ᵗ ∫ ⟪N(s), m_{e^{−4π²ν‖ξ‖²(t−s)} G}⟫ ds`.

A prova não deriva nada no tempo: `H(r) = ∫ ⟪b(r), m_{ψ_r}⟫ + ∫₀ʳ ∫ ⟪N(s), m_{ψ_s}⟫ ds` satisfaz
`|H(r') − H(r)| ≤ K (r' − r)²`, logo é constante (`const_of_sq`).

**CLOSED_MATH continua false.**
-/

open MeasureTheory FourierTransform SchwartzMap Filter Set ComplexConjugate
open scoped ContDiff InnerProductSpace Real

namespace ATK.NSDuhamel

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSSuave ATK.NSFisico ATK.NSFraca ATK.NSCorte ATK.NSL2
  ATK.NSDado ATK.NSPicard ATK.NSFracaFourier

/-! ### Funções com incremento quadrático são constantes -/

theorem const_of_sq {H : ℝ → ℂ} {t δ K : ℝ} (ht : 0 ≤ t) (hδ : 0 < δ)
    (h : ∀ r r', 0 ≤ r → r ≤ r' → r' ≤ t → r' - r ≤ δ → ‖H r' - H r‖ ≤ K * (r' - r) ^ 2) :
    H t = H 0 := by
  rcases ht.eq_or_lt with h0 | htpos
  · rw [← h0]
  have hK : 0 ≤ K := by
    have := h 0 (min t δ) le_rfl (le_min ht hδ.le) (min_le_left _ _) (by simp)
    have hm : 0 < min t δ := lt_min htpos hδ
    have h2 : 0 < (min t δ - 0) ^ 2 := by positivity
    by_contra hneg
    have hneg' : K < 0 := lt_of_not_ge hneg
    have : K * (min t δ - 0) ^ 2 < 0 := mul_neg_of_neg_of_pos hneg' h2
    linarith [norm_nonneg (H (min t δ) - H 0)]
  have key : ∀ n : ℕ, 0 < n → t / n ≤ δ → ‖H t - H 0‖ ≤ K * t ^ 2 / n := by
    intro n hn hnδ
    have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    set x : ℕ → ℝ := fun i => t * i / n with hx
    have hx0 : x 0 = 0 := by simp [hx]
    have hxn : x n = t := by simp [hx, hnr.ne']
    have hsum : H t - H 0 = ∑ i ∈ Finset.range n, (H (x (i + 1)) - H (x i)) := by
      rw [Finset.sum_range_sub (fun i => H (x i)), hxn, hx0]
    rw [hsum]
    calc ‖∑ i ∈ Finset.range n, (H (x (i + 1)) - H (x i))‖
        ≤ ∑ i ∈ Finset.range n, ‖H (x (i + 1)) - H (x i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range n, K * (t / n) ^ 2 := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : (i : ℝ) + 1 ≤ n := by
            have := Finset.mem_range.mp hi; exact_mod_cast this
          have hd : x (i + 1) - x i = t / n := by simp [hx]; field_simp; ring
          have h1 : 0 ≤ x i := by simp only [hx]; positivity
          have h2 : x i ≤ x (i + 1) := by linarith [div_nonneg ht hnr.le]
          have h3 : x (i + 1) ≤ t := by
            simp only [hx]; push_cast
            rw [div_le_iff₀ hnr]; nlinarith
          have := h (x i) (x (i + 1)) h1 h2 h3 (by rw [hd]; exact hnδ)
          rwa [hd] at this
      _ = K * t ^ 2 / n := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
  by_contra hne
  have hpos : 0 < ‖H t - H 0‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (K * t ^ 2 / ‖H t - H 0‖ + t / δ + 1)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
    exact_mod_cast this
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn0
  have hnδ : t / n ≤ δ := by
    rw [div_le_iff₀ hnr]
    have : t / δ < n := by linarith [div_nonneg (mul_nonneg hK (sq_nonneg t)) hpos.le]
    rw [div_lt_iff₀ hδ] at this; linarith
  have h1 := key n hn0 hnδ
  have h2 : K * t ^ 2 / n < ‖H t - H 0‖ := by
    rw [div_lt_iff₀ hnr]
    have : K * t ^ 2 / ‖H t - H 0‖ < n := by linarith [div_nonneg ht hδ.le]
    rw [div_lt_iff₀ hpos] at this; linarith
  linarith

/-! ### Estimativas da exponencial -/

theorem abs_exp_sub_exp_le {q a b : ℝ} (hq : 0 ≤ q) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-(q * a)) - Real.exp (-(q * b))| ≤ q * |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, abs_sub_comm a b]; exact this hb ha (le_of_not_ge hab)
  have h1 : Real.exp (-(q * b)) ≤ Real.exp (-(q * a)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [abs_of_nonneg (sub_nonneg.mpr h1), abs_of_nonpos (sub_nonpos.mpr hab)]
  have h2 : Real.exp (-(q * b)) = Real.exp (-(q * a)) * Real.exp (-(q * (b - a))) := by
    rw [← Real.exp_add]; ring_nf
  have h3 : 1 - q * (b - a) ≤ Real.exp (-(q * (b - a))) := by
    have := Real.add_one_le_exp (-(q * (b - a))); linarith
  have h4 : Real.exp (-(q * a)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have h5 : 0 ≤ q * (b - a) := mul_nonneg hq (by linarith)
  rw [h2]
  nlinarith [Real.exp_pos (-(q * a))]

theorem abs_exp_taylor_le {q a b t : ℝ} (hq : 0 ≤ q) (hab : a ≤ b) (hbt : b ≤ t)
    (hsmall : q * (b - a) ≤ 1) :
    |Real.exp (-(q * (t - b))) - Real.exp (-(q * (t - a))) -
        (b - a) * q * Real.exp (-(q * (t - a)))| ≤ (q * (b - a)) ^ 2 := by
  have h0 : 0 ≤ q * (b - a) := mul_nonneg hq (by linarith)
  have e : Real.exp (-(q * (t - b))) = Real.exp (-(q * (t - a))) * Real.exp (q * (b - a)) := by
    rw [← Real.exp_add]; ring_nf
  have he : Real.exp (-(q * (t - b))) - Real.exp (-(q * (t - a))) -
      (b - a) * q * Real.exp (-(q * (t - a))) =
      Real.exp (-(q * (t - a))) * (Real.exp (q * (b - a)) - 1 - q * (b - a)) := by
    rw [e]; ring
  rw [he, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := Real.abs_exp_sub_one_sub_id_le (x := q * (b - a)) (by rw [abs_of_nonneg h0]; exact hsmall)
  have h2 : Real.exp (-(q * (t - a))) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  calc Real.exp (-(q * (t - a))) * |Real.exp (q * (b - a)) - 1 - q * (b - a)|
      ≤ 1 * (q * (b - a)) ^ 2 :=
        mul_le_mul h2 h1 (abs_nonneg _) zero_le_one
    _ = (q * (b - a)) ^ 2 := one_mul _

/-! ### O produto vetorial e o campo-teste -/

theorem abs_coord_le (v : C3) (k : Fin 3) : ‖v k‖ ≤ ‖v‖ := PiLp.norm_apply_le v k

theorem norm_cr_le (v w : C3) : ‖cr v w‖ ≤ 4 * (‖v‖ * ‖w‖) := by
  have hc : ∀ i j k l : Fin 3, ‖v i * w j - v k * w l‖ ≤ 2 * (‖v‖ * ‖w‖) := by
    intro i j k l
    calc ‖v i * w j - v k * w l‖ ≤ ‖v i‖ * ‖w j‖ + ‖v k‖ * ‖w l‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ ‖v‖ * ‖w‖ + ‖v‖ * ‖w‖ := add_le_add
          (mul_le_mul (abs_coord_le v i) (abs_coord_le w j) (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul (abs_coord_le v k) (abs_coord_le w l) (norm_nonneg _) (norm_nonneg _))
      _ = 2 * (‖v‖ * ‖w‖) := by ring
  have hsq : ‖cr v w‖ ^ 2 ≤ (4 * (‖v‖ * ‖w‖)) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, cr_apply0, cr_apply1, cr_apply2]
    have h0 := hc 1 2 2 1
    have h1 := hc 2 0 0 2
    have h2 := hc 0 1 1 0
    have hn : 0 ≤ ‖v‖ * ‖w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    nlinarith [norm_nonneg (v 1 * w 2 - v 2 * w 1), norm_nonneg (v 2 * w 0 - v 0 * w 2),
      norm_nonneg (v 0 * w 1 - v 1 * w 0)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

theorem norm_mt_le (H : E3 → C3) (ξ : E3) : ‖mtf H ξ‖ ≤ 8 * π * (‖ξ‖ * ‖H ξ‖) := by
  rw [mtf, norm_smul]
  have h1 : ‖((2 * π : ℝ) * Complex.I : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [h1]
  calc 2 * π * ‖cr (cpx ξ) (H ξ)‖ ≤ 2 * π * (4 * (‖cpx ξ‖ * ‖H ξ‖)) :=
        mul_le_mul_of_nonneg_left (norm_cr_le _ _) (by positivity)
    _ = 8 * π * (‖ξ‖ * ‖H ξ‖) := by rw [norm_cpx]; ring

theorem mt_smul (H : E3 → C3) (φ : E3 → ℂ) (ξ : E3) :
    mtf (fun η => φ η • H η) ξ = φ ξ • mtf H ξ := by
  rw [mtf, mtf, cr_smul_right, smul_comm]

theorem continuous_cr : Continuous fun p : C3 × C3 => cr p.1 p.2 := by
  unfold cr
  refine (PiLp.continuous_toLp 2 _).comp ?_
  refine continuous_pi fun k => ?_
  fin_cases k <;> simp only <;> fun_prop

theorem continuous_mt {H : E3 → C3} (hH : Continuous H) : Continuous (mtf H) := by
  have e : mtf H = fun ξ => ((2 * π : ℝ) * Complex.I : ℂ) • cr (cpx ξ) (H ξ) := rfl
  rw [e]
  exact (continuous_const (y := ((2 * π : ℝ) * Complex.I : ℂ))).smul
    (continuous_cr.comp (continuous_cpx.prodMk hH))

/-- O campo-teste `φ G`. -/
noncomputable def tst (G : E3 → C3) (φ : E3 → ℂ) (ξ : E3) : C3 := φ ξ • G ξ

/-- A bola fechada como indicadora. -/
noncomputable def chiB (R : ℝ) (ξ : E3) : ℝ := (Metric.closedBall (0 : E3) R).indicator 1 ξ

theorem integrable_chiB (R : ℝ) : Integrable (chiB R) := by
  unfold chiB
  exact (integrable_indicator_iff measurableSet_closedBall).mpr
    (integrableOn_const (measure_closedBall_lt_top).ne)

theorem chiB_nonneg (R : ℝ) (ξ : E3) : 0 ≤ chiB R ξ := by
  unfold chiB; by_cases h : ξ ∈ Metric.closedBall (0 : E3) R <;> simp [h]

theorem chiB_sq (R : ℝ) (ξ : E3) : chiB R ξ ^ 2 = chiB R ξ := by
  unfold chiB; by_cases h : ξ ∈ Metric.closedBall (0 : E3) R <;> simp [h]

/-- Campo localizado: suporte em `‖ξ‖ ≤ R` e `‖H‖ ≤ M`. -/
structure Loc (R M : ℝ) (H : E3 → C3) : Prop where
  cont : Continuous H
  bound : ∀ ξ, ‖H ξ‖ ≤ M
  supp : ∀ ξ, R < ‖ξ‖ → H ξ = 0

theorem Loc.norm_mt_le {R M : ℝ} {H : E3 → C3} (hH : Loc R M H) (hR : 0 ≤ R) (ξ : E3) :
    ‖mtf H ξ‖ ≤ 8 * π * R * M * chiB R ξ := by
  by_cases hξ : ‖ξ‖ ≤ R
  · have hc : chiB R ξ = 1 := by
      unfold chiB; rw [indicator_of_mem (by simpa using hξ)]; rfl
    rw [hc, mul_one]
    refine (_root_.ATK.NSDuhamel.norm_mt_le H ξ).trans ?_
    have hM : 0 ≤ M := (norm_nonneg _).trans (hH.bound ξ)
    have := mul_le_mul hξ (hH.bound ξ) (norm_nonneg _) hR
    nlinarith [Real.pi_pos]
  · replace hξ : R < ‖ξ‖ := lt_of_not_ge hξ
    have hz : cr (cpx ξ) 0 = 0 := by
      ext k; fin_cases k <;> simp [cr_apply0, cr_apply1, cr_apply2]
    have h0 : mtf H ξ = 0 := by rw [mtf, hH.supp ξ hξ, hz, smul_zero]
    rw [h0, norm_zero]
    have hM : 0 ≤ M := (norm_nonneg _).trans (hH.bound 0)
    exact mul_nonneg (by positivity) (chiB_nonneg R ξ)

theorem integral_chiB (R : ℝ) : ∫ ξ, chiB R ξ = volume.real (Metric.closedBall (0 : E3) R) :=
  integral_indicator_one measurableSet_closedBall

/-! ### Os pareamentos `A` e `n` -/

/-- `A(s, H) = ∫ ⟪b(s), m_H⟫`. -/
noncomputable def Ap (U : E3 × ℝ → E3) (s : ℝ) (H : E3 → C3) : ℂ := ∫ ξ, ⟪bF U s ξ, mtf H ξ⟫_ℂ

/-- `n(s, H) = ∫ ⟪N(s), m_H⟫`. -/
noncomputable def np (U : E3 × ℝ → E3) (s : ℝ) (H : E3 → C3) : ℂ := ∫ ξ, ⟪NU U s ξ, mtf H ξ⟫_ℂ

section Est

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}

theorem integral_norm_sq_bF (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) :
    ∫ ξ, ‖bF U s ξ‖ ^ 2 = ∫ x, ‖U (x, s)‖ ^ 2 := by
  rw [bF, integral_norm_sq_FL (memLp_cU h hs)]
  simp_rw [norm_cpx]

theorem memLp_bF (U : E3 × ℝ → E3) (s : ℝ) : MemLp (bF U s) 2 := memLp_FL _

theorem norm_NU_le (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) (ξ : E3) :
    ‖NU U s ξ‖ ≤ 2 * π * ‖ξ‖ * ∫ x, ‖U (x, s)‖ ^ 2 := by
  rw [NU, norm_smul]
  have h1 : ‖((2 * π : ℝ) * Complex.I : ℂ)‖ = 2 * π := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [h1]
  suffices hs2 : ‖𝓕 (fun x => ⟪cpx ξ, cpx (U (x, s))⟫_ℂ • cpx (U (x, s))) ξ‖ ≤
      ‖ξ‖ * ∫ x, ‖U (x, s)‖ ^ 2 by
    calc 2 * π * ‖𝓕 (fun x => ⟪cpx ξ, cpx (U (x, s))⟫_ℂ • cpx (U (x, s))) ξ‖
        ≤ 2 * π * (‖ξ‖ * ∫ x, ‖U (x, s)‖ ^ 2) := mul_le_mul_of_nonneg_left hs2 (by positivity)
      _ = 2 * π * ‖ξ‖ * ∫ x, ‖U (x, s)‖ ^ 2 := by ring
  refine (norm_fourier_le_L1 ξ).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
    ((integrable_sq_U h hs).const_mul _) (Eventually.of_forall fun x => ?_)
  simp only
  rw [norm_smul, norm_cpx]
  have := norm_inner_le_norm (𝕜 := ℂ) (cpx ξ) (cpx (U (x, s)))
  rw [norm_cpx, norm_cpx] at this
  calc ‖⟪cpx ξ, cpx (U (x, s))⟫_ℂ‖ * ‖U (x, s)‖ ≤ ‖ξ‖ * ‖U (x, s)‖ * ‖U (x, s)‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = ‖ξ‖ * ‖U (x, s)‖ ^ 2 := by ring

theorem continuous_NU (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) :
    Continuous (NU U s) := by
  have e : NU U s = fun ξ => ∑ j, cj j ξ • 𝓕 (fun x => cpx (U (x, s) j • U (x, s))) ξ :=
    funext (NU_eq h hs)
  rw [e]
  exact continuous_finsetSum _ fun j _ =>
    (continuous_cj j).smul (continuous_fourier_L1 (integrable_cpx_mul h hs j))

theorem integrable_Ap (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T)
    {R M : ℝ} (hR : 0 ≤ R) {H : E3 → C3} (hH : Loc R M H) :
    Integrable fun ξ => ⟪bF U s ξ, mtf H ξ⟫_ℂ := by
  have hb := memLp_bF U s
  have hb2 := integrable_sq_norm_of_memLp hb
  refine (((hb2.add (integrable_chiB R)).div_const 2).const_mul (8 * π * R * M)).mono'
    (hb.aestronglyMeasurable.inner (continuous_mt hH.cont).aestronglyMeasurable)
    (Eventually.of_forall fun ξ => ?_)
  have h1 := hH.norm_mt_le hR ξ
  have h2 := norm_inner_le_norm (𝕜 := ℂ) (bF U s ξ) (mtf H ξ)
  have hM : 0 ≤ M := (norm_nonneg _).trans (hH.bound 0)
  have hc := chiB_nonneg R ξ
  have hc2 := chiB_sq R ξ
  have hK : 0 ≤ 8 * π * R * M := by positivity
  have h3 : ‖bF U s ξ‖ * chiB R ξ ≤ (‖bF U s ξ‖ ^ 2 + chiB R ξ) / 2 := by
    nlinarith [sq_nonneg (‖bF U s ξ‖ - chiB R ξ)]
  calc ‖⟪bF U s ξ, mtf H ξ⟫_ℂ‖ ≤ ‖bF U s ξ‖ * (8 * π * R * M * chiB R ξ) :=
        h2.trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
    _ = 8 * π * R * M * (‖bF U s ξ‖ * chiB R ξ) := by ring
    _ ≤ 8 * π * R * M * ((‖bF U s ξ‖ ^ 2 + chiB R ξ) / 2) :=
        mul_le_mul_of_nonneg_left h3 hK

theorem norm_Ap_le (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) {C : ℝ}
    (hC : ∫ x, ‖U (x, s)‖ ^ 2 ≤ C) {R M : ℝ} (hR : 0 ≤ R) {H : E3 → C3} (hH : Loc R M H) :
    ‖Ap U s H‖ ≤ 4 * π * R * M * (C + volume.real (Metric.closedBall (0 : E3) R)) := by
  have hb := memLp_bF U s
  have hb2 := integrable_sq_norm_of_memLp hb
  have hM : 0 ≤ M := (norm_nonneg _).trans (hH.bound 0)
  have hK : 0 ≤ 8 * π * R * M := by positivity
  calc ‖Ap U s H‖ ≤ ∫ ξ, 8 * π * R * M * ((‖bF U s ξ‖ ^ 2 + chiB R ξ) / 2) := by
        refine norm_integral_le_of_norm_le
          (((hb2.add (integrable_chiB R)).div_const 2).const_mul _)
          (Eventually.of_forall fun ξ => ?_)
        have h1 := hH.norm_mt_le hR ξ
        have h2 := norm_inner_le_norm (𝕜 := ℂ) (bF U s ξ) (mtf H ξ)
        have hc := chiB_nonneg R ξ
        have h3 : ‖bF U s ξ‖ * chiB R ξ ≤ (‖bF U s ξ‖ ^ 2 + chiB R ξ) / 2 := by
          nlinarith [sq_nonneg (‖bF U s ξ‖ - chiB R ξ), chiB_sq R ξ]
        calc ‖⟪bF U s ξ, mtf H ξ⟫_ℂ‖ ≤ ‖bF U s ξ‖ * (8 * π * R * M * chiB R ξ) :=
              h2.trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
          _ = 8 * π * R * M * (‖bF U s ξ‖ * chiB R ξ) := by ring
          _ ≤ 8 * π * R * M * ((‖bF U s ξ‖ ^ 2 + chiB R ξ) / 2) :=
              mul_le_mul_of_nonneg_left h3 hK
    _ = 4 * π * R * M * ((∫ ξ, ‖bF U s ξ‖ ^ 2) + ∫ ξ, chiB R ξ) := by
        rw [integral_const_mul, integral_div, integral_add hb2 (integrable_chiB R)]; ring
    _ ≤ 4 * π * R * M * (C + volume.real (Metric.closedBall (0 : E3) R)) := by
        rw [integral_norm_sq_bF h hs, integral_chiB]
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem integrable_np (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T)
    {R M : ℝ} (hR : 0 ≤ R) {H : E3 → C3} (hH : Loc R M H) :
    Integrable fun ξ => ⟪NU U s ξ, mtf H ξ⟫_ℂ := by
  set C := ∫ x, ‖U (x, s)‖ ^ 2
  have hC0 : 0 ≤ C := integral_nonneg fun _ => sq_nonneg _
  have hM : 0 ≤ M := (norm_nonneg _).trans (hH.bound 0)
  refine ((integrable_chiB R).const_mul (16 * π ^ 2 * R ^ 2 * C * M)).mono'
    ((continuous_NU h hs).aestronglyMeasurable.inner (continuous_mt hH.cont).aestronglyMeasurable)
    (Eventually.of_forall fun ξ => ?_)
  have h1 := hH.norm_mt_le hR ξ
  have h2 := norm_inner_le_norm (𝕜 := ℂ) (NU U s ξ) (mtf H ξ)
  have h3 := norm_NU_le h hs ξ
  have hc := chiB_nonneg R ξ
  have h4 : ‖ξ‖ * chiB R ξ ≤ R * chiB R ξ := by
    by_cases hξ : ‖ξ‖ ≤ R
    · exact mul_le_mul_of_nonneg_right hξ hc
    · have : chiB R ξ = 0 := by
        unfold chiB; rw [indicator_of_notMem (by simpa using hξ)]
      rw [this]; simp
  calc ‖⟪NU U s ξ, mtf H ξ⟫_ℂ‖ ≤ (2 * π * ‖ξ‖ * C) * (8 * π * R * M * chiB R ξ) :=
        h2.trans (mul_le_mul h3 h1 (norm_nonneg _) (by positivity))
    _ = 16 * π ^ 2 * R * C * M * (‖ξ‖ * chiB R ξ) := by ring
    _ ≤ 16 * π ^ 2 * R * C * M * (R * chiB R ξ) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 16 * π ^ 2 * R ^ 2 * C * M * chiB R ξ := by ring

theorem norm_np_le (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) {C : ℝ}
    (hC : ∫ x, ‖U (x, s)‖ ^ 2 ≤ C) {R M : ℝ} (hR : 0 ≤ R) {H : E3 → C3} (hH : Loc R M H) :
    ‖np U s H‖ ≤ 16 * π ^ 2 * R ^ 2 * C * M * volume.real (Metric.closedBall (0 : E3) R) := by
  have hC0 : 0 ≤ ∫ x, ‖U (x, s)‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hM : 0 ≤ M := (norm_nonneg _).trans (hH.bound 0)
  calc ‖np U s H‖ ≤ ∫ ξ, 16 * π ^ 2 * R ^ 2 * C * M * chiB R ξ := by
        refine norm_integral_le_of_norm_le ((integrable_chiB R).const_mul _)
          (Eventually.of_forall fun ξ => ?_)
        have h1 := hH.norm_mt_le hR ξ
        have h2 := norm_inner_le_norm (𝕜 := ℂ) (NU U s ξ) (mtf H ξ)
        have h3 := (norm_NU_le h hs ξ).trans
          (mul_le_mul_of_nonneg_left hC (by positivity))
        have hc := chiB_nonneg R ξ
        have hC' : 0 ≤ C := hC0.trans hC
        have h4 : ‖ξ‖ * chiB R ξ ≤ R * chiB R ξ := by
          by_cases hξ : ‖ξ‖ ≤ R
          · exact mul_le_mul_of_nonneg_right hξ hc
          · have : chiB R ξ = 0 := by
              unfold chiB; rw [indicator_of_notMem (by simpa using hξ)]
            rw [this]; simp
        calc ‖⟪NU U s ξ, mtf H ξ⟫_ℂ‖ ≤ (2 * π * ‖ξ‖ * C) * (8 * π * R * M * chiB R ξ) :=
              h2.trans (mul_le_mul h3 h1 (norm_nonneg _) (by positivity))
          _ = 16 * π ^ 2 * R * C * M * (‖ξ‖ * chiB R ξ) := by ring
          _ ≤ 16 * π ^ 2 * R * C * M * (R * chiB R ξ) :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
          _ = 16 * π ^ 2 * R ^ 2 * C * M * chiB R ξ := by ring
    _ = 16 * π ^ 2 * R ^ 2 * C * M * volume.real (Metric.closedBall (0 : E3) R) := by
        rw [integral_const_mul, integral_chiB]

end Est

/-! ### Campos-teste `φ G` -/

/-- O núcleo do calor como função complexa. -/
noncomputable def hk (ν τ : ℝ) (ξ : E3) : ℂ := ((heat ν τ ξ : ℝ) : ℂ)

/-- O símbolo `q(ξ) = 4π²ν‖ξ‖²`. -/
noncomputable def qf (ν : ℝ) (ξ : E3) : ℂ := ((4 * π ^ 2 * ν * ‖ξ‖ ^ 2 : ℝ) : ℂ)

theorem contDiff_hk (ν τ : ℝ) : ContDiff ℝ ∞ (hk ν τ) := by
  unfold hk heat
  exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp
    ((contDiff_const.mul (contDiff_norm_sq ℝ)).mul contDiff_const).neg)

theorem contDiff_qf (ν : ℝ) : ContDiff ℝ ∞ (qf ν) := by
  unfold qf
  exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_norm_sq ℝ))

theorem norm_hk_le {ν τ : ℝ} (hν : 0 ≤ ν) (hτ : 0 ≤ τ) (ξ : E3) : ‖hk ν τ ξ‖ ≤ 1 := by
  rw [hk, Complex.norm_real, Real.norm_of_nonneg (heat_pos ν τ ξ).le]
  exact heat_le_one hν hτ ξ

theorem norm_qf_le {ν R : ℝ} (hν : 0 ≤ ν) {ξ : E3} (hξ : ‖ξ‖ ≤ R) :
    ‖qf ν ξ‖ ≤ 4 * π ^ 2 * ν * R ^ 2 := by
  rw [qf, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have : ‖ξ‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hξ 2
  have h4 : 0 ≤ 4 * π ^ 2 * ν := by positivity
  nlinarith

theorem heat_eq_exp (ν τ : ℝ) (ξ : E3) :
    heat ν τ ξ = Real.exp (-((4 * π ^ 2 * ν * ‖ξ‖ ^ 2) * τ)) := rfl

theorem tst_apply (G : E3 → C3) (φ : E3 → ℂ) (ξ : E3) : tst G φ ξ = φ ξ • G ξ := rfl

theorem tst_sub (G : E3 → C3) (φ ψ : E3 → ℂ) :
    tst G (fun ξ => φ ξ - ψ ξ) = fun ξ => tst G φ ξ - tst G ψ ξ := by
  funext ξ; simp [tst, sub_smul]

section G

variable {G : E3 → C3} (hG : ContDiff ℝ ∞ G) (hGs : HasCompactSupport G)
include hG hGs

theorem exists_R : ∃ R, 0 ≤ R ∧ ∀ ξ, R < ‖ξ‖ → G ξ = 0 := by
  obtain ⟨R, hR⟩ := hGs.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun ξ hξ => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hm => ?_
  have := hR hm
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left R 0]

theorem exists_MG : ∃ MG, 0 ≤ MG ∧ ∀ ξ, ‖G ξ‖ ≤ MG := by
  obtain ⟨C, hC⟩ := hG.continuous.bounded_above_of_compact_support hGs
  exact ⟨max C 0, le_max_right _ _, fun ξ => (hC ξ).trans (le_max_left _ _)⟩

theorem loc_tst {R : ℝ} (hR : ∀ ξ, R < ‖ξ‖ → G ξ = 0) {MG : ℝ} (hMG0 : 0 ≤ MG)
    (hMG : ∀ ξ, ‖G ξ‖ ≤ MG) {φ : E3 → ℂ} (hφ : Continuous φ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ ξ, ‖ξ‖ ≤ R → ‖φ ξ‖ ≤ M) : Loc R (MG * M) (tst G φ) where
  cont := hφ.smul hG.continuous
  bound ξ := by
    rw [tst_apply, norm_smul]
    by_cases hξ : ‖ξ‖ ≤ R
    · rw [mul_comm MG]; exact mul_le_mul (hM ξ hξ) (hMG ξ) (norm_nonneg _) hM0
    · rw [hR ξ (lt_of_not_ge hξ), norm_zero, mul_zero]; exact mul_nonneg hMG0 hM0
  supp ξ hξ := by rw [tst_apply, hR ξ hξ, smul_zero]

theorem contDiff_tst {φ : E3 → ℂ} (hφ : ContDiff ℝ ∞ φ) : ContDiff ℝ ∞ (tst G φ) :=
  hφ.smul hG

theorem hasCompactSupport_tst (φ : E3 → ℂ) : HasCompactSupport (tst G φ) :=
  hGs.smul_left (f := φ)

/-- `φ G` como campo de Schwartz. -/
noncomputable def tstS {φ : E3 → ℂ} (hφ : ContDiff ℝ ∞ φ) : 𝓢(E3, C3) :=
  (hasCompactSupport_tst hG hGs φ).toSchwartzMap (contDiff_tst hG hGs hφ)

theorem tstS_apply {φ : E3 → ℂ} (hφ : ContDiff ℝ ∞ φ) (ξ : E3) :
    tstS hG hGs hφ ξ = tst G φ ξ := rfl

end G

/-- `A₀(H) = ∫ ⟪â₀, m_H⟫`. -/
noncomputable def A0 (u₀S : SchwartzMap E3 E3) (H : E3 → C3) : ℂ :=
  ∫ ξ, ⟪ahat u₀S ξ, mtf H ξ⟫_ℂ

theorem mtf_tst_qf (G : E3 → C3) (ν : ℝ) (φ : E3 → ℂ) (ξ : E3) :
    mtf (tst G (fun η => qf ν η * φ η)) ξ = qf ν ξ • mtf (tst G φ) ξ := by
  have e : tst G (fun η => qf ν η * φ η) = fun η => qf ν η • tst G φ η := by
    funext η; simp only [tst, mul_smul]
  rw [e, mt_smul]

section FW

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}
variable {G : E3 → C3} (hG : ContDiff ℝ ∞ G) (hGs : HasCompactSupport G)
include hG hGs

/-- **A formulação fraca em termos de `A` e `n`**:
`A(t', φG) − A₀(φG) = ∫₀^{t'} (−A(s, qφG) − n(s, φG)) ds`. -/
theorem fw (h : SolucaoLocal ν u₀ T U P) (u₀S : SchwartzMap E3 E3) (hu₀ : ∀ x, u₀S x = u₀ x)
    {φ : E3 → ℂ} (hφ : ContDiff ℝ ∞ φ) {t' : ℝ} (ht' : t' ∈ Ico 0 T) :
    Ap U t' (tst G φ) - A0 u₀S (tst G φ) =
      ∫ s in (0 : ℝ)..t', (-Ap U s (tst G (fun η => qf ν η * φ η)) - np U s (tst G φ)) := by
  have hf := fraca_fourier h u₀S hu₀ (tstS hG hGs hφ) ht'
  have e : (⇑(tstS hG hGs hφ) : E3 → C3) = tst G φ := rfl
  rw [e] at hf
  unfold Ap A0 np
  rw [hf]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  congr 1
  rw [← integral_const_mul, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [mtf_tst_qf, inner_smul_right, inner_smul_right, qf]
  push_cast
  ring

/-- `s ↦ A(s, φG)` é integrável em `[0, t]`. -/
theorem intervalIntegrable_Ap (h : SolucaoLocal ν u₀ T U P) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < T) {φ : E3 → ℂ} (hφ : ContDiff ℝ ∞ φ) :
    IntervalIntegrable (fun s => Ap U s (tst G φ)) volume 0 t := by
  set S : 𝓢(E3, C3) := tstS hG hGs hφ
  set Φ : 𝓢(E3, C3) := 𝓕⁻ (Ms S)
  obtain ⟨C, hC0, hC⟩ := exists_energy h ht
  have hUc : ContinuousOn U (univ ×ˢ Icc 0 t) :=
    h.1.continuousOn.mono (fun p hp => ⟨mem_univ _, hp.2.1, hp.2.2.trans_lt ht⟩)
  have hΦ2 : Integrable fun x => ‖Φ x‖ ^ 2 := integrable_sq_norm_of_memLp (Φ.memLp 2)
  have hint := intervalIntegrable_param (F := fun p : E3 × ℝ => ⟪cpx (U p), Φ p.1⟫_ℂ) ht0
    ((continuous_cpx.comp_continuousOn hUc).inner (Φ.continuous.comp continuous_fst).continuousOn)
    (M := (C + ∫ x, ‖Φ x‖ ^ 2) / 2) (fun s hs => by
      have hs' : s ∈ Ico 0 T := ⟨hs.1, hs.2.trans_lt ht⟩
      have hi := integrable_sq_U h hs'
      calc ‖∫ x, ⟪cpx (U (x, s)), Φ x⟫_ℂ‖ ≤ ∫ x, (‖U (x, s)‖ ^ 2 + ‖Φ x‖ ^ 2) / 2 := by
            refine norm_integral_le_of_norm_le ((hi.add hΦ2).div_const 2)
              (Eventually.of_forall fun x => ?_)
            have := norm_inner_le_norm (𝕜 := ℂ) (cpx (U (x, s))) (Φ x)
            rw [norm_cpx] at this
            nlinarith [sq_nonneg (‖U (x, s)‖ - ‖Φ x‖)]
        _ = ((∫ x, ‖U (x, s)‖ ^ 2) + ∫ x, ‖Φ x‖ ^ 2) / 2 := by
            rw [integral_div, integral_add hi hΦ2]
        _ ≤ (C + ∫ x, ‖Φ x‖ ^ 2) / 2 := by linarith [hC s hs])
  refine (intervalIntegrable_congr (fun s hs => ?_)).mp hint
  rw [uIoc_of_le ht0] at hs
  have hs' : s ∈ Ico 0 T := ⟨hs.1.le, hs.2.trans_lt ht⟩
  simp only
  rw [term_A h hs' (Ms S), Ap]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only [Ms_apply]
  rfl

end FW

section Med

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}

/-- Medibilidade conjunta de `N` (com o tempo truncado em `[0, t]`). -/
theorem stronglyMeasurable_NUc (h : SolucaoLocal ν u₀ T U P) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < T) : StronglyMeasurable fun p : ℝ × E3 => NU U (max 0 (min p.1 t)) p.2 := by
  set c : ℝ → ℝ := fun s => max 0 (min s t) with hc_def
  have hc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hcm : ∀ s, c s ∈ Icc 0 t := fun s => ⟨le_max_left _ _, max_le ht0 (min_le_right _ _)⟩
  have hUc : ContinuousOn U (univ ×ˢ Icc 0 t) :=
    h.1.continuousOn.mono (fun p hp => ⟨mem_univ _, hp.2.1, hp.2.2.trans_lt ht⟩)
  set W : E3 × (ℝ × E3) → C3 := fun q => cpx (U (q.1, c q.2.1)) with hW
  have hWc : Continuous W :=
    continuous_cpx.comp (hUc.comp_continuous (continuous_fst.prodMk
      (hc.comp (continuous_fst.comp continuous_snd))) (fun q => ⟨mem_univ _, hcm _⟩))
  set F : E3 × (ℝ × E3) → C3 := fun q =>
    ((𝐞 (-⟪q.1, q.2.2⟫_ℝ) : ℂ)) • (⟪cpx q.2.2, W q⟫_ℂ • W q) with hF
  have hFc : Continuous F := by
    have he : Continuous fun q : E3 × (ℝ × E3) => ((𝐞 (-⟪q.1, q.2.2⟫_ℝ) : ℂ)) :=
      (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        ((continuous_fst.inner (continuous_snd.comp continuous_snd)).neg)
    have hi : Continuous fun q : E3 × (ℝ × E3) => ⟪cpx q.2.2, W q⟫_ℂ :=
      Continuous.inner (𝕜 := ℂ) (continuous_cpx.comp (continuous_snd.comp continuous_snd)) hWc
    exact he.smul (hi.smul hWc)
  have e : (fun p : ℝ × E3 => NU U (c p.1) p.2) =
      fun p => ((2 * π : ℝ) * Complex.I : ℂ) • ∫ x, F (x, p) := by
    funext p
    simp only [NU, Real.fourier_eq, hF, hW, Circle.smul_def]
  rw [e]
  exact (stronglyMeasurable_const (b := ((2 * π : ℝ) * Complex.I : ℂ))).smul
    (MeasureTheory.StronglyMeasurable.integral_prod_left' (μ := (volume : Measure E3))
      hFc.stronglyMeasurable)

/-- `s ↦ n(s, H_s)` é integrável em `[0, t]` para uma família contínua de campos localizados. -/
theorem intervalIntegrable_np_fam (h : SolucaoLocal ν u₀ T U P) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < T) {Ht : ℝ → E3 → C3} (hcont : Continuous fun p : ℝ × E3 => Ht p.1 p.2)
    {R M : ℝ} (hR : 0 ≤ R) (hloc : ∀ s ∈ Icc 0 t, Loc R M (Ht s)) :
    IntervalIntegrable (fun s => np U s (Ht s)) volume 0 t := by
  obtain ⟨C, hC0, hC⟩ := exists_energy h ht
  set c : ℝ → ℝ := fun s => max 0 (min s t) with hc_def
  have hcs : ∀ s ∈ Icc 0 t, c s = s := fun s hs => by
    simp only [hc_def, min_eq_left hs.2, max_eq_right hs.1]
  have hmt : Continuous fun p : ℝ × E3 => mtf (Ht p.1) p.2 := by
    have e : (fun p : ℝ × E3 => mtf (Ht p.1) p.2) =
        fun p => ((2 * π : ℝ) * Complex.I : ℂ) • cr (cpx p.2) (Ht p.1 p.2) := rfl
    rw [e]
    exact (continuous_const (y := ((2 * π : ℝ) * Complex.I : ℂ))).smul
      (continuous_cr.comp ((continuous_cpx.comp continuous_snd).prodMk hcont))
  have hf2 : StronglyMeasurable fun p : ℝ × E3 => ⟪NU U (c p.1) p.2, mtf (Ht p.1) p.2⟫_ℂ :=
    StronglyMeasurable.inner (𝕜 := ℂ) (stronglyMeasurable_NUc h ht0 ht) hmt.stronglyMeasurable
  have hg : StronglyMeasurable fun s => ∫ ξ, ⟪NU U (c s) ξ, mtf (Ht s) ξ⟫_ℂ :=
    MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := (volume : Measure E3)) hf2
  have hI : IntegrableOn (fun s => ∫ ξ, ⟪NU U (c s) ξ, mtf (Ht s) ξ⟫_ℂ) (Ioc 0 t) volume := by
    refine Measure.integrableOn_of_bounded
      (M := 16 * π ^ 2 * R ^ 2 * C * M * volume.real (Metric.closedBall (0 : E3) R))
      (by simp) hg.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => ?_)
    have hs2 : s ∈ Icc 0 t := Ioc_subset_Icc_self hs
    rw [hcs s hs2]
    exact norm_np_le h ⟨hs2.1, hs2.2.trans_lt ht⟩ (hC s hs2) hR (hloc s hs2)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht0]
  refine hI.congr_fun (fun s hs => ?_) measurableSet_Ioc
  simp only [np, hcs s (Ioc_subset_Icc_self hs)]

end Med

/-! ### Linearidade dos pareamentos -/

theorem mtf_tst_lin (G : E3 → C3) (c₁ c₂ : ℂ) (ψ₁ ψ₂ : E3 → ℂ) (ξ : E3) :
    mtf (tst G (fun η => c₁ * ψ₁ η + c₂ * ψ₂ η)) ξ =
      c₁ • mtf (tst G ψ₁) ξ + c₂ • mtf (tst G ψ₂) ξ := by
  simp only [mtf, tst, add_smul, mul_smul, cr_add_right, cr_smul_right, smul_add]
  module

section Lin

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}

theorem Ap_lin (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) {G : E3 → C3}
    {R M₁ M₂ : ℝ} (hR : 0 ≤ R) {ψ₁ ψ₂ : E3 → ℂ} (h₁ : Loc R M₁ (tst G ψ₁))
    (h₂ : Loc R M₂ (tst G ψ₂)) (c₁ c₂ : ℂ) :
    Ap U s (tst G (fun η => c₁ * ψ₁ η + c₂ * ψ₂ η)) =
      c₁ * Ap U s (tst G ψ₁) + c₂ * Ap U s (tst G ψ₂) := by
  unfold Ap
  simp_rw [mtf_tst_lin, inner_add_right, inner_smul_right]
  rw [integral_add ((integrable_Ap h hs hR h₁).const_mul _) ((integrable_Ap h hs hR h₂).const_mul _),
    integral_const_mul, integral_const_mul]

theorem np_lin (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) {G : E3 → C3}
    {R M₁ M₂ : ℝ} (hR : 0 ≤ R) {ψ₁ ψ₂ : E3 → ℂ} (h₁ : Loc R M₁ (tst G ψ₁))
    (h₂ : Loc R M₂ (tst G ψ₂)) (c₁ c₂ : ℂ) :
    np U s (tst G (fun η => c₁ * ψ₁ η + c₂ * ψ₂ η)) =
      c₁ * np U s (tst G ψ₁) + c₂ * np U s (tst G ψ₂) := by
  unfold np
  simp_rw [mtf_tst_lin, inner_add_right, inner_smul_right]
  rw [integral_add ((integrable_np h hs hR h₁).const_mul _) ((integrable_np h hs hR h₂).const_mul _),
    integral_const_mul, integral_const_mul]

theorem Ap_sub (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) {G : E3 → C3}
    {R M₁ M₂ : ℝ} (hR : 0 ≤ R) {ψ₁ ψ₂ : E3 → ℂ} (h₁ : Loc R M₁ (tst G ψ₁))
    (h₂ : Loc R M₂ (tst G ψ₂)) :
    Ap U s (tst G ψ₁) - Ap U s (tst G ψ₂) = Ap U s (tst G (fun η => ψ₁ η - ψ₂ η)) := by
  have e : (fun η => ψ₁ η - ψ₂ η) = fun η => (1 : ℂ) * ψ₁ η + (-1 : ℂ) * ψ₂ η := by
    funext η; ring
  rw [e, Ap_lin h hs hR h₁ h₂]; ring

theorem np_sub (h : SolucaoLocal ν u₀ T U P) {s : ℝ} (hs : s ∈ Ico 0 T) {G : E3 → C3}
    {R M₁ M₂ : ℝ} (hR : 0 ≤ R) {ψ₁ ψ₂ : E3 → ℂ} (h₁ : Loc R M₁ (tst G ψ₁))
    (h₂ : Loc R M₂ (tst G ψ₂)) :
    np U s (tst G ψ₁) - np U s (tst G ψ₂) = np U s (tst G (fun η => ψ₁ η - ψ₂ η)) := by
  have e : (fun η => ψ₁ η - ψ₂ η) = fun η => (1 : ℂ) * ψ₁ η + (-1 : ℂ) * ψ₂ η := by
    funext η; ring
  rw [e, np_lin h hs hR h₁ h₂]; ring

end Lin

/-! ### A fórmula de Duhamel -/

section Main

variable {ν T : ℝ} {u₀ : E3 → E3} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ}

theorem uIcc_sub {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ t) : uIcc a b ⊆ uIcc 0 t := by
  rw [uIcc_of_le hab, uIcc_of_le (ha.trans (hab.trans hb))]
  exact Icc_subset_Icc ha hb

/-- `A(·, ψG)` é lipschitziana no tempo. -/
theorem lip_Ap (h : SolucaoLocal ν u₀ T U P) (u₀S : SchwartzMap E3 E3)
    (hu₀ : ∀ x, u₀S x = u₀ x) {G : E3 → C3} (hG : ContDiff ℝ ∞ G) (hGs : HasCompactSupport G)
    {R MG : ℝ} (hR0 : 0 ≤ R) (hR : ∀ ξ, R < ‖ξ‖ → G ξ = 0) (hMG0 : 0 ≤ MG)
    (hMG : ∀ ξ, ‖G ξ‖ ≤ MG) {t : ℝ} (ht : t ∈ Ico 0 T) {C : ℝ}
    (hC : ∀ s ∈ Icc 0 t, ∫ x, ‖U (x, s)‖ ^ 2 ≤ C) {ψ : E3 → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    {M M' : ℝ} (hM0 : 0 ≤ M) (hM'0 : 0 ≤ M') (hM : ∀ ξ, ‖ξ‖ ≤ R → ‖ψ ξ‖ ≤ M)
    (hM' : ∀ ξ, ‖ξ‖ ≤ R → ‖qf ν ξ * ψ ξ‖ ≤ M') {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ t) :
    ‖Ap U b (tst G ψ) - Ap U a (tst G ψ)‖ ≤
      (4 * π * R * MG * (C + volume.real (Metric.closedBall (0 : E3) R)) * M' +
        16 * π ^ 2 * R ^ 2 * C * MG * volume.real (Metric.closedBall (0 : E3) R) * M) *
        (b - a) := by
  have hqψ : ContDiff ℝ ∞ fun η => qf ν η * ψ η := (contDiff_qf ν).mul hψ
  have hL1 : Loc R (MG * M') (tst G fun η => qf ν η * ψ η) :=
    loc_tst hG hGs hR hMG0 hMG hqψ.continuous hM'0 hM'
  have hL2 : Loc R (MG * M) (tst G ψ) := loc_tst hG hGs hR hMG0 hMG hψ.continuous hM0 hM
  have fb := fw hG hGs h u₀S hu₀ hψ ⟨ha.trans hab, hb.trans_lt ht.2⟩
  have fa := fw hG hGs h u₀S hu₀ hψ ⟨ha, (hab.trans hb).trans_lt ht.2⟩
  have hint : IntervalIntegrable (fun s => -Ap U s (tst G fun η => qf ν η * ψ η) -
      np U s (tst G ψ)) volume 0 t :=
    (intervalIntegrable_Ap hG hGs h ht.1 ht.2 hqψ).neg.sub
      (intervalIntegrable_np_fam h ht.1 ht.2 (Ht := fun _ => tst G ψ)
        (hL2.cont.comp continuous_snd) hR0 (fun _ _ => hL2))
  have hib := hint.mono_set (uIcc_sub le_rfl (ha.trans hab) hb)
  have hia := hint.mono_set (uIcc_sub le_rfl ha (hab.trans hb))
  have e : Ap U b (tst G ψ) - Ap U a (tst G ψ) = ∫ s in a..b,
      (-Ap U s (tst G fun η => qf ν η * ψ η) - np U s (tst G ψ)) := by
    rw [← intervalIntegral.integral_interval_sub_left hib hia, ← fb, ← fa]; ring
  rw [e]
  set Kc := 4 * π * R * MG * (C + volume.real (Metric.closedBall (0 : E3) R)) * M' +
    16 * π ^ 2 * R ^ 2 * C * MG * volume.real (Metric.closedBall (0 : E3) R) * M
  have hbound : ∀ s ∈ uIoc a b, ‖-Ap U s (tst G fun η => qf ν η * ψ η) - np U s (tst G ψ)‖ ≤ Kc := by
    intro s hs
    rw [uIoc_of_le hab] at hs
    have hs2 : s ∈ Icc 0 t := ⟨ha.trans hs.1.le, hs.2.trans hb⟩
    have hs3 : s ∈ Ico 0 T := ⟨hs2.1, hs2.2.trans_lt ht.2⟩
    have h1 := norm_Ap_le h hs3 (hC s hs2) hR0 hL1
    have h2 := norm_np_le h hs3 (hC s hs2) hR0 hL2
    calc ‖-Ap U s (tst G fun η => qf ν η * ψ η) - np U s (tst G ψ)‖
        ≤ ‖Ap U s (tst G fun η => qf ν η * ψ η)‖ + ‖np U s (tst G ψ)‖ := by
          rw [sub_eq_add_neg, ← neg_add, norm_neg]; exact norm_add_le _ _
      _ ≤ Kc := add_le_add (h1.trans (le_of_eq (by ring))) (h2.trans (le_of_eq (by ring)))
  calc ‖∫ s in a..b, (-Ap U s (tst G fun η => qf ν η * ψ η) - np U s (tst G ψ))‖
      ≤ Kc * |b - a| := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = Kc * (b - a) := by rw [abs_of_nonneg (sub_nonneg.mpr hab)]

/-- **Fórmula de Duhamel (forma integrada)** para uma solução suave qualquer:
`A(t, G) = A₀(e^{−q t} G) − ∫₀ᵗ n(s, e^{−q(t−s)} G) ds`, `q = 4π²ν‖ξ‖²`. -/
theorem duhamel (h : SolucaoLocal ν u₀ T U P) (hν : 0 ≤ ν) (u₀S : SchwartzMap E3 E3)
    (hu₀ : ∀ x, u₀S x = u₀ x) {G : E3 → C3} (hG : ContDiff ℝ ∞ G) (hGs : HasCompactSupport G)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    Ap U t G = A0 u₀S (tst G (hk ν t)) - ∫ s in (0 : ℝ)..t, np U s (tst G (hk ν (t - s))) := by
  obtain ⟨R, hR0, hR⟩ := exists_R hG hGs
  obtain ⟨MG, hMG0, hMG⟩ := exists_MG hG hGs
  obtain ⟨C, hC0, hC⟩ := exists_energy h ht.2
  set V := volume.real (Metric.closedBall (0 : E3) R) with hV
  have hV0 : 0 ≤ V := measureReal_nonneg
  set qR := 4 * π ^ 2 * ν * R ^ 2 with hqR_def
  have hqR : 0 ≤ qR := by positivity
  set KA := 4 * π * R * MG * (C + V) with hKA
  set Kn := 16 * π ^ 2 * R ^ 2 * C * MG * V with hKn
  have hKA0 : 0 ≤ KA := by positivity
  have hKn0 : 0 ≤ Kn := by positivity
  set φ : ℝ → E3 → ℂ := fun r => hk ν (t - r) with hφ_def
  have hφs : ∀ r, ContDiff ℝ ∞ (φ r) := fun r => contDiff_hk _ _
  have hφb : ∀ r ≤ t, ∀ ξ, ‖φ r ξ‖ ≤ 1 := fun r hr ξ => norm_hk_le hν (by linarith) ξ
  have hqφb : ∀ r ≤ t, ∀ ξ, ‖ξ‖ ≤ R → ‖qf ν ξ * φ r ξ‖ ≤ qR := by
    intro r hr ξ hξ
    rw [norm_mul]
    calc ‖qf ν ξ‖ * ‖φ r ξ‖ ≤ qR * 1 :=
          mul_le_mul (norm_qf_le hν hξ) (hφb r hr ξ) (norm_nonneg _) hqR
      _ = qR := mul_one _
  have hqqφb : ∀ r ≤ t, ∀ ξ, ‖ξ‖ ≤ R → ‖qf ν ξ * (qf ν ξ * φ r ξ)‖ ≤ qR ^ 2 := by
    intro r hr ξ hξ
    rw [norm_mul, sq]
    exact mul_le_mul (norm_qf_le hν hξ) (hqφb r hr ξ hξ) (norm_nonneg _) hqR
  have hloc : ∀ r ≤ t, Loc R (MG * 1) (tst G (φ r)) := fun r hr =>
    loc_tst hG hGs hR hMG0 hMG (hφs r).continuous zero_le_one (fun ξ _ => hφb r hr ξ)
  have hfam : Continuous fun p : ℝ × E3 => tst G (φ p.1) p.2 := by
    have e : (fun p : ℝ × E3 => tst G (φ p.1) p.2) =
        fun p => ((heat ν (t - p.1) p.2 : ℝ) : ℂ) • G p.2 := rfl
    rw [e]
    exact (Complex.continuous_ofReal.comp ((continuous_heat ν).comp
      ((continuous_const.sub continuous_fst).prodMk continuous_snd))).smul
      (hG.continuous.comp continuous_snd)
  have hnI : IntervalIntegrable (fun s => np U s (tst G (φ s))) volume 0 t :=
    intervalIntegrable_np_fam h ht.1 ht.2 hfam hR0 (fun s hs => hloc s hs.2)
  set Hf : ℝ → ℂ := fun r => Ap U r (tst G (φ r)) + ∫ s in (0 : ℝ)..r, np U s (tst G (φ s))
    with hHf
  set δ := 1 / (qR + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  set Kf := KA * qR ^ 2 + (KA * qR ^ 2 + Kn * qR) + Kn * qR with hKf
  have key : ∀ a b, 0 ≤ a → a ≤ b → b ≤ t → b - a ≤ δ → ‖Hf b - Hf a‖ ≤ Kf * (b - a) ^ 2 := by
    intro a b ha hab hb hbδ
    set d := b - a with hd
    have hd0 : 0 ≤ d := sub_nonneg.mpr hab
    have hqd : qR * d ≤ 1 := by
      have h1 : qR * d ≤ qR * δ := mul_le_mul_of_nonneg_left hbδ hqR
      have h2 : qR * δ ≤ 1 := by
        rw [hδ, mul_one_div, div_le_one (by positivity)]; linarith
      linarith
    have hat : a ≤ t := hab.trans hb
    have hb' : b ∈ Ico 0 T := ⟨ha.trans hab, hb.trans_lt ht.2⟩
    have ha' : a ∈ Ico 0 T := ⟨ha, hat.trans_lt ht.2⟩
    -- o resto de Taylor
    set ρ : E3 → ℂ := fun ξ => φ b ξ - φ a ξ - (d : ℂ) * (qf ν ξ * φ a ξ) with hρ
    have hρc : ContDiff ℝ ∞ ρ :=
      ((hφs b).sub (hφs a)).sub (contDiff_const.mul ((contDiff_qf ν).mul (hφs a)))
    have hρb : ∀ ξ, ‖ξ‖ ≤ R → ‖ρ ξ‖ ≤ (qR * d) ^ 2 := by
      intro ξ hξ
      set q := 4 * π ^ 2 * ν * ‖ξ‖ ^ 2 with hq
      have hq0 : 0 ≤ q := by positivity
      have hqq : q ≤ qR := by
        have : ‖ξ‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hξ 2
        have h4 : 0 ≤ 4 * π ^ 2 * ν := by positivity
        rw [hq, hqR_def]; nlinarith
      have hφq : ∀ r, φ r ξ = ((Real.exp (-(q * (t - r))) : ℝ) : ℂ) := fun r => rfl
      have hqf : qf ν ξ = ((q : ℝ) : ℂ) := rfl
      have e : ρ ξ = ((Real.exp (-(q * (t - b))) - Real.exp (-(q * (t - a))) -
          (b - a) * q * Real.exp (-(q * (t - a))) : ℝ) : ℂ) := by
        simp only [hρ, hφq, hqf, hd, Complex.ofReal_sub, Complex.ofReal_mul]
        ring
      rw [e, Complex.norm_real, Real.norm_eq_abs]
      refine (abs_exp_taylor_le hq0 hab hb ((mul_le_mul_of_nonneg_right hqq hd0).trans hqd)).trans ?_
      exact pow_le_pow_left₀ (mul_nonneg hq0 hd0) (mul_le_mul_of_nonneg_right hqq hd0) 2
    have hlocρ : Loc R (MG * (qR * d) ^ 2) (tst G ρ) :=
      loc_tst hG hGs hR hMG0 hMG hρc.continuous (sq_nonneg _) hρb
    have hXs : ContDiff ℝ ∞ fun η => qf ν η * φ a η := (contDiff_qf ν).mul (hφs a)
    have hlocX : Loc R (MG * qR) (tst G fun η => qf ν η * φ a η) :=
      loc_tst hG hGs hR hMG0 hMG hXs.continuous hqR (hqφb a hat)
    -- decomposição de `A(b, φ_b) − A(b, φ_a)`
    have hdec : Ap U b (tst G (φ b)) - Ap U b (tst G (φ a)) =
        Ap U b (tst G ρ) + (d : ℂ) * Ap U b (tst G fun η => qf ν η * φ a η) := by
      rw [Ap_sub h hb' hR0 (hloc b hb) (hloc a hat)]
      have e : (fun η => φ b η - φ a η) =
          fun η => (1 : ℂ) * ρ η + (d : ℂ) * (qf ν η * φ a η) := by
        funext η; simp only [hρ]; ring
      rw [e, Ap_lin h hb' hR0 hlocρ hlocX, one_mul]
    -- a formulação fraca entre `a` e `b`
    have hiA : IntervalIntegrable (fun s => Ap U s (tst G fun η => qf ν η * φ a η)) volume 0 t :=
      intervalIntegrable_Ap hG hGs h ht.1 ht.2 hXs
    have hiY : IntervalIntegrable (fun s => np U s (tst G (φ a))) volume 0 t :=
      intervalIntegrable_np_fam h ht.1 ht.2 (Ht := fun _ => tst G (φ a))
        ((hloc a hat).cont.comp continuous_snd) hR0 (fun _ _ => hloc a hat)
    have hsub : uIcc a b ⊆ uIcc 0 t := uIcc_sub ha hab hb
    have fb := fw hG hGs h u₀S hu₀ (hφs a) hb'
    have fa := fw hG hGs h u₀S hu₀ (hφs a) ha'
    have hint : IntervalIntegrable (fun s => -Ap U s (tst G fun η => qf ν η * φ a η) -
        np U s (tst G (φ a))) volume 0 t := hiA.neg.sub hiY
    have hfw : Ap U b (tst G (φ a)) - Ap U a (tst G (φ a)) =
        -(∫ s in a..b, Ap U s (tst G fun η => qf ν η * φ a η)) -
          ∫ s in a..b, np U s (tst G (φ a)) := by
      have e1 := intervalIntegral.integral_interval_sub_left
        (hint.mono_set (uIcc_sub le_rfl (ha.trans hab) hb)) (hint.mono_set (uIcc_sub le_rfl ha hat))
      rw [← fb, ← fa] at e1
      have hneg : IntervalIntegrable (fun s => -Ap U s (tst G fun η => qf ν η * φ a η))
          volume a b := (hiA.mono_set hsub).neg
      rw [intervalIntegral.integral_sub hneg (hiY.mono_set hsub),
        intervalIntegral.integral_neg] at e1
      rw [← e1]; ring
    have hI1 : (∫ s in (0 : ℝ)..b, np U s (tst G (φ s))) - ∫ s in (0 : ℝ)..a, np U s (tst G (φ s)) =
        ∫ s in a..b, np U s (tst G (φ s)) :=
      intervalIntegral.integral_interval_sub_left (hnI.mono_set (uIcc_sub le_rfl (ha.trans hab) hb))
        (hnI.mono_set (uIcc_sub le_rfl ha hat))
    have E : Hf b - Hf a = Ap U b (tst G ρ) +
        (∫ s in a..b, (Ap U b (tst G fun η => qf ν η * φ a η) -
          Ap U s (tst G fun η => qf ν η * φ a η))) +
        ∫ s in a..b, (np U s (tst G (φ s)) - np U s (tst G (φ a))) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hiA.mono_set hsub),
        intervalIntegral.integral_sub (hnI.mono_set hsub) (hiY.mono_set hsub),
        intervalIntegral.integral_const, ← hI1]
      simp only [hHf]
      rw [← hd, Complex.real_smul]
      linear_combination hdec + hfw
    -- as três cotas
    have b1 : ‖Ap U b (tst G ρ)‖ ≤ KA * qR ^ 2 * d ^ 2 := by
      refine (norm_Ap_le h hb' (hC b ⟨hb'.1, hb⟩) hR0 hlocρ).trans (le_of_eq ?_)
      rw [hKA]; ring
    have b2 : ‖∫ s in a..b, (Ap U b (tst G fun η => qf ν η * φ a η) -
        Ap U s (tst G fun η => qf ν η * φ a η))‖ ≤ (KA * qR ^ 2 + Kn * qR) * d * d := by
      have hb2 : ∀ s ∈ uIoc a b, ‖Ap U b (tst G fun η => qf ν η * φ a η) -
          Ap U s (tst G fun η => qf ν η * φ a η)‖ ≤ (KA * qR ^ 2 + Kn * qR) * d := by
        intro s hs
        rw [uIoc_of_le hab] at hs
        have hl := lip_Ap h u₀S hu₀ hG hGs hR0 hR hMG0 hMG ht hC hXs hqR (sq_nonneg qR)
          (hqφb a hat) (hqqφb a hat) (ha.trans hs.1.le) hs.2 hb
        refine hl.trans ?_
        have hc : 0 ≤ 4 * π * R * MG * (C + V) * qR ^ 2 + 16 * π ^ 2 * R ^ 2 * C * MG * V * qR := by
          positivity
        calc (4 * π * R * MG * (C + V) * qR ^ 2 + 16 * π ^ 2 * R ^ 2 * C * MG * V * qR) * (b - s)
            ≤ (4 * π * R * MG * (C + V) * qR ^ 2 + 16 * π ^ 2 * R ^ 2 * C * MG * V * qR) * d :=
              mul_le_mul_of_nonneg_left (by rw [hd]; linarith [hs.1]) hc
          _ = (KA * qR ^ 2 + Kn * qR) * d := by rw [hKA, hKn]
      calc _ ≤ (KA * qR ^ 2 + Kn * qR) * d * |b - a| :=
            intervalIntegral.norm_integral_le_of_norm_le_const hb2
        _ = (KA * qR ^ 2 + Kn * qR) * d * d := by rw [abs_of_nonneg hd0]
    have b3 : ‖∫ s in a..b, (np U s (tst G (φ s)) - np U s (tst G (φ a)))‖ ≤ Kn * qR * d * d := by
      have hb3 : ∀ s ∈ uIoc a b, ‖np U s (tst G (φ s)) - np U s (tst G (φ a))‖ ≤ Kn * qR * d := by
        intro s hs
        rw [uIoc_of_le hab] at hs
        have hst : s ≤ t := hs.2.trans hb
        have hs' : s ∈ Ico 0 T := ⟨ha.trans hs.1.le, hst.trans_lt ht.2⟩
        rw [np_sub h hs' hR0 (hloc s hst) (hloc a hat)]
        have hdb : ∀ ξ, ‖ξ‖ ≤ R → ‖φ s ξ - φ a ξ‖ ≤ qR * d := by
          intro ξ hξ
          set q := 4 * π ^ 2 * ν * ‖ξ‖ ^ 2 with hq
          have hq0 : 0 ≤ q := by positivity
          have hqq : q ≤ qR := by
            have : ‖ξ‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hξ 2
            have h4 : 0 ≤ 4 * π ^ 2 * ν := by positivity
            rw [hq, hqR_def]; nlinarith
          have hφq : ∀ r, φ r ξ = ((Real.exp (-(q * (t - r))) : ℝ) : ℂ) := fun r => rfl
          have e : φ s ξ - φ a ξ =
              ((Real.exp (-(q * (t - s))) - Real.exp (-(q * (t - a))) : ℝ) : ℂ) := by
            rw [hφq s, hφq a, Complex.ofReal_sub]
          rw [e, Complex.norm_real, Real.norm_eq_abs]
          refine (abs_exp_sub_exp_le hq0 (by linarith) (by linarith)).trans ?_
          have h1 : |t - s - (t - a)| ≤ d := by
            rw [show t - s - (t - a) = a - s by ring, abs_of_nonpos (by linarith [hs.1])]
            rw [hd]; linarith [hs.2]
          exact mul_le_mul hqq h1 (abs_nonneg _) hqR
        have hl : Loc R (MG * (qR * d)) (tst G fun η => φ s η - φ a η) :=
          loc_tst hG hGs hR hMG0 hMG ((hφs s).continuous.sub (hφs a).continuous)
            (mul_nonneg hqR hd0) hdb
        refine (norm_np_le h hs' (hC s ⟨hs'.1, hst⟩) hR0 hl).trans (le_of_eq ?_)
        rw [hKn]; ring
      calc _ ≤ Kn * qR * d * |b - a| := intervalIntegral.norm_integral_le_of_norm_le_const hb3
        _ = Kn * qR * d * d := by rw [abs_of_nonneg hd0]
    rw [E]
    calc ‖Ap U b (tst G ρ) + (∫ s in a..b, (Ap U b (tst G fun η => qf ν η * φ a η) -
          Ap U s (tst G fun η => qf ν η * φ a η))) +
          ∫ s in a..b, (np U s (tst G (φ s)) - np U s (tst G (φ a)))‖
        ≤ KA * qR ^ 2 * d ^ 2 + (KA * qR ^ 2 + Kn * qR) * d * d + Kn * qR * d * d :=
          (norm_add₃_le).trans (add_le_add (add_le_add b1 b2) b3)
      _ = Kf * d ^ 2 := by rw [hKf]; ring
  have hconst := const_of_sq ht.1 hδ0 key
  -- extremos
  have h0 : Hf 0 = A0 u₀S (tst G (hk ν t)) := by
    have f0 := fw hG hGs h u₀S hu₀ (hφs 0) ⟨le_rfl, ht.1.trans_lt ht.2⟩
    rw [intervalIntegral.integral_same, sub_eq_zero] at f0
    simp only [hHf, intervalIntegral.integral_same, add_zero]
    rw [f0]
    simp only [hφ_def, sub_zero]
  have hφt : tst G (φ t) = G := by
    funext ξ
    simp only [tst, hφ_def, sub_self, hk, heat_zero, Complex.ofReal_one, one_smul]
  have ht' : Hf t = Ap U t G + ∫ s in (0 : ℝ)..t, np U s (tst G (hk ν (t - s))) := by
    simp only [hHf, hφt]
    rfl
  rw [ht', h0] at hconst
  rw [← hconst]; ring

end Main

end ATK.NSDuhamel

#print axioms ATK.NSDuhamel.const_of_sq
#print axioms ATK.NSDuhamel.abs_exp_sub_exp_le
#print axioms ATK.NSDuhamel.abs_exp_taylor_le
#print axioms ATK.NSDuhamel.abs_coord_le
#print axioms ATK.NSDuhamel.norm_cr_le
#print axioms ATK.NSDuhamel.norm_mt_le
#print axioms ATK.NSDuhamel.mt_smul
#print axioms ATK.NSDuhamel.continuous_cr
#print axioms ATK.NSDuhamel.continuous_mt
#print axioms ATK.NSDuhamel.integrable_chiB
#print axioms ATK.NSDuhamel.chiB_nonneg
#print axioms ATK.NSDuhamel.chiB_sq
#print axioms ATK.NSDuhamel.Loc.norm_mt_le
#print axioms ATK.NSDuhamel.integral_chiB
#print axioms ATK.NSDuhamel.integral_norm_sq_bF
#print axioms ATK.NSDuhamel.memLp_bF
#print axioms ATK.NSDuhamel.norm_NU_le
#print axioms ATK.NSDuhamel.continuous_NU
#print axioms ATK.NSDuhamel.integrable_Ap
#print axioms ATK.NSDuhamel.norm_Ap_le
#print axioms ATK.NSDuhamel.integrable_np
#print axioms ATK.NSDuhamel.norm_np_le
#print axioms ATK.NSDuhamel.contDiff_hk
#print axioms ATK.NSDuhamel.contDiff_qf
#print axioms ATK.NSDuhamel.norm_hk_le
#print axioms ATK.NSDuhamel.norm_qf_le
#print axioms ATK.NSDuhamel.heat_eq_exp
#print axioms ATK.NSDuhamel.tst_apply
#print axioms ATK.NSDuhamel.tst_sub
#print axioms ATK.NSDuhamel.exists_R
#print axioms ATK.NSDuhamel.exists_MG
#print axioms ATK.NSDuhamel.loc_tst
#print axioms ATK.NSDuhamel.contDiff_tst
#print axioms ATK.NSDuhamel.hasCompactSupport_tst
#print axioms ATK.NSDuhamel.tstS_apply
#print axioms ATK.NSDuhamel.mtf_tst_qf
#print axioms ATK.NSDuhamel.fw
#print axioms ATK.NSDuhamel.intervalIntegrable_Ap
#print axioms ATK.NSDuhamel.stronglyMeasurable_NUc
#print axioms ATK.NSDuhamel.intervalIntegrable_np_fam
#print axioms ATK.NSDuhamel.mtf_tst_lin
#print axioms ATK.NSDuhamel.Ap_lin
#print axioms ATK.NSDuhamel.np_lin
#print axioms ATK.NSDuhamel.Ap_sub
#print axioms ATK.NSDuhamel.np_sub
#print axioms ATK.NSDuhamel.uIcc_sub
#print axioms ATK.NSDuhamel.lip_Ap
#print axioms ATK.NSDuhamel.duhamel
