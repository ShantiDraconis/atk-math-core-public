import ATK.RHLogZeta
import ATK.GammaVertical
import ATK.ZeroClasses.VariacaoArg

/-!
# RH ⟹ a hipótese de Lindelöf (rodada 61)

**`lindelof_of_RH`**: sob RH, para todo `ε > 0` existe `C` com `|ζ(½ + it)| ≤ C(1 + |t|)^ε` para todo `t` — a
hipótese de Lindelöf (`Lindelof`), que é OPEN_MATH sem RH.

A prova (Titchmarsh §14.2) junta três peças já certificadas:

* `ATK.RHLogZeta.norm_zeta_le_RH` (rodada 38): sob RH, `|ζ(s)| ≤ C(1 + |t|)^η` em `½ + δ ≤ Re s ≤ ¾`;
* `ATK.GammaVertical.norm_zeta_one_sub_le` (Stirling + equação funcional): `|ζ(1 − w)| ≤ 2C_Γ|w|^{Re w − ½}|ζ(w)|`,
  que leva a cota à reta `Re s = ½ − δ` com expoente `δ + η`;
* **Phragmén–Lindelöf** da Mathlib na faixa `½ − δ ≤ Re s ≤ ½ + δ`, aplicado a `g(s) = ζ(s)(s + 2)^{−(δ+η)}`
  (limitada nas duas retas; crescimento polinomial dentro, por `ATK.ZeroClasses.VariacaoArg.cota_zeta_quarto`).

Com `δ = η = ε/4`, `|ζ(½ + it)| ≤ C|½ + it + 2|^{ε/2}`.

Classificação (rodada 61): **consequência** de RH (RH ⟹ LH). A hipótese de Lindelöf continua OPEN_MATH.
-/

open Complex Set Filter Asymptotics
open scoped Real

namespace ATK.ZeroClasses.LindelofRH

open ATK.GammaVertical (CΓ CΓ_pos norm_zeta_one_sub_le)

/-- **A hipótese de Lindelöf**: `ζ(½ + it) = O((1 + |t|)^ε)` para todo `ε > 0`. -/
def Lindelof : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * (1 + |t|) ^ ε

/-- `g(s) = ζ(s)(s + 2)^{−k}`. -/
noncomputable def gL (k : ℝ) (s : ℂ) : ℂ := riemannZeta s * (s + 2) ^ (-(k : ℂ))

theorem norm_cpow_neg (k : ℝ) (s : ℂ) : ‖(s + 2) ^ (-(k : ℂ))‖ = ‖s + 2‖ ^ (-k) := by
  rw [show (-(k : ℂ)) = ((-k : ℝ) : ℂ) by push_cast; ring, Complex.norm_cpow_real]

theorem norm_gL (k : ℝ) (s : ℂ) : ‖gL k s‖ = ‖riemannZeta s‖ * ‖s + 2‖ ^ (-k) := by
  rw [gL, norm_mul, norm_cpow_neg]

theorem one_le_norm_add_two {s : ℂ} (hs : 0 ≤ s.re) : 1 ≤ ‖s + 2‖ := by
  have := Complex.re_le_norm (s + 2)
  rw [add_re, re_ofNat] at this
  linarith

theorem um_add_le {s : ℂ} (hs : 0 ≤ s.re) : 1 + |s.im| ≤ 2 * ‖s + 2‖ := by
  have h1 := one_le_norm_add_two hs
  have h2 : |s.im| ≤ ‖s + 2‖ := by
    have := Complex.abs_im_le_norm (s + 2)
    rwa [add_im, im_ofNat, add_zero] at this
  linarith

/-- `(1 + |t|)^a ‖s + 2‖^{−k} ≤ 2^a` se `0 ≤ a ≤ k`. -/
theorem fator_le {s : ℂ} (hs : 0 ≤ s.re) {a k : ℝ} (ha : 0 ≤ a) (hak : a ≤ k) :
    (1 + |s.im|) ^ a * ‖s + 2‖ ^ (-k) ≤ 2 ^ a := by
  have h1 := one_le_norm_add_two hs
  have hn0 : 0 < ‖s + 2‖ := by linarith
  have hp : (1 + |s.im|) ^ a ≤ 2 ^ a * ‖s + 2‖ ^ a := by
    rw [← Real.mul_rpow (by norm_num) hn0.le]
    exact Real.rpow_le_rpow (by positivity) (um_add_le hs) ha
  have hq : ‖s + 2‖ ^ a * ‖s + 2‖ ^ (-k) ≤ 1 := by
    rw [← Real.rpow_add hn0]
    exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
  calc (1 + |s.im|) ^ a * ‖s + 2‖ ^ (-k) ≤ 2 ^ a * ‖s + 2‖ ^ a * ‖s + 2‖ ^ (-k) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 2 ^ a * (‖s + 2‖ ^ a * ‖s + 2‖ ^ (-k)) := by ring
    _ ≤ 2 ^ a * 1 := mul_le_mul_of_nonneg_left hq (by positivity)
    _ = 2 ^ a := mul_one _

/-- Na faixa `¼ ≤ Re s ≤ ¾`, `|g(s)| ≤ 11(1 + |t|)` (crescimento polinomial). -/
theorem norm_gL_faixa {k : ℝ} (hk : 0 ≤ k) {s : ℂ} (h1 : 1 / 4 ≤ s.re) (h2 : s.re ≤ 3 / 4) :
    ‖gL k s‖ ≤ 11 * (1 + |s.im|) := by
  have hs1 : s ≠ 1 := by intro h; rw [h, one_re] at h2; norm_num at h2
  have hz := ATK.ZeroClasses.VariacaoArg.cota_zeta_quarto h1 hs1
  have hd : 1 / 4 ≤ ‖s - 1‖ := by
    have := Complex.abs_re_le_norm (s - 1)
    rw [sub_re, one_re] at this
    have : |s.re - 1| = 1 - s.re := by rw [abs_of_nonpos (by linarith)]; ring
    linarith
  have hinv : 1 / ‖s - 1‖ ≤ 4 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hs : ‖s‖ ≤ 1 + |s.im| := by
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 1 + |s.im| := by
          have : |s.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
          linarith
  have hc : ‖s + 2‖ ^ (-k) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (one_le_norm_add_two (by linarith)) (by linarith)
  rw [norm_gL]
  calc ‖riemannZeta s‖ * ‖s + 2‖ ^ (-k) ≤ ‖riemannZeta s‖ * 1 :=
        mul_le_mul_of_nonneg_left hc (norm_nonneg _)
    _ ≤ 1 / 2 + 4 + 6 * (1 + |s.im|) := by linarith
    _ ≤ 11 * (1 + |s.im|) := by nlinarith [abs_nonneg s.im]

theorem differentiableAt_gL (k : ℝ) {s : ℂ} (h1 : 0 ≤ s.re) (h2 : s.re < 1) :
    DifferentiableAt ℂ (gL k) s := by
  have hs1 : s ≠ 1 := by intro h; rw [h, one_re] at h2; exact lt_irrefl 1 h2
  have hslit : s + 2 ∈ slitPlane := by
    rw [mem_slitPlane_iff]; left; rw [add_re, re_ofNat]; linarith
  exact (differentiableAt_riemannZeta hs1).mul
    ((differentiableAt_id.add_const 2).cpow (differentiableAt_const _) hslit)

/-- **RH ⟹ Lindelöf**, com `0 < ε ≤ 1`. -/
theorem lindelof_um (hRH : RiemannHypothesis) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, ∀ t : ℝ, ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * (1 + |t|) ^ ε := by
  set δ : ℝ := ε / 4 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ ≤ 1 / 4 := by rw [hδ]; linarith
  obtain ⟨C₁, hC₁, hζ⟩ := ATK.RHLogZeta.norm_zeta_le_RH hRH (δ := δ) (η := δ) hδ0 (by linarith) hδ0
  set k : ℝ := δ + δ with hk
  have hk0 : 0 ≤ k := by rw [hk]; linarith
  set C₂ : ℝ := C₁ * 2 ^ δ + 2 * CΓ * C₁ * 4 ^ δ * 2 ^ k with hC₂
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; have := CΓ_pos; positivity
  -- Phragmén–Lindelöf
  have hPL : ∀ z : ℂ, 1 / 2 - δ ≤ z.re → z.re ≤ 1 / 2 + δ → ‖gL k z‖ ≤ C₂ := by
    intro z hza hzb
    have hsub : closure (re ⁻¹' Ioo (1 / 2 - δ) (1 / 2 + δ)) ⊆ re ⁻¹' Icc (1 / 2 - δ) (1 / 2 + δ) :=
      closure_minimal (fun w hw => ⟨le_of_lt hw.1, le_of_lt hw.2⟩)
        (isClosed_Icc.preimage Complex.continuous_re)
    refine PhragmenLindelof.vertical_strip (a := 1 / 2 - δ) (b := 1 / 2 + δ) ?_ ?_ ?_ ?_ hza hzb
    · refine ⟨fun w (hw : w ∈ re ⁻¹' Ioo (1 / 2 - δ) (1 / 2 + δ)) =>
        (differentiableAt_gL k (by have := hw.1; linarith) (by have := hw.2; linarith)).differentiableWithinAt,
        fun w hw => ?_⟩
      have hw' := hsub hw
      exact (differentiableAt_gL k (by have := hw'.1; linarith)
        (by have := hw'.2; linarith)).continuousAt.continuousWithinAt
    · refine ⟨1, by
        have := Real.pi_gt_three
        rw [show (1 / 2 + δ) - (1 / 2 - δ) = 2 * δ by ring, lt_div_iff₀ (by linarith)]
        nlinarith, 1, ?_⟩
      refine Asymptotics.IsBigO.of_bound 11 ?_
      refine Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall fun w hw => ?_)
      have hw1 : 1 / 4 ≤ w.re := by have := hw.1; linarith
      have hw2 : w.re ≤ 3 / 4 := by have := hw.2; linarith
      refine (norm_gL_faixa hk0 hw1 hw2).trans ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul, one_mul]
      have e1 := Real.add_one_le_exp |w.im|
      have e2 := Real.add_one_le_exp (Real.exp |w.im|)
      have : 1 + |w.im| ≤ Real.exp (Real.exp |w.im|) := by linarith
      linarith
    · -- a reta esquerda `Re z = ½ − δ`: equação funcional
      intro w hw
      set u : ℂ := 1 - w with hu
      have hure : u.re = 1 / 2 + δ := by rw [hu, sub_re, one_re, hw]; ring
      have hu1 : u ≠ 1 := by
        intro h; rw [h, one_re] at hure; linarith
      have hfe := norm_zeta_one_sub_le (w := u) (by linarith) (by linarith) hu1
      rw [show (1 : ℂ) - u = w by rw [hu]; ring, hure] at hfe
      have hζu := hζ u (by linarith) (by linarith)
      have huim : |u.im| = |w.im| := by rw [hu, sub_im, one_im, zero_sub, abs_neg]
      rw [huim] at hζu
      have hw0 : 0 ≤ w.re := by linarith
      have hun : ‖u‖ ≤ 4 * ‖w + 2‖ := by
        have h1 := one_le_norm_add_two hw0
        calc ‖u‖ = ‖3 - (w + 2)‖ := by rw [hu]; ring_nf
          _ ≤ ‖(3 : ℂ)‖ + ‖w + 2‖ := norm_sub_le _ _
          _ ≤ 4 * ‖w + 2‖ := by rw [norm_ofNat]; linarith
      have hupow : ‖u‖ ^ (1 / 2 + δ - 1 / 2) ≤ 4 ^ δ * ‖w + 2‖ ^ δ := by
        rw [show 1 / 2 + δ - 1 / 2 = δ by ring, ← Real.mul_rpow (by norm_num) (norm_nonneg _)]
        exact Real.rpow_le_rpow (norm_nonneg _) hun hδ0.le
      have hn0 : 0 < ‖w + 2‖ := by linarith [one_le_norm_add_two hw0]
      have hmain : ‖riemannZeta w‖ ≤ 2 * CΓ * C₁ * 4 ^ δ * (‖w + 2‖ ^ δ * (1 + |w.im|) ^ δ) := by
        calc ‖riemannZeta w‖ ≤ 2 * CΓ * ‖u‖ ^ (1 / 2 + δ - 1 / 2) * ‖riemannZeta u‖ := hfe
          _ ≤ 2 * CΓ * (4 ^ δ * ‖w + 2‖ ^ δ) * (C₁ * (1 + |w.im|) ^ δ) := by
              have := CΓ_pos
              gcongr
          _ = 2 * CΓ * C₁ * 4 ^ δ * (‖w + 2‖ ^ δ * (1 + |w.im|) ^ δ) := by ring
      have hpow : ‖w + 2‖ ^ δ * ‖w + 2‖ ^ (-k) = ‖w + 2‖ ^ (-δ) := by
        rw [← Real.rpow_add hn0]; congr 1; rw [hk]; ring
      have hf := fator_le hw0 (a := δ) (k := δ) hδ0.le le_rfl
      have h2k : (2 : ℝ) ^ δ ≤ 2 ^ k := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by rw [hk]; linarith)
      have hA : 0 ≤ 2 * CΓ * C₁ * 4 ^ δ := by have := CΓ_pos; positivity
      rw [norm_gL]
      calc ‖riemannZeta w‖ * ‖w + 2‖ ^ (-k)
          ≤ 2 * CΓ * C₁ * 4 ^ δ * (‖w + 2‖ ^ δ * (1 + |w.im|) ^ δ) * ‖w + 2‖ ^ (-k) :=
            mul_le_mul_of_nonneg_right hmain (by positivity)
        _ = 2 * CΓ * C₁ * 4 ^ δ * ((1 + |w.im|) ^ δ * (‖w + 2‖ ^ δ * ‖w + 2‖ ^ (-k))) := by ring
        _ = 2 * CΓ * C₁ * 4 ^ δ * ((1 + |w.im|) ^ δ * ‖w + 2‖ ^ (-δ)) := by rw [hpow]
        _ ≤ 2 * CΓ * C₁ * 4 ^ δ * 2 ^ δ := mul_le_mul_of_nonneg_left hf hA
        _ ≤ 2 * CΓ * C₁ * 4 ^ δ * 2 ^ k := mul_le_mul_of_nonneg_left h2k hA
        _ ≤ C₂ := by
            rw [hC₂]
            have : 0 ≤ C₁ * 2 ^ δ := by positivity
            linarith
    · -- a reta direita `Re z = ½ + δ`
      intro w hw
      have hw0 : 0 ≤ w.re := by linarith
      rw [norm_gL]
      have h1 := hζ w (by linarith) (by linarith)
      have hfat := fator_le hw0 (a := δ) (k := k) hδ0.le (by rw [hk]; linarith)
      calc ‖riemannZeta w‖ * ‖w + 2‖ ^ (-k) ≤ C₁ * (1 + |w.im|) ^ δ * ‖w + 2‖ ^ (-k) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = C₁ * ((1 + |w.im|) ^ δ * ‖w + 2‖ ^ (-k)) := by ring
        _ ≤ C₁ * 2 ^ δ := mul_le_mul_of_nonneg_left hfat hC₁.le
        _ ≤ C₂ := by
            rw [hC₂]
            have : 0 ≤ 2 * CΓ * C₁ * 4 ^ δ * 2 ^ k := by have := CΓ_pos; positivity
            linarith
  refine ⟨C₂ * 3 ^ k, fun t => ?_⟩
  set z : ℂ := 1 / 2 + t * I with hz
  have hzre : z.re = 1 / 2 := by rw [hz]; simp
  have hzim : z.im = t := by rw [hz]; simp
  have h := hPL z (by rw [hzre]; linarith) (by rw [hzre]; linarith)
  rw [norm_gL] at h
  have hz0 : 0 ≤ z.re := by rw [hzre]; norm_num
  have hn1 := one_le_norm_add_two hz0
  have hn0 : 0 < ‖z + 2‖ := by linarith
  have hpos : 0 < ‖z + 2‖ ^ (-k) := Real.rpow_pos_of_pos hn0 _
  have hζz : ‖riemannZeta z‖ ≤ C₂ * ‖z + 2‖ ^ k := by
    have h' : ‖riemannZeta z‖ ≤ C₂ / ‖z + 2‖ ^ (-k) := by rw [le_div_iff₀ hpos]; exact h
    rwa [Real.rpow_neg hn0.le, div_inv_eq_mul] at h'
  have hzn : ‖z + 2‖ ≤ 3 * (1 + |t|) := by
    calc ‖z + 2‖ ≤ |(z + 2).re| + |(z + 2).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = 5 / 2 + |t| := by
          rw [add_re, add_im, hzre, hzim, re_ofNat, im_ofNat, add_zero]; norm_num
      _ ≤ 3 * (1 + |t|) := by nlinarith [abs_nonneg t]
  have hkε : k ≤ ε := by rw [hk, hδ]; linarith
  have h1t : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  calc ‖riemannZeta z‖ ≤ C₂ * ‖z + 2‖ ^ k := hζz
    _ ≤ C₂ * (3 * (1 + |t|)) ^ k := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (norm_nonneg _) hzn hk0) hC₂0
    _ = C₂ * 3 ^ k * (1 + |t|) ^ k := by
        rw [Real.mul_rpow (by norm_num) (by linarith)]; ring
    _ ≤ C₂ * 3 ^ k * (1 + |t|) ^ ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le h1t hkε) (by positivity)

/-- **RH ⟹ a hipótese de Lindelöf**: `ζ(½ + it) = O((1 + |t|)^ε)` para todo `ε > 0`. -/
theorem lindelof_of_RH (hRH : RiemannHypothesis) : Lindelof := by
  intro ε hε
  rcases le_or_gt ε 1 with h1 | h1
  · exact lindelof_um hRH hε h1
  · obtain ⟨C, hC⟩ := lindelof_um hRH one_pos le_rfl
    have hC0 : 0 ≤ C := by
      have := hC 0
      simp only [abs_zero, add_zero, Real.one_rpow, mul_one] at this
      exact le_trans (norm_nonneg _) this
    refine ⟨C, fun t => (hC t).trans ?_⟩
    have h1t : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1t h1.le) hC0

end ATK.ZeroClasses.LindelofRH

#print axioms ATK.ZeroClasses.LindelofRH.norm_cpow_neg
#print axioms ATK.ZeroClasses.LindelofRH.norm_gL
#print axioms ATK.ZeroClasses.LindelofRH.one_le_norm_add_two
#print axioms ATK.ZeroClasses.LindelofRH.um_add_le
#print axioms ATK.ZeroClasses.LindelofRH.fator_le
#print axioms ATK.ZeroClasses.LindelofRH.norm_gL_faixa
#print axioms ATK.ZeroClasses.LindelofRH.differentiableAt_gL
#print axioms ATK.ZeroClasses.LindelofRH.lindelof_um
#print axioms ATK.ZeroClasses.LindelofRH.lindelof_of_RH
