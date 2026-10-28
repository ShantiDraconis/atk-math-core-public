import ATK.ZeroClasses.RegiaoLivre

/-!
# `ζ′/ζ = O(log² t)` na região livre de zeros (rodada 52)

Primeira peça do teorema dos números primos com o termo de erro de de la Vallée Poussin. Sobre o lema de Landau
(rodada 36) e a região livre de zeros (rodada 37):

* **`landau_fora`** — o lema de Landau **fora do centro**, com contagem: se `f` é analítica em `‖z − z₀‖ ≤ R`,
  `f(z₀) ≠ 0` e `‖f‖ ≤ M‖f(z₀)‖` lá, os zeros `S` em `‖z − z₀‖ ≤ R/4` satisfazem `(Σ m_ρ) log 2 ≤ log M` e, para
  todo `z` com `‖z − z₀‖ ≤ R/16` e `f(z) ≠ 0`,
  `‖f′/f(z) − Σ_{ρ ∈ S} m_ρ/(z − ρ)‖ ≤ 32(log M + 1)/R`
  (módulo máximo de `f/Q` no círculo `3R/4` para a contagem; Borel–Carathéodory no disco `R/8` e Cauchy no círculo
  `R/16` em volta de `z`);
* `zeta_disco` e **`zeta_local_fora`**: a aplicação a `ζ` no disco `‖z − (σ + it)‖ ≤ ½`, `1 < σ ≤ 2`, `|t| ≥ 2`;
* `norm_logDeriv_le`: `|ζ′/ζ(σ + it)| ≤ −ζ′/ζ(σ)` em `σ > 1` (série de von Mangoldt);
* **`logDeriv_zeta_le`**: existem `c > 0`, `T₁` e `C` tais que, para `|t| ≥ T₁` e
  `1 − c/log|t| ≤ σ ≤ 2`, `ζ(σ + it) ≠ 0` e `|ζ′/ζ(σ + it)| ≤ C log²|t|`.

Classificação (rodada 52): **ferramenta** (a cota de `ζ′/ζ` que o deslocamento de contorno do TNP pede). RH continua
OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.LogDerivZeta

open ATK.ZeroClasses.Landau (quociente_local ordem_poli logDeriv_poli)
open ATK.ZeroClasses.RegiaoLivre (cota_zeta_faixa zeta_lb re_lt_um)

/-! ## 1. O lema de Landau fora do centro -/

/-- **Landau fora do centro, com contagem.** -/
theorem landau_fora {f : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ R)) (hf0 : f z₀ ≠ 0)
    (hb : ∀ z ∈ closedBall z₀ R, ‖f z‖ ≤ M * ‖f z₀‖) :
    ∃ S : Finset ℂ, (∀ u ∈ S, u ∈ closedBall z₀ (R / 4) ∧ f u = 0) ∧
      (∀ u ∈ closedBall z₀ (R / 4), f u = 0 → u ∈ S) ∧
      ((∑ u ∈ S, analyticOrderNatAt f u : ℕ) : ℝ) * Real.log 2 ≤ Real.log M ∧
      ∀ z ∈ closedBall z₀ (R / 16), f z ≠ 0 →
        ‖logDeriv f z - ∑ u ∈ S, (analyticOrderNatAt f u : ℂ) / (z - u)‖ ≤
          32 * (Real.log M + 1) / R := by
  classical
  have hR4 : R / 4 ≤ R := by linarith
  -- ordens finitas
  have htopf : ∀ u ∈ closedBall z₀ R, analyticOrderAt f u ≠ ⊤ := fun u hu =>
    ATK.ArgPrincipio.ordem_finita hf (convex_closedBall z₀ R).isPreconnected
      (mem_closedBall_self hR.le) hf0 hu
  -- os zeros no disco de raio R/4 são finitos
  set Zs := {u | u ∈ closedBall z₀ (R / 4) ∧ f u = 0} with hZs
  have hfin : Zs.Finite := by
    have han4 : AnalyticOnNhd ℂ f (closedBall z₀ |R / 4|) := by
      rw [abs_of_pos (by linarith)]
      exact hf.mono (closedBall_subset_closedBall hR4)
    have hD := (MeromorphicOn.divisor f (closedBall z₀ |R / 4|)).finiteSupport (isCompact_closedBall _ _)
    refine hD.subset fun u ⟨hu, hfu⟩ => ?_
    have hu' : u ∈ closedBall z₀ |R / 4| := by rwa [abs_of_pos (by linarith)]
    rw [Function.mem_support, ATK.ArgPrincipio.divisor_eq_ordem han4 hu'
      (htopf u (closedBall_subset_closedBall hR4 hu))]
    have h0 : analyticOrderNatAt f u ≠ 0 := by
      intro h
      exact ((ATK.ArgPrincipio.ordemNat_zero_iff (hf u (closedBall_subset_closedBall hR4 hu))
        (htopf u (closedBall_subset_closedBall hR4 hu))).mp h) hfu
    exact_mod_cast h0
  set S := hfin.toFinset with hS
  have hmemS : ∀ u, u ∈ S ↔ u ∈ closedBall z₀ (R / 4) ∧ f u = 0 := fun u => by
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  refine ⟨S, fun u hu => (hmemS u).mp hu, fun u hu hfu => (hmemS u).mpr ⟨hu, hfu⟩, ?_⟩
  set m : ℂ → ℕ := fun u => analyticOrderNatAt f u with hm
  set Q : ℂ → ℂ := fun z => ∏ u ∈ S, (z - u) ^ m u with hQ
  have hz₀S : z₀ ∉ S := fun h => hf0 ((hmemS z₀).mp h).2
  have hQan : AnalyticOnNhd ℂ Q univ := fun z _ => by simp only [hQ]; fun_prop
  -- ordens de Q
  have hordQ : ∀ w, analyticOrderAt Q w = if w ∈ S then (m w : ℕ∞) else 0 := fun w => ordem_poli S m w
  have hmw : ∀ w ∈ S, (m w : ℕ∞) = analyticOrderAt f w := by
    intro w hw
    have hwR := closedBall_subset_closedBall hR4 ((hmemS w).mp hw).1
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (htopf w hwR)
    simp only [hm, analyticOrderNatAt, ← hk]
    simp
  have hle : ∀ w ∈ ball z₀ R, analyticOrderAt Q w ≤ analyticOrderAt f w := by
    intro w _
    rw [hordQ]
    split_ifs with h
    · rw [hmw w h]
    · simp
  have htopQ : ∀ w ∈ ball z₀ R, analyticOrderAt Q w ≠ ⊤ := by
    intro w _
    rw [hordQ]
    split_ifs <;> simp
  obtain ⟨G, hGan, hfQG, hG0⟩ := quociente_local isOpen_ball (hf.mono ball_subset_closedBall)
    (hQan.mono (subset_univ _)) hle htopQ
  have hGne : ∀ w ∈ closedBall z₀ (R / 4), G w ≠ 0 := by
    intro w hw
    have hwb : w ∈ ball z₀ R := mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hw) (by linarith))
    apply hG0 w hwb
    rw [hordQ]
    split_ifs with h
    · exact (hmw w h).symm
    · have hfw : f w ≠ 0 := fun h' => h ((hmemS w).mpr ⟨hw, h'⟩)
      exact analyticOrderAt_eq_zero.mpr (Or.inr hfw)
  -- cotas de Q
  set n := ∑ u ∈ S, m u with hn
  have hQ0 : ‖Q z₀‖ ≤ (R / 4) ^ n := by
    simp only [hQ, norm_prod, norm_pow]
    rw [hn, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun u _ => by positivity) (fun u hu => ?_)
    have := ((hmemS u).mp hu).1
    rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this _
  have hQs : ∀ z ∈ sphere z₀ (R / 2), (R / 4) ^ n ≤ ‖Q z‖ := by
    intro z hz
    simp only [hQ, norm_prod, norm_pow]
    rw [hn, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun u _ => by positivity) (fun u hu => ?_)
    have hu := ((hmemS u).mp hu).1
    rw [mem_closedBall, dist_eq_norm] at hu
    rw [mem_sphere_iff_norm] at hz
    have : R / 4 ≤ ‖z - u‖ := by
      have h := norm_sub_norm_le (z - z₀) (u - z₀)
      rw [show z - z₀ - (u - z₀) = z - u by ring] at h
      linarith
    exact pow_le_pow_left₀ (by positivity) this _
  have hQz₀ : Q z₀ ≠ 0 := by
    simp only [hQ]
    exact Finset.prod_ne_zero_iff.mpr fun u hu =>
      pow_ne_zero _ (sub_ne_zero.mpr (fun h => hz₀S (by rw [h]; exact hu)))
  have hz₀b : z₀ ∈ ball z₀ R := mem_ball_self hR
  have hGz₀ : G z₀ = f z₀ / Q z₀ := by
    rw [hfQG z₀ hz₀b, mul_div_cancel_left₀ _ hQz₀]
  -- módulo máximo: ‖G‖ ≤ M ‖G z₀‖ em ‖z − z₀‖ ≤ R/2
  have hsph : ∀ z ∈ sphere z₀ (R / 2), ‖G z‖ ≤ M * ‖G z₀‖ := by
    intro z hz
    have hzb : z ∈ ball z₀ R := by
      rw [mem_sphere_iff_norm] at hz
      rw [mem_ball, dist_eq_norm, hz]
      linarith
    have hQz := hQs z hz
    have hQpos : 0 < ‖Q z‖ := lt_of_lt_of_le (by positivity) hQz
    have hGz : G z = f z / Q z := by
      rw [hfQG z hzb, mul_div_cancel_left₀ _ (norm_pos_iff.mp hQpos)]
    have hfz := hb z (ball_subset_closedBall hzb)
    have hQ0pos : 0 < ‖Q z₀‖ := norm_pos_iff.mpr hQz₀
    rw [hGz, hGz₀, norm_div, norm_div]
    rw [div_le_iff₀ hQpos]
    calc ‖f z‖ ≤ M * ‖f z₀‖ := hfz
      _ = M * (‖f z₀‖ / ‖Q z₀‖) * ‖Q z₀‖ := by field_simp
      _ ≤ M * (‖f z₀‖ / ‖Q z₀‖) * ‖Q z‖ := by
          have : 0 ≤ M * (‖f z₀‖ / ‖Q z₀‖) := by positivity
          exact mul_le_mul_of_nonneg_left (hQ0.trans hQz) this
  have hGd2 : DifferentiableOn ℂ G (closedBall z₀ (R / 2)) := fun z hz =>
    (hGan z (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith)))).differentiableAt.differentiableWithinAt
  have hmax : ∀ z ∈ closedBall z₀ (R / 2), ‖G z‖ ≤ M * ‖G z₀‖ := by
    intro z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (DifferentiableOn.diffContOnCl (by rw [closure_ball z₀ (show R / 2 ≠ 0 by positivity)]; exact hGd2)) ?_
      (by rw [closure_ball z₀ (show R / 2 ≠ 0 by positivity)]; exact hz)
    rw [frontier_ball z₀ (show R / 2 ≠ 0 by positivity)]
    exact hsph
  -- a contagem: `2^n ≤ M` (módulo máximo de `G` em `‖z − z₀‖ ≤ 3R/4`)
  have hcount : (n : ℝ) * Real.log 2 ≤ Real.log M := by
    have hQs3 : ∀ z ∈ sphere z₀ (3 * R / 4), (R / 2) ^ n ≤ ‖Q z‖ := by
      intro z hz
      simp only [hQ, norm_prod, norm_pow]
      rw [hn, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod₀ (fun u _ => by positivity) (fun u hu => ?_)
      have hu := ((hmemS u).mp hu).1
      rw [mem_closedBall, dist_eq_norm] at hu
      rw [mem_sphere_iff_norm] at hz
      have : R / 2 ≤ ‖z - u‖ := by
        have h := norm_sub_norm_le (z - z₀) (u - z₀)
        rw [show z - z₀ - (u - z₀) = z - u by ring] at h
        linarith
      exact pow_le_pow_left₀ (by positivity) this _
    have hGd3 : DifferentiableOn ℂ G (closedBall z₀ (3 * R / 4)) := fun z hz =>
      (hGan z (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith)))).differentiableAt.differentiableWithinAt
    have hsph3 : ∀ z ∈ sphere z₀ (3 * R / 4), ‖G z‖ ≤ M * ‖f z₀‖ / (R / 2) ^ n := by
      intro z hz
      have hzb : z ∈ ball z₀ R := by
        rw [mem_sphere_iff_norm] at hz
        rw [mem_ball, dist_eq_norm, hz]
        linarith
      have hQz := hQs3 z hz
      have hQpos : 0 < ‖Q z‖ := lt_of_lt_of_le (by positivity) hQz
      have hGz : G z = f z / Q z := by
        rw [hfQG z hzb, mul_div_cancel_left₀ _ (norm_pos_iff.mp hQpos)]
      rw [hGz, norm_div, div_le_div_iff₀ hQpos (by positivity)]
      have hfz := hb z (ball_subset_closedBall hzb)
      calc ‖f z‖ * (R / 2) ^ n ≤ (M * ‖f z₀‖) * ‖Q z‖ :=
            mul_le_mul hfz hQz (by positivity) (by positivity)
        _ = M * ‖f z₀‖ * ‖Q z‖ := by ring
    have hGz₀le : ‖G z₀‖ ≤ M * ‖f z₀‖ / (R / 2) ^ n := by
      refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
        (DifferentiableOn.diffContOnCl (by
          rw [closure_ball z₀ (show 3 * R / 4 ≠ 0 by positivity)]; exact hGd3)) ?_
        (by rw [closure_ball z₀ (show 3 * R / 4 ≠ 0 by positivity)]; exact mem_closedBall_self (by positivity))
      rw [frontier_ball z₀ (show 3 * R / 4 ≠ 0 by positivity)]
      exact hsph3
    rw [hGz₀, norm_div] at hGz₀le
    have hf0pos : 0 < ‖f z₀‖ := norm_pos_iff.mpr hf0
    have hQ0pos : 0 < ‖Q z₀‖ := norm_pos_iff.mpr hQz₀
    have h1 : ‖f z₀‖ / (R / 4) ^ n ≤ ‖f z₀‖ / ‖Q z₀‖ := div_le_div_of_nonneg_left hf0pos.le hQ0pos hQ0
    have h2 : ‖f z₀‖ / (R / 4) ^ n ≤ M * ‖f z₀‖ / (R / 2) ^ n := h1.trans hGz₀le
    have e : (R / 2) ^ n = 2 ^ n * (R / 4) ^ n := by rw [← mul_pow]; ring_nf
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)] at h2
    have h2' : 2 ^ n * (‖f z₀‖ * (R / 4) ^ n) ≤ M * (‖f z₀‖ * (R / 4) ^ n) := by linarith
    have h3 : (2 : ℝ) ^ n ≤ M := le_of_mul_le_mul_right h2' (by positivity)
    have h4 := Real.log_le_log (by positivity) h3
    rwa [Real.log_pow] at h4
  -- o logaritmo em ‖z − z₀‖ < R/4
  set B := ball z₀ (R / 4) with hBdef
  have hBsub : B ⊆ ball z₀ R := ball_subset_ball hR4
  have hGB : ∀ z ∈ B, G z ≠ 0 := fun z hz => hGne z (ball_subset_closedBall hz)
  have hΦ : DifferentiableOn ℂ (fun z => deriv G z / G z) B := by
    intro z hz
    have hza := hGan z (hBsub hz)
    exact (hza.deriv.differentiableAt.div hza.differentiableAt (hGB z hz)).differentiableWithinAt
  obtain ⟨H, hH0, hH⟩ := (hΦ.isExactOn_ball).with_val_at z₀ 0
  have hHd : DifferentiableOn ℂ H B := fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
  have hK : ∀ z ∈ B, G z * cexp (-H z) = G z₀ := by
    intro z hz
    have hd : ∀ w ∈ B, HasDerivAt (fun w => G w * cexp (-H w)) 0 w := by
      intro w hw
      have h1 := (hGan w (hBsub hw)).differentiableAt.hasDerivAt
      have h2 := ((hH w hw).neg).cexp
      convert h1.mul h2 using 1
      field_simp [hGB w hw]
      ring
    have hc := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z₀ (R / 4)).isPreconnected
      (fun w hw => (hd w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hd w hw).deriv) hz (mem_ball_self (by linarith))
    rw [hc, hH0, neg_zero, Complex.exp_zero, mul_one]
  have hreH : ∀ z ∈ B, (H z).re ≤ Real.log M + 1 := by
    intro z hz
    have e : cexp (H z) = G z / G z₀ := by
      have h := hK z hz
      rw [Complex.exp_neg] at h
      rw [← h]
      have hGz : G z ≠ 0 := hGB z hz
      have he : cexp (H z) ≠ 0 := Complex.exp_ne_zero _
      field_simp
    have hn := congrArg norm e
    rw [Complex.norm_exp, norm_div] at hn
    have hG0pos : 0 < ‖G z₀‖ := norm_pos_iff.mpr (hGB z₀ (mem_ball_self (by linarith)))
    have hle' : ‖G z‖ / ‖G z₀‖ ≤ M := by
      rw [div_le_iff₀ hG0pos]
      exact hmax z (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz))
    have : Real.exp (H z).re ≤ M := hn ▸ hle'
    have hlog := Real.log_le_log (Real.exp_pos _) this
    rw [Real.log_exp] at hlog
    linarith
  -- Borel–Carathéodory: `‖H‖ ≤ 2A` em `‖z − z₀‖ ≤ R/8`
  set A := Real.log M + 1 with hA
  have hA0 : 0 < A := by have := Real.log_nonneg hM; linarith
  have hBC : ∀ z ∈ closedBall z₀ (R / 8), ‖H z‖ ≤ 2 * A := by
    intro z hz
    have hzn : ‖z - z₀‖ ≤ R / 8 := by rw [mem_closedBall, dist_eq_norm] at hz; exact hz
    have hzz : z - z₀ ∈ ball (0 : ℂ) (R / 4) := by
      rw [mem_ball_zero_iff]
      linarith
    have hdiff : DifferentiableOn ℂ (fun w => H (z₀ + w)) (ball 0 (R / 4)) := by
      intro w hw
      have hw' : z₀ + w ∈ B := by
        rw [hBdef, mem_ball, dist_eq_norm, add_sub_cancel_left]
        exact mem_ball_zero_iff.mp hw
      exact ((hH (z₀ + w) hw').differentiableAt.comp w
        ((differentiableAt_const z₀).add differentiableAt_id)).differentiableWithinAt
    have hmaps : MapsTo (fun w => H (z₀ + w)) (ball 0 (R / 4)) {z | z.re ≤ A} := by
      intro w hw
      show (H (z₀ + w)).re ≤ A
      apply hreH
      rw [hBdef, mem_ball, dist_eq_norm, add_sub_cancel_left]
      exact mem_ball_zero_iff.mp hw
    have hbc := Complex.borelCaratheodory_zero hA0 hdiff hmaps (by linarith) hzz (by simp [hH0])
    simp only [add_sub_cancel] at hbc
    have hden : 0 < R / 4 - ‖z - z₀‖ := by linarith
    calc ‖H z‖ ≤ 2 * A * ‖z - z₀‖ / (R / 4 - ‖z - z₀‖) := hbc
      _ ≤ 2 * A := by
        rw [div_le_iff₀ hden]
        nlinarith [norm_nonneg (z - z₀)]
  refine ⟨?_, fun z hz hfz => ?_⟩
  · have e : ((∑ u ∈ S, analyticOrderNatAt f u : ℕ) : ℝ) = (n : ℝ) := rfl
    rw [e]
    exact hcount
  have hzn : ‖z - z₀‖ ≤ R / 16 := by rw [mem_closedBall, dist_eq_norm] at hz; exact hz
  have hzB : z ∈ B := by
    rw [hBdef, mem_ball, dist_eq_norm]
    linarith
  have hzb : z ∈ ball z₀ R := hBsub hzB
  have hsub : closedBall z (R / 16) ⊆ closedBall z₀ (R / 8) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw ⊢
    calc ‖w - z₀‖ ≤ ‖w - z‖ + ‖z - z₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ R / 16 + R / 16 := add_le_add hw hzn
      _ = R / 8 := by ring
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < R / 16)
    (DifferentiableOn.diffContOnCl (by
      rw [closure_ball z (show R / 16 ≠ 0 by positivity)]
      exact hHd.mono (hsub.trans (closedBall_subset_ball (by linarith)))))
    (fun w hw => hBC w (hsub (sphere_subset_closedBall hw)))
  have hzS : z ∉ S := fun h => hfz ((hmemS z).mp h).2
  have hQz : Q z ≠ 0 := by
    simp only [hQ]
    exact Finset.prod_ne_zero_iff.mpr fun u hu =>
      pow_ne_zero _ (sub_ne_zero.mpr (fun h => hzS (by rw [h]; exact hu)))
  have hderH : deriv H z = logDeriv G z := by
    rw [(hH z hzB).deriv, logDeriv_apply]
  have hlogf : logDeriv f z = logDeriv Q z + logDeriv G z := by
    have hev : f =ᶠ[𝓝 z] Q * G := by
      filter_upwards [isOpen_ball.mem_nhds hzb] with w hw
      rw [Pi.mul_apply, hfQG w hw]
    rw [(logDeriv_congr_nhds hev).self_of_nhds, logDeriv_mul z hQz (hGB z hzB)
      ((hQan z (mem_univ _)).differentiableAt) (hGan z hzb).differentiableAt]
  have hlogQ : logDeriv Q z = ∑ u ∈ S, (analyticOrderNatAt f u : ℂ) / (z - u) := by
    simp only [hQ]
    exact logDeriv_poli S m hzS
  rw [hlogf, hlogQ, add_sub_cancel_left, ← hderH]
  calc ‖deriv H z‖ ≤ 2 * A / (R / 16) := hcau
    _ = 32 * (Real.log M + 1) / R := by rw [hA]; field_simp; ring

/-! ## 2. Aplicação a ζ -/

theorem zeta_disco {σ t : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    AnalyticOnNhd ℂ riemannZeta (closedBall ((σ : ℂ) + t * I) (1 / 2)) ∧
      riemannZeta ((σ : ℂ) + t * I) ≠ 0 ∧
      ∃ M : ℝ, 1 ≤ M ∧
        (∀ z ∈ closedBall ((σ : ℂ) + t * I) (1 / 2),
          ‖riemannZeta z‖ ≤ M * ‖riemannZeta ((σ : ℂ) + t * I)‖) ∧
        Real.log M + 1 ≤ 2 * Real.log |t| + Real.log (1 / (σ - 1)) + 7 := by
  set z₀ : ℂ := σ + t * I with hz₀
  have hre0 : z₀.re = σ := by simp [hz₀]
  have him0 : z₀.im = t := by simp [hz₀]
  have coord : ∀ z ∈ closedBall z₀ (1 / 2), |z.re - σ| ≤ 1 / 2 ∧ |z.im - t| ≤ 1 / 2 := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    refine ⟨?_, ?_⟩
    · have := Complex.abs_re_le_norm (z - z₀)
      rw [sub_re, hre0] at this
      linarith
    · have := Complex.abs_im_le_norm (z - z₀)
      rw [sub_im, him0] at this
      linarith
  have hbound : ∀ z ∈ closedBall z₀ (1 / 2), ‖riemannZeta z‖ ≤ 3 * |t| + 14 := by
    intro z hz
    obtain ⟨hr, hi⟩ := coord z hz
    have hi1 : |t| - 1 / 2 ≤ |z.im| := by
      have := abs_sub_abs_le_abs_sub t z.im
      rw [abs_sub_comm] at this
      linarith
    have hi2 : |z.im| ≤ |t| + 1 / 2 := by
      have := abs_sub_abs_le_abs_sub z.im t
      linarith
    have := cota_zeta_faixa (s := z) (by linarith [(abs_le.mp hr).1]) (by linarith [(abs_le.mp hr).2])
      (by linarith)
    linarith
  have hana : AnalyticOnNhd ℂ riemannZeta (closedBall z₀ (1 / 2)) := by
    refine analyticOn_riemannZeta.mono fun z hz => ?_
    rw [Set.mem_compl_singleton_iff]
    rintro rfl
    obtain ⟨_, hi⟩ := coord 1 hz
    rw [one_im, zero_sub, abs_neg] at hi
    linarith
  have hz0 : riemannZeta z₀ ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hre0]; linarith)
  set a := ‖riemannZeta z₀‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr hz0
  have haU : a ≤ 3 * |t| + 12 := by
    have := cota_zeta_faixa (s := z₀) (by rw [hre0]; linarith) (by rw [hre0]; linarith)
      (by rw [him0]; linarith)
    rwa [him0] at this
  set M := (3 * |t| + 14) / a with hM
  have hM1 : 1 ≤ M := by rw [hM, le_div_iff₀ ha0]; linarith
  have hb : ∀ z ∈ closedBall z₀ (1 / 2), ‖riemannZeta z‖ ≤ M * a := by
    intro z hz
    rw [hM, div_mul_cancel₀ _ ha0.ne']
    exact hbound z hz
  have hlogM : Real.log M + 1 ≤ 2 * Real.log |t| + Real.log (1 / (σ - 1)) + 7 := by
    have ht0 : 0 < |t| := by linarith
    have hs : 0 < σ - 1 := by linarith
    have hL : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
    have hl1 : 0 ≤ Real.log (1 / (σ - 1)) := Real.log_nonneg (by rw [le_div_iff₀ hs]; linarith)
    have hlinv : Real.log (1 / (σ - 1)) = -Real.log (σ - 1) := by rw [one_div, Real.log_inv]
    have hl2 := Real.log_two_lt_d9
    have hlog16 : Real.log (16 * |t|) = 4 * Real.log 2 + Real.log |t| := by
      rw [Real.log_mul (by norm_num) ht0.ne', show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      push_cast
      ring
    have hA : Real.log (3 * |t| + 14) ≤ 4 * Real.log 2 + Real.log |t| := by
      rw [← hlog16]
      exact Real.log_le_log (by positivity) (by linarith)
    have hB : Real.log (6 * |t| + 12) ≤ 4 * Real.log 2 + Real.log |t| := by
      rw [← hlog16]
      exact Real.log_le_log (by positivity) (by linarith)
    have hlb' : (σ - 1) ^ 3 / (512 * (6 * |t| + 12)) ≤ a ^ 4 := zeta_lb h1 h2 (by linarith)
    have hpos : 0 < (σ - 1) ^ 3 / (512 * (6 * |t| + 12)) := by positivity
    have hlog := Real.log_le_log hpos hlb'
    rw [Real.log_pow, Real.log_div (by positivity) (by positivity), Real.log_pow,
      Real.log_mul (by norm_num) (by positivity), show (512 : ℝ) = 2 ^ 9 by norm_num, Real.log_pow] at hlog
    push_cast at hlog
    have hMdef : Real.log M = Real.log (3 * |t| + 14) - Real.log a := by
      rw [hM, Real.log_div (by positivity) ha0.ne']
    rw [hMdef]
    linarith
  exact ⟨hana, hz0, M, hM1, hb, hlogM⟩

/-- **Landau fora do centro para ζ** no disco `‖z − (σ + it)‖ ≤ ½`. -/
theorem zeta_local_fora {σ t : ℝ} (h1 : 1 < σ) (h2 : σ ≤ 2) (ht : 2 ≤ |t|) :
    ∃ S : Finset ℂ, (∀ u ∈ S, u ∈ closedBall ((σ : ℂ) + t * I) (1 / 8) ∧ riemannZeta u = 0) ∧
      ((∑ u ∈ S, analyticOrderNatAt riemannZeta u : ℕ) : ℝ) * Real.log 2 ≤
        2 * Real.log |t| + Real.log (1 / (σ - 1)) + 6 ∧
      ∀ z ∈ closedBall ((σ : ℂ) + t * I) (1 / 32), riemannZeta z ≠ 0 →
        ‖logDeriv riemannZeta z - ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (z - u)‖ ≤
          64 * (2 * Real.log |t| + Real.log (1 / (σ - 1)) + 7) := by
  obtain ⟨hana, hz0, M, hM1, hb, hlogM⟩ := zeta_disco h1 h2 ht
  obtain ⟨S, hS1, -, hS3, hS4⟩ := landau_fora (f := riemannZeta) (R := 1 / 2) (M := M) (by norm_num) hM1
    hana hz0 hb
  have h8 : (1 / 2 : ℝ) / 4 = 1 / 8 := by norm_num
  have h32 : (1 / 2 : ℝ) / 16 = 1 / 32 := by norm_num
  rw [h8] at hS1
  rw [h32] at hS4
  refine ⟨S, hS1, by linarith, fun z hz hfz => (hS4 z hz hfz).trans ?_⟩
  have e : 32 * (Real.log M + 1) / (1 / 2) = 64 * (Real.log M + 1) := by ring
  rw [e]
  linarith

/-- `|ζ′/ζ(σ + it)| ≤ −ζ′/ζ(σ)` em `σ > 1`. -/
theorem norm_logDeriv_le {σ : ℝ} (h1 : 1 < σ) (t : ℝ) :
    ‖logDeriv riemannZeta ((σ : ℂ) + t * I)‖ ≤ (-(logDeriv riemannZeta σ)).re := by
  have hs : 1 < ((σ : ℂ) + t * I).re := by simpa using h1
  have hσ : 1 < (σ : ℂ).re := by simpa using h1
  have e1 : logDeriv riemannZeta ((σ : ℂ) + t * I) =
      -LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) ((σ : ℂ) + t * I) := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, logDeriv_apply]
    ring
  have e2 : -(logDeriv riemannZeta σ) =
      LSeries (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) σ := by
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hσ, logDeriv_apply]
    ring
  rw [e1, norm_neg, e2]
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hsumσ := ArithmeticFunction.LSeriesSummable_vonMangoldt hσ
  unfold LSeries
  refine (norm_tsum_le_tsum_norm hsum.norm).trans (le_of_eq ?_)
  rw [Complex.re_tsum hsumσ]
  congr 1
  funext n
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hn), LSeries.term_of_ne_zero hn]
    have hre : ((σ : ℂ) + t * I).re = σ := by simp
    rw [hre, ← ofReal_natCast, ← ofReal_cpow (Nat.cast_nonneg n), ← ofReal_div, ofReal_re,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- **`ζ′/ζ = O(log² t)` na região livre de zeros**: existem `c > 0`, `T₁ ≥ 2` e `C ≥ 0` tais que, para
`|t| ≥ T₁` e `1 − c/log|t| ≤ σ ≤ 2`, `ζ(σ + it) ≠ 0` e `|ζ′/ζ(σ + it)| ≤ C log²|t|`. -/
theorem logDeriv_zeta_le : ∃ c > 0, ∃ T₁ : ℝ, 2 ≤ T₁ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, T₁ ≤ |s.im| →
    1 - c / Real.log |s.im| ≤ s.re → s.re ≤ 2 →
      riemannZeta s ≠ 0 ∧ ‖logDeriv riemannZeta s‖ ≤ C * Real.log |s.im| ^ 2 := by
  obtain ⟨c₀, hc₀, hreg⟩ := ATK.ZeroClasses.RegiaoLivre.regiao_livre
  obtain ⟨Cp, hCp0, hpolo⟩ := ATK.ZeroClasses.RegiaoLivre.polo
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = c₀ / 4 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : ℝ, T₁ = Real.exp (32 * (1 + c)) := ⟨_, rfl⟩
  have hT₁33 : 33 ≤ T₁ := by
    rw [hT₁]
    have := Real.add_one_le_exp (32 * (1 + c))
    nlinarith
  have hT₁2 : 2 ≤ T₁ := by linarith
  refine ⟨c, hc0, T₁, hT₁2, (1 + Cp) + 640 + 36 / (c₀ * Real.log 2), by positivity, fun s hT hlo hhi => ?_⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = s.re := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = s.im := ⟨_, rfl⟩
  have hs : s = (σ : ℂ) + t * I := by rw [hσ, ht]; exact (Complex.re_add_im s).symm
  rw [← ht] at hT hlo ⊢
  rw [← hσ] at hlo hhi
  have ht2 : 2 ≤ |t| := hT₁2.trans hT
  have ht33 : 33 ≤ |t| := hT₁33.trans hT
  have ht0 : 0 < |t| := by linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log |t| := ⟨_, rfl⟩
  rw [← hL] at hlo ⊢
  have hL32 : 32 * (1 + c) ≤ L := by
    rw [hL]
    have := Real.log_le_log (by linarith) hT
    rwa [hT₁, Real.log_exp] at this
  have hL1 : 1 ≤ L := by nlinarith
  have hLpos : 0 < L := by linarith
  have hlogL : Real.log L ≤ L := by
    have := Real.log_le_sub_one_of_pos hLpos
    linarith
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  -- o centro `σ₀ = 1 + 1/L`
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : ℝ, σ₀ = 1 + 1 / L := ⟨_, rfl⟩
  have hσ₀1 : 1 < σ₀ := by rw [hσ₀]; have : 0 < 1 / L := by positivity
                           linarith
  have hσ₀2 : σ₀ ≤ 2 := by
    rw [hσ₀]
    have : 1 / L ≤ 1 := by rw [div_le_one hLpos]; exact hL1
    linarith
  have hCsq : 0 ≤ (1 + Cp) * L ^ 2 := by positivity
  rcases le_or_gt σ₀ σ with hA | hB
  · -- caso `σ ≥ σ₀`: a série de Dirichlet
    have hσ1 : 1 < σ := lt_of_lt_of_le hσ₀1 hA
    refine ⟨?_, ?_⟩
    · rw [hs]
      exact riemannZeta_ne_zero_of_one_le_re (by simp; linarith)
    · rw [hs]
      have h1 := norm_logDeriv_le hσ1 t
      have h2 := hpolo σ hσ1 hhi
      have h3 : 1 / (σ - 1) ≤ L := by
        rw [div_le_iff₀ (by linarith)]
        have : 1 / L ≤ σ - 1 := by rw [hσ₀] at hA; linarith
        rw [div_le_iff₀ hLpos] at this
        linarith
      have hLL : L ≤ L ^ 2 := by nlinarith
      have h1L : 1 ≤ L ^ 2 := by nlinarith
      have h4 : L + Cp ≤ (1 + Cp) * L ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_left h1L hCp0]
      have h5 : 0 ≤ 640 + 36 / (c₀ * Real.log 2) := by positivity
      nlinarith
  · -- caso `σ < σ₀`: Landau fora do centro
    obtain ⟨S, hS1, hS2, hS3⟩ := zeta_local_fora hσ₀1 hσ₀2 ht2
    have hlog1 : Real.log (1 / (σ₀ - 1)) = Real.log L := by
      rw [hσ₀, show 1 + 1 / L - 1 = 1 / L by ring, one_div_one_div]
    rw [hlog1, ← hL] at hS2 hS3
    -- `s` está no disco `1/32`
    have hdist : ‖s - ((σ₀ : ℂ) + t * I)‖ ≤ 1 / 32 := by
      have e : s - ((σ₀ : ℂ) + t * I) = ((σ - σ₀ : ℝ) : ℂ) := by rw [hs]; push_cast; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      have h1 : σ₀ - σ ≤ (1 + c) / L := by
        rw [hσ₀]
        have : 1 - c / L ≤ σ := hlo
        rw [add_div]
        linarith
      have h2 : (1 + c) / L ≤ 1 / 32 := by
        rw [div_le_div_iff₀ hLpos (by norm_num)]
        linarith
      linarith
    -- os zeros de `S` estão à esquerda de `1 − c₀/(2L)`
    have hzeros : ∀ u ∈ S, u.re ≤ 1 - c₀ / (2 * L) := by
      intro u hu
      obtain ⟨hub, hu0⟩ := hS1 u hu
      rw [mem_closedBall, dist_eq_norm] at hub
      have hre : |u.re - σ₀| ≤ 1 / 8 := by
        have h := Complex.abs_re_le_norm (u - ((σ₀ : ℂ) + t * I))
        have e : (u - ((σ₀ : ℂ) + t * I)).re = u.re - σ₀ := by simp
        rw [e] at h
        linarith
      have him : |u.im - t| ≤ 1 / 8 := by
        have h := Complex.abs_im_le_norm (u - ((σ₀ : ℂ) + t * I))
        have e : (u - ((σ₀ : ℂ) + t * I)).im = u.im - t := by simp
        rw [e] at h
        linarith
      have hure : 0 < u.re := by
        have := (abs_le.mp hre).1
        linarith
      have hu1 : u.re < 1 := re_lt_um hu0
      have hui1 : |t| - 1 / 8 ≤ |u.im| := by
        have h := abs_sub_abs_le_abs_sub t u.im
        rw [abs_sub_comm] at h
        linarith
      have hui2 : |u.im| ≤ |t| + 1 / 8 := by
        have h := abs_sub_abs_le_abs_sub u.im t
        linarith
      have hu2 : 2 ≤ |u.im| := by linarith
      have hZ : u ∈ ATK.ZetaSimetria.Z := ⟨hu0, hure, hu1⟩
      have hb := hreg u hZ hu2
      have hlogu : Real.log |u.im| ≤ 2 * L := by
        rw [hL, ← Real.log_rpow ht0]
        refine Real.log_le_log (by linarith) ?_
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        nlinarith
      have hlogu0 : 0 < Real.log |u.im| := Real.log_pos (by linarith)
      have : c₀ / (2 * L) ≤ c₀ / Real.log |u.im| :=
        div_le_div_of_nonneg_left hc₀.le hlogu0 hlogu
      linarith
    have hz : riemannZeta s ≠ 0 := by
      intro h0
      have hsre : 0 < s.re := by
        rw [← hσ]
        have : c / L < 1 := by
          rw [div_lt_one hLpos]; linarith
        linarith
      have hs1 : s.re < 1 := re_lt_um h0
      have hZ : s ∈ ATK.ZetaSimetria.Z := ⟨h0, hsre, hs1⟩
      have hb := hreg s hZ (by rw [← ht]; exact ht2)
      rw [← ht, ← hL, ← hσ] at hb
      have : c / L < c₀ / L := by
        rw [hc]; exact div_lt_div_of_pos_right (by linarith) hLpos
      linarith
    refine ⟨hz, ?_⟩
    have hmem : s ∈ closedBall ((σ₀ : ℂ) + t * I) (1 / 32) := by
      rw [mem_closedBall, dist_eq_norm]; exact hdist
    have hloc := hS3 s hmem hz
    -- a soma sobre os zeros
    have hterm : ∀ u ∈ S, ‖(analyticOrderNatAt riemannZeta u : ℂ) / (s - u)‖ ≤
        (analyticOrderNatAt riemannZeta u : ℝ) * (4 * L / c₀) := by
      intro u hu
      have hu := hzeros u hu
      have hgap : c₀ / (4 * L) ≤ (s - u).re := by
        rw [sub_re, ← hσ]
        have h1 : 1 - c / L ≤ σ := hlo
        have h2 : c / L = c₀ / (4 * L) := by rw [hc]; field_simp
        have h3 : c₀ / (2 * L) = 2 * (c₀ / (4 * L)) := by field_simp; ring
        linarith
      have hgap0 : 0 < c₀ / (4 * L) := by positivity
      have hnorm : c₀ / (4 * L) ≤ ‖s - u‖ := hgap.trans (Complex.re_le_norm _)
      rw [norm_div, Complex.norm_natCast, div_le_iff₀ (lt_of_lt_of_le hgap0 hnorm)]
      have hm0 : (0 : ℝ) ≤ analyticOrderNatAt riemannZeta u := Nat.cast_nonneg _
      calc (analyticOrderNatAt riemannZeta u : ℝ)
          = (analyticOrderNatAt riemannZeta u : ℝ) * (4 * L / c₀) * (c₀ / (4 * L)) := by
            field_simp
        _ ≤ (analyticOrderNatAt riemannZeta u : ℝ) * (4 * L / c₀) * ‖s - u‖ := by gcongr
    have hsum : ‖∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (s - u)‖ ≤
        ((∑ u ∈ S, analyticOrderNatAt riemannZeta u : ℕ) : ℝ) * (4 * L / c₀) := by
      refine (norm_sum_le _ _).trans ?_
      rw [Nat.cast_sum, Finset.sum_mul]
      exact Finset.sum_le_sum hterm
    have hcount : ((∑ u ∈ S, analyticOrderNatAt riemannZeta u : ℕ) : ℝ) ≤ 9 * L / Real.log 2 := by
      rw [le_div_iff₀ hl2]
      linarith
    have hcount0 : (0 : ℝ) ≤ ((∑ u ∈ S, analyticOrderNatAt riemannZeta u : ℕ) : ℝ) := Nat.cast_nonneg _
    have hsum2 : ‖∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (s - u)‖ ≤
        36 / (c₀ * Real.log 2) * L ^ 2 := by
      refine hsum.trans ?_
      calc ((∑ u ∈ S, analyticOrderNatAt riemannZeta u : ℕ) : ℝ) * (4 * L / c₀)
          ≤ 9 * L / Real.log 2 * (4 * L / c₀) := by gcongr
        _ = 36 / (c₀ * Real.log 2) * L ^ 2 := by field_simp; ring
    have htri : ‖logDeriv riemannZeta s‖ ≤
        ‖logDeriv riemannZeta s - ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (s - u)‖ +
          ‖∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (s - u)‖ := by
      have h := norm_add_le (logDeriv riemannZeta s - ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (s - u))
        (∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (s - u))
      rwa [sub_add_cancel] at h
    have hLL : L ≤ L ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hLpos.le hL1
    have h1L : 1 ≤ L ^ 2 := one_le_pow₀ hL1
    have h640 : 64 * (2 * L + Real.log L + 7) ≤ 640 * L ^ 2 := by linarith
    have hCp : 0 ≤ (1 + Cp) * L ^ 2 := hCsq
    have e : ((1 + Cp) + 640 + 36 / (c₀ * Real.log 2)) * L ^ 2 =
        (1 + Cp) * L ^ 2 + 640 * L ^ 2 + 36 / (c₀ * Real.log 2) * L ^ 2 := by ring
    calc ‖logDeriv riemannZeta s‖
        ≤ ‖logDeriv riemannZeta s - ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (s - u)‖ +
          ‖∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) / (s - u)‖ := htri
      _ ≤ 64 * (2 * L + Real.log L + 7) + 36 / (c₀ * Real.log 2) * L ^ 2 := add_le_add hloc hsum2
      _ ≤ 640 * L ^ 2 + 36 / (c₀ * Real.log 2) * L ^ 2 := by gcongr
      _ ≤ ((1 + Cp) + 640 + 36 / (c₀ * Real.log 2)) * L ^ 2 := by rw [e]; linarith

end ATK.ZeroClasses.LogDerivZeta

#print axioms ATK.ZeroClasses.LogDerivZeta.landau_fora
#print axioms ATK.ZeroClasses.LogDerivZeta.zeta_disco
#print axioms ATK.ZeroClasses.LogDerivZeta.zeta_local_fora
#print axioms ATK.ZeroClasses.LogDerivZeta.norm_logDeriv_le
#print axioms ATK.ZeroClasses.LogDerivZeta.logDeriv_zeta_le
