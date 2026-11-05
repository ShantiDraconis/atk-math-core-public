import ATK.ZeroClasses.Expoente

/-!
# O lema de Landau: a derivada logarítmica perto do centro de um disco (rodada 36)

**Lema (Landau; Titchmarsh §3.9; Montgomery–Vaughan, Lema 6.3).** Se `f` é analítica em `‖z − z₀‖ ≤ R`,
`f(z₀) ≠ 0` e `‖f‖ ≤ M‖f(z₀)‖` no disco (`M ≥ 1`), então

  `‖f′/f(z₀) − Σ_{ρ ∈ S} m_ρ/(z₀ − ρ)‖ ≤ 16 (log M + 1)/R`,

onde `S` são os zeros de `f` em `‖z − z₀‖ ≤ R/4`, com multiplicidade `m_ρ`. A Mathlib não tem o lema; aqui ele sai
de quatro ferramentas que ela tem:

1. **o quociente local** (`quociente_local`): se `ord Q ≤ ord f` num aberto, `f = Q · G` com `G` analítica, e
   `G ≠ 0` onde as ordens coincidem; `ordem_poli`: a ordem de `Q = ∏ (z − u)^{m_u}`;
2. **módulo máximo** para `G = f/Q` em `‖z − z₀‖ ≤ R/2` (`Complex.norm_le_of_forall_mem_frontier_norm_le`):
   `|Q| ≥ (R/4)^n` no círculo e `|Q(z₀)| ≤ (R/4)^n`, logo `|G| ≤ M|G(z₀)|`;
3. **o logaritmo no disco** (`DifferentiableOn.isExactOn_ball`): `G = G(z₀) e^h` com `h(z₀) = 0`,
   `Re h ≤ log M`;
4. **Borel–Carathéodory e Cauchy**: `|h| ≤ 2(log M + 1)` em `‖z − z₀‖ = R/8`, logo `|h′(z₀)| ≤ 16(log M + 1)/R`,
   e `h′ = f′/f − Σ m_ρ/(z − ρ)`.

Classificação (rodada 36): **ferramenta** — o ingrediente local da região livre de zeros de de la Vallée Poussin
(rodada 37). RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.Landau

/-! ## 1. O quociente local -/

/-- **O quociente local**: se `ord Q ≤ ord f` num aberto `U`, então `f = Q · G` com `G` analítica em `U`, e `G` não
se anula onde as ordens coincidem. -/
theorem quociente_local {f Q : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hQ : AnalyticOnNhd ℂ Q U) (hle : ∀ z ∈ U, analyticOrderAt Q z ≤ analyticOrderAt f z)
    (htop : ∀ z ∈ U, analyticOrderAt Q z ≠ ⊤) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧ (∀ z ∈ U, f z = Q z * G z) ∧
      (∀ z ∈ U, analyticOrderAt f z = analyticOrderAt Q z → G z ≠ 0) := by
  classical
  have ex : ∀ z, ∃ g₁ g₂ : ℂ → ℂ, ∃ n : ℕ, z ∈ U → (AnalyticAt ℂ g₁ z ∧ AnalyticAt ℂ g₂ z ∧ g₂ z ≠ 0 ∧
      (∀ᶠ w in 𝓝 z, f w = (w - z) ^ n • g₁ w) ∧ (∀ᶠ w in 𝓝 z, Q w = (w - z) ^ n • g₂ w) ∧
      (analyticOrderAt f z = analyticOrderAt Q z → g₁ z ≠ 0)) := by
    intro z
    by_cases hz : z ∈ U
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (htop z hz)
      obtain ⟨g₂, hg₂a, hg₂0, hg₂e⟩ := ((hQ z hz).analyticOrderAt_eq_natCast).mp hn.symm
      have hfn : (n : ℕ∞) ≤ analyticOrderAt f z := hn ▸ hle z hz
      obtain ⟨g₁, hg₁a, hg₁e⟩ := (natCast_le_analyticOrderAt (hf z hz)).mp hfn
      refine ⟨g₁, g₂, n, fun _ => ⟨hg₁a, hg₂a, hg₂0, hg₁e, hg₂e, fun heq => ?_⟩⟩
      intro h0
      -- ord f = n + ord g₁ ≥ n + 1
      have hmon : AnalyticAt ℂ (fun w : ℂ => (w - z) ^ n) z := by fun_prop
      have hcongr : f =ᶠ[𝓝 z] (fun w : ℂ => (w - z) ^ n) * g₁ := by
        filter_upwards [hg₁e] with w hw
        rw [hw, smul_eq_mul, Pi.mul_apply]
      have hord : analyticOrderAt f z = n + analyticOrderAt g₁ z := by
        rw [analyticOrderAt_congr hcongr, analyticOrderAt_mul hmon hg₁a]
        congr 1
        exact analyticOrderAt_centeredMonomial
      have hg1 : analyticOrderAt g₁ z ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨hg₁a, h0⟩
      rw [heq, ← hn] at hord
      have htop' : analyticOrderAt g₁ z ≠ ⊤ := by
        intro ht
        rw [ht] at hord
        simp at hord
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp htop'
      rw [← hk] at hord hg1
      have : (n : ℕ∞) = ((n + k : ℕ) : ℕ∞) := by rw [hord]; push_cast; rfl
      have hk0 : k = 0 := by
        have := ENat.natCast_inj.mp this
        omega
      exact hg1 (by rw [hk0]; rfl)
    · exact ⟨0, 0, 0, fun h => absurd h hz⟩
  choose g₁ g₂ n hspec using ex
  have hval : ∀ w ∈ U, Q w ≠ 0 → g₁ w w / g₂ w w = f w / Q w := by
    intro w hw hQw
    obtain ⟨_, _, _, e1, e2, _⟩ := hspec w hw
    have e1 := e1.self_of_nhds
    have e2 := e2.self_of_nhds
    have hn0 : n w = 0 := by
      by_contra h
      apply hQw
      rw [e2, sub_self, zero_pow h, zero_smul]
    rw [hn0, pow_zero, one_smul] at e1 e2
    rw [e1, e2]
  refine ⟨fun z => g₁ z z / g₂ z z, ?_, ?_, ?_⟩
  · intro z₀ hz₀
    obtain ⟨hg₁a, hg₂a, hg₂0, he₁, he₂, _⟩ := hspec z₀ hz₀
    have hne : ∀ᶠ w in 𝓝[≠] z₀, Q w ≠ 0 :=
      ((hQ z₀ hz₀).eventually_eq_zero_or_eventually_ne_zero).resolve_left
        (fun h => htop z₀ hz₀ (analyticOrderAt_eq_top.mpr h))
    have hg2ne : ∀ᶠ w in 𝓝 z₀, g₂ z₀ w ≠ 0 := hg₂a.continuousAt.eventually_ne hg₂0
    have hUn : ∀ᶠ w in 𝓝 z₀, w ∈ U := hU.mem_nhds hz₀
    have hF : (fun w => g₁ z₀ w / g₂ z₀ w) =ᶠ[𝓝 z₀] (fun z => g₁ z z / g₂ z z) := by
      rw [eventually_nhdsWithin_iff] at hne
      filter_upwards [hne, he₁, he₂, hg2ne, hUn] with w hw1 hw2 hw3 hw4 hw5
      by_cases hw : w = z₀
      · subst hw
        rfl
      · rw [hval w hw5 (hw1 hw), hw2, hw3, smul_eq_mul, smul_eq_mul]
        have hp : (w - z₀) ^ n z₀ ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hw)
        field_simp
    exact (hg₁a.div hg₂a hg₂0).congr hF
  · intro z hz
    by_cases hQz : Q z = 0
    · obtain ⟨_, _, hg₂0, e1, e2, _⟩ := hspec z hz
      have e1 := e1.self_of_nhds
      have e2 := e2.self_of_nhds
      have hn : n z ≠ 0 := by
        intro h
        rw [h, pow_zero, one_smul] at e2
        exact hg₂0 (e2 ▸ hQz)
      rw [e1, sub_self, zero_pow hn, zero_smul, hQz, zero_mul]
    · show f z = Q z * (g₁ z z / g₂ z z)
      rw [hval z hz hQz]
      field_simp
  · intro z hz heq
    obtain ⟨_, _, hg₂0, _, _, h3⟩ := hspec z hz
    exact div_ne_zero (h3 heq) hg₂0

/-! ## 2. O polinômio dos zeros -/

theorem ordem_monomio (u w : ℂ) (k : ℕ) :
    analyticOrderAt (fun z : ℂ => (z - u) ^ k) w = if w = u then (k : ℕ∞) else 0 := by
  split_ifs with h
  · subst h
    exact analyticOrderAt_centeredMonomial
  · exact analyticOrderAt_eq_zero.mpr (Or.inr (pow_ne_zero _ (sub_ne_zero.mpr h)))

theorem ordem_poli (S : Finset ℂ) (m : ℂ → ℕ) (w : ℂ) :
    analyticOrderAt (fun z : ℂ => ∏ u ∈ S, (z - u) ^ m u) w = if w ∈ S then (m w : ℕ∞) else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.notMem_empty, ite_false]
    exact analyticOrderAt_eq_zero.mpr (Or.inr one_ne_zero)
  | insert a s ha ih =>
    have e : (fun z : ℂ => ∏ u ∈ insert a s, (z - u) ^ m u) =
        (fun z : ℂ => (z - a) ^ m a) * (fun z : ℂ => ∏ u ∈ s, (z - u) ^ m u) := by
      funext z
      rw [Finset.prod_insert ha, Pi.mul_apply]
    rw [e, analyticOrderAt_mul (by fun_prop) (by fun_prop), ordem_monomio, ih]
    by_cases hw : w = a
    · subst hw
      simp [ha]
    · by_cases hws : w ∈ s
      · simp [hw, hws]
      · simp [hw, hws]

theorem logDeriv_poli (S : Finset ℂ) (m : ℂ → ℕ) {x : ℂ} (hx : x ∉ S) :
    logDeriv (fun z : ℂ => ∏ u ∈ S, (z - u) ^ m u) x = ∑ u ∈ S, (m u : ℂ) / (x - u) := by
  have e : (fun z : ℂ => ∏ u ∈ S, (z - u) ^ m u) = ∏ u ∈ S, (fun z : ℂ => (z - u) ^ m u) := by
    funext z
    rw [Finset.prod_apply]
  rw [e, logDeriv_prod (fun u hu => pow_ne_zero _ (sub_ne_zero.mpr (fun h => hx (by rw [h]; exact hu))))
    (fun u _ => by fun_prop)]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hxu : x - u ≠ 0 := sub_ne_zero.mpr (fun h => hx (by rw [h]; exact hu))
  rw [logDeriv_fun_pow (f := fun z : ℂ => z - u) (by fun_prop), logDeriv_apply]
  have : deriv (fun z : ℂ => z - u) x = 1 := by
    rw [deriv_sub_const, deriv_id'']
  rw [this]
  field_simp

/-! ## 3. O lema de Landau -/

/-- **O lema de Landau** (forma no centro). -/
theorem landau {f : ℂ → ℂ} {z₀ : ℂ} {R M : ℝ} (hR : 0 < R) (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall z₀ R)) (hf0 : f z₀ ≠ 0)
    (hb : ∀ z ∈ closedBall z₀ R, ‖f z‖ ≤ M * ‖f z₀‖) :
    ∃ S : Finset ℂ, (∀ u ∈ S, u ∈ closedBall z₀ (R / 4) ∧ f u = 0) ∧
      (∀ u ∈ closedBall z₀ (R / 4), f u = 0 → u ∈ S) ∧
      ‖logDeriv f z₀ - ∑ u ∈ S, (analyticOrderNatAt f u : ℂ) / (z₀ - u)‖ ≤
        16 * (Real.log M + 1) / R := by
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
  -- Borel–Carathéodory em ‖w‖ < R/4 para w ↦ H(z₀ + w)
  set A := Real.log M + 1 with hA
  have hA0 : 0 < A := by have := Real.log_nonneg hM; linarith
  have hBC : ∀ z ∈ sphere z₀ (R / 8), ‖H z‖ ≤ 2 * A := by
    intro z hz
    have hzz : z - z₀ ∈ ball (0 : ℂ) (R / 4) := by
      rw [mem_ball_zero_iff]
      rw [mem_sphere_iff_norm] at hz
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
    rw [mem_sphere_iff_norm] at hz
    rw [hz] at hbc
    calc ‖H z‖ ≤ 2 * A * (R / 8) / (R / 4 - R / 8) := hbc
      _ = 2 * A := by field_simp; ring
  -- Cauchy no centro
  have hcau := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < R / 8)
    (DifferentiableOn.diffContOnCl (by
      rw [closure_ball z₀ (show R / 8 ≠ 0 by positivity)]
      exact hHd.mono (closedBall_subset_ball (by linarith)))) hBC
  -- h′ = f′/f − Σ m/(z − ρ)
  have hderH : deriv H z₀ = logDeriv G z₀ := by
    rw [(hH z₀ (mem_ball_self (by linarith))).deriv, logDeriv_apply]
  have hlogf : logDeriv f z₀ = logDeriv Q z₀ + logDeriv G z₀ := by
    have hev : f =ᶠ[𝓝 z₀] Q * G := by
      filter_upwards [isOpen_ball.mem_nhds hz₀b] with z hz
      rw [Pi.mul_apply, hfQG z hz]
    rw [(logDeriv_congr_nhds hev).self_of_nhds, logDeriv_mul z₀ hQz₀ (hGB z₀ (mem_ball_self (by linarith)))
      ((hQan z₀ (mem_univ _)).differentiableAt) (hGan z₀ hz₀b).differentiableAt]
  have hlogQ : logDeriv Q z₀ = ∑ u ∈ S, (analyticOrderNatAt f u : ℂ) / (z₀ - u) := by
    simp only [hQ]
    exact logDeriv_poli S m hz₀S
  rw [hlogf, hlogQ, add_sub_cancel_left, ← hderH]
  calc ‖deriv H z₀‖ ≤ 2 * A / (R / 8) := hcau
    _ = 16 * (Real.log M + 1) / R := by rw [hA]; field_simp; ring

end ATK.ZeroClasses.Landau

#print axioms ATK.ZeroClasses.Landau.quociente_local
#print axioms ATK.ZeroClasses.Landau.ordem_monomio
#print axioms ATK.ZeroClasses.Landau.ordem_poli
#print axioms ATK.ZeroClasses.Landau.logDeriv_poli
#print axioms ATK.ZeroClasses.Landau.landau
