import ATK.ZeroClasses.HardyMomentos

/-!
# ATK — Hardy (parte 4): o teorema de Hardy (1914)

Rodada 50 do projeto Hardy: **a função zeta de Riemann tem infinitos zeros na reta crítica**
(`ATK.AtaqueRH.Hardy`, alvo R4). O argumento de Hardy (Titchmarsh §10.2) sobre a identidade dos momentos
(rodada 49):

* `existe_Xi_ne_zero`: `Ξ` não se anula identicamente em nenhuma semirreta (princípio da identidade para
  `ξ`, inteira, com `ξ(0) = 1/2`);
* `sinal_constante`: sem trocas de sinal depois de `T`, `Ξ` tem sinal constante em `[T, ∞)`;
* **`sem_sinal_constante`**: isso é impossível. Se `σΞ ≥ 0` em `[T, ∞)` (`σ = ±1`), escolhe-se `t₀ ≥ 2T` com
  `Ξ(t₀) ≠ 0`; para `0 < α < π/4`,
  `σ ∫₀^∞ Fx(t) t^{2n} cosh(αt) dt ≥ t₀^{2n} cδ − T^{2n} A`, com `c, δ, A` independentes de `n` e `α`.
  Quando `α → π/4⁻` o lado esquerdo tende a `σ(−1)^n π 4^{−n} cos(π/8)` (`momento_tendsto`), que é negativo
  para `n` de paridade adequada, enquanto `t₀^{2n} cδ − T^{2n}A ≥ T^{2n}(4^n cδ − A) > 0` para `n` grande;
* **`trocasInfinitas`**: `Ξ` troca de sinal arbitrariamente longe;
* **`hardy`**: `ATK.AtaqueRH.Hardy` — infinitos zeros de `ζ` na reta crítica; `existe_zero_acima`: há zeros
  `ζ(1/2 + it) = 0` com `t` arbitrariamente grande.

Isto **não** é a Hipótese de Riemann: Hardy dá infinitos zeros na reta, não todos.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real

namespace ATK.ZeroClasses.Hardy

open ATK.BaseRiemannXi (Xi riemannXi riemannXi_critical differentiable_riemannXi riemannXi_zero)
open ATK.AtaqueRH (Hardy TrocasInfinitas hardy_of_trocas zerosReta zero_de_troca)

/-- `Ξ` não se anula identicamente em nenhuma semirreta. -/
theorem existe_Xi_ne_zero (M : ℝ) : ∃ t, M ≤ t ∧ Xi t ≠ 0 := by
  by_contra h
  push Not at h
  have hA : AnalyticOnNhd ℂ riemannXi univ := fun z _ => differentiable_riemannXi.analyticAt z
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ℂ, z₀ = 1 / 2 + ((M + 1 : ℝ) : ℂ) * I := ⟨_, rfl⟩
  have hf : Tendsto (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I) (𝓝[≠] (M + 1)) (𝓝[≠] z₀) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I := by fun_prop
      rw [hz₀]
      exact (hc.tendsto (M + 1)).mono_left nhdsWithin_le_nhds
    · refine eventually_nhdsWithin_of_forall fun t ht => ?_
      rw [hz₀]
      intro heq
      apply ht
      have := congrArg Complex.im heq
      simpa using this
  have hev : ∀ᶠ t : ℝ in 𝓝[≠] (M + 1), riemannXi ((1 / 2 : ℂ) + (t : ℂ) * I) = 0 := by
    have : ∀ᶠ t : ℝ in 𝓝 (M + 1), M < t := Ioi_mem_nhds (by linarith)
    filter_upwards [nhdsWithin_le_nhds this] with t ht
    rw [riemannXi_critical, h t ht.le, ofReal_zero]
  have hfreq := hf.frequently (p := fun z => riemannXi z = 0) hev.frequently
  have hz := hA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ z₀) hfreq
    (mem_univ 0)
  simp [riemannXi_zero] at hz

/-- Sem trocas de sinal depois de `T`, `Ξ` tem sinal constante em `[T, ∞)`. -/
theorem sinal_constante {T : ℝ} (h : ∀ a b, T ≤ a → a ≤ b → 0 ≤ Xi a * Xi b) :
    (∀ t, T ≤ t → 0 ≤ Xi t) ∨ (∀ t, T ≤ t → Xi t ≤ 0) := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨a, ha, hXa⟩, ⟨b, hb, hXb⟩⟩ := hc
  rcases le_total a b with hab | hab
  · have := h a b ha hab; nlinarith
  · have := h b a hb hab; nlinarith

/-- **O argumento de Hardy**: `Ξ` não tem sinal constante em nenhuma semirreta `[T, ∞)`. -/
theorem sem_sinal_constante {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {T : ℝ} (hT : 1 ≤ T)
    (hpos : ∀ t, T ≤ t → 0 ≤ σ * Xi t) : False := by
  have hπ := Real.pi_pos
  have hσabs : |σ| = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  obtain ⟨t₀, ht₀, hX₀⟩ := existe_Xi_ne_zero (2 * T)
  have hT0 : 0 < T := by linarith
  have ht₀T : T < t₀ := by linarith
  have hσF : ∀ t, T ≤ t → 0 ≤ σ * Fx t := by
    intro t ht
    unfold Fx
    rw [mul_div_assoc']
    exact div_nonneg (hpos t ht) (by positivity)
  have hF₀ : 0 < σ * Fx t₀ := by
    rcases (hσF t₀ ht₀T.le).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hX₀
      have h0 : σ * Fx t₀ = 0 := h.symm
      unfold Fx at h0
      have hd : (0 : ℝ) < t₀ ^ 2 + 1 / 4 := by positivity
      rcases mul_eq_zero.mp h0 with h1 | h1
      · rcases hσ with h2 | h2 <;> rw [h2] at h1 <;> norm_num at h1
      · rwa [div_eq_zero_iff, or_iff_left hd.ne'] at h1
  -- o intervalo `[t₀, t₀ + δ]` onde `σ Fx ≥ c`
  obtain ⟨c, hc⟩ : ∃ c, c = σ * Fx t₀ / 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; linarith
  have hcont : ContinuousAt (fun t => σ * Fx t) t₀ := (continuous_const.mul continuous_Fx).continuousAt
  obtain ⟨δ', hδ'0, hδ'⟩ :=
    Metric.eventually_nhds_iff.mp (hcont.eventually (lt_mem_nhds (show c < σ * Fx t₀ by linarith)))
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = δ' / 2 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hnear : ∀ t ∈ Icc t₀ (t₀ + δ), c ≤ σ * Fx t := by
    intro t ht
    have hd : dist t t₀ < δ' := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [ht.1])]
      linarith [ht.2]
    exact (hδ' hd).le
  -- a massa em `(0, T]`
  obtain ⟨A, hA⟩ : ∃ A, A = ∫ t in Ioc 0 T, |Fx t| * Real.cosh (π / 4 * t) := ⟨_, rfl⟩
  have key : ∀ n : ℕ, ∀ α : ℝ, 0 < α → α < π / 4 →
      t₀ ^ (2 * n) * (c * δ) - T ^ (2 * n) * A ≤
        σ * ∫ t in Ioi (0 : ℝ), Fx t * t ^ (2 * n) * Real.cosh (α * t) := by
    intro n α hα0 hα
    have hint : IntegrableOn (fun t => Fx t * t ^ (2 * n) * Real.cosh (α * t)) (Ioi 0) := by
      refine (integrableOn_dom (2 * n) hα).mono' ?_ ?_
      · exact ((continuous_Fx.mul (continuous_pow _)).mul
          (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
      · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
        have ht0 : (0 : ℝ) < t := ht
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht0.le _),
          abs_of_pos (Real.cosh_pos _)]
        have hch : Real.cosh (α * t) ≤ Real.exp (α * t) := by
          have := ATK.GammaVertical.cosh_le_exp_abs (α * t)
          rwa [abs_of_nonneg (by positivity)] at this
        gcongr
    have hsplit : ∫ t in Ioi (0 : ℝ), Fx t * t ^ (2 * n) * Real.cosh (α * t) =
        (∫ t in Ioc 0 T, Fx t * t ^ (2 * n) * Real.cosh (α * t)) +
          ∫ t in Ioi T, Fx t * t ^ (2 * n) * Real.cosh (α * t) := by
      rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hT0.le)),
        Ioc_union_Ioi_eq_Ioi hT0.le]
    have hcosh : ∀ t, 0 ≤ t → Real.cosh (α * t) ≤ Real.cosh (π / 4 * t) := by
      intro t ht
      rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      gcongr
    have h1 : |∫ t in Ioc 0 T, Fx t * t ^ (2 * n) * Real.cosh (α * t)| ≤ T ^ (2 * n) * A := by
      rw [hA, ← integral_const_mul]
      refine abs_integral_le_integral_abs.trans (setIntegral_mono_on ?_ ?_ measurableSet_Ioc fun t ht => ?_)
      · exact (hint.mono_set Ioc_subset_Ioi_self).abs
      · exact (continuous_const.mul ((continuous_abs.comp continuous_Fx).mul
          (Real.continuous_cosh.comp (continuous_const.mul continuous_id)))).integrableOn_Ioc
      · obtain ⟨ht0, htT⟩ := ht
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg ht0.le _), abs_of_pos (Real.cosh_pos _)]
        have hp : t ^ (2 * n) ≤ T ^ (2 * n) := pow_le_pow_left₀ ht0.le htT _
        have hc2 := hcosh t ht0.le
        calc |Fx t| * t ^ (2 * n) * Real.cosh (α * t)
            ≤ |Fx t| * T ^ (2 * n) * Real.cosh (π / 4 * t) := by gcongr
          _ = T ^ (2 * n) * (|Fx t| * Real.cosh (π / 4 * t)) := by ring
    have h2 : t₀ ^ (2 * n) * (c * δ) ≤ σ * ∫ t in Ioi T, Fx t * t ^ (2 * n) * Real.cosh (α * t) := by
      rw [← integral_const_mul]
      have hsub : Icc t₀ (t₀ + δ) ⊆ Ioi T := fun t ht => lt_of_lt_of_le ht₀T ht.1
      have hnn : ∀ t ∈ Ioi T, 0 ≤ σ * (Fx t * t ^ (2 * n) * Real.cosh (α * t)) := by
        intro t ht
        have ht' : T < t := ht
        have hs := hσF t ht'.le
        have ht0 : 0 < t := by linarith
        rw [show σ * (Fx t * t ^ (2 * n) * Real.cosh (α * t)) =
          (σ * Fx t) * t ^ (2 * n) * Real.cosh (α * t) by ring]
        have := Real.cosh_pos (α * t)
        positivity
      have hintT : IntegrableOn (fun t => σ * (Fx t * t ^ (2 * n) * Real.cosh (α * t))) (Ioi T) :=
        (hint.mono_set (Ioi_subset_Ioi hT0.le)).const_mul σ
      calc t₀ ^ (2 * n) * (c * δ) = ∫ _ in Icc t₀ (t₀ + δ), t₀ ^ (2 * n) * c := by
            rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
            ring
        _ ≤ ∫ t in Icc t₀ (t₀ + δ), σ * (Fx t * t ^ (2 * n) * Real.cosh (α * t)) := by
            refine setIntegral_mono_on continuous_const.integrableOn_Icc (hintT.mono_set hsub)
              measurableSet_Icc fun t ht => ?_
            have ht0 : 0 ≤ t₀ := by linarith
            have hc1 := hnear t ht
            have hp : t₀ ^ (2 * n) ≤ t ^ (2 * n) := pow_le_pow_left₀ ht0 ht.1 _
            have hch : 1 ≤ Real.cosh (α * t) := Real.one_le_cosh _
            rw [show σ * (Fx t * t ^ (2 * n) * Real.cosh (α * t)) =
              (σ * Fx t) * t ^ (2 * n) * Real.cosh (α * t) by ring]
            have hσt : 0 ≤ σ * Fx t := by linarith
            have htp : 0 ≤ t ^ (2 * n) := pow_nonneg (by linarith [ht.1]) _
            calc t₀ ^ (2 * n) * c = c * t₀ ^ (2 * n) * 1 := by ring
              _ ≤ (σ * Fx t) * t ^ (2 * n) * Real.cosh (α * t) :=
                mul_le_mul (mul_le_mul hc1 hp (pow_nonneg ht0 _) hσt) hch zero_le_one (mul_nonneg hσt htp)
        _ ≤ ∫ t in Ioi T, σ * (Fx t * t ^ (2 * n) * Real.cosh (α * t)) :=
            setIntegral_mono_set hintT
              ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => hnn t ht))
              hsub.eventuallyLE
    rw [hsplit, mul_add]
    have h3 : -(T ^ (2 * n) * A) ≤ σ * ∫ t in Ioc 0 T, Fx t * t ^ (2 * n) * Real.cosh (α * t) := by
      have := neg_abs_le (σ * ∫ t in Ioc 0 T, Fx t * t ^ (2 * n) * Real.cosh (α * t))
      rw [abs_mul, hσabs, one_mul] at this
      linarith
    linarith
  -- o limite `α → π/4⁻`
  have hlim : ∀ n : ℕ, t₀ ^ (2 * n) * (c * δ) - T ^ (2 * n) * A ≤
      σ * ((-1) ^ n * π * (1 / 4) ^ n * Real.cos (π / 8)) := by
    intro n
    refine ge_of_tendsto ((momento_tendsto n).const_mul σ) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 8 by positivity)] with r hr
    obtain ⟨hr0, hr1⟩ := hr
    exact key n (π / 4 - 2 * r) (by linarith) (by linarith)
  -- a escolha de `n`
  have hcδ : 0 < c * δ := mul_pos hc0 hδ0
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (A / (c * δ)) (by norm_num : (1 : ℝ) < 4)
  have hcos : 0 < Real.cos (π / 8) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hgood : ∀ n : ℕ, N ≤ n → σ * (-1) ^ n = -1 → False := by
    intro n hn hs
    have h := hlim n
    have e : σ * ((-1) ^ n * π * (1 / 4) ^ n * Real.cos (π / 8)) =
        -(π * (1 / 4) ^ n * Real.cos (π / 8)) := by
      rw [show σ * ((-1) ^ n * π * (1 / 4) ^ n * Real.cos (π / 8)) =
        (σ * (-1) ^ n) * (π * (1 / 4) ^ n * Real.cos (π / 8)) by ring, hs]
      ring
    rw [e] at h
    have hneg : 0 < π * (1 / 4) ^ n * Real.cos (π / 8) := by positivity
    have h4 : (4 : ℝ) ^ n * T ^ (2 * n) ≤ t₀ ^ (2 * n) := by
      rw [pow_mul, pow_mul, ← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith
    have hNn : A / (c * δ) < 4 ^ n := lt_of_lt_of_le hN (pow_le_pow_right₀ (by norm_num) hn)
    have hA' : A < 4 ^ n * (c * δ) := by rwa [div_lt_iff₀ hcδ] at hNn
    have hTn : 0 < T ^ (2 * n) := by positivity
    have hlt : T ^ (2 * n) * A < t₀ ^ (2 * n) * (c * δ) := by
      calc T ^ (2 * n) * A < T ^ (2 * n) * (4 ^ n * (c * δ)) := by gcongr
        _ = 4 ^ n * T ^ (2 * n) * (c * δ) := by ring
        _ ≤ t₀ ^ (2 * n) * (c * δ) := by gcongr
    linarith
  rcases neg_one_pow_eq_or ℝ N with hN1 | hN1
  · rcases hσ with h | h
    · exact hgood (N + 1) (Nat.le_succ N) (by rw [h, pow_succ, hN1]; norm_num)
    · exact hgood N le_rfl (by rw [h, hN1]; norm_num)
  · rcases hσ with h | h
    · exact hgood N le_rfl (by rw [h, hN1]; norm_num)
    · exact hgood (N + 1) (Nat.le_succ N) (by rw [h, pow_succ, hN1]; norm_num)

/-- **`Ξ` troca de sinal arbitrariamente longe.** -/
theorem trocasInfinitas : TrocasInfinitas := by
  by_contra hne
  unfold TrocasInfinitas at hne
  push Not at hne
  obtain ⟨T, hT⟩ := hne
  have hT' : ∀ a b, max T 1 ≤ a → a ≤ b → 0 ≤ Xi a * Xi b :=
    fun a b ha hab => hT a b (le_trans (le_max_left _ _) ha) hab
  rcases sinal_constante hT' with h | h
  · exact sem_sinal_constante (σ := 1) (Or.inl rfl) (le_max_right T 1) fun t ht => by
      rw [one_mul]; exact h t ht
  · exact sem_sinal_constante (σ := -1) (Or.inr rfl) (le_max_right T 1) fun t ht => by
      have := h t ht; linarith

/-- **Teorema de Hardy (1914)**: `ζ` tem infinitos zeros na reta crítica `Re s = 1/2`. -/
theorem hardy : Hardy := hardy_of_trocas trocasInfinitas

/-- Há zeros `ζ(1/2 + it) = 0` com `t` arbitrariamente grande. -/
theorem existe_zero_acima (T : ℝ) : ∃ t, T < t ∧ riemannZeta (1 / 2 + t * I) = 0 := by
  obtain ⟨a, b, ha, hab, hs⟩ := trocasInfinitas (max T 0)
  obtain ⟨t, ht, hat, -⟩ := zero_de_troca (le_trans (le_max_right T 0) ha) hab hs
  exact ⟨t, lt_of_le_of_lt (le_trans (le_max_left T 0) ha) hat, ht.2⟩

end ATK.ZeroClasses.Hardy

#print axioms ATK.ZeroClasses.Hardy.existe_Xi_ne_zero
#print axioms ATK.ZeroClasses.Hardy.sinal_constante
#print axioms ATK.ZeroClasses.Hardy.sem_sinal_constante
#print axioms ATK.ZeroClasses.Hardy.trocasInfinitas
#print axioms ATK.ZeroClasses.Hardy.hardy
#print axioms ATK.ZeroClasses.Hardy.existe_zero_acima
