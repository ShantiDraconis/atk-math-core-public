import ATK.ZeroIncognito

/-!
# ATK-RH — Truncamento inexato, limite exato: o modelo `ρ_N = A_N/B_N` com uma regra concreta

O texto encaminhado propõe `ρ_N = x_N + i y_N`, `ε_N = x_N − 1/2`, com `ε_N ≠ 0` para cada `N` e
`ε_N → 0`, e pede "a regra que gera `A_N, B_N`". Aqui a regra é o truncamento de Euler–Maclaurin do
próprio kernel, `ζ_N(s) = Σ_{n≤N} n^{−s} + N^{1−s}/(s−1)` (`zetaN`), e o kernel decide:

* **eixo único** (`eixo_unico`): se o conjunto dos zeros não triviais é simétrico em torno de `Re s = κ`
  e há algum zero, então `κ = 1/2`. Só a invariância é suposta: composta com `s ↦ 1 − s̄`, a reflexão em
  `κ` vira a translação `s ↦ s + (1 − 2κ)`, que tira da faixa qualquer zero se `κ ≠ 1/2`. (O argumento
  "igualar as duas transformações em todo ponto" do texto supõe o que quer provar; este não.)
* **zeros exatos com `ε_N ≠ 0`, `ε_N → 0` sobem ao infinito** (`aproximantes_sobem`): `‖ρ_N‖ → ∞` — não
  há aproximação de um ponto finito por zeros exatos fora da reta; e um só deles já refuta RH
  (`aproximante_refuta`);
* **resíduo do truncamento** (`residuo_trunc`): `|ζ(s) − ζ_N(s)| ≤ |s|·N^{−σ}/σ`, com
  `|I_N(s)| ≤ N^{−σ}/σ` (`norm_cauda_le`);
* **o limite é exato** (`limite_de_zeros_truncados`): se `ζ_N(ρ_N) = 0` e `ρ_N → ρ` (`Re ρ > 0`, `ρ ≠ 1`),
  então `ζ(ρ) = 0` exatamente. Truncamentos inexatos, limite exato.

* **o sistema com três incógnitas** `(k, d, y)` — `ζ(k + d + iy) = 0`, `ζ(k − d + iy) = 0`, `d ≠ 0`, os dois
  na faixa (`SolKDY`): **RH ⟺ o sistema não tem solução** (`rh_iff_sem_solucao`); e uma solução com
  `k ≠ 1/2` exige um terceiro zero distinto na mesma altura (`solucao_eixo_deslocado`).

Nada aqui diz onde está a parte real do limite; isso é RH para aquele zero.
-/

open Complex Filter Topology Metric Set MeasureTheory

namespace ATK.TruncamentoZero

open ATK.ZetaSimetria ATK.ForaDaLinha ATK.EixoDeslocado ATK.BLEulerMaclaurin

/-- Reflexão em torno da reta `Re s = κ`. -/
noncomputable def refl (κ : ℝ) (s : ℂ) : ℂ := 2 * (κ : ℂ) - (starRingEnd ℂ) s

/-- **Eixo de simetria único**: zeros simétricos em torno de `Re s = κ` (e algum zero) ⇒ `κ = 1/2`. -/
theorem eixo_unico {κ : ℝ} (hne : ∃ ρ, ρ ∈ Z) (hsim : ∀ ρ ∈ Z, refl κ ρ ∈ Z) : κ = 1 / 2 := by
  obtain ⟨ρ, hρ⟩ := hne
  have htr : ∀ s ∈ Z, s + ((1 - 2 * κ : ℝ) : ℂ) ∈ Z := by
    intro s hs
    have h := torcao_mem_Z (hsim s hs)
    have e : torcao (refl κ s) = s + ((1 - 2 * κ : ℝ) : ℂ) := by
      unfold torcao refl
      apply Complex.ext <;> simp; ring
    rwa [e] at h
  have hn : ∀ n : ℕ, ρ + (((n : ℝ) * (1 - 2 * κ) : ℝ) : ℂ) ∈ Z := by
    intro n
    induction n with
    | zero => simpa using hρ
    | succ n ih =>
      have := htr _ ih
      convert this using 1
      push_cast; ring
  by_contra hκ
  have hc : 1 - 2 * κ ≠ 0 := by intro h; apply hκ; linarith
  have hpos : 0 < |1 - 2 * κ| := abs_pos.mpr hc
  obtain ⟨n, hnbig⟩ := exists_nat_gt (1 / |1 - 2 * κ|)
  have habs : 1 < (n : ℝ) * |1 - 2 * κ| := by rwa [div_lt_iff₀ hpos] at hnbig
  obtain ⟨-, h0, h1⟩ := hn n
  obtain ⟨-, r0, r1⟩ := hρ
  have hre : (ρ + (((n : ℝ) * (1 - 2 * κ) : ℝ) : ℂ)).re = ρ.re + n * (1 - 2 * κ) := by simp
  rw [hre] at h0 h1
  rcases lt_or_gt_of_ne hc with hneg | hpos'
  · rw [abs_of_neg hneg] at habs; nlinarith
  · rw [abs_of_pos hpos'] at habs; nlinarith

/-- **Zeros exatos que se aproximam de `1/2` sem estar nela sobem ao infinito.** -/
theorem aproximantes_sobem {ρ : ℕ → ℂ} (hz : ∀ N, ρ N ∈ Z) (hfora : ∀ N, (ρ N).re ≠ 1 / 2)
    (hlim : Tendsto (fun N => (ρ N).re) atTop (𝓝 (1 / 2))) :
    Tendsto (fun N => ‖ρ N‖) atTop atTop := by
  classical
  rw [Filter.tendsto_atTop]
  intro B
  have hK := (isCompact_closedBall (0 : ℂ) B).inter_riemannZetaZeros_finite
  set S : Finset ℂ := hK.toFinset.filter (fun z => z.re ≠ 1 / 2) with hSdef
  have hmemS : ∀ N, ‖ρ N‖ ≤ B → ρ N ∈ S := by
    intro N hN
    rw [hSdef, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨by rw [mem_closedBall, dist_zero_right]; exact hN, (hz N).1⟩, hfora N⟩
  by_cases hS : S.Nonempty
  · obtain ⟨z0, hz0S, hmin⟩ := S.exists_min_image (fun z => |z.re - 1 / 2|) hS
    have hm : 0 < |z0.re - 1 / 2| :=
      abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hz0S).2)
    filter_upwards [(Metric.tendsto_nhds.mp hlim) _ hm] with N hN
    rw [Real.dist_eq] at hN
    by_contra hlt
    push Not at hlt
    have := hmin _ (hmemS N hlt.le)
    linarith
  · filter_upwards with N
    by_contra hlt
    push Not at hlt
    exact hS ⟨ρ N, hmemS N hlt.le⟩

/-- Um único zero exato com `ε ≠ 0` já refuta RH. -/
theorem aproximante_refuta {ρ : ℂ} (hz : ρ ∈ Z) (hfora : ρ.re ≠ 1 / 2) : ¬ RiemannHypothesis :=
  fun h => hfora (re_de_rh h hz)

/-- **O truncamento**: `ζ_N(s) = Σ_{n≤N} n^{−s} + N^{1−s}/(s−1)`. -/
noncomputable def zetaN (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-s)) + (N : ℂ) ^ (1 - s) / (s - 1)

theorem zeta_eq_trunc {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    riemannZeta s = zetaN N s - s * cauda N s :=
  zeta_eq hs hs1 N hN

/-- `|I_N(s)| ≤ N^{−σ}/σ`. -/
theorem norm_cauda_le {s : ℂ} (hs : 0 < s.re) {N : ℕ} (hN : 1 ≤ N) :
    ‖cauda N s‖ ≤ (N : ℝ) ^ (-s.re) / s.re := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold cauda
  have hint := (integrableOn_cauda hs hN1).norm
  have hrp : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hN0
  calc ‖∫ t in Ioi (N : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)‖
      ≤ ∫ t in Ioi (N : ℝ), ‖(t : ℂ) ^ (-s - 1) * ((Int.fract t : ℝ) : ℂ)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (N : ℝ), t ^ (-s.re - 1) := by
        refine setIntegral_mono_on hint hrp measurableSet_Ioi fun t ht => ?_
        have ht0 : 0 < t := hN0.trans ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t)]
        have hre : (-s - 1).re = -s.re - 1 := by simp
        rw [hre]
        have := Int.fract_lt_one t
        have hp : 0 ≤ t ^ (-s.re - 1) := Real.rpow_nonneg ht0.le _
        nlinarith
    _ = (N : ℝ) ^ (-s.re) / s.re := by
        rw [integral_Ioi_rpow_of_lt (by linarith) hN0]
        have e : -s.re - 1 + 1 = -s.re := by ring
        rw [e]
        field_simp

/-- **Resíduo do truncamento**: `|ζ(s) − ζ_N(s)| ≤ |s|·N^{−σ}/σ`. -/
theorem residuo_trunc {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - zetaN N s‖ ≤ ‖s‖ * ((N : ℝ) ^ (-s.re) / s.re) := by
  rw [zeta_eq_trunc hs hs1 hN, sub_sub_cancel_left, norm_neg, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cauda_le hs hN) (norm_nonneg _)

/-- **Truncamentos inexatos, limite exato**: o limite de zeros de `ζ_N` é zero exato de `ζ`. -/
theorem limite_de_zeros_truncados {ρN : ℕ → ℂ} {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ ≠ 1)
    (hlim : Tendsto ρN atTop (𝓝 ρ)) (hzero : ∀ᶠ N in atTop, zetaN N (ρN N) = 0) :
    riemannZeta ρ = 0 := by
  have hcont : Tendsto (fun N => riemannZeta (ρN N)) atTop (𝓝 (riemannZeta ρ)) :=
    (differentiableAt_riemannZeta hρ1).continuousAt.tendsto.comp hlim
  set σ0 : ℝ := ρ.re / 2 with hσ0
  have hσ0p : 0 < σ0 := by linarith
  have hre : ∀ᶠ N in atTop, σ0 < (ρN N).re :=
    ((Complex.continuous_re.tendsto ρ).comp hlim).eventually (lt_mem_nhds (by linarith))
  have hnorm : ∀ᶠ N in atTop, ‖ρN N‖ < ‖ρ‖ + 1 :=
    ((continuous_norm.tendsto ρ).comp hlim).eventually (gt_mem_nhds (by linarith))
  have hne1 : ∀ᶠ N in atTop, ρN N ≠ 1 := hlim.eventually_ne hρ1
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ (-σ0)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hσ0p).comp tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun N : ℕ => (‖ρ‖ + 1) * ((N : ℝ) ^ (-σ0) / σ0)) atTop (𝓝 0) := by
    have := (hpow.div_const σ0).const_mul (‖ρ‖ + 1)
    simpa using this
  have h0 : Tendsto (fun N => riemannZeta (ρN N)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hre, hnorm, hne1, hzero, eventually_ge_atTop 1] with N hr hn h1 hz hN
    have hrpos : 0 < (ρN N).re := hσ0p.trans hr
    have hres := residuo_trunc hrpos h1 hN
    rw [hz, sub_zero] at hres
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hp1 : (N : ℝ) ^ (-(ρN N).re) ≤ (N : ℝ) ^ (-σ0) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hp0 : 0 ≤ (N : ℝ) ^ (-(ρN N).re) := Real.rpow_nonneg (by linarith) _
    have hq : (N : ℝ) ^ (-(ρN N).re) / (ρN N).re ≤ (N : ℝ) ^ (-σ0) / σ0 := by
      calc (N : ℝ) ^ (-(ρN N).re) / (ρN N).re ≤ (N : ℝ) ^ (-(ρN N).re) / σ0 :=
            div_le_div_of_nonneg_left hp0 hσ0p hr.le
        _ ≤ (N : ℝ) ^ (-σ0) / σ0 := by gcongr
    calc ‖riemannZeta (ρN N)‖ ≤ ‖ρN N‖ * ((N : ℝ) ^ (-(ρN N).re) / (ρN N).re) := hres
      _ ≤ (‖ρ‖ + 1) * ((N : ℝ) ^ (-σ0) / σ0) :=
          mul_le_mul hn.le hq (by positivity) (by positivity)
  exact tendsto_nhds_unique hcont h0

/-- **O sistema com três incógnitas** `(k, d, y)`: dois zeros na mesma altura `y`, simétricos em torno
de `Re s = k`, com `d ≠ 0` e os dois na faixa. -/
def SolKDY (k d y : ℝ) : Prop :=
  d ≠ 0 ∧ 0 < k - d ∧ k - d < 1 ∧ 0 < k + d ∧ k + d < 1 ∧
    riemannZeta (((k + d : ℝ) : ℂ) + (y : ℂ) * I) = 0 ∧
    riemannZeta (((k - d : ℝ) : ℂ) + (y : ℂ) * I) = 0

/-- **RH ⟺ o sistema `(k, d, y)` não tem solução.** -/
theorem rh_iff_sem_solucao : RiemannHypothesis ↔ ∀ k d y : ℝ, ¬ SolKDY k d y := by
  constructor
  · rintro h k d y ⟨hd, h1, h2, h3, h4, hz1, hz2⟩
    have m1 : (((k + d : ℝ) : ℂ) + (y : ℂ) * I) ∈ Z := ⟨hz1, by simpa using h3, by simpa using h4⟩
    have m2 : (((k - d : ℝ) : ℂ) + (y : ℂ) * I) ∈ Z := ⟨hz2, by simpa using h1, by simpa using h2⟩
    have r1 := re_de_rh h m1
    have r2 := re_de_rh h m2
    simp at r1 r2
    apply hd; linarith
  · intro h
    refine riemann_iff_vazio.mpr ⟨fun ρ => ?_⟩
    obtain ⟨ρ, ⟨hz, h0, h1⟩, hne⟩ := ρ
    apply h (1 / 2) (ρ.re - 1 / 2) ρ.im
    refine ⟨sub_ne_zero.mpr hne, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
    · have e : (((1 / 2 + (ρ.re - 1 / 2) : ℝ)) : ℂ) + (ρ.im : ℂ) * I = ρ := by
        apply Complex.ext <;> simp
      rw [e]; exact hz
    · have e : (((1 / 2 - (ρ.re - 1 / 2) : ℝ)) : ℂ) + (ρ.im : ℂ) * I = torcao ρ := by
        apply Complex.ext <;> simp [torcao] ; ring
      rw [e]; exact (torcao_mem_Z ⟨hz, h0, h1⟩).1

/-- Uma solução com eixo `k ≠ 1/2` exige um **terceiro** zero distinto na mesma altura. -/
theorem solucao_eixo_deslocado {k d y : ℝ} (hs : SolKDY k d y) (hk : k ≠ 1 / 2) :
    ∃ ρ₃ ∈ Z, ρ₃.im = y ∧ ρ₃ ≠ ((k + d : ℝ) : ℂ) + (y : ℂ) * I ∧
      ρ₃ ≠ ((k - d : ℝ) : ℂ) + (y : ℂ) * I := by
  obtain ⟨hd, h1, h2, h3, h4, hz1, hz2⟩ := hs
  have m1 : (((k + d : ℝ) : ℂ) + (y : ℂ) * I) ∈ Z := ⟨hz1, by simpa using h3, by simpa using h4⟩
  have m2 : (((k - d : ℝ) : ℂ) + (y : ℂ) * I) ∈ Z := ⟨hz2, by simpa using h1, by simpa using h2⟩
  have him : (((k + d : ℝ) : ℂ) + (y : ℂ) * I).im = (((k - d : ℝ) : ℂ) + (y : ℂ) * I).im := by simp
  have hne : (((k + d : ℝ) : ℂ) + (y : ℂ) * I) ≠ (((k - d : ℝ) : ℂ) + (y : ℂ) * I) := by
    intro h; have := congrArg Complex.re h; simp at this; apply hd; linarith
  have heps : eps (((k + d : ℝ) : ℂ) + (y : ℂ) * I) (((k - d : ℝ) : ℂ) + (y : ℂ) * I) = k - 1 / 2 := by
    unfold eps; simp
  have he : eps (((k + d : ℝ) : ℂ) + (y : ℂ) * I) (((k - d : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
    rw [heps]; exact sub_ne_zero.mpr hk
  obtain ⟨ρ₃, h3Z, h3im, h31, h32⟩ := tres_zeros m1 m2 him hne he
  exact ⟨ρ₃, h3Z, by rw [h3im]; simp, h31, h32⟩

end ATK.TruncamentoZero

#print axioms ATK.TruncamentoZero.eixo_unico
#print axioms ATK.TruncamentoZero.aproximantes_sobem
#print axioms ATK.TruncamentoZero.aproximante_refuta
#print axioms ATK.TruncamentoZero.zeta_eq_trunc
#print axioms ATK.TruncamentoZero.norm_cauda_le
#print axioms ATK.TruncamentoZero.residuo_trunc
#print axioms ATK.TruncamentoZero.limite_de_zeros_truncados
#print axioms ATK.TruncamentoZero.rh_iff_sem_solucao
#print axioms ATK.TruncamentoZero.solucao_eixo_deslocado
