import ATK.ForaDaLinha
import ATK.DInfinito

/-!
# ATK-RH — A barreira de um zero fora da linha: `D_N ≥ (2σ−1)|1−ρ|²/|ρ|⁴`

Reforça `ATK.ForaDaLinha.piso_DN` (`D_N ≥ m(ρ)²`). Se `ζ(ρ) = 0` com `1/2 < σ = Re ρ < 1`, para todo
resíduo `res = χ − Σ c_k ρ_{k+1}` com constante de cauda `S = Σ c_k/(k+1)`:

* `mellin_cauda`: `∫_1^∞ t^{ρ−1} res = −S/(1−ρ)` (em `t > 1`, `res = −S/t`);
* `mellin_cabeca`: logo `∫_0^1 t^{ρ−1} res = 1/ρ + S/(1−ρ)` (`mellin_res`: o total é `1/ρ`);
* `cabeca_cs`: `(2σ−1)·|1/ρ + S/(1−ρ)|² ≤ ∫_0^1 res²` (Cauchy–Schwarz via AM-GM com λ ótimo);
* `residual_split`: `‖res‖² = ∫_0^1 res² + S²`;
* `algebra_barreira`: `S² + (2σ−1)|1/ρ + S/(1−ρ)|² − B(ρ) = ((a²S − t(a−σ))² + t²γ²)/(a³b) ≥ 0`,
  com `t = 2σ−1`, `a = |ρ|²`, `b = |1−ρ|²` (e `a = b + t`);
* **`barreira_le_DN`**, **`barreira_le_dInf`**: `B(ρ) = (2σ−1)|1−ρ|²/|ρ|⁴ ≤ D_N` para todo `N`, e `≤ D_∞`;
* `m_sq_le_barreira`: `m(ρ)² ≤ B(ρ)` — a barreira nova nunca é pior que a do kernel
  (fica até ~5,7 vezes maior em `σ ≈ 0,63`, e não se anula quando `σ → 1`);
* **`exclusao`**: qualquer cota `D_N < B(ρ)` exclui um zero em `ρ` — uma região livre de zeros
  obtida de um valor de `D_N`; `regiao_livre_D256` é o caso da cota `D_256 ≤ 0,00823372`.

Tudo incondicional (só os três axiomas padrão). Nada aqui produz um zero fora da linha nem prova RH.
-/

open Complex Set Filter Topology MeasureTheory

namespace ATK.BarreiraZero

open ATK.Conditional.Riemann ATK.RiemannConcrete ATK.BaezDuarteBridge

/-- A barreira `B(ρ) = (2σ−1)|1−ρ|²/|ρ|⁴`. -/
noncomputable def barreira (ρ : ℂ) : ℝ := (2 * ρ.re - 1) * normSq (1 - ρ) / normSq ρ ^ 2

/-- `|ρ|² = |1−ρ|² + (2σ−1)`. -/
theorem normSq_eq_add (ρ : ℂ) : normSq ρ = normSq (1 - ρ) + (2 * ρ.re - 1) := by
  simp only [normSq_apply, sub_re, one_re, sub_im, one_im]; ring

/-! ### Mellin da cauda e da cabeça -/

theorem mellin_cauda {N : ℕ} (c : Fin N → ℝ) {s : ℂ} (hs1 : s.re < 1) :
    ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • ((res c t : ℝ) : ℂ) = -(tailS c : ℂ) / (1 - s) := by
  have hpt : ∀ t ∈ Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • ((res c t : ℝ) : ℂ) =
      -(tailS c : ℂ) * (t : ℂ) ^ (s - 2) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have e : (t : ℂ) ^ (s - 2) = (t : ℂ) ^ (s - 1) / (t : ℂ) := by
      rw [show s - 2 = (s - 1) - 1 by ring, cpow_sub _ _ htc, cpow_one]
    rw [res_of_gt_one c ht, smul_eq_mul, e]
    push_cast
    field_simp
  have hre : (s - 2).re < -1 := by rw [sub_re]; norm_num; linarith
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_Ioi_cpow_of_lt hre zero_lt_one]
  have h1 : (1 : ℂ) - s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : s - 2 + 1 = -(1 - s) := by ring
  rw [h2, ofReal_one, one_cpow]
  field_simp

theorem mellin_cabeca {N : ℕ} (c : Fin N → ℝ) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) :
    ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • ((res c t : ℝ) : ℂ) = 1 / s + (tailS c : ℂ) / (1 - s) := by
  obtain ⟨hconv, hval⟩ := mellin_res c hs0 hs1 hz
  have hu := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hconv.mono_set Ioc_subset_Ioi_self) (hconv.mono_set (Ioi_subset_Ioi zero_le_one))
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one] at hu
  have hm : mellin (fun t => ((res c t : ℝ) : ℂ)) s =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • ((res c t : ℝ) : ℂ) := rfl
  rw [← hm, hval, mellin_cauda c hs1] at hu
  rw [neg_div] at hu
  linear_combination -hu

/-! ### Cauchy–Schwarz na cabeça -/

/-- Em `(0,1]`: `∫ t^{σ−1}|res| ≤ (λ·∫_0^1 res² + 1/(λ(2σ−1)))/2`. -/
theorem integral_head_le' {N : ℕ} (c : Fin N → ℝ) {σ : ℝ} (hσ : 1 / 2 < σ) {l : ℝ} (hl : 0 < l)
    (hint : IntegrableOn (fun t => t ^ (σ - 1) * |res c t|) (Ioc 0 1)) :
    ∫ t in Ioc (0 : ℝ) 1, t ^ (σ - 1) * |res c t| ≤
      (l * (∫ t in Ioc (0 : ℝ) 1, res c t ^ 2) + 1 / (l * (2 * σ - 1))) / 2 := by
  have hr2 : IntegrableOn (fun t => res c t ^ 2) (Ioc 0 1) :=
    (integrable_res_sq c).mono_set Ioc_subset_Ioi_self
  have hpow : IntegrableOn (fun t : ℝ => t ^ (2 * σ - 2)) (Ioc 0 1) :=
    integrableOn_rpow_Ioc (by linarith)
  have hg : IntegrableOn (fun t => (l * res c t ^ 2 + t ^ (2 * σ - 2) / l) / 2) (Ioc 0 1) :=
    Integrable.div_const (Integrable.add (Integrable.const_mul hr2 l) (Integrable.div_const hpow l)) 2
  have hle : ∫ t in Ioc (0 : ℝ) 1, t ^ (σ - 1) * |res c t| ≤
      ∫ t in Ioc (0 : ℝ) 1, (l * res c t ^ 2 + t ^ (2 * σ - 2) / l) / 2 := by
    refine setIntegral_mono_on hint hg measurableSet_Ioc fun t ht => ?_
    have hsq : t ^ (2 * σ - 2) = (t ^ (σ - 1)) ^ 2 := by
      rw [show 2 * σ - 2 = (σ - 1) * 2 by ring, Real.rpow_mul ht.1.le, Real.rpow_two]
    rw [hsq, ← sq_abs (res c t)]
    exact amgm hl
  have hval : ∫ t in Ioc (0 : ℝ) 1, (l * res c t ^ 2 + t ^ (2 * σ - 2) / l) / 2 =
      (l * ∫ t in Ioc (0 : ℝ) 1, res c t ^ 2) / 2 + (1 / (2 * σ - 1)) / l / 2 := by
    rw [integral_div, integral_add (Integrable.const_mul hr2 l) (Integrable.div_const hpow l),
      integral_const_mul, integral_div, integral_rpow_Ioc (by linarith)]
    ring_nf
  have h2σ : 0 < 2 * σ - 1 := by linarith
  rw [hval] at hle
  calc _ ≤ _ := hle
    _ = _ := by field_simp

/-- De `w ≤ (λJ + 1/(λt))/2` para todo `λ > 0` sai `t·w² ≤ J`. -/
theorem cs_de_amgm {w J t : ℝ} (ht : 0 < t) (hw0 : 0 ≤ w) (hJ : 0 ≤ J)
    (h : ∀ l : ℝ, 0 < l → w ≤ (l * J + 1 / (l * t)) / 2) : t * w ^ 2 ≤ J := by
  rcases eq_or_lt_of_le hw0 with h0 | hpos
  · rw [← h0]; simpa using hJ
  · have hl : 0 < 1 / (t * w) := by positivity
    have hh := h (1 / (t * w)) hl
    have e1 : 1 / (1 / (t * w) * t) = w := by field_simp
    have e2 : 1 / (t * w) * J = J / (t * w) := by ring
    rw [e1, e2] at hh
    have hw : w ≤ J / (t * w) := by linarith
    rw [le_div_iff₀ (by positivity)] at hw
    nlinarith

theorem integral_head_nonneg {N : ℕ} (c : Fin N → ℝ) : 0 ≤ ∫ t in Ioc (0 : ℝ) 1, res c t ^ 2 :=
  setIntegral_nonneg measurableSet_Ioc fun _ _ => sq_nonneg _

/-- **Cauchy–Schwarz na cabeça**: `(2σ−1)·|1/ρ + S/(1−ρ)|² ≤ ∫_0^1 res²`. -/
theorem cabeca_cs {N : ℕ} (c : Fin N → ℝ) {s : ℂ} (hs0 : 1 / 2 < s.re) (hs1 : s.re < 1)
    (hz : riemannZeta s = 0) :
    (2 * s.re - 1) * ‖1 / s + (tailS c : ℂ) / (1 - s)‖ ^ 2 ≤ ∫ t in Ioc (0 : ℝ) 1, res c t ^ 2 := by
  obtain ⟨hconv, _⟩ := mellin_res c (by linarith) hs1 hz
  have hw : IntegrableOn (fun t => t ^ (s.re - 1) * |res c t|) (Ioi 0) := by
    refine IntegrableOn.congr_fun (Integrable.norm hconv) (fun t ht => ?_) measurableSet_Ioi
    simp only
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re, Complex.norm_real,
      Real.norm_eq_abs]
  have hnorm : ‖1 / s + (tailS c : ℂ) / (1 - s)‖ ≤
      ∫ t in Ioc (0 : ℝ) 1, t ^ (s.re - 1) * |res c t| := by
    rw [← mellin_cabeca c (by linarith) hs1 hz]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos ht.1, sub_re, one_re, Complex.norm_real,
      Real.norm_eq_abs]
  refine cs_de_amgm (by linarith) (norm_nonneg _) (integral_head_nonneg c) fun l hl => ?_
  exact hnorm.trans (integral_head_le' c hs0 hl (hw.mono_set Ioc_subset_Ioi_self))

/-- `‖res‖² = ∫_0^1 res² + S²`. -/
theorem residual_split {N : ℕ} (c : Fin N → ℝ) :
    residualSq N c = (∫ t in Ioc (0 : ℝ) 1, res c t ^ 2) + tailS c ^ 2 := by
  have hint := integrable_res_sq c
  have hu := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one))
  rw [Ioc_union_Ioi_eq_Ioi zero_le_one, integral_tail_sq] at hu
  rw [residualSq_eq_res, hu]

/-! ### A álgebra da barreira -/

/-- `S² + t·|1/ρ + S/(1−ρ)|² ≥ B(ρ)` para todo `S` real (com `t = 2σ−1 > 0`). -/
theorem algebra_barreira {s : ℂ} (hs0 : 1 / 2 < s.re) (hs1 : s.re < 1) (S : ℝ) :
    barreira s ≤ S ^ 2 + (2 * s.re - 1) * ‖1 / s + (S : ℂ) / (1 - s)‖ ^ 2 := by
  have hs : s ≠ 0 := by intro h; rw [h, zero_re] at hs0; linarith
  have h1s : (1 : ℂ) - s ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hw : 1 / s + (S : ℂ) / (1 - s) = ((1 - s) + (S : ℂ) * s) / (s * (1 - s)) := by
    field_simp
  rw [hw, Complex.sq_norm, normSq_div, normSq_mul]
  unfold barreira
  set σ := s.re with hσ
  set γ := s.im with hγ
  have ha : normSq s = σ ^ 2 + γ ^ 2 := by rw [normSq_apply]; ring
  have hb : normSq (1 - s) = (1 - σ) ^ 2 + γ ^ 2 := by
    rw [normSq_apply]; simp only [sub_re, one_re, sub_im, one_im]; ring
  have hn : normSq ((1 - s) + (S : ℂ) * s) = (1 - σ + S * σ) ^ 2 + (S * γ - γ) ^ 2 := by
    rw [normSq_apply]; simp only [add_re, sub_re, one_re, mul_re, ofReal_re, ofReal_im, add_im,
      sub_im, one_im, mul_im]; ring
  rw [ha, hb, hn]
  have hpa : 0 < σ ^ 2 + γ ^ 2 := by positivity
  have h1σ : 0 < 1 - σ := by linarith
  have hpb : 0 < (1 - σ) ^ 2 + γ ^ 2 := by positivity
  have key : S ^ 2 + (2 * σ - 1) * (((1 - σ + S * σ) ^ 2 + (S * γ - γ) ^ 2) /
      ((σ ^ 2 + γ ^ 2) * ((1 - σ) ^ 2 + γ ^ 2))) -
      (2 * σ - 1) * ((1 - σ) ^ 2 + γ ^ 2) / (σ ^ 2 + γ ^ 2) ^ 2 =
      (((σ ^ 2 + γ ^ 2) ^ 2 * S - (2 * σ - 1) * (σ ^ 2 + γ ^ 2 - σ)) ^ 2 +
        (2 * σ - 1) ^ 2 * γ ^ 2) / ((σ ^ 2 + γ ^ 2) ^ 3 * ((1 - σ) ^ 2 + γ ^ 2)) := by
    field_simp; ring
  have hnn : 0 ≤ (((σ ^ 2 + γ ^ 2) ^ 2 * S - (2 * σ - 1) * (σ ^ 2 + γ ^ 2 - σ)) ^ 2 +
        (2 * σ - 1) ^ 2 * γ ^ 2) / ((σ ^ 2 + γ ^ 2) ^ 3 * ((1 - σ) ^ 2 + γ ^ 2)) := by positivity
  linarith

/-! ### A barreira -/

/-- **Barreira**: um zero com `1/2 < Re ρ < 1` força `‖res‖² ≥ B(ρ)` para todo `N, c`. -/
theorem barreira_le_residual {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 1 / 2 < ρ.re) (h1 : ρ.re < 1)
    {N : ℕ} (c : Fin N → ℝ) : barreira ρ ≤ residualSq N c := by
  rw [residual_split]
  have hcs := cabeca_cs c h0 h1 hz
  have hal := algebra_barreira h0 h1 (tailS c)
  linarith

/-- **`D_N ≥ (2σ−1)|1−ρ|²/|ρ|⁴`** para todo `N`. -/
theorem barreira_le_DN {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 1 / 2 < ρ.re) (h1 : ρ.re < 1)
    (N : ℕ) : barreira ρ ≤ DN N :=
  le_ciInf fun c => barreira_le_residual hz h0 h1 c

/-- **`D_∞ ≥ B(ρ)`.** -/
theorem barreira_le_dInf {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    barreira ρ ≤ ATK.DInfinito.dInf :=
  le_ciInf fun N => barreira_le_DN hz h0 h1 N

theorem barreira_pos {ρ : ℂ} (h0 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) : 0 < barreira ρ := by
  have hs : ρ ≠ 0 := by intro h; rw [h, zero_re] at h0; linarith
  have h1s : (1 : ℂ) - ρ ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold barreira
  have := normSq_pos.mpr hs
  have := normSq_pos.mpr h1s
  have : 0 < 2 * ρ.re - 1 := by linarith
  positivity

/-- **Região livre de zeros a partir de um valor de `D_N`**: se `D_N < B(ρ)`, então `ζ(ρ) ≠ 0`. -/
theorem exclusao {ρ : ℂ} (h0 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) {N : ℕ} (h : DN N < barreira ρ) :
    riemannZeta ρ ≠ 0 :=
  fun hz => absurd (barreira_le_DN hz h0 h1 N) (not_le.mpr h)

/-- **Região livre de zeros da cota numérica de `D_256`** (`ContracaoDN.cert_Dinf_numerico` usa a mesma
hipótese; ela foi certificada fora do kernel por aritmética intervalar, `pesquisa/rodada3/certificado_D256`):
nenhum zero com `1/2 < Re ρ < 1` e `B(ρ) > 0,00823372` — por exemplo `Re ρ = 7/8`, `|Im ρ| < 9,46`. -/
theorem regiao_livre_D256 (h : DN 256 ≤ 823372 / 10 ^ 8) {ρ : ℂ} (h0 : 1 / 2 < ρ.re) (h1 : ρ.re < 1)
    (hB : 823372 / 10 ^ 8 < barreira ρ) : riemannZeta ρ ≠ 0 :=
  exclusao h0 h1 (lt_of_le_of_lt h hB)

/-- **A barreira nova domina a do kernel**: `m(ρ)² ≤ B(ρ)`. -/
theorem m_sq_le_barreira {ρ : ℂ} (h0 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    ATK.ForaDaLinha.m ρ ^ 2 ≤ barreira ρ := by
  have hs : ρ ≠ 0 := by intro h; rw [h, zero_re] at h0; linarith
  set σ := ρ.re with hσ
  set q := Real.sqrt (2 * σ - 1) with hq
  have ht : 0 < 2 * σ - 1 := by linarith
  have hq0 : 0 < q := Real.sqrt_pos.mpr ht
  have hq2 : q ^ 2 = 2 * σ - 1 := Real.sq_sqrt ht.le
  have hb0 : 0 < 1 - σ := by linarith
  set a := normSq ρ with ha
  set b := normSq (1 - ρ) with hb
  have hab : a = b + q ^ 2 := by rw [hq2, ha, hb, normSq_eq_add]
  have hbσ : (1 - σ) ^ 2 ≤ b := by
    rw [hb, normSq_apply]; simp only [sub_re, one_re, sub_im, one_im]; nlinarith [sq_nonneg ρ.im]
  have ha0 : 0 < a := normSq_pos.mpr hs
  have hnorm : ‖ρ‖ ^ 2 = a := Complex.sq_norm ρ
  have hm : ATK.ForaDaLinha.m ρ ^ 2 = 1 / (a * (1 / q + 1 / (1 - σ)) ^ 2) := by
    unfold ATK.ForaDaLinha.m
    rw [← hσ, ← hq, div_pow, one_pow, mul_pow, hnorm]
  rw [hm]
  unfold barreira
  rw [← hσ, ← ha, ← hb, ← hq2]
  have hK : 0 < 1 / q + 1 / (1 - σ) := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  -- a² ≤ q² b a (1/q + 1/(1−σ))²  ⇐  a ≤ b (1 + q/(1−σ))²
  have hexp : q ^ 2 * b * (a * (1 / q + 1 / (1 - σ)) ^ 2) =
      a * (b * (1 + q / (1 - σ)) ^ 2) := by field_simp
  rw [hexp]
  have hkey : a ≤ b * (1 + q / (1 - σ)) ^ 2 := by
    have e : b * (1 + q / (1 - σ)) ^ 2 = b + 2 * b * q / (1 - σ) + b * q ^ 2 / (1 - σ) ^ 2 := by
      field_simp; ring
    have i1 : 0 ≤ 2 * b * q / (1 - σ) := by
      have : 0 ≤ b := normSq_nonneg _
      positivity
    have i2 : q ^ 2 ≤ b * q ^ 2 / (1 - σ) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [sq_nonneg q]
    rw [e, hab]; linarith
  have : a ^ 2 = a * a := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left hkey ha0.le

end ATK.BarreiraZero

#print axioms ATK.BarreiraZero.normSq_eq_add
#print axioms ATK.BarreiraZero.mellin_cauda
#print axioms ATK.BarreiraZero.mellin_cabeca
#print axioms ATK.BarreiraZero.cabeca_cs
#print axioms ATK.BarreiraZero.residual_split
#print axioms ATK.BarreiraZero.algebra_barreira
#print axioms ATK.BarreiraZero.barreira_le_residual
#print axioms ATK.BarreiraZero.barreira_le_DN
#print axioms ATK.BarreiraZero.barreira_le_dInf
#print axioms ATK.BarreiraZero.barreira_pos
#print axioms ATK.BarreiraZero.exclusao
#print axioms ATK.BarreiraZero.regiao_livre_D256
#print axioms ATK.BarreiraZero.m_sq_le_barreira
