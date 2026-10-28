import ATK.ZeroClasses.LagariasHadamard

/-!
# O expoente de convergência dos zeros é exatamente 1; há infinitos zeros não triviais (rodada 35)

A rodada 32 provou `Σ_ρ m_ρ/|ρ|^p < ∞` para todo `p > 1`. Aqui, com o teorema de Hadamard (rodada 33):

* `norm_E1_le_lin`: `‖(1 − z)e^z‖ ≤ e^{2‖z‖}`; `prodE_norm_le_lin`: se `Σ 1/|r_i| < ∞`, então
  `‖∏' E1(z/r_i)‖ ≤ e^{2‖z‖ Σ 1/|r_i|}`;
* `zeta_lb_re_ge_dois`: `|ζ(s)| ≥ 2 − π²/6` em `Re s ≥ 2`;
* `xi_lb_par`: `|ξ(2n + 2)| ≥ (2 − π²/6) · n!/π^{n+1}` (crescimento super-exponencial no eixo real, via
  `Γ(n + 1) = n!`);
* **`nao_somavel_ZM`: `Σ_{(ρ,j)} 1/|ρ| = ∞`**. Se a série convergisse, Hadamard daria `|ξ(s)| ≤ e^{a + K|s|}`,
  o que contradiz `n!/π^{n+1}` (`tendsto_pow_div_factorial_atTop`);
* **`expoente_exato`: `Σ_ρ m_ρ/|ρ|^p < ∞ ⟺ p > 1`**: o expoente de convergência dos zeros de `ζ` é exatamente 1;
* **`zeros_infinitos`**: `Z` é infinito; **`zeros_infinitos_acima`**: há infinitos zeros com `Im ρ > 0` (a
  conjugação `ρ ↦ ρ̄` leva `Z` em `Z`); **`N_tende_infinito`**: `N(T) → ∞`.

Classificação (rodada 35): **consequência** (Hadamard 1893). `N(T)/T → ∞` (`CrescimentoN`, B10) continua
BUILD_PENDING: pede as constantes de Riemann–von Mangoldt. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real Nat ComplexConjugate

namespace ATK.ZeroClasses.Expoente

open ATK.BaseRiemannXi ATK.ZeroClasses.Canonico ATK.ZeroClasses.CanonicoInteira
  ATK.ZeroClasses.Hadamard ATK.ZeroClasses.LagariasHadamard

/-! ## 1. Cotas lineares do produto -/

theorem norm_E1_le_lin (z : ℂ) : ‖E1 z‖ ≤ Real.exp (2 * ‖z‖) := by
  have e : ‖E1 z‖ = ‖1 - z‖ * Real.exp z.re := by
    unfold E1
    rw [norm_mul, Complex.norm_exp]
  have h1 : ‖1 - z‖ ≤ 1 + ‖z‖ := by
    calc ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = 1 + ‖z‖ := by rw [norm_one]
  have h2 : 1 + ‖z‖ ≤ Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
  have h3 : Real.exp z.re ≤ Real.exp ‖z‖ := Real.exp_le_exp.mpr (Complex.re_le_norm z)
  rw [e]
  calc ‖1 - z‖ * Real.exp z.re ≤ Real.exp ‖z‖ * Real.exp ‖z‖ :=
        mul_le_mul (h1.trans h2) h3 (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (2 * ‖z‖) := by rw [← Real.exp_add]; ring_nf

theorem prodE_norm_le_lin {ι : Type*} {r : ι → ℂ} (hr0 : ∀ i, r i ≠ 0)
    (hs : Summable (fun i => 1 / ‖r i‖ ^ 2)) (h1 : Summable (fun i => 1 / ‖r i‖)) (z : ℂ) :
    ‖∏' i, E1 (z / r i)‖ ≤ Real.exp (2 * ‖z‖ * ∑' i, 1 / ‖r i‖) := by
  have hp : Tendsto (fun F : Finset ι => ∏ i ∈ F, E1 (z / r i)) atTop
      (𝓝 (∏' i, E1 (z / r i))) := (prodE_multipliable hr0 hs z).hasProd
  have hn := (continuous_norm.tendsto _).comp hp
  refine le_of_tendsto' hn fun F => ?_
  simp only [Function.comp_apply]
  rw [norm_prod]
  have e : ∀ i, 2 * ‖z / r i‖ = 2 * ‖z‖ * (1 / ‖r i‖) := by
    intro i
    rw [norm_div]
    ring
  calc ∏ i ∈ F, ‖E1 (z / r i)‖ ≤ ∏ i ∈ F, Real.exp (2 * ‖z / r i‖) :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => norm_E1_le_lin _)
    _ = Real.exp (∑ i ∈ F, 2 * ‖z / r i‖) := (Real.exp_sum F _).symm
    _ ≤ Real.exp (2 * ‖z‖ * ∑' i, 1 / ‖r i‖) := by
        apply Real.exp_le_exp.mpr
        simp_rw [e]
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (h1.sum_le_tsum F (fun i _ => by positivity)) (by positivity)

/-! ## 2. `ξ` cresce super-exponencialmente no eixo real -/

theorem zeta_lb_re_ge_dois {s : ℂ} (hs : 2 ≤ s.re) : 2 - π ^ 2 / 6 ≤ ‖riemannZeta s‖ := by
  have hs1 : 1 < s.re := by linarith
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow hs1
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hf
  have hnorm : ∀ n : ℕ, ‖f n‖ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    simp only [hf, norm_div, norm_one]
    have e : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_natCast_cpow_of_pos (by omega)]
    have e2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [e2]
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have h2 : ((n : ℝ) + 1) ^ (2 : ℝ) ≤ ((n : ℝ) + 1) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le h1 hs
    rw [Real.rpow_two] at h2
    exact one_div_le_one_div_of_le (by positivity) h2
  have hR : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    simpa using this
  have hsum : Summable (fun n => ‖f n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnorm hR.summable
  have hfs : Summable f := hsum.of_norm
  have hf0 : f 0 = 1 := by simp [hf]
  have htot : ∑' n, ‖f n‖ ≤ Real.pi ^ 2 / 6 := by
    rw [← hR.tsum_eq]
    exact hsum.tsum_le_tsum hnorm hR.summable
  have htail : ∑' n, ‖f (n + 1)‖ ≤ Real.pi ^ 2 / 6 - 1 := by
    have h1 := hsum.tsum_eq_zero_add
    rw [hf0, norm_one] at h1
    linarith
  have hs1' : Summable (fun n => ‖f (n + 1)‖) := (summable_nat_add_iff 1).mpr hsum
  have hle : ‖∑' n, f (n + 1)‖ ≤ Real.pi ^ 2 / 6 - 1 := (norm_tsum_le_tsum_norm hs1').trans htail
  have hzeta : riemannZeta s = 1 + ∑' n, f (n + 1) := by
    rw [hz]
    change ∑' n, f n = _
    rw [hfs.tsum_eq_zero_add, hf0]
  rw [hzeta]
  have h := norm_sub_norm_le (1 : ℂ) (-(∑' n, f (n + 1)))
  rw [norm_neg, sub_neg_eq_add, norm_one] at h
  linarith

/-- **`|ξ(2n + 2)| ≥ (2 − π²/6) · n!/π^{n+1}`**. -/
theorem xi_lb_par (n : ℕ) :
    (2 - π ^ 2 / 6) * (n ! : ℝ) / π ^ (n + 1) ≤ ‖riemannXi (2 * n + 2)‖ := by
  set s : ℂ := 2 * n + 2 with hsd
  have hre : s.re = 2 * n + 2 := by simp [hsd]
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hre, zero_re] at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hre, one_re] at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hpos : 0 < s.re := by rw [hre]; positivity
  have hG := Gammaℝ_ne_zero_of_re_pos hpos
  rw [riemannXi_eq_zeta hs0 hs1 hG, norm_mul, norm_mul]
  -- os três fatores
  have h1 : (1 : ℝ) ≤ ‖s * (s - 1) / 2‖ := by
    have e : s * (s - 1) / 2 = (((2 * n + 2) * (2 * n + 1) / 2 : ℝ) : ℂ) := by
      rw [hsd]; push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h2 : ‖Gammaℝ s‖ = (n ! : ℝ) / π ^ (n + 1) := by
    rw [Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have e1 : s / 2 = (n : ℂ) + 1 := by rw [hsd]; ring
    have e2 : (-s / 2).re = -((n : ℝ) + 1) := by rw [hsd]; simp; ring
    rw [e1, e2, Complex.Gamma_nat_eq_factorial, Complex.norm_natCast, Real.rpow_neg Real.pi_pos.le]
    have : Real.pi ^ ((n : ℝ) + 1) = Real.pi ^ (n + 1) := by
      rw [← Real.rpow_natCast]
      push_cast
      ring_nf
    rw [this]
    field_simp
  have h3 := zeta_lb_re_ge_dois (s := s) (by rw [hre]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  rw [h2]
  have hb := ATK.BLProva.dois_menos_pos
  have hf0 : (0 : ℝ) ≤ (n ! : ℝ) / π ^ (n + 1) := by positivity
  calc (2 - π ^ 2 / 6) * (n ! : ℝ) / π ^ (n + 1)
      = 1 * ((n ! : ℝ) / π ^ (n + 1)) * (2 - π ^ 2 / 6) := by ring
    _ ≤ ‖s * (s - 1) / 2‖ * ((n ! : ℝ) / π ^ (n + 1)) * ‖riemannZeta s‖ := by gcongr

/-! ## 3. `Σ 1/|ρ| = ∞` -/

/-- **`Σ_{(ρ,j)} 1/|ρ| = ∞`**: os zeros não são esparsos o bastante para um produto de gênero 0. -/
theorem nao_somavel_ZM : ¬ Summable (fun q : ZM => 1 / ‖rZ q‖) := by
  intro h1
  obtain ⟨A, B, hAB⟩ := xi_hadamard
  set S1 := ∑' q : ZM, 1 / ‖rZ q‖ with hS1
  have hS0 : 0 ≤ S1 := tsum_nonneg fun q => by positivity
  set K := ‖B‖ + 2 * S1 with hK
  have hP : ∀ z, ‖Pcan z‖ ≤ Real.exp (2 * ‖z‖ * S1) := fun z =>
    prodE_norm_le_lin (r := rZ) ZM_ne_zero summable_ZM h1 z
  -- cota superior: |ξ(z)| ≤ e^{‖A‖ + K‖z‖}
  have hup : ∀ z, ‖riemannXi z‖ ≤ Real.exp (‖A‖ + K * ‖z‖) := by
    intro z
    rw [hAB z, norm_mul, Complex.norm_exp]
    have he : (A + B * z).re ≤ ‖A‖ + ‖B‖ * ‖z‖ := by
      calc (A + B * z).re ≤ ‖A + B * z‖ := Complex.re_le_norm _
        _ ≤ ‖A‖ + ‖B * z‖ := norm_add_le _ _
        _ = ‖A‖ + ‖B‖ * ‖z‖ := by rw [norm_mul]
    calc Real.exp (A + B * z).re * ‖Pcan z‖ ≤ Real.exp (‖A‖ + ‖B‖ * ‖z‖) * Real.exp (2 * ‖z‖ * S1) :=
          mul_le_mul (Real.exp_le_exp.mpr he) (hP z) (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (‖A‖ + K * ‖z‖) := by rw [← Real.exp_add, hK]; ring_nf
  -- n! ≤ C · D^n
  set D := π * Real.exp (2 * K) with hD
  set C := π * Real.exp (‖A‖ + 2 * K) / (2 - π ^ 2 / 6) with hC
  have hb := ATK.BLProva.dois_menos_pos
  have hCpos : 0 < C := by positivity
  have hbound : ∀ n : ℕ, (n ! : ℝ) ≤ C * D ^ n := by
    intro n
    have hl := xi_lb_par n
    have hu := hup (2 * n + 2)
    have hn : ‖(2 * (n : ℂ) + 2)‖ = 2 * n + 2 := by
      have e : (2 * (n : ℂ) + 2) = ((2 * n + 2 : ℝ) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hn] at hu
    have hcomb := hl.trans hu
    have hpi : 0 < π ^ (n + 1) := by positivity
    rw [div_le_iff₀ hpi] at hcomb
    have eD : Real.exp (‖A‖ + K * (2 * n + 2)) * π ^ (n + 1) =
        π * Real.exp (‖A‖ + 2 * K) * D ^ n := by
      rw [hD, mul_pow, ← Real.exp_nat_mul]
      rw [show π ^ (n + 1) = π * π ^ n by ring, mul_comm (π ^ n)]
      have : Real.exp (‖A‖ + K * (2 * n + 2)) = Real.exp (‖A‖ + 2 * K) * Real.exp (n * (2 * K)) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]
      ring
    rw [eD] at hcomb
    rw [hC, div_mul_eq_mul_div, le_div_iff₀ hb]
    linarith
  -- contradição com D^n/n! → 0
  have ht := FloorSemiring.tendsto_pow_div_factorial_atTop D
  have hev := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / C by positivity))
  obtain ⟨n, hn⟩ := hev.exists
  have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  rw [div_lt_div_iff₀ hfac hCpos, one_mul] at hn
  have := hbound n
  linarith

/-- `Σ_ρ m_ρ/|ρ| = ∞` (soma sobre `Z`, com multiplicidade). -/
theorem soma_ordem_inv_diverge :
    ¬ Summable (fun ρ : ATK.ZetaSimetria.Z =>
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖) := by
  intro h
  apply nao_somavel_ZM
  rw [summable_sigma_of_nonneg (fun q => by positivity)]
  refine ⟨fun x => Summable.of_finite, ?_⟩
  convert h using 1
  funext x
  rw [tsum_fintype]
  simp only [rZ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **O expoente de convergência dos zeros é exatamente 1**: `Σ_ρ m_ρ/|ρ|^p < ∞ ⟺ p > 1`. -/
theorem expoente_exato (p : ℝ) :
    Summable (fun ρ : ATK.ZetaSimetria.Z =>
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ p) ↔ 1 < p := by
  constructor
  · intro h
    by_contra hp'
    have hp : p ≤ 1 := not_lt.mp hp'
    apply soma_ordem_inv_diverge
    refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_) h
    have h13 := ATK.ZeroClasses.Faixa.zeros_acima_13 ρ ρ.2
    have h1 : (1 : ℝ) ≤ ‖(ρ : ℂ)‖ := by
      have := Complex.abs_im_le_norm (ρ : ℂ)
      linarith
    have hpow : ‖(ρ : ℂ)‖ ^ p ≤ ‖(ρ : ℂ)‖ := by
      conv_rhs => rw [← Real.rpow_one ‖(ρ : ℂ)‖]
      exact Real.rpow_le_rpow_of_exponent_le h1 hp
    have hpos : 0 < ‖(ρ : ℂ)‖ ^ p := Real.rpow_pos_of_pos (by linarith) p
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos hpow
  · exact fun hp => soma_ordem_inv_pot hp

/-! ## 4. Infinitos zeros -/

/-- **Há infinitos zeros não triviais.** -/
theorem zeros_infinitos : ATK.ZetaSimetria.Z.Infinite := by
  intro hfin
  apply soma_ordem_inv_diverge
  have : Finite ↥ATK.ZetaSimetria.Z := hfin.to_subtype
  exact Summable.of_finite

theorem conj_mem_Z {ρ : ℂ} (hρ : ρ ∈ ATK.ZetaSimetria.Z) : conj ρ ∈ ATK.ZetaSimetria.Z := by
  refine ⟨?_, by simpa using hρ.2.1, by simpa using hρ.2.2⟩
  rw [riemannZeta_conj, hρ.1, map_zero]

/-- **Há infinitos zeros com `Im ρ > 0`.** -/
theorem zeros_infinitos_acima : {ρ ∈ ATK.ZetaSimetria.Z | 0 < ρ.im}.Infinite := by
  intro hfin
  apply zeros_infinitos
  refine (hfin.union (hfin.image conj)).subset fun ρ hρ => ?_
  have h13 := ATK.ZeroClasses.Faixa.zeros_acima_13 ρ hρ
  rcases lt_or_gt_of_ne (show ρ.im ≠ 0 by intro h; rw [h, abs_zero] at h13; norm_num at h13) with h | h
  · right
    refine ⟨conj ρ, ⟨conj_mem_Z hρ, by simpa using h⟩, by simp⟩
  · left
    exact ⟨hρ, h⟩

theorem ordem_pos {ρ : ℂ} (hρ : ρ ∈ ATK.ZetaSimetria.Z) : 1 ≤ analyticOrderNatAt riemannZeta ρ := by
  have h1 : ρ ≠ 1 := by
    rintro rfl
    have := hρ.2.2
    simp at this
  have htop := ATK.ZeroClasses.JensenLocal.ordem_zeta_finita hρ.2.1 h1
  by_contra hlt
  have h0 : analyticOrderNatAt riemannZeta ρ = 0 := by omega
  exact ((ATK.ArgPrincipio.ordemNat_zero_iff (analyticOn_riemannZeta _ h1) htop).mp h0) hρ.1

/-- **`N(T) → ∞`.** -/
theorem N_tende_infinito : Tendsto (fun T => (ATK.FechamentoO1.N T : ℝ)) atTop atTop := by
  classical
  rw [Filter.tendsto_atTop]
  intro b
  obtain ⟨k, hk⟩ := exists_nat_ge b
  obtain ⟨F, hF, hcard⟩ := zeros_infinitos_acima.exists_subset_card_eq k
  refine Filter.eventually_atTop.mpr ⟨∑ ρ ∈ F, |ρ.im|, fun T hT => ?_⟩
  have hsub : F ⊆ (ATK.FechamentoO1.zerosAte_finito T).toFinset := by
    intro ρ hρ
    obtain ⟨hZ, hpos⟩ := hF hρ
    rw [Set.Finite.mem_toFinset]
    refine ⟨hZ, hpos, ?_⟩
    have := Finset.single_le_sum (f := fun ρ : ℂ => |ρ.im|) (fun _ _ => abs_nonneg _) hρ
    linarith [le_abs_self ρ.im]
  have hN : (k : ℝ) ≤ ATK.FechamentoO1.N T := by
    unfold ATK.FechamentoO1.N
    have h1 : k ≤ ∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ := by
      calc k = ∑ _ρ ∈ F, 1 := by simp [hcard]
        _ ≤ ∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ :=
            Finset.sum_le_sum fun ρ hρ => ordem_pos (hF hρ).1
    have h2 := Finset.sum_le_sum_of_subset (f := fun ρ => analyticOrderNatAt riemannZeta ρ) hsub
    exact_mod_cast h1.trans h2
  linarith

end ATK.ZeroClasses.Expoente

#print axioms ATK.ZeroClasses.Expoente.norm_E1_le_lin
#print axioms ATK.ZeroClasses.Expoente.prodE_norm_le_lin
#print axioms ATK.ZeroClasses.Expoente.zeta_lb_re_ge_dois
#print axioms ATK.ZeroClasses.Expoente.xi_lb_par
#print axioms ATK.ZeroClasses.Expoente.nao_somavel_ZM
#print axioms ATK.ZeroClasses.Expoente.soma_ordem_inv_diverge
#print axioms ATK.ZeroClasses.Expoente.expoente_exato
#print axioms ATK.ZeroClasses.Expoente.zeros_infinitos
#print axioms ATK.ZeroClasses.Expoente.conj_mem_Z
#print axioms ATK.ZeroClasses.Expoente.zeros_infinitos_acima
#print axioms ATK.ZeroClasses.Expoente.ordem_pos
#print axioms ATK.ZeroClasses.Expoente.N_tende_infinito
