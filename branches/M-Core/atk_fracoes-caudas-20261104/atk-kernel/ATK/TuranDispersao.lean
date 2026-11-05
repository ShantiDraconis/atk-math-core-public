import ATK.HurwitzJensen

/-!
# ATK — A identidade de dispersão de ordem 2 e PF₂ dos coeficientes de `Ξ` sem HR (módulo o lema de Csordas)

**Identidade de dispersão** (`turan_disp`): para um núcleo `K > 0` em `(0, ∞)` regular e rapidamente decrescente,
com `γₖ = ∫₀^∞u^{2k}K(u)du` e `ψ(u) = −K′(u)/(uK(u))`, integrando por partes (`ibp`) e simetrizando (Fubini),

`(2m+3)γ_{m+1}² − (2m+1)γ_mγ_{m+2} = ½∬ K(t)K(s)(ts)^{2m+2}(t² − s²)(ψ(t) − ψ(s)) ds dt`,

e o integrando é `≥ 0` se `ψ` é crescente. É o mecanismo de Csordas–Norfolk–Varga (1986).

**Para `Ξ`**: `Φ` é um núcleo regular (`nucleo_Phi`: derivada termo a termo `Φ′ = Σ phiTd`, `|Φ′(u)| ≤ C e^{−2u}`,
integrabilidade e decaimento de todos os `uᵏΦ`, `uᵏΦ′`). Daí:

* `turan_de_csordas`: **se `ψ_Φ` é crescente, `γ(n)γ(n+2) ≤ γ(n+1)²`** (`γ(k) = k!aₖ`) — a desigualdade de Turán,
  agora **sem HR** como hipótese (compare `ATK.JensenPolya.turan_de_rh`);
* `pf2_de_csordas`: **todos os menores `2 × 2` de `T(aₙ)` são `≥ 0`** (PF₂), via `pf2_de_logconcava`.

**`BUILD_PENDING`**: a monotonia de `ψ_Φ` (equivalente à log-concavidade de `Φ(√x)`) é um teorema de Csordas
(CNV 1986; Csordas 2015, Thm. 4.2(b)), não formalizado aqui; numericamente `ψ_Φ` cresce em `(0, 2]`. As ordens `r ≥ 3`
(PF_r) continuam `OPEN_MATH` — PF∞ é HR.
-/

open Filter Topology Set MeasureTheory
open scoped Nat

namespace ATK.TuranDisp

open ATK.ToeplitzTN (toep)

/-! ## 1. A identidade de dispersão para um núcleo geral -/

/-- `γₖ(K) = ∫₀^∞u^{2k}K(u)du`. -/
noncomputable def gam (K : ℝ → ℝ) (k : ℕ) : ℝ := ∫ u in Ioi (0 : ℝ), u ^ (2 * k) * K u

/-- Hipóteses de regularidade de um núcleo. -/
structure Nucleo (K K' : ℝ → ℝ) : Prop where
  deriv : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt K (K' u) u
  cont0 : ContinuousWithinAt K (Ici 0) 0
  pos : ∀ u ∈ Ioi (0 : ℝ), 0 < K u
  intK : ∀ k : ℕ, IntegrableOn (fun u => u ^ k * K u) (Ioi 0)
  intK' : ∀ k : ℕ, IntegrableOn (fun u => u ^ k * K' u) (Ioi 0)
  decay : ∀ k : ℕ, Tendsto (fun u => u ^ k * K u) atTop (𝓝 0)

/-- **Integração por partes**: `(k+1)∫uᵏK = −∫u^{k+1}K′`. -/
theorem ibp {K K' : ℝ → ℝ} (h : Nucleo K K') (k : ℕ) :
    ((k : ℝ) + 1) * ∫ u in Ioi (0 : ℝ), u ^ k * K u = -∫ u in Ioi (0 : ℝ), u ^ (k + 1) * K' u := by
  have hf := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun u => u ^ (k + 1) * K u)
    (f' := fun u => ((k : ℝ) + 1) * (u ^ k * K u) + u ^ (k + 1) * K' u) (a := 0) (m := 0)
    (((continuous_pow _).continuousWithinAt).mul h.cont0)
    (fun x hx => by
      have h1 := (hasDerivAt_pow (k + 1) x).mul (h.deriv x hx)
      convert h1 using 1
      push_cast
      ring)
    (((h.intK k).const_mul _).add (h.intK' (k + 1))) (h.decay (k + 1))
  rw [integral_add ((h.intK k).const_mul _) (h.intK' (k + 1)), integral_const_mul] at hf
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow, zero_mul,
    sub_zero] at hf
  linarith

/-- **Identidade de dispersão de ordem 2 ⇒ Turán**: se `ψ = −K′/(uK)` é crescente,
`(2m+1)γ_mγ_{m+2} ≤ (2m+3)γ_{m+1}²`. -/
theorem turan_disp {K K' : ℝ → ℝ} (h : Nucleo K K')
    (hψ : MonotoneOn (fun u => -K' u / (u * K u)) (Ioi 0)) (m : ℕ) :
    (2 * (m : ℝ) + 1) * gam K m * gam K (m + 2) ≤ (2 * (m : ℝ) + 3) * gam K (m + 1) ^ 2 := by
  set μ : Measure ℝ := volume.restrict (Ioi 0) with hμ
  set ψ : ℝ → ℝ := fun u => -K' u / (u * K u) with hψdef
  -- integração por partes
  have hA : (2 * (m : ℝ) + 3) * gam K (m + 1) = ∫ t in Ioi (0 : ℝ), -(t ^ (2 * m + 3) * K' t) := by
    have := ibp h (2 * m + 2)
    rw [integral_neg]
    unfold gam
    rw [show 2 * (m + 1) = 2 * m + 2 by ring]
    push_cast at this ⊢
    rw [show 2 * m + 2 + 1 = 2 * m + 3 by ring] at this
    linarith
  have hB : (2 * (m : ℝ) + 1) * gam K m = ∫ t in Ioi (0 : ℝ), -(t ^ (2 * m + 1) * K' t) := by
    have := ibp h (2 * m)
    rw [integral_neg]
    unfold gam
    push_cast at this ⊢
    linarith
  -- as funções e o produto
  set f1 : ℝ → ℝ := fun t => -(t ^ (2 * m + 3) * K' t) with hf1
  set g1 : ℝ → ℝ := fun s => s ^ (2 * m + 2) * K s with hg1
  set f2 : ℝ → ℝ := fun t => -(t ^ (2 * m + 1) * K' t) with hf2
  set g2 : ℝ → ℝ := fun s => s ^ (2 * m + 4) * K s with hg2
  have i1 : Integrable f1 μ := (h.intK' _).neg
  have i2 : Integrable f2 μ := (h.intK' _).neg
  have j1 : Integrable g1 μ := h.intK _
  have j2 : Integrable g2 μ := h.intK _
  set G : ℝ × ℝ → ℝ := fun z => f1 z.1 * g1 z.2 - f2 z.1 * g2 z.2 with hG
  have iG : Integrable G (μ.prod μ) := (i1.mul_prod j1).sub (i2.mul_prod j2)
  have hE : (2 * (m : ℝ) + 3) * gam K (m + 1) ^ 2 - (2 * (m : ℝ) + 1) * gam K m * gam K (m + 2) =
      ∫ z, G z ∂(μ.prod μ) := by
    rw [hG, integral_sub (i1.mul_prod j1) (i2.mul_prod j2), integral_prod_mul, integral_prod_mul]
    have e1 : gam K (m + 1) = ∫ s, g1 s ∂μ := by
      unfold gam; rw [show 2 * (m + 1) = 2 * m + 2 by ring]
    have e2 : gam K (m + 2) = ∫ s, g2 s ∂μ := by
      unfold gam; rw [show 2 * (m + 2) = 2 * m + 4 by ring]
    rw [show (2 * (m : ℝ) + 3) * gam K (m + 1) ^ 2 = ((2 * (m : ℝ) + 3) * gam K (m + 1)) * gam K (m + 1)
      by ring, show (2 * (m : ℝ) + 1) * gam K m * gam K (m + 2) = ((2 * (m : ℝ) + 1) * gam K m) *
      gam K (m + 2) by ring, hA, hB, e1, e2]
  have hswap : ∫ z, G z.swap ∂(μ.prod μ) = ∫ z, G z ∂(μ.prod μ) := integral_prod_swap G
  have hsum : 0 ≤ ∫ z, (G z + G z.swap) ∂(μ.prod μ) := by
    rw [hμ, Measure.prod_restrict]
    refine integral_nonneg_of_ae (ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi)
      fun z hz => ?_)
    obtain ⟨t, s⟩ := z
    simp only [mem_prod, mem_Ioi] at hz
    obtain ⟨ht, hs⟩ := hz
    have hKt := h.pos t ht
    have hKs := h.pos s hs
    have eKt : K' t = -(ψ t * t * K t) := by
      simp only [hψdef]
      field_simp
    have eKs : K' s = -(ψ s * s * K s) := by
      simp only [hψdef]
      field_simp
    have key : G (t, s) + G (t, s).swap =
        K t * K s * (t * s) ^ (2 * m + 2) * ((t ^ 2 - s ^ 2) * (ψ t - ψ s)) := by
      simp only [hG, hf1, hg1, hf2, hg2, Prod.swap_prod_mk, eKt, eKs]
      ring
    show 0 ≤ G (t, s) + G (t, s).swap
    rw [key]
    apply mul_nonneg (by positivity)
    rcases le_total t s with hts | hts
    · have h1 : t ^ 2 - s ^ 2 ≤ 0 := by nlinarith
      have h2 : ψ t - ψ s ≤ 0 := by linarith [hψ (mem_Ioi.mpr ht) (mem_Ioi.mpr hs) hts]
      nlinarith
    · have h1 : 0 ≤ t ^ 2 - s ^ 2 := by nlinarith
      have h2 : 0 ≤ ψ t - ψ s := by linarith [hψ (mem_Ioi.mpr hs) (mem_Ioi.mpr ht) hts]
      nlinarith
  have hadd : ∫ z, (G z + G z.swap) ∂(μ.prod μ) = ∫ z, G z ∂(μ.prod μ) + ∫ z, G z.swap ∂(μ.prod μ) :=
    integral_add iG iG.swap
  rw [hadd, hswap] at hsum
  linarith

/-! ## 2. PF₂ a partir da log-concavidade -/

/-- Para `a > 0` log-côncava, `a(l+d)a(k) ≤ a(k+d)a(l)` quando `k ≤ l`. -/
theorem razao_lc {a : ℕ → ℝ} (hpos : ∀ n, 0 < a n) (hlc : ∀ n, a n * a (n + 2) ≤ a (n + 1) ^ 2) :
    ∀ d k l, k ≤ l → a (l + d) * a k ≤ a (k + d) * a l := by
  have hr : Antitone fun n => a (n + 1) / a n := by
    refine antitone_nat_of_succ_le fun n => ?_
    show a (n + 1 + 1) / a (n + 1) ≤ a (n + 1) / a n
    rw [div_le_div_iff₀ (hpos _) (hpos _)]
    have := hlc n
    nlinarith
  intro d
  induction d with
  | zero => intro k l _; simp [mul_comm]
  | succ d ih =>
    intro k l hkl
    have h1 := ih k l hkl
    have h2 := hr (show k + d ≤ l + d by omega)
    simp only at h2
    rw [div_le_div_iff₀ (hpos _) (hpos _)] at h2
    have hk := hpos k
    have hl := hpos l
    have hkd := hpos (k + d)
    have hld := hpos (l + d)
    rw [show l + (d + 1) = l + d + 1 by ring, show k + (d + 1) = k + d + 1 by ring]
    -- a(l+d+1)a(k)·a(k+d)a(l+d) ≤ …: usar a(l+d+1)a(k+d) ≤ a(k+d+1)a(l+d) e h1
    have h3 : a (l + d + 1) * a k * a (l + d) ≤ a (k + d + 1) * a l * a (l + d) := by
      nlinarith [mul_le_mul_of_nonneg_left h1 (hpos (l + d + 1)).le,
        mul_le_mul_of_nonneg_left h2 (hpos l).le]
    exact le_of_mul_le_mul_right h3 hld

/-- **PF₂**: se `a > 0` é log-côncava, todos os menores `2 × 2` de `T(a)` são `≥ 0`. -/
theorem pf2_de_logconcava {a : ℕ → ℝ} (hpos : ∀ n, 0 < a n)
    (hlc : ∀ n, a n * a (n + 2) ≤ a (n + 1) ^ 2) (I J : Fin 2 → ℕ) (hI : StrictMono I)
    (hJ : StrictMono J) : 0 ≤ ((toep a).submatrix I J).det := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.submatrix_apply, toep]
  have hi : I 0 < I 1 := hI (by decide)
  have hj : J 0 < J 1 := hJ (by decide)
  have hnn : ∀ n, 0 ≤ a n := fun n => (hpos n).le
  by_cases h01 : J 1 ≤ I 0
  · rw [if_pos (by omega), if_pos (by omega), if_pos h01, if_pos (by omega)]
    -- a(x)a(y) − a(u)a(v), u = I0 − J1, x = I0 − J0, y = I1 − J1, v = I1 − J0
    have := razao_lc hpos hlc (J 1 - J 0) (I 0 - J 1) (I 1 - J 1) (by omega)
    rw [show I 1 - J 1 + (J 1 - J 0) = I 1 - J 0 by omega,
      show I 0 - J 1 + (J 1 - J 0) = I 0 - J 0 by omega] at this
    linarith
  · rw [if_neg h01, zero_mul, sub_zero]
    apply mul_nonneg <;> split_ifs <;> simp [hnn]

/-! ## 3. `Φ` é um núcleo regular -/

open ATK.XiPhi (Phi phiT cN hT)
open ATK.XiMom ATK.XiCresc ATK.XiTP ATK.JensenPolya

/-- `∂ᵤ phiT(c, u) = (−8w³ + 30w² − 15w)e^{u/2−w}`, `w = ce^{2u}`. -/
noncomputable def phiTd (c u : ℝ) : ℝ :=
  (-8 * (c * Real.exp (2 * u)) ^ 3 + 30 * (c * Real.exp (2 * u)) ^ 2 - 15 * (c * Real.exp (2 * u))) *
    hT c u

theorem continuous_phiTd (c : ℝ) : Continuous (phiTd c) := by
  unfold phiTd
  exact (by fun_prop : Continuous fun u : ℝ => (-8 * (c * Real.exp (2 * u)) ^ 3 +
    30 * (c * Real.exp (2 * u)) ^ 2 - 15 * (c * Real.exp (2 * u)))).mul (ATK.XiPhi.continuous_hT c)

theorem hasDerivAt_phiT (c u : ℝ) : HasDerivAt (phiT c) (phiTd c u) u := by
  have hw : HasDerivAt (fun u => c * Real.exp (2 * u)) (c * (Real.exp (2 * u) * 2)) u := by
    have := (((hasDerivAt_id u).const_mul 2).exp).const_mul c
    simpa using this
  have hw2 : HasDerivAt (fun u => (c * Real.exp (2 * u)) ^ 2)
      (2 * (c * Real.exp (2 * u)) * (c * (Real.exp (2 * u) * 2))) u := by
    have h2 := hw.fun_pow 2
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at h2
    exact h2
  have hP : HasDerivAt (fun u => 4 * (c * Real.exp (2 * u)) ^ 2 - 6 * (c * Real.exp (2 * u)))
      (4 * (2 * (c * Real.exp (2 * u)) * (c * (Real.exp (2 * u) * 2))) - 6 * (c * (Real.exp (2 * u) * 2)))
      u := (hw2.const_mul 4).sub (hw.const_mul 6)
  have h : HasDerivAt (fun u => (4 * (c * Real.exp (2 * u)) ^ 2 - 6 * (c * Real.exp (2 * u))) * hT c u)
      ((4 * (2 * (c * Real.exp (2 * u)) * (c * (Real.exp (2 * u) * 2))) -
        6 * (c * (Real.exp (2 * u) * 2))) * hT c u +
        (4 * (c * Real.exp (2 * u)) ^ 2 - 6 * (c * Real.exp (2 * u))) * ATK.XiPhi.hT1 c u) u :=
    hP.mul (ATK.XiPhi.hasDerivAt_hT c u)
  have e : phiT c = fun u => (4 * (c * Real.exp (2 * u)) ^ 2 - 6 * (c * Real.exp (2 * u))) * hT c u := by
    funext u
    rfl
  rw [e]
  convert h using 1
  unfold phiTd ATK.XiPhi.hT1
  ring

theorem cN_ge3 (n : ℕ) : 3 ≤ cN n := by
  unfold cN
  have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
    nlinarith
  nlinarith [Real.pi_gt_three]

/-- `|phiTd(c, u)| ≤ 744·e^{−c/2}·e^{−2u}` (`c ≥ 3`, `u ≥ 0`). -/
theorem phiTd_cota {c u : ℝ} (hc : 3 ≤ c) (hu : 0 ≤ u) :
    |phiTd c u| ≤ 744 * Real.exp (-(c / 2)) * Real.exp (-(2 * u)) := by
  set w := c * Real.exp (2 * u) with hwdef
  have hE : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  have hw : c + 2 * c * u ≤ w := by
    rw [hwdef]
    nlinarith
  have hw0 : 0 ≤ w := by nlinarith
  have p1 := ATK.XiPhi.pow_le_exp_half hw0 (k := 1) (by norm_num)
  have p2 := ATK.XiPhi.pow_le_exp_half hw0 (k := 2) le_rfl
  have p3 : w ^ 3 ≤ 48 * Real.exp (w / 2) := by
    have := Real.pow_div_factorial_le_exp (w / 2) (by linarith) 3
    simp [Nat.factorial] at this
    nlinarith
  rw [pow_one] at p1
  unfold phiTd hT
  rw [← hwdef, abs_mul, abs_of_pos (Real.exp_pos _)]
  have habs : |-8 * w ^ 3 + 30 * w ^ 2 - 15 * w| ≤ 744 * Real.exp (w / 2) := by
    rw [abs_le]
    constructor <;> nlinarith [pow_nonneg hw0 2, pow_nonneg hw0 3, Real.exp_pos (w / 2)]
  calc |-8 * w ^ 3 + 30 * w ^ 2 - 15 * w| * Real.exp (u / 2 - w)
      ≤ 744 * Real.exp (w / 2) * Real.exp (u / 2 - w) :=
        mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le
    _ = 744 * Real.exp (u / 2 - w / 2) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ 744 * Real.exp (-(c / 2) + -(2 * u)) := by
        gcongr
        nlinarith
    _ = 744 * Real.exp (-(c / 2)) * Real.exp (-(2 * u)) := by rw [Real.exp_add]; ring

/-- `Φ′(u) = Σₙ phiTd(cₙ, u)`. -/
noncomputable def Phid (u : ℝ) : ℝ := ∑' n : ℕ, phiTd (cN n) u

theorem phiTd_cota' {n : ℕ} {u : ℝ} (hu : 0 ≤ u) : ‖phiTd (cN n) u‖ ≤ 744 * Real.exp (-(cN n / 2)) := by
  rw [Real.norm_eq_abs]
  refine (phiTd_cota (cN_ge3 n) hu).trans ?_
  have : Real.exp (-(2 * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 := Real.exp_pos (-(cN n / 2))
  nlinarith

theorem hasDerivAt_Phi {u : ℝ} (hu : 0 < u) : HasDerivAt Phi (Phid u) u := by
  have h := hasDerivAt_tsum_of_isPreconnected (u := fun n => 744 * Real.exp (-(cN n / 2)))
    (g := fun n => phiT (cN n)) (g' := fun n y => phiTd (cN n) y) (t := Ioi 0) (y₀ := 1) (y := u)
    (ATK.XiPhi.summable_exp_cN.mul_left 744) isOpen_Ioi isPreconnected_Ioi
    (fun n y _ => hasDerivAt_phiT _ _) (fun n y hy => phiTd_cota' (le_of_lt hy))
    (mem_Ioi.mpr one_pos) (summable_phiT (by norm_num)) hu
  exact h

theorem Phid_cota {u : ℝ} (hu : 0 ≤ u) :
    |Phid u| ≤ 744 * (∑' n : ℕ, Real.exp (-(cN n / 2))) * Real.exp (-(2 * u)) := by
  have hb : ∀ n, ‖phiTd (cN n) u‖ ≤ 744 * Real.exp (-(cN n / 2)) * Real.exp (-(2 * u)) := fun n => by
    rw [Real.norm_eq_abs]
    exact phiTd_cota (cN_ge3 n) hu
  have hs : Summable fun n : ℕ => 744 * Real.exp (-(cN n / 2)) * Real.exp (-(2 * u)) :=
    (ATK.XiPhi.summable_exp_cN.mul_left 744).mul_right _
  have hsn : Summable fun n => ‖phiTd (cN n) u‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs
  calc |Phid u| = ‖∑' n, phiTd (cN n) u‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖phiTd (cN n) u‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' n : ℕ, 744 * Real.exp (-(cN n / 2)) * Real.exp (-(2 * u)) := Summable.tsum_le_tsum hb hsn hs
    _ = _ := by rw [tsum_mul_right, tsum_mul_left]

theorem continuousOn_Phid : ContinuousOn Phid (Ici 0) :=
  continuousOn_tsum (u := fun n => 744 * Real.exp (-(cN n / 2)))
    (fun n => (continuous_phiTd _).continuousOn) (ATK.XiPhi.summable_exp_cN.mul_left 744)
    fun n u hu => phiTd_cota' (mem_Ici.mp hu)

theorem pow_le_fact_exp (k : ℕ) {u : ℝ} (hu : 0 ≤ u) : u ^ k ≤ (k ! : ℝ) * Real.exp u := by
  have := Real.pow_div_factorial_le_exp u hu k
  rw [div_le_iff₀ (by positivity)] at this
  linarith

/-- **`Φ` é um núcleo regular.** -/
theorem nucleo_Phi : Nucleo Phi Phid where
  deriv u hu := hasDerivAt_Phi hu
  cont0 := continuousOn_Phi 0 (mem_Ici.mpr le_rfl)
  pos u hu := Phi_pos (le_of_lt hu)
  intK k := by
    refine Integrable.mono' (ATK.XiPhi.integrableOn_exp_neg_mul
      ((k ! : ℝ) * (160 * Real.exp (1 * Real.sqrt 1)))) ?_ ?_
    · exact ((continuous_pow k).continuousOn.mul (continuousOn_Phi.mono Ioi_subset_Ici_self)
        ).aestronglyMeasurable measurableSet_Ioi
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      have hu0 : 0 ≤ u := le_of_lt hu
      have h1 := pow_le_fact_exp k hu0
      have h2 := Phi_exp_cota (y := 1) (by norm_num) hu0
      rw [one_mul] at h2
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hu0 k)]
      calc u ^ k * |Phi u| ≤ ((k ! : ℝ) * Real.exp u) * |Phi u| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = (k ! : ℝ) * (|Phi u| * Real.exp u) := by ring
        _ ≤ (k ! : ℝ) * (160 * Real.exp (1 * Real.sqrt 1) * Real.exp (-u)) := by gcongr
        _ = _ := by ring
  intK' k := by
    refine Integrable.mono' (ATK.XiPhi.integrableOn_exp_neg_mul
      ((k ! : ℝ) * (744 * ∑' n : ℕ, Real.exp (-(cN n / 2))))) ?_ ?_
    · exact ((continuous_pow k).continuousOn.mul (continuousOn_Phid.mono Ioi_subset_Ici_self)
        ).aestronglyMeasurable measurableSet_Ioi
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ?_
      have hu0 : 0 ≤ u := le_of_lt hu
      have h1 := pow_le_fact_exp k hu0
      have h2 := Phid_cota hu0
      have hS : 0 ≤ ∑' n : ℕ, Real.exp (-(cN n / 2)) := tsum_nonneg fun _ => (Real.exp_pos _).le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hu0 k)]
      have e : Real.exp u * Real.exp (-(2 * u)) = Real.exp (-u) := by rw [← Real.exp_add]; ring_nf
      calc u ^ k * |Phid u| ≤ ((k ! : ℝ) * Real.exp u) *
            (744 * (∑' n : ℕ, Real.exp (-(cN n / 2))) * Real.exp (-(2 * u))) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = (k ! : ℝ) * (744 * ∑' n : ℕ, Real.exp (-(cN n / 2))) * (Real.exp u * Real.exp (-(2 * u))) := by
            ring
        _ = _ := by rw [e]
  decay k := by
    have hb : ∀ u : ℝ, 0 ≤ u → ‖u ^ k * Phi u‖ ≤ ((k ! : ℝ) * (160 * Real.exp (1 * Real.sqrt 1))) *
        Real.exp (-u) := by
      intro u hu0
      have h1 := pow_le_fact_exp k hu0
      have h2 := Phi_exp_cota (y := 1) (by norm_num) hu0
      rw [one_mul] at h2
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hu0 k)]
      calc u ^ k * |Phi u| ≤ ((k ! : ℝ) * Real.exp u) * |Phi u| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = (k ! : ℝ) * (|Phi u| * Real.exp u) := by ring
        _ ≤ (k ! : ℝ) * (160 * Real.exp (1 * Real.sqrt 1) * Real.exp (-u)) := by gcongr
        _ = _ := by ring
    have ht : Tendsto (fun u : ℝ => ((k ! : ℝ) * (160 * Real.exp (1 * Real.sqrt 1))) * Real.exp (-u))
        atTop (𝓝 0) := by
      simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
        ((k ! : ℝ) * (160 * Real.exp (1 * Real.sqrt 1)))
    exact squeeze_zero_norm' (eventually_atTop.mpr ⟨0, fun u hu => hb u hu⟩) ht

/-! ## 4. Turán e PF₂ para `Ξ`, condicionais ao lema de Csordas (não a HR) -/

theorem gam_Phi (k : ℕ) : gam Phi k = (2 * k).factorial * aXi k / 2 := by
  have h := aXi_eq_mom k
  have hf : ((2 * k).factorial : ℝ) ≠ 0 := by positivity
  have hm : mom k = (2 * k).factorial * aXi k := by
    rw [h]
    field_simp
  have e : gam Phi k = mom k / 2 := by
    unfold gam mom
    have : (∫ u in Ioi (0 : ℝ), u ^ (2 * k) * Phi u) = ∫ u in Ioi (0 : ℝ), Phi u * u ^ (2 * k) := by
      congr 1
      funext u
      ring
    rw [this]
    ring
  rw [e, hm]

/-- **Turán nos `aₙ`, sem HR**: se `ψ_Φ = −Φ′/(uΦ)` é crescente (lema de Csordas, `BUILD_PENDING`),
`(n+2)aₙa_{n+2} ≤ (n+1)a_{n+1}²`. -/
theorem turan_a_de_csordas (hψ : MonotoneOn (fun u => -Phid u / (u * Phi u)) (Ioi 0)) (n : ℕ) :
    ((n : ℝ) + 2) * (aXi n * aXi (n + 2)) ≤ ((n : ℝ) + 1) * aXi (n + 1) ^ 2 := by
  have h := turan_disp nucleo_Phi hψ n
  rw [gam_Phi, gam_Phi, gam_Phi] at h
  set F : ℝ := ((2 * n).factorial : ℝ) with hFdef
  have hF : 0 < F := by positivity
  have e2 : ((2 * (n + 1)).factorial : ℝ) = (2 * n + 2) * (2 * n + 1) * F := by
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, hFdef]
    push_cast
    ring
  have e4 : ((2 * (n + 2)).factorial : ℝ) = (2 * n + 4) * (2 * n + 3) * (2 * n + 2) * (2 * n + 1) * F := by
    rw [show 2 * (n + 2) = 2 * n + 1 + 1 + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_succ, hFdef]
    push_cast
    ring
  rw [e2, e4] at h
  set P : ℝ := (2 * n + 1) ^ 2 * (2 * n + 2) * (2 * n + 3) * F ^ 2 / 2 with hP
  have hPpos : 0 < P := by positivity
  have h2 : P * (((n : ℝ) + 2) * (aXi n * aXi (n + 2))) ≤ P * (((n : ℝ) + 1) * aXi (n + 1) ^ 2) := by
    rw [hP]
    nlinarith [h]
  exact le_of_mul_le_mul_left h2 hPpos

/-- **Turán (forma `γ(k) = k!aₖ`), sem HR**: `γ(n)γ(n+2) ≤ γ(n+1)²` sob o lema de Csordas. -/
theorem turan_de_csordas (hψ : MonotoneOn (fun u => -Phid u / (u * Phi u)) (Ioi 0)) (n : ℕ) :
    γXi n * γXi (n + 2) ≤ γXi (n + 1) ^ 2 := by
  have key := turan_a_de_csordas hψ n
  unfold γXi
  set f : ℝ := (n.factorial : ℝ) with hfdef
  have hf : 0 < f := by positivity
  have e1 : ((n + 1).factorial : ℝ) = (n + 1) * f := by
    rw [Nat.factorial_succ, hfdef]; push_cast; ring
  have e2 : ((n + 2).factorial : ℝ) = (n + 2) * (n + 1) * f := by
    rw [show n + 2 = n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, hfdef]; push_cast; ring
  rw [e1, e2]
  have hm := mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) * f ^ 2)
  nlinarith [hm]

/-- **PF₂ dos coeficientes de `Ξ`, sem HR**: sob o lema de Csordas, todo menor `2 × 2` de `T(aₙ)` é `≥ 0`. -/
theorem pf2_de_csordas (hψ : MonotoneOn (fun u => -Phid u / (u * Phi u)) (Ioi 0))
    (I J : Fin 2 → ℕ) (hI : StrictMono I) (hJ : StrictMono J) :
    0 ≤ ((toep aXi).submatrix I J).det := by
  refine pf2_de_logconcava aXi_pos (fun n => ?_) I J hI hJ
  have key := turan_a_de_csordas hψ n
  have h1 : 0 ≤ aXi n * aXi (n + 2) := (mul_pos (aXi_pos n) (aXi_pos (n + 2))).le
  nlinarith [key, h1]

end ATK.TuranDisp

#print axioms ATK.TuranDisp.ibp
#print axioms ATK.TuranDisp.turan_disp
#print axioms ATK.TuranDisp.razao_lc
#print axioms ATK.TuranDisp.pf2_de_logconcava
#print axioms ATK.TuranDisp.continuous_phiTd
#print axioms ATK.TuranDisp.hasDerivAt_phiT
#print axioms ATK.TuranDisp.cN_ge3
#print axioms ATK.TuranDisp.phiTd_cota
#print axioms ATK.TuranDisp.phiTd_cota'
#print axioms ATK.TuranDisp.hasDerivAt_Phi
#print axioms ATK.TuranDisp.Phid_cota
#print axioms ATK.TuranDisp.continuousOn_Phid
#print axioms ATK.TuranDisp.pow_le_fact_exp
#print axioms ATK.TuranDisp.nucleo_Phi
#print axioms ATK.TuranDisp.gam_Phi
#print axioms ATK.TuranDisp.turan_a_de_csordas
#print axioms ATK.TuranDisp.turan_de_csordas
#print axioms ATK.TuranDisp.pf2_de_csordas
