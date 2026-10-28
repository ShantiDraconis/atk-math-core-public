import ATK.EdreiInteira
import ATK.BaseRiemannXiSinal

/-!
# ATK — PF∞ dos coeficientes de `Ξ` implica HR (no kernel, sem hipótese oculta)

`g(z) = ξ(1/2 + iz)` é inteira e par; seus coeficientes de Taylor `d_k` são reais (`dXi_real`, por
unicidade de séries de potências) e os ímpares se anulam (`iteratedDeriv_gXi_odd`). Com
`aₙ = (−1)ⁿ d_{2n}` (`aXi`), a função inteira `B(w) = Σ aₙwⁿ` satisfaz **`B(−z²) = g(z)`** (`ev_aXi`), e
`a₀ = Ξ(0) > 0`.

**Teorema (`rh_de_tn`)**: se a matriz de Toeplitz `T(aₙ)` é totalmente não negativa (`aₙ` é uma
sequência de Pólya, PF∞), então vale a Hipótese de Riemann (`RiemannHypothesis` do Mathlib).

Prova: um zero `z` de `g` dá o zero `−z²` de `B`; por `ATK.Edrei.edrei_inteira`, `−z²` é real negativo,
logo `z` é real; e `RH ⟺ zeros de g reais` (`ATK.BaseRiemannXi.riemannHypothesis_iff_Xi`).

**Estado**: a hipótese `(toep aXi).IsTotallyNonneg` é **`OPEN_MATH`** — é equivalente a HR (a volta
precisa da fatoração de Hadamard de gênero 0 de `B`: `ATK/HadamardGenero0.lean` e `ATK.XiCresc.rh_iff_tn`,
rodada 11). Este arquivo prova a implicação, não a hipótese.
-/

open Complex Filter Topology Finset
open scoped Nat

namespace ATK.XiTP

open ATK.BaseRiemannXi
open ATK.Edrei
open ATK.ToeplitzTN (toep)

/-! ## 1. `g(z) = ξ(1/2 + iz)` -/

noncomputable def gXi (z : ℂ) : ℂ := riemannXi (1 / 2 + z * I)

theorem gXi_differentiable : Differentiable ℂ gXi := by
  unfold gXi
  exact differentiable_riemannXi.comp
    ((differentiable_const _).add (differentiable_id.mul (differentiable_const _)))

theorem gXi_neg (z : ℂ) : gXi (-z) = gXi z := by
  unfold gXi
  rw [← riemannXi_one_sub]
  congr 1
  ring

theorem gXi_ofReal (t : ℝ) : gXi t = (Xi t : ℂ) := riemannXi_critical t

/-! ## 2. Coeficientes de Taylor -/

/-- `d_k = g^{(k)}(0)/k!`. -/
noncomputable def dXi (k : ℕ) : ℂ := (k ! : ℂ)⁻¹ * iteratedDeriv k gXi 0

theorem hasSum_dXi (z : ℂ) : HasSum (fun k => dXi k * z ^ k) (gXi z) := by
  have h := Complex.hasSum_taylorSeries_of_entire gXi_differentiable 0 z
  convert h using 1
  funext k
  simp only [dXi, sub_zero, smul_eq_mul]
  ring

theorem iteratedDeriv_gXi_odd (k : ℕ) : iteratedDeriv (2 * k + 1) gXi 0 = 0 := by
  have h := iteratedDeriv_comp_neg (2 * k + 1) gXi 0
  have e : (fun x => gXi (-x)) = gXi := funext gXi_neg
  rw [e, neg_zero, smul_eq_mul, Odd.neg_one_pow ⟨k, rfl⟩] at h
  linear_combination h / 2

theorem dXi_odd (k : ℕ) : dXi (2 * k + 1) = 0 := by
  rw [dXi, iteratedDeriv_gXi_odd, mul_zero]

theorem dXi_zero : dXi 0 = gXi 0 := by
  simp [dXi]

theorem summable_norm_dXi (R : ℝ) (hR : 0 ≤ R) : Summable fun k => ‖dXi k‖ * R ^ k := by
  set S : ℝ := R + 1 with hSdef
  have hS : 0 < S := by positivity
  have ht := (hasSum_dXi (S : ℂ)).summable.tendsto_atTop_zero
  have hev : ∀ᶠ k in atTop, ‖dXi k * (S : ℂ) ^ k‖ ≤ 1 :=
    (tendsto_norm_zero.comp ht).eventually_le_const zero_lt_one
  have hgeo : Summable fun k : ℕ => (R / S) ^ k :=
    summable_geometric_of_lt_one (div_nonneg hR hS.le) ((div_lt_one hS).mpr (by linarith))
  refine Summable.of_norm_bounded_eventually hgeo ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hev] with k hk
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hS.le] at hk
  rw [Real.norm_of_nonneg (by positivity), div_pow]
  have hSk : 0 < S ^ k := pow_pos hS k
  rw [le_div_iff₀ hSk]
  calc ‖dXi k‖ * R ^ k * S ^ k = (‖dXi k‖ * S ^ k) * R ^ k := by ring
    _ ≤ 1 * R ^ k := mul_le_mul_of_nonneg_right hk (pow_nonneg hR _)
    _ = R ^ k := one_mul _

/-! ## 3. Unicidade de séries de potências reais e realidade dos `d_k` -/

/-- Uma série de potências inteira que se anula em toda a reta tem todos os coeficientes nulos. -/
theorem coef_zero_of_hasSum_zero {e : ℕ → ℝ} (he : Inteira e)
    (h : ∀ t : ℝ, HasSum (fun k => e k * t ^ k) 0) : ∀ k, e k = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  have hs1 : Summable fun m => |e (m + k)| :=
    (summable_nat_add_iff (f := fun j => |e j|) k).mpr ((he 1 zero_le_one).congr fun j => by simp)
  have htail : ∀ t : ℝ, t ≠ 0 → ∑' m, e (m + k) * t ^ m = 0 := by
    intro t ht
    have hs : Summable fun j => e j * t ^ j := (h t).summable
    have h1 := hs.sum_add_tsum_nat_add k
    rw [(h t).tsum_eq, Finset.sum_eq_zero (fun j hj => by rw [ih j (Finset.mem_range.mp hj), zero_mul]),
      zero_add] at h1
    have e2 : ∑' m, e (m + k) * t ^ (m + k) = t ^ k * ∑' m, e (m + k) * t ^ m := by
      rw [← tsum_mul_left]
      congr 1
      funext m
      ring
    rw [e2] at h1
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ ht)
  set F : ℝ → ℝ := fun t => ∑' m, e (m + k) * t ^ m with hF
  have hcont : ContinuousOn F (Set.Icc (-1) 1) := by
    refine continuousOn_tsum (u := fun m => |e (m + k)|)
      (fun m => (continuous_const.mul (continuous_pow m)).continuousOn) hs1 ?_
    intro m t ht
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    calc |e (m + k)| * |t| ^ m ≤ |e (m + k)| * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) this) (abs_nonneg _)
      _ = |e (m + k)| := mul_one _
  have h0 : F 0 = e k := by
    simp only [hF]
    rw [tsum_eq_single 0]
    · simp
    · intro m hm
      simp [zero_pow hm]
  have hseq : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝[Set.Icc (-1) 1] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun n => ?_⟩
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hq : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    exact ⟨by linarith, hq⟩
  have hlim := ((hcont (0 : ℝ) (by norm_num)).tendsto).comp hseq
  rw [h0] at hlim
  have hz : F ∘ (fun n : ℕ => (1 : ℝ) / (n + 1)) = fun _ => 0 := by
    funext n
    exact htail _ (by positivity)
  rw [hz] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

theorem dXi_im (k : ℕ) : (dXi k).im = 0 := by
  have he : Inteira fun k => (dXi k).im := by
    intro R hR
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (summable_norm_dXi R hR)
    exact mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm _) (pow_nonneg hR _)
  refine coef_zero_of_hasSum_zero he (fun t => ?_) k
  have h := Complex.hasSum_im (hasSum_dXi (t : ℂ))
  rw [gXi_ofReal, Complex.ofReal_im] at h
  convert h using 1
  funext j
  rw [← Complex.ofReal_pow, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]

theorem dXi_real (k : ℕ) : ((dXi k).re : ℂ) = dXi k :=
  Complex.ext (by simp) (by simp [dXi_im])

/-! ## 4. `B(w) = Σ aₙwⁿ` com `B(−z²) = g(z)` -/

/-- `aₙ = (−1)ⁿ d_{2n}`: `Ξ(t) = Σ (−1)ⁿ aₙ t^{2n}`, `B(w) = Σ aₙ wⁿ`. -/
noncomputable def aXi (n : ℕ) : ℝ := (-1) ^ n * (dXi (2 * n)).re

theorem inteira_aXi : Inteira aXi := by
  intro R hR
  have hs := (summable_norm_dXi (Real.sqrt R) (Real.sqrt_nonneg R)).comp_injective
    (fun a b (h : 2 * a = 2 * b) => by omega)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  simp only [Function.comp, aXi]
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, pow_mul, Real.sq_sqrt hR]
  exact mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) (pow_nonneg hR _)

theorem aXi_zero : aXi 0 = Xi 0 := by
  simp only [aXi, pow_zero, one_mul, mul_zero, dXi_zero]
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, gXi_ofReal, Complex.ofReal_re]

theorem aXi_zero_pos : 0 < aXi 0 := by
  rw [aXi_zero]
  exact ATK.BaseRiemannXiSinal.Xi_zero_pos

theorem ev_aXi (z : ℂ) : ev aXi (-z ^ 2) = gXi z := by
  have h := hasSum_dXi z
  have hinj : Function.Injective fun n : ℕ => 2 * n := fun a b (h : 2 * a = 2 * b) => by omega
  have hodd : ∀ k, k ∉ Set.range (fun n : ℕ => 2 * n) → dXi k * z ^ k = 0 := by
    intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := by
      rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact absurd ⟨m, by show 2 * m = k; omega⟩ hk
      · exact ⟨m, hm⟩
    rw [dXi_odd, zero_mul]
  have h2 := (hinj.hasSum_iff hodd).mpr h
  unfold ev
  rw [← h2.tsum_eq]
  congr 1
  funext n
  simp only [Function.comp, aXi]
  rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one, dXi_real,
    neg_pow (z ^ 2) n, ← pow_mul]
  have : ((-1 : ℂ)) ^ n * (-1) ^ n = 1 := by rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (dXi (2 * n) * z ^ (2 * n)) * this

/-! ## 5. O teorema -/

/-- **PF∞ dos coeficientes de `Ξ` ⇒ HR.** Se `T(aₙ)` é totalmente não negativa — todos os menores
`det(a_{i_p − j_q}) ≥ 0` — então vale a Hipótese de Riemann. A hipótese é `OPEN_MATH`. -/
theorem rh_de_tn (h : (toep aXi).IsTotallyNonneg) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_Xi]
  intro z hz
  have hw : ev aXi (-z ^ 2) = 0 := by rw [ev_aXi]; exact hz
  obtain ⟨him, hre⟩ := edrei_inteira inteira_aXi aXi_zero_pos h hw
  have him' : z.re * z.im = 0 := by
    simp only [neg_im, sq, Complex.mul_im] at him
    linarith
  have hre' : z.im * z.im < z.re * z.re := by
    simp only [neg_re, sq, Complex.mul_re] at hre
    linarith
  rcases mul_eq_zero.mp him' with h1 | h1
  · rw [h1] at hre'
    nlinarith [mul_self_nonneg z.im]
  · exact h1

/-- Forma explícita dos menores: se todo menor de Toeplitz dos `aₙ` é `≥ 0`, vale HR. -/
theorem rh_de_menores
    (h : ∀ (r : ℕ) (I J : Fin r → ℕ), StrictMono I → StrictMono J →
      0 ≤ (Matrix.of fun p q => if J q ≤ I p then aXi (I p - J q) else 0).det) :
    RiemannHypothesis :=
  rh_de_tn fun r I J hI hJ => by
    have := h r I J hI hJ
    convert this using 2
    ext p q
    simp [toep, Matrix.submatrix_apply]

end ATK.XiTP

#print axioms ATK.XiTP.gXi_differentiable
#print axioms ATK.XiTP.gXi_neg
#print axioms ATK.XiTP.gXi_ofReal
#print axioms ATK.XiTP.hasSum_dXi
#print axioms ATK.XiTP.iteratedDeriv_gXi_odd
#print axioms ATK.XiTP.dXi_odd
#print axioms ATK.XiTP.dXi_zero
#print axioms ATK.XiTP.summable_norm_dXi
#print axioms ATK.XiTP.coef_zero_of_hasSum_zero
#print axioms ATK.XiTP.dXi_im
#print axioms ATK.XiTP.dXi_real
#print axioms ATK.XiTP.inteira_aXi
#print axioms ATK.XiTP.aXi_zero
#print axioms ATK.XiTP.aXi_zero_pos
#print axioms ATK.XiTP.ev_aXi
#print axioms ATK.XiTP.rh_de_tn
#print axioms ATK.XiTP.rh_de_menores
