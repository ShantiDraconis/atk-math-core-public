import ATK.ZeroClasses.TuranLiouville

/-!
# Primos em intervalos curtos: `Θ`, RH e o TNP (rodada 101)

* `existe_primo_of_theta_lt`: se `θ(x) < θ(y)`, há primo em `(x, y]`.
* **`primo_curto_Teta`**: para todo `θ > Θ`, há primo em `(x, x + x^θ]` para `x` grande. Logo
  `p_{n+1} − p_n ≪ p_n^{Θ+ε}`. Para `θ ≥ 1` é Bertrand (Mathlib). Para `θ < 1`, sai de `θ(x) = x + O(x^{t+ε})`,
  `Θ ≤ t < θ` (rodada 60).
* **`primo_curto_RH`**: sob RH, há primo em `(x, x + C√x log³ x]` para `x` grande. Sai da cota
  `θ(x) = x + O(√x log³ x)` da rodada 65. Cramér (1920) tem `√x log x`.
* **`primo_curto_tnp`** (sem hipóteses): existe `c > 0` com primo em `(x, x + x e^{−c√log x}]` para `x` grande, isto
  é, `p_{n+1} − p_n ≪ p_n e^{−c√log p_n}`. Sai do resto de de la Vallée Poussin no TNP
  (`PNT.psi_tnp`, rodada 53) e de `ψ − θ ≤ C√x`: com `h = x e^{−c√log x}` e `c = b/2`, os dois restos ficam abaixo
  de `h/2` (`theta_tnp`, `parte_a`, `combina`).

Classificação: **consequência**, e as três formas são clássicas: a de `Θ` é imediata da cota de `θ(x) − x`; a de RH é
uma versão mais fraca da de Cramér (1920); a sem hipóteses vem do resto de de la Vallée Poussin. Nada aqui chega a
`p_{n+1} − p_n ≪ p_n^{0,525}` (Baker–Harman–Pintz 2001), que usa estimativas de densidade de zeros. Também não chega
à conjectura de Cramér, `O(log² p)`. RH continua OPEN_MATH.
-/

open Filter
open scoped Real

namespace ATK.ZeroClasses.PrimosCurtos

open ATK.ZeroClasses.BDTheta (Teta Teta_le_iff Teta_le_um meio_le_Teta)
open ATK.ZeroClasses.PiLi (semZeros_iff_theta)

/-! ## 1. `θ(y) > θ(x)` dá um primo em `(x, y]` -/

theorem existe_primo_of_theta_lt {x y : ℝ} (h : Chebyshev.theta x < Chebyshev.theta y) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ y := by
  by_contra hne
  push Not at hne
  have hsub : (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime ⊆ (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    obtain ⟨⟨hp0, hpy⟩, hpp⟩ := hp
    refine ⟨⟨hp0, ?_⟩, hpp⟩
    have hy0 : 0 ≤ y := by
      by_contra hy
      push Not at hy
      rw [Nat.floor_eq_zero.mpr (by linarith)] at hpy
      omega
    have hpy' : (p : ℝ) ≤ y := (Nat.cast_le.mpr hpy).trans (Nat.floor_le hy0)
    by_contra hpx
    push Not at hpx
    have hxp : x < p := by
      by_contra hle
      push Not at hle
      exact absurd (Nat.le_floor hle) (by omega)
    linarith [hne p hpp hxp]
  have : Chebyshev.theta y ≤ Chebyshev.theta x := by
    unfold Chebyshev.theta
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => Real.log_nonneg (by
      have := (Finset.mem_filter.mp hp).2.one_lt
      exact_mod_cast this.le)
  linarith

/-! ## 2. `θ > Θ`: há primo em `(x, x + x^θ]` para `x` grande -/

/-- **Para todo `θ > Θ`, há primo em `(x, x + x^θ]` para `x` grande.** Em particular
`p_{n+1} − p_n ≪ p_n^{Θ+ε}`. -/
theorem primo_curto_Teta {θ : ℝ} (hθ : Teta < θ) :
    ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x ^ θ := by
  rcases le_or_gt 1 θ with h1 | h1
  · -- Bertrand
    refine ⟨1, fun x hx => ?_⟩
    have hn : ⌊x⌋₊ ≠ 0 := by
      have := Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ x by simpa using hx)
      omega
    obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul ⌊x⌋₊ hn
    refine ⟨p, hp, ?_, ?_⟩
    · have := Nat.lt_floor_add_one x
      have h2 : ((⌊x⌋₊ : ℕ) : ℝ) + 1 ≤ p := by exact_mod_cast hlt
      linarith
    · have h2 : (p : ℝ) ≤ 2 * ⌊x⌋₊ := by exact_mod_cast hle
      have h3 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
      have h4 : x ≤ x ^ θ := by
        simpa using Real.rpow_le_rpow_of_exponent_le hx h1
      linarith
  · set t := (Teta + θ) / 2 with ht
    have hm := meio_le_Teta
    have ht1 : 1 / 2 ≤ t := by rw [ht]; linarith
    have ht2 : t < 1 := by rw [ht]; linarith [Teta_le_um]
    have hT : Teta ≤ t := by rw [ht]; linarith
    set b := t + (θ - t) / 2 with hb
    have hbθ : b < θ := by rw [hb]; linarith
    have hb0 : 0 ≤ b := by rw [hb]; linarith
    have hb1 : b ≤ 1 := by rw [hb]; linarith
    obtain ⟨C, hC⟩ := (semZeros_iff_theta ht1 ht2).mp ((Teta_le_iff ht1).mp hT) ((θ - t) / 2) (by linarith)
    have hC0 : 0 ≤ C := by
      have h := hC 2 le_rfl
      have hp : 0 < (2 : ℝ) ^ (t + (θ - t) / 2) := by positivity
      by_contra hneg
      push Not at hneg
      nlinarith [abs_nonneg (Chebyshev.theta 2 - 2)]
    have hev : ∀ᶠ x : ℝ in atTop, 3 * C + 1 ≤ x ^ (θ - b) :=
      (tendsto_rpow_atTop (by linarith)).eventually_ge_atTop _
    obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp hev
    refine ⟨max X₁ 2, fun x hx => ?_⟩
    have hx2 : 2 ≤ x := le_trans (le_max_right _ _) hx
    have hx0 : 0 < x := by linarith
    have hxb := hX₁ x (le_trans (le_max_left _ _) hx)
    set h := x ^ θ with hh
    have hhx : h ≤ x := by simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ x) h1.le
    have hpos : 0 < h := Real.rpow_pos_of_pos hx0 _
    set y := x + h with hy
    have hy2 : 2 ≤ y := by linarith
    have hCx := hC x hx2
    have hCy := hC y hy2
    have hyb : y ^ b ≤ 2 * x ^ b := by
      have : y ^ b ≤ (2 * x) ^ b := Real.rpow_le_rpow (by linarith) (by linarith) hb0
      rw [Real.mul_rpow (by norm_num) hx0.le] at this
      have h2b : (2 : ℝ) ^ b ≤ 2 := by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hb1
      nlinarith [Real.rpow_nonneg hx0.le b]
    have hsplit : h = x ^ (θ - b) * x ^ b := by
      rw [hh, ← Real.rpow_add hx0]; ring_nf
    have hxb0 : 0 ≤ x ^ b := Real.rpow_nonneg hx0.le b
    have hbig : 3 * C * x ^ b < h := by
      rw [hsplit]
      have : (3 * C + 1) * x ^ b ≤ x ^ (θ - b) * x ^ b := mul_le_mul_of_nonneg_right hxb hxb0
      have hxb1 : 0 < x ^ b := Real.rpow_pos_of_pos hx0 b
      nlinarith
    have hlt : Chebyshev.theta x < Chebyshev.theta y := by
      rw [abs_le] at hCx hCy
      nlinarith [hCx.1, hCx.2, hCy.1, hCy.2]
    exact existe_primo_of_theta_lt hlt

/-! ## 3. Sob RH: primo em `(x, x + C√x log³ x]` -/

/-- `C√x log³ x ≤ x` para `x ≥ max 2 (1728C)⁴`. -/
theorem raiz_log3_le {C x : ℝ} (hC : 0 ≤ C) (hx : max 2 ((1728 * C) ^ 4) ≤ x) :
    C * √x * Real.log x ^ 3 ≤ x := by
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hl := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1 / 12)
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hq : 0 ≤ x ^ (1 / 12 : ℝ) := Real.rpow_nonneg hx0.le _
  have hl3 : Real.log x ^ 3 ≤ 1728 * x ^ (1 / 4 : ℝ) := by
    have e : x ^ (1 / 4 : ℝ) = (x ^ (1 / 12 : ℝ)) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    rw [e]
    have : Real.log x ≤ 12 * x ^ (1 / 12 : ℝ) := by
      rw [div_div_eq_mul_div, div_one] at hl; linarith
    calc Real.log x ^ 3 ≤ (12 * x ^ (1 / 12 : ℝ)) ^ 3 := pow_le_pow_left₀ hl0 this 3
      _ = 1728 * (x ^ (1 / 12 : ℝ)) ^ 3 := by ring
  have h4 : 1728 * C ≤ x ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hx) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), show ((4 : ℕ) : ℝ) * (1 / 4) = 1 by norm_num,
      Real.rpow_one] at h
  have hs : √x = x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; norm_num
  have hx1 : x = x ^ (1 / 4 : ℝ) * (x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
  have hq4 : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx0.le _
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  calc C * √x * Real.log x ^ 3 ≤ C * √x * (1728 * x ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hl3 (by positivity)
    _ = (1728 * C) * (x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) := by rw [hs]; ring
    _ ≤ x ^ (1 / 4 : ℝ) * (x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right h4 (by positivity)
    _ = x := hx1.symm

/-- **Sob RH, há primo em `(x, x + C√x log³ x]` para `x` grande** (Cramér 1920 tem `√x log x`; aqui sai da cota
`θ(x) = x + O(√x log³ x)` da rodada 65). -/
theorem primo_curto_RH (hRH : RiemannHypothesis) :
    ∃ C X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + C * √x * Real.log x ^ 3 := by
  obtain ⟨K, hK⟩ := ATK.ZeroClasses.PiLiRH.theta_RH hRH
  have hK0 : 0 ≤ K := by
    have h := hK 2 le_rfl
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hp : 0 < √(2 : ℝ) * Real.log 2 ^ 3 := by positivity
    by_contra hneg
    push Not at hneg
    have : K * √2 * Real.log 2 ^ 3 < 0 := by
      have := mul_neg_of_neg_of_pos hneg hp
      linarith [show K * √2 * Real.log 2 ^ 3 = K * (√2 * Real.log 2 ^ 3) by ring]
    linarith [abs_nonneg (Chebyshev.theta 2 - 2)]
  set C := 17 * K + 1 with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; linarith
  refine ⟨C, max 2 ((1728 * C) ^ 4), fun x hx => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hhx := raiz_log3_le hC0 hx
  set h := C * √x * Real.log x ^ 3 with hh
  set y := x + h with hy
  have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hS : 0 < √x * Real.log x ^ 3 := by have := Real.sqrt_pos.mpr hx0; positivity
  have hh0 : 0 ≤ h := by rw [hh]; positivity
  have hy2 : 2 ≤ y := by linarith
  have hyx : y ≤ 2 * x := by linarith
  -- `√y ≤ 2√x` e `log y ≤ 2 log x`
  have hsy : √y ≤ 2 * √x := by
    have h1 : √y ≤ √(2 * x) := Real.sqrt_le_sqrt hyx
    rw [Real.sqrt_mul (by norm_num)] at h1
    have : √(2 : ℝ) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg x]
  have hly : Real.log y ≤ 2 * Real.log x := by
    have h1 : Real.log y ≤ Real.log (2 * x) := Real.log_le_log (by linarith) hyx
    rw [Real.log_mul (by norm_num) hx0.ne'] at h1
    have : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx2
    linarith
  have hly0 : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hly3 : Real.log y ^ 3 ≤ 8 * Real.log x ^ 3 := by
    have := pow_le_pow_left₀ hly0 hly 3
    linarith [show (2 * Real.log x) ^ 3 = 8 * Real.log x ^ 3 by ring]
  have hEy : K * √y * Real.log y ^ 3 ≤ 16 * K * (√x * Real.log x ^ 3) := by
    have h1 : √y * Real.log y ^ 3 ≤ (2 * √x) * (8 * Real.log x ^ 3) :=
      mul_le_mul hsy hly3 (by positivity) (by positivity)
    nlinarith
  have hCx := hK x hx2
  have hCy := hK y hy2
  rw [abs_le] at hCx hCy
  have hlt : Chebyshev.theta x < Chebyshev.theta y := by
    have e : h = C * (√x * Real.log x ^ 3) := by rw [hh]; ring
    have e2 : K * √x * Real.log x ^ 3 = K * (√x * Real.log x ^ 3) := by ring
    nlinarith [hCx.1, hCx.2, hCy.1, hCy.2]
  exact existe_primo_of_theta_lt hlt

/-! ## 4. Sem hipóteses: primo em `(x, x + x e^{−c√log x}]` (pelo TNP com resto) -/

/-- `|θ(x) − x| ≤ K x e^{−b√log x} + C√x` para `x` grande (o TNP da rodada 53 e `ψ − θ ≤ C√x`). -/
theorem theta_tnp : ∃ b > 0, ∃ K C X₁ : ℝ, 0 ≤ K ∧ 0 ≤ C ∧ ∀ x : ℝ, X₁ ≤ x →
    |Chebyshev.theta x - x| ≤ K * x * Real.exp (-(b * √(Real.log x))) + C * √x := by
  obtain ⟨b, hb, K, hK⟩ := ATK.ZeroClasses.PNT.psi_tnp
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp hK
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨b, hb, max K 0, max C 0, max X₁ 1, le_max_right _ _, le_max_right _ _, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have h1 := hX₁ x (le_trans (le_max_left _ _) hx)
  have h2 := hC x
  have h3 := Chebyshev.theta_le_psi x
  have he : 0 ≤ x * Real.exp (-(b * √(Real.log x))) := by positivity
  have hs : 0 ≤ √x := Real.sqrt_nonneg x
  have hK' : K * x * Real.exp (-(b * √(Real.log x))) ≤ max K 0 * x * Real.exp (-(b * √(Real.log x))) := by
    rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) he
  have hC' : C * √x ≤ max C 0 * √x := mul_le_mul_of_nonneg_right (le_max_left _ _) hs
  have hC0 : 0 ≤ max C 0 * √x := mul_nonneg (le_max_right _ _) hs
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

/-- A combinação final, isolada: se `θ(x) ≤ x + A + B`, `θ(y) ≥ y − 2A − 2B`, `y = x + h`, `3A < h/2` e
`6B ≤ h`, então `θ(x) < θ(y)`. -/
theorem combina {tx ty x y h A B : ℝ} (hx : tx ≤ x + A + B) (hy : y - 2 * A - 2 * B ≤ ty) (hyh : y = x + h)
    (hA : 3 * A < h / 2) (hB : 6 * B ≤ h) : tx < ty := by
  linarith

/-- `e^{−cu}(6K + 1) ≤ 1` ⟹ `3K x e^{−2cu} < (x e^{−cu})/2` para `x > 0`. -/
theorem parte_a {K x e : ℝ} (_hK : 0 ≤ K) (hx : 0 < x) (he : 0 < e) (h : e * (6 * K + 1) ≤ 1) :
    3 * K * (x * (e * e)) < x * e / 2 := by
  have h1 : 6 * K * e < 1 := by nlinarith
  have hxe : 0 < x * e := mul_pos hx he
  have e1 : 3 * K * (x * (e * e)) = (6 * K * e) * (x * e / 2) := by ring
  rw [e1]
  have : 0 < x * e / 2 := by positivity
  nlinarith

/-- **Sem hipóteses: há `c > 0` com primo em `(x, x + x e^{−c√log x}]` para `x` grande**, isto é,
`p_{n+1} − p_n ≪ p_n e^{−c√log p_n}` (pelo resto de de la Vallée Poussin no TNP). -/
theorem primo_curto_tnp : ∃ c > 0, ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x →
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + x * Real.exp (-(c * √(Real.log x))) := by
  obtain ⟨b, hb, K, C, X₁, hK0, hC0, hE⟩ := theta_tnp
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = b / 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; linarith
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log (6 * C + 1) := ⟨_, rfl⟩
  have hL0 : 0 ≤ L := by rw [hL]; exact Real.log_nonneg (by linarith)
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = max (max (Real.log (6 * K + 1) / c) (4 * c)) (2 * √L) := ⟨_, rfl⟩
  refine ⟨c, hc0, max (max X₁ 2) (Real.exp (U ^ 2)), fun x hx => ?_⟩
  have hx2 : 2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx0 : 0 < x := by linarith
  have hxX : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = √(Real.log x) := ⟨_, rfl⟩
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hu2 : u ^ 2 = Real.log x := by rw [hu]; exact Real.sq_sqrt hlx0
  have hu0 : 0 ≤ u := by rw [hu]; exact Real.sqrt_nonneg _
  have hUu : U ≤ u := by
    have h1 : Real.exp (U ^ 2) ≤ x := le_trans (le_max_right _ _) hx
    have h2 : U ^ 2 ≤ Real.log x := by rw [Real.le_log_iff_exp_le hx0]; exact h1
    rw [hu]; exact Real.le_sqrt_of_sq_le h2
  have hu1 : Real.log (6 * K + 1) / c ≤ u := by
    rw [hU] at hUu; exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hUu
  have hu3 : 4 * c ≤ u := by
    rw [hU] at hUu; exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hUu
  have hu4 : 2 * √L ≤ u := by rw [hU] at hUu; exact le_trans (le_max_right _ _) hUu
  have hsx : √x = Real.exp (u ^ 2 / 2) := by
    have hxe : x = Real.exp (u ^ 2) := by rw [hu2, Real.exp_log hx0]
    rw [hxe, Real.sqrt_eq_rpow, ← Real.exp_mul]; ring_nf
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = Real.exp (-(c * u)) := ⟨_, rfl⟩
  have he0 : 0 < e := by rw [he]; exact Real.exp_pos _
  have he1 : e ≤ 1 := by rw [he, Real.exp_le_one_iff]; nlinarith
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = x * e := ⟨_, rfl⟩
  have hh0 : 0 < h := by rw [hh]; positivity
  have hhx : h ≤ x := by rw [hh]; nlinarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = x + h := ⟨_, rfl⟩
  have hy2 : 2 ≤ y := by linarith
  have hyX : X₁ ≤ y := by linarith
  have hbu : Real.exp (-(b * u)) = e * e := by
    rw [he, ← Real.exp_add, hc]; ring_nf
  -- o resto em `y` é dominado pelo de `x`
  have hexp : Real.exp (-(b * √(Real.log y))) ≤ e * e := by
    rw [← hbu, Real.exp_le_exp, neg_le_neg_iff, hu]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Real.log_le_log hx0 (by linarith))) hb.le
  have hsy : √y ≤ 2 * √x := by
    have h1 : √y ≤ √(2 * x) := Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_mul (by norm_num)] at h1
    have : √(2 : ℝ) ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg x]
  have hEx := hE x hxX
  have hEy := hE y hyX
  rw [← hu, hbu] at hEx
  rw [abs_le] at hEx hEy
  -- (a)
  have hecu : e * (6 * K + 1) ≤ 1 := by
    have h1 : Real.log (6 * K + 1) ≤ c * u := by rw [div_le_iff₀ hc0] at hu1; linarith
    have h2 : 6 * K + 1 ≤ Real.exp (c * u) := by
      calc 6 * K + 1 = Real.exp (Real.log (6 * K + 1)) := (Real.exp_log (by linarith)).symm
        _ ≤ Real.exp (c * u) := Real.exp_le_exp.mpr h1
    rw [he, Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _), mul_one]
    exact h2
  have ha := parte_a hK0 hx0 he0 hecu
  -- (b)
  have hb2 : 6 * C + 1 ≤ √x * e := by
    rw [hsx, he, ← Real.exp_add]
    have hq : L ≤ u ^ 2 / 2 + -(c * u) := by
      have h1 : 4 * L ≤ u ^ 2 := by
        have : (2 * √L) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hu4 2
        rw [mul_pow, Real.sq_sqrt hL0] at this; linarith
      nlinarith
    calc 6 * C + 1 = Real.exp L := by rw [hL, Real.exp_log (by linarith)]
      _ ≤ Real.exp (u ^ 2 / 2 + -(c * u)) := Real.exp_le_exp.mpr hq
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  have hb3 : 6 * (C * √x) ≤ h := by
    have e1 : h = √x * (√x * e) := by rw [hh, ← mul_assoc, Real.mul_self_sqrt hx0.le]
    rw [e1]
    have : 6 * C * √x ≤ √x * (√x * e) := by nlinarith
    linarith
  -- as duas cotas
  have hKy : K * y * Real.exp (-(b * √(Real.log y))) ≤ 2 * (K * (x * (e * e))) := by
    have h1 : y * Real.exp (-(b * √(Real.log y))) ≤ (2 * x) * (e * e) :=
      mul_le_mul (by linarith) hexp (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_left h1 hK0
    linarith [show K * (y * Real.exp (-(b * √(Real.log y)))) = K * y * Real.exp (-(b * √(Real.log y))) by ring,
      show K * (2 * x * (e * e)) = 2 * (K * (x * (e * e))) by ring]
  have hCy : C * √y ≤ 2 * (C * √x) := by
    have := mul_le_mul_of_nonneg_left hsy hC0
    linarith
  have hx' : Chebyshev.theta x ≤ x + K * (x * (e * e)) + C * √x := by
    have := hEx.2
    linarith [show K * x * (e * e) = K * (x * (e * e)) by ring]
  have hy' : y - 2 * (K * (x * (e * e))) - 2 * (C * √x) ≤ Chebyshev.theta y := by
    have := hEy.1
    linarith
  have ha' : 3 * (K * (x * (e * e))) < h / 2 := by
    rw [hh, show 3 * (K * (x * (e * e))) = 3 * K * (x * (e * e)) by ring]
    exact ha
  have hlt := combina hx' hy' hy ha' hb3
  obtain ⟨p, hp, hxp, hpy⟩ := existe_primo_of_theta_lt hlt
  refine ⟨p, hp, hxp, ?_⟩
  rw [hy, hh, he, hu] at hpy
  exact hpy

end ATK.ZeroClasses.PrimosCurtos

#print axioms ATK.ZeroClasses.PrimosCurtos.existe_primo_of_theta_lt
#print axioms ATK.ZeroClasses.PrimosCurtos.primo_curto_Teta
#print axioms ATK.ZeroClasses.PrimosCurtos.raiz_log3_le
#print axioms ATK.ZeroClasses.PrimosCurtos.primo_curto_RH
#print axioms ATK.ZeroClasses.PrimosCurtos.theta_tnp
#print axioms ATK.ZeroClasses.PrimosCurtos.combina
#print axioms ATK.ZeroClasses.PrimosCurtos.parte_a
#print axioms ATK.ZeroClasses.PrimosCurtos.primo_curto_tnp
