import ATK.ZeroClasses.ExplicitaPecas
import ATK.LiCriterio

/-!
# O critério de Li completo: RH ⟺ `λ_n ≥ 0` para todo `n ≥ 1` (rodada 68)

**Teorema** (Li, 1997; Bombieri–Lagarias, 1999). Com

  `λ_n = Σ_{(ρ,j)} Re(1 − (1 − 1/ρ)^n)`

(soma sobre os zeros não triviais com multiplicidade, `ZM`, absolutamente convergente: `summable_termo`),

  **`rh_iff_li : RiemannHypothesis ↔ ∀ n ≥ 1, 0 ≤ λ_n`**.

A rodada 15 (`ATK.Li`) tinha só o núcleo algébrico zero a zero (`|1 − 1/ρ| = 1 ⟺ Re ρ = ½`); faltava a soma, que
precisa da contagem dos zeros (`Σ 1/|ρ|² < ∞`, rodada 31) e de um argumento de crescimento:

1. **o resto binomial** (`resto_binom`): `|(1 − u)^n − 1 + nu| ≤ n²|u|²(1 + |u|)^n`, por indução; daí
   `|Re(1 − w^n)| ≤ (n + n²(14/13)^n)/|ρ|²` (`abs_termo_le`, `|1/ρ| ≤ 1/13`) e, para `|ρ| ≥ n`,
   `Re(1 − w^n) ≤ n Re(1/ρ) + 3n²/|ρ|²` (`termo_le_cauda`);
2. **RH ⟹ `λ_n ≥ 0`** (`lam_nonneg_of_RH`): cada parcela tem `|w| = 1` (rodada 15);
3. **a volta** (`RH_of_lam_nonneg`): se um zero tem `Re ρ < ½` (há um, pela simetria `ρ ↦ 1 − ρ̄`), então
   `|w| > 1`; os zeros de módulo máximo `r = max|w|` formam um conjunto finito `A` (`|w|² ≤ 1 + 1/|ρ|²`), os demais
   têm `|w| ≤ r₂ < r`. Pela **casa dos pombos no toro** (`dirichlet_simultaneo`) há `n` arbitrariamente grande com
   `cos(n arg w) ≥ ½` em `A`, e então `λ_n ≤ |A| − |A| r^n/2 + (1 + r₂^n)n²S₂ + nS₁ + 3n²S₂ < 0`.

Classificação (rodada 68): **reformulação** — o critério de Li, agora com a soma sobre os zeros. Provar `λ_n ≥ 0` para
todo `n` seria RH; RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.LiCompleto

open ATK.ZeroClasses.Canonico ATK.ZeroClasses.CanonicoInteira ATK.ZeroClasses.LagariasHadamard
  ATK.ZeroClasses.SomaZeros

/-! ## 1. O resto binomial -/

/-- **`|(1 − u)^n − 1 + nu| ≤ n²|u|²(1 + |u|)^n`**. -/
theorem resto_binom (u : ℂ) (n : ℕ) :
    ‖(1 - u) ^ n - 1 + n * u‖ ≤ (n : ℝ) ^ 2 * ‖u‖ ^ 2 * (1 + ‖u‖) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (1 - u) ^ (n + 1) - 1 + ((n + 1 : ℕ) : ℂ) * u =
        (1 - u) * ((1 - u) ^ n - 1 + n * u) + n * u ^ 2 := by
      push_cast
      ring
    rw [e]
    have h1 : ‖1 - u‖ ≤ 1 + ‖u‖ := by
      have := norm_sub_le (1 : ℂ) u
      rwa [norm_one] at this
    have hu := norm_nonneg u
    have hp : 1 ≤ (1 + ‖u‖) ^ n := one_le_pow₀ (by linarith)
    have hp' : (1 + ‖u‖) ^ (n + 1) = (1 + ‖u‖) * (1 + ‖u‖) ^ n := by ring
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc ‖(1 - u) * ((1 - u) ^ n - 1 + n * u) + n * u ^ 2‖
        ≤ ‖1 - u‖ * ‖(1 - u) ^ n - 1 + n * u‖ + n * ‖u‖ ^ 2 := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
      _ ≤ (1 + ‖u‖) * ((n : ℝ) ^ 2 * ‖u‖ ^ 2 * (1 + ‖u‖) ^ n) + n * ‖u‖ ^ 2 := by
          gcongr
      _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * ‖u‖ ^ 2 * (1 + ‖u‖) ^ (n + 1) := by
          push_cast
          rw [hp']
          have hq : 0 ≤ ‖u‖ ^ 2 := by positivity
          have hA : n * ‖u‖ ^ 2 ≤ (2 * n + 1) * ‖u‖ ^ 2 * ((1 + ‖u‖) * (1 + ‖u‖) ^ n) := by
            have h2 : 1 ≤ (1 + ‖u‖) * (1 + ‖u‖) ^ n := by nlinarith
            have h3 : (n : ℝ) ≤ 2 * n + 1 := by linarith
            calc (n : ℝ) * ‖u‖ ^ 2 ≤ (2 * n + 1) * ‖u‖ ^ 2 * 1 := by nlinarith
              _ ≤ (2 * n + 1) * ‖u‖ ^ 2 * ((1 + ‖u‖) * (1 + ‖u‖) ^ n) := by
                  apply mul_le_mul_of_nonneg_left h2
                  positivity
          nlinarith

/-! ## 2. As parcelas de Li -/

/-- `w(ρ) = 1 − 1/ρ` numa cópia `(ρ, j)`. -/
noncomputable def wq (q : ZM) : ℂ := ATK.Li.w (rZ q)

/-- A parcela `Re(1 − w^n)`. -/
noncomputable def termo (n : ℕ) (q : ZM) : ℝ := (1 - wq q ^ n).re

/-- **O coeficiente de Li** `λ_n = Σ_{(ρ,j)} Re(1 − (1 − 1/ρ)^n)`. -/
noncomputable def lam (n : ℕ) : ℝ := ∑' q, termo n q

theorem norm_rZ_ge (q : ZM) : 13 < ‖rZ q‖ :=
  (ATK.ZeroClasses.Faixa.zeros_acima_13 _ q.1.2).trans_le (abs_im_le_norm _)

theorem inv_props (q : ZM) :
    0 ≤ (1 / rZ q).re ∧ (1 / rZ q).re ≤ 1 / ‖rZ q‖ ^ 2 ∧ ‖1 / rZ q‖ ≤ 1 / 13 ∧
      ‖1 / rZ q‖ ^ 2 = 1 / ‖rZ q‖ ^ 2 := by
  obtain ⟨_, h0, h1⟩ := q.1.2
  have hn := norm_rZ_ge q
  have hpos : 0 < ‖rZ q‖ := by linarith
  have hre : (1 / rZ q).re = (rZ q).re / ‖rZ q‖ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]
    positivity
  · rw [hre]
    exact div_le_div_of_nonneg_right h1.le (by positivity)
  · rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by norm_num) hn.le
  · rw [norm_div, norm_one, div_pow, one_pow]

theorem termo_eq (n : ℕ) (q : ZM) :
    termo n q = n * (1 / rZ q).re - ((1 - 1 / rZ q) ^ n - 1 + n * (1 / rZ q)).re := by
  unfold termo wq ATK.Li.w
  simp only [sub_re, one_re, add_re, mul_re, natCast_re, natCast_im, zero_mul, sub_zero]
  ring

theorem abs_termo_le (n : ℕ) (q : ZM) :
    |termo n q| ≤ ((n : ℝ) + (n : ℝ) ^ 2 * (14 / 13) ^ n) * (1 / ‖rZ q‖ ^ 2) := by
  obtain ⟨hr0, hr1, hu, hu2⟩ := inv_props q
  have hR := resto_binom (1 / rZ q) n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpow : (1 + ‖1 / rZ q‖) ^ n ≤ (14 / 13) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith) n
  rw [termo_eq]
  have h1 := Complex.abs_re_le_norm ((1 - 1 / rZ q) ^ n - 1 + n * (1 / rZ q))
  have hq : 0 ≤ 1 / ‖rZ q‖ ^ 2 := by positivity
  calc |n * (1 / rZ q).re - ((1 - 1 / rZ q) ^ n - 1 + n * (1 / rZ q)).re|
      ≤ |n * (1 / rZ q).re| + |((1 - 1 / rZ q) ^ n - 1 + n * (1 / rZ q)).re| := abs_sub _ _
    _ ≤ n * (1 / ‖rZ q‖ ^ 2) + (n : ℝ) ^ 2 * (1 / ‖rZ q‖ ^ 2) * (14 / 13) ^ n := by
        rw [abs_of_nonneg (mul_nonneg hn0 hr0)]
        have a1 := mul_le_mul_of_nonneg_left hr1 hn0
        have a2 : (n : ℝ) ^ 2 * ‖1 / rZ q‖ ^ 2 * (1 + ‖1 / rZ q‖) ^ n ≤
            (n : ℝ) ^ 2 * (1 / ‖rZ q‖ ^ 2) * (14 / 13) ^ n := by
          rw [hu2]
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
        linarith
    _ = ((n : ℝ) + (n : ℝ) ^ 2 * (14 / 13) ^ n) * (1 / ‖rZ q‖ ^ 2) := by ring

theorem summable_inv_sq : Summable (fun q : ZM => 1 / ‖rZ q‖ ^ 2) := summable_ZM

theorem summable_termo (n : ℕ) : Summable (termo n) :=
  Summable.of_norm_bounded (summable_inv_sq.mul_left _) fun q => by
    rw [Real.norm_eq_abs]
    exact abs_termo_le n q

theorem termo_le_cauda {n : ℕ} (hn : 1 ≤ n) {q : ZM} (hq : (n : ℝ) ≤ ‖rZ q‖) :
    termo n q ≤ n * (1 / rZ q).re + 3 * (n : ℝ) ^ 2 * (1 / ‖rZ q‖ ^ 2) := by
  obtain ⟨hr0, hr1, hu, hu2⟩ := inv_props q
  have hR := resto_binom (1 / rZ q) n
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hun : ‖1 / rZ q‖ ≤ 1 / n := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hn0 hq
  have hpow : (1 + ‖1 / rZ q‖) ^ n ≤ 3 := by
    have h1 : (1 + ‖1 / rZ q‖) ^ n ≤ (1 + 1 / (n : ℝ)) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    have h2 : (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp 1 := by
      have h3 : 1 + 1 / (n : ℝ) ≤ Real.exp (1 / n) := by
        have := Real.add_one_le_exp (1 / (n : ℝ))
        linarith
      calc (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp (1 / n) ^ n := pow_le_pow_left₀ (by positivity) h3 n
        _ = Real.exp 1 := by
            rw [← Real.exp_nat_mul]
            congr 1
            field_simp
    have := Real.exp_one_lt_d9
    linarith
  rw [termo_eq]
  have h1 : -((1 - 1 / rZ q) ^ n - 1 + n * (1 / rZ q)).re ≤ ‖(1 - 1 / rZ q) ^ n - 1 + n * (1 / rZ q)‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  have h2 : (n : ℝ) ^ 2 * ‖1 / rZ q‖ ^ 2 * (1 + ‖1 / rZ q‖) ^ n ≤ 3 * (n : ℝ) ^ 2 * (1 / ‖rZ q‖ ^ 2) := by
    rw [hu2]
    have : 0 ≤ (n : ℝ) ^ 2 * (1 / ‖rZ q‖ ^ 2) := by positivity
    nlinarith
  linarith

theorem termo_le_norma (n : ℕ) (q : ZM) : termo n q ≤ 1 + ‖wq q‖ ^ n := by
  unfold termo
  have h1 := Complex.re_le_norm (1 - wq q ^ n)
  have h2 := norm_sub_le (1 : ℂ) (wq q ^ n)
  rw [norm_one, norm_pow] at h2
  linarith

/-! ## 3. RH ⟹ `λ_n ≥ 0` -/

theorem lam_nonneg_of_RH (hRH : RiemannHypothesis) (n : ℕ) : 0 ≤ lam n :=
  tsum_nonneg fun q => ATK.Li.rh_parcelas hRH q.1.2

/-! ## 4. A casa dos pombos no toro -/

theorem fract_proximo {y₁ y₂ : ℝ} (h : ⌊6 * Int.fract y₁⌋₊ = ⌊6 * Int.fract y₂⌋₊) :
    |Int.fract y₂ - Int.fract y₁| < 1 / 6 := by
  have a1 := Nat.floor_le (by have := Int.fract_nonneg y₁; positivity : (0 : ℝ) ≤ 6 * Int.fract y₁)
  have a2 := Nat.lt_floor_add_one (6 * Int.fract y₁)
  have b1 := Nat.floor_le (by have := Int.fract_nonneg y₂; positivity : (0 : ℝ) ≤ 6 * Int.fract y₂)
  have b2 := Nat.lt_floor_add_one (6 * Int.fract y₂)
  rw [h] at a1 a2
  rw [abs_lt]
  constructor <;> linarith

theorem floor_lt_seis (y : ℝ) : ⌊6 * Int.fract y⌋₊ < 6 := by
  have h := Int.fract_lt_one y
  have h0 := Int.fract_nonneg y
  rw [Nat.floor_lt (by positivity)]
  push_cast
  linarith

/-- **Dirichlet simultâneo**: para `n₀ ≥ 1` e ângulos `a_q` (`q ∈ A` finito) há `n ≥ n₀` com `n a_q` a menos de
`1/6` de um inteiro, para todo `q ∈ A`. -/
theorem dirichlet_simultaneo {ι : Type*} (A : Finset ι) (a : ι → ℝ) (n₀ : ℕ) (_hn₀ : 1 ≤ n₀) :
    ∃ n : ℕ, n₀ ≤ n ∧ ∀ q ∈ A, ∃ m : ℤ, |(n : ℝ) * a q - m| < 1 / 6 := by
  classical
  set k := A.card with hk
  let f : Fin (6 ^ k + 1) → (A → Fin 6) := fun j q =>
    ⟨⌊6 * Int.fract ((j : ℕ) * n₀ * a q)⌋₊, floor_lt_seis _⟩
  have hcard : Fintype.card (A → Fin 6) < Fintype.card (Fin (6 ^ k + 1)) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Fintype.card_coe, ← hk]
    omega
  obtain ⟨j₁, j₂, hne, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have key : ∀ i₁ i₂ : Fin (6 ^ k + 1), f i₁ = f i₂ → (i₁ : ℕ) < i₂ →
      ∃ n : ℕ, n₀ ≤ n ∧ ∀ q ∈ A, ∃ m : ℤ, |(n : ℝ) * a q - m| < 1 / 6 := by
    intro i₁ i₂ hf hlt
    refine ⟨((i₂ : ℕ) - i₁) * n₀, ?_, fun q hq => ?_⟩
    · have : 1 ≤ (i₂ : ℕ) - i₁ := by omega
      nlinarith
    · have hq' := congrFun hf ⟨q, hq⟩
      simp only [f, Fin.mk.injEq] at hq'
      have hp := fract_proximo hq'
      set y₁ := ((i₁ : ℕ) : ℝ) * n₀ * a q with hy₁
      set y₂ := ((i₂ : ℕ) : ℝ) * n₀ * a q with hy₂
      refine ⟨⌊y₂⌋ - ⌊y₁⌋, ?_⟩
      have e : ((((i₂ : ℕ) - i₁) * n₀ : ℕ) : ℝ) * a q - ((⌊y₂⌋ - ⌊y₁⌋ : ℤ) : ℝ) =
          Int.fract y₂ - Int.fract y₁ := by
        rw [Nat.cast_mul, Nat.cast_sub hlt.le, Int.fract, Int.fract, hy₁, hy₂]
        push_cast
        ring
      rw [e]
      exact hp
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hne) with h | h
  · exact key j₁ j₂ hfeq h
  · exact key j₂ j₁ hfeq.symm h

theorem cos_ge_meio {x : ℝ} {m : ℤ} (h : |x / (2 * π) - m| < 1 / 6) : 1 / 2 ≤ Real.cos x := by
  have hpi := Real.pi_pos
  have e : Real.cos x = Real.cos (x - m * (2 * π)) := (Real.cos_sub_int_mul_two_pi x m).symm
  set y := x - m * (2 * π) with hy
  have hyb : |y| ≤ π / 3 := by
    have e2 : y = 2 * π * (x / (2 * π) - m) := by rw [hy]; field_simp
    rw [e2, abs_mul, abs_of_pos (by positivity)]
    have := mul_le_mul_of_nonneg_left h.le (by positivity : (0 : ℝ) ≤ 2 * π)
    linarith
  rw [e, ← Real.cos_abs]
  rw [← Real.cos_pi_div_three]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y) (by linarith) hyb

/-! ## 5. A volta -/

theorem re_pow_eq (z : ℂ) (n : ℕ) : (z ^ n).re = ‖z‖ ^ n * Real.cos (n * Complex.arg z) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [mul_pow, ← Complex.exp_nat_mul, ← Complex.ofReal_pow]
  have e : (n : ℂ) * ((Complex.arg z : ℂ) * I) = (((n : ℝ) * Complex.arg z : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem norm_wq_sq_le (q : ZM) : ‖wq q‖ ^ 2 ≤ 1 + 1 / ‖rZ q‖ ^ 2 := by
  have h0 := ATK.Li.ne_zero_of_mem_Z q.1.2
  obtain ⟨_, hb0, hb1⟩ := q.1.2
  unfold wq
  rw [ATK.Li.norm_w_sq h0]
  have hn : ‖rZ q‖ ^ 2 = (rZ q).re ^ 2 + (rZ q).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hpos : 0 < (rZ q).re ^ 2 + (rZ q).im ^ 2 := ATK.Li.normSq_pos h0
  rw [← hn] at hpos ⊢
  rw [div_le_iff₀ hpos, add_mul, one_mul, one_div, inv_mul_cancel₀ hpos.ne']
  rw [hn]
  nlinarith

theorem finito_grande {r₁ : ℝ} (hr₁ : 1 < r₁) : {q : ZM | r₁ ≤ ‖wq q‖}.Finite := by
  have h := summable_inv_sq.tendsto_cofinite_zero
  have hpos : (0 : ℝ) < r₁ ^ 2 - 1 := by nlinarith
  have hev : ∀ᶠ q in cofinite, 1 / ‖rZ q‖ ^ 2 < r₁ ^ 2 - 1 := h.eventually (gt_mem_nhds hpos)
  refine (Filter.eventually_cofinite.mp hev).subset fun q hq => ?_
  simp only [Set.mem_ofPred_eq, not_lt] at hq ⊢
  have h1 := norm_wq_sq_le q
  have h2 : r₁ ^ 2 ≤ ‖wq q‖ ^ 2 := pow_le_pow_left₀ (by linarith) hq 2
  linarith

theorem existe_fora (hnot : ¬ RiemannHypothesis) : ∃ q : ZM, 1 < ‖wq q‖ := by
  rw [ATK.Li.rh_iff_li_unitario] at hnot
  push Not at hnot
  obtain ⟨ρ, hρ, hne⟩ := hnot
  have h0 := ATK.Li.ne_zero_of_mem_Z hρ
  rcases lt_or_gt_of_ne hne with h | h
  · -- `|w| < 1`: `Re ρ > ½`; usar `1 − ρ̄`
    have hre : 1 / 2 < ρ.re := (ATK.Li.w_dentro_iff h0).mp h
    have hρ' := ATK.ZetaSimetria.torcao_mem_Z hρ
    have hre' : (ATK.ZetaSimetria.torcao ρ).re < 1 / 2 := by
      rw [ATK.ZetaSimetria.re_torcao]
      linarith
    obtain ⟨q, hq⟩ := ATK.ZeroClasses.Explicita.existe_q hρ'
    refine ⟨q, ?_⟩
    unfold wq
    rw [hq]
    exact (ATK.Li.w_fora_iff (ATK.Li.ne_zero_of_mem_Z hρ')).mpr hre'
  · obtain ⟨q, hq⟩ := ATK.ZeroClasses.Explicita.existe_q hρ
    exact ⟨q, by unfold wq; rw [hq]; exact h⟩

/-- **A volta do critério de Li**: `λ_n ≥ 0` para todo `n ≥ 1` ⟹ RH. -/
theorem RH_of_lam_nonneg (h : ∀ n : ℕ, 1 ≤ n → 0 ≤ lam n) : RiemannHypothesis := by
  classical
  by_contra hnot
  obtain ⟨q₀, hq₀⟩ := existe_fora hnot
  set r₁ : ℝ := (1 + ‖wq q₀‖) / 2 with hr₁
  have hr₁1 : 1 < r₁ := by rw [hr₁]; linarith
  have hr₁q : r₁ < ‖wq q₀‖ := by rw [hr₁]; linarith
  set F : Finset ZM := (finito_grande hr₁1).toFinset with hF
  have hmemF : ∀ q, q ∈ F ↔ r₁ ≤ ‖wq q‖ := fun q => by rw [hF, Set.Finite.mem_toFinset]; rfl
  have hq₀F : q₀ ∈ F := (hmemF q₀).mpr hr₁q.le
  have hFne : F.Nonempty := ⟨q₀, hq₀F⟩
  obtain ⟨qm, hqmF, hqmax⟩ := F.exists_max_image (fun q => ‖wq q‖) hFne
  set r : ℝ := ‖wq qm‖ with hr
  have hrq₀ : ‖wq q₀‖ ≤ r := hqmax q₀ hq₀F
  have hr1 : r₁ < r := hr₁q.trans_le hrq₀
  have hall : ∀ q, ‖wq q‖ ≤ r := by
    intro q
    by_cases hq : q ∈ F
    · exact hqmax q hq
    · rw [hmemF, not_le] at hq
      linarith
  set A : Finset ZM := F.filter (fun q => ‖wq q‖ = r) with hA
  have hqmA : qm ∈ A := Finset.mem_filter.mpr ⟨hqmF, rfl⟩
  have hAcard : 1 ≤ A.card := Finset.card_pos.mpr ⟨qm, hqmA⟩
  -- `r₂ < r` majora os demais
  set G : Finset ZM := F.filter (fun q => ‖wq q‖ ≠ r) with hG
  set r₂ : ℝ := G.fold max r₁ (fun q => ‖wq q‖) with hr₂
  have hr₂r : r₂ < r := by
    rw [hr₂, Finset.fold_max_lt]
    refine ⟨hr1, fun q hq => ?_⟩
    rw [hG, Finset.mem_filter] at hq
    exact lt_of_le_of_ne (hall q) hq.2
  have hr₁r₂ : r₁ ≤ r₂ := by
    rw [hr₂, Finset.le_fold_max]
    exact Or.inl le_rfl
  have hfora : ∀ q, q ∉ A → ‖wq q‖ ≤ r₂ := by
    intro q hq
    by_cases hqF : q ∈ F
    · have hqG : q ∈ G := by
        rw [hG, Finset.mem_filter]
        refine ⟨hqF, fun h => hq ?_⟩
        rw [hA, Finset.mem_filter]
        exact ⟨hqF, h⟩
      rw [hr₂, Finset.le_fold_max]
      exact Or.inr ⟨q, hqG, le_rfl⟩
    · rw [hmemF, not_le] at hqF
      linarith
  have hr₂1 : 1 < r₂ := by linarith
  have hr0 : 0 < r := by linarith
  -- as constantes
  set S₁ : ℝ := ∑' q : ZM, (1 / rZ q).re with hS₁
  set S₂ : ℝ := ∑' q : ZM, 1 / ‖rZ q‖ ^ 2 with hS₂
  have hS₁s : Summable (fun q : ZM => (1 / rZ q).re) :=
    Summable.of_nonneg_of_le (fun q => (inv_props q).1) (fun q => (inv_props q).2.1) summable_inv_sq
  have hS₁0 : 0 ≤ S₁ := tsum_nonneg fun q => (inv_props q).1
  have hS₂0 : 0 ≤ S₂ := tsum_nonneg fun q => by positivity
  -- a cota superior para `λ_n`
  have hlam : ∀ n : ℕ, 1 ≤ n → lam n ≤ ∑ q ∈ A, termo n q + (1 + r₂ ^ n) * ((n : ℝ) ^ 2 * S₂) +
      (n * S₁ + 3 * (n : ℝ) ^ 2 * S₂) := by
    intro n hn
    set ind : ZM → ℝ := fun q => if q ∈ A then termo n q else 0 with hind
    set pq : ZM → ℝ := fun q => if ‖rZ q‖ < n then (1 + r₂ ^ n) else 0 with hpq
    set rest : ZM → ℝ := fun q => n * (1 / rZ q).re + 3 * (n : ℝ) ^ 2 * (1 / ‖rZ q‖ ^ 2) with hrest
    have hsind : Summable ind := summable_of_ne_finset_zero (s := A) fun q hq => by
      simp only [hind, hq, ↓reduceIte]
    have hr2n : 0 ≤ 1 + r₂ ^ n := by positivity
    have hpq_le : ∀ q, pq q ≤ (1 + r₂ ^ n) * (n : ℝ) ^ 2 * (1 / ‖rZ q‖ ^ 2) := by
      intro q
      simp only [hpq]
      split_ifs with hlt
      · have hρ := norm_rZ_ge q
        have hρ0 : 0 < ‖rZ q‖ := by linarith
        have h1 : 1 ≤ (n : ℝ) ^ 2 * (1 / ‖rZ q‖ ^ 2) := by
          rw [mul_one_div, le_div_iff₀ (by positivity), one_mul]
          exact pow_le_pow_left₀ hρ0.le hlt.le 2
        calc 1 + r₂ ^ n = (1 + r₂ ^ n) * 1 := by ring
          _ ≤ (1 + r₂ ^ n) * ((n : ℝ) ^ 2 * (1 / ‖rZ q‖ ^ 2)) := mul_le_mul_of_nonneg_left h1 hr2n
          _ = (1 + r₂ ^ n) * (n : ℝ) ^ 2 * (1 / ‖rZ q‖ ^ 2) := by ring
      · positivity
    have hpq0 : ∀ q, 0 ≤ pq q := fun q => by
      simp only [hpq]
      split_ifs
      · exact hr2n
      · exact le_rfl
    have hspq : Summable pq := Summable.of_nonneg_of_le hpq0 hpq_le (summable_inv_sq.mul_left _)
    have hsrest : Summable rest := (hS₁s.mul_left _).add (summable_inv_sq.mul_left _)
    have hle : ∀ q, termo n q ≤ ind q + pq q + rest q := by
      intro q
      have hr0' := (inv_props q).1
      have hrest0 : 0 ≤ rest q := by
        simp only [hrest]
        positivity
      have hpq0' := hpq0 q
      by_cases hqA : q ∈ A
      · have : ind q = termo n q := by simp only [hind, hqA, ↓reduceIte]
        linarith
      · have hi : ind q = 0 := by simp only [hind, hqA, ↓reduceIte]
        rw [hi, zero_add]
        by_cases hlt : ‖rZ q‖ < n
        · have hp : pq q = 1 + r₂ ^ n := by simp only [hpq, hlt, ↓reduceIte]
          have h1 := termo_le_norma n q
          have h2 : ‖wq q‖ ^ n ≤ r₂ ^ n := pow_le_pow_left₀ (norm_nonneg _) (hfora q hqA) n
          linarith
        · have hp : pq q = 0 := by simp only [hpq, hlt, ↓reduceIte]
          rw [hp, zero_add]
          exact termo_le_cauda hn (not_lt.mp hlt)
    have hsum1 : ∑' q, ind q = ∑ q ∈ A, termo n q := by
      rw [tsum_eq_sum (s := A) fun q hq => by simp only [hind, hq, ↓reduceIte]]
      exact Finset.sum_congr rfl fun q hq => by simp only [hind, hq, ↓reduceIte]
    have hsum2 : ∑' q, pq q ≤ (1 + r₂ ^ n) * ((n : ℝ) ^ 2 * S₂) := by
      calc ∑' q, pq q ≤ ∑' q, (1 + r₂ ^ n) * (n : ℝ) ^ 2 * (1 / ‖rZ q‖ ^ 2) :=
            hspq.tsum_le_tsum hpq_le (summable_inv_sq.mul_left _)
        _ = (1 + r₂ ^ n) * ((n : ℝ) ^ 2 * S₂) := by rw [tsum_mul_left]; ring
    have hsum3 : ∑' q, rest q = n * S₁ + 3 * (n : ℝ) ^ 2 * S₂ := by
      simp only [hrest]
      rw [(hS₁s.mul_left _).tsum_add (summable_inv_sq.mul_left _), tsum_mul_left, tsum_mul_left]
    calc lam n = ∑' q, termo n q := rfl
      _ ≤ ∑' q, (ind q + pq q + rest q) :=
          (summable_termo n).tsum_le_tsum hle ((hsind.add hspq).add hsrest)
      _ = ∑' q, ind q + ∑' q, pq q + ∑' q, rest q := by
          rw [(hsind.add hspq).tsum_add hsrest, hsind.tsum_add hspq]
      _ ≤ ∑ q ∈ A, termo n q + (1 + r₂ ^ n) * ((n : ℝ) ^ 2 * S₂) + (n * S₁ + 3 * (n : ℝ) ^ 2 * S₂) := by
          rw [hsum1, hsum3]
          linarith
  -- o crescimento
  have hrinv : |1 / r| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hr0]
    linarith
  have hr2r : |r₂ / r| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one hr0]
    exact hr₂r
  set g : ℕ → ℝ := fun n => (A.card : ℝ) * (1 / r) ^ n + S₁ * ((n : ℝ) ^ 1 * (1 / r) ^ n) +
    4 * S₂ * ((n : ℝ) ^ 2 * (1 / r) ^ n) + S₂ * ((n : ℝ) ^ 2 * (r₂ / r) ^ n) with hgdef
  have hg : Tendsto g atTop (𝓝 0) := by
    have t1 : Tendsto (fun n : ℕ => (1 / r) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by rw [abs_of_pos (by positivity)] at hrinv; exact hrinv)
    have t2 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hrinv
    have t3 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hrinv
    have t4 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hr2r
    have := (((t1.const_mul (A.card : ℝ)).add (t2.const_mul S₁)).add (t3.const_mul (4 * S₂))).add
      (t4.const_mul S₂)
    simpa [hgdef] using this
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp (hg.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  obtain ⟨n, hnn, hdir⟩ := dirichlet_simultaneo A (fun q => Complex.arg (wq q) / (2 * π)) (max n₁ 1)
    (le_max_right _ _)
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hnn
  have hgn : g n < 1 / 2 := hn₁ n ((le_max_left _ _).trans hnn)
  have hrn : 0 < r ^ n := pow_pos hr0 n
  -- a soma sobre `A`
  have htop : ∑ q ∈ A, termo n q ≤ A.card * (1 - r ^ n / 2) := by
    have hq : ∀ q ∈ A, termo n q ≤ 1 - r ^ n / 2 := by
      intro q hq
      have hqr : ‖wq q‖ = r := (Finset.mem_filter.mp hq).2
      obtain ⟨m, hm⟩ := hdir q hq
      have hcos : 1 / 2 ≤ Real.cos (n * Complex.arg (wq q)) := by
        apply cos_ge_meio (m := m)
        have e : (n : ℝ) * Complex.arg (wq q) / (2 * π) = (n : ℝ) * (Complex.arg (wq q) / (2 * π)) := by
          ring
        rw [e]
        exact hm
      unfold termo
      rw [sub_re, one_re, re_pow_eq, hqr]
      have := mul_le_mul_of_nonneg_left hcos hrn.le
      linarith
    calc ∑ q ∈ A, termo n q ≤ ∑ q ∈ A, (1 - r ^ n / 2) := Finset.sum_le_sum hq
      _ = A.card * (1 - r ^ n / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
  have e1 : (1 / r) ^ n * r ^ n = 1 := by
    rw [one_div, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hr0.ne')]
  have e2 : (r₂ / r) ^ n * r ^ n = r₂ ^ n := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hr0.ne')]
  have hexp : g n * r ^ n = (A.card : ℝ) + S₁ * n + 4 * S₂ * (n : ℝ) ^ 2 + S₂ * (n : ℝ) ^ 2 * r₂ ^ n := by
    have : g n * r ^ n = (A.card : ℝ) * ((1 / r) ^ n * r ^ n) + S₁ * (n : ℝ) * ((1 / r) ^ n * r ^ n) +
        4 * S₂ * (n : ℝ) ^ 2 * ((1 / r) ^ n * r ^ n) + S₂ * (n : ℝ) ^ 2 * ((r₂ / r) ^ n * r ^ n) := by
      simp only [hgdef]
      ring
    rw [this, e1, e2]
    ring
  have hlt : g n * r ^ n < 1 / 2 * r ^ n := mul_lt_mul_of_pos_right hgn hrn
  have hAr : (1 / 2 : ℝ) * r ^ n ≤ A.card * (r ^ n / 2) := by
    have hA1 : (1 : ℝ) ≤ A.card := by exact_mod_cast hAcard
    nlinarith
  have hL := hlam n hn1
  have hneg : lam n < 0 := by
    rw [hexp] at hlt
    nlinarith
  exact absurd (h n hn1) (not_le.mpr hneg)

/-- **O critério de Li**: RH ⟺ `λ_n ≥ 0` para todo `n ≥ 1`. -/
theorem rh_iff_li : RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ lam n :=
  ⟨fun hRH n _ => lam_nonneg_of_RH hRH n, RH_of_lam_nonneg⟩

end ATK.ZeroClasses.LiCompleto

#print axioms ATK.ZeroClasses.LiCompleto.resto_binom
#print axioms ATK.ZeroClasses.LiCompleto.norm_rZ_ge
#print axioms ATK.ZeroClasses.LiCompleto.inv_props
#print axioms ATK.ZeroClasses.LiCompleto.termo_eq
#print axioms ATK.ZeroClasses.LiCompleto.abs_termo_le
#print axioms ATK.ZeroClasses.LiCompleto.summable_inv_sq
#print axioms ATK.ZeroClasses.LiCompleto.summable_termo
#print axioms ATK.ZeroClasses.LiCompleto.termo_le_cauda
#print axioms ATK.ZeroClasses.LiCompleto.termo_le_norma
#print axioms ATK.ZeroClasses.LiCompleto.lam_nonneg_of_RH
#print axioms ATK.ZeroClasses.LiCompleto.fract_proximo
#print axioms ATK.ZeroClasses.LiCompleto.floor_lt_seis
#print axioms ATK.ZeroClasses.LiCompleto.dirichlet_simultaneo
#print axioms ATK.ZeroClasses.LiCompleto.cos_ge_meio
#print axioms ATK.ZeroClasses.LiCompleto.re_pow_eq
#print axioms ATK.ZeroClasses.LiCompleto.norm_wq_sq_le
#print axioms ATK.ZeroClasses.LiCompleto.finito_grande
#print axioms ATK.ZeroClasses.LiCompleto.existe_fora
#print axioms ATK.ZeroClasses.LiCompleto.RH_of_lam_nonneg
#print axioms ATK.ZeroClasses.LiCompleto.rh_iff_li
