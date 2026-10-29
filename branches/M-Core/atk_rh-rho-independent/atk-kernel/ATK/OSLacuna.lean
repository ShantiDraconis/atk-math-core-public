import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# ATK — B7: decaimento exponencial das correlações ⇒ lacuna espectral

Camada OS-4 do ataque a B7 (reconstrução de Osterwalder–Schrader). A segunda metade da ponte
`OSReconstruction` diz: *correlações que decaem como `e^{−m t}` dão lacuna `≥ m`*. Aqui ela é
provada para um semigrupo de transferência `P(t) = e^{−tH}` abstrato (autoadjunto, `P(0) = 1`,
`P(s + t) = P(s) P(t)`), sem teorema espectral nem operadores ilimitados:

* `decai_de_convexo`: se `φ ≥ 0`, `φ(t)² ≤ φ(0) φ(2t)` (convexidade logarítmica no ponto médio) e
  `φ(t) ≤ C e^{−m t}`, então `φ(t) ≤ φ(0) e^{−m t}` — a constante `C` desaparece (iteração
  `φ(t)^{2ⁿ} φ(0) ≤ φ(0)^{2ⁿ} φ(2ⁿ t)` e crescimento de `qⁿ` para `q > 1`);
* `lacuna_de_decaimento`: se `⟪v, P(t) v⟫ ≤ C_v e^{−m t}` para `v` num conjunto `D`, então
  `‖P(t) w‖ ≤ e^{−m t} ‖w‖` em todo o fecho de `D` (`φ_v(t) = ⟪v, P(t) v⟫ = ‖P(t/2) v‖²` é
  logaritmicamente convexa por Cauchy–Schwarz).

Com `D` denso no complemento ortogonal do vácuo, isto é a lacuna `spec(H) ∩ (0, m) = ∅`.

**CLOSED_MATH continua false.**
-/

open scoped InnerProductSpace

namespace ATK.OSLacuna

/-- **A constante some**: convexidade logarítmica no ponto médio e decaimento `C e^{−m t}`
dão decaimento `φ(0) e^{−m t}`. -/
theorem decai_de_convexo {φ : ℝ → ℝ} {m C : ℝ} (h0 : ∀ t, 0 ≤ t → 0 ≤ φ t)
    (hcv : ∀ t, 0 ≤ t → φ t ^ 2 ≤ φ 0 * φ (2 * t))
    (hC : ∀ t, 0 ≤ t → φ t ≤ C * Real.exp (-(m * t))) {t : ℝ} (ht : 0 ≤ t) :
    φ t ≤ φ 0 * Real.exp (-(m * t)) := by
  set E : ℝ := Real.exp (-(m * t)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  rcases (h0 0 le_rfl).eq_or_lt with h00 | h0pos
  · -- `φ(0) = 0` força `φ(t) = 0`
    have h1 := hcv t ht
    rw [← h00, zero_mul] at h1
    have : φ t = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm h1 (sq_nonneg _))
    rw [this, ← h00, zero_mul]
  -- a iteração
  have hit : ∀ n : ℕ, φ t ^ (2 ^ n) * φ 0 ≤ φ 0 ^ (2 ^ n) * φ ((2 : ℝ) ^ n * t) := by
    intro n
    induction n with
    | zero => simp [mul_comm]
    | succ n ih =>
      have hA : 0 ≤ φ t ^ (2 ^ n) * φ 0 := mul_nonneg (pow_nonneg (h0 t ht) _) h0pos.le
      have hsq := pow_le_pow_left₀ hA ih 2
      have hn : 0 ≤ (2 : ℝ) ^ n * t := mul_nonneg (pow_nonneg (by norm_num) _) ht
      have hc := hcv _ hn
      have e2 : 2 * ((2 : ℝ) ^ n * t) = (2 : ℝ) ^ (n + 1) * t := by rw [pow_succ]; ring
      rw [e2] at hc
      have hB : (φ 0 ^ (2 ^ n) * φ ((2 : ℝ) ^ n * t)) ^ 2 ≤
          φ 0 ^ (2 ^ (n + 1)) * (φ 0 * φ ((2 : ℝ) ^ (n + 1) * t)) := by
        rw [mul_pow, ← pow_mul, ← pow_succ]
        exact mul_le_mul_of_nonneg_left hc (pow_nonneg h0pos.le _)
      have key : (φ t ^ (2 ^ (n + 1)) * φ 0) * φ 0 ≤
          (φ 0 ^ (2 ^ (n + 1)) * φ ((2 : ℝ) ^ (n + 1) * t)) * φ 0 := by
        have e1 : (φ t ^ (2 ^ n) * φ 0) ^ 2 = (φ t ^ (2 ^ (n + 1)) * φ 0) * φ 0 := by
          rw [mul_pow, ← pow_mul, ← pow_succ]; ring
        have e3 : φ 0 ^ (2 ^ (n + 1)) * (φ 0 * φ ((2 : ℝ) ^ (n + 1) * t)) =
            (φ 0 ^ (2 ^ (n + 1)) * φ ((2 : ℝ) ^ (n + 1) * t)) * φ 0 := by ring
        rw [← e1, ← e3]
        exact hsq.trans hB
      exact le_of_mul_le_mul_right key h0pos
  -- por contradição
  by_contra hlt
  push_neg at hlt
  have hpos : 0 < φ 0 * E := mul_pos h0pos hE0
  set q : ℝ := φ t / (φ 0 * E) with hq
  have hq1 : 1 < q := by rw [hq, one_lt_div hpos]; exact hlt
  have hφt : φ t = q * (φ 0 * E) := by rw [hq]; field_simp
  -- `qⁿ φ(0) ≤ C` para potências `2ⁿ`
  have hbound : ∀ n : ℕ, q ^ (2 ^ n) * φ 0 ≤ C := by
    intro n
    have h1 := hit n
    have hn : 0 ≤ (2 : ℝ) ^ n * t := mul_nonneg (pow_nonneg (by norm_num) _) ht
    have h2 := hC _ hn
    have eE : Real.exp (-(m * ((2 : ℝ) ^ n * t))) = E ^ (2 ^ n) := by
      rw [hE, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [eE] at h2
    have h3 : φ t ^ (2 ^ n) * φ 0 ≤ φ 0 ^ (2 ^ n) * (C * E ^ (2 ^ n)) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 (pow_nonneg h0pos.le _))
    rw [hφt, mul_pow, mul_pow] at h3
    have hP : 0 < φ 0 ^ (2 ^ n) * E ^ (2 ^ n) := mul_pos (pow_pos h0pos _) (pow_pos hE0 _)
    have h4 : (q ^ (2 ^ n) * φ 0) * (φ 0 ^ (2 ^ n) * E ^ (2 ^ n)) ≤
        C * (φ 0 ^ (2 ^ n) * E ^ (2 ^ n)) := by
      calc (q ^ (2 ^ n) * φ 0) * (φ 0 ^ (2 ^ n) * E ^ (2 ^ n))
          = q ^ (2 ^ n) * (φ 0 ^ (2 ^ n) * E ^ (2 ^ n)) * φ 0 := by ring
        _ ≤ φ 0 ^ (2 ^ n) * (C * E ^ (2 ^ n)) := h3
        _ = C * (φ 0 ^ (2 ^ n) * E ^ (2 ^ n)) := by ring
    exact le_of_mul_le_mul_right h4 hP
  -- mas `q^{2ⁿ} ≥ 1 + n (q − 1)` cresce sem limite
  obtain ⟨n, hn⟩ := exists_nat_gt (C / (φ 0 * (q - 1)))
  have hq0 : 0 < q - 1 := by linarith
  have hb1 : 1 + (n : ℝ) * (q - 1) ≤ q ^ n := by
    have := one_add_mul_le_pow (a := q - 1) (by linarith) n
    simpa using this
  have hb2 : q ^ n ≤ q ^ (2 ^ n) := pow_le_pow_right₀ hq1.le (Nat.lt_two_pow_self).le
  have hb3 : C < (1 + (n : ℝ) * (q - 1)) * φ 0 := by
    rw [div_lt_iff₀ (mul_pos h0pos hq0)] at hn
    nlinarith
  have := hbound n
  nlinarith [mul_le_mul_of_nonneg_right (hb1.trans hb2) h0pos.le]

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Decaimento exponencial das correlações ⇒ lacuna** para um semigrupo de transferência
autoadjunto: `⟪v, P(t) v⟫ ≤ C_v e^{−m t}` em `D` dá `‖P(t) w‖ ≤ e^{−m t} ‖w‖` no fecho de `D`. -/
theorem lacuna_de_decaimento {P : ℝ → H →L[ℂ] H} (hP0 : P 0 = ContinuousLinearMap.id ℂ H)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → P (s + t) = (P s).comp (P t))
    (hsa : ∀ t, 0 ≤ t → ∀ u v, ⟪P t u, v⟫_ℂ = ⟪u, P t v⟫_ℂ) {D : Set H} {m : ℝ}
    (hdec : ∀ v ∈ D, ∃ C, ∀ t, 0 ≤ t → (⟪v, P t v⟫_ℂ).re ≤ C * Real.exp (-(m * t))) :
    ∀ w ∈ closure D, ∀ t, 0 ≤ t → ‖P t w‖ ≤ Real.exp (-(m * t)) * ‖w‖ := by
  -- `‖P(t) v‖² = Re ⟪v, P(2t) v⟫`
  have hnorm : ∀ v : H, ∀ t, 0 ≤ t → ‖P t v‖ ^ 2 = (⟪v, P (2 * t) v⟫_ℂ).re := by
    intro v t ht
    have e : P (2 * t) = (P t).comp (P t) := by rw [two_mul]; exact hadd t t ht ht
    rw [e, ContinuousLinearMap.comp_apply, ← hsa t ht]
    exact norm_sq_eq_re_inner (𝕜 := ℂ) _
  have hφ0 : ∀ v : H, (⟪v, P 0 v⟫_ℂ).re = ‖v‖ ^ 2 := by
    intro v
    rw [hP0, ContinuousLinearMap.id_apply]
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have hφnn : ∀ v : H, ∀ t, 0 ≤ t → 0 ≤ (⟪v, P t v⟫_ℂ).re := by
    intro v t ht
    have h := hnorm v (t / 2) (by linarith)
    rw [show 2 * (t / 2) = t by ring] at h
    rw [← h]
    exact sq_nonneg _
  -- a cota em `D`
  have hD : ∀ v ∈ D, ∀ t, 0 ≤ t → ‖P t v‖ ≤ Real.exp (-(m * t)) * ‖v‖ := by
    intro v hv t ht
    obtain ⟨C, hC⟩ := hdec v hv
    set φ : ℝ → ℝ := fun s => (⟪v, P s v⟫_ℂ).re with hφ
    have hcv : ∀ s, 0 ≤ s → φ s ^ 2 ≤ φ 0 * φ (2 * s) := by
      intro s hs
      have h1 : φ s ≤ ‖v‖ * ‖P s v‖ :=
        (Complex.re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)
      have h2 := hφnn v s hs
      have h3 : φ s ^ 2 ≤ (‖v‖ * ‖P s v‖) ^ 2 := pow_le_pow_left₀ h2 h1 2
      calc φ s ^ 2 ≤ (‖v‖ * ‖P s v‖) ^ 2 := h3
        _ = ‖v‖ ^ 2 * ‖P s v‖ ^ 2 := by ring
        _ = φ 0 * φ (2 * s) := by rw [hnorm v s hs]; simp only [hφ, hφ0]
    have h2t : 0 ≤ 2 * t := by linarith
    have hb := decai_de_convexo (φ := φ) (fun s hs => hφnn v s hs) hcv hC h2t
    have e0 : φ 0 = ‖v‖ ^ 2 := hφ0 v
    rw [e0] at hb
    have hsq : ‖P t v‖ ^ 2 ≤ (Real.exp (-(m * t)) * ‖v‖) ^ 2 := by
      rw [hnorm v t ht]
      calc (⟪v, P (2 * t) v⟫_ℂ).re = φ (2 * t) := rfl
        _ ≤ ‖v‖ ^ 2 * Real.exp (-(m * (2 * t))) := hb
        _ = (Real.exp (-(m * t)) * ‖v‖) ^ 2 := by
            rw [mul_pow, ← Real.exp_nat_mul]
            push_cast
            ring_nf
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) two_ne_zero).mp hsq
  -- passagem ao fecho
  intro w hw t ht
  have hcl : IsClosed {u : H | ‖P t u‖ ≤ Real.exp (-(m * t)) * ‖u‖} :=
    isClosed_le ((P t).continuous.norm) (continuous_const.mul continuous_norm)
  exact closure_minimal (fun v hv => hD v hv t ht) hcl hw

end Hilbert

end ATK.OSLacuna

#print axioms ATK.OSLacuna.decai_de_convexo
#print axioms ATK.OSLacuna.lacuna_de_decaimento
