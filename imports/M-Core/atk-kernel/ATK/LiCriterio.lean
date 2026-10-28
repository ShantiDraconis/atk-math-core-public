import ATK.JensenTuran

/-!
# ATK — O núcleo algébrico do critério de Li

Li (1997): `λₙ = Σ_ρ [1 − (1 − 1/ρ)ⁿ]` e **HR ⟺ λₙ ≥ 0 para todo n ≥ 1**. A soma sobre todos os zeros (com a
ordem de soma de Keiper–Li) não está no Mathlib; aqui fica o que faz o critério funcionar, zero a zero:

* `w(ρ) = 1 − 1/ρ = (ρ − 1)/ρ` leva a linha crítica no **círculo unitário**: `|w(ρ)| = 1 ⟺ Re ρ = ½`
  (`w_unitario_iff`), `|w| < 1 ⟺ Re ρ > ½`, `|w| > 1 ⟺ Re ρ < ½`.
* **HR ⟺ todo zero não trivial vai para o círculo unitário** (`rh_iff_li_unitario`).
* No círculo, cada parcela tem parte real `≥ 0`: `Re(1 − wⁿ) ≥ 0` (`parcela_nao_negativa`); fora dele,
  `|1 − wⁿ| → ∞` (`parcela_ilimitada`) — é isso que torna `λₙ` negativo para `n` grande se HR falhar.
* A simetria `ρ ↦ 1 − ρ̄` vira `w ↦ 1/w̄` (`w_torcao`): um zero fora da linha produz um par com `|w| > 1`.
-/

open Complex Filter Topology

namespace ATK.Li

open ATK.ZetaSimetria ATK.CEZ

/-- `w(ρ) = 1 − 1/ρ`. -/
noncomputable def w (ρ : ℂ) : ℂ := 1 - 1 / ρ

theorem w_eq {ρ : ℂ} (h : ρ ≠ 0) : w ρ = (ρ - 1) / ρ := by
  unfold w; field_simp

theorem norm_w_sq {ρ : ℂ} (h : ρ ≠ 0) :
    ‖w ρ‖ ^ 2 = ((ρ.re - 1) ^ 2 + ρ.im ^ 2) / (ρ.re ^ 2 + ρ.im ^ 2) := by
  rw [w_eq h, norm_div, div_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [sub_re, sub_im, one_re, one_im, sub_zero]
  ring_nf

theorem normSq_pos {ρ : ℂ} (h : ρ ≠ 0) : 0 < ρ.re ^ 2 + ρ.im ^ 2 := by
  have := Complex.normSq_pos.mpr h
  rw [Complex.normSq_apply] at this
  nlinarith

/-- `|w|² − 1 = (1 − 2 Re ρ)/|ρ|²`. -/
theorem norm_w_sq_sub_one {ρ : ℂ} (h : ρ ≠ 0) :
    ‖w ρ‖ ^ 2 - 1 = (1 - 2 * ρ.re) / (ρ.re ^ 2 + ρ.im ^ 2) := by
  rw [norm_w_sq h]
  have := normSq_pos h
  field_simp
  ring

/-- **A linha crítica vai no círculo unitário.** -/
theorem w_unitario_iff {ρ : ℂ} (h : ρ ≠ 0) : ‖w ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  have hp := normSq_pos h
  have key := norm_w_sq_sub_one h
  constructor
  · intro h1
    rw [h1, one_pow, sub_self] at key
    have := (div_eq_zero_iff.mp key.symm).resolve_right hp.ne'
    linarith
  · intro h1
    have : ‖w ρ‖ ^ 2 = 1 := by
      have e : (1 - 2 * ρ.re) = 0 := by rw [h1]; ring
      rw [e, zero_div] at key
      linarith
    have h0 := norm_nonneg (w ρ)
    nlinarith [sq_nonneg (‖w ρ‖ - 1), sq_nonneg (‖w ρ‖ + 1)]

theorem w_dentro_iff {ρ : ℂ} (h : ρ ≠ 0) : ‖w ρ‖ < 1 ↔ 1 / 2 < ρ.re := by
  have hp := normSq_pos h
  have key := norm_w_sq_sub_one h
  have h0 := norm_nonneg (w ρ)
  constructor
  · intro h1
    have : ‖w ρ‖ ^ 2 - 1 < 0 := by nlinarith
    rw [key] at this
    have := (div_neg_iff.mp this)
    rcases this with ⟨a, _⟩ | ⟨_, b⟩
    · linarith
    · linarith
  · intro h1
    have : ‖w ρ‖ ^ 2 - 1 < 0 := by rw [key]; exact div_neg_of_neg_of_pos (by linarith) hp
    nlinarith

theorem w_fora_iff {ρ : ℂ} (h : ρ ≠ 0) : 1 < ‖w ρ‖ ↔ ρ.re < 1 / 2 := by
  have hp := normSq_pos h
  have key := norm_w_sq_sub_one h
  have h0 := norm_nonneg (w ρ)
  constructor
  · intro h1
    have : 0 < ‖w ρ‖ ^ 2 - 1 := by nlinarith
    rw [key] at this
    have := (div_pos_iff.mp this)
    rcases this with ⟨a, _⟩ | ⟨_, b⟩
    · linarith
    · linarith
  · intro h1
    have : 0 < ‖w ρ‖ ^ 2 - 1 := by rw [key]; exact div_pos (by linarith) hp
    nlinarith

theorem ne_zero_of_mem_Z {ρ : ℂ} (hρ : ρ ∈ Z) : ρ ≠ 0 := by
  rintro rfl; exact lt_irrefl 0 (by simpa using hρ.2.1)

/-- **HR ⟺ todo zero não trivial tem `|1 − 1/ρ| = 1`.** -/
theorem rh_iff_li_unitario : RiemannHypothesis ↔ ∀ ρ ∈ Z, ‖w ρ‖ = 1 := by
  rw [rh_iff_externa_vazia]
  constructor
  · intro h ρ hρ
    rw [w_unitario_iff (ne_zero_of_mem_Z hρ)]
    by_contra hne
    have hm : ρ ∈ ZE := ⟨hρ, hne⟩
    rw [h] at hm
    exact hm
  · intro h
    ext ρ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hρ, hne⟩
    exact hne ((w_unitario_iff (ne_zero_of_mem_Z hρ)).mp (h ρ hρ))

/-- No círculo unitário, `Re(1 − zⁿ) ≥ 0`. -/
theorem parcela_nao_negativa {z : ℂ} (hz : ‖z‖ = 1) (n : ℕ) : 0 ≤ (1 - z ^ n).re := by
  have h1 : ‖z ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
  have := Complex.re_le_norm (z ^ n)
  rw [h1] at this
  simp only [sub_re, one_re]
  linarith

/-- **Sob HR, cada parcela de Li tem parte real `≥ 0`.** -/
theorem rh_parcelas {n : ℕ} (hRH : RiemannHypothesis) {ρ : ℂ} (hρ : ρ ∈ Z) :
    0 ≤ (1 - w ρ ^ n).re :=
  parcela_nao_negativa ((rh_iff_li_unitario.mp hRH) ρ hρ) n

/-- Fora do círculo, `|1 − zⁿ| → ∞`. -/
theorem parcela_ilimitada {z : ℂ} (hz : 1 < ‖z‖) :
    Tendsto (fun n : ℕ => ‖1 - z ^ n‖) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => ‖z‖ ^ n) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hz
  have hle : ∀ n : ℕ, ‖z‖ ^ n - 1 ≤ ‖1 - z ^ n‖ := by
    intro n
    have := norm_sub_norm_le (z ^ n) 1
    rw [norm_pow, norm_one] at this
    rw [norm_sub_rev]
    exact this
  exact tendsto_atTop_mono hle (tendsto_atTop_add_const_right _ (-1) hpow)

/-- A simetria `ρ ↦ 1 − ρ̄` vira `w ↦ 1/w̄`. -/
theorem w_torcao {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    w (torcao ρ) = (starRingEnd ℂ) (w ρ)⁻¹ := by
  have hc1 : (1 : ℂ) - (starRingEnd ℂ) ρ ≠ 0 := by
    intro h; apply h1
    have := congrArg (starRingEnd ℂ) h
    simp at this
    rw [sub_eq_zero] at this
    exact this.symm
  have hρ1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hc2 : (starRingEnd ℂ) ρ - 1 ≠ 0 := by
    intro h; apply hc1; linear_combination -h
  rw [w_eq h0, inv_div, map_div₀, map_sub, map_one]
  unfold w torcao
  rw [eq_div_iff hc2]
  field_simp
  ring

end ATK.Li

-- Auditoria de axiomas (kernel)
#print axioms ATK.Li.w_eq
#print axioms ATK.Li.norm_w_sq
#print axioms ATK.Li.normSq_pos
#print axioms ATK.Li.norm_w_sq_sub_one
#print axioms ATK.Li.w_unitario_iff
#print axioms ATK.Li.w_dentro_iff
#print axioms ATK.Li.w_fora_iff
#print axioms ATK.Li.ne_zero_of_mem_Z
#print axioms ATK.Li.rh_iff_li_unitario
#print axioms ATK.Li.parcela_nao_negativa
#print axioms ATK.Li.rh_parcelas
#print axioms ATK.Li.parcela_ilimitada
#print axioms ATK.Li.w_torcao
