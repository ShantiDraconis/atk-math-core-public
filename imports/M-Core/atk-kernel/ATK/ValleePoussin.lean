import ATK.ZetaLog
import ATK.ForaDaLinha

/-!
# ATK — A lei de de la Vallée Poussin (forma logarítmica) aplicada aos zeros fora da linha

Junta a região logarítmica (`ATK.ZetaLog`) ao anti-produto de RH (`ATK.ForaDaLinha`):

* `cl_pos`: a largura `c(t) = 1/(256 e⁵ (ℓ² + 7ℓ + 13)⁴ (ℓ + 7))`, `ℓ = log(3|t|)`, é positiva;
* **`log_vence_poly`**: para `|t| ≥ 2000`, `c(t)` é **maior** que a largura polinomial
  `1/(256 (9 + 4|t|)⁴ (3 + 3|t|))` de `ATK.ZetaRegiao` (numericamente já a partir de `|t| ≈ 31,3`);
* `evita_log`: um zero fora da linha com `|Im ρ| ≥ 4` evita as bordas logarítmicas
  `Re ρ ≤ c(t)` e `Re ρ ≥ 1 − c(t)`;
* **`m_ge_log`**, **`piso_DN_log`**: a condensação `D_N ≥ m(ρ)²` ganha um piso explícito que só
  depende de `Re ρ` e da altura: `m(ρ) ≥ 1/(|ρ|(1/√(2σ − 1) + 1/c(t)))`.

O que **não** muda: `m` é uma função fixa de `ρ`; a região só restringe onde um zero fora da linha
pode estar. Perto de `σ = 1/2` o piso continua indo a `0`, então não há piso uniforme para `D_N`:
escolher entre os estados `zero` e `finito` de `D_N` continua sendo RH (O1).
-/

open Complex

namespace ATK.ValleePoussin

open ATK.ZetaSimetria ATK.ZetaRegiao ATK.ZetaLog ATK.ForaDaLinha ATK.BaezDuarteBridge
  ATK.RiemannConcrete ATK.Conditional.Riemann

theorem ell_ge {t : ℝ} (ht : 4 ≤ |t|) : 2 < Real.log (3 * |t|) := by
  have : (8 : ℝ) ≤ 3 * |t| := by linarith
  exact log_oito.trans_le (Real.log_le_log (by norm_num) this)

theorem cl_pos {t : ℝ} (ht : 4 ≤ |t|) : 0 < cl t := by
  have hℓ := ell_ge ht
  have hK := (Kc_ge (by linarith : (0 : ℝ) ≤ Real.log (3 * |t|))).1
  have hB := Bc_ge (by linarith : (0 : ℝ) ≤ Real.log (3 * |t|))
  unfold cl
  have : 0 < 256 * Kc (Real.log (3 * |t|)) ^ 4 * Bc (Real.log (3 * |t|)) := by positivity
  positivity

/-- `log(3|t|)⁹ ≤ 9⁹·3|t|` (de `log x ≤ 9·x^{1/9}`). -/
theorem ell_pow_le {t : ℝ} (ht : 4 ≤ |t|) : Real.log (3 * |t|) ^ 9 ≤ 9 ^ 9 * (3 * |t|) := by
  have hx : 0 ≤ 3 * |t| := by positivity
  have hℓ := ell_ge ht
  have h := Real.log_le_rpow_div hx (ε := ((9 : ℕ) : ℝ)⁻¹) (by positivity)
  have e1 : (3 * |t|) ^ (((9 : ℕ) : ℝ)⁻¹) / ((9 : ℕ) : ℝ)⁻¹ =
      9 * (3 * |t|) ^ (((9 : ℕ) : ℝ)⁻¹) := by
    rw [div_inv_eq_mul]; push_cast; ring
  rw [e1] at h
  calc Real.log (3 * |t|) ^ 9 ≤ (9 * (3 * |t|) ^ (((9 : ℕ) : ℝ)⁻¹)) ^ 9 :=
        pow_le_pow_left₀ (by linarith) h 9
    _ = 9 ^ 9 * ((3 * |t|) ^ (((9 : ℕ) : ℝ)⁻¹)) ^ 9 := by ring
    _ = 9 ^ 9 * (3 * |t|) := by rw [Real.rpow_inv_natCast_pow hx (by norm_num)]

/-- **A região logarítmica supera a polinomial** a partir de `|t| = 2000`. -/
theorem log_vence_poly {t : ℝ} (ht : 2000 ≤ |t|) : 1 / (256 * A t) < cl t := by
  have ht4 : 4 ≤ |t| := by linarith
  have hc := cl_ge ht4
  have hp := ell_pow_le ht4
  have hℓ := ell_ge ht4
  have hℓ9 : 0 < Real.log (3 * |t|) ^ 9 := by positivity
  have hpos : 0 ≤ |t| := abs_nonneg t
  have h1 : 1 / (10 ^ 9 * (9 ^ 9 * (3 * |t|))) ≤ 1 / (10 ^ 9 * Real.log (3 * |t|) ^ 9) :=
    one_div_le_one_div_of_le (by positivity) (by gcongr)
  have hA : 768 * |t| ^ 5 ≤ A t := by
    unfold A
    have h4 : (4 * |t|) ^ 4 ≤ (9 + 4 * |t|) ^ 4 := pow_le_pow_left₀ (by positivity) (by linarith) 4
    have h3 : 3 * |t| ≤ 3 + 3 * |t| := by linarith
    calc 768 * |t| ^ 5 = (4 * |t|) ^ 4 * (3 * |t|) := by ring
      _ ≤ (9 + 4 * |t|) ^ 4 * (3 + 3 * |t|) := by gcongr
  have ht4' : (2000 : ℝ) ^ 4 ≤ |t| ^ 4 := pow_le_pow_left₀ (by norm_num) ht 4
  have hbig : 10 ^ 9 * (9 ^ 9 * (3 * |t|)) < 256 * A t := by
    have : 10 ^ 9 * (9 ^ 9 * (3 * |t|)) < 256 * (768 * |t| ^ 5) := by
      have e : 256 * (768 * |t| ^ 5) = 196608 * |t| ^ 4 * |t| := by ring
      rw [e]
      have : (10 : ℝ) ^ 9 * (9 ^ 9 * 3) < 196608 * |t| ^ 4 := by
        have : (10 : ℝ) ^ 9 * (9 ^ 9 * 3) < 196608 * 2000 ^ 4 := by norm_num
        linarith
      nlinarith
    linarith
  have h2 : 1 / (256 * A t) < 1 / (10 ^ 9 * (9 ^ 9 * (3 * |t|))) :=
    one_div_lt_one_div_of_lt (by positivity) hbig
  linarith

/-- Um zero fora da linha com `|Im ρ| ≥ 4` evita as bordas logarítmicas. -/
theorem evita_log (ρ : ZeroFora) (ht : 4 ≤ |ρ.1.im|) :
    cl ρ.1.im < ρ.1.re ∧ ρ.1.re < 1 - cl ρ.1.im :=
  faixa_log ρ.1 ρ.2.1 ht

/-- **Piso de `m(ρ)` pela região logarítmica**: `m(ρ) ≥ 1/(|ρ|(1/√(2σ − 1) + 1/c(t)))`. -/
theorem m_ge_log {ρ : ℂ} (hz : ρ ∈ Z) (h0 : 1 / 2 < ρ.re) (ht : 4 ≤ |ρ.im|) :
    1 / (‖ρ‖ * (1 / Real.sqrt (2 * ρ.re - 1) + 1 / cl ρ.im)) ≤ m ρ := by
  have hb := (faixa_log ρ hz ht).2
  have hc0 := cl_pos ht
  have hρ : ρ ≠ 0 := by intro h; rw [h, zero_re] at h0; linarith
  have hn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have ha : 0 < Real.sqrt (2 * ρ.re - 1) := Real.sqrt_pos.mpr (by linarith)
  have h1 : 0 < 1 - ρ.re := by linarith
  have hle : 1 / (1 - ρ.re) ≤ 1 / cl ρ.im := one_div_le_one_div_of_le hc0 (by linarith)
  unfold m
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith) hn.le

/-- **Condensação com piso explícito**: um zero `ρ` com `1/2 < Re ρ` e `|Im ρ| ≥ 4` força, para
todo `N`, `D_N ≥ (1/(|ρ|(1/√(2σ − 1) + 1/c(t))))²`. -/
theorem piso_DN_log {ρ : ℂ} (hz : ρ ∈ Z) (h0 : 1 / 2 < ρ.re) (ht : 4 ≤ |ρ.im|) (N : ℕ) :
    (1 / (‖ρ‖ * (1 / Real.sqrt (2 * ρ.re - 1) + 1 / cl ρ.im))) ^ 2 ≤ DN N := by
  have hm := m_ge_log hz h0 ht
  have hc0 := cl_pos ht
  have h0' : 0 ≤ 1 / (‖ρ‖ * (1 / Real.sqrt (2 * ρ.re - 1) + 1 / cl ρ.im)) := by positivity
  exact (pow_le_pow_left₀ h0' hm 2).trans (piso_DN hz.1 h0 hz.2.2 N)

end ATK.ValleePoussin

#print axioms ATK.ValleePoussin.ell_ge
#print axioms ATK.ValleePoussin.cl_pos
#print axioms ATK.ValleePoussin.ell_pow_le
#print axioms ATK.ValleePoussin.log_vence_poly
#print axioms ATK.ValleePoussin.evita_log
#print axioms ATK.ValleePoussin.m_ge_log
#print axioms ATK.ValleePoussin.piso_DN_log
