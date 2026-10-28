import ATK.ModeloParametrico
import ATK.DInfinito

/-!
# ATK-RH — A zeta nas coordenadas trocadas, e `D_∞`

O que o texto encaminhado afirma sobre a zeta depois da troca `T(a + ib) = b + ia`, provado:

* **Cota do texto** (`norm_zeta_sub_one_le`): para `σ = Re s > 1`,
  `|ζ(s) − 1| ≤ 2^{−σ} + 2^{1−σ}/(σ − 1)`; para `σ ≥ 2`, `≤ 3·2^{−σ}` (`norm_zeta_sub_one_le_tres`);
* **`ζ → 1` uniformemente** quando `Re s → ∞` (`zeta_tende_um`);
* **números certificados**: `Re s ≥ 14 ⇒ |ζ(s) − 1| < 10⁻⁴` (`zeta_quatorze`) — cobre todos os zeros trocados
  com `γ ≥ 14`; `Re s ≥ 10¹² ⇒ |ζ(s) − 1| ≤ 3·2^{−10¹²}` (`zeta_trilhao`);
* **zeros trocados não são zeros**: `ρ ∈ Z`, `Im ρ ≥ 1` ou `Im ρ < 0` ⇒ `ζ(T ρ) ≠ 0` (`troca_nao_zero`);
  a função transformada `F = ζ ∘ T` tem os zeros transportados (`F_preserva`);
* **o sistema `ζ(a + ib) = 0 = ζ(b + ia)`** (com o primeiro não trivial) força `0 < a, b < 1`
  (`sistema_trocado`): uma solução exige zeros não triviais com `0 < Im < 1`; sem tais zeros, não há
  solução (`sistema_trocado_sem_solucao`). (Que não existem — o primeiro zero tem `γ = 14,13…` — é
  verificação numérica rigorosa da literatura, não está na Mathlib; fica como hipótese explícita.)
* **`D_∞ ≤ D_N`** para todo `N` (`dInf_le_DN`): qualquer cota certificada de um `D_N` limita `D_∞`.
-/

open Complex Filter Topology Set MeasureTheory

namespace ATK.ZetaTroca

open ATK.ModeloParametrico ATK.ZetaSimetria
open ATK.Conditional.Riemann ATK.ForaDaLinha ATK.FechamentoO1 ATK.BaezDuarteBridge

/-- `Σ_{n≥3} n^{−σ} ≤ 2^{1−σ}/(σ−1)` (comparação soma–integral). -/
theorem soma_cauda_le {σ : ℝ} (hσ : 1 < σ) :
    ∑' n : ℕ, ((n : ℝ) + 3) ^ (-σ) ≤ 2 ^ (1 - σ) / (σ - 1) := by
  refine Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (by positivity) _) fun M => ?_
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-σ)) (Icc (2 : ℝ) (2 + M)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have hs := hanti.sum_le_integral
  have hcast : ∀ i : ℕ, (2 : ℝ) + ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 3 := by
    intro i; push_cast; ring
  simp_rw [hcast] at hs
  have hM : (0 : ℝ) ≤ M := M.cast_nonneg
  have hint : ∫ x in (2 : ℝ)..2 + M, x ^ (-σ) =
      ((2 + (M : ℝ)) ^ (1 - σ) - 2 ^ (1 - σ)) / (1 - σ) := by
    rw [integral_rpow (Or.inr ⟨by intro h; linarith, by
      rw [mem_uIcc]; rintro (h | h) <;> linarith [h.1, h.2]⟩)]
    rw [show -σ + 1 = 1 - σ by ring]
  rw [hint] at hs
  have hp : 0 ≤ (2 + (M : ℝ)) ^ (1 - σ) := Real.rpow_nonneg (by positivity) _
  have e : ((2 + (M : ℝ)) ^ (1 - σ) - 2 ^ (1 - σ)) / (1 - σ) =
      (2 ^ (1 - σ) - (2 + (M : ℝ)) ^ (1 - σ)) / (σ - 1) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]; ring
  rw [e] at hs
  have : (2 ^ (1 - σ) - (2 + (M : ℝ)) ^ (1 - σ)) / (σ - 1) ≤ 2 ^ (1 - σ) / (σ - 1) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  linarith

/-- **A cota do texto**: `|ζ(s) − 1| ≤ 2^{−σ} + 2^{1−σ}/(σ−1)` para `σ = Re s > 1`. -/
theorem norm_zeta_sub_one_le {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s - 1‖ ≤ 2 ^ (-s.re) + 2 ^ (1 - s.re) / (s.re - 1) := by
  set σ := s.re with hσ
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hf
  have hnorm : ∀ n : ℕ, ‖f n‖ = ((n : ℝ) + 1) ^ (-σ) := by
    intro n
    simp only [hf, norm_div, norm_one]
    have e : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_natCast_cpow_of_pos (by omega)]
    push_cast
    rw [Real.rpow_neg (by positivity), one_div]
  have hsumR : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-σ)) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -σ < -1))
    exact h.congr fun n => by push_cast; ring_nf
  have hsum : Summable (fun n => ‖f n‖) := by
    have e : (fun n => ‖f n‖) = fun n : ℕ => ((n : ℝ) + 1) ^ (-σ) := funext hnorm
    rw [e]; exact hsumR
  have hfs : Summable f := hsum.of_norm
  have hf0 : f 0 = 1 := by simp [hf]
  have hzeta : riemannZeta s - 1 = ∑' n, f (n + 1) := by
    rw [hz]; change ∑' n, f n - 1 = _; rw [hfs.tsum_eq_zero_add, hf0]; ring
  rw [hzeta]
  have hsum1 : Summable (fun n => ‖f (n + 1)‖) := (summable_nat_add_iff 1).mpr hsum
  have hs2 : Summable (fun n : ℕ => ((n : ℝ) + 2) ^ (-σ)) :=
    ((summable_nat_add_iff 1).mpr hsumR).congr fun n => by push_cast; ring_nf
  calc ‖∑' n, f (n + 1)‖ ≤ ∑' n, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm hsum1
    _ = ∑' n : ℕ, ((n : ℝ) + 2) ^ (-σ) := by
        congr 1; funext n; rw [hnorm]; push_cast; ring_nf
    _ = 2 ^ (-σ) + ∑' n : ℕ, ((n : ℝ) + 3) ^ (-σ) := by
        rw [hs2.tsum_eq_zero_add]
        congr 1
        · simp
        · congr 1; funext n; push_cast; ring_nf
    _ ≤ 2 ^ (-σ) + 2 ^ (1 - σ) / (σ - 1) := by linarith [soma_cauda_le hs]

/-- Para `σ ≥ 2`: `|ζ(s) − 1| ≤ 3·2^{−σ}`. -/
theorem norm_zeta_sub_one_le_tres {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ 3 * 2 ^ (-s.re) := by
  have h := norm_zeta_sub_one_le (by linarith : 1 < s.re)
  have e : (2 : ℝ) ^ (1 - s.re) = 2 * 2 ^ (-s.re) := by
    rw [sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one]
  have hp : 0 ≤ (2 : ℝ) ^ (-s.re) := by positivity
  have hd : 2 ^ (1 - s.re) / (s.re - 1) ≤ (2 : ℝ) ^ (1 - s.re) :=
    div_le_self (by positivity) (by linarith)
  rw [e] at h hd
  linarith

/-- **`ζ → 1` uniformemente** quando `Re s → ∞`. -/
theorem zeta_tende_um {ε : ℝ} (hε : 0 < ε) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ ≤ s.re → ‖riemannZeta s - 1‖ < ε := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (3 / ε) (by norm_num : (1 : ℝ) < 2)
  refine ⟨max 2 n, fun s hs => ?_⟩
  have h2 : 2 ≤ s.re := le_trans (le_max_left _ _) hs
  have hn' : (n : ℝ) ≤ s.re := le_trans (le_max_right _ _) hs
  have hb := norm_zeta_sub_one_le_tres h2
  have hpow : (2 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-(n : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have e : (2 : ℝ) ^ (-(n : ℝ)) = ((2 : ℝ) ^ n)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  have h2n : 0 < (2 : ℝ) ^ n := by positivity
  have h3 : 3 * ((2 : ℝ) ^ n)⁻¹ < ε := by
    rw [← div_eq_mul_inv, div_lt_iff₀ h2n]
    rw [div_lt_iff₀ hε] at hn
    linarith
  have := mul_le_mul_of_nonneg_left (hpow.trans e.le) (by norm_num : (0 : ℝ) ≤ 3)
  linarith

/-- **Certificado**: `Re s ≥ 14 ⇒ |ζ(s) − 1| < 10⁻⁴`. -/
theorem zeta_quatorze {s : ℂ} (hs : 14 ≤ s.re) : ‖riemannZeta s - 1‖ < 1 / 10000 := by
  have h := norm_zeta_sub_one_le (by linarith : 1 < s.re)
  have h1 : (2 : ℝ) ^ (-s.re) ≤ 2 ^ (-(14 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ^ (1 - s.re) ≤ 2 ^ (-(13 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2 : ℝ) ^ (1 - s.re) / (s.re - 1) ≤ 2 ^ (-(13 : ℝ)) / 13 := by
    calc (2 : ℝ) ^ (1 - s.re) / (s.re - 1) ≤ 2 ^ (-(13 : ℝ)) / (s.re - 1) :=
          div_le_div_of_nonneg_right h2 (by linarith)
      _ ≤ 2 ^ (-(13 : ℝ)) / 13 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  have e14 : (2 : ℝ) ^ (-(14 : ℝ)) = 1 / 16384 := by
    rw [Real.rpow_neg (by norm_num), show (14 : ℝ) = ((14 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]; norm_num
  have e13 : (2 : ℝ) ^ (-(13 : ℝ)) = 1 / 8192 := by
    rw [Real.rpow_neg (by norm_num), show (13 : ℝ) = ((13 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]; norm_num
  rw [e14] at h1
  rw [e13] at h3
  linarith

/-- **Escala de um trilhão**: `Re s ≥ 10¹² ⇒ |ζ(s) − 1| ≤ 3·2^{−10¹²}`. -/
theorem zeta_trilhao {s : ℂ} (hs : (10 : ℝ) ^ 12 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ 3 * 2 ^ (-(10 : ℝ) ^ 12) := by
  have h := norm_zeta_sub_one_le_tres (by nlinarith : 2 ≤ s.re)
  have hp : (2 : ℝ) ^ (-s.re) ≤ 2 ^ (-(10 : ℝ) ^ 12) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  linarith

/-- A função transformada `F = ζ ∘ T` tem os zeros transportados. -/
theorem F_preserva (z : ℂ) : riemannZeta (troca (troca z)) = riemannZeta z := by
  rw [troca_troca]

/-- **Zeros trocados não são zeros**: `ρ ∈ Z` com `Im ρ ≥ 1` ou `Im ρ < 0` ⇒ `ζ(T ρ) ≠ 0`. -/
theorem troca_nao_zero {ρ : ℂ} (hρ : ρ ∈ Z) (h : 1 ≤ ρ.im ∨ ρ.im < 0) :
    riemannZeta (troca ρ) ≠ 0 := by
  intro hz
  obtain ⟨-, h0, -⟩ := hρ
  rcases h with h | h
  · exact riemannZeta_ne_zero_of_one_le_re (by rw [troca_re]; exact h) hz
  · obtain ⟨n, hn⟩ := zero_trivial_de_re_nao_pos hz (by rw [troca_re]; linarith)
    have := congrArg Complex.im hn
    rw [troca_im] at this
    simp at this
    linarith

/-- Um zero trocado com `γ ≥ 14` dá `|ζ(T ρ) − 1| < 10⁻⁴`. -/
theorem troca_perto_de_um {z : ℂ} (hz : 14 ≤ z.im) : ‖riemannZeta (troca z) - 1‖ < 1 / 10000 :=
  zeta_quatorze (by rw [troca_re]; exact hz)

/-- **O sistema `ζ(a + ib) = 0 = ζ(b + ia)`** força `0 < a < 1` e `0 < b < 1`. -/
theorem sistema_trocado {a b : ℝ} (h1 : riemannZeta ((a : ℂ) + (b : ℂ) * I) = 0)
    (ht : ¬ Trivial ((a : ℂ) + (b : ℂ) * I)) (h2 : riemannZeta ((b : ℂ) + (a : ℂ) * I) = 0) :
    0 < a ∧ a < 1 ∧ 0 < b ∧ b < 1 := by
  obtain ⟨ha0, ha1, -, -, -, -⟩ := ATK.ZeroIncognito.sistema h1 ht
  have hb1 : b < 1 := by
    by_contra hb
    push Not at hb
    exact riemannZeta_ne_zero_of_one_le_re (by simpa using hb) h2
  have hb0 : 0 < b := by
    by_contra hb
    push Not at hb
    obtain ⟨n, hn⟩ := zero_trivial_de_re_nao_pos h2 (by simpa using hb)
    have := congrArg Complex.im hn
    simp at this
    linarith
  exact ⟨ha0, ha1, hb0, hb1⟩

/-- Sem zeros não triviais de altura `|γ| < 1`, o sistema trocado não tem solução. -/
theorem sistema_trocado_sem_solucao (hbaixo : ∀ ρ ∈ Z, 1 ≤ |ρ.im|) {a b : ℝ}
    (h1 : riemannZeta ((a : ℂ) + (b : ℂ) * I) = 0) (ht : ¬ Trivial ((a : ℂ) + (b : ℂ) * I))
    (h2 : riemannZeta ((b : ℂ) + (a : ℂ) * I) = 0) : False := by
  obtain ⟨ha0, ha1, hb0, hb1⟩ := sistema_trocado h1 ht h2
  have hZ : ((a : ℂ) + (b : ℂ) * I) ∈ Z := ⟨h1, by simpa using ha0, by simpa using ha1⟩
  have := hbaixo _ hZ
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, zero_add,
    add_zero] at this
  rw [abs_of_pos hb0] at this
  linarith

/-! ### `D_∞` -/

theorem dInf_le_DN (N : ℕ) : ATK.DInfinito.dInf ≤ DN N :=
  ciInf_le ⟨0, by rintro _ ⟨M, rfl⟩; exact DN_nonneg M⟩ N

/-- Qualquer cota certificada de um `D_N` limita `D_∞`. -/
theorem dInf_le_de_cota {N : ℕ} {b : ℝ} (h : DN N ≤ b) : ATK.DInfinito.dInf ≤ b :=
  (dInf_le_DN N).trans h

end ATK.ZetaTroca

#print axioms ATK.ZetaTroca.soma_cauda_le
#print axioms ATK.ZetaTroca.norm_zeta_sub_one_le
#print axioms ATK.ZetaTroca.norm_zeta_sub_one_le_tres
#print axioms ATK.ZetaTroca.zeta_tende_um
#print axioms ATK.ZetaTroca.zeta_quatorze
#print axioms ATK.ZetaTroca.zeta_trilhao
#print axioms ATK.ZetaTroca.F_preserva
#print axioms ATK.ZetaTroca.troca_nao_zero
#print axioms ATK.ZetaTroca.troca_perto_de_um
#print axioms ATK.ZetaTroca.sistema_trocado
#print axioms ATK.ZetaTroca.sistema_trocado_sem_solucao
#print axioms ATK.ZetaTroca.dInf_le_DN
#print axioms ATK.ZetaTroca.dInf_le_de_cota
