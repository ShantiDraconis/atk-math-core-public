import ATK.ZeroClasses.FaixaPecas1
import ATK.ZeroClasses.FaixaPecas2
import ATK.ZeroClasses.FaixaPecas3
import ATK.ZeroClasses.Escalas

/-!
# Nenhum zero de `ζ` na faixa crítica até a altura 13 (rodada 29)

* `faixa_ate_13`: `|ζ(s)| ≥ 1/50` em `[½, 1] × [43/50, 13]` — 50 retângulos (`FaixaPecas1`–`3`), cada um
  certificado por `peca_ret`: cota grosseira na região de Cauchy, `‖ζ′‖ ≤ B/r`, e uma malha de centros em que o
  retângulo certificado de `ζ(σ + it)` (`σ` racional, `mem_zetaIG`) tem norma `≥ (B/r)h + 1/50`. Ao todo
  930 avaliações certificadas, todas verificadas pelo kernel (`decide +kernel`);
* `cota_metade`, `sem_zeros_pos`: pela torção `s ↦ 1 − s̄`, também a metade `0 < Re s < ½`;
* **`faixa_sem_zeros`: `ζ(s) ≠ 0` para `0 < Re s < 1` e `|Im s| ≤ 13`** (a faixa baixa `t² < ¾` vem de
  `ATK.ZetaRetangulo.zeta_ne_zero_baixo`; `Im s < 0` pela conjugação);
* **`verificado_13`: a hipótese nomeada `VerificadoAte 13` (Platt–Trudgian) passa a ser teorema**;
* `zeros_acima_13`: todo zero não trivial tem `|Im ρ| > 13`; `primeiro_zero_entre`: com o certificado de
  `ρ₁` (§4f), o zero não trivial de menor altura positiva está entre `13` e `14,1347…`;
* `m_pos_ate_13`: `m_n > 0` para todo `4 ≤ n ≤ 13`; `novo_primeiro_ponto_14`: o primeiro ponto aberto passa a ser
  `m₁₄ > 0`.

Classificação: **parcial** (RH verificada, sem hipótese, até a altura 13 — vacuamente: não há zeros). Não é RH.
-/

open Complex ComplexConjugate Set

namespace ATK.ZeroClasses.Faixa

open ATK.ZeroClasses.Regions

/-- **`|ζ| ≥ 1/50` em `[½, 1] × [43/50, 13]`.** -/
theorem faixa_ate_13 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((43 / 50 : ℚ) : ℝ) ((13 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((2 : ℚ) : ℝ)) faixa_0 (ret_split_im (tm := ((3 : ℚ) : ℝ)) faixa_1 (ret_split_im (tm := ((4 : ℚ) : ℝ)) faixa_2 (ret_split_im (tm := ((5 : ℚ) : ℝ)) faixa_3 (ret_split_im (tm := ((6 : ℚ) : ℝ)) faixa_4 (ret_split_im (tm := ((7 : ℚ) : ℝ)) faixa_5 (ret_split_im (tm := ((8 : ℚ) : ℝ)) faixa_6 (ret_split_im (tm := ((9 : ℚ) : ℝ)) faixa_7 (ret_split_im (tm := ((10 : ℚ) : ℝ)) faixa_8 (ret_split_im (tm := ((11 : ℚ) : ℝ)) faixa_9 (ret_split_im (tm := ((12 : ℚ) : ℝ)) faixa_10 (faixa_11)))))))))))

theorem cota_metade {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 1) (h3 : 43 / 50 ≤ s.im) (h4 : s.im ≤ 13) :
    (1 / 50 : ℝ) ≤ ‖riemannZeta s‖ := by
  have := faixa_ate_13 s ⟨by push_cast; linarith, by push_cast; linarith, by push_cast; linarith,
    by push_cast; linarith⟩
  push_cast at this
  exact this

theorem im_torcao (s : ℂ) : (ATK.ZetaSimetria.torcao s).im = s.im := by
  unfold ATK.ZetaSimetria.torcao
  simp

theorem sem_zeros_pos {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (h3 : 43 / 50 ≤ s.im) (h4 : s.im ≤ 13) :
    riemannZeta s ≠ 0 := by
  intro hz
  rcases le_or_gt (1 / 2) s.re with hr | hr
  · have := cota_metade hr h1.le h3 h4
    rw [hz, norm_zero] at this
    norm_num at this
  · have hT := ATK.ZetaSimetria.torcao_mem_Z (⟨hz, h0, h1⟩ : s ∈ ATK.ZetaSimetria.Z)
    have e := ATK.ZetaSimetria.re_torcao s
    have := cota_metade (s := ATK.ZetaSimetria.torcao s) (by rw [e]; linarith) (by rw [e]; linarith)
      (by rw [im_torcao]; exact h3) (by rw [im_torcao]; exact h4)
    rw [hT.1, norm_zero] at this
    norm_num at this

/-- **Não há zero de `ζ` na faixa crítica com `|Im s| ≤ 13`.** -/
theorem faixa_sem_zeros {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (ht : |s.im| ≤ 13) :
    riemannZeta s ≠ 0 := by
  by_cases hb : s.im ^ 2 < 3 / 4
  · exact ATK.ZetaRetangulo.zeta_ne_zero_baixo h0 h1 hb
  have hb' : 43 / 50 ≤ |s.im| := by
    by_contra hc
    have hc' : |s.im| < 43 / 50 := lt_of_not_ge hc
    have h2 : |s.im| ^ 2 < (43 / 50) ^ 2 := pow_lt_pow_left₀ hc' (abs_nonneg _) (by norm_num)
    rw [sq_abs] at h2
    exact hb (by linarith)
  rcases le_or_gt 0 s.im with hi | hi
  · rw [abs_of_nonneg hi] at hb' ht
    exact sem_zeros_pos h0 h1 hb' ht
  · rw [abs_of_neg hi] at hb' ht
    intro hz
    have hc : riemannZeta (conj s) = 0 := by rw [riemannZeta_conj, hz, map_zero]
    exact sem_zeros_pos (s := conj s) (by simpa using h0) (by simpa using h1) (by simpa using hb')
      (by simpa using ht) hc

/-- **`VerificadoAte 13` é teorema.** -/
theorem verificado_13 : ATK.ZeroClasses.Escalas.VerificadoAte 13 := fun ρ hρ hT =>
  absurd hρ.1 (faixa_sem_zeros hρ.2.1 hρ.2.2 hT)

/-- **Todo zero não trivial tem `|Im ρ| > 13`.** -/
theorem zeros_acima_13 : ∀ ρ ∈ ATK.ZetaSimetria.Z, 13 < |ρ.im| := fun ρ hρ => by
  by_contra h
  exact faixa_sem_zeros hρ.2.1 hρ.2.2 (le_of_not_gt h) hρ.1

/-- **O primeiro zero**: `ρ₁` (na linha, a menos de `10⁻⁶` de `½ + 14,1347251417i`) existe e todo zero não trivial
tem altura `> 13`. -/
theorem primeiro_zero_entre :
    (∃ ρ ∈ ATK.ZetaSimetria.Z, ρ.re = 1 / 2 ∧ ρ ∈ Metric.closedBall ATK.ZeroCert.z0 ((ATK.ZeroCert.rr : ℚ) : ℝ)) ∧
      ∀ ρ ∈ ATK.ZetaSimetria.Z, 13 < |ρ.im| := by
  obtain ⟨ρ, hρ, hre, hb, -⟩ := ATK.ZeroCert.zero_na_linha
  exact ⟨⟨ρ, hρ, hre, hb⟩, zeros_acima_13⟩

/-- **`m_n > 0` para todo `4 ≤ n ≤ 13`.** -/
theorem m_pos_ate_13 {n : ℕ} (h4 : 4 ≤ n) (h13 : n ≤ 13) : 0 < m n := by
  rw [m_pos_iff h4]
  intro s hs
  obtain ⟨k1, k2, k3, k4⟩ := hs
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hn13 : (n : ℝ) ≤ 13 := by exact_mod_cast h13
  apply faixa_sem_zeros (by linarith) (by linarith)
  rw [abs_le]
  constructor <;> linarith

/-- **O novo primeiro ponto aberto é `m₁₄ > 0`.** -/
theorem novo_primeiro_ponto_14 :
    (∀ n : ℕ, 4 ≤ n → n ≤ 13 → 0 < m n) ∧ (0 < m 14 ↔ ∀ s ∈ K 14, riemannZeta s ≠ 0) ∧
      (RiemannHypothesis → 0 < m 14) :=
  ⟨fun _ h4 h13 => m_pos_ate_13 h4 h13, m_pos_iff (by norm_num), fun h => rh_iff_m_pos.mp h 14 (by norm_num)⟩

end ATK.ZeroClasses.Faixa

#print axioms ATK.ZeroClasses.Faixa.faixa_ate_13
#print axioms ATK.ZeroClasses.Faixa.cota_metade
#print axioms ATK.ZeroClasses.Faixa.im_torcao
#print axioms ATK.ZeroClasses.Faixa.sem_zeros_pos
#print axioms ATK.ZeroClasses.Faixa.faixa_sem_zeros
#print axioms ATK.ZeroClasses.Faixa.verificado_13
#print axioms ATK.ZeroClasses.Faixa.zeros_acima_13
#print axioms ATK.ZeroClasses.Faixa.primeiro_zero_entre
#print axioms ATK.ZeroClasses.Faixa.m_pos_ate_13
#print axioms ATK.ZeroClasses.Faixa.novo_primeiro_ponto_14
