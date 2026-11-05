import ATK.FracoesGama
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# ATK — O par recorde 12 363 187 982 787/788 inteiro em frações (rodada 104)

As bolas da Arb do par (do teorema `par_mais_fragil_continuacao8` de `clay-riemann-proof`; aqui hipóteses
`h₁`, `h₂`, nada de `ζ`) são `|γ₁ − c₁| ≤ 265·10⁻²⁰`, `|γ₂ − c₂| ≤ 379·10⁻²⁰`, com parte inteira comum
`E = 3 000 183 404 278`. Tudo abaixo é consequência exata, em `ℚ`/`ℝ`, dessas duas desigualdades:

* **as caudas `{γ}` em fração contínua** (`cauda1_fc`, `cauda2_fc`): 16 e 17 quocientes certificados e o resto
  num intervalo racional; as duas frações coincidem em `[0; 1, 3, 7]` e se separam no 4º quociente
  (`separam_no_quarto`);
* **a fração mais simples de cada bola** (`simples1`, `simples2`): `314 849 491/415 434 260` e
  `296 762 215/391 380 514` estão nas bolas e **nenhuma fração de denominador menor está** (vizinhos de Farey,
  `farey_min`);
* **a distância** (`delta_bolas`, `delta_fc`, `simples_delta`): `Δγ ∈ 3 643 183 291 679/10¹⁶ ± 644·10⁻²⁰`,
  `Δγ = [0; 2744, 1, 5, 1, 3, 2, 1, 6, 1, 10, 6, x₁₂]`, e `97 021/266 308 314` é a fração mais simples no erro;
* **`λ ≈ −Δγ²/2`** (`lambda_bolas`) em racionais exatos;
* **o espaçamento normalizado** `s = Δγ · log(γ₁/2π)/(2π)` (`s_novo`): `3/2000 < s < 1/600`, e o recorde
  anterior (12 363 167 808 945/946) tem `s > 1/400` (`s_anterior`), logo **o novo par é mais apertado**
  (`recorde`). Usa `3,14 < π < 3,15` e `2,7182818283 < e < 2,7182818286` (Mathlib).

Classificação: **consequência** (aritmética certificada sobre as bolas). Nada aqui é sobre `Re ρ`: RH continua
`OPEN_MATH`.
-/

namespace ATK.Fracoes.ParRecorde

open ATK.Fracoes.Gama Real

/-- Parte inteira comum do par. -/
def E : ℤ := 3000183404278

/-- **Vizinhos de Farey**: se `a/b < p/q < c/d` com `bc − ad = 1`, então `q ≥ b + d`. -/
theorem farey_min {a b c d p q : ℤ} (hb : 0 < b) (hd : 0 < d) (hdet : b * c - a * d = 1)
    (h1 : a * q < p * b) (h2 : p * d < c * q) : b + d ≤ q := by
  have e1 : 1 ≤ p * b - a * q := by linarith
  have e2 : 1 ≤ c * q - p * d := by linarith
  have key : q = b * (c * q - p * d) + d * (p * b - a * q) := by linear_combination (-q) * hdet
  nlinarith [mul_le_mul_of_nonneg_left e2 hb.le, mul_le_mul_of_nonneg_left e1 hd.le]

/-- Versão racional: toda fração `p/q` (`q > 0`) em `[lo, hi] ⊂ (a/b, c/d)` tem `q ≥ b + d`. -/
theorem farey_min_q {a b c d : ℤ} {lo hi : ℚ} (hb : 0 < b) (hd : 0 < d) (hdet : b * c - a * d = 1)
    (hlo : (a : ℚ) / b < lo) (hhi : hi < (c : ℚ) / d) {p q : ℤ} (hq : 0 < q)
    (h1 : lo ≤ (p : ℚ) / q) (h2 : (p : ℚ) / q ≤ hi) : b + d ≤ q := by
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  refine farey_min (p := p) hb hd hdet ?_ ?_
  · have : (a : ℚ) / b < p / q := lt_of_lt_of_le hlo h1
    rw [div_lt_div_iff₀ hb' hq'] at this
    exact_mod_cast this
  · have : (p : ℚ) / q < c / d := lt_of_le_of_lt h2 hhi
    rw [div_lt_div_iff₀ hq' hd'] at this
    exact_mod_cast this


/-- **Cauda de `γ₁`**: `[0; 1, 3, 7, 1, 2, 7, 2, 1, 1, 4, 17, 10, 2, 1, 3, 1, x_17]`, `x_17 ∈ [8.37855, 9.25772]`. -/
theorem cauda1_fc {γ₁ : ℝ} (h₁ : |γ₁ - 300018340427875788041891393358 / 10 ^ 17| ≤ 265 / 10 ^ 20) :
      ⌊passo^[0] (γ₁ - E)⌋ = 0 ∧
      ⌊passo^[1] (γ₁ - E)⌋ = 1 ∧
      ⌊passo^[2] (γ₁ - E)⌋ = 3 ∧
      ⌊passo^[3] (γ₁ - E)⌋ = 7 ∧
      ⌊passo^[4] (γ₁ - E)⌋ = 1 ∧
      ⌊passo^[5] (γ₁ - E)⌋ = 2 ∧
      ⌊passo^[6] (γ₁ - E)⌋ = 7 ∧
      ⌊passo^[7] (γ₁ - E)⌋ = 2 ∧
      ⌊passo^[8] (γ₁ - E)⌋ = 1 ∧
      ⌊passo^[9] (γ₁ - E)⌋ = 1 ∧
      ⌊passo^[10] (γ₁ - E)⌋ = 4 ∧
      ⌊passo^[11] (γ₁ - E)⌋ = 17 ∧
      ⌊passo^[12] (γ₁ - E)⌋ = 10 ∧
      ⌊passo^[13] (γ₁ - E)⌋ = 2 ∧
      ⌊passo^[14] (γ₁ - E)⌋ = 1 ∧
      ⌊passo^[15] (γ₁ - E)⌋ = 3 ∧
      ⌊passo^[16] (γ₁ - E)⌋ = 1 ∧
      (430714988867 / 51406891183 : ℝ) ≤ passo^[17] (γ₁ - E) ∧ passo^[17] (γ₁ - E) ≤ (434252755933 / 46907084017 : ℝ) := by
  rw [abs_le] at h₁
  obtain ⟨ha, hb⟩ := h₁
  norm_num at ha hb
  have hE : ((E : ℤ) : ℝ) = 3000183404278 := by norm_num [E]
  have l0 : (15157608378278671547 / 20000000000000000000 : ℝ) ≤ passo^[0] (γ₁ - E) := by simp only [Function.iterate_zero, id]; linarith
  have u0 : passo^[0] (γ₁ - E) ≤ (15157608378278671653 / 20000000000000000000 : ℝ) := by simp only [Function.iterate_zero, id]; linarith
  obtain ⟨f0, l1, u1⟩ := passo_iter (x := γ₁ - E) (lo' := (20000000000000000000 / 15157608378278671653 : ℝ)) (hi' := (20000000000000000000 / 15157608378278671547 : ℝ)) 0 0
    (by norm_num) (by norm_num) l0 u0 (by norm_num) (by norm_num)
  obtain ⟨f1, l2, u2⟩ := passo_iter (x := γ₁ - E) (lo' := (15157608378278671547 / 4842391621721328453 : ℝ)) (hi' := (15157608378278671653 / 4842391621721328347 : ℝ)) 1 1
    (by norm_num) (by norm_num) l1 u1 (by norm_num) (by norm_num)
  obtain ⟨f2, l3, u3⟩ := passo_iter (x := γ₁ - E) (lo' := (4842391621721328347 / 630433513114686612 : ℝ)) (hi' := (4842391621721328453 / 630433513114686188 : ℝ)) 3 2
    (by norm_num) (by norm_num) l2 u2 (by norm_num) (by norm_num)
  obtain ⟨f3, l4, u4⟩ := passo_iter (x := γ₁ - E) (lo' := (630433513114686188 / 429357029918525137 : ℝ)) (hi' := (630433513114686612 / 429357029918522063 : ℝ)) 7 3
    (by norm_num) (by norm_num) l3 u3 (by norm_num) (by norm_num)
  obtain ⟨f4, l5, u5⟩ := passo_iter (x := γ₁ - E) (lo' := (429357029918522063 / 201076483196164549 : ℝ)) (hi' := (429357029918525137 / 201076483196161051 : ℝ)) 1 4
    (by norm_num) (by norm_num) l4 u4 (by norm_num) (by norm_num)
  obtain ⟨f5, l6, u6⟩ := passo_iter (x := γ₁ - E) (lo' := (201076483196161051 / 27204063526203035 : ℝ)) (hi' := (201076483196164549 / 27204063526192965 : ℝ)) 2 5
    (by norm_num) (by norm_num) l5 u5 (by norm_num) (by norm_num)
  obtain ⟨f6, l7, u7⟩ := passo_iter (x := γ₁ - E) (lo' := (27204063526192965 / 10648038512813794 : ℝ)) (hi' := (27204063526203035 / 10648038512739806 : ℝ)) 7 6
    (by norm_num) (by norm_num) l6 u6 (by norm_num) (by norm_num)
  obtain ⟨f7, l8, u8⟩ := passo_iter (x := γ₁ - E) (lo' := (10648038512739806 / 5907986500723423 : ℝ)) (hi' := (10648038512813794 / 5907986500565377 : ℝ)) 2 7
    (by norm_num) (by norm_num) l7 u7 (by norm_num) (by norm_num)
  obtain ⟨f8, l9, u9⟩ := passo_iter (x := γ₁ - E) (lo' := (5907986500565377 / 4740052012248417 : ℝ)) (hi' := (5907986500723423 / 4740052012016383 : ℝ)) 1 8
    (by norm_num) (by norm_num) l8 u8 (by norm_num) (by norm_num)
  obtain ⟨f9, l10, u10⟩ := passo_iter (x := γ₁ - E) (lo' := (4740052012016383 / 1167934488707040 : ℝ)) (hi' := (4740052012248417 / 1167934488316960 : ℝ)) 1 9
    (by norm_num) (by norm_num) l9 u9 (by norm_num) (by norm_num)
  obtain ⟨f10, l11, u11⟩ := passo_iter (x := γ₁ - E) (lo' := (1167934488316960 / 68314058980577 : ℝ)) (hi' := (1167934488707040 / 68314057188223 : ℝ)) 4 10
    (by norm_num) (by norm_num) l10 u10 (by norm_num) (by norm_num)
  obtain ⟨f11, l12, u12⟩ := passo_iter (x := γ₁ - E) (lo' := (68314057188223 / 6595516507249 : ℝ)) (hi' := (68314058980577 / 6595485647151 : ℝ)) 17 11
    (by norm_num) (by norm_num) l11 u11 (by norm_num) (by norm_num)
  obtain ⟨f12, l13, u13⟩ := passo_iter (x := γ₁ - E) (lo' := (6595485647151 / 2359202509067 : ℝ)) (hi' := (6595516507249 / 2358892115733 : ℝ)) 10 12
    (by norm_num) (by norm_num) l12 u12 (by norm_num) (by norm_num)
  obtain ⟨f13, l14, u14⟩ := passo_iter (x := γ₁ - E) (lo' := (2358892115733 / 1877732275783 : ℝ)) (hi' := (2359202509067 / 1877080629017 : ℝ)) 2 13
    (by norm_num) (by norm_num) l13 u13 (by norm_num) (by norm_num)
  obtain ⟨f14, l15, u15⟩ := passo_iter (x := γ₁ - E) (lo' := (1877080629017 / 482121880050 : ℝ)) (hi' := (1877732275783 / 481159839950 : ℝ)) 1 14
    (by norm_num) (by norm_num) l14 u14 (by norm_num) (by norm_num)
  obtain ⟨f15, l16, u16⟩ := passo_iter (x := γ₁ - E) (lo' := (481159839950 / 434252755933 : ℝ)) (hi' := (482121880050 / 430714988867 : ℝ)) 3 15
    (by norm_num) (by norm_num) l15 u15 (by norm_num) (by norm_num)
  obtain ⟨f16, l17, u17⟩ := passo_iter (x := γ₁ - E) (lo' := (430714988867 / 51406891183 : ℝ)) (hi' := (434252755933 / 46907084017 : ℝ)) 1 16
    (by norm_num) (by norm_num) l16 u16 (by norm_num) (by norm_num)
  exact ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, l17, u17⟩

/-- **Cauda de `γ₂`**: `[0; 1, 3, 7, 3, 40, 4, 1, 1, 2, 3, 1, 3, 1, 2, 3, 4, 2, x_18]`, `x_18 ∈ [1.58232, 2.89892]`. -/
theorem cauda2_fc {γ₂ : ℝ} (h₂ : |γ₂ - 300018340427875824473724310148 / 10 ^ 17| ≤ 379 / 10 ^ 20) :
      ⌊passo^[0] (γ₂ - E)⌋ = 0 ∧
      ⌊passo^[1] (γ₂ - E)⌋ = 1 ∧
      ⌊passo^[2] (γ₂ - E)⌋ = 3 ∧
      ⌊passo^[3] (γ₂ - E)⌋ = 7 ∧
      ⌊passo^[4] (γ₂ - E)⌋ = 3 ∧
      ⌊passo^[5] (γ₂ - E)⌋ = 40 ∧
      ⌊passo^[6] (γ₂ - E)⌋ = 4 ∧
      ⌊passo^[7] (γ₂ - E)⌋ = 1 ∧
      ⌊passo^[8] (γ₂ - E)⌋ = 1 ∧
      ⌊passo^[9] (γ₂ - E)⌋ = 2 ∧
      ⌊passo^[10] (γ₂ - E)⌋ = 3 ∧
      ⌊passo^[11] (γ₂ - E)⌋ = 1 ∧
      ⌊passo^[12] (γ₂ - E)⌋ = 3 ∧
      ⌊passo^[13] (γ₂ - E)⌋ = 1 ∧
      ⌊passo^[14] (γ₂ - E)⌋ = 2 ∧
      ⌊passo^[15] (γ₂ - E)⌋ = 3 ∧
      ⌊passo^[16] (γ₂ - E)⌋ = 4 ∧
      ⌊passo^[17] (γ₂ - E)⌋ = 2 ∧
      (487467507456 / 308072325131 : ℝ) ≤ passo^[18] (γ₂ - E) ∧ passo^[18] (γ₂ - E) ≤ (541748748544 / 186879730869 : ℝ) := by
  rw [abs_le] at h₂
  obtain ⟨ha, hb⟩ := h₂
  norm_num at ha hb
  have hE : ((E : ℤ) : ℝ) = 3000183404278 := by norm_num [E]
  have l0 : (75824473724310147621 / 100000000000000000000 : ℝ) ≤ passo^[0] (γ₂ - E) := by simp only [Function.iterate_zero, id]; linarith
  have u0 : passo^[0] (γ₂ - E) ≤ (75824473724310148379 / 100000000000000000000 : ℝ) := by simp only [Function.iterate_zero, id]; linarith
  obtain ⟨f0, l1, u1⟩ := passo_iter (x := γ₂ - E) (lo' := (100000000000000000000 / 75824473724310148379 : ℝ)) (hi' := (100000000000000000000 / 75824473724310147621 : ℝ)) 0 0
    (by norm_num) (by norm_num) l0 u0 (by norm_num) (by norm_num)
  obtain ⟨f1, l2, u2⟩ := passo_iter (x := γ₂ - E) (lo' := (75824473724310147621 / 24175526275689852379 : ℝ)) (hi' := (75824473724310148379 / 24175526275689851621 : ℝ)) 1 1
    (by norm_num) (by norm_num) l1 u1 (by norm_num) (by norm_num)
  obtain ⟨f2, l3, u3⟩ := passo_iter (x := γ₂ - E) (lo' := (24175526275689851621 / 3297894897240593516 : ℝ)) (hi' := (24175526275689852379 / 3297894897240590484 : ℝ)) 3 2
    (by norm_num) (by norm_num) l2 u2 (by norm_num) (by norm_num)
  obtain ⟨f3, l4, u4⟩ := passo_iter (x := γ₂ - E) (lo' := (3297894897240590484 / 1090261995005718991 : ℝ)) (hi' := (3297894897240593516 / 1090261995005697009 : ℝ)) 7 3
    (by norm_num) (by norm_num) l3 u3 (by norm_num) (by norm_num)
  obtain ⟨f4, l5, u5⟩ := passo_iter (x := γ₂ - E) (lo' := (1090261995005697009 / 27108912223502489 : ℝ)) (hi' := (1090261995005718991 / 27108912223433511 : ℝ)) 3 4
    (by norm_num) (by norm_num) l4 u4 (by norm_num) (by norm_num)
  obtain ⟨f5, l6, u6⟩ := passo_iter (x := γ₂ - E) (lo' := (27108912223433511 / 5905506068378551 : ℝ)) (hi' := (27108912223502489 / 5905506065597449 : ℝ)) 40 5
    (by norm_num) (by norm_num) l5 u5 (by norm_num) (by norm_num)
  obtain ⟨f6, l7, u7⟩ := passo_iter (x := γ₂ - E) (lo' := (5905506065597449 / 3486887961112693 : ℝ)) (hi' := (5905506068378551 / 3486887949919307 : ℝ)) 4 6
    (by norm_num) (by norm_num) l6 u6 (by norm_num) (by norm_num)
  obtain ⟨f7, l8, u8⟩ := passo_iter (x := γ₂ - E) (lo' := (3486887949919307 / 2418618118459244 : ℝ)) (hi' := (3486887961112693 / 2418618104484756 : ℝ)) 1 7
    (by norm_num) (by norm_num) l7 u7 (by norm_num) (by norm_num)
  obtain ⟨f8, l9, u9⟩ := passo_iter (x := γ₂ - E) (lo' := (2418618104484756 / 1068269856627937 : ℝ)) (hi' := (2418618118459244 / 1068269831460063 : ℝ)) 1 8
    (by norm_num) (by norm_num) l8 u8 (by norm_num) (by norm_num)
  obtain ⟨f9, l10, u10⟩ := passo_iter (x := γ₂ - E) (lo' := (1068269831460063 / 282078455539118 : ℝ)) (hi' := (1068269856627937 / 282078391228882 : ℝ)) 2 9
    (by norm_num) (by norm_num) l9 u9 (by norm_num) (by norm_num)
  obtain ⟨f10, l11, u11⟩ := passo_iter (x := γ₂ - E) (lo' := (282078391228882 / 222034682941291 : ℝ)) (hi' := (282078455539118 / 222034464842709 : ℝ)) 3 10
    (by norm_num) (by norm_num) l10 u10 (by norm_num) (by norm_num)
  obtain ⟨f11, l12, u12⟩ := passo_iter (x := γ₂ - E) (lo' := (222034464842709 / 60043990696409 : ℝ)) (hi' := (222034682941291 / 60043708287591 : ℝ)) 1 11
    (by norm_num) (by norm_num) l11 u11 (by norm_num) (by norm_num)
  obtain ⟨f12, l13, u13⟩ := passo_iter (x := γ₂ - E) (lo' := (60043708287591 / 41903558078518 : ℝ)) (hi' := (60043990696409 / 41902492753482 : ℝ)) 3 12
    (by norm_num) (by norm_num) l12 u12 (by norm_num) (by norm_num)
  obtain ⟨f13, l14, u14⟩ := passo_iter (x := γ₂ - E) (lo' := (41902492753482 / 18141497942927 : ℝ)) (hi' := (41903558078518 / 18140150209073 : ℝ)) 1 13
    (by norm_num) (by norm_num) l13 u13 (by norm_num) (by norm_num)
  obtain ⟨f14, l15, u15⟩ := passo_iter (x := γ₂ - E) (lo' := (18140150209073 / 5623257660372 : ℝ)) (hi' := (18141497942927 / 5619496867628 : ℝ)) 2 14
    (by norm_num) (by norm_num) l14 u14 (by norm_num) (by norm_num)
  obtain ⟨f15, l16, u16⟩ := passo_iter (x := γ₂ - E) (lo' := (5619496867628 / 1283007340043 : ℝ)) (hi' := (5623257660372 / 1270377227957 : ℝ)) 3 15
    (by norm_num) (by norm_num) l15 u15 (by norm_num) (by norm_num)
  obtain ⟨f16, l17, u17⟩ := passo_iter (x := γ₂ - E) (lo' := (1270377227957 / 541748748544 : ℝ)) (hi' := (1283007340043 / 487467507456 : ℝ)) 4 16
    (by norm_num) (by norm_num) l16 u16 (by norm_num) (by norm_num)
  obtain ⟨f17, l18, u18⟩ := passo_iter (x := γ₂ - E) (lo' := (487467507456 / 308072325131 : ℝ)) (hi' := (541748748544 / 186879730869 : ℝ)) 2 17
    (by norm_num) (by norm_num) l17 u17 (by norm_num) (by norm_num)
  exact ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, l18, u18⟩

/-- **As duas caudas se separam no 4º quociente**: `⌊x₃⌋ = 7` nas duas, `⌊x₄⌋ = 1` numa e `3` na outra. -/
theorem separam_no_quarto {γ₁ γ₂ : ℝ} (h₁ : |γ₁ - 300018340427875788041891393358 / 10 ^ 17| ≤ 265 / 10 ^ 20) (h₂ : |γ₂ - 300018340427875824473724310148 / 10 ^ 17| ≤ 379 / 10 ^ 20) :
    ⌊passo^[3] (γ₁ - E)⌋ = ⌊passo^[3] (γ₂ - E)⌋ ∧ ⌊passo^[4] (γ₁ - E)⌋ ≠ ⌊passo^[4] (γ₂ - E)⌋ := by
  obtain ⟨-, -, -, a3, a4, -⟩ := cauda1_fc h₁
  obtain ⟨-, -, -, b3, b4, -⟩ := cauda2_fc h₂
  rw [a3, b3, a4, b4]
  norm_num

/-- **Fração mais simples da bola de `γ₁`**: `314849491/415434260` está na bola (`|γ₁ − (E + m)| ≤ 2r`) e
toda fração `p/q` da bola tem `q ≥ 415434260` (vizinhos `32172790/42451011`, `282676701/372983249`). -/
theorem simples1 {γ₁ : ℝ} (h₁ : |γ₁ - 300018340427875788041891393358 / 10 ^ 17| ≤ 265 / 10 ^ 20) :
    |γ₁ - (E + (314849491 : ℝ) / 415434260)| ≤ 2 * (53 / 20000000000000000000) ∧
      ∀ p q : ℤ, 0 < q → (15157608378278671547 / 20000000000000000000 : ℚ) ≤ (p : ℚ) / q → (p : ℚ) / q ≤ (15157608378278671653 / 20000000000000000000 : ℚ) → 415434260 ≤ q := by
  refine ⟨?_, fun p q hq h1 h2 => ?_⟩
  · rw [abs_le] at h₁ ⊢
    obtain ⟨ha, hb⟩ := h₁
    norm_num [E] at ha hb ⊢
    constructor <;> linarith
  · have := farey_min_q (a := 32172790) (b := 42451011) (c := 282676701) (d := 372983249) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hq h1 h2
    linarith

/-- **Fração mais simples da bola de `γ₂`**: `296762215/391380514` está na bola (`|γ₂ − (E + m)| ≤ 2r`) e
toda fração `p/q` da bola tem `q ≥ 391380514` (vizinhos `175530491/231495825`, `121231724/159884689`). -/
theorem simples2 {γ₂ : ℝ} (h₂ : |γ₂ - 300018340427875824473724310148 / 10 ^ 17| ≤ 379 / 10 ^ 20) :
    |γ₂ - (E + (296762215 : ℝ) / 391380514)| ≤ 2 * (379 / 100000000000000000000) ∧
      ∀ p q : ℤ, 0 < q → (75824473724310147621 / 100000000000000000000 : ℚ) ≤ (p : ℚ) / q → (p : ℚ) / q ≤ (75824473724310148379 / 100000000000000000000 : ℚ) → 391380514 ≤ q := by
  refine ⟨?_, fun p q hq h1 h2 => ?_⟩
  · rw [abs_le] at h₂ ⊢
    obtain ⟨ha, hb⟩ := h₂
    norm_num [E] at ha hb ⊢
    constructor <;> linarith
  · have := farey_min_q (a := 175530491) (b := 231495825) (c := 121231724) (d := 159884689) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hq h1 h2
    linarith

/-- **A distância**: `Δγ ∈ [9107958229197339/25000000000000000000, 9107958229197661/25000000000000000000]`
(centro `3643183291679/10000000000000000`, erro `161/25000000000000000000`). -/
theorem delta_bolas {γ₁ γ₂ : ℝ} (h₁ : |γ₁ - 300018340427875788041891393358 / 10 ^ 17| ≤ 265 / 10 ^ 20) (h₂ : |γ₂ - 300018340427875824473724310148 / 10 ^ 17| ≤ 379 / 10 ^ 20) :
    (9107958229197339 / 25000000000000000000 : ℝ) ≤ γ₂ - γ₁ ∧ γ₂ - γ₁ ≤ (9107958229197661 / 25000000000000000000 : ℝ) := by
  rw [abs_le] at h₁ h₂
  obtain ⟨a1, b1⟩ := h₁
  obtain ⟨a2, b2⟩ := h₂
  norm_num at a1 b1 a2 b2 ⊢
  constructor <;> linarith

/-- **`Δγ` em fração contínua**: `[0; 2744, 1, 5, 1, 3, 2, 1, 6, 1, 10, 6, x_12]`, `x_12 ∈ [1.71287, 2.79684]`. -/
theorem delta_fc {γ₁ γ₂ : ℝ} (h₁ : |γ₁ - 300018340427875788041891393358 / 10 ^ 17| ≤ 265 / 10 ^ 20) (h₂ : |γ₂ - 300018340427875824473724310148 / 10 ^ 17| ≤ 379 / 10 ^ 20) :
      ⌊passo^[0] (γ₂ - γ₁)⌋ = 0 ∧
      ⌊passo^[1] (γ₂ - γ₁)⌋ = 2744 ∧
      ⌊passo^[2] (γ₂ - γ₁)⌋ = 1 ∧
      ⌊passo^[3] (γ₂ - γ₁)⌋ = 5 ∧
      ⌊passo^[4] (γ₂ - γ₁)⌋ = 1 ∧
      ⌊passo^[5] (γ₂ - γ₁)⌋ = 3 ∧
      ⌊passo^[6] (γ₂ - γ₁)⌋ = 2 ∧
      ⌊passo^[7] (γ₂ - γ₁)⌋ = 1 ∧
      ⌊passo^[8] (γ₂ - γ₁)⌋ = 6 ∧
      ⌊passo^[9] (γ₂ - γ₁)⌋ = 1 ∧
      ⌊passo^[10] (γ₂ - γ₁)⌋ = 10 ∧
      ⌊passo^[11] (γ₂ - γ₁)⌋ = 6 ∧
      (185395081752 / 108236352653 : ℝ) ≤ passo^[12] (γ₂ - γ₁) ∧ passo^[12] (γ₂ - γ₁) ≤ (191899278248 / 68612812347 : ℝ) := by
  obtain ⟨ha, hb⟩ := delta_bolas h₁ h₂
  have l0 : (9107958229197339 / 25000000000000000000 : ℝ) ≤ passo^[0] (γ₂ - γ₁) := by simp only [Function.iterate_zero, id]; linarith
  have u0 : passo^[0] (γ₂ - γ₁) ≤ (9107958229197661 / 25000000000000000000 : ℝ) := by simp only [Function.iterate_zero, id]; linarith
  obtain ⟨f0, l1, u1⟩ := passo_iter (x := γ₂ - γ₁) (lo' := (25000000000000000000 / 9107958229197661 : ℝ)) (hi' := (25000000000000000000 / 9107958229197339 : ℝ)) 0 0
    (by norm_num) (by norm_num) l0 u0 (by norm_num) (by norm_num)
  obtain ⟨f1, l2, u2⟩ := passo_iter (x := γ₂ - γ₁) (lo' := (9107958229197339 / 7762619082501784 : ℝ)) (hi' := (9107958229197661 / 7762619081618216 : ℝ)) 2744 1
    (by norm_num) (by norm_num) l1 u1 (by norm_num) (by norm_num)
  obtain ⟨f2, l3, u3⟩ := passo_iter (x := γ₂ - γ₁) (lo' := (7762619081618216 / 1345339147579445 : ℝ)) (hi' := (7762619082501784 / 1345339146695555 : ℝ)) 1 2
    (by norm_num) (by norm_num) l2 u2 (by norm_num) (by norm_num)
  obtain ⟨f3, l4, u4⟩ := passo_iter (x := γ₂ - γ₁) (lo' := (1345339146695555 / 1035923349024009 : ℝ)) (hi' := (1345339147579445 / 1035923343720991 : ℝ)) 5 3
    (by norm_num) (by norm_num) l3 u3 (by norm_num) (by norm_num)
  obtain ⟨f4, l5, u5⟩ := passo_iter (x := γ₂ - γ₁) (lo' := (1035923343720991 / 309415803858454 : ℝ)) (hi' := (1035923349024009 / 309415797671546 : ℝ)) 1 4
    (by norm_num) (by norm_num) l4 u4 (by norm_num) (by norm_num)
  obtain ⟨f5, l6, u6⟩ := passo_iter (x := γ₂ - γ₁) (lo' := (309415797671546 / 107675956009371 : ℝ)) (hi' := (309415803858454 / 107675932145629 : ℝ)) 3 5
    (by norm_num) (by norm_num) l5 u5 (by norm_num) (by norm_num)
  obtain ⟨f6, l7, u7⟩ := passo_iter (x := γ₂ - γ₁) (lo' := (107675932145629 / 94063939567196 : ℝ)) (hi' := (107675956009371 / 94063885652804 : ℝ)) 2 6
    (by norm_num) (by norm_num) l6 u6 (by norm_num) (by norm_num)
  obtain ⟨f7, l8, u8⟩ := passo_iter (x := γ₂ - γ₁) (lo' := (94063885652804 / 13612070356567 : ℝ)) (hi' := (94063939567196 / 13611992578433 : ℝ)) 1 7
    (by norm_num) (by norm_num) l7 u7 (by norm_num) (by norm_num)
  obtain ⟨f8, l9, u9⟩ := passo_iter (x := γ₂ - γ₁) (lo' := (13611992578433 / 12391984096598 : ℝ)) (hi' := (13612070356567 / 12391463513402 : ℝ)) 6 8
    (by norm_num) (by norm_num) l8 u8 (by norm_num) (by norm_num)
  obtain ⟨f9, l10, u10⟩ := passo_iter (x := γ₂ - γ₁) (lo' := (12391463513402 / 1220606843165 : ℝ)) (hi' := (12391984096598 / 1220008481835 : ℝ)) 1 9
    (by norm_num) (by norm_num) l9 u9 (by norm_num) (by norm_num)
  obtain ⟨f10, l11, u11⟩ := passo_iter (x := γ₂ - γ₁) (lo' := (1220008481835 / 191899278248 : ℝ)) (hi' := (1220606843165 / 185395081752 : ℝ)) 10 10
    (by norm_num) (by norm_num) l10 u10 (by norm_num) (by norm_num)
  obtain ⟨f11, l12, u12⟩ := passo_iter (x := γ₂ - γ₁) (lo' := (185395081752 / 108236352653 : ℝ)) (hi' := (191899278248 / 68612812347 : ℝ)) 6 11
    (by norm_num) (by norm_num) l11 u11 (by norm_num) (by norm_num)
  exact ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, l12, u12⟩

/-- **Fração mais simples no erro de `Δγ`**: `97021/266308314`; nenhuma de denominador menor. -/
theorem simples_delta {γ₁ γ₂ : ℝ} (h₁ : |γ₁ - 300018340427875788041891393358 / 10 ^ 17| ≤ 265 / 10 ^ 20) (h₂ : |γ₂ - 300018340427875824473724310148 / 10 ^ 17| ≤ 379 / 10 ^ 20) :
    |(γ₂ - γ₁) - (97021 : ℝ) / 266308314| ≤ 2 * (161 / 25000000000000000000) ∧
      ∀ p q : ℤ, 0 < q → (9107958229197339 / 25000000000000000000 : ℚ) ≤ (p : ℚ) / q → (p : ℚ) / q ≤ (9107958229197661 / 25000000000000000000 : ℚ) → 266308314 ≤ q := by
  refine ⟨?_, fun p q hq h1 h2 => ?_⟩
  · obtain ⟨ha, hb⟩ := delta_bolas h₁ h₂
    rw [abs_le]
    constructor <;> norm_num at ha hb ⊢ <;> linarith
  · have := farey_min_q (a := 52190) (b := 143253841) (c := 44831) (d := 123054473) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hq h1 h2
    linarith

/-- **`λ ≈ −Δγ²/2`** em racionais exatos. -/
theorem lambda_bolas {γ₁ γ₂ : ℝ} (h₁ : |γ₁ - 300018340427875788041891393358 / 10 ^ 17| ≤ 265 / 10 ^ 20) (h₂ : |γ₂ - 300018340427875824473724310148 / 10 ^ 17| ≤ 379 / 10 ^ 20) :
    (-82954903104809392704043807870921 / 1250000000000000000000000000000000000000 : ℝ) ≤ -(γ₂ - γ₁) ^ 2 / 2 ∧ -(γ₂ - γ₁) ^ 2 / 2 ≤ (-82954903104803527178944204680921 / 1250000000000000000000000000000000000000 : ℝ) := by
  obtain ⟨ha, hb⟩ := delta_bolas h₁ h₂
  have h0 : (0 : ℝ) ≤ γ₂ - γ₁ := le_trans (by norm_num) ha
  constructor <;> nlinarith

/-- `26 < log(T/2π) < 28` para `3·10¹² ≤ T ≤ 3,001·10¹²`. -/
theorem log_altura {T : ℝ} (h1 : 3000000000000 ≤ T) (h2 : T ≤ 3001000000000) :
    26 < Real.log (T / (2 * π)) ∧ Real.log (T / (2 * π)) < 28 := by
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hpos : 0 < T / (2 * π) := by positivity
  have e26 : Real.exp 26 = Real.exp 1 ^ 26 := by rw [← Real.exp_nat_mul]; norm_num
  have e28 : Real.exp 28 = Real.exp 1 ^ 28 := by rw [← Real.exp_nat_mul]; norm_num
  have hlo : T / (2 * π) > 3000000000000 / (2 * 3.15) := by
    rw [gt_iff_lt, div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith
  have hhi : T / (2 * π) < 3001000000000 / (2 * 3.14) := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have p26 : Real.exp 1 ^ 26 < (2.7182818286 : ℝ) ^ 26 :=
    pow_lt_pow_left₀ he2 (Real.exp_pos 1).le (by norm_num)
  have p28 : (2.7182818283 : ℝ) ^ 28 < Real.exp 1 ^ 28 :=
    pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
  constructor
  · rw [Real.lt_log_iff_exp_lt hpos, e26]
    calc Real.exp 1 ^ 26 < (2.7182818286 : ℝ) ^ 26 := p26
      _ < 3000000000000 / (2 * 3.15) := by norm_num
      _ < T / (2 * π) := hlo
  · rw [Real.log_lt_iff_lt_exp hpos, e28]
    calc T / (2 * π) < 3001000000000 / (2 * 3.14) := hhi
      _ < (2.7182818283 : ℝ) ^ 28 := by norm_num
      _ < Real.exp 1 ^ 28 := p28

/-- Espaçamento normalizado na altura `T`. -/
noncomputable def sNorm (T Δ : ℝ) : ℝ := Δ * Real.log (T / (2 * π)) / (2 * π)

theorem sNorm_bounds {T Δ lo hi : ℝ} (h1 : 3000000000000 ≤ T) (h2 : T ≤ 3001000000000) (hlo : 0 < lo)
    (hd1 : lo ≤ Δ) (hd2 : Δ ≤ hi) :
    lo * 26 / (2 * 3.15) < sNorm T Δ ∧ sNorm T Δ < hi * 28 / (2 * 3.14) := by
  obtain ⟨l1, l2⟩ := log_altura h1 h2
  have hp1 := Real.pi_gt_d2
  have hp2 := Real.pi_lt_d2
  have hΔ : 0 < Δ := lt_of_lt_of_le hlo hd1
  unfold sNorm
  constructor
  · rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    have : lo * 26 ≤ Δ * Real.log (T / (2 * π)) := by nlinarith
    nlinarith
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : Δ * Real.log (T / (2 * π)) ≤ hi * 28 := by nlinarith
    nlinarith

/-- **O novo par**: `3/2000 < s < 1/600`. -/
theorem s_novo {γ₁ γ₂ : ℝ} (h₁ : |γ₁ - 300018340427875788041891393358 / 10 ^ 17| ≤ 265 / 10 ^ 20) (h₂ : |γ₂ - 300018340427875824473724310148 / 10 ^ 17| ≤ 379 / 10 ^ 20) :
    3 / 2000 < sNorm γ₁ (γ₂ - γ₁) ∧ sNorm γ₁ (γ₂ - γ₁) < 1 / 600 := by
  obtain ⟨ha, hb⟩ := delta_bolas h₁ h₂
  rw [abs_le] at h₁
  obtain ⟨c1, c2⟩ := h₁
  obtain ⟨s1, s2⟩ := sNorm_bounds (T := γ₁) (by norm_num at c1 ⊢; linarith) (by norm_num at c2 ⊢; linarith)
    (by norm_num) ha hb
  constructor
  · exact lt_of_le_of_lt (by norm_num) s1
  · exact lt_of_lt_of_le s2 (by norm_num)

/-- **O recorde anterior** (12 363 167 808 945/946): `Δγ ∈ [30920182174104737/50000000000000000000, …]` e `s > 1/400`. -/
theorem s_anterior {γ₁ γ₂ : ℝ} (h₁ : |γ₁ - 300017869072616233566825147131 / 10 ^ 17| ≤ 313 / 10 ^ 20) (h₂ : |γ₂ - 300017869072616295407189495341 / 10 ^ 17| ≤ 213 / 10 ^ 20) :
    1 / 400 < sNorm γ₁ (γ₂ - γ₁) := by
  rw [abs_le] at h₁ h₂
  obtain ⟨a1, b1⟩ := h₁
  obtain ⟨a2, b2⟩ := h₂
  have ha : (30920182174104737 / 50000000000000000000 : ℝ) ≤ γ₂ - γ₁ := by norm_num at a1 b1 a2 b2 ⊢; linarith
  have hb : γ₂ - γ₁ ≤ (30920182174105263 / 50000000000000000000 : ℝ) := by norm_num at a1 b1 a2 b2 ⊢; linarith
  obtain ⟨s1, -⟩ := sNorm_bounds (T := γ₁) (by norm_num at a1 ⊢; linarith) (by norm_num at b1 ⊢; linarith)
    (by norm_num) ha hb
  exact lt_of_le_of_lt (by norm_num) s1

/-- **Recorde**: o par novo é mais apertado que o anterior em espaçamento normalizado. -/
theorem recorde {γ₁ γ₂ δ₁ δ₂ : ℝ} (h₁ : |γ₁ - 300018340427875788041891393358 / 10 ^ 17| ≤ 265 / 10 ^ 20) (h₂ : |γ₂ - 300018340427875824473724310148 / 10 ^ 17| ≤ 379 / 10 ^ 20)
    (k₁ : |δ₁ - 300017869072616233566825147131 / 10 ^ 17| ≤ 313 / 10 ^ 20)
    (k₂ : |δ₂ - 300017869072616295407189495341 / 10 ^ 17| ≤ 213 / 10 ^ 20) :
    sNorm γ₁ (γ₂ - γ₁) < 1 / 600 ∧ 1 / 400 < sNorm δ₁ (δ₂ - δ₁) ∧
      sNorm γ₁ (γ₂ - γ₁) < sNorm δ₁ (δ₂ - δ₁) := by
  have a := (s_novo h₁ h₂).2
  have b := s_anterior k₁ k₂
  exact ⟨a, b, by linarith⟩

end ATK.Fracoes.ParRecorde

#print axioms ATK.Fracoes.ParRecorde.farey_min
#print axioms ATK.Fracoes.ParRecorde.farey_min_q
#print axioms ATK.Fracoes.ParRecorde.cauda1_fc
#print axioms ATK.Fracoes.ParRecorde.cauda2_fc
#print axioms ATK.Fracoes.ParRecorde.separam_no_quarto
#print axioms ATK.Fracoes.ParRecorde.simples1
#print axioms ATK.Fracoes.ParRecorde.simples2
#print axioms ATK.Fracoes.ParRecorde.delta_bolas
#print axioms ATK.Fracoes.ParRecorde.delta_fc
#print axioms ATK.Fracoes.ParRecorde.simples_delta
#print axioms ATK.Fracoes.ParRecorde.lambda_bolas
#print axioms ATK.Fracoes.ParRecorde.log_altura
#print axioms ATK.Fracoes.ParRecorde.sNorm_bounds
#print axioms ATK.Fracoes.ParRecorde.s_novo
#print axioms ATK.Fracoes.ParRecorde.s_anterior
#print axioms ATK.Fracoes.ParRecorde.recorde
