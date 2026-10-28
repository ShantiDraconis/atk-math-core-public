import ATK.ZeroClasses.FaixaGeral

/-!
# Peças da faixa sem zeros, arquivo 1 de 3 (rodada 29)

Retângulos `[s0, s1] × [a, b]` dentro de `[½, 1] × [43/50, 13]`, cada um certificado por `peca_ret` com `δ = 1/50`
(todas as avaliações de `ζ` nos centros verificadas pelo kernel com `decide +kernel`).
-/

open Complex

namespace ATK.ZeroClasses.Faixa

/-! ## Faixa `5 ≤ t ≤ 6` -/

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [5, 11/2]`: 6×6 centros. -/
theorem P4_1 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((5 : ℚ) : ℝ) ((11 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (5 : ℚ)) (b := (11 / 2 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (121 / 25 : ℚ)) (hs := (1 / 24 : ℚ)) (ht := (1 / 24 : ℚ)) (h := (5893 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (733053 / 1000000 : ℚ)) (R := (758 / 125 : ℚ)) (d := (23 / 5 : ℚ)) (ns := 6) (nt := 6)
    (Nc := 3) (Mc := 10) (Ne := 8) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [11/2, 23/4]`: 6×3 centros. -/
theorem P4_2 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((11 / 2 : ℚ) : ℝ) ((23 / 4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (11 / 2 : ℚ)) (b := (23 / 4 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (123 / 25 : ℚ)) (hs := (1 / 24 : ℚ)) (ht := (1 / 24 : ℚ)) (h := (5893 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (744839 / 1000000 : ℚ)) (R := (1577 / 250 : ℚ)) (d := (51 / 10 : ℚ)) (ns := 6) (nt := 3)
    (Nc := 3) (Mc := 10) (Ne := 8) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [23/4, 6]`: 5×3 centros. -/
theorem P4_3 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((23 / 4 : ℚ) : ℝ) ((6 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (23 / 4 : ℚ)) (b := (6 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (127 / 25 : ℚ)) (hs := (1 / 20 : ℚ)) (ht := (1 / 24 : ℚ)) (h := (6509 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (846643 / 1000000 : ℚ)) (R := (819 / 125 : ℚ)) (d := (107 / 20 : ℚ)) (ns := 5) (nt := 3)
    (Nc := 3) (Mc := 10) (Ne := 8) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

theorem P4_4 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((11 / 2 : ℚ) : ℝ) ((6 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((23 / 4 : ℚ) : ℝ)) P4_2 P4_3

theorem P4_5 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((5 : ℚ) : ℝ) ((6 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((11 / 2 : ℚ) : ℝ)) P4_1 P4_4

/-- **A faixa `[½, 1] × [5, 6]`.** -/
theorem faixa_4 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((5 : ℚ) : ℝ) ((6 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  P4_5

/-! ## Faixa `8 ≤ t ≤ 9` -/

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [8, 9]`: 4×10 centros. -/
theorem P7_1 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((8 : ℚ) : ℝ) ((9 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (8 : ℚ)) (b := (9 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (6 : ℚ)) (hs := (1 / 16 : ℚ)) (ht := (1 / 20 : ℚ)) (h := (2001 / 25000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (6103 / 5000 : ℚ)) (R := (1188 / 125 : ℚ)) (d := (38 / 5 : ℚ)) (ns := 4) (nt := 10)
    (Nc := 4) (Mc := 10) (Ne := 8) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

/-- **A faixa `[½, 1] × [8, 9]`.** -/
theorem faixa_7 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((8 : ℚ) : ℝ) ((9 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  P7_1

/-! ## Faixa `10 ≤ t ≤ 11` -/

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 3/4] × [10, 11]`: 2×9 centros. -/
theorem P9_1 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) ((10 : ℚ) : ℝ) ((11 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (3 / 4 : ℚ)) (a := (10 : ℚ)) (b := (11 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (663 / 100 : ℚ)) (hs := (1 / 16 : ℚ)) (ht := (1 / 18 : ℚ)) (h := (8363 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (5624669 / 4000000 : ℚ)) (R := (5729 / 500 : ℚ)) (d := (48 / 5 : ℚ)) (ns := 2) (nt := 9)
    (Nc := 5) (Mc := 10) (Ne := 10) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[3/4, 1] × [10, 11]`: 2×11 centros. -/
theorem P9_2 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((10 : ℚ) : ℝ) ((11 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (3 / 4 : ℚ)) (s1 := (1 : ℚ)) (a := (10 : ℚ)) (b := (11 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (166 / 25 : ℚ)) (hs := (1 / 16 : ℚ)) (ht := (1 / 22 : ℚ)) (h := (7729 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (651507 / 500000 : ℚ)) (R := (5743 / 500 : ℚ)) (d := (48 / 5 : ℚ)) (ns := 2) (nt := 11)
    (Nc := 5) (Mc := 10) (Ne := 10) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

theorem P9_3 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((10 : ℚ) : ℝ) ((11 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_re (sm := ((3 / 4 : ℚ) : ℝ)) P9_1 P9_2

/-- **A faixa `[½, 1] × [10, 11]`.** -/
theorem faixa_9 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((10 : ℚ) : ℝ) ((11 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  P9_3

/-! ## Faixa `12 ≤ t ≤ 13` -/

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [12, 49/4]`: 7×3 centros. -/
theorem P11_1 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((12 : ℚ) : ℝ) ((49 / 4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (12 : ℚ)) (b := (49 / 4 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (176 / 25 : ℚ)) (hs := (1 / 28 : ℚ)) (ht := (1 / 24 : ℚ)) (h := (343 / 6250 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (30809 / 31250 : ℚ)) (R := (1591 / 125 : ℚ)) (d := (58 / 5 : ℚ)) (ns := 7) (nt := 3)
    (Nc := 5) (Mc := 10) (Ne := 10) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [49/4, 99/8]`: 6×2 centros. -/
theorem P11_2 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((49 / 4 : ℚ) : ℝ) ((99 / 8 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (49 / 4 : ℚ)) (b := (99 / 8 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (709 / 100 : ℚ)) (hs := (1 / 24 : ℚ)) (ht := (1 / 32 : ℚ)) (h := (5209 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (3773181 / 4000000 : ℚ)) (R := (3213 / 250 : ℚ)) (d := (237 / 20 : ℚ)) (ns := 6) (nt := 2)
    (Nc := 5) (Mc := 10) (Ne := 10) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [99/8, 25/2]`: 7×2 centros. -/
theorem P11_3 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((99 / 8 : ℚ) : ℝ) ((25 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (99 / 8 : ℚ)) (b := (25 / 2 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (179 / 25 : ℚ)) (hs := (1 / 28 : ℚ)) (ht := (1 / 32 : ℚ)) (h := (2373 / 50000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (434767 / 500000 : ℚ)) (R := (1622 / 125 : ℚ)) (d := (479 / 40 : ℚ)) (ns := 7) (nt := 2)
    (Nc := 5) (Mc := 10) (Ne := 10) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [25/2, 101/8]`: 7×2 centros. -/
theorem P11_6 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((25 / 2 : ℚ) : ℝ) ((101 / 8 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (25 / 2 : ℚ)) (b := (101 / 8 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (181 / 25 : ℚ)) (hs := (1 / 28 : ℚ)) (ht := (1 / 32 : ℚ)) (h := (2373 / 50000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (439513 / 500000 : ℚ)) (R := (13101 / 1000 : ℚ)) (d := (121 / 10 : ℚ)) (ns := 7) (nt := 2)
    (Nc := 5) (Mc := 10) (Ne := 10) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [101/8, 51/4]`: 8×2 centros. -/
theorem P11_7 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((101 / 8 : ℚ) : ℝ) ((51 / 4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (101 / 8 : ℚ)) (b := (51 / 4 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (731 / 100 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (1 / 32 : ℚ)) (h := (221 / 5000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (165551 / 200000 : ℚ)) (R := (529 / 40 : ℚ)) (d := (489 / 40 : ℚ)) (ns := 8) (nt := 2)
    (Nc := 5) (Mc := 10) (Ne := 10) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [51/4, 103/8]`: 10×2 centros. -/
theorem P11_9 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((51 / 4 : ℚ) : ℝ) ((103 / 8 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (51 / 4 : ℚ)) (b := (103 / 8 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (37 / 5 : ℚ)) (hs := (1 / 40 : ℚ)) (ht := (1 / 32 : ℚ)) (h := (2001 / 50000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (76037 / 100000 : ℚ)) (R := (13349 / 1000 : ℚ)) (d := (247 / 20 : ℚ)) (ns := 10) (nt := 2)
    (Nc := 5) (Mc := 10) (Ne := 10) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [103/8, 13]`: 8×3 centros. -/
theorem P11_10 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((103 / 8 : ℚ) : ℝ) ((13 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (103 / 8 : ℚ)) (b := (13 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (149 / 20 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (1 / 48 : ℚ)) (h := (939 / 25000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (143911 / 200000 : ℚ)) (R := (13473 / 1000 : ℚ)) (d := (499 / 40 : ℚ)) (ns := 8) (nt := 3)
    (Nc := 6) (Mc := 10) (Ne := 10) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

theorem P11_4 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((49 / 4 : ℚ) : ℝ) ((25 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((99 / 8 : ℚ) : ℝ)) P11_2 P11_3

theorem P11_5 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((12 : ℚ) : ℝ) ((25 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((49 / 4 : ℚ) : ℝ)) P11_1 P11_4

theorem P11_8 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((25 / 2 : ℚ) : ℝ) ((51 / 4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((101 / 8 : ℚ) : ℝ)) P11_6 P11_7

theorem P11_11 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((51 / 4 : ℚ) : ℝ) ((13 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((103 / 8 : ℚ) : ℝ)) P11_9 P11_10

theorem P11_12 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((25 / 2 : ℚ) : ℝ) ((13 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((51 / 4 : ℚ) : ℝ)) P11_8 P11_11

theorem P11_13 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((12 : ℚ) : ℝ) ((13 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((25 / 2 : ℚ) : ℝ)) P11_5 P11_12

/-- **A faixa `[½, 1] × [12, 13]`.** -/
theorem faixa_11 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((12 : ℚ) : ℝ) ((13 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  P11_13

end ATK.ZeroClasses.Faixa

#print axioms ATK.ZeroClasses.Faixa.P4_1
#print axioms ATK.ZeroClasses.Faixa.P4_2
#print axioms ATK.ZeroClasses.Faixa.P4_3
#print axioms ATK.ZeroClasses.Faixa.P4_4
#print axioms ATK.ZeroClasses.Faixa.P4_5
#print axioms ATK.ZeroClasses.Faixa.faixa_4
#print axioms ATK.ZeroClasses.Faixa.P7_1
#print axioms ATK.ZeroClasses.Faixa.faixa_7
#print axioms ATK.ZeroClasses.Faixa.P9_1
#print axioms ATK.ZeroClasses.Faixa.P9_2
#print axioms ATK.ZeroClasses.Faixa.P9_3
#print axioms ATK.ZeroClasses.Faixa.faixa_9
#print axioms ATK.ZeroClasses.Faixa.P11_1
#print axioms ATK.ZeroClasses.Faixa.P11_2
#print axioms ATK.ZeroClasses.Faixa.P11_3
#print axioms ATK.ZeroClasses.Faixa.P11_6
#print axioms ATK.ZeroClasses.Faixa.P11_7
#print axioms ATK.ZeroClasses.Faixa.P11_9
#print axioms ATK.ZeroClasses.Faixa.P11_10
#print axioms ATK.ZeroClasses.Faixa.P11_4
#print axioms ATK.ZeroClasses.Faixa.P11_5
#print axioms ATK.ZeroClasses.Faixa.P11_8
#print axioms ATK.ZeroClasses.Faixa.P11_11
#print axioms ATK.ZeroClasses.Faixa.P11_12
#print axioms ATK.ZeroClasses.Faixa.P11_13
#print axioms ATK.ZeroClasses.Faixa.faixa_11
