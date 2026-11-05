import ATK.ZeroClasses.FaixaGeral

/-!
# Peças da faixa sem zeros, arquivo 3 de 3 (rodada 29)

Retângulos `[s0, s1] × [a, b]` dentro de `[½, 1] × [43/50, 13]`, cada um certificado por `peca_ret` com `δ = 1/50`
(todas as avaliações de `ζ` nos centros verificadas pelo kernel com `decide +kernel`).
-/

open Complex

namespace ATK.ZeroClasses.Faixa

/-! ## Faixa `2 ≤ t ≤ 3` -/

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 5/8] × [2, 5/2]`: 2×8 centros. -/
theorem P1_1 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((5 / 8 : ℚ) : ℝ) ((2 : ℚ) : ℝ) ((5 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (5 / 8 : ℚ)) (a := (2 : ℚ)) (b := (5 / 2 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (217 / 50 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (1 / 32 : ℚ)) (h := (221 / 5000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (49957 / 100000 : ℚ)) (R := (769 / 250 : ℚ)) (d := (8 / 5 : ℚ)) (ns := 2) (nt := 8)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 5/8] × [5/2, 3]`: 2×8 centros. -/
theorem P1_2 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((5 / 8 : ℚ) : ℝ) ((5 / 2 : ℚ) : ℝ) ((3 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (5 / 8 : ℚ)) (a := (5 / 2 : ℚ)) (b := (3 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (453 / 100 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (1 / 32 : ℚ)) (h := (221 / 5000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (104113 / 200000 : ℚ)) (R := (444 / 125 : ℚ)) (d := (21 / 10 : ℚ)) (ns := 2) (nt := 8)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[5/8, 3/4] × [2, 5/2]`: 2×7 centros. -/
theorem P1_4 : ∀ z ∈ ret ((5 / 8 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) ((2 : ℚ) : ℝ) ((5 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (5 / 8 : ℚ)) (s1 := (3 / 4 : ℚ)) (a := (2 : ℚ)) (b := (5 / 2 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (437 / 100 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (1 / 28 : ℚ)) (h := (2373 / 50000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (1077001 / 2000000 : ℚ)) (R := (78 / 25 : ℚ)) (d := (8 / 5 : ℚ)) (ns := 2) (nt := 7)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[5/8, 3/4] × [5/2, 3]`: 2×8 centros. -/
theorem P1_5 : ∀ z ∈ ret ((5 / 8 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) ((5 / 2 : ℚ) : ℝ) ((3 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (5 / 8 : ℚ)) (s1 := (3 / 4 : ℚ)) (a := (5 / 2 : ℚ)) (b := (3 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (229 / 50 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (1 / 32 : ℚ)) (h := (221 / 5000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (52609 / 100000 : ℚ)) (R := (359 / 100 : ℚ)) (d := (21 / 10 : ℚ)) (ns := 2) (nt := 8)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[3/4, 1] × [2, 9/4]`: 3×4 centros. -/
theorem P1_8 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((2 : ℚ) : ℝ) ((9 / 4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (3 / 4 : ℚ)) (s1 := (1 : ℚ)) (a := (2 : ℚ)) (b := (9 / 4 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (107 / 25 : ℚ)) (hs := (1 / 24 : ℚ)) (ht := (1 / 32 : ℚ)) (h := (5209 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (577363 / 1000000 : ℚ)) (R := (1499 / 500 : ℚ)) (d := (8 / 5 : ℚ)) (ns := 3) (nt := 4)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[3/4, 1] × [9/4, 5/2]`: 3×4 centros. -/
theorem P1_9 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((9 / 4 : ℚ) : ℝ) ((5 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (3 / 4 : ℚ)) (s1 := (1 : ℚ)) (a := (9 / 4 : ℚ)) (b := (5 / 2 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (429 / 100 : ℚ)) (hs := (1 / 24 : ℚ)) (ht := (1 / 32 : ℚ)) (h := (5209 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (2314661 / 4000000 : ℚ)) (R := (3221 / 1000 : ℚ)) (d := (37 / 20 : ℚ)) (ns := 3) (nt := 4)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[3/4, 1] × [5/2, 3]`: 4×7 centros. -/
theorem P1_11 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((5 / 2 : ℚ) : ℝ) ((3 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (3 / 4 : ℚ)) (s1 := (1 : ℚ)) (a := (5 / 2 : ℚ)) (b := (3 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (471 / 100 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (1 / 28 : ℚ)) (h := (2373 / 50000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (1157683 / 2000000 : ℚ)) (R := (3677 / 1000 : ℚ)) (d := (21 / 10 : ℚ)) (ns := 4) (nt := 7)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

theorem P1_3 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((5 / 8 : ℚ) : ℝ) ((2 : ℚ) : ℝ) ((3 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((5 / 2 : ℚ) : ℝ)) P1_1 P1_2

theorem P1_6 : ∀ z ∈ ret ((5 / 8 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) ((2 : ℚ) : ℝ) ((3 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((5 / 2 : ℚ) : ℝ)) P1_4 P1_5

theorem P1_7 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) ((2 : ℚ) : ℝ) ((3 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_re (sm := ((5 / 8 : ℚ) : ℝ)) P1_3 P1_6

theorem P1_10 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((2 : ℚ) : ℝ) ((5 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((9 / 4 : ℚ) : ℝ)) P1_8 P1_9

theorem P1_12 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((2 : ℚ) : ℝ) ((3 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((5 / 2 : ℚ) : ℝ)) P1_10 P1_11

theorem P1_13 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((2 : ℚ) : ℝ) ((3 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_re (sm := ((3 / 4 : ℚ) : ℝ)) P1_7 P1_12

/-- **A faixa `[½, 1] × [2, 3]`.** -/
theorem faixa_1 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((2 : ℚ) : ℝ) ((3 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  P1_13

/-! ## Faixa `3 ≤ t ≤ 4` -/

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 5/8] × [3, 7/2]`: 2×9 centros. -/
theorem P2_1 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((5 / 8 : ℚ) : ℝ) ((3 : ℚ) : ℝ) ((7 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (5 / 8 : ℚ)) (a := (3 : ℚ)) (b := (7 / 2 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (241 / 50 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (1 / 36 : ℚ)) (h := (2091 / 50000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (523931 / 1000000 : ℚ)) (R := (4033 / 1000 : ℚ)) (d := (13 / 5 : ℚ)) (ns := 2) (nt := 9)
    (Nc := 3) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 5/8] × [7/2, 4]`: 2×8 centros. -/
theorem P2_2 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((5 / 8 : ℚ) : ℝ) ((7 / 2 : ℚ) : ℝ) ((4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (5 / 8 : ℚ)) (a := (7 / 2 : ℚ)) (b := (4 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (469 / 100 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (1 / 32 : ℚ)) (h := (221 / 5000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (107649 / 200000 : ℚ)) (R := (2259 / 500 : ℚ)) (d := (31 / 10 : ℚ)) (ns := 2) (nt := 8)
    (Nc := 3) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[5/8, 3/4] × [3, 7/2]`: 2×8 centros. -/
theorem P2_4 : ∀ z ∈ ret ((5 / 8 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) ((3 : ℚ) : ℝ) ((7 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (5 / 8 : ℚ)) (s1 := (3 / 4 : ℚ)) (a := (3 : ℚ)) (b := (7 / 2 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (483 / 100 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (1 / 32 : ℚ)) (h := (221 / 5000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (110743 / 200000 : ℚ)) (R := (4067 / 1000 : ℚ)) (d := (13 / 5 : ℚ)) (ns := 2) (nt := 8)
    (Nc := 3) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[5/8, 3/4] × [7/2, 4]`: 2×7 centros. -/
theorem P2_5 : ∀ z ∈ ret ((5 / 8 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) ((7 / 2 : ℚ) : ℝ) ((4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (5 / 8 : ℚ)) (s1 := (3 / 4 : ℚ)) (a := (7 / 2 : ℚ)) (b := (4 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (47 / 10 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (1 / 28 : ℚ)) (h := (2373 / 50000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (115531 / 200000 : ℚ)) (R := (1137 / 250 : ℚ)) (d := (31 / 10 : ℚ)) (ns := 2) (nt := 7)
    (Nc := 3) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[3/4, 7/8] × [3, 7/2]`: 2×8 centros. -/
theorem P2_8 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((7 / 8 : ℚ) : ℝ) ((3 : ℚ) : ℝ) ((7 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (3 / 4 : ℚ)) (s1 := (7 / 8 : ℚ)) (a := (3 : ℚ)) (b := (7 / 2 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (483 / 100 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (1 / 32 : ℚ)) (h := (221 / 5000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (110743 / 200000 : ℚ)) (R := (513 / 125 : ℚ)) (d := (13 / 5 : ℚ)) (ns := 2) (nt := 8)
    (Nc := 3) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[7/8, 1] × [3, 7/2]`: 2×7 centros. -/
theorem P2_9 : ∀ z ∈ ret ((7 / 8 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((3 : ℚ) : ℝ) ((7 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (7 / 8 : ℚ)) (s1 := (1 : ℚ)) (a := (3 : ℚ)) (b := (7 / 2 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (121 / 25 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (1 / 28 : ℚ)) (h := (2373 / 50000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (297133 / 500000 : ℚ)) (R := (518 / 125 : ℚ)) (d := (13 / 5 : ℚ)) (ns := 2) (nt := 7)
    (Nc := 3) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[3/4, 1] × [7/2, 15/4]`: 3×5 centros. -/
theorem P2_11 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((7 / 2 : ℚ) : ℝ) ((15 / 4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (3 / 4 : ℚ)) (s1 := (1 : ℚ)) (a := (7 / 2 : ℚ)) (b := (15 / 4 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (117 / 25 : ℚ)) (hs := (1 / 24 : ℚ)) (ht := (1 / 40 : ℚ)) (h := (243 / 5000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (29431 / 50000 : ℚ)) (R := (219 / 50 : ℚ)) (d := (31 / 10 : ℚ)) (ns := 3) (nt := 5)
    (Nc := 3) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[3/4, 1] × [15/4, 4]`: 3×4 centros. -/
theorem P2_12 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((15 / 4 : ℚ) : ℝ) ((4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (3 / 4 : ℚ)) (s1 := (1 : ℚ)) (a := (15 / 4 : ℚ)) (b := (4 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (116 / 25 : ℚ)) (hs := (1 / 24 : ℚ)) (ht := (1 / 32 : ℚ)) (h := (5209 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (156061 / 250000 : ℚ)) (R := (2309 / 500 : ℚ)) (d := (67 / 20 : ℚ)) (ns := 3) (nt := 4)
    (Nc := 3) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

theorem P2_3 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((5 / 8 : ℚ) : ℝ) ((3 : ℚ) : ℝ) ((4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((7 / 2 : ℚ) : ℝ)) P2_1 P2_2

theorem P2_6 : ∀ z ∈ ret ((5 / 8 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) ((3 : ℚ) : ℝ) ((4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((7 / 2 : ℚ) : ℝ)) P2_4 P2_5

theorem P2_7 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) ((3 : ℚ) : ℝ) ((4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_re (sm := ((5 / 8 : ℚ) : ℝ)) P2_3 P2_6

theorem P2_10 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((3 : ℚ) : ℝ) ((7 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_re (sm := ((7 / 8 : ℚ) : ℝ)) P2_8 P2_9

theorem P2_13 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((7 / 2 : ℚ) : ℝ) ((4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((15 / 4 : ℚ) : ℝ)) P2_11 P2_12

theorem P2_14 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((3 : ℚ) : ℝ) ((4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((7 / 2 : ℚ) : ℝ)) P2_10 P2_13

theorem P2_15 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((3 : ℚ) : ℝ) ((4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_re (sm := ((3 / 4 : ℚ) : ℝ)) P2_7 P2_14

/-- **A faixa `[½, 1] × [3, 4]`.** -/
theorem faixa_2 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((3 : ℚ) : ℝ) ((4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  P2_15

/-! ## Faixa `6 ≤ t ≤ 7` -/

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [6, 25/4]`: 5×3 centros. -/
theorem P5_1 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((6 : ℚ) : ℝ) ((25 / 4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (6 : ℚ)) (b := (25 / 4 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (527 / 100 : ℚ)) (hs := (1 / 20 : ℚ)) (ht := (1 / 24 : ℚ)) (h := (6509 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (3510243 / 4000000 : ℚ)) (R := (1699 / 250 : ℚ)) (d := (28 / 5 : ℚ)) (ns := 5) (nt := 3)
    (Nc := 3) (Mc := 10) (Ne := 8) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [25/4, 13/2]`: 5×3 centros. -/
theorem P5_2 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((25 / 4 : ℚ) : ℝ) ((13 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (25 / 4 : ℚ)) (b := (13 / 2 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (136 / 25 : ℚ)) (hs := (1 / 20 : ℚ)) (ht := (1 / 24 : ℚ)) (h := (6509 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (113153 / 125000 : ℚ)) (R := (7041 / 1000 : ℚ)) (d := (117 / 20 : ℚ)) (ns := 5) (nt := 3)
    (Nc := 4) (Mc := 10) (Ne := 8) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [13/2, 27/4]`: 5×3 centros. -/
theorem P5_4 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((13 / 2 : ℚ) : ℝ) ((27 / 4 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (13 / 2 : ℚ)) (b := (27 / 4 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (109 / 20 : ℚ)) (hs := (1 / 20 : ℚ)) (ht := (1 / 24 : ℚ)) (h := (6509 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (725481 / 800000 : ℚ)) (R := (3643 / 500 : ℚ)) (d := (61 / 10 : ℚ)) (ns := 5) (nt := 3)
    (Nc := 4) (Mc := 10) (Ne := 8) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [27/4, 7]`: 7×2 centros. -/
theorem P5_5 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((27 / 4 : ℚ) : ℝ) ((7 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (27 / 4 : ℚ)) (b := (7 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (273 / 50 : ℚ)) (hs := (1 / 28 : ℚ)) (ht := (1 / 16 : ℚ)) (h := (7199 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (2005327 / 2000000 : ℚ)) (R := (1883 / 250 : ℚ)) (d := (127 / 20 : ℚ)) (ns := 7) (nt := 2)
    (Nc := 4) (Mc := 10) (Ne := 8) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

theorem P5_3 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((6 : ℚ) : ℝ) ((13 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((25 / 4 : ℚ) : ℝ)) P5_1 P5_2

theorem P5_6 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((13 / 2 : ℚ) : ℝ) ((7 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((27 / 4 : ℚ) : ℝ)) P5_4 P5_5

theorem P5_7 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((6 : ℚ) : ℝ) ((7 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((13 / 2 : ℚ) : ℝ)) P5_3 P5_6

/-- **A faixa `[½, 1] × [6, 7]`.** -/
theorem faixa_5 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((6 : ℚ) : ℝ) ((7 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  P5_7

/-! ## Faixa `9 ≤ t ≤ 10` -/

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 3/4] × [9, 10]`: 2×9 centros. -/
theorem P8_1 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) ((9 : ℚ) : ℝ) ((10 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (3 / 4 : ℚ)) (a := (9 : ℚ)) (b := (10 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (162 / 25 : ℚ)) (hs := (1 / 16 : ℚ)) (ht := (1 / 18 : ℚ)) (h := (8363 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (687403 / 500000 : ℚ)) (R := (1308 / 125 : ℚ)) (d := (43 / 5 : ℚ)) (ns := 2) (nt := 9)
    (Nc := 5) (Mc := 10) (Ne := 10) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[3/4, 1] × [9, 10]`: 2×10 centros. -/
theorem P8_2 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((9 : ℚ) : ℝ) ((10 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (3 / 4 : ℚ)) (s1 := (1 : ℚ)) (a := (9 : ℚ)) (b := (10 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (162 / 25 : ℚ)) (hs := (1 / 16 : ℚ)) (ht := (1 / 20 : ℚ)) (h := (2001 / 25000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (164581 / 125000 : ℚ)) (R := (5247 / 500 : ℚ)) (d := (43 / 5 : ℚ)) (ns := 2) (nt := 10)
    (Nc := 5) (Mc := 10) (Ne := 10) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

theorem P8_3 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((9 : ℚ) : ℝ) ((10 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_re (sm := ((3 / 4 : ℚ) : ℝ)) P8_1 P8_2

/-- **A faixa `[½, 1] × [9, 10]`.** -/
theorem faixa_8 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((9 : ℚ) : ℝ) ((10 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  P8_3

end ATK.ZeroClasses.Faixa

#print axioms ATK.ZeroClasses.Faixa.P1_1
#print axioms ATK.ZeroClasses.Faixa.P1_2
#print axioms ATK.ZeroClasses.Faixa.P1_4
#print axioms ATK.ZeroClasses.Faixa.P1_5
#print axioms ATK.ZeroClasses.Faixa.P1_8
#print axioms ATK.ZeroClasses.Faixa.P1_9
#print axioms ATK.ZeroClasses.Faixa.P1_11
#print axioms ATK.ZeroClasses.Faixa.P1_3
#print axioms ATK.ZeroClasses.Faixa.P1_6
#print axioms ATK.ZeroClasses.Faixa.P1_7
#print axioms ATK.ZeroClasses.Faixa.P1_10
#print axioms ATK.ZeroClasses.Faixa.P1_12
#print axioms ATK.ZeroClasses.Faixa.P1_13
#print axioms ATK.ZeroClasses.Faixa.faixa_1
#print axioms ATK.ZeroClasses.Faixa.P2_1
#print axioms ATK.ZeroClasses.Faixa.P2_2
#print axioms ATK.ZeroClasses.Faixa.P2_4
#print axioms ATK.ZeroClasses.Faixa.P2_5
#print axioms ATK.ZeroClasses.Faixa.P2_8
#print axioms ATK.ZeroClasses.Faixa.P2_9
#print axioms ATK.ZeroClasses.Faixa.P2_11
#print axioms ATK.ZeroClasses.Faixa.P2_12
#print axioms ATK.ZeroClasses.Faixa.P2_3
#print axioms ATK.ZeroClasses.Faixa.P2_6
#print axioms ATK.ZeroClasses.Faixa.P2_7
#print axioms ATK.ZeroClasses.Faixa.P2_10
#print axioms ATK.ZeroClasses.Faixa.P2_13
#print axioms ATK.ZeroClasses.Faixa.P2_14
#print axioms ATK.ZeroClasses.Faixa.P2_15
#print axioms ATK.ZeroClasses.Faixa.faixa_2
#print axioms ATK.ZeroClasses.Faixa.P5_1
#print axioms ATK.ZeroClasses.Faixa.P5_2
#print axioms ATK.ZeroClasses.Faixa.P5_4
#print axioms ATK.ZeroClasses.Faixa.P5_5
#print axioms ATK.ZeroClasses.Faixa.P5_3
#print axioms ATK.ZeroClasses.Faixa.P5_6
#print axioms ATK.ZeroClasses.Faixa.P5_7
#print axioms ATK.ZeroClasses.Faixa.faixa_5
#print axioms ATK.ZeroClasses.Faixa.P8_1
#print axioms ATK.ZeroClasses.Faixa.P8_2
#print axioms ATK.ZeroClasses.Faixa.P8_3
#print axioms ATK.ZeroClasses.Faixa.faixa_8
