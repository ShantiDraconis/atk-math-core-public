import ATK.ZeroClasses.FaixaGeral

/-!
# Peças da faixa sem zeros, arquivo 2 de 3 (rodada 29)

Retângulos `[s0, s1] × [a, b]` dentro de `[½, 1] × [43/50, 13]`, cada um certificado por `peca_ret` com `δ = 1/50`
(todas as avaliações de `ζ` nos centros verificadas pelo kernel com `decide +kernel`).
-/

open Complex

namespace ATK.ZeroClasses.Faixa

/-! ## Faixa `43/50 ≤ t ≤ 2` -/

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 3/4] × [43/50, 401/400]`: 4×3 centros. -/
theorem P0_1 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) ((43 / 50 : ℚ) : ℝ) ((401 / 400 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (3 / 4 : ℚ)) (a := (43 / 50 : ℚ)) (b := (401 / 400 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (349 / 50 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (19 / 800 : ℚ)) (h := (1963 / 50000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (705087 / 1000000 : ℚ)) (R := (907 / 500 : ℚ)) (d := (23 / 50 : ℚ)) (ns := 4) (nt := 3)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 3/4] × [401/400, 229/200]`: 5×2 centros. -/
theorem P0_2 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) ((401 / 400 : ℚ) : ℝ) ((229 / 200 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (3 / 4 : ℚ)) (a := (401 / 400 : ℚ)) (b := (229 / 200 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (597 / 100 : ℚ)) (hs := (1 / 40 : ℚ)) (ht := (57 / 1600 : ℚ)) (h := (4353 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (2678741 / 4000000 : ℚ)) (R := (1927 / 1000 : ℚ)) (d := (241 / 400 : ℚ)) (ns := 5) (nt := 2)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[3/4, 1] × [43/50, 229/200]`: 4×4 centros. -/
theorem P0_4 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((43 / 50 : ℚ) : ℝ) ((229 / 200 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (3 / 4 : ℚ)) (s1 := (1 : ℚ)) (a := (43 / 50 : ℚ)) (b := (229 / 200 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (351 / 50 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (57 / 1600 : ℚ)) (h := (4739 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (1703389 / 2000000 : ℚ)) (R := (417 / 200 : ℚ)) (d := (23 / 50 : ℚ)) (ns := 4) (nt := 4)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [229/200, 103/80]`: 9×2 centros. -/
theorem P0_6 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((229 / 200 : ℚ) : ℝ) ((103 / 80 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (229 / 200 : ℚ)) (b := (103 / 80 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (269 / 50 : ℚ)) (hs := (1 / 36 : ℚ)) (ht := (57 / 1600 : ℚ)) (h := (2259 / 50000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (627671 / 1000000 : ℚ)) (R := (2193 / 1000 : ℚ)) (d := (149 / 200 : ℚ)) (ns := 9) (nt := 2)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [103/80, 143/100]`: 8×2 centros. -/
theorem P0_7 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((103 / 80 : ℚ) : ℝ) ((143 / 100 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (103 / 80 : ℚ)) (b := (143 / 100 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (249 / 50 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (57 / 1600 : ℚ)) (h := (4739 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (1220011 / 2000000 : ℚ)) (R := (461 / 200 : ℚ)) (d := (71 / 80 : ℚ)) (ns := 8) (nt := 2)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [143/100, 629/400]`: 8×2 centros. -/
theorem P0_10 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((143 / 100 : ℚ) : ℝ) ((629 / 400 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (143 / 100 : ℚ)) (b := (629 / 400 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (47 / 10 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (57 / 1600 : ℚ)) (h := (4739 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (230733 / 400000 : ℚ)) (R := (2419 / 1000 : ℚ)) (d := (103 / 100 : ℚ)) (ns := 8) (nt := 2)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [629/400, 343/200]`: 8×2 centros. -/
theorem P0_11 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((629 / 400 : ℚ) : ℝ) ((343 / 200 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (629 / 400 : ℚ)) (b := (343 / 200 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (9 / 2 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (57 / 1600 : ℚ)) (h := (4739 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (44251 / 80000 : ℚ)) (R := (2537 / 1000 : ℚ)) (d := (469 / 400 : ℚ)) (ns := 8) (nt := 2)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 3/4] × [343/200, 2]`: 4×4 centros. -/
theorem P0_13 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) ((343 / 200 : ℚ) : ℝ) ((2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (3 / 4 : ℚ)) (a := (343 / 200 : ℚ)) (b := (2 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (437 / 100 : ℚ)) (hs := (1 / 32 : ℚ)) (ht := (57 / 1600 : ℚ)) (h := (4739 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (2150943 / 4000000 : ℚ)) (R := (1331 / 500 : ℚ)) (d := (263 / 200 : ℚ)) (ns := 4) (nt := 4)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[3/4, 1] × [343/200, 2]`: 3×5 centros. -/
theorem P0_14 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((343 / 200 : ℚ) : ℝ) ((2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (3 / 4 : ℚ)) (s1 := (1 : ℚ)) (a := (343 / 200 : ℚ)) (b := (2 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (221 / 50 : ℚ)) (hs := (1 / 24 : ℚ)) (ht := (57 / 2000 : ℚ)) (h := (5049 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (1155829 / 2000000 : ℚ)) (R := (2779 / 1000 : ℚ)) (d := (263 / 200 : ℚ)) (ns := 3) (nt := 5)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

theorem P0_3 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) ((43 / 50 : ℚ) : ℝ) ((229 / 200 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((401 / 400 : ℚ) : ℝ)) P0_1 P0_2

theorem P0_5 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((43 / 50 : ℚ) : ℝ) ((229 / 200 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_re (sm := ((3 / 4 : ℚ) : ℝ)) P0_3 P0_4

theorem P0_8 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((229 / 200 : ℚ) : ℝ) ((143 / 100 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((103 / 80 : ℚ) : ℝ)) P0_6 P0_7

theorem P0_9 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((43 / 50 : ℚ) : ℝ) ((143 / 100 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((229 / 200 : ℚ) : ℝ)) P0_5 P0_8

theorem P0_12 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((143 / 100 : ℚ) : ℝ) ((343 / 200 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((629 / 400 : ℚ) : ℝ)) P0_10 P0_11

theorem P0_15 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((343 / 200 : ℚ) : ℝ) ((2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_re (sm := ((3 / 4 : ℚ) : ℝ)) P0_13 P0_14

theorem P0_16 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((143 / 100 : ℚ) : ℝ) ((2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((343 / 200 : ℚ) : ℝ)) P0_12 P0_15

theorem P0_17 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((43 / 50 : ℚ) : ℝ) ((2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((143 / 100 : ℚ) : ℝ)) P0_9 P0_16

/-- **A faixa `[½, 1] × [43/50, 2]`.** -/
theorem faixa_0 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((43 / 50 : ℚ) : ℝ) ((2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  P0_17

/-! ## Faixa `4 ≤ t ≤ 5` -/

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [4, 9/2]`: 7×7 centros. -/
theorem P3_1 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((4 : ℚ) : ℝ) ((9 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (4 : ℚ)) (b := (9 / 2 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (467 / 100 : ℚ)) (hs := (1 / 28 : ℚ)) (ht := (1 / 28 : ℚ)) (h := (5051 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (2438817 / 4000000 : ℚ)) (R := (5097 / 1000 : ℚ)) (d := (18 / 5 : ℚ)) (ns := 7) (nt := 7)
    (Nc := 3) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [9/2, 5]`: 6×7 centros. -/
theorem P3_2 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((9 / 2 : ℚ) : ℝ) ((5 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (9 / 2 : ℚ)) (b := (5 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (47 / 10 : ℚ)) (hs := (1 / 24 : ℚ)) (ht := (1 / 28 : ℚ)) (h := (343 / 6250 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (16621 / 25000 : ℚ)) (R := (5579 / 1000 : ℚ)) (d := (41 / 10 : ℚ)) (ns := 6) (nt := 7)
    (Nc := 3) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

theorem P3_3 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((4 : ℚ) : ℝ) ((5 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((9 / 2 : ℚ) : ℝ)) P3_1 P3_2

/-- **A faixa `[½, 1] × [4, 5]`.** -/
theorem faixa_3 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((4 : ℚ) : ℝ) ((5 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  P3_3

/-! ## Faixa `7 ≤ t ≤ 8` -/

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [7, 15/2]`: 4×6 centros. -/
theorem P6_1 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((7 : ℚ) : ℝ) ((15 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (7 : ℚ)) (b := (15 / 2 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (553 / 100 : ℚ)) (hs := (1 / 16 : ℚ)) (ht := (1 / 24 : ℚ)) (h := (939 / 12500 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (529267 / 500000 : ℚ)) (R := (1003 / 125 : ℚ)) (d := (33 / 5 : ℚ)) (ns := 4) (nt := 6)
    (Nc := 4) (Mc := 10) (Ne := 8) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [15/2, 8]`: 4×5 centros. -/
theorem P6_2 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((15 / 2 : ℚ) : ℝ) ((8 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (15 / 2 : ℚ)) (b := (8 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (561 / 100 : ℚ)) (hs := (1 / 16 : ℚ)) (ht := (1 / 20 : ℚ)) (h := (2001 / 25000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (1142561 / 1000000 : ℚ)) (R := (2129 / 250 : ℚ)) (d := (71 / 10 : ℚ)) (ns := 4) (nt := 5)
    (Nc := 4) (Mc := 10) (Ne := 8) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

theorem P6_3 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((7 : ℚ) : ℝ) ((8 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((15 / 2 : ℚ) : ℝ)) P6_1 P6_2

/-- **A faixa `[½, 1] × [7, 8]`.** -/
theorem faixa_6 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((7 : ℚ) : ℝ) ((8 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  P6_3

/-! ## Faixa `11 ≤ t ≤ 12` -/

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 1] × [11, 23/2]`: 5×5 centros. -/
theorem P10_1 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((11 : ℚ) : ℝ) ((23 / 2 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (1 : ℚ)) (a := (11 : ℚ)) (b := (23 / 2 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (27 / 4 : ℚ)) (hs := (1 / 20 : ℚ)) (ht := (1 / 20 : ℚ)) (h := (221 / 3125 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (6067 / 5000 : ℚ)) (R := (11983 / 1000 : ℚ)) (d := (53 / 5 : ℚ)) (ns := 5) (nt := 5)
    (Nc := 5) (Mc := 10) (Ne := 10) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[1/2, 3/4] × [23/2, 12]`: 3×5 centros. -/
theorem P10_2 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((3 / 4 : ℚ) : ℝ) ((23 / 2 : ℚ) : ℝ) ((12 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (1 / 2 : ℚ)) (s1 := (3 / 4 : ℚ)) (a := (23 / 2 : ℚ)) (b := (12 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (173 / 25 : ℚ)) (hs := (1 / 24 : ℚ)) (ht := (1 / 20 : ℚ)) (h := (6509 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (1146057 / 1000000 : ℚ)) (R := (6227 / 500 : ℚ)) (d := (111 / 10 : ℚ)) (ns := 3) (nt := 5)
    (Nc := 5) (Mc := 10) (Ne := 10) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

set_option maxRecDepth 100000 in
/-- Peça `[3/4, 1] × [23/2, 12]`: 3×6 centros. -/
theorem P10_3 : ∀ z ∈ ret ((3 / 4 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((23 / 2 : ℚ) : ℝ) ((12 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  peca_ret (s0 := (3 / 4 : ℚ)) (s1 := (1 : ℚ)) (a := (23 / 2 : ℚ)) (b := (12 : ℚ)) (r := (2 / 5 : ℚ))
    (B := (693 / 100 : ℚ)) (hs := (1 / 24 : ℚ)) (ht := (1 / 24 : ℚ)) (h := (5893 / 100000 : ℚ)) (δ := (1 / 50 : ℚ))
    (v := (4163849 / 4000000 : ℚ)) (R := (12479 / 1000 : ℚ)) (d := (111 / 10 : ℚ)) (ns := 3) (nt := 6)
    (Nc := 5) (Mc := 10) (Ne := 10) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)

theorem P10_4 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((23 / 2 : ℚ) : ℝ) ((12 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_re (sm := ((3 / 4 : ℚ) : ℝ)) P10_2 P10_3

theorem P10_5 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((11 : ℚ) : ℝ) ((12 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((23 / 2 : ℚ) : ℝ)) P10_1 P10_4

/-- **A faixa `[½, 1] × [11, 12]`.** -/
theorem faixa_10 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((11 : ℚ) : ℝ) ((12 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  P10_5

end ATK.ZeroClasses.Faixa

#print axioms ATK.ZeroClasses.Faixa.P0_1
#print axioms ATK.ZeroClasses.Faixa.P0_2
#print axioms ATK.ZeroClasses.Faixa.P0_4
#print axioms ATK.ZeroClasses.Faixa.P0_6
#print axioms ATK.ZeroClasses.Faixa.P0_7
#print axioms ATK.ZeroClasses.Faixa.P0_10
#print axioms ATK.ZeroClasses.Faixa.P0_11
#print axioms ATK.ZeroClasses.Faixa.P0_13
#print axioms ATK.ZeroClasses.Faixa.P0_14
#print axioms ATK.ZeroClasses.Faixa.P0_3
#print axioms ATK.ZeroClasses.Faixa.P0_5
#print axioms ATK.ZeroClasses.Faixa.P0_8
#print axioms ATK.ZeroClasses.Faixa.P0_9
#print axioms ATK.ZeroClasses.Faixa.P0_12
#print axioms ATK.ZeroClasses.Faixa.P0_15
#print axioms ATK.ZeroClasses.Faixa.P0_16
#print axioms ATK.ZeroClasses.Faixa.P0_17
#print axioms ATK.ZeroClasses.Faixa.faixa_0
#print axioms ATK.ZeroClasses.Faixa.P3_1
#print axioms ATK.ZeroClasses.Faixa.P3_2
#print axioms ATK.ZeroClasses.Faixa.P3_3
#print axioms ATK.ZeroClasses.Faixa.faixa_3
#print axioms ATK.ZeroClasses.Faixa.P6_1
#print axioms ATK.ZeroClasses.Faixa.P6_2
#print axioms ATK.ZeroClasses.Faixa.P6_3
#print axioms ATK.ZeroClasses.Faixa.faixa_6
#print axioms ATK.ZeroClasses.Faixa.P10_1
#print axioms ATK.ZeroClasses.Faixa.P10_2
#print axioms ATK.ZeroClasses.Faixa.P10_3
#print axioms ATK.ZeroClasses.Faixa.P10_4
#print axioms ATK.ZeroClasses.Faixa.P10_5
#print axioms ATK.ZeroClasses.Faixa.faixa_10
