import ATK.GramDois
import ATK.BarreiraModelos

/-!
# ATK — Erros dos textos (Gram / Báez-Duarte): explicação, correção e teoremas

Para cada erro: **de onde vem** (o que o número do texto realmente calcula), **a correção** e os
teoremas do kernel (refutação + versão corrigida).

* **E1 (963449d2), `G₁₁ = log 2π − γ − 1`.** O texto calculou só `∫_{(0,1]} {1/t}²`
  (`G11_partes`), esquecendo a cauda `∫_1^∞ t⁻² = 1`. Correção: `G₁₁ = log 2π − γ`. O seu
  `D₁ = 1 − (1−γ)²/(log 2π − γ − 1) ≈ 0,31426` é o **mínimo do resíduo local** em `(0,1]`
  (`D1texto_minimo_local`), que ignora a penalidade `x²` da cauda: `‖χ − xρ₁‖² = ∫_{(0,1]}(1 − x{1/t})² + x²`
  (`residuo_split`). Por isso `D1texto < D₁ ≈ 0,85821` (`D1texto_lt_DN1`, `D1texto_cotas`).
* **E2 (1fb0a5dd), `G₁₁ = log 2`, `D₁ ≈ 0,7421`.** O `0,7421` é coerente com o `G₁₁` errado:
  `1 − (1−γ)²/log 2 ∈ (0,74212; 0,74213)` (`D1log2_cotas`); como `log 2 < G₁₁`, subestima `D₁`.
* **E3 (9654e97e), `b_k = (1 − γ + log k − H_{k−1})/k`.** É `b_k − H_{k−1}/k` (`bTexto_eq`), com
  `b_k = (log k + 1 − γ)/k`. Como `H_{k−1} − log k` cresce para `γ > 1 − γ`, a fórmula do texto é
  **negativa para todo `k ≥ 4`** (`bTexto_neg`), contra `b_k > 0`. Os próprios valores listados para
  `k = 3, 4` nem batem com a fórmula (`bTexto_valores`); o de `k = 2` bate.
* **E4 (9e0c6efb).** Os dois coeficientes `q/i + p/j` (certo) e `p/i + q/j` (texto) só coincidem se
  `(p − q)(1/i − 1/j) = 0` (`coef_coincide_iff`). O valor tabelado `G₁₂ ≈ 0,7722083` está **abaixo** do
  intervalo certificado `(0,7722084; 0,7722094)` (`G12_cotas`), coerente com truncar a série: toda
  soma parcial fica por baixo (`truncado_por_baixo`).
* **E12 (99d52102).** O intercepto negativo vem de ajustar `a + C/log N` a dois pontos. O que os dados
  dizem: `D_N log N` cai de `0,04566` para `0,04556` e fica **abaixo** de `C₀ = 2 + γ − log 4π ≈ 0,04619`
  (razões `≈ 0,988` e `≈ 0,986`, `razoes_C0`); um modelo só com `C/log N` também não passa pelos dois
  (`sem_C_unico`); e `D_∞ ≥ 0` sempre. O ajuste de dois pontos não estima `D_∞`.
-/

open MeasureTheory Set Filter Topology Real

namespace ATK.ErrosGram

open ATK.Conditional.Riemann (rho chi DN residualSq)
open ATK.BaezDuarteVetorB (fr)
open ATK.Cert (IR)

/-! ## E1. `G₁₁` e o resíduo local -/

/-- **Resíduo expandido**: `‖χ − Σ cₖ ρₖ‖² = 1 − 2 Σ bₖ cₖ + cᵀ G c`. -/
theorem residuo_expandido {N : ℕ} (c : Fin N → ℝ) :
    residualSq N c = 1 - 2 * ∑ i, ATK.GramBaezDuarte.b N i * c i +
      ATK.OmegaGramRho.quad (ATK.GramBaezDuarte.G N) c := by
  rw [← ATK.GramBaezDuarte.err_eq, ATK.OmegaGramRho.err_expand, ATK.GramBaezDuarte.ip_chi,
    ATK.GramBaezDuarte.bvec_eq, ATK.GramBaezDuarte.gram_eq]

/-- **`N = 1`**: `‖χ − xρ₁‖² = 1 − 2x(1 − γ) + x²(log 2π − γ)`. -/
theorem residuo_um (x : ℝ) :
    residualSq 1 (fun _ => x) =
      1 - 2 * x * (1 - eulerMascheroniConstant) +
        x ^ 2 * (Real.log (2 * π) - eulerMascheroniConstant) := by
  rw [residuo_expandido]
  have hG : ATK.GramBaezDuarte.G 1 0 0 = Real.log (2 * π) - eulerMascheroniConstant :=
    ATK.GramExato.G_zero 1 one_pos
  have hb : ATK.GramBaezDuarte.b 1 0 = 1 - eulerMascheroniConstant :=
    ATK.BaezDuarteVetorB.b_zero 1 one_pos
  simp only [ATK.OmegaGramRho.quad, Fin.sum_univ_one, hG, hb]
  ring

/-- **Resíduo local** (só em `(0,1]`): `∫_{(0,1]}(1 − x{1/t})² = 1 − 2x(1 − γ) + x²(log 2π − γ − 1)`. -/
theorem local_um (x : ℝ) :
    ∫ t in Ioc (0 : ℝ) 1, (1 - x * fr t) ^ 2 =
      1 - 2 * x * (1 - eulerMascheroniConstant) +
        x ^ 2 * (Real.log (2 * π) - eulerMascheroniConstant - 1) := by
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 1) :=
    (continuous_const.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h2 : IntegrableOn (fun t => (-2 * x) * fr t) (Ioc 0 1) :=
    (ATK.BaezDuarteVetorB.integrableOn_fr 0 1).const_mul _
  have h3 : IntegrableOn (fun t => x ^ 2 * fr t ^ 2) (Ioc 0 1) :=
    (ATK.GramExato.integrableOn_fr_sq 0 1).const_mul _
  have e : (fun t => (1 - x * fr t) ^ 2) = fun t => (1 + (-2 * x) * fr t) + x ^ 2 * fr t ^ 2 := by
    funext t; ring
  have h12 : IntegrableOn (fun t => 1 + (-2 * x) * fr t) (Ioc 0 1) := h1.add h2
  rw [e, integral_add h12 h3, integral_add h1 h2, integral_const_mul, integral_const_mul,
    ATK.BaezDuarteVetorB.integral_fract_inv, ATK.GramExato.integral_Ioc_fr_sq]
  simp
  ring

/-- **A origem do erro**: `‖χ − xρ₁‖² = (resíduo local em (0,1]) + x²` (a cauda `∫_1^∞ (x/t)²`). -/
theorem residuo_split (x : ℝ) :
    residualSq 1 (fun _ => x) = (∫ t in Ioc (0 : ℝ) 1, (1 - x * fr t) ^ 2) + x ^ 2 := by
  rw [residuo_um, local_um]; ring

/-- `G₁₁ = ∫_{(0,1]}{1/t}² + ∫_1^∞ t⁻²`, com as partes `log 2π − γ − 1` (o valor do texto) e `1`. -/
theorem G11_partes :
    ATK.GramBaezDuarte.G 1 0 0 = (∫ t in Ioc (0 : ℝ) 1, fr t ^ 2) + ∫ t in Ioi (1 : ℝ), fr t ^ 2 ∧
      ∫ t in Ioc (0 : ℝ) 1, fr t ^ 2 = Real.log (2 * π) - eulerMascheroniConstant - 1 ∧
      ∫ t in Ioi (1 : ℝ), fr t ^ 2 = 1 := by
  have hG : ATK.GramBaezDuarte.G 1 0 0 = Real.log (2 * π) - eulerMascheroniConstant :=
    ATK.GramExato.G_zero 1 one_pos
  refine ⟨?_, ATK.GramExato.integral_Ioc_fr_sq, ATK.GramExato.integral_Ioi_fr_sq⟩
  rw [hG, ATK.GramExato.integral_Ioc_fr_sq, ATK.GramExato.integral_Ioi_fr_sq]
  ring

/-- O `D₁` do texto. -/
noncomputable def D1texto : ℝ :=
  1 - (1 - eulerMascheroniConstant) ^ 2 / (Real.log (2 * π) - eulerMascheroniConstant - 1)

theorem g1_pos : 0 < Real.log (2 * π) - eulerMascheroniConstant - 1 := by
  rw [ATK.GamaCotas.log_two_pi]
  obtain ⟨h1, -⟩ := ATK.GamaCotas.log_pi_cotas
  obtain ⟨-, h2⟩ := ATK.GamaCotas.gama_cotas
  have h3 := Real.log_two_gt_d9
  norm_num at h3
  linarith

theorem quad_min {a g : ℝ} (hg : 0 < g) (x : ℝ) : 1 - a ^ 2 / g ≤ 1 - 2 * x * a + x ^ 2 * g := by
  have e : 1 - 2 * x * a + x ^ 2 * g - (1 - a ^ 2 / g) = (x * g - a) ^ 2 / g := by
    field_simp; ring
  have h2 : 0 ≤ (x * g - a) ^ 2 / g := by positivity
  linarith

theorem quad_min_eq {a g : ℝ} (hg : 0 < g) : 1 - 2 * (a / g) * a + (a / g) ^ 2 * g = 1 - a ^ 2 / g := by
  field_simp; ring

/-- **O `D₁` do texto é o mínimo do resíduo local** (sem a cauda), atingido em
`x = (1 − γ)/(log 2π − γ − 1)`. -/
theorem D1texto_minimo_local :
    (∀ x : ℝ, D1texto ≤ ∫ t in Ioc (0 : ℝ) 1, (1 - x * fr t) ^ 2) ∧
      ∫ t in Ioc (0 : ℝ) 1,
          (1 - (1 - eulerMascheroniConstant) /
            (Real.log (2 * π) - eulerMascheroniConstant - 1) * fr t) ^ 2 = D1texto := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [local_um]; exact quad_min g1_pos x
  · rw [local_um]; exact quad_min_eq g1_pos

/-- **`D1texto < D₁`**: ignorar a cauda subestima o resíduo. -/
theorem D1texto_lt_DN1 : D1texto < DN 1 := by
  rw [ATK.GramExato.DN_um]
  unfold D1texto
  have hg := g1_pos
  have ha : 0 < 1 - eulerMascheroniConstant := by
    linarith [eulerMascheroniConstant_lt_two_thirds]
  have : (1 - eulerMascheroniConstant) ^ 2 / (Real.log (2 * π) - eulerMascheroniConstant) <
      (1 - eulerMascheroniConstant) ^ 2 / (Real.log (2 * π) - eulerMascheroniConstant - 1) :=
    div_lt_div_of_pos_left (by positivity) hg (by linarith)
  linarith

def Ig1 : IR := IR.sub ATK.GramDois.Ig11 (IR.pt 1)
def ID1t : IR :=
  IR.sub (IR.pt 1) (IR.mul (IR.mul ATK.GramDois.Ib1 ATK.GramDois.Ib1) (IR.inv Ig1))

theorem Ig1_pos : (0 : ℚ) < Ig1.lo := by decide +kernel
theorem ID1t_lo : (31425 / 100000 : ℚ) < ID1t.lo := by decide +kernel
theorem ID1t_hi : ID1t.hi < (31427 / 100000 : ℚ) := by decide +kernel

theorem mem_g1 : IR.mem (ATK.GramDois.g11 - 1) Ig1 := by
  have := IR.mem_sub ATK.GramDois.mem_g11 (IR.mem_pt 1)
  push_cast at this
  exact this

/-- **`0,31425 < D1texto < 0,31427`** (contra `D₁ ∈ (0,85821; 0,85822)`). -/
theorem D1texto_cotas : (31425 / 100000 : ℝ) < D1texto ∧ D1texto < 31427 / 100000 := by
  have hm := IR.mem_sub (IR.mem_pt 1)
    (IR.mem_mul (IR.mem_mul ATK.GramDois.mem_b1 ATK.GramDois.mem_b1) (IR.mem_inv mem_g1 Ig1_pos))
  have hD : D1texto = 1 - ATK.GramDois.b1 * ATK.GramDois.b1 * (ATK.GramDois.g11 - 1)⁻¹ := by
    unfold D1texto ATK.GramDois.b1 ATK.GramDois.g11; rw [div_eq_mul_inv, sq]
  rw [hD]
  have hlo : ((31425 / 100000 : ℚ) : ℝ) < (ID1t.lo : ℝ) := by exact_mod_cast ID1t_lo
  have hhi : (ID1t.hi : ℝ) < ((31427 / 100000 : ℚ) : ℝ) := by exact_mod_cast ID1t_hi
  push_cast at hlo hhi hm
  obtain ⟨m1, m2⟩ := hm
  constructor
  · unfold ID1t at hlo; linarith
  · unfold ID1t at hhi; linarith

/-- **E1 corrigido**: `G₁₁ = log 2π − γ`, `D₁ = 1 − (1−γ)²/(log 2π − γ) ∈ (0,85821; 0,85822)`, e a
distância ao `D₁` do texto é `> 0,54`. -/
theorem E1_corrigido :
    ATK.GramBaezDuarte.G 1 0 0 = Real.log (2 * π) - eulerMascheroniConstant ∧
      DN 1 = 1 - (1 - eulerMascheroniConstant) ^ 2 / (Real.log (2 * π) - eulerMascheroniConstant) ∧
      (85821 / 100000 : ℝ) < DN 1 ∧ DN 1 < 85822 / 100000 ∧ 54 / 100 < DN 1 - D1texto := by
  refine ⟨ATK.GramExato.G_zero 1 one_pos, ATK.GramExato.DN_um, ATK.GramDois.D1_cotas.1,
    ATK.GramDois.D1_cotas.2, ?_⟩
  linarith [ATK.GramDois.D1_cotas.1, D1texto_cotas.2]

/-! ## E2. `G₁₁ = log 2` -/

/-- O `D₁` que sai de `G₁₁ = log 2`. -/
noncomputable def D1log2 : ℝ := 1 - (1 - eulerMascheroniConstant) ^ 2 / Real.log 2

def ID1l2 : IR :=
  IR.sub (IR.pt 1) (IR.mul (IR.mul ATK.GramDois.Ib1 ATK.GramDois.Ib1) (IR.inv ATK.GramDois.Il2))

theorem Il2_pos : (0 : ℚ) < ATK.GramDois.Il2.lo := by decide +kernel
theorem ID1l2_lo : (74212 / 100000 : ℚ) < ID1l2.lo := by decide +kernel
theorem ID1l2_hi : ID1l2.hi < (74213 / 100000 : ℚ) := by decide +kernel

/-- **O `0,7421` do texto vem do `G₁₁ = log 2` errado**: `1 − (1−γ)²/log 2 ∈ (0,74212; 0,74213)`. -/
theorem D1log2_cotas : (74212 / 100000 : ℝ) < D1log2 ∧ D1log2 < 74213 / 100000 := by
  have hm := IR.mem_sub (IR.mem_pt 1)
    (IR.mem_mul (IR.mem_mul ATK.GramDois.mem_b1 ATK.GramDois.mem_b1)
      (IR.mem_inv ATK.GramDois.mem_l2 Il2_pos))
  have hD : D1log2 = 1 - ATK.GramDois.b1 * ATK.GramDois.b1 * (Real.log 2)⁻¹ := by
    unfold D1log2 ATK.GramDois.b1; rw [div_eq_mul_inv, sq]
  rw [hD]
  have hlo : ((74212 / 100000 : ℚ) : ℝ) < (ID1l2.lo : ℝ) := by exact_mod_cast ID1l2_lo
  have hhi : (ID1l2.hi : ℝ) < ((74213 / 100000 : ℚ) : ℝ) := by exact_mod_cast ID1l2_hi
  push_cast at hlo hhi hm
  obtain ⟨m1, m2⟩ := hm
  constructor
  · unfold ID1l2 at hlo; linarith
  · unfold ID1l2 at hhi; linarith

/-- `log 2 < G₁₁` (a diferença é `log π − γ > 0`), logo o `D₁` do texto 1fb0a5dd subestima `D₁`. -/
theorem D1log2_lt_DN1 : D1log2 < DN 1 := by
  rw [ATK.GramExato.DN_um]
  unfold D1log2
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.log 2 < Real.log (2 * π) - eulerMascheroniConstant := by
    rw [ATK.GamaCotas.log_two_pi]
    obtain ⟨h1, -⟩ := ATK.GamaCotas.log_pi_cotas
    obtain ⟨-, h3⟩ := ATK.GamaCotas.gama_cotas
    linarith
  have ha : 0 < 1 - eulerMascheroniConstant := by
    linarith [eulerMascheroniConstant_lt_two_thirds]
  have : (1 - eulerMascheroniConstant) ^ 2 / (Real.log (2 * π) - eulerMascheroniConstant) <
      (1 - eulerMascheroniConstant) ^ 2 / Real.log 2 :=
    div_lt_div_of_pos_left (by positivity) h2 hlt
  linarith

/-! ## E3. A fórmula de `b_k` -/

/-- A fórmula do texto: `b̃_k = (1 − γ + log k − H_{k−1})/k`. -/
noncomputable def bTexto (k : ℕ) : ℝ :=
  (1 - eulerMascheroniConstant + Real.log k - (harmonic (k - 1) : ℝ)) / k

/-- **De onde vem**: `b̃_{j+1} = b_{j+1} − H_j/(j+1)` (subtrai `H_{k−1}/k` da fórmula certa). -/
theorem bTexto_eq (N : ℕ) (j : Fin N) :
    bTexto (j.val + 1) = ATK.GramBaezDuarte.b N j - (harmonic j.val : ℝ) / ((j.val : ℝ) + 1) := by
  rw [ATK.BaezDuarteVetorB.b_formula]
  unfold bTexto
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

/-- `b̃_{n+1} = (1 − γ − (H_n − log(n+1)))/(n+1)`. -/
theorem bTexto_eq_seq (n : ℕ) :
    bTexto (n + 1) = (1 - eulerMascheroniConstant - eulerMascheroniSeq n) / ((n : ℝ) + 1) := by
  unfold bTexto eulerMascheroniSeq
  simp only [Nat.add_sub_cancel]
  push_cast
  ring

theorem harmonic_tres : (harmonic 3 : ℝ) = 11 / 6 := by
  have : harmonic 3 = 11 / 6 := by
    simp only [harmonic, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  rw [this]; push_cast; ring

/-- **A fórmula do texto é negativa para todo `k ≥ 4`**: `H_{k−1} − log k ≥ H₃ − log 4 > 1 − γ`. -/
theorem bTexto_neg {k : ℕ} (hk : 4 ≤ k) : bTexto k < 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [bTexto_eq_seq]
  have h3 : eulerMascheroniSeq 3 ≤ eulerMascheroniSeq n :=
    strictMono_eulerMascheroniSeq.monotone (by omega)
  have hv : eulerMascheroniSeq 3 = 11 / 6 - 2 * Real.log 2 := by
    unfold eulerMascheroniSeq
    rw [harmonic_tres, show ((3 : ℕ) : ℝ) + 1 = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hg := ATK.GamaCotas.gama_cotas.1
  have hl := Real.log_two_lt_d9
  norm_num at hl
  apply div_neg_of_neg_of_pos _ (by positivity)
  linarith

/-- **Contradiz `b_k > 0`** para todo índice `k = j + 1 ≥ 4`. -/
theorem bTexto_contradiz (N : ℕ) (j : Fin N) (hj : 3 ≤ j.val) :
    bTexto (j.val + 1) < 0 ∧ 0 < ATK.GramBaezDuarte.b N j ∧
      ATK.GramBaezDuarte.b N j =
        (Real.log ((j.val : ℝ) + 1) + 1 - eulerMascheroniConstant) / ((j.val : ℝ) + 1) :=
  ⟨bTexto_neg (by omega), ATK.BaezDuarteVetorB.b_pos N j, ATK.BaezDuarteVetorB.b_formula N j⟩

/-- **Valores**: o `k = 2` do texto (`0,0579657578`) bate com a fórmula; os de `k = 3`
(`0,0072177332`) e `k = 4` (`−0,0060668825`) não. -/
theorem bTexto_valores :
    (579654 / 10 ^ 7 : ℝ) < bTexto 2 ∧ bTexto 2 < 579658 / 10 ^ 7 ∧
      bTexto 3 < 71323 / 10 ^ 7 ∧ (71323 / 10 ^ 7 : ℝ) < 72177332 / 10 ^ 10 ∧
      (-60639 / 10 ^ 7 : ℝ) < bTexto 4 ∧ (-60668825 / 10 ^ 10 : ℝ) < -60639 / 10 ^ 7 := by
  have hg := ATK.GamaCotas.gama_cotas
  have h2a := Real.log_two_gt_d9
  have h2b := Real.log_two_lt_d9
  have h3 := ATK.GamaCotas.log3_cotas
  norm_num at h2a h2b
  have e2 : bTexto 2 = (Real.log 2 - eulerMascheroniConstant) / 2 := by
    unfold bTexto; norm_num [harmonic]; ring
  have e3 : bTexto 3 = (1 - eulerMascheroniConstant + Real.log 3 - 3 / 2) / 3 := by
    unfold bTexto; norm_num [harmonic, Finset.sum_range_succ]
  have e4 : bTexto 4 = (1 - eulerMascheroniConstant + 2 * Real.log 2 - 11 / 6) / 4 := by
    unfold bTexto
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, show 4 - 1 = 3 from rfl, harmonic_tres]
    push_cast; ring
  rw [e2, e3, e4]
  refine ⟨by linarith [hg.2], by linarith [hg.1], by linarith [hg.1, h3.2], by norm_num,
    by linarith [hg.2], by norm_num⟩

/-! ## E4. Integral por pedaços e o valor tabelado de `G₁₂` -/

/-- **Quando os coeficientes coincidem**: `q/i + p/j = p/i + q/j ⟺ (p − q)(1/i − 1/j) = 0`. -/
theorem coef_coincide_iff {i j p q : ℝ} :
    q / i + p / j = p / i + q / j ↔ (p - q) * (1 / i - 1 / j) = 0 := by
  have e : (p / i + q / j) - (q / i + p / j) = (p - q) * (1 / i - 1 / j) := by ring
  constructor
  · intro h; rw [← e]; linarith
  · intro h; linarith [e, h]

/-- **Toda soma parcial fica por baixo**: `Pc(K) + ½ ≤ G₁₂` (integrando `≥ 0`). -/
theorem truncado_por_baixo (K : ℕ) : ATK.GramDois.Pc K + 1 / 2 ≤ ATK.GramBaezDuarte.G 2 0 1 := by
  have hb1 : 1 / (2 * (K : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [K.cast_nonneg (α := ℝ)]
  have h1 : ATK.GramDois.Pc K = ∫ t in Ioc (1 / (2 * (K : ℝ) + 1)) 1, rho 1 t * rho 2 t := by
    rw [← ATK.GramDois.integral_pares K, intervalIntegral.integral_of_le hb1]
  have h2 : ∫ t in Ioc (1 / (2 * (K : ℝ) + 1)) 1, rho 1 t * rho 2 t ≤
      ∫ t in Ioc (0 : ℝ) 1, rho 1 t * rho 2 t :=
    setIntegral_mono_set (ATK.GramDois.integrableOn_rho12 0 1)
      (Eventually.of_forall fun t => ATK.GramDois.rho12_nonneg t)
      (Set.Ioc_subset_Ioc_left (by positivity)).eventuallyLE
  have h3 : ATK.GramBaezDuarte.G 2 0 1 = (∫ t in Ioc (0 : ℝ) 1, rho 1 t * rho 2 t) + 1 / 2 := by
    rw [ATK.GramDois.G_um_dois, ATK.GramDois.integral_Ioc_rho12, ATK.GamaCotas.log_two_pi]
    ring
  linarith

theorem IG12_lo : (7722084 / 10 ^ 7 : ℚ) < ATK.GramDois.Ig12.lo := by decide +kernel
theorem IG12_hi : ATK.GramDois.Ig12.hi < (7722094 / 10 ^ 7 : ℚ) := by decide +kernel

/-- **`0,7722084 < G₁₂ < 0,7722094`**; o valor tabelado `0,7722083` está abaixo. -/
theorem G12_cotas :
    (7722084 / 10 ^ 7 : ℝ) < ATK.GramBaezDuarte.G 2 0 1 ∧
      ATK.GramBaezDuarte.G 2 0 1 < 7722094 / 10 ^ 7 ∧
      ATK.GramBaezDuarte.G 2 0 1 ≠ 7722083 / 10 ^ 7 := by
  rw [ATK.GramDois.G2_01]
  have hm := ATK.GramDois.mem_g12
  have hlo : ((7722084 / 10 ^ 7 : ℚ) : ℝ) < (ATK.GramDois.Ig12.lo : ℝ) := by exact_mod_cast IG12_lo
  have hhi : (ATK.GramDois.Ig12.hi : ℝ) < ((7722094 / 10 ^ 7 : ℚ) : ℝ) := by exact_mod_cast IG12_hi
  push_cast at hlo hhi
  obtain ⟨m1, m2⟩ := hm
  refine ⟨by linarith, by linarith, fun h => by linarith⟩

/-! ## E12. O ajuste de dois pontos e `C₀` -/

open ATK.BarreiraModelos (D256 D8000)

/-- `C₀ = 2 + γ − log 4π`. -/
noncomputable def C0 : ℝ := 2 + eulerMascheroniConstant - Real.log (4 * π)

theorem C0_pos : 0 < C0 := by unfold C0; linarith [ATK.GamaCotas.C0_cotas.1]

/-- **Os dois produtos `D_N log N` estão abaixo de `C₀`.** -/
theorem produtos_abaixo_C0 : D256 * Real.log 256 < C0 ∧ D8000 * Real.log 8000 < C0 := by
  obtain ⟨hc1, -⟩ := ATK.GamaCotas.C0_cotas
  rw [ATK.BarreiraModelos.log256, ATK.BarreiraModelos.log8000]
  have h4 := ATK.BarreiraModelos.log4
  have h2b := Real.log_two_lt_d9
  obtain ⟨-, h5b⟩ := ATK.BarreiraModelos.log5_sub_log4_bounds
  unfold D256 D8000 C0
  norm_num at h2b
  constructor <;> linarith

/-- **Razões**: `D₂₅₆ log 256/C₀ ∈ (0,988; 0,9885)`, `D₈₀₀₀ log 8000/C₀ ∈ (0,986; 0,9864)`. -/
theorem razoes_C0 :
    (988 / 1000 : ℝ) < D256 * Real.log 256 / C0 ∧ D256 * Real.log 256 / C0 < 9885 / 10000 ∧
      (986 / 1000 : ℝ) < D8000 * Real.log 8000 / C0 ∧ D8000 * Real.log 8000 / C0 < 9864 / 10000 := by
  have hC := C0_pos
  obtain ⟨hc1, hc2⟩ := ATK.GamaCotas.C0_cotas
  have h4 := ATK.BarreiraModelos.log4
  have h2a := Real.log_two_gt_d9
  have h2b := Real.log_two_lt_d9
  obtain ⟨h5a, h5b⟩ := ATK.BarreiraModelos.log5_sub_log4_bounds
  norm_num at h2a h2b
  have e256 : D256 * Real.log 256 = 8 * D256 * Real.log 2 := by
    rw [ATK.BarreiraModelos.log256]; ring
  have e8000 : D8000 * Real.log 8000 = D8000 * (6 * Real.log 2 + 3 * Real.log 5) := by
    rw [ATK.BarreiraModelos.log8000]
  unfold C0 at hC ⊢
  rw [e256, e8000]
  unfold D256 D8000
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hC]; linarith
  · rw [div_lt_iff₀ hC]; linarith
  · rw [lt_div_iff₀ hC]; linarith
  · rw [div_lt_iff₀ hC]; linarith

/-- Também não há modelo `C/log N` (intercepto `0`) passando pelos dois pontos. -/
theorem sem_C_unico : ¬ ∃ C : ℝ, D256 = C / Real.log 256 ∧ D8000 = C / Real.log 8000 := by
  rintro ⟨C, h0, h1⟩
  have hL0 : 0 < Real.log 256 := Real.log_pos (by norm_num)
  have hL1 : 0 < Real.log 8000 := Real.log_pos (by norm_num)
  have e0 : D256 * Real.log 256 = C := by rw [h0]; field_simp
  have e1 : D8000 * Real.log 8000 = C := by rw [h1]; field_simp
  have := ATK.BarreiraModelos.produto_decresce
  linarith

/-- **E12 corrigido**: o que os dois valores sustentam é `D₈₀₀₀ log 8000 < D₂₅₆ log 256 < C₀`;
`D_∞ ≥ 0` sempre, e o intercepto do ajuste (negativo) não é estimativa de `D_∞`. -/
theorem E12_corrigido :
    D8000 * Real.log 8000 < D256 * Real.log 256 ∧ D256 * Real.log 256 < C0 ∧
      0 ≤ ATK.DInfinito.dInf ∧
      ∀ a C : ℝ, D256 = a + C / Real.log 256 → D8000 = a + C / Real.log 8000 →
        a < 0 ∧ a < ATK.DInfinito.dInf :=
  ⟨ATK.BarreiraModelos.produto_decresce, produtos_abaixo_C0.1, ATK.DInfinito.dInf_nonneg,
    fun _ _ h0 h1 => ⟨(ATK.BarreiraModelos.ajuste_negativo h0 h1).1,
      lt_of_lt_of_le (ATK.BarreiraModelos.ajuste_negativo h0 h1).1 ATK.DInfinito.dInf_nonneg⟩⟩

end ATK.ErrosGram

-- Auditoria de axiomas (kernel)
#print axioms ATK.ErrosGram.residuo_expandido
#print axioms ATK.ErrosGram.residuo_um
#print axioms ATK.ErrosGram.local_um
#print axioms ATK.ErrosGram.residuo_split
#print axioms ATK.ErrosGram.G11_partes
#print axioms ATK.ErrosGram.g1_pos
#print axioms ATK.ErrosGram.quad_min
#print axioms ATK.ErrosGram.quad_min_eq
#print axioms ATK.ErrosGram.D1texto_minimo_local
#print axioms ATK.ErrosGram.D1texto_lt_DN1
#print axioms ATK.ErrosGram.Ig1_pos
#print axioms ATK.ErrosGram.ID1t_lo
#print axioms ATK.ErrosGram.ID1t_hi
#print axioms ATK.ErrosGram.mem_g1
#print axioms ATK.ErrosGram.D1texto_cotas
#print axioms ATK.ErrosGram.E1_corrigido
#print axioms ATK.ErrosGram.Il2_pos
#print axioms ATK.ErrosGram.ID1l2_lo
#print axioms ATK.ErrosGram.ID1l2_hi
#print axioms ATK.ErrosGram.D1log2_cotas
#print axioms ATK.ErrosGram.D1log2_lt_DN1
#print axioms ATK.ErrosGram.bTexto_eq
#print axioms ATK.ErrosGram.bTexto_eq_seq
#print axioms ATK.ErrosGram.harmonic_tres
#print axioms ATK.ErrosGram.bTexto_neg
#print axioms ATK.ErrosGram.bTexto_contradiz
#print axioms ATK.ErrosGram.bTexto_valores
#print axioms ATK.ErrosGram.coef_coincide_iff
#print axioms ATK.ErrosGram.truncado_por_baixo
#print axioms ATK.ErrosGram.IG12_lo
#print axioms ATK.ErrosGram.IG12_hi
#print axioms ATK.ErrosGram.G12_cotas
#print axioms ATK.ErrosGram.C0_pos
#print axioms ATK.ErrosGram.produtos_abaixo_C0
#print axioms ATK.ErrosGram.razoes_C0
#print axioms ATK.ErrosGram.sem_C_unico
#print axioms ATK.ErrosGram.E12_corrigido
