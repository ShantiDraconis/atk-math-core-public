import ATK.TruncamentoZero

/-!
# ATK-PARAMETRIC-GEOMETRY — o sistema paramétrico do texto encaminhado, provado

Tudo aqui é sobre o **modelo**, não sobre a zeta (essa parte está em `ATK.ZetaTroca`).

* **Troca** `T(z) = i z̄` (`troca`): `T(a + ib) = b + ia`, `T ∘ T = id`, `|T z| = |z|`, matriz `[[0,1],[1,0]]`
  com determinante `−1` (isometria que inverte a orientação).
* **Lei A7** `k_N = c + 1/(2N) + 1/(2(N+1)²)` com `c` livre (`k`): é o centro de `c + 1/N` e `c + 1/(N+1)²`;
  `k_N > c`, estritamente decrescente, `k_N → c`, `N(k_N − c) → 1/2`.
* **Cálculo** em `t > 0`: `k′ = −1/(2t²) − 1/(t+1)³ < 0`, `k″ = 1/t³ + 3/(t+1)⁴ > 0`, primitiva
  `ct + ½ log t − 1/(2(t+1))`; `∫_{N₀}^{N} (k − c) = ½ log(N/N₀) + 1/(2(N₀+1)) − 1/(2(N+1))`, que diverge.
* **Lei geral** `c + A/N^p + B/(N+1)^q` (`p, q > 0`) → `c`; com `A, B > 0` fica acima e decresce; com sinais
  opostos pode ficar abaixo (`sinal_depende_da_lei`).
* **Centro** de duas aproximações: dentro da tolerância (`centro_aprox`); pode ser **exatamente** `c` com as
  duas coordenadas fora de `c` (`cancelamento`).
* **Semântica**: `Approx ⇏ Exact`; `(∀ N, v_N ≠ c)` é compatível com `v_N → c`; **um número fixo que é
  aproximação de `c` em toda tolerância é igual a `c`** (`exato_de_toda_tolerancia`).
* **Constante terminal**: os incrementos, as derivadas e a taxa não determinam `c` (`incrementos_iguais`);
  uma medição exata de `k_{N₀}` determina (`c_de_medicao`).
-/

open Complex Filter Topology Set

namespace ATK.ModeloParametrico

/-! ### Troca de coordenadas -/

/-- `T(z) = i z̄`: troca parte real e parte imaginária. -/
noncomputable def troca (z : ℂ) : ℂ := I * (starRingEnd ℂ) z

theorem troca_re (z : ℂ) : (troca z).re = z.im := by simp [troca]

theorem troca_im (z : ℂ) : (troca z).im = z.re := by simp [troca]

theorem troca_troca (z : ℂ) : troca (troca z) = z :=
  Complex.ext (by rw [troca_re, troca_im]) (by rw [troca_im, troca_re])

theorem norm_troca (z : ℂ) : ‖troca z‖ = ‖z‖ := by simp [troca]

theorem det_troca : Matrix.det !![(0 : ℝ), 1; 1, 0] = -1 := by
  simp [Matrix.det_fin_two]

theorem troca_matriz (z : ℂ) :
    ![(troca z).re, (troca z).im] = (!![(0 : ℝ), 1; 1, 0]).mulVec ![z.re, z.im] := by
  ext i
  fin_cases i <;> simp [troca_re, troca_im, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-! ### Lei A7 -/

/-- `k_N = c + 1/(2N) + 1/(2(N+1)²)`, com `c` livre. -/
noncomputable def k (c : ℝ) (N : ℕ) : ℝ := c + 1 / (2 * (N : ℝ)) + 1 / (2 * ((N : ℝ) + 1) ^ 2)

/-- Centro de duas coordenadas. -/
noncomputable def centro (v₁ v₂ : ℝ) : ℝ := (v₁ + v₂) / 2

theorem k_eq_centro (c : ℝ) (N : ℕ) :
    k c N = centro (c + 1 / (N : ℝ)) (c + 1 / ((N : ℝ) + 1) ^ 2) := by
  unfold k centro; simp only [one_div, mul_inv]; ring

theorem k_gt (c : ℝ) {N : ℕ} (hN : 1 ≤ N) : c < k c N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 0 < 1 / (2 * (N : ℝ)) := by positivity
  have h2 : 0 < 1 / (2 * ((N : ℝ) + 1) ^ 2) := by positivity
  unfold k; linarith

theorem k_ne (c : ℝ) {N : ℕ} (hN : 1 ≤ N) : k c N ≠ c := (k_gt c hN).ne'

theorem k_anti (c : ℝ) {N : ℕ} (hN : 1 ≤ N) : k c (N + 1) < k c N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have a : 1 / (2 * ((N : ℝ) + 1)) < 1 / (2 * (N : ℝ)) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have b : 1 / (2 * ((N : ℝ) + 1 + 1) ^ 2) < 1 / (2 * ((N : ℝ) + 1) ^ 2) :=
    one_div_lt_one_div_of_lt (by positivity) (by nlinarith)
  unfold k; push_cast; linarith

theorem k_tendsto (c : ℝ) : Tendsto (k c) atTop (𝓝 c) := by
  have h1 : Tendsto (fun N : ℕ => ((N : ℝ))⁻¹) atTop (𝓝 0) := tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hsq : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun N => by nlinarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])
      tendsto_natCast_atTop_atTop
  have h2 := hsq.inv_tendsto_atTop
  have e : k c = fun N : ℕ => c + 1 / 2 * ((N : ℝ))⁻¹ + 1 / 2 * (((N : ℝ) + 1) ^ 2)⁻¹ := by
    funext N; unfold k; simp only [one_div, mul_inv]
  rw [e]
  have := (tendsto_const_nhds (x := c)).add (h1.const_mul (1 / 2)) |>.add (h2.const_mul (1 / 2))
  simpa using this

/-- `N(k_N − c) → 1/2`. -/
theorem k_taxa (c : ℝ) : Tendsto (fun N : ℕ => (N : ℝ) * (k c N - c)) atTop (𝓝 (1 / 2)) := by
  have hg : Tendsto (fun N : ℕ => (N : ℝ) / (2 * ((N : ℝ) + 1) ^ 2)) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => by positivity) (fun N => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]
  have heq : ∀ᶠ N : ℕ in atTop,
      1 / 2 + (N : ℝ) / (2 * ((N : ℝ) + 1) ^ 2) = (N : ℝ) * (k c N - c) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    unfold k; field_simp; ring
  have := (tendsto_const_nhds (x := (1 / 2 : ℝ))).add hg
  rw [add_zero] at this
  exact this.congr' heq

/-! ### Constante terminal -/

/-- Os incrementos não veem `c`. -/
theorem incrementos_iguais (c c' : ℝ) (N M : ℕ) : k c N - k c M = k c' N - k c' M := by
  unfold k; ring

theorem k_desloca (c c' : ℝ) (N : ℕ) : k c' N = k c N + (c' - c) := by unfold k; ring

/-- Duas constantes diferentes dão curvas com os mesmos incrementos e limites diferentes. -/
theorem terminal_indeterminado {c c' : ℝ} (h : c ≠ c') :
    (∀ N M, k c N - k c M = k c' N - k c' M) ∧
      Tendsto (k c) atTop (𝓝 c) ∧ Tendsto (k c') atTop (𝓝 c') ∧ c ≠ c' :=
  ⟨incrementos_iguais c c', k_tendsto c, k_tendsto c', h⟩

/-- Uma medição exata de `k_{N₀}` determina `c`. -/
theorem c_de_medicao (c : ℝ) (N : ℕ) :
    c = k c N - 1 / (2 * (N : ℝ)) - 1 / (2 * ((N : ℝ) + 1) ^ 2) := by
  unfold k; ring

/-! ### Cálculo em `t > 0` -/

/-- A lei em variável contínua. -/
noncomputable def kt (c t : ℝ) : ℝ := c + 1 / (2 * t) + 1 / (2 * (t + 1) ^ 2)

noncomputable def kt' (t : ℝ) : ℝ := -1 / (2 * t ^ 2) - 1 / (t + 1) ^ 3

noncomputable def kt'' (t : ℝ) : ℝ := 1 / t ^ 3 + 3 / (t + 1) ^ 4

theorem hasDerivAt_kt (c : ℝ) {t : ℝ} (ht : 0 < t) : HasDerivAt (kt c) (kt' t) t := by
  have ht1 : t + 1 ≠ 0 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => x⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht.ne'
  have h2 : HasDerivAt (fun x : ℝ => ((x + 1) ^ 2)⁻¹)
      (-((↑2 : ℝ) * (t + 1) ^ (2 - 1) * 1) / ((t + 1) ^ 2) ^ 2) t :=
    (((hasDerivAt_id' t).add_const 1).pow 2).inv (pow_ne_zero 2 ht1)
  have h := ((hasDerivAt_const t c).add (h1.const_mul (1 / 2))).add (h2.const_mul (1 / 2))
  have e : kt c = fun x => c + 1 / 2 * x⁻¹ + 1 / 2 * ((x + 1) ^ 2)⁻¹ := by
    funext x; unfold kt; simp only [one_div, mul_inv]
  rw [e]
  convert h using 1
  unfold kt'
  field_simp
  ring

theorem hasDerivAt_kt' {t : ℝ} (ht : 0 < t) : HasDerivAt kt' (kt'' t) t := by
  have ht1 : t + 1 ≠ 0 := by linarith
  have h1 : HasDerivAt (fun x : ℝ => (x ^ 2)⁻¹) (-((↑2 : ℝ) * t ^ (2 - 1) * 1) / (t ^ 2) ^ 2) t :=
    ((hasDerivAt_id' t).pow 2).inv (pow_ne_zero 2 ht.ne')
  have h2 : HasDerivAt (fun x : ℝ => ((x + 1) ^ 3)⁻¹)
      (-((↑3 : ℝ) * (t + 1) ^ (3 - 1) * 1) / ((t + 1) ^ 3) ^ 2) t :=
    (((hasDerivAt_id' t).add_const 1).pow 3).inv (pow_ne_zero 3 ht1)
  have h := (h1.const_mul (-1 / 2)).sub h2
  have e : kt' = fun x => -1 / 2 * (x ^ 2)⁻¹ - ((x + 1) ^ 3)⁻¹ := by
    funext x; unfold kt'; simp only [div_eq_mul_inv, mul_inv, neg_mul, one_mul]
  rw [e]
  convert h using 1
  unfold kt''
  field_simp
  ring

theorem kt'_neg {t : ℝ} (ht : 0 < t) : kt' t < 0 := by
  unfold kt'
  have : 0 < 1 / (2 * t ^ 2) := by positivity
  have : 0 < 1 / (t + 1) ^ 3 := by positivity
  rw [neg_div]; linarith

theorem kt''_pos {t : ℝ} (ht : 0 < t) : 0 < kt'' t := by unfold kt''; positivity

theorem kt_strictAntiOn (c : ℝ) : StrictAntiOn (kt c) (Ioi 0) :=
  strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun t ht => (hasDerivAt_kt c ht).continuousAt.continuousWithinAt)
    (fun t ht => by
      rw [interior_Ioi] at ht
      rw [(hasDerivAt_kt c ht).deriv]; exact kt'_neg ht)

/-- Primitiva: `P(t) = ct + ½ log t − 1/(2(t+1))`. -/
noncomputable def P (c t : ℝ) : ℝ := c * t + 1 / 2 * Real.log t - 1 / (2 * (t + 1))

theorem hasDerivAt_P (c : ℝ) {t : ℝ} (ht : 0 < t) : HasDerivAt (P c) (kt c t) t := by
  have ht1 : t + 1 ≠ 0 := by linarith
  have h1 := (hasDerivAt_id' t).const_mul c
  have h2 := (Real.hasDerivAt_log ht.ne').const_mul (1 / 2)
  have h3 : HasDerivAt (fun x : ℝ => (x + 1)⁻¹) (-1 / (t + 1) ^ 2) t :=
    ((hasDerivAt_id' t).add_const 1).inv ht1
  have h := (h1.add h2).sub (h3.const_mul (1 / 2))
  have e : P c = fun x => c * x + 1 / 2 * Real.log x - 1 / 2 * (x + 1)⁻¹ := by
    funext x; unfold P; simp only [one_div, mul_inv]
  rw [e]
  convert h using 1
  unfold kt
  field_simp
  ring

/-- **Integral do desvio**: `∫_{N₀}^{N} (k − c) = ½ log(N/N₀) + 1/(2(N₀+1)) − 1/(2(N+1))`. -/
theorem integral_desvio {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, (kt 0 t) = 1 / 2 * Real.log (b / a) + 1 / (2 * (a + 1)) - 1 / (2 * (b + 1)) := by
  have hb : 0 < b := ha.trans_le hab
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (P 0) (kt 0 x) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact hasDerivAt_P 0 (ha.trans_le hx.1)
  have hcont : ContinuousOn (kt 0) (uIcc a b) := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    exact (hasDerivAt_kt 0 (ha.trans_le hx.1)).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  unfold P
  rw [Real.log_div hb.ne' ha.ne']
  ring

/-- O erro instantâneo vai a zero, mas a integral acumulada diverge. -/
theorem integral_desvio_diverge :
    Tendsto (fun b : ℝ => ∫ t in (1 : ℝ)..b, kt 0 t) atTop atTop := by
  have hlog : Tendsto (fun b : ℝ => 1 / 2 * Real.log b) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hlog
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with b hb
  rw [integral_desvio one_pos hb, div_one]
  have : 1 / (2 * (b + 1)) ≤ 1 / (2 * (1 + 1)) :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

/-! ### Lei geral -/

/-- `c + A/N^p + B/(N+1)^q`. -/
noncomputable def kg (c A B p q : ℝ) (N : ℕ) : ℝ :=
  c + A / (N : ℝ) ^ p + B / ((N : ℝ) + 1) ^ q

theorem kg_tendsto (c A B : ℝ) {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Tendsto (kg c A B p q) atTop (𝓝 c) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ q) atTop atTop :=
    (tendsto_rpow_atTop hq).comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have := ((tendsto_const_nhds (x := c)).add ((tendsto_const_nhds (x := A)).div_atTop h1)).add
    ((tendsto_const_nhds (x := B)).div_atTop h2)
  simp only [add_zero] at this
  exact this

theorem kg_acima (c : ℝ) {A B p q : ℝ} (hA : 0 < A) (hB : 0 < B) {N : ℕ} (hN : 1 ≤ N) :
    c < kg c A B p q N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 0 < A / (N : ℝ) ^ p := div_pos hA (Real.rpow_pos_of_pos hN0 p)
  have h2 : 0 < B / ((N : ℝ) + 1) ^ q := div_pos hB (Real.rpow_pos_of_pos (by linarith) q)
  unfold kg; linarith

theorem kg_decresce (c : ℝ) {A B p q : ℝ} (hA : 0 < A) (hB : 0 < B) (hp : 0 < p) (hq : 0 < q)
    {N : ℕ} (hN : 1 ≤ N) : kg c A B p q (N + 1) < kg c A B p q N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : A / ((N : ℝ) + 1) ^ p < A / (N : ℝ) ^ p :=
    div_lt_div_of_pos_left hA (Real.rpow_pos_of_pos hN0 p)
      (Real.rpow_lt_rpow hN0.le (by linarith) hp)
  have h2 : B / ((N : ℝ) + 1 + 1) ^ q < B / ((N : ℝ) + 1) ^ q :=
    div_lt_div_of_pos_left hB (Real.rpow_pos_of_pos (by linarith) q)
      (Real.rpow_lt_rpow (by linarith) (by linarith) hq)
  unfold kg; push_cast; linarith

/-- O lado da aproximação depende da lei: com `A = 1`, `B = −2`, `p = q = 1`, `k_2 < c`. -/
theorem sinal_depende_da_lei (c : ℝ) : kg c 1 (-2) 1 1 2 < c := by
  unfold kg; norm_num

/-! ### Centro de duas aproximações -/

theorem centro_aprox {v₁ v₂ c τ : ℝ} (h1 : |v₁ - c| ≤ τ) (h2 : |v₂ - c| ≤ τ) :
    |centro v₁ v₂ - c| ≤ τ := by
  unfold centro
  have e : (v₁ + v₂) / 2 - c = ((v₁ - c) + (v₂ - c)) / 2 := by ring
  rw [e, abs_div, abs_two, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith [abs_add_le (v₁ - c) (v₂ - c)]

/-- Desvios opostos se cancelam: as duas coordenadas fora de `c`, o centro exatamente em `c`. -/
theorem cancelamento (c ε : ℝ) (hε : ε ≠ 0) :
    c + ε ≠ c ∧ c - ε ≠ c ∧ centro (c + ε) (c - ε) = c := by
  refine ⟨fun h => hε (by linarith), fun h => hε (by linarith), ?_⟩
  unfold centro; ring

/-! ### Semântica -/

def Approx (v c τ : ℝ) : Prop := |v - c| ≤ τ
def Exact (v c : ℝ) : Prop := v = c
def Offset (v c : ℝ) : Prop := v ≠ c
def Converges (v : ℕ → ℝ) (c : ℝ) : Prop := Tendsto v atTop (𝓝 c)

theorem approx_nao_implica_exato : ∃ v c τ : ℝ, Approx v c τ ∧ ¬ Exact v c :=
  ⟨1 / 2 + 1 / 10, 1 / 2, 1, by unfold Approx; norm_num [abs_of_pos], by unfold Exact; norm_num⟩

/-- `(∀ N, v_N ≠ c)` é compatível com `v_N → c`. -/
theorem offset_compativel (c : ℝ) :
    ∃ v : ℕ → ℝ, (∀ N, Offset (v N) c) ∧ Converges v c := by
  refine ⟨fun N => c + 1 / ((N : ℝ) + 1), fun N => ?_, ?_⟩
  · unfold Offset
    have : 0 < 1 / ((N : ℝ) + 1) := by positivity
    linarith
  · unfold Converges
    have := (tendsto_const_nhds (x := c)).add tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using this

/-- **Um número fixo que aproxima `c` em toda tolerância é `c`.** Só uma sequência pode ser
"aproximada sem nunca ser exata". -/
theorem exato_de_toda_tolerancia {v c : ℝ} (h : ∀ τ > 0, Approx v c τ) : Exact v c := by
  unfold Exact
  by_contra hne
  have hpos : 0 < |v - c| / 2 := by
    have : 0 < |v - c| := abs_pos.mpr (sub_ne_zero.mpr hne)
    linarith
  have := h _ hpos
  unfold Approx at this
  linarith

/-- O limite de uma sequência sempre deslocada é único: se `v_N → c` e `v_N → c'`, então `c = c'`. -/
theorem limite_unico {v : ℕ → ℝ} {c c' : ℝ} (h : Converges v c) (h' : Converges v c') : c = c' :=
  tendsto_nhds_unique h h'

end ATK.ModeloParametrico

#print axioms ATK.ModeloParametrico.troca_re
#print axioms ATK.ModeloParametrico.troca_im
#print axioms ATK.ModeloParametrico.troca_troca
#print axioms ATK.ModeloParametrico.norm_troca
#print axioms ATK.ModeloParametrico.det_troca
#print axioms ATK.ModeloParametrico.troca_matriz
#print axioms ATK.ModeloParametrico.k_eq_centro
#print axioms ATK.ModeloParametrico.k_gt
#print axioms ATK.ModeloParametrico.k_ne
#print axioms ATK.ModeloParametrico.k_anti
#print axioms ATK.ModeloParametrico.k_tendsto
#print axioms ATK.ModeloParametrico.k_taxa
#print axioms ATK.ModeloParametrico.incrementos_iguais
#print axioms ATK.ModeloParametrico.k_desloca
#print axioms ATK.ModeloParametrico.terminal_indeterminado
#print axioms ATK.ModeloParametrico.c_de_medicao
#print axioms ATK.ModeloParametrico.hasDerivAt_kt
#print axioms ATK.ModeloParametrico.hasDerivAt_kt'
#print axioms ATK.ModeloParametrico.kt'_neg
#print axioms ATK.ModeloParametrico.kt''_pos
#print axioms ATK.ModeloParametrico.kt_strictAntiOn
#print axioms ATK.ModeloParametrico.hasDerivAt_P
#print axioms ATK.ModeloParametrico.integral_desvio
#print axioms ATK.ModeloParametrico.integral_desvio_diverge
#print axioms ATK.ModeloParametrico.kg_tendsto
#print axioms ATK.ModeloParametrico.kg_acima
#print axioms ATK.ModeloParametrico.kg_decresce
#print axioms ATK.ModeloParametrico.sinal_depende_da_lei
#print axioms ATK.ModeloParametrico.centro_aprox
#print axioms ATK.ModeloParametrico.cancelamento
#print axioms ATK.ModeloParametrico.approx_nao_implica_exato
#print axioms ATK.ModeloParametrico.offset_compativel
#print axioms ATK.ModeloParametrico.exato_de_toda_tolerancia
#print axioms ATK.ModeloParametrico.limite_unico
