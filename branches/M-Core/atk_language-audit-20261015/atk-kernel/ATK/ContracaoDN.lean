import ATK.BaezDuarteBridge
import ATK.AlgebraTerminal

/-!
# ATK — Caudas de `D_N`: contração, piso logarítmico e o que uma amostra finita decide

Testa no kernel as propostas de "certificado quantitativo" para Riemann:

* `tendsto_zero_de_contracao`, **`riemann_de_contracao`**: se `D_{2N} ≤ q·D_N` para todo `N ≥ N₀`,
  com `q < 1`, então `D_N → 0` e (ponte B1, já provada) **RH**.
* **`sem_contracao_de_piso_log`**: uma contração geométrica é **incompatível** com um piso
  `D_N ≥ c/log(N+2)`. Báez-Duarte–Balazard–Landreau–Saias (2000) e Burnol (2002) provaram
  `liminf D_N log N > 0` para a distância de Báez-Duarte; logo a contração proposta é **falsa**
  para a sequência real (o que o kernel certifica é a incompatibilidade; o piso é literatura).
  A taxa certa é `1/log N` — a forma de O1 (`UniformLogBound`).
* **`amostra_finita_nao_decide`**: qualquer prefixo finito decrescente e positivo admite uma
  extensão com limite `0` e outra com limite positivo — nenhuma tabela finita de `D_N` decide O1.
* Certificados: `cert_Dinf` (`D_∞ ∈ [0,1]`, estado `P`), `cert_Dinf_numerico` (`D_∞ ∈ [0; 0,00823372]`
  sob a hipótese numérica `D_256 ≤ 0,00823372`, estado `A`), **`fecho_RH_iff`**: existe certificado
  demonstrado `D_∞ ∈ [0,0]` ⟺ `D_∞ = 0`, e isso implica RH (`fecho_RH`).
-/

open Filter Topology

namespace ATK.ContracaoDN

open ATK.Conditional.Riemann ATK.RiemannConcrete ATK.BaezDuarteBridge ATK.AlgebraTerminal
  ATK.AlgebraTerminal.Intervalo

theorem iter_contracao {D : ℕ → ℝ} {q : ℝ} {N₀ : ℕ} (hc : ∀ N ≥ N₀, D (2 * N) ≤ q * D N)
    (hq0 : 0 ≤ q) {M : ℕ} (hM : N₀ ≤ M) (k : ℕ) : D (2 ^ k * M) ≤ q ^ k * D M := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : N₀ ≤ 2 ^ k * M := le_trans hM (Nat.le_mul_of_pos_left M (by positivity))
    calc D (2 ^ (k + 1) * M) = D (2 * (2 ^ k * M)) := by rw [pow_succ]; ring_nf
      _ ≤ q * D (2 ^ k * M) := hc _ hk
      _ ≤ q * (q ^ k * D M) := mul_le_mul_of_nonneg_left ih hq0
      _ = q ^ (k + 1) * D M := by ring

/-- **Contração por duplicação ⇒ limite zero.** -/
theorem tendsto_zero_de_contracao {D : ℕ → ℝ} (hD : Antitone D) (h0 : ∀ n, 0 ≤ D n)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {N₀ : ℕ}
    (hc : ∀ N ≥ N₀, D (2 * N) ≤ q * D N) : Tendsto D atTop (𝓝 0) := by
  have hbdd : BddBelow (Set.range D) := ⟨0, by rintro _ ⟨n, rfl⟩; exact h0 n⟩
  have hL := tendsto_atTop_ciInf hD hbdd
  have hinf0 : 0 ≤ ⨅ n, D n := le_ciInf h0
  have hle : ∀ k : ℕ, ⨅ n, D n ≤ q ^ k * D N₀ := fun k =>
    (ciInf_le hbdd _).trans (iter_contracao hc hq0 le_rfl k)
  have hlim : Tendsto (fun k : ℕ => q ^ k * D N₀) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (D N₀)
  have hinf : ⨅ n, D n = 0 := le_antisymm (ge_of_tendsto' hlim hle) hinf0
  rwa [hinf] at hL

/-- **Contração de `D_N` ⇒ RH** (via a ponte B1 provada). -/
theorem riemann_de_contracao {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {N₀ : ℕ}
    (hc : ∀ N ≥ N₀, DN (2 * N) ≤ q * DN N) : RiemannHypothesis := by
  have h := tendsto_zero_de_contracao DN_antitone DN_nonneg hq0 hq1 hc
  exact riemann_of_iInf_zero (tendsto_nhds_unique DN_tendsto_iInf h)

theorem log_pow_mul_le {M k : ℕ} (hM : 1 ≤ M) :
    Real.log (((2 ^ k * M : ℕ) : ℝ) + 2) ≤ (k + 1) * Real.log ((M : ℝ) + 2) := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hle : ((2 ^ k * M : ℕ) : ℝ) + 2 ≤ 2 ^ k * ((M : ℝ) + 2) := by push_cast; nlinarith
  have hlog2 : Real.log 2 ≤ Real.log ((M : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith)
  calc Real.log (((2 ^ k * M : ℕ) : ℝ) + 2) ≤ Real.log (2 ^ k * ((M : ℝ) + 2)) :=
        Real.log_le_log (by positivity) hle
    _ = k * Real.log 2 + Real.log ((M : ℝ) + 2) := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    _ ≤ k * Real.log ((M : ℝ) + 2) + Real.log ((M : ℝ) + 2) := by
        gcongr
    _ = (k + 1) * Real.log ((M : ℝ) + 2) := by ring

/-- **Contração geométrica é incompatível com um piso logarítmico.** -/
theorem sem_contracao_de_piso_log {D : ℕ → ℝ} {c : ℝ} (hc : 0 < c) {N₁ : ℕ}
    (hpiso : ∀ N ≥ N₁, c / Real.log ((N : ℝ) + 2) ≤ D N) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (N₀ : ℕ) : ¬ ∀ N ≥ N₀, D (2 * N) ≤ q * D N := by
  intro hcon
  set M := max (max N₀ N₁) 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMN₀ : N₀ ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hMN₁ : N₁ ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  set L := Real.log ((M : ℝ) + 2) with hLdef
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hL : 0 < L := Real.log_pos (by linarith)
  have key : ∀ k : ℕ, c ≤ ((k : ℝ) + 1) * q ^ k * (L * D M) := by
    intro k
    have hN : N₁ ≤ 2 ^ k * M := le_trans hMN₁ (Nat.le_mul_of_pos_left M (by positivity))
    have h1 := hpiso _ hN
    have h2 := iter_contracao hcon hq0 hMN₀ k
    have h3 := log_pow_mul_le (k := k) hM1
    have hlogpos : 0 < Real.log (((2 ^ k * M : ℕ) : ℝ) + 2) :=
      Real.log_pos (by have : (0 : ℝ) ≤ ((2 ^ k * M : ℕ) : ℝ) := by positivity
                       linarith)
    have h4 : c ≤ D (2 ^ k * M) * Real.log (((2 ^ k * M : ℕ) : ℝ) + 2) := by
      rwa [div_le_iff₀ hlogpos] at h1
    have hD0 : 0 ≤ D (2 ^ k * M) := le_trans (div_nonneg hc.le hlogpos.le) h1
    calc c ≤ D (2 ^ k * M) * Real.log (((2 ^ k * M : ℕ) : ℝ) + 2) := h4
      _ ≤ D (2 ^ k * M) * ((k + 1) * L) := mul_le_mul_of_nonneg_left h3 hD0
      _ ≤ (q ^ k * D M) * ((k + 1) * L) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = ((k : ℝ) + 1) * q ^ k * (L * D M) := by ring
  have hlim : Tendsto (fun k : ℕ => ((k : ℝ) + 1) * q ^ k * (L * D M)) atTop (𝓝 0) := by
    have hq : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
    have a := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hq
    have b := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    have := (a.add b).mul_const (L * D M)
    simpa [add_mul, pow_one] using this
  have := ge_of_tendsto' hlim key
  linarith

/-- O piso de BBLS/Burnol, como hipótese (`liminf D_N log N > 0`). -/
def PisoLog : Prop := ∃ c > 0, ∃ N₁ : ℕ, ∀ N ≥ N₁, c / Real.log ((N : ℝ) + 2) ≤ DN N

/-- **Refutação da contração para `D_N`**: com o piso logarítmico, não existe `q < 1` com
`D_{2N} ≤ q D_N` a partir de algum `N₀`. -/
theorem contracao_impossivel (h : PisoLog) :
    ¬ ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, DN (2 * N) ≤ q * DN N := by
  rintro ⟨q, hq0, hq1, N₀, hc⟩
  obtain ⟨c, hc0, N₁, hp⟩ := h
  exact sem_contracao_de_piso_log hc0 hp hq0 hq1 N₀ hc

/-- **Uma amostra finita não decide o limite**: todo prefixo decrescente com último valor
positivo se estende a uma sequência decrescente com limite `0` e a outra com limite positivo. -/
theorem amostra_finita_nao_decide (d : ℕ → ℝ) (N : ℕ)
    (hd : ∀ m n, m ≤ n → n ≤ N → d n ≤ d m) (hpos : 0 < d N) :
    (∃ f : ℕ → ℝ, Antitone f ∧ (∀ n, 0 ≤ f n) ∧ (∀ n ≤ N, f n = d n) ∧
        Tendsto f atTop (𝓝 0)) ∧
      (∃ g : ℕ → ℝ, Antitone g ∧ (∀ n, 0 ≤ g n) ∧ (∀ n ≤ N, g n = d n) ∧
        Tendsto g atTop (𝓝 (d N))) := by
  have hge : ∀ n ≤ N, d N ≤ d n := fun n hn => hd n N hn le_rfl
  constructor
  · refine ⟨fun n => if n ≤ N then d n else d N / ((n : ℝ) - N + 1), ?_, ?_, ?_, ?_⟩
    · intro m n hmn
      simp only
      by_cases hn : n ≤ N
      · simp only [hn, le_trans hmn hn, ↓reduceIte]; exact hd m n hmn hn
      · simp only [hn, ↓reduceIte]
        have hn' : (N : ℝ) + 1 ≤ n := by exact_mod_cast (show N + 1 ≤ n by omega)
        by_cases hm : m ≤ N
        · simp only [hm, ↓reduceIte]
          calc d N / ((n : ℝ) - N + 1) ≤ d N / 1 :=
                div_le_div_of_nonneg_left hpos.le (by norm_num) (by linarith)
            _ ≤ d m := by rw [div_one]; exact hge m hm
        · simp only [hm, ↓reduceIte]
          have hm' : (N : ℝ) + 1 ≤ m := by exact_mod_cast (show N + 1 ≤ m by omega)
          have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
          exact div_le_div_of_nonneg_left hpos.le (by linarith) (by linarith)
    · intro n
      simp only
      split_ifs with hn
      · exact le_trans hpos.le (hge n hn)
      · have hn' : (N : ℝ) + 1 ≤ n := by exact_mod_cast (show N + 1 ≤ n by omega)
        exact div_nonneg hpos.le (by linarith)
    · intro n hn; simp only [hn, ↓reduceIte]
    · have h1 : Tendsto (fun n : ℕ => (n : ℝ) - N + 1) atTop atTop := by
        have := tendsto_atTop_add_const_right atTop (1 - (N : ℝ)) tendsto_natCast_atTop_atTop
        refine this.congr fun n => ?_
        ring
      have h2 := (tendsto_const_nhds (x := d N)).div_atTop h1
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop N] with n hn
      simp only [not_le.mpr hn, ↓reduceIte]
  · refine ⟨fun n => if n ≤ N then d n else d N, ?_, ?_, ?_, ?_⟩
    · intro m n hmn
      simp only
      by_cases hn : n ≤ N
      · simp only [hn, le_trans hmn hn, ↓reduceIte]; exact hd m n hmn hn
      · simp only [hn, ↓reduceIte]
        split_ifs with hm
        · exact hge m hm
        · exact le_rfl
    · intro n
      simp only
      split_ifs with hn
      · exact le_trans hpos.le (hge n hn)
      · exact hpos.le
    · intro n hn; simp only [hn, ↓reduceIte]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop N] with n hn
      simp only [not_le.mpr hn, ↓reduceIte]

/-! ## Certificados para `D_∞` -/

theorem bdd_DN : BddBelow (Set.range DN) := ⟨0, by rintro _ ⟨n, rfl⟩; exact DN_nonneg n⟩

theorem Dinf_nonneg : 0 ≤ ⨅ N, DN N := le_ciInf DN_nonneg

/-- **Certificado demonstrado**: `D_∞ ∈ [0, 1]`. -/
noncomputable def cert_Dinf : Cert (⨅ N, DN N) True :=
  ⟨⟨0, 1, by norm_num⟩, fun _ => by
    rw [mem_def]; push_cast
    exact ⟨Dinf_nonneg, (ciInf_le bdd_DN 0).trans DN_zero_le_one⟩⟩

theorem cert_Dinf_mem : Mem (⨅ N, DN N) cert_Dinf.I := cert_Dinf.demonstrado

/-- **Certificado condicional**: sob a hipótese numérica `D_256 ≤ 0,00823372` (valor do
cálculo de precisão 45 do repositório, não verificado no kernel), `D_∞ ∈ [0; 0,00823372]`. -/
noncomputable def cert_Dinf_numerico : Cert (⨅ N, DN N) (DN 256 ≤ 823372 / 10 ^ 8) :=
  ⟨⟨0, 823372 / 10 ^ 8, by norm_num⟩, fun h => by
    rw [mem_def]; push_cast
    exact ⟨Dinf_nonneg, (ciInf_le bdd_DN 256).trans h⟩⟩

theorem cert_Dinf_numerico_mem (h : DN 256 ≤ 823372 / 10 ^ 8) :
    Mem (⨅ N, DN N) cert_Dinf_numerico.I := cert_Dinf_numerico.descarga h

/-- **Fechamento de RH na linguagem dos certificados**: existe certificado demonstrado
`D_∞ ∈ [0, 0]` exatamente quando `D_∞ = 0`. -/
theorem fecho_RH_iff :
    (∃ c : Cert (⨅ N, DN N) True, c.I = ponto 0) ↔ ⨅ N, DN N = 0 := by
  constructor
  · rintro ⟨c, hc⟩
    have h := c.demonstrado
    rw [hc, mem_ponto] at h
    simpa using h
  · intro h
    exact ⟨⟨ponto 0, fun _ => by rw [mem_ponto, h]; simp⟩, rfl⟩

/-- E esse certificado implica RH (ponte B1). -/
theorem fecho_RH (h : ∃ c : Cert (⨅ N, DN N) True, c.I = ponto 0) : RiemannHypothesis :=
  riemann_of_iInf_zero (fecho_RH_iff.1 h)

end ATK.ContracaoDN

#print axioms ATK.ContracaoDN.iter_contracao
#print axioms ATK.ContracaoDN.tendsto_zero_de_contracao
#print axioms ATK.ContracaoDN.riemann_de_contracao
#print axioms ATK.ContracaoDN.log_pow_mul_le
#print axioms ATK.ContracaoDN.sem_contracao_de_piso_log
#print axioms ATK.ContracaoDN.contracao_impossivel
#print axioms ATK.ContracaoDN.amostra_finita_nao_decide
#print axioms ATK.ContracaoDN.bdd_DN
#print axioms ATK.ContracaoDN.Dinf_nonneg
#print axioms ATK.ContracaoDN.cert_Dinf_mem
#print axioms ATK.ContracaoDN.cert_Dinf_numerico_mem
#print axioms ATK.ContracaoDN.fecho_RH_iff
#print axioms ATK.ContracaoDN.fecho_RH
