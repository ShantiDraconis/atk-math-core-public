import ATK.CapturaIncondicional
import ATK.DInfinito

/-!
# ATK-RH — As "leis de ganho por passo" propostas para Báez-Duarte, testadas no kernel

Para a captura relativa `η_N = (D_N − D_{N+1}) / D_N` (`ATK.CapturaRH.η`) da sequência genuína
`D_N` (`ATK.Conditional.Riemann.DN`), textos externos propuseram como "produtor material" uma lei
por passo. Aqui as duas formas são decididas no kernel, até onde o kernel alcança:

* `lei_log_suficiente`, `rh_de_lei_log`: **se** `η_N ≥ c / ((N+2) log (N+2))` a partir de algum `N₀`,
  com **qualquer** `c > 0`, então `D_N → 0` e (ponte B1, provada) **RH**. É uma condição suficiente;
  ninguém a provou.
* `sem_lei_polinomial`: sob o piso logarítmico `PisoLog` (Báez-Duarte–Balazard–Landreau–Saias 2000,
  Burnol 2002; literatura, não formalizado aqui), a lei polinomial `η_N ≥ c / (N+1)` é **falsa** para
  todo `c > 0` — ela daria `D_N ≤ C·N^{−c}`.
* `sem_lei_log_forte`: sob `PisoLog`, a lei logarítmica com `c > 1` é **falsa**.

Sobra só a janela `0 < c ≤ 1` na forma logarítmica. Na numérica de `pesquisa/rodada2/RH_Gram.md`
(D_N exato para N ≤ 8000) a lei por passo só se sustenta com `c ≤ 6·10⁻⁸`: os ganhos por passo são
erráticos. A versão acumulada equivalente é a própria O1
(`ATK.CapturaIncondicional.captura_log_iff_incondicional`).

Nada aqui assume RH e nada aqui prova O1. OPEN_MATH continua true.
-/

open Filter Topology Finset
open ATK.Conditional.Riemann ATK.CapturaRH ATK.ContracaoDN

namespace ATK.LeisDeGanho

/-- Lei polinomial por passo: `η_N ≥ c/(N+1)` a partir de `N₀`, com `c > 0`. -/
def LeiPolinomial : Prop := ∃ c > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, c / ((N : ℝ) + 1) ≤ η N

/-- Lei logarítmica por passo com constante `c`: `η_N ≥ c/((N+2) log (N+2))` a partir de `N₀`. -/
def LeiLog (c : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, c / (((N : ℝ) + 2) * Real.log ((N : ℝ) + 2)) ≤ η N

/-! ### Somas de comparação -/

/-- `log(n+2) − log(n+1) ≤ 1/(n+1)`. -/
theorem log_succ_sub_le (n : ℕ) :
    Real.log ((n : ℝ) + 2) - Real.log ((n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  rw [← Real.log_div h2.ne' h1.ne']
  have := Real.log_le_sub_one_of_pos (div_pos h2 h1)
  have e : ((n : ℝ) + 2) / ((n : ℝ) + 1) - 1 = 1 / ((n : ℝ) + 1) := by field_simp; ring
  linarith

/-- Soma harmônica por baixo: `log(N+1) − log(N₀+1) ≤ Σ_{N₀ ≤ j < N} 1/(j+1)`. -/
theorem harm_ge {N₀ N : ℕ} (h : N₀ ≤ N) :
    Real.log ((N : ℝ) + 1) - Real.log ((N₀ : ℝ) + 1) ≤ ∑ j ∈ Ico N₀ N, 1 / ((j : ℝ) + 1) := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [sum_Ico_succ_top hn]
    have := log_succ_sub_le n
    push_cast
    have e : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
    rw [e]
    linarith

/-- `log log(n+3) − log log(n+2) ≤ 1/((n+2) log(n+2))`. -/
theorem loglog_succ_sub_le (n : ℕ) :
    Real.log (Real.log ((n : ℝ) + 3)) - Real.log (Real.log ((n : ℝ) + 2))
      ≤ 1 / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) := by
  have ha : 0 < Real.log ((n : ℝ) + 2) := log_pos_N n
  have hb : 0 < Real.log ((n : ℝ) + 3) :=
    Real.log_pos (by have := n.cast_nonneg (α := ℝ); linarith)
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  rw [← Real.log_div hb.ne' ha.ne']
  have hq := Real.log_le_sub_one_of_pos (div_pos hb ha)
  -- log(n+3) − log(n+2) ≤ 1/(n+2)
  have hd : Real.log ((n : ℝ) + 3) - Real.log ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) := by
    have := log_succ_sub_le (n + 1)
    push_cast at this
    have e1 : (n : ℝ) + 1 + 2 = (n : ℝ) + 3 := by ring
    have e2 : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
    rw [e1, e2] at this
    exact this
  have e : Real.log ((n : ℝ) + 3) / Real.log ((n : ℝ) + 2) - 1
      = (Real.log ((n : ℝ) + 3) - Real.log ((n : ℝ) + 2)) / Real.log ((n : ℝ) + 2) := by
    field_simp
  have hfin : (Real.log ((n : ℝ) + 3) - Real.log ((n : ℝ) + 2)) / Real.log ((n : ℝ) + 2)
      ≤ 1 / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) := by
    rw [div_le_iff₀ ha]
    calc Real.log ((n : ℝ) + 3) - Real.log ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) := hd
      _ = 1 / (((n : ℝ) + 2) * Real.log ((n : ℝ) + 2)) * Real.log ((n : ℝ) + 2) := by
        field_simp
  linarith

/-- `log log(N+2) − log log(N₀+2) ≤ Σ_{N₀ ≤ j < N} 1/((j+2) log(j+2))`. -/
theorem loglog_ge {N₀ N : ℕ} (h : N₀ ≤ N) :
    Real.log (Real.log ((N : ℝ) + 2)) - Real.log (Real.log ((N₀ : ℝ) + 2))
      ≤ ∑ j ∈ Ico N₀ N, 1 / (((j : ℝ) + 2) * Real.log ((j : ℝ) + 2)) := by
  induction N, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [sum_Ico_succ_top hn]
    have := loglog_succ_sub_le n
    push_cast
    have e : (n : ℝ) + 1 + 2 = (n : ℝ) + 3 := by ring
    rw [e]
    linarith

/-! ### Fatos sobre η -/

theorem sum_Ico_le_range (N₀ N : ℕ) : ∑ j ∈ Ico N₀ N, η j ≤ ∑ j ∈ range N, η j := by
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => η_nonneg j)
  intro x hx
  simp only [mem_Ico] at hx
  simp only [mem_range]
  omega

/-- `η ≤ −log(1 − η)` (incondicional, pois `η < 1`). -/
theorem η_le_neg_log (j : ℕ) : η j ≤ -Real.log (1 - η j) := by
  have h := ATK.CapturaIncondicional.η_lt_one j
  have := Real.log_le_sub_one_of_pos (show 0 < 1 - η j by linarith)
  linarith

/-- Sob `PisoLog`, a captura linear acumulada cresce no máximo como `log log N`. -/
theorem soma_eta_le_loglog (hP : PisoLog) : ∃ C : ℝ, ∃ N₁ : ℕ, ∀ N ≥ N₁,
    ∑ j ∈ range N, η j ≤ Real.log (Real.log ((N : ℝ) + 2)) + C := by
  obtain ⟨C, N₁, h⟩ := captura_teto hP
  exact ⟨C, N₁, fun N hN => (sum_le_sum fun j _ => η_le_neg_log j).trans (h N hN)⟩

/-- Para todo `B` existe `N ≥ M` com `B < log (N+1)`. -/
theorem existe_log_grande (B : ℝ) (M : ℕ) : ∃ N ≥ M, B < Real.log ((N : ℝ) + 1) := by
  refine ⟨max M ⌈Real.exp B⌉₊, le_max_left _ _, ?_⟩
  have h1 : Real.exp B ≤ ((max M ⌈Real.exp B⌉₊ : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  have h2 : Real.exp B < ((max M ⌈Real.exp B⌉₊ : ℕ) : ℝ) + 1 := by linarith
  have := Real.log_lt_log (Real.exp_pos B) h2
  rwa [Real.log_exp] at this

/-- Para todo `B` existe `N ≥ M` com `B < log log (N+2)`. -/
theorem existe_loglog_grande (B : ℝ) (M : ℕ) : ∃ N ≥ M, B < Real.log (Real.log ((N : ℝ) + 2)) := by
  obtain ⟨N, hN, h⟩ := existe_log_grande (Real.exp B) M
  refine ⟨N, hN, ?_⟩
  have h3 : Real.log ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have := Real.log_lt_log (Real.exp_pos B) (h.trans_le h3)
  rwa [Real.log_exp] at this

/-! ### Os três resultados -/

/-- **Suficiência**: a lei logarítmica por passo, com qualquer `c > 0`, força `D_N → 0`. -/
theorem lei_log_suficiente {c : ℝ} (hc : 0 < c) (hL : LeiLog c) : Tendsto DN atTop (𝓝 0) := by
  obtain ⟨N₀, hN₀⟩ := hL
  rw [ATK.DInfinito.dInf_eq_zero_iff]
  refine le_antisymm ?_ ATK.DInfinito.dInf_nonneg
  by_contra hpos'
  have hpos : 0 < ATK.DInfinito.dInf := not_le.mp hpos'
  set d := ATK.DInfinito.dInf with hd
  have hD0 := ATK.RelacionalDN.DN_pos 0
  -- escolhe N com log log (N+2) grande
  set B := Real.log (Real.log ((N₀ : ℝ) + 2)) + (Real.log (DN 0) - Real.log (d / 2)) / c
  obtain ⟨N, hN, hB⟩ := existe_loglog_grande B N₀
  -- Σ_{j<N} η_j ≥ c (log log (N+2) − log log (N₀+2))
  have hsum : c * (Real.log (Real.log ((N : ℝ) + 2)) - Real.log (Real.log ((N₀ : ℝ) + 2)))
      ≤ ∑ j ∈ range N, η j := by
    calc c * (Real.log (Real.log ((N : ℝ) + 2)) - Real.log (Real.log ((N₀ : ℝ) + 2)))
        ≤ c * ∑ j ∈ Ico N₀ N, 1 / (((j : ℝ) + 2) * Real.log ((j : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left (loglog_ge hN) hc.le
      _ = ∑ j ∈ Ico N₀ N, c / (((j : ℝ) + 2) * Real.log ((j : ℝ) + 2)) := by
          rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
      _ ≤ ∑ j ∈ Ico N₀ N, η j := sum_le_sum fun j hj => hN₀ j (mem_Ico.mp hj).1
      _ ≤ ∑ j ∈ range N, η j := sum_Ico_le_range N₀ N
  have hexp : -∑ j ∈ range N, η j < Real.log (d / 2) - Real.log (DN 0) := by
    have : c * (B - Real.log (Real.log ((N₀ : ℝ) + 2))) = Real.log (DN 0) - Real.log (d / 2) := by
      simp only [B]; field_simp; ring
    nlinarith
  have hDN : DN N < d / 2 := by
    calc DN N ≤ DN 0 * Real.exp (-∑ j ∈ range N, η j) := le_exp N
      _ < DN 0 * Real.exp (Real.log (d / 2) - Real.log (DN 0)) :=
          mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hexp) hD0
      _ = d / 2 := by
          rw [Real.exp_sub, Real.exp_log (by linarith), Real.exp_log hD0]
          field_simp
  have hle : d ≤ DN N := ciInf_le bdd_DN N
  linarith

/-- RH a partir da lei logarítmica por passo (com qualquer `c > 0`) — produtor suficiente, não provado. -/
theorem rh_de_lei_log {c : ℝ} (hc : 0 < c) (hL : LeiLog c) : RiemannHypothesis :=
  ATK.BaezDuarteBridge.baezDuarteCriterion (lei_log_suficiente hc hL)

/-- **Refutação**: sob o piso logarítmico, a lei polinomial por passo é falsa. -/
theorem sem_lei_polinomial (hP : PisoLog) : ¬ LeiPolinomial := by
  rintro ⟨c, hc, N₀, hN₀⟩
  obtain ⟨C, N₁, hN₁⟩ := soma_eta_le_loglog hP
  set K := c * Real.log ((N₀ : ℝ) + 1) + c / 2 * Real.log 2 - 1 - Real.log (c / 2) + C
  obtain ⟨N, hN, hB⟩ := existe_log_grande (2 * K / c) (max N₀ N₁)
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN1 : N₁ ≤ N := (le_max_right _ _).trans hN
  have hlow : c * (Real.log ((N : ℝ) + 1) - Real.log ((N₀ : ℝ) + 1)) ≤ ∑ j ∈ range N, η j := by
    calc c * (Real.log ((N : ℝ) + 1) - Real.log ((N₀ : ℝ) + 1))
        ≤ c * ∑ j ∈ Ico N₀ N, 1 / ((j : ℝ) + 1) := mul_le_mul_of_nonneg_left (harm_ge hN0) hc.le
      _ = ∑ j ∈ Ico N₀ N, c / ((j : ℝ) + 1) := by
          rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
      _ ≤ ∑ j ∈ Ico N₀ N, η j := sum_le_sum fun j hj => hN₀ j (mem_Ico.mp hj).1
      _ ≤ ∑ j ∈ range N, η j := sum_Ico_le_range N₀ N
  have hup := hN₁ N hN1
  -- log L ≤ (c/2) L − 1 − log(c/2), com L = log(N+2) > 0
  set L := Real.log ((N : ℝ) + 2)
  have hL : 0 < L := log_pos_N N
  have hc2 : 0 < c / 2 := by linarith
  have hlogL : Real.log L ≤ c / 2 * L - 1 - Real.log (c / 2) := by
    have := Real.log_le_sub_one_of_pos (mul_pos hc2 hL)
    rw [Real.log_mul hc2.ne' hL.ne'] at this
    linarith
  -- L ≤ log 2 + log(N+1)
  have hL2 : L ≤ Real.log 2 + Real.log ((N : ℝ) + 1) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hfin : c / 2 * Real.log ((N : ℝ) + 1) ≤ K := by
    simp only [K]; nlinarith
  have : c / 2 * (2 * K / c) < c / 2 * Real.log ((N : ℝ) + 1) :=
    mul_lt_mul_of_pos_left hB hc2
  have e : c / 2 * (2 * K / c) = K := by field_simp
  linarith

/-- **Refutação**: sob o piso logarítmico, a lei logarítmica por passo com `c > 1` é falsa. -/
theorem sem_lei_log_forte (hP : PisoLog) {c : ℝ} (hc : 1 < c) : ¬ LeiLog c := by
  rintro ⟨N₀, hN₀⟩
  obtain ⟨C, N₁, hN₁⟩ := soma_eta_le_loglog hP
  set K := C + c * Real.log (Real.log ((N₀ : ℝ) + 2))
  obtain ⟨N, hN, hB⟩ := existe_loglog_grande (K / (c - 1)) (max N₀ N₁)
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN1 : N₁ ≤ N := (le_max_right _ _).trans hN
  have hc0 : 0 < c := by linarith
  have hlow : c * (Real.log (Real.log ((N : ℝ) + 2)) - Real.log (Real.log ((N₀ : ℝ) + 2)))
      ≤ ∑ j ∈ range N, η j := by
    calc c * (Real.log (Real.log ((N : ℝ) + 2)) - Real.log (Real.log ((N₀ : ℝ) + 2)))
        ≤ c * ∑ j ∈ Ico N₀ N, 1 / (((j : ℝ) + 2) * Real.log ((j : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left (loglog_ge hN0) hc0.le
      _ = ∑ j ∈ Ico N₀ N, c / (((j : ℝ) + 2) * Real.log ((j : ℝ) + 2)) := by
          rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
      _ ≤ ∑ j ∈ Ico N₀ N, η j := sum_le_sum fun j hj => hN₀ j (mem_Ico.mp hj).1
      _ ≤ ∑ j ∈ range N, η j := sum_Ico_le_range N₀ N
  have hup := hN₁ N hN1
  have hc1 : 0 < c - 1 := by linarith
  have : (c - 1) * (K / (c - 1)) < (c - 1) * Real.log (Real.log ((N : ℝ) + 2)) :=
    mul_lt_mul_of_pos_left hB hc1
  have e : (c - 1) * (K / (c - 1)) = K := by field_simp
  simp only [K] at e this
  nlinarith

end ATK.LeisDeGanho

#print axioms ATK.LeisDeGanho.harm_ge
#print axioms ATK.LeisDeGanho.loglog_ge
#print axioms ATK.LeisDeGanho.soma_eta_le_loglog
#print axioms ATK.LeisDeGanho.lei_log_suficiente
#print axioms ATK.LeisDeGanho.rh_de_lei_log
#print axioms ATK.LeisDeGanho.sem_lei_polinomial
#print axioms ATK.LeisDeGanho.sem_lei_log_forte
