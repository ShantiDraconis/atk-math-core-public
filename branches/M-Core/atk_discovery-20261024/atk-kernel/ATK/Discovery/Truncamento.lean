import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# ATK-Discovery — Truncamento decimal e cauda

Para `x : ℝ` e uma precisão `N : ℕ`:

* parte preservada `P_N(x) = ⌊10ᴺ x⌋ / 10ᴺ` e cauda `T_N(x) = x − P_N(x)`;
* **reconstrução exata** `x = P_N(x) + T_N(x)` (`reconstrucao`) e `0 ≤ T_N(x) < 10⁻ᴺ`
  (`cauda_nonneg`, `cauda_lt`);
* o zero observado pode esconder um valor positivo: `P_N(1/(2·10ᴺ)) = 0` e a cauda é positiva
  (`zero_observado_esconde`); a projeção não é injetiva (`projecao_nao_injetiva`);
* **critério exato de comparação** `a < b ⟺ P_N(a) − P_N(b) < T_N(b) − T_N(a)` (`lt_iff_cauda`); com
  partes preservadas iguais, a ordem é a ordem das caudas (`lt_iff_cauda_de_P_eq`);
* contagens naturais não têm cauda: `T_N(n) = 0` (`natural_sem_cauda`);
* `P_N(x)` cresce com `N` e converge para `x` (`P_mono`, `tendsto_P`, `tendsto_cauda`);
* a observação zero sozinha não prova convergência (`projecao_zero_nao_basta`), nem a cauda que some
  (`cauda_some_valor_nao`); com as **duas** componentes indo a zero, o valor vai a zero
  (`fechamento_duas_componentes`).

Matemática elementar; nada aqui toca uma conjectura.
-/

namespace ATK.Discovery.Truncamento

open Filter Topology

/-- Parte preservada na precisão `N`: `P_N(x) = ⌊10ᴺ x⌋ / 10ᴺ`. -/
noncomputable def P (N : ℕ) (x : ℝ) : ℝ := (⌊(10 : ℝ) ^ N * x⌋ : ℝ) / (10 : ℝ) ^ N

/-- Cauda descartada na precisão `N`: `T_N(x) = x − P_N(x)`. -/
noncomputable def T (N : ℕ) (x : ℝ) : ℝ := x - P N x

theorem dez_pow_pos (N : ℕ) : (0 : ℝ) < (10 : ℝ) ^ N := by positivity

/-- **Reconstrução exata**: `x = P_N(x) + T_N(x)`. -/
theorem reconstrucao (N : ℕ) (x : ℝ) : x = P N x + T N x := by
  unfold T; ring

theorem P_le (N : ℕ) (x : ℝ) : P N x ≤ x := by
  unfold P
  rw [div_le_iff₀ (dez_pow_pos N), mul_comm]
  exact Int.floor_le _

/-- A cauda é não negativa. -/
theorem cauda_nonneg (N : ℕ) (x : ℝ) : 0 ≤ T N x := by
  unfold T; linarith [P_le N x]

/-- A cauda é menor que `10⁻ᴺ`. -/
theorem cauda_lt (N : ℕ) (x : ℝ) : T N x < 1 / (10 : ℝ) ^ N := by
  have h10 := dez_pow_pos N
  have hfl := Int.lt_floor_add_one ((10 : ℝ) ^ N * x)
  unfold T P
  rw [sub_lt_iff_lt_add, ← add_div, lt_div_iff₀ h10]
  linarith

/-- O zero observado pode esconder um valor positivo, em qualquer precisão. -/
theorem zero_observado_esconde (N : ℕ) :
    P N (1 / (2 * (10 : ℝ) ^ N)) = 0 ∧ 0 < T N (1 / (2 * (10 : ℝ) ^ N)) := by
  have h10 := dez_pow_pos N
  have hx : (10 : ℝ) ^ N * (1 / (2 * (10 : ℝ) ^ N)) = 1 / 2 := by
    field_simp
  have hP : P N (1 / (2 * (10 : ℝ) ^ N)) = 0 := by
    unfold P
    rw [hx, Int.floor_eq_zero_iff.mpr (by norm_num)]
    simp
  refine ⟨hP, ?_⟩
  unfold T
  rw [hP, sub_zero]
  positivity

/-- A projeção não é injetiva: valores distintos e ordenados com a mesma parte preservada. -/
theorem projecao_nao_injetiva (N : ℕ) :
    let a := 1 / (4 * (10 : ℝ) ^ N)
    let b := 1 / (2 * (10 : ℝ) ^ N)
    P N a = P N b ∧ a < b := by
  intro a b
  have h10 := dez_pow_pos N
  have ha : (10 : ℝ) ^ N * a = 1 / 4 := by simp only [a]; field_simp
  have hb : (10 : ℝ) ^ N * b = 1 / 2 := by simp only [b]; field_simp
  refine ⟨?_, ?_⟩
  · unfold P
    rw [ha, hb, Int.floor_eq_zero_iff.mpr (by norm_num), Int.floor_eq_zero_iff.mpr (by norm_num)]
  · simp only [a, b]
    apply one_div_lt_one_div_of_lt (by positivity)
    linarith

/-- **Critério exato de comparação**: `a < b ⟺ P_N(a) − P_N(b) < T_N(b) − T_N(a)`. -/
theorem lt_iff_cauda (N : ℕ) (a b : ℝ) : a < b ↔ P N a - P N b < T N b - T N a := by
  have ha := reconstrucao N a
  have hb := reconstrucao N b
  constructor <;> intro h <;> linarith

/-- Com partes preservadas iguais, a ordem dos valores é a ordem das caudas. -/
theorem lt_iff_cauda_de_P_eq {N : ℕ} {a b : ℝ} (h : P N a = P N b) : a < b ↔ T N a < T N b := by
  rw [lt_iff_cauda, h, sub_self]
  constructor <;> intro h' <;> linarith

/-- Contagens naturais não têm cauda: `P_N(n) = n` e `T_N(n) = 0`. -/
theorem natural_sem_cauda (N n : ℕ) : P N (n : ℝ) = n ∧ T N (n : ℝ) = 0 := by
  have h10 := dez_pow_pos N
  have hP : P N (n : ℝ) = n := by
    unfold P
    have : (10 : ℝ) ^ N * (n : ℝ) = ((10 ^ N * n : ℕ) : ℝ) := by push_cast; ring
    rw [this, Int.floor_natCast]
    push_cast
    field_simp
  exact ⟨hP, by unfold T; rw [hP, sub_self]⟩

/-- Para o par `combustível = 1`, `tamanho = 1`: em toda precisão as partes e as caudas coincidem,
e `1 < 1` continua falso. Nenhuma cauda escondida existe em contagens exatas. -/
theorem p01_sem_cauda (N : ℕ) :
    P N 1 = P N 1 ∧ T N (1 : ℝ) = 0 ∧ ¬ ((1 : ℝ) < 1) := by
  have := natural_sem_cauda N 1
  push_cast at this
  exact ⟨rfl, this.2, lt_irrefl 1⟩

/-- A parte preservada cresce com a precisão. -/
theorem P_mono (N : ℕ) (x : ℝ) : P N x ≤ P (N + 1) x := by
  have h10 := dez_pow_pos N
  unfold P
  rw [div_le_div_iff₀ h10 (dez_pow_pos (N + 1)), pow_succ]
  have hfl : (10 : ℤ) * ⌊(10 : ℝ) ^ N * x⌋ ≤ ⌊(10 : ℝ) ^ N * 10 * x⌋ := by
    apply Int.le_floor.mpr
    push_cast
    have := Int.floor_le ((10 : ℝ) ^ N * x)
    nlinarith
  have hfl' : (10 : ℝ) * (⌊(10 : ℝ) ^ N * x⌋ : ℝ) ≤ (⌊(10 : ℝ) ^ N * 10 * x⌋ : ℝ) := by
    exact_mod_cast hfl
  nlinarith

/-- A cauda tende a zero quando a precisão cresce. -/
theorem tendsto_cauda (x : ℝ) : Tendsto (fun N => T N x) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => 1 / (10 : ℝ) ^ N) atTop (𝓝 0) := by
    have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 10 : ℝ)) (by norm_num) (by norm_num)
    simpa [one_div, inv_pow] using this
  exact squeeze_zero (fun N => cauda_nonneg N x) (fun N => (cauda_lt N x).le) hlim

/-- O truncamento converge para o valor: `P_N(x) → x`. -/
theorem tendsto_P (x : ℝ) : Tendsto (fun N => P N x) atTop (𝓝 x) := by
  have h := (tendsto_const_nhds (x := x)).sub (tendsto_cauda x)
  rw [sub_zero] at h
  refine h.congr fun N => ?_
  unfold T; ring

/-- A observação zero, sozinha, não prova convergência: `d_n = 1/2` tem `P₀(d_n) = 0` para todo `n`
e não tende a zero. -/
theorem projecao_zero_nao_basta :
    (∀ _n : ℕ, P 0 (1 / 2 : ℝ) = 0) ∧ ¬ Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 0) := by
  refine ⟨fun _ => ?_, fun h => ?_⟩
  · unfold P
    rw [pow_zero, one_mul, Int.floor_eq_zero_iff.mpr (by norm_num)]
    simp
  · have := tendsto_nhds_unique h tendsto_const_nhds
    norm_num at this

/-- A cauda que some não basta: `T_N(1/2) = 0` para todo `N ≥ 1`, e `1/2 ≠ 0`. -/
theorem cauda_some_valor_nao (N : ℕ) (hN : 1 ≤ N) : T N (1 / 2 : ℝ) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  have hint : (10 : ℝ) ^ (k + 1) * (1 / 2) = ((5 * 10 ^ k : ℕ) : ℝ) := by
    push_cast; rw [pow_succ]; ring
  unfold T P
  rw [hint, Int.floor_natCast]
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-- **Fechamento por duas componentes**: se `D_n = P_n + T_n` com `P_n → 0` e `T_n → 0`, então
`D_n → 0`. -/
theorem fechamento_duas_componentes {D Pn Tn : ℕ → ℝ} (hdec : ∀ n, D n = Pn n + Tn n)
    (hP : Tendsto Pn atTop (𝓝 0)) (hT : Tendsto Tn atTop (𝓝 0)) : Tendsto D atTop (𝓝 0) := by
  have := hP.add hT
  rw [add_zero] at this
  exact this.congr fun n => (hdec n).symm

end ATK.Discovery.Truncamento

#print axioms ATK.Discovery.Truncamento.reconstrucao
#print axioms ATK.Discovery.Truncamento.cauda_nonneg
#print axioms ATK.Discovery.Truncamento.cauda_lt
#print axioms ATK.Discovery.Truncamento.zero_observado_esconde
#print axioms ATK.Discovery.Truncamento.projecao_nao_injetiva
#print axioms ATK.Discovery.Truncamento.lt_iff_cauda
#print axioms ATK.Discovery.Truncamento.lt_iff_cauda_de_P_eq
#print axioms ATK.Discovery.Truncamento.natural_sem_cauda
#print axioms ATK.Discovery.Truncamento.p01_sem_cauda
#print axioms ATK.Discovery.Truncamento.P_mono
#print axioms ATK.Discovery.Truncamento.tendsto_cauda
#print axioms ATK.Discovery.Truncamento.tendsto_P
#print axioms ATK.Discovery.Truncamento.projecao_zero_nao_basta
#print axioms ATK.Discovery.Truncamento.cauda_some_valor_nao
#print axioms ATK.Discovery.Truncamento.fechamento_duas_componentes
