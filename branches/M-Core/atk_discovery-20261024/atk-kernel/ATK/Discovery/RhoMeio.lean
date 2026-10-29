import Mathlib

/-!
# ATK-Discovery — O primeiro aproximante de Nyman–Beurling: `E₁ = 1 − log 2`, no kernel

No espaço `L²(0,1)` do critério de Nyman–Beurling, com `ρ_θ(x) = {θ/x} − θ{1/x}` (`rhoNB`), o alvo é
a constante `1`. Para `θ = 1/2` (`rhoMeio`):

* **degraus** (`rhoMeio_degrau`): em `(1/(n+2), 1/(n+1)]`, `ρ_{1/2} = ((n+1) mod 2)/2` — vale `1/2`
  quando `⌊1/x⌋` é ímpar e `0` quando é par;
* `ρ_{1/2}² = ρ_{1/2}/2` em `(0,1]` (`rhoMeio_sq`);
* soma das faixas: `Σ_{n<2K} cₙ (1/(n+1) − 1/(n+2)) = (H_{2K} − H_K)/2` (`soma_faixas`), e
  `H_{2K} − H_K → log 2` (`tendsto_harmonic_dobro`);
* **as integrais** (`integral_rhoMeio`, `integral_rhoMeio_sq`):
  `b = ∫₀¹ ρ_{1/2} = (log 2)/2`, `G = ∫₀¹ ρ_{1/2}² = (log 2)/4`;
* **o erro** (`erro_eq`): `E(c) = ∫₀¹ (1 − c ρ_{1/2})² = 1 − c log 2 + c² (log 2)/4`;
* **o mínimo** (`erro_minimo`, `erro_em_dois`, `erro_minimo_iff`, `iInf_erro`): `E(c) ≥ 1 − log 2` para
  todo `c`, com igualdade **só** em `c = 2`; logo `inf_c E(c) = 1 − log 2` e o aproximante ótimo é
  `f₁ = 2ρ_{1/2}`;
* `0 < 1 − log 2` (`erro_um_pos`): este aproximante não chega a zero.

Isto é um cálculo incondicional de **um** aproximante. A densidade (erro → 0 numa família inteira),
que equivale a RH, continua aberta.
-/

namespace ATK.Discovery.RhoMeio

open MeasureTheory Set Filter Topology intervalIntegral

/-- A função de Nyman–Beurling `ρ_θ(x) = {θ/x} − θ{1/x}`. -/
noncomputable def rhoNB (θ x : ℝ) : ℝ := Int.fract (θ / x) - θ * Int.fract (1 / x)

/-- `ρ_{1/2}`. -/
noncomputable def rhoMeio (x : ℝ) : ℝ := rhoNB (1 / 2) x

/-- O valor de `ρ_{1/2}` na faixa `n`. -/
noncomputable def c (n : ℕ) : ℝ := (((n + 1) % 2 : ℕ) : ℝ) / 2

theorem measurable_rhoMeio : Measurable rhoMeio := by
  unfold rhoMeio rhoNB
  exact (measurable_fract.comp (by fun_prop)).sub
    (measurable_const.mul (measurable_fract.comp (by fun_prop)))

theorem abs_rhoMeio_le (x : ℝ) : |rhoMeio x| ≤ 1 := by
  unfold rhoMeio rhoNB
  have h1 := Int.fract_nonneg ((1 / 2 : ℝ) / x)
  have h2 := Int.fract_lt_one ((1 / 2 : ℝ) / x)
  have h3 := Int.fract_nonneg (1 / x)
  have h4 := Int.fract_lt_one (1 / x)
  rw [abs_le]; constructor <;> linarith

/-- **Degraus**: em `(1/(n+2), 1/(n+1)]`, `ρ_{1/2} = ((n+1) mod 2)/2`. -/
theorem rhoMeio_degrau (n : ℕ) {x : ℝ} (hx : x ∈ Ioc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1))) :
    rhoMeio x = c n := by
  obtain ⟨h1, h2⟩ := hx
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hx0 : 0 < x := lt_trans (by positivity) h1
  have hy1 : (n : ℝ) + 1 ≤ 1 / x := by
    rw [le_div_iff₀ hx0]; rw [le_div_iff₀ hn1] at h2; linarith
  have hy2 : 1 / x < (n : ℝ) + 2 := by
    rw [div_lt_iff₀ hx0]; rw [div_lt_iff₀ hn2] at h1; linarith
  set m := (n + 1) / 2 with hm
  set r := (n + 1) % 2 with hr
  have hnr : ((n : ℝ) + 1) = 2 * (m : ℝ) + r := by
    have := Nat.div_add_mod (n + 1) 2
    rw [← hm, ← hr] at this
    have h' : (((n + 1 : ℕ)) : ℝ) = ((2 * m + r : ℕ) : ℝ) := by rw [this]
    push_cast at h'; linarith
  have hr1 : (r : ℝ) ≤ 1 := by
    have : r < 2 := Nat.mod_lt _ (by norm_num)
    exact_mod_cast Nat.lt_succ_iff.mp this
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hf1 : Int.fract (1 / x) = 1 / x - ((n : ℝ) + 1) := by
    rw [Int.fract_eq_iff]
    refine ⟨by linarith, by linarith, (n + 1 : ℤ), by push_cast; ring⟩
  have hf2 : Int.fract ((1 / 2 : ℝ) / x) = (1 / 2 : ℝ) / x - (m : ℝ) := by
    rw [Int.fract_eq_iff]
    have e : (1 / 2 : ℝ) / x = (1 / x) / 2 := by ring
    refine ⟨by rw [e]; linarith, by rw [e]; linarith, (m : ℤ), by push_cast; ring⟩
  unfold rhoMeio rhoNB c
  rw [hf1, hf2]
  have e : (1 / 2 : ℝ) / x = (1 / x) / 2 := by ring
  rw [e]
  rw [← hr]
  linarith

theorem c_sq (n : ℕ) : c n ^ 2 = c n / 2 := by
  unfold c
  rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h <;> rw [h] <;> norm_num

/-- `ρ_{1/2}² = ρ_{1/2}/2` em `(0,1]`. -/
theorem rhoMeio_sq {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) : rhoMeio x ^ 2 = rhoMeio x / 2 := by
  obtain ⟨hx0, hx1⟩ := hx
  have hy : 1 ≤ 1 / x := by rw [le_div_iff₀ hx0]; linarith
  set k := ⌊1 / x⌋₊ with hk
  have hk1 : 1 ≤ k := Nat.le_floor (by exact_mod_cast hy)
  obtain ⟨n, hn⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hfl1 : (k : ℝ) ≤ 1 / x := Nat.floor_le (by positivity)
  have hfl2 : 1 / x < (k : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmem : x ∈ Ioc (1 / ((n : ℝ) + 2)) (1 / ((n : ℝ) + 1)) := by
    rw [hn] at hfl1 hfl2; push_cast at hfl1 hfl2
    constructor
    · rw [div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ hx0] at hfl2; linarith
    · rw [le_div_iff₀ (by positivity)]; rw [le_div_iff₀ hx0] at hfl1; linarith
  rw [rhoMeio_degrau n hmem, c_sq]

theorem integrableOn_rhoMeio (s : Set ℝ) (hs : volume s ≠ ⊤) : IntegrableOn rhoMeio s := by
  refine Measure.integrableOn_of_bounded (M := 1) hs measurable_rhoMeio.aestronglyMeasurable ?_
  exact Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_rhoMeio_le x

theorem intervalIntegrable_rhoMeio (a b : ℝ) : IntervalIntegrable rhoMeio volume a b := by
  rw [intervalIntegrable_iff]
  exact integrableOn_rhoMeio _ (by rw [Real.volume_uIoc]; exact ENNReal.ofReal_ne_top)

/-- A integral numa faixa: `cₙ (1/(n+1) − 1/(n+2))`. -/
theorem integral_faixa (n : ℕ) :
    ∫ x in (1 / ((n : ℝ) + 2))..(1 / ((n : ℝ) + 1)), rhoMeio x =
      c n * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hab : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) := one_div_le_one_div_of_le hn1 (by linarith)
  rw [intervalIntegral.integral_of_le hab,
    setIntegral_congr_fun measurableSet_Ioc (fun x hx => rhoMeio_degrau n hx),
    ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Somas parciais: `∫_{1/(M+1)}^1 ρ_{1/2} = Σ_{n<M} cₙ (1/(n+1) − 1/(n+2))`. -/
theorem integral_parcial (M : ℕ) :
    ∫ x in (1 / ((M : ℝ) + 1))..1, rhoMeio x =
      ∑ n ∈ Finset.range M, c n * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have e1 : (1 : ℝ) / (((M + 1 : ℕ) : ℝ) + 1) = 1 / ((M : ℝ) + 2) := by push_cast; ring
    rw [e1, ← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_rhoMeio _ _)
      (intervalIntegrable_rhoMeio _ _), ih, integral_faixa M, Finset.sum_range_succ]
    ring

/-- Soma das faixas até `2K`: `(H_{2K} − H_K)/2`. -/
theorem soma_faixas (K : ℕ) :
    ∑ n ∈ Finset.range (2 * K), c n * (1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) =
      ((harmonic (2 * K) : ℝ) - harmonic K) / 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    have e : 2 * (K + 1) = 2 * K + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, ← e, ih]
    have c1 : c (2 * K) = 1 / 2 := by
      unfold c; rw [show (2 * K + 1) % 2 = 1 by omega]; norm_num
    have c2 : c (2 * K + 1) = 0 := by
      unfold c; rw [show (2 * K + 1 + 1) % 2 = 0 by omega]; norm_num
    rw [c1, c2, e, harmonic_succ, harmonic_succ, harmonic_succ]
    push_cast
    have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
    field_simp
    ring

/-- `H_{2K} − H_K → log 2`. -/
theorem tendsto_harmonic_dobro :
    Tendsto (fun K : ℕ => (harmonic (2 * K) : ℝ) - harmonic K) atTop (𝓝 (Real.log 2)) := by
  have h2K : Tendsto (fun K : ℕ => 2 * K) atTop atTop :=
    tendsto_atTop_mono (fun K => Nat.le_mul_of_pos_left K two_pos) tendsto_id
  have hA := Real.tendsto_harmonic_sub_log.comp h2K
  have hB := Real.tendsto_harmonic_sub_log
  have hlim := (hA.sub hB).add_const (Real.log 2)
  rw [sub_self, zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  simp only [Function.comp]
  push_cast
  rw [Real.log_mul (by norm_num) hK0.ne']
  ring

/-- **`b = ∫₀¹ ρ_{1/2} = (log 2)/2`.** -/
theorem integral_rhoMeio : ∫ x in Ioc (0 : ℝ) 1, rhoMeio x = Real.log 2 / 2 := by
  let s : ℕ → Set ℝ := fun M => Ioc (1 / ((M : ℝ) + 1)) 1
  have hmono : Monotone s := by
    intro M M' h
    have hM : (M : ℝ) ≤ M' := by exact_mod_cast h
    exact Set.Ioc_subset_Ioc_left (one_div_le_one_div_of_le (by positivity) (by linarith))
  have hU : (⋃ M, s M) = Ioc 0 1 := by
    ext x
    simp only [s, Set.mem_iUnion, Set.mem_Ioc]
    constructor
    · rintro ⟨M, h1, h2⟩
      exact ⟨lt_trans (by positivity) h1, h2⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨M, hM⟩ := exists_nat_one_div_lt h1
      exact ⟨M, hM, h2⟩
  have hlim := tendsto_setIntegral_of_monotone (μ := volume) (f := rhoMeio)
    (fun M => measurableSet_Ioc) hmono
    (by rw [hU]; exact integrableOn_rhoMeio _ (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
  rw [hU] at hlim
  have h2K : Tendsto (fun K : ℕ => 2 * K) atTop atTop :=
    tendsto_atTop_mono (fun K => Nat.le_mul_of_pos_left K two_pos) tendsto_id
  have hsub := hlim.comp h2K
  have hval : Tendsto (fun K : ℕ => ∫ x in s (2 * K), rhoMeio x) atTop (𝓝 (Real.log 2 / 2)) := by
    have := tendsto_harmonic_dobro.div_const 2
    refine this.congr fun K => ?_
    have hM1 : (0 : ℝ) < ((2 * K : ℕ) : ℝ) + 1 := by positivity
    have hb1 : 1 / (((2 * K : ℕ) : ℝ) + 1) ≤ 1 := by
      have := (Nat.cast_nonneg (2 * K) : (0 : ℝ) ≤ ((2 * K : ℕ) : ℝ))
      rw [div_le_one hM1]; linarith
    simp only [s]
    rw [← intervalIntegral.integral_of_le hb1, integral_parcial, soma_faixas]
  exact tendsto_nhds_unique hsub hval

/-- **`G = ∫₀¹ ρ_{1/2}² = (log 2)/4`.** -/
theorem integral_rhoMeio_sq : ∫ x in Ioc (0 : ℝ) 1, rhoMeio x ^ 2 = Real.log 2 / 4 := by
  rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx => rhoMeio_sq hx), MeasureTheory.integral_div,
    integral_rhoMeio]
  ring

/-- O erro do aproximante `c·ρ_{1/2}` em `L²(0,1)`. -/
noncomputable def erro (a : ℝ) : ℝ := ∫ x in Ioc (0 : ℝ) 1, (1 - a * rhoMeio x) ^ 2

/-- **`E(c) = 1 − c log 2 + c² (log 2)/4`.** -/
theorem erro_eq (a : ℝ) : erro a = 1 - a * Real.log 2 + a ^ 2 * (Real.log 2 / 4) := by
  have hfin : volume (Ioc (0 : ℝ) 1) ≠ ⊤ := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hi1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 1) := integrableOn_const hfin
  have hiρ : IntegrableOn rhoMeio (Ioc 0 1) := integrableOn_rhoMeio _ hfin
  have hiρ2 : IntegrableOn (fun x => rhoMeio x ^ 2) (Ioc 0 1) := by
    refine Measure.integrableOn_of_bounded (M := 1) hfin
      (measurable_rhoMeio.pow_const 2).aestronglyMeasurable ?_
    refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_pow]
    have := abs_rhoMeio_le x
    have h0 := abs_nonneg (rhoMeio x)
    nlinarith
  have hexp : ∀ x, (1 - a * rhoMeio x) ^ 2 = 1 - (2 * a) * rhoMeio x + a ^ 2 * rhoMeio x ^ 2 := by
    intro x; ring
  have hA : IntegrableOn (fun x => 1 - 2 * a * rhoMeio x) (Ioc 0 1) := hi1.sub (hiρ.const_mul (2 * a))
  have hB : IntegrableOn (fun x => a ^ 2 * rhoMeio x ^ 2) (Ioc 0 1) := hiρ2.const_mul (a ^ 2)
  have h1 : ∫ x in Ioc (0 : ℝ) 1, (1 : ℝ) = 1 := by simp
  unfold erro
  simp_rw [hexp]
  rw [integral_add hA hB, integral_sub hi1 (hiρ.const_mul (2 * a)), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, integral_rhoMeio, integral_rhoMeio_sq, h1]
  ring

/-- `E(c) − (1 − log 2) = (log 2/4)(c − 2)²`. -/
theorem erro_sub (a : ℝ) : erro a - (1 - Real.log 2) = Real.log 2 / 4 * (a - 2) ^ 2 := by
  rw [erro_eq]; ring

/-- **O mínimo**: `E(c) ≥ 1 − log 2` para todo `c`. -/
theorem erro_minimo (a : ℝ) : 1 - Real.log 2 ≤ erro a := by
  have h := erro_sub a
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith [sq_nonneg (a - 2)]

/-- O coeficiente ótimo é `c = 2`: `E(2) = 1 − log 2`. -/
theorem erro_em_dois : erro 2 = 1 - Real.log 2 := by
  have h := erro_sub 2
  norm_num at h
  linarith

/-- O mínimo é atingido **só** em `c = 2`. -/
theorem erro_minimo_iff (a : ℝ) : erro a = 1 - Real.log 2 ↔ a = 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro h
    have h2 := erro_sub a
    rw [h, sub_self] at h2
    have : (a - 2) ^ 2 = 0 := by
      have hne : Real.log 2 / 4 ≠ 0 := by positivity
      exact (mul_eq_zero.mp h2.symm).resolve_left hne
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · rintro rfl; exact erro_em_dois

/-- `D₁ = inf_c E(c) = 1 − log 2`. -/
theorem iInf_erro : ⨅ a : ℝ, erro a = 1 - Real.log 2 := by
  refine le_antisymm ?_ (le_ciInf erro_minimo)
  rw [← erro_em_dois]
  exact ciInf_le ⟨1 - Real.log 2, by rintro _ ⟨a, rfl⟩; exact erro_minimo a⟩ 2

/-- `0 < 1 − log 2`: este aproximante não chega a zero. -/
theorem erro_um_pos : 0 < 1 - Real.log 2 := by
  have := Real.log_two_lt_d9
  linarith

end ATK.Discovery.RhoMeio

#print axioms ATK.Discovery.RhoMeio.rhoMeio_degrau
#print axioms ATK.Discovery.RhoMeio.rhoMeio_sq
#print axioms ATK.Discovery.RhoMeio.integral_faixa
#print axioms ATK.Discovery.RhoMeio.integral_parcial
#print axioms ATK.Discovery.RhoMeio.soma_faixas
#print axioms ATK.Discovery.RhoMeio.tendsto_harmonic_dobro
#print axioms ATK.Discovery.RhoMeio.integral_rhoMeio
#print axioms ATK.Discovery.RhoMeio.integral_rhoMeio_sq
#print axioms ATK.Discovery.RhoMeio.erro_eq
#print axioms ATK.Discovery.RhoMeio.erro_sub
#print axioms ATK.Discovery.RhoMeio.erro_minimo
#print axioms ATK.Discovery.RhoMeio.erro_em_dois
#print axioms ATK.Discovery.RhoMeio.erro_minimo_iff
#print axioms ATK.Discovery.RhoMeio.iInf_erro
#print axioms ATK.Discovery.RhoMeio.erro_um_pos
