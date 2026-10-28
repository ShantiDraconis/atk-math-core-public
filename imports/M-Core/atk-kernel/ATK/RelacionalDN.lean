/-
ATK-I — Nível III para Riemann: a família de Báez-Duarte lida como relações.

A "transformação a investigar" para Riemann no texto ATK-I é a aproximação por subespaços finitos.
Aqui ela é lida na linguagem relacional, com um teorema novo e incondicional no caminho:

* **`DN_pos`: `D_N > 0` para todo N.**  Nenhuma etapa finita é exata: em `(1,∞)` o resíduo é
  `−S/t` (não nulo se `S ≠ 0`); se `S = 0`, no degrau `(1/(N!+1), 1/N!]` todo
  `ρ^{NB}_{k+1}` vale `{N!/(k+1)} = 0`, logo o resíduo vale `χ = 1` num conjunto de medida positiva;
* `etapa N = R(D_N, 0)`: `d(etapa N) = D_N` e **toda etapa é falsa**;
* `etapa N → limite = R(D_∞, 0)` e **`O1 ⟺ limite verdadeiro`** (pelo `limite_iff` de ATK-I);
* `cota_uniforme_refuta_O1`: uma cota uniforme `D_N ≥ c > 0` (não colapso uniforme) refutaria O1 —
  O1 exige exatamente que a proteção uniforme desapareça no limite.

Isto é a forma exata, no kernel, de "aproximação ≠ igualdade" para a rota de Riemann: o único
certificado possível é o do limite.  O1 continua OPEN; certificados terminais 0/7.
-/
import ATK.GramBaezDuarte
import ATK.RelacionalI

namespace ATK.RelacionalDN

open MeasureTheory Set Filter Topology Finset
open ATK.Conditional.Riemann (chi rho residualSq DN)
open ATK.RelacionalI

/-! ### D_N > 0 -/

/-- No degrau `(1/(L+1), 1/L]`, `⌊1/t⌋ = L`. -/
theorem int_floor_of_mem_step {L : ℕ} (hL : 1 ≤ L) {t : ℝ} (ht : t ∈ ATK.OmegaGramL2.step L) :
    ⌊1 / t⌋ = (L : ℤ) := by
  obtain ⟨h1, h2⟩ := ht
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
  have hx0 : 0 < t := lt_trans (by positivity) h1
  have h2' : t * (L : ℝ) ≤ 1 := (le_div_iff₀ hL0).mp h2
  have h1' : 1 < t * ((L : ℝ) + 1) := (div_lt_iff₀ (by positivity)).mp h1
  rw [Int.floor_eq_iff]
  push_cast
  constructor
  · rw [le_div_iff₀ hx0]; linarith [mul_comm t (L : ℝ)]
  · rw [div_lt_iff₀ hx0]; nlinarith [mul_comm t ((L : ℝ) + 1)]

/-- Se `m ∣ L`, então `ρ^{NB}_m ≡ 0` no degrau L. -/
theorem nb_rho_zero_of_dvd {L m : ℕ} (hm : 1 ≤ m) (hdvd : m ∣ L) (hL : 1 ≤ L) {t : ℝ}
    (ht : t ∈ ATK.OmegaGramL2.step L) : ATK.RhoIndependente.rho (K := ℝ) m t = 0 := by
  have hx0 : 0 < t := lt_trans (by positivity) ht.1
  rw [ATK.RhoIndependente.rho_eq_step m hm hx0, int_floor_of_mem_step hL ht]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  rw [Int.cast_natCast, ← Nat.cast_div hdvd hm0, Int.fract_natCast]

/-- **O resíduo nunca se anula**: `‖χ − Σ c_k ρ_{k+1}‖² > 0` para todo N e todo c. -/
theorem residualSq_pos (N : ℕ) (c : Fin N → ℝ) : 0 < residualSq N c := by
  classical
  have hint := ATK.RiemannFaithful.integrable_residual N c
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t => (chi t - ∑ k : Fin N, c k * rho (k.val + 1) t) ^ 2 :=
    Eventually.of_forall fun t => sq_nonneg _
  unfold residualSq
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  by_cases hS : ATK.GramBaezDuarte.S c = 0
  · -- degrau L = N!: todos os ρ^{NB}_{k+1} se anulam e o resíduo vale 1
    have hL : 1 ≤ N.factorial := Nat.factorial_pos N
    have hsub : ATK.OmegaGramL2.step N.factorial ⊆
        Function.support (fun t => (chi t - ∑ k : Fin N, c k * rho (k.val + 1) t) ^ 2) ∩
          Ioi 0 := by
      intro t ht
      have ht01 := ATK.OmegaGramL2.step_subset N.factorial hL ht
      refine ⟨?_, ht01.1⟩
      have hF : ATK.GramBaezDuarte.F c t = 0 := by
        rw [ATK.GramBaezDuarte.F_decomp, hS, zero_mul, add_zero]
        refine Finset.sum_eq_zero fun k _ => ?_
        have hk : k.val + 1 ≤ N := k.isLt
        rw [nb_rho_zero_of_dvd (Nat.succ_pos _) (Nat.dvd_factorial (Nat.succ_pos _) hk) hL ht,
          mul_zero]
      simp only [Function.mem_support]
      change (chi t - ATK.GramBaezDuarte.F c t) ^ 2 ≠ 0
      rw [hF, sub_zero, ATK.RiemannFaithful.chi_of_mem ht01]
      norm_num
    exact lt_of_lt_of_le (ATK.OmegaGramL2.volume_step N.factorial hL) (measure_mono hsub)
  · -- cauda (1,∞): o resíduo é −S/t ≠ 0
    have hsub : Ioi (1 : ℝ) ⊆
        Function.support (fun t => (chi t - ∑ k : Fin N, c k * rho (k.val + 1) t) ^ 2) ∩
          Ioi 0 := by
      intro t ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      refine ⟨?_, ht0⟩
      simp only [Function.mem_support]
      change (chi t - ATK.GramBaezDuarte.F c t) ^ 2 ≠ 0
      rw [ATK.GramBaezDuarte.F_of_gt_one c ht, ATK.RiemannFaithful.chi_of_gt_one ht, zero_sub,
        neg_sq]
      exact pow_ne_zero 2 (div_ne_zero hS ht0.ne')
    have hvol : (0 : ENNReal) < volume (Ioi (1 : ℝ)) := by
      rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
    exact lt_of_lt_of_le hvol (measure_mono hsub)

/-- **`D_N > 0` para todo N** (incondicional). -/
theorem DN_pos (N : ℕ) : 0 < DN N := by
  rw [ATK.GramBaezDuarte.DN_attained]
  exact residualSq_pos N _

/-! ### Leitura relacional -/

/-- A relação da etapa N: `R(D_N, 0)`. -/
noncomputable def etapa (N : ℕ) : Relacao ℝ := (DN N, 0)

/-- A relação-limite: `R(D_∞, 0)`. -/
noncomputable def limite : Relacao ℝ := (⨅ N, DN N, 0)

theorem d_etapa (N : ℕ) : d (etapa N) = DN N := by
  unfold d etapa
  simp only [sub_zero, Real.norm_eq_abs]
  exact abs_of_pos (DN_pos N)

/-- **Toda etapa finita é falsa.** -/
theorem etapa_falsa (N : ℕ) : ¬ Verdadeira (etapa N) := fun h => (DN_pos N).ne' h

theorem etapa_tendsto : Tendsto etapa atTop (𝓝 limite) :=
  ATK.RiemannConcrete.DN_tendsto_iInf.prodMk_nhds tendsto_const_nhds

/-- **O1 ⟺ a relação-limite `R(D_∞, 0)` é verdadeira.** -/
theorem O1_iff_limite_verdadeiro : Tendsto DN atTop (𝓝 0) ↔ Verdadeira limite := by
  rw [← limite_iff etapa_tendsto]
  simp_rw [d_etapa]

theorem limite_verdadeiro_iff : Verdadeira limite ↔ ⨅ N, DN N = 0 := Iff.rfl

/-- **Riemann pela ATK-I**: toda etapa é falsa, e O1 é exatamente a verdade do limite. -/
theorem riemann_so_no_limite :
    (∀ N, ¬ Verdadeira (etapa N)) ∧ (Tendsto DN atTop (𝓝 0) ↔ Verdadeira limite) ∧
      (Verdadeira limite ↔ ⨅ N, DN N = 0) :=
  ⟨etapa_falsa, O1_iff_limite_verdadeiro, limite_verdadeiro_iff⟩

/-- Uma cota uniforme `D_N ≥ c > 0` (não colapso uniforme) **refutaria** O1. -/
theorem cota_uniforme_refuta_O1 (h : ∃ c > 0, ∀ N, c ≤ DN N) : ¬ Tendsto DN atTop (𝓝 0) := by
  obtain ⟨c, hc, hN⟩ := h
  intro hlim
  have : c ≤ 0 := ge_of_tendsto' hlim hN
  linarith

/-- Reciprocamente: se O1 vale, nenhuma cota uniforme positiva existe. -/
theorem O1_sem_cota_uniforme (h : Tendsto DN atTop (𝓝 0)) : ¬ ∃ c > 0, ∀ N, c ≤ DN N :=
  fun hc => cota_uniforme_refuta_O1 hc h

end ATK.RelacionalDN

#print axioms ATK.RelacionalDN.int_floor_of_mem_step
#print axioms ATK.RelacionalDN.nb_rho_zero_of_dvd
#print axioms ATK.RelacionalDN.residualSq_pos
#print axioms ATK.RelacionalDN.DN_pos
#print axioms ATK.RelacionalDN.d_etapa
#print axioms ATK.RelacionalDN.etapa_falsa
#print axioms ATK.RelacionalDN.etapa_tendsto
#print axioms ATK.RelacionalDN.O1_iff_limite_verdadeiro
#print axioms ATK.RelacionalDN.limite_verdadeiro_iff
#print axioms ATK.RelacionalDN.riemann_so_no_limite
#print axioms ATK.RelacionalDN.cota_uniforme_refuta_O1
#print axioms ATK.RelacionalDN.O1_sem_cota_uniforme
