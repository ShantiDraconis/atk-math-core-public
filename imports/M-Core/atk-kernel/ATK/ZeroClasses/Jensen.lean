import ATK.ZeroClasses.Lagarias
import ATK.FechamentoO1
import ATK.GammaVertical
import ATK.ZeroCritico
import Mathlib.Analysis.Complex.JensenFormula

/-!
# `N(T) = O(T log T)` pela fórmula de Jensen (rodada 30)

A Mathlib tem a **fórmula de Jensen** (`AnalyticOnNhd.sum_divisor_le`): o número de zeros (com
multiplicidade) de `f` em `‖s − c‖ ≤ r` é `≤ log(M/‖f c‖)/log(R/r)` quando `‖f‖ ≤ M` em `‖s − c‖ = R`.
Faltava aplicá-la a `ξ`. Este arquivo faz isso e obtém a cota superior clássica da contagem de zeros:

* **cota de `ζ`** (`cota_zeta`): em `Re s ≥ ½`, `‖(s − 1) ζ(s)‖ ≤ 1 + ‖s − 1‖(½ + 3‖s‖)`
  (Euler–Maclaurin de ordem 1, `norm_zeta_sub_EM_le`);
* **cota de `Γℝ`** (`cota_Gammaℝ`): `‖Γℝ(s)‖ ≤ Γ(Re s/2)` (`|π^{−s/2}| ≤ 1` e `‖Γ(w)‖ ≤ Γ(Re w)`);
* **cota de `Γ` real** (`Gamma_le`): `Γ(x) ≤ 4 + n!` em `¼ ≤ x ≤ n + 1` (convexidade em `[1, 2]`,
  `Γ(x) = Γ(x+1)/x` abaixo de 1, monotonia acima de 2);
* **cota de `ξ` na bola** (`cota_xi`): `‖ξ(s)‖ ≤ Bx R n` em `‖s − ½‖ ≤ R` (lado direito por
  `ξ = s(s−1)/2 · Γℝ · ζ`, lado esquerdo pela equação funcional `ξ(1 − s) = ξ(s)`);
* **Jensen para `ξ`** (`jensen_xi`): `Σ div ξ (‖s − ½‖ ≤ T + 1) ≤ log(Bx/‖ξ(½)‖)/log 2`;
* **as ordens de `ζ` e `ξ` coincidem na faixa** (`ordem_zeta_eq_xi`): `ζ = ξ · g` perto de `ρ` com
  `g = 2 Γℝ⁻¹/(s(s−1))` analítica e não nula;
* **contagem** (`N_le_divisor`, `N_cota`): `N(T) ≤ log(Bx(2T+2, ⌈T⌉+1)/‖ξ(½)‖)/log 2`;
* **`N(T) = O(T log T)`** (`N_O_TlogT`): `∃ C, ∀ T ≥ 2, N(T) ≤ C · T · log T`.

Classificação (rodada 30): **parcial** — é a metade superior (fraca) de Riemann–von Mangoldt
(`RiemannVonMangoldt`, BUILD_PENDING em `ATK.FechamentoO1`), com a ordem de grandeza certa
`T log T`. Não diz nada sobre a posição dos zeros: RH continua OPEN_MATH.
-/

open Complex Set Filter Topology Metric
open scoped Real Nat

namespace ATK.ZeroClasses.Jensen

open ATK.BaseRiemannXi

/-! ## 1. Cotas de `ζ`, `Γℝ` e `Γ` -/

/-- **Cota de `ζ` em `Re s ≥ ½`** por Euler–Maclaurin de ordem 1. -/
theorem cota_zeta {s : ℂ} (hre : 1 / 2 ≤ s.re) (hs1 : s ≠ 1) :
    ‖(s - 1) * riemannZeta s‖ ≤ 1 + ‖s - 1‖ * (1 / 2 + 3 * ‖s‖) := by
  have hpos : 0 < s.re := by linarith
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hEM := ATK.EMGeral.norm_zeta_sub_EM_le hpos hs1 (N := 1) le_rfl (M := 1) le_rfl
  have hp : ATK.EMGeral.poch s 1 = s := by simp [ATK.EMGeral.poch]
  have hR0 : ‖riemannZeta s - ATK.EMGeral.EM 1 1 s‖ ≤ 3 / 2 * ‖s‖ / s.re := by
    refine hEM.trans (le_of_eq ?_)
    rw [hp, ATK.ZeroCert.Cb_um]
    simp
    ring
  have hR : ‖riemannZeta s - ATK.EMGeral.EM 1 1 s‖ ≤ 3 * ‖s‖ := by
    refine hR0.trans ?_
    rw [div_le_iff₀ hpos]
    nlinarith [norm_nonneg s]
  have e : (s - 1) * riemannZeta s =
      (s - 1) * (riemannZeta s - ATK.EMGeral.EM 1 1 s) + ((s - 1) / 2 + 1) := by
    rw [ATK.ZeroCert.EM_um]
    field_simp
    ring
  rw [e]
  calc _ ≤ ‖(s - 1) * (riemannZeta s - ATK.EMGeral.EM 1 1 s)‖ + ‖(s - 1) / 2 + 1‖ :=
        norm_add_le _ _
    _ ≤ ‖s - 1‖ * (3 * ‖s‖) + (‖s - 1‖ / 2 + 1) := by
        gcongr
        · rw [norm_mul]
          gcongr
        · calc ‖(s - 1) / 2 + 1‖ ≤ ‖(s - 1) / 2‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
            _ = ‖s - 1‖ / 2 + 1 := by rw [norm_div]; simp
    _ = _ := by ring

/-- **`‖Γℝ(s)‖ ≤ Γ(Re s / 2)`** para `Re s > 0`. -/
theorem cota_Gammaℝ {s : ℂ} (hre : 0 < s.re) : ‖Gammaℝ s‖ ≤ Real.Gamma (s.re / 2) := by
  rw [Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have h1 : Real.pi ^ ((-s / 2).re) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    rw [Complex.div_ofNat_re, Complex.neg_re]
    linarith
  have h2 : ‖Complex.Gamma (s / 2)‖ ≤ Real.Gamma (s.re / 2) := by
    have := ATK.GammaVertical.norm_Gamma_le_Gamma_re (w := s / 2)
      (by rw [Complex.div_ofNat_re]; linarith)
    rwa [Complex.div_ofNat_re] at this
  calc _ ≤ 1 * ‖Complex.Gamma (s / 2)‖ := by gcongr
    _ ≤ _ := by rw [one_mul]; exact h2

/-- `Γ ≤ 1` em `[1, 2]` (convexidade, `Γ(1) = Γ(2) = 1`). -/
theorem Gamma_le_um {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : Real.Gamma x ≤ 1 := by
  have := Real.convexOn_Gamma.le_max_of_mem_Icc (x := 1) (y := 2) (z := x)
    (by norm_num : (1 : ℝ) ∈ Ioi 0) (by norm_num : (2 : ℝ) ∈ Ioi 0) ⟨h1, h2⟩
  rwa [Real.Gamma_one, Real.Gamma_two, max_self] at this

/-- **`Γ(x) ≤ 4 + n!`** em `¼ ≤ x ≤ n + 1`. -/
theorem Gamma_le {x : ℝ} {n : ℕ} (hn : 1 ≤ n) (h1 : 1 / 4 ≤ x) (h2 : x ≤ n + 1) :
    Real.Gamma x ≤ 4 + n ! := by
  have hf : (0 : ℝ) ≤ n ! := by positivity
  rcases lt_or_ge x 1 with hx | hx
  · have hx0 : 0 < x := by linarith
    have e := Real.Gamma_add_one hx0.ne'
    have hb : Real.Gamma (x + 1) ≤ 1 := Gamma_le_um (by linarith) (by linarith)
    have hg : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx0
    have : Real.Gamma x ≤ 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr h1) hg.le]
    linarith
  rcases le_or_gt x 2 with hx2 | hx2
  · have := Gamma_le_um hx hx2
    linarith
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hmono := Real.Gamma_strictMonoOn_Ici.monotoneOn (mem_Ici.mpr hx2.le)
      (mem_Ici.mpr (by linarith : (2 : ℝ) ≤ n + 1)) h2
    rw [Real.Gamma_nat_eq_factorial] at hmono
    linarith

/-! ## 2. Cota de `ξ` na bola `‖s − ½‖ ≤ R` -/

/-- A cota explícita de `ξ` na bola de raio `R` (com `R + ½ ≤ 2(n + 1)`). -/
noncomputable def Bx (R : ℝ) (n : ℕ) : ℝ :=
  (R + 1) / 2 * (4 + n !) * (1 + (R + 1) * (1 / 2 + 3 * (R + 1)))

theorem Bx_ge {R : ℝ} (hR : 0 ≤ R) (n : ℕ) : 2 ≤ Bx R n := by
  unfold Bx
  have h1 : (1 : ℝ) / 2 ≤ (R + 1) / 2 := by linarith
  have h2 : (4 : ℝ) ≤ 4 + n ! := by
    have : (0 : ℝ) ≤ n ! := by positivity
    linarith
  have h3 : (1 : ℝ) ≤ 1 + (R + 1) * (1 / 2 + 3 * (R + 1)) := by nlinarith
  calc (2 : ℝ) = 1 / 2 * 4 * 1 := by norm_num
    _ ≤ _ := by gcongr

theorem norm_le_de {s : ℂ} {R : ℝ} (hs : ‖s - 1 / 2‖ ≤ R) : ‖s‖ ≤ R + 1 ∧ ‖s - 1‖ ≤ R + 1 ∧
    s.re ≤ R + 1 / 2 := by
  have hh : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  refine ⟨?_, ?_, ?_⟩
  · calc ‖s‖ = ‖(s - 1 / 2) + 1 / 2‖ := by ring_nf
      _ ≤ ‖s - 1 / 2‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
      _ ≤ R + 1 := by rw [hh]; linarith
  · calc ‖s - 1‖ = ‖(s - 1 / 2) - 1 / 2‖ := by ring_nf
      _ ≤ ‖s - 1 / 2‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
      _ ≤ R + 1 := by rw [hh]; linarith
  · have := Complex.abs_re_le_norm (s - 1 / 2)
    have e : (s - 1 / 2).re = s.re - 1 / 2 := by simp
    rw [e] at this
    linarith [le_abs_self (s.re - 1 / 2)]

/-- **Cota de `ξ` no lado direito** `Re s ≥ ½`. -/
theorem cota_xi_direita {s : ℂ} {R : ℝ} {n : ℕ} (hn : 1 ≤ n) (hR : 0 ≤ R)
    (hRn : R + 1 / 2 ≤ 2 * (n + 1)) (hre : 1 / 2 ≤ s.re) (hs : ‖s - 1 / 2‖ ≤ R) :
    ‖riemannXi s‖ ≤ Bx R n := by
  by_cases hs1 : s = 1
  · subst hs1
    rw [riemannXi_one]
    have := Bx_ge hR n
    norm_num
    linarith
  have hpos : 0 < s.re := by linarith
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hpos
  have hG := Gammaℝ_ne_zero_of_re_pos hpos
  obtain ⟨hn1, hn2, hn3⟩ := norm_le_de hs
  rw [riemannXi_eq_zeta hs0 hs1 hG]
  have e : s * (s - 1) / 2 * Gammaℝ s * riemannZeta s =
      s / 2 * Gammaℝ s * ((s - 1) * riemannZeta s) := by ring
  rw [e, norm_mul, norm_mul, norm_div]
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have hz := cota_zeta hre hs1
  have hg := (cota_Gammaℝ hpos).trans (Gamma_le hn (x := s.re / 2) (by linarith) (by linarith))
  unfold Bx
  gcongr
  exact hz.trans (by gcongr)

/-- **Cota de `ξ` na bola** `‖s − ½‖ ≤ R` (o lado esquerdo pela equação funcional). -/
theorem cota_xi {s : ℂ} {R : ℝ} {n : ℕ} (hn : 1 ≤ n) (hR : 0 ≤ R)
    (hRn : R + 1 / 2 ≤ 2 * (n + 1)) (hs : ‖s - 1 / 2‖ ≤ R) : ‖riemannXi s‖ ≤ Bx R n := by
  rcases le_or_gt (1 / 2) s.re with h | h
  · exact cota_xi_direita hn hR hRn h hs
  · have h' : 1 / 2 ≤ (1 - s).re := by
      simp
      linarith
    have hs' : ‖(1 - s) - 1 / 2‖ ≤ R := by
      have e : (1 - s) - 1 / 2 = -(s - 1 / 2) := by ring
      rw [e, norm_neg]
      exact hs
    have := cota_xi_direita hn hR hRn h' hs'
    rwa [riemannXi_one_sub] at this

/-! ## 3. Jensen para `ξ` -/

/-- `ξ(½) ≠ 0` (porque `ζ(½) ≠ 0`). -/
theorem xi_metade_ne_zero : riemannXi (1 / 2) ≠ 0 := by
  intro h
  rw [riemannXi_eq_zero_iff (by norm_num) (by norm_num)] at h
  exact ATK.ZetaRetangulo.zeta_ne_zero_baixo (s := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num) h

/-- **Jensen para `ξ`**: os zeros em `‖s − ½‖ ≤ T + 1` (com multiplicidade) são
`≤ log(Bx(2T+2, ⌈T⌉+1)/‖ξ(½)‖)/log 2`. -/
theorem jensen_xi {T : ℝ} (hT : 0 ≤ T) :
    ((∑ᶠ u, MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) (T + 1)) u : ℤ) : ℝ) ≤
      Real.log (Bx (2 * (T + 1)) (⌈T⌉₊ + 1) / ‖riemannXi (1 / 2)‖) / Real.log 2 := by
  have hT1 : (0 : ℝ) < T + 1 := by linarith
  have hr : 0 < |T + 1| := by rw [abs_of_pos hT1]; exact hT1
  have hrR : |T + 1| < |2 * (T + 1)| := by
    rw [abs_of_pos hT1, abs_of_pos (by linarith)]
    linarith
  have hM : 1 ≤ Bx (2 * (T + 1)) (⌈T⌉₊ + 1) := by
    have := Bx_ge (R := 2 * (T + 1)) (by linarith) (⌈T⌉₊ + 1)
    linarith
  have han : AnalyticOnNhd ℂ riemannXi (closedBall (1 / 2) |2 * (T + 1)|) :=
    fun z _ => ATK.ZeroClasses.Lagarias.analitica z
  have hb : ∀ z ∈ sphere (1 / 2 : ℂ) |2 * (T + 1)|,
      ‖riemannXi z‖ ≤ Bx (2 * (T + 1)) (⌈T⌉₊ + 1) := by
    intro z hz
    rw [mem_sphere_iff_norm, abs_of_pos (by linarith)] at hz
    refine cota_xi (by omega) (by linarith) ?_ hz.le
    have := Nat.le_ceil T
    push_cast
    linarith
  have J := AnalyticOnNhd.sum_divisor_le hr hrR hM han xi_metade_ne_zero hb
  rw [abs_of_pos hT1] at J
  have e : 2 * (T + 1) / (T + 1) = 2 := by field_simp
  rwa [e] at J

/-! ## 4. As ordens de `ζ` e `ξ` coincidem na faixa -/

/-- **`ord_ρ ζ = ord_ρ ξ`** para `Re ρ > 0`, `ρ ≠ 1`. -/
theorem ordem_zeta_eq_xi {ρ : ℂ} (hre : 0 < ρ.re) (h1 : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ = analyticOrderAt riemannXi ρ := by
  have h0 : ρ ≠ 0 := by
    rintro rfl
    simp at hre
  set g : ℂ → ℂ := fun s => 2 * (Gammaℝ s)⁻¹ / (s * (s - 1)) with hg
  have hga : AnalyticAt ℂ g ρ := by
    have hGi : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) ρ := differentiable_Gammaℝ_inv.analyticAt ρ
    have hp : AnalyticAt ℂ (fun s : ℂ => s * (s - 1)) ρ :=
      analyticAt_id.mul (analyticAt_id.sub analyticAt_const)
    exact (analyticAt_const.mul hGi).div hp (mul_ne_zero h0 (sub_ne_zero.mpr h1))
  have hg0 : g ρ ≠ 0 := by
    simp only [hg]
    exact div_ne_zero (mul_ne_zero two_ne_zero (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hre)))
      (mul_ne_zero h0 (sub_ne_zero.mpr h1))
  have hev : riemannZeta =ᶠ[𝓝 ρ] riemannXi * g := by
    have e1 : ∀ᶠ s in 𝓝 ρ, 0 < s.re :=
      (Complex.continuous_re.tendsto ρ).eventually (lt_mem_nhds hre)
    have e2 : ∀ᶠ s in 𝓝 ρ, s ≠ 1 := eventually_ne_nhds h1
    filter_upwards [e1, e2] with s hs hs1
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hs
    have hG := Gammaℝ_ne_zero_of_re_pos hs
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    simp only [Pi.mul_apply, hg]
    rw [riemannXi_eq_zeta hs0 hs1 hG]
    field_simp
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul (ATK.ZeroClasses.Lagarias.analitica ρ) hga,
    analyticOrderAt_eq_zero.mpr (Or.inr hg0), add_zero]

theorem ordemNat_zeta_eq_xi {ρ : ℂ} (hre : 0 < ρ.re) (h1 : ρ ≠ 1) :
    analyticOrderNatAt riemannZeta ρ = analyticOrderNatAt riemannXi ρ := by
  unfold analyticOrderNatAt
  rw [ordem_zeta_eq_xi hre h1]

/-! ## 5. A contagem `N(T)` -/

/-- Os zeros com `0 < Im ρ ≤ T` estão na bola `‖s − ½‖ ≤ T + 1`. -/
theorem zerosAte_sub_bola (T : ℝ) :
    ATK.FechamentoO1.zerosAte T ⊆ closedBall (1 / 2 : ℂ) (T + 1) := by
  intro ρ hρ
  obtain ⟨⟨_, h0, h1⟩, him0, _⟩ := hρ
  rw [mem_closedBall, dist_eq_norm]
  have e1 : (ρ - 1 / 2).re = ρ.re - 1 / 2 := by simp
  have e2 : (ρ - 1 / 2).im = ρ.im := by simp
  have ha : |ρ.re - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc ‖ρ - 1 / 2‖ ≤ |(ρ - 1 / 2).re| + |(ρ - 1 / 2).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / 2 + T := by
      rw [e1, e2, abs_of_pos him0]
      linarith
    _ ≤ T + 1 := by linarith

/-- **`N(T) ≤ Σ div ξ`** na bola `‖s − ½‖ ≤ T + 1`. -/
theorem N_le_divisor (T : ℝ) :
    ((ATK.FechamentoO1.N T : ℕ) : ℤ) ≤
      ∑ᶠ u, MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) (T + 1)) u := by
  set U := closedBall (1 / 2 : ℂ) (T + 1) with hU
  set D := MeromorphicOn.divisor riemannXi U with hD
  set S := (ATK.FechamentoO1.zerosAte_finito T).toFinset with hS
  have hfin : (Function.support D).Finite := D.finiteSupport (isCompact_closedBall _ _)
  have han : AnalyticOnNhd ℂ riemannXi U := fun z _ => ATK.ZeroClasses.Lagarias.analitica z
  have hnn : ∀ u, 0 ≤ D u := fun u => by simpa using MeromorphicOn.AnalyticOnNhd.divisor_nonneg han u
  rw [finsum_eq_sum_of_support_subset D (s := hfin.toFinset ∪ S)
    (by intro u hu; simp [hu])]
  unfold ATK.FechamentoO1.N
  push_cast
  calc ∑ ρ ∈ (ATK.FechamentoO1.zerosAte_finito T).toFinset,
        ((analyticOrderNatAt riemannZeta ρ : ℕ) : ℤ) = ∑ ρ ∈ S, D ρ := by
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        have hρ' : ρ ∈ ATK.FechamentoO1.zerosAte T := (Set.Finite.mem_toFinset _).mp hρ
        have hρU : ρ ∈ U := zerosAte_sub_bola T hρ'
        obtain ⟨⟨_, h0, h1⟩, _, _⟩ := hρ'
        have hρ1 : ρ ≠ 1 := by
          rintro rfl
          simp at h1
        rw [hD, ATK.ArgPrincipio.divisor_eq_ordem han hρU
          (ATK.ZeroClasses.Lagarias.ordem_xi_finita ρ), ordemNat_zeta_eq_xi h0 hρ1]
    _ ≤ ∑ u ∈ hfin.toFinset ∪ S, D u :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right (fun u _ _ => hnn u)

/-- **Cota explícita da contagem**: `N(T) ≤ log(Bx(2T+2, ⌈T⌉+1)/‖ξ(½)‖)/log 2`. -/
theorem N_cota {T : ℝ} (hT : 0 ≤ T) :
    (ATK.FechamentoO1.N T : ℝ) ≤
      Real.log (Bx (2 * (T + 1)) (⌈T⌉₊ + 1) / ‖riemannXi (1 / 2)‖) / Real.log 2 := by
  have h1 := N_le_divisor T
  have h2 := jensen_xi hT
  have h1' : ((ATK.FechamentoO1.N T : ℤ) : ℝ) ≤
      ((∑ᶠ u, MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) (T + 1)) u : ℤ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h1'
  linarith

/-! ## 6. `N(T) = O(T log T)` -/

/-- `log Bx(2T+2, n) ≤ 13 log T + 4 T log T` para `T ≥ 2`, `1 ≤ n ≤ 2T`. -/
theorem log_Bx_le {T : ℝ} (hT : 2 ≤ T) {n : ℕ} (hn0 : (1 : ℝ) ≤ n) (hn1 : (n : ℝ) ≤ 2 * T) :
    Real.log (Bx (2 * (T + 1)) n) ≤ 13 * Real.log T + 4 * T * Real.log T := by
  have hT0 : 0 ≤ T := by linarith
  have lp : ∀ k : ℕ, Real.log (T ^ k) = k * Real.log T := fun k => by rw [Real.log_pow]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  unfold Bx
  have p1 : 0 < (2 * (T + 1) + 1) / 2 := by positivity
  have p2 : 0 < 4 + (n ! : ℝ) := by positivity
  have p3 : 0 < 1 + (2 * (T + 1) + 1) * (1 / 2 + 3 * (2 * (T + 1) + 1)) := by positivity
  rw [Real.log_mul (by positivity) p3.ne', Real.log_mul p1.ne' p2.ne']
  have hTT := mul_nonneg (sub_nonneg.mpr hT) hT0
  have q1 : Real.log ((2 * (T + 1) + 1) / 2) ≤ 2 * Real.log T := by
    have := Real.log_le_log p1 (show (2 * (T + 1) + 1) / 2 ≤ T ^ 2 by nlinarith)
    rw [lp] at this
    push_cast at this
    exact this
  have q3 : Real.log (1 + (2 * (T + 1) + 1) * (1 / 2 + 3 * (2 * (T + 1) + 1))) ≤
      8 * Real.log T := by
    have h6 : (64 : ℝ) ≤ T ^ 6 := by
      calc (64 : ℝ) = 2 ^ 6 := by norm_num
        _ ≤ T ^ 6 := pow_le_pow_left₀ (by norm_num) hT 6
    have h8 : T ^ 8 = T ^ 6 * T ^ 2 := by ring
    have hb : 1 + (2 * (T + 1) + 1) * (1 / 2 + 3 * (2 * (T + 1) + 1)) ≤ T ^ 8 := by
      rw [h8]
      nlinarith [mul_nonneg (sub_nonneg.mpr h6) (sq_nonneg T)]
    have := Real.log_le_log p3 hb
    rw [lp] at this
    push_cast at this
    exact this
  have q2 : Real.log (4 + (n ! : ℝ)) ≤ 3 * Real.log T + 4 * T * Real.log T := by
    have f1 : (1 : ℝ) ≤ n ! := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)
    have f2 : (n ! : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have f3 : 4 + (n ! : ℝ) ≤ 5 * (n : ℝ) ^ n := by linarith
    have f4 : Real.log (5 * (n : ℝ) ^ n) = Real.log 5 + n * Real.log n := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have f5 : Real.log 5 ≤ 3 * Real.log T := by
      have h3 : (8 : ℝ) ≤ T ^ 3 := by
        calc (8 : ℝ) = 2 ^ 3 := by norm_num
          _ ≤ T ^ 3 := pow_le_pow_left₀ (by norm_num) hT 3
      have := Real.log_le_log (by norm_num) (show (5 : ℝ) ≤ T ^ 3 by linarith)
      rw [lp] at this
      push_cast at this
      exact this
    have f6 : Real.log n ≤ 2 * Real.log T := by
      have := Real.log_le_log (by linarith) (show (n : ℝ) ≤ T ^ 2 by nlinarith)
      rw [lp] at this
      push_cast at this
      exact this
    have f7 : (n : ℝ) * Real.log n ≤ 2 * T * (2 * Real.log T) :=
      mul_le_mul hn1 f6 (Real.log_nonneg hn0) (by linarith)
    calc Real.log (4 + (n ! : ℝ)) ≤ Real.log (5 * (n : ℝ) ^ n) := Real.log_le_log p2 f3
      _ = Real.log 5 + n * Real.log n := f4
      _ ≤ 3 * Real.log T + 4 * T * Real.log T := by nlinarith
  linarith

/-- **`N(T) = O(T log T)`**: existe `C` com `N(T) ≤ C · T · log T` para todo `T ≥ 2`. -/
theorem N_O_TlogT : ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
    (ATK.FechamentoO1.N T : ℝ) ≤ C * T * Real.log T := by
  set a := ‖riemannXi (1 / 2)‖ with ha
  have ha0 : 0 < a := norm_pos_iff.mpr xi_metade_ne_zero
  set A := |Real.log a| with hA
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨((13 + A / Real.log 2) / 2 + 4) / Real.log 2, fun T hT => ?_⟩
  have hT0 : 0 ≤ T := by linarith
  have hL2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  have hL0 : 0 < Real.log T := lt_of_lt_of_le hl2 hL2
  have hc := Nat.ceil_lt_add_one hT0
  have hc0 : (0 : ℝ) ≤ ⌈T⌉₊ := Nat.cast_nonneg _
  have hn1 : ((⌈T⌉₊ + 1 : ℕ) : ℝ) ≤ 2 * T := by
    push_cast
    linarith
  have hn0 : (1 : ℝ) ≤ ((⌈T⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hX := log_Bx_le hT hn0 hn1
  have hBpos : 0 < Bx (2 * (T + 1)) (⌈T⌉₊ + 1) :=
    lt_of_lt_of_le (by norm_num) (Bx_ge (R := 2 * (T + 1)) (by linarith) _)
  have hB : Real.log (Bx (2 * (T + 1)) (⌈T⌉₊ + 1) / a) ≤
      13 * Real.log T + 4 * T * Real.log T + A := by
    rw [Real.log_div hBpos.ne' ha0.ne']
    have : -Real.log a ≤ A := neg_le_abs _
    linarith
  have hAL : A ≤ A / Real.log 2 * Real.log T := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hL2 (abs_nonneg _)
  have hLT : Real.log T ≤ T * Real.log T / 2 := by nlinarith
  have c0 : 0 ≤ 13 + A / Real.log 2 := by positivity
  have hm := mul_le_mul_of_nonneg_left hLT c0
  have hK : 13 * Real.log T + 4 * T * Real.log T + A ≤
      ((13 + A / Real.log 2) / 2 + 4) * (T * Real.log T) := by nlinarith
  have hN := N_cota hT0
  calc (ATK.FechamentoO1.N T : ℝ)
      ≤ Real.log (Bx (2 * (T + 1)) (⌈T⌉₊ + 1) / a) / Real.log 2 := hN
    _ ≤ (((13 + A / Real.log 2) / 2 + 4) * (T * Real.log T)) / Real.log 2 := by
        gcongr
        linarith
    _ = _ := by ring

end ATK.ZeroClasses.Jensen

#print axioms ATK.ZeroClasses.Jensen.cota_zeta
#print axioms ATK.ZeroClasses.Jensen.cota_Gammaℝ
#print axioms ATK.ZeroClasses.Jensen.Gamma_le_um
#print axioms ATK.ZeroClasses.Jensen.Gamma_le
#print axioms ATK.ZeroClasses.Jensen.Bx_ge
#print axioms ATK.ZeroClasses.Jensen.norm_le_de
#print axioms ATK.ZeroClasses.Jensen.cota_xi_direita
#print axioms ATK.ZeroClasses.Jensen.cota_xi
#print axioms ATK.ZeroClasses.Jensen.xi_metade_ne_zero
#print axioms ATK.ZeroClasses.Jensen.jensen_xi
#print axioms ATK.ZeroClasses.Jensen.ordem_zeta_eq_xi
#print axioms ATK.ZeroClasses.Jensen.ordemNat_zeta_eq_xi
#print axioms ATK.ZeroClasses.Jensen.zerosAte_sub_bola
#print axioms ATK.ZeroClasses.Jensen.N_le_divisor
#print axioms ATK.ZeroClasses.Jensen.N_cota
#print axioms ATK.ZeroClasses.Jensen.log_Bx_le
#print axioms ATK.ZeroClasses.Jensen.N_O_TlogT
