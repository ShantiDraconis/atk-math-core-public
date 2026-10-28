import ATK.ZeroClasses.PsiRH

/-!
# As peças da fórmula explícita (rodada 66)

Para deslocar o contorno de Perron **através** dos zeros (Davenport, cap. 17):

* **o princípio do argumento ponderado** (`principio_ponderado`): para `f` e `φ` analíticas perto do retângulo `R`,
  sem zeros de `f` no bordo, `∮_{∂R} (f′/f)·φ = 2πi Σ_{u ∈ R, f(u) = 0} m_u φ(u)` (o quociente local da rodada 40
  e `φ(s)/(s − u) = dslope φ u (s) + φ(u)/(s − u)`);
* **o resíduo explícito** (`bordo_explicita`): no retângulo `[b, c] × [−T, T]`, `0 < b < 1 < c`, sem zeros de `ζ` no
  bordo, `∮ x^s(−ζ′/ζ)(s)/s ds = 2πi (x − Σ_{ρ ∈ R} m_ρ x^ρ/ρ)`, via `G(s) = (s − 1)ζ(s)` (`ordem_Gp`:
  `ord_ρ G = ord_ρ ζ`);
* **`Σ_{|γ| ≤ T} m_ρ/|ρ| ≤ C (1 + log T)²`** (`soma_ordem_norm`), por blocos `⌊|γ|⌋ = k`, caixas de Jensen e
  `H_n ≤ 1 + log n` da Mathlib;
* **alturas boas** (`altura_boa`): para todo `T₀ ≥ 6` existe `T ∈ [T₀, T₀ + 1]` a distância `≥ δ` de todo `|γ|`,
  `δ⁻¹ = O(log T₀)` (casa dos pombos entre `n + 1` candidatos e os `n = O(log T₀)` zeros próximos); lá
  `ζ(σ ± iT) ≠ 0` e `|ζ′/ζ(σ ± iT)| ≤ C log²(2 + T)` em `0 < σ ≤ 2` (`zeta_local`, rodada 63);
* **sob RH**, `|ζ′/ζ(¼ + it)| ≤ C log(2 + |t|)` para todo `t` (`logDeriv_quarto_RH`).

Classificação (rodada 66): **ferramenta** — o que falta para `RH ⟹ ψ(x) = x + O(√x log² x)`. RH continua OPEN_MATH.
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real Interval

namespace ATK.ZeroClasses.Explicita

open ATK.ZeroClasses.ArgRetangulo (bordo Bordo Ret bordo_congr bordo_add bordo_sum bordo_cauchy bordo_inv
  bordo_const_mul)
open ATK.ZeroClasses.RegiaoLivre (Gp Gp_diff Gp_eq Gp_ne_zero)
open ATK.ZeroClasses.PsiRH (Fx px px_diff px_one)
open ATK.ZeroClasses.Canonico ATK.ZeroClasses.CanonicoInteira ATK.ZeroClasses.LagariasHadamard
  ATK.ZeroClasses.JensenLocal ATK.ZeroClasses.SomaZeros

/-! ## 1. O princípio do argumento ponderado -/

/-- **`∮_{∂R} (f′/f)·φ = 2πi Σ_{u} m_u φ(u)`**, `u` os zeros de `f` em `R` (todos interiores). -/
theorem principio_ponderado {f φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (hφ : AnalyticOnNhd ℂ φ U) {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im) (hK : Ret z w ⊆ U)
    (htop : ∀ p ∈ Ret z w, analyticOrderAt f p ≠ ⊤) (hbd : ∀ p ∈ Bordo z w, f p ≠ 0) :
    ∃ S : Finset ℂ, (∀ u, u ∈ S ↔ u ∈ Ret z w ∧ f u = 0) ∧
      bordo (fun s => logDeriv f s * φ s) z w =
        2 * π * I * ∑ u ∈ S, (analyticOrderNatAt f u : ℂ) * φ u := by
  classical
  have hKc : IsCompact (Ret z w) := isCompact_uIcc.reProdIm isCompact_uIcc
  set Zs := {u | u ∈ Ret z w ∧ f u = 0} with hZs
  have hfin : Zs.Finite := by
    have hD := (MeromorphicOn.divisor f (Ret z w)).finiteSupport hKc
    refine hD.subset fun u ⟨hu, hfu⟩ => ?_
    rw [Function.mem_support, ATK.ArgPrincipio.divisor_eq_ordem (hf.mono hK) hu (htop u hu)]
    have h0 : analyticOrderNatAt f u ≠ 0 := fun h =>
      ((ATK.ArgPrincipio.ordemNat_zero_iff (hf u (hK hu)) (htop u hu)).mp h) hfu
    exact_mod_cast h0
  set S := hfin.toFinset with hS
  have hmemS : ∀ u, u ∈ S ↔ u ∈ Ret z w ∧ f u = 0 := fun u => by
    rw [hS, Set.Finite.mem_toFinset]
    rfl
  refine ⟨S, hmemS, ?_⟩
  have hint : ∀ u ∈ S, z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im := by
    intro u hu
    obtain ⟨huK, hfu⟩ := (hmemS u).mp hu
    have hr := (mem_reProdIm.mp huK).1
    have hi := (mem_reProdIm.mp huK).2
    rw [uIcc_of_le hre.le] at hr
    rw [uIcc_of_le him.le] at hi
    refine ⟨lt_of_le_of_ne hr.1 fun h => hbd u ⟨huK, Or.inl h.symm⟩ hfu,
      lt_of_le_of_ne hr.2 fun h => hbd u ⟨huK, Or.inr (Or.inl h)⟩ hfu,
      lt_of_le_of_ne hi.1 fun h => hbd u ⟨huK, Or.inr (Or.inr (Or.inl h.symm))⟩ hfu,
      lt_of_le_of_ne hi.2 fun h => hbd u ⟨huK, Or.inr (Or.inr (Or.inr h))⟩ hfu⟩
  set m : ℂ → ℕ := fun u => analyticOrderNatAt f u with hm
  set Q : ℂ → ℂ := fun s => ∏ u ∈ S, (s - u) ^ m u with hQ
  have hQan : AnalyticOnNhd ℂ Q univ := fun s _ => by simp only [hQ]; fun_prop
  have hordQ : ∀ p, analyticOrderAt Q p = if p ∈ S then (m p : ℕ∞) else 0 := fun p =>
    ATK.ZeroClasses.Landau.ordem_poli S m p
  have hmw : ∀ p ∈ S, (m p : ℕ∞) = analyticOrderAt f p := by
    intro p hp
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (htop p ((hmemS p).mp hp).1)
    simp only [hm, analyticOrderNatAt, ← hk]
    simp
  have hle : ∀ p ∈ U, analyticOrderAt Q p ≤ analyticOrderAt f p := by
    intro p _
    rw [hordQ]
    split_ifs with h
    · rw [hmw p h]
    · simp
  have htopQ : ∀ p ∈ U, analyticOrderAt Q p ≠ ⊤ := by
    intro p _
    rw [hordQ]
    split_ifs <;> simp
  obtain ⟨G, hGan, hfQG, hG0⟩ := ATK.ZeroClasses.Landau.quociente_local hU hf
    (hQan.mono (subset_univ _)) hle htopQ
  have hGne : ∀ p ∈ Ret z w, G p ≠ 0 := by
    intro p hp
    apply hG0 p (hK hp)
    rw [hordQ]
    split_ifs with h
    · exact (hmw p h).symm
    · have hfp : f p ≠ 0 := fun h' => h ((hmemS p).mpr ⟨hp, h'⟩)
      exact analyticOrderAt_eq_zero.mpr (Or.inr hfp)
  -- a parte holomorfa e os polos simples
  set H : ℂ → ℂ := fun s => ∑ u ∈ S, (m u : ℂ) * dslope φ u s + logDeriv G s * φ s with hH
  have hlogf : EqOn (fun s => logDeriv f s * φ s)
      (fun s => H s + ∑ u ∈ S, ((m u : ℂ) * φ u) * (s - u)⁻¹) (Bordo z w) := by
    intro p hp
    have hpS : p ∉ S := fun h => hbd p hp ((hmemS p).mp h).2
    have hpU : p ∈ U := hK hp.1
    have hev : f =ᶠ[𝓝 p] fun s => Q s * G s := by
      filter_upwards [hU.mem_nhds hpU] with s hs
      exact hfQG s hs
    have hQp : Q p ≠ 0 := by
      simp only [hQ]
      rw [Finset.prod_ne_zero_iff]
      intro u hu
      exact pow_ne_zero _ (sub_ne_zero.mpr fun h => hpS (h ▸ hu))
    have hlog : logDeriv f p = ∑ u ∈ S, (m u : ℂ) / (p - u) + logDeriv G p := by
      rw [(logDeriv_congr_nhds hev).self_of_nhds]
      change logDeriv (Q * G) p = _
      rw [logDeriv_mul p hQp (hGne p hp.1) (hQan p (mem_univ _)).differentiableAt
        (hGan p hpU).differentiableAt, ATK.ZeroClasses.Landau.logDeriv_poli S m hpS]
    simp only [hH]
    rw [hlog, add_mul, Finset.sum_mul]
    have hterm : ∀ u ∈ S, (m u : ℂ) / (p - u) * φ p =
        (m u : ℂ) * dslope φ u p + ((m u : ℂ) * φ u) * (p - u)⁻¹ := by
      intro u hu
      have hpu : p ≠ u := fun h => hpS (h ▸ hu)
      have hs : p - u ≠ 0 := sub_ne_zero.mpr hpu
      rw [dslope_of_ne _ hpu, slope_def_field]
      field_simp
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    ring
  have hHd : DifferentiableOn ℂ H (Ret z w) := by
    intro p hp
    have hpU := hK hp
    have h1 : DifferentiableAt ℂ (fun s => ∑ u ∈ S, (m u : ℂ) * dslope φ u s) p := by
      have : (fun s => ∑ u ∈ S, (m u : ℂ) * dslope φ u s) =
          ∑ u ∈ S, (fun s => (m u : ℂ) * dslope φ u s) := by
        funext s
        rw [Finset.sum_apply]
      rw [this]
      refine DifferentiableAt.sum fun u hu => ?_
      have huU : u ∈ U := hK ((hmemS u).mp hu).1
      have hD : DifferentiableOn ℂ (dslope φ u) U :=
        (differentiableOn_dslope (hU.mem_nhds huU)).mpr fun q hq => (hφ q hq).differentiableAt.differentiableWithinAt
      exact (differentiableAt_const _).mul (hD.differentiableAt (hU.mem_nhds hpU))
    have h2 : DifferentiableAt ℂ (logDeriv G) p := by
      have e : logDeriv G = fun s => deriv G s / G s := funext fun s => logDeriv_apply G s
      rw [e]
      exact (hGan p hpU).deriv.differentiableAt.div (hGan p hpU).differentiableAt (hGne p hp)
    exact (h1.add (h2.mul (hφ p hpU).differentiableAt)).differentiableWithinAt
  have hBR : Bordo z w ⊆ Ret z w := fun p hp => hp.1
  have hcont1 : ∀ u ∈ S, ContinuousOn (fun s => ((m u : ℂ) * φ u) * (s - u)⁻¹) (Bordo z w) := by
    intro u hu
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ (by fun_prop) fun p hp h => ?_)
    have hpu : p = u := sub_eq_zero.mp h
    exact hbd p hp (hpu ▸ ((hmemS u).mp hu).2)
  rw [bordo_congr hlogf, bordo_add (hHd.mono hBR).continuousOn (continuousOn_finsetSum S hcont1),
    bordo_cauchy hHd, zero_add, bordo_sum S (fun u s => ((m u : ℂ) * φ u) * (s - u)⁻¹) hcont1,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  obtain ⟨a1, a2, a3, a4⟩ := hint u hu
  rw [bordo_const_mul, bordo_inv a1 a2 a3 a4]
  ring

/-! ## 2. `G(s) = (s − 1)ζ(s)` -/

theorem Gp_analytic : AnalyticOnNhd ℂ Gp {s : ℂ | 0 < s.re} := by
  have hV : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hd : DifferentiableOn ℂ Gp {s : ℂ | 0 < s.re} := fun s hs => by
    have h0 : s ≠ 0 := fun h => by
      have : (0 : ℝ) < s.re := hs
      rw [h, zero_re] at this
      exact lt_irrefl 0 this
    exact (Gp_diff h0).differentiableWithinAt
  exact fun s hs => hd.analyticAt (hV.mem_nhds hs)

theorem zeta_analytic {u : ℂ} (h1 : u ≠ 1) : AnalyticAt ℂ riemannZeta u := by
  have hV : IsOpen {s : ℂ | s ≠ 1} := isOpen_ne
  have hd : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  exact hd.analyticAt (hV.mem_nhds h1)

/-- `ord_u G = ord_u ζ` em `Re u > 0`, `u ≠ 1`. -/
theorem ordem_Gp {u : ℂ} (h0 : 0 < u.re) (h1 : u ≠ 1) :
    analyticOrderAt Gp u = analyticOrderAt riemannZeta u := by
  have hU : IsOpen {s : ℂ | 0 < s.re ∧ s ≠ 1} :=
    (isOpen_lt continuous_const continuous_re).inter isOpen_ne
  have hev : Gp =ᶠ[𝓝 u] (fun s : ℂ => s - 1) * riemannZeta := by
    filter_upwards [hU.mem_nhds ⟨h0, h1⟩] with s hs
    exact Gp_eq hs.1 hs.2
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul (by fun_prop) (zeta_analytic h1)]
  have : analyticOrderAt (fun s : ℂ => s - 1) u = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (sub_ne_zero.mpr h1))
  rw [this, zero_add]

theorem Gp_eq_zero_iff {u : ℂ} (h0 : 0 < u.re) : Gp u = 0 ↔ riemannZeta u = 0 := by
  by_cases h1 : u = 1
  · subst h1
    have hG : Gp 1 ≠ 0 := by simpa using Gp_ne_zero (σ := 1) le_rfl
    exact ⟨fun h => absurd h hG, fun h => absurd h riemannZeta_one_ne_zero⟩
  · rw [Gp_eq h0 h1, mul_eq_zero]
    exact ⟨fun h => h.resolve_left (sub_ne_zero.mpr h1), Or.inr⟩

/-! ## 3. O resíduo explícito -/

/-- **`∮ x^s(−ζ′/ζ)(s)/s ds = 2πi (x − Σ_ρ m_ρ x^ρ/ρ)`** no retângulo `[b, c] × [−T, T]`, os zeros `ρ` de `ζ`
no retângulo. -/
theorem bordo_explicita {x b c T : ℝ} (hx : 0 < x) (hb : 0 < b) (hb1 : b < 1) (hc : 1 < c) (hT : 0 < T)
    (hbd : ∀ p ∈ Bordo ⟨b, -T⟩ ⟨c, T⟩, riemannZeta p ≠ 0) :
    ∃ S : Finset ℂ, (∀ u, u ∈ S ↔ u ∈ Ret ⟨b, -T⟩ ⟨c, T⟩ ∧ riemannZeta u = 0) ∧
      bordo (Fx x) ⟨b, -T⟩ ⟨c, T⟩ =
        2 * π * I * (x - ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) * px x u) := by
  set z : ℂ := ⟨b, -T⟩ with hz
  set w : ℂ := ⟨c, T⟩ with hw
  set U : Set ℂ := {s : ℂ | 0 < s.re} with hUdef
  have hU : IsOpen U := isOpen_lt continuous_const continuous_re
  have hRre : ∀ p ∈ Ret z w, b ≤ p.re := by
    intro p hp
    have h := (mem_reProdIm.mp hp).1
    change p.re ∈ [[b, c]] at h
    rw [uIcc_of_le (by linarith)] at h
    exact h.1
  have hK : Ret z w ⊆ U := fun p hp => lt_of_lt_of_le hb (hRre p hp)
  have hpxan : AnalyticOnNhd ℂ (px x) U := by
    have hd : DifferentiableOn ℂ (px x) U := fun p hp => (px_diff hx hp).differentiableWithinAt
    exact fun s hs => hd.analyticAt (hU.mem_nhds hs)
  have hne1 : ∀ p ∈ Bordo z w, p ≠ 1 := by
    rintro p ⟨_, h⟩ hp
    change p.re = b ∨ p.re = c ∨ p.im = -T ∨ p.im = T at h
    have hr : p.re = 1 := by rw [hp, one_re]
    have hi : p.im = 0 := by rw [hp, one_im]
    rcases h with h | h | h | h <;> linarith
  have htop : ∀ p ∈ Ret z w, analyticOrderAt Gp p ≠ ⊤ := by
    intro p hp
    have hp0 : 0 < p.re := hK hp
    by_cases h1 : p = 1
    · subst h1
      have hG : Gp 1 ≠ 0 := by simpa using Gp_ne_zero (σ := 1) le_rfl
      rw [analyticOrderAt_eq_zero.mpr (Or.inr hG)]
      simp
    · rw [ordem_Gp hp0 h1]
      exact ordem_zeta_finita hp0 h1
  have hbdG : ∀ p ∈ Bordo z w, Gp p ≠ 0 := fun p hp h =>
    hbd p hp ((Gp_eq_zero_iff (hK hp.1)).mp h)
  obtain ⟨S, hS, hpond⟩ := principio_ponderado hU Gp_analytic hpxan (z := z) (w := w)
    (by simp [hz, hw]; linarith) (by simp [hz, hw]; linarith) hK htop hbdG
  have hSm : ∀ u ∈ S, analyticOrderNatAt Gp u = analyticOrderNatAt riemannZeta u := by
    intro u hu
    obtain ⟨huR, hGu⟩ := (hS u).mp hu
    have hu1 : u ≠ 1 := by
      rintro rfl
      exact (by simpa using Gp_ne_zero (σ := 1) le_rfl : Gp 1 ≠ 0) hGu
    simp only [analyticOrderNatAt, ordem_Gp (hK huR) hu1]
  refine ⟨S, fun u => ?_, ?_⟩
  · rw [hS u]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (Gp_eq_zero_iff (hK h1)).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (Gp_eq_zero_iff (hK h1)).mpr h2⟩
  -- `F = −(G′/G)·φ + dslope φ 1 + φ(1)/(s − 1)` no bordo
  have hφd : DifferentiableOn ℂ (px x) U := fun p hp => (px_diff hx hp).differentiableWithinAt
  have h1U : (1 : ℂ) ∈ U := by show (0 : ℝ) < (1 : ℂ).re; simp
  have hD : DifferentiableOn ℂ (dslope (px x) 1) U :=
    (differentiableOn_dslope (hU.mem_nhds h1U)).mpr hφd
  have heq : EqOn (Fx x) (fun p => (-1 : ℂ) * (logDeriv Gp p * px x p) +
      (dslope (px x) 1 p + px x 1 * (p - 1)⁻¹)) (Bordo z w) := by
    intro p hp
    have hp1 := hne1 p hp
    have hp0 : 0 < p.re := hK hp.1
    have hpn : p ≠ 0 := fun h => by rw [h, zero_re] at hp0; exact lt_irrefl 0 hp0
    have hzp := hbd p hp
    simp only [Fx]
    rw [ATK.ZeroClasses.PNT.logDeriv_eq_Gp hp0 hp1 hzp, dslope_of_ne _ hp1, slope_def_field]
    have hs1 : p - 1 ≠ 0 := sub_ne_zero.mpr hp1
    unfold px
    field_simp
    ring
  have hBR : Bordo z w ⊆ Ret z w := fun p hp => hp.1
  have hlogc : ContinuousOn (fun p => logDeriv Gp p * px x p) (Bordo z w) := by
    intro p hp
    have hp0 : 0 < p.re := hK hp.1
    have hpn : p ≠ 0 := fun h => by rw [h, zero_re] at hp0; exact lt_irrefl 0 hp0
    have hl : ContinuousAt (logDeriv Gp) p := by
      have e : logDeriv Gp = fun z => deriv Gp z / Gp z := funext fun z => logDeriv_apply Gp z
      rw [e]
      exact (Gp_analytic p hp0).deriv.continuousAt.div (Gp_analytic p hp0).continuousAt (hbdG p hp)
    exact (hl.mul (px_diff hx hp0).continuousAt).continuousWithinAt
  have hc1 : ContinuousOn (fun p => (-1 : ℂ) * (logDeriv Gp p * px x p)) (Bordo z w) :=
    continuousOn_const.mul hlogc
  have hdc : ContinuousOn (dslope (px x) 1) (Bordo z w) :=
    (hD.mono (hBR.trans hK)).continuousOn
  have hic : ContinuousOn (fun p : ℂ => px x 1 * (p - 1)⁻¹) (Bordo z w) := fun p hp =>
    (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).inv₀
      (sub_ne_zero.mpr (hne1 p hp)))).continuousWithinAt
  have hc2 : ContinuousOn (fun p => dslope (px x) 1 p + px x 1 * (p - 1)⁻¹) (Bordo z w) := hdc.add hic
  rw [bordo_congr heq, bordo_add hc1 hc2, bordo_const_mul, hpond,
    bordo_add hdc hic, bordo_cauchy (hD.mono hK), bordo_const_mul,
    bordo_inv (z := z) (w := w) (u := 1) (by simp [hz]; linarith) (by simp [hw]; linarith)
      (by simp [hz]; linarith) (by simp [hw]; linarith), px_one]
  rw [Finset.sum_congr rfl (fun u hu => by rw [hSm u hu])]
  ring

/-! ## 4. `Σ_{|γ| ≤ T} m_ρ/|ρ| ≤ C (1 + log T)²` -/

theorem soma_harm (n : ℕ) : ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 + Real.log n := by
  have h := harmonic_le_one_add_log n
  have e : ((harmonic n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (1 : ℝ) / ((i : ℝ) + 1) := by
    simp [harmonic, Rat.cast_sum]
  rw [e] at h
  exact h

theorem Lc_bloco {k : ℕ} (hk : 1 ≤ k) :
    Lc |(k : ℝ) + 1 / 2| ≤ (a0 + Real.log 3 + Real.log ((k : ℝ) + 1)) / l0 := by
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [abs_of_pos (by linarith)]
  refine (Lc_le (by linarith)).trans (div_le_div_of_nonneg_right ?_ l0_pos.le)
  have h : Real.log (2 + ((k : ℝ) + 1 / 2)) ≤ Real.log 3 + Real.log ((k : ℝ) + 1) := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  linarith

/-- **`Σ_{ρ ∈ S} m_ρ/|ρ| ≤ C (1 + log T)²`** para todo conjunto finito `S` de zeros da faixa com `|γ| ≤ T`. -/
theorem soma_ordem_norm : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → ∀ S : Finset ℂ,
    (∀ u ∈ S, u ∈ ATK.ZetaSimetria.Z ∧ |u.im| ≤ T) →
    ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℝ) / ‖u‖ ≤ C * (1 + Real.log T) ^ 2 := by
  classical
  have hl0 := l0_pos
  have ha0 := one_le_a0
  have hl3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  set A := a0 + Real.log 3 + 1 with hA
  refine ⟨16 * A / l0, by positivity, fun T hT S hS => ?_⟩
  have hLT : 0 ≤ Real.log T := Real.log_nonneg hT
  set M := ⌊T⌋₊ with hM
  have hM1 : (M : ℝ) ≤ T := Nat.floor_le (by linarith)
  set κ : ℂ → ℕ := fun u => ⌊|u.im|⌋₊ with hκ
  have hκprop : ∀ u ∈ S, (κ u : ℝ) ≤ |u.im| ∧ |u.im| < κ u + 1 ∧ 13 ≤ κ u ∧ κ u ≤ M := by
    intro u hu
    obtain ⟨hz, hT'⟩ := hS u hu
    have h13 := ATK.ZeroClasses.Faixa.zeros_acima_13 u hz
    refine ⟨Nat.floor_le (abs_nonneg _), Nat.lt_floor_add_one _, ?_, Nat.floor_le_floor hT'⟩
    have : (13 : ℝ) ≤ |u.im| := h13.le
    exact Nat.le_floor (by exact_mod_cast this)
  -- o termo de cada bloco
  set g : ℕ → ℝ := fun k => 8 * (a0 + Real.log 3 + Real.log ((k : ℝ) + 1)) / (l0 * ((k : ℝ) + 1))
    with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => by
    have : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    simp only [hg]
    positivity
  have hbloco : ∀ k ∈ S.image κ, ∑ u ∈ S with κ u = k, (analyticOrderNatAt riemannZeta u : ℝ) / ‖u‖ ≤
      g k := by
    intro k hk
    obtain ⟨u₀, hu₀, hκ₀⟩ := Finset.mem_image.mp hk
    have hk13 : 13 ≤ k := hκ₀ ▸ (hκprop u₀ hu₀).2.2.1
    have hk1 : 1 ≤ k := by omega
    have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    set W := S.filter (fun u => κ u = k) with hW
    have hWp : ∀ u ∈ W, u ∈ S ∧ κ u = k := fun u hu => Finset.mem_filter.mp hu
    have hnorm : ∀ u ∈ W, (analyticOrderNatAt riemannZeta u : ℝ) / ‖u‖ ≤
        (analyticOrderNatAt riemannZeta u : ℝ) / k := by
      intro u hu
      obtain ⟨huS, hκu⟩ := hWp u hu
      have h1 := (hκprop u huS).1
      rw [hκu] at h1
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith) (h1.trans (abs_im_le_norm u))
    have hmais := caixa_le' (y := (k : ℝ) + 1 / 2) (W.filter (fun u => 0 < u.im)) (fun u hu => by
      rw [Finset.mem_filter] at hu
      obtain ⟨huS, hκu⟩ := hWp u hu.1
      obtain ⟨h1, h2, _, _⟩ := hκprop u huS
      rw [hκu, abs_of_pos hu.2] at h1 h2
      refine ⟨(hS u huS).1, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
    have hmenos := caixa_le' (y := -((k : ℝ) + 1 / 2)) (W.filter (fun u => ¬ 0 < u.im)) (fun u hu => by
      rw [Finset.mem_filter] at hu
      obtain ⟨huS, hκu⟩ := hWp u hu.1
      obtain ⟨h1, h2, _, _⟩ := hκprop u huS
      have h13 := ATK.ZeroClasses.Faixa.zeros_acima_13 u (hS u huS).1
      have hneg : u.im < 0 := by
        rcases lt_trichotomy u.im 0 with h | h | h
        · exact h
        · rw [h, abs_zero] at h13; norm_num at h13
        · exact absurd h hu.2
      rw [hκu, abs_of_neg hneg] at h1 h2
      refine ⟨(hS u huS).1, abs_le.mpr ⟨by linarith, by linarith⟩⟩)
    rw [abs_neg] at hmenos
    have hLc := Lc_bloco hk1
    have hsum : (∑ u ∈ W, (analyticOrderNatAt riemannZeta u : ℝ)) ≤
        4 * ((a0 + Real.log 3 + Real.log ((k : ℝ) + 1)) / l0) := by
      rw [← Finset.sum_filter_add_sum_filter_not W (fun u => 0 < u.im)]
      linarith
    calc ∑ u ∈ W, (analyticOrderNatAt riemannZeta u : ℝ) / ‖u‖
        ≤ ∑ u ∈ W, (analyticOrderNatAt riemannZeta u : ℝ) / k := Finset.sum_le_sum hnorm
      _ = (∑ u ∈ W, (analyticOrderNatAt riemannZeta u : ℝ)) / k := by rw [Finset.sum_div]
      _ ≤ 4 * ((a0 + Real.log 3 + Real.log ((k : ℝ) + 1)) / l0) / k :=
          div_le_div_of_nonneg_right hsum (by linarith)
      _ ≤ g k := by
          simp only [hg]
          have hpos : 0 ≤ a0 + Real.log 3 + Real.log ((k : ℝ) + 1) := by
            have : 0 ≤ Real.log ((k : ℝ) + 1) := Real.log_nonneg (by linarith)
            linarith
          have e : 4 * ((a0 + Real.log 3 + Real.log ((k : ℝ) + 1)) / l0) / k =
              (4 * (a0 + Real.log 3 + Real.log ((k : ℝ) + 1))) / (l0 * k) := by
            field_simp
          rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
          have : (k : ℝ) + 1 ≤ 2 * k := by linarith
          have hX := mul_nonneg hpos hl0.le
          have := mul_le_mul_of_nonneg_left this hX
          nlinarith
  rw [← Finset.sum_fiberwise_of_maps_to (fun u hu => Finset.mem_image_of_mem κ hu)]
  have hsub : S.image κ ⊆ Finset.range (M + 1) := by
    intro k hk
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hκprop u hu).2.2.2)
  have hLM : Real.log ((M : ℝ) + 1) ≤ 1 + Real.log T := by
    have h2T : (M : ℝ) + 1 ≤ 2 * T := by linarith
    have := Real.log_le_log (by positivity) h2T
    rw [Real.log_mul (by norm_num) (by linarith)] at this
    linarith
  calc ∑ k ∈ S.image κ, ∑ u ∈ S with κ u = k, (analyticOrderNatAt riemannZeta u : ℝ) / ‖u‖
      ≤ ∑ k ∈ S.image κ, g k := Finset.sum_le_sum hbloco
    _ ≤ ∑ k ∈ Finset.range (M + 1), g k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hg0 k
    _ ≤ ∑ k ∈ Finset.range (M + 1), 8 * A * (1 + Real.log T) / l0 * (1 / ((k : ℝ) + 1)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkM : (k : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have hlk : Real.log ((k : ℝ) + 1) ≤ 1 + Real.log T :=
          (Real.log_le_log (by positivity) (by linarith)).trans hLM
        simp only [hg]
        rw [mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have hpos : 0 ≤ l0 * ((k : ℝ) + 1) := by positivity
        have h1 : a0 + Real.log 3 + Real.log ((k : ℝ) + 1) ≤ A * (1 + Real.log T) := by
          rw [hA]
          nlinarith
        have := mul_le_mul_of_nonneg_right h1 hpos
        nlinarith
    _ = 8 * A * (1 + Real.log T) / l0 * ∑ k ∈ Finset.range (M + 1), (1 / ((k : ℝ) + 1)) := by
        rw [Finset.mul_sum]
    _ ≤ 8 * A * (1 + Real.log T) / l0 * (2 * (1 + Real.log T)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h := soma_harm (M + 1)
        push_cast at h
        linarith
    _ = 16 * A / l0 * (1 + Real.log T) ^ 2 := by ring

/-! ## 5. Alturas boas -/

theorem existe_q {ρ : ℂ} (hρ : ρ ∈ ATK.ZetaSimetria.Z) : ∃ q : ZM, rZ q = ρ := by
  have h0 := hρ.2.1
  have h1 : ρ ≠ 1 := by
    intro h
    have := hρ.2.2
    rw [h, one_re] at this
    exact lt_irrefl 1 this
  have htop := ordem_zeta_finita h0 h1
  have hord : 0 < analyticOrderNatAt riemannZeta ρ := by
    by_contra hlt
    have h0' : analyticOrderNatAt riemannZeta ρ = 0 := by omega
    exact ((ATK.ArgPrincipio.ordemNat_zero_iff (analyticOn_riemannZeta _ h1) htop).mp h0') hρ.1
  exact ⟨⟨⟨ρ, hρ⟩, ⟨0, hord⟩⟩, rfl⟩

theorem faixa_finito (R : ℝ) : {q : ZM | |(rZ q).im| ≤ R}.Finite := by
  have h := (summable_wz 0).tendsto_cofinite_zero
  have hpos : (0 : ℝ) < 1 / (1 + R ^ 2) := by positivity
  have hev : ∀ᶠ q in cofinite, wz 0 q < 1 / (1 + R ^ 2) := h.eventually (gt_mem_nhds hpos)
  refine (Filter.eventually_cofinite.mp hev).subset fun q hq => ?_
  simp only [Set.mem_ofPred_eq, not_lt] at hq ⊢
  unfold wz
  have hsq : (0 - (rZ q).im) ^ 2 ≤ R ^ 2 := by
    rw [zero_sub, neg_sq, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hq 2
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- **Alturas boas**: em cada `[T₀, T₀ + 1]` há `T` com `||γ| − T| ≥ δ` para todo zero, `δ⁻¹ = 2(n + 1)`,
`n = #{|γ| ∈ [T₀ − 1, T₀ + 2]}`. -/
theorem separa (T₀ : ℝ) : ∃ T : ℝ, T₀ ≤ T ∧ T ≤ T₀ + 1 ∧ ∃ n : ℕ,
    ((n : ℝ) ≤ 13 / 4 * (∑' q, wz (T₀ + 1 / 2) q + ∑' q, wz (-(T₀ + 1 / 2)) q)) ∧
    ∀ q : ZM, 1 / (2 * ((n : ℝ) + 1)) ≤ |T - (|(rZ q).im|)| := by
  classical
  set W : Finset ZM := (faixa_finito (T₀ + 2)).toFinset.filter (fun q => T₀ - 1 ≤ |(rZ q).im|) with hW
  have hmemW : ∀ q, q ∈ W ↔ T₀ - 1 ≤ |(rZ q).im| ∧ |(rZ q).im| ≤ T₀ + 2 := by
    intro q
    rw [hW, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  set n := W.card with hn
  -- a contagem
  have hcount : (n : ℝ) ≤ 13 / 4 * (∑' q, wz (T₀ + 1 / 2) q + ∑' q, wz (-(T₀ + 1 / 2)) q) := by
    have hge : ∀ q ∈ W, (4 / 13 : ℝ) ≤ wz (T₀ + 1 / 2) q + wz (-(T₀ + 1 / 2)) q := by
      intro q hq
      obtain ⟨h1, h2⟩ := (hmemW q).mp hq
      have hp := wz_pos (T₀ + 1 / 2) q
      have hm := wz_pos (-(T₀ + 1 / 2)) q
      rcases le_or_gt 0 (rZ q).im with hγ | hγ
      · rw [abs_of_nonneg hγ] at h1 h2
        have hw : (4 / 13 : ℝ) ≤ wz (T₀ + 1 / 2) q := by
          unfold wz
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          nlinarith
        linarith
      · rw [abs_of_neg hγ] at h1 h2
        have hw : (4 / 13 : ℝ) ≤ wz (-(T₀ + 1 / 2)) q := by
          unfold wz
          rw [div_le_div_iff₀ (by norm_num) (by positivity)]
          nlinarith
        linarith
    have hs := ((summable_wz (T₀ + 1 / 2)).add (summable_wz (-(T₀ + 1 / 2))))
    calc (n : ℝ) = 13 / 4 * ∑ q ∈ W, (4 / 13 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, hn]
          ring
      _ ≤ 13 / 4 * ∑ q ∈ W, (wz (T₀ + 1 / 2) q + wz (-(T₀ + 1 / 2)) q) := by
          gcongr with q hq
          exact hge q hq
      _ ≤ 13 / 4 * ∑' q, (wz (T₀ + 1 / 2) q + wz (-(T₀ + 1 / 2)) q) := by
          gcongr
          exact hs.sum_le_tsum _ fun q _ => by
            have := wz_pos (T₀ + 1 / 2) q
            have := wz_pos (-(T₀ + 1 / 2)) q
            positivity
      _ = 13 / 4 * (∑' q, wz (T₀ + 1 / 2) q + ∑' q, wz (-(T₀ + 1 / 2)) q) := by
          rw [(summable_wz _).tsum_add (summable_wz _)]
  -- os candidatos `T₀ + k/(n + 1)`
  set δ : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hδ
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set t : ℕ → ℝ := fun k => T₀ + k / ((n : ℝ) + 1) with ht
  set bloq : ZM → Finset ℕ := fun q => (Finset.range (n + 1)).filter (fun k => |t k - (|(rZ q).im|)| < δ)
    with hbloq
  have hbloq1 : ∀ q, (bloq q).card ≤ 1 := by
    intro q
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [hbloq, Finset.mem_filter] at ha hb
    by_contra hab
    have hd : (1 : ℝ) ≤ |(a : ℝ) - b| := by
      have : (a : ℤ) ≠ b := by exact_mod_cast hab
      have h1 : (1 : ℤ) ≤ |(a : ℤ) - b| := Int.one_le_abs (sub_ne_zero.mpr this)
      exact_mod_cast h1
    have htt : |t a - t b| < 2 * δ := by
      calc |t a - t b| = |(t a - |(rZ q).im|) - (t b - |(rZ q).im|)| := by ring_nf
        _ ≤ |t a - (|(rZ q).im|)| + |t b - (|(rZ q).im|)| := abs_sub _ _
        _ < δ + δ := add_lt_add ha.2 hb.2
        _ = 2 * δ := by ring
    have e : t a - t b = ((a : ℝ) - b) / ((n : ℝ) + 1) := by
      simp only [ht]
      ring
    rw [e, abs_div, abs_of_pos hn1, hδ] at htt
    rw [div_lt_iff₀ hn1] at htt
    have : 2 * (1 / (2 * ((n : ℝ) + 1))) * ((n : ℝ) + 1) = 1 := by field_simp
    linarith
  have hcardB : (W.biUnion bloq).card ≤ n := by
    calc (W.biUnion bloq).card ≤ ∑ q ∈ W, (bloq q).card := Finset.card_biUnion_le
      _ ≤ ∑ q ∈ W, 1 := Finset.sum_le_sum fun q _ => hbloq1 q
      _ = n := by rw [Finset.sum_const, smul_eq_mul, mul_one]
  obtain ⟨k, hk, hkB⟩ : ∃ k ∈ Finset.range (n + 1), k ∉ W.biUnion bloq := by
    by_contra hall
    push Not at hall
    have : Finset.range (n + 1) ⊆ W.biUnion bloq := fun k hk => hall k hk
    have := Finset.card_le_card this
    rw [Finset.card_range] at this
    omega
  have hkn : (k : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  refine ⟨t k, ?_, ?_, n, hcount, fun q => ?_⟩
  · simp only [ht]
    have : (0 : ℝ) ≤ k / ((n : ℝ) + 1) := by positivity
    linarith
  · simp only [ht]
    have : (k : ℝ) / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one hn1]; linarith
    linarith
  · by_cases hq : q ∈ W
    · by_contra hlt
      push Not at hlt
      apply hkB
      rw [Finset.mem_biUnion]
      exact ⟨q, hq, by simp only [hbloq, Finset.mem_filter]; exact ⟨hk, hlt⟩⟩
    · rw [hmemW, not_and_or, not_le, not_le] at hq
      have htk1 : T₀ ≤ t k := by
        simp only [ht]
        have : (0 : ℝ) ≤ k / ((n : ℝ) + 1) := by positivity
        linarith
      have htk2 : t k ≤ T₀ + 1 := by
        simp only [ht]
        have : (k : ℝ) / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one hn1]; linarith
        linarith
      have hδ1 : δ ≤ 1 / 2 := by
        rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      rcases hq with h | h
      · rw [abs_of_pos (by linarith)]
        linarith
      · rw [abs_of_neg (by linarith)]
        linarith

/-- **Alturas boas**: para todo `T₀ ≥ 6` existe `T ∈ [T₀, T₀ + 1]` com `ζ(σ ± iT) ≠ 0` e
`|ζ′/ζ(σ ± iT)| ≤ C log²(2 + T)` em `0 < σ ≤ 2`. -/
theorem altura_boa : ∃ C : ℝ, 0 ≤ C ∧ ∀ T₀ : ℝ, 6 ≤ T₀ → ∃ T : ℝ, T₀ ≤ T ∧ T ≤ T₀ + 1 ∧
    ∀ σ : ℝ, 0 < σ → σ ≤ 2 → ∀ τ : ℝ, (τ = T ∨ τ = -T) →
      riemannZeta ((σ : ℂ) + τ * I) ≠ 0 ∧
      ‖logDeriv riemannZeta ((σ : ℂ) + τ * I)‖ ≤ C * Real.log (2 + T) ^ 2 := by
  obtain ⟨Cw, hCw0, hCw⟩ := soma_wz_O
  obtain ⟨Cl, hCl0, hCl⟩ := zeta_local_O
  refine ⟨Cl + 52 * Cw ^ 2 + 4 * Cw, by positivity, fun T₀ hT₀ => ?_⟩
  obtain ⟨T, hT1, hT2, n, hn, hsep⟩ := separa T₀
  refine ⟨T, hT1, hT2, fun σ hσ0 hσ2 τ hτ => ?_⟩
  have hT6 : 6 ≤ T := by linarith
  have hτabs : |τ| = T := by
    rcases hτ with h | h <;> rw [h]
    · exact abs_of_pos (by linarith)
    · rw [abs_neg]; exact abs_of_pos (by linarith)
  set δ : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hsepτ : ∀ q : ZM, δ ≤ |τ - (rZ q).im| := fun q => by
    have h1 := abs_abs_sub_abs_le_abs_sub τ (rZ q).im
    rw [hτabs] at h1
    exact (hsep q).trans h1
  set s : ℂ := (σ : ℂ) + τ * I with hs
  have hsim : s.im = τ := by simp [hs]
  have hsre : s.re = σ := by simp [hs]
  -- `ζ(s) ≠ 0`
  have hz : riemannZeta s ≠ 0 := by
    intro h
    rcases le_or_gt 1 σ with h1 | h1
    · exact riemannZeta_ne_zero_of_one_le_re (by rw [hsre]; exact h1) h
    · have hZ : s ∈ ATK.ZetaSimetria.Z := ⟨h, by rw [hsre]; exact hσ0, by rw [hsre]; exact h1⟩
      obtain ⟨q, hq⟩ := existe_q hZ
      have := hsepτ q
      rw [hq, hsim, sub_self, abs_zero] at this
      linarith
  refine ⟨hz, ?_⟩
  set L := Real.log (2 + T) with hL
  have hL2 : 2 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by linarith)]
    have h := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]
    have h0 := (Real.exp_pos 1).le
    have h' : Real.exp 1 ≤ 2.72 := by linarith
    have := mul_le_mul h' h' h0 (by norm_num)
    norm_num at this
    linarith
  -- a contagem dos zeros próximos e a separação
  have hloc := hCl τ σ (by rw [hτabs]; exact hT6) hσ0 hσ2 hz
  rw [hτabs] at hloc
  have hcard : ((perto τ).card : ℝ) ≤ 2 * Cw * L := by
    have := card_perto_le τ
    have h2 := hCw τ
    rw [hτabs] at h2
    linarith
  have hlogT0 : Real.log (2 + |T₀ + 1 / 2|) ≤ 2 * L := by
    rw [abs_of_pos (by linarith)]
    have h1 : 2 + (T₀ + 1 / 2) ≤ 2 * (2 + T) := by linarith
    have h2 := Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) (by linarith)] at h2
    have h3 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hlogT0' : Real.log (2 + |-(T₀ + 1 / 2)|) ≤ 2 * L := by rw [abs_neg]; exact hlogT0
  have hinvδ : 1 / δ ≤ 26 * Cw * L + 2 := by
    rw [hδ, one_div_one_div]
    have h1 := hCw (T₀ + 1 / 2)
    have h2 := hCw (-(T₀ + 1 / 2))
    have h3 : (n : ℝ) ≤ 13 / 4 * (Cw * (2 * L) + Cw * (2 * L)) := by
      have a1 := mul_le_mul_of_nonneg_left hlogT0 hCw0
      have a2 := mul_le_mul_of_nonneg_left hlogT0' hCw0
      linarith
    linarith
  have hsum : ‖∑ q ∈ perto τ, 1 / (s - rZ q)‖ ≤ ((perto τ).card : ℝ) * (1 / δ) := by
    calc ‖∑ q ∈ perto τ, 1 / (s - rZ q)‖ ≤ ∑ q ∈ perto τ, ‖1 / (s - rZ q)‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ perto τ, 1 / δ := Finset.sum_le_sum fun q _ => by
          have h := abs_im_le_norm (s - rZ q)
          rw [sub_im, hsim] at h
          rw [norm_div, norm_one]
          exact one_div_le_one_div_of_le hδ0 ((hsepτ q).trans h)
      _ = ((perto τ).card : ℝ) * (1 / δ) := by rw [Finset.sum_const, nsmul_eq_mul]
  have htri : ‖logDeriv riemannZeta s‖ ≤
      ‖logDeriv riemannZeta s - ∑ q ∈ perto τ, 1 / (s - rZ q)‖ + ‖∑ q ∈ perto τ, 1 / (s - rZ q)‖ := by
    have := norm_add_le (logDeriv riemannZeta s - ∑ q ∈ perto τ, 1 / (s - rZ q))
      (∑ q ∈ perto τ, 1 / (s - rZ q))
    rwa [sub_add_cancel] at this
  have hc0 : (0 : ℝ) ≤ (perto τ).card := Nat.cast_nonneg _
  have hprod : ((perto τ).card : ℝ) * (1 / δ) ≤ 2 * Cw * L * (26 * Cw * L + 2) :=
    mul_le_mul hcard hinvδ (by positivity) (by positivity)
  have hLL : L ≤ L ^ 2 := by nlinarith
  have e : 2 * Cw * L * (26 * Cw * L + 2) = 52 * Cw ^ 2 * L ^ 2 + 4 * Cw * L := by ring
  have a1 := mul_le_mul_of_nonneg_left hLL hCl0
  have a2 := mul_le_mul_of_nonneg_left hLL (by positivity : (0 : ℝ) ≤ 4 * Cw)
  calc ‖logDeriv riemannZeta s‖ ≤ Cl * L + (52 * Cw ^ 2 * L ^ 2 + 4 * Cw * L) := by linarith
    _ ≤ (Cl + 52 * Cw ^ 2 + 4 * Cw) * L ^ 2 := by nlinarith

/-! ## 6. Sob RH, `ζ′/ζ` em `Re s = ¼` -/

/-- `ζ′/ζ` é limitada no compacto `¼ ≤ σ ≤ ¾`, `|t| ≤ 6`. -/
theorem compacto_quarto : ∃ M : ℝ, ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → |s.im| ≤ 6 →
    ‖logDeriv riemannZeta s‖ ≤ M := by
  set K : Set ℂ := (Icc (1 / 4 : ℝ) (3 / 4)) ×ℂ (Icc (-6 : ℝ) 6) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hmem : ∀ s ∈ K, s ≠ 1 ∧ riemannZeta s ≠ 0 := by
    intro s hs
    rw [hK, mem_reProdIm] at hs
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hs
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [h, one_re] at h2
      norm_num at h2
    · have hz : s ∈ ATK.ZetaSimetria.Z := ⟨h, by linarith, by linarith⟩
      have h13 := ATK.ZeroClasses.Faixa.zeros_acima_13 s hz
      have : |s.im| ≤ 6 := abs_le.mpr ⟨h3, h4⟩
      linarith
  have hV : IsOpen {p : ℂ | p ≠ 1} := isOpen_ne
  have hζd : DifferentiableOn ℂ riemannZeta {p : ℂ | p ≠ 1} := fun p hp =>
    (differentiableAt_riemannZeta hp).differentiableWithinAt
  have hdd : DifferentiableOn ℂ (deriv riemannZeta) {p : ℂ | p ≠ 1} := hζd.deriv hV
  have hcont : ContinuousOn (logDeriv riemannZeta) K := by
    intro s hs
    obtain ⟨hs1, hz⟩ := hmem s hs
    have e : logDeriv riemannZeta = fun z => deriv riemannZeta z / riemannZeta z :=
      funext fun z => logDeriv_apply _ z
    rw [e]
    exact ((hdd.differentiableAt (hV.mem_nhds hs1)).continuousAt.div
      (differentiableAt_riemannZeta hs1).continuousAt hz).continuousWithinAt
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hcont
  exact ⟨M, fun s h1 h2 h3 => hM s (by rw [hK, mem_reProdIm]; exact ⟨⟨h1, h2⟩, abs_le.mp h3⟩)⟩

/-- **Sob RH, `|ζ′/ζ(¼ + it)| ≤ C log(2 + |t|)`** para todo `t`. -/
theorem logDeriv_quarto_RH (hRH : RiemannHypothesis) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
    ‖logDeriv riemannZeta (((1 / 4 : ℝ) : ℂ) + t * I)‖ ≤ C * Real.log (2 + |t|) := by
  obtain ⟨Cl, hCl0, hCl⟩ := zeta_local_O
  obtain ⟨Cp, hCp0, hCp⟩ := card_perto_O
  obtain ⟨M, hM⟩ := compacto_quarto
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Cl + 4 * Cp + |M| / Real.log 2, by positivity, fun t => ?_⟩
  have hL2 : Real.log 2 ≤ Real.log (2 + |t|) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hL0 : 0 < Real.log (2 + |t|) := hl2.trans_le hL2
  set s : ℂ := (((1 / 4 : ℝ) : ℂ) + t * I) with hs
  have hsre : s.re = 1 / 4 := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have hMb : |M| ≤ |M| / Real.log 2 * Real.log (2 + |t|) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
    exact mul_le_mul_of_nonneg_left hL2 (abs_nonneg M)
  rcases le_or_gt 6 |t| with ht | ht
  · have hz : riemannZeta s ≠ 0 := by
      intro h
      have hZ : s ∈ ATK.ZetaSimetria.Z := ⟨h, by rw [hsre]; norm_num, by rw [hsre]; norm_num⟩
      have := re_de_RH hRH hZ
      rw [hsre] at this
      norm_num at this
    have hloc := hCl t (1 / 4) ht (by norm_num) (by norm_num) hz
    have hsum : ‖∑ q ∈ perto t, 1 / (s - rZ q)‖ ≤ ((perto t).card : ℝ) * 4 := by
      calc ‖∑ q ∈ perto t, 1 / (s - rZ q)‖ ≤ ∑ q ∈ perto t, ‖1 / (s - rZ q)‖ := norm_sum_le _ _
        _ ≤ ∑ q ∈ perto t, (4 : ℝ) := Finset.sum_le_sum fun q _ => by
            have hρ := re_de_RH hRH q.1.2
            have h := abs_re_le_norm (s - rZ q)
            rw [sub_re, hsre, hρ] at h
            norm_num at h
            rw [norm_div, norm_one, div_le_iff₀ (by linarith)]
            linarith
        _ = ((perto t).card : ℝ) * 4 := by rw [Finset.sum_const, nsmul_eq_mul]
    have htri : ‖logDeriv riemannZeta s‖ ≤
        ‖logDeriv riemannZeta s - ∑ q ∈ perto t, 1 / (s - rZ q)‖ + ‖∑ q ∈ perto t, 1 / (s - rZ q)‖ := by
      have := norm_add_le (logDeriv riemannZeta s - ∑ q ∈ perto t, 1 / (s - rZ q))
        (∑ q ∈ perto t, 1 / (s - rZ q))
      rwa [sub_add_cancel] at this
    have hc := hCp t
    have : 0 ≤ |M| / Real.log 2 * Real.log (2 + |t|) := by positivity
    have e : (Cl + 4 * Cp + |M| / Real.log 2) * Real.log (2 + |t|) =
        Cl * Real.log (2 + |t|) + 4 * (Cp * Real.log (2 + |t|)) + |M| / Real.log 2 * Real.log (2 + |t|) := by
      ring
    rw [e]
    linarith
  · have h := hM s hsre.ge (by rw [hsre]; norm_num) (by rw [hsim]; linarith)
    have a1 : 0 ≤ Cl * Real.log (2 + |t|) := by positivity
    have a2 : 0 ≤ 4 * Cp * Real.log (2 + |t|) := by positivity
    have e : (Cl + 4 * Cp + |M| / Real.log 2) * Real.log (2 + |t|) =
        Cl * Real.log (2 + |t|) + 4 * Cp * Real.log (2 + |t|) + |M| / Real.log 2 * Real.log (2 + |t|) := by
      ring
    rw [e]
    linarith [le_abs_self M]

end ATK.ZeroClasses.Explicita

#print axioms ATK.ZeroClasses.Explicita.principio_ponderado
#print axioms ATK.ZeroClasses.Explicita.Gp_analytic
#print axioms ATK.ZeroClasses.Explicita.zeta_analytic
#print axioms ATK.ZeroClasses.Explicita.ordem_Gp
#print axioms ATK.ZeroClasses.Explicita.Gp_eq_zero_iff
#print axioms ATK.ZeroClasses.Explicita.bordo_explicita
#print axioms ATK.ZeroClasses.Explicita.soma_harm
#print axioms ATK.ZeroClasses.Explicita.Lc_bloco
#print axioms ATK.ZeroClasses.Explicita.soma_ordem_norm
#print axioms ATK.ZeroClasses.Explicita.existe_q
#print axioms ATK.ZeroClasses.Explicita.faixa_finito
#print axioms ATK.ZeroClasses.Explicita.separa
#print axioms ATK.ZeroClasses.Explicita.altura_boa
#print axioms ATK.ZeroClasses.Explicita.compacto_quarto
#print axioms ATK.ZeroClasses.Explicita.logDeriv_quarto_RH
