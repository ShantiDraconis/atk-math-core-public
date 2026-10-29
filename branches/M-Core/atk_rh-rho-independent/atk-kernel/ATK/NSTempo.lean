import ATK.NSMild
import ATK.NSSuave

/-!
# ATK — Navier–Stokes: as derivadas temporais da solução branda

Camada 4 do ataque a B3. A solução branda `a(t, ξ)` de `ATK.NSMild.existe_branda` satisfaz, no
lado de Fourier, a EDO `∂ₜa = −κ(ξ) a − P(ξ) Nl(a, a)`, `κ(ξ) = 4π²ν‖ξ‖²`. Derivando de novo
(regra de Leibniz para o termo bilinear `Nl`), as derivadas temporais são

  `a₀ = a`,   `a_{k+1} = −κ a_k − P(ξ) Σ_{i ≤ k} C(k, i) Nl(a_i, a_{k−i})`   (`ader`).

Aqui:

* `BoaW`: amplitudes contínuas em `ℝ × ℝ³` com todas as cotas `C_m w_m⁻¹`; estável por soma,
  por `κ` e por `P(ξ) Nl` (`BoaW.lpNl`);
* **regra do produto para `Nl`** (`Nl_integral`): se `f t = f 0 + ∫₀ᵗ f'` e `g t = g 0 + ∫₀ᵗ g'`
  pontualmente, então `Nl(f t, g t) = Nl(f 0, g 0) + ∫₀ᵗ (Nl(f', g) + Nl(f, g'))` (Fubini);
* **a EDO na forma integral** a partir da forma branda (`ader_zero_integral`);
* **`amp_ader`**: a sequência `ader` é uma amplitude suave (`ATK.NSSuave.Amp`) em `[0, T]`.

Nada aqui conclui B3; **CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology Finset
open scoped Real

namespace ATK.NSTempo

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSPicard ATK.NSSuave

/-! ### Amplitudes boas em todos os pesos -/

/-- Contínua em `ℝ × ℝ³` com `‖f t ξ‖ ≤ C_m w_m(ξ)⁻¹` para todo `m`. -/
structure BoaW (f : ℝ → E3 → C3) : Prop where
  cont : Continuous fun p : ℝ × E3 => f p.1 p.2
  bound : ∀ m : ℕ, ∃ C, 0 ≤ C ∧ ∀ t ξ, ‖f t ξ‖ ≤ C * (w m ξ)⁻¹

theorem BoaW.boa4 {f : ℝ → E3 → C3} (h : BoaW f) : ∃ A, Boa4 f A := by
  obtain ⟨A, -, hA⟩ := h.bound 4
  exact ⟨A, h.cont, hA⟩

theorem BoaW.cont_s {f : ℝ → E3 → C3} (h : BoaW f) (s : ℝ) : Continuous (f s) :=
  h.cont.comp (continuous_const.prodMk continuous_id)

theorem BoaW.cont_t {f : ℝ → E3 → C3} (h : BoaW f) (ξ : E3) : Continuous fun t => f t ξ :=
  h.cont.comp (continuous_id.prodMk continuous_const)

theorem BoaW.bound_le {f : ℝ → E3 → C3} (h : BoaW f) (m : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ t ξ, ∀ n ≤ m, ‖f t ξ‖ ≤ C * (w n ξ)⁻¹ := by
  obtain ⟨C, hC0, hC⟩ := h.bound m
  exact ⟨C, hC0, fun t ξ n hn => (hC t ξ).trans (mul_le_mul_of_nonneg_left (w_inv_anti hn ξ) hC0)⟩

theorem BoaW.add {f g : ℝ → E3 → C3} (hf : BoaW f) (hg : BoaW g) :
    BoaW fun t ξ => f t ξ + g t ξ where
  cont := hf.cont.add hg.cont
  bound m := by
    obtain ⟨A, hA0, hA⟩ := hf.bound m
    obtain ⟨B, hB0, hB⟩ := hg.bound m
    refine ⟨A + B, add_nonneg hA0 hB0, fun t ξ => ?_⟩
    calc ‖f t ξ + g t ξ‖ ≤ ‖f t ξ‖ + ‖g t ξ‖ := norm_add_le _ _
      _ ≤ A * (w m ξ)⁻¹ + B * (w m ξ)⁻¹ := add_le_add (hA t ξ) (hB t ξ)
      _ = (A + B) * (w m ξ)⁻¹ := by ring

theorem BoaW.neg {f : ℝ → E3 → C3} (hf : BoaW f) : BoaW fun t ξ => -f t ξ where
  cont := hf.cont.neg
  bound m := by
    obtain ⟨A, hA0, hA⟩ := hf.bound m
    exact ⟨A, hA0, fun t ξ => by rw [norm_neg]; exact hA t ξ⟩

theorem BoaW.sub {f g : ℝ → E3 → C3} (hf : BoaW f) (hg : BoaW g) :
    BoaW fun t ξ => f t ξ - g t ξ := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem BoaW.nsmul {f : ℝ → E3 → C3} (hf : BoaW f) (n : ℕ) : BoaW fun t ξ => n • f t ξ where
  cont := hf.cont.const_smul n
  bound m := by
    obtain ⟨A, hA0, hA⟩ := hf.bound m
    refine ⟨n * A, by positivity, fun t ξ => ?_⟩
    rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hA t ξ) (Nat.cast_nonneg n)

theorem BoaW.zero : BoaW fun (_ : ℝ) (_ : E3) => (0 : C3) where
  cont := continuous_const
  bound m := ⟨0, le_rfl, fun t ξ => by simp⟩

theorem BoaW.sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → E3 → C3} (hf : ∀ i ∈ s, BoaW (f i)) :
    BoaW fun t ξ => ∑ i ∈ s, f i t ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BoaW.zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (mem_insert_self i s)).add (ih fun j hj => hf j (mem_insert_of_mem hj))

/-- `κ(ξ) = 4π²ν‖ξ‖²`. -/
noncomputable def kappa (ν : ℝ) (ξ : E3) : ℝ := 4 * π ^ 2 * ν * ‖ξ‖ ^ 2

theorem continuous_kappa (ν : ℝ) : Continuous (kappa ν) := by unfold kappa; fun_prop

theorem norm_kappa_le (ν : ℝ) (ξ : E3) : ‖((kappa ν ξ : ℝ) : ℂ)‖ ≤ 4 * π ^ 2 * |ν| * w 2 ξ := by
  rw [Complex.norm_real, Real.norm_eq_abs, kappa]
  have h1 : |4 * π ^ 2 * ν * ‖ξ‖ ^ 2| = 4 * π ^ 2 * |ν| * ‖ξ‖ ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
      abs_of_nonneg (sq_nonneg π), abs_of_nonneg (sq_nonneg ‖ξ‖)]
  rw [h1]
  exact mul_le_mul_of_nonneg_left (norm_sq_le_w2 ξ) (by positivity)

theorem BoaW.mulKappa {f : ℝ → E3 → C3} (hf : BoaW f) (ν : ℝ) :
    BoaW fun t ξ => ((kappa ν ξ : ℝ) : ℂ) • f t ξ where
  cont := ((Complex.continuous_ofReal.comp ((continuous_kappa ν).comp continuous_snd))).smul hf.cont
  bound m := by
    obtain ⟨A, hA0, hA⟩ := hf.bound (m + 2)
    refine ⟨4 * π ^ 2 * |ν| * A, by positivity, fun t ξ => ?_⟩
    rw [norm_smul]
    calc ‖((kappa ν ξ : ℝ) : ℂ)‖ * ‖f t ξ‖ ≤ (4 * π ^ 2 * |ν| * w 2 ξ) * (A * (w (m + 2) ξ)⁻¹) :=
          mul_le_mul (norm_kappa_le ν ξ) (hA t ξ) (norm_nonneg _) (by have := w_pos 2 ξ; positivity)
      _ = 4 * π ^ 2 * |ν| * A * (w m ξ)⁻¹ := by
          rw [w_add]; have := w_pos m ξ; have := w_pos 2 ξ; field_simp

/-- Cota com pesos de `Nl`. -/
theorem norm_Nl_le_w {f g : E3 → C3} (hf : Continuous f) (hg : Continuous g) (m : ℕ)
    {A A' B B' : ℝ} (hA : ∀ η, ‖f η‖ ≤ A * (w 4 η)⁻¹) (hA' : ∀ η, ‖f η‖ ≤ A' * (w (m + 1) η)⁻¹)
    (hB : ∀ η, ‖g η‖ ≤ B * (w 4 η)⁻¹) (hB' : ∀ η, ‖g η‖ ≤ B' * (w (m + 1) η)⁻¹) (ξ : E3) :
    ‖Nl f g ξ‖ ≤ (2 * π * (2 ^ (m + 1) * I4 * (A' * B + A * B'))) * (w m ξ)⁻¹ := by
  have hB1 : ∀ η, ‖g η‖ ≤ B := fun η => (hB η).trans (by
    have hB0 : 0 ≤ B := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hB 0))
      (inv_pos.mpr (w_pos 4 0))
    exact mul_le_of_le_one_right hB0 (inv_le_one_of_one_le₀ (one_le_w 4 η)))
  have hint := integrable_convN hf hg hA hB1 ξ
  have hc := convN_peso (m + 1) hf hg hA hA' hB hB' ξ
  have hw := w_pos (m + 1) ξ
  have hcn : 0 ≤ convN f g ξ := integral_nonneg fun η => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  refine (norm_Nl_le ξ hint).trans ?_
  have h1 : ‖ξ‖ * convN f g ξ ≤ (2 ^ (m + 1) * I4 * (A' * B + A * B')) * (w m ξ)⁻¹ := by
    have e : w (m + 1) ξ = w m ξ * w 1 ξ := w_add m 1 ξ
    have hcm : convN f g ξ ≤ (2 ^ (m + 1) * I4 * (A' * B + A * B')) * (w (m + 1) ξ)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hw, mul_comm]; exact hc
    calc ‖ξ‖ * convN f g ξ ≤ w 1 ξ * ((2 ^ (m + 1) * I4 * (A' * B + A * B')) * (w (m + 1) ξ)⁻¹) :=
          mul_le_mul (norm_le_w1 ξ) hcm hcn (w_pos 1 ξ).le
      _ = (2 ^ (m + 1) * I4 * (A' * B + A * B')) * (w m ξ)⁻¹ := by
          rw [e]; have := w_pos m ξ; have := w_pos 1 ξ; field_simp
  calc 2 * π * ‖ξ‖ * convN f g ξ = 2 * π * (‖ξ‖ * convN f g ξ) := by ring
    _ ≤ 2 * π * ((2 ^ (m + 1) * I4 * (A' * B + A * B')) * (w m ξ)⁻¹) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

theorem BoaW.nl {f g : ℝ → E3 → C3} (hf : BoaW f) (hg : BoaW g) :
    BoaW fun t ξ => Nl (f t) (g t) ξ where
  cont := by
    obtain ⟨A, hA⟩ := hf.boa4
    obtain ⟨B, hB⟩ := hg.boa4
    exact continuous_Nl hA hB
  bound m := by
    obtain ⟨A, hA0, hA⟩ := hf.bound_le (max 4 (m + 1))
    obtain ⟨B, hB0, hB⟩ := hg.bound_le (max 4 (m + 1))
    refine ⟨2 * π * (2 ^ (m + 1) * I4 * (A * B + A * B)), by have := I4_nonneg; positivity,
      fun t ξ => ?_⟩
    exact norm_Nl_le_w (hf.cont_s t) (hg.cont_s t) m (fun η => hA t η 4 (le_max_left _ _))
      (fun η => hA t η (m + 1) (le_max_right _ _)) (fun η => hB t η 4 (le_max_left _ _))
      (fun η => hB t η (m + 1) (le_max_right _ _)) ξ

theorem BoaW.lpNl {f g : ℝ → E3 → C3} (hf : BoaW f) (hg : BoaW g) :
    BoaW fun t ξ => lp ξ (Nl (f t) (g t) ξ) where
  cont := by
    obtain ⟨A, hA⟩ := hf.boa4
    obtain ⟨B, hB⟩ := hg.boa4
    exact continuous_lpNl hA hB
  bound m := by
    obtain ⟨C, hC0, hC⟩ := (hf.nl hg).bound m
    exact ⟨C, hC0, fun t ξ => (norm_lp_le _ _).trans (hC t ξ)⟩

/-! ### O projetor de Leray como aplicação linear contínua -/

/-- `P(ξ)` como aplicação `ℂ`-linear contínua. -/
noncomputable def lpL (ξ : E3) : C3 →L[ℂ] C3 :=
  ContinuousLinearMap.id ℂ C3 -
    (((‖ξ‖ ^ 2 : ℝ) : ℂ)⁻¹ • (innerSL ℂ (cpx ξ)).smulRight (cpx ξ))

theorem lpL_apply (ξ : E3) (v : C3) : lpL ξ v = lp ξ v := by
  simp only [lpL, lp, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    smul_smul, div_eq_inv_mul]

theorem lp_integral (ξ : E3) {g : ℝ → C3} {a b : ℝ} (hg : IntervalIntegrable g volume a b) :
    lp ξ (∫ s in a..b, g s) = ∫ s in a..b, lp ξ (g s) := by
  rw [← lpL_apply, ← (lpL ξ).intervalIntegral_comp_comm hg]
  simp only [lpL_apply]

/-! ### Derivadas a partir da forma integral -/

/-- Se `f t = f 0 + ∫₀ᵗ f'` em `[0, T]` com `f'` contínua, `f` tem derivada `f'` no interior. -/
theorem hasDerivAt_of_integral {T : ℝ} {f f' : ℝ → C3} (hf' : Continuous f')
    (hfd : ∀ t ∈ Icc 0 T, f t = f 0 + ∫ s in (0 : ℝ)..t, f' s) {s : ℝ} (hs : s ∈ Ioo 0 T) :
    HasDerivAt f (f' s) s := by
  have h1 : HasDerivAt (fun r => f 0 + ∫ u in (0 : ℝ)..r, f' u) (f' s) s := by
    have := intervalIntegral.integral_hasDerivAt_right (hf'.intervalIntegrable 0 s)
      (hf'.stronglyMeasurableAtFilter _ _) hf'.continuousAt
    simpa using this.const_add (f 0)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hs.1 hs.2] with r hr
  exact hfd r hr

/-- **Regra do produto para `Nl` na forma integral.** -/
theorem Nl_integral {T : ℝ} {f f' g g' : ℝ → E3 → C3} (hf : BoaW f) (hf' : BoaW f')
    (hg : BoaW g) (hg' : BoaW g')
    (hfd : ∀ η, ∀ t ∈ Icc 0 T, f t η = f 0 η + ∫ s in (0 : ℝ)..t, f' s η)
    (hgd : ∀ η, ∀ t ∈ Icc 0 T, g t η = g 0 η + ∫ s in (0 : ℝ)..t, g' s η)
    (ξ : E3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Nl (f t) (g t) ξ = Nl (f 0) (g 0) ξ +
      ∫ s in (0 : ℝ)..t, (Nl (f' s) (g s) ξ + Nl (f s) (g' s) ξ) := by
  -- integrandos
  set P : ℝ → E3 → C3 := fun s η => inner ℂ (cpx ξ) (f s η) • g s (ξ - η) with hP
  set P' : ℝ → E3 → C3 := fun s η => inner ℂ (cpx ξ) (f' s η) • g s (ξ - η) +
    inner ℂ (cpx ξ) (f s η) • g' s (ξ - η) with hP'
  have hcP' : Continuous fun q : ℝ × E3 => P' q.1 q.2 := by
    have c1 := hf.cont; have c2 := hf'.cont; have c3 := hg.cont; have c4 := hg'.cont
    have e1 : Continuous fun q : ℝ × E3 => g q.1 (ξ - q.2) :=
      c3.comp (continuous_fst.prodMk (continuous_const.sub continuous_snd))
    have e2 : Continuous fun q : ℝ × E3 => g' q.1 (ξ - q.2) :=
      c4.comp (continuous_fst.prodMk (continuous_const.sub continuous_snd))
    exact ((Continuous.inner (𝕜 := ℂ) (continuous_const (y := cpx ξ)) c2).smul e1).add
      ((Continuous.inner (𝕜 := ℂ) (continuous_const (y := cpx ξ)) c1).smul e2)
  -- cotas
  obtain ⟨A, hA0, hA⟩ := hf.bound 4
  obtain ⟨A', hA'0, hA'⟩ := hf'.bound 4
  obtain ⟨B, hB0, hB⟩ := hg.bound 0
  obtain ⟨B', hB'0, hB'⟩ := hg'.bound 0
  have hw0 : ∀ η, (w 0 η)⁻¹ = 1 := fun η => by simp [w]
  have hbP' : ∀ s η, ‖P' s η‖ ≤ ‖ξ‖ * (A' * B + A * B') * (w 4 η)⁻¹ := by
    intro s η
    have h1 : ‖inner ℂ (cpx ξ) (f' s η) • g s (ξ - η)‖ ≤ ‖ξ‖ * (A' * (w 4 η)⁻¹) * B := by
      rw [norm_smul]
      refine mul_le_mul ((norm_inner_cpx_le _ _).trans (mul_le_mul_of_nonneg_left (hA' s η)
        (norm_nonneg _))) ?_ (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (mul_nonneg hA'0 (inv_pos.mpr (w_pos 4 η)).le))
      simpa [hw0] using hB s (ξ - η)
    have h2 : ‖inner ℂ (cpx ξ) (f s η) • g' s (ξ - η)‖ ≤ ‖ξ‖ * (A * (w 4 η)⁻¹) * B' := by
      rw [norm_smul]
      refine mul_le_mul ((norm_inner_cpx_le _ _).trans (mul_le_mul_of_nonneg_left (hA s η)
        (norm_nonneg _))) ?_ (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (mul_nonneg hA0 (inv_pos.mpr (w_pos 4 η)).le))
      simpa [hw0] using hB' s (ξ - η)
    calc ‖P' s η‖ ≤ ‖inner ℂ (cpx ξ) (f' s η) • g s (ξ - η)‖ +
          ‖inner ℂ (cpx ξ) (f s η) • g' s (ξ - η)‖ := norm_add_le _ _
      _ ≤ ‖ξ‖ * (A' * (w 4 η)⁻¹) * B + ‖ξ‖ * (A * (w 4 η)⁻¹) * B' := add_le_add h1 h2
      _ = ‖ξ‖ * (A' * B + A * B') * (w 4 η)⁻¹ := by ring
  have hbP : ∀ s η, ‖P s η‖ ≤ ‖ξ‖ * (A * B) * (w 4 η)⁻¹ := by
    intro s η
    rw [hP]; simp only
    rw [norm_smul]
    calc ‖inner ℂ (cpx ξ) (f s η)‖ * ‖g s (ξ - η)‖ ≤ (‖ξ‖ * (A * (w 4 η)⁻¹)) * B :=
          mul_le_mul ((norm_inner_cpx_le _ _).trans (mul_le_mul_of_nonneg_left (hA s η)
            (norm_nonneg _))) (by simpa [hw0] using hB s (ξ - η)) (norm_nonneg _)
            (mul_nonneg (norm_nonneg _) (mul_nonneg hA0 (inv_pos.mpr (w_pos 4 η)).le))
      _ = ‖ξ‖ * (A * B) * (w 4 η)⁻¹ := by ring
  have hcPs : ∀ s, Continuous (P s) := by
    intro s
    exact (Continuous.inner (𝕜 := ℂ) (continuous_const (y := cpx ξ)) (hf.cont_s s)).smul
      ((hg.cont_s s).comp (continuous_const.sub continuous_id))
  have hintP : ∀ s, Integrable (P s) := fun s =>
    ((integrable_w_inv.const_mul (‖ξ‖ * (A * B)))).mono' (hcPs s).aestronglyMeasurable
      (Eventually.of_forall (hbP s))
  have hintP'1 : ∀ s, Integrable fun η => inner ℂ (cpx ξ) (f' s η) • g s (ξ - η) := by
    intro s
    refine (integrable_w_inv.const_mul (‖ξ‖ * A' * B)).mono' ?_ (Eventually.of_forall fun η => ?_)
    · exact ((Continuous.inner (𝕜 := ℂ) (continuous_const (y := cpx ξ)) (hf'.cont_s s)).smul
        ((hg.cont_s s).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · rw [norm_smul]
      calc ‖inner ℂ (cpx ξ) (f' s η)‖ * ‖g s (ξ - η)‖ ≤ (‖ξ‖ * (A' * (w 4 η)⁻¹)) * B :=
            mul_le_mul ((norm_inner_cpx_le _ _).trans (mul_le_mul_of_nonneg_left (hA' s η)
              (norm_nonneg _))) (by simpa [hw0] using hB s (ξ - η)) (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (mul_nonneg hA'0 (inv_pos.mpr (w_pos 4 η)).le))
        _ = ‖ξ‖ * A' * B * (w 4 η)⁻¹ := by ring
  have hintP'2 : ∀ s, Integrable fun η => inner ℂ (cpx ξ) (f s η) • g' s (ξ - η) := by
    intro s
    refine (integrable_w_inv.const_mul (‖ξ‖ * A * B')).mono' ?_ (Eventually.of_forall fun η => ?_)
    · exact ((Continuous.inner (𝕜 := ℂ) (continuous_const (y := cpx ξ)) (hf.cont_s s)).smul
        ((hg'.cont_s s).comp (continuous_const.sub continuous_id))).aestronglyMeasurable
    · rw [norm_smul]
      calc ‖inner ℂ (cpx ξ) (f s η)‖ * ‖g' s (ξ - η)‖ ≤ (‖ξ‖ * (A * (w 4 η)⁻¹)) * B' :=
            mul_le_mul ((norm_inner_cpx_le _ _).trans (mul_le_mul_of_nonneg_left (hA s η)
              (norm_nonneg _))) (by simpa [hw0] using hB' s (ξ - η)) (norm_nonneg _)
              (mul_nonneg (norm_nonneg _) (mul_nonneg hA0 (inv_pos.mpr (w_pos 4 η)).le))
        _ = ‖ξ‖ * A * B' * (w 4 η)⁻¹ := by ring
  -- passo 1: identidade pontual em `η`
  have hpt : ∀ η, P t η - P 0 η = ∫ s in (0 : ℝ)..t, P' s η := by
    intro η
    have hderiv : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => P r η) (P' s η) s := by
      intro s hs
      have hsT : s ∈ Ioo 0 T := ⟨hs.1, hs.2.trans_le ht.2⟩
      have d1 := hasDerivAt_of_integral (hf'.cont_t η) (hfd η) hsT
      have d2 := hasDerivAt_of_integral (hg'.cont_t (ξ - η)) (hgd (ξ - η)) hsT
      have d3 : HasDerivAt (fun r => inner ℂ (cpx ξ) (f r η)) (inner ℂ (cpx ξ) (f' s η)) s := by
        exact ((((innerSL ℂ (cpx ξ)).restrictScalars ℝ)).hasFDerivAt (x := f s η)).comp_hasDerivAt
          s d1
      have := d3.smul d2
      have e : P' s η = inner ℂ (cpx ξ) (f s η) • g' s (ξ - η) +
          inner ℂ (cpx ξ) (f' s η) • g s (ξ - η) := by
        simp only [hP']; abel
      rw [e]
      exact this
    have hPc : ContinuousOn (fun r => P r η) (Icc 0 t) :=
      (Continuous.smul (Continuous.inner (𝕜 := ℂ) (continuous_const (y := cpx ξ)) (hf.cont_t η))
        (hg.cont_t (ξ - η))).continuousOn
    have hP'i : IntervalIntegrable (fun s => P' s η) volume 0 t :=
      (hcP'.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 t
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun r => P r η)
      (f' := fun s => P' s η) ht.1 hPc hderiv hP'i
    exact this.symm
  -- passo 2: Fubini
  have hswap : ∫ s in (0 : ℝ)..t, ∫ η, P' s η = ∫ η, ∫ s in (0 : ℝ)..t, P' s η := by
    refine MeasureTheory.intervalIntegral_integral_swap ?_
    have hK : Integrable (fun q : ℝ × E3 => (1 : ℝ) * (‖ξ‖ * (A' * B + A * B') * (w 4 q.2)⁻¹))
        ((volume.restrict (uIoc 0 t)).prod volume) := by
      refine Integrable.mul_prod (f := fun _ : ℝ => (1 : ℝ)) ?_ (integrable_w_inv.const_mul _)
      rw [uIoc_of_le ht.1]
      exact (continuous_const.integrableOn_Icc (a := 0) (b := t)).mono_set Ioc_subset_Icc_self
    refine hK.mono' hcP'.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
    rw [one_mul]
    exact hbP' q.1 q.2
  have hsplit : ∀ s, ∫ η, P' s η =
      (∫ η, inner ℂ (cpx ξ) (f' s η) • g s (ξ - η)) +
        ∫ η, inner ℂ (cpx ξ) (f s η) • g' s (ξ - η) := fun s =>
    integral_add (hintP'1 s) (hintP'2 s)
  -- conclusão
  have hc : ((2 * π : ℝ) * Complex.I : ℂ) • ∫ s in (0 : ℝ)..t, ∫ η, P' s η =
      ∫ s in (0 : ℝ)..t, (Nl (f' s) (g s) ξ + Nl (f s) (g' s) ξ) := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hsplit, Nl, smul_add]
  rw [← hc, hswap, ← integral_congr_ae (Eventually.of_forall hpt), integral_sub (hintP t)
    (hintP 0), smul_sub]
  simp only [Nl, hP]
  abel

/-! ### A EDO a partir da forma branda -/

theorem heat_sub (ν t s : ℝ) (ξ : E3) : heat ν (t - s) ξ = heat ν t ξ * heat ν (-s) ξ := by
  unfold heat
  rw [← Real.exp_add]
  ring_nf

theorem hasDerivAt_heat (ν : ℝ) (ξ : E3) (t : ℝ) :
    HasDerivAt (fun t => heat ν t ξ) (-kappa ν ξ * heat ν t ξ) t := by
  unfold heat kappa
  have := ((hasDerivAt_id t).const_mul (-(4 * π ^ 2 * ν * ‖ξ‖ ^ 2))).exp
  convert this using 1
  · ext r; simp only [id_eq, neg_mul]
  · simp only [id, mul_one]; ring_nf

/-- **A EDO na forma integral**: se `a` é a solução branda em `[0, T]` com `g(s) = P Nl(a, a)`,
então `a t = a 0 + ∫₀ᵗ (−κ a − g)`. -/
theorem edo_integral {ν T : ℝ} {a₀ : E3 → C3} {a : ℝ → E3 → C3} (ha : BoaW a)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a₀ ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ)
    (ξ : E3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    a t ξ = a 0 ξ + ∫ s in (0 : ℝ)..t,
      (-((kappa ν ξ : ℝ) : ℂ) • a s ξ - lp ξ (Nl (a s) (a s) ξ)) := by
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  set g : ℝ → C3 := fun s => lp ξ (Nl (a s) (a s) ξ) with hg
  have hgc : Continuous g := by
    have := (ha.lpNl ha).cont
    exact Continuous.comp (g := fun p : ℝ × E3 => lp p.2 (Nl (a p.1) (a p.1) p.2))
      (f := fun s : ℝ => (s, ξ)) this (continuous_id.prodMk continuous_const)
  set G : ℝ → C3 := fun s => heat ν (-s) ξ • g s with hG
  have hGc : Continuous G := by
    have : Continuous fun s => heat ν (-s) ξ := by unfold heat; fun_prop
    exact this.smul hgc
  set F : ℝ → C3 := fun r => heat ν r ξ • (a₀ ξ - ∫ s in (0 : ℝ)..r, G s) with hF
  have hFa : ∀ r ∈ Icc 0 T, a r ξ = F r := by
    intro r hr
    rw [hmild r hr ξ, hF]
    simp only
    rw [smul_sub]
    congr 1
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [duhI, hG, smul_smul, ← heat_sub]
    rfl
  have hFd : ∀ r, HasDerivAt F (-((kappa ν ξ : ℝ) : ℂ) • F r - g r) r := by
    intro r
    have h1 := hasDerivAt_heat ν ξ r
    have h2 : HasDerivAt (fun r => a₀ ξ - ∫ s in (0 : ℝ)..r, G s) (-G r) r := by
      have := intervalIntegral.integral_hasDerivAt_right (hGc.intervalIntegrable 0 r)
        (hGc.stronglyMeasurableAtFilter _ _) hGc.continuousAt
      simpa using this.const_sub (a₀ ξ)
    have h3 : HasDerivAt F (heat ν r ξ • (-G r) +
        (-kappa ν ξ * heat ν r ξ) • (a₀ ξ - ∫ s in (0 : ℝ)..r, G s)) r := h1.smul h2
    refine h3.congr_deriv ?_
    have hh : heat ν r ξ * heat ν (-r) ξ = 1 := by rw [← heat_sub, sub_self, heat_zero]
    have e1 : heat ν r ξ • (-G r) = -g r := by
      simp only [hG, smul_neg, smul_smul, hh, one_smul]
    have e2 : (-kappa ν ξ * heat ν r ξ) • (a₀ ξ - ∫ s in (0 : ℝ)..r, G s) =
        -((kappa ν ξ : ℝ) : ℂ) • F r := by
      simp only [hF, neg_mul, neg_smul, Complex.coe_smul, smul_smul]
    rw [e1, e2]
    abel
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun r => (hFd r).continuousAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hFd r)
    ((((Complex.continuous_ofReal.comp (continuous_const (y := kappa ν ξ))).neg.smul hFc).sub
      hgc).intervalIntegrable 0 t)
  have hcongr : ∫ s in (0 : ℝ)..t, (-((kappa ν ξ : ℝ) : ℂ) • a s ξ - g s) =
      ∫ s in (0 : ℝ)..t, (-((kappa ν ξ : ℝ) : ℂ) • F s - g s) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht.1] at hs
    rw [hFa s ⟨hs.1, hs.2.trans ht.2⟩]
  show a t ξ = a 0 ξ + ∫ s in (0 : ℝ)..t, (-((kappa ν ξ : ℝ) : ℂ) • a s ξ - g s)
  rw [hcongr, hint, hFa t ht, hFa 0 h0T]
  abel

/-! ### As derivadas temporais -/

/-- `N_k = Σ_{i ≤ k} C(k, i) Nl(f_i, f_{k−i})`. -/
noncomputable def Nk (f : ℕ → ℝ → E3 → C3) (k : ℕ) (t : ℝ) (ξ : E3) : C3 :=
  ∑ i ∈ range (k + 1), (k.choose i) • Nl (f i t) (f (k - i) t) ξ

/-- As derivadas temporais `a_k` da solução branda. -/
noncomputable def ader (ν : ℝ) (a : ℝ → E3 → C3) : ℕ → ℝ → E3 → C3
  | 0 => a
  | k + 1 => fun t ξ => -((kappa ν ξ : ℝ) : ℂ) • ader ν a k t ξ -
      lp ξ (∑ i : Fin (k + 1), (k.choose i) • Nl (ader ν a i t) (ader ν a (k - i) t) ξ)

theorem ader_zero (ν : ℝ) (a : ℝ → E3 → C3) : ader ν a 0 = a := by rw [ader]

theorem ader_succ (ν : ℝ) (a : ℝ → E3 → C3) (k : ℕ) (t : ℝ) (ξ : E3) :
    ader ν a (k + 1) t ξ = -((kappa ν ξ : ℝ) : ℂ) • ader ν a k t ξ - lp ξ (Nk (ader ν a) k t ξ) := by
  rw [ader, Nk, ← Fin.sum_univ_eq_sum_range
    (fun i => (k.choose i) • Nl (ader ν a i t) (ader ν a (k - i) t) ξ)]

/-- Todas as `a_k` são boas. -/
theorem boaW_ader {ν : ℝ} {a : ℝ → E3 → C3} (ha : BoaW a) : ∀ k, BoaW (ader ν a k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases k with _ | k
    · rw [ader_zero]; exact ha
    · have hN : BoaW fun t ξ => Nk (ader ν a) k t ξ := by
        unfold Nk
        refine BoaW.sum _ fun i hi => ?_
        have hi' : i < k + 1 := mem_range.mp hi
        exact ((ih i (by omega)).nl (ih (k - i) (by omega))).nsmul _
      have hlpN : BoaW fun t ξ => lp ξ (Nk (ader ν a) k t ξ) := by
        refine ⟨?_, fun m => ?_⟩
        · -- `P(ξ) N_k` é contínua: soma de termos `P(ξ) Nl`
          have : (fun p : ℝ × E3 => lp p.2 (Nk (ader ν a) k p.1 p.2)) =
              fun p => ∑ i ∈ range (k + 1), (k.choose i) •
                lp p.2 (Nl (ader ν a i p.1) (ader ν a (k - i) p.1) p.2) := by
            funext p
            rw [Nk, ← lpL_apply, map_sum]
            simp only [map_nsmul, lpL_apply]
          rw [this]
          refine continuous_finsetSum _ fun i hi => ?_
          have hi' : i < k + 1 := mem_range.mp hi
          exact ((ih i (by omega)).lpNl (ih (k - i) (by omega))).cont.const_smul _
        · obtain ⟨C, hC0, hC⟩ := hN.bound m
          exact ⟨C, hC0, fun t ξ => (norm_lp_le _ _).trans (hC t ξ)⟩
      have h := ((ih k (by omega)).mulKappa ν).neg.sub hlpN
      have e : ader ν a (k + 1) = fun t ξ => -(((kappa ν ξ : ℝ) : ℂ) • ader ν a k t ξ) -
          lp ξ (Nk (ader ν a) k t ξ) := by
        funext t ξ; rw [ader_succ, neg_smul]
      rw [e]; exact h

/-- **Leibniz**: a derivada de `N_k` é `N_{k+1}`. -/
theorem Nk_succ (f : ℕ → ℝ → E3 → C3) (k : ℕ) (t : ℝ) (ξ : E3) :
    Nk f (k + 1) t ξ = ∑ i ∈ range (k + 1), (k.choose i) •
      (Nl (f (i + 1) t) (f (k - i) t) ξ + Nl (f i t) (f (k + 1 - i) t) ξ) := by
  unfold Nk
  rw [sum_choose_succ_nsmul (fun i j => Nl (f i t) (f j t) ξ) k]
  simp only [smul_add, sum_add_distrib]
  rw [add_comm]

theorem Nk_zero (f : ℕ → ℝ → E3 → C3) (t : ℝ) (ξ : E3) : Nk f 0 t ξ = Nl (f 0 t) (f 0 t) ξ := by
  simp [Nk]

theorem nsmul_eq_cast_smul (n : ℕ) (v : C3) : n • v = (n : ℂ) • v :=
  (Nat.cast_smul_eq_nsmul ℂ n v).symm

/-- **A forma integral das derivadas temporais**: em `[0, T]`, `a_k t = a_k 0 + ∫₀ᵗ a_{k+1}`. -/
theorem ader_integral {ν T : ℝ} {a₀ : E3 → C3} {a : ℝ → E3 → C3} (ha : BoaW a)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a₀ ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ) :
    ∀ k ξ, ∀ t ∈ Icc 0 T,
      ader ν a k t ξ = ader ν a k 0 ξ + ∫ s in (0 : ℝ)..t, ader ν a (k + 1) s ξ := by
  have hb := boaW_ader (ν := ν) ha
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro ξ t ht
    rcases k with _ | k
    · -- a EDO
      have h := edo_integral ha hmild ξ ht
      rw [ader_zero]
      refine h.trans ?_
      congr 1
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [ader_succ, ader_zero, Nk_zero, ader_zero]
    · -- derivando a recorrência
      have hcs : ∀ j, Continuous fun s => ader ν a j s ξ := fun j => (hb j).cont_t ξ
      -- `∫ a_{k+1} = a_k t − a_k 0`
      have h1 : ∫ s in (0 : ℝ)..t, ader ν a (k + 1) s ξ = ader ν a k t ξ - ader ν a k 0 ξ := by
        rw [ih k (by omega) ξ t ht]; abel
      -- `∫ N_{k+1} = N_k t − N_k 0`
      have hNc : ∀ j, Continuous fun s => Nk (ader ν a) j s ξ := by
        intro j
        unfold Nk
        refine continuous_finsetSum _ fun i hi => ?_
        exact (((hb i).nl (hb (j - i))).cont_t ξ).const_smul _
      have h2 : ∫ s in (0 : ℝ)..t, Nk (ader ν a) (k + 1) s ξ =
          Nk (ader ν a) k t ξ - Nk (ader ν a) k 0 ξ := by
        have hterm : ∀ i ∈ range (k + 1),
            Nl (ader ν a i t) (ader ν a (k - i) t) ξ - Nl (ader ν a i 0) (ader ν a (k - i) 0) ξ =
            ∫ s in (0 : ℝ)..t, (Nl (ader ν a (i + 1) s) (ader ν a (k - i) s) ξ +
              Nl (ader ν a i s) (ader ν a (k + 1 - i) s) ξ) := by
          intro i hi
          have hi' : i < k + 1 := mem_range.mp hi
          have e : k + 1 - i = k - i + 1 := by omega
          rw [e]
          have := Nl_integral (T := T) (hb i) (hb (i + 1)) (hb (k - i)) (hb (k - i + 1))
            (fun η t ht => ih i (by omega) η t ht) (fun η t ht => ih (k - i) (by omega) η t ht)
            ξ ht
          rw [this]; abel
        have hint : ∀ i ∈ range (k + 1), IntervalIntegrable (fun s =>
            (k.choose i : ℂ) • (Nl (ader ν a (i + 1) s) (ader ν a (k - i) s) ξ +
              Nl (ader ν a i s) (ader ν a (k + 1 - i) s) ξ)) volume 0 t := by
          intro i _
          have hc : Continuous fun s => (k.choose i : ℂ) •
              (Nl (ader ν a (i + 1) s) (ader ν a (k - i) s) ξ +
                Nl (ader ν a i s) (ader ν a (k + 1 - i) s) ξ) :=
            ((((hb (i + 1)).nl (hb (k - i))).cont_t ξ).add
              (((hb i).nl (hb (k + 1 - i))).cont_t ξ)).const_smul (k.choose i : ℂ)
          exact hc.intervalIntegrable 0 t
        have eN : ∀ s, Nk (ader ν a) (k + 1) s ξ = ∑ i ∈ range (k + 1), (k.choose i : ℂ) •
            (Nl (ader ν a (i + 1) s) (ader ν a (k - i) s) ξ +
              Nl (ader ν a i s) (ader ν a (k + 1 - i) s) ξ) := by
          intro s
          rw [Nk_succ]
          simp only [nsmul_eq_cast_smul]
        simp only [eN]
        rw [intervalIntegral.integral_finsetSum hint, Nk, Nk, ← sum_sub_distrib]
        refine sum_congr rfl fun i hi => ?_
        rw [intervalIntegral.integral_smul, ← hterm i hi, nsmul_eq_cast_smul, nsmul_eq_cast_smul,
          smul_sub]
      -- conclusão
      have hlpi : IntervalIntegrable (fun s => Nk (ader ν a) (k + 1) s ξ) volume 0 t :=
        (hNc (k + 1)).intervalIntegrable 0 t
      have hai : IntervalIntegrable (fun s => ader ν a (k + 1) s ξ) volume 0 t :=
        (hcs (k + 1)).intervalIntegrable 0 t
      have e3 : ∫ s in (0 : ℝ)..t, ader ν a (k + 1 + 1) s ξ =
          -((kappa ν ξ : ℝ) : ℂ) • (∫ s in (0 : ℝ)..t, ader ν a (k + 1) s ξ) -
            lp ξ (∫ s in (0 : ℝ)..t, Nk (ader ν a) (k + 1) s ξ) := by
        simp only [ader_succ ν a (k + 1)]
        have hai' : IntervalIntegrable (fun s => -((kappa ν ξ : ℝ) : ℂ) • ader ν a (k + 1) s ξ)
            volume 0 t :=
          ((hcs (k + 1)).const_smul (-((kappa ν ξ : ℝ) : ℂ))).intervalIntegrable 0 t
        rw [intervalIntegral.integral_sub hai' ?_, intervalIntegral.integral_smul,
          lp_integral ξ hlpi]
        have hc : Continuous fun s => lp ξ (Nk (ader ν a) (k + 1) s ξ) := by
          rw [show (fun s => lp ξ (Nk (ader ν a) (k + 1) s ξ)) =
            fun s => lpL ξ (Nk (ader ν a) (k + 1) s ξ) from funext fun s => (lpL_apply ξ _).symm]
          exact (lpL ξ).continuous.comp (hNc (k + 1))
        exact hc.intervalIntegrable 0 t
      rw [e3, h1, h2, ader_succ, ader_succ]
      have hl : lp ξ (Nk (ader ν a) k t ξ - Nk (ader ν a) k 0 ξ) =
          lp ξ (Nk (ader ν a) k t ξ) - lp ξ (Nk (ader ν a) k 0 ξ) := lp_sub _ _ _
      rw [hl, smul_sub]
      abel

/-- **As derivadas temporais formam uma amplitude suave em `[0, T]`.** -/
theorem amp_ader {ν T : ℝ} {a₀ : E3 → C3} {a : ℝ → E3 → C3} (ha : BoaW a)
    (hmild : ∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a₀ ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ) :
    Amp T (ader ν a) where
  meas k t := ((boaW_ader ha k).cont_s t).aestronglyMeasurable
  cont k ξ := ((boaW_ader ha k).cont_t ξ).continuousOn
  bound k m := by
    obtain ⟨C, hC0, hC⟩ := (boaW_ader ha k).bound m
    exact ⟨C, hC0, fun t _ ξ => hC t ξ⟩
  deriv k ξ t ht := ader_integral ha hmild k ξ t ht

end ATK.NSTempo

#print axioms ATK.NSTempo.BoaW.boa4
#print axioms ATK.NSTempo.BoaW.cont_s
#print axioms ATK.NSTempo.BoaW.cont_t
#print axioms ATK.NSTempo.BoaW.bound_le
#print axioms ATK.NSTempo.BoaW.add
#print axioms ATK.NSTempo.BoaW.neg
#print axioms ATK.NSTempo.BoaW.sub
#print axioms ATK.NSTempo.BoaW.nsmul
#print axioms ATK.NSTempo.BoaW.zero
#print axioms ATK.NSTempo.BoaW.sum
#print axioms ATK.NSTempo.continuous_kappa
#print axioms ATK.NSTempo.norm_kappa_le
#print axioms ATK.NSTempo.BoaW.mulKappa
#print axioms ATK.NSTempo.norm_Nl_le_w
#print axioms ATK.NSTempo.BoaW.nl
#print axioms ATK.NSTempo.BoaW.lpNl
#print axioms ATK.NSTempo.lpL_apply
#print axioms ATK.NSTempo.lp_integral
#print axioms ATK.NSTempo.hasDerivAt_of_integral
#print axioms ATK.NSTempo.Nl_integral
#print axioms ATK.NSTempo.heat_sub
#print axioms ATK.NSTempo.hasDerivAt_heat
#print axioms ATK.NSTempo.edo_integral
#print axioms ATK.NSTempo.ader_zero
#print axioms ATK.NSTempo.ader_succ
#print axioms ATK.NSTempo.boaW_ader
#print axioms ATK.NSTempo.Nk_succ
#print axioms ATK.NSTempo.Nk_zero
#print axioms ATK.NSTempo.nsmul_eq_cast_smul
#print axioms ATK.NSTempo.ader_integral
#print axioms ATK.NSTempo.amp_ader
