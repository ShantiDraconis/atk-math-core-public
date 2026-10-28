import ATK.NSFourierBase
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.MetricSpace.Contracting

/-!
# ATK — Navier–Stokes no lado de Fourier, marco NS2: a não linearidade e a existência local

Ponte B3, marco NS2. Sobre `NSFourierBase`:

* `nl f g ξ = ∫ (ξ · f(ξ−η)) g(η) dη` e `Bq f ξ = 𝐏(ξ)(−2πi · nl f f ξ)` — a transformada de
  Fourier de `−(u·∇)u` projetada (para `f = û` de divergência nula);
* cotas com pesos (`norm_nl_le`, `norm_Bq_le`, `norm_Bq_sub_le`), bilinearidade e continuidade
  conjunta em `(ξ, s)` (`continuous_Bq_param`);
* o operador de Duhamel e, pelo teorema do ponto fixo de Banach num espaço de funções contínuas
  limitadas com peso `(1+|ξ|)^4`, **a existência local** (`existe_local`): para cada dado `v₀`
  contínuo com `‖v₀(ξ)‖ (1+|ξ|)^4 ≤ M₀` existe, num intervalo `[0, T₀]` com `T₀` dependendo só de
  `M₀` e `c`, uma solução contínua da equação de Duhamel.

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta**; **CLOSED_MATH continua
false**.
-/

set_option autoImplicit false

open MeasureTheory Real Filter Topology
open scoped BoundedContinuousFunction
open ATK.LigacaoNS (E3)
open ATK.NSFourierBase

namespace ATK.NSPicard

/-! ### Cotas com peso -/

/-- `‖f ζ‖ (1+|ζ|)^m ≤ A` para todo `ζ`. -/
def Cota (m : ℕ) (A : ℝ) (f : E3 → C3) : Prop := ∀ ζ, ‖f ζ‖ * (1 + ‖ζ‖) ^ m ≤ A

theorem Cota.nonneg {m : ℕ} {A : ℝ} {f : E3 → C3} (h : Cota m A f) : 0 ≤ A :=
  le_trans (by positivity) (h 0)

theorem Cota.le {m : ℕ} {A : ℝ} {f : E3 → C3} (h : Cota m A f) (ζ : E3) : ‖f ζ‖ ≤ A := by
  have h1 : 1 ≤ (1 + ‖ζ‖) ^ m := one_le_pow₀ (by linarith [norm_nonneg ζ])
  have := h ζ
  nlinarith [norm_nonneg (f ζ)]

theorem Cota.le_inv {m : ℕ} {A : ℝ} {f : E3 → C3} (h : Cota m A f) (ζ : E3) :
    ‖f ζ‖ ≤ A * ((1 + ‖ζ‖) ^ m)⁻¹ :=
  le_of_mul_le (f := fun ζ => ‖f ζ‖) h ζ

theorem Cota.sub {m : ℕ} {A B : ℝ} {f g : E3 → C3} (hf : Cota m A f) (hg : Cota m B g) :
    Cota m (A + B) (f - g) := by
  intro ζ
  have := norm_sub_le (f ζ) (g ζ)
  have h1 := hf ζ
  have h2 := hg ζ
  simp only [Pi.sub_apply]
  nlinarith [show (0 : ℝ) ≤ (1 + ‖ζ‖) ^ m by positivity]

theorem Cota.mono {m : ℕ} {A B : ℝ} {f : E3 → C3} (hf : Cota m A f) (h : A ≤ B) : Cota m B f :=
  fun ζ => (hf ζ).trans h

/-! ### A convolução não linear -/

/-- `N(f, g)(ξ) = ∫ (ξ · f(ξ−η)) g(η) dη`. -/
noncomputable def nl (f g : E3 → C3) (ξ : E3) : C3 := ∫ η, ip ξ (f (ξ - η)) • g η

theorem continuous_ip_comp {f : E3 → C3} (hf : Continuous f) (ξ : E3) :
    Continuous fun η => ip ξ (f (ξ - η)) := by
  have : (fun η => ip ξ (f (ξ - η))) = fun η => ipL ξ (f (ξ - η)) := by
    funext η
    rw [ipL_apply]
  rw [this]
  exact (ipL ξ).continuous.comp (hf.comp (continuous_const.sub continuous_id))

theorem integrable_nl {f g : E3 → C3} (hf : Continuous f) (hg : Continuous g) {A B : ℝ}
    (hA : Cota 4 A f) (hB : Cota 4 B g) (ξ : E3) :
    Integrable (fun η => ip ξ (f (ξ - η)) • g η) := by
  have hs := integrable_conv (f := fun ζ => ‖f ζ‖) (g := fun ζ => ‖g ζ‖)
    hf.norm.aestronglyMeasurable hg.norm.aestronglyMeasurable (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hA hB ξ
  refine (hs.const_mul ‖ξ‖).mono' ((continuous_ip_comp hf ξ).smul hg).aestronglyMeasurable
    (Eventually.of_forall fun η => ?_)
  rw [norm_smul]
  calc ‖ip ξ (f (ξ - η))‖ * ‖g η‖ ≤ ‖ξ‖ * ‖f (ξ - η)‖ * ‖g η‖ := by
        gcongr
        exact norm_ip_le _ _
    _ = ‖ξ‖ * (‖f (ξ - η)‖ * ‖g η‖) := by ring

theorem norm_nl_le_conv {f g : E3 → C3} (hf : Continuous f) (hg : Continuous g) {A B : ℝ}
    (hA : Cota 4 A f) (hB : Cota 4 B g) (ξ : E3) :
    ‖nl f g ξ‖ ≤ ‖ξ‖ * ∫ η, ‖f (ξ - η)‖ * ‖g η‖ := by
  have hs := integrable_conv (f := fun ζ => ‖f ζ‖) (g := fun ζ => ‖g ζ‖)
    hf.norm.aestronglyMeasurable hg.norm.aestronglyMeasurable (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hA hB ξ
  unfold nl
  calc ‖∫ η, ip ξ (f (ξ - η)) • g η‖ ≤ ∫ η, ‖ip ξ (f (ξ - η)) • g η‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ η, ‖ξ‖ * (‖f (ξ - η)‖ * ‖g η‖) := by
        refine integral_mono (integrable_nl hf hg hA hB ξ).norm (hs.const_mul _) fun η => ?_
        simp only
        rw [norm_smul]
        calc ‖ip ξ (f (ξ - η))‖ * ‖g η‖ ≤ ‖ξ‖ * ‖f (ξ - η)‖ * ‖g η‖ := by
              gcongr
              exact norm_ip_le _ _
          _ = ‖ξ‖ * (‖f (ξ - η)‖ * ‖g η‖) := by ring
    _ = ‖ξ‖ * ∫ η, ‖f (ξ - η)‖ * ‖g η‖ := integral_const_mul _ _

/-- **Cota mansa de `N`** com peso `m`. -/
theorem norm_nl_le {f g : E3 → C3} (hf : Continuous f) (hg : Continuous g) (m : ℕ)
    {A₄ Am B₄ Bm : ℝ} (hA₄ : Cota 4 A₄ f) (hAm : Cota m Am f) (hB₄ : Cota 4 B₄ g)
    (hBm : Cota m Bm g) (ξ : E3) :
    ‖nl f g ξ‖ * (1 + ‖ξ‖) ^ m ≤ ‖ξ‖ * (2 ^ m * Kp 4 * (Am * B₄ + A₄ * Bm)) := by
  have hc := conv_bound (f := fun ζ => ‖f ζ‖) (g := fun ζ => ‖g ζ‖)
    hf.norm.aestronglyMeasurable hg.norm.aestronglyMeasurable (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) m hA₄ hAm hB₄ hBm ξ
  have h1 := norm_nl_le_conv hf hg hA₄ hB₄ ξ
  calc ‖nl f g ξ‖ * (1 + ‖ξ‖) ^ m ≤ (‖ξ‖ * ∫ η, ‖f (ξ - η)‖ * ‖g η‖) * (1 + ‖ξ‖) ^ m := by
        gcongr
    _ = ‖ξ‖ * ((∫ η, ‖f (ξ - η)‖ * ‖g η‖) * (1 + ‖ξ‖) ^ m) := by ring
    _ ≤ ‖ξ‖ * (2 ^ m * Kp 4 * (Am * B₄ + A₄ * Bm)) := by gcongr

theorem norm_nl_le4 {f g : E3 → C3} (hf : Continuous f) (hg : Continuous g) {A B : ℝ}
    (hA : Cota 4 A f) (hB : Cota 4 B g) (ξ : E3) :
    ‖nl f g ξ‖ * (1 + ‖ξ‖) ^ 4 ≤ ‖ξ‖ * (32 * Kp 4 * A * B) := by
  have := norm_nl_le hf hg 4 hA hA hB hB ξ
  calc ‖nl f g ξ‖ * (1 + ‖ξ‖) ^ 4 ≤ ‖ξ‖ * (2 ^ 4 * Kp 4 * (A * B + A * B)) := this
    _ = ‖ξ‖ * (32 * Kp 4 * A * B) := by ring

theorem nl_sub_left {f₁ f₂ g : E3 → C3} (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hg : Continuous g) {A₁ A₂ B : ℝ} (h₁ : Cota 4 A₁ f₁) (h₂ : Cota 4 A₂ f₂) (hB : Cota 4 B g)
    (ξ : E3) : nl (f₁ - f₂) g ξ = nl f₁ g ξ - nl f₂ g ξ := by
  unfold nl
  rw [← integral_sub (integrable_nl hf₁ hg h₁ hB ξ) (integrable_nl hf₂ hg h₂ hB ξ)]
  congr 1
  funext η
  simp [ip_sub, sub_smul]

theorem nl_sub_right {f g₁ g₂ : E3 → C3} (hf : Continuous f) (hg₁ : Continuous g₁)
    (hg₂ : Continuous g₂) {A B₁ B₂ : ℝ} (hA : Cota 4 A f) (h₁ : Cota 4 B₁ g₁) (h₂ : Cota 4 B₂ g₂)
    (ξ : E3) : nl f (g₁ - g₂) ξ = nl f g₁ ξ - nl f g₂ ξ := by
  unfold nl
  rw [← integral_sub (integrable_nl hf hg₁ hA h₁ ξ) (integrable_nl hf hg₂ hA h₂ ξ)]
  congr 1
  funext η
  simp [smul_sub]

/-- `N(f,f) − N(h,h) = N(f−h, f) + N(h, f−h)`. -/
theorem nl_sub_nl {f h : E3 → C3} (hf : Continuous f) (hh : Continuous h) {A B : ℝ}
    (hA : Cota 4 A f) (hB : Cota 4 B h) (ξ : E3) :
    nl f f ξ - nl h h ξ = nl (f - h) f ξ + nl h (f - h) ξ := by
  rw [nl_sub_left hf hh hf hA hB hA, nl_sub_right hh hf hh hB hA hB]
  abel

/-! ### A não linearidade projetada -/

/-- A constante `−2πi`. -/
noncomputable def cI : ℂ := -(2 * (π : ℂ) * Complex.I)

theorem norm_cI : ‖cI‖ = 2 * π := by
  unfold cI
  rw [norm_neg, norm_mul, Complex.norm_I, mul_one, norm_mul]
  simp [abs_of_pos pi_pos]

/-- `B(f)(ξ) = 𝐏(ξ)(−2πi N(f, f)(ξ))`. -/
noncomputable def Bq (f : E3 → C3) (ξ : E3) : C3 := leray ξ (cI • nl f f ξ)

theorem norm_Bq_le_nl (f : E3 → C3) (ξ : E3) : ‖Bq f ξ‖ ≤ 2 * π * ‖nl f f ξ‖ := by
  unfold Bq
  have := norm_leray_smul_le ξ cI (nl f f ξ)
  rwa [norm_cI] at this

theorem norm_Bq_le {f : E3 → C3} (hf : Continuous f) {A : ℝ} (hA : Cota 4 A f) (ξ : E3) :
    ‖Bq f ξ‖ * (1 + ‖ξ‖) ^ 4 ≤ ‖ξ‖ * (2 * π * (32 * Kp 4 * A * A)) := by
  have h1 := norm_Bq_le_nl f ξ
  have h2 := norm_nl_le4 hf hf hA hA ξ
  calc ‖Bq f ξ‖ * (1 + ‖ξ‖) ^ 4 ≤ 2 * π * ‖nl f f ξ‖ * (1 + ‖ξ‖) ^ 4 := by gcongr
    _ = 2 * π * (‖nl f f ξ‖ * (1 + ‖ξ‖) ^ 4) := by ring
    _ ≤ 2 * π * (‖ξ‖ * (32 * Kp 4 * A * A)) := by gcongr
    _ = ‖ξ‖ * (2 * π * (32 * Kp 4 * A * A)) := by ring

theorem Bq_sub {f h : E3 → C3} (hf : Continuous f) (hh : Continuous h) {A B : ℝ}
    (hA : Cota 4 A f) (hB : Cota 4 B h) (ξ : E3) :
    Bq f ξ - Bq h ξ = leray ξ (cI • (nl (f - h) f ξ + nl h (f - h) ξ)) := by
  unfold Bq
  rw [← map_sub, ← smul_sub, nl_sub_nl hf hh hA hB]

/-- **Lipschitz de `B`** com peso 4. -/
theorem norm_Bq_sub_le {f h : E3 → C3} (hf : Continuous f) (hh : Continuous h) {A B D : ℝ}
    (hA : Cota 4 A f) (hB : Cota 4 B h) (hD : Cota 4 D (f - h)) (ξ : E3) :
    ‖Bq f ξ - Bq h ξ‖ * (1 + ‖ξ‖) ^ 4 ≤ ‖ξ‖ * (2 * π * (32 * Kp 4 * (D * A + B * D))) := by
  rw [Bq_sub hf hh hA hB]
  have h0 := norm_leray_smul_le ξ cI (nl (f - h) f ξ + nl h (f - h) ξ)
  rw [norm_cI] at h0
  have h1 := norm_nl_le4 (hf.sub hh) hf hD hA ξ
  have h2 := norm_nl_le4 hh (hf.sub hh) hB hD ξ
  have h3 := norm_add_le (nl (f - h) f ξ) (nl h (f - h) ξ)
  have hw : 0 ≤ (1 + ‖ξ‖) ^ 4 := by positivity
  calc ‖leray ξ (cI • (nl (f - h) f ξ + nl h (f - h) ξ))‖ * (1 + ‖ξ‖) ^ 4
      ≤ 2 * π * (‖nl (f - h) f ξ‖ + ‖nl h (f - h) ξ‖) * (1 + ‖ξ‖) ^ 4 := by
        gcongr
        exact h0.trans (by gcongr)
    _ = 2 * π * (‖nl (f - h) f ξ‖ * (1 + ‖ξ‖) ^ 4 + ‖nl h (f - h) ξ‖ * (1 + ‖ξ‖) ^ 4) := by ring
    _ ≤ 2 * π * (‖ξ‖ * (32 * Kp 4 * D * A) + ‖ξ‖ * (32 * Kp 4 * B * D)) := by gcongr
    _ = ‖ξ‖ * (2 * π * (32 * Kp 4 * (D * A + B * D))) := by ring

/-! ### Continuidade conjunta -/

theorem continuous_cx : Continuous cx := by
  let L : E3 →ₗ[ℝ] C3 :=
    { toFun := cx
      map_add' := fun a b => by ext j; simp
      map_smul' := fun r a => by ext j; simp [Complex.real_smul] }
  exact L.continuous_of_finiteDimensional

theorem continuous_ip : Continuous fun q : E3 × C3 => ip q.1 q.2 := by
  unfold ip
  refine continuous_finsetSum _ fun j _ => ?_
  have h1 : Continuous fun q : E3 × C3 => q.1 j :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.comp continuous_fst
  have h2 : Continuous fun q : E3 × C3 => q.2 j :=
    (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp continuous_snd
  exact (Complex.continuous_ofReal.comp h1).mul h2

/-- `(ξ, a) ↦ 𝐏(ξ) a` é contínua nos pontos com `ξ ≠ 0`. -/
theorem continuousAt_leray {ξ₀ : E3} (hξ₀ : ξ₀ ≠ 0) (a₀ : C3) :
    ContinuousAt (fun q : E3 × C3 => leray q.1 q.2) (ξ₀, a₀) := by
  have he : (fun q : E3 × C3 => leray q.1 q.2) =
      fun q => q.2 - ((((‖q.1‖ ^ 2 : ℝ) : ℂ))⁻¹ * ip q.1 q.2) • cx q.1 := by
    funext q
    rw [leray_apply]
  rw [he]
  have hn : ((‖ξ₀‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : ‖ξ₀‖ ≠ 0 := norm_ne_zero_iff.mpr hξ₀
    exact_mod_cast pow_ne_zero 2 this
  have h1 : ContinuousAt (fun q : E3 × C3 => (((‖q.1‖ ^ 2 : ℝ) : ℂ))⁻¹) (ξ₀, a₀) := by
    refine ContinuousAt.inv₀ ?_ hn
    exact (Complex.continuous_ofReal.comp ((continuous_fst.norm).pow 2)).continuousAt
  exact continuous_snd.continuousAt.sub
    ((h1.mul continuous_ip.continuousAt).smul (continuous_cx.comp continuous_fst).continuousAt)

theorem nl_zero_left (f g : E3 → C3) : nl f g 0 = 0 := by
  simp [nl, ip_zero_left]

theorem Bq_zero (f : E3 → C3) : Bq f 0 = 0 := by
  simp [Bq, nl_zero_left]

/-- Continuidade conjunta de `(ξ, s) ↦ N(v(·, s), w(·, s))(ξ)`. -/
theorem continuous_nl_param {v w : E3 × ℝ → C3} (hv : Continuous v) (hw : Continuous w)
    {A B : ℝ} (hA : ∀ s, Cota 4 A (fun η => v (η, s))) (hB : ∀ s, Cota 4 B (fun η => w (η, s))) :
    Continuous fun p : E3 × ℝ => nl (fun η => v (η, p.2)) (fun η => w (η, p.2)) p.1 := by
  rw [continuous_iff_continuousAt]
  intro p₀
  unfold nl
  have hB0 : 0 ≤ B := (hB 0).nonneg
  refine continuousAt_of_dominated
    (bound := fun η => (‖p₀.1‖ + 1) * (A * (B * ((1 + ‖η‖) ^ 4)⁻¹))) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun p => ?_
    have h1 : Continuous fun η => v (η, p.2) := hv.comp (by fun_prop)
    have h2 : Continuous fun η => w (η, p.2) := hw.comp (by fun_prop)
    exact ((continuous_ip_comp h1 p.1).smul h2).aestronglyMeasurable
  · have hev : ∀ᶠ p in 𝓝 p₀, ‖p.1‖ < ‖p₀.1‖ + 1 :=
      (continuous_fst.norm.continuousAt).eventually (gt_mem_nhds (lt_add_one _))
    filter_upwards [hev] with p hp
    refine Eventually.of_forall fun η => ?_
    rw [norm_smul]
    have e1 := norm_ip_le p.1 (v (p.1 - η, p.2))
    have e2 := (hA p.2).le (p.1 - η)
    have e3 := (hB p.2).le_inv η
    calc ‖ip p.1 (v (p.1 - η, p.2))‖ * ‖w (η, p.2)‖
        ≤ (‖p.1‖ * ‖v (p.1 - η, p.2)‖) * ‖w (η, p.2)‖ := by gcongr
      _ ≤ ((‖p₀.1‖ + 1) * A) * (B * ((1 + ‖η‖) ^ 4)⁻¹) := by
          have hA0 : 0 ≤ A := (hA 0).nonneg
          exact mul_le_mul (mul_le_mul hp.le e2 (norm_nonneg _) (by positivity)) e3
            (norm_nonneg _) (by positivity)
      _ = (‖p₀.1‖ + 1) * (A * (B * ((1 + ‖η‖) ^ 4)⁻¹)) := by ring
  · exact (((integrable_inv_pow le_rfl).const_mul B).const_mul A).const_mul _
  · refine Eventually.of_forall fun η => ?_
    have h1 : Continuous fun p : E3 × ℝ => (p.1, v (p.1 - η, p.2)) :=
      continuous_fst.prodMk (hv.comp (by fun_prop))
    exact ((continuous_ip.comp h1).smul (hw.comp (by fun_prop))).continuousAt

/-- Continuidade conjunta de `(ξ, s) ↦ B(v(·, s))(ξ)`. -/
theorem continuous_Bq_param {v : E3 × ℝ → C3} (hv : Continuous v) {A : ℝ}
    (hA : ∀ s, Cota 4 A (fun η => v (η, s))) :
    Continuous fun p : E3 × ℝ => Bq (fun η => v (η, p.2)) p.1 := by
  have hN := continuous_nl_param hv hv hA hA
  rw [continuous_iff_continuousAt]
  intro p₀
  by_cases h0 : p₀.1 = 0
  · -- em `ξ = 0`: `B = 0` e `‖B(ξ)‖ ≤ |ξ| Q`
    have hval : Bq (fun η => v (η, p₀.2)) p₀.1 = 0 := by rw [h0]; exact Bq_zero _
    rw [ContinuousAt, hval, tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    have hQ : ∀ p : E3 × ℝ, ‖Bq (fun η => v (η, p.2)) p.1‖ ≤
        ‖p.1‖ * (2 * π * (32 * Kp 4 * A * A)) := by
      intro p
      have hs : Continuous fun η => v (η, p.2) := hv.comp (by fun_prop)
      have := norm_Bq_le hs (hA p.2) p.1
      have h1 : 1 ≤ (1 + ‖p.1‖) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg p.1])
      nlinarith [norm_nonneg (Bq (fun η => v (η, p.2)) p.1)]
    refine squeeze_zero (fun p => norm_nonneg _) hQ ?_
    have : Tendsto (fun p : E3 × ℝ => ‖p.1‖) (𝓝 p₀) (𝓝 0) := by
      have := (continuous_fst.norm (E := E3)).tendsto p₀
      simpa [h0] using this
    simpa using this.mul_const (2 * π * (32 * Kp 4 * A * A))
  · have hL := continuousAt_leray h0 (cI • nl (fun η => v (η, p₀.2)) (fun η => v (η, p₀.2)) p₀.1)
    have hg : ContinuousAt (fun p : E3 × ℝ =>
        (p.1, cI • nl (fun η => v (η, p.2)) (fun η => v (η, p.2)) p.1)) p₀ :=
      continuous_fst.continuousAt.prodMk (hN.continuousAt.const_smul cI)
    have he : (fun p : E3 × ℝ => Bq (fun η => v (η, p.2)) p.1) =
        (fun q : E3 × C3 => leray q.1 q.2) ∘
          (fun p : E3 × ℝ => (p.1, cI • nl (fun η => v (η, p.2)) (fun η => v (η, p.2)) p.1)) := by
      funext p
      rfl
    rw [he]
    exact ContinuousAt.comp (g := fun q : E3 × C3 => leray q.1 q.2) hL hg

/-! ### O operador de Duhamel -/

/-- Os dados do problema no lado de Fourier: `c = 4π²ν > 0` e `v₀` contínuo com cota de peso 4. -/
structure Dado where
  c : ℝ
  hc : 0 < c
  v₀ : E3 → C3
  cont : Continuous v₀
  M₀ : ℝ
  cota : Cota 4 M₀ v₀

/-- `clamp T t = max 0 (min t T)`: o tempo congelado fora de `[0, T]`. -/
def clamp (T t : ℝ) : ℝ := max 0 (min t T)

theorem clamp_nonneg (T t : ℝ) : 0 ≤ clamp T t := le_max_left _ _

theorem clamp_le {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clamp T t ≤ T :=
  max_le hT (min_le_right _ _)

theorem clamp_of_mem {T t : ℝ} (ht : t ∈ Set.Icc 0 T) : clamp T t = t := by
  unfold clamp
  rw [min_eq_left ht.2, max_eq_right ht.1]

theorem clamp_clamp {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clamp T (clamp T t) = clamp T t :=
  clamp_of_mem ⟨clamp_nonneg _ _, clamp_le hT _⟩

theorem continuous_clamp (T : ℝ) : Continuous (clamp T) := by
  unfold clamp
  fun_prop

/-- O fator do calor `e^{−c|ξ|²τ}`. -/
noncomputable def hk (c : ℝ) (ξ : E3) (τ : ℝ) : ℝ := exp (-(c * ‖ξ‖ ^ 2 * τ))

theorem continuous_hk (c : ℝ) : Continuous fun q : E3 × ℝ => hk c q.1 q.2 := by
  unfold hk
  fun_prop

theorem hk_le_one {c τ : ℝ} (hc : 0 ≤ c) (hτ : 0 ≤ τ) (ξ : E3) : hk c ξ τ ≤ 1 :=
  heat_le_one hc hτ ξ

theorem hk_pos (c : ℝ) (ξ : E3) (τ : ℝ) : 0 < hk c ξ τ := exp_pos _

/-- A integral de Duhamel `∫₀^τ e^{−c|ξ|²(τ−s)} G(ξ, s) ds`. -/
noncomputable def Iduh (c : ℝ) (G : E3 × ℝ → C3) (ξ : E3) (τ : ℝ) : C3 :=
  ∫ s in (0 : ℝ)..τ, hk c ξ (τ - s) • G (ξ, s)

theorem intervalIntegrable_duh (c : ℝ) {G : E3 × ℝ → C3} (hG : Continuous G) (ξ : E3)
    (τ a b : ℝ) : IntervalIntegrable (fun s => hk c ξ (τ - s) • G (ξ, s)) volume a b := by
  refine Continuous.intervalIntegrable ?_ _ _
  have h1 : Continuous fun s : ℝ => hk c ξ (τ - s) := by
    unfold hk
    fun_prop
  have h2 : Continuous fun s : ℝ => G (ξ, s) := hG.comp (continuous_const.prodMk continuous_id)
  exact h1.smul h2

/-- **Cota da integral de Duhamel**: se `‖G(ξ,s)‖ (1+|ξ|)^m ≤ |ξ| Q`, então
`‖∫₀^τ …‖ (1+|ξ|)^m ≤ Q √(τ/c)`. -/
theorem norm_Iduh_le {c : ℝ} (hc : 0 < c) {G : E3 × ℝ → C3} {m : ℕ} {Q : ℝ}
    (hQ0 : 0 ≤ Q) (hQ : ∀ q : E3 × ℝ, ‖G q‖ * (1 + ‖q.1‖) ^ m ≤ ‖q.1‖ * Q) (ξ : E3) {τ : ℝ}
    (hτ : 0 ≤ τ) : ‖Iduh c G ξ τ‖ * (1 + ‖ξ‖) ^ m ≤ Q * sqrt (τ / c) := by
  have hw : 0 < (1 + ‖ξ‖) ^ m := by positivity
  set k : ℝ := ‖ξ‖ * Q * ((1 + ‖ξ‖) ^ m)⁻¹
  have hpt : ∀ s, ‖hk c ξ (τ - s) • G (ξ, s)‖ ≤ hk c ξ (τ - s) * k := by
    intro s
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hk_pos _ _ _)]
    refine mul_le_mul_of_nonneg_left ?_ (hk_pos _ _ _).le
    rw [le_mul_inv_iff₀ hw]
    exact hQ (ξ, s)
  have hint : IntervalIntegrable (fun s => hk c ξ (τ - s) * k) volume 0 τ := by
    refine Continuous.intervalIntegrable ?_ _ _
    have h1 : Continuous fun s : ℝ => hk c ξ (τ - s) := by
      unfold hk
      fun_prop
    exact h1.mul continuous_const
  have h1 : ‖Iduh c G ξ τ‖ ≤ ∫ s in (0 : ℝ)..τ, hk c ξ (τ - s) * k :=
    intervalIntegral.norm_integral_le_of_norm_le hτ (Eventually.of_forall fun s _ => hpt s) hint
  rw [intervalIntegral.integral_mul_const] at h1
  have hK := kernel_bound hc hτ ξ
  have hK' : ‖ξ‖ * ∫ s in (0 : ℝ)..τ, hk c ξ (τ - s) ≤ sqrt (τ / c) := by
    simpa [hk] using hK
  calc ‖Iduh c G ξ τ‖ * (1 + ‖ξ‖) ^ m
      ≤ ((∫ s in (0 : ℝ)..τ, hk c ξ (τ - s)) * k) * (1 + ‖ξ‖) ^ m := by gcongr
    _ = (‖ξ‖ * ∫ s in (0 : ℝ)..τ, hk c ξ (τ - s)) * Q := by
        simp only [k]
        field_simp
    _ ≤ sqrt (τ / c) * Q := by gcongr
    _ = Q * sqrt (τ / c) := by ring

theorem Iduh_sub (c : ℝ) {G₁ G₂ : E3 × ℝ → C3} (h₁ : Continuous G₁) (h₂ : Continuous G₂)
    (ξ : E3) (τ : ℝ) : Iduh c G₁ ξ τ - Iduh c G₂ ξ τ = Iduh c (G₁ - G₂) ξ τ := by
  unfold Iduh
  rw [← intervalIntegral.integral_sub (intervalIntegrable_duh c h₁ _ _ _ _)
    (intervalIntegrable_duh c h₂ _ _ _ _)]
  congr 1
  funext s
  simp only [Pi.sub_apply, smul_sub]

/-- `G_v(ξ, s) = B(v(·, s))(ξ)`. -/
noncomputable def Gv (v : E3 × ℝ → C3) (q : E3 × ℝ) : C3 := Bq (fun η => v (η, q.2)) q.1

/-- O lado direito de Duhamel (tempo congelado em `[0, T]`). -/
noncomputable def duh (D : Dado) (T : ℝ) (v : E3 × ℝ → C3) (p : E3 × ℝ) : C3 :=
  hk D.c p.1 (clamp T p.2) • D.v₀ p.1 + Iduh D.c (Gv v) p.1 (clamp T p.2)

theorem duh_clamp (D : Dado) {T : ℝ} (hT : 0 ≤ T) (v : E3 × ℝ → C3) (ξ : E3) (t : ℝ) :
    duh D T v (ξ, clamp T t) = duh D T v (ξ, t) := by
  simp only [duh, clamp_clamp hT]

/-! ### O espaço com peso e a aplicação de Picard -/

/-- Funções contínuas limitadas em `ℝ³ × ℝ`; `F` representa `v = (1+|ξ|)^{−4} F`. -/
abbrev X := E3 × ℝ →ᵇ C3

/-- `v = (1+|ξ|)^{−4} F`. -/
noncomputable def unw (F : X) (p : E3 × ℝ) : C3 := ((1 + ‖p.1‖) ^ 4)⁻¹ • F p

theorem continuous_unw (F : X) : Continuous (unw F) := by
  unfold unw
  have hw : Continuous fun p : E3 × ℝ => ((1 + ‖p.1‖) ^ 4)⁻¹ := by
    refine Continuous.inv₀ (by fun_prop) fun p => ?_
    have := norm_nonneg p.1
    positivity
  exact hw.smul F.continuous

theorem cota_unw (F : X) (s : ℝ) : Cota 4 ‖F‖ (fun η => unw F (η, s)) := by
  intro ζ
  simp only [unw]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hw : 0 < (1 + ‖ζ‖) ^ 4 := by positivity
  rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]
  exact F.norm_coe_le_norm _

theorem unw_sub (F H : X) : unw (F - H) = unw F - unw H := by
  funext p
  simp [unw, smul_sub]

theorem weight_unw (F : X) (p : E3 × ℝ) : (1 + ‖p.1‖) ^ 4 • unw F p = F p := by
  simp only [unw, smul_smul]
  rw [mul_inv_cancel₀ (by positivity), one_smul]

/-- `G_F(ξ, s) = B(v_F(·, s))(ξ)`. -/
noncomputable def GF (F : X) : E3 × ℝ → C3 := Gv (unw F)

theorem continuous_GF (F : X) : Continuous (GF F) :=
  continuous_Bq_param (continuous_unw F) (cota_unw F)

theorem norm_GF_le (F : X) (q : E3 × ℝ) :
    ‖GF F q‖ * (1 + ‖q.1‖) ^ 4 ≤ ‖q.1‖ * (2 * π * (32 * Kp 4 * ‖F‖ * ‖F‖)) :=
  norm_Bq_le ((continuous_unw F).comp (by fun_prop)) (cota_unw F q.2) q.1

theorem norm_GF_sub_le (F H : X) (q : E3 × ℝ) :
    ‖(GF F - GF H) q‖ * (1 + ‖q.1‖) ^ 4 ≤
      ‖q.1‖ * (2 * π * (32 * Kp 4 * (‖F - H‖ * ‖F‖ + ‖H‖ * ‖F - H‖))) := by
  have hF : Continuous fun η => unw F (η, q.2) := (continuous_unw F).comp (by fun_prop)
  have hH : Continuous fun η => unw H (η, q.2) := (continuous_unw H).comp (by fun_prop)
  have hD : Cota 4 ‖F - H‖ ((fun η => unw F (η, q.2)) - fun η => unw H (η, q.2)) := by
    have := cota_unw (F - H) q.2
    rw [unw_sub] at this
    exact this
  exact norm_Bq_sub_le hF hH (cota_unw F q.2) (cota_unw H q.2) hD q.1

/-- A função de Picard com peso. -/
noncomputable def Φfun (D : Dado) (T : ℝ) (F : X) (p : E3 × ℝ) : C3 :=
  (1 + ‖p.1‖) ^ 4 • duh D T (unw F) p

theorem continuous_Φfun (D : Dado) (T : ℝ) (F : X) : Continuous (Φfun D T F) := by
  unfold Φfun duh Iduh
  have hw : Continuous fun p : E3 × ℝ => (1 + ‖p.1‖) ^ 4 := by fun_prop
  refine hw.smul (Continuous.add ?_ ?_)
  · have hc := continuous_clamp T
    have h1 : Continuous fun p : E3 × ℝ => hk D.c p.1 (clamp T p.2) := by
      unfold hk
      fun_prop
    exact h1.smul (D.cont.comp continuous_fst)
  · have hf : Continuous (Function.uncurry fun (p : E3 × ℝ) (s : ℝ) =>
        hk D.c p.1 (clamp T p.2 - s) • Gv (unw F) (p.1, s)) := by
      have hc := continuous_clamp T
      have h1 : Continuous fun z : (E3 × ℝ) × ℝ => hk D.c z.1.1 (clamp T z.1.2 - z.2) := by
        unfold hk
        fun_prop
      have h2 : Continuous fun z : (E3 × ℝ) × ℝ => Gv (unw F) (z.1.1, z.2) :=
        (continuous_GF F).comp (by fun_prop)
      exact h1.smul h2
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf
      ((continuous_clamp T).comp continuous_snd)

theorem norm_Φfun_le (D : Dado) {T : ℝ} (hT : 0 ≤ T) (F : X) (p : E3 × ℝ) :
    ‖Φfun D T F p‖ ≤ D.M₀ + 2 * π * (32 * Kp 4 * ‖F‖ * ‖F‖) * sqrt (T / D.c) := by
  have hw : 0 ≤ (1 + ‖p.1‖) ^ 4 := by positivity
  have hτ := clamp_nonneg T p.2
  unfold Φfun duh
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
  have h1 : ‖hk D.c p.1 (clamp T p.2) • D.v₀ p.1‖ * (1 + ‖p.1‖) ^ 4 ≤ D.M₀ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hk_pos _ _ _), mul_assoc]
    calc hk D.c p.1 (clamp T p.2) * (‖D.v₀ p.1‖ * (1 + ‖p.1‖) ^ 4)
        ≤ 1 * D.M₀ := mul_le_mul (hk_le_one D.hc.le hτ _) (D.cota _) (by positivity) zero_le_one
      _ = D.M₀ := one_mul _
  have hQ0 : 0 ≤ 2 * π * (32 * Kp 4 * ‖F‖ * ‖F‖) := by
    have := Kp_nonneg 4
    positivity
  have h2 := norm_Iduh_le D.hc hQ0 (norm_GF_le F) p.1 hτ
  have h3 : sqrt (clamp T p.2 / D.c) ≤ sqrt (T / D.c) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (clamp_le hT _) D.hc.le)
  have h2' : ‖Iduh D.c (Gv (unw F)) p.1 (clamp T p.2)‖ *
      (1 + ‖p.1‖) ^ 4 ≤ 2 * π * (32 * Kp 4 * ‖F‖ * ‖F‖) * sqrt (T / D.c) :=
    h2.trans (mul_le_mul_of_nonneg_left h3 hQ0)
  calc (1 + ‖p.1‖) ^ 4 * ‖hk D.c p.1 (clamp T p.2) • D.v₀ p.1 +
        Iduh D.c (Gv (unw F)) p.1 (clamp T p.2)‖
      ≤ (1 + ‖p.1‖) ^ 4 * (‖hk D.c p.1 (clamp T p.2) • D.v₀ p.1‖ +
        ‖Iduh D.c (Gv (unw F)) p.1 (clamp T p.2)‖) := by gcongr; exact norm_add_le _ _
    _ = ‖hk D.c p.1 (clamp T p.2) • D.v₀ p.1‖ * (1 + ‖p.1‖) ^ 4 +
        ‖Iduh D.c (Gv (unw F)) p.1 (clamp T p.2)‖ * (1 + ‖p.1‖) ^ 4 := by ring
    _ ≤ D.M₀ + 2 * π * (32 * Kp 4 * ‖F‖ * ‖F‖) * sqrt (T / D.c) := add_le_add h1 h2'

/-- **A aplicação de Picard** no espaço com peso. -/
noncomputable def Φ (D : Dado) {T : ℝ} (hT : 0 ≤ T) (F : X) : X :=
  BoundedContinuousFunction.ofNormedAddCommGroup (Φfun D T F) (continuous_Φfun D T F)
    (D.M₀ + 2 * π * (32 * Kp 4 * ‖F‖ * ‖F‖) * sqrt (T / D.c)) (norm_Φfun_le D hT F)

theorem Φ_apply (D : Dado) {T : ℝ} (hT : 0 ≤ T) (F : X) (p : E3 × ℝ) :
    Φ D hT F p = Φfun D T F p := rfl

theorem Φfun_sub (D : Dado) (T : ℝ) (F H : X) (p : E3 × ℝ) :
    Φfun D T F p - Φfun D T H p =
      (1 + ‖p.1‖) ^ 4 • Iduh D.c (GF F - GF H) p.1 (clamp T p.2) := by
  unfold Φfun duh
  rw [← smul_sub, add_sub_add_left_eq_sub]
  exact congrArg _ (Iduh_sub D.c (continuous_GF F) (continuous_GF H) _ _)

theorem dist_Φ_le (D : Dado) {T : ℝ} (hT : 0 ≤ T) (F H : X) :
    dist (Φ D hT F) (Φ D hT H) ≤
      2 * π * (32 * Kp 4 * (‖F‖ + ‖H‖)) * sqrt (T / D.c) * dist F H := by
  have hK := Kp_nonneg 4
  have hC : 0 ≤ 2 * π * (32 * Kp 4 * (‖F‖ + ‖H‖)) * sqrt (T / D.c) * dist F H := by positivity
  rw [BoundedContinuousFunction.dist_le hC]
  intro p
  rw [Φ_apply, Φ_apply, dist_eq_norm, Φfun_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), mul_comm]
  have hQ0 : 0 ≤ 2 * π * (32 * Kp 4 * (‖F - H‖ * ‖F‖ + ‖H‖ * ‖F - H‖)) := by positivity
  have h1 := norm_Iduh_le D.hc hQ0
    (norm_GF_sub_le F H) p.1 (clamp_nonneg T p.2)
  have h3 : sqrt (clamp T p.2 / D.c) ≤ sqrt (T / D.c) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (clamp_le hT _) D.hc.le)
  rw [dist_eq_norm]
  calc ‖Iduh D.c (GF F - GF H) p.1 (clamp T p.2)‖ * (1 + ‖p.1‖) ^ 4
      ≤ 2 * π * (32 * Kp 4 * (‖F - H‖ * ‖F‖ + ‖H‖ * ‖F - H‖)) * sqrt (clamp T p.2 / D.c) := h1
    _ ≤ 2 * π * (32 * Kp 4 * (‖F - H‖ * ‖F‖ + ‖H‖ * ‖F - H‖)) * sqrt (T / D.c) := by gcongr
    _ = 2 * π * (32 * Kp 4 * (‖F‖ + ‖H‖)) * sqrt (T / D.c) * ‖F - H‖ := by ring

/-! ### O ponto fixo -/

theorem norm_Φ_le (D : Dado) {T : ℝ} (hT : 0 ≤ T) (F : X) :
    ‖Φ D hT F‖ ≤ D.M₀ + 2 * π * (32 * Kp 4 * ‖F‖ * ‖F‖) * sqrt (T / D.c) := by
  have := D.cota.nonneg
  have := Kp_nonneg 4
  exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _

/-- **Ponto fixo de Banach** na bola de raio `R`. -/
theorem ponto_fixo (D : Dado) {T R : ℝ} (hT : 0 ≤ T) (hR : 2 * D.M₀ ≤ R)
    (hδ : 128 * π * Kp 4 * R * sqrt (T / D.c) ≤ 1 / 2) :
    ∃ F : X, ‖F‖ ≤ R ∧ Φ D hT F = F := by
  have hM := D.cota.nonneg
  have hR0 : 0 ≤ R := by linarith
  have hK := Kp_nonneg 4
  have hs0 : 0 ≤ sqrt (T / D.c) := sqrt_nonneg _
  set S : Set X := Metric.closedBall 0 R
  have hS : IsComplete S := Metric.isClosed_closedBall.isComplete
  have hmem : ∀ F : X, F ∈ S ↔ ‖F‖ ≤ R := fun F => by
    rw [Metric.mem_closedBall, dist_zero_right]
  have hmaps : Set.MapsTo (Φ D hT) S S := by
    intro F hF
    rw [hmem] at hF ⊢
    have h1 := norm_Φ_le D hT F
    have hFF : ‖F‖ * ‖F‖ ≤ R * R := mul_self_le_mul_self (norm_nonneg _) hF
    have h2 : 2 * π * (32 * Kp 4 * ‖F‖ * ‖F‖) * sqrt (T / D.c) ≤ R / 4 := by
      calc 2 * π * (32 * Kp 4 * ‖F‖ * ‖F‖) * sqrt (T / D.c)
          = (64 * π * Kp 4 * sqrt (T / D.c)) * (‖F‖ * ‖F‖) := by ring
        _ ≤ (64 * π * Kp 4 * sqrt (T / D.c)) * (R * R) := by gcongr
        _ = (128 * π * Kp 4 * R * sqrt (T / D.c)) * R / 2 := by ring
        _ ≤ (1 / 2) * R / 2 := by gcongr
        _ = R / 4 := by ring
    linarith
  have hcont : ContractingWith (1 / 2 : NNReal) (hmaps.restrict (Φ D hT) S S) := by
    refine ⟨by norm_num, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq]
    simp only [Set.MapsTo.val_restrict_apply]
    have hx : ‖(x : X)‖ ≤ R := (hmem _).mp x.2
    have hy : ‖(y : X)‖ ≤ R := (hmem _).mp y.2
    have h := dist_Φ_le D hT (x : X) (y : X)
    have hd := dist_nonneg (x := (x : X)) (y := (y : X))
    calc dist (Φ D hT (x : X)) (Φ D hT (y : X))
        ≤ 2 * π * (32 * Kp 4 * (‖(x : X)‖ + ‖(y : X)‖)) * sqrt (T / D.c) * dist (x : X) y := h
      _ ≤ 2 * π * (32 * Kp 4 * (R + R)) * sqrt (T / D.c) * dist (x : X) y := by gcongr
      _ = (128 * π * Kp 4 * R * sqrt (T / D.c)) * dist (x : X) y := by ring
      _ ≤ (1 / 2) * dist (x : X) y := by gcongr
      _ = ((1 / 2 : NNReal) : ℝ) * dist (x : X) y := by norm_num
  obtain ⟨F, hFS, hfix, -, -⟩ :=
    hcont.exists_fixedPoint' hS hmaps (Metric.mem_closedBall_self hR0) (edist_ne_top _ _)
  exact ⟨F, (hmem F).mp hFS, hfix⟩

/-- **Unicidade do ponto fixo** na bola de raio `R`. -/
theorem ponto_fixo_unico (D : Dado) {T R : ℝ} (hT : 0 ≤ T)
    (hδ : 128 * π * Kp 4 * R * sqrt (T / D.c) ≤ 1 / 2) {F H : X} (hF : ‖F‖ ≤ R) (hH : ‖H‖ ≤ R)
    (hFf : Φ D hT F = F) (hHf : Φ D hT H = H) : F = H := by
  have hK := Kp_nonneg 4
  have h := dist_Φ_le D hT F H
  rw [hFf, hHf] at h
  have hd := dist_nonneg (x := F) (y := H)
  have h2 : dist F H ≤ (1 / 2) * dist F H := by
    calc dist F H ≤ 2 * π * (32 * Kp 4 * (‖F‖ + ‖H‖)) * sqrt (T / D.c) * dist F H := h
      _ ≤ 2 * π * (32 * Kp 4 * (R + R)) * sqrt (T / D.c) * dist F H := by gcongr
      _ = (128 * π * Kp 4 * R * sqrt (T / D.c)) * dist F H := by ring
      _ ≤ (1 / 2) * dist F H := by gcongr
  exact dist_le_zero.mp (by linarith)

/-! ### O tempo de existência -/

/-- O raio da bola: `2 max(M, 0) + 1`. -/
noncomputable def Rad (M : ℝ) : ℝ := 2 * max M 0 + 1

theorem Rad_pos (M : ℝ) : 0 < Rad M := by
  unfold Rad
  have := le_max_right M 0
  linarith

theorem two_le_Rad (M : ℝ) : 2 * M ≤ Rad M := by
  unfold Rad
  have := le_max_left M 0
  linarith

/-- `δ₀(M) = 1 / (256 π (K₄ + 1) R)`. -/
noncomputable def δ₀ (M : ℝ) : ℝ := 1 / (256 * π * (Kp 4 + 1) * Rad M)

theorem δ₀_pos (M : ℝ) : 0 < δ₀ M := by
  unfold δ₀
  have := Kp_nonneg 4
  have := Rad_pos M
  positivity

/-- **O tempo de existência** `T₀(c, M) = c δ₀(M)²` (depende só de `c` e da cota `M`). -/
noncomputable def T₀ (c M : ℝ) : ℝ := c * δ₀ M ^ 2

theorem T₀_pos {c : ℝ} (hc : 0 < c) (M : ℝ) : 0 < T₀ c M := by
  unfold T₀
  have := δ₀_pos M
  positivity

theorem sqrt_T₀ {c : ℝ} (hc : 0 < c) (M : ℝ) : sqrt (T₀ c M / c) = δ₀ M := by
  unfold T₀
  rw [mul_div_cancel_left₀ _ hc.ne', Real.sqrt_sq (δ₀_pos M).le]

theorem cond_T₀ {c : ℝ} (hc : 0 < c) (M : ℝ) :
    128 * π * Kp 4 * Rad M * sqrt (T₀ c M / c) ≤ 1 / 2 := by
  rw [sqrt_T₀ hc]
  unfold δ₀
  have hK := Kp_nonneg 4
  have hR := Rad_pos M
  rw [mul_one_div, div_le_iff₀ (by positivity)]
  have := mul_pos pi_pos hR
  nlinarith

/-! ### A existência local -/

/-- Uma solução contínua da equação de Duhamel em `[0, T]` (tempo congelado fora), com cota
de peso 4. -/
structure Sol (D : Dado) (T : ℝ) (v : E3 × ℝ → C3) : Prop where
  cont : Continuous v
  cota : ∃ R, ∀ s, Cota 4 R (fun η => v (η, s))
  duhamel : ∀ p, v p = duh D T v p

theorem unw_eq_duh (D : Dado) {T : ℝ} (hT : 0 ≤ T) {F : X} (hF : Φ D hT F = F)
    (p : E3 × ℝ) : unw F p = duh D T (unw F) p := by
  have h : F p = Φfun D T F p := by rw [← Φ_apply D hT F p, hF]
  show ((1 + ‖p.1‖) ^ 4)⁻¹ • F p = duh D T (unw F) p
  rw [h, Φfun, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-- **Existência local** no lado de Fourier: existe uma solução de Duhamel em `[0, T₀(c, M₀)]`. -/
theorem existe_local (D : Dado) :
    ∃ v, Sol D (T₀ D.c D.M₀) v ∧ ∀ s, Cota 4 (Rad D.M₀) (fun η => v (η, s)) := by
  have hT := (T₀_pos D.hc D.M₀).le
  obtain ⟨F, hFR, hfix⟩ := ponto_fixo D hT (two_le_Rad D.M₀) (cond_T₀ D.hc D.M₀)
  refine ⟨unw F, ⟨continuous_unw F, ⟨‖F‖, cota_unw F⟩, unw_eq_duh D hT hfix⟩, fun s => ?_⟩
  exact (cota_unw F s).mono hFR

/-! ### Divergência nula e simetria hermitiana -/

theorem leray_real_smul (ξ : E3) (r : ℝ) (a : C3) : leray ξ (r • a) = r • leray ξ a :=
  (leray ξ).map_smul_of_tower r a

theorem ip_real_smul (ξ : E3) (r : ℝ) (a : C3) : ip ξ (r • a) = (r : ℂ) * ip ξ a := by
  rw [show (r • a : C3) = (r : ℂ) • a from (Complex.coe_smul r a).symm, ip_smul]

theorem continuous_nl_slice {v : E3 × ℝ → C3} (hv : Continuous v) {R : ℝ}
    (hR : ∀ s, Cota 4 R (fun η => v (η, s))) (ξ : E3) :
    Continuous fun s : ℝ => nl (fun η => v (η, s)) (fun η => v (η, s)) ξ := by
  have h1 : Continuous fun s : ℝ => ((ξ, s) : E3 × ℝ) := continuous_const.prodMk continuous_id
  refine ((continuous_nl_param hv hv hR hR).comp h1).congr fun s => ?_
  simp only [Function.comp_apply]

/-- A integral de Duhamel de `B` é `𝐏(ξ)` de uma integral. -/
theorem Iduh_Gv (c : ℝ) {v : E3 × ℝ → C3} (hv : Continuous v) {R : ℝ}
    (hR : ∀ s, Cota 4 R (fun η => v (η, s))) (ξ : E3) (τ : ℝ) :
    Iduh c (Gv v) ξ τ = leray ξ (∫ s in (0 : ℝ)..τ,
      hk c ξ (τ - s) • (cI • nl (fun η => v (η, s)) (fun η => v (η, s)) ξ)) := by
  unfold Iduh Gv Bq
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm]
  · congr 1
    funext s
    rw [leray_real_smul]
  · refine Continuous.intervalIntegrable ?_ _ _
    have h1 : Continuous fun s : ℝ => hk c ξ (τ - s) := by
      unfold hk
      fun_prop
    exact h1.smul ((continuous_nl_slice hv hR ξ).const_smul cI)

/-- **A solução tem divergência nula** se o dado tem. -/
theorem ip_sol_eq_zero {D : Dado} {T : ℝ} {v : E3 × ℝ → C3} (hv : Sol D T v)
    (hdiv : ∀ ξ, ip ξ (D.v₀ ξ) = 0) (p : E3 × ℝ) : ip p.1 (v p) = 0 := by
  obtain ⟨R, hR⟩ := hv.cota
  rw [hv.duhamel p, duh, ip_add, ip_real_smul, hdiv, mul_zero, zero_add,
    Iduh_Gv D.c hv.cont hR, ip_leray]

/-- A conjugação como isometria `ℝ`-linear. -/
noncomputable def cjI : C3 →ₗᵢ[ℝ] C3 :=
  { cjL with norm_map' := norm_cj }

theorem cjI_apply (a : C3) : cjI a = cj a := rfl

theorem cj_integral (f : E3 → C3) : ∫ η, cj (f η) = cj (∫ η, f η) := by
  have := cjI.integral_comp_comm (μ := (volume : Measure E3)) f
  simpa [cjI_apply] using this

theorem cj_intervalIntegral (f : ℝ → C3) (a b : ℝ) :
    ∫ s in a..b, cj (f s) = cj (∫ s in a..b, f s) := by
  simp only [intervalIntegral]
  have h1 := cjI.integral_comp_comm (μ := (volume.restrict (Set.Ioc a b) : Measure ℝ)) f
  have h2 := cjI.integral_comp_comm (μ := (volume.restrict (Set.Ioc b a) : Measure ℝ)) f
  simp only [cjI_apply] at h1 h2
  rw [h1, h2, cj_sub]

theorem cj_real_smul (r : ℝ) (a : C3) : cj (r • a) = r • cj a := by
  rw [show (r • a : C3) = (r : ℂ) • a from (Complex.coe_smul r a).symm, cj_smul,
    Complex.conj_ofReal, Complex.coe_smul]

theorem conj_cI : (starRingEnd ℂ) cI = -cI := by
  simp [cI, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]

/-- `N(f̃, f̃)(ξ) = −conj N(f, f)(−ξ)` para `f̃(η) = conj f(−η)`. -/
theorem nl_cj (f : E3 → C3) (ξ : E3) :
    nl (fun η => cj (f (-η))) (fun η => cj (f (-η))) ξ = -cj (nl f f (-ξ)) := by
  unfold nl
  rw [← cj_integral, ← integral_neg]
  rw [← integral_neg_eq_self]
  congr 1
  funext η
  have e1 : -(ξ - -η) = -ξ - η := by abel
  simp only []
  rw [e1, neg_neg, cj_smul, ip_neg_left, map_neg, neg_smul, neg_neg, ip_cj]

theorem Bq_cj (f : E3 → C3) (ξ : E3) :
    Bq (fun η => cj (f (-η))) ξ = cj (Bq f (-ξ)) := by
  unfold Bq
  rw [nl_cj, ← leray_cj, leray_neg, cj_smul, conj_cI, smul_neg, neg_smul]

/-- `S F (ξ, t) = conj F(−ξ, t)`. -/
noncomputable def Sfun (F : X) (p : E3 × ℝ) : C3 := cj (F (-p.1, p.2))

theorem continuous_Sfun (F : X) : Continuous (Sfun F) :=
  cjL.continuous.comp (F.continuous.comp (by fun_prop))

/-- A simetria hermitiana no espaço com peso. -/
noncomputable def S (F : X) : X :=
  BoundedContinuousFunction.ofNormedAddCommGroup (Sfun F) (continuous_Sfun F) ‖F‖ fun p => by
    rw [Sfun, norm_cj]
    exact F.norm_coe_le_norm _

theorem S_apply (F : X) (p : E3 × ℝ) : S F p = cj (F (-p.1, p.2)) := rfl

theorem norm_S_le (F : X) : ‖S F‖ ≤ ‖F‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg _) _

theorem unw_S (F : X) (ξ : E3) (t : ℝ) : unw (S F) (ξ, t) = cj (unw F (-ξ, t)) := by
  simp only [unw, S_apply, norm_neg, cj_real_smul]

theorem Gv_unw_S (F : X) (ξ : E3) (s : ℝ) :
    Gv (unw (S F)) (ξ, s) = cj (Gv (unw F) (-ξ, s)) := by
  unfold Gv
  simp only [unw_S]
  exact Bq_cj (fun η => unw F (η, s)) ξ

theorem hk_neg (c : ℝ) (ξ : E3) (τ : ℝ) : hk c (-ξ) τ = hk c ξ τ := by
  simp [hk]

theorem Iduh_unw_S (c : ℝ) (F : X) (ξ : E3) (τ : ℝ) :
    Iduh c (Gv (unw (S F))) ξ τ = cj (Iduh c (Gv (unw F)) (-ξ) τ) := by
  unfold Iduh
  rw [← cj_intervalIntegral]
  congr 1
  funext s
  rw [Gv_unw_S, cj_real_smul, hk_neg]

/-- `Φ` comuta com a simetria hermitiana quando o dado é hermitiano. -/
theorem Φ_S (D : Dado) {T : ℝ} (hT : 0 ≤ T) (hherm : ∀ ξ, D.v₀ (-ξ) = cj (D.v₀ ξ)) (F : X) :
    Φ D hT (S F) = S (Φ D hT F) := by
  ext p
  obtain ⟨ξ, t⟩ := p
  rw [Φ_apply, S_apply, Φ_apply]
  simp only [Φfun, duh, Iduh_unw_S, norm_neg, hk_neg]
  rw [cj_real_smul, cj_add, cj_real_smul, ← hherm, neg_neg]

/-- **Existência local com divergência nula e simetria hermitiana.** -/
theorem existe_local_sim (D : Dado) (hdiv : ∀ ξ, ip ξ (D.v₀ ξ) = 0)
    (hherm : ∀ ξ, D.v₀ (-ξ) = cj (D.v₀ ξ)) :
    ∃ v, Sol D (T₀ D.c D.M₀) v ∧ (∀ s, Cota 4 (Rad D.M₀) (fun η => v (η, s))) ∧
      (∀ p, ip p.1 (v p) = 0) ∧ ∀ ξ t, v (-ξ, t) = cj (v (ξ, t)) := by
  have hT := (T₀_pos D.hc D.M₀).le
  obtain ⟨F, hFR, hfix⟩ := ponto_fixo D hT (two_le_Rad D.M₀) (cond_T₀ D.hc D.M₀)
  have hsol : Sol D (T₀ D.c D.M₀) (unw F) :=
    ⟨continuous_unw F, ⟨‖F‖, cota_unw F⟩, unw_eq_duh D hT hfix⟩
  have hSF : S F = F :=
    ponto_fixo_unico D hT (cond_T₀ D.hc D.M₀) ((norm_S_le F).trans hFR) hFR
      (by rw [Φ_S D hT hherm, hfix]) hfix
  refine ⟨unw F, hsol, fun s => (cota_unw F s).mono hFR, ip_sol_eq_zero hsol hdiv,
    fun ξ t => ?_⟩
  have := unw_S F (-ξ) t
  rw [hSF, neg_neg] at this
  exact this

end ATK.NSPicard

#print axioms ATK.NSPicard.Cota
#print axioms ATK.NSPicard.Cota.nonneg
#print axioms ATK.NSPicard.Cota.le
#print axioms ATK.NSPicard.Cota.le_inv
#print axioms ATK.NSPicard.Cota.sub
#print axioms ATK.NSPicard.Cota.mono
#print axioms ATK.NSPicard.nl
#print axioms ATK.NSPicard.continuous_ip_comp
#print axioms ATK.NSPicard.integrable_nl
#print axioms ATK.NSPicard.norm_nl_le_conv
#print axioms ATK.NSPicard.norm_nl_le
#print axioms ATK.NSPicard.norm_nl_le4
#print axioms ATK.NSPicard.nl_sub_left
#print axioms ATK.NSPicard.nl_sub_right
#print axioms ATK.NSPicard.nl_sub_nl
#print axioms ATK.NSPicard.cI
#print axioms ATK.NSPicard.norm_cI
#print axioms ATK.NSPicard.Bq
#print axioms ATK.NSPicard.norm_Bq_le_nl
#print axioms ATK.NSPicard.norm_Bq_le
#print axioms ATK.NSPicard.Bq_sub
#print axioms ATK.NSPicard.norm_Bq_sub_le
#print axioms ATK.NSPicard.continuous_cx
#print axioms ATK.NSPicard.continuous_ip
#print axioms ATK.NSPicard.continuousAt_leray
#print axioms ATK.NSPicard.nl_zero_left
#print axioms ATK.NSPicard.Bq_zero
#print axioms ATK.NSPicard.continuous_nl_param
#print axioms ATK.NSPicard.continuous_Bq_param
#print axioms ATK.NSPicard.Dado
#print axioms ATK.NSPicard.clamp
#print axioms ATK.NSPicard.clamp_nonneg
#print axioms ATK.NSPicard.clamp_le
#print axioms ATK.NSPicard.clamp_of_mem
#print axioms ATK.NSPicard.clamp_clamp
#print axioms ATK.NSPicard.continuous_clamp
#print axioms ATK.NSPicard.hk
#print axioms ATK.NSPicard.continuous_hk
#print axioms ATK.NSPicard.hk_le_one
#print axioms ATK.NSPicard.hk_pos
#print axioms ATK.NSPicard.Iduh
#print axioms ATK.NSPicard.intervalIntegrable_duh
#print axioms ATK.NSPicard.norm_Iduh_le
#print axioms ATK.NSPicard.Iduh_sub
#print axioms ATK.NSPicard.Gv
#print axioms ATK.NSPicard.duh
#print axioms ATK.NSPicard.duh_clamp
#print axioms ATK.NSPicard.X
#print axioms ATK.NSPicard.unw
#print axioms ATK.NSPicard.continuous_unw
#print axioms ATK.NSPicard.cota_unw
#print axioms ATK.NSPicard.unw_sub
#print axioms ATK.NSPicard.weight_unw
#print axioms ATK.NSPicard.GF
#print axioms ATK.NSPicard.continuous_GF
#print axioms ATK.NSPicard.norm_GF_le
#print axioms ATK.NSPicard.norm_GF_sub_le
#print axioms ATK.NSPicard.Φfun
#print axioms ATK.NSPicard.continuous_Φfun
#print axioms ATK.NSPicard.norm_Φfun_le
#print axioms ATK.NSPicard.Φ
#print axioms ATK.NSPicard.Φ_apply
#print axioms ATK.NSPicard.Φfun_sub
#print axioms ATK.NSPicard.dist_Φ_le
#print axioms ATK.NSPicard.norm_Φ_le
#print axioms ATK.NSPicard.ponto_fixo
#print axioms ATK.NSPicard.ponto_fixo_unico
#print axioms ATK.NSPicard.Rad
#print axioms ATK.NSPicard.Rad_pos
#print axioms ATK.NSPicard.two_le_Rad
#print axioms ATK.NSPicard.δ₀
#print axioms ATK.NSPicard.δ₀_pos
#print axioms ATK.NSPicard.T₀
#print axioms ATK.NSPicard.T₀_pos
#print axioms ATK.NSPicard.sqrt_T₀
#print axioms ATK.NSPicard.cond_T₀
#print axioms ATK.NSPicard.Sol
#print axioms ATK.NSPicard.unw_eq_duh
#print axioms ATK.NSPicard.existe_local
#print axioms ATK.NSPicard.leray_real_smul
#print axioms ATK.NSPicard.ip_real_smul
#print axioms ATK.NSPicard.continuous_nl_slice
#print axioms ATK.NSPicard.Iduh_Gv
#print axioms ATK.NSPicard.ip_sol_eq_zero
#print axioms ATK.NSPicard.cjI
#print axioms ATK.NSPicard.cjI_apply
#print axioms ATK.NSPicard.cj_integral
#print axioms ATK.NSPicard.cj_intervalIntegral
#print axioms ATK.NSPicard.cj_real_smul
#print axioms ATK.NSPicard.conj_cI
#print axioms ATK.NSPicard.nl_cj
#print axioms ATK.NSPicard.Bq_cj
#print axioms ATK.NSPicard.Sfun
#print axioms ATK.NSPicard.continuous_Sfun
#print axioms ATK.NSPicard.S
#print axioms ATK.NSPicard.S_apply
#print axioms ATK.NSPicard.norm_S_le
#print axioms ATK.NSPicard.unw_S
#print axioms ATK.NSPicard.Gv_unw_S
#print axioms ATK.NSPicard.hk_neg
#print axioms ATK.NSPicard.Iduh_unw_S
#print axioms ATK.NSPicard.Φ_S
#print axioms ATK.NSPicard.existe_local_sim
