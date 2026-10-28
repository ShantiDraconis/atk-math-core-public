import ATK.NSPicard

/-!
# ATK — Navier–Stokes no lado de Fourier, marco NS3: persistência dos pesos e regularidade em `t`

Ponte B3, marco NS3. Para uma solução de Duhamel `v` em `[0, T]` (`NSPicard.Sol`):

* **`persist`**: se o dado tem cota de peso `(1+|ξ|)^m`, a solução também tem (em todo `[0, T]`,
  sem encolher o intervalo). Prova: pesos truncados `min((1+|ξ|)^m, L)` (para os quais a cota é
  finita a priori), o truque do peso exponencial `e^{−λt}` e o supremo; depois `L → ∞` ponto a
  ponto;
* derivação sob a integral **dentro** de um conjunto convexo (`hasDerivWithinAt_integral`);
* a classe `Suave T k` das funções `g(ξ, t)` com `k` derivadas em `t` dentro de `[0, T]`, todas
  contínuas em `ξ` e com cotas de todos os pesos; fechada pela não linearidade bilinear;
* **`sol_suave`**: a solução está em `Suave T k` para todo `k`.

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta**; **CLOSED_MATH continua
false**.
-/

set_option autoImplicit false

open MeasureTheory Real Filter Topology Set
open ATK.LigacaoNS (E3)
open ATK.NSFourierBase ATK.NSPicard

namespace ATK.NSRegular

/-! ### Convolução com peso geral -/

/-- **Convolução com um peso geral** `W` que satisfaz `W(ξ) ≤ P (W(ξ−η) + W(η))`. -/
theorem conv_bound_W {f g : E3 → ℝ} (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g)
    (hf0 : ∀ ζ, 0 ≤ f ζ) (hg0 : ∀ ζ, 0 ≤ g ζ) {W : E3 → ℝ} (hW0 : ∀ ζ, 0 ≤ W ζ) {P : ℝ}
    (hP0 : 0 ≤ P) (hP : ∀ ξ η, W ξ ≤ P * (W (ξ - η) + W η)) {A₄ AW B₄ BW : ℝ}
    (hA₄ : ∀ ζ, f ζ * (1 + ‖ζ‖) ^ 4 ≤ A₄) (hAW : ∀ ζ, f ζ * W ζ ≤ AW)
    (hB₄ : ∀ ζ, g ζ * (1 + ‖ζ‖) ^ 4 ≤ B₄) (hBW : ∀ ζ, g ζ * W ζ ≤ BW) (ξ : E3) :
    (∫ η, f (ξ - η) * g η) * W ξ ≤ P * Kp 4 * (AW * B₄ + A₄ * BW) := by
  have hint := integrable_conv hf hg hf0 hg0 hA₄ hB₄ ξ
  have hAW0 : 0 ≤ AW := le_trans (mul_nonneg (hf0 0) (hW0 0)) (hAW 0)
  have hBW0 : 0 ≤ BW := le_trans (mul_nonneg (hg0 0) (hW0 0)) (hBW 0)
  have hpt : ∀ η, f (ξ - η) * g η * W ξ ≤
      P * (AW * B₄ * ((1 + ‖η‖) ^ 4)⁻¹ + A₄ * BW * ((1 + ‖ξ - η‖) ^ 4)⁻¹) := by
    intro η
    have hfg : 0 ≤ f (ξ - η) * g η := mul_nonneg (hf0 _) (hg0 _)
    have e1 : f (ξ - η) * W (ξ - η) * g η ≤ AW * (B₄ * ((1 + ‖η‖) ^ 4)⁻¹) :=
      mul_le_mul (hAW _) (le_of_mul_le hB₄ η) (hg0 _) hAW0
    have e2 : f (ξ - η) * (g η * W η) ≤ (A₄ * ((1 + ‖ξ - η‖) ^ 4)⁻¹) * BW :=
      mul_le_mul (le_of_mul_le hA₄ _) (hBW _) (mul_nonneg (hg0 η) (hW0 η))
        (by have := le_of_mul_le hA₄ (ξ - η); nlinarith [hf0 (ξ - η)])
    calc f (ξ - η) * g η * W ξ
        ≤ f (ξ - η) * g η * (P * (W (ξ - η) + W η)) := mul_le_mul_of_nonneg_left (hP ξ η) hfg
      _ = P * (f (ξ - η) * W (ξ - η) * g η + f (ξ - η) * (g η * W η)) := by ring
      _ ≤ P * (AW * (B₄ * ((1 + ‖η‖) ^ 4)⁻¹) + (A₄ * ((1 + ‖ξ - η‖) ^ 4)⁻¹) * BW) := by
          gcongr
      _ = P * (AW * B₄ * ((1 + ‖η‖) ^ 4)⁻¹ + A₄ * BW * ((1 + ‖ξ - η‖) ^ 4)⁻¹) := by ring
  have hI1 := integrable_inv_pow (m := 4) le_rfl
  have hI2 := integrable_inv_pow_sub le_rfl ξ
  have hR : Integrable (fun η : E3 =>
      P * (AW * B₄ * ((1 + ‖η‖) ^ 4)⁻¹ + A₄ * BW * ((1 + ‖ξ - η‖) ^ 4)⁻¹)) :=
    ((hI1.const_mul _).add (hI2.const_mul _)).const_mul _
  rw [← integral_mul_const]
  calc ∫ η, f (ξ - η) * g η * W ξ
      ≤ ∫ η : E3, P * (AW * B₄ * ((1 + ‖η‖) ^ 4)⁻¹ + A₄ * BW * ((1 + ‖ξ - η‖) ^ 4)⁻¹) :=
        integral_mono (hint.mul_const _) hR hpt
    _ = P * Kp 4 * (AW * B₄ + A₄ * BW) := by
        rw [integral_const_mul, integral_add (hI1.const_mul _) (hI2.const_mul _),
          integral_const_mul, integral_const_mul, integral_inv_pow_sub]
        unfold Kp
        ring

/-- Cota de `N(f, g)` com peso geral. -/
theorem norm_nl_le_W {f g : E3 → C3} (hf : Continuous f) (hg : Continuous g) {W : E3 → ℝ}
    (hW0 : ∀ ζ, 0 ≤ W ζ) {P : ℝ} (hP0 : 0 ≤ P) (hP : ∀ ξ η, W ξ ≤ P * (W (ξ - η) + W η))
    {A₄ AW B₄ BW : ℝ} (hA₄ : Cota 4 A₄ f) (hAW : ∀ ζ, ‖f ζ‖ * W ζ ≤ AW) (hB₄ : Cota 4 B₄ g)
    (hBW : ∀ ζ, ‖g ζ‖ * W ζ ≤ BW) (ξ : E3) :
    ‖nl f g ξ‖ * W ξ ≤ ‖ξ‖ * (P * Kp 4 * (AW * B₄ + A₄ * BW)) := by
  have hc := conv_bound_W (f := fun ζ => ‖f ζ‖) (g := fun ζ => ‖g ζ‖)
    hf.norm.aestronglyMeasurable hg.norm.aestronglyMeasurable (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hW0 hP0 hP hA₄ hAW hB₄ hBW ξ
  have h1 := norm_nl_le_conv hf hg hA₄ hB₄ ξ
  calc ‖nl f g ξ‖ * W ξ ≤ (‖ξ‖ * ∫ η, ‖f (ξ - η)‖ * ‖g η‖) * W ξ :=
        mul_le_mul_of_nonneg_right h1 (hW0 ξ)
    _ = ‖ξ‖ * ((∫ η, ‖f (ξ - η)‖ * ‖g η‖) * W ξ) := by ring
    _ ≤ ‖ξ‖ * (P * Kp 4 * (AW * B₄ + A₄ * BW)) := mul_le_mul_of_nonneg_left hc (norm_nonneg _)

/-! ### Pesos truncados -/

/-- O peso truncado `min((1+|ξ|)^m, L)`. -/
noncomputable def Wt (m : ℕ) (L : ℝ) (ξ : E3) : ℝ := min ((1 + ‖ξ‖) ^ m) L

theorem Wt_nonneg {m : ℕ} {L : ℝ} (hL : 0 ≤ L) (ξ : E3) : 0 ≤ Wt m L ξ :=
  le_min (by positivity) hL

theorem Wt_le_pow (m : ℕ) (L : ℝ) (ξ : E3) : Wt m L ξ ≤ (1 + ‖ξ‖) ^ m := min_le_left _ _

theorem Wt_le_L (m : ℕ) (L : ℝ) (ξ : E3) : Wt m L ξ ≤ L := min_le_right _ _

theorem Wt_of_le {m : ℕ} {L : ℝ} {ξ : E3} (h : (1 + ‖ξ‖) ^ m ≤ L) : Wt m L ξ = (1 + ‖ξ‖) ^ m :=
  min_eq_left h

/-- **Peetre para o peso truncado.** -/
theorem Wt_peetre {m : ℕ} {L : ℝ} (hL : 0 ≤ L) (ξ η : E3) :
    Wt m L ξ ≤ 2 ^ m * (Wt m L (ξ - η) + Wt m L η) := by
  have h2 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  by_cases h1 : L ≤ (1 + ‖ξ - η‖) ^ m
  · rw [show Wt m L (ξ - η) = L from min_eq_right h1]
    have := Wt_le_L m L ξ
    have := Wt_nonneg (m := m) hL η
    nlinarith
  by_cases h3 : L ≤ (1 + ‖η‖) ^ m
  · rw [show Wt m L η = L from min_eq_right h3]
    have := Wt_le_L m L ξ
    have := Wt_nonneg (m := m) hL (ξ - η)
    nlinarith
  rw [not_le] at h1 h3
  rw [show Wt m L (ξ - η) = (1 + ‖ξ - η‖) ^ m from min_eq_left h1.le,
    show Wt m L η = (1 + ‖η‖) ^ m from min_eq_left h3.le]
  exact (Wt_le_pow m L ξ).trans (one_add_norm_pow_le ξ η m)

/-! ### O núcleo com peso exponencial -/

/-- `|ξ| ∫₀ᵗ e^{−c|ξ|²(t−s)} e^{λs} ds ≤ e^{λt} / (2√(cλ))`. -/
theorem kernel_exp_bound {c lam : ℝ} (hc : 0 < c) (hl : 0 < lam) (t : ℝ) (ξ : E3) :
    ‖ξ‖ * ∫ s in (0 : ℝ)..t, hk c ξ (t - s) * exp (lam * s) ≤
      exp (lam * t) / (2 * sqrt (c * lam)) := by
  set A := c * ‖ξ‖ ^ 2 + lam
  have hA : 0 < A := by positivity
  have he : ∀ s, hk c ξ (t - s) * exp (lam * s) = exp (lam * t) * exp (-(A * (t - s))) := by
    intro s
    simp only [hk, A, ← exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, integral_heat hA]
  have h1 : (1 - exp (-(A * t))) / A ≤ 1 / A := by
    gcongr
    have := exp_pos (-(A * t))
    linarith
  have hcl : 0 < sqrt (c * lam) := Real.sqrt_pos.mpr (by positivity)
  have h2 : 2 * ‖ξ‖ * sqrt (c * lam) ≤ A := by
    have hs : sqrt (c * lam) = sqrt c * sqrt lam := Real.sqrt_mul hc.le lam
    have hc' := Real.sq_sqrt hc.le
    have hl' := Real.sq_sqrt hl.le
    rw [hs]
    nlinarith [sq_nonneg (sqrt c * ‖ξ‖ - sqrt lam), Real.sqrt_nonneg c, Real.sqrt_nonneg lam]
  have hE := exp_pos (lam * t)
  calc ‖ξ‖ * (exp (lam * t) * ((1 - exp (-(A * t))) / A))
      ≤ ‖ξ‖ * (exp (lam * t) * (1 / A)) := by gcongr
    _ = exp (lam * t) * ‖ξ‖ / A := by ring
    _ ≤ exp (lam * t) / (2 * sqrt (c * lam)) := by
        rw [div_le_div_iff₀ hA (by positivity)]
        nlinarith [norm_nonneg ξ]

/-- Cota da integral de Duhamel com peso exponencial no tempo. -/
theorem norm_Iduh_le_exp {c lam : ℝ} (hc : 0 < c) (hl : 0 < lam) {G : E3 × ℝ → C3}
    {W : E3 → ℝ} {Q : ℝ} (ξ : E3) {τ : ℝ} (hτ : 0 ≤ τ) (hW : 0 ≤ W ξ)
    (hQ : ∀ s ∈ Icc 0 τ, ‖G (ξ, s)‖ * W ξ ≤ ‖ξ‖ * Q * exp (lam * s)) (hQ0 : 0 ≤ Q) :
    ‖Iduh c G ξ τ‖ * W ξ ≤ Q * (exp (lam * τ) / (2 * sqrt (c * lam))) := by
  have hpt : ∀ s ∈ Ioc 0 τ, ‖hk c ξ (τ - s) • G (ξ, s)‖ * W ξ ≤
      hk c ξ (τ - s) * (‖ξ‖ * Q * exp (lam * s)) := by
    intro s hs
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hk_pos _ _ _), mul_assoc]
    exact mul_le_mul_of_nonneg_left (hQ s ⟨hs.1.le, hs.2⟩) (hk_pos _ _ _).le
  have hcont : Continuous fun s : ℝ => hk c ξ (τ - s) * (‖ξ‖ * Q * exp (lam * s)) := by
    unfold hk
    fun_prop
  have h1 : ‖Iduh c G ξ τ‖ * W ξ ≤
      (∫ s in (0 : ℝ)..τ, hk c ξ (τ - s) * (‖ξ‖ * Q * exp (lam * s))) := by
    rcases hW.lt_or_eq with hWp | hW0
    · rw [← le_div_iff₀ hWp, ← intervalIntegral.integral_div]
      refine intervalIntegral.norm_integral_le_of_norm_le hτ
        (Eventually.of_forall fun s hs => ?_) ((hcont.div_const _).intervalIntegrable _ _)
      rw [le_div_iff₀ hWp]
      exact hpt s hs
    · rw [← hW0, mul_zero]
      refine intervalIntegral.integral_nonneg hτ fun s _ => ?_
      have := hk_pos c ξ (τ - s)
      have := exp_pos (lam * s)
      positivity
  have h2 : (∫ s in (0 : ℝ)..τ, hk c ξ (τ - s) * (‖ξ‖ * Q * exp (lam * s))) =
      Q * (‖ξ‖ * ∫ s in (0 : ℝ)..τ, hk c ξ (τ - s) * exp (lam * s)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    congr 1
    funext s
    ring
  rw [h2] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (kernel_exp_bound hc hl τ ξ) hQ0)

/-! ### Persistência dos pesos -/

end ATK.NSRegular

namespace ATK.NSPicard

/-- A solução é congelada fora de `[0, T]`. -/
theorem Sol.congela {D : Dado} {T : ℝ} (hT : 0 ≤ T) {v : E3 × ℝ → C3} (hv : Sol D T v)
    (ξ : E3) (t : ℝ) : v (ξ, t) = v (ξ, clamp T t) := by
  rw [hv.duhamel (ξ, t), hv.duhamel (ξ, clamp T t), duh_clamp D hT]

theorem Sol.eq_of_mem {D : Dado} {T : ℝ} {v : E3 × ℝ → C3} (hv : Sol D T v) {ξ : E3} {t : ℝ}
    (ht : t ∈ Icc 0 T) : v (ξ, t) = hk D.c ξ t • D.v₀ ξ + Iduh D.c (Gv v) ξ t := by
  rw [hv.duhamel (ξ, t), duh, clamp_of_mem ht]

end ATK.NSPicard

namespace ATK.NSRegular

/-- **Persistência dos pesos**: cotas de peso `(1+|ξ|)^m` do dado passam à solução em todo
`[0, T]`. -/
theorem persist {D : Dado} {T : ℝ} (hT : 0 ≤ T) {v : E3 × ℝ → C3} (hv : Sol D T v) {R : ℝ}
    (hR : ∀ s, Cota 4 R (fun η => v (η, s))) (m : ℕ) {M : ℝ} (hM : Cota m M D.v₀) :
    ∃ C, ∀ s, Cota m C (fun η => v (η, s)) := by
  have hR0 : 0 ≤ R := (hR 0).nonneg
  have hM0 : 0 ≤ M := hM.nonneg
  have hK := Kp_nonneg 4
  have hc := D.hc
  set q : ℝ := 4 * π * 2 ^ m * Kp 4 * R with hq_def
  have hq0 : 0 ≤ q := by positivity
  set lam : ℝ := q ^ 2 / D.c + 1 with hlam
  have hl : 0 < lam := by positivity
  have hsq : q ≤ sqrt (D.c * lam) := by
    have h1 : D.c * lam = q ^ 2 + D.c := by
      rw [hlam]
      field_simp
    rw [h1]
    calc q = sqrt (q ^ 2) := (Real.sqrt_sq hq0).symm
      _ ≤ sqrt (q ^ 2 + D.c) := Real.sqrt_le_sqrt (by linarith)
  have hsp : 0 < sqrt (D.c * lam) := Real.sqrt_pos.mpr (by positivity)
  have hq : q / (2 * sqrt (D.c * lam)) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have key : ∀ L : ℝ, 0 ≤ L → ∀ ξ, ∀ t ∈ Icc 0 T,
      ‖v (ξ, t)‖ * Wt m L ξ ≤ 2 * M * exp (lam * T) := by
    intro L hL
    set S : Set ℝ := {z | ∃ ξ, ∃ t ∈ Icc 0 T, z = exp (-(lam * t)) * (‖v (ξ, t)‖ * Wt m L ξ)}
    have hbdd : BddAbove S := by
      refine ⟨R * L, ?_⟩
      rintro z ⟨ξ, t, ht, rfl⟩
      have e1 : exp (-(lam * t)) ≤ 1 := by
        rw [exp_le_one_iff]
        have := mul_nonneg hl.le ht.1
        linarith
      have e2 : ‖v (ξ, t)‖ ≤ R := (hR t).le ξ
      have e3 := Wt_le_L m L ξ
      have e4 := Wt_nonneg (m := m) hL ξ
      calc exp (-(lam * t)) * (‖v (ξ, t)‖ * Wt m L ξ) ≤ 1 * (R * L) := by
            gcongr
        _ = R * L := one_mul _
    have hne : S.Nonempty := ⟨_, 0, 0, ⟨le_rfl, hT⟩, rfl⟩
    set Z := sSup S
    have hZ : ∀ ξ, ∀ t ∈ Icc 0 T, exp (-(lam * t)) * (‖v (ξ, t)‖ * Wt m L ξ) ≤ Z :=
      fun ξ t ht => le_csSup hbdd ⟨ξ, t, ht, rfl⟩
    have hZ0 : 0 ≤ Z := le_trans (by have := Wt_nonneg (m := m) hL 0; positivity)
      (hZ 0 0 ⟨le_rfl, hT⟩)
    have hslice : ∀ s ∈ Icc 0 T, ∀ ζ, ‖v (ζ, s)‖ * Wt m L ζ ≤ Z * exp (lam * s) := by
      intro s hs ζ
      have := hZ ζ s hs
      rw [exp_neg, inv_mul_le_iff₀ (exp_pos _)] at this
      linarith
    have hstep : ∀ ξ, ∀ t ∈ Icc 0 T,
        exp (-(lam * t)) * (‖v (ξ, t)‖ * Wt m L ξ) ≤ M + Z / 2 := by
      intro ξ t ht
      have hW0 := Wt_nonneg (m := m) hL ξ
      rw [hv.eq_of_mem ht]
      have hv0 : ‖hk D.c ξ t • D.v₀ ξ‖ * Wt m L ξ ≤ M := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hk_pos _ _ _)]
        calc hk D.c ξ t * ‖D.v₀ ξ‖ * Wt m L ξ ≤ 1 * ‖D.v₀ ξ‖ * (1 + ‖ξ‖) ^ m := by
              gcongr
              · exact hk_le_one hc.le ht.1 ξ
              · exact Wt_le_pow m L ξ
          _ ≤ M := by rw [one_mul]; exact hM ξ
      have hG : ∀ s ∈ Icc 0 t, ‖Gv v (ξ, s)‖ * Wt m L ξ ≤ ‖ξ‖ * (q * Z) * exp (lam * s) := by
        intro s hs
        have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans ht.2⟩
        have hvs : Continuous fun η => v (η, s) := hv.cont.comp (by fun_prop)
        have hb := norm_Bq_le_nl (fun η => v (η, s)) ξ
        have hn := norm_nl_le_W hvs hvs (fun ζ => Wt_nonneg (m := m) hL ζ) (by positivity)
          (Wt_peetre (m := m) hL) (hR s) (hslice s hsT) (hR s) (hslice s hsT) ξ
        calc ‖Gv v (ξ, s)‖ * Wt m L ξ
            ≤ 2 * π * ‖nl (fun η => v (η, s)) (fun η => v (η, s)) ξ‖ * Wt m L ξ := by
              unfold Gv
              gcongr
          _ = 2 * π * (‖nl (fun η => v (η, s)) (fun η => v (η, s)) ξ‖ * Wt m L ξ) := by ring
          _ ≤ 2 * π * (‖ξ‖ * (2 ^ m * Kp 4 * (Z * exp (lam * s) * R + R * (Z * exp (lam * s))))) := by
              gcongr
          _ = ‖ξ‖ * (q * Z) * exp (lam * s) := by
              rw [hq_def]
              ring
      have hI := norm_Iduh_le_exp hc hl ξ ht.1 hW0 hG (by positivity)
      have h3 := norm_add_le (hk D.c ξ t • D.v₀ ξ) (Iduh D.c (Gv v) ξ t)
      have he : exp (-(lam * t)) * exp (lam * t) = 1 := by rw [← exp_add]; simp
      have heb : exp (-(lam * t)) ≤ 1 := by
        rw [exp_le_one_iff]
        have := mul_nonneg hl.le ht.1
        linarith
      calc exp (-(lam * t)) * (‖hk D.c ξ t • D.v₀ ξ + Iduh D.c (Gv v) ξ t‖ * Wt m L ξ)
          ≤ exp (-(lam * t)) * ((‖hk D.c ξ t • D.v₀ ξ‖ + ‖Iduh D.c (Gv v) ξ t‖) * Wt m L ξ) := by
            gcongr
        _ = exp (-(lam * t)) * (‖hk D.c ξ t • D.v₀ ξ‖ * Wt m L ξ) +
            exp (-(lam * t)) * (‖Iduh D.c (Gv v) ξ t‖ * Wt m L ξ) := by ring
        _ ≤ 1 * M + exp (-(lam * t)) * (q * Z * (exp (lam * t) / (2 * sqrt (D.c * lam)))) := by
            gcongr
        _ = M + Z * (q / (2 * sqrt (D.c * lam))) := by
            rw [one_mul, mul_div_assoc', mul_div_assoc', ← mul_assoc, mul_comm _ (q * Z),
              mul_assoc, he]
            ring
        _ ≤ M + Z * (1 / 2) := by gcongr
        _ = M + Z / 2 := by ring
    have hZle : Z ≤ M + Z / 2 := csSup_le hne (by rintro z ⟨ξ, t, ht, rfl⟩; exact hstep ξ t ht)
    intro ξ t ht
    have h1 := hZ ξ t ht
    rw [exp_neg, inv_mul_le_iff₀ (exp_pos _)] at h1
    have h2 : exp (lam * t) ≤ exp (lam * T) := exp_le_exp.mpr (by nlinarith [ht.2])
    calc ‖v (ξ, t)‖ * Wt m L ξ ≤ exp (lam * t) * Z := h1
      _ ≤ exp (lam * T) * (2 * M) := by
          gcongr
          linarith
      _ = 2 * M * exp (lam * T) := by ring
  refine ⟨2 * M * exp (lam * T), fun s ζ => ?_⟩
  simp only
  rw [hv.congela hT ζ s]
  have := key ((1 + ‖ζ‖) ^ m) (by positivity) ζ (clamp T s) ⟨clamp_nonneg _ _, clamp_le hT _⟩
  rwa [Wt_of_le le_rfl] at this

/-! ### Derivação sob a integral dentro de um convexo -/

/-- **Derivação sob o sinal de integral, dentro de um convexo** (com dominação uniforme da
derivada). -/
theorem hasDerivWithinAt_integral {F F' : ℝ → E3 → C3} {s : Set ℝ} (hs : Convex ℝ s) {t₀ : ℝ}
    (ht₀ : t₀ ∈ s) (hmeas : ∀ t ∈ s, AEStronglyMeasurable (F t)) (hint : Integrable (F t₀))
    {b : E3 → ℝ} (hb : Integrable b)
    (hderiv : ∀ η, ∀ t ∈ s, HasDerivWithinAt (fun t => F t η) (F' t η) s t)
    (hbound : ∀ η, ∀ t ∈ s, ‖F' t η‖ ≤ b η) :
    HasDerivWithinAt (fun t => ∫ η, F t η) (∫ η, F' t₀ η) s t₀ := by
  -- MVT: `‖F t η − F t₀ η‖ ≤ b η |t − t₀|`
  have hmvt : ∀ η, ∀ t ∈ s, ‖F t η - F t₀ η‖ ≤ b η * ‖t - t₀‖ := fun η t ht =>
    hs.norm_image_sub_le_of_norm_hasDerivWithin_le (hderiv η) (hbound η) ht₀ ht
  have hintt : ∀ t ∈ s, Integrable (F t) := by
    intro t ht
    have h1 : Integrable (fun η => F t η - F t₀ η) :=
      (hb.mul_const ‖t - t₀‖).mono' ((hmeas t ht).sub hint.aestronglyMeasurable)
        (Eventually.of_forall fun η => hmvt η t ht)
    have := h1.add hint
    refine this.congr (Eventually.of_forall fun η => ?_)
    simp
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hev : ∀ᶠ t in 𝓝[s \ {t₀}] t₀, t ∈ s \ {t₀} := self_mem_nhdsWithin
  have hslope : ∀ᶠ t in 𝓝[s \ {t₀}] t₀,
      slope (fun t => ∫ η, F t η) t₀ t = ∫ η, slope (fun t => F t η) t₀ t := by
    filter_upwards [hev] with t ht
    simp only [slope_def_module]
    rw [integral_smul, integral_sub (hintt t ht.1) hint]
  refine Tendsto.congr' (EventuallyEq.symm hslope) ?_
  refine tendsto_integral_filter_of_dominated_convergence b ?_ ?_ hb ?_
  · filter_upwards [hev] with t ht
    simp only [slope_def_module]
    exact (((hmeas t ht.1).sub hint.aestronglyMeasurable).const_smul (t - t₀)⁻¹)
  · filter_upwards [hev] with t ht
    refine Eventually.of_forall fun η => ?_
    simp only [slope_def_module]
    have hne : t - t₀ ≠ 0 := sub_ne_zero.mpr ht.2
    rw [norm_smul, norm_inv]
    have := hmvt η t ht.1
    rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hne)]
    linarith [mul_comm (b η) ‖t - t₀‖]
  · exact Eventually.of_forall fun η =>
      (hasDerivWithinAt_iff_tendsto_slope.mp (hderiv η t₀ ht₀))

/-! ### A classe das funções suaves em `t` com todos os pesos -/

/-- `g(·, t)` contínua para cada `t` e cotas de todos os pesos, uniformes em `[0, T]`. -/
def Reg0 (T : ℝ) (g : E3 × ℝ → C3) : Prop :=
  (∀ t ∈ Icc 0 T, Continuous fun ξ => g (ξ, t)) ∧
    ∀ m : ℕ, ∃ C, ∀ t ∈ Icc 0 T, Cota m C (fun ξ => g (ξ, t))

/-- `k` derivadas em `t` dentro de `[0, T]`, todas em `Reg0`. -/
def Suave (T : ℝ) : ℕ → (E3 × ℝ → C3) → Prop
  | 0, g => Reg0 T g
  | k + 1, g => Reg0 T g ∧ ∃ g', Suave T k g' ∧
      ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => g (ξ, s)) (g' (ξ, t)) (Icc 0 T) t

theorem Suave.reg0 {T : ℝ} : ∀ {k : ℕ} {g : E3 × ℝ → C3}, Suave T k g → Reg0 T g
  | 0, _, h => h
  | _ + 1, _, h => h.1

theorem Suave.mono {T : ℝ} : ∀ {k : ℕ} {g : E3 × ℝ → C3}, Suave T (k + 1) g → Suave T k g
  | 0, _, h => h.1
  | _ + 1, _, h => by
    obtain ⟨h0, g', hg', hd⟩ := h
    exact ⟨h0, g', hg'.mono, hd⟩

theorem Reg0.add {T : ℝ} {f g : E3 × ℝ → C3} (hf : Reg0 T f) (hg : Reg0 T g) :
    Reg0 T (f + g) := by
  refine ⟨fun t ht => (hf.1 t ht).add (hg.1 t ht), fun m => ?_⟩
  obtain ⟨A, hA⟩ := hf.2 m
  obtain ⟨B, hB⟩ := hg.2 m
  refine ⟨A + B, fun t ht ζ => ?_⟩
  have h1 := hA t ht ζ
  have h2 := hB t ht ζ
  have h3 := norm_add_le (f (ζ, t)) (g (ζ, t))
  simp only [Pi.add_apply]
  nlinarith [show (0 : ℝ) ≤ (1 + ‖ζ‖) ^ m by positivity]

theorem Suave.add {T : ℝ} : ∀ {k : ℕ} {f g : E3 × ℝ → C3}, Suave T k f → Suave T k g →
    Suave T k (f + g)
  | 0, _, _, hf, hg => Reg0.add hf hg
  | _ + 1, _, _, hf, hg => by
    obtain ⟨hf0, f', hf', hdf⟩ := hf
    obtain ⟨hg0, g', hg', hdg⟩ := hg
    exact ⟨Reg0.add hf0 hg0, f' + g', hf'.add hg',
      fun ξ t ht => (hdf ξ t ht).add (hdg ξ t ht)⟩

/-- Multiplicação por `φ(ξ)` real, contínua e de crescimento polinomial. -/
theorem Reg0.smul_left {T : ℝ} {φ : E3 → ℝ} (hφ : Continuous φ) {K : ℝ} {p : ℕ}
    (hK : ∀ ξ, |φ ξ| ≤ K * (1 + ‖ξ‖) ^ p) {g : E3 × ℝ → C3} (hg : Reg0 T g) :
    Reg0 T (fun q => φ q.1 • g q) := by
  refine ⟨fun t ht => hφ.smul (hg.1 t ht), fun m => ?_⟩
  obtain ⟨C, hC⟩ := hg.2 (m + p)
  refine ⟨K * C, fun t ht ζ => ?_⟩
  have h1 := hC t ht ζ
  have h2 := hK ζ
  simp only
  rw [norm_smul, Real.norm_eq_abs]
  have hw : 0 ≤ (1 + ‖ζ‖) ^ m := by positivity
  calc |φ ζ| * ‖g (ζ, t)‖ * (1 + ‖ζ‖) ^ m
      ≤ (K * (1 + ‖ζ‖) ^ p) * ‖g (ζ, t)‖ * (1 + ‖ζ‖) ^ m := by gcongr
    _ = K * (‖g (ζ, t)‖ * (1 + ‖ζ‖) ^ (m + p)) := by ring
    _ ≤ K * C := by
        have hK0 : 0 ≤ K := by
          have := hK 0
          have h0 : (0 : ℝ) < (1 + ‖(0 : E3)‖) ^ p := by positivity
          nlinarith [abs_nonneg (φ 0)]
        gcongr

theorem Suave.smul_left {T : ℝ} {φ : E3 → ℝ} (hφ : Continuous φ) {K : ℝ} {p : ℕ}
    (hK : ∀ ξ, |φ ξ| ≤ K * (1 + ‖ξ‖) ^ p) :
    ∀ {k : ℕ} {g : E3 × ℝ → C3}, Suave T k g → Suave T k (fun q => φ q.1 • g q)
  | 0, _, hg => Reg0.smul_left hφ hK hg
  | _ + 1, _, hg => by
    obtain ⟨hg0, g', hg', hd⟩ := hg
    exact ⟨Reg0.smul_left hφ hK hg0, fun q => φ q.1 • g' q, Suave.smul_left hφ hK hg',
      fun ξ t ht => (hd ξ t ht).const_smul (φ ξ)⟩

/-! ### A forma bilinear projetada -/

/-- `B(f, g)(ξ, t) = 𝐏(ξ)(−2πi N(f(·,t), g(·,t))(ξ))`. -/
noncomputable def Bil (f g : E3 × ℝ → C3) (q : E3 × ℝ) : C3 :=
  leray q.1 (cI • nl (fun η => f (η, q.2)) (fun η => g (η, q.2)) q.1)

theorem Gv_eq_Bil (v : E3 × ℝ → C3) : Gv v = Bil v v := rfl

theorem continuous_nl {f g : E3 → C3} (hf : Continuous f) (hg : Continuous g) {A B : ℝ}
    (hA : Cota 4 A f) (hB : Cota 4 B g) : Continuous (nl f g) := by
  rw [continuous_iff_continuousAt]
  intro ξ₀
  unfold nl
  refine continuousAt_of_dominated
    (bound := fun η => (‖ξ₀‖ + 1) * (A * (B * ((1 + ‖η‖) ^ 4)⁻¹))) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun ξ => ((continuous_ip_comp hf ξ).smul hg).aestronglyMeasurable
  · have hev : ∀ᶠ ξ in 𝓝 ξ₀, ‖ξ‖ < ‖ξ₀‖ + 1 :=
      (continuous_norm.continuousAt).eventually (gt_mem_nhds (lt_add_one _))
    filter_upwards [hev] with ξ hp
    refine Eventually.of_forall fun η => ?_
    rw [norm_smul]
    have e1 := norm_ip_le ξ (f (ξ - η))
    have e2 := hA.le (ξ - η)
    have e3 := hB.le_inv η
    have hA0 : 0 ≤ A := hA.nonneg
    calc ‖ip ξ (f (ξ - η))‖ * ‖g η‖ ≤ (‖ξ‖ * ‖f (ξ - η)‖) * ‖g η‖ := by gcongr
      _ ≤ ((‖ξ₀‖ + 1) * A) * (B * ((1 + ‖η‖) ^ 4)⁻¹) :=
          mul_le_mul (mul_le_mul hp.le e2 (norm_nonneg _) (by positivity)) e3
            (norm_nonneg _) (by positivity)
      _ = (‖ξ₀‖ + 1) * (A * (B * ((1 + ‖η‖) ^ 4)⁻¹)) := by ring
  · exact (((integrable_inv_pow le_rfl).const_mul B).const_mul A).const_mul _
  · refine Eventually.of_forall fun η => ?_
    have h1 : Continuous fun ξ : E3 => ((ξ, f (ξ - η)) : E3 × C3) :=
      continuous_id.prodMk (hf.comp (by fun_prop))
    exact ((continuous_ip.comp h1).smul continuous_const).continuousAt

/-- `ξ ↦ 𝐏(ξ) N(ξ)` é contínua se `N` é contínua e `‖N(ξ)‖ ≤ |ξ| Q`. -/
theorem continuous_leray_of {N : E3 → C3} (hN : Continuous N) {Q : ℝ}
    (hQ : ∀ ξ, ‖N ξ‖ ≤ ‖ξ‖ * Q) : Continuous fun ξ => leray ξ (N ξ) := by
  rw [continuous_iff_continuousAt]
  intro ξ₀
  by_cases h0 : ξ₀ = 0
  · subst h0
    have hN0 : N 0 = 0 := by
      have := hQ 0
      simpa using this
    rw [ContinuousAt, hN0, map_zero, tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun ξ => norm_nonneg _) (fun ξ => (norm_leray_le ξ (N ξ)).trans (hQ ξ)) ?_
    have : Tendsto (fun ξ : E3 => ‖ξ‖) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_norm (E := E3)).tendsto 0
    simpa using this.mul_const Q
  · have hL := continuousAt_leray h0 (N ξ₀)
    have hg : ContinuousAt (fun ξ : E3 => ((ξ, N ξ) : E3 × C3)) ξ₀ :=
      continuousAt_id.prodMk hN.continuousAt
    have he : (fun ξ => leray ξ (N ξ)) =
        (fun q : E3 × C3 => leray q.1 q.2) ∘ (fun ξ : E3 => ((ξ, N ξ) : E3 × C3)) := by
      funext ξ
      rfl
    rw [he]
    exact ContinuousAt.comp (g := fun q : E3 × C3 => leray q.1 q.2) hL hg

theorem norm_cI_nl_le {f g : E3 → C3} (hf : Continuous f) (hg : Continuous g) {A B : ℝ}
    (hA : Cota 4 A f) (hB : Cota 4 B g) (ξ : E3) :
    ‖cI • nl f g ξ‖ ≤ ‖ξ‖ * (2 * π * (32 * Kp 4 * A * B)) := by
  rw [norm_smul, norm_cI]
  have h1 := norm_nl_le4 hf hg hA hB ξ
  have h2 : 1 ≤ (1 + ‖ξ‖) ^ 4 := one_le_pow₀ (by linarith [norm_nonneg ξ])
  have h3 : ‖nl f g ξ‖ ≤ ‖ξ‖ * (32 * Kp 4 * A * B) := by
    nlinarith [norm_nonneg (nl f g ξ)]
  calc 2 * π * ‖nl f g ξ‖ ≤ 2 * π * (‖ξ‖ * (32 * Kp 4 * A * B)) := by gcongr
    _ = ‖ξ‖ * (2 * π * (32 * Kp 4 * A * B)) := by ring

theorem Reg0.bil {T : ℝ} {f g : E3 × ℝ → C3} (hf : Reg0 T f) (hg : Reg0 T g) :
    Reg0 T (Bil f g) := by
  obtain ⟨A, hA⟩ := hf.2 4
  obtain ⟨B, hB⟩ := hg.2 4
  refine ⟨fun t ht => ?_, fun m => ?_⟩
  · have hN := (continuous_nl (hf.1 t ht) (hg.1 t ht) (hA t ht) (hB t ht)).const_smul cI
    exact continuous_leray_of hN (norm_cI_nl_le (hf.1 t ht) (hg.1 t ht) (hA t ht) (hB t ht))
  · obtain ⟨Am, hAm⟩ := hf.2 (m + 1)
    obtain ⟨Bm, hBm⟩ := hg.2 (m + 1)
    refine ⟨2 * π * (2 ^ (m + 1) * Kp 4 * (Am * B + A * Bm)), fun t ht ξ => ?_⟩
    have h1 := norm_nl_le (hf.1 t ht) (hg.1 t ht) (m + 1) (hA t ht) (hAm t ht) (hB t ht)
      (hBm t ht) ξ
    have hw : 0 < 1 + ‖ξ‖ := by positivity
    have hQ0 : 0 ≤ 2 ^ (m + 1) * Kp 4 * (Am * B + A * Bm) := by
      have := (hAm t ht).nonneg
      have := (hBm t ht).nonneg
      have := (hA t ht).nonneg
      have := (hB t ht).nonneg
      have := Kp_nonneg 4
      positivity
    have h2 : ‖nl (fun η => f (η, t)) (fun η => g (η, t)) ξ‖ * (1 + ‖ξ‖) ^ m ≤
        2 ^ (m + 1) * Kp 4 * (Am * B + A * Bm) := by
      rw [pow_succ] at h1
      have h3 : ‖ξ‖ * (2 ^ (m + 1) * Kp 4 * (Am * B + A * Bm)) ≤
          (1 + ‖ξ‖) * (2 ^ (m + 1) * Kp 4 * (Am * B + A * Bm)) := by
        gcongr
        linarith
      have h4 : ‖nl (fun η => f (η, t)) (fun η => g (η, t)) ξ‖ * (1 + ‖ξ‖) ^ m * (1 + ‖ξ‖) ≤
          (2 ^ (m + 1) * Kp 4 * (Am * B + A * Bm)) * (1 + ‖ξ‖) := by
        rw [← mul_assoc] at h1
        linarith
      exact le_of_mul_le_mul_right h4 hw
    simp only [Bil]
    calc ‖leray ξ (cI • nl (fun η => f (η, t)) (fun η => g (η, t)) ξ)‖ * (1 + ‖ξ‖) ^ m
        ≤ 2 * π * ‖nl (fun η => f (η, t)) (fun η => g (η, t)) ξ‖ * (1 + ‖ξ‖) ^ m := by
          gcongr
          have := norm_leray_smul_le ξ cI (nl (fun η => f (η, t)) (fun η => g (η, t)) ξ)
          rwa [norm_cI] at this
      _ = 2 * π * (‖nl (fun η => f (η, t)) (fun η => g (η, t)) ξ‖ * (1 + ‖ξ‖) ^ m) := by ring
      _ ≤ 2 * π * (2 ^ (m + 1) * Kp 4 * (Am * B + A * Bm)) := by gcongr

theorem Bil_add_left (f₁ f₂ g : E3 × ℝ → C3) {T : ℝ} (h₁ : Reg0 T f₁) (h₂ : Reg0 T f₂)
    (hg : Reg0 T g) (q : E3 × ℝ) (hq : q.2 ∈ Icc 0 T) :
    Bil f₁ g q + Bil f₂ g q = Bil (f₁ + f₂) g q := by
  obtain ⟨A₁, hA₁⟩ := h₁.2 4
  obtain ⟨A₂, hA₂⟩ := h₂.2 4
  obtain ⟨B, hB⟩ := hg.2 4
  simp only [Bil]
  rw [← map_add, ← smul_add]
  congr 2
  unfold nl
  rw [← integral_add (integrable_nl (h₁.1 _ hq) (hg.1 _ hq) (hA₁ _ hq) (hB _ hq) _)
    (integrable_nl (h₂.1 _ hq) (hg.1 _ hq) (hA₂ _ hq) (hB _ hq) _)]
  congr 1
  funext η
  simp [ip_add, add_smul]

/-- **Derivada de `B(f, g)` em `t`** (regra do produto sob a integral). -/
theorem hasDerivWithinAt_Bil {T : ℝ} {f g f' g' : E3 × ℝ → C3} (hf : Reg0 T f) (hg : Reg0 T g)
    (hf' : Reg0 T f') (hg' : Reg0 T g')
    (hdf : ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => f (ξ, s)) (f' (ξ, t)) (Icc 0 T) t)
    (hdg : ∀ ξ, ∀ t ∈ Icc 0 T, HasDerivWithinAt (fun s => g (ξ, s)) (g' (ξ, t)) (Icc 0 T) t)
    (ξ : E3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => Bil f g (ξ, s)) (Bil f' g (ξ, t) + Bil f g' (ξ, t)) (Icc 0 T) t := by
  obtain ⟨A, hA⟩ := hf.2 4
  obtain ⟨B, hB⟩ := hg.2 4
  obtain ⟨A', hA'⟩ := hf'.2 4
  obtain ⟨B', hB'⟩ := hg'.2 4
  have hA0 : 0 ≤ A := (hA t ht).nonneg
  have hB0 : 0 ≤ B := (hB t ht).nonneg
  have hA'0 : 0 ≤ A' := (hA' t ht).nonneg
  have hB'0 : 0 ≤ B' := (hB' t ht).nonneg
  set F : ℝ → E3 → C3 := fun s η => ip ξ (f (ξ - η, s)) • g (η, s)
  set F' : ℝ → E3 → C3 := fun s η =>
    ip ξ (f' (ξ - η, s)) • g (η, s) + ip ξ (f (ξ - η, s)) • g' (η, s)
  have hderiv : ∀ η, ∀ s ∈ Icc 0 T, HasDerivWithinAt (fun s => F s η) (F' s η) (Icc 0 T) s := by
    intro η s hs
    have h1 : HasDerivWithinAt (fun s => ip ξ (f (ξ - η, s))) (ip ξ (f' (ξ - η, s))) (Icc 0 T) s := by
      have := ((ipL ξ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt s (hdf (ξ - η) s hs)
      simpa [Function.comp_def, ipL_apply] using this
    have h2 := h1.smul (hdg η s hs)
    convert h2 using 1
    simp only [F']
    abel
  have hb : Integrable fun η : E3 => ‖ξ‖ * ((A' * B + A * B') * ((1 + ‖η‖) ^ 4)⁻¹) :=
    ((integrable_inv_pow (m := 4) le_rfl).const_mul _).const_mul _
  have hbound : ∀ η, ∀ s ∈ Icc 0 T, ‖F' s η‖ ≤ ‖ξ‖ * ((A' * B + A * B') * ((1 + ‖η‖) ^ 4)⁻¹) := by
    intro η s hs
    simp only [F']
    have e1 := norm_ip_le ξ (f' (ξ - η, s))
    have e2 := norm_ip_le ξ (f (ξ - η, s))
    have e3 := (hA' s hs).le (ξ - η)
    have e4 := (hA s hs).le (ξ - η)
    have e5 := (hB s hs).le_inv η
    have e6 := (hB' s hs).le_inv η
    have hinv : 0 ≤ ((1 + ‖η‖) ^ 4)⁻¹ := by positivity
    calc ‖ip ξ (f' (ξ - η, s)) • g (η, s) + ip ξ (f (ξ - η, s)) • g' (η, s)‖
        ≤ ‖ip ξ (f' (ξ - η, s))‖ * ‖g (η, s)‖ + ‖ip ξ (f (ξ - η, s))‖ * ‖g' (η, s)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul]
      _ ≤ (‖ξ‖ * A') * (B * ((1 + ‖η‖) ^ 4)⁻¹) + (‖ξ‖ * A) * (B' * ((1 + ‖η‖) ^ 4)⁻¹) := by
          gcongr
          · exact e1.trans (by gcongr)
          · exact e2.trans (by gcongr)
      _ = ‖ξ‖ * ((A' * B + A * B') * ((1 + ‖η‖) ^ 4)⁻¹) := by ring
  have hmeas : ∀ s ∈ Icc 0 T, AEStronglyMeasurable (F s) := fun s hs =>
    ((continuous_ip_comp (hf.1 s hs) ξ).smul (hg.1 s hs)).aestronglyMeasurable
  have hint := integrable_nl (hf.1 t ht) (hg.1 t ht) (hA t ht) (hB t ht) ξ
  have hI := hasDerivWithinAt_integral (convex_Icc 0 T) ht hmeas hint hb hderiv hbound
  have hI1 := integrable_nl (hf'.1 t ht) (hg.1 t ht) (hA' t ht) (hB t ht) ξ
  have hI2 := integrable_nl (hf.1 t ht) (hg'.1 t ht) (hA t ht) (hB' t ht) ξ
  have hsum : ∫ η, F' t η = nl (fun η => f' (η, t)) (fun η => g (η, t)) ξ +
      nl (fun η => f (η, t)) (fun η => g' (η, t)) ξ := by
    simp only [F', nl]
    exact integral_add hI1 hI2
  rw [hsum] at hI
  have hI' : HasDerivWithinAt (fun s => cI • ∫ η, F s η)
      (cI • (nl (fun η => f' (η, t)) (fun η => g (η, t)) ξ +
        nl (fun η => f (η, t)) (fun η => g' (η, t)) ξ)) (Icc 0 T) t := hI.const_smul cI
  have hL := ((leray ξ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t hI'
  have key : (fun s => Bil f g (ξ, s)) =
      (⇑((leray ξ).restrictScalars ℝ) ∘ fun s => cI • ∫ η, F s η) := by
    funext s
    rfl
  rw [key]
  convert hL using 1
  simp [Bil, smul_add, map_add]

theorem Suave.bil {T : ℝ} : ∀ {k : ℕ} {f g : E3 × ℝ → C3}, Suave T k f → Suave T k g →
    Suave T k (Bil f g)
  | 0, _, _, hf, hg => Reg0.bil hf hg
  | _ + 1, f, g, hf, hg => by
    obtain ⟨hf0, f', hf', hdf⟩ := hf
    obtain ⟨hg0, g', hg', hdg⟩ := hg
    refine ⟨Reg0.bil hf0 hg0, Bil f' g + Bil f g', ?_, ?_⟩
    · exact (Suave.bil hf' (Suave.mono ⟨hg0, g', hg', hdg⟩)).add
        (Suave.bil (Suave.mono ⟨hf0, f', hf', hdf⟩) hg')
    · intro ξ t ht
      exact hasDerivWithinAt_Bil hf0 hg0 hf'.reg0 hg'.reg0 hdf hdg ξ ht

/-! ### A solução é suave em `t` -/

/-- `φ_c(ξ) = −c|ξ|²`. -/
noncomputable def phiC (c : ℝ) (ξ : E3) : ℝ := -(c * ‖ξ‖ ^ 2)

theorem continuous_phiC (c : ℝ) : Continuous (phiC c) := by
  unfold phiC
  fun_prop

theorem abs_phiC_le {c : ℝ} (hc : 0 ≤ c) (ξ : E3) : |phiC c ξ| ≤ c * (1 + ‖ξ‖) ^ 2 := by
  unfold phiC
  rw [abs_neg, abs_of_nonneg (by positivity)]
  have : ‖ξ‖ ^ 2 ≤ (1 + ‖ξ‖) ^ 2 := by
    have := norm_nonneg ξ
    nlinarith
  exact mul_le_mul_of_nonneg_left this hc

/-- A derivada temporal: `∂ₜv = −c|ξ|² v + B(v, v)`. -/
noncomputable def dv (c : ℝ) (v : E3 × ℝ → C3) : E3 × ℝ → C3 :=
  (fun q => phiC c q.1 • v q) + Bil v v

/-- **A equação diferencial em `t`**, ponto a ponto em `ξ`, dentro de `[0, T]`. -/
theorem sol_hasDerivWithinAt {D : Dado} {T : ℝ} {v : E3 × ℝ → C3} (hv : Sol D T v) (ξ : E3)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => v (ξ, s)) (dv D.c v (ξ, t)) (Icc 0 T) t := by
  obtain ⟨R, hR⟩ := hv.cota
  set a := D.c * ‖ξ‖ ^ 2
  set G : ℝ → C3 := fun r => Gv v (ξ, r)
  have hG : Continuous G := by
    have h1 : Continuous fun r : ℝ => ((ξ, r) : E3 × ℝ) := continuous_const.prodMk continuous_id
    exact (continuous_Bq_param hv.cont hR).comp h1
  set u : ℝ → C3 := fun s => exp (-(a * s)) • (D.v₀ ξ + ∫ r in (0 : ℝ)..s, exp (a * r) • G r)
  have hu : ∀ s, hk D.c ξ s • D.v₀ ξ + Iduh D.c (Gv v) ξ s = u s := by
    intro s
    simp only [u, Iduh, smul_add]
    congr 1
    rw [← intervalIntegral.integral_smul]
    congr 1
    funext r
    rw [smul_smul, ← exp_add]
    simp only [hk, a]
    congr 2
    ring
  have hcont : Continuous fun r : ℝ => exp (a * r) • G r := by
    have : Continuous fun r : ℝ => exp (a * r) := by fun_prop
    exact this.smul hG
  have h1 : HasDerivAt (fun s => exp (-(a * s))) (-a * exp (-(a * t))) t := by
    have h0 : HasDerivAt (fun s => -(a * s)) (-a) t := by
      have h00 : HasDerivAt (fun s => -a * s) (-a) t := by
        simpa using (hasDerivAt_id t).const_mul (-a)
      convert h00 using 1
      funext s
      ring
    have := h0.exp
    convert this using 1
    ring
  have h2 : HasDerivAt (fun s => ∫ r in (0 : ℝ)..s, exp (a * r) • G r) (exp (a * t) • G t) t :=
    intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have h3 := h1.smul (h2.const_add (D.v₀ ξ))
  have hval : (exp (-(a * t)) • (exp (a * t) • G t) +
      (-a * exp (-(a * t))) • (D.v₀ ξ + ∫ r in (0 : ℝ)..t, exp (a * r) • G r)) =
      dv D.c v (ξ, t) := by
    have hut : u t = v (ξ, t) := by rw [← hu, hv.eq_of_mem ht]
    rw [smul_smul, ← exp_add, show -(a * t) + a * t = 0 by ring, exp_zero, one_smul, mul_smul]
    change G t + (-a) • u t = _
    rw [hut]
    simp only [dv, Pi.add_apply, phiC, G, Gv_eq_Bil, a]
    rw [add_comm]
  rw [hval] at h3
  refine h3.hasDerivWithinAt.congr (fun s hs => ?_) ?_
  · show v (ξ, s) = u s
    rw [hv.eq_of_mem hs, hu]
  · show v (ξ, t) = u t
    rw [hv.eq_of_mem ht, hu]

theorem sol_reg0 {D : Dado} {T : ℝ} (hT : 0 ≤ T) {v : E3 × ℝ → C3} (hv : Sol D T v)
    (hv₀ : ∀ m : ℕ, ∃ M, Cota m M D.v₀) : Reg0 T v := by
  obtain ⟨R, hR⟩ := hv.cota
  refine ⟨fun t _ => hv.cont.comp (continuous_id.prodMk continuous_const), fun m => ?_⟩
  obtain ⟨M, hM⟩ := hv₀ m
  obtain ⟨C, hC⟩ := persist hT hv hR m hM
  exact ⟨C, fun t _ => hC t⟩

/-- **A solução de Duhamel é `C^∞` em `t` dentro de `[0, T]`**, com todas as derivadas contínuas em
`ξ` e com cotas de todos os pesos. -/
theorem sol_suave {D : Dado} {T : ℝ} (hT : 0 ≤ T) {v : E3 × ℝ → C3} (hv : Sol D T v)
    (hv₀ : ∀ m : ℕ, ∃ M, Cota m M D.v₀) : ∀ k, Suave T k v
  | 0 => sol_reg0 hT hv hv₀
  | k + 1 => by
    have ih := sol_suave hT hv hv₀ k
    refine ⟨sol_reg0 hT hv hv₀, dv D.c v, ?_, fun ξ t ht => sol_hasDerivWithinAt hv ξ ht⟩
    exact (Suave.smul_left (continuous_phiC D.c) (abs_phiC_le D.hc.le) ih).add (Suave.bil ih ih)

end ATK.NSRegular

#print axioms ATK.NSRegular.conv_bound_W
#print axioms ATK.NSRegular.norm_nl_le_W
#print axioms ATK.NSRegular.Wt
#print axioms ATK.NSRegular.Wt_nonneg
#print axioms ATK.NSRegular.Wt_le_pow
#print axioms ATK.NSRegular.Wt_le_L
#print axioms ATK.NSRegular.Wt_of_le
#print axioms ATK.NSRegular.Wt_peetre
#print axioms ATK.NSRegular.kernel_exp_bound
#print axioms ATK.NSRegular.norm_Iduh_le_exp
#print axioms ATK.NSPicard.Sol.congela
#print axioms ATK.NSPicard.Sol.eq_of_mem
#print axioms ATK.NSRegular.persist
#print axioms ATK.NSRegular.hasDerivWithinAt_integral
#print axioms ATK.NSRegular.Reg0
#print axioms ATK.NSRegular.Suave
#print axioms ATK.NSRegular.Suave.reg0
#print axioms ATK.NSRegular.Suave.mono
#print axioms ATK.NSRegular.Reg0.add
#print axioms ATK.NSRegular.Suave.add
#print axioms ATK.NSRegular.Reg0.smul_left
#print axioms ATK.NSRegular.Suave.smul_left
#print axioms ATK.NSRegular.Bil
#print axioms ATK.NSRegular.Gv_eq_Bil
#print axioms ATK.NSRegular.continuous_nl
#print axioms ATK.NSRegular.continuous_leray_of
#print axioms ATK.NSRegular.norm_cI_nl_le
#print axioms ATK.NSRegular.Reg0.bil
#print axioms ATK.NSRegular.Bil_add_left
#print axioms ATK.NSRegular.hasDerivWithinAt_Bil
#print axioms ATK.NSRegular.Suave.bil
#print axioms ATK.NSRegular.phiC
#print axioms ATK.NSRegular.continuous_phiC
#print axioms ATK.NSRegular.abs_phiC_le
#print axioms ATK.NSRegular.dv
#print axioms ATK.NSRegular.sol_hasDerivWithinAt
#print axioms ATK.NSRegular.sol_reg0
#print axioms ATK.NSRegular.sol_suave
