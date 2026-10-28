import ATK.NSLocal

/-!
# ATK — Navier–Stokes, marco NS6: unicidade de Duhamel, concatenação e a solução maximal

Ponte B3, marco NS6 (lado de Fourier):

* **`sol_unique`**: duas soluções de Duhamel com o mesmo dado coincidem no intervalo comum;
* **`sol_concat`**: uma solução em `[0, T]` seguida de uma solução em `[0, τ]` com dado `v(·, T)`
  é uma solução em `[0, T + τ]` (propriedade de semigrupo da fórmula de Duhamel);
* `Ext D T`: existe solução (de divergência nula, hermitiana) em `[0, T]`; o conjunto dos `T` com
  `Ext` é um intervalo; **`explosao_peso4`**: se ele é limitado, a cota de peso 4 da solução não é
  uniforme (alternativa de explosão).

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta**; **CLOSED_MATH continua
false**.
-/

set_option autoImplicit false

open MeasureTheory Real Set Filter Topology
open scoped ContDiff
open ATK.LigacaoNS (E3)
open ATK.NSFourierBase ATK.NSPicard ATK.NSRegular ATK.NSFisico ATK.NSCampos ATK.NSEquacao
  ATK.NSPlancherel ATK.NSLocal

namespace ATK.NSMaximal

/-! ### Unicidade -/

/-- **Unicidade das soluções de Duhamel** no intervalo comum `[0, τ]`. -/
theorem sol_unique {D : Dado} {T₁ T₂ : ℝ} {v₁ v₂ : E3 × ℝ → C3} (h₁ : Sol D T₁ v₁)
    (h₂ : Sol D T₂ v₂) {τ : ℝ} (hτ : 0 ≤ τ) (hτ₁ : τ ≤ T₁) (hτ₂ : τ ≤ T₂) :
    ∀ ξ, ∀ t ∈ Icc 0 τ, v₁ (ξ, t) = v₂ (ξ, t) := by
  obtain ⟨R₁, hR₁⟩ := h₁.cota
  obtain ⟨R₂, hR₂⟩ := h₂.cota
  have hR₁0 : 0 ≤ R₁ := (hR₁ 0).nonneg
  have hR₂0 : 0 ≤ R₂ := (hR₂ 0).nonneg
  have hK := Kp_nonneg 4
  have hc := D.hc
  set q : ℝ := 2 * π * (32 * Kp 4 * (R₁ + R₂)) with hq_def
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
  set w : E3 × ℝ → C3 := fun p => v₁ p - v₂ p
  set S : Set ℝ := {z | ∃ ξ, ∃ t ∈ Icc 0 τ, z = exp (-(lam * t)) * (‖w (ξ, t)‖ * (1 + ‖ξ‖) ^ 4)}
  have hbdd : BddAbove S := by
    refine ⟨R₁ + R₂, ?_⟩
    rintro z ⟨ξ, t, ht, rfl⟩
    have e1 : exp (-(lam * t)) ≤ 1 := by
      rw [exp_le_one_iff]
      have := mul_nonneg hl.le ht.1
      linarith
    have e2 : ‖w (ξ, t)‖ * (1 + ‖ξ‖) ^ 4 ≤ R₁ + R₂ := (Cota.sub (hR₁ t) (hR₂ t)) ξ
    calc exp (-(lam * t)) * (‖w (ξ, t)‖ * (1 + ‖ξ‖) ^ 4) ≤ 1 * (R₁ + R₂) := by
          gcongr
      _ = R₁ + R₂ := one_mul _
  have hne : S.Nonempty := ⟨_, 0, 0, ⟨le_rfl, hτ⟩, rfl⟩
  set Z := sSup S
  have hZ : ∀ ξ, ∀ t ∈ Icc 0 τ, exp (-(lam * t)) * (‖w (ξ, t)‖ * (1 + ‖ξ‖) ^ 4) ≤ Z :=
    fun ξ t ht => le_csSup hbdd ⟨ξ, t, ht, rfl⟩
  have hZ0 : 0 ≤ Z := le_trans (by positivity) (hZ 0 0 ⟨le_rfl, hτ⟩)
  have hslice : ∀ s ∈ Icc 0 τ, Cota 4 (Z * exp (lam * s)) (fun η => w (η, s)) := by
    intro s hs ζ
    have := hZ ζ s hs
    rw [exp_neg, inv_mul_le_iff₀ (exp_pos _)] at this
    linarith
  have hstep : ∀ ξ, ∀ t ∈ Icc 0 τ,
      exp (-(lam * t)) * (‖w (ξ, t)‖ * (1 + ‖ξ‖) ^ 4) ≤ Z / 2 := by
    intro ξ t ht
    have ht₁ : t ∈ Icc 0 T₁ := ⟨ht.1, ht.2.trans hτ₁⟩
    have ht₂ : t ∈ Icc 0 T₂ := ⟨ht.1, ht.2.trans hτ₂⟩
    have hw : w (ξ, t) = Iduh D.c (Gv v₁ - Gv v₂) ξ t := by
      simp only [w]
      have g₁ : Continuous (Gv v₁) := continuous_Bq_param h₁.cont hR₁
      have g₂ : Continuous (Gv v₂) := continuous_Bq_param h₂.cont hR₂
      rw [h₁.eq_of_mem ht₁, h₂.eq_of_mem ht₂, add_sub_add_left_eq_sub, Iduh_sub D.c g₁ g₂]
    have hG : ∀ s ∈ Icc 0 t, ‖(Gv v₁ - Gv v₂) (ξ, s)‖ * (1 + ‖ξ‖) ^ 4 ≤
        ‖ξ‖ * (q * Z) * exp (lam * s) := by
      intro s hs
      have hsτ : s ∈ Icc 0 τ := ⟨hs.1, hs.2.trans ht.2⟩
      have hv₁ : Continuous fun η => v₁ (η, s) := h₁.cont.comp (by fun_prop)
      have hv₂ : Continuous fun η => v₂ (η, s) := h₂.cont.comp (by fun_prop)
      have hb := norm_Bq_sub_le hv₁ hv₂ (hR₁ s) (hR₂ s) (hslice s hsτ) ξ
      calc ‖(Gv v₁ - Gv v₂) (ξ, s)‖ * (1 + ‖ξ‖) ^ 4
          ≤ ‖ξ‖ * (2 * π * (32 * Kp 4 * (Z * exp (lam * s) * R₁ + R₂ * (Z * exp (lam * s))))) :=
            hb
        _ = ‖ξ‖ * (q * Z) * exp (lam * s) := by
            rw [hq_def]
            ring
    have hI := norm_Iduh_le_exp (W := fun ζ => (1 + ‖ζ‖) ^ 4) hc hl ξ ht.1 (by positivity) hG
      (mul_nonneg hq0 hZ0)
    rw [hw]
    have he : exp (-(lam * t)) * exp (lam * t) = 1 := by rw [← exp_add]; simp
    calc exp (-(lam * t)) * (‖Iduh D.c (Gv v₁ - Gv v₂) ξ t‖ * (1 + ‖ξ‖) ^ 4)
        ≤ exp (-(lam * t)) * (q * Z * (exp (lam * t) / (2 * sqrt (D.c * lam)))) := by
          gcongr
      _ = Z * (q / (2 * sqrt (D.c * lam))) := by
          rw [mul_div_assoc', mul_div_assoc', ← mul_assoc, mul_comm _ (q * Z), mul_assoc, he]
          ring
      _ ≤ Z * (1 / 2) := by gcongr
      _ = Z / 2 := by ring
  have hZle : Z ≤ Z / 2 := csSup_le hne (by rintro z ⟨ξ, t, ht, rfl⟩; exact hstep ξ t ht)
  have hZz : Z = 0 := by linarith
  intro ξ t ht
  have h1 := hZ ξ t ht
  rw [hZz] at h1
  have h2 : 0 < exp (-(lam * t)) * (1 + ‖ξ‖) ^ 4 := by positivity
  have h3 : ‖w (ξ, t)‖ ≤ 0 := by nlinarith [norm_nonneg (w (ξ, t))]
  have h4 : w (ξ, t) = 0 := norm_le_zero_iff.mp h3
  exact sub_eq_zero.mp h4


/-! ### Concatenação -/

/-- O dado deslocado: `v(·, T)` como novo dado inicial. -/
noncomputable def shift (D : Dado) {v : E3 × ℝ → C3} (hv : Continuous v) (T M : ℝ)
    (hM : Cota 4 M fun ξ => v (ξ, T)) : Dado where
  c := D.c
  hc := D.hc
  v₀ := fun ξ => v (ξ, T)
  cont := hv.comp (by fun_prop)
  M₀ := M
  cota := hM

/-- A concatenação `v` em `[0, T]`, `w(· − T)` depois. -/
noncomputable def cat (T : ℝ) (v w : E3 × ℝ → C3) (p : E3 × ℝ) : C3 :=
  if p.2 ≤ T then v p else w (p.1, p.2 - T)

theorem cat_of_le {T : ℝ} {v w : E3 × ℝ → C3} {ξ : E3} {s : ℝ} (h : s ≤ T) :
    cat T v w (ξ, s) = v (ξ, s) := by
  simp [cat, h]

theorem cat_of_ge {T : ℝ} {v w : E3 × ℝ → C3} (hvw : ∀ ξ, w (ξ, 0) = v (ξ, T)) {ξ : E3}
    {s : ℝ} (h : T ≤ s) : cat T v w (ξ, s) = w (ξ, s - T) := by
  rcases h.lt_or_eq with h | h
  · simp [cat, not_le.mpr h]
  · subst h
    simp [cat, hvw]

theorem hk_zero (c : ℝ) (ξ : E3) : hk c ξ 0 = 1 := by simp [hk]

theorem hk_mul (c : ℝ) (ξ : E3) (a b : ℝ) : hk c ξ a * hk c ξ b = hk c ξ (a + b) := by
  unfold hk
  rw [← exp_add]
  ring_nf

theorem clamp_of_neg {T t : ℝ} (hT : 0 ≤ T) (ht : t < 0) : clamp T t = 0 := by
  unfold clamp
  rw [min_eq_left (by linarith)]
  exact max_eq_left ht.le

theorem clamp_of_gt {T t : ℝ} (hT : 0 ≤ T) (ht : T < t) : clamp T t = T := by
  unfold clamp
  rw [min_eq_right ht.le]
  exact max_eq_right hT

/-- **Concatenação**: solução em `[0, T]` seguida de solução com dado `v(·, T)` em `[0, τ]`. -/
theorem sol_concat {D : Dado} {T τ : ℝ} (hT : 0 ≤ T) (hτ : 0 ≤ τ) {v w : E3 × ℝ → C3}
    (hv : Sol D T v) {M : ℝ} (hM : Cota 4 M fun ξ => v (ξ, T))
    (hw : Sol (shift D hv.cont T M hM) τ w) : Sol D (T + τ) (cat T v w) := by
  have hvw : ∀ ξ, w (ξ, 0) = v (ξ, T) := fun ξ => sol_zero hτ hw ξ
  obtain ⟨Rv, hRv⟩ := hv.cota
  obtain ⟨Rw, hRw⟩ := hw.cota
  set u := cat T v w with hu
  have hcont : Continuous u := by
    have h1 : Continuous fun p : E3 × ℝ => w (p.1, p.2 - T) := hw.cont.comp (by fun_prop)
    refine Continuous.if_le hv.cont h1 continuous_snd continuous_const ?_
    intro p hp
    obtain ⟨ξ, s⟩ := p
    simp only at hp
    subst hp
    simp [hvw]
  have hcota : ∀ s, Cota 4 (max Rv Rw) (fun η => u (η, s)) := by
    intro s
    by_cases hs : s ≤ T
    · intro ζ
      show ‖cat T v w (ζ, s)‖ * _ ≤ _
      rw [cat_of_le hs]
      exact (hRv s ζ).trans (le_max_left _ _)
    · intro ζ
      show ‖cat T v w (ζ, s)‖ * _ ≤ _
      rw [cat_of_ge hvw (not_le.mp hs).le]
      exact (hRw (s - T) ζ).trans (le_max_right _ _)
  have gu : Continuous (Gv u) := continuous_Bq_param hcont hcota
  have gv : Continuous (Gv v) := continuous_Bq_param hv.cont hRv
  have gw : Continuous (Gv w) := continuous_Bq_param hw.cont hRw
  have Gu_v : ∀ ξ s, s ≤ T → Gv u (ξ, s) = Gv v (ξ, s) := by
    intro ξ s hs
    simp only [Gv]
    congr 1
    funext η
    exact cat_of_le hs
  have Gu_w : ∀ ξ s, T ≤ s → Gv u (ξ, s) = Gv w (ξ, s - T) := by
    intro ξ s hs
    simp only [Gv]
    congr 1
    funext η
    exact cat_of_ge hvw hs
  -- a identidade em `[0, T + τ]`
  have hmem : ∀ ξ, ∀ t ∈ Icc 0 (T + τ), u (ξ, t) = hk D.c ξ t • D.v₀ ξ + Iduh D.c (Gv u) ξ t := by
    intro ξ t ht
    by_cases htT : t ≤ T
    · rw [hu, cat_of_le htT, hv.eq_of_mem ⟨ht.1, htT⟩]
      congr 1
      unfold Iduh
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht.1] at hs
      rw [Gu_v ξ s (hs.2.trans htT)]
    · have hTt : T ≤ t := (not_le.mp htT).le
      have hmw : t - T ∈ Icc 0 τ := ⟨by linarith, by linarith [ht.2]⟩
      rw [hu, cat_of_ge hvw hTt, hw.eq_of_mem hmw]
      have e0 : (shift D hv.cont T M hM).v₀ ξ = v (ξ, T) := rfl
      have e1 : (shift D hv.cont T M hM).c = D.c := rfl
      rw [e0, e1, hv.eq_of_mem ⟨hT, le_rfl⟩]
      -- dividir a integral de Duhamel em `T`
      have hsplit : Iduh D.c (Gv u) ξ t =
          (∫ s in (0 : ℝ)..T, hk D.c ξ (t - s) • Gv u (ξ, s)) +
            ∫ s in T..t, hk D.c ξ (t - s) • Gv u (ξ, s) := by
        unfold Iduh
        rw [intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_duh D.c gu ξ t 0 T)
          (intervalIntegrable_duh D.c gu ξ t T t)]
      have hA : (∫ s in (0 : ℝ)..T, hk D.c ξ (t - s) • Gv u (ξ, s)) =
          hk D.c ξ (t - T) • Iduh D.c (Gv v) ξ T := by
        unfold Iduh
        rw [← intervalIntegral.integral_smul]
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [uIcc_of_le hT] at hs
        rw [Gu_v ξ s hs.2, smul_smul, hk_mul]
        congr 2
        ring
      have hB : (∫ s in T..t, hk D.c ξ (t - s) • Gv u (ξ, s)) = Iduh D.c (Gv w) ξ (t - T) := by
        unfold Iduh
        have h1 : (∫ s in T..t, hk D.c ξ (t - s) • Gv u (ξ, s)) =
            ∫ s in T..t, (fun r => hk D.c ξ (t - T - r) • Gv w (ξ, r)) (s - T) := by
          refine intervalIntegral.integral_congr fun s hs => ?_
          rw [uIcc_of_le hTt] at hs
          rw [Gu_w ξ s hs.1]
          congr 2
          ring
        rw [h1, intervalIntegral.integral_comp_sub_right
          (fun r => hk D.c ξ (t - T - r) • Gv w (ξ, r)) T, sub_self]
      rw [hsplit, hA, hB, smul_add, smul_smul, hk_mul]
      have e2 : t - T + T = t := by ring
      rw [e2]
      abel
  -- `u` é congelada fora de `[0, T + τ]`
  have hcl : ∀ ξ t, u (ξ, t) = u (ξ, clamp (T + τ) t) := by
    intro ξ t
    have hTτ : 0 ≤ T + τ := by linarith
    rcases lt_or_ge t 0 with h0 | h0
    · rw [clamp_of_neg hTτ h0, hu, cat_of_le (h0.le.trans hT), cat_of_le hT,
        hv.congela hT ξ t, clamp_of_neg hT h0]
    rcases le_or_gt t (T + τ) with h1 | h1
    · rw [clamp_of_mem ⟨h0, h1⟩]
    · rw [clamp_of_gt hTτ h1, hu, cat_of_ge hvw (by linarith), cat_of_ge hvw (by linarith),
        hw.congela hτ ξ (t - T), clamp_of_gt hτ (by linarith)]
      ring_nf
  refine ⟨hcont, ⟨_, hcota⟩, ?_⟩
  rintro ⟨ξ, t⟩
  have hTτ : 0 ≤ T + τ := by linarith
  rw [hcl ξ t, ← duh_clamp D hTτ u ξ t]
  have hm : clamp (T + τ) t ∈ Icc 0 (T + τ) := ⟨clamp_nonneg _ _, clamp_le hTτ _⟩
  rw [hmem ξ _ hm, duh, clamp_clamp hTτ]


theorem cat_div {T : ℝ} {v w : E3 × ℝ → C3} (hv : ∀ p : E3 × ℝ, ip p.1 (v p) = 0)
    (hw : ∀ p : E3 × ℝ, ip p.1 (w p) = 0) : ∀ p : E3 × ℝ, ip p.1 (cat T v w p) = 0 := by
  rintro ⟨ξ, t⟩
  unfold cat
  split_ifs
  · exact hv _
  · exact hw (ξ, t - T)

theorem cat_herm {T : ℝ} {v w : E3 × ℝ → C3} (hv : ∀ ξ t, v (-ξ, t) = cj (v (ξ, t)))
    (hw : ∀ ξ t, w (-ξ, t) = cj (w (ξ, t))) : ∀ ξ t, cat T v w (-ξ, t) = cj (cat T v w (ξ, t)) := by
  intro ξ t
  unfold cat
  split_ifs
  · exact hv _ _
  · exact hw _ _

/-! ### Existência em `[0, T]` -/

/-- Existe solução (de divergência nula, hermitiana) em `[0, T]`. -/
def Ext (D : Dado) (T : ℝ) : Prop :=
  ∃ v, Sol D T v ∧ (∀ p : E3 × ℝ, ip p.1 (v p) = 0) ∧ ∀ ξ t, v (-ξ, t) = cj (v (ξ, t))

/-- Dado com simetrias. -/
def DadoSim (D : Dado) : Prop := (∀ ξ, ip ξ (D.v₀ ξ) = 0) ∧ ∀ ξ, D.v₀ (-ξ) = cj (D.v₀ ξ)

theorem ext_local {D : Dado} (hD : DadoSim D) : Ext D (T₀ D.c D.M₀) := by
  obtain ⟨v, hv, -, hd, hh⟩ := existe_local_sim D hD.1 hD.2
  exact ⟨v, hv, hd, hh⟩

/-- **Passo de extensão**: com cota `M` em `t = T`, a solução continua até `T + T₀(c, M)`. -/
theorem ext_step {D : Dado} {T : ℝ} (hT : 0 ≤ T) {v : E3 × ℝ → C3} (hv : Sol D T v)
    (hd : ∀ p : E3 × ℝ, ip p.1 (v p) = 0) (hh : ∀ ξ t, v (-ξ, t) = cj (v (ξ, t))) {M : ℝ}
    (hM : Cota 4 M fun ξ => v (ξ, T)) : Ext D (T + T₀ D.c M) := by
  set D' := shift D hv.cont T M hM
  obtain ⟨w, hw, -, hwd, hwh⟩ :=
    existe_local_sim D' (fun ξ => hd (ξ, T)) (fun ξ => hh ξ T)
  have hτ := (T₀_pos D.hc M).le
  exact ⟨cat T v w, sol_concat hT hτ hv hM hw, cat_div hd hwd, cat_herm hh hwh⟩

/-- **Restrição** a `[0, T']`. -/
theorem ext_mono {D : Dado} {T T' : ℝ} (h : Ext D T) (hT' : 0 ≤ T') (hle : T' ≤ T) :
    Ext D T' := by
  obtain ⟨v, hv, hd, hh⟩ := h
  obtain ⟨R, hR⟩ := hv.cota
  set v' : E3 × ℝ → C3 := fun p => v (p.1, clamp T' p.2)
  have hc : Continuous v' := hv.cont.comp (by have := continuous_clamp T'; fun_prop)
  have hR' : ∀ s, Cota 4 R (fun η => v' (η, s)) := fun s => hR (clamp T' s)
  refine ⟨v', ⟨hc, ⟨R, hR'⟩, ?_⟩, fun p => hd (p.1, clamp T' p.2), fun ξ t => hh _ _⟩
  rintro ⟨ξ, t⟩
  have hm : clamp T' t ∈ Icc 0 T := ⟨clamp_nonneg _ _, (clamp_le hT' t).trans hle⟩
  show v (ξ, clamp T' t) = _
  rw [hv.eq_of_mem hm, duh]
  congr 1
  unfold Iduh
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le (clamp_nonneg _ _)] at hs
  have hs' : s ∈ Icc 0 T' := ⟨hs.1, hs.2.trans (clamp_le hT' t)⟩
  show hk D.c ξ (clamp T' t - s) • Bq (fun η => v (η, s)) ξ =
    hk D.c ξ (clamp T' t - s) • Bq (fun η => v (η, clamp T' s)) ξ
  rw [clamp_of_mem hs']

/-! ### O tempo maximal e a alternativa de explosão -/

/-- O conjunto dos tempos de existência. -/
def Tempos (D : Dado) : Set ℝ := {T | 0 ≤ T ∧ Ext D T}

theorem T₀_mem {D : Dado} (hD : DadoSim D) : T₀ D.c D.M₀ ∈ Tempos D :=
  ⟨(T₀_pos D.hc _).le, ext_local hD⟩

/-- Abaixo do tempo maximal, existe solução. -/
theorem ext_of_lt {D : Dado} (hD : DadoSim D) {T : ℝ} (hT : 0 ≤ T)
    (hlt : T < sSup (Tempos D)) : Ext D T := by
  obtain ⟨T', hT', hlt'⟩ := exists_lt_of_lt_csSup ⟨_, T₀_mem hD⟩ hlt
  exact ext_mono hT'.2 hT hlt'.le

theorem Tstar_pos {D : Dado} (hb : BddAbove (Tempos D)) (hD : DadoSim D) :
    0 < sSup (Tempos D) :=
  (T₀_pos D.hc _).trans_le (le_csSup hb (T₀_mem hD))

/-- **Alternativa de explosão** (forma contrapositiva): se as soluções em `[0, T]`, `T < T*`, têm
cota de peso 4 uniforme em `t = T`, então `T*` não é o tempo maximal — absurdo. -/
theorem explosao_peso4 {D : Dado} (hb : BddAbove (Tempos D)) (hD : DadoSim D) {M : ℝ}
    (hM : ∀ T, 0 ≤ T → T < sSup (Tempos D) → ∀ v, Sol D T v →
      (∀ p : E3 × ℝ, ip p.1 (v p) = 0) → (∀ ξ t, v (-ξ, t) = cj (v (ξ, t))) →
        Cota 4 M fun ξ => v (ξ, T)) : False := by
  set Ts := sSup (Tempos D)
  have hpos := Tstar_pos hb hD
  have h0 := T₀_pos D.hc M
  set T₁ := max 0 (Ts - T₀ D.c M / 2)
  have hT₁ : 0 ≤ T₁ := le_max_left _ _
  have hT₁lt : T₁ < Ts := max_lt hpos (by linarith)
  obtain ⟨v, hv, hd, hh⟩ := ext_of_lt hD hT₁ hT₁lt
  have hE := ext_step hT₁ hv hd hh (hM T₁ hT₁ hT₁lt v hv hd hh)
  have hle : T₁ + T₀ D.c M ≤ Ts := le_csSup hb ⟨by linarith, hE⟩
  have : Ts - T₀ D.c M / 2 ≤ T₁ := le_max_right _ _
  linarith

/-! ### A solução colada -/

open scoped Classical in
/-- Colagem: em cada `t ∈ A`, o valor da solução escolhida em `[0, t]`. -/
noncomputable def glue (D : Dado) (A : Set ℝ) (h : ∀ t ∈ A, Ext D t) (p : E3 × ℝ) : C3 :=
  if hp : p.2 ∈ A then Classical.choose (h p.2 hp) p else 0

theorem glue_eq {D : Dado} {A : Set ℝ} (h : ∀ t ∈ A, Ext D t) (hA : A ⊆ Ici 0) {T : ℝ}
    {v : E3 × ℝ → C3} (hv : Sol D T v) {ξ : E3} {t : ℝ} (ht : t ∈ A) (htT : t ≤ T) :
    glue D A h (ξ, t) = v (ξ, t) := by
  have ht0 : 0 ≤ t := hA ht
  unfold glue
  simp only [ht, ↓reduceDIte]
  exact sol_unique (Classical.choose_spec (h t ht)).1 hv ht0 le_rfl htT ξ t ⟨ht0, le_rfl⟩

theorem glue_div {D : Dado} {A : Set ℝ} (h : ∀ t ∈ A, Ext D t) :
    ∀ p : E3 × ℝ, ip p.1 (glue D A h p) = 0 := by
  rintro ⟨ξ, t⟩
  unfold glue
  split_ifs with hp
  · exact (Classical.choose_spec (h t hp)).2.1 _
  · simp [ip]

theorem glue_herm {D : Dado} {A : Set ℝ} (h : ∀ t ∈ A, Ext D t) :
    ∀ ξ t, glue D A h (-ξ, t) = cj (glue D A h (ξ, t)) := by
  intro ξ t
  unfold glue
  split_ifs with hp
  · exact (Classical.choose_spec (h t hp)).2.2 _ _
  · ext j
    simp [cj]


/-- Se os tempos de existência são ilimitados, há solução em todo `[0, T]`. -/
theorem ext_of_not_bdd {D : Dado} (hb : ¬ BddAbove (Tempos D)) {T : ℝ} (hT : 0 ≤ T) :
    Ext D T := by
  rw [not_bddAbove_iff] at hb
  obtain ⟨T', hT', hlt⟩ := hb T
  exact ext_mono hT'.2 hT hlt.le

end ATK.NSMaximal

#print axioms ATK.NSMaximal.sol_unique
#print axioms ATK.NSMaximal.shift
#print axioms ATK.NSMaximal.cat
#print axioms ATK.NSMaximal.cat_of_le
#print axioms ATK.NSMaximal.cat_of_ge
#print axioms ATK.NSMaximal.hk_zero
#print axioms ATK.NSMaximal.hk_mul
#print axioms ATK.NSMaximal.clamp_of_neg
#print axioms ATK.NSMaximal.clamp_of_gt
#print axioms ATK.NSMaximal.sol_concat
#print axioms ATK.NSMaximal.cat_div
#print axioms ATK.NSMaximal.cat_herm
#print axioms ATK.NSMaximal.Ext
#print axioms ATK.NSMaximal.DadoSim
#print axioms ATK.NSMaximal.ext_local
#print axioms ATK.NSMaximal.ext_step
#print axioms ATK.NSMaximal.ext_mono
#print axioms ATK.NSMaximal.Tempos
#print axioms ATK.NSMaximal.T₀_mem
#print axioms ATK.NSMaximal.ext_of_lt
#print axioms ATK.NSMaximal.Tstar_pos
#print axioms ATK.NSMaximal.explosao_peso4
#print axioms ATK.NSMaximal.glue
#print axioms ATK.NSMaximal.glue_eq
#print axioms ATK.NSMaximal.glue_div
#print axioms ATK.NSMaximal.glue_herm
#print axioms ATK.NSMaximal.ext_of_not_bdd
