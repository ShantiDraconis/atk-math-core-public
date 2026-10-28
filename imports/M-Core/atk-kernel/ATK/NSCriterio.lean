import ATK.NSUnico

/-!
# ATK — Navier–Stokes, marco NS9: o critério de explosão da enstrofia no modelo genuíno

Ponte B3. **`criterio : EnstrophyBlowupCriterion modeloNS`**, montado a partir dos marcos
NS1–NS8:

* se os tempos de extensão da solução de Fourier são ilimitados, a colagem (`glue`) dá uma
  `SolucaoGlobal` (`solucaoGlobal_compat`), contra `¬ GlobalSmooth`;
* senão, `T* = sSup (Tempos D) > 0` e a colagem em `[0, T*)` é uma `SolucaoLocal`
  (`solucaoLocal_compat`); pela unicidade (`NSUnico.unicidade`, a segunda solução é limitada em
  cada `ℝ³ × [0, t]`) o conjunto que define `modeloNS.enstrophy` é um singleto, e a enstrofia do
  modelo é `4π² Q 1 (v(·, t))` (`enstrofia_eq_Q`);
* se ela fosse limitada em `[0, T*)`, `cota_continua` daria uma cota de peso 4 uniforme abaixo
  de `T*`, contra a maximalidade (`explosao_peso4`).

Só `propext`, `Classical.choice`, `Quot.sound`. A ponte B3 está **provada no kernel** (pendente
a revisão humana do titular); **CLOSED_MATH continua false** (O1–O8 continuam abertas).
-/

set_option autoImplicit false

open MeasureTheory Real Set Filter Topology
open scoped ContDiff SchwartzMap
open ATK.LigacaoNS (E3 dX e div lap conv grad gradSq fatia NSEq SolucaoLocal SolucaoGlobal
  EnergiaAte)
open ATK.NSFourierBase ATK.NSPicard ATK.NSRegular ATK.NSFisico ATK.NSCampos ATK.NSEquacao
  ATK.NSPlancherel ATK.NSLocal ATK.NSMaximal ATK.NSContinua
open ATK.NSEnergia (Q Q_nonneg)

namespace ATK.NSCriterio

/-! ### Congruências: `Ufis`, `Pfis` só dependem da fatia -/

theorem Ufis_congr {V W : E3 × ℝ → C3} {t : ℝ} (h : ∀ ξ, V (ξ, t) = W (ξ, t)) (x : E3) :
    Ufis V (x, t) = Ufis W (x, t) := by
  unfold Ufis
  rw [Fi_apply, Fi_apply]
  simp only [h]

theorem Pfis_congr {V W : E3 × ℝ → C3} {t : ℝ} (h : ∀ ξ, V (ξ, t) = W (ξ, t)) (x : E3) :
    Pfis V (x, t) = Pfis W (x, t) := by
  have e : (fun η => V (η, t)) = fun η => W (η, t) := funext h
  unfold Pfis NSFisico.Φ
  simp only [Nl, e]

/-- `‖Ufis v (x, s)‖ ≤ R · Kp 4` para uma solução de Fourier com cota `R`. -/
theorem norm_Ufis_le {D : Dado} {c T : ℝ} {v : E3 × ℝ → C3} (hv : Sol D T v) (h : SolF c T v)
    {R : ℝ} (hR : ∀ s, Cota 4 R fun η => v (η, s)) (x : E3) (s : ℝ) :
    ‖Ufis v (x, s)‖ ≤ R * Kp 4 := by
  rw [norm_Ufis h, Fi_apply]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hc : Continuous fun ξ => v (ξ, s) := hv.cont.comp (continuous_id.prodMk continuous_const)
  have hi := (integrable_inv_pow (le_refl 4)).const_mul R
  have hle : ∀ ξ, ‖ex ξ x • v (ξ, s)‖ ≤ R * ((1 + ‖ξ‖) ^ 4)⁻¹ := fun ξ => by
    rw [norm_smul, norm_ex, one_mul]
    exact (hR s).le_inv ξ
  have hce : Continuous fun ξ => ex ξ x := continuous_ex.comp (continuous_id.prodMk continuous_const)
  have hint : Integrable fun ξ => ‖ex ξ x • v (ξ, s)‖ :=
    hi.mono' (hce.smul hc).norm.aestronglyMeasurable
      (Eventually.of_forall fun ξ => by rw [norm_norm]; exact hle ξ)
  calc ∫ ξ, ‖ex ξ x • v (ξ, s)‖ ≤ ∫ ξ : E3, R * ((1 + ‖ξ‖) ^ 4)⁻¹ := integral_mono hint hi hle
    _ = R * Kp 4 := by rw [integral_const_mul]; rfl

/-! ### Famílias compatíveis de soluções de Fourier -/

/-- `V` coincide, em cada `[0, T]` com `T < Ts`, com uma solução de Fourier simétrica. -/
def Compat (D : Dado) (Ts : ℝ) (V : E3 × ℝ → C3) : Prop :=
  ∀ T, 0 ≤ T → T < Ts → ∃ v, Sol D T v ∧ (∀ p : E3 × ℝ, ip p.1 (v p) = 0) ∧
    (∀ ξ t, v (-ξ, t) = cj (v (ξ, t))) ∧ ∀ ξ, ∀ t ∈ Icc 0 T, V (ξ, t) = v (ξ, t)

theorem compat_glue (D : Dado) {A : Set ℝ} (h : ∀ t ∈ A, Ext D t) (hA : A ⊆ Ici 0) {Ts : ℝ}
    (hTs : ∀ T, 0 ≤ T → T < Ts → Icc 0 T ⊆ A) : Compat D Ts (glue D A h) := by
  intro T hT0 hT
  have hTA : T ∈ A := hTs T hT0 hT ⟨hT0, le_rfl⟩
  obtain ⟨v, hv, hd, hh⟩ := h T hTA
  exact ⟨v, hv, hd, hh, fun ξ t ht => glue_eq h hA hv (hTs T hT0 hT ht) ht.2⟩

theorem nhds_Icc_prod {Ts T : ℝ} (p : E3 × ℝ) (hp : p.2 < T) :
    (univ : Set E3) ×ˢ Icc 0 T ∈ 𝓝[(univ : Set E3) ×ˢ Ico 0 Ts] p :=
  mem_nhdsWithin.mpr ⟨(univ : Set E3) ×ˢ Iio T, isOpen_univ.prod isOpen_Iio, ⟨mem_univ _, hp⟩,
    fun _ hq => ⟨mem_univ _, hq.2.2.1, hq.1.2.le⟩⟩

section Montagem

variable {ν : ℝ} (hν : 0 < ν) (u₀ : 𝓢(E3, E3))
include hν

/-- **Uma família compatível dá uma `SolucaoLocal` em `[0, Ts)`**, com energia limitada por
`Q 0 v̂₀` e velocidade limitada em cada `ℝ³ × [0, t]`. -/
theorem solucaoLocal_compat {Ts : ℝ} (hTs : 0 < Ts) {V : E3 × ℝ → C3}
    (hV : Compat (dadoNS ν hν u₀) Ts V) :
    SolucaoLocal ν u₀ Ts (Ufis V) (Pfis V) ∧
      (∀ t ∈ Ico 0 Ts, EnergiaAte (Ufis V) t (Q 0 (v0S u₀))) ∧
      ∀ t ∈ Ico 0 Ts, ∃ B, ∀ x, ∀ s ∈ Icc 0 t, ‖Ufis V (x, s)‖ ≤ B := by
  set D := dadoNS ν hν u₀
  -- o esqueleto: para cada `t < Ts`, uma solução `v` em `[0, T]`, `t < T < Ts`
  have pick : ∀ t ∈ Ico 0 Ts, ∃ T, t < T ∧ T < Ts ∧ ∃ v, Sol D T v ∧
      (∀ p : E3 × ℝ, ip p.1 (v p) = 0) ∧ (∀ ξ t, v (-ξ, t) = cj (v (ξ, t))) ∧
      ∀ ξ, ∀ s ∈ Icc 0 T, V (ξ, s) = v (ξ, s) := by
    intro t ht
    obtain ⟨T, hT1, hT2⟩ := exists_between ht.2
    exact ⟨T, hT1, hT2, hV T (ht.1.trans hT1.le) hT2⟩
  have eU : ∀ {T : ℝ} {v : E3 × ℝ → C3}, (∀ ξ, ∀ s ∈ Icc 0 T, V (ξ, s) = v (ξ, s)) →
      ∀ s ∈ Icc 0 T, fatia (Ufis V) s = fatia (Ufis v) s := fun he s hs =>
    funext fun x => Ufis_congr (fun ξ => he ξ s hs) x
  have eP : ∀ {T : ℝ} {v : E3 × ℝ → C3}, (∀ ξ, ∀ s ∈ Icc 0 T, V (ξ, s) = v (ξ, s)) →
      ∀ s ∈ Icc 0 T, fatia (Pfis V) s = fatia (Pfis v) s := fun he s hs =>
    funext fun x => Pfis_congr (fun ξ => he ξ s hs) x
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro p hp
    obtain ⟨T, hT1, hT2, v, hv, hd, hh, he⟩ := pick p.2 hp.2
    have hF := solF_of_sol hν (hp.2.1.trans_lt hT1) hv hd hh
    have h1 := (contDiffOn_Ufis hF).contDiffWithinAt ⟨mem_univ _, hp.2.1, hT1.le⟩
    refine (h1.congr (fun y hy => ?_) ?_).mono_of_mem_nhdsWithin (nhds_Icc_prod p hT1)
    · obtain ⟨x, s⟩ := y
      exact Ufis_congr (fun ξ => he ξ s hy.2) x
    · obtain ⟨x, s⟩ := p
      exact Ufis_congr (fun ξ => he ξ s ⟨hp.2.1, hT1.le⟩) x
  · intro p hp
    obtain ⟨T, hT1, hT2, v, hv, hd, hh, he⟩ := pick p.2 hp.2
    have hF := solF_of_sol hν (hp.2.1.trans_lt hT1) hv hd hh
    have h1 := (contDiffOn_Pfis hF).contDiffWithinAt ⟨mem_univ _, hp.2.1, hT1.le⟩
    refine (h1.congr (fun y hy => ?_) ?_).mono_of_mem_nhdsWithin (nhds_Icc_prod p hT1)
    · obtain ⟨x, s⟩ := y
      exact Pfis_congr (fun ξ => he ξ s hy.2) x
    · obtain ⟨x, s⟩ := p
      exact Pfis_congr (fun ξ => he ξ s ⟨hp.2.1, hT1.le⟩) x
  · intro x
    obtain ⟨T, hT1, hT2, v, hv, hd, hh, he⟩ := pick 0 ⟨le_rfl, hTs⟩
    rw [Ufis_congr (fun ξ => he ξ 0 ⟨le_rfl, hT1.le⟩) x]
    exact Ufis_zero hν hT1.le hv x
  · intro x t ht
    obtain ⟨T, hT1, hT2, v, hv, hd, hh, he⟩ := pick t ⟨ht.1.le, ht.2⟩
    have hF := solF_of_sol hν (ht.1.trans hT1) hv hd hh
    have h1 := NSEq_fis hF x ⟨ht.1, hT1⟩
    unfold NSEq at h1 ⊢
    rw [eU he t ⟨ht.1.le, hT1.le⟩, eP he t ⟨ht.1.le, hT1.le⟩]
    have hder : deriv (fun s => Ufis V (x, s)) t = deriv (fun s => Ufis v (x, s)) t := by
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [isOpen_Ioo.mem_nhds (⟨ht.1, hT1⟩ : t ∈ Ioo 0 T)] with s hs
      exact Ufis_congr (fun ξ => he ξ s ⟨hs.1.le, hs.2.le⟩) x
    rw [hder]
    exact h1
  · intro x t ht
    obtain ⟨T, hT1, hT2, v, hv, hd, hh, he⟩ := pick t ht
    have hF := solF_of_sol hν (ht.1.trans_lt hT1) hv hd hh
    rw [eU he t ⟨ht.1, hT1.le⟩]
    exact div_Ufis hF x ⟨ht.1, hT1.le⟩
  · intro T' hT'
    rcases lt_or_ge T' 0 with hneg | hpos
    · exact ⟨0, fun t ht => absurd (ht.1.trans ht.2) (not_le.mpr hneg)⟩
    obtain ⟨T, hT1, hT2, v, hv, hd, hh, he⟩ := pick T' ⟨hpos, hT'⟩
    have hS := solucaoLocal_de_sol hν (hpos.trans_lt hT1) hv hd hh
    obtain ⟨C, hC⟩ := hS.2.2.2.2.2 T' hT1
    refine ⟨C, fun t ht => ?_⟩
    have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hT1.le⟩
    have hx : ∀ x, Ufis V (x, t) = Ufis v (x, t) := fun x =>
      Ufis_congr (fun ξ => he ξ t htT) x
    obtain ⟨⟨i1, i2⟩, i3, i4⟩ := hC t ht
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · simpa only [hx] using i1
    · simpa only [hx] using i2
    · rw [eU he t htT]; exact i3
    · rw [eU he t htT]; exact i4
  · intro t ht
    obtain ⟨T, hT1, hT2, v, hv, hd, hh, he⟩ := pick t ht
    have hT : 0 < T := ht.1.trans_lt hT1
    have hF := solF_of_sol hν hT hv hd hh
    have htT : t ∈ Icc 0 T := ⟨ht.1, hT1.le⟩
    have hx : ∀ x, Ufis V (x, t) = Ufis v (x, t) := fun x =>
      Ufis_congr (fun ξ => he ξ t htT) x
    obtain ⟨i1, i2⟩ := energia_Ufis hF htT
    have hdec := energia_decresce hF htT
    have h0 : (fun ξ => v (ξ, 0)) = ⇑(v0S u₀) := funext fun ξ => sol_zero hT.le hv ξ
    rw [h0] at hdec
    refine ⟨by simpa only [hx] using i1, ?_⟩
    simp only [hx]
    rw [i2]
    refine le_trans (le_of_eq ?_) hdec
    simp [Q]
  · intro t ht
    obtain ⟨T, hT1, hT2, v, hv, hd, hh, he⟩ := pick t ht
    have hF := solF_of_sol hν (ht.1.trans_lt hT1) hv hd hh
    obtain ⟨R, hR⟩ := hv.cota
    refine ⟨R * Kp 4, fun x s hs => ?_⟩
    rw [Ufis_congr (fun ξ => he ξ s ⟨hs.1, hs.2.trans hT1.le⟩) x]
    exact norm_Ufis_le hv hF hR x s

omit hν in
theorem nhds_Ico_prod (p : E3 × ℝ) :
    (univ : Set E3) ×ˢ Ico 0 (p.2 + 1) ∈ 𝓝[(univ : Set E3) ×ˢ Ici 0] p :=
  mem_nhdsWithin.mpr ⟨(univ : Set E3) ×ˢ Iio (p.2 + 1), isOpen_univ.prod isOpen_Iio,
    ⟨mem_univ _, mem_Iio.mpr (lt_add_one _)⟩, fun _ hq => ⟨mem_univ _, hq.2.2, hq.1.2⟩⟩

/-- **Uma família compatível em todo `[0, Ts)` dá uma `SolucaoGlobal`.** -/
theorem solucaoGlobal_compat {V : E3 × ℝ → C3}
    (hV : ∀ Ts, 0 < Ts → Compat (dadoNS ν hν u₀) Ts V) :
    SolucaoGlobal ν u₀ (Ufis V) (Pfis V) := by
  have hloc := fun (Ts : ℝ) (hTs : 0 < Ts) => solucaoLocal_compat hν u₀ hTs (hV Ts hTs)
  refine ⟨?_, ?_, (hloc 1 one_pos).1.2.2.1, fun x t ht => ?_, fun x t ht => ?_,
    ⟨Q 0 (v0S u₀), fun t ht => (hloc (t + 1) (by linarith)).2.1 t ⟨ht, lt_add_one t⟩⟩⟩
  · intro p hp
    have hp2 : (0 : ℝ) ≤ p.2 := hp.2
    have h := (hloc (p.2 + 1) (by linarith)).1.1.contDiffWithinAt
      ⟨mem_univ _, hp2, lt_add_one _⟩
    exact h.mono_of_mem_nhdsWithin (nhds_Ico_prod p)
  · intro p hp
    have hp2 : (0 : ℝ) ≤ p.2 := hp.2
    have h := (hloc (p.2 + 1) (by linarith)).1.2.1.contDiffWithinAt
      ⟨mem_univ _, hp2, lt_add_one _⟩
    exact h.mono_of_mem_nhdsWithin (nhds_Ico_prod p)
  · exact (hloc (t + 1) (by linarith)).1.2.2.2.1 x t ⟨ht, lt_add_one t⟩
  · exact (hloc (t + 1) (by linarith)).1.2.2.2.2.1 x t ⟨ht, lt_add_one t⟩

end Montagem

/-- `∫ |∇ Ufis v(t)|² = 4π² Q 1 (v(·, t))`. -/
theorem enstrofia_eq_Q {c T : ℝ} {v : E3 × ℝ → C3} (h : SolF c T v) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫ x, gradSq (fatia (Ufis v) t) x = 4 * π ^ 2 * Q 1 fun ξ => v (ξ, t) := by
  rw [(enstrofia_Ufis h ht).2, Q, ← integral_const_mul]
  congr 1
  funext ξ
  ring

/-- **A ponte B3 no modelo genuíno**: o critério de explosão da enstrofia. -/
theorem criterio :
    ATK.Conditional.NavierStokes.EnstrophyBlowupCriterion ATK.LigacaoNS.modeloNS := by
  rintro ⟨ν, u⟩ ⟨hν, ⟨S, hS⟩, hdiv⟩ hng
  simp only at hν hS hdiv
  subst hS
  set D := dadoNS ν hν S with hD_def
  have hD : DadoSim D := ⟨ip_v0 S hdiv, herm_v0 S⟩
  have hw : ∀ m, ∃ M, Cota m M D.v₀ := fun m => cota_v0 S m
  by_cases hb : BddAbove (Tempos D)
  swap
  · exfalso
    apply hng
    have h : ∀ t ∈ Ici (0 : ℝ), Ext D t := fun t ht => ext_of_not_bdd hb ht
    have hV : ∀ Ts, 0 < Ts → Compat D Ts (glue D (Ici 0) h) := fun Ts _ =>
      compat_glue D h subset_rfl fun T hT0 _ => Icc_subset_Ici_self
    exact ⟨_, _, solucaoGlobal_compat hν S hV⟩
  set Ts := sSup (Tempos D) with hTs_def
  have hTs : 0 < Ts := Tstar_pos hb hD
  have h : ∀ t ∈ Ico 0 Ts, Ext D t := fun t ht => ext_of_lt hD ht.1 ht.2
  set V := glue D (Ico 0 Ts) h with hV_def
  have hV : Compat D Ts V :=
    compat_glue D h Ico_subset_Ici_self fun T _ hT s hs => ⟨hs.1, hs.2.trans_lt hT⟩
  obtain ⟨hS, -, hB⟩ := solucaoLocal_compat hν S hTs hV
  refine ⟨Ts, hTs, ⟨_, _, hS⟩, ?_⟩
  -- identificação da enstrofia do modelo pela unicidade
  have hens : ∀ t ∈ Ico 0 Ts, ATK.LigacaoNS.modeloNS.enstrophy (ν, ⇑S) t =
      ∫ x, gradSq (fatia (Ufis V) t) x := by
    intro t ht
    show sSup {E | ∃ T U P, t < T ∧ SolucaoLocal ν (⇑S) T U P ∧
      E = ∫ x, gradSq (fatia U t) x} = _
    have e : {E | ∃ T U P, t < T ∧ SolucaoLocal ν (⇑S) T U P ∧ E = ∫ x, gradSq (fatia U t) x} =
        {∫ x, gradSq (fatia (Ufis V) t) x} := by
      ext E
      simp only [Set.mem_ofPred_eq, mem_singleton_iff]
      constructor
      · rintro ⟨T, U, P, hT, hU, rfl⟩
        obtain ⟨B, hB'⟩ := hB t ht
        have hu := ATK.NSUnico.unicidade hU hS hν ht.1 hT ht.2 hB'
        have ef : fatia U t = fatia (Ufis V) t := funext fun x => hu x t ⟨ht.1, le_rfl⟩
        rw [ef]
      · rintro rfl
        exact ⟨Ts, _, _, ht.2, hS, rfl⟩
    rw [e, csSup_singleton]
  by_contra hcon
  push Not at hcon
  obtain ⟨B, hBe⟩ := hcon
  set E := B / (4 * π ^ 2) with hE_def
  -- a enstrofia de Fourier de toda solução abaixo de `Ts` é `≤ E`
  have hQ : ∀ T, 0 ≤ T → T < Ts → ∀ v, Sol D T v → (∀ p : E3 × ℝ, ip p.1 (v p) = 0) →
      (∀ ξ t, v (-ξ, t) = cj (v (ξ, t))) → ∀ t ∈ Icc 0 T, Q 1 (fun ξ => v (ξ, t)) ≤ E := by
    intro T hT0 hT v hv hd hh t ht
    obtain ⟨v', hv', -, -, he⟩ := hV T hT0 hT
    have hu := sol_unique hv hv' ht.1 ht.2 ht.2
    have htT : t ∈ Ico 0 Ts := ⟨ht.1, ht.2.trans_lt hT⟩
    have hx : fatia (Ufis V) t = fatia (Ufis v) t := funext fun x =>
      Ufis_congr (fun ξ => (he ξ t ht).trans (hu ξ t ⟨ht.1, le_rfl⟩).symm) x
    rcases eq_or_lt_of_le hT0 with hT0' | hTpos
    · subst hT0'
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      subst ht0
      have := hBe 0 htT
      rw [hens 0 htT, hx] at this
      obtain ⟨v₁, hv₁, hd₁, hh₁, he₁⟩ := hV (Ts / 2) (by positivity) (by linarith)
      have hF₁ := solF_of_sol hν (by positivity) hv₁ hd₁ hh₁
      have hx₁ : fatia (Ufis v) 0 = fatia (Ufis v₁) 0 := funext fun x =>
        Ufis_congr (fun ξ => (hu ξ 0 ⟨le_rfl, le_rfl⟩).trans
          ((he ξ 0 ⟨le_rfl, le_rfl⟩).symm.trans (he₁ ξ 0 ⟨le_rfl, by positivity⟩))) x
      rw [hx₁, enstrofia_eq_Q hF₁ ⟨le_rfl, by positivity⟩] at this
      have hv0 : (fun ξ => v (ξ, 0)) = fun ξ => v₁ (ξ, 0) := funext fun ξ =>
        (hu ξ 0 ⟨le_rfl, le_rfl⟩).trans ((he ξ 0 ⟨le_rfl, le_rfl⟩).symm.trans
          (he₁ ξ 0 ⟨le_rfl, by positivity⟩))
      rw [hv0, hE_def, le_div_iff₀ (by positivity)]
      linarith
    · have hF := solF_of_sol hν hTpos hv hd hh
      have := hBe t htT
      rw [hens t htT, hx, enstrofia_eq_Q hF ht] at this
      rw [hE_def, le_div_iff₀ (by positivity)]
      linarith
  -- cota de peso 4 uniforme abaixo de `Ts` ⇒ contradição com a maximalidade
  refine explosao_peso4 hb hD (M := max D.M₀ (Bnd D.c D.M₀ (Q 0 D.v₀) E Ts)) ?_
  intro T hT0 hT v hv hd hh
  rcases eq_or_lt_of_le hT0 with hT0' | hTpos
  · subst hT0'
    have h0 : (fun ξ => v (ξ, 0)) = D.v₀ := funext fun ξ => sol_zero le_rfl hv ξ
    rw [h0]
    exact D.cota.mono (le_max_left _ _)
  · have := cota_continua hTpos hv hw hd hh (hQ T hT0 hT v hv hd hh) hT.le T ⟨hT0, le_rfl⟩
    exact this.mono (le_max_right _ _)

end ATK.NSCriterio

#print axioms ATK.NSCriterio.Ufis_congr
#print axioms ATK.NSCriterio.Pfis_congr
#print axioms ATK.NSCriterio.norm_Ufis_le
#print axioms ATK.NSCriterio.Compat
#print axioms ATK.NSCriterio.compat_glue
#print axioms ATK.NSCriterio.nhds_Icc_prod
#print axioms ATK.NSCriterio.solucaoLocal_compat
#print axioms ATK.NSCriterio.nhds_Ico_prod
#print axioms ATK.NSCriterio.solucaoGlobal_compat
#print axioms ATK.NSCriterio.enstrofia_eq_Q
#print axioms ATK.NSCriterio.criterio
