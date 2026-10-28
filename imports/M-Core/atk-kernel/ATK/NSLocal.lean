import ATK.NSPlancherel

/-!
# ATK — Navier–Stokes, marco NS5b: existência local de solução suave (dados do Clay)

Ponte B3. **`existe_solucaoLocal`**: para todo `ν > 0` e todo `u₀ ∈ 𝓢(ℝ³, ℝ³)` de divergência
nula existe `T > 0` e campos `U, P` com `SolucaoLocal ν u₀ T U P` — isto é,
`modeloNS.SmoothOn (ν, u₀) T`: solução `C^∞` em `ℝ³ × [0, T)` da equação de Navier–Stokes, de
divergência nula, com o dado inicial, energia e enstrofia finitas e limitadas em cada `[0, T']`.

O tempo `T` depende só de `ν` e de `sup (1+|ξ|)^4 |û₀(ξ)|`. Isto é a teoria local clássica; **não
diz nada sobre regularidade global** (o problema do Clay). A ponte B3 (critério de explosão da
enstrofia) ainda exige unicidade na classe do modelo, a solução maximal e a continuação.

Só `propext`, `Classical.choice`, `Quot.sound`. **B3 continua aberta**; **CLOSED_MATH continua
false**.
-/

set_option autoImplicit false

open MeasureTheory Real Set
open scoped ContDiff
open ATK.LigacaoNS (E3)
open ATK.NSFourierBase ATK.NSPicard ATK.NSRegular ATK.NSFisico ATK.NSCampos ATK.NSEquacao
  ATK.NSPlancherel

namespace ATK.NSLocal

/-- Cota uniforme da energia e da enstrofia do lado de Fourier em `[0, T]`. -/
theorem cota_energia {T : ℝ} {v : E3 × ℝ → C3} (hv : Reg0 T v) :
    ∃ C, ∀ t ∈ Icc 0 T, ∫ ξ, ‖v (ξ, t)‖ ^ 2 ≤ C ∧
      ∫ ξ, 4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖v (ξ, t)‖ ^ 2 ≤ C := by
  obtain ⟨A, hA⟩ := hv.2 5
  have hK := Kp_nonneg 4
  refine ⟨(1 + 4 * π ^ 2) * (A * A * Kp 4), fun t ht => ?_⟩
  have hA0 : 0 ≤ A := (hA t ht).nonneg
  have hpt : ∀ ξ : E3, (1 + ‖ξ‖) ^ 2 * ‖v (ξ, t)‖ ^ 2 ≤ A * A * ((1 + ‖ξ‖) ^ 4)⁻¹ := by
    intro ξ
    have h1 := (hA t ht) ξ
    have hw : (0 : ℝ) < 1 + ‖ξ‖ := by positivity
    have hn := norm_nonneg (v (ξ, t))
    rw [le_mul_inv_iff₀ (by positivity)]
    have h2 : ‖v (ξ, t)‖ * (1 + ‖ξ‖) ^ 5 * (‖v (ξ, t)‖ * (1 + ‖ξ‖) ^ 5) ≤ A * A :=
      mul_le_mul h1 h1 (by positivity) hA0
    have h3 : (1 + ‖ξ‖) ^ 2 * ‖v (ξ, t)‖ ^ 2 * (1 + ‖ξ‖) ^ 4 ≤
        ‖v (ξ, t)‖ * (1 + ‖ξ‖) ^ 5 * (‖v (ξ, t)‖ * (1 + ‖ξ‖) ^ 5) := by
      have h4 : (1 + ‖ξ‖) ^ 6 ≤ (1 + ‖ξ‖) ^ 10 :=
        pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) (by norm_num)
      calc (1 + ‖ξ‖) ^ 2 * ‖v (ξ, t)‖ ^ 2 * (1 + ‖ξ‖) ^ 4
          = ‖v (ξ, t)‖ ^ 2 * (1 + ‖ξ‖) ^ 6 := by ring
        _ ≤ ‖v (ξ, t)‖ ^ 2 * (1 + ‖ξ‖) ^ 10 := by gcongr
        _ = ‖v (ξ, t)‖ * (1 + ‖ξ‖) ^ 5 * (‖v (ξ, t)‖ * (1 + ‖ξ‖) ^ 5) := by ring
    linarith
  have hI := (integrable_inv_pow (m := 4) le_rfl).const_mul (A * A)
  have hm : Continuous fun ξ => v (ξ, t) := hv.1 t ht
  have hint1 : Integrable fun ξ => ‖v (ξ, t)‖ ^ 2 := by
    refine hI.mono' (hm.norm.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ‖v (ξ, t)‖ ^ 2 ≤ (1 + ‖ξ‖) ^ 2 * ‖v (ξ, t)‖ ^ 2 := by
      have : (1 : ℝ) ≤ (1 + ‖ξ‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg ξ])
      nlinarith [sq_nonneg ‖v (ξ, t)‖]
    exact h1.trans (hpt ξ)
  have hint2 : Integrable fun ξ : E3 => 4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖v (ξ, t)‖ ^ 2 := by
    have hc : Continuous fun ξ : E3 => 4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖v (ξ, t)‖ ^ 2 :=
      (continuous_const.mul (continuous_norm.pow 2)).mul (hm.norm.pow 2)
    refine (hI.const_mul (4 * π ^ 2)).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ‖ξ‖ ^ 2 ≤ (1 + ‖ξ‖) ^ 2 := by
      have := norm_nonneg ξ
      nlinarith
    calc 4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖v (ξ, t)‖ ^ 2
        ≤ 4 * π ^ 2 * ((1 + ‖ξ‖) ^ 2 * ‖v (ξ, t)‖ ^ 2) := by
          rw [mul_assoc]
          gcongr
      _ ≤ 4 * π ^ 2 * (A * A * ((1 + ‖ξ‖) ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left (hpt ξ) (by positivity)
  have hb1 : ∫ ξ, ‖v (ξ, t)‖ ^ 2 ≤ A * A * Kp 4 := by
    calc ∫ ξ, ‖v (ξ, t)‖ ^ 2 ≤ ∫ ξ : E3, A * A * ((1 + ‖ξ‖) ^ 4)⁻¹ := by
          refine integral_mono hint1 hI fun ξ => ?_
          have : (1 : ℝ) ≤ (1 + ‖ξ‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg ξ])
          have := hpt ξ
          nlinarith [sq_nonneg ‖v (ξ, t)‖]
      _ = A * A * Kp 4 := by rw [integral_const_mul]; rfl
  have hb2 : ∫ ξ, 4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖v (ξ, t)‖ ^ 2 ≤ 4 * π ^ 2 * (A * A * Kp 4) := by
    calc ∫ ξ, 4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖v (ξ, t)‖ ^ 2
        ≤ ∫ ξ : E3, 4 * π ^ 2 * (A * A * ((1 + ‖ξ‖) ^ 4)⁻¹) := by
          refine integral_mono hint2 (hI.const_mul _) fun ξ => ?_
          have h1 : ‖ξ‖ ^ 2 ≤ (1 + ‖ξ‖) ^ 2 := by
            have := norm_nonneg ξ
            nlinarith
          calc 4 * π ^ 2 * ‖ξ‖ ^ 2 * ‖v (ξ, t)‖ ^ 2
              ≤ 4 * π ^ 2 * ((1 + ‖ξ‖) ^ 2 * ‖v (ξ, t)‖ ^ 2) := by
                rw [mul_assoc]
                gcongr
            _ ≤ 4 * π ^ 2 * (A * A * ((1 + ‖ξ‖) ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left (hpt ξ) (by positivity)
      _ = 4 * π ^ 2 * (A * A * Kp 4) := by
          rw [integral_const_mul, integral_const_mul]
          rfl
  have hAA : 0 ≤ A * A * Kp 4 := by positivity
  constructor
  · nlinarith [pi_pos]
  · nlinarith [pi_pos]

/-- **Uma solução de Fourier dá uma `SolucaoLocal`.** -/
theorem solucaoLocal_de_sol {ν : ℝ} (hν : 0 < ν) {u₀ : SchwartzMap E3 E3} {T : ℝ} (hT : 0 < T)
    {v : E3 × ℝ → C3} (hv : Sol (dadoNS ν hν u₀) T v) (hdiv : ∀ p : E3 × ℝ, ip p.1 (v p) = 0)
    (herm : ∀ ξ t, v (-ξ, t) = cj (v (ξ, t))) :
    ATK.LigacaoNS.SolucaoLocal ν u₀ T (Ufis v) (Pfis v) := by
  have h := solF_of_sol hν hT hv hdiv herm
  have hsub : (univ : Set E3) ×ˢ Ico 0 T ⊆ (univ : Set E3) ×ˢ Icc 0 T :=
    prod_mono subset_rfl Ico_subset_Icc_self
  refine ⟨(contDiffOn_Ufis h).mono hsub, (contDiffOn_Pfis h).mono hsub,
    fun x => Ufis_zero hν hT.le hv x, fun x t ht => NSEq_fis h x ht,
    fun x t ht => div_Ufis h x (Ico_subset_Icc_self ht), fun T' hT' => ?_⟩
  obtain ⟨C, hC⟩ := cota_energia h.reg0
  refine ⟨C, fun t ht => ?_⟩
  have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hT'.le⟩
  obtain ⟨hE1, hE2⟩ := energia_Ufis h htT
  obtain ⟨hG1, hG2⟩ := enstrofia_Ufis h htT
  exact ⟨⟨hE1, hE2 ▸ (hC t htT).1⟩, hG1, hG2 ▸ (hC t htT).2⟩

/-- **Existência local de solução suave para os dados do Clay (caso A).** Para todo `ν > 0` e
todo `u₀` de Schwartz com divergência nula, existe `T > 0` com `modeloNS.SmoothOn (ν, u₀) T`. -/
theorem existe_solucaoLocal {ν : ℝ} (hν : 0 < ν) (u₀ : SchwartzMap E3 E3)
    (hdiv0 : ∀ x, ATK.LigacaoNS.div u₀ x = 0) :
    ∃ T > 0, ∃ U P, ATK.LigacaoNS.SolucaoLocal ν u₀ T U P := by
  set D := dadoNS ν hν u₀
  obtain ⟨v, hv, -, hdiv, herm⟩ := existe_local_sim D (ip_v0 u₀ hdiv0) (herm_v0 u₀)
  exact ⟨T₀ D.c D.M₀, T₀_pos D.hc D.M₀, Ufis v, Pfis v,
    solucaoLocal_de_sol hν (T₀_pos D.hc D.M₀) hv hdiv herm⟩

/-- Em termos do modelo genuíno: `SmoothOn` vale para algum `T > 0`. -/
theorem smoothOn_local (d : ℝ × (E3 → E3)) (hd : ATK.LigacaoNS.modeloNS.Admissible d) :
    ∃ T > 0, ATK.LigacaoNS.modeloNS.SmoothOn d T := by
  obtain ⟨ν, u⟩ := d
  obtain ⟨hν, ⟨S, hS⟩, hdiv⟩ := hd
  simp only at hν hS hdiv
  subst hS
  obtain ⟨T, hT, U, P, hsol⟩ := existe_solucaoLocal hν S hdiv
  exact ⟨T, hT, U, P, hsol⟩

end ATK.NSLocal

#print axioms ATK.NSLocal.cota_energia
#print axioms ATK.NSLocal.solucaoLocal_de_sol
#print axioms ATK.NSLocal.existe_solucaoLocal
#print axioms ATK.NSLocal.smoothOn_local
