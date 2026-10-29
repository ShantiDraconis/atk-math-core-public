import ATK.NSPicard

/-!
# ATK — Navier–Stokes: existência da solução branda no lado de Fourier (ponto fixo de Picard)

Dado `a₀ : ℝ³ → ℂ³` contínuo, de divergência nula (`⟪ξ, a₀(ξ)⟫ = 0`), com
`‖a₀(ξ)‖ ≤ M_m (1 + ‖ξ‖)^{−m}` para todo `m`, e `ν > 0`, existe `T > 0` (dependendo só de `ν` e
da cota `m = 4`) e uma amplitude contínua `a(t, ξ)` que resolve a **forma branda**

  `a(t, ξ) = e^{−4π²ν‖ξ‖²t} a₀(ξ) − ∫₀^t e^{−4π²ν‖ξ‖²(t−s)} P(ξ) Nl(a(s), a(s))(ξ) ds`

em `[0, T]`, com divergência nula e com **todas** as cotas `‖a(t, ξ)‖ ≤ C_m (1 + ‖ξ‖)^{−m}`
(`existe_branda`). A prova é o ponto fixo de Picard, com contração na norma `m = 4` e a estimativa
mansa (`conv_peso`) mais uma supersolução exponencial para as normas `m` (o tempo de existência
não depende de `m`).
-/

open MeasureTheory Set Filter Topology intervalIntegral
open scoped Real

namespace ATK.NSMild

open ATK.LigacaoNS ATK.NSFourierBase ATK.NSPicard

/-! ### Truncamento do tempo -/

/-- `cl T t = max 0 (min t T) ∈ [0, T]`. -/
noncomputable def cl (T t : ℝ) : ℝ := max 0 (min t T)

theorem cl_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : cl T t ∈ Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

theorem cl_of_mem {T t : ℝ} (h : t ∈ Icc 0 T) : cl T t = t := by
  unfold cl; rw [min_eq_left h.2, max_eq_right h.1]

theorem continuous_cl (T : ℝ) : Continuous (cl T) := by
  unfold cl; fun_prop

/-! ### O mapa de Picard -/

/-- `Φ(a)(t, ξ) = e^{−4π²ν‖ξ‖²τ} a₀(ξ) − ∫₀^τ duhI`, com `τ = cl T t`. -/
noncomputable def Phi (ν T : ℝ) (a₀ : E3 → C3) (a : ℝ → E3 → C3) (t : ℝ) (ξ : E3) : C3 :=
  heat ν (cl T t) ξ • a₀ ξ - ∫ s in (0 : ℝ)..(cl T t), duhI ν a a (cl T t) s ξ

/-- As iteradas de Picard. -/
noncomputable def it (ν T : ℝ) (a₀ : E3 → C3) : ℕ → ℝ → E3 → C3
  | 0 => fun t ξ => heat ν (cl T t) ξ • a₀ ξ
  | n + 1 => Phi ν T a₀ (it ν T a₀ n)

theorem continuous_lin (ν T : ℝ) {a₀ : E3 → C3} (h₀ : Continuous a₀) :
    Continuous fun p : ℝ × E3 => heat ν (cl T p.1) p.2 • a₀ p.2 := by
  have : Continuous fun p : ℝ × E3 => heat ν (cl T p.1) p.2 :=
    Continuous.comp (g := fun p : ℝ × E3 => heat ν p.1 p.2)
      (f := fun p : ℝ × E3 => (cl T p.1, p.2)) (continuous_heat ν)
      (((continuous_cl T).comp continuous_fst).prodMk continuous_snd)
  exact this.smul (h₀.comp continuous_snd)

theorem continuous_duhInt {ν T : ℝ} {a : ℝ → E3 → C3} {A : ℝ} (ha : Boa4 a A) :
    Continuous fun p : ℝ × E3 => ∫ s in (0 : ℝ)..(cl T p.1), duhI ν a a (cl T p.1) s p.2 := by
  have hc := continuous_duhI ha ha ν
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun (p : ℝ × E3) (s : ℝ) => duhI ν a a (cl T p.1) s p.2) ?_
    ((continuous_cl T).comp continuous_fst)
  exact Continuous.comp (g := fun q : (ℝ × ℝ) × E3 => duhI ν a a q.1.1 q.1.2 q.2)
    (f := fun x : (ℝ × E3) × ℝ => ((cl T x.1.1, x.2), x.1.2)) hc (by
      have := continuous_cl T
      fun_prop)

theorem continuous_Phi {ν T : ℝ} {a₀ : E3 → C3} (h₀ : Continuous a₀) {a : ℝ → E3 → C3} {A : ℝ}
    (ha : Boa4 a A) : Continuous fun p : ℝ × E3 => Phi ν T a₀ a p.1 p.2 :=
  (continuous_lin ν T h₀).sub (continuous_duhInt ha)

/-! ### Constantes -/

/-- `L = 512 (I₄ + 1)(M + 1)`. -/
noncomputable def Lc (M : ℝ) : ℝ := 512 * (I4 + 1) * (M + 1)

/-- O tempo de existência `T₀ = ν / L²`. -/
noncomputable def T0 (ν M : ℝ) : ℝ := ν / Lc M ^ 2

theorem Lc_pos {M : ℝ} (hM : 0 ≤ M) : 0 < Lc M := by
  unfold Lc; have := I4_nonneg; positivity

theorem T0_pos {ν M : ℝ} (hν : 0 < ν) (hM : 0 ≤ M) : 0 < T0 ν M := by
  unfold T0; have := Lc_pos hM; positivity

/-- `ν^{−1/2} · 2 τ^{1/2} ≤ 2 / L` para `τ ≤ T₀`. -/
theorem raiz_le {ν M τ : ℝ} (hν : 0 < ν) (hM : 0 ≤ M) (hτ : 0 ≤ τ) (hτT : τ ≤ T0 ν M) :
    ν ^ (-(1 / 2 : ℝ)) * (2 * τ ^ (1 / 2 : ℝ)) ≤ 2 / Lc M := by
  have hL := Lc_pos hM
  have h1 : τ ^ (1 / 2 : ℝ) ≤ (T0 ν M) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hτ hτT (by norm_num)
  have h2 : (T0 ν M) ^ (1 / 2 : ℝ) = ν ^ (1 / 2 : ℝ) / Lc M := by
    unfold T0
    rw [Real.div_rpow hν.le (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    norm_num
  have h3 : ν ^ (-(1 / 2 : ℝ)) * ν ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hν]; norm_num
  have hνp : 0 < ν ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hν _
  calc ν ^ (-(1 / 2 : ℝ)) * (2 * τ ^ (1 / 2 : ℝ))
      ≤ ν ^ (-(1 / 2 : ℝ)) * (2 * (ν ^ (1 / 2 : ℝ) / Lc M)) := by
        rw [← h2]; gcongr
    _ = 2 / Lc M * (ν ^ (-(1 / 2 : ℝ)) * ν ^ (1 / 2 : ℝ)) := by ring
    _ = 2 / Lc M := by rw [h3, mul_one]

/-! ### Cotas das iteradas -/

/-- O dado: contínuo, com `‖a₀(ξ)‖ ≤ M w₄(ξ)⁻¹`. -/
structure Dado (a₀ : E3 → C3) (M : ℝ) : Prop where
  cont : Continuous a₀
  bound : ∀ ξ, ‖a₀ ξ‖ ≤ M * (w 4 ξ)⁻¹

theorem Dado.nonneg {a₀ : E3 → C3} {M : ℝ} (h : Dado a₀ M) : 0 ≤ M := by
  have := (norm_nonneg _).trans (h.bound 0)
  exact nonneg_of_mul_nonneg_left this (inv_pos.mpr (w_pos 4 0))

theorem norm_lin_le {ν T : ℝ} (hν : 0 ≤ ν) (hT : 0 ≤ T) {a₀ : E3 → C3} (t : ℝ) (ξ : E3) :
    ‖heat ν (cl T t) ξ • a₀ ξ‖ ≤ ‖a₀ ξ‖ := by
  rw [norm_smul, Real.norm_of_nonneg (heat_pos _ _ _).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (heat_le_one hν (cl_mem hT t).1 ξ)

/-- **Cota da parte de Duhamel na norma `m = 4`**: `‖∫duhI‖ ≤ (M/2) w₄⁻¹` se `‖a‖ ≤ 2M w₄⁻¹`. -/
theorem norm_duhInt_le {ν M T : ℝ} (hν : 0 < ν) (hM : 0 ≤ M) (hT : 0 ≤ T) (hTT : T ≤ T0 ν M)
    {a : ℝ → E3 → C3} (ha : Boa4 a (2 * M)) (t : ℝ) (ξ : E3) :
    ‖∫ s in (0 : ℝ)..(cl T t), duhI ν a a (cl T t) s ξ‖ ≤ M / 2 * (w 4 ξ)⁻¹ := by
  set τ := cl T t
  have hτ := cl_mem hT t
  have h := norm_duh_le hν 4 ha ha (A' := fun _ => 2 * M) (B' := fun _ => 2 * M)
    continuous_const continuous_const hτ.1 (fun s _ η => ha.bound s η) (fun s _ η => ha.bound s η) ξ
  have hint : ∫ s in (0 : ℝ)..τ, (τ - s) ^ (-(1 / 2 : ℝ)) * (2 * M * (2 * M) + 2 * M * (2 * M)) =
      (8 * M ^ 2) * (2 * τ ^ (1 / 2 : ℝ)) := by
    rw [intervalIntegral.integral_mul_const, integral_sing hτ.1]; ring
  rw [hint] at h
  have hr := raiz_le hν hM hτ.1 (hτ.2.trans hTT)
  have hL := Lc_pos hM
  have hw := w_pos 4 ξ
  have hI := I4_nonneg
  have key : ν ^ (-(1 / 2 : ℝ)) * (2 ^ 4 * I4) * ((8 * M ^ 2) * (2 * τ ^ (1 / 2 : ℝ))) ≤ M / 2 := by
    have e : ν ^ (-(1 / 2 : ℝ)) * (2 ^ 4 * I4) * ((8 * M ^ 2) * (2 * τ ^ (1 / 2 : ℝ))) =
        (128 * I4 * M ^ 2) * (ν ^ (-(1 / 2 : ℝ)) * (2 * τ ^ (1 / 2 : ℝ))) := by ring
    rw [e]
    calc (128 * I4 * M ^ 2) * (ν ^ (-(1 / 2 : ℝ)) * (2 * τ ^ (1 / 2 : ℝ)))
        ≤ (128 * I4 * M ^ 2) * (2 / Lc M) := mul_le_mul_of_nonneg_left hr (by positivity)
      _ ≤ M / 2 := by
          unfold Lc
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_nonneg hI hM, mul_nonneg (mul_nonneg hI hM) hM, sq_nonneg M]
  have h2 := h.trans key
  rw [← le_div_iff₀' hw, div_eq_mul_inv] at h2
  exact h2

/-- As iteradas são boas, com cota `2M`. -/
theorem it_boa {ν M T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTT : T ≤ T0 ν M) {a₀ : E3 → C3}
    (h₀ : Dado a₀ M) (n : ℕ) : Boa4 (it ν T a₀ n) (2 * M) := by
  have hM := h₀.nonneg
  induction n with
  | zero =>
    refine ⟨continuous_lin ν T h₀.cont, fun t ξ => ?_⟩
    refine (norm_lin_le hν.le hT t ξ).trans ((h₀.bound ξ).trans ?_)
    have := inv_pos.mpr (w_pos 4 ξ)
    nlinarith
  | succ n ih =>
    refine ⟨continuous_Phi h₀.cont ih, fun t ξ => ?_⟩
    show ‖Phi ν T a₀ (it ν T a₀ n) t ξ‖ ≤ _
    unfold Phi
    refine (norm_sub_le _ _).trans ?_
    have h1 := (norm_lin_le hν.le hT t ξ).trans (h₀.bound ξ)
    have h2 := norm_duhInt_le hν hM hT hTT ih t ξ
    have := inv_pos.mpr (w_pos 4 ξ)
    nlinarith

/-- **Contração** na norma `m = 4`. -/
theorem norm_Phi_sub_le {ν M T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTT : T ≤ T0 ν M)
    {a₀ : E3 → C3} (h₀ : Dado a₀ M) {a b : ℝ → E3 → C3} (ha : Boa4 a (2 * M))
    (hb : Boa4 b (2 * M)) {D : ℝ} (hD : ∀ s ξ, ‖a s ξ - b s ξ‖ ≤ D * (w 4 ξ)⁻¹) (t : ℝ) (ξ : E3) :
    ‖Phi ν T a₀ a t ξ - Phi ν T a₀ b t ξ‖ ≤ D / 2 * (w 4 ξ)⁻¹ := by
  have hM := h₀.nonneg
  have hDb : Boa4 (a - b) D := ha.sub hb hD
  have hD0 := hDb.nonneg
  set τ := cl T t
  have hτ := cl_mem hT t
  unfold Phi
  have hia : IntervalIntegrable (fun s => duhI ν a a τ s ξ) volume 0 τ :=
    (Continuous.comp (g := fun q : (ℝ × ℝ) × E3 => duhI ν a a q.1.1 q.1.2 q.2)
      (f := fun s : ℝ => ((τ, s), ξ)) (continuous_duhI ha ha ν) (by fun_prop)).intervalIntegrable _ _
  have hib : IntervalIntegrable (fun s => duhI ν b b τ s ξ) volume 0 τ :=
    (Continuous.comp (g := fun q : (ℝ × ℝ) × E3 => duhI ν b b q.1.1 q.1.2 q.2)
      (f := fun s : ℝ => ((τ, s), ξ)) (continuous_duhI hb hb ν) (by fun_prop)).intervalIntegrable _ _
  have hi1 : IntervalIntegrable (fun s => duhI ν (a - b) a τ s ξ) volume 0 τ :=
    (Continuous.comp (g := fun q : (ℝ × ℝ) × E3 => duhI ν (a - b) a q.1.1 q.1.2 q.2)
      (f := fun s : ℝ => ((τ, s), ξ)) (continuous_duhI hDb ha ν) (by fun_prop)).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun s => duhI ν b (a - b) τ s ξ) volume 0 τ :=
    (Continuous.comp (g := fun q : (ℝ × ℝ) × E3 => duhI ν b (a - b) q.1.1 q.1.2 q.2)
      (f := fun s : ℝ => ((τ, s), ξ)) (continuous_duhI hb hDb ν) (by fun_prop)).intervalIntegrable _ _
  have e : (heat ν τ ξ • a₀ ξ - ∫ s in (0 : ℝ)..τ, duhI ν a a τ s ξ) -
      (heat ν τ ξ • a₀ ξ - ∫ s in (0 : ℝ)..τ, duhI ν b b τ s ξ) =
      -((∫ s in (0 : ℝ)..τ, duhI ν (a - b) a τ s ξ) + ∫ s in (0 : ℝ)..τ, duhI ν b (a - b) τ s ξ) := by
    rw [sub_sub_sub_cancel_left, ← neg_sub, ← intervalIntegral.integral_sub hia hib,
      ← intervalIntegral.integral_add hi1 hi2]
    congr 1
    exact intervalIntegral.integral_congr fun s _ => duhI_sub ha hb hDb τ s ξ
  rw [e, norm_neg]
  refine (norm_add_le _ _).trans ?_
  have h1 := norm_duh_le hν 4 hDb ha (A' := fun _ => D) (B' := fun _ => 2 * M)
    continuous_const continuous_const hτ.1 (fun s _ η => hDb.bound s η) (fun s _ η => ha.bound s η) ξ
  have h2 := norm_duh_le hν 4 hb hDb (A' := fun _ => 2 * M) (B' := fun _ => D)
    continuous_const continuous_const hτ.1 (fun s _ η => hb.bound s η) (fun s _ η => hDb.bound s η) ξ
  have hint1 : ∫ s in (0 : ℝ)..τ, (τ - s) ^ (-(1 / 2 : ℝ)) * (D * (2 * M) + D * (2 * M)) =
      (4 * M * D) * (2 * τ ^ (1 / 2 : ℝ)) := by
    rw [intervalIntegral.integral_mul_const, integral_sing hτ.1]; ring
  have hint2 : ∫ s in (0 : ℝ)..τ, (τ - s) ^ (-(1 / 2 : ℝ)) * (2 * M * D + 2 * M * D) =
      (4 * M * D) * (2 * τ ^ (1 / 2 : ℝ)) := by
    rw [intervalIntegral.integral_mul_const, integral_sing hτ.1]; ring
  rw [hint1] at h1
  rw [hint2] at h2
  have hr := raiz_le hν hM hτ.1 (hτ.2.trans hTT)
  have hL := Lc_pos hM
  have hw := w_pos 4 ξ
  have hI := I4_nonneg
  have key : ν ^ (-(1 / 2 : ℝ)) * (2 ^ 4 * I4) * ((4 * M * D) * (2 * τ ^ (1 / 2 : ℝ))) ≤ D / 4 := by
    have e : ν ^ (-(1 / 2 : ℝ)) * (2 ^ 4 * I4) * ((4 * M * D) * (2 * τ ^ (1 / 2 : ℝ))) =
        (64 * I4 * M * D) * (ν ^ (-(1 / 2 : ℝ)) * (2 * τ ^ (1 / 2 : ℝ))) := by ring
    rw [e]
    calc (64 * I4 * M * D) * (ν ^ (-(1 / 2 : ℝ)) * (2 * τ ^ (1 / 2 : ℝ)))
        ≤ (64 * I4 * M * D) * (2 / Lc M) := mul_le_mul_of_nonneg_left hr (by positivity)
      _ ≤ D / 4 := by
          unfold Lc
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_nonneg hI hM, mul_nonneg (mul_nonneg hI hM) hD0, mul_nonneg hM hD0,
            mul_nonneg hI hD0]
  have k1 := h1.trans key
  have k2 := h2.trans key
  rw [← le_div_iff₀' hw, div_eq_mul_inv] at k1 k2
  linarith

/-! ### Convergência das iteradas -/

theorem norm_it_succ_sub_le {ν M T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTT : T ≤ T0 ν M)
    {a₀ : E3 → C3} (h₀ : Dado a₀ M) (n : ℕ) (t : ℝ) (ξ : E3) :
    ‖it ν T a₀ (n + 1) t ξ - it ν T a₀ n t ξ‖ ≤ M / 2 / 2 ^ n * (w 4 ξ)⁻¹ := by
  have hM := h₀.nonneg
  induction n generalizing t ξ with
  | zero =>
    show ‖Phi ν T a₀ (it ν T a₀ 0) t ξ - heat ν (cl T t) ξ • a₀ ξ‖ ≤ _
    unfold Phi
    rw [sub_sub_cancel_left, norm_neg]
    have := norm_duhInt_le hν hM hT hTT (it_boa hν hT hTT h₀ 0) t ξ
    simpa using this
  | succ n ih =>
    show ‖Phi ν T a₀ (it ν T a₀ (n + 1)) t ξ - Phi ν T a₀ (it ν T a₀ n) t ξ‖ ≤ _
    refine (norm_Phi_sub_le hν hT hTT h₀ (it_boa hν hT hTT h₀ (n + 1)) (it_boa hν hT hTT h₀ n)
      (fun s η => ih s η) t ξ).trans_eq ?_
    rw [pow_succ]; ring

/-- O limite das iteradas. -/
noncomputable def lim (ν T : ℝ) (a₀ : E3 → C3) (t : ℝ) (ξ : E3) : C3 :=
  limUnder atTop fun n => it ν T a₀ n t ξ

theorem dist_it_le {ν M T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTT : T ≤ T0 ν M)
    {a₀ : E3 → C3} (h₀ : Dado a₀ M) (t : ℝ) (ξ : E3) (n : ℕ) :
    dist (it ν T a₀ n t ξ) (it ν T a₀ (n + 1) t ξ) ≤ M * (w 4 ξ)⁻¹ / 2 / 2 ^ n := by
  rw [dist_eq_norm, norm_sub_rev]
  refine (norm_it_succ_sub_le hν hT hTT h₀ n t ξ).trans_eq ?_
  ring

theorem tendsto_it {ν M T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTT : T ≤ T0 ν M)
    {a₀ : E3 → C3} (h₀ : Dado a₀ M) (t : ℝ) (ξ : E3) :
    Tendsto (fun n => it ν T a₀ n t ξ) atTop (𝓝 (lim ν T a₀ t ξ)) :=
  (cauchySeq_of_le_geometric_two (dist_it_le hν hT hTT h₀ t ξ)).tendsto_limUnder

theorem norm_it_sub_lim_le {ν M T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTT : T ≤ T0 ν M)
    {a₀ : E3 → C3} (h₀ : Dado a₀ M) (n : ℕ) (t : ℝ) (ξ : E3) :
    ‖it ν T a₀ n t ξ - lim ν T a₀ t ξ‖ ≤ M / 2 ^ n * (w 4 ξ)⁻¹ := by
  rw [← dist_eq_norm]
  refine (dist_le_of_le_geometric_two_of_tendsto (dist_it_le hν hT hTT h₀ t ξ)
    (tendsto_it hν hT hTT h₀ t ξ) n).trans_eq ?_
  ring

/-- O limite é bom, com cota `2M`. -/
theorem lim_boa {ν M T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTT : T ≤ T0 ν M)
    {a₀ : E3 → C3} (h₀ : Dado a₀ M) : Boa4 (lim ν T a₀) (2 * M) := by
  have hM := h₀.nonneg
  refine ⟨?_, fun t ξ => ?_⟩
  · have hu : TendstoUniformly (fun n (p : ℝ × E3) => it ν T a₀ n p.1 p.2)
        (fun p => lim ν T a₀ p.1 p.2) atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (M + 1) by positivity)
        (show (1 / 2 : ℝ) < 1 by norm_num)
      filter_upwards [eventually_ge_atTop N] with n hn
      intro p
      rw [dist_comm, dist_eq_norm]
      have h1 := norm_it_sub_lim_le hν hT hTT h₀ n p.1 p.2
      have hw : (w 4 p.2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_w 4 p.2)
      have h2 : M / 2 ^ n ≤ M * (1 / 2) ^ N := by
        rw [div_eq_mul_inv, ← inv_pow, ← one_div]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn) hM
      have h3 : M * (1 / 2) ^ N < ε := by
        calc M * (1 / 2) ^ N ≤ (M + 1) * (1 / 2) ^ N := by
              gcongr; linarith
          _ < (M + 1) * (ε / (M + 1)) := by gcongr
          _ = ε := by field_simp
      calc ‖it ν T a₀ n p.1 p.2 - lim ν T a₀ p.1 p.2‖ ≤ M / 2 ^ n * (w 4 p.2)⁻¹ := h1
        _ ≤ M / 2 ^ n := mul_le_of_le_one_right (by positivity) hw
        _ < ε := lt_of_le_of_lt h2 h3
    exact hu.continuous (Eventually.of_forall fun n => (it_boa hν hT hTT h₀ n).cont).frequently
  · exact le_of_tendsto (tendsto_it hν hT hTT h₀ t ξ).norm
      (Eventually.of_forall fun n => (it_boa hν hT hTT h₀ n).bound t ξ)

/-- **O limite é ponto fixo de `Φ`** (a forma branda). -/
theorem lim_fixo {ν M T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTT : T ≤ T0 ν M)
    {a₀ : E3 → C3} (h₀ : Dado a₀ M) (t : ℝ) (ξ : E3) :
    Phi ν T a₀ (lim ν T a₀) t ξ = lim ν T a₀ t ξ := by
  have hM := h₀.nonneg
  have hl := lim_boa hν hT hTT h₀
  have h1 : Tendsto (fun n => it ν T a₀ (n + 1) t ξ) atTop (𝓝 (Phi ν T a₀ (lim ν T a₀) t ξ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim0 : Tendsto (fun n : ℕ => M / 2 * (w 4 ξ)⁻¹ * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (M / 2 * (w 4 ξ)⁻¹)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim0
    show ‖Phi ν T a₀ (it ν T a₀ n) t ξ - Phi ν T a₀ (lim ν T a₀) t ξ‖ ≤
      M / 2 * (w 4 ξ)⁻¹ * (1 / 2) ^ n
    refine (norm_Phi_sub_le hν hT hTT h₀ (it_boa hν hT hTT h₀ n) hl
      (D := M / 2 ^ n) (fun s η => norm_it_sub_lim_le hν hT hTT h₀ n s η) t ξ).trans_eq ?_
    rw [one_div, inv_pow]; ring
  have h2 : Tendsto (fun n => it ν T a₀ (n + 1) t ξ) atTop (𝓝 (lim ν T a₀ t ξ)) :=
    (tendsto_it hν hT hTT h₀ t ξ).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique h1 h2

/-! ### Cotas em todas as normas `m` (o tempo não depende de `m`) -/

/-- `κ_m = (32 · 2^m I₄ M ν^{−1/2} + 1)²`. -/
noncomputable def kap (ν M : ℝ) (m : ℕ) : ℝ := (32 * 2 ^ m * I4 * M * ν ^ (-(1 / 2 : ℝ)) + 1) ^ 2

theorem it_bound_m {ν M T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTT : T ≤ T0 ν M) {a₀ : E3 → C3}
    (h₀ : Dado a₀ M) {m : ℕ} {Mm : ℝ} (hm : ∀ ξ, ‖a₀ ξ‖ ≤ Mm * (w m ξ)⁻¹) (n : ℕ) (t : ℝ)
    (ξ : E3) : ‖it ν T a₀ n t ξ‖ ≤ 2 * Mm * Real.exp (kap ν M m * cl T t) * (w m ξ)⁻¹ := by
  have hM := h₀.nonneg
  have hMm : 0 ≤ Mm := by
    have := (norm_nonneg _).trans (hm 0)
    exact nonneg_of_mul_nonneg_left this (inv_pos.mpr (w_pos m 0))
  set κ := kap ν M m with hκ
  set c := 32 * 2 ^ m * I4 * M * ν ^ (-(1 / 2 : ℝ)) + 1 with hc
  have hνp : 0 < ν ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hν _
  have hI := I4_nonneg
  have hc1 : 1 ≤ c := by
    rw [hc]; have : 0 ≤ 32 * 2 ^ m * I4 * M * ν ^ (-(1 / 2 : ℝ)) := by positivity
    linarith
  have hκpos : 0 < κ := by rw [hκ, kap]; positivity
  have hκc : κ ^ (-(1 / 2 : ℝ)) = c⁻¹ := by
    rw [hκ, kap, ← hc, Real.rpow_neg (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by linarith)]
    norm_num
  induction n generalizing t ξ with
  | zero =>
    show ‖heat ν (cl T t) ξ • a₀ ξ‖ ≤ _
    refine (norm_lin_le hν.le hT t ξ).trans ((hm ξ).trans ?_)
    have he : 1 ≤ Real.exp (κ * cl T t) :=
      Real.one_le_exp (mul_nonneg hκpos.le (cl_mem hT t).1)
    have hw := inv_pos.mpr (w_pos m ξ)
    nlinarith [mul_nonneg hMm hw.le]
  | succ n ih =>
    show ‖Phi ν T a₀ (it ν T a₀ n) t ξ‖ ≤ _
    set τ := cl T t
    have hτ := cl_mem hT t
    have hb := it_boa hν hT hTT h₀ n
    have hY : Continuous fun s : ℝ => 2 * Mm * Real.exp (κ * s) := by fun_prop
    have hA' : ∀ s ∈ Icc 0 τ, ∀ η, ‖it ν T a₀ n s η‖ ≤
        (fun s => 2 * Mm * Real.exp (κ * s)) s * (w m η)⁻¹ := by
      intro s hs η
      have := ih s η
      rwa [cl_of_mem ⟨hs.1, hs.2.trans hτ.2⟩] at this
    have hD := norm_duh_le hν m hb hb hY hY hτ.1 hA' hA' ξ
    have hint : ∫ s in (0 : ℝ)..τ, (τ - s) ^ (-(1 / 2 : ℝ)) *
        (2 * Mm * Real.exp (κ * s) * (2 * M) + 2 * M * (2 * Mm * Real.exp (κ * s))) =
        (8 * M * Mm) * ∫ s in (0 : ℝ)..τ, (τ - s) ^ (-(1 / 2 : ℝ)) * Real.exp (κ * s) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext s; ring
    rw [hint] at hD
    have hS := integral_sing_exp hτ.1 hκpos
    have hw := w_pos m ξ
    have he : 1 ≤ Real.exp (κ * τ) := Real.one_le_exp (mul_nonneg hκpos.le hτ.1)
    have key : ν ^ (-(1 / 2 : ℝ)) * (2 ^ m * I4) * ((8 * M * Mm) *
        ∫ s in (0 : ℝ)..τ, (τ - s) ^ (-(1 / 2 : ℝ)) * Real.exp (κ * s)) ≤
        Mm * Real.exp (κ * τ) := by
      have hpos : 0 ≤ ν ^ (-(1 / 2 : ℝ)) * (2 ^ m * I4) * (8 * M * Mm) := by positivity
      calc ν ^ (-(1 / 2 : ℝ)) * (2 ^ m * I4) * ((8 * M * Mm) *
            ∫ s in (0 : ℝ)..τ, (τ - s) ^ (-(1 / 2 : ℝ)) * Real.exp (κ * s))
          = (ν ^ (-(1 / 2 : ℝ)) * (2 ^ m * I4) * (8 * M * Mm)) *
            ∫ s in (0 : ℝ)..τ, (τ - s) ^ (-(1 / 2 : ℝ)) * Real.exp (κ * s) := by ring
        _ ≤ (ν ^ (-(1 / 2 : ℝ)) * (2 ^ m * I4) * (8 * M * Mm)) *
            (4 * κ ^ (-(1 / 2 : ℝ)) * Real.exp (κ * τ)) := mul_le_mul_of_nonneg_left hS hpos
        _ = ((c - 1) / c) * (Mm * Real.exp (κ * τ)) := by
            rw [hκc, hc]; field_simp; ring
        _ ≤ 1 * (Mm * Real.exp (κ * τ)) := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            rw [div_le_one (by linarith)]; linarith
        _ = Mm * Real.exp (κ * τ) := one_mul _
    have hD2 := hD.trans key
    rw [← le_div_iff₀' hw, div_eq_mul_inv] at hD2
    unfold Phi
    refine (norm_sub_le _ _).trans ?_
    have h1 := (norm_lin_le hν.le hT t ξ).trans (hm ξ)
    have hwi := inv_pos.mpr hw
    nlinarith [mul_nonneg hMm hwi.le, mul_le_mul_of_nonneg_right he (mul_nonneg hMm hwi.le)]

theorem lim_bound_m {ν M T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTT : T ≤ T0 ν M) {a₀ : E3 → C3}
    (h₀ : Dado a₀ M) {m : ℕ} {Mm : ℝ} (hm : ∀ ξ, ‖a₀ ξ‖ ≤ Mm * (w m ξ)⁻¹) (t : ℝ) (ξ : E3) :
    ‖lim ν T a₀ t ξ‖ ≤ 2 * Mm * Real.exp (kap ν M m * cl T t) * (w m ξ)⁻¹ :=
  le_of_tendsto (tendsto_it hν hT hTT h₀ t ξ).norm
    (Eventually.of_forall fun n => it_bound_m hν hT hTT h₀ hm n t ξ)

/-! ### Divergência nula -/

theorem inner_duhI (ν : ℝ) (a b : ℝ → E3 → C3) (τ s : ℝ) (ξ : E3) :
    inner ℂ (cpx ξ) (duhI ν a b τ s ξ) = 0 := by
  unfold duhI
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, inner_lp, mul_zero]

theorem inner_Phi {ν T : ℝ} {a₀ : E3 → C3} (hdiv : ∀ ξ, inner ℂ (cpx ξ) (a₀ ξ) = 0)
    {a : ℝ → E3 → C3} {A : ℝ} (ha : Boa4 a A) (t : ℝ) (ξ : E3) :
    inner ℂ (cpx ξ) (Phi ν T a₀ a t ξ) = 0 := by
  unfold Phi
  have hint : IntervalIntegrable (fun s => duhI ν a a (cl T t) s ξ) volume 0 (cl T t) :=
    (Continuous.comp (g := fun q : (ℝ × ℝ) × E3 => duhI ν a a q.1.1 q.1.2 q.2)
      (f := fun s : ℝ => ((cl T t, s), ξ)) (continuous_duhI ha ha ν) (by fun_prop)).intervalIntegrable _ _
  have hcomm := (innerSL ℂ (cpx ξ)).intervalIntegral_comp_comm hint
  simp only [innerSL_apply_apply] at hcomm
  rw [inner_sub_right, RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, hdiv, mul_zero,
    ← hcomm]
  simp [inner_duhI]

/-! ### Resumo: a solução branda -/

/-- **Existência da solução branda no lado de Fourier.** -/
theorem existe_branda {ν M : ℝ} (hν : 0 < ν) {a₀ : E3 → C3} (h₀ : Dado a₀ M)
    (hdiv : ∀ ξ, inner ℂ (cpx ξ) (a₀ ξ) = 0) :
    ∃ T > 0, ∃ a : ℝ → E3 → C3, Boa4 a (2 * M) ∧
      (∀ t ∈ Icc 0 T, ∀ ξ, a t ξ = heat ν t ξ • a₀ ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ) ∧
      (∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0) ∧
      (∀ t, a t = a (cl T t)) ∧
      ∀ (m : ℕ) (Mm : ℝ), (∀ ξ, ‖a₀ ξ‖ ≤ Mm * (w m ξ)⁻¹) →
        ∃ C, ∀ t ξ, ‖a t ξ‖ ≤ C * (w m ξ)⁻¹ := by
  have hM := h₀.nonneg
  set T := T0 ν M
  have hT := T0_pos hν hM
  refine ⟨T, hT, lim ν T a₀, lim_boa hν hT.le le_rfl h₀, fun t ht ξ => ?_, fun t ξ => ?_,
    fun t => ?_, fun m Mm hm => ?_⟩
  · have := (lim_fixo hν hT.le le_rfl h₀ t ξ).symm
    rw [this]
    unfold Phi
    rw [cl_of_mem ht]
  · rw [← lim_fixo hν hT.le le_rfl h₀ t ξ]
    exact inner_Phi hdiv (lim_boa hν hT.le le_rfl h₀) t ξ
  · funext ξ
    rw [← lim_fixo hν hT.le le_rfl h₀ t ξ, ← lim_fixo hν hT.le le_rfl h₀ (cl T t) ξ]
    unfold Phi
    have : cl T (cl T t) = cl T t := cl_of_mem (cl_mem hT.le t)
    rw [this]
  · refine ⟨2 * Mm * Real.exp (kap ν M m * T), fun t ξ => ?_⟩
    have hMm : 0 ≤ Mm := by
      have := (norm_nonneg _).trans (hm 0)
      exact nonneg_of_mul_nonneg_left this (inv_pos.mpr (w_pos m 0))
    refine (lim_bound_m hν hT.le le_rfl h₀ hm t ξ).trans ?_
    have hk : 0 ≤ kap ν M m := by unfold kap; positivity
    have : Real.exp (kap ν M m * cl T t) ≤ Real.exp (kap ν M m * T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (cl_mem hT.le t).2 hk)
    have hw := inv_pos.mpr (w_pos m ξ)
    gcongr

end ATK.NSMild

#print axioms ATK.NSMild.cl_mem
#print axioms ATK.NSMild.cl_of_mem
#print axioms ATK.NSMild.continuous_cl
#print axioms ATK.NSMild.continuous_lin
#print axioms ATK.NSMild.continuous_duhInt
#print axioms ATK.NSMild.continuous_Phi
#print axioms ATK.NSMild.Lc_pos
#print axioms ATK.NSMild.T0_pos
#print axioms ATK.NSMild.raiz_le
#print axioms ATK.NSMild.Dado.nonneg
#print axioms ATK.NSMild.norm_lin_le
#print axioms ATK.NSMild.norm_duhInt_le
#print axioms ATK.NSMild.it_boa
#print axioms ATK.NSMild.norm_Phi_sub_le
#print axioms ATK.NSMild.norm_it_succ_sub_le
#print axioms ATK.NSMild.dist_it_le
#print axioms ATK.NSMild.tendsto_it
#print axioms ATK.NSMild.norm_it_sub_lim_le
#print axioms ATK.NSMild.lim_boa
#print axioms ATK.NSMild.lim_fixo
#print axioms ATK.NSMild.it_bound_m
#print axioms ATK.NSMild.lim_bound_m
#print axioms ATK.NSMild.inner_duhI
#print axioms ATK.NSMild.inner_Phi
#print axioms ATK.NSMild.existe_branda
