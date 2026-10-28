import Mathlib.Analysis.SpecificLimits.Basic

/-!
# ATK — A fronteira em 1: fase `t/(t + ε)` e "o ponto antes do infinito"

**Fase I** (catálogo D, G41): `φ_ε(t) = t/(t + ε)`, `ε > 0`.
* `fase_zero`, `fase_lt_one`, `fase_nonneg`: `φ_ε(0) = 0` e `0 ≤ φ_ε(t) < 1` para `t ≥ 0`;
* `fase_strictMonoOn`: estritamente crescente em `[0, ∞)`;
* `fase_image`: `φ_ε([0, ∞)) = [0, 1)` — leva a semirreta **exatamente** sobre `[0, 1)`;
* `fase_tendsto_one`: `φ_ε(t) → 1⁻` quando `t → ∞`; `fase_ne_one`: o valor 1 nunca é atingido;
* `fase_sSup`: `sup φ_ε([0, ∞)) = 1` sem máximo (`fase_sem_maximo`).

**Fronteira antes do infinito** (`FINAL_FAIL_EXTENDED_HISTORICAL_RECOVERY.md`):
`ρ(r) = r/(1 + r)` e `ε(r) = 1/(1 + r)`.
* `rho_add_eps`: `ρ + ε = 1` em `[0, ∞)`;
* `fronteira_iff_eps`: para `f ≥ 0`, `f → ∞ ⟺ ε(f) → 0`;
* `fronteira_iff_rho`: para `f ≥ 0`, `f → ∞ ⟺ ρ(f) → 1`.

Leitura: não existe "último número finito"; o que existe é a casca `ε > 0`, e cruzar para
`ρ = 1` é uma operação de limite (compactificação de `[0, ∞]` em `[0, 1]`), não um sucessor.
Matemática elementar; nova só a formalização.
-/

open Filter Topology Set

namespace ATK.FronteiraUm

/-- Fase `φ_ε(t) = t/(t + ε)`. -/
noncomputable def fase (ε t : ℝ) : ℝ := t / (t + ε)

theorem fase_zero (ε : ℝ) : fase ε 0 = 0 := by simp [fase]

theorem fase_nonneg {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) : 0 ≤ fase ε t :=
  div_nonneg ht (by linarith)

theorem fase_lt_one {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) : fase ε t < 1 := by
  unfold fase
  rw [div_lt_one (by linarith)]
  linarith

theorem fase_ne_one {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) : fase ε t ≠ 1 :=
  (fase_lt_one hε ht).ne

theorem fase_strictMonoOn {ε : ℝ} (hε : 0 < ε) : StrictMonoOn (fase ε) (Ici 0) := by
  intro s hs t ht hst
  simp only [mem_Ici] at hs ht
  unfold fase
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Todo `y ∈ [0, 1)` é atingido: `t = εy/(1 − y)`. -/
theorem fase_surj {ε y : ℝ} (hε : 0 < ε) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ∃ t, 0 ≤ t ∧ fase ε t = y := by
  have h1 : 0 < 1 - y := by linarith
  refine ⟨ε * y / (1 - y), div_nonneg (mul_nonneg hε.le hy0) h1.le, ?_⟩
  unfold fase
  have h2 : ε * y / (1 - y) + ε = ε / (1 - y) := by field_simp; ring
  rw [h2, div_div_div_cancel_right₀ h1.ne', mul_div_cancel_left₀ y hε.ne']

/-- **`φ_ε([0, ∞)) = [0, 1)`.** -/
theorem fase_image {ε : ℝ} (hε : 0 < ε) : fase ε '' Ici 0 = Ico 0 1 := by
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨fase_nonneg hε ht, fase_lt_one hε ht⟩
  · rintro ⟨hy0, hy1⟩
    obtain ⟨t, ht, h⟩ := fase_surj hε hy0 hy1
    exact ⟨t, ht, h⟩

/-- **`φ_ε(t) → 1` quando `t → ∞`**, por baixo. -/
theorem fase_tendsto_one {ε : ℝ} (hε : 0 < ε) : Tendsto (fase ε) atTop (𝓝[<] 1) := by
  have hden : Tendsto (fun t : ℝ => t + ε) atTop atTop := tendsto_atTop_add_const_right _ ε tendsto_id
  have hlim : Tendsto (fun t : ℝ => 1 - ε / (t + ε)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hden)
  rw [sub_zero] at hlim
  have heq : (fun t : ℝ => 1 - ε / (t + ε)) =ᶠ[atTop] fase ε := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    unfold fase
    have : t + ε ≠ 0 := by linarith
    field_simp
    ring
  refine tendsto_nhdsWithin_iff.mpr ⟨hlim.congr' heq, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact fase_lt_one hε ht

/-- **`sup φ_ε([0, ∞)) = 1`.** -/
theorem fase_sSup {ε : ℝ} (hε : 0 < ε) : sSup (fase ε '' Ici 0) = 1 := by
  rw [fase_image hε, csSup_Ico zero_lt_one]

/-- **Não há máximo**: todo valor da fase é superado por outro. -/
theorem fase_sem_maximo {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    ∃ t', t < t' ∧ fase ε t < fase ε t' :=
  ⟨t + 1, by linarith, fase_strictMonoOn hε ht (by simp only [mem_Ici]; linarith) (by linarith)⟩

/-! ## A fronteira antes do infinito: `ρ = r/(1 + r)`, `ε = 1/(1 + r)` -/

/-- `ρ(r) = r/(1 + r)`. -/
noncomputable def rho (r : ℝ) : ℝ := r / (1 + r)

/-- `ε(r) = 1/(1 + r)`. -/
noncomputable def eps (r : ℝ) : ℝ := 1 / (1 + r)

theorem rho_eq_fase (r : ℝ) : rho r = fase 1 r := by
  unfold rho fase
  rw [add_comm]

theorem rho_add_eps {r : ℝ} (hr : 0 ≤ r) : rho r + eps r = 1 := by
  unfold rho eps
  have : 1 + r ≠ 0 := by linarith
  field_simp
  ring

theorem eps_pos {r : ℝ} (hr : 0 ≤ r) : 0 < eps r := by
  unfold eps
  exact div_pos one_pos (by linarith)

/-- **`f → ∞ ⟺ ε(f) → 0`** (para `f ≥ 0`). -/
theorem fronteira_iff_eps {α : Type*} {l : Filter α} {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    Tendsto f l atTop ↔ Tendsto (fun x => eps (f x)) l (𝓝 0) := by
  have heps : (fun x => eps (f x)) = fun x => (1 + f x)⁻¹ := by
    funext x
    simp [eps]
  constructor
  · intro h
    rw [heps]
    exact (tendsto_atTop_add_const_left l 1 h).inv_tendsto_atTop
  · intro h
    have hpos : Tendsto (fun x => eps (f x)) l (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨h, Eventually.of_forall fun x => eps_pos (hf x)⟩
    have h1 : Tendsto (fun x => 1 + f x) l atTop := by
      have := hpos.inv_tendsto_nhdsGT_zero
      rw [heps] at this
      exact this.congr fun x => by simp [Pi.inv_apply]
    have h2 := tendsto_atTop_add_const_left l (-1) h1
    simpa using h2

/-- **`f → ∞ ⟺ ρ(f) → 1`** (para `f ≥ 0`). -/
theorem fronteira_iff_rho {α : Type*} {l : Filter α} {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    Tendsto f l atTop ↔ Tendsto (fun x => rho (f x)) l (𝓝 1) := by
  have hr : (fun x => rho (f x)) = fun x => 1 - eps (f x) := by
    funext x
    have := rho_add_eps (hf x)
    linarith
  rw [fronteira_iff_eps hf, hr]
  constructor
  · intro h
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  · intro h
    have := (tendsto_const_nhds (x := (1 : ℝ))).sub h
    simpa using this

end ATK.FronteiraUm

#print axioms ATK.FronteiraUm.fase_zero
#print axioms ATK.FronteiraUm.fase_nonneg
#print axioms ATK.FronteiraUm.fase_lt_one
#print axioms ATK.FronteiraUm.fase_ne_one
#print axioms ATK.FronteiraUm.fase_strictMonoOn
#print axioms ATK.FronteiraUm.fase_surj
#print axioms ATK.FronteiraUm.fase_image
#print axioms ATK.FronteiraUm.fase_tendsto_one
#print axioms ATK.FronteiraUm.fase_sSup
#print axioms ATK.FronteiraUm.fase_sem_maximo
#print axioms ATK.FronteiraUm.rho_eq_fase
#print axioms ATK.FronteiraUm.rho_add_eps
#print axioms ATK.FronteiraUm.eps_pos
#print axioms ATK.FronteiraUm.fronteira_iff_eps
#print axioms ATK.FronteiraUm.fronteira_iff_rho
