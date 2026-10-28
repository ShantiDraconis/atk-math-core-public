import ATK.BLProva

/-!
# ATK-RH — `1/2` como incógnita: o zero `β + iγ` com as duas partes livres

Nada é fixado em `1/2`. As incógnitas são `β = Re ρ`, `γ = Im ρ` e um centro `κ` no lugar de `1/2`;
o sistema é `Re ζ(β + iγ) = 0` e `Im ζ(β + iγ) = 0` (`sistema_iff`). O que o kernel decide:

* **as soluções vêm em quartetos** `(β, γ), (1 − β, γ), (β, −γ), (1 − β, −γ)`, com `0 < β < 1` e `γ ≠ 0`
  (`sistema`);
* **o centro**: para qualquer `κ`, `Σ_{ρ, 0<γ≤T} (β − κ) = (1/2 − κ)·N(T)` (`soma_desvio`); igualar o
  resto a zero, `Σ (β − κ) = 0`, **resolve a incógnita**: `κ = 1/2` (`incognita_resolvida`), sem RH.
  A média das partes reais dos zeros até qualquer altura é **exatamente** `1/2` (`centro_exato`);
* **a dispersão** `Σ (β − 1/2)²`: `≤ δ²·N(T) + C_δ·T` para todo `δ > 0` (`dispersao_le`, via Bohr–Landau,
  incondicional); a dispersão média tende a `0` se `N(T)/T → ∞` (`dispersao_media_tende_zero`, condicional
  só em B10);
* **o máximo**: dispersão nula em toda altura `⟺ RH` (`rh_iff_dispersao`) — aberto.

Ou seja: o centro `1/2` é exato (teorema); a concentração em torno dele é assintótica (teorema, com B10
para a média); que **cada** zero esteja no centro é RH.
-/

open Complex Filter Topology

namespace ATK.ZeroIncognito

open ATK.ZetaSimetria ATK.ForaDaLinha ATK.BohrLandau ATK.BLProva ATK.EixoDeslocado

/-- **O sistema**: `ζ(β + iγ) = 0` são duas equações reais nas incógnitas `β, γ`. -/
theorem sistema_iff (β γ : ℝ) :
    riemannZeta ((β : ℂ) + (γ : ℂ) * I) = 0 ↔
      (riemannZeta ((β : ℂ) + (γ : ℂ) * I)).re = 0 ∧
        (riemannZeta ((β : ℂ) + (γ : ℂ) * I)).im = 0 := by
  rw [Complex.ext_iff]; simp

/-- **Quartetos**: uma solução não trivial `(β, γ)` tem `0 < β < 1`, `γ ≠ 0`, e `(1 − β, γ)`,
`(β, −γ)`, `(1 − β, −γ)` também são soluções. -/
theorem sistema {β γ : ℝ} (hz : riemannZeta ((β : ℂ) + (γ : ℂ) * I) = 0)
    (ht : ¬ Trivial ((β : ℂ) + (γ : ℂ) * I)) :
    0 < β ∧ β < 1 ∧ γ ≠ 0 ∧
      riemannZeta (((1 - β : ℝ) : ℂ) + (γ : ℂ) * I) = 0 ∧
      riemannZeta ((β : ℂ) + ((-γ : ℝ) : ℂ) * I) = 0 ∧
      riemannZeta (((1 - β : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I) = 0 := by
  set s : ℂ := (β : ℂ) + (γ : ℂ) * I with hs
  have hZ : s ∈ Z := (mem_Z_iff_nao_trivial s).mpr ⟨hz, ht⟩
  have hre : s.re = β := by simp [hs]
  have him : s.im = γ := by simp [hs]
  obtain ⟨-, h0, h1⟩ := hZ
  have hγ : γ ≠ 0 := by rw [← him]; exact im_ne_zero_of_mem_Z ⟨hz, h0, h1⟩
  have e1 : torcao s = ((1 - β : ℝ) : ℂ) + (γ : ℂ) * I := by
    apply Complex.ext <;> simp [torcao, hs]
  have e2 : espelho s = (β : ℂ) + ((-γ : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [espelho, hs]
  have e3 : tensao s = ((1 - β : ℝ) : ℂ) + ((-γ : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [tensao, hs]
  refine ⟨by rw [← hre]; exact h0, by rw [← hre]; exact h1, hγ, ?_, ?_, ?_⟩
  · rw [← e1]; exact (torcao_mem_Z ⟨hz, h0, h1⟩).1
  · rw [← e2]; exact (espelho_mem_Z ⟨hz, h0, h1⟩).1
  · rw [← e3]; exact (tensao_mem_Z ⟨hz, h0, h1⟩).1

/-- Os zeros não triviais com `0 < γ ≤ T`, como `Finset`. -/
noncomputable def F (T : ℝ) : Finset ℂ := (todos_finite T).toFinset

theorem mem_F {ρ : ℂ} {T : ℝ} : ρ ∈ F T ↔ ρ ∈ todos T := Set.Finite.mem_toFinset _

theorem card_F (T : ℝ) : ((F T).card : ℝ) = (todos T).ncard := by
  rw [Set.ncard_eq_toFinset_card _ (todos_finite T)]; rfl

theorem torcao_mem_todos {ρ : ℂ} {T : ℝ} (h : ρ ∈ todos T) : torcao ρ ∈ todos T :=
  ⟨torcao_mem_Z h.1, by rw [im_torcao]; exact h.2.1, by rw [im_torcao]; exact h.2.2⟩

/-- **Desvio total nulo**: `Σ_{0<γ≤T} (β − 1/2) = 0`, incondicional. -/
theorem soma_desvio_meio (T : ℝ) : ∑ ρ ∈ F T, (ρ.re - 1 / 2) = 0 := by
  have h : ∑ ρ ∈ F T, (ρ.re - 1 / 2) = ∑ ρ ∈ F T, ((torcao ρ).re - 1 / 2) := by
    refine Finset.sum_nbij' torcao torcao ?_ ?_ ?_ ?_ ?_
    · intro ρ hρ; exact mem_F.mpr (torcao_mem_todos (mem_F.mp hρ))
    · intro ρ hρ; exact mem_F.mpr (torcao_mem_todos (mem_F.mp hρ))
    · intro ρ _; exact ZetaSimetria.torcao_torcao ρ
    · intro ρ _; exact ZetaSimetria.torcao_torcao ρ
    · intro ρ _; rw [ZetaSimetria.torcao_torcao]
  have h2 : ∑ ρ ∈ F T, ((torcao ρ).re - 1 / 2) = -∑ ρ ∈ F T, (ρ.re - 1 / 2) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [re_torcao]; ring
  linarith

/-- **Desvio em relação a um centro incógnito `κ`**: `Σ (β − κ) = (1/2 − κ)·N(T)`. -/
theorem soma_desvio (κ T : ℝ) : ∑ ρ ∈ F T, (ρ.re - κ) = (1 / 2 - κ) * (F T).card := by
  have : ∀ ρ : ℂ, ρ.re - κ = (ρ.re - 1 / 2) + (1 / 2 - κ) := fun ρ => by ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, soma_desvio_meio, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **A incógnita é resolvida**: havendo zeros até a altura `T`, `Σ (β − κ) = 0 ⟺ κ = 1/2`. -/
theorem incognita_resolvida (κ T : ℝ) (hne : (todos T).Nonempty) :
    ∑ ρ ∈ F T, (ρ.re - κ) = 0 ↔ κ = 1 / 2 := by
  rw [soma_desvio]
  obtain ⟨ρ, hρ⟩ := hne
  have hc : (0 : ℝ) < (F T).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨ρ, mem_F.mpr hρ⟩
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · linarith
    · linarith
  · intro h; rw [h]; ring

/-- **O centro é exato**: a média das partes reais dos zeros com `0 < γ ≤ T` é `1/2`. -/
theorem centro_exato (T : ℝ) (hne : (todos T).Nonempty) :
    (∑ ρ ∈ F T, ρ.re) / (F T).card = 1 / 2 := by
  obtain ⟨ρ, hρ⟩ := hne
  have hc : (0 : ℝ) < (F T).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨ρ, mem_F.mpr hρ⟩
  have h := soma_desvio_meio T
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h
  rw [div_eq_iff hc.ne']
  linarith

/-- **Dispersão** dos zeros em torno de `1/2` até a altura `T`. -/
noncomputable def dispersao (T : ℝ) : ℝ := ∑ ρ ∈ F T, (ρ.re - 1 / 2) ^ 2

theorem dispersao_nonneg (T : ℝ) : 0 ≤ dispersao T :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **RH ⟺ dispersão nula em toda altura.** -/
theorem rh_iff_dispersao : RiemannHypothesis ↔ ∀ T : ℝ, dispersao T = 0 := by
  constructor
  · intro h T
    refine Finset.sum_eq_zero fun ρ hρ => ?_
    rw [re_de_rh h (mem_F.mp hρ).1]; ring
  · intro h
    refine riemann_iff_vazio.mpr ⟨fun ρ => ?_⟩
    obtain ⟨ρ, hρZ, hne⟩ := ρ
    have him := im_ne_zero_of_mem_Z hρZ
    -- um representante com parte imaginária positiva e a mesma parte real
    obtain ⟨σ, hσZ, hσim, hσre⟩ : ∃ σ ∈ Z, 0 < σ.im ∧ σ.re = ρ.re := by
      rcases lt_or_gt_of_ne him with hneg | hpos
      · refine ⟨espelho ρ, espelho_mem_Z hρZ, ?_, ?_⟩
        · simp [espelho]; linarith
        · simp [espelho]
      · exact ⟨ρ, hρZ, hpos, rfl⟩
    have hmem : σ ∈ F σ.im := mem_F.mpr ⟨hσZ, hσim, le_rfl⟩
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun ρ _ => sq_nonneg (ρ.re - 1 / 2))).mp
      (h σ.im) σ hmem
    have : σ.re = 1 / 2 := by nlinarith [sq_nonneg (σ.re - 1 / 2)]
    exact hne (hσre ▸ this)

theorem card_filter_le (T : ℝ) (D : Set ℂ) (hD : D.Finite) [DecidablePred (· ∈ D)] :
    (((F T).filter (· ∈ D)).card : ℝ) ≤ D.ncard := by
  have h : (((F T).filter (· ∈ D) : Finset ℂ) : Set ℂ) ⊆ D :=
    fun ρ hρ => (Finset.mem_filter.mp hρ).2
  have := Set.ncard_le_ncard h hD
  rw [Set.ncard_coe_finset] at this
  exact_mod_cast this

/-- **Dispersão, incondicional** (via Bohr–Landau): `Σ (β − 1/2)² ≤ δ²·N(T) + C_δ·T`. -/
theorem dispersao_le (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T → dispersao T ≤ δ ^ 2 * (F T).card + C * T := by
  classical
  obtain ⟨C, hC⟩ := fora_da_faixa δ hδ
  refine ⟨C / 4, fun T hT => ?_⟩
  set D := direita (1 / 2 + δ) T with hD
  set E := esquerda (1 / 2 - δ) T with hE
  have hDf : D.Finite := (todos_finite T).subset (direita_subset _ T)
  have hEf : E.Finite := (todos_finite T).subset (esquerda_subset _ T)
  have hterm : ∀ ρ ∈ F T, (ρ.re - 1 / 2) ^ 2 ≤
      δ ^ 2 + 1 / 4 * ((if ρ ∈ D then (1 : ℝ) else 0) + (if ρ ∈ E then (1 : ℝ) else 0)) := by
    intro ρ hρ
    obtain ⟨⟨hz, h0, h1⟩, hi0, hiT⟩ := mem_F.mp hρ
    have hD0 : (0 : ℝ) ≤ if ρ ∈ D then 1 else 0 := by split_ifs <;> norm_num
    have hE0 : (0 : ℝ) ≤ if ρ ∈ E then 1 else 0 := by split_ifs <;> norm_num
    by_cases hd : 1 / 2 + δ < ρ.re
    · have hm : ρ ∈ D := ⟨⟨hz, h0, h1⟩, hd, hi0, hiT⟩
      rw [if_pos hm]
      nlinarith
    · by_cases he : ρ.re < 1 / 2 - δ
      · have hm : ρ ∈ E := ⟨⟨hz, h0, h1⟩, he, hi0, hiT⟩
        rw [if_pos hm]
        nlinarith
      · push Not at hd he
        nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole] at hsum
  have hDc := card_filter_le T D hDf
  have hEc := card_filter_le T E hEf
  have hCT := hC T hT
  unfold dispersao
  nlinarith

/-- **Condicional só em B10**: a dispersão média `Σ (β − 1/2)² / N(T)` tende a `0`. -/
theorem dispersao_media_tende_zero (hN : CrescimentoN) :
    Tendsto (fun T => dispersao T / ((F T).card : ℝ)) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun T =>
    lt_of_lt_of_le ha (div_nonneg (dispersao_nonneg T) (Nat.cast_nonneg _)), fun b hb => ?_⟩
  set δ : ℝ := Real.sqrt (b / 4) with hδdef
  have hδ : 0 < δ := Real.sqrt_pos.mpr (by linarith)
  have hδ2 : δ ^ 2 = b / 4 := Real.sq_sqrt (by linarith)
  obtain ⟨C, hC⟩ := dispersao_le δ hδ
  set K : ℝ := 4 * (|C| + 1) / b with hK
  have hKpos : 0 < K := by positivity
  filter_upwards [eventually_ge_atTop (2 : ℝ), hN.eventually_ge_atTop K] with T hT hNT
  have hT0 : (0 : ℝ) < T := by linarith
  have h2 : K * T ≤ (F T).card := by rw [card_F]; exact (le_div_iff₀ hT0).mp hNT
  have hn : (0 : ℝ) < (F T).card := lt_of_lt_of_le (by positivity) h2
  rw [div_lt_iff₀ hn]
  have hbK : b / 4 * K = |C| + 1 := by rw [hK]; field_simp
  have h3 : (|C| + 1) * T ≤ b / 4 * (F T).card := by
    calc (|C| + 1) * T = b / 4 * (K * T) := by rw [← hbK]; ring
      _ ≤ b / 4 * (F T).card := mul_le_mul_of_nonneg_left h2 (by linarith)
  have h1 := hC T hT
  rw [hδ2] at h1
  nlinarith [le_abs_self C]

end ATK.ZeroIncognito

#print axioms ATK.ZeroIncognito.sistema_iff
#print axioms ATK.ZeroIncognito.sistema
#print axioms ATK.ZeroIncognito.mem_F
#print axioms ATK.ZeroIncognito.card_F
#print axioms ATK.ZeroIncognito.torcao_mem_todos
#print axioms ATK.ZeroIncognito.soma_desvio_meio
#print axioms ATK.ZeroIncognito.soma_desvio
#print axioms ATK.ZeroIncognito.incognita_resolvida
#print axioms ATK.ZeroIncognito.centro_exato
#print axioms ATK.ZeroIncognito.dispersao_nonneg
#print axioms ATK.ZeroIncognito.rh_iff_dispersao
#print axioms ATK.ZeroIncognito.card_filter_le
#print axioms ATK.ZeroIncognito.dispersao_le
#print axioms ATK.ZeroIncognito.dispersao_media_tende_zero
