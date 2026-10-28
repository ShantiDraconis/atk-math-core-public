import ATK.ArgPrincipio
import ATK.ZeroClasses.Pontes

/-!
# ATK-ZERO-CLASSES — princípio do argumento e Rouché aplicados a `ζ` (rodada 25)

`ATK/ArgPrincipio.lean` prova o que faltava na Mathlib: o **princípio do argumento** em círculos, o teorema de
**Rouché** e a forma **afiada** de `E1` (`|f(c)| + M r²/2 < r|f′(c)|` ⟹ exatamente um zero, simples). Aqui eles
são aplicados a `ζ`:

* `contagem_zeta`: `∮ ζ′/ζ = 2πi · Σ ord` em todo disco fechado sem o polo e sem zeros no círculo;
* `rouche_zeta`: `ζ` e qualquer aproximante `F` com `|ζ − F| < |F|` no círculo têm o mesmo número de zeros;
* `E1_zeta_fora`: um disco **fora da linha** que passa `E1` afiado contém **exatamente um** zero de `ζ`, simples,
  fora da linha — e isso **refuta RH**;
* `E1_zeta_linha`: um disco **centrado na linha** (raio `< ½`) que passa `E1` afiado contém exatamente um zero, e
  ele está **na linha** (a torção o fixa);
* `cauda_E1`: infinitos discos disjuntos fora da linha passando `E1` ⟹ infinitos zeros externos;
* `exemplo_quadratico_unico`: o exemplo quadrático enviado (`69/1280 < 160/1280`) tem **exatamente um** zero no
  disco, com `Re > ½`.
-/

open Complex Metric Set Filter Topology
open scoped Real

namespace ATK.ZeroClasses.Rouche

open ATK.ArgPrincipio ATK.ZeroClasses ATK.ZeroClasses.Zeta ATK.ZeroClasses.Hipotetico ATK.ZeroClasses.Encontro

theorem analitica_disco {c : ℂ} {R : ℝ} (h1 : (1 : ℂ) ∉ closedBall c R) :
    AnalyticOnNhd ℂ riemannZeta (closedBall c R) := fun z hz =>
  analyticOn_riemannZeta z fun e => h1 (e ▸ hz)

/-- **Contagem de zeros de `ζ`** pelo princípio do argumento. -/
theorem contagem_zeta {c : ℂ} {R : ℝ} (hR : 0 < R) (h1 : (1 : ℂ) ∉ closedBall c R)
    (hs : ∀ z ∈ sphere c R, riemannZeta z ≠ 0) :
    ∃ S : Finset ℂ, (∀ u, u ∈ S ↔ u ∈ ball c R ∧ riemannZeta u = 0) ∧
      (∮ z in C(c, R), logDeriv riemannZeta z) = 2 * π * I * ∑ u ∈ S, (analyticOrderNatAt riemannZeta u : ℂ) :=
  principio_argumento hR (analitica_disco h1) hs

/-- **Rouché para `ζ`**: um aproximante `F` com `|ζ − F| < |F|` no círculo tem o mesmo número de zeros. -/
theorem rouche_zeta {F : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R) (h1 : (1 : ℂ) ∉ closedBall c R)
    (hF : AnalyticOnNhd ℂ F (closedBall c R)) (hlt : ∀ z ∈ sphere c R, ‖riemannZeta z - F z‖ < ‖F z‖) :
    ∃ SF Sζ : Finset ℂ, (∀ u, u ∈ SF ↔ u ∈ ball c R ∧ F u = 0) ∧
      (∀ u, u ∈ Sζ ↔ u ∈ ball c R ∧ riemannZeta u = 0) ∧
      ∑ u ∈ SF, analyticOrderNatAt F u = ∑ u ∈ Sζ, analyticOrderNatAt riemannZeta u :=
  rouche hR hF (analitica_disco h1) hlt

theorem um_fora_disco {c : ℂ} {r : ℝ} (hD : DiscoFora c r) : (1 : ℂ) ∉ closedBall c r := fun h => by
  have := (discoFora_pontos hD h).2.1
  rw [one_re] at this
  exact lt_irrefl _ this

/-- **`E1` afiado num disco fora da linha**: exatamente um zero de `ζ`, simples, fora da linha — **refuta RH**. -/
theorem E1_zeta_fora {c : ℂ} {r M : ℝ} (hr : 0 < r) (hD : DiscoFora c r)
    (hM : ∀ w ∈ closedBall c r, ‖deriv (deriv riemannZeta) w‖ ≤ M)
    (h : ‖riemannZeta c‖ + M * r ^ 2 / 2 < r * ‖deriv riemannZeta c‖) :
    (∃ ρ ∈ ball c r, ForaCritico ρ ∧ deriv riemannZeta ρ ≠ 0 ∧
      ∀ w ∈ ball c r, riemannZeta w = 0 → w = ρ) ∧ ¬ RiemannHypothesis := by
  obtain ⟨ρ, hρ, h0, hd, hu⟩ := E1_afiado hr (analitica_disco (um_fora_disco hD)) hM h
  obtain ⟨a, b, e⟩ := discoFora_pontos hD (ball_subset_closedBall hρ)
  exact ⟨⟨ρ, hρ, ⟨⟨h0, a, b⟩, e⟩, hd, hu⟩, hFora_iff.mp ⟨ρ, h0, a, b, e⟩⟩

/-- A torção `s ↦ 1 − s̄` preserva um disco centrado na linha. -/
theorem torcao_disco {c z : ℂ} {r : ℝ} (hc : c.re = 1 / 2) (hz : z ∈ ball c r) :
    ATK.ZetaSimetria.torcao z ∈ ball c r := by
  rw [mem_ball, dist_eq_norm] at hz ⊢
  have e : ATK.ZetaSimetria.torcao z - c = -(starRingEnd ℂ) (z - c) := by
    have hc' : ATK.ZetaSimetria.torcao c = c := (ATK.ZetaSimetria.torcao_fixo_iff c).mpr hc
    conv_lhs => rw [← hc']
    unfold ATK.ZetaSimetria.torcao
    simp only [map_sub]
    ring
  rw [e, norm_neg, Complex.norm_conj]
  exact hz

/-- **`E1` afiado num disco centrado na linha** (raio `< ½`): o único zero está **na linha**. -/
theorem E1_zeta_linha {c : ℂ} {r M : ℝ} (hr : 0 < r) (hr2 : r < 1 / 2) (hc : c.re = 1 / 2)
    (hM : ∀ w ∈ closedBall c r, ‖deriv (deriv riemannZeta) w‖ ≤ M)
    (h : ‖riemannZeta c‖ + M * r ^ 2 / 2 < r * ‖deriv riemannZeta c‖) :
    ∃ ρ ∈ ball c r, Critico ρ ∧ deriv riemannZeta ρ ≠ 0 ∧ ∀ w ∈ ball c r, riemannZeta w = 0 → w = ρ := by
  have hstrip : ∀ z ∈ closedBall c r, 0 < z.re ∧ z.re < 1 := by
    intro z hz
    have := Complex.abs_re_le_norm (z - c)
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [sub_re, hc] at this
    have := abs_le.mp (this.trans hz)
    constructor <;> linarith [this.1, this.2]
  have h1 : (1 : ℂ) ∉ closedBall c r := fun h => by
    have := (hstrip 1 h).2; rw [one_re] at this; exact lt_irrefl _ this
  obtain ⟨ρ, hρ, h0, hd, hu⟩ := E1_afiado hr (analitica_disco h1) hM h
  have hρZ : ρ ∈ ATK.ZetaSimetria.Z := ⟨h0, hstrip ρ (ball_subset_closedBall hρ)⟩
  have ht := ATK.ZetaSimetria.torcao_mem_Z hρZ
  have hfix : ATK.ZetaSimetria.torcao ρ = ρ := hu _ (torcao_disco hc hρ) ht.1
  exact ⟨ρ, hρ, ⟨hρZ, (ATK.ZetaSimetria.torcao_fixo_iff ρ).mp hfix⟩, hd, hu⟩

/-- **Cauda por `E1` afiado**: infinitos discos disjuntos fora da linha passando `E1` ⟹ infinitos zeros externos. -/
theorem cauda_E1 {c : ℕ → ℂ} {r M : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hD : ∀ n, DiscoFora (c n) (r n))
    (hM : ∀ n, ∀ w ∈ closedBall (c n) (r n), ‖deriv (deriv riemannZeta) w‖ ≤ M n)
    (h : ∀ n, ‖riemannZeta (c n)‖ + M n * r n ^ 2 / 2 < r n * ‖deriv riemannZeta (c n)‖)
    (hdisj : Pairwise fun m n => Disjoint (ball (c m) (r m)) (ball (c n) (r n))) :
    ATK.ZeroClasses.MundoFora.ForaSet.Infinite := by
  choose ρ hρ using fun n => (E1_zeta_fora (hr n) (hD n) (hM n) (h n)).1
  refine Set.infinite_of_injective_forall_mem (f := ρ) (fun m n hmn => ?_) fun n => (hρ n).2.1
  by_contra hne
  exact Set.disjoint_left.mp (hdisj hne) (hρ m).1 (hmn ▸ (hρ n).1)

/-- **O exemplo quadrático enviado**: `f(z) = (z − c) + ¼(z − c)² + 1/20`, `c = ¾ + 10i`, `r = ⅛`, `M = ½`:
`1/20 + (½)(⅛)²/2 = 69/1280 < 160/1280`, logo **exatamente um** zero em `B(c, ⅛)`, simples, com `Re > ½`. -/
theorem exemplo_quadratico_unico :
    ∃ ρ ∈ ball ATK.ZeroClasses.Forcar.cEx (1 / 8),
      (ρ - ATK.ZeroClasses.Forcar.cEx) + 1 / 4 * (ρ - ATK.ZeroClasses.Forcar.cEx) ^ 2 + 1 / 20 = 0 ∧
      1 / 2 < ρ.re ∧ ∀ w ∈ ball ATK.ZeroClasses.Forcar.cEx (1 / 8),
        (w - ATK.ZeroClasses.Forcar.cEx) + 1 / 4 * (w - ATK.ZeroClasses.Forcar.cEx) ^ 2 + 1 / 20 = 0 → w = ρ := by
  set c := ATK.ZeroClasses.Forcar.cEx
  set f : ℂ → ℂ := fun z => (z - c) + 1 / 4 * (z - c) ^ 2 + 1 / 20 with hf
  have hdf : ∀ z, HasDerivAt f (1 + 1 / 2 * (z - c)) z := by
    intro z
    have h1 := (hasDerivAt_id z).sub_const c
    have h2 := (h1.pow 2).const_mul (1 / 4 : ℂ)
    have h3 := (h1.add h2).add_const (1 / 20 : ℂ)
    convert h3 using 1
    · funext w; simp [hf]
    · simp; ring
  have hdeq : deriv f = fun z => 1 + 1 / 2 * (z - c) := funext fun z => (hdf z).deriv
  have hdd : ∀ z, deriv (deriv f) z = 1 / 2 := by
    intro z
    rw [hdeq]
    have : HasDerivAt (fun z : ℂ => 1 + 1 / 2 * (z - c)) (1 / 2) z := by
      simpa using (((hasDerivAt_id z).sub_const c).const_mul (1 / 2 : ℂ)).const_add 1
    exact this.deriv
  have hfa : AnalyticOnNhd ℂ f (closedBall c (1 / 8)) := fun z _ => by simp only [hf]; fun_prop
  obtain ⟨ρ, hρ, h0, -, hu⟩ := E1_afiado (f := f) (c := c) (r := 1 / 8) (M := 1 / 2) (by norm_num) hfa
    (fun w _ => by rw [hdd]; norm_num)
    (by
      rw [hdeq]
      simp only [hf, sub_self, mul_zero, add_zero, zero_add]
      norm_num)
  refine ⟨ρ, hρ, h0, ?_, hu⟩
  have := Complex.abs_re_le_norm (ρ - c)
  rw [mem_ball, dist_eq_norm] at hρ
  have hre : (ρ - c).re = ρ.re - 3 / 4 := by simp [c, ATK.ZeroClasses.Forcar.cEx]
  rw [hre, abs_le] at this
  linarith [this.1]

end ATK.ZeroClasses.Rouche

#print axioms ATK.ZeroClasses.Rouche.analitica_disco
#print axioms ATK.ZeroClasses.Rouche.contagem_zeta
#print axioms ATK.ZeroClasses.Rouche.rouche_zeta
#print axioms ATK.ZeroClasses.Rouche.um_fora_disco
#print axioms ATK.ZeroClasses.Rouche.E1_zeta_fora
#print axioms ATK.ZeroClasses.Rouche.torcao_disco
#print axioms ATK.ZeroClasses.Rouche.E1_zeta_linha
#print axioms ATK.ZeroClasses.Rouche.cauda_E1
#print axioms ATK.ZeroClasses.Rouche.exemplo_quadratico_unico
