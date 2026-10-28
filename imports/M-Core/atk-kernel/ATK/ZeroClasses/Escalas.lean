import ATK.ZeroClasses.Construcao

/-!
# ATK-ZERO-CLASSES — as escalas em que um zero fora da linha ainda pode existir

Um zero não trivial fora da linha só pode estar no **complemento das regiões excluídas**. O kernel prova as
exclusões que tem; as da literatura entram como **hipóteses nomeadas** (com a referência), e o kernel deriva a
janela que sobra.

**1. Perto do primeiro zero: a lei da cauda certificada** (`lei_da_cauda`, `primeiro_zero_simples`,
`cauda_nao_zero`). No disco de raio `10⁻⁶` em torno de `½ + 14,1347251417 i`, a contração `g` do certificado
(§4f) dá, para todo `z` do disco,

  `(|c|/2)·|z − ρ₁| ≤ |ζ(z)| ≤ (3|c|/2)·|z − ρ₁|`,  `c ≈ 0,7833 + 0,1247 i`, `|c| ≈ 0,793`;

o primeiro zero é **simples**, e nenhum ponto do disco fora da linha é zero. É a versão provada da medição
numérica `R_n ≈ 0,79316·d_n` da "cauda ATK": a cauda tende a zero, sem zeros exatos.

**2. O que o kernel exclui sozinho** (`escalas_kernel`): um zero fora da linha tem `(Im ρ)² ≥ 3/4`,
`c(γ) < Re ρ < 1 − c(γ)` e está fora do disco certificado.

**3. A janela da literatura** (`janela`, hipóteses `VerificadoAte H` e `RegiaoClassica R`):
* `H = 3 000 175 332 800` (Platt–Trudgian 2021: todos os zeros até essa altura estão na linha e são simples);
* `R = 4,896`, `t ≥ 3` (Bellotti–Trudgian–Yang 2026: sem zeros em `σ ≥ 1 − 1/(R log t)`).

Então todo zero fora da linha tem **`|γ| > H` e `1/(R log|γ|) < Re ρ < 1 − 1/(R log|γ|)`**. A janela **alarga** com a
altura (`janela_alarga`): **nenhuma reta vertical `σ₀ ∈ (0,1)` fica excluída em todas as alturas**
(`nenhuma_reta_excluida`); as retas ATK `σₙ = ½ + 1/(2n+3)` estão **todas** dentro da janela acima de `H`
(`retas_atk_na_janela`, `retas_atk_acima_de_H`). Por isso não existe "uma escala exata": existe a região
`|γ| > 3·10¹²`, `Re ρ` na janela, e a esparsidade (Bohr–Landau, §4w; Guth–Maynard 2026: `N(σ,T) ≤ T^{30(1−σ)/13+o(1)}`).
-/

open Complex ComplexConjugate Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.Escalas

open ATK.ZeroClasses ATK.ZeroClasses.Zeta ATK.ZeroClasses.Hipotetico
open ATK.ZeroCert (z0 rr g cC lip_g fixo_iff zero_na_linha hasDerivAt_g norm_deriv_g cC_ne B_sub sub_bola)

/-! ## 1. A lei da cauda certificada -/

theorem zeta_eq_cC (z : ℂ) : riemannZeta z = cC * (z - g z) := by
  unfold g
  field_simp [cC_ne]
  ring

/-- **Lei da cauda certificada** no disco de raio `10⁻⁶`: `(|c|/2)·d ≤ |ζ| ≤ (3|c|/2)·d`, `d = |z − ρ₁|`. -/
theorem lei_da_cauda : ∃ ρ ∈ ATK.ZetaSimetria.Z, ρ.re = 1 / 2 ∧ ρ ∈ closedBall z0 ((rr : ℚ) : ℝ) ∧
    ∀ z ∈ closedBall z0 ((rr : ℚ) : ℝ),
      ‖cC‖ / 2 * ‖z - ρ‖ ≤ ‖riemannZeta z‖ ∧ ‖riemannZeta z‖ ≤ 3 * ‖cC‖ / 2 * ‖z - ρ‖ := by
  obtain ⟨ρ, hρ, hre, hB, _⟩ := zero_na_linha
  refine ⟨ρ, hρ, hre, hB, fun z hz => ?_⟩
  have hfix : g ρ = ρ := (fixo_iff ρ).mpr hρ.1
  have hl := lip_g.dist_le_mul z hz ρ hB
  rw [hfix, dist_eq_norm, dist_eq_norm] at hl
  have hl' : ‖g z - ρ‖ ≤ 1 / 2 * ‖z - ρ‖ := by simpa using hl
  have hnorm : ‖riemannZeta z‖ = ‖cC‖ * ‖z - g z‖ := by rw [zeta_eq_cC, norm_mul]
  have e : z - g z = (z - ρ) - (g z - ρ) := by ring
  have h1 : ‖z - ρ‖ - ‖g z - ρ‖ ≤ ‖z - g z‖ := by rw [e]; exact norm_sub_norm_le _ _
  have h2 : ‖z - g z‖ ≤ ‖z - ρ‖ + ‖g z - ρ‖ := by rw [e]; exact norm_sub_le _ _
  have hc := norm_nonneg cC
  rw [hnorm]
  constructor <;> nlinarith

/-- **O primeiro zero é simples.** -/
theorem primeiro_zero_simples : ∃ ρ ∈ ATK.ZetaSimetria.Z, ρ.re = 1 / 2 ∧
    ρ ∈ closedBall z0 ((rr : ℚ) : ℝ) ∧ deriv riemannZeta ρ ≠ 0 := by
  obtain ⟨ρ, hρ, hre, hB, _⟩ := zero_na_linha
  refine ⟨ρ, hρ, hre, hB, fun h0 => ?_⟩
  have hd := (hasDerivAt_g (sub_bola (by norm_num) (B_sub hB))).deriv
  have hn := norm_deriv_g hB
  rw [hd, h0, zero_div, sub_zero, norm_one] at hn
  norm_num at hn

/-- **Nenhum ponto do disco certificado fora da linha é zero.** -/
theorem cauda_nao_zero {z : ℂ} (hz : z ∈ closedBall z0 ((rr : ℚ) : ℝ)) (hre : z.re ≠ 1 / 2) :
    riemannZeta z ≠ 0 := by
  obtain ⟨ρ, _, hρre, _, huniq⟩ := zero_na_linha
  intro h0
  exact hre (huniq z hz h0 ▸ hρre)

/-! ## 2. O que o kernel exclui sozinho -/

/-- **As escalas excluídas pelo kernel**: altura, bordas e o disco do primeiro zero. -/
theorem escalas_kernel {ρ : ℂ} (h : ForaCritico ρ) :
    3 / 4 ≤ ρ.im ^ 2 ∧ 1 / (256 * ATK.ZetaRegiao.A ρ.im) < ρ.re ∧
      ρ.re < 1 - 1 / (256 * ATK.ZetaRegiao.A ρ.im) ∧ ρ ∉ closedBall z0 ((rr : ℚ) : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := restricoes_locais ρ h
  exact ⟨h1, h2, h3, fun hB => cauda_nao_zero hB h.2 h.1.1⟩

/-! ## 3. A janela da literatura -/

/-- Verificação até a altura `H` (Platt–Trudgian 2021: `H = 3 000 175 332 800`). -/
def VerificadoAte (H : ℝ) : Prop := ∀ ρ ∈ ATK.ZetaSimetria.Z, |ρ.im| ≤ H → ρ.re = 1 / 2

/-- Região clássica sem zeros `σ ≥ 1 − 1/(R log t)`, `|t| ≥ 3` (Bellotti–Trudgian–Yang 2026: `R = 4,896`). -/
def RegiaoClassica (R : ℝ) : Prop :=
  ∀ s : ℂ, 3 ≤ |s.im| → riemannZeta s = 0 → s.re < 1 - 1 / (R * Real.log |s.im|)

/-- **A janela**: todo zero fora da linha tem `|γ| > H` e `1/(R log|γ|) < Re ρ < 1 − 1/(R log|γ|)`. -/
theorem janela {H R : ℝ} (hV : VerificadoAte H) (hH : 3 ≤ H) (hR : RegiaoClassica R) {ρ : ℂ}
    (h : ForaCritico ρ) :
    H < |ρ.im| ∧ 1 / (R * Real.log |ρ.im|) < ρ.re ∧ ρ.re < 1 - 1 / (R * Real.log |ρ.im|) := by
  have hγ : H < |ρ.im| := by
    by_contra hc
    exact h.2 (hV ρ h.1 (not_lt.mp hc))
  have h3 : 3 ≤ |ρ.im| := by linarith
  refine ⟨hγ, ?_, hR ρ h3 h.1.1⟩
  have ht := ATK.ZetaSimetria.torcao_mem_Z h.1
  have him : (ATK.ZetaSimetria.torcao ρ).im = ρ.im := by simp [ATK.ZetaSimetria.torcao]
  have := hR _ (him ▸ h3) ht.1
  rw [ATK.ZetaSimetria.re_torcao, him] at this
  linarith

/-- **A janela alarga com a altura**: `1/(R log t) → 0`. -/
theorem janela_alarga {R : ℝ} (hR : 0 < R) : Tendsto (fun t : ℝ => 1 / (R * Real.log t)) atTop (𝓝 0) := by
  have h : Tendsto (fun t : ℝ => R * Real.log t) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hR
  refine h.inv_tendsto_atTop.congr fun t => ?_
  simp only [Pi.inv_apply, one_div]

/-- **Nenhuma reta vertical `σ₀ < 1` fica excluída em todas as alturas** pela região clássica. -/
theorem nenhuma_reta_excluida {R σ₀ : ℝ} (hR : 0 < R) (h : σ₀ < 1) :
    ∃ T : ℝ, ∀ t ≥ T, σ₀ < 1 - 1 / (R * Real.log t) := by
  have hev : ∀ᶠ t in atTop, 1 / (R * Real.log t) < 1 - σ₀ :=
    (janela_alarga hR).eventually (gt_mem_nhds (by linarith))
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  exact ⟨T, fun t ht => by have := hT t ht; linarith⟩

/-- **As retas ATK `σₙ = ½ + 1/(2n+3)` estão dentro da janela** sempre que `R log t > 6`. -/
theorem retas_atk_na_janela {R t : ℝ} (hRt : 6 < R * Real.log t) (n : ℕ) :
    1 / (R * Real.log t) < 1 / 2 + ATK.ZeroClasses.Construcao.delta n ∧
      1 / 2 + ATK.ZeroClasses.Construcao.delta n < 1 - 1 / (R * Real.log t) := by
  have hd := ATK.ZeroClasses.Construcao.delta_pos n
  have hd3 := ATK.ZeroClasses.Construcao.delta_le n
  have hpos : 0 < R * Real.log t := by linarith
  have hlt : 1 / (R * Real.log t) < 1 / 6 := by
    rw [div_lt_div_iff₀ hpos (by norm_num)]; linarith
  constructor <;> linarith

/-- Acima de `H = 3 000 175 332 800` com `R = 4,896`, **todas** as retas ATK estão na janela. -/
theorem retas_atk_acima_de_H {t : ℝ} (ht : (3000175332800 : ℝ) < t) (n : ℕ) :
    1 / (4.896 * Real.log t) < 1 / 2 + ATK.ZeroClasses.Construcao.delta n ∧
      1 / 2 + ATK.ZeroClasses.Construcao.delta n < 1 - 1 / (4.896 * Real.log t) := by
  refine retas_atk_na_janela ?_ n
  have he : Real.exp 2 < t := by
    have : Real.exp 2 < 8 := by
      have := Real.exp_one_lt_d9
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [h2]; nlinarith [Real.exp_pos 1]
    linarith
  have hl : 2 < Real.log t := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]; exact he
  linarith

/-- **A janela concreta de 2026** (as duas referências como hipóteses). -/
theorem janela_2026 (hV : VerificadoAte 3000175332800) (hR : RegiaoClassica 4.896) {ρ : ℂ}
    (h : ForaCritico ρ) :
    (3000175332800 : ℝ) < |ρ.im| ∧ 1 / (4.896 * Real.log |ρ.im|) < ρ.re ∧
      ρ.re < 1 - 1 / (4.896 * Real.log |ρ.im|) :=
  janela hV (by norm_num) hR h

end ATK.ZeroClasses.Escalas

#print axioms ATK.ZeroClasses.Escalas.zeta_eq_cC
#print axioms ATK.ZeroClasses.Escalas.lei_da_cauda
#print axioms ATK.ZeroClasses.Escalas.primeiro_zero_simples
#print axioms ATK.ZeroClasses.Escalas.cauda_nao_zero
#print axioms ATK.ZeroClasses.Escalas.escalas_kernel
#print axioms ATK.ZeroClasses.Escalas.janela
#print axioms ATK.ZeroClasses.Escalas.janela_alarga
#print axioms ATK.ZeroClasses.Escalas.nenhuma_reta_excluida
#print axioms ATK.ZeroClasses.Escalas.retas_atk_na_janela
#print axioms ATK.ZeroClasses.Escalas.retas_atk_acima_de_H
#print axioms ATK.ZeroClasses.Escalas.janela_2026
