import ATK.ZeroClasses.Regions
import ATK.ZeroClasses.Laws
import ATK.TruncamentoToeplitz

/-!
# ATK-ZERO-CLASSES — o universo hipotético: zeros fora da reta como **hipótese**, não axioma

O prompt pede `OFF_LINE_ZEROS EXIST (AXIOM)`. No kernel isto entra como **hipótese** `HFora`
(`structure UniversoATK`), nunca como `axiom`: se RH for verdadeira, um axioma `HFora` tornaria o
sistema inconsistente e tudo seria "provável". Com a hipótese, cada consequência é um teorema
`HFora → X`, certificado sem risco.

* **o que o universo é** (`universo_iff`): `UniversoATK ⟺ ¬RH`. **Refutar o universo é provar RH**
  (`refutar_universo_iff`): a consistência interna do universo ATK não é "a verificar" separadamente —
  ela **é** a questão aberta;
* **consequências necessárias** (todas incondicionais como implicações): o **quarteto** distinto
  (`quarteto`); um representante em `Ω` e um em `1/2 < Re < 1, Im > 0` (`forma_normal`); os **dois ramos**
  aritméticos, cada um refutando RH sozinho (`ramos`, `ramo_racional_refuta`, `ramo_irracional_refuta`);
  altura `(Im ρ)² ≥ 3/4` e bordas `c(t)` (`restricoes_locais`); só finitos abaixo de cada altura
  (`finitos_abaixo`); **piso de Báez-Duarte** `D_N ≥ μ > 0` (`piso_DN`); **falha de TN** com nível único
  `N ≥ 1` (`falha_toeplitz`) e, sob Csordas, um menor negativo de ordem `≥ 3` (`falha_ordem_tres`);
  **Jensen** não hiperbólico (`falha_jensen`); **mínimo nulo** `m_n = 0` para algum `n ≥ 4`
  (`minimo_nulo`); **nenhum certificado de positividade** (`sem_certificado`); `F(σ,t) = 0` em `Ω`
  (`F_nulo`);
* **painel** (`painel`): `HFora` é equivalente a cada uma dessas falhas — nenhuma é mais fraca do que
  RH, e **nenhuma contradição foi derivada** (derivá-la seria provar RH).
-/

open Complex ComplexConjugate Set Filter Topology

namespace ATK.ZeroClasses.Hipotetico

open ATK.ZeroClasses ATK.ZeroClasses.Zeta ATK.ZeroClasses.Regions ATK.TruncToep

/-- **`H_fora`**: existe um zero `ρ` com `0 < Re ρ < 1`, `Re ρ ≠ 1/2`. -/
def HFora : Prop := ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re ≠ 1 / 2

theorem hFora_iff_fora : HFora ↔ ∃ ρ, ForaCritico ρ :=
  ⟨fun ⟨ρ, h0, h1, h2, h3⟩ => ⟨ρ, ⟨h0, h1, h2⟩, h3⟩, fun ⟨ρ, ⟨h0, h1, h2⟩, h3⟩ => ⟨ρ, h0, h1, h2, h3⟩⟩

/-- **`H_fora ⟺ ¬RH`.** -/
theorem hFora_iff : HFora ↔ ¬ RiemannHypothesis := hFora_iff_fora.trans nao_rh_iff_fora.symm

/-- O universo ATK com zeros fora da reta, como hipótese. -/
structure UniversoATK : Prop where
  fora : HFora

theorem universo_iff : UniversoATK ↔ ¬ RiemannHypothesis :=
  ⟨fun h => hFora_iff.mp h.fora, fun h => ⟨hFora_iff.mpr h⟩⟩

/-- **Refutar o universo ATK é exatamente provar RH.** -/
theorem refutar_universo_iff : (UniversoATK → False) ↔ RiemannHypothesis := by
  rw [universo_iff]
  exact ⟨fun h => by by_contra hc; exact h hc, fun h hn => hn h⟩

theorem orbita_mem {ρ : ℂ} : conj ρ ∈ orbita (1 / 2) ρ ∧ refl (1 / 2) ρ ∈ orbita (1 / 2) ρ ∧
    tor (1 / 2) ρ ∈ orbita (1 / 2) ρ := by
  classical
  simp [orbita]

/-- **Restrições locais**: `(Im ρ)² ≥ 3/4` e `c(t) < Re ρ < 1 − c(t)`. -/
theorem restricoes_locais : ∀ ρ, ForaCritico ρ →
    3 / 4 ≤ ρ.im ^ 2 ∧ 1 / (256 * ATK.ZetaRegiao.A ρ.im) < ρ.re ∧
      ρ.re < 1 - 1 / (256 * ATK.ZetaRegiao.A ρ.im) :=
  fun ρ hρ => ⟨ATK.ZetaRetangulo.sem_zeros_ate_altura ρ hρ.1, ATK.ZetaRegiao.faixa_estreitada ρ hρ.1⟩

/-- Só finitos zeros fora da reta abaixo de cada altura. -/
theorem finitos_abaixo (T : ℝ) : {ρ | ForaCritico ρ ∧ |ρ.im| ≤ T}.Finite :=
  (ATK.ZerosFora.foraAte_finito T).subset fun _ ⟨⟨hz, hre⟩, hT⟩ => ⟨⟨hz, hre⟩, hT⟩

theorem falha_nivel_ge_um : ∀ N, P ATK.XiTP.aXi N ∧ ¬ P ATK.XiTP.aXi (N + 1) → 1 ≤ N :=
  fun _ h => nivel_ge_um h

section Consequencias

variable (H : HFora)
include H

/-- **O quarteto**: quatro zeros distintos, todos fora da reta. -/
theorem quarteto : ∃ ρ, ForaCritico ρ ∧ (orbita (1 / 2) ρ).card = 4 ∧
    ∀ w ∈ orbita (1 / 2) ρ, ForaCritico w := by
  obtain ⟨ρ, hρ, hre⟩ := hFora_iff_fora.mp H
  obtain ⟨h4, hall⟩ := (quarteto_ou_par hρ).1 hre
  exact ⟨ρ, ⟨hρ, hre⟩, h4, hall⟩

/-- **Forma normal**: há um zero fora da reta em `Ω` e outro em `1/2 < Re < 1`, `Im > 0`. -/
theorem forma_normal : (∃ ρ, ForaCritico ρ ∧ ρ ∈ Omega) ∧
    (∃ ρ, ForaCritico ρ ∧ 1 / 2 < ρ.re ∧ 0 < ρ.im) := by
  obtain ⟨ρ, hρ, h4, hall⟩ := quarteto H
  obtain ⟨hc, hr, ht⟩ := orbita_mem (ρ := ρ)
  have him := ATK.ZetaSimetria.im_ne_zero_of_mem_Z hρ.1
  have hs0 := hρ.1.2.1
  have hs1 := hρ.1.2.2
  -- escolhe, entre `ρ, ρ̄, 1 − ρ, 1 − ρ̄`, os de `Im > 0` à esquerda e à direita
  rcases lt_or_gt_of_ne hρ.2 with hl | hg <;> rcases lt_or_gt_of_ne him with hn | hp
  · refine ⟨⟨conj ρ, hall _ hc, by simpa using hs0, by simpa using hl, by simp; linarith⟩,
      ⟨refl (1 / 2) ρ, hall _ hr, by simp; linarith, by simp; linarith⟩⟩
  · refine ⟨⟨ρ, hρ, hs0, hl, hp⟩, ⟨tor (1 / 2) ρ, hall _ ht, by simp; linarith, by simpa using hp⟩⟩
  · refine ⟨⟨refl (1 / 2) ρ, hall _ hr, by simp; linarith, by simp; linarith, by simp; linarith⟩,
      ⟨conj ρ, hall _ hc, by simpa using hg, by simp; linarith⟩⟩
  · refine ⟨⟨tor (1 / 2) ρ, hall _ ht, by simp; linarith, by simp; linarith, by simpa using hp⟩,
      ⟨ρ, hρ, hg, hp⟩⟩

/-- **Os dois ramos aritméticos.** -/
theorem ramos : (∃ ρ, ForaCritico ρ ∧ RatRe riemannZeta ρ) ∨ (∃ ρ, ForaCritico ρ ∧ IrrRe riemannZeta ρ) := by
  obtain ⟨ρ, hρ⟩ := hFora_iff_fora.mp H
  rcases ratRe_or_irrRe (f := riemannZeta) hρ.1.1 with h | h
  · exact Or.inl ⟨ρ, hρ, h⟩
  · exact Or.inr ⟨ρ, hρ, h⟩

/-- **Piso de Báez-Duarte**: `D_N ≥ μ > 0` para todo `N`. -/
theorem piso_DN : ∃ μ : ℝ, 0 < μ ∧ ∀ N, μ ≤ ATK.Conditional.Riemann.DN N := by
  obtain ⟨ρ, hρ, hre⟩ := hFora_iff_fora.mp H
  exact ATK.ForaDaLinha.condensacao ⟨ρ, hρ, hre⟩

/-- **Falha de Toeplitz**: `T(a_Ξ)` não é TN, com nível único de primeira falha `N ≥ 1`. -/
theorem falha_toeplitz : ¬ (ATK.ToeplitzTN.toep ATK.XiTP.aXi).IsTotallyNonneg ∧
    ∃! N, P ATK.XiTP.aXi N ∧ ¬ P ATK.XiTP.aXi (N + 1) := by
  have hn := hFora_iff.mp H
  exact ⟨fun h => hn (ATK.XiCresc.rh_iff_tn.mpr h), nivel_de_zero_fora hn⟩

/-- Sob Csordas: o nível é `≥ 2` e há um menor negativo de ordem `≥ 3`. -/
theorem falha_ordem_tres (hψ : Csordas) :
    (∀ N, P ATK.XiTP.aXi N ∧ ¬ P ATK.XiTP.aXi (N + 1) → 2 ≤ N) ∧
      ∃ r, 3 ≤ r ∧ ∃ I J : Fin r → ℕ, StrictMono I ∧ StrictMono J ∧
        ((ATK.ToeplitzTN.toep ATK.XiTP.aXi).submatrix I J).det < 0 :=
  ⟨fun _ h => nivel_ge_dois_de_csordas hψ h, ordem_ge_tres_de_csordas hψ (hFora_iff.mp H)⟩

/-- **Jensen**: algum `J^{d,0}` não é hiperbólico. -/
theorem falha_jensen : ∃ d, ¬ ATK.Laguerre.RealRooted (ATK.JensenPolya.jensen ATK.JensenPolya.γXi d 0) := by
  by_contra hc
  have : ∀ d, ATK.Laguerre.RealRooted (ATK.JensenPolya.jensen ATK.JensenPolya.γXi d 0) :=
    fun d => by by_contra h; exact hc ⟨d, h⟩
  exact hFora_iff.mp H (ATK.Hurwitz.rh_iff_jensen0.mpr this)

/-- **Mínimo nulo**: `m_n = 0` para algum `n ≥ 4`. -/
theorem minimo_nulo : ∃ n ≥ 4, m n = 0 := by
  by_contra hc
  have : ∀ n ≥ 4, 0 < m n := fun n hn =>
    lt_of_le_of_ne (m_nonneg n) (fun h => hc ⟨n, hn, h.symm⟩)
  exact hFora_iff.mp H (rh_iff_m_pos.mpr this)

/-- **Nenhum certificado de positividade existe.** -/
theorem sem_certificado : ¬ ∃ L, PositiveCertificate K riemannZeta L :=
  fun h => hFora_iff.mp H (rh_iff_certificado.mpr h)

/-- **`F(σ,t) = 0` em algum ponto de `Ω`.** -/
theorem F_nulo : ∃ σ t : ℝ, 0 < σ ∧ σ < 1 / 2 ∧ 0 < t ∧ F σ t = 0 := by
  by_contra hc
  have : ∀ σ t : ℝ, 0 < σ → σ < 1 / 2 → 0 < t → 0 < F σ t := fun σ t h0 h1 ht =>
    lt_of_le_of_ne (F_nonneg σ t) (fun h => hc ⟨σ, t, h0, h1, ht, h.symm⟩)
  exact hFora_iff.mp H (obrigacao_exata.mpr this)

end Consequencias

/-- Cada ramo aritmético, sozinho, refuta RH. -/
theorem ramo_racional_refuta (h : ∃ ρ, ForaCritico ρ ∧ RatRe riemannZeta ρ) : ¬ RiemannHypothesis :=
  let ⟨_, hρ, _⟩ := h; nao_rh_iff_fora.mpr ⟨_, hρ⟩

theorem ramo_irracional_refuta (h : ∃ ρ, ForaCritico ρ ∧ IrrRe riemannZeta ρ) : ¬ RiemannHypothesis :=
  let ⟨_, hρ, hi⟩ := h; irr_refuta hρ.1 hi

/-- **Painel**: `H_fora` é equivalente a cada falha. Nenhuma é mais fraca do que RH. -/
theorem painel :
    (HFora ↔ ¬ RiemannHypothesis) ∧
      (HFora ↔ ¬ (ATK.ToeplitzTN.toep ATK.XiTP.aXi).IsTotallyNonneg) ∧
      (HFora ↔ ∃ N, P ATK.XiTP.aXi N ∧ ¬ Q ATK.XiTP.aXi (N + 1)) ∧
      (HFora ↔ ∃ d, ¬ ATK.Laguerre.RealRooted (ATK.JensenPolya.jensen ATK.JensenPolya.γXi d 0)) ∧
      (HFora ↔ ∃ n ≥ 4, m n = 0) ∧
      (HFora ↔ ZL.Nonempty) ∧
      (HFora ↔ ¬ ∃ L, PositiveCertificate K riemannZeta L) := by
  refine ⟨hFora_iff, ?_, ?_, ⟨falha_jensen, fun ⟨d, hd⟩ => hFora_iff.mpr fun h =>
    hd (ATK.Hurwitz.rh_iff_jensen0.mp h d)⟩, ⟨minimo_nulo, fun ⟨n, hn, h0⟩ => hFora_iff.mpr fun h => by
      have := rh_iff_m_pos.mp h n hn; linarith⟩, ?_, ⟨sem_certificado, fun h => hFora_iff.mpr fun hr =>
        h (rh_iff_certificado.mp hr)⟩⟩
  · rw [hFora_iff, ATK.XiCresc.rh_iff_tn]
  · constructor
    · intro H
      have hn := hFora_iff.mp H
      rw [ATK.XiCresc.rh_iff_tn] at hn
      exact primeira_falha ATK.XiTP.aXi_zero_pos.le hn
    · rintro ⟨N, hP, hQ⟩
      exact hFora_iff.mpr fun h => hQ (rh_iff_Q.mp h N)
  · rw [hFora_iff, rh_iff_ZL, ← not_nonempty_iff_eq_empty, not_not]

end ATK.ZeroClasses.Hipotetico

#print axioms ATK.ZeroClasses.Hipotetico.hFora_iff_fora
#print axioms ATK.ZeroClasses.Hipotetico.hFora_iff
#print axioms ATK.ZeroClasses.Hipotetico.universo_iff
#print axioms ATK.ZeroClasses.Hipotetico.refutar_universo_iff
#print axioms ATK.ZeroClasses.Hipotetico.orbita_mem
#print axioms ATK.ZeroClasses.Hipotetico.restricoes_locais
#print axioms ATK.ZeroClasses.Hipotetico.finitos_abaixo
#print axioms ATK.ZeroClasses.Hipotetico.falha_nivel_ge_um
#print axioms ATK.ZeroClasses.Hipotetico.quarteto
#print axioms ATK.ZeroClasses.Hipotetico.forma_normal
#print axioms ATK.ZeroClasses.Hipotetico.ramos
#print axioms ATK.ZeroClasses.Hipotetico.piso_DN
#print axioms ATK.ZeroClasses.Hipotetico.falha_toeplitz
#print axioms ATK.ZeroClasses.Hipotetico.falha_ordem_tres
#print axioms ATK.ZeroClasses.Hipotetico.falha_jensen
#print axioms ATK.ZeroClasses.Hipotetico.minimo_nulo
#print axioms ATK.ZeroClasses.Hipotetico.sem_certificado
#print axioms ATK.ZeroClasses.Hipotetico.F_nulo
#print axioms ATK.ZeroClasses.Hipotetico.ramo_racional_refuta
#print axioms ATK.ZeroClasses.Hipotetico.ramo_irracional_refuta
#print axioms ATK.ZeroClasses.Hipotetico.painel
