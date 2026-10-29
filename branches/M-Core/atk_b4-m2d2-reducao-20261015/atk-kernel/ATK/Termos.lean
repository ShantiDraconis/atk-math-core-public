import ATK.FinalRoot
import ATK.LigacaoNS
import ATK.LigacaoPNP

/-!
# Os termos terminais, um a um, com o tipo exato

Os 21 modelos de portão (`terminal-templates/*.lean.tpl`) têm **25 lacunas distintas**:

* rota da prova — **18** lacunas: 13 provas (`PROVA_DO_PRODUTOR` de RH e de Beal, pontes B3–B7,
  produtores O3–O8) + 5 ligações (`LIGACAO_L2`, `LIGACAO_L2_SAT`, `LIGACAO_L3`, `LIGACAO_L4`,
  `LIGACAO_L5`);
* rota da refutação — **12** lacunas: as 7 `PROVA_DA_REFUTACAO` + as mesmas 5 ligações
  (a refutação fala do mesmo modelo que a prova).

18 + 12 = 30 ocorrências por rota; 30 − 5 ligações compartilhadas = 25 lacunas distintas.

Este módulo dá **um nome Lean a cada uma**, com o tipo exato que o portão exige, e prova, sem
hipóteses e sem `sorry`, o que já se pode provar sobre ela:

* `fecha` — preencher as lacunas da linha dá o enunciado oficial;
* `exato` / `decomposicao` — onde vale, a lacuna é *equivalente* ao enunciado (não é mais forte
  do que o necessário);
* `refutacao_iff` — a forma-testemunha da refutação (o objeto concreto que a refutaria);
* `refutacao_nega_produtor` / `colapso_de_refutacao` — o que uma refutação acarreta.

`scripts/verificar_fiacao.py` troca cada lacuna por `(sorry : <tipo deste catálogo>)` e compila
os 21 modelos: se o tipo daqui divergir do que o portão espera, a compilação falha.
Nenhum teorema aqui prova uma das 7 conjecturas: as lacunas continuam lacunas.
-/

namespace ATK.Termos

/-! ## RH — T01 (prova), T14 (refutação) -/

namespace RH

/-- **T01** · `RH.lean.tpl : PROVA_DO_PRODUTOR` · obrigação O1: não há zero não trivial de ζ
fora da reta crítica. -/
def produtor : Prop := IsEmpty ATK.ForaDaLinha.ZeroFora

/-- **T14** · `RHRefutacao.lean.tpl : PROVA_DA_REFUTACAO`. -/
def refutacao : Prop := ¬ RiemannHypothesis

theorem fecha (h : produtor) : RiemannHypothesis :=
  ATK.ForaDaLinha.riemann_iff_vazio.mpr h

/-- O produtor é exatamente RH: nem mais forte, nem mais fraco. -/
theorem exato : produtor ↔ RiemannHypothesis :=
  ATK.ForaDaLinha.riemann_iff_vazio.symm

/-- Refutar RH é exibir um zero fora da reta (o tipo `ZeroFora` habitado). -/
theorem refutacao_iff_zero_fora : refutacao ↔ Nonempty ATK.ForaDaLinha.ZeroFora :=
  ATK.ForaDaLinha.nao_riemann_iff

/-- Forma-testemunha literal, direto da definição da Mathlib: um zero de ζ que não é trivial,
não é o polo e tem parte real ≠ 1/2. -/
theorem refutacao_iff :
    refutacao ↔ ∃ s : ℂ, riemannZeta s = 0 ∧ (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1 ∧
      s.re ≠ 1 / 2 := by
  unfold refutacao RiemannHypothesis
  simp only [not_forall, exists_prop, ne_eq]

theorem refutacao_nega_produtor (hr : refutacao) : ¬ produtor := fun h => hr (fecha h)

end RH

/-! ## Beal — T02 (prova), T15 (refutação) -/

namespace Beal

open ATK.Conditional.Beal

/-- **T02** · `Beal.lean.tpl : PROVA_DO_PRODUTOR` · obrigação O2: nenhuma solução coprima no
residual que sobra depois das descidas já certificadas. -/
def produtor : Prop := ATK.BealFermatDescent.ExclusaoResidualDescida

/-- **T15** · `BealRefutacao.lean.tpl : PROVA_DA_REFUTACAO`. -/
def refutacao : Prop := ¬ BealConjecture

theorem fecha (h : produtor) : BealConjecture :=
  ATK.BealCompleto.beal_incondicional.mpr h

/-- O produtor é exatamente Beal. -/
theorem exato : produtor ↔ BealConjecture :=
  ATK.BealCompleto.beal_incondicional.symm

/-- Forma-testemunha: um contraexemplo de Beal (nenhum primo divide as três bases). -/
theorem refutacao_iff :
    refutacao ↔ ∃ a b c x y z : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 2 < x ∧ 2 < y ∧ 2 < z ∧
      a ^ x + b ^ y = c ^ z ∧ ∀ p : ℕ, p.Prime → p ∣ a → p ∣ b → ¬ p ∣ c := by
  unfold refutacao BealConjecture
  simp only [not_forall, not_exists, not_and, exists_prop]

/-- "Nenhum primo comum" é o mesmo que `mdc(a, b, c) = 1`. -/
theorem sem_primo_comum_iff (a b c : ℕ) :
    (∀ p : ℕ, p.Prime → p ∣ a → p ∣ b → ¬ p ∣ c) ↔ Nat.gcd a (Nat.gcd b c) = 1 := by
  rw [Nat.eq_one_iff_not_exists_prime_dvd]
  refine forall_congr' fun p => imp_congr_right fun _ => ?_
  rw [Nat.dvd_gcd_iff, Nat.dvd_gcd_iff]
  tauto

/-- Forma-testemunha com mdc: uma solução primitiva `aˣ + bʸ = cᶻ`, `x, y, z ≥ 3`. -/
theorem refutacao_iff_mdc :
    refutacao ↔ ∃ a b c x y z : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 2 < x ∧ 2 < y ∧ 2 < z ∧
      a ^ x + b ^ y = c ^ z ∧ Nat.gcd a (Nat.gcd b c) = 1 := by
  rw [refutacao_iff]
  simp only [sem_primo_comum_iff]

/-- **Espaço de busca reduzido**: um contraexemplo de Beal existe se e só se existe um no
residual da descida (expoentes sem 3 nem 4 no mdc, fora dos três padrões (4,4,2)) com `a`, `b`
coprimos. Quem procura contraexemplo só precisa varrer este residual. -/
theorem refutacao_iff_residual :
    refutacao ↔ ∃ a b c x y z : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 2 < x ∧ 2 < y ∧ 2 < z ∧
      ¬ 3 ∣ Nat.gcd x (Nat.gcd y z) ∧ ¬ 4 ∣ Nat.gcd x (Nat.gcd y z) ∧
      ¬ (4 ∣ x ∧ 4 ∣ y ∧ 2 ∣ z) ∧ ¬ (4 ∣ x ∧ 2 ∣ y ∧ 4 ∣ z) ∧ ¬ (2 ∣ x ∧ 4 ∣ y ∧ 4 ∣ z) ∧
      Nat.Coprime a b ∧ a ^ x + b ^ y = c ^ z := by
  have h : refutacao ↔ ¬ produtor := not_congr exato.symm
  rw [h]
  unfold produtor ATK.BealFermatDescent.ExclusaoResidualDescida
  simp only [not_forall, not_not, exists_prop]

theorem refutacao_nega_produtor (hr : refutacao) : ¬ produtor := fun h => hr (fecha h)

end Beal

/-! ## Navier–Stokes — T03 (ponte B3), T04 (produtor O3), T16 (refutação); ligação L1 construída -/

namespace NS

open ATK.Conditional.NavierStokes

universe u

/-- **T03** · `NS.lean.tpl : PROVA_DA_PONTE_B3` · Leray 1934 + teoria local: sem solução global,
a enstrofia explode num tempo finito. -/
def ponteB3 (M : NSModel.{u}) : Prop := EnstrophyBlowupCriterion M

/-- **T04** · `NS.lean.tpl : PROVA_DO_PRODUTOR_O3` · obrigação O3: cota a priori da enstrofia. -/
def produtorO3 (M : NSModel.{u}) : Prop := EnstrophyAPrioriBound M

/-- **T16** · `NSRefutacao.lean.tpl : PROVA_DA_REFUTACAO`. -/
def refutacao (M : NSModel.{u}) : Prop := ¬ ClayStatementA M

theorem fecha {M : NSModel.{u}} (hb : ponteB3 M) (ho : produtorO3 M) : ClayStatementA M :=
  ns_conditional hb ho

theorem refutacao_nega_produtor {M : NSModel.{u}} (hb : ponteB3 M) (hr : refutacao M) :
    ¬ produtorO3 M := fun ho => hr (fecha hb ho)

/-- Com a ponte B3, uma refutação produz explosão da enstrofia em tempo finito: é o enunciado
(C) do Clay (com força nula). -/
theorem colapso_de_refutacao {M : NSModel.{u}} (hb : ponteB3 M) (hr : refutacao M) :
    ∃ u₀, M.Admissible u₀ ∧ ∃ T : ℝ, 0 < T ∧ M.SmoothOn u₀ T ∧
      ∀ B : ℝ, ∃ t ∈ Set.Ico 0 T, B < M.enstrophy u₀ t := by
  unfold refutacao ClayStatementA at hr
  push Not at hr
  obtain ⟨u₀, hu, hg⟩ := hr
  exact ⟨u₀, hu, hb u₀ hu hg⟩

open ATK.LigacaoNS

/-- No modelo genuíno (L1), preencher T03 e T04 dá o enunciado (A) do Clay, escrito com os
objetos reais (dados de Schwartz em ℝ³, soluções suaves de energia limitada). -/
theorem fecha_oficial (hb : ponteB3 modeloNS) (ho : produtorO3 modeloNS) :
    ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzMap E3 E3, (∀ x, div u₀ x = 0) →
      ∃ U P, SolucaoGlobal ν u₀ U P :=
  clayA_iff.mp (fecha hb ho)

/-- Forma-testemunha da refutação no modelo genuíno: viscosidade `ν > 0` e um campo de Schwartz
de divergência nula sem solução global suave de energia limitada. -/
theorem refutacao_iff :
    refutacao modeloNS ↔ ∃ ν : ℝ, 0 < ν ∧ ∃ u₀ : SchwartzMap E3 E3, (∀ x, div u₀ x = 0) ∧
      ¬ ∃ U P, SolucaoGlobal ν u₀ U P := by
  unfold refutacao
  rw [clayA_iff]
  simp only [not_forall, exists_prop]

end NS

/-! ## P vs NP — T05 (ponte B4), T06 (produtor O4), T17 (refutação); ligação L2 -/

namespace PNP

open ATK.Conditional.PvsNP

universe u

/-- **T05** · `PNP.lean.tpl : PROVA_DA_PONTE_B4` · Cook–Levin: SAT é NP-completo no modelo. -/
def ponteB4 (M : ComplexityModel.{u}) (s : M.Lang) : Prop := CookLevin M s

/-- **T06** · `PNP.lean.tpl : PROVA_DO_PRODUTOR_O4` · obrigação O4: SAT ∉ P. -/
def produtorO4 (M : ComplexityModel.{u}) (s : M.Lang) : Prop := SATNotInP M s

/-- **T17** · `PNPRefutacao.lean.tpl : PROVA_DA_REFUTACAO`. -/
def refutacao (M : ComplexityModel.{u}) : Prop := ¬ PneNP M

theorem fecha {M : ComplexityModel.{u}} {s : M.Lang} (hb : ponteB4 M s) (ho : produtorO4 M s) :
    PneNP M :=
  pvsnp_conditional hb ho

/-- Dada a ponte, o produtor é exatamente P ≠ NP. -/
theorem exato {M : ComplexityModel.{u}} {s : M.Lang} (hb : ponteB4 M s) :
    produtorO4 M s ↔ PneNP M :=
  (pneNP_iff_sat_not_in_P hb).symm

/-- Refutar é P = NP. -/
theorem refutacao_iff (M : ComplexityModel.{u}) : refutacao M ↔ M.P = M.NP := by
  unfold refutacao PneNP
  exact not_not

/-- Dada a ponte, refutar é exibir SAT em P (um algoritmo polinomial para SAT). -/
theorem refutacao_iff_sat {M : ComplexityModel.{u}} {s : M.Lang} (hb : ponteB4 M s) :
    refutacao M ↔ s ∈ M.P := by
  unfold refutacao
  rw [pneNP_iff_sat_not_in_P hb]
  unfold SATNotInP
  exact not_not

/-- **Critério de fidelidade da ligação L2**: as classes do modelo são, a menos de uma
bijeção das linguagens, as classes P e NP sobre `Turing.FinTM2` de `ATK.LigacaoPNP`. -/
def FielL2 (M : ComplexityModel.{0}) : Prop :=
  ∃ e : M.Lang ≃ ATK.LigacaoPNP.Linguagem,
    (∀ L, L ∈ M.P ↔ e L ∈ ATK.LigacaoPNP.classeP) ∧ (∀ L, L ∈ M.NP ↔ e L ∈ ATK.LigacaoPNP.classeNP)

/-- Um modelo fiel no sentido de `FielL2` tem o enunciado oficial: `PneNP M ↔ P ≠ NP` sobre
máquinas de Turing. Fecha o buraco "modelo de brinquedo" de L2: basta provar `FielL2`. -/
theorem pneNP_de_fiel {M : ComplexityModel.{0}} (h : FielL2 M) :
    PneNP M ↔ ATK.LigacaoPNP.PneNP := by
  obtain ⟨e, hP, hNP⟩ := h
  unfold PneNP ATK.LigacaoPNP.PneNP
  apply not_congr
  constructor
  · intro hPNP
    ext L
    have h1 := hP (e.symm L)
    have h2 := hNP (e.symm L)
    rw [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, hPNP]
  · intro hc
    ext L
    rw [hP, hNP, hc]

/-- Um modelo com finitas linguagens nunca é fiel: há infinitas (incontáveis) linguagens binárias.
Em particular o modelo de brinquedo de `ATK.FinalRoot.pnp_depende_do_modelo` (`Lang := Bool`) não
satisfaz `FielL2`. -/
theorem finito_nao_fiel (M : ComplexityModel.{0}) [Finite M.Lang] : ¬ FielL2 M := by
  rintro ⟨e, -, -⟩
  have : Finite ATK.LigacaoPNP.Linguagem := Finite.of_equiv _ e
  have : Finite (List Bool) :=
    Finite.of_injective (fun w => ({w} : Set (List Bool))) Set.singleton_injective
  exact not_finite (List Bool)

end PNP

/-! ## Hodge — T07 (ponte B5), T08 (produtor O5), T18 (refutação); ligação L3 -/

namespace Hodge

open ATK.Conditional.Hodge

universe u v

/-- **T07** · `Hodge.lean.tpl : PROVA_DA_PONTE_B5` · casos conhecidos (p ≤ 1, p ≥ dim X − 1). -/
def ponteB5 (M : HodgeModel.{u, v}) : Prop := KnownCases M

/-- **T08** · `Hodge.lean.tpl : PROVA_DO_PRODUTOR_O5` · obrigação O5: codimensões do meio. -/
def produtorO5 (M : HodgeModel.{u, v}) : Prop := MiddleCodimension M

/-- **T18** · `HodgeRefutacao.lean.tpl : PROVA_DA_REFUTACAO`. -/
def refutacao (M : HodgeModel.{u, v}) : Prop := ¬ HodgeConjecture M

theorem fecha {M : HodgeModel.{u, v}} (hb : ponteB5 M) (ho : produtorO5 M) : HodgeConjecture M :=
  hodge_conditional hb ho

/-- **Decomposição exata**: Hodge = casos conhecidos ∧ codimensão do meio. Nenhuma das duas
lacunas pede mais do que a conjectura. -/
theorem decomposicao (M : HodgeModel.{u, v}) : HodgeConjecture M ↔ ponteB5 M ∧ produtorO5 M := by
  constructor
  · intro h
    exact ⟨fun X hX p α _ hα => h X hX p α hα, fun X hX p α _ _ hα => h X hX p α hα⟩
  · rintro ⟨hb, ho⟩
    exact hodge_conditional hb ho

/-- Forma-testemunha: uma classe de Hodge racional que não é algébrica. -/
theorem refutacao_iff (M : HodgeModel.{u, v}) :
    refutacao M ↔ ∃ X, M.SmoothProjective X ∧ ∃ (p : ℕ) (α : M.Class X p),
      M.IsHodge α ∧ ¬ M.IsAlgebraic α := by
  unfold refutacao HodgeConjecture
  simp only [not_forall, exists_prop]

/-- Com a ponte B5, um contraexemplo está forçosamente na codimensão do meio — em particular
numa variedade de dimensão ≥ 4 (o primeiro caso em aberto é p = 2, dim X = 4). -/
theorem refutacao_meio {M : HodgeModel.{u, v}} (hb : ponteB5 M) (hr : refutacao M) :
    ∃ X, M.SmoothProjective X ∧ 4 ≤ M.dim X ∧ ∃ (p : ℕ) (α : M.Class X p),
      2 ≤ p ∧ p + 2 ≤ M.dim X ∧ M.IsHodge α ∧ ¬ M.IsAlgebraic α := by
  obtain ⟨X, hX, p, α, hα, hna⟩ := (refutacao_iff M).mp hr
  have h1 : ¬ p ≤ 1 := fun h => hna (hb X hX p α (Or.inl h) hα)
  have h2 : ¬ M.dim X ≤ p + 1 := fun h => hna (hb X hX p α (Or.inr h) hα)
  exact ⟨X, hX, by omega, p, α, by omega, by omega, hα, hna⟩

theorem refutacao_nega_produtor {M : HodgeModel.{u, v}} (hb : ponteB5 M) (hr : refutacao M) :
    ¬ produtorO5 M := fun ho => hr (fecha hb ho)

end Hodge

/-! ## BSD — T09 (ponte B6), T10 (O6), T11 (O7), T19 (refutação); ligação L4 -/

namespace BSD

open ATK.Conditional.BSD

universe u

/-- **T09** · `BSD.lean.tpl : PROVA_DA_PONTE_B6` · Gross–Zagier–Kolyvagin (posto analítico ≤ 1). -/
def ponteB6 (M : BSDModel.{u}) : Prop := GrossZagierKolyvagin M

/-- **T10** · `BSD.lean.tpl : PROVA_DO_PRODUTOR_O6` · obrigação O6: posto analítico ≥ 2. -/
def produtorO6 (M : BSDModel.{u}) : Prop := RankOpen M

/-- **T11** · `BSD.lean.tpl : PROVA_DO_PRODUTOR_O7` · obrigação O7: Ш finito e fórmula refinada. -/
def produtorO7 (M : BSDModel.{u}) : Prop := RefinedOpen M

/-- **T19** · `BSDRefutacao.lean.tpl : PROVA_DA_REFUTACAO`. -/
def refutacao (M : BSDModel.{u}) : Prop := ¬ BSDFull M

theorem fecha {M : BSDModel.{u}} (hb : ponteB6 M) (h6 : produtorO6 M) (h7 : produtorO7 M) :
    BSDFull M :=
  bsd_conditional hb h6 h7

/-- **Decomposição exata**: BSD = GZK ∧ posto ≥ 2 ∧ fórmula refinada. -/
theorem decomposicao (M : BSDModel.{u}) :
    BSDFull M ↔ ponteB6 M ∧ produtorO6 M ∧ produtorO7 M := by
  constructor
  · rintro ⟨hr, hf⟩
    exact ⟨fun E _ => (hr E).symm, fun E _ => (hr E).symm, hf⟩
  · rintro ⟨hb, h6, h7⟩
    exact bsd_conditional hb h6 h7

/-- Forma-testemunha: uma curva com postos diferentes, ou uma em que a fórmula refinada falha. -/
theorem refutacao_iff (M : BSDModel.{u}) :
    refutacao M ↔ (∃ E, M.analyticRank E ≠ M.rank E) ∨ ∃ E, ¬ M.RefinedFormula E := by
  unfold refutacao BSDFull BSDRank
  rw [not_and_or]
  simp only [not_forall, ne_eq]

/-- Com a ponte B6, uma curva com postos diferentes tem posto analítico ≥ 2. -/
theorem refutacao_posto {M : BSDModel.{u}} (hb : ponteB6 M) {E : M.Curve}
    (h : M.analyticRank E ≠ M.rank E) : 2 ≤ M.analyticRank E := by
  by_contra h'
  exact h (hb E (by omega)).symm

end BSD

/-! ## Yang–Mills — T12 (ponte B7), T13 (produtor O8), T20 (refutação); ligação L5 -/

namespace YM

open ATK.Conditional.YangMills

universe u v w

/-- **T12** · `YM.lean.tpl : PROVA_DA_PONTE_B7` · reconstrução de Osterwalder–Schrader. -/
def ponteB7 (M : YMModel.{u, v, w}) : Prop := OSReconstruction M

/-- **T13** · `YM.lean.tpl : PROVA_DO_PRODUTOR_O8` · obrigação O8: construção 4D com clustering
exponencial, para todo grupo compacto simples. -/
def produtorO8 (M : YMModel.{u, v, w}) : Prop := ConstructiveYM4D M

/-- **T20** · `YMRefutacao.lean.tpl : PROVA_DA_REFUTACAO`. -/
def refutacao (M : YMModel.{u, v, w}) : Prop := ¬ ClayYM M

theorem fecha {M : YMModel.{u, v, w}} (hb : ponteB7 M) (ho : produtorO8 M) : ClayYM M :=
  ym_conditional hb ho

/-- Forma-testemunha: um grupo compacto simples para o qual nenhuma teoria quântica de
Yang–Mills tem gap positivo. -/
theorem refutacao_iff (M : YMModel.{u, v, w}) :
    refutacao M ↔ ∃ G, M.CompactSimple G ∧
      ∀ T, M.IsQuantumYM G T → ∀ Δ : ℝ, 0 < Δ → ¬ M.GapAtLeast T Δ := by
  unfold refutacao ClayYM
  simp only [not_forall, not_exists, not_and, exists_prop]

theorem refutacao_nega_produtor {M : YMModel.{u, v, w}} (hb : ponteB7 M) (hr : refutacao M) :
    ¬ produtorO8 M := fun ho => hr (fecha hb ho)

end YM

/-! ## Ligações L2–L5 — T21–T25: o tipo exato de cada modelo genuíno -/

namespace Ligacoes

/-- **T21** · `PNPModelo.lean.tpl : LIGACAO_L2` (critério de fidelidade: `PNP.FielL2`). -/
abbrev L2 : Type 1 := ATK.Conditional.PvsNP.ComplexityModel.{0}

/-- **T22** · `PNPModelo.lean.tpl : LIGACAO_L2_SAT` — a linguagem SAT dentro do modelo L2. -/
abbrev L2SAT (M : L2) : Type := M.Lang

/-- **T23** · `HodgeModelo.lean.tpl : LIGACAO_L3`. -/
abbrev L3 : Type 1 := ATK.Conditional.Hodge.HodgeModel.{0, 0}

/-- **T24** · `BSDModelo.lean.tpl : LIGACAO_L4`. -/
abbrev L4 : Type 1 := ATK.Conditional.BSD.BSDModel.{0}

/-- **T25** · `YMModelo.lean.tpl : LIGACAO_L5`. -/
abbrev L5 : Type 1 := ATK.Conditional.YangMills.YMModel.{0, 0, 0}

/-- A ligação L1 já está construída: é `ATK.LigacaoNS.modeloNS`, com fidelidade `clayA_iff`. -/
theorem L1_fiel :
    ATK.Conditional.NavierStokes.ClayStatementA ATK.LigacaoNS.modeloNS ↔
      ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzMap ATK.LigacaoNS.E3 ATK.LigacaoNS.E3,
        (∀ x, ATK.LigacaoNS.div u₀ x = 0) → ∃ U P, ATK.LigacaoNS.SolucaoGlobal ν u₀ U P :=
  ATK.LigacaoNS.clayA_iff

end Ligacoes

/-! ## Fechamento pelos termos -/

/-- **Fechamento pelos termos**: as 13 provas dos portões, sobre os modelos `M` que as ligações
fixam, dão a raiz (os sete enunciados). Sem hipótese escondida: cada argumento é uma lacuna. -/
theorem raiz_de_termos (M : ATK.ClosedMath.Models)
    (t01 : RH.produtor) (t02 : Beal.produtor)
    (t03 : NS.ponteB3 M.ns) (t04 : NS.produtorO3 M.ns)
    (t05 : PNP.ponteB4 M.cx M.sat) (t06 : PNP.produtorO4 M.cx M.sat)
    (t07 : Hodge.ponteB5 M.hodge) (t08 : Hodge.produtorO5 M.hodge)
    (t09 : BSD.ponteB6 M.bsd) (t10 : BSD.produtorO6 M.bsd) (t11 : BSD.produtorO7 M.bsd)
    (t12 : YM.ponteB7 M.ym) (t13 : YM.produtorO8 M.ym) : ATK.FinalRoot.Raiz M :=
  ⟨RH.fecha t01, Beal.fecha t02, NS.fecha t03 t04, PNP.fecha t05 t06, Hodge.fecha t07 t08,
    BSD.fecha t09 t10 t11, YM.fecha t12 t13⟩

/-- Onde as lacunas são exatas, a raiz é *equivalente* a elas: RH, Beal, Hodge e BSD pedem
exatamente as suas lacunas; NS, P vs NP e YM entram pelo enunciado. -/
theorem raiz_iff (M : ATK.ClosedMath.Models) :
    ATK.FinalRoot.Raiz M ↔ RH.produtor ∧ Beal.produtor ∧
      ATK.Conditional.NavierStokes.ClayStatementA M.ns ∧ ATK.Conditional.PvsNP.PneNP M.cx ∧
      (Hodge.ponteB5 M.hodge ∧ Hodge.produtorO5 M.hodge) ∧
      (BSD.ponteB6 M.bsd ∧ BSD.produtorO6 M.bsd ∧ BSD.produtorO7 M.bsd) ∧
      ATK.Conditional.YangMills.ClayYM M.ym := by
  unfold ATK.FinalRoot.Raiz ATK.ClosedMath.SevenStatements
  rw [RH.exato, Beal.exato, Hodge.decomposicao, BSD.decomposicao]

/-- Prova e refutação de uma mesma linha não coexistem (sem base inconsistente). -/
theorem exclusao {P : Prop} (hp : P) (hr : ¬ P) : False := hr hp

end ATK.Termos

#print axioms ATK.Termos.RH.fecha
#print axioms ATK.Termos.RH.exato
#print axioms ATK.Termos.RH.refutacao_iff_zero_fora
#print axioms ATK.Termos.RH.refutacao_iff
#print axioms ATK.Termos.RH.refutacao_nega_produtor
#print axioms ATK.Termos.Beal.fecha
#print axioms ATK.Termos.Beal.exato
#print axioms ATK.Termos.Beal.refutacao_iff
#print axioms ATK.Termos.Beal.sem_primo_comum_iff
#print axioms ATK.Termos.Beal.refutacao_iff_mdc
#print axioms ATK.Termos.Beal.refutacao_iff_residual
#print axioms ATK.Termos.Beal.refutacao_nega_produtor
#print axioms ATK.Termos.NS.fecha
#print axioms ATK.Termos.NS.refutacao_nega_produtor
#print axioms ATK.Termos.NS.colapso_de_refutacao
#print axioms ATK.Termos.NS.fecha_oficial
#print axioms ATK.Termos.NS.refutacao_iff
#print axioms ATK.Termos.PNP.fecha
#print axioms ATK.Termos.PNP.exato
#print axioms ATK.Termos.PNP.refutacao_iff
#print axioms ATK.Termos.PNP.refutacao_iff_sat
#print axioms ATK.Termos.PNP.pneNP_de_fiel
#print axioms ATK.Termos.PNP.finito_nao_fiel
#print axioms ATK.Termos.Hodge.fecha
#print axioms ATK.Termos.Hodge.decomposicao
#print axioms ATK.Termos.Hodge.refutacao_iff
#print axioms ATK.Termos.Hodge.refutacao_meio
#print axioms ATK.Termos.Hodge.refutacao_nega_produtor
#print axioms ATK.Termos.BSD.fecha
#print axioms ATK.Termos.BSD.decomposicao
#print axioms ATK.Termos.BSD.refutacao_iff
#print axioms ATK.Termos.BSD.refutacao_posto
#print axioms ATK.Termos.YM.fecha
#print axioms ATK.Termos.YM.refutacao_iff
#print axioms ATK.Termos.YM.refutacao_nega_produtor
#print axioms ATK.Termos.Ligacoes.L1_fiel
#print axioms ATK.Termos.raiz_de_termos
#print axioms ATK.Termos.raiz_iff
#print axioms ATK.Termos.exclusao
