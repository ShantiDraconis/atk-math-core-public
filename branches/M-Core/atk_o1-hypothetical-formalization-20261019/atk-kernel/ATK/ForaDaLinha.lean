import ATK.ZetaRegiao
import ATK.RiemannStates

/-!
# ATK — Os zeros fora da linha crítica: o anti-produto material de RH

O teorema que **supõe** que existem zeros fora da linha e diz o que eles teriam de satisfazer.
Tudo aqui é incondicional; nada afirma que tais zeros existam ou não existam.

* `ZeroFora`: o tipo das testemunhas (zeros na faixa com `Re ρ ≠ 1/2`);
* `riemann_iff_vazio`, `nao_riemann_iff`: **RH ⟺ o tipo é vazio**; `¬RH ⟺ existe testemunha`
  (anti-produto completo);
* `evita`: um zero fora da linha **evita** a reta crítica, o eixo real, a faixa baixa
  `|Im ρ| < √3/2` e as bordas `Re ρ ≤ c(t)`, `Re ρ ≥ 1 − c(t)` (`ZetaRegiao`);
* `quarteto_fora`: ele vem com mais três (`1 − ρ`, `ρ̄`, `1 − ρ̄`), **quatro zeros fora da linha
  distintos** — o parâmetro de **tensão** (`s ↦ 1 − s`) e de **torção** (`s ↦ 1 − s̄`);
* `piso_DN`: **condensação** — um zero `ρ` com `1/2 < Re ρ < 1` força
  `D_N ≥ m(ρ)²` para **todo** `N`, `m(ρ) = 1/(|ρ|(1/√(2σ−1) + 1/(1−σ)))`, `σ = Re ρ`;
* `finito_de_zero_fora`: logo `D_N` fica no estado `finito` (limite `≥ m(ρ)² > 0`): o zero
  fora da linha se **materializa** como um piso positivo da distância de Báez-Duarte.

Leitura: a família de Báez-Duarte (produto `D_N → 0 ⇒ RH`, já provado) e a contra-família dos zeros
fora da linha (anti-produto) são as duas metades da mesma lacuna O1.
-/

open Complex Set Filter Topology

namespace ATK.ForaDaLinha

open ATK.ZetaSimetria ATK.ZetaRetangulo ATK.ZetaRegiao ATK.BaezDuarteBridge
  ATK.Conditional.Riemann ATK.RiemannStates ATK.IndeterminacyStates ATK.RiemannConcrete

/-- Testemunha que refutaria RH: um zero não trivial fora da reta crítica. -/
def ZeroFora : Type := {ρ : ℂ // ρ ∈ Z ∧ ρ.re ≠ 1 / 2}

/-- **RH ⟺ não há zero fora da linha.** -/
theorem riemann_iff_vazio : RiemannHypothesis ↔ IsEmpty ZeroFora := by
  rw [riemann_iff_torcao]
  constructor
  · intro h
    exact ⟨fun ρ => ρ.2.2 ((torcao_fixo_iff _).mp (h _ ρ.2.1))⟩
  · intro h s hs
    by_contra hne
    exact h.false ⟨s, hs, fun hre => hne ((torcao_fixo_iff s).mpr hre)⟩

/-- **¬RH ⟺ existe zero fora da linha** (o anti-produto é completo). -/
theorem nao_riemann_iff : ¬ RiemannHypothesis ↔ Nonempty ZeroFora := by
  rw [riemann_iff_vazio, not_isEmpty_iff]

/-- Um zero fora da linha **evita**: a reta crítica, o eixo real, a faixa baixa e as duas bordas. -/
theorem evita (ρ : ZeroFora) :
    ρ.1.re ≠ 1 / 2 ∧ ρ.1.im ≠ 0 ∧ 3 / 4 ≤ ρ.1.im ^ 2 ∧
      1 / (256 * A ρ.1.im) < ρ.1.re ∧ ρ.1.re < 1 - 1 / (256 * A ρ.1.im) :=
  ⟨ρ.2.2, im_ne_zero_of_mem_Z ρ.2.1, sem_zeros_ate_altura _ ρ.2.1,
    (faixa_estreitada _ ρ.2.1).1, (faixa_estreitada _ ρ.2.1).2⟩

/-- A tensão de um zero fora da linha é um zero fora da linha. -/
def ZeroFora.tensao (ρ : ZeroFora) : ZeroFora :=
  ⟨ATK.ZetaSimetria.tensao ρ.1, tensao_mem_Z ρ.2.1, by
    rw [re_tensao]; intro h; apply ρ.2.2; linarith⟩

/-- O espelho de um zero fora da linha é um zero fora da linha. -/
noncomputable def ZeroFora.espelho (ρ : ZeroFora) : ZeroFora :=
  ⟨ATK.ZetaSimetria.espelho ρ.1, espelho_mem_Z ρ.2.1, by
    unfold ATK.ZetaSimetria.espelho; simpa using ρ.2.2⟩

/-- A torção de um zero fora da linha é um zero fora da linha. -/
noncomputable def ZeroFora.torcao (ρ : ZeroFora) : ZeroFora :=
  ⟨ATK.ZetaSimetria.torcao ρ.1, torcao_mem_Z ρ.2.1, by
    rw [re_torcao]; intro h; apply ρ.2.2; linarith⟩

/-- **Quarteto**: `ρ, 1 − ρ, ρ̄, 1 − ρ̄` são quatro zeros fora da linha, dois a dois distintos. -/
theorem quarteto_fora (ρ : ZeroFora) :
    ρ.1 ≠ ρ.tensao.1 ∧ ρ.1 ≠ ρ.espelho.1 ∧ ρ.1 ≠ ρ.torcao.1 ∧ ρ.espelho.1 ≠ ρ.tensao.1 ∧
      ρ.espelho.1 ≠ ρ.torcao.1 ∧ ρ.tensao.1 ≠ ρ.torcao.1 := by
  obtain ⟨hesp, hten, _, hoff⟩ := quarteto ρ.2.1
  obtain ⟨htor, h1, h2, h3⟩ := hoff ρ.2.2
  exact ⟨fun h => hten h.symm, fun h => hesp h.symm, fun h => htor h.symm, h1, h2, h3⟩

/-- Sempre existe um representante no lado direito `1/2 < Re ρ < 1`. -/
theorem lado_direito (ρ : ZeroFora) : ∃ σ ∈ Z, 1 / 2 < σ.re := by
  rcases lt_or_gt_of_ne ρ.2.2 with h | h
  · exact ⟨_, tensao_mem_Z ρ.2.1, by rw [re_tensao]; linarith⟩
  · exact ⟨ρ.1, ρ.2.1, h⟩

/-- O parâmetro de condensação `m(ρ)`. -/
noncomputable def m (ρ : ℂ) : ℝ :=
  1 / (‖ρ‖ * (1 / Real.sqrt (2 * ρ.re - 1) + 1 / (1 - ρ.re)))

theorem m_pos {ρ : ℂ} (h0 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) : 0 < m ρ := by
  have hρ : ρ ≠ 0 := by intro h; rw [h, zero_re] at h0; linarith
  have ha : 0 < Real.sqrt (2 * ρ.re - 1) := Real.sqrt_pos.mpr (by linarith)
  have hb : 0 < 1 - ρ.re := by linarith
  unfold m
  have : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  positivity

/-- **Condensação**: um zero com `1/2 < Re ρ < 1` força `residualSq N c ≥ m(ρ)²` para todo `N, c`. -/
theorem piso_residual {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 1 / 2 < ρ.re) (h1 : ρ.re < 1)
    {N : ℕ} (c : Fin N → ℝ) : m ρ ^ 2 ≤ residualSq N c := by
  set R := residualSq N c with hRdef
  set sa := Real.sqrt (2 * ρ.re - 1) with hsa
  set b := 1 - ρ.re with hbdef
  have hρ : ρ ≠ 0 := by intro h; rw [h, zero_re] at h0; linarith
  have hnorm : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have hsa0 : 0 < sa := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < b := by linarith
  have hR0 : 0 ≤ R := MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hm := m_pos h0 h1
  set mm := m ρ with hmm
  have hK : mm * (1 / sa + 1 / b) = 1 / ‖ρ‖ := by
    rw [hmm, m, ← hsa, ← hbdef]; field_simp
  by_contra hlt
  have hlt' : R < mm ^ 2 := not_le.mp hlt
  have hsq : Real.sqrt R < mm := by
    rw [show mm = Real.sqrt (mm ^ 2) from (Real.sqrt_sq hm.le).symm]
    exact Real.sqrt_lt_sqrt hR0 hlt'
  set l := 1 / (mm * sa) with hl
  have hl0 : 0 < l := by positivity
  have hkey := key_ineq c h0 h1 hz hl0
  have ha2 : 2 * ρ.re - 1 = sa ^ 2 := by rw [hsa, Real.sq_sqrt (by linarith)]
  have e1 : l * R < mm / sa := by
    rw [hl, div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by positivity) hsa0]
    nlinarith
  have e2 : 1 / (l * (2 * ρ.re - 1)) = mm / sa := by
    rw [ha2, hl]; field_simp
  have e3 : Real.sqrt R / (1 - ρ.re) < mm / b := by
    rw [← hbdef]; exact div_lt_div_of_pos_right hsq hb0
  have hfinal : (l * R + 1 / (l * (2 * ρ.re - 1))) / 2 + Real.sqrt R / (1 - ρ.re) <
      mm * (1 / sa + 1 / b) := by
    rw [e2]
    have : mm * (1 / sa + 1 / b) = mm / sa + mm / b := by ring
    rw [this]; linarith
  rw [hK] at hfinal
  linarith

/-- **Condensação**: `D_N ≥ m(ρ)²` para todo `N`. -/
theorem piso_DN {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) (N : ℕ) :
    m ρ ^ 2 ≤ DN N :=
  le_ciInf fun c => piso_residual hz h0 h1 c

/-- Todo zero fora da linha condensa: existe `μ > 0` com `D_N ≥ μ` para todo `N`. -/
theorem condensacao (ρ : ZeroFora) : ∃ μ : ℝ, 0 < μ ∧ ∀ N, μ ≤ DN N := by
  obtain ⟨σ, hσ, hre⟩ := lado_direito ρ
  exact ⟨m σ ^ 2, by have := m_pos hre hσ.2.2; positivity, piso_DN hσ.1 hre hσ.2.2⟩

/-- **Materialização**: um zero fora da linha põe `D_N` no estado `finito`. -/
theorem finito_de_zero_fora (ρ : ZeroFora) : Comporta atTop DN Estado7.finito := by
  obtain ⟨μ, hμ, hle⟩ := condensacao ρ
  rw [estado_DN_finito_iff]
  exact lt_of_lt_of_le hμ (le_ciInf hle)

/-- `¬RH ⇒ D_N` no estado `finito` (a direção incondicional; a recíproca é a necessidade de
Báez-Duarte, não formalizada). -/
theorem finito_de_nao_riemann (h : ¬ RiemannHypothesis) : Comporta atTop DN Estado7.finito := by
  obtain ⟨ρ⟩ := nao_riemann_iff.mp h
  exact finito_de_zero_fora ρ

end ATK.ForaDaLinha

#print axioms ATK.ForaDaLinha.riemann_iff_vazio
#print axioms ATK.ForaDaLinha.nao_riemann_iff
#print axioms ATK.ForaDaLinha.evita
#print axioms ATK.ForaDaLinha.quarteto_fora
#print axioms ATK.ForaDaLinha.lado_direito
#print axioms ATK.ForaDaLinha.m_pos
#print axioms ATK.ForaDaLinha.piso_residual
#print axioms ATK.ForaDaLinha.piso_DN
#print axioms ATK.ForaDaLinha.condensacao
#print axioms ATK.ForaDaLinha.finito_de_zero_fora
#print axioms ATK.ForaDaLinha.finito_de_nao_riemann
