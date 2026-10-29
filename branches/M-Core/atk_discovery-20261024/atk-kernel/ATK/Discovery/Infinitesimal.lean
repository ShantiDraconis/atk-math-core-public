import ATK.TerceiroTemplo

/-!
# ATK-Discovery — A unidade com um dígito na posição infinita

Nos hiper-reais `ℝ*`, com `H = [n ↦ n]` hiperinteiro infinito e `ε_H = 10⁻ᴴ`
(`ATK.TerceiroTemplo.dezMenosH`, já provado `> 0` com parte padrão `0`):

* `0 < ε_H < 10⁻ⁿ` para **todo** `n` natural, e `ε_H < r` para todo real `r > 0`
  (`eps_lt_dez_pot`, `eps_lt_real`);
* `𝟏⁻ = 1 − ε_H < 1 < 𝟏⁺ = 1 + ε_H` (`umMenos_lt_um`, `um_lt_umMais`), e **os três têm parte padrão `1`**
  (`stdPart_umMais`, `stdPart_umMenos`): mesma parte padrão, ordem estrita (`mesma_parte_padrao`);
* classe observacional do zero: `0 < ε_H < 2ε_H`, todos com parte padrão `0` (`classe_do_zero`);
* **a cauda não decide a parte padrão**: `ε_H` e `1/4 + ε_H` têm a mesma cauda infinitesimal e partes
  padrão `0` e `1/4` (`cauda_nao_decide`);
* em `ℝ` não existe esse dígito: nenhum real positivo fica abaixo de todo `10⁻ⁿ`
  (`real_sem_infinitesimal`), e a desigualdade estrita `1 − 10⁻ᴺ < 1` de cada etapa **não** passa ao
  limite (`estrita_nao_passa_ao_limite`);
* em qualquer corpo ordenado: `1 − ε < 1 < 1 + ε` e `(1 + ε) − 1 = ε` para `ε > 0` (`unidade_estendida`).

O que isto **não** faz: atribuir a uma quantidade genuína (um `D_N`, um combustível natural) um valor
infinitesimal. Isso exigiria prová-lo sobre o objeto original.
-/

namespace ATK.Discovery.Infinitesimal

open Filter Topology ArchimedeanClass
open ATK.TerceiroTemplo (dezMenosH dezMenosH_infinitesimal dez_pot_pos dez_pot_tende_zero)

/-- `ε_H = 10⁻ᴴ` tende a `0` como germe. -/
theorem eps_tendsto : dezMenosH.Tendsto (𝓝 0) := by
  rw [dezMenosH, Hyperreal.tendsto_ofSeq]
  exact dez_pot_tende_zero.mono_left
    (Filter.hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le)

/-- A classe arquimediana de `ε_H` é positiva: `ε_H` é infinitesimal. -/
theorem mk_eps_pos : 0 < mk dezMenosH := Hyperreal.archimedeanClassMk_pos_of_tendsto eps_tendsto

theorem eps_pos : 0 < dezMenosH := dezMenosH_infinitesimal.1

theorem stdPart_eps : stdPart dezMenosH = 0 := dezMenosH_infinitesimal.2

/-- `ε_H` está abaixo de todo real positivo. -/
theorem eps_lt_real {r : ℝ} (hr : 0 < r) : dezMenosH < (r : ℝ*) :=
  lt_of_pos_of_archimedean Hyperreal.coeRingHom mk_eps_pos hr

/-- `0 < ε_H < 10⁻ⁿ` para todo `n` natural: o dígito está além de toda posição finita. -/
theorem eps_lt_dez_pot (n : ℕ) : 0 < dezMenosH ∧ dezMenosH < ((((1 : ℝ) / 10) ^ n : ℝ) : ℝ*) :=
  ⟨eps_pos, eps_lt_real (dez_pot_pos n)⟩

/-- `𝟏⁺ = 1 + 10⁻ᴴ`. -/
noncomputable def umMais : ℝ* := 1 + dezMenosH

/-- `𝟏⁻ = 1 − 10⁻ᴴ`. -/
noncomputable def umMenos : ℝ* := 1 - dezMenosH

theorem um_lt_umMais : (1 : ℝ*) < umMais := by
  unfold umMais; linarith [eps_pos]

theorem umMenos_lt_um : umMenos < 1 := by
  unfold umMenos; linarith [eps_pos]

theorem stdPart_umMais : stdPart umMais = 1 := by
  unfold umMais
  rw [stdPart_add_eq_left mk_eps_pos, stdPart_one]

theorem stdPart_umMenos : stdPart umMenos = 1 := by
  unfold umMenos
  rw [stdPart_sub_eq_left mk_eps_pos, stdPart_one]

/-- Mesma parte padrão, ordem estrita: `𝟏⁻ < 1 < 𝟏⁺` e os três têm parte padrão `1`. -/
theorem mesma_parte_padrao :
    umMenos < 1 ∧ (1 : ℝ*) < umMais ∧
      stdPart umMenos = 1 ∧ stdPart (1 : ℝ*) = 1 ∧ stdPart umMais = 1 :=
  ⟨umMenos_lt_um, um_lt_umMais, stdPart_umMenos, stdPart_one, stdPart_umMais⟩

/-- A classe observacional do zero: `0 < ε_H < 2ε_H`, todos com parte padrão `0`. -/
theorem classe_do_zero :
    (0 : ℝ*) < dezMenosH ∧ dezMenosH < 2 * dezMenosH ∧
      stdPart (0 : ℝ*) = 0 ∧ stdPart dezMenosH = 0 ∧ stdPart (2 * dezMenosH) = 0 := by
  refine ⟨eps_pos, by linarith [eps_pos], ?_, stdPart_eps, ?_⟩
  · simp
  · rw [stdPart_eq_zero, mk_mul, mk_ofNat, zero_add]
    exact mk_eps_pos.ne'

/-- **A cauda não decide a parte padrão**: `ε_H` e `1/4 + ε_H` têm a mesma cauda e partes padrão
`0` e `1/4`. -/
theorem cauda_nao_decide :
    stdPart dezMenosH = 0 ∧ stdPart (((1 / 4 : ℝ) : ℝ*) + dezMenosH) = 1 / 4 := by
  refine ⟨stdPart_eps, ?_⟩
  rw [stdPart_add_eq_left mk_eps_pos, Hyperreal.stdPart_coe]

/-- Em `ℝ` não existe o dígito na posição infinita: nenhum real positivo fica abaixo de todo `10⁻ⁿ`. -/
theorem real_sem_infinitesimal : ¬ ∃ x : ℝ, 0 < x ∧ ∀ n : ℕ, x < ((1 : ℝ) / 10) ^ n := by
  rintro ⟨x, hx, h⟩
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hx (by norm_num : ((1 : ℝ) / 10) < 1)
  exact lt_asymm hn (h n)

/-- A desigualdade estrita de cada etapa não passa ao limite: `1 − 10⁻ᴺ < 1` para todo `N`, e o
limite é `1`, que não é `< 1`. -/
theorem estrita_nao_passa_ao_limite :
    (∀ N : ℕ, 1 - ((1 : ℝ) / 10) ^ N < 1) ∧
      Tendsto (fun N : ℕ => 1 - ((1 : ℝ) / 10) ^ N) atTop (𝓝 1) ∧ ¬ ((1 : ℝ) < 1) := by
  refine ⟨fun N => by linarith [dez_pot_pos N], ?_, lt_irrefl 1⟩
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub dez_pot_tende_zero
  simpa using this

section Corpo

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Em qualquer corpo ordenado, `1 − ε < 1 < 1 + ε` e `(1 + ε) − 1 = ε` para `ε > 0`. -/
theorem unidade_estendida {ε : K} (hε : 0 < ε) :
    1 - ε < 1 ∧ (1 : K) < 1 + ε ∧ 1 + ε ≠ 1 ∧ (1 + ε) - 1 = ε := by
  refine ⟨by linarith, by linarith, by intro h; linarith, by ring⟩

end Corpo

end ATK.Discovery.Infinitesimal

#print axioms ATK.Discovery.Infinitesimal.eps_tendsto
#print axioms ATK.Discovery.Infinitesimal.mk_eps_pos
#print axioms ATK.Discovery.Infinitesimal.eps_lt_real
#print axioms ATK.Discovery.Infinitesimal.eps_lt_dez_pot
#print axioms ATK.Discovery.Infinitesimal.um_lt_umMais
#print axioms ATK.Discovery.Infinitesimal.umMenos_lt_um
#print axioms ATK.Discovery.Infinitesimal.stdPart_umMais
#print axioms ATK.Discovery.Infinitesimal.stdPart_umMenos
#print axioms ATK.Discovery.Infinitesimal.mesma_parte_padrao
#print axioms ATK.Discovery.Infinitesimal.classe_do_zero
#print axioms ATK.Discovery.Infinitesimal.cauda_nao_decide
#print axioms ATK.Discovery.Infinitesimal.real_sem_infinitesimal
#print axioms ATK.Discovery.Infinitesimal.estrita_nao_passa_ao_limite
#print axioms ATK.Discovery.Infinitesimal.unidade_estendida
