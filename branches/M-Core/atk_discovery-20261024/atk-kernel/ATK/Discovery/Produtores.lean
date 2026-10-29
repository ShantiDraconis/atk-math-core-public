import ATK.ATKIBagchi
import ATK.ATKIAplicacoes
import ATK.Discovery.Contracao
import ATK.Discovery.LeisInfinitesimais

/-!
# ATK-Discovery — Produtores de RH sobre o defeito genuíno

`D N = Defeito wTexto gTexto N` é o defeito da família do texto ATK-I, que é a família de Bagchi
(`ATK.ATKIBagchi`). Ele **não** é um parâmetro: `D 0 = 1` (`D_zero`), então o modelo vácuo
`D ≡ 0` está excluído (`vacuo_excluido`).

Cinco produtores, todos enunciados (`Prop`), nenhum afirmado:

| Produtor | Enunciado | Liga a RH por |
|---|---|---|
| `ProdutorPrecisoes` | `∀ m, ∃ N, D N < 10⁻ᵐ` | `⟺ D∞ = 0` (`dInf_zero_iff_precisoes`) |
| `ProdutorCotaLog` | `∃ K, ∀ N, D N ≤ K / log(N + 2)` | confronto (`precisoes_de_cotaLog`) |
| `ProdutorContracao` | `D_{n+1} ≤ (1 − αₙ)D_n`, `αₙ ≤ 1`, `Σαₙ = ∞` | `D_N ≤ D_0 e^{−Σα}` (`precisoes_de_contracao`) |
| `ProdutorGanho` | `D_n − D_{n+1} ≥ D_n/(n + 2)` para `n ≥ 2` | contração com `α = 1/(k + 4)` (`contracao_de_ganho`) |
| `ProdutorInfinitesimal` | `D_H` infinitesimal em `H = [n ↦ n]` (`0 < mk (ofSeq D)`) | `⟺ precisões` (`infinitesimal_iff_precisoes`) |

* Cada produtor implica `RiemannHypothesis` da Mathlib (`rh_de_*`), pela ponte de Bagchi já provada.
* Sem RH, **todo** produtor é falso (`sem_rh_*`): eles não são vácuos, são tão difíceis quanto RH.
* Habitantes (`HabitanteCotaLog`, `HabitanteContracao`) empacotam os dados e as provas; um
  habitante dá RH, e sem RH os tipos são vazios (`habitante_*_vazio`).

Nenhum produtor é provado aqui: `D∞ = 0` continua aberto.
-/

namespace ATK.Discovery.Produtores

open Filter Topology Finset ArchimedeanClass Hyperreal
open ATK.ATKI (Defeito wTexto gTexto wTexto_nonneg defeito_nonneg defeito_antitone
  defeito_limite_zero_iff)
open ATK.ATKIBagchi (rh_of_texto texto_pos_of_not_rh)

/-- O defeito genuíno (família do texto = família de Bagchi). -/
noncomputable abbrev D : ℕ → ℝ := Defeito wTexto gTexto

theorem D_nonneg (N : ℕ) : 0 ≤ D N := defeito_nonneg wTexto_nonneg N

theorem D_antitone : Antitone D := defeito_antitone wTexto_nonneg

/-- `D 0 = 1`: sem geradores, a distância de `1` a `0`. -/
theorem D_zero : D 0 = 1 := ATK.ATKIAplicacoes.defeito_texto_zero

/-- O objeto não é o modelo vácuo: `D ≠ 0`. -/
theorem vacuo_excluido : D ≠ fun _ => 0 := by
  intro h
  have := congrFun h 0
  rw [D_zero] at this
  exact one_ne_zero this

/-! ## Os produtores -/

/-- Todas as precisões decimais. -/
def ProdutorPrecisoes : Prop := ∀ m : ℕ, ∃ N, D N < ((1 : ℝ) / 10) ^ m

/-- Cota logarítmica uniforme. -/
def ProdutorCotaLog : Prop := ∃ K : ℝ, ∀ N : ℕ, D N ≤ K / Real.log ((N : ℝ) + 2)

/-- Contração acumulada. -/
def ProdutorContracao : Prop :=
  ∃ α : ℕ → ℝ, (∀ n, α n ≤ 1) ∧ (∀ n, D (n + 1) ≤ (1 - α n) * D n) ∧
    Tendsto (fun N => ∑ n ∈ range N, α n) atTop atTop

/-- Ganho quantitativo `g_n = D_n − D_{n+1} ≥ D_n/(n + 2)` a partir de `n = 2`. -/
def ProdutorGanho : Prop := ∀ n : ℕ, 2 ≤ n → D n / ((n : ℝ) + 2) ≤ D n - D (n + 1)

/-- `D_H` infinitesimal na posição hiperinteira `H = [n ↦ n]`. -/
def ProdutorInfinitesimal : Prop := 0 < mk (ofSeq D)

/-! ## Equivalências e reduções -/

/-- `D∞ = 0 ⟺ ∀ m, ∃ N, D N < 10⁻ᵐ`. -/
theorem dInf_zero_iff_precisoes : (⨅ N, D N) = 0 ↔ ProdutorPrecisoes := by
  rw [defeito_limite_zero_iff wTexto_nonneg]
  constructor
  · intro h m
    exact h _ (by positivity)
  · intro h e he
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one he (by norm_num : ((1 : ℝ) / 10) < 1)
    obtain ⟨N, hN⟩ := h m
    exact ⟨N, hN.trans hm⟩

theorem tende_zero_iff_precisoes : Tendsto D atTop (𝓝 0) ↔ ProdutorPrecisoes :=
  ATK.Discovery.Contracao.tende_zero_iff_precisoes D_antitone D_nonneg

theorem rh_de_precisoes (h : ProdutorPrecisoes) : RiemannHypothesis :=
  rh_of_texto (dInf_zero_iff_precisoes.mpr h)

/-- Cota logarítmica ⟹ precisões (confronto com `K/log(N + 2) → 0`). -/
theorem precisoes_de_cotaLog (h : ProdutorCotaLog) : ProdutorPrecisoes := by
  obtain ⟨K, hK⟩ := h
  apply tende_zero_iff_precisoes.mp
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hq : Tendsto (fun N : ℕ => K / Real.log ((N : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hq D_nonneg hK

theorem rh_de_cotaLog (h : ProdutorCotaLog) : RiemannHypothesis :=
  rh_de_precisoes (precisoes_de_cotaLog h)

/-- Contração acumulada ⟹ precisões. -/
theorem precisoes_de_contracao (h : ProdutorContracao) : ProdutorPrecisoes := by
  obtain ⟨α, hα1, hrec, hdiv⟩ := h
  exact tende_zero_iff_precisoes.mp
    (ATK.Discovery.Contracao.tende_zero_de_contracao D_nonneg hα1 hrec hdiv)

theorem rh_de_contracao (h : ProdutorContracao) : RiemannHypothesis :=
  rh_de_precisoes (precisoes_de_contracao h)

/-- `Σ_{k<N} 1/(k + 4) → ∞` (compara com `¼ Σ 1/(k + 1)`). -/
theorem diverge_quarto : Tendsto (fun N => ∑ k ∈ range N, 1 / ((k : ℝ) + 4)) atTop atTop := by
  have hH := (Real.tendsto_sum_range_one_div_nat_succ_atTop).const_mul_atTop
    (by norm_num : (0 : ℝ) < 1 / 4)
  refine tendsto_atTop_mono (fun N => ?_) hH
  rw [mul_sum]
  refine sum_le_sum fun k _ => ?_
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  rw [show (1 : ℝ) / 4 * (1 / ((k : ℝ) + 1)) = 1 / (4 * ((k : ℝ) + 1)) by field_simp]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- Ganho `≥ D_n/(n + 2)` (n ≥ 2) ⟹ a cauda `D_{k+2}` contrai com `α = 1/(k + 4)` e vai a `0`. -/
theorem tende_zero_de_ganho (h : ProdutorGanho) : Tendsto D atTop (𝓝 0) := by
  set E : ℕ → ℝ := fun k => D (k + 2)
  have hE : Tendsto E atTop (𝓝 0) := by
    refine ATK.Discovery.Contracao.tende_zero_de_contracao (α := fun k => 1 / ((k : ℝ) + 4))
      (fun k => D_nonneg (k + 2)) (fun k => ?_) (fun k => ?_) diverge_quarto
    · rw [div_le_one (by positivity)]
      linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
    · have hg := h (k + 2) (by omega)
      have hc : ((k + 2 : ℕ) : ℝ) + 2 = (k : ℝ) + 4 := by push_cast; ring
      rw [hc] at hg
      show D (k + 2 + 1) ≤ (1 - 1 / ((k : ℝ) + 4)) * D (k + 2)
      have : (1 - 1 / ((k : ℝ) + 4)) * D (k + 2) = D (k + 2) - D (k + 2) / ((k : ℝ) + 4) := by
        ring
      rw [this]
      linarith
  exact (tendsto_add_atTop_iff_nat 2).mp hE

theorem precisoes_de_ganho (h : ProdutorGanho) : ProdutorPrecisoes :=
  tende_zero_iff_precisoes.mp (tende_zero_de_ganho h)

theorem rh_de_ganho (h : ProdutorGanho) : RiemannHypothesis :=
  rh_de_precisoes (precisoes_de_ganho h)

/-- `D_H` infinitesimal ⟺ todas as precisões. -/
theorem infinitesimal_iff_precisoes : ProdutorInfinitesimal ↔ ProdutorPrecisoes := by
  constructor
  · intro h m
    have hlt : ofSeq D < ((((1 : ℝ) / 10) ^ m : ℝ) : ℝ*) :=
      lt_of_pos_of_archimedean Hyperreal.coeRingHom h (by positivity)
    have hc : ((((1 : ℝ) / 10) ^ m : ℝ) : ℝ*) = ofSeq fun _ => ((1 : ℝ) / 10) ^ m := rfl
    rw [hc, ofSeq_lt_ofSeq] at hlt
    exact hlt.exists
  · intro h
    exact ATK.Discovery.Leis.mk_pos_ofSeq (tende_zero_iff_precisoes.mpr h)

theorem rh_de_infinitesimal (h : ProdutorInfinitesimal) : RiemannHypothesis :=
  rh_de_precisoes (infinitesimal_iff_precisoes.mp h)

/-! ## Sem RH, nenhum produtor vale -/

theorem sem_rh_precisoes (h : ¬ RiemannHypothesis) : ¬ ProdutorPrecisoes :=
  fun hp => h (rh_de_precisoes hp)

theorem sem_rh_cotaLog (h : ¬ RiemannHypothesis) : ¬ ProdutorCotaLog :=
  fun hp => h (rh_de_cotaLog hp)

theorem sem_rh_contracao (h : ¬ RiemannHypothesis) : ¬ ProdutorContracao :=
  fun hp => h (rh_de_contracao hp)

theorem sem_rh_ganho (h : ¬ RiemannHypothesis) : ¬ ProdutorGanho :=
  fun hp => h (rh_de_ganho hp)

theorem sem_rh_infinitesimal (h : ¬ RiemannHypothesis) : ¬ ProdutorInfinitesimal :=
  fun hp => h (rh_de_infinitesimal hp)

/-- Sem RH, `D∞ > 0`: o defeito genuíno fica longe de zero (`ATK.ATKIBagchi`). -/
theorem sem_rh_defeito_positivo (h : ¬ RiemannHypothesis) : 0 < ⨅ N, D N :=
  texto_pos_of_not_rh h

/-! ## Habitantes dos produtores -/

/-- Habitante da cota logarítmica: a constante e a prova da cota. -/
structure HabitanteCotaLog where
  K : ℝ
  cota : ∀ N : ℕ, D N ≤ K / Real.log ((N : ℝ) + 2)

/-- Habitante da contração: a sequência de taxas e as provas. -/
structure HabitanteContracao where
  α : ℕ → ℝ
  le_one : ∀ n, α n ≤ 1
  contrai : ∀ n, D (n + 1) ≤ (1 - α n) * D n
  diverge : Tendsto (fun N => ∑ n ∈ range N, α n) atTop atTop

theorem HabitanteCotaLog.rh (h : HabitanteCotaLog) : RiemannHypothesis :=
  rh_de_cotaLog ⟨h.K, h.cota⟩

theorem HabitanteContracao.rh (h : HabitanteContracao) : RiemannHypothesis :=
  rh_de_contracao ⟨h.α, h.le_one, h.contrai, h.diverge⟩

theorem habitante_cotaLog_iff : Nonempty HabitanteCotaLog ↔ ProdutorCotaLog :=
  ⟨fun ⟨h⟩ => ⟨h.K, h.cota⟩, fun ⟨K, hK⟩ => ⟨⟨K, hK⟩⟩⟩

theorem habitante_contracao_iff : Nonempty HabitanteContracao ↔ ProdutorContracao :=
  ⟨fun ⟨h⟩ => ⟨h.α, h.le_one, h.contrai, h.diverge⟩,
    fun ⟨α, h1, h2, h3⟩ => ⟨⟨α, h1, h2, h3⟩⟩⟩

/-- Sem RH, não há habitante da cota logarítmica. -/
theorem habitante_cotaLog_vazio (h : ¬ RiemannHypothesis) : IsEmpty HabitanteCotaLog :=
  ⟨fun x => h x.rh⟩

/-- Sem RH, não há habitante da contração. -/
theorem habitante_contracao_vazio (h : ¬ RiemannHypothesis) : IsEmpty HabitanteContracao :=
  ⟨fun x => h x.rh⟩

/-! ## Por que o objeto genuíno importa -/

/-- Para uma sequência qualquer (um parâmetro), o produtor de precisões é trivial em `D' ≡ 0`. -/
theorem produtor_generico_vacuo : ∀ m : ℕ, ∃ N : ℕ, (fun _ : ℕ => (0 : ℝ)) N < ((1 : ℝ) / 10) ^ m :=
  fun m => ⟨0, by positivity⟩

end ATK.Discovery.Produtores

#print axioms ATK.Discovery.Produtores.D_nonneg
#print axioms ATK.Discovery.Produtores.D_antitone
#print axioms ATK.Discovery.Produtores.D_zero
#print axioms ATK.Discovery.Produtores.vacuo_excluido
#print axioms ATK.Discovery.Produtores.dInf_zero_iff_precisoes
#print axioms ATK.Discovery.Produtores.tende_zero_iff_precisoes
#print axioms ATK.Discovery.Produtores.rh_de_precisoes
#print axioms ATK.Discovery.Produtores.precisoes_de_cotaLog
#print axioms ATK.Discovery.Produtores.rh_de_cotaLog
#print axioms ATK.Discovery.Produtores.precisoes_de_contracao
#print axioms ATK.Discovery.Produtores.rh_de_contracao
#print axioms ATK.Discovery.Produtores.diverge_quarto
#print axioms ATK.Discovery.Produtores.tende_zero_de_ganho
#print axioms ATK.Discovery.Produtores.precisoes_de_ganho
#print axioms ATK.Discovery.Produtores.rh_de_ganho
#print axioms ATK.Discovery.Produtores.infinitesimal_iff_precisoes
#print axioms ATK.Discovery.Produtores.rh_de_infinitesimal
#print axioms ATK.Discovery.Produtores.sem_rh_precisoes
#print axioms ATK.Discovery.Produtores.sem_rh_cotaLog
#print axioms ATK.Discovery.Produtores.sem_rh_contracao
#print axioms ATK.Discovery.Produtores.sem_rh_ganho
#print axioms ATK.Discovery.Produtores.sem_rh_infinitesimal
#print axioms ATK.Discovery.Produtores.sem_rh_defeito_positivo
#print axioms ATK.Discovery.Produtores.HabitanteCotaLog.rh
#print axioms ATK.Discovery.Produtores.HabitanteContracao.rh
#print axioms ATK.Discovery.Produtores.habitante_cotaLog_iff
#print axioms ATK.Discovery.Produtores.habitante_contracao_iff
#print axioms ATK.Discovery.Produtores.habitante_cotaLog_vazio
#print axioms ATK.Discovery.Produtores.habitante_contracao_vazio
#print axioms ATK.Discovery.Produtores.produtor_generico_vacuo
