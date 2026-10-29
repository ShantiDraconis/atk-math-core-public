import ATK.Indeterminacy
import ATK.Conditional.Riemann
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# ATK — Estrutura de estados das indeterminações (7 estados, ordem de informação, leis de composição)

Extensão de `ATK.Indeterminacy` seguindo a proposta: `I = 0/0` é apenas **uma face** de uma
estrutura maior de estados. Um quociente `f/g` é classificado pelo comportamento no limite:

| estado | significado |
|---|---|
| `zero` | limite 0 |
| `finito` | limite finito não nulo |
| `maisInf` | diverge para +∞ |
| `menosInf` | diverge para −∞ |
| `oscila` | nenhum dos anteriores (sem limite em ℝ ∪ {±∞}) |
| `indeterminado` | informação insuficiente (não afirma nada) |
| `foraDominio` | expressão fora do domínio (nenhuma função real o realiza) |

Resultados verificados pelo kernel:

* **classificação**: os 5 comportamentos são exaustivos (`classificacao_exaustiva`) e mutuamente
  exclusivos (`classificacao_exclusiva`) em qualquer filtro não trivial;
* **ordem de informação**: `indeterminado` abaixo de tudo; ordem parcial (`refina_*`); menos informação
  é consequência de mais (`comporta_de_refina`);
* **leis de composição**: tabelas `mulTab` e `divTab` com **correção** provada
  (`mulTab_correta`, `divTab_correta`): o estado da tabela vale para *qualquer* par de funções nos estados
  de entrada; e **monotonia** na ordem de informação (`mulTab_mono`, `divTab_mono`);
* **otimalidade**: para `0/0` não existe estado determinado correto — as 5 faces ocorrem
  (`zero_div_zero_cinco_faces`), logo `indeterminado` é forçado (`zero_div_zero_sem_estado_correto`);
* **ponte com os pontos de 3 estados**: o germe `a·tᵐ` está no estado `ponto7 p` (`comporta_germe`);
* **derivação**: a derivada de um ponto é um ponto, com ordem `m − 1` (`germe_hasDerivAt`); o quociente
  das derivadas tem a mesma ordem relativa — L'Hôpital preserva o estado (`lhopital_preserva_estado`);
* **dissipação**: `D_{n+1} ≤ D_n − δ_n`, `D ≥ 0`, `Σ δ = D_0` ⇒ `D_n → 0` (`dissipacao_total`); e, com
  `δ_n = D_n − D_{n+1}`, dissipação total **equivale** a `D_n → 0` (`dissipacao_iff_limite_zero`) —
  é uma reformulação da obrigação, não uma estimativa nova;
* **a obrigação O1 na linguagem de estados**: `D_N` no estado `zero` + ponte de Báez-Duarte ⇒ RH
  (`riemann_de_estado_zero`). Que `D_N` esteja no estado `zero` **é** a obrigação aberta: a tabela
  não a decide, porque `D_N` não é dado como composição de estados conhecidos.
-/

open Filter Topology Set

namespace ATK.IndeterminacyStates

open ATK.Indeterminacy

/-- Os 7 estados. -/
inductive Estado7
  | zero
  | finito
  | maisInf
  | menosInf
  | oscila
  | indeterminado
  | foraDominio
  deriving DecidableEq, Repr

open Estado7

instance : Fintype Estado7 :=
  Fintype.ofList [zero, finito, maisInf, menosInf, oscila, indeterminado, foraDominio]
    (fun x => by cases x <;> simp)

/-- Semântica: o que cada estado afirma sobre `f` ao longo do filtro `l`. -/
def Comporta {α : Type*} (l : Filter α) (f : α → ℝ) : Estado7 → Prop
  | zero => Tendsto f l (𝓝 0)
  | finito => ∃ L : ℝ, L ≠ 0 ∧ Tendsto f l (𝓝 L)
  | maisInf => Tendsto f l atTop
  | menosInf => Tendsto f l atBot
  | oscila => (¬ ∃ L, Tendsto f l (𝓝 L)) ∧ ¬ Tendsto f l atTop ∧ ¬ Tendsto f l atBot
  | indeterminado => True
  | foraDominio => False

/-- Os 5 estados de comportamento (os outros dois são estados de informação). -/
def eComportamento : Estado7 → Bool
  | indeterminado => false
  | foraDominio => false
  | _ => true

/-! ## Classificação -/

/-- **Exaustiva**: toda função está em algum dos 5 comportamentos. -/
theorem classificacao_exaustiva {α : Type*} (l : Filter α) (f : α → ℝ) :
    ∃ s, eComportamento s = true ∧ Comporta l f s := by
  by_cases h : ∃ L, Tendsto f l (𝓝 L)
  · obtain ⟨L, hL⟩ := h
    by_cases h0 : L = 0
    · subst h0; exact ⟨zero, rfl, hL⟩
    · exact ⟨finito, rfl, L, h0, hL⟩
  · by_cases ht : Tendsto f l atTop
    · exact ⟨maisInf, rfl, ht⟩
    · by_cases hb : Tendsto f l atBot
      · exact ⟨menosInf, rfl, hb⟩
      · exact ⟨oscila, rfl, h, ht, hb⟩

section Exclusiva

variable {α : Type*} {l : Filter α} [NeBot l] {f : α → ℝ}

theorem nao_zero_finito (h1 : Comporta l f zero) (h2 : Comporta l f finito) : False := by
  obtain ⟨L, hL0, hL⟩ := h2
  exact hL0 (tendsto_nhds_unique hL h1)

theorem nao_lim_maisInf {L : ℝ} (h1 : Tendsto f l (𝓝 L)) (h2 : Tendsto f l atTop) : False :=
  h1.not_tendsto (disjoint_nhds_atTop L) h2

theorem nao_lim_menosInf {L : ℝ} (h1 : Tendsto f l (𝓝 L)) (h2 : Tendsto f l atBot) : False :=
  h1.not_tendsto (disjoint_nhds_atBot L) h2

theorem nao_maisInf_menosInf (h1 : Tendsto f l atTop) (h2 : Tendsto f l atBot) : False :=
  h1.not_tendsto Filter.disjoint_atTop_atBot h2

/-- **Exclusiva**: em filtro não trivial, uma função está em no máximo um comportamento. -/
theorem classificacao_exclusiva {s r : Estado7} (hs : eComportamento s = true)
    (hr : eComportamento r = true) (h1 : Comporta l f s) (h2 : Comporta l f r) : s = r := by
  cases s <;> cases r <;> (try simp [eComportamento] at hs) <;> (try simp [eComportamento] at hr) <;>
    simp only [Comporta] at h1 h2 <;> first
    | rfl
    | exact (nao_zero_finito h1 h2).elim
    | exact (nao_zero_finito h2 h1).elim
    | exact (nao_lim_maisInf h1 h2).elim
    | exact (nao_lim_maisInf h2 h1).elim
    | exact (nao_lim_menosInf h1 h2).elim
    | exact (nao_lim_menosInf h2 h1).elim
    | exact (nao_maisInf_menosInf h1 h2).elim
    | exact (nao_maisInf_menosInf h2 h1).elim
    | exact (h2.1 ⟨0, h1⟩).elim
    | exact (h1.1 ⟨0, h2⟩).elim
    | exact (h2.2.1 h1).elim
    | exact (h1.2.1 h2).elim
    | exact (h2.2.2 h1).elim
    | exact (h1.2.2 h2).elim
    | (obtain ⟨L, -, hL⟩ := h1; first
        | exact (nao_lim_maisInf hL h2).elim
        | exact (nao_lim_menosInf hL h2).elim
        | exact (h2.1 ⟨L, hL⟩).elim)
    | (obtain ⟨L, -, hL⟩ := h2; first
        | exact (nao_lim_maisInf hL h1).elim
        | exact (nao_lim_menosInf hL h1).elim
        | exact (h1.1 ⟨L, hL⟩).elim)

end Exclusiva

/-- Comportamento respeita igualdade eventual. -/
theorem comporta_congr {α : Type*} {l : Filter α} {f g : α → ℝ} (h : f =ᶠ[l] g) {s : Estado7}
    (hf : Comporta l f s) : Comporta l g s := by
  cases s
  · exact Tendsto.congr' h hf
  · obtain ⟨L, hL0, hL⟩ := hf; exact ⟨L, hL0, hL.congr' h⟩
  · exact Tendsto.congr' h hf
  · exact Tendsto.congr' h hf
  · obtain ⟨h1, h2, h3⟩ := hf
    exact ⟨fun ⟨L, hL⟩ => h1 ⟨L, hL.congr' h.symm⟩, fun ht => h2 (ht.congr' h.symm),
      fun hb => h3 (hb.congr' h.symm)⟩
  · trivial
  · exact hf

/-! ## Ordem de informação -/

/-- `refina s r`: `r` tem pelo menos a informação de `s`. -/
def refina : Estado7 → Estado7 → Bool
  | indeterminado, _ => true
  | s, r => decide (s = r)

theorem refina_refl : ∀ s, refina s s = true := by decide
theorem refina_antisymm : ∀ s r, refina s r = true → refina r s = true → s = r := by decide
theorem refina_trans : ∀ s r u, refina s r = true → refina r u = true → refina s u = true := by
  decide
theorem indeterminado_minimo : ∀ s, refina indeterminado s = true := by decide

/-- Menos informação é consequência de mais. -/
theorem comporta_de_refina {α : Type*} {l : Filter α} {f : α → ℝ} {s r : Estado7}
    (hsr : refina s r = true) (h : Comporta l f r) : Comporta l f s := by
  cases s <;> cases r <;> simp [refina] at hsr <;> first | exact h | trivial

/-! ## Leis de composição -/

/-- Tabela do produto. -/
def mulTab : Estado7 → Estado7 → Estado7
  | foraDominio, _ => foraDominio
  | _, foraDominio => foraDominio
  | zero, zero => zero
  | zero, finito => zero
  | finito, zero => zero
  | finito, finito => finito
  | maisInf, maisInf => maisInf
  | menosInf, menosInf => maisInf
  | maisInf, menosInf => menosInf
  | menosInf, maisInf => menosInf
  | _, _ => indeterminado

/-- Tabela do quociente. -/
def divTab : Estado7 → Estado7 → Estado7
  | foraDominio, _ => foraDominio
  | _, foraDominio => foraDominio
  | zero, finito => zero
  | finito, finito => finito
  | zero, maisInf => zero
  | zero, menosInf => zero
  | finito, maisInf => zero
  | finito, menosInf => zero
  | _, _ => indeterminado

/-- `0·∞`, `0/0`, `∞/∞` são `indeterminado` na tabela. -/
theorem formas_indeterminadas :
    mulTab zero maisInf = indeterminado ∧ divTab zero zero = indeterminado ∧
      divTab maisInf maisInf = indeterminado := ⟨rfl, rfl, rfl⟩

/-- **Correção do produto**: o estado da tabela vale para qualquer par de funções. -/
theorem mulTab_correta {α : Type*} {l : Filter α} {f g : α → ℝ} {s r : Estado7}
    (hf : Comporta l f s) (hg : Comporta l g r) :
    Comporta l (fun x => f x * g x) (mulTab s r) := by
  cases s <;> cases r <;> simp only [mulTab, Comporta] at hf hg ⊢ <;> first
    | trivial
    | exact hf.elim
    | exact hg.elim
    | simpa using hf.mul hg
    | (obtain ⟨L, hL0, hL⟩ := hg; simpa using hf.mul hL)
    | (obtain ⟨L, hL0, hL⟩ := hf; simpa using hL.mul hg)
    | (obtain ⟨L, hL0, hL⟩ := hf; obtain ⟨M, hM0, hM⟩ := hg
       exact ⟨L * M, mul_ne_zero hL0 hM0, hL.mul hM⟩)
    | exact hf.atTop_mul_atTop₀ hg
    | exact hf.atBot_mul_atBot₀ hg
    | exact hf.atTop_mul_atBot₀ hg
    | exact hf.atBot_mul_atTop₀ hg

/-- **Correção do quociente.** -/
theorem divTab_correta {α : Type*} {l : Filter α} {f g : α → ℝ} {s r : Estado7}
    (hf : Comporta l f s) (hg : Comporta l g r) :
    Comporta l (fun x => f x / g x) (divTab s r) := by
  cases s <;> cases r <;> simp only [divTab, Comporta] at hf hg ⊢ <;> first
    | trivial
    | exact hf.elim
    | exact hg.elim
    | (obtain ⟨M, hM0, hM⟩ := hg; have h := hf.div hM hM0; rw [zero_div] at h; exact h)
    | (obtain ⟨L, hL0, hL⟩ := hf; obtain ⟨M, hM0, hM⟩ := hg
       exact ⟨L / M, div_ne_zero hL0 hM0, hL.div hM hM0⟩)
    | exact hf.div_atTop hg
    | exact hf.div_atBot hg
    | (obtain ⟨L, hL0, hL⟩ := hf; exact hL.div_atTop hg)
    | (obtain ⟨L, hL0, hL⟩ := hf; exact hL.div_atBot hg)

/-- **Monotonia**: mais informação na entrada nunca dá menos informação na saída. -/
theorem mulTab_mono : ∀ s s' r r', refina s s' = true → refina r r' = true →
    refina (mulTab s r) (mulTab s' r') = true := by decide

theorem divTab_mono : ∀ s s' r r', refina s s' = true → refina r r' = true →
    refina (divTab s r) (divTab s' r') = true := by decide

/-! ## Ponte com os pontos de 3 estados -/

/-- Estado de 7 de um ponto `a·tᵐ` (o sinal de `a` separa `+∞` de `−∞`). -/
noncomputable def ponto7 (p : Ponto) : Estado7 :=
  if 0 < p.m then zero else if p.m = 0 then finito else if 0 < p.a then maisInf else menosInf

theorem comporta_germe (p : Ponto) : Comporta (𝓝[>] (0 : ℝ)) p.germe (ponto7 p) := by
  unfold ponto7
  split_ifs with h1 h2 h3
  · exact Ponto.estado_zero_tendsto p h1
  · refine ⟨p.a, p.a_ne, tendsto_const_nhds.congr' ?_⟩
    filter_upwards with t
    simp [Ponto.germe, h2]
  · exact Ponto.estado_infinito_tendsto p (by omega) h3
  · have ha : 0 < -p.a := by
      have := p.a_ne
      rcases lt_or_gt_of_ne this with h | h
      · linarith
      · exact absurd h h3
    let q : Ponto := ⟨-p.a, p.m, neg_ne_zero.mpr p.a_ne⟩
    have hq := Ponto.estado_infinito_tendsto q (by show p.m < 0; omega) ha
    have : p.germe = fun t => -(q.germe t) := by
      funext t; simp [Ponto.germe, q]
    show Tendsto p.germe _ atBot
    rw [this]
    exact tendsto_neg_atTop_atBot.comp hq

/-- Quociente de germes, como função. -/
theorem comporta_div_germes (p q : Ponto) :
    Comporta (𝓝[>] (0 : ℝ)) (fun t => p.germe t / q.germe t) (ponto7 (p.div q)) := by
  refine comporta_congr ?_ (comporta_germe (p.div q))
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact Ponto.germe_div p q (ne_of_gt ht)

/-! ## Otimalidade: as 5 faces de `0/0` -/

/-- Sinal alternante `(-1)^⌊1/t⌋`, que oscila quando `t → 0⁺`. -/
noncomputable def sinalAlt (t : ℝ) : ℝ := (-1) ^ ⌊t⁻¹⌋₊

theorem sinalAlt_inv_nat (k : ℕ) : sinalAlt ((k : ℝ)⁻¹) = (-1) ^ k := by
  simp [sinalAlt, inv_inv, Nat.floor_natCast]

theorem seq_tendsto (a : ℕ) :
    Tendsto (fun n : ℕ => (((2 * n + a + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
  · have h : Tendsto (fun n : ℕ => 2 * n + a + 1) atTop atTop :=
      tendsto_atTop_mono (fun n => show n ≤ 2 * n + a + 1 by omega) tendsto_id
    exact tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp h)
  · show (0 : ℝ) < _
    positivity

theorem sinalAlt_par (n : ℕ) : sinalAlt (((2 * n + 1 + 1 : ℕ) : ℝ))⁻¹ = 1 := by
  rw [sinalAlt_inv_nat]; exact Even.neg_one_pow ⟨n + 1, by ring⟩

theorem sinalAlt_impar (n : ℕ) : sinalAlt (((2 * n + 2 + 1 : ℕ) : ℝ))⁻¹ = -1 := by
  rw [sinalAlt_inv_nat]; exact Odd.neg_one_pow ⟨n + 1, by ring⟩

/-- `sinalAlt` está no estado `oscila` quando `t → 0⁺`. -/
theorem sinalAlt_oscila : Comporta (𝓝[>] (0 : ℝ)) sinalAlt oscila := by
  have hp : Tendsto (fun n : ℕ => sinalAlt (((2 * n + 1 + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 1) := by
    simp only [sinalAlt_par]; exact tendsto_const_nhds
  have hi : Tendsto (fun n : ℕ => sinalAlt (((2 * n + 2 + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 (-1)) := by
    simp only [sinalAlt_impar]; exact tendsto_const_nhds
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨L, hL⟩
    have h1 := tendsto_nhds_unique (hL.comp (seq_tendsto 1)) hp
    have h2 := tendsto_nhds_unique (hL.comp (seq_tendsto 2)) hi
    linarith
  · intro ht
    exact nao_lim_maisInf hp (ht.comp (seq_tendsto 1))
  · intro hb
    exact nao_lim_menosInf hp (hb.comp (seq_tendsto 1))

/-- **As 5 faces de `0/0`**: para cada comportamento existe um par `f, g → 0` cujo quociente o realiza. -/
theorem zero_div_zero_cinco_faces (s : Estado7) (hs : eComportamento s = true) :
    ∃ f g : ℝ → ℝ, Comporta (𝓝[>] (0 : ℝ)) f zero ∧ Comporta (𝓝[>] (0 : ℝ)) g zero ∧
      Comporta (𝓝[>] (0 : ℝ)) (fun t => f t / g t) s := by
  have face : ∀ p q : Ponto, 0 < p.m → 0 < q.m →
      ∃ f g : ℝ → ℝ, Comporta (𝓝[>] (0 : ℝ)) f zero ∧ Comporta (𝓝[>] (0 : ℝ)) g zero ∧
        Comporta (𝓝[>] (0 : ℝ)) (fun t => f t / g t) (ponto7 (p.div q)) := fun p q hp hq =>
    ⟨p.germe, q.germe, Ponto.estado_zero_tendsto p hp, Ponto.estado_zero_tendsto q hq,
      comporta_div_germes p q⟩
  cases s
  · have := face ⟨1, 2, one_ne_zero⟩ ⟨1, 1, one_ne_zero⟩ (by norm_num) (by norm_num)
    simpa [ponto7, Ponto.div] using this
  · have := face ⟨1, 1, one_ne_zero⟩ ⟨1, 1, one_ne_zero⟩ (by norm_num) (by norm_num)
    simpa [ponto7, Ponto.div] using this
  · have := face ⟨1, 1, one_ne_zero⟩ ⟨1, 2, one_ne_zero⟩ (by norm_num) (by norm_num)
    simpa [ponto7, Ponto.div] using this
  · have := face ⟨-1, 1, by norm_num⟩ ⟨1, 2, one_ne_zero⟩ (by norm_num) (by norm_num)
    norm_num [ponto7, Ponto.div] at this ⊢; exact this
  · refine ⟨fun t => t * sinalAlt t, fun t => t, ?_, ?_, ?_⟩
    · show Tendsto _ _ _
      refine squeeze_zero_norm (a := fun t => ‖t‖) (fun t => ?_)
        (tendsto_norm_zero.mono_left nhdsWithin_le_nhds)
      simp [sinalAlt, norm_mul, norm_pow]
    · exact tendsto_id.mono_left nhdsWithin_le_nhds
    · refine comporta_congr ?_ sinalAlt_oscila
      filter_upwards [self_mem_nhdsWithin] with t ht
      field_simp [ne_of_gt (show (0 : ℝ) < t from ht)]
  · simp [eComportamento] at hs
  · simp [eComportamento] at hs

/-- **Otimalidade**: nenhum estado de comportamento é correto para todo `0/0`; `indeterminado` é forçado. -/
theorem zero_div_zero_sem_estado_correto :
    ¬ ∃ s, eComportamento s = true ∧ ∀ f g : ℝ → ℝ,
      Comporta (𝓝[>] (0 : ℝ)) f zero → Comporta (𝓝[>] (0 : ℝ)) g zero →
        Comporta (𝓝[>] (0 : ℝ)) (fun t => f t / g t) s := by
  rintro ⟨s, hs, hall⟩
  -- escolhe uma face diferente de s
  have key : ∀ r, eComportamento r = true → r ≠ s → False := fun r hr hrs => by
    obtain ⟨f, g, hf, hg, hq⟩ := zero_div_zero_cinco_faces r hr
    exact hrs (classificacao_exclusiva hr hs hq (hall f g hf hg))
  by_cases h : s = zero
  · exact key finito rfl (by rw [h]; decide)
  · exact key zero rfl (Ne.symm h)

/-! ## A obrigação O1 na linguagem de estados -/

open ATK.Conditional.Riemann in
/-- `D_N` no estado `zero` + ponte de Báez-Duarte ⇒ RH. O antecedente é a obrigação O1. -/
theorem riemann_de_estado_zero (hB : BaezDuarteCriterion) (h : Comporta atTop DN zero) :
    RiemannHypothesis :=
  hB h

open ATK.Conditional.Riemann in
/-- O majorante logarítmico coloca `D_N` no estado `zero`. -/
theorem estado_zero_de_majorante (h : UniformLogBound) : Comporta atTop DN zero :=
  DN_tendsto_zero h

open ATK.Conditional.Riemann in
/-- Sem informação, a estrutura só garante `indeterminado` para `D_N` (que vale para qualquer função). -/
theorem DN_indeterminado : Comporta atTop DN indeterminado := trivial

/-! ## Derivação de pontos -/

/-- Derivada de um ponto de ordem não nula: `(a·tᵐ)' = (a·m)·t^(m−1)`. -/
noncomputable def derivPonto (p : Ponto) (hm : p.m ≠ 0) : Ponto :=
  ⟨p.a * p.m, p.m - 1, mul_ne_zero p.a_ne (Int.cast_ne_zero.mpr hm)⟩

/-- **Lei de derivação**: o germe é derivável fora de 0 e a derivada é o germe do ponto derivado. -/
theorem germe_hasDerivAt (p : Ponto) (hm : p.m ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt p.germe ((derivPonto p hm).germe t) t := by
  have h := (hasDerivAt_zpow p.m t (Or.inl ht)).const_mul p.a
  have hg : p.germe = fun y => p.a * y ^ p.m := rfl
  rw [hg]
  convert h using 1
  simp only [derivPonto, Ponto.germe]
  ring

/-- **L'Hôpital preserva o estado**: o quociente das derivadas tem a mesma ordem relativa. -/
theorem lhopital_preserva_estado (p q : Ponto) (hp : p.m ≠ 0) (hq : q.m ≠ 0) :
    ((derivPonto p hp).div (derivPonto q hq)).m = (p.div q).m ∧
      ((derivPonto p hp).div (derivPonto q hq)).estado = (p.div q).estado := by
  have : ((derivPonto p hp).div (derivPonto q hq)).m = (p.div q).m := by
    simp only [derivPonto, Ponto.div]; ring
  exact ⟨this, by simp only [Ponto.estado, this]⟩

/-! ## Operador de dissipação -/

/-- **Anulação por dissipação total**: `D_{n+1} ≤ D_n − δ_n`, `D ≥ 0`, `Σ δ = D_0` ⇒ `D_n → 0`.
(O sinal de `δ` nem é necessário.) -/
theorem dissipacao_total {D δ : ℕ → ℝ} (h0 : ∀ n, 0 ≤ D n) (hstep : ∀ n, D (n + 1) ≤ D n - δ n)
    (hsum : HasSum δ (D 0)) : Tendsto D atTop (𝓝 0) := by
  have hle : ∀ M, D M ≤ D 0 - ∑ n ∈ Finset.range M, δ n := by
    intro M
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ]; linarith [hstep M]
  have hup : Tendsto (fun M => D 0 - ∑ n ∈ Finset.range M, δ n) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := D 0)).sub hsum.tendsto_sum_nat
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup h0 hle

/-- **Dissipação total ⟺ limite zero** (para `D` decrescente, com `δ_n = D_n − D_{n+1}`): a rota da
dissipação é uma reformulação da obrigação `D_n → 0`, não uma estimativa nova. -/
theorem dissipacao_iff_limite_zero {D : ℕ → ℝ} (hanti : Antitone D) :
    HasSum (fun n => D n - D (n + 1)) (D 0) ↔ Tendsto D atTop (𝓝 0) := by
  have hnn : ∀ n, 0 ≤ D n - D (n + 1) := fun n => sub_nonneg.mpr (hanti (Nat.le_succ n))
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  simp_rw [Finset.sum_range_sub']
  constructor
  · intro h
    have := (tendsto_const_nhds (x := D 0)).sub h
    simpa using this
  · intro h
    have := (tendsto_const_nhds (x := D 0)).sub h
    simpa using this

open ATK.Conditional.Riemann in
/-- Rota da dissipação até RH: ponte de Báez-Duarte + dissipação total de `D_N` ⇒ RH. -/
theorem riemann_de_dissipacao (hB : BaezDuarteCriterion) {δ : ℕ → ℝ}
    (hstep : ∀ n, DN (n + 1) ≤ DN n - δ n) (hsum : HasSum δ (DN 0)) : RiemannHypothesis :=
  hB (dissipacao_total DN_nonneg hstep hsum)

end ATK.IndeterminacyStates

#print axioms ATK.IndeterminacyStates.classificacao_exaustiva
#print axioms ATK.IndeterminacyStates.nao_zero_finito
#print axioms ATK.IndeterminacyStates.nao_lim_maisInf
#print axioms ATK.IndeterminacyStates.nao_lim_menosInf
#print axioms ATK.IndeterminacyStates.nao_maisInf_menosInf
#print axioms ATK.IndeterminacyStates.classificacao_exclusiva
#print axioms ATK.IndeterminacyStates.comporta_congr
#print axioms ATK.IndeterminacyStates.refina_refl
#print axioms ATK.IndeterminacyStates.refina_antisymm
#print axioms ATK.IndeterminacyStates.refina_trans
#print axioms ATK.IndeterminacyStates.indeterminado_minimo
#print axioms ATK.IndeterminacyStates.comporta_de_refina
#print axioms ATK.IndeterminacyStates.formas_indeterminadas
#print axioms ATK.IndeterminacyStates.mulTab_correta
#print axioms ATK.IndeterminacyStates.divTab_correta
#print axioms ATK.IndeterminacyStates.mulTab_mono
#print axioms ATK.IndeterminacyStates.divTab_mono
#print axioms ATK.IndeterminacyStates.comporta_germe
#print axioms ATK.IndeterminacyStates.comporta_div_germes
#print axioms ATK.IndeterminacyStates.sinalAlt_inv_nat
#print axioms ATK.IndeterminacyStates.seq_tendsto
#print axioms ATK.IndeterminacyStates.sinalAlt_par
#print axioms ATK.IndeterminacyStates.sinalAlt_impar
#print axioms ATK.IndeterminacyStates.sinalAlt_oscila
#print axioms ATK.IndeterminacyStates.zero_div_zero_cinco_faces
#print axioms ATK.IndeterminacyStates.zero_div_zero_sem_estado_correto
#print axioms ATK.IndeterminacyStates.riemann_de_estado_zero
#print axioms ATK.IndeterminacyStates.estado_zero_de_majorante
#print axioms ATK.IndeterminacyStates.DN_indeterminado
#print axioms ATK.IndeterminacyStates.germe_hasDerivAt
#print axioms ATK.IndeterminacyStates.lhopital_preserva_estado
#print axioms ATK.IndeterminacyStates.dissipacao_total
#print axioms ATK.IndeterminacyStates.dissipacao_iff_limite_zero
#print axioms ATK.IndeterminacyStates.riemann_de_dissipacao
