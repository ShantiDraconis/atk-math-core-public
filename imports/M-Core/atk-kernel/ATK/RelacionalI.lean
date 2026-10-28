/-
ATK-I — Álgebra Relacional de Defeitos, Transições e Invariantes.

Estrutura 𝔍(K) = (K², ⊕, ⊗, d, ≽, T, 𝒯) sobre um corpo normado K:

* uma relação `R(a,b)` é o par `(a, b)` — a expressão "a = b" guardada como objeto;
* `⊕`, `⊗` : operações componente a componente;
* `d(R) = ‖a − b‖` : defeito da igualdade;
* `R ≽ S` : `d R ≤ d S` (R está pelo menos tão perto da verdade quanto S);
* `𝒯` : relações verdadeiras (`a = b`), isto é, a diagonal;
* transformações `T : K² → K²`, com as classes
  `𝒫` (preservam a equivalência: `T R ∈ 𝒯 ⟺ R ∈ 𝒯`) e `𝒞` (contraem defeitos: `d(T R) ≤ d R`).

Nível I (fundamentos): `d R = 0 ⟺ R ∈ 𝒯`; desigualdades de defeito para ⊕, ⊗ e somas finitas;
fechamento simultâneo de famílias finitas (`∀ i, R_i ∈ 𝒯 ⟺ Σ d(R_i) = 0`); ⊕ não reflete a verdade.

Nível II (transformações): Teorema ATK-I de preservação e fechamento; a escala `T_k` (k ≠ 0) está em
𝒫 com `d(T_k R) = ‖k‖ d(R)`; o colapso está em 𝒞 mas não em 𝒫; uma escala com ‖k‖ > 1 está em 𝒫
mas não em 𝒞 — **as classes 𝒫 e 𝒞 são independentes**.

**Aproximação ≠ igualdade** (`aproximacao_nao_certifica`): existe T ∈ 𝒫 ∩ 𝒞_q, q < 1, e R falsa
com `d(Tⁿ R) → 0` e `Tⁿ R` falsa para todo n.  O que o defeito → 0 certifica é a relação-limite
(`limite_certifica`), nunca os termos da sequência.

**Transporte de certificados** (`Morfismo`, `transporte_certificados`): um homomorfismo de corpos
isométrico f : K → L transporta, sem perda de semântica, verdade, defeitos, certificados ε,
as classes 𝒫, 𝒞, 𝒞_q de transformações entrelaçadas e certificados por limite, de L para K.
Instâncias: ℚ → ℝ e ℝ → ℂ.

Honestidade: os objetos básicos (pares, operações componente a componente, `‖a − b‖`) já existem
na literatura com outros nomes; o que este arquivo fixa é a semântica exata e os teoremas acima,
verificados pelo kernel.  Nada aqui diz algo sobre os sete problemas.
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Rat
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Separation.Hausdorff

namespace ATK.RelacionalI

open Filter Topology

section Basico

variable {K : Type*} [NormedField K]

/-- Uma relação `R(a, b)`. -/
abbrev Relacao (K : Type*) := K × K

/-- `𝒯`: a relação é verdadeira. -/
def Verdadeira (R : Relacao K) : Prop := R.1 = R.2

/-- Defeito `d(R) = ‖a − b‖`. -/
noncomputable def d (R : Relacao K) : ℝ := ‖R.1 - R.2‖

/-- `⊕`. -/
def oplus (R S : Relacao K) : Relacao K := (R.1 + S.1, R.2 + S.2)

/-- `⊗`. -/
def otimes (R S : Relacao K) : Relacao K := (R.1 * S.1, R.2 * S.2)

/-- `R ≽ S`. -/
def Prox (R S : Relacao K) : Prop := d R ≤ d S

/-! ### Nível I -/

theorem d_nonneg (R : Relacao K) : 0 ≤ d R := norm_nonneg _

/-- **Semântica exata**: defeito zero ⟺ verdade. -/
theorem d_eq_zero_iff (R : Relacao K) : d R = 0 ↔ Verdadeira R := by
  unfold d Verdadeira
  rw [norm_eq_zero, sub_eq_zero]

theorem d_pos_iff (R : Relacao K) : 0 < d R ↔ ¬ Verdadeira R := by
  rw [← d_eq_zero_iff]
  exact ⟨fun h h0 => by linarith, fun h => lt_of_le_of_ne (d_nonneg R) (Ne.symm h)⟩

theorem d_swap (R : Relacao K) : d R.swap = d R := by
  unfold d
  exact norm_sub_rev _ _

theorem d_trans (a b c : K) : d (a, c) ≤ d (a, b) + d (b, c) := by
  unfold d
  exact norm_sub_le_norm_sub_add_norm_sub a b c

theorem d_oplus_le (R S : Relacao K) : d (oplus R S) ≤ d R + d S := by
  unfold d oplus
  have e : R.1 + S.1 - (R.2 + S.2) = (R.1 - R.2) + (S.1 - S.2) := by ring
  rw [e]
  exact norm_add_le _ _

theorem d_otimes_le (R S : Relacao K) : d (otimes R S) ≤ ‖R.1‖ * d S + ‖S.2‖ * d R := by
  unfold d otimes
  have e : R.1 * S.1 - R.2 * S.2 = R.1 * (S.1 - S.2) + S.2 * (R.1 - R.2) := by ring
  rw [e]
  calc ‖R.1 * (S.1 - S.2) + S.2 * (R.1 - R.2)‖
      ≤ ‖R.1 * (S.1 - S.2)‖ + ‖S.2 * (R.1 - R.2)‖ := norm_add_le _ _
    _ = ‖R.1‖ * ‖S.1 - S.2‖ + ‖S.2‖ * ‖R.1 - R.2‖ := by rw [norm_mul, norm_mul]

/-- Defeito de uma soma finita de relações. -/
theorem d_sum_le {ι : Type*} (s : Finset ι) (R : ι → Relacao K) :
    d (∑ i ∈ s, R i) ≤ ∑ i ∈ s, d (R i) := by
  unfold d
  rw [Prod.fst_sum, Prod.snd_sum, ← Finset.sum_sub_distrib]
  exact norm_sum_le _ _

theorem verdadeira_refl (a : K) : Verdadeira (a, a) := rfl

theorem verdadeira_oplus {R S : Relacao K} (hR : Verdadeira R) (hS : Verdadeira S) :
    Verdadeira (oplus R S) := by
  unfold Verdadeira oplus at *
  rw [hR, hS]

theorem verdadeira_otimes {R S : Relacao K} (hR : Verdadeira R) (hS : Verdadeira S) :
    Verdadeira (otimes R S) := by
  unfold Verdadeira otimes at *
  rw [hR, hS]

/-- `⊕` não reflete a verdade: `(1,0) ⊕ (0,1) = (1,1)`. -/
theorem oplus_nao_reflete :
    ∃ R S : Relacao K, Verdadeira (oplus R S) ∧ ¬ Verdadeira R ∧ ¬ Verdadeira S :=
  ⟨(1, 0), (0, 1), by simp [Verdadeira, oplus], by simp [Verdadeira], by simp [Verdadeira]⟩

/-- **Fechamento simultâneo** de uma família finita: todas verdadeiras ⟺ soma dos defeitos = 0. -/
theorem familia_verdadeira_iff {ι : Type*} (s : Finset ι) (R : ι → Relacao K) :
    (∀ i ∈ s, Verdadeira (R i)) ↔ ∑ i ∈ s, d (R i) = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => d_nonneg (R i))]
  simp only [d_eq_zero_iff]

/-- Uma única relação falsa basta para a família não fechar. -/
theorem familia_falha {ι : Type*} (s : Finset ι) (R : ι → Relacao K) {i : ι} (hi : i ∈ s)
    (hf : ¬ Verdadeira (R i)) : 0 < ∑ i ∈ s, d (R i) := by
  have h0 : 0 ≤ ∑ i ∈ s, d (R i) := Finset.sum_nonneg fun i _ => d_nonneg (R i)
  refine lt_of_le_of_ne h0 fun h => hf ?_
  exact (familia_verdadeira_iff s R).mpr h.symm i hi

/-! ### Proximidade -/

theorem prox_refl (R : Relacao K) : Prox R R := le_refl _

theorem prox_trans {R S U : Relacao K} (h1 : Prox R S) (h2 : Prox S U) : Prox R U := le_trans h1 h2

theorem prox_total (R S : Relacao K) : Prox R S ∨ Prox S R := le_total _ _

/-- As relações verdadeiras são as mais próximas. -/
theorem verdadeira_maxima {R : Relacao K} (hR : Verdadeira R) (S : Relacao K) : Prox R S := by
  unfold Prox
  rw [(d_eq_zero_iff R).mpr hR]
  exact d_nonneg S

theorem verdadeira_de_prox {R S : Relacao K} (h : Prox R S) (hS : Verdadeira S) : Verdadeira R := by
  rw [← d_eq_zero_iff]
  have := (d_eq_zero_iff S).mpr hS
  exact le_antisymm (by unfold Prox at h; linarith) (d_nonneg R)

/-! ### Nível II — transformações -/

/-- `𝒫`: preservam a equivalência. -/
def PreservaEquiv (T : Relacao K → Relacao K) : Prop := ∀ R, Verdadeira (T R) ↔ Verdadeira R

/-- `𝒞`: contraem defeitos. -/
def Contrai (T : Relacao K → Relacao K) : Prop := ∀ R, d (T R) ≤ d R

/-- `𝒞_q`: contraem defeitos com fator q. -/
def ContraiQ (q : ℝ) (T : Relacao K → Relacao K) : Prop := ∀ R, d (T R) ≤ q * d R

/-- **Teorema ATK-I (preservação e fechamento)**: T ∈ 𝒫 e d(T R) = 0 ⇒ d(R) = 0. -/
theorem preservacao_e_fechamento {T : Relacao K → Relacao K} (hT : PreservaEquiv T) {R : Relacao K}
    (h : d (T R) = 0) : d R = 0 :=
  (d_eq_zero_iff R).mpr ((hT R).mp ((d_eq_zero_iff (T R)).mp h))

theorem preservaEquiv_id : PreservaEquiv (id : Relacao K → Relacao K) := fun _ => Iff.rfl

theorem preservaEquiv_comp {T U : Relacao K → Relacao K} (hT : PreservaEquiv T) (hU : PreservaEquiv U) :
    PreservaEquiv (T ∘ U) := fun R => (hT (U R)).trans (hU R)

theorem contrai_id : Contrai (id : Relacao K → Relacao K) := fun _ => le_refl _

theorem contrai_comp {T U : Relacao K → Relacao K} (hT : Contrai T) (hU : Contrai U) :
    Contrai (T ∘ U) := fun R => (hT (U R)).trans (hU R)

theorem contraiQ_iter {q : ℝ} (hq : 0 ≤ q) {T : Relacao K → Relacao K} (hT : ContraiQ q T) (R : Relacao K)
    (n : ℕ) : d (T^[n] R) ≤ q ^ n * d R := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    calc d (T (T^[n] R)) ≤ q * d (T^[n] R) := hT _
      _ ≤ q * (q ^ n * d R) := mul_le_mul_of_nonneg_left ih hq
      _ = q ^ n * q * d R := by ring

/-- Órbitas de T ∈ 𝒫 têm o valor de verdade do ponto inicial. -/
theorem orbita_iff {T : Relacao K → Relacao K} (hT : PreservaEquiv T) (R : Relacao K) (n : ℕ) :
    Verdadeira (T^[n] R) ↔ Verdadeira R := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (hT _).trans ih

/-- Escala `T_k(a, b) = (k a, k b)`. -/
def escala (k : K) (R : Relacao K) : Relacao K := (k * R.1, k * R.2)

theorem d_escala (k : K) (R : Relacao K) : d (escala k R) = ‖k‖ * d R := by
  unfold d escala
  rw [← mul_sub, norm_mul]

theorem d_iter_escala (k : K) (R : Relacao K) (n : ℕ) : d ((escala k)^[n] R) = ‖k‖ ^ n * d R := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', d_escala, ih, pow_succ]
    ring

theorem escala_preserva {k : K} (hk : k ≠ 0) : PreservaEquiv (escala k) := by
  intro R
  unfold Verdadeira escala
  exact mul_right_inj' hk

theorem escala_contraiQ (k : K) : ContraiQ ‖k‖ (escala k) := fun R => (d_escala k R).le

theorem escala_contrai {k : K} (hk : ‖k‖ ≤ 1) : Contrai (escala k) := by
  intro R
  rw [d_escala]
  calc ‖k‖ * d R ≤ 1 * d R := mul_le_mul_of_nonneg_right hk (d_nonneg R)
    _ = d R := one_mul _

/-- Exemplo do texto: `k ≠ 0` e `d(T_k R) = 0` ⇒ `d(R) = 0`. -/
theorem escala_fecha {k : K} (hk : k ≠ 0) {R : Relacao K} (h : d (escala k R) = 0) : d R = 0 :=
  preservacao_e_fechamento (escala_preserva hk) h

/-- Colapso: tudo vai para `(0, 0)`. -/
def colapso (_ : Relacao K) : Relacao K := (0, 0)

theorem colapso_contrai : Contrai (colapso (K := K)) := by
  intro R
  have : d (colapso R) = 0 := by simp [d, colapso]
  rw [this]
  exact d_nonneg R

theorem colapso_nao_preserva : ¬ PreservaEquiv (colapso (K := K)) := by
  intro h
  have h1 : Verdadeira ((1 : K), (0 : K)) := (h (1, 0)).mp rfl
  exact one_ne_zero h1

/-- **𝒞 ⊄ 𝒫**: contrair defeitos não preserva a verdade. -/
theorem contrai_nao_implica_preserva :
    ∃ T : Relacao K → Relacao K, Contrai T ∧ ¬ PreservaEquiv T :=
  ⟨colapso, colapso_contrai, colapso_nao_preserva⟩

/-! ### O limite certifica; os termos não -/

theorem continuous_d : Continuous (d : Relacao K → ℝ) := by
  unfold d
  exact (continuous_fst.sub continuous_snd).norm

theorem isClosed_verdadeiras : IsClosed {R : Relacao K | Verdadeira R} :=
  isClosed_diagonal

/-- **O limite certifica**: `R_n → R₀` e `d(R_n) → 0` ⇒ `R₀` verdadeira. -/
theorem limite_certifica {R : ℕ → Relacao K} {R₀ : Relacao K} (hR : Tendsto R atTop (𝓝 R₀))
    (hd : Tendsto (fun n => d (R n)) atTop (𝓝 0)) : Verdadeira R₀ := by
  have h1 : Tendsto (fun n => d (R n)) atTop (𝓝 (d R₀)) :=
    (continuous_d.tendsto R₀).comp hR
  exact (d_eq_zero_iff R₀).mp (tendsto_nhds_unique h1 hd)

/-- Com `R_n → R₀`: `d(R_n) → 0` ⟺ `R₀` verdadeira. -/
theorem limite_iff {R : ℕ → Relacao K} {R₀ : Relacao K} (hR : Tendsto R atTop (𝓝 R₀)) :
    Tendsto (fun n => d (R n)) atTop (𝓝 0) ↔ Verdadeira R₀ := by
  refine ⟨limite_certifica hR, fun h => ?_⟩
  have h1 : Tendsto (fun n => d (R n)) atTop (𝓝 (d R₀)) :=
    (continuous_d.tendsto R₀).comp hR
  rwa [(d_eq_zero_iff R₀).mpr h] at h1

end Basico

section NaoTrivial

variable {L : Type*} [NontriviallyNormedField L]

/-- **𝒫 ⊄ 𝒞**: preservar a verdade não contrai defeitos (escala com ‖k‖ > 1). -/
theorem preserva_nao_implica_contrai :
    ∃ T : Relacao L → Relacao L, PreservaEquiv T ∧ ¬ Contrai T := by
  obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm L
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, norm_zero] at hk
    linarith
  refine ⟨escala k, escala_preserva hk0, fun h => ?_⟩
  have h1 := h (1, 0)
  rw [d_escala] at h1
  have hd : d ((1 : L), (0 : L)) = 1 := by simp [d]
  rw [hd] at h1
  linarith

/-- **Independência das classes**: 𝒫 ⊄ 𝒞 e 𝒞 ⊄ 𝒫. -/
theorem classes_independentes :
    (∃ T : Relacao L → Relacao L, PreservaEquiv T ∧ ¬ Contrai T) ∧
      (∃ T : Relacao L → Relacao L, Contrai T ∧ ¬ PreservaEquiv T) :=
  ⟨preserva_nao_implica_contrai, contrai_nao_implica_preserva⟩

/-- **Aproximação não é igualdade**: existe `T ∈ 𝒫 ∩ 𝒞_q` com `q < 1` e uma relação falsa `R`
cuja órbita tem defeito `→ 0`, mas em que **todo** `Tⁿ R` é falso. -/
theorem aproximacao_nao_certifica :
    ∃ (T : Relacao L → Relacao L) (q : ℝ), q < 1 ∧ PreservaEquiv T ∧ ContraiQ q T ∧
      ∃ R : Relacao L, (∀ n, ¬ Verdadeira (T^[n] R)) ∧
        Tendsto (fun n => d (T^[n] R)) atTop (𝓝 0) := by
  obtain ⟨k, hk0, hk1⟩ := NormedField.exists_norm_lt_one L
  have hk : k ≠ 0 := norm_pos_iff.mp hk0
  refine ⟨escala k, ‖k‖, hk1, escala_preserva hk, escala_contraiQ k, (1, 0), ?_, ?_⟩
  · intro n h
    have := (orbita_iff (escala_preserva hk) (1, 0) n).mp h
    exact one_ne_zero this
  · have hd : ∀ n, d ((escala k)^[n] ((1 : L), (0 : L))) = ‖k‖ ^ n := by
      intro n
      rw [d_iter_escala]
      simp [d]
    simp_rw [hd]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one hk0.le hk1

end NaoTrivial

/-! ### Transporte de certificados -/

/-- Morfismo de estruturas ATK-I: homomorfismo de corpos isométrico. -/
structure Morfismo (K L : Type*) [NormedField K] [NormedField L] where
  φ : K →+* L
  isom : ∀ x, ‖φ x‖ = ‖x‖

namespace Morfismo

variable {K L M : Type*} [NormedField K] [NormedField L] [NormedField M]

/-- Imagem de uma relação. -/
def map (f : Morfismo K L) (R : Relacao K) : Relacao L := (f.φ R.1, f.φ R.2)

theorem map_oplus (f : Morfismo K L) (R S : Relacao K) :
    f.map (oplus R S) = oplus (f.map R) (f.map S) := by
  simp [map, oplus]

theorem map_otimes (f : Morfismo K L) (R S : Relacao K) :
    f.map (otimes R S) = otimes (f.map R) (f.map S) := by
  simp [map, otimes]

theorem map_escala (f : Morfismo K L) (k : K) (R : Relacao K) :
    f.map (escala k R) = escala (f.φ k) (f.map R) := by
  simp [map, escala]

/-- **Invariância do defeito.** -/
theorem d_map (f : Morfismo K L) (R : Relacao K) : d (f.map R) = d R := by
  unfold d map
  rw [← map_sub, f.isom]

/-- **Verdade transportada nas duas direções.** -/
theorem verdadeira_map_iff (f : Morfismo K L) (R : Relacao K) :
    Verdadeira (f.map R) ↔ Verdadeira R := by
  rw [← d_eq_zero_iff, ← d_eq_zero_iff, d_map]

/-- Certificados quantitativos (`d ≤ ε`) passam de L para K sem perda. -/
theorem transporte_eps (f : Morfismo K L) (R : Relacao K) (ε : ℝ) :
    d (f.map R) ≤ ε ↔ d R ≤ ε := by
  rw [d_map]

theorem transporte_preserva (f : Morfismo K L) {TK : Relacao K → Relacao K} {TL : Relacao L → Relacao L}
    (hent : ∀ R, f.map (TK R) = TL (f.map R)) (hTL : PreservaEquiv TL) : PreservaEquiv TK := by
  intro R
  rw [← f.verdadeira_map_iff, hent, hTL, f.verdadeira_map_iff]

theorem transporte_contrai (f : Morfismo K L) {TK : Relacao K → Relacao K} {TL : Relacao L → Relacao L}
    (hent : ∀ R, f.map (TK R) = TL (f.map R)) (hTL : Contrai TL) : Contrai TK := by
  intro R
  rw [← f.d_map (TK R), hent, ← f.d_map R]
  exact hTL _

theorem transporte_contraiQ (f : Morfismo K L) {q : ℝ} {TK : Relacao K → Relacao K}
    {TL : Relacao L → Relacao L} (hent : ∀ R, f.map (TK R) = TL (f.map R)) (hTL : ContraiQ q TL) :
    ContraiQ q TK := by
  intro R
  rw [← f.d_map (TK R), hent, ← f.d_map R]
  exact hTL _

theorem transporte_limite (f : Morfismo K L) (R : ℕ → Relacao K) :
    Tendsto (fun n => d (f.map (R n))) atTop (𝓝 0) ↔ Tendsto (fun n => d (R n)) atTop (𝓝 0) := by
  simp_rw [d_map]

/-- **Teorema de transporte de certificados (ATK-I).**  Para um morfismo isométrico `f : K → L`:
verdade, defeitos, certificados ε, as classes 𝒫 e 𝒞 de transformações entrelaçadas e os
certificados por limite passam de `L` para `K` sem perda de semântica. -/
theorem transporte_certificados (f : Morfismo K L) {TK : Relacao K → Relacao K} {TL : Relacao L → Relacao L}
    (hent : ∀ R, f.map (TK R) = TL (f.map R)) :
    (∀ R, Verdadeira (f.map R) ↔ Verdadeira R) ∧
    (∀ R, d (f.map R) = d R) ∧
    (∀ R ε, d (f.map R) ≤ ε ↔ d R ≤ ε) ∧
    (PreservaEquiv TL → PreservaEquiv TK) ∧
    (Contrai TL → Contrai TK) ∧
    (∀ R : ℕ → Relacao K, Tendsto (fun n => d (f.map (R n))) atTop (𝓝 0) ↔
      Tendsto (fun n => d (R n)) atTop (𝓝 0)) :=
  ⟨f.verdadeira_map_iff, f.d_map, f.transporte_eps, f.transporte_preserva hent,
    f.transporte_contrai hent, f.transporte_limite⟩

/-- Morfismo identidade. -/
def id (K : Type*) [NormedField K] : Morfismo K K := ⟨RingHom.id K, fun _ => rfl⟩

/-- Composição de morfismos. -/
def comp (g : Morfismo L M) (f : Morfismo K L) : Morfismo K M :=
  ⟨g.φ.comp f.φ, fun x => by simp [g.isom, f.isom]⟩

theorem map_comp (g : Morfismo L M) (f : Morfismo K L) (R : Relacao K) :
    (g.comp f).map R = g.map (f.map R) := rfl

end Morfismo

/-- `ℝ → ℂ` é um morfismo ATK-I. -/
noncomputable def realComplexo : Morfismo ℝ ℂ :=
  ⟨Complex.ofRealHom, fun x => by simp [Complex.norm_real]⟩

/-- `ℚ → ℝ` é um morfismo ATK-I. -/
noncomputable def racionalReal : Morfismo ℚ ℝ :=
  ⟨Rat.castHom ℝ, fun q => Rat.norm_cast_real q⟩

/-- Exemplo: a escala por `2` em ℂ entrelaça a escala por `2` em ℝ; logo o fato
"`T_2 ∈ 𝒫` em ℂ" desce para ℝ. -/
theorem exemplo_transporte : PreservaEquiv (escala (2 : ℝ)) :=
  realComplexo.transporte_preserva (TL := escala (2 : ℂ))
    (fun R => by rw [Morfismo.map_escala]; simp [realComplexo])
    (escala_preserva two_ne_zero)

end ATK.RelacionalI

#print axioms ATK.RelacionalI.d_nonneg
#print axioms ATK.RelacionalI.d_eq_zero_iff
#print axioms ATK.RelacionalI.d_pos_iff
#print axioms ATK.RelacionalI.d_swap
#print axioms ATK.RelacionalI.d_trans
#print axioms ATK.RelacionalI.d_oplus_le
#print axioms ATK.RelacionalI.d_otimes_le
#print axioms ATK.RelacionalI.d_sum_le
#print axioms ATK.RelacionalI.verdadeira_refl
#print axioms ATK.RelacionalI.verdadeira_oplus
#print axioms ATK.RelacionalI.verdadeira_otimes
#print axioms ATK.RelacionalI.oplus_nao_reflete
#print axioms ATK.RelacionalI.familia_verdadeira_iff
#print axioms ATK.RelacionalI.familia_falha
#print axioms ATK.RelacionalI.prox_refl
#print axioms ATK.RelacionalI.prox_trans
#print axioms ATK.RelacionalI.prox_total
#print axioms ATK.RelacionalI.verdadeira_maxima
#print axioms ATK.RelacionalI.verdadeira_de_prox
#print axioms ATK.RelacionalI.preservacao_e_fechamento
#print axioms ATK.RelacionalI.preservaEquiv_id
#print axioms ATK.RelacionalI.preservaEquiv_comp
#print axioms ATK.RelacionalI.contrai_id
#print axioms ATK.RelacionalI.contrai_comp
#print axioms ATK.RelacionalI.contraiQ_iter
#print axioms ATK.RelacionalI.orbita_iff
#print axioms ATK.RelacionalI.d_escala
#print axioms ATK.RelacionalI.d_iter_escala
#print axioms ATK.RelacionalI.escala_preserva
#print axioms ATK.RelacionalI.escala_contraiQ
#print axioms ATK.RelacionalI.escala_contrai
#print axioms ATK.RelacionalI.escala_fecha
#print axioms ATK.RelacionalI.colapso_contrai
#print axioms ATK.RelacionalI.colapso_nao_preserva
#print axioms ATK.RelacionalI.contrai_nao_implica_preserva
#print axioms ATK.RelacionalI.continuous_d
#print axioms ATK.RelacionalI.isClosed_verdadeiras
#print axioms ATK.RelacionalI.limite_certifica
#print axioms ATK.RelacionalI.limite_iff
#print axioms ATK.RelacionalI.preserva_nao_implica_contrai
#print axioms ATK.RelacionalI.classes_independentes
#print axioms ATK.RelacionalI.aproximacao_nao_certifica
#print axioms ATK.RelacionalI.Morfismo.map_oplus
#print axioms ATK.RelacionalI.Morfismo.map_otimes
#print axioms ATK.RelacionalI.Morfismo.map_escala
#print axioms ATK.RelacionalI.Morfismo.d_map
#print axioms ATK.RelacionalI.Morfismo.verdadeira_map_iff
#print axioms ATK.RelacionalI.Morfismo.transporte_eps
#print axioms ATK.RelacionalI.Morfismo.transporte_preserva
#print axioms ATK.RelacionalI.Morfismo.transporte_contrai
#print axioms ATK.RelacionalI.Morfismo.transporte_contraiQ
#print axioms ATK.RelacionalI.Morfismo.transporte_limite
#print axioms ATK.RelacionalI.Morfismo.transporte_certificados
#print axioms ATK.RelacionalI.Morfismo.map_comp
#print axioms ATK.RelacionalI.exemplo_transporte
