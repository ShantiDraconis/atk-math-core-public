import ATK.TerceiroTemplo
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing

/-!
# Terceiro Templo II — gap espectral da Árvore, operadores U·C·R e comutadores

Continua `ATK.TerceiroTemplo`.

* **Média e desvio** (`media`, `desvio_minimo`): a soma dos quadrados dos desvios é mínima na
  média, com `∑(f − c)² = ∑(f − m)² + n(m − c)²`.
* **Gap espectral da Árvore** (Teorema 3 do documento, no grafo concreto):
  `∑ₛ (f s − f̄)² ≤ 10 · E(f)` (`poincare_arvore`). O quociente de Rayleigh fora das constantes
  é então `≥ 1/10` (`gap_arvore`): `λ₂ ≥ 1/10`. A constante vem dos caminhos explícitos a partir
  de Keter (comprimento ≤ 3), com Tiferet usado 10 vezes.
* **Operadores U·C·R** (simetria, contração, reconstrução): se `U` preserva o defeito, `C` o
  contrai por `q` e `R` não o aumenta, então `d(R(C(Ux))) ≤ q·d(x)`, e iterando, `≤ qⁿ d(x) → 0`.
  Contraexemplo: sem a hipótese sobre `R`, a lei falha (`urc_precisa_R`).
* **Comutadores** `[a, b] = ab − ba` (portas como pares de operadores): antissimetria, `[a, a] = 0`,
  identidade de Jacobi, `[a, b] = 0 ↔` comutam; exemplo matricial **não** comutativo
  `[E₁₂, E₂₁] = diag(1, −1)`.
-/

open Filter Topology

namespace ATK.TerceiroTemplo

/-! ## 1. Média e desvio mínimo -/

/-- A média de `f` sobre um tipo finito. -/
noncomputable def media {V : Type*} [Fintype V] (f : V → ℝ) : ℝ :=
  (∑ v, f v) / Fintype.card V

/-- `∑(f − c)² = ∑(f − m)² + n(m − c)²`. -/
theorem decomposicao_desvio {V : Type*} [Fintype V] [Nonempty V] (f : V → ℝ) (c : ℝ) :
    ∑ v, (f v - c) ^ 2 = ∑ v, (f v - media f) ^ 2 + Fintype.card V * (media f - c) ^ 2 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ v, (f v - media f) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, media]
    field_simp
    ring
  have e : ∑ v, (f v - c) ^ 2 = ∑ v, (f v - media f) ^ 2
      + ∑ v, (2 * (media f - c) * (f v - media f) + (media f - c) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [e, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

/-- A média minimiza a soma dos quadrados dos desvios. -/
theorem desvio_minimo {V : Type*} [Fintype V] [Nonempty V] (f : V → ℝ) (c : ℝ) :
    ∑ v, (f v - media f) ^ 2 ≤ ∑ v, (f v - c) ^ 2 := by
  rw [decomposicao_desvio f c]
  have : 0 ≤ (Fintype.card V : ℝ) * (media f - c) ^ 2 := by positivity
  linarith

/-! ## 2. Gap espectral da Árvore -/

instance : Nonempty Sefira := ⟨.keter⟩

/-- A energia da Árvore escrita nos seus 22 termos. -/
theorem energiaArvore_expl (f : Sefira → ℝ) : energiaArvore f =
    (f .keter - f .chokhmah) ^ 2 + (f .keter - f .binah) ^ 2 + (f .keter - f .tiferet) ^ 2
    + (f .chokhmah - f .binah) ^ 2 + (f .chokhmah - f .tiferet) ^ 2
    + (f .chokhmah - f .chesed) ^ 2 + (f .binah - f .tiferet) ^ 2 + (f .binah - f .gevurah) ^ 2
    + (f .chesed - f .gevurah) ^ 2 + (f .chesed - f .tiferet) ^ 2 + (f .chesed - f .netzach) ^ 2
    + (f .gevurah - f .tiferet) ^ 2 + (f .gevurah - f .hod) ^ 2 + (f .tiferet - f .netzach) ^ 2
    + (f .tiferet - f .yesod) ^ 2 + (f .tiferet - f .hod) ^ 2 + (f .netzach - f .hod) ^ 2
    + (f .netzach - f .yesod) ^ 2 + (f .netzach - f .malkhut) ^ 2 + (f .hod - f .yesod) ^ 2
    + (f .hod - f .malkhut) ^ 2 + (f .yesod - f .malkhut) ^ 2 := by
  simp only [energiaArvore, Fin.sum_univ_succ, Fin.sum_univ_zero, caminho]
  simp
  ring

/-- Soma sobre as dez sefirot, termo a termo. -/
theorem soma_sefirot (g : Sefira → ℝ) : ∑ s, g s =
    g .keter + g .chokhmah + g .binah + g .chesed + g .gevurah + g .tiferet + g .netzach
    + g .hod + g .yesod + g .malkhut := by
  rw [show (Finset.univ : Finset Sefira) = {.keter, .chokhmah, .binah, .chesed, .gevurah,
    .tiferet, .netzach, .hod, .yesod, .malkhut} from rfl]
  simp [Finset.sum_insert]
  ring

/-- Caminhos a partir de Keter: `∑ₛ (f s − f Keter)² ≤ 10 · E(f)`. -/
theorem poincare_keter (f : Sefira → ℝ) :
    ∑ s, (f s - f .keter) ^ 2 ≤ 10 * energiaArvore f := by
  rw [soma_sefirot, energiaArvore_expl]
  have h2 : ∀ a b : ℝ, (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := fun a b => by
    nlinarith [sq_nonneg (a - b)]
  have h3 : ∀ a b c : ℝ, (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := fun a b c => by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
  -- caminhos a partir de Keter (arestas 0, 1, 2, 5, 7, 13, 14, 15, 21)
  have hk : (f .keter - f .keter) ^ 2 = 0 := by ring
  have hc : (f .chokhmah - f .keter) ^ 2 = (f .keter - f .chokhmah) ^ 2 := by ring
  have hb : (f .binah - f .keter) ^ 2 = (f .keter - f .binah) ^ 2 := by ring
  have ht : (f .tiferet - f .keter) ^ 2 = (f .keter - f .tiferet) ^ 2 := by ring
  have hch : (f .chesed - f .keter) ^ 2 ≤
      2 * ((f .keter - f .chokhmah) ^ 2 + (f .chokhmah - f .chesed) ^ 2) := by
    have := h2 (-(f .keter - f .chokhmah)) (-(f .chokhmah - f .chesed)); ring_nf at this ⊢; linarith
  have hge : (f .gevurah - f .keter) ^ 2 ≤
      2 * ((f .keter - f .binah) ^ 2 + (f .binah - f .gevurah) ^ 2) := by
    have := h2 (-(f .keter - f .binah)) (-(f .binah - f .gevurah)); ring_nf at this ⊢; linarith
  have hne : (f .netzach - f .keter) ^ 2 ≤
      2 * ((f .keter - f .tiferet) ^ 2 + (f .tiferet - f .netzach) ^ 2) := by
    have := h2 (-(f .keter - f .tiferet)) (-(f .tiferet - f .netzach)); ring_nf at this ⊢; linarith
  have hye : (f .yesod - f .keter) ^ 2 ≤
      2 * ((f .keter - f .tiferet) ^ 2 + (f .tiferet - f .yesod) ^ 2) := by
    have := h2 (-(f .keter - f .tiferet)) (-(f .tiferet - f .yesod)); ring_nf at this ⊢; linarith
  have hho : (f .hod - f .keter) ^ 2 ≤
      2 * ((f .keter - f .tiferet) ^ 2 + (f .tiferet - f .hod) ^ 2) := by
    have := h2 (-(f .keter - f .tiferet)) (-(f .tiferet - f .hod)); ring_nf at this ⊢; linarith
  have hma : (f .malkhut - f .keter) ^ 2 ≤ 3 * ((f .keter - f .tiferet) ^ 2
      + (f .tiferet - f .yesod) ^ 2 + (f .yesod - f .malkhut) ^ 2) := by
    have := h3 (-(f .keter - f .tiferet)) (-(f .tiferet - f .yesod)) (-(f .yesod - f .malkhut))
    ring_nf at this ⊢; linarith
  rw [hk, hc, hb, ht]
  linarith [sq_nonneg (f .keter - f .chokhmah), sq_nonneg (f .keter - f .binah),
    sq_nonneg (f .keter - f .tiferet), sq_nonneg (f .chokhmah - f .binah),
    sq_nonneg (f .chokhmah - f .tiferet), sq_nonneg (f .chokhmah - f .chesed),
    sq_nonneg (f .binah - f .tiferet), sq_nonneg (f .binah - f .gevurah),
    sq_nonneg (f .chesed - f .gevurah), sq_nonneg (f .chesed - f .tiferet),
    sq_nonneg (f .chesed - f .netzach), sq_nonneg (f .gevurah - f .tiferet),
    sq_nonneg (f .gevurah - f .hod), sq_nonneg (f .tiferet - f .netzach),
    sq_nonneg (f .tiferet - f .yesod), sq_nonneg (f .tiferet - f .hod),
    sq_nonneg (f .netzach - f .hod), sq_nonneg (f .netzach - f .yesod),
    sq_nonneg (f .netzach - f .malkhut), sq_nonneg (f .hod - f .yesod),
    sq_nonneg (f .hod - f .malkhut), sq_nonneg (f .yesod - f .malkhut)]

/-- **Desigualdade de Poincaré da Árvore**: `∑ₛ (f s − f̄)² ≤ 10 · E(f)`. -/
theorem poincare_arvore (f : Sefira → ℝ) :
    ∑ s, (f s - media f) ^ 2 ≤ 10 * energiaArvore f :=
  (desvio_minimo f (f .keter)).trans (poincare_keter f)

/-- **Gap espectral da Árvore**: fora das constantes, `E(f) ≥ (1/10)·∑(f − f̄)²`, isto é,
`λ₂ ≥ 1/10` (com a energia contada uma vez por caminho). -/
theorem gap_arvore (f : Sefira → ℝ) :
    (1 / 10 : ℝ) * ∑ s, (f s - media f) ^ 2 ≤ energiaArvore f := by
  have := poincare_arvore f
  linarith

/-- O gap é positivo: se `f` não é constante, `E(f) > 0`. -/
theorem energia_pos_de_nao_constante (f : Sefira → ℝ) (h : ∃ s, f s ≠ f .keter) :
    0 < energiaArvore f := by
  rcases (energiaArvore_nonneg f).lt_or_eq with hlt | heq
  · exact hlt
  · obtain ⟨s, hs⟩ := h
    exact absurd ((energiaArvore_zero_iff f).1 heq.symm s) hs

/-! ## 3. Operadores U · C · R -/

/-- Iteração de uma contração de defeito: `d(Fⁿx) ≤ qⁿ d(x)`. -/
theorem defeito_iterado {α : Type*} {d : α → ℝ} {F : α → α} {q : ℝ} (hq : 0 ≤ q)
    (h : ∀ x, d (F x) ≤ q * d x) (n : ℕ) (x : α) : d (F^[n] x) ≤ q ^ n * d x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    calc d (F (F^[n] x)) ≤ q * d (F^[n] x) := h _
      _ ≤ q * (q ^ n * d x) := mul_le_mul_of_nonneg_left ih hq
      _ = q ^ n * q * d x := by ring

/-- **Lei U·C·R**: simetria que preserva, contração por `q`, reconstrução que não aumenta. -/
theorem lei_URC {α : Type*} {d : α → ℝ} {U C R : α → α} {q : ℝ}
    (hU : ∀ x, d (U x) = d x) (hC : ∀ x, d (C x) ≤ q * d x) (hR : ∀ x, d (R x) ≤ d x) (x : α) :
    d (R (C (U x))) ≤ q * d x :=
  calc d (R (C (U x))) ≤ d (C (U x)) := hR _
    _ ≤ q * d (U x) := hC _
    _ = q * d x := by rw [hU]

/-- Iterando `R ∘ C ∘ U` com `0 ≤ q < 1` e `d ≥ 0`, o defeito tende a zero. -/
theorem URC_tende_zero {α : Type*} {d : α → ℝ} {U C R : α → α} {q : ℝ} (hq : 0 ≤ q)
    (hq1 : q < 1) (hd : ∀ x, 0 ≤ d x)
    (hU : ∀ x, d (U x) = d x) (hC : ∀ x, d (C x) ≤ q * d x) (hR : ∀ x, d (R x) ≤ d x) (x : α) :
    Tendsto (fun n => d ((R ∘ C ∘ U)^[n] x)) atTop (𝓝 0) := by
  have hb := defeito_iterado (F := R ∘ C ∘ U) hq (fun y => lei_URC hU hC hR y)
  have hlim : Tendsto (fun n : ℕ => q ^ n * d x) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const (d x)
  exact squeeze_zero (fun n => hd _) (fun n => hb n x) hlim

/-- **Contraexemplo**: sem a hipótese sobre `R`, a lei falha (em `ℝ`, `d = |·|`, `U = C = id`
com `q = 1`, `R x = 2x`). -/
theorem urc_precisa_R :
    ¬ ∀ x : ℝ, |(fun y : ℝ => 2 * y) (id (id x))| ≤ 1 * |x| := by
  intro h
  have := h 1
  norm_num at this

/-! ## 4. Comutadores das portas -/

section Comutador

variable {A : Type*} [Ring A]

/-- `[a, b] = ab − ba`. -/
def comutador (a b : A) : A := a * b - b * a

theorem comutador_antissim (a b : A) : comutador a b = -comutador b a := by
  unfold comutador; noncomm_ring

theorem comutador_self (a : A) : comutador a a = 0 := sub_self _

theorem comutador_jacobi (a b c : A) :
    comutador a (comutador b c) + comutador b (comutador c a) + comutador c (comutador a b) = 0 := by
  unfold comutador; noncomm_ring

theorem comutador_zero_iff (a b : A) : comutador a b = 0 ↔ a * b = b * a := sub_eq_zero

end Comutador

/-- Exemplo não comutativo: `[E₁₂, E₂₁] = diag(1, −1) ≠ 0`. -/
theorem comutador_matriz :
    comutador !![(0 : ℤ), 1; 0, 0] !![0, 0; 1, 0] = !![1, 0; 0, -1] := by
  unfold comutador
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem comutador_matriz_ne_zero :
    comutador !![(0 : ℤ), 1; 0, 0] !![0, 0; 1, 0] ≠ 0 := by
  rw [comutador_matriz]
  intro h
  have := congrFun (congrFun h 0) 0
  simp at this

end ATK.TerceiroTemplo

#print axioms ATK.TerceiroTemplo.decomposicao_desvio
#print axioms ATK.TerceiroTemplo.desvio_minimo
#print axioms ATK.TerceiroTemplo.energiaArvore_expl
#print axioms ATK.TerceiroTemplo.soma_sefirot
#print axioms ATK.TerceiroTemplo.poincare_keter
#print axioms ATK.TerceiroTemplo.poincare_arvore
#print axioms ATK.TerceiroTemplo.gap_arvore
#print axioms ATK.TerceiroTemplo.energia_pos_de_nao_constante
#print axioms ATK.TerceiroTemplo.defeito_iterado
#print axioms ATK.TerceiroTemplo.lei_URC
#print axioms ATK.TerceiroTemplo.URC_tende_zero
#print axioms ATK.TerceiroTemplo.urc_precisa_R
#print axioms ATK.TerceiroTemplo.comutador_antissim
#print axioms ATK.TerceiroTemplo.comutador_self
#print axioms ATK.TerceiroTemplo.comutador_jacobi
#print axioms ATK.TerceiroTemplo.comutador_zero_iff
#print axioms ATK.TerceiroTemplo.comutador_matriz
#print axioms ATK.TerceiroTemplo.comutador_matriz_ne_zero
