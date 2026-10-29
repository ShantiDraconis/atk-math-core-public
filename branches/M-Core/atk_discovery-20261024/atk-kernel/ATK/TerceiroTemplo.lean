import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Powerset

/-!
# Terceiro Templo — a estrutura da Cabala como objeto matemático

Formaliza a parte **demonstrável** do documento "Terceiro Templo" (Cabala × problemas do milênio):

* **Alfabeto** (`Letra`): as 22 letras, as três famílias do Sefer Yetzirah (3 mães, 7 duplas,
  12 simples), a gematria padrão (injetiva, soma 1495), as 231 portas `= C(22, 2)` e os 32 caminhos
  `= 10 + 22` (e `32 = ל + ב`).
* **Árvore da Vida** (`Sefira`, `caminho`): as 10 sefirot e os 22 caminhos da convenção de Kircher
  (1652); sem laços, sem caminhos repetidos, conexa; número ciclomático `22 − 10 + 1 = 13`.
* **Energia e laplaciano**: `energia ≥ 0`; `2⟨f, Lf⟩ = energia` (pesos simétricos), logo `L ⪰ 0`;
  na Árvore, energia nula **se e só se** `f` é constante.
* **Ciclo `C₁₀`**: `cos(θx)` é autovetor do laplaciano do ciclo com autovalor `2 − 2cos θ`;
  primeiro autovalor positivo `2 − 2cos(π/5) = (3 − √5)/2`; para `T = I − L/4`, `μ = cos²(πk/10)`
  e `q = cos²(π/10) = (5 + √5)/8 < 1`.
* **Invariância e contração**: invariantes preservados por composição e identidade;
  `‖Tⁿx‖ ≤ qⁿ‖x‖ → 0`; um defeito invariante **e** estritamente contraído já é zero.
* **Zero, seta e infinitésimo**: `10⁻ᴺ > 0` e `10⁻ᴺ → 0`; `1/5 + 1/(N+1)` é positivo e
  decrescente mas **não** tende a zero; `10⁻ᴴ` hiper-real (`H` infinito) é `> 0` com parte padrão 0;
  `E₁ = 1 − ln 2 ∈ (0,3068528192; 0,3068528197)`.
* **Defeitos dos outros problemas**: `d_δ(Δ) = max(0, δ − Δ) = 0 ↔ Δ ≥ δ` (YM); o espectro
  `{1/(n+1)}` não tem gap; `D_N ≤ K/log(N+2)` e `D_N ≤ C qⁿ` forçam `D_N → 0` (RH);
  `y = (1 − 2t)^(−1/2)` resolve `y' = y³` e explode em `t = 1/2` (NS); defeito inteiro `< 1`
  fecha a igualdade (BSD, versão em ℤ).
* **Atribuição simbólica** (`letrasDe`): a tabela letra → problema do documento, registrada como
  **dado**; cobre as 22 letras e `ת` está em todos os oito. É só rótulo: nenhum teorema daqui
  usa a tabela como hipótese de uma conjectura.

Nenhum teorema deste arquivo prova um problema do milênio: as pontes (do grafo finito para
Nyman–Beurling, para o Hamiltoniano de Yang–Mills etc.) continuam `OPEN_MATH`.
-/

open Filter Topology Real

namespace ATK.TerceiroTemplo

/-! ## 1. O alfabeto -/

/-- As 22 letras hebraicas. -/
inductive Letra
  | alef | bet | gimel | dalet | he | vav | zayin | chet | tet | yod | kaf
  | lamed | mem | nun | samekh | ayin | pe | tsadi | qof | resh | shin | tav
  deriving DecidableEq, Repr

open Letra in
instance : Fintype Letra :=
  ⟨{alef, bet, gimel, dalet, he, vav, zayin, chet, tet, yod, kaf,
    lamed, mem, nun, samekh, ayin, pe, tsadi, qof, resh, shin, tav}, fun x => by cases x <;> decide⟩

/-- As três famílias do Sefer Yetzirah. -/
inductive Familia
  | mae | dupla | simples
  deriving DecidableEq, Repr

open Letra in
/-- Mães `א מ ש`; duplas `ב ג ד כ פ ר ת`; as outras doze são simples. -/
def familia : Letra → Familia
  | alef | mem | shin => .mae
  | bet | gimel | dalet | kaf | pe | resh | tav => .dupla
  | _ => .simples

open Letra in
/-- Gematria padrão (valores sem as formas finais). -/
def gematria : Letra → ℕ
  | alef => 1 | bet => 2 | gimel => 3 | dalet => 4 | he => 5 | vav => 6 | zayin => 7
  | chet => 8 | tet => 9 | yod => 10 | kaf => 20 | lamed => 30 | mem => 40 | nun => 50
  | samekh => 60 | ayin => 70 | pe => 80 | tsadi => 90 | qof => 100 | resh => 200
  | shin => 300 | tav => 400

theorem card_letras : Fintype.card Letra = 22 := rfl

theorem card_maes : (Finset.univ.filter fun l => familia l = .mae).card = 3 := by decide

theorem card_duplas : (Finset.univ.filter fun l => familia l = .dupla).card = 7 := by decide

theorem card_simples : (Finset.univ.filter fun l => familia l = .simples).card = 12 := by decide

/-- `22 = 3 + 7 + 12`. -/
theorem familias_particionam :
    (Finset.univ.filter fun l => familia l = .mae).card
      + (Finset.univ.filter fun l => familia l = .dupla).card
      + (Finset.univ.filter fun l => familia l = .simples).card = Fintype.card Letra := by
  decide

/-- Letras diferentes têm valores diferentes. -/
theorem gematria_injetiva : Function.Injective gematria := by decide

theorem gematria_soma : ∑ l, gematria l = 1495 := by decide

/-- As mães `א + מ + ש = 1 + 40 + 300`. -/
theorem gematria_maes : gematria .alef + gematria .mem + gematria .shin = 341 := rfl

/-- As 231 portas: os pares não ordenados de letras distintas. -/
theorem portas_231 : (Finset.univ.powersetCard 2 : Finset (Finset Letra)).card = 231 := by
  rw [Finset.card_powersetCard, Finset.card_univ, card_letras]
  rfl

theorem portas_eq_choose : Nat.choose 22 2 = 231 := rfl

/-- Os 32 caminhos da sabedoria: 10 sefirot + 22 letras; e `32 = ל + ב` (*lev*, coração). -/
theorem caminhos_32 : 10 + Fintype.card Letra = 32 ∧ gematria .lamed + gematria .bet = 32 :=
  ⟨rfl, rfl⟩

/-! ## 2. A Árvore da Vida -/

/-- As dez sefirot. -/
inductive Sefira
  | keter | chokhmah | binah | chesed | gevurah | tiferet | netzach | hod | yesod | malkhut
  deriving DecidableEq, Repr

open Sefira in
instance : Fintype Sefira :=
  ⟨{keter, chokhmah, binah, chesed, gevurah, tiferet, netzach, hod, yesod, malkhut},
    fun x => by cases x <;> decide⟩

theorem card_sefirot : Fintype.card Sefira = 10 := rfl

open Sefira in
/-- Os 22 caminhos (convenção de Kircher, *Oedipus Aegyptiacus*, 1652). -/
def caminho : Fin 22 → Sefira × Sefira :=
  ![(keter, chokhmah), (keter, binah), (keter, tiferet), (chokhmah, binah),
    (chokhmah, tiferet), (chokhmah, chesed), (binah, tiferet), (binah, gevurah),
    (chesed, gevurah), (chesed, tiferet), (chesed, netzach), (gevurah, tiferet),
    (gevurah, hod), (tiferet, netzach), (tiferet, yesod), (tiferet, hod),
    (netzach, hod), (netzach, yesod), (netzach, malkhut), (hod, yesod),
    (hod, malkhut), (yesod, malkhut)]

/-- Nenhum caminho liga uma sefirá a si mesma. -/
theorem caminho_sem_laco : ∀ i, (caminho i).1 ≠ (caminho i).2 := by decide

/-- Nenhum par de sefirot é ligado por dois caminhos (em qualquer orientação). -/
theorem caminho_sem_repeticao :
    ∀ i j, i ≠ j → Sym2.mk (caminho i) ≠ Sym2.mk (caminho j) := by decide

/-- Um passo de alcance a partir de um conjunto de sefirot. -/
def passo (S : Finset Sefira) : Finset Sefira :=
  S ∪ Finset.univ.filter fun t => ∃ i, ((caminho i).1 ∈ S ∧ (caminho i).2 = t) ∨
    ((caminho i).2 ∈ S ∧ (caminho i).1 = t)

/-- A partir de Keter, quatro passos alcançam as dez sefirot: a Árvore é conexa. -/
theorem arvore_conexa : passo (passo (passo (passo {.keter}))) = Finset.univ := by decide

/-- Número ciclomático (primeiro número de Betti) de um grafo conexo: `|E| − |V| + 1 = 13`. -/
theorem betti_um : (22 : ℤ) - Fintype.card Sefira + 1 = 13 := by rw [card_sefirot]; norm_num

/-! ## 3. Energia e laplaciano -/

section Laplaciano

variable {V : Type*} [Fintype V]

/-- Energia `E(f) = ∑ᵤ ∑ᵥ w u v (f u − f v)²`. -/
def energia (w : V → V → ℝ) (f : V → ℝ) : ℝ := ∑ u, ∑ v, w u v * (f u - f v) ^ 2

/-- Laplaciano ponderado `(L f)(u) = ∑ᵥ w u v (f u − f v)`. -/
def lap (w : V → V → ℝ) (f : V → ℝ) (u : V) : ℝ := ∑ v, w u v * (f u - f v)

theorem energia_nonneg {w : V → V → ℝ} (hw : ∀ u v, 0 ≤ w u v) (f : V → ℝ) :
    0 ≤ energia w f :=
  Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => mul_nonneg (hw u v) (sq_nonneg _)

/-- `2⟨f, Lf⟩ = E(f)` para pesos simétricos. -/
theorem forma_laplaciano {w : V → V → ℝ} (hw : ∀ u v, w u v = w v u) (f : V → ℝ) :
    2 * ∑ u, f u * lap w f u = energia w f := by
  have hswap : ∑ u, ∑ v, w u v * (f v * (f v - f u)) = ∑ u, ∑ v, w u v * (f u * (f u - f v)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [hw v u]
  have hsplit : energia w f = ∑ u, ∑ v, w u v * (f u * (f u - f v))
      + ∑ u, ∑ v, w u v * (f v * (f v - f u)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [hsplit, hswap, ← two_mul]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [lap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

/-- O laplaciano é positivo semidefinido: `⟨f, Lf⟩ ≥ 0`. -/
theorem lap_psd {w : V → V → ℝ} (hs : ∀ u v, w u v = w v u) (hw : ∀ u v, 0 ≤ w u v)
    (f : V → ℝ) : 0 ≤ ∑ u, f u * lap w f u := by
  have := forma_laplaciano hs f
  have := energia_nonneg hw f
  linarith

end Laplaciano

/-- Energia da Árvore: soma de `(f a − f b)²` sobre os 22 caminhos. -/
def energiaArvore (f : Sefira → ℝ) : ℝ := ∑ i, (f (caminho i).1 - f (caminho i).2) ^ 2

theorem energiaArvore_nonneg (f : Sefira → ℝ) : 0 ≤ energiaArvore f :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Energia nula na Árvore **se e só se** `f` é constante (equilíbrio). -/
theorem energiaArvore_zero_iff (f : Sefira → ℝ) :
    energiaArvore f = 0 ↔ ∀ s, f s = f .keter := by
  constructor
  · intro h
    have e : ∀ i, f (caminho i).1 = f (caminho i).2 := by
      intro i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg
        (f (caminho j).1 - f (caminho j).2))).1 h i (Finset.mem_univ i)
      exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hi)
    have h0 : f .keter = f .chokhmah := e 0
    have h1 : f .keter = f .binah := e 1
    have h2 : f .keter = f .tiferet := e 2
    have h5 : f .chokhmah = f .chesed := e 5
    have h7 : f .binah = f .gevurah := e 7
    have h13 : f .tiferet = f .netzach := e 13
    have h14 : f .tiferet = f .yesod := e 14
    have h15 : f .tiferet = f .hod := e 15
    have h21 : f .yesod = f .malkhut := e 21
    intro s
    cases s <;> linarith
  · intro h
    unfold energiaArvore
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h (caminho i).1, h (caminho i).2]
    ring

/-! ## 4. O ciclo de dez estados -/

/-- `cos(θx)` é autovetor do laplaciano do ciclo: `2f(x) − f(x−1) − f(x+1) = (2 − 2cos θ) f(x)`. -/
theorem ciclo_autovetor (θ x : ℝ) :
    2 * cos (θ * x) - cos (θ * (x - 1)) - cos (θ * (x + 1)) = (2 - 2 * cos θ) * cos (θ * x) := by
  have h1 : θ * (x - 1) = θ * x - θ := by ring
  have h2 : θ * (x + 1) = θ * x + θ := by ring
  rw [h1, h2, cos_sub, cos_add]
  ring

/-- Periodicidade: com `θ = 2πk/n`, o autovetor fecha o ciclo de `n` vértices. -/
theorem ciclo_periodico (k : ℤ) {n : ℝ} (hn : n ≠ 0) (x : ℝ) :
    cos (2 * π * k / n * (x + n)) = cos (2 * π * k / n * x) := by
  have : 2 * π * k / n * (x + n) = 2 * π * k / n * x + k * (2 * π) := by
    field_simp
  rw [this, cos_add_int_mul_two_pi]

/-- Primeiro autovalor positivo de `C₁₀`: `2 − 2cos(2π/10) = (3 − √5)/2`. -/
theorem lambda1_C10 : 2 - 2 * cos (2 * π / 10) = (3 - √5) / 2 := by
  have : 2 * π / 10 = π / 5 := by ring
  rw [this, cos_pi_div_five]
  ring

theorem lambda1_C10_pos : 0 < (3 - √5) / 2 := by
  have h : √5 < 3 := by
    rw [show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
    exact sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-- Para `T = I − L/4`: `μₖ = 1 − λₖ/4 = cos²(πk/10)`. -/
theorem mu_C10 (k : ℝ) : 1 - (2 - 2 * cos (2 * π * k / 10)) / 4 = cos (π * k / 10) ^ 2 := by
  have : 2 * π * k / 10 = 2 * (π * k / 10) := by ring
  rw [this, cos_two_mul]
  ring

/-- Taxa de contração em `C₁₀`: `q = cos²(π/10) = (5 + √5)/8`. -/
theorem q_C10 : cos (π / 10) ^ 2 = (5 + √5) / 8 := by
  have h := cos_sq (π / 10)
  have : 2 * (π / 10) = π / 5 := by ring
  rw [this, cos_pi_div_five] at h
  rw [h]
  ring

theorem q_C10_lt_one : (5 + √5) / 8 < 1 := by
  have := lambda1_C10_pos
  linarith

theorem q_C10_pos : 0 < (5 + √5) / 8 := by positivity

/-! ## 5. Invariância e contração -/

/-- `f` preserva o invariante `I`. -/
def Preserva {α β : Type*} (I : α → β) (f : α → α) : Prop := ∀ x, I (f x) = I x

theorem preserva_id {α β : Type*} (I : α → β) : Preserva I id := fun _ => rfl

theorem preserva_comp {α β : Type*} {I : α → β} {f g : α → α}
    (hf : Preserva I f) (hg : Preserva I g) : Preserva I (f ∘ g) :=
  fun x => (hf (g x)).trans (hg x)

/-- `‖Tⁿx‖ ≤ qⁿ‖x‖`. -/
theorem contracao_iterada {E : Type*} [SeminormedAddCommGroup E] (T : E → E) {q : ℝ}
    (hq : 0 ≤ q) (h : ∀ x, ‖T x‖ ≤ q * ‖x‖) (n : ℕ) (x : E) : ‖T^[n] x‖ ≤ q ^ n * ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    calc ‖T (T^[n] x)‖ ≤ q * ‖T^[n] x‖ := h _
      _ ≤ q * (q ^ n * ‖x‖) := mul_le_mul_of_nonneg_left ih hq
      _ = q ^ n * q * ‖x‖ := by ring

/-- Com `q < 1`, o resíduo `Tⁿx` tende a zero. -/
theorem contracao_tende_zero {E : Type*} [SeminormedAddCommGroup E] (T : E → E) {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) (h : ∀ x, ‖T x‖ ≤ q * ‖x‖) (x : E) :
    Tendsto (fun n => ‖T^[n] x‖) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ => q ^ n * ‖x‖) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const ‖x‖
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => contracao_iterada T hq h n x) hlim

/-- Um defeito invariante **e** estritamente contraído por `T` já é zero: invariância + contração
não criam o zero, só o detectam. -/
theorem invariante_contraido_zero {α : Type*} {d : α → ℝ} {T : α → α} {q : ℝ} (hq : q < 1)
    (hd : ∀ x, 0 ≤ d x) (hinv : Preserva d T) (hc : ∀ x, d (T x) ≤ q * d x) (x : α) :
    d x = 0 := by
  have h1 := hc x
  rw [hinv x] at h1
  have h2 := hd x
  nlinarith

/-! ## 6. Zero, seta e infinitésimo -/

theorem dez_pot_pos (N : ℕ) : (0 : ℝ) < (1 / 10) ^ N := by positivity

/-- `10⁻ᴺ → 0`: cada termo é positivo, o limite é exatamente zero. -/
theorem dez_pot_tende_zero : Tendsto (fun N : ℕ => ((1 : ℝ) / 10) ^ N) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Contraexemplo: `1/5 + 1/(N+1)` é positivo e decrescente, mas tende a `1/5 ≠ 0`. -/
theorem positivo_decrescente_nao_basta :
    (∀ N : ℕ, 0 < (1 : ℝ) / 5 + 1 / ((N : ℝ) + 1)) ∧
    Antitone (fun N : ℕ => (1 : ℝ) / 5 + 1 / ((N : ℝ) + 1)) ∧
    Tendsto (fun N : ℕ => (1 : ℝ) / 5 + 1 / ((N : ℝ) + 1)) atTop (𝓝 (1 / 5)) ∧
    ¬ Tendsto (fun N : ℕ => (1 : ℝ) / 5 + 1 / ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => (1 : ℝ) / 5 + 1 / ((N : ℝ) + 1)) atTop (𝓝 (1 / 5)) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add ((1 : ℝ) / 5)
  refine ⟨fun N => by positivity, fun a b hab => ?_, hlim, fun h0 => ?_⟩
  · have : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hab 1
    have := one_div_le_one_div_of_le (by positivity) this
    linarith
  · have := tendsto_nhds_unique hlim h0
    norm_num at this

/-- `10⁻ᴴ` para o hiperinteiro infinito `H = [n ↦ n]`. -/
noncomputable def dezMenosH : ℝ* := Hyperreal.ofSeq fun n => ((1 : ℝ) / 10) ^ n

/-- `10⁻ᴴ > 0` e a sua parte padrão é `0`: infinitesimal positivo. -/
theorem dezMenosH_infinitesimal :
    0 < dezMenosH ∧ ArchimedeanClass.stdPart dezMenosH = 0 := by
  constructor
  · have : (0 : ℝ*) = Hyperreal.ofSeq fun _ => (0 : ℝ) := rfl
    rw [dezMenosH, this, Hyperreal.ofSeq_lt_ofSeq]
    exact Eventually.of_forall fun n => dez_pot_pos n
  · apply Hyperreal.stdPart_of_tendsto
    rw [dezMenosH, Hyperreal.tendsto_ofSeq]
    exact dez_pot_tende_zero.mono_left
      (Filter.hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le)

/-- O primeiro erro do texto: `E₁ = 1 − ln 2 ∈ (0,3068528192; 0,3068528197)`. -/
theorem E1_intervalo :
    (0.3068528192 : ℝ) < 1 - Real.log 2 ∧ 1 - Real.log 2 < 0.3068528197 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-! ## 7. Defeitos dos outros problemas -/

/-- YM: defeito de gap `d_δ(Δ) = max(0, δ − Δ)`; zero **se e só se** `Δ ≥ δ`. -/
theorem defeito_gap_zero_iff (δ Δ : ℝ) : max 0 (δ - Δ) = 0 ↔ δ ≤ Δ := by
  constructor
  · intro h
    have := le_max_right 0 (δ - Δ)
    linarith
  · intro h
    exact max_eq_left (by linarith)

theorem defeito_gap_exemplo : max (0 : ℝ) (1 / 2 - 1) = 0 := by norm_num

/-- O espectro `{1/(n+1)}` acumula em `0`: para todo `δ > 0` há energia em `(0, δ)` — sem gap. -/
theorem espectro_sem_gap {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < 1 / ((n : ℝ) + 1) ∧ 1 / ((n : ℝ) + 1) < δ := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  exact ⟨n, by positivity, hn⟩

/-- RH: uma cota `0 ≤ D_N ≤ K / log(N + 2)` força `D_N → 0`. -/
theorem cota_log_fecha {D : ℕ → ℝ} {K : ℝ} (h0 : ∀ N, 0 ≤ D N)
    (h : ∀ N, D N ≤ K / Real.log ((N : ℝ) + 2)) : Tendsto D atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  exact squeeze_zero h0 h (tendsto_const_nhds.div_atTop hlog)

/-- RH: uma aproximação geométrica `0 ≤ D_N ≤ C qᴺ`, `0 ≤ q < 1`, força `D_N → 0`. -/
theorem cota_geometrica_fecha {D : ℕ → ℝ} {C q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (h0 : ∀ N, 0 ≤ D N) (h : ∀ N, D N ≤ C * q ^ N) : Tendsto D atTop (𝓝 0) := by
  have : Tendsto (fun N : ℕ => C * q ^ N) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).const_mul C
  exact squeeze_zero h0 h this

/-- NS: `y(t) = (1 − 2t)^(−1/2)` resolve `y' = y³` para `t < 1/2`. -/
theorem riccati_solucao {t : ℝ} (ht : t < 1 / 2) :
    HasDerivAt (fun s => (1 - 2 * s) ^ (-(1 / 2 : ℝ))) (((1 - 2 * t) ^ (-(1 / 2 : ℝ))) ^ 3) t := by
  have hpos : 0 < 1 - 2 * t := by linarith
  have hg : HasDerivAt (fun s : ℝ => 1 - 2 * s) (-2) t := by
    simpa using ((hasDerivAt_id t).const_mul 2).const_sub 1
  have h := hg.rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hpos.ne')
  convert h using 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
  norm_num

/-- NS: a solução de `y' = y³` explode quando `t → 1/2⁻`. -/
theorem riccati_explode :
    Tendsto (fun s : ℝ => (1 - 2 * s) ^ (-(1 / 2 : ℝ))) (𝓝[<] (1 / 2)) atTop := by
  have h1 : Tendsto (fun s : ℝ => 1 - 2 * s) (𝓝[<] (1 / 2)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun s : ℝ => 1 - 2 * s) (𝓝 (1 / 2)) (𝓝 (1 - 2 * (1 / 2))) :=
        (continuous_const.sub (continuous_const.mul continuous_id)).tendsto _
      norm_num at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_Ioi]
      have : s < 1 / 2 := hs
      linarith
  exact (tendsto_rpow_neg_nhdsGT_zero (by norm_num)).comp h1

/-- BSD (versão em ℤ): defeito inteiro `|a − b| < 1` fecha a igualdade. -/
theorem fechamento_inteiro_int {a b : ℤ} (h : |(a : ℝ) - b| < 1) : a = b := by
  have h' : |a - b| < 1 := by exact_mod_cast h
  rw [abs_lt] at h'
  omega

/-! ## 8. A atribuição simbólica letra → problema (dado, não ponte) -/

/-- Os oito problemas do programa (sete abertos + Poincaré, já demonstrado). -/
inductive Problema
  | rh | pnp | ns | ym | hodge | bsd | beal | poincare
  deriving DecidableEq, Repr

open Problema in
instance : Fintype Problema :=
  ⟨{rh, pnp, ns, ym, hodge, bsd, beal, poincare}, fun x => by cases x <;> decide⟩

open Letra in
/-- A tabela do documento (camada `SYMBOLIC`). -/
def letrasDe : Problema → Finset Letra
  | .rh => {alef, zayin, kaf, ayin, qof, tav}
  | .pnp => {bet, gimel, he, nun, pe, tav}
  | .ns => {dalet, lamed, mem, samekh, shin, tav}
  | .ym => {vav, tet, samekh, ayin, shin, tav}
  | .hodge => {gimel, vav, tav}
  | .bsd => {tsadi, qof, resh, tav}
  | .beal => {yod, tav}
  | .poincare => {alef, dalet, chet, tav}

/-- A tabela cobre as 22 letras. -/
theorem letras_cobertas : ∀ l : Letra, ∃ p, l ∈ letrasDe p := by decide

/-- `ת` (fechamento, certificação) aparece nos oito problemas. -/
theorem tav_em_todos : ∀ p, Letra.tav ∈ letrasDe p := by decide

end ATK.TerceiroTemplo

#print axioms ATK.TerceiroTemplo.card_letras
#print axioms ATK.TerceiroTemplo.card_maes
#print axioms ATK.TerceiroTemplo.card_duplas
#print axioms ATK.TerceiroTemplo.card_simples
#print axioms ATK.TerceiroTemplo.familias_particionam
#print axioms ATK.TerceiroTemplo.gematria_injetiva
#print axioms ATK.TerceiroTemplo.gematria_soma
#print axioms ATK.TerceiroTemplo.gematria_maes
#print axioms ATK.TerceiroTemplo.portas_231
#print axioms ATK.TerceiroTemplo.portas_eq_choose
#print axioms ATK.TerceiroTemplo.caminhos_32
#print axioms ATK.TerceiroTemplo.card_sefirot
#print axioms ATK.TerceiroTemplo.caminho_sem_laco
#print axioms ATK.TerceiroTemplo.caminho_sem_repeticao
#print axioms ATK.TerceiroTemplo.arvore_conexa
#print axioms ATK.TerceiroTemplo.betti_um
#print axioms ATK.TerceiroTemplo.energia_nonneg
#print axioms ATK.TerceiroTemplo.forma_laplaciano
#print axioms ATK.TerceiroTemplo.lap_psd
#print axioms ATK.TerceiroTemplo.energiaArvore_nonneg
#print axioms ATK.TerceiroTemplo.energiaArvore_zero_iff
#print axioms ATK.TerceiroTemplo.ciclo_autovetor
#print axioms ATK.TerceiroTemplo.ciclo_periodico
#print axioms ATK.TerceiroTemplo.lambda1_C10
#print axioms ATK.TerceiroTemplo.lambda1_C10_pos
#print axioms ATK.TerceiroTemplo.mu_C10
#print axioms ATK.TerceiroTemplo.q_C10
#print axioms ATK.TerceiroTemplo.q_C10_lt_one
#print axioms ATK.TerceiroTemplo.q_C10_pos
#print axioms ATK.TerceiroTemplo.preserva_id
#print axioms ATK.TerceiroTemplo.preserva_comp
#print axioms ATK.TerceiroTemplo.contracao_iterada
#print axioms ATK.TerceiroTemplo.contracao_tende_zero
#print axioms ATK.TerceiroTemplo.invariante_contraido_zero
#print axioms ATK.TerceiroTemplo.dez_pot_pos
#print axioms ATK.TerceiroTemplo.dez_pot_tende_zero
#print axioms ATK.TerceiroTemplo.positivo_decrescente_nao_basta
#print axioms ATK.TerceiroTemplo.dezMenosH_infinitesimal
#print axioms ATK.TerceiroTemplo.E1_intervalo
#print axioms ATK.TerceiroTemplo.defeito_gap_zero_iff
#print axioms ATK.TerceiroTemplo.defeito_gap_exemplo
#print axioms ATK.TerceiroTemplo.espectro_sem_gap
#print axioms ATK.TerceiroTemplo.cota_log_fecha
#print axioms ATK.TerceiroTemplo.cota_geometrica_fecha
#print axioms ATK.TerceiroTemplo.riccati_solucao
#print axioms ATK.TerceiroTemplo.riccati_explode
#print axioms ATK.TerceiroTemplo.fechamento_inteiro_int
#print axioms ATK.TerceiroTemplo.letras_cobertas
#print axioms ATK.TerceiroTemplo.tav_em_todos
