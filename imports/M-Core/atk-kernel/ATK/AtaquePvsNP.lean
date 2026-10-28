/-
ATK — Programa de ataque, frente P vs NP: cotas inferiores de circuitos para linguagens.

Liga as linguagens do modelo genuíno (`ATK.LigacaoPNP`, `Linguagem = Set (List Bool)`) ao modelo
de circuitos de `ATK.Shannon`:

* `fatia L n : (Fin n → Bool) → Bool` — a função booleana de `L` nas palavras de tamanho `n`;
* `CotaInferior L s`: para `n` grande, `L` em tamanho `n` não tem circuito com `≤ s(n)` portas;
  **`cota_mono`**: cotas maiores implicam menores;
* `EmPpoly L`: circuitos de tamanho polinomial; **`naoPpoly_de_cotas`**: cotas inferiores
  superpolinomiais ⇒ `L ∉ P/poly`;
* `PemPpoly` (**ponte publicada**: Savage 1972, Pippenger–Fischer 1979 — máquinas de tempo
  polinomial têm circuitos de tamanho polinomial) e **`p_ne_np_de_ppoly`**:
  `PemPpoly ∧ (∃ L ∈ NP, L ∉ P/poly) ⇒ P ≠ NP`;
* **alvo da fronteira** `FronteiraLinear α`: alguma `L ∈ NP` exige `> α·n` portas (o recorde
  explícito conhecido é `α ≈ 3,1`); **`fronteira_mono`**: a fronteira para `α` implica a de
  `α' ≤ α`.

Nada aqui decide P vs NP (O4 continua `OPEN_MATH`).
-/
import ATK.LigacaoPNP
import ATK.Shannon

namespace ATK.AtaquePvsNP

open ATK.LigacaoPNP ATK.Shannon Filter

open Classical in
/-- A função booleana de `L` nas palavras de tamanho `n`. -/
noncomputable def fatia (L : Linguagem) (n : ℕ) : (Fin n → Bool) → Bool :=
  fun x => decide (List.ofFn x ∈ L)

/-- Cota inferior de circuitos para `L`: eventualmente nenhum circuito com `≤ s n` portas. -/
def CotaInferior (L : Linguagem) (s : ℕ → ℕ) : Prop :=
  ∀ᶠ n in atTop, ¬ TemCircuito (fatia L n) (s n)

theorem cota_mono {L : Linguagem} {s t : ℕ → ℕ} (h : CotaInferior L s) (hts : ∀ n, t n ≤ s n) :
    CotaInferior L t := by
  filter_upwards [h] with n hn ht
  exact hn (temCircuito_mono (hts n) ht)

/-- `L ∈ P/poly`: circuitos de tamanho polinomial em todo tamanho. -/
def EmPpoly (L : Linguagem) : Prop := ∃ k : ℕ, ∀ n, TemCircuito (fatia L n) (n ^ k + k)

/-- Cotas superpolinomiais ⇒ `L ∉ P/poly`. -/
theorem naoPpoly_de_cotas {L : Linguagem} (h : ∀ k : ℕ, CotaInferior L fun n => n ^ k + k) :
    ¬ EmPpoly L := by
  rintro ⟨k, hk⟩
  obtain ⟨n, hn⟩ := (h k).exists
  exact hn (hk n)

/-- **Ponte publicada** (Savage; Pippenger–Fischer): `P ⊆ P/poly`. -/
def PemPpoly : Prop := ∀ L ∈ classeP, EmPpoly L

/-- `NP ⊄ P/poly`. -/
def NPnaoEmPpoly : Prop := ∃ L ∈ classeNP, ¬ EmPpoly L

/-- **`P ⊆ P/poly` e `NP ⊄ P/poly` ⇒ `P ≠ NP`.** -/
theorem p_ne_np_de_ppoly (hP : PemPpoly) (hN : NPnaoEmPpoly) : PneNP := by
  obtain ⟨L, hL, hnp⟩ := hN
  intro h
  rw [← h] at hL
  exact hnp (hP L hL)

/-- **Alvo da fronteira**: alguma linguagem de NP exige mais que `α·n` portas. -/
def FronteiraLinear (α : ℚ) : Prop :=
  ∃ L ∈ classeNP, CotaInferior L fun n => ⌊α * n⌋₊

theorem fronteira_mono {α α' : ℚ} (h : α' ≤ α) (hF : FronteiraLinear α) : FronteiraLinear α' := by
  obtain ⟨L, hL, hc⟩ := hF
  refine ⟨L, hL, cota_mono hc fun n => Nat.floor_le_floor ?_⟩
  exact mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n)

/-- A fronteira superpolinomial em NP já decide P vs NP (com a ponte). -/
theorem p_ne_np_de_cotas (hP : PemPpoly) {L : Linguagem} (hL : L ∈ classeNP)
    (h : ∀ k : ℕ, CotaInferior L fun n => n ^ k + k) : PneNP :=
  p_ne_np_de_ppoly hP ⟨L, hL, naoPpoly_de_cotas h⟩

end ATK.AtaquePvsNP

#print axioms ATK.AtaquePvsNP.cota_mono
#print axioms ATK.AtaquePvsNP.naoPpoly_de_cotas
#print axioms ATK.AtaquePvsNP.p_ne_np_de_ppoly
#print axioms ATK.AtaquePvsNP.fronteira_mono
#print axioms ATK.AtaquePvsNP.p_ne_np_de_cotas
