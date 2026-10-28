import ATK.Shannon
import Mathlib.Data.List.GetD

/-!
# ATK — Obrigação O4: uma cota inferior **explícita** (linear) de circuitos

`ATK.Shannon` prova, por contagem, que existem funções de `n` bits que exigem `2ⁿ/(8n)` portas — sem
exibir nenhuma. Do lado explícito, o que se prova com um argumento direto é linear:

* `computa_update`: se nenhuma porta lê a entrada `i` (e a saída não é a própria entrada `i`), o
  circuito não depende de `xᵢ`;
* `cota_linear`: **toda função que depende das `n` entradas exige `s ≥ (n − 1)/2` portas**
  (`n ≤ 2s + 1`), no modelo de circuitos de `ATK.Shannon` (portas de entrada dupla);
* `ou_cota`: em particular `OUₙ(x) = x₀ ∨ … ∨ x_{n−1}` (função explícita) exige `n ≤ 2s + 1`.

Esta é a situação real da teoria: as melhores cotas inferiores explícitas conhecidas para circuitos
booleanos gerais são lineares (≈ `5n`), enquanto O4 (`SAT ∉ P`, equivalente a `P ≠ NP` dada B4) pede
uma família em NP com cota **superpolinomial**. O4 continua `OPEN_MATH`.
-/

namespace ATK.CircuitoExplicito

open ATK.Shannon

/-- Um passo da avaliação. -/
def passo (v : List Bool) (g : Op × ℕ × ℕ) : List Bool :=
  v ++ [g.1.ap (v.getD g.2.1 false) (v.getD g.2.2 false)]

theorem avalia_cons (g : Op × ℕ × ℕ) (G : List (Op × ℕ × ℕ)) (v : List Bool) :
    avalia (g :: G) v = avalia G (passo v g) := rfl

theorem avalia_nil (v : List Bool) : avalia [] v = v := rfl

theorem getLastD_eq_getD (l : List Bool) (d : Bool) : l.getLastD d = l.getD (l.length - 1) d := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

/-- `v` e `v'` coincidem fora do índice `i`. -/
def ForaDe (i : ℕ) (v v' : List Bool) : Prop :=
  v.length = v'.length ∧ ∀ j, j ≠ i → v.getD j false = v'.getD j false

theorem foraDe_passo {i : ℕ} {v v' : List Bool} (h : ForaDe i v v') (g : Op × ℕ × ℕ)
    (h1 : g.2.1 ≠ i) (h2 : g.2.2 ≠ i) : ForaDe i (passo v g) (passo v' g) := by
  obtain ⟨hl, he⟩ := h
  refine ⟨by simp [passo, hl], fun j hj => ?_⟩
  simp only [passo]
  rw [he g.2.1 h1, he g.2.2 h2]
  rcases lt_trichotomy j v.length with hlt | heq | hgt
  · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hl ▸ hlt), he j hj]
  · subst heq
    rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ (hl ▸ le_rfl)]
    simp [hl]
  · rw [List.getD_append_right _ _ _ _ hgt.le, List.getD_append_right _ _ _ _ (hl ▸ hgt.le)]
    simp only [List.getD_eq_getElem?_getD, hl]

theorem foraDe_avalia {i : ℕ} (G : List (Op × ℕ × ℕ)) (hG : ∀ g ∈ G, g.2.1 ≠ i ∧ g.2.2 ≠ i)
    {v v' : List Bool} (h : ForaDe i v v') : ForaDe i (avalia G v) (avalia G v') := by
  induction G generalizing v v' with
  | nil => exact h
  | cons g G ih =>
    rw [avalia_cons, avalia_cons]
    have hg := hG g (List.mem_cons_self ..)
    exact ih (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg')) (foraDe_passo h g hg.1 hg.2)

theorem length_avalia (G : List (Op × ℕ × ℕ)) (v : List Bool) :
    (avalia G v).length = v.length + G.length := by
  induction G generalizing v with
  | nil => simp [avalia_nil]
  | cons g G ih => rw [avalia_cons, ih]; simp [passo]; ring

/-- Se nenhuma porta lê a entrada `i` e a saída não é a entrada `i`, o circuito não depende de
`xᵢ`. -/
theorem computa_update {n s : ℕ} (C : Circuito n s) (i : Fin n)
    (hC : ∀ k, ((C k).2.1 : ℕ) ≠ i ∧ ((C k).2.2 : ℕ) ≠ i) (hs : 0 < s ∨ (i : ℕ) ≠ n - 1)
    (x : Fin n → Bool) (b : Bool) : C.computa (Function.update x i b) = C.computa x := by
  have hF : ForaDe i (List.ofFn (Function.update x i b)) (List.ofFn x) := by
    refine ⟨by simp, fun j hj => ?_⟩
    by_cases hjn : j < n
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      have hne : (⟨j, hjn⟩ : Fin n) ≠ i := fun h => hj (by rw [← h])
      simp [hjn, Function.update_of_ne hne]
    · simp [List.getD_eq_getElem?_getD, hjn]
  have hG : ∀ g ∈ List.ofFn (fun k => ((C k).1, ((C k).2.1 : ℕ), ((C k).2.2 : ℕ))),
      g.2.1 ≠ i ∧ g.2.2 ≠ i := by
    intro g hg
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hg
    exact hC k
  have hA := foraDe_avalia _ hG hF
  unfold Circuito.computa
  rw [getLastD_eq_getD, getLastD_eq_getD, hA.1]
  apply hA.2
  rw [length_avalia]
  simp only [List.length_ofFn]
  omega

/-- `f` depende da entrada `i`. -/
def Depende {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x

/-- **Cota inferior linear explícita**: se `f` depende das `n` entradas, todo circuito para `f` tem
`s` portas com `n ≤ 2s + 1`. -/
theorem cota_linear {n s : ℕ} {f : (Fin n → Bool) → Bool} (hf : ∀ i, Depende f i)
    (C : Circuito n s) (hC : C.computa = f) : n ≤ 2 * s + 1 := by
  classical
  -- os índices lidos pelas portas
  set L : Finset ℕ := Finset.univ.image (fun k : Fin s => ((C k).2.1 : ℕ)) ∪
    Finset.univ.image (fun k : Fin s => ((C k).2.2 : ℕ)) with hL
  have hLcard : L.card ≤ 2 * s := by
    calc L.card ≤ (Finset.univ.image (fun k : Fin s => ((C k).2.1 : ℕ))).card +
          (Finset.univ.image (fun k : Fin s => ((C k).2.2 : ℕ))).card := Finset.card_union_le _ _
      _ ≤ s + s := add_le_add (Finset.card_image_le.trans (by simp))
          (Finset.card_image_le.trans (by simp))
      _ = 2 * s := by ring
  -- toda entrada `i < n − 1` é lida por alguma porta
  have hsub : Finset.range (n - 1) ⊆ L := by
    intro j hj
    rw [Finset.mem_range] at hj
    by_contra hjL
    have hjn : j < n := by omega
    obtain ⟨x, hx⟩ := hf ⟨j, hjn⟩
    apply hx
    rw [← hC]
    refine computa_update C ⟨j, hjn⟩ (fun k => ⟨?_, ?_⟩) (Or.inr (by simp; omega)) x _
    · intro h; apply hjL; rw [hL]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, by simp, h⟩)
    · intro h; apply hjL; rw [hL]; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, by simp, h⟩)
  have := (Finset.card_le_card hsub).trans hLcard
  simp only [Finset.card_range] at this
  omega

/-- `OUₙ`: o ou de todas as entradas. -/
def ou (n : ℕ) (x : Fin n → Bool) : Bool := decide (∃ i, x i = true)

theorem ou_depende (n : ℕ) (i : Fin n) : Depende (ou n) i := by
  refine ⟨fun _ => false, ?_⟩
  simp only [ou, Bool.not_false]
  have h1 : (∃ j, Function.update (fun _ => false) i true j = true) := ⟨i, by simp⟩
  have h2 : ¬ ∃ j : Fin n, (fun _ => false) j = true := by simp
  simp [h1]

/-- **Teste explícito**: todo circuito para `OUₙ` tem `n ≤ 2s + 1`. -/
theorem ou_cota {n s : ℕ} (C : Circuito n s) (hC : C.computa = ou n) : n ≤ 2 * s + 1 :=
  cota_linear (ou_depende n) C hC

end ATK.CircuitoExplicito

#print axioms ATK.CircuitoExplicito.avalia_cons
#print axioms ATK.CircuitoExplicito.avalia_nil
#print axioms ATK.CircuitoExplicito.getLastD_eq_getD
#print axioms ATK.CircuitoExplicito.foraDe_passo
#print axioms ATK.CircuitoExplicito.foraDe_avalia
#print axioms ATK.CircuitoExplicito.length_avalia
#print axioms ATK.CircuitoExplicito.computa_update
#print axioms ATK.CircuitoExplicito.cota_linear
#print axioms ATK.CircuitoExplicito.ou_depende
#print axioms ATK.CircuitoExplicito.ou_cota
