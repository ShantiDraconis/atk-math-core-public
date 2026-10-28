import ATK.CookLevinTableau

/-!
# ATK — Cook–Levin, marco CL3c: a linha inicial com certificado livre

A entrada de um verificador NP é `par w c`: um prefixo fixo (dependente de `w`) seguido do
certificado `c`, de comprimento variável `≤ m`. Na linha 0 do tableau:

* `iniF`: rótulo e estado iniciais, pilhas vazias fora de `k₀`; na pilha `k₀`, o prefixo `E` fixo,
  depois `m` células livres, cada uma `none` ou um bit, com `none` hereditário (`none` em `p` força
  `none` em `p+1`), e `none` daí em diante;
* `ini_sat`: a configuração inicial de qualquer certificado `c` com `|c| ≤ m` satisfaz `iniF`;
* `ini_dec`: de toda valoração que satisfaz `iniF` (e a unicidade da linha 0) lê-se um certificado
  `c` com `|c| ≤ m` cuja configuração inicial é a linha 0.

São as hipóteses `hI1`/`hI2` de `tableau_correto`. **CLOSED_MATH continua false.**
-/

namespace ATK.CookLevinInicio

open Turing Function ATK.CookLevinTableau

set_option linter.unusedSectionVars false

noncomputable section

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} [∀ k, Fintype (Γ k)]
  [∀ k, DecidableEq (Γ k)] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {σ : Type} [Fintype σ]
  [DecidableEq σ]

variable (k₀ : K) (E : List (Γ k₀)) (g : Bool → Γ k₀) (m : ℕ) (main : Λ) (s₀ : σ)

/-- A configuração inicial com certificado `c`. -/
def cfgIni (c : List Bool) : TM2.Cfg Γ Λ σ :=
  ⟨some main, s₀, update (fun _ => []) k₀ (E ++ c.map g)⟩

/-- As configurações iniciais permitidas: certificados de comprimento `≤ m`. -/
def Ini : Set (TM2.Cfg Γ Λ σ) := {C | ∃ c : List Bool, c.length ≤ m ∧ C = cfgIni k₀ E g main s₀ c}

/-- A fórmula da linha inicial. -/
def iniF (S : ℕ) : Fm (Var K Γ Λ σ) :=
  [(Var.lab 0 (some main), true)] :: [(Var.st 0 s₀, true)] ::
  (((todos K).flatMap fun k =>
      if k = k₀ then [] else (List.range S).map fun p => [(Var.cel 0 k p none, true)]) ++
    ((List.range E.length).map fun p => [(Var.cel 0 k₀ p E[p]?, true)]) ++
    ((List.range m).map fun i =>
      [(Var.cel 0 k₀ (E.length + i) none, true), (Var.cel 0 k₀ (E.length + i) (some (g false)), true),
        (Var.cel 0 k₀ (E.length + i) (some (g true)), true)]) ++
    ((List.range m).map fun i =>
      [(Var.cel 0 k₀ (E.length + i) none, false), (Var.cel 0 k₀ (E.length + i + 1) none, true)]) ++
    ((List.range (S - (E.length + m))).map fun i =>
      [(Var.cel 0 k₀ (E.length + m + i) none, true)]))

variable {k₀ E g m main s₀}

theorem cfgIni_k₀ (c : List Bool) : (cfgIni (Λ := Λ) k₀ E g main s₀ c).stk k₀ = E ++ c.map g := by
  simp [cfgIni]

theorem cfgIni_ne {k : K} (hk : k ≠ k₀) (c : List Bool) :
    (cfgIni (Λ := Λ) k₀ E g main s₀ c).stk k = [] := by
  simp [cfgIni, update_of_ne hk]

theorem sat_iniF {τ : Var K Γ Λ σ → Bool} {S : ℕ} :
    Sat τ (iniF k₀ E g m main s₀ S) ↔
      τ (Var.lab 0 (some main)) = true ∧ τ (Var.st 0 s₀) = true ∧
      (∀ k, k ≠ k₀ → ∀ p < S, τ (Var.cel 0 k p none) = true) ∧
      (∀ p < E.length, τ (Var.cel 0 k₀ p E[p]?) = true) ∧
      (∀ i < m, τ (Var.cel 0 k₀ (E.length + i) none) = true ∨
        τ (Var.cel 0 k₀ (E.length + i) (some (g false))) = true ∨
        τ (Var.cel 0 k₀ (E.length + i) (some (g true))) = true) ∧
      (∀ i < m, τ (Var.cel 0 k₀ (E.length + i) none) = true →
        τ (Var.cel 0 k₀ (E.length + i + 1) none) = true) ∧
      (∀ i < S - (E.length + m), τ (Var.cel 0 k₀ (E.length + m + i) none) = true) := by
  simp only [iniF, sat_cons, sat_append, sat_map, sat_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  have hk : (∀ x ∈ todos K, Sat τ (if x = k₀ then [] else (List.range S).map fun p =>
      [(Var.cel 0 x p (none : Option (Γ x)), true)])) ↔
      ∀ k, k ≠ k₀ → ∀ p < S, τ (Var.cel 0 k p none) = true := by
    constructor
    · intro h k hk p hp
      have := h k (mem_todos k)
      simp only [hk, ↓reduceIte, sat_map] at this
      simpa using this p (List.mem_range.mpr hp)
    · intro h k _
      split_ifs with hk
      · exact sat_nil τ
      · rw [sat_map]
        intro p hp
        simpa using h k hk p (List.mem_range.mp hp)
  rw [hk]
  constructor
  · rintro ⟨h1, h2, ⟨⟨⟨⟨h3, h4⟩, h5⟩, h6⟩, h7⟩⟩
    refine ⟨h1, h2, h3, h4, h5, fun i hi hn => ?_, h7⟩
    rcases h6 i hi with h | h
    · rw [h] at hn; exact absurd hn (by decide)
    · exact h
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨h1, h2, ⟨⟨⟨⟨h3, h4⟩, h5⟩, fun i hi => ?_⟩, h7⟩⟩
    cases hn : τ (Var.cel 0 k₀ (E.length + i) none)
    · exact Or.inl rfl
    · exact Or.inr (h6 i hi hn)

/-- **A linha inicial de um certificado satisfaz `iniF`.** -/
theorem ini_sat {τ : Var K Γ Λ σ → Bool} {S : ℕ} {c : List Bool} (hc : c.length ≤ m)
    (hS : E.length + m < S) (h : Linha τ 0 S (cfgIni k₀ E g main s₀ c)) :
    Sat τ (iniF k₀ E g m main s₀ S) := by
  obtain ⟨hl, hv, hcel⟩ := h
  have hk₀ : ∀ p < S, ∀ a, τ (Var.cel 0 k₀ p a) = decide (a = (E ++ c.map g)[p]?) := by
    intro p hp a
    rw [hcel k₀ p hp a, cfgIni_k₀]
  rw [sat_iniF]
  refine ⟨by rw [hl]; simp [cfgIni], by rw [hv]; simp [cfgIni], fun k hk p hp => ?_,
    fun p hp => ?_, fun i hi => ?_, fun i hi hn => ?_, fun i hi => ?_⟩
  · rw [hcel k p hp, cfgIni_ne hk]; simp
  · rw [hk₀ p (by omega), List.getElem?_append_left hp]; simp
  · rw [hk₀ _ (by omega), hk₀ _ (by omega), hk₀ _ (by omega),
      List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left, List.getElem?_map]
    rcases hci : c[i]? with _ | b
    · simp
    · cases b <;> simp
  · rw [hk₀ _ (by omega), List.getElem?_append_right (by omega)] at hn
    rw [hk₀ _ (by omega), List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left, List.getElem?_map, decide_eq_true_eq] at hn ⊢
    have : c.length ≤ i := by
      by_contra h'
      rw [List.getElem?_eq_getElem (by omega)] at hn
      simp at hn
    rw [show E.length + i + 1 - E.length = i + 1 by omega, List.getElem?_eq_none (by omega)]
    simp
  · rw [hk₀ _ (by omega), List.getElem?_append_right (by omega),
      List.getElem?_eq_none (by simp; omega)]
    simp

/-- A leitura do certificado: célula por célula, até o primeiro `none`. -/
def dec (τ : Var K Γ Λ σ → Bool) : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, i =>
    if τ (Var.cel 0 k₀ (E.length + i) none) then []
    else τ (Var.cel 0 k₀ (E.length + i) (some (g true))) :: dec τ n (i + 1)

omit [Fintype K] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [Fintype Λ] [DecidableEq Λ]
  [Fintype σ] [DecidableEq σ] in
theorem dec_length (τ : Var K Γ Λ σ → Bool) : ∀ n i, (dec (k₀ := k₀) (E := E) (g := g) τ n i).length ≤ n
  | 0, _ => by simp [dec]
  | n + 1, i => by
    simp only [dec]
    split_ifs
    · simp
    · simpa using dec_length τ n (i + 1)

omit [Fintype K] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [Fintype Λ] [DecidableEq Λ]
  [Fintype σ] [DecidableEq σ] in
theorem dec_get (τ : Var K Γ Λ σ → Bool)
    (mono : ∀ i < m, τ (Var.cel 0 k₀ (E.length + i) none) = true →
      τ (Var.cel 0 k₀ (E.length + i + 1) none) = true) :
    ∀ n i, i + n ≤ m → ∀ j < n, (dec (k₀ := k₀) (E := E) (g := g) τ n i)[j]? =
      if τ (Var.cel 0 k₀ (E.length + (i + j)) none) then none
      else some (τ (Var.cel 0 k₀ (E.length + (i + j)) (some (g true))))
  | 0, _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | n + 1, i, hin, j, hj => by
    simp only [dec]
    by_cases hN : τ (Var.cel 0 k₀ (E.length + i) none) = true
    · have key : ∀ j', i + j' ≤ m → τ (Var.cel 0 k₀ (E.length + (i + j')) none) = true := by
        intro j' hj'
        induction j' with
        | zero => simpa using hN
        | succ j' ih =>
          have := mono (i + j') (by omega) (ih (by omega))
          rwa [show E.length + (i + (j' + 1)) = E.length + (i + j') + 1 by omega]
      simp only [hN, ↓reduceIte, key j (by omega)]
      simp
    · simp only [hN, ↓reduceIte, Bool.false_eq_true]
      cases j with
      | zero => simp [hN]
      | succ j =>
        simp only [List.getElem?_cons_succ]
        rw [dec_get τ mono n (i + 1) (by omega) j (by omega)]
        rw [show i + 1 + j = i + (j + 1) by omega]

/-- **A linha inicial determina um certificado.** -/
theorem ini_dec {τ : Var K Γ Λ σ → Bool} {S : ℕ} (hS : E.length + m < S)
    (hL : Sat τ (clsLinha (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) 0 S))
    (hI : Sat τ (iniF k₀ E g m main s₀ S)) :
    ∃ C ∈ Ini (Λ := Λ) k₀ E g m main s₀, Linha τ 0 S C := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := sat_iniF.mp hI
  set c := dec (k₀ := k₀) (E := E) (g := g) τ m 0 with hc
  have hlen : c.length ≤ m := dec_length τ m 0
  have hget := dec_get (g := g) τ h6 m 0 (by omega)
  refine ⟨cfgIni k₀ E g main s₀ c, ⟨c, hlen, rfl⟩, Linha.de hL h1 h2 fun k p hp => ?_⟩
  by_cases hk : k = k₀
  · subst hk
    rw [cfgIni_k₀]
    by_cases hp1 : p < E.length
    · rw [List.getElem?_append_left hp1]; exact h4 p hp1
    by_cases hp2 : p < E.length + m
    · obtain ⟨i, rfl⟩ : ∃ i, p = E.length + i := ⟨p - E.length, by omega⟩
      rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, List.getElem?_map,
        hget i (by omega)]
      simp only [Nat.zero_add]
      by_cases hN : τ (Var.cel 0 k (E.length + i) none) = true
      · simp only [hN, ↓reduceIte, Option.map_none]
      · simp only [hN, ↓reduceIte, Bool.false_eq_true, Option.map_some]
        cases hB : τ (Var.cel 0 k (E.length + i) (some (g true)))
        · rcases h5 i (by omega) with h | h | h
          · exact absurd h hN
          · exact h
          · rw [hB] at h; exact absurd h (by decide)
        · exact hB
    · obtain ⟨i, rfl⟩ : ∃ i, p = E.length + m + i := ⟨p - (E.length + m), by omega⟩
      rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega)]
      exact h7 i (by omega)
  · rw [cfgIni_ne hk]
    simpa using h3 k hk p hp

end

end ATK.CookLevinInicio

#print axioms ATK.CookLevinInicio.cfgIni
#print axioms ATK.CookLevinInicio.Ini
#print axioms ATK.CookLevinInicio.iniF
#print axioms ATK.CookLevinInicio.cfgIni_k₀
#print axioms ATK.CookLevinInicio.cfgIni_ne
#print axioms ATK.CookLevinInicio.sat_iniF
#print axioms ATK.CookLevinInicio.ini_sat
#print axioms ATK.CookLevinInicio.dec
#print axioms ATK.CookLevinInicio.dec_length
#print axioms ATK.CookLevinInicio.dec_get
#print axioms ATK.CookLevinInicio.ini_dec
