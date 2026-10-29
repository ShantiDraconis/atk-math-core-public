import ATK.Compilador

/-!
# ATK — Ponte B4, marco M2d (parte 2a): programas de laço que só emitem

Uma subclasse `Lp W c` dos programas do compilador (`ATK.Compilador.Cmd`): só `emit`, `emitU`,
`seq`, `forU` e `forBits`; escrevem apenas os contadores dos seus laços (todos em `W`) e nunca
leem um registrador de `W`. Para ela:

* `Lp.env`: os registradores fora de `W` não mudam;
* `Lp.out_congr`: a saída só depende dos registradores fora de `W`;
* **`Lp.out_forU`**: a saída de `forU x y body` é `(range (E x)).flatMap (k ↦ saída de body com y = k)`;
* `Lp.le`: cota uniforme dos registradores preservada;
* **`Lp.custo_le`**: `custo ≤ cb B c`, um polinômio em `B` (cota dos registradores e de `|w|`)
  com grau = profundidade de aninhamento;
* `Lp.wf`: boa formação para o compilador.

Nada aqui decide P vs NP. **CLOSED_MATH continua false.**
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ATK.Lacos

open ATK.Compilador Function

variable {R : ℕ}

/-- Programas de laço: só emitem; escrevem apenas os contadores dos seus laços (em `W`) e não
leem registradores de `W`. -/
inductive Lp : Finset (Fin R) → Cmd R → Prop
  | emit (W : Finset (Fin R)) (s : List Bool) : Lp W (.emit s)
  | emitU {W : Finset (Fin R)} {x : Fin R} (s : List Bool) (hx : x ∉ W) : Lp W (.emitU x s)
  | seq {W : Finset (Fin R)} {c₁ c₂ : Cmd R} (h₁ : Lp W c₁) (h₂ : Lp W c₂) : Lp W (.seq c₁ c₂)
  | forU {W : Finset (Fin R)} {x y : Fin R} {body : Cmd R} (hx : x ∉ W) (hy : y ∈ W)
      (hb : Lp (W.erase y) body) : Lp W (.forU x y body)
  | forBits {W : Finset (Fin R)} {b₀ b₁ : Cmd R} (h₀ : Lp W b₀) (h₁ : Lp W b₁) :
      Lp W (.forBits b₀ b₁)
  /-- Laço sobre os bits da entrada com contador de posição `c ∈ W` (zerado antes, incrementado
  depois de cada corpo): os corpos podem ler `c`. -/
  | bitsC {W : Finset (Fin R)} {c : Fin R} {b₀ b₁ : Cmd R} (hc : c ∈ W)
      (h₀ : Lp (W.erase c) b₀) (h₁ : Lp (W.erase c) b₁) :
      Lp W (.seq (.zero c) (.forBits (.seq b₀ (.inc c)) (.seq b₁ (.inc c))))

/-! ### Semântica dos laços com corpo "quase puro" -/

section semFor

variable (f : Env R → Env R × List Bool) (y : Fin R) (W : Finset (Fin R)) (hyW : y ∈ W)
  (henv : ∀ E r, r ∉ W.erase y → (f E).1 r = E r)
  (hout : ∀ E E', (∀ r, r ∉ W.erase y → E r = E' r) → (f E).2 = (f E').2)
include hyW henv hout

theorem semFor_env : ∀ (m : ℕ) (E : Env R) (r : Fin R), r ∉ W →
    (semFor f y m E).1 r = E r
  | 0, E, r, _ => rfl
  | m + 1, E, r, hr => by
    have hr' : r ∉ W.erase y := fun h => hr (Finset.mem_of_mem_erase h)
    have hry : r ≠ y := fun h => hr (by rw [h]; exact hyW)
    simp only [semFor]
    rw [semFor_env m _ r hr, update_of_ne hry, henv E r hr']

theorem semFor_y : ∀ (m : ℕ) (E : Env R), (semFor f y m E).1 y = E y + m
  | 0, E => rfl
  | m + 1, E => by
    simp only [semFor]
    rw [semFor_y m, update_self, henv E y (by simp)]
    ring

theorem semFor_out : ∀ (m : ℕ) (E : Env R),
    (semFor f y m E).2 = (List.range m).flatMap fun k => (f (update E y (E y + k))).2
  | 0, E => by simp [semFor]
  | m + 1, E => by
    simp only [semFor]
    rw [semFor_out m, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    congr 1
    · rw [add_zero, update_eq_self]
    · refine List.flatMap_congr fun k _ => hout _ _ fun r hr => ?_
      rcases eq_or_ne r y with rfl | hry
      · simp only [update_self]
        rw [henv E r (by simp)]
        omega
      · simp only [update_of_ne hry]
        exact henv E r hr

end semFor

section semBits

variable (f₀ f₁ : Env R → Env R × List Bool) (W : Finset (Fin R))
  (henv₀ : ∀ E r, r ∉ W → (f₀ E).1 r = E r) (henv₁ : ∀ E r, r ∉ W → (f₁ E).1 r = E r)
  (hout₀ : ∀ E E', (∀ r, r ∉ W → E r = E' r) → (f₀ E).2 = (f₀ E').2)
  (hout₁ : ∀ E E', (∀ r, r ∉ W → E r = E' r) → (f₁ E).2 = (f₁ E').2)
include henv₀ henv₁ hout₀ hout₁

theorem semBits_env : ∀ (L : List Bool) (E : Env R) (r : Fin R), r ∉ W →
    (semBits f₀ f₁ L E).1 r = E r
  | [], E, r, _ => rfl
  | b :: L, E, r, hr => by
    simp only [semBits]
    rw [semBits_env L _ r hr]
    cases b
    · exact henv₀ E r hr
    · exact henv₁ E r hr

theorem semBits_out : ∀ (L : List Bool) (E : Env R),
    (semBits f₀ f₁ L E).2 = L.flatMap fun b => ((if b then f₁ else f₀) E).2
  | [], E => by simp [semBits]
  | b :: L, E => by
    simp only [semBits, List.flatMap_cons]
    rw [semBits_out L]
    congr 1
    refine List.flatMap_congr fun b' _ => ?_
    have hagree : ∀ r, r ∉ W → ((if b then f₁ else f₀) E).1 r = E r := fun r hr => by
      cases b
      · simpa using henv₀ E r hr
      · simpa using henv₁ E r hr
    cases b'
    · simpa using hout₀ _ _ hagree
    · simpa using hout₁ _ _ hagree

end semBits

/-! ### Laço sobre os bits com contador de posição -/

section semBitsC

variable (w : List Bool) (b₀ b₁ : Cmd R) (S : Finset (Fin R)) (c : Fin R) (hcS : c ∉ S)
  (henv₀ : ∀ E r, r ∉ S → (sem w b₀ E).1 r = E r) (henv₁ : ∀ E r, r ∉ S → (sem w b₁ E).1 r = E r)
  (hout₀ : ∀ E E', (∀ r, r ∉ S → E r = E' r) → (sem w b₀ E).2 = (sem w b₀ E').2)
  (hout₁ : ∀ E E', (∀ r, r ∉ S → E r = E' r) → (sem w b₁ E).2 = (sem w b₁ E').2)

include hcS in
theorem sem_body {b : Cmd R} (henv : ∀ E r, r ∉ S → (sem w b E).1 r = E r) (E : Env R) :
    sem w (.seq b (.inc c)) E = (update (sem w b E).1 c (E c + 1), (sem w b E).2) := by
  simp [sem, henv E c hcS]

include hcS henv₀ henv₁ in
theorem semBitsC_c : ∀ (L : List Bool) (E : Env R),
    (semBits (sem w (.seq b₀ (.inc c))) (sem w (.seq b₁ (.inc c))) L E).1 c = E c + L.length
  | [], E => rfl
  | b :: L, E => by
    simp only [semBits, List.length_cons]
    rw [semBitsC_c L]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [sem_body w S c hcS henv₀]; simp; ring
    · simp only [↓reduceIte]
      rw [sem_body w S c hcS henv₁]; simp; ring

include hcS henv₀ henv₁ in
theorem semBitsC_env : ∀ (L : List Bool) (E : Env R) (r : Fin R), r ≠ c → r ∉ S →
    (semBits (sem w (.seq b₀ (.inc c))) (sem w (.seq b₁ (.inc c))) L E).1 r = E r
  | [], E, r, _, _ => rfl
  | b :: L, E, r, h1, h2 => by
    simp only [semBits]
    rw [semBitsC_env L _ r h1 h2]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [sem_body w S c hcS henv₀]; dsimp only; rw [update_of_ne h1, henv₀ E r h2]
    · simp only [↓reduceIte]
      rw [sem_body w S c hcS henv₁]; dsimp only; rw [update_of_ne h1, henv₁ E r h2]

include hcS henv₀ henv₁ hout₀ hout₁ in
theorem semBitsC_out_congr : ∀ (L : List Bool) (E E' : Env R), (∀ r, r ∉ S → E r = E' r) →
    (semBits (sem w (.seq b₀ (.inc c))) (sem w (.seq b₁ (.inc c))) L E).2 =
      (semBits (sem w (.seq b₀ (.inc c))) (sem w (.seq b₁ (.inc c))) L E').2
  | [], E, E', _ => rfl
  | b :: L, E, E', hE => by
    simp only [semBits]
    have hc : E c = E' c := hE c hcS
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [sem_body w S c hcS henv₀, sem_body w S c hcS henv₀, hout₀ E E' hE]
      congr 1
      refine semBitsC_out_congr L _ _ fun r hr => ?_
      by_cases hrc : r = c
      · subst hrc; simp [hc]
      · dsimp only; rw [update_of_ne hrc, update_of_ne hrc, henv₀ E r hr, henv₀ E' r hr]; exact hE r hr
    · simp only [↓reduceIte]
      rw [sem_body w S c hcS henv₁, sem_body w S c hcS henv₁, hout₁ E E' hE]
      congr 1
      refine semBitsC_out_congr L _ _ fun r hr => ?_
      by_cases hrc : r = c
      · subst hrc; simp [hc]
      · dsimp only; rw [update_of_ne hrc, update_of_ne hrc, henv₁ E r hr, henv₁ E' r hr]; exact hE r hr

end semBitsC

/-! ### Propriedades de `Lp` -/

/-- Registradores fora de `W` não mudam; a saída só depende dos de fora de `W`. -/
theorem Lp.env_out (w : List Bool) {W : Finset (Fin R)} {c : Cmd R} (h : Lp W c) :
    (∀ E r, r ∉ W → (sem w c E).1 r = E r) ∧
      ∀ E E', (∀ r, r ∉ W → E r = E' r) → (sem w c E).2 = (sem w c E').2 := by
  induction h with
  | emit W s => exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  | @emitU W x s hx => exact ⟨fun _ _ _ => rfl, fun E E' hE => by simp [sem, hE _ hx]⟩
  | @seq W c₁ c₂ h₁ h₂ ih₁ ih₂ =>
    refine ⟨fun E r hr => ?_, fun E E' hE => ?_⟩
    · simp only [sem]
      rw [ih₂.1 _ r hr, ih₁.1 E r hr]
    · simp only [sem]
      rw [ih₁.2 E E' hE, ih₂.2 (sem w c₁ E).1 (sem w c₁ E').1 fun r hr => by
        rw [ih₁.1 E r hr, ih₁.1 E' r hr]; exact hE r hr]
  | @forU W x y body hx hy hb ih =>
    refine ⟨fun E r hr => ?_, fun E E' hE => ?_⟩
    · simp only [sem]
      rw [semFor_env _ _ _ hy ih.1 ih.2 _ _ r hr, update_of_ne (fun h => hr (by rw [h]; exact hy))]
    · simp only [sem]
      rw [semFor_out _ _ _ hy ih.1 ih.2, semFor_out _ _ _ hy ih.1 ih.2, hE _ hx]
      refine List.flatMap_congr fun k _ => ih.2 _ _ fun r hr => ?_
      by_cases hry : r = y
      · subst hry; simp
      · rw [update_of_ne hry, update_of_ne hry, update_of_ne hry, update_of_ne hry]
        exact hE r fun h => hr (Finset.mem_erase.mpr ⟨hry, h⟩)
  | @forBits W b₀ b₁ h₀ h₁ ih₀ ih₁ =>
    refine ⟨fun E r hr => ?_, fun E E' hE => ?_⟩
    · simp only [sem]
      exact semBits_env _ _ _ ih₀.1 ih₁.1 ih₀.2 ih₁.2 w E r hr
    · simp only [sem]
      rw [semBits_out _ _ _ ih₀.1 ih₁.1 ih₀.2 ih₁.2, semBits_out _ _ _ ih₀.1 ih₁.1 ih₀.2 ih₁.2]
      refine List.flatMap_congr fun b _ => ?_
      cases b
      · exact ih₀.2 E E' hE
      · exact ih₁.2 E E' hE
  | @bitsC W c b₀ b₁ hc h₀ h₁ ih₀ ih₁ =>
    have hcS : c ∉ W.erase c := by simp
    refine ⟨fun E r hr => ?_, fun E E' hE => ?_⟩
    · have hrc : r ≠ c := fun h => hr (h ▸ hc)
      have hrS : r ∉ W.erase c := fun h => hr (Finset.mem_of_mem_erase h)
      change (semBits (sem w (.seq b₀ (.inc c))) (sem w (.seq b₁ (.inc c))) w (update E c 0)).1 r = E r
      rw [semBitsC_env w b₀ b₁ (W.erase c) c hcS ih₀.1 ih₁.1 w _ r hrc hrS, update_of_ne hrc]
    · change (semBits (sem w (.seq b₀ (.inc c))) (sem w (.seq b₁ (.inc c))) w (update E c 0)).2 =
        (semBits (sem w (.seq b₀ (.inc c))) (sem w (.seq b₁ (.inc c))) w (update E' c 0)).2
      refine semBitsC_out_congr w b₀ b₁ (W.erase c) c hcS ih₀.1 ih₁.1 ih₀.2 ih₁.2 w
        (update E c 0) (update E' c 0) ?_
      intro r hr
      by_cases hrc : r = c
      · subst hrc; simp
      · rw [update_of_ne hrc, update_of_ne hrc]
        exact hE r fun h => hr (Finset.mem_erase.mpr ⟨hrc, h⟩)

theorem Lp.env (w : List Bool) {W : Finset (Fin R)} {c : Cmd R} (h : Lp W c) (E : Env R)
    {r : Fin R} (hr : r ∉ W) : (sem w c E).1 r = E r := (h.env_out w).1 E r hr

theorem Lp.out_congr (w : List Bool) {W : Finset (Fin R)} {c : Cmd R} (h : Lp W c) {E E' : Env R}
    (hE : ∀ r, r ∉ W → E r = E' r) : (sem w c E).2 = (sem w c E').2 := (h.env_out w).2 E E' hE

/-- **A saída de um laço** é a concatenação das saídas do corpo com `y = 0, 1, …, E x − 1`. -/
theorem Lp.out_forU (w : List Bool) {W : Finset (Fin R)} {x y : Fin R} {body : Cmd R}
    (hy : y ∈ W) (hb : Lp (W.erase y) body) (E : Env R) :
    (sem w (.forU x y body) E).2 =
      (List.range (E x)).flatMap fun k => (sem w body (update E y k)).2 := by
  simp only [sem]
  rw [semFor_out _ _ _ hy (hb.env_out w).1 (hb.env_out w).2]
  refine List.flatMap_congr fun k _ => ?_
  simp [update_self, update_idem]

theorem Lp.out_forBits (w : List Bool) {W : Finset (Fin R)} {b₀ b₁ : Cmd R} (h₀ : Lp W b₀)
    (h₁ : Lp W b₁) (E : Env R) :
    (sem w (.forBits b₀ b₁) E).2 = w.flatMap fun b => (sem w (if b then b₁ else b₀) E).2 := by
  simp only [sem]
  rw [semBits_out _ _ _ (h₀.env_out w).1 (h₁.env_out w).1 (h₀.env_out w).2 (h₁.env_out w).2]
  refine List.flatMap_congr fun b _ => ?_
  cases b <;> rfl

theorem Lp.out_seq (w : List Bool) {W : Finset (Fin R)} {c₁ c₂ : Cmd R} (h₁ : Lp W c₁)
    (h₂ : Lp W c₂) (E : Env R) :
    (sem w (.seq c₁ c₂) E).2 = (sem w c₁ E).2 ++ (sem w c₂ E).2 := by
  simp only [sem]
  congr 1
  exact h₂.out_congr w fun r hr => h₁.env w E hr

/-- Os registradores permanecem `≤ B`. -/
theorem Lp.le (w : List Bool) {W : Finset (Fin R)} {c : Cmd R} (h : Lp W c) {B : ℕ}
    (hw : w.length ≤ B) :
    ∀ E : Env R, (∀ r, E r ≤ B) → ∀ r, (sem w c E).1 r ≤ B := by
  induction h with
  | emit W s => exact fun E hE r => hE r
  | @emitU W x s hx => exact fun E hE r => hE r
  | @seq W c₁ c₂ h₁ h₂ ih₁ ih₂ => exact fun E hE r => ih₂ _ (ih₁ E hE) r
  | @forU W x y body hx hy hb ih =>
    intro E hE r
    simp only [sem]
    have key : ∀ (m : ℕ) (E' : Env R), (∀ r, E' r ≤ B) → E' y + m ≤ B →
        ∀ r, (semFor (sem w body) y m E').1 r ≤ B := by
      intro m
      induction m with
      | zero => exact fun E' hE' _ r => hE' r
      | succ m ihm =>
        intro E' hE' hy' r
        simp only [semFor]
        refine ihm _ (fun r' => ?_) ?_ r
        · by_cases hr' : r' = y
          · subst hr'
            rw [update_self, hb.env w E' (by simp)]
            omega
          · rw [update_of_ne hr']
            exact ih E' hE' r'
        · rw [update_self, hb.env w E' (by simp)]
          omega
    refine key (E x) (update E y 0) (fun r' => ?_) ?_ r
    · by_cases hr' : r' = y
      · subst hr'; simp
      · rw [update_of_ne hr']; exact hE r'
    · rw [update_self]
      simpa using hE x
  | @forBits W b₀ b₁ h₀ h₁ ih₀ ih₁ =>
    intro E hE r
    simp only [sem]
    have key : ∀ (L : List Bool) (E' : Env R), (∀ r, E' r ≤ B) →
        ∀ r, (semBits (sem w b₀) (sem w b₁) L E').1 r ≤ B := by
      intro L
      induction L with
      | nil => exact fun E' hE' r => hE' r
      | cons b L ihL =>
        intro E' hE' r
        simp only [semBits]
        refine ihL _ (fun r' => ?_) r
        cases b
        · exact ih₀ E' hE' r'
        · exact ih₁ E' hE' r'
    exact key w E hE r
  | @bitsC W c b₀ b₁ hc h₀ h₁ ih₀ ih₁ =>
    intro E hE r
    have hcS : c ∉ W.erase c := by simp
    have ih₀' : ∀ E r, r ∉ W.erase c → (sem w b₀ E).1 r = E r := fun E r hr => h₀.env w E hr
    have ih₁' : ∀ E r, r ∉ W.erase c → (sem w b₁ E).1 r = E r := fun E r hr => h₁.env w E hr
    simp only [sem]
    have key : ∀ (L : List Bool) (E' : Env R), (∀ r, E' r ≤ B) → E' c + L.length ≤ B →
        ∀ r, (semBits (sem w (.seq b₀ (.inc c))) (sem w (.seq b₁ (.inc c))) L E').1 r ≤ B := by
      intro L
      induction L with
      | nil => exact fun E' hE' _ r => hE' r
      | cons b L ihL =>
        intro E' hE' hl r
        simp only [semBits, List.length_cons] at hl ⊢
        have step : ∀ (b' : Cmd R) (henv : ∀ E r, r ∉ W.erase c → (sem w b' E).1 r = E r)
            (hle : ∀ E : Env R, (∀ r, E r ≤ B) → ∀ r, (sem w b' E).1 r ≤ B),
            ∀ r, (sem w (.seq b' (.inc c)) E').1 r ≤ B := by
          intro b' henv hle r'
          rw [sem_body w (W.erase c) c hcS henv]
          by_cases hr' : r' = c
          · subst hr'; simp; omega
          · simp only [update_of_ne hr']; exact hle E' hE' r'
        cases b
        · simp only [Bool.false_eq_true, ↓reduceIte]
          refine ihL _ (step b₀ ih₀' ih₀) ?_ r
          rw [sem_body w (W.erase c) c hcS ih₀']; simp; omega
        · simp only [↓reduceIte]
          refine ihL _ (step b₁ ih₁' ih₁) ?_ r
          rw [sem_body w (W.erase c) c hcS ih₁']; simp; omega
    refine key w _ (fun r' => ?_) ?_ r
    · by_cases hr' : r' = c
      · subst hr'; simp
      · rw [update_of_ne hr']; exact hE r'
    · simpa using hw

/-! ### Custo -/

theorem custoFor_le {f : Env R → ℕ} {g : Env R → Env R × List Bool} {y : Fin R} {C : ℕ}
    (I : ℕ → Env R → Prop)
    (hstep : ∀ k E, I (k + 1) E → f E ≤ C ∧ I k (update (g E).1 y ((g E).1 y + 1))) :
    ∀ (m : ℕ) (E : Env R), I m E → custoFor f g y m E ≤ m * (C + 2) + 1
  | 0, _, _ => by simp [custoFor]
  | m + 1, E, hI => by
    obtain ⟨h1, h2⟩ := hstep m E hI
    have := custoFor_le I hstep m _ h2
    simp only [custoFor]
    nlinarith

theorem custoBits_le {f₀ f₁ : Env R → ℕ} {g₀ g₁ : Env R → Env R × List Bool} {C : ℕ}
    (I : List Bool → Env R → Prop)
    (h₀ : ∀ L E, I (false :: L) E → f₀ E ≤ C ∧ I L (g₀ E).1)
    (h₁ : ∀ L E, I (true :: L) E → f₁ E ≤ C ∧ I L (g₁ E).1) :
    ∀ (L : List Bool) (E : Env R), I L E → custoBits f₀ f₁ g₀ g₁ L E ≤ L.length * (C + 3) + 1
  | [], _, _ => by simp [custoBits]
  | b :: L, E, hI => by
    simp only [custoBits, List.length_cons]
    cases b
    · obtain ⟨c1, c2⟩ := h₀ L E hI
      have := custoBits_le I h₀ h₁ L _ c2
      simp only [Bool.false_eq_true, ↓reduceIte] at this ⊢
      nlinarith
    · obtain ⟨c1, c2⟩ := h₁ L E hI
      have := custoBits_le I h₀ h₁ L _ c2
      simp only [↓reduceIte] at this ⊢
      nlinarith

/-- Cota sintática do custo, com todos os registradores e `|w|` cotados por `B`. -/
def cb (B : ℕ) : Cmd R → ℕ
  | .emit _ => 1
  | .emitU _ _ => 5 * B + 2
  | .zero _ => 2 * B + 1
  | .inc _ => 1
  | .add _ _ => 4 * B + 2
  | .lenIn _ => 4 * B + 2
  | .seq c₁ c₂ => cb B c₁ + cb B c₂
  | .forU _ _ body => B * (cb B body + 2) + 1 + (6 * B + 3)
  | .forBits b₀ b₁ => (2 * B + 1) + (B * (cb B b₀ + cb B b₁ + 3) + 1)

/-- **O custo de um programa de laço** é cotado por `cb B c`. -/
theorem Lp.custo_le (w : List Bool) {W : Finset (Fin R)} {c : Cmd R} (h : Lp W c) {B : ℕ}
    (hw : w.length ≤ B) : ∀ E : Env R, (∀ r, E r ≤ B) → custo w c E ≤ cb B c := by
  induction h with
  | emit W s => intro E _; simp [custo, cb]
  | @emitU W x s hx => intro E hE; simp only [custo, cb]; have := hE x; omega
  | @seq W c₁ c₂ h₁ h₂ ih₁ ih₂ =>
    intro E hE
    simp only [custo, cb]
    have := ih₂ _ (h₁.le w hw E hE)
    have := ih₁ E hE
    omega
  | @forU W x y body hx hy hb ih =>
    intro E hE
    simp only [custo, cb]
    have hcf := custoFor_le (f := custo w body) (g := sem w body) (y := y) (C := cb B body)
      (fun k E' => (∀ r, E' r ≤ B) ∧ E' y + k ≤ B) (fun k E' hI => ?_) (E x) (update E y 0) ?_
    · have h1 := hE x
      have h2 := hE y
      have h3 : E x * (cb B body + 2) ≤ B * (cb B body + 2) := Nat.mul_le_mul_right _ h1
      omega
    · refine ⟨ih E' hI.1, fun r => ?_, ?_⟩
      · by_cases hr : r = y
        · subst hr; rw [update_self, hb.env w E' (by simp)]; have := hI.2; omega
        · rw [update_of_ne hr]; exact hb.le w hw E' hI.1 r
      · rw [update_self, hb.env w E' (by simp)]; have := hI.2; omega
    · refine ⟨fun r => ?_, ?_⟩
      · by_cases hr : r = y
        · subst hr; simp
        · rw [update_of_ne hr]; exact hE r
      · rw [update_self]; simpa using hE x
  | @forBits W b₀ b₁ h₀ h₁ ih₀ ih₁ =>
    intro E hE
    simp only [custo, cb]
    have hcb := custoBits_le (f₀ := custo w b₀) (f₁ := custo w b₁) (g₀ := sem w b₀)
      (g₁ := sem w b₁) (C := cb B b₀ + cb B b₁) (fun _ E' => ∀ r, E' r ≤ B)
      (fun _ E' hI => ⟨(ih₀ E' hI).trans (Nat.le_add_right _ _), h₀.le w hw E' hI⟩)
      (fun _ E' hI => ⟨(ih₁ E' hI).trans (Nat.le_add_left _ _), h₁.le w hw E' hI⟩) w E hE
    have h3 : w.length * (cb B b₀ + cb B b₁ + 3) ≤ B * (cb B b₀ + cb B b₁ + 3) :=
      Nat.mul_le_mul_right _ hw
    omega
  | @bitsC W c b₀ b₁ hc h₀ h₁ ih₀ ih₁ =>
    intro E hE
    have hcS : c ∉ W.erase c := by simp
    have ih₀' : ∀ E r, r ∉ W.erase c → (sem w b₀ E).1 r = E r := fun E r hr => h₀.env w E hr
    have ih₁' : ∀ E r, r ∉ W.erase c → (sem w b₁ E).1 r = E r := fun E r hr => h₁.env w E hr
    have e : custo w (.seq (.zero c) (.forBits (.seq b₀ (.inc c)) (.seq b₁ (.inc c)))) E =
        ((2 * w.length + 1) + custoBits (custo w (.seq b₀ (.inc c))) (custo w (.seq b₁ (.inc c)))
          (sem w (.seq b₀ (.inc c))) (sem w (.seq b₁ (.inc c))) w (update E c 0)) +
          (2 * E c + 1) := rfl
    have hI : ∀ (b' : Cmd R) (henv : ∀ E r, r ∉ W.erase c → (sem w b' E).1 r = E r)
        (hle : ∀ E : Env R, (∀ r, E r ≤ B) → ∀ r, (sem w b' E).1 r ≤ B) (L : List Bool)
        (E' : Env R), ((∀ r, E' r ≤ B) ∧ E' c + (L.length + 1) ≤ B) →
        (∀ r, (sem w (.seq b' (.inc c)) E').1 r ≤ B) ∧
          (sem w (.seq b' (.inc c)) E').1 c + L.length ≤ B := by
      intro b' henv hle L E' hI
      rw [sem_body w (W.erase c) c hcS henv]
      refine ⟨fun r => ?_, by simp; omega⟩
      by_cases hr : r = c
      · subst hr; simp; omega
      · simp only [update_of_ne hr]; exact hle E' hI.1 r
    have hbits := custoBits_le (f₀ := custo w (.seq b₀ (.inc c))) (f₁ := custo w (.seq b₁ (.inc c)))
      (g₀ := sem w (.seq b₀ (.inc c))) (g₁ := sem w (.seq b₁ (.inc c)))
      (C := cb B b₀ + cb B b₁ + 2) (fun L E' => (∀ r, E' r ≤ B) ∧ E' c + L.length ≤ B)
      (fun L E' hl => by
        have h1 := ih₀ E' hl.1
        refine ⟨?_, hI b₀ ih₀' (fun E'' h'' => h₀.le w hw E'' h'') L E' hl⟩
        show custo w (.inc c) _ + custo w b₀ E' ≤ _
        simp only [custo]; omega)
      (fun L E' hl => by
        have h1 := ih₁ E' hl.1
        refine ⟨?_, hI b₁ ih₁' (fun E'' h'' => h₁.le w hw E'' h'') L E' hl⟩
        show custo w (.inc c) _ + custo w b₁ E' ≤ _
        simp only [custo]; omega)
      w (update E c 0) ⟨fun r => by
        by_cases hr : r = c
        · subst hr; simp
        · rw [update_of_ne hr]; exact hE r, by simpa using hw⟩
    have h3 : w.length * (cb B b₀ + cb B b₁ + 2 + 3) ≤ B * (cb B b₀ + cb B b₁ + 2 + 3) :=
      Nat.mul_le_mul_right _ hw
    have h4 := hE c
    rw [e]
    simp only [cb]
    nlinarith

/-! ### Boa formação -/

/-- Profundidade de aninhamento dos laços `forU`. -/
def prof : Cmd R → ℕ
  | .seq c₁ c₂ => max (prof c₁) (prof c₂)
  | .forU _ _ body => prof body + 1
  | .forBits b₀ b₁ => max (prof b₀) (prof b₁)
  | _ => 0

/-- Sem `forBits`. -/
def SemBits : Cmd R → Prop
  | .seq c₁ c₂ => SemBits c₁ ∧ SemBits c₂
  | .forU _ _ body => SemBits body
  | .forBits _ _ => False
  | _ => True

/-- Nenhum `forBits` dentro de outro `forBits`. -/
def Bem : Cmd R → Prop
  | .seq c₁ c₂ => Bem c₁ ∧ Bem c₂
  | .forU _ _ body => Bem body
  | .forBits b₀ b₁ => SemBits b₀ ∧ SemBits b₁
  | _ => True

theorem semBits_bem : ∀ {c : Cmd R}, SemBits c → Bem c
  | .seq c₁ c₂, h => ⟨semBits_bem h.1, semBits_bem h.2⟩
  | .forU _ _ body, h => semBits_bem (c := body) h
  | .forBits _ _, h => h.elim
  | .emit _, _ => trivial
  | .emitU _ _, _ => trivial
  | .zero _, _ => trivial
  | .inc _, _ => trivial
  | .add _ _, _ => trivial
  | .lenIn _, _ => trivial

theorem Lp.wf {A : ℕ} {W : Finset (Fin R)} {c : Cmd R} (h : Lp W c) (hbem : Bem c) :
    ∀ (δ : ℕ) (β : Bool), prof c + δ ≤ A → (β = true → SemBits c) → WF A c δ β := by
  induction h with
  | emit W s => intro δ β _ _; trivial
  | @emitU W x s hx => intro δ β _ _; trivial
  | @seq W c₁ c₂ h₁ h₂ ih₁ ih₂ =>
    intro δ β hp hβ
    simp only [prof] at hp
    exact ⟨ih₁ hbem.1 δ β (by omega) fun hb => (hβ hb).1,
      ih₂ hbem.2 δ β (by omega) fun hb => (hβ hb).2⟩
  | @forU W x y body hx hy hb ih =>
    intro δ β hp hβ
    simp only [prof] at hp
    refine ⟨fun hxy => hx (hxy ▸ hy), by omega, ih hbem (δ + 1) β (by omega) hβ⟩
  | @forBits W b₀ b₁ h₀ h₁ ih₀ ih₁ =>
    intro δ β hp hβ
    simp only [prof] at hp
    refine ⟨?_, ih₀ (semBits_bem hbem.1) δ true (by omega) fun _ => hbem.1,
      ih₁ (semBits_bem hbem.2) δ true (by omega) fun _ => hbem.2⟩
    cases β
    · rfl
    · exact (hβ rfl).elim
  | @bitsC W c b₀ b₁ hc h₀ h₁ ih₀ ih₁ =>
    intro δ β hp hβ
    have hb0 : SemBits b₀ := hbem.2.1.1
    have hb1 : SemBits b₁ := hbem.2.2.1
    simp only [prof] at hp
    refine ⟨trivial, ?_, ⟨ih₀ (semBits_bem hb0) δ true (by omega) fun _ => hb0, trivial⟩,
      ⟨ih₁ (semBits_bem hb1) δ true (by omega) fun _ => hb1, trivial⟩⟩
    cases β
    · rfl
    · exact (hβ rfl).2.elim

end ATK.Lacos
