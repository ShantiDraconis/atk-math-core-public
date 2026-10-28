import ATK.CookLevinReducao
import ATK.GeradorForm

/-!
# ATK — Cook–Levin, marco CL4b-4c: o molde da fórmula de Cook–Levin

O tableau (`CookLevinTableau.formula`) escrito como molde `FT` (`ATK.Gerador`): laços sobre os
contadores `t` (instante), `j` (célula), `i` (bit / posição do certificado), com os limites `T+1`,
`T`, `S`, `S − c` em contadores calculados antes. **`sem_formulaT`**: o molde gera exatamente a
fórmula. **`fmOutV_cod3`**: a sua saída é `codCNF (mapF enc ·)`.

**Nada aqui prova Cook–Levin. CLOSED_MATH continua false.**
-/

namespace ATK.CookLevinMolde

set_option linter.unusedSectionVars false

open Turing Function ATK.Gerador ATK.CookLevinTableau ATK.CookLevinReducao ATK.CookLevinJanela

noncomputable section

/-! ### Contadores -/

/-- Contadores: 13 fixos e `C` para `S − c`. -/
abbrev Rg (C : ℕ) := Fin 13 ⊕ Fin C

namespace Rg
variable {C : ℕ}
abbrev N : Rg C := .inl 0
abbrev Mq : Rg C := .inl 1
abbrev X : Rg C := .inl 2
abbrev TT : Rg C := .inl 3
abbrev T1 : Rg C := .inl 4
abbrev SS : Rg C := .inl 5
abbrev TP : Rg C := .inl 6
abbrev pw : Rg C := .inl 7
abbrev tm : Rg C := .inl 8
abbrev t : Rg C := .inl 9
abbrev j : Rg C := .inl 10
abbrev i : Rg C := .inl 11
abbrev E2 : Rg C := .inl 12
/-- `S − c` (com `c` truncado a `C − 1`). -/
def sm (c : ℕ) : Rg C := if h : c < C then .inr ⟨c, h⟩ else .inl 5
end Rg

/-- Os índices (contadores de laço). -/
def idxR {C : ℕ} (r : Rg C) : Prop := r = Rg.t ∨ r = Rg.j ∨ r = Rg.i

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} [∀ k, Fintype (Γ k)]
  [∀ k, DecidableEq (Γ k)] {Λ : Type} [Fintype Λ] [DecidableEq Λ] {σ : Type} [Fintype σ]
  [DecidableEq σ]

/-! ### Literais -/

/-- A variável de um dado finito, instante e célula. -/
def varOf : Dado K Γ Λ σ → ℕ → ℕ → Var K Γ Λ σ
  | .inl o, t, _ => .lab t o
  | .inr (.inl v), t, _ => .st t v
  | .inr (.inr ⟨k, a⟩), t, p => .cel t k p a

/-- Índice de um dado finito. -/
def idxD (d : Dado K Γ Λ σ) : ℕ :=
  (Fintype.equivFin (Dado K Γ Λ σ) d).val

/-- Código das variáveis: índice, instante, célula. -/
def cod3 (v : Var K Γ Λ σ) : ℕ × ℕ × ℕ := (idx v, inst v, celula v)

variable {C : ℕ}

/-- Literal de rótulo. -/
def litLab (b : Bool) (o : Option Λ) (tt : UT (Rg C)) : LT (Var K Γ Λ σ) (Rg C) :=
  ⟨fun g => .lab (val tt g) o, b, idxD (K := K) (Γ := Γ) (σ := σ) (.inl o), tt, ([], 0)⟩

/-- Literal de estado. -/
def litSt (b : Bool) (v : σ) (tt : UT (Rg C)) : LT (Var K Γ Λ σ) (Rg C) :=
  ⟨fun g => .st (val tt g) v, b, idxD (K := K) (Γ := Γ) (Λ := Λ) (.inr (.inl v)), tt, ([], 0)⟩

/-- Literal de célula. -/
def litCel (b : Bool) (k : K) (a : Option (Γ k)) (tt pt : UT (Rg C)) : LT (Var K Γ Λ σ) (Rg C) :=
  ⟨fun g => .cel (val tt g) k (val pt g) a, b,
    idxD (Λ := Λ) (σ := σ) (.inr (.inr ⟨k, a⟩)), tt, pt⟩

/-- Um literal lido só de contadores fora de `sc` é bem formado. -/
def LitOK (sc : Rg C → Prop) (l : LT (Var K Γ Λ σ) (Rg C)) : Prop :=
  (∀ r ∈ l.tt.1 ++ l.pt.1, ¬ sc r) ∧ Insens sc l.v ∧ ∀ g, cod3 (l.v g) = (l.a, val l.tt g, val l.pt g)

theorem val_insens {sc : Rg C → Prop} {u : UT (Rg C)} (h : ∀ r ∈ u.1, ¬ sc r) :
    Insens sc (val u) := by
  intro g g' hg
  simp only [val]
  rw [List.map_congr_left (fun r hr => hg r (h r hr))]

theorem litLab_ok {sc : Rg C → Prop} (b : Bool) (o : Option Λ) (tt : UT (Rg C))
    (h : ∀ r ∈ tt.1, ¬ sc r) : LitOK (K := K) (Γ := Γ) (σ := σ) sc (litLab b o tt) := by
  refine ⟨by simpa [litLab] using h, fun g g' hg => ?_, fun g => ?_⟩
  · simp only [litLab]; rw [val_insens h g g' hg]
  · simp [litLab, cod3, idx, idxD, dado, inst, celula, val]

theorem litSt_ok {sc : Rg C → Prop} (b : Bool) (v : σ) (tt : UT (Rg C))
    (h : ∀ r ∈ tt.1, ¬ sc r) : LitOK (K := K) (Γ := Γ) (Λ := Λ) sc (litSt b v tt) := by
  refine ⟨by simpa [litSt] using h, fun g g' hg => ?_, fun g => ?_⟩
  · simp only [litSt]; rw [val_insens h g g' hg]
  · simp [litSt, cod3, idx, idxD, dado, inst, celula, val]

theorem litCel_ok {sc : Rg C → Prop} (b : Bool) (k : K) (a : Option (Γ k)) (tt pt : UT (Rg C))
    (h : ∀ r ∈ tt.1 ++ pt.1, ¬ sc r) :
    LitOK (Λ := Λ) (σ := σ) sc (litCel b k a tt pt) := by
  refine ⟨by simpa [litCel] using h, fun g g' hg => ?_, fun g => ?_⟩
  · simp only [litCel]
    rw [val_insens (fun r hr => h r (List.mem_append_left _ hr)) g g' hg,
      val_insens (fun r hr => h r (List.mem_append_right _ hr)) g g' hg]
  · simp [litCel, cod3, idx, idxD, dado, inst, celula]

/-! ### Saída = `codCNF ∘ mapF enc` -/

theorem unS_eq (n : ℕ) : (u n).flatMap ATK.ModeloPNP.simb = unS n := by
  simp only [u, unS, List.flatMap_append, List.flatMap_replicate, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, ATK.ModeloPNP.simb]
  congr 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons, ih, show 2 * (n + 1) = 2 + 2 * n by ring,
      List.replicate_add]
    rfl

theorem litOutV_cod3 (ℓ : Var K Γ Λ σ × Bool) :
    litOutV cod3 ℓ = ATK.ModeloPNP.codLiteral (enc ℓ.1, ℓ.2) := by
  simp only [litOutV, litOut, ATK.ModeloPNP.codLiteral, bits_enc, code, cod3,
    List.flatMap_append, unS_eq, sb, ATK.ModeloPNP.simb, List.append_assoc]

theorem fmOutV_cod3 (φ : Fm (Var K Γ Λ σ)) :
    fmOutV cod3 φ = ATK.ModeloPNP.codCNF (mapF enc φ) := by
  simp only [fmOutV, ATK.ModeloPNP.codCNF, mapF, List.flatMap_map]
  congr 1
  funext C
  simp only [clOutV, ATK.ModeloPNP.codClausula, List.flatMap_map]
  congr 1
  congr 1
  funext ℓ
  exact litOutV_cod3 ℓ

/-! ### Combinadores de moldes -/

omit [DecidableEq K] [Fintype K] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [Fintype Λ]
  [DecidableEq Λ] [Fintype σ] [DecidableEq σ] in
theorem sem_cat {V R : Type} [DecidableEq R] (w : List Bool) (a b : FT V R) (g : R → ℕ) :
    sem w (.cat a b) g = sem w a g ++ sem w b g := rfl

/-- Concatenação de muitos moldes. -/
def manyF {V R : Type} (xs : List (FT V R)) : FT V R := xs.foldr .cat .nil

omit [DecidableEq K] [Fintype K] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [Fintype Λ]
  [DecidableEq Λ] [Fintype σ] [DecidableEq σ] in
theorem sem_manyF {V R : Type} [DecidableEq R] (w : List Bool) (xs : List (FT V R)) (g : R → ℕ) :
    sem w (manyF xs) g = xs.flatMap (sem w · g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [manyF, List.foldr_cons, sem, List.flatMap_cons] at ih ⊢; rw [ih]

theorem wf_manyF {V R : Type} [DecidableEq R] (c3 : V → ℕ × ℕ × ℕ) (xs : List (FT V R))
    (sc : R → Prop) (h : ∀ x ∈ xs, WF c3 x sc) : WF c3 (manyF xs) sc := by
  induction xs with
  | nil => trivial
  | cons x xs ih =>
    exact ⟨h x (List.mem_cons_self ..), ih fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

theorem wf_cl (sc : Rg C → Prop) (lits : List (LT (Var K Γ Λ σ) (Rg C)))
    (h : ∀ l ∈ lits, LitOK sc l) : WF cod3 (.cl lits) sc := fun l hl => h l hl

/-- O molde de `umDe`. -/
def umDeT {α : Type} [Fintype α] [DecidableEq α] (mk : α → Bool → LT (Var K Γ Λ σ) (Rg C)) :
    FT (Var K Γ Λ σ) (Rg C) :=
  .cat (.cl ((todos α).map fun x => mk x true))
    (manyF ((todos α).map fun x => manyF (((todos α).filter (· ≠ x)).map fun y =>
      .cl [mk x false, mk y false])))

theorem sem_umDeT {α : Type} [Fintype α] [DecidableEq α] (w : List Bool)
    (mk : α → Bool → LT (Var K Γ Λ σ) (Rg C)) (f : (Rg C → ℕ) → α → Var K Γ Λ σ)
    (hv : ∀ x b, (mk x b).v = fun g => f g x) (hb : ∀ x b, (mk x b).b = b) (g : Rg C → ℕ) :
    sem w (umDeT mk) g = umDe (f g) := by
  simp only [umDeT, sem, sem_manyF, umDe, List.map_map, List.flatMap_map, List.cons_append,
    List.nil_append]
  congr 1
  · congr 1
    funext x
    simp [hv, hb]
  · apply List.flatMap_congr
    intro x _
    simp only [sem_manyF, List.flatMap_map, sem, hv, hb, List.map_cons, List.map_nil]
    induction ((todos α).filter (· ≠ x)) with
    | nil => rfl
    | cons y ys ih => simp [ih]

omit [DecidableEq K] [Fintype K] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [Fintype Λ]
  [DecidableEq Λ] [Fintype σ] [DecidableEq σ] in
theorem sem_manyF_cl {V R α : Type} [DecidableEq R] (w : List Bool) (xs : List α)
    (L : α → List (LT V R)) (g : R → ℕ) :
    sem w (manyF (xs.map fun x => .cl (L x))) g = xs.map fun x => (L x).map fun l => (l.v g, l.b) := by
  rw [sem_manyF, List.flatMap_map]
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.flatMap_cons, List.map_cons, ← ih]; rfl

omit [DecidableEq K] [Fintype K] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [Fintype Λ]
  [DecidableEq Λ] [Fintype σ] [DecidableEq σ] in
theorem flatMap_single {α β : Type*} (l : List α) (f : α → β) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons x xs ih => rw [List.flatMap_cons, List.map_cons, ih]; rfl

theorem val_t (g : Rg C → ℕ) (c : ℕ) : val ([Rg.t], c) g = g Rg.t + c := by simp [val]
theorem val_r (r : Rg C) (g : Rg C → ℕ) (c : ℕ) : val ([r], c) g = g r + c := by simp [val]
theorem val_c (g : Rg C → ℕ) (c : ℕ) : val (([] : List (Rg C)), c) g = c := by simp [val]

/-! ### As linhas -/

/-- Instante `t` e `t+1`; célula `j`. -/
abbrev T0 : UT (Rg C) := ([Rg.t], 0)
abbrev TS : UT (Rg C) := ([Rg.t], 1)
abbrev J0 : UT (Rg C) := ([Rg.j], 0)
abbrev Z : UT (Rg C) := ([], 0)

/-- Molde de `clsLinha t S` (instante em `t`, `S` em `SS`). -/
def linhaT : FT (Var K Γ Λ σ) (Rg C) :=
  .cat (umDeT fun o b => litLab b o T0)
    (.cat (umDeT fun v b => litSt b v T0)
      (manyF ((todos K).map fun k => .rng Rg.SS Rg.j (umDeT fun a b => litCel b k a T0 J0))))

theorem sem_linhaT (w : List Bool) (g : Rg C → ℕ) :
    sem w (linhaT (K := K) (Γ := Γ) (Λ := Λ) (σ := σ)) g = clsLinha (g Rg.t) (g Rg.SS) := by
  simp only [linhaT, sem, sem_manyF, List.flatMap_map, clsLinha, List.append_assoc]
  rw [sem_umDeT w _ (fun g o => Var.lab (g Rg.t) o) (fun _ _ => by funext g; simp [litLab, val])
      (fun _ _ => rfl),
    sem_umDeT w _ (fun g v => Var.st (g Rg.t) v) (fun _ _ => by funext g; simp [litSt, val])
      (fun _ _ => rfl)]
  congr 1
  congr 1
  apply List.flatMap_congr
  intro k _
  apply List.flatMap_congr
  intro p _
  rw [sem_umDeT w _ (fun g a => Var.cel (g Rg.t) k (g Rg.j) a)
    (fun _ _ => by funext g; simp [litCel, val]) (fun _ _ => rfl)]
  simp

/-! ### A parada -/

/-- Molde de `clsPara t S`. -/
def paraT : FT (Var K Γ Λ σ) (Rg C) :=
  .cat (.cl [litLab false none T0, litLab true none TS])
    (.cat (manyF ((todos σ).map fun v => .cl [litLab false none T0, litSt false v T0,
        litSt true v TS]))
      (manyF ((todos K).map fun k => .rng Rg.SS Rg.j (manyF ((todos (Option (Γ k))).map fun a =>
        .cl [litLab false none T0, litCel false k a T0 J0, litCel true k a TS J0])))))

theorem sem_paraT (w : List Bool) (g : Rg C → ℕ) :
    sem w (paraT (K := K) (Γ := Γ) (Λ := Λ) (σ := σ)) g = clsPara (g Rg.t) (g Rg.SS) := by
  simp only [paraT, sem, sem_manyF_cl, clsPara, imp]
  simp only [sem_manyF, List.flatMap_map, sem_manyF_cl]
  simp [sem, sem_manyF_cl, litLab, litSt, litCel, val, flatMap_single]

/-! ### Os casos: a divisão das células em zonas -/

theorem range_zonas {β : Type} (S L D : ℕ) (hL : L ≤ S) (hD : D ≤ S) (A B Cn : ℕ → List β) :
    (List.range S).flatMap (fun p => if p < L then A p else if p - L + D < S then B p else Cn p) =
      (List.range L).flatMap A ++
        (List.range (S - max L D)).flatMap (fun j => B (j + L)) ++
        (List.range (max L D - L)).flatMap (fun i => Cn (S - (max L D - L) + i)) := by
  obtain ⟨a, ha⟩ : ∃ a, S - max L D = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, max L D - L = b := ⟨_, rfl⟩
  have hS : S = L + (a + b) := by omega
  have hrange : List.range S = List.range L ++ ((List.range a).map (L + ·) ++
      (List.range b).map (L + a + ·)) := by
    rw [hS, List.range_add, List.range_add, List.map_append, List.map_map]
    congr 3
    funext x
    simp only [Function.comp]
    omega
  rw [hrange, ha, hb, List.flatMap_append, List.flatMap_append, List.flatMap_map,
    List.flatMap_map, List.append_assoc]
  congr 1
  · apply List.flatMap_congr
    intro p hp
    simp [List.mem_range.mp hp]
  · congr 1
    · apply List.flatMap_congr
      intro j hj
      have hj := List.mem_range.mp hj
      have h1 : ¬ (L + j < L) := by omega
      have h2 : L + j - L + D < S := by omega
      simp only [h1, h2, ↓reduceIte]
      rw [Nat.add_comm]
    · apply List.flatMap_congr
      intro i hi
      have hi := List.mem_range.mp hi
      have h1 : ¬ (L + a + i < L) := by omega
      have h2 : ¬ (L + a + i - L + D < S) := by omega
      simp only [h1, h2, ↓reduceIte]
      congr 1
      omega

variable (M : Λ → TM2.Stmt Γ Λ σ)

/-- As premissas de um caso. -/
def premT (c : Caso M) : List (LT (Var K Γ Λ σ) (Rg C)) :=
  litLab false (some c.1) T0 :: litSt false c.2.1 T0 ::
    (todos K).flatMap fun k => (todos (Fin (profMax M))).map fun i =>
      litCel false k (c.2.2 k i) T0 ([], i.val)

theorem premT_v (c : Caso M) (g : Rg C → ℕ) :
    (premT M c).map (fun l => (l.v g, l.b)) = (prem M (g Rg.t) c).map fun x => (x, false) := by
  simp only [premT, prem, List.map_cons, List.map_flatMap, List.map_map, List.cons.injEq]
  refine ⟨by simp [litLab, val], by simp [litSt, val], ?_⟩
  apply List.flatMap_congr
  intro k _
  apply List.map_congr_left
  intro i _
  simp [litCel, val]

/-- Molde das células de um caso, na pilha `k`. -/
def celT (c : Caso M) (k : K) : FT (Var K Γ Λ σ) (Rg C) :=
  .cat (manyF ((List.range ((res M c).stk k).length).map fun p =>
      .cl (premT M c ++ [litCel true k ((res M c).stk k)[p]? TS ([], p)])))
    (.cat (.rng (Rg.sm (max ((res M c).stk k).length (profMax M))) Rg.j
        (manyF ((todos (Option (Γ k))).map fun a =>
          .cl (litCel false k a T0 ([Rg.j], profMax M) :: premT M c ++
            [litCel true k a TS ([Rg.j], ((res M c).stk k).length)]))))
      (manyF ((List.range (max ((res M c).stk k).length (profMax M) -
          ((res M c).stk k).length)).map fun i =>
        .cl (premT M c ++ [litCel true k none TS
          ([Rg.sm (max ((res M c).stk k).length (profMax M) - ((res M c).stk k).length)], i)]))))

/-- Molde de `clsCaso t S c`. -/
def casoT (c : Caso M) : FT (Var K Γ Λ σ) (Rg C) :=
  .cat (.cl (premT M c ++ [litLab true (res M c).l TS]))
    (.cat (.cl (premT M c ++ [litSt true (res M c).var TS]))
      (manyF ((todos K).map fun k => celT M c k)))

/-- O tamanho de uma janela nova não passa de `profMax M + pushMax M`. -/
theorem res_len_le (c : Caso M) (k : K) :
    ((res M c).stk k).length ≤ profMax M + pushMax M := by
  have h1 := stepAux_len (M c.1) c.2.1 (janC c.2.2) k
  have h2 : (janC c.2.2 k).length ≤ profMax M := by
    simp only [janC]
    exact (List.length_filterMap_le _ _).trans (by simp)
  have h3 : npush (M c.1) ≤ pushMax M :=
    Finset.le_sup (f := fun l => npush (M l)) (Finset.mem_univ c.1)
  simp only [res]
  omega

/-- Os contadores `S − c` estão certos. -/
def SmOK (g : Rg C → ℕ) : Prop := ∀ c < C, g (Rg.sm c) = g Rg.SS - c

theorem sem_casoT (w : List Bool) (g : Rg C → ℕ) (hC : profMax M + pushMax M < C)
    (hsm : SmOK g) (hS : profMax M + pushMax M ≤ g Rg.SS) (c : Caso M) :
    sem w (casoT M c) g = clsCaso M (g Rg.t) (g Rg.SS) c := by
  simp only [casoT, sem, sem_manyF, List.flatMap_map, clsCaso, imp, List.map_append,
    premT_v, List.cons_append, List.nil_append]
  simp only [List.map_cons, List.map_nil, litLab, litSt, val_t]
  congr 3
  funext k
  have hL := res_len_le M c k
  set L := ((res M c).stk k).length with hLdef
  have hDm : max L (profMax M) < C := by omega
  have hDmL : max L (profMax M) - L < C := by omega
  rw [range_zonas (g Rg.SS) L (profMax M) (by omega) (by omega)]
  simp only [celT, sem, sem_manyF, List.flatMap_map, ← hLdef, List.append_assoc]
  have hpv : ∀ g' : Rg C → ℕ, g' Rg.t = g Rg.t →
      (premT M c).map (fun l => (l.v g', l.b)) = (prem M (g Rg.t) c).map fun x => (x, false) := by
    intro g' h; rw [premT_v, h]
  congr 1
  · apply List.flatMap_congr
    intro p _
    simp only [List.map_append, hpv g rfl, imp, List.map_cons, List.map_nil]
    simp [litCel, val]
  · congr 1
    · rw [show g (Rg.sm (max L (profMax M))) = g Rg.SS - max L (profMax M) from hsm _ hDm]
      apply List.flatMap_congr
      intro j _
      rw [flatMap_single]
      apply List.map_congr_left
      intro a _
      simp only [List.map_append, List.map_cons, List.map_nil, imp, List.cons_append]
      rw [hpv _ (by simp)]
      simp [litCel, val]
    · apply List.flatMap_congr
      intro i _
      simp only [List.map_append, hpv g rfl, imp, List.map_cons, List.map_nil]
      simp [litCel, val, hsm _ hDmL]

/-- Molde de `clsTrans t S`. -/
def transT : FT (Var K Γ Λ σ) (Rg C) :=
  .cat paraT (manyF ((todos (Caso M)).map fun c => casoT M c))

theorem sem_transT (w : List Bool) (g : Rg C → ℕ) (hC : profMax M + pushMax M < C)
    (hsm : SmOK g) (hS : profMax M + pushMax M ≤ g Rg.SS) :
    sem w (transT M) g = clsTrans M (g Rg.t) (g Rg.SS) := by
  simp only [transT, sem, sem_manyF, List.flatMap_map, clsTrans, sem_paraT]
  congr 1
  apply List.flatMap_congr
  intro c _
  exact sem_casoT M w g hC hsm hS c

/-- Molde da estrutura: linhas `0..T` (contador `T1 = T+1`) e passos `0..T-1`. -/
def estruturaT : FT (Var K Γ Λ σ) (Rg C) :=
  .cat (.rng Rg.T1 Rg.t linhaT) (.rng Rg.TT Rg.t (transT M))

theorem SmOK_upd {g : Rg C → ℕ} (hsm : SmOK g) (r : Rg C) (hr : r = Rg.t ∨ r = Rg.j ∨ r = Rg.i)
    (n : ℕ) : SmOK (update g r n) := by
  intro c hc
  have h1 : (Rg.sm c : Rg C) ≠ r := by
    simp only [Rg.sm, hc, dite_true]; rcases hr with rfl | rfl | rfl <;> simp
  have h2 : (Rg.SS : Rg C) ≠ r := by rcases hr with rfl | rfl | rfl <;> simp
  rw [update_of_ne h1, update_of_ne h2]
  exact hsm c hc

theorem sem_estruturaT (w : List Bool) (g : Rg C → ℕ) (hC : profMax M + pushMax M < C)
    (hsm : SmOK g) (hS : profMax M + pushMax M ≤ g Rg.SS) (hT : g Rg.T1 = g Rg.TT + 1) :
    sem w (estruturaT M) g = estrutura M (g Rg.TT) (g Rg.SS) := by
  simp only [estruturaT, sem, estrutura, hT]
  congr 1
  · apply List.flatMap_congr
    intro k _
    rw [sem_linhaT]
    simp
  · apply List.flatMap_congr
    intro k _
    rw [sem_transT M w _ hC (SmOK_upd hsm _ (Or.inl rfl) k) (by simpa using hS)]
    simp

/-- Molde da aceitação. -/
def aceitaT (k₁ : K) (y : Γ k₁) : FT (Var K Γ Λ σ) (Rg C) :=
  .cat (.cl [litLab true none ([Rg.TT], 0)]) (.cl [litCel true k₁ (some y) ([Rg.TT], 0) Z])

theorem sem_aceitaT (w : List Bool) (g : Rg C → ℕ) (k₁ : K) (y : Γ k₁) :
    sem w (aceitaT (Λ := Λ) (σ := σ) k₁ y) g = aceita (g Rg.TT) k₁ y := by
  simp [aceitaT, sem, aceita, litLab, litCel, val]

/-! ### A linha inicial -/

omit [DecidableEq K] [Fintype K] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [Fintype Λ]
  [DecidableEq Λ] [Fintype σ] [DecidableEq σ] in
theorem dobro_get : ∀ (v : List Bool) (i : ℕ), i < v.length →
    (v.flatMap fun b => [b, b])[2 * i]? = v[i]? ∧ (v.flatMap fun b => [b, b])[2 * i + 1]? = v[i]?
  | [], i, h => absurd h (by simp)
  | b :: v, 0, _ => by simp
  | b :: v, i + 1, h => by
    have := dobro_get v i (by simpa using h)
    simp only [List.flatMap_cons, List.getElem?_cons_succ]
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, show 2 * i + 1 + 1 + 1 = 2 * i + 1 + 1 + 1 from rfl]
    simpa [List.getElem?_cons_succ, show 2 * i + 1 + 1 = (2 * i) + 2 by ring] using this

omit [DecidableEq K] [Fintype K] [∀ k, Fintype (Γ k)] [∀ k, DecidableEq (Γ k)] [Fintype Λ]
  [DecidableEq Λ] [Fintype σ] [DecidableEq σ] in
theorem dobro_length (v : List Bool) : (v.flatMap fun b => [b, b]).length = 2 * v.length := by
  induction v with
  | nil => rfl
  | cons b v ih => simp [ih]; ring

/-- O prefixo `par w ·` como símbolos. -/
def Epre (k₀ : K) (g : Bool → Γ k₀) (w : List Bool) : List (Γ k₀) :=
  ((w.flatMap fun b => [b, b]) ++ [false, true]).map g

theorem Epre_length (k₀ : K) (g : Bool → Γ k₀) (w : List Bool) :
    (Epre k₀ g w).length = 2 * w.length + 2 := by
  simp only [Epre, List.length_map, List.length_append, dobro_length]
  rfl

/-- A célula `p` da linha 0 com o símbolo do prefixo. -/
def celPre (k₀ : K) (g : Bool → Γ k₀) (w : List Bool) (p : ℕ) : List (Var K Γ Λ σ × Bool) :=
  [(Var.cel 0 k₀ p (Epre k₀ g w)[p]?, true)]

theorem rangeL_pre (k₀ : K) (g : Bool → Γ k₀) (w : List Bool) :
    ∀ (v : List Bool) (n : ℕ), (∀ i < v.length, (Epre k₀ g w)[2 * (n + i)]? = some (g v[i]!) ∧
      (Epre k₀ g w)[2 * (n + i) + 1]? = some (g v[i]!)) →
      (List.range' (2 * n) (2 * v.length)).map (celPre (Λ := Λ) (σ := σ) k₀ g w) =
        (v.zipIdx n).flatMap fun x =>
          [[(Var.cel 0 k₀ (x.2 + x.2) (some (g x.1)), true)],
            [(Var.cel 0 k₀ (x.2 + x.2 + 1) (some (g x.1)), true)]]
  | [], n, _ => by simp
  | b :: v, n, h => by
    have h0 := h 0 (by simp)
    have ih := rangeL_pre k₀ g w v (n + 1) (fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [show n + (i + 1) = n + 1 + i by ring] using this)
    rw [List.length_cons, show 2 * (v.length + 1) = 2 * v.length + 1 + 1 by ring,
      List.range'_succ, List.range'_succ, List.map_cons, List.map_cons,
      show 2 * n + 1 + 1 = 2 * (n + 1) by ring, ih]
    simp only [List.zipIdx_cons, List.flatMap_cons, celPre]
    simp only [Nat.add_zero, List.getElem!_cons_zero] at h0
    rw [h0.1, h0.2, show 2 * n = n + n by ring]
    rfl

theorem sem_pre_range (k₀ : K) (g : Bool → Γ k₀) (w : List Bool) :
    (List.range (Epre k₀ g w).length).map (celPre (Λ := Λ) (σ := σ) k₀ g w) =
      (w.zipIdx.flatMap fun x =>
          [[(Var.cel 0 k₀ (x.2 + x.2) (some (g x.1)), true)],
            [(Var.cel 0 k₀ (x.2 + x.2 + 1) (some (g x.1)), true)]]) ++
        [[(Var.cel 0 k₀ (w.length + w.length) (some (g false)), true)],
          [(Var.cel 0 k₀ (w.length + w.length + 1) (some (g true)), true)]] := by
  rw [Epre_length, List.range_eq_range', ← List.range'_append_1, List.map_append]
  have hw : ∀ i < w.length, (Epre k₀ g w)[2 * (0 + i)]? = some (g w[i]!) ∧
      (Epre k₀ g w)[2 * (0 + i) + 1]? = some (g w[i]!) := by
    intro i hi
    have := dobro_get w i hi
    simp only [Epre, Nat.zero_add, List.getElem?_map]
    rw [List.getElem?_append_left (by rw [dobro_length]; omega),
      List.getElem?_append_left (by rw [dobro_length]; omega), this.1, this.2,
      List.getElem?_eq_getElem hi]
    simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have := rangeL_pre (Λ := Λ) (σ := σ) k₀ g w w 0 hw
  rw [Nat.mul_zero] at this
  rw [this]
  congr 1
  simp only [Nat.zero_add, List.range'_succ, List.range'_zero, List.map_cons, List.map_nil, celPre,
    Epre]
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_append_right (by rw [dobro_length]),
    List.getElem?_append_right (by rw [dobro_length]; omega), dobro_length]
  simp [show 2 * w.length = w.length + w.length by ring]

/-- Molde do prefixo (bits de `w` duplicados e o separador). -/
def preT (k₀ : K) (g : Bool → Γ k₀) : FT (Var K Γ Λ σ) (Rg C) :=
  .cat (.bits Rg.i
      (.cat (.cl [litCel true k₀ (some (g false)) Z ([Rg.i, Rg.i], 0)])
        (.cl [litCel true k₀ (some (g false)) Z ([Rg.i, Rg.i], 1)]))
      (.cat (.cl [litCel true k₀ (some (g true)) Z ([Rg.i, Rg.i], 0)])
        (.cl [litCel true k₀ (some (g true)) Z ([Rg.i, Rg.i], 1)])))
    (.cat (.cl [litCel true k₀ (some (g false)) Z ([Rg.N, Rg.N], 0)])
      (.cl [litCel true k₀ (some (g true)) Z ([Rg.N, Rg.N], 1)]))

theorem sem_preT (k₀ : K) (g : Bool → Γ k₀) (w : List Bool) (gr : Rg C → ℕ)
    (hN : gr Rg.N = w.length) :
    sem w (preT (Λ := Λ) (σ := σ) k₀ g) gr =
      (List.range (Epre k₀ g w).length).map fun p => [(Var.cel 0 k₀ p (Epre k₀ g w)[p]?, true)] := by
  have := sem_pre_range (Λ := Λ) (σ := σ) k₀ g w
  change _ = (List.range (Epre k₀ g w).length).map (celPre (Λ := Λ) (σ := σ) k₀ g w)
  rw [this]
  simp only [preT, sem]
  congr 1
  · apply List.flatMap_congr
    intro x _
    cases x.1 <;> simp [sem, litCel, val]
  · simp [litCel, val, hN]

/-- `E2 + i` (`E2 = 2N + 2`) e `X + i` (`X = E2 + Mq`). -/
abbrev P2 : UT (Rg C) := ([Rg.E2, Rg.i], 0)
abbrev P3 : UT (Rg C) := ([Rg.E2, Rg.i], 1)
abbrev PX : UT (Rg C) := ([Rg.X, Rg.i], 0)

/-- Molde da linha inicial. -/
def iniT (k₀ : K) (g : Bool → Γ k₀) (main : Λ) (s₀ : σ) : FT (Var K Γ Λ σ) (Rg C) :=
  .cat (.cl [litLab true (some main) Z]) (.cat (.cl [litSt true s₀ Z])
    (.cat (manyF ((todos K).map fun k =>
        if k = k₀ then .nil else .rng Rg.SS Rg.j (.cl [litCel true k none Z J0])))
      (.cat (preT k₀ g)
        (.cat (.rng Rg.Mq Rg.i (.cl [litCel true k₀ none Z P2, litCel true k₀ (some (g false)) Z P2,
            litCel true k₀ (some (g true)) Z P2]))
          (.cat (.rng Rg.Mq Rg.i (.cl [litCel false k₀ none Z P2, litCel true k₀ none Z P3]))
            (.rng Rg.TP Rg.i (.cl [litCel true k₀ none Z PX])))))))

theorem sem_iniT (k₀ : K) (g : Bool → Γ k₀) (main : Λ) (s₀ : σ) (w : List Bool)
    (gr : Rg C → ℕ) (hN : gr Rg.N = w.length) (hE : gr Rg.E2 = (Epre k₀ g w).length)
    (hX : gr Rg.X = (Epre k₀ g w).length + gr Rg.Mq)
    (hTP : gr Rg.TP = gr Rg.SS - ((Epre k₀ g w).length + gr Rg.Mq)) :
    sem w (iniT k₀ g main s₀) gr =
      ATK.CookLevinInicio.iniF k₀ (Epre k₀ g w) g (gr Rg.Mq) main s₀ (gr Rg.SS) := by
  have e1 : sem w (.cl [litLab (K := K) (Γ := Γ) (σ := σ) (C := C) true (some main) Z]) gr =
      [[(Var.lab 0 (some main), true)]] := by simp [sem, litLab, val]
  have e2 : sem w (.cl [litSt (K := K) (Γ := Γ) (Λ := Λ) (C := C) true s₀ Z]) gr =
      [[(Var.st 0 s₀, true)]] := by simp [sem, litSt, val]
  have e3 : sem w (manyF ((todos K).map fun k =>
        if k = k₀ then (.nil : FT (Var K Γ Λ σ) (Rg C))
        else .rng Rg.SS Rg.j (.cl [litCel true k none Z J0]))) gr =
      (todos K).flatMap fun k =>
        if k = k₀ then [] else (List.range (gr Rg.SS)).map fun p => [(Var.cel 0 k p none, true)] := by
    rw [sem_manyF, List.flatMap_map]
    apply List.flatMap_congr
    intro k _
    split_ifs
    · rfl
    · simp only [sem]
      rw [← flatMap_single]
      apply List.flatMap_congr
      intro p _
      simp [sem, litCel, val]
  have e4 : sem w (.rng Rg.Mq Rg.i (.cl [litCel (Γ := Γ) (Λ := Λ) (σ := σ) true k₀ none Z P2,
        litCel true k₀ (some (g false)) Z P2, litCel (Λ := Λ) (σ := σ) true k₀ (some (g true)) Z P2]))
        gr =
      (List.range (gr Rg.Mq)).map fun i =>
        [(Var.cel 0 k₀ ((Epre k₀ g w).length + i) none, true),
          (Var.cel 0 k₀ ((Epre k₀ g w).length + i) (some (g false)), true),
          (Var.cel 0 k₀ ((Epre k₀ g w).length + i) (some (g true)), true)] := by
    simp only [sem]
    rw [← flatMap_single]
    apply List.flatMap_congr
    intro i _
    simp [sem, litCel, val, hE]
  have e5 : sem w (.rng Rg.Mq Rg.i (.cl [litCel (Γ := Γ) (Λ := Λ) (σ := σ) false k₀ none Z P2,
        litCel (Γ := Γ) (Λ := Λ) (σ := σ) true k₀ none Z P3])) gr =
      (List.range (gr Rg.Mq)).map fun i =>
        [(Var.cel 0 k₀ ((Epre k₀ g w).length + i) none, false),
          (Var.cel 0 k₀ ((Epre k₀ g w).length + i + 1) none, true)] := by
    simp only [sem]
    rw [← flatMap_single]
    apply List.flatMap_congr
    intro i _
    simp [sem, litCel, val, hE]
  have e6 : sem w (.rng Rg.TP Rg.i (.cl [litCel (Γ := Γ) (Λ := Λ) (σ := σ) true k₀ none Z PX]))
      gr =
      (List.range (gr Rg.SS - ((Epre k₀ g w).length + gr Rg.Mq))).map fun i =>
        [(Var.cel 0 k₀ ((Epre k₀ g w).length + gr Rg.Mq + i) none, true)] := by
    simp only [sem]
    rw [hTP, ← flatMap_single]
    apply List.flatMap_congr
    intro i _
    simp [sem, litCel, val, hX]
  simp only [iniT, sem_cat]
  rw [e1, e2, e3, sem_preT k₀ g w gr hN, e4, e5, e6]
  simp [ATK.CookLevinInicio.iniF, List.append_assoc]

/-- **O molde da fórmula de Cook–Levin.** -/
def formulaT (k₀ k₁ : K) (g : Bool → Γ k₀) (y : Γ k₁) (main : Λ) (s₀ : σ) :
    FT (Var K Γ Λ σ) (Rg C) :=
  .cat (estruturaT M) (.cat (iniT k₀ g main s₀) (aceitaT k₁ y))

/-- Os valores dos contadores que o molde exige. -/
structure RegOK (w : List Bool) (gr : Rg C → ℕ) : Prop where
  N : gr Rg.N = w.length
  E2 : gr Rg.E2 = 2 * w.length + 2
  X : gr Rg.X = gr Rg.E2 + gr Rg.Mq
  T1 : gr Rg.T1 = gr Rg.TT + 1
  TP : gr Rg.TP = gr Rg.SS - gr Rg.X
  sm : SmOK gr
  SS : profMax M + pushMax M ≤ gr Rg.SS

theorem sem_formulaT (k₀ k₁ : K) (g : Bool → Γ k₀) (y : Γ k₁) (main : Λ) (s₀ : σ)
    (w : List Bool) (gr : Rg C → ℕ) (hC : profMax M + pushMax M < C) (h : RegOK M w gr) :
    sem w (formulaT M k₀ k₁ g y main s₀) gr =
      formula M (gr Rg.TT) (gr Rg.SS)
        (ATK.CookLevinInicio.iniF k₀ (Epre k₀ g w) g (gr Rg.Mq) main s₀ (gr Rg.SS)) k₁ y := by
  simp only [formulaT, sem, formula, List.append_assoc]
  have hE : gr Rg.E2 = (Epre k₀ g w).length := by rw [h.E2, Epre_length]
  rw [sem_estruturaT M w gr hC h.sm h.SS h.T1,
    sem_iniT k₀ g main s₀ w gr h.N hE (by rw [h.X, hE]) (by rw [h.TP, h.X, hE]), sem_aceitaT]

/-! ### Boa formação -/

theorem sm_not_idx (c : ℕ) : ¬ idxR (Rg.sm c : Rg C) := by
  unfold Rg.sm idxR
  split_ifs <;> simp

theorem wf_umDeT {α : Type} [Fintype α] [DecidableEq α] (sc : Rg C → Prop)
    (mk : α → Bool → LT (Var K Γ Λ σ) (Rg C)) (h : ∀ x b, LitOK sc (mk x b)) :
    WF cod3 (umDeT mk) sc := by
  refine ⟨fun l hl => ?_, wf_manyF _ _ _ fun x hx => ?_⟩
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hl
    exact h x true
  · obtain ⟨x, -, rfl⟩ := List.mem_map.mp hx
    refine wf_manyF _ _ _ fun y hy => ?_
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hy
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact h x false
    · exact h y false

/-- Os conjuntos de índices dentro dos laços. -/
def sc1 : Rg C → Prop := fun x => idxR x ∧ x ≠ Rg.t
def sc2 : Rg C → Prop := fun x => sc1 x ∧ x ≠ Rg.j

theorem wf_linhaT : WF cod3 (linhaT (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) (C := C)) sc1 := by
  refine ⟨wf_umDeT _ _ fun o b => litLab_ok b o _ (by simp [sc1, idxR]),
    wf_umDeT _ _ fun v b => litSt_ok b v _ (by simp [sc1, idxR]),
    wf_manyF _ _ _ fun x hx => ?_⟩
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
  exact ⟨by simp [sc1, idxR], by simp [sc1, idxR],
    wf_umDeT _ _ fun a b => litCel_ok b k a _ _ (by simp [sc1, idxR])⟩

theorem wf_paraT : WF cod3 (paraT (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) (C := C)) sc1 := by
  refine ⟨wf_cl _ _ ?_, wf_manyF _ _ _ fun x hx => ?_, wf_manyF _ _ _ fun x hx => ?_⟩
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> exact litLab_ok _ _ _ (by simp [sc1, idxR])
  · obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact litLab_ok _ _ _ (by simp [sc1, idxR])
    · exact litSt_ok _ _ _ (by simp [sc1, idxR])
    · exact litSt_ok _ _ _ (by simp [sc1, idxR])
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    refine ⟨by simp [sc1, idxR], by simp [sc1, idxR], wf_manyF _ _ _ fun y hy => ?_⟩
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hy
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact litLab_ok _ _ _ (by simp [sc1, idxR])
    · exact litCel_ok _ _ _ _ _ (by simp [sc1, idxR])
    · exact litCel_ok _ _ _ _ _ (by simp [sc1, idxR])

theorem premT_ok (sc : Rg C → Prop) (ht : ¬ sc Rg.t) (c : Caso M) :
    ∀ l ∈ premT (C := C) M c, LitOK sc l := by
  intro l hl
  simp only [premT, List.mem_cons, List.mem_flatMap, List.mem_map] at hl
  rcases hl with rfl | rfl | ⟨k, -, i, -, rfl⟩
  · exact litLab_ok _ _ _ (by simpa using ht)
  · exact litSt_ok _ _ _ (by simpa using ht)
  · exact litCel_ok _ _ _ _ _ (by simpa using ht)

theorem wf_casoT (c : Caso M) : WF cod3 (casoT (C := C) M c) sc1 := by
  have hp1 := premT_ok (C := C) M sc1 (by simp [sc1]) c
  have hp2 := premT_ok (C := C) M sc2 (by simp [sc2, sc1]) c
  refine ⟨wf_cl _ _ ?_, wf_cl _ _ ?_, wf_manyF _ _ _ fun x hx => ?_⟩
  · intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact hp1 l hl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl; exact litLab_ok _ _ _ (by simp [sc1, idxR])
  · intro l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact hp1 l hl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      subst hl; exact litSt_ok _ _ _ (by simp [sc1, idxR])
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    refine ⟨wf_manyF _ _ _ fun y hy => ?_, ⟨fun h => sm_not_idx _ h.1, by simp [sc1, idxR],
      wf_manyF _ _ _ fun y hy => ?_⟩, wf_manyF _ _ _ fun y hy => ?_⟩
    · obtain ⟨p, -, rfl⟩ := List.mem_map.mp hy
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · exact hp1 l hl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        subst hl; exact litCel_ok _ _ _ _ _ (by simp [sc1, idxR])
    · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hy
      intro l hl
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hl
      rcases hl with rfl | hl | rfl
      · exact litCel_ok _ _ _ _ _ (by simp [sc2, sc1, idxR])
      · exact hp2 l hl
      · exact litCel_ok _ _ _ _ _ (by simp [sc2, sc1, idxR])
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
      intro l hl
      rcases List.mem_append.mp hl with hl | hl
      · exact hp1 l hl
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        subst hl
        exact litCel_ok _ _ _ _ _ (by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false, forall_eq_or_imp, forall_eq]
          exact ⟨by simp [sc1, idxR], fun h => sm_not_idx _ h.1⟩)

theorem wf_transT : WF cod3 (transT (C := C) M) sc1 :=
  ⟨wf_paraT, wf_manyF _ _ _ fun x hx => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hx
    exact wf_casoT M c⟩

theorem wf_estruturaT : WF cod3 (estruturaT (C := C) M) idxR :=
  ⟨⟨by simp [idxR], by simp [idxR], wf_linhaT⟩, ⟨by simp [idxR], by simp [idxR], wf_transT M⟩⟩

theorem wf_iniT (k₀ : K) (g : Bool → Γ k₀) (main : Λ) (s₀ : σ) :
    WF cod3 (iniT (C := C) k₀ g main s₀) idxR := by
  refine ⟨wf_cl _ _ ?_, wf_cl _ _ ?_, wf_manyF _ _ _ fun x hx => ?_, ⟨⟨by simp [idxR], ?_, ?_⟩,
    wf_cl _ _ ?_, wf_cl _ _ ?_⟩, ⟨by simp [idxR], by simp [idxR], wf_cl _ _ ?_⟩,
    ⟨by simp [idxR], by simp [idxR], wf_cl _ _ ?_⟩, ⟨by simp [idxR], by simp [idxR], wf_cl _ _ ?_⟩⟩
  all_goals first
    | (intro l hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl;
       first
        | (subst hl; first
            | exact litLab_ok _ _ _ (by simp [idxR])
            | exact litSt_ok _ _ _ (by simp [idxR])
            | exact litCel_ok _ _ _ _ _ (by simp [idxR]))
        | (rcases hl with rfl | rfl | rfl <;>
            exact litCel_ok _ _ _ _ _ (by simp [idxR]))
        | (rcases hl with rfl | rfl <;> exact litCel_ok _ _ _ _ _ (by simp [idxR])))
    | skip
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    split_ifs
    · trivial
    · exact ⟨by simp [idxR], by simp [idxR], fun l hl => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        subst hl; exact litCel_ok _ _ _ _ _ (by simp [idxR])⟩
  all_goals
    refine ⟨fun l hl => ?_, fun l hl => ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;>
    subst hl <;> exact litCel_ok _ _ _ _ _ (by simp [idxR])

theorem wf_aceitaT (k₁ : K) (y : Γ k₁) :
    WF cod3 (aceitaT (Λ := Λ) (σ := σ) (C := C) k₁ y) idxR := by
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩ <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl <;> subst hl
  · exact litLab_ok _ _ _ (by simp [idxR])
  · exact litCel_ok _ _ _ _ _ (by simp [idxR])

theorem wf_formulaT (k₀ k₁ : K) (g : Bool → Γ k₀) (y : Γ k₁) (main : Λ) (s₀ : σ) :
    WF cod3 (formulaT (C := C) M k₀ k₁ g y main s₀) idxR :=
  ⟨wf_estruturaT M, wf_iniT k₀ g main s₀, wf_aceitaT k₁ y⟩

end

end ATK.CookLevinMolde

#print axioms ATK.CookLevinMolde.Rg
#print axioms ATK.CookLevinMolde.Rg.N
#print axioms ATK.CookLevinMolde.Rg.Mq
#print axioms ATK.CookLevinMolde.Rg.X
#print axioms ATK.CookLevinMolde.Rg.TT
#print axioms ATK.CookLevinMolde.Rg.T1
#print axioms ATK.CookLevinMolde.Rg.SS
#print axioms ATK.CookLevinMolde.Rg.TP
#print axioms ATK.CookLevinMolde.Rg.pw
#print axioms ATK.CookLevinMolde.Rg.tm
#print axioms ATK.CookLevinMolde.Rg.t
#print axioms ATK.CookLevinMolde.Rg.j
#print axioms ATK.CookLevinMolde.Rg.i
#print axioms ATK.CookLevinMolde.Rg.E2
#print axioms ATK.CookLevinMolde.Rg.sm
#print axioms ATK.CookLevinMolde.idxR
#print axioms ATK.CookLevinMolde.varOf
#print axioms ATK.CookLevinMolde.idxD
#print axioms ATK.CookLevinMolde.cod3
#print axioms ATK.CookLevinMolde.litLab
#print axioms ATK.CookLevinMolde.litSt
#print axioms ATK.CookLevinMolde.litCel
#print axioms ATK.CookLevinMolde.LitOK
#print axioms ATK.CookLevinMolde.val_insens
#print axioms ATK.CookLevinMolde.litLab_ok
#print axioms ATK.CookLevinMolde.litSt_ok
#print axioms ATK.CookLevinMolde.litCel_ok
#print axioms ATK.CookLevinMolde.unS_eq
#print axioms ATK.CookLevinMolde.litOutV_cod3
#print axioms ATK.CookLevinMolde.fmOutV_cod3
#print axioms ATK.CookLevinMolde.sem_cat
#print axioms ATK.CookLevinMolde.manyF
#print axioms ATK.CookLevinMolde.sem_manyF
#print axioms ATK.CookLevinMolde.wf_manyF
#print axioms ATK.CookLevinMolde.wf_cl
#print axioms ATK.CookLevinMolde.umDeT
#print axioms ATK.CookLevinMolde.sem_umDeT
#print axioms ATK.CookLevinMolde.sem_manyF_cl
#print axioms ATK.CookLevinMolde.flatMap_single
#print axioms ATK.CookLevinMolde.val_t
#print axioms ATK.CookLevinMolde.val_r
#print axioms ATK.CookLevinMolde.val_c
#print axioms ATK.CookLevinMolde.T0
#print axioms ATK.CookLevinMolde.TS
#print axioms ATK.CookLevinMolde.J0
#print axioms ATK.CookLevinMolde.Z
#print axioms ATK.CookLevinMolde.linhaT
#print axioms ATK.CookLevinMolde.sem_linhaT
#print axioms ATK.CookLevinMolde.paraT
#print axioms ATK.CookLevinMolde.sem_paraT
#print axioms ATK.CookLevinMolde.range_zonas
#print axioms ATK.CookLevinMolde.premT
#print axioms ATK.CookLevinMolde.premT_v
#print axioms ATK.CookLevinMolde.celT
#print axioms ATK.CookLevinMolde.casoT
#print axioms ATK.CookLevinMolde.res_len_le
#print axioms ATK.CookLevinMolde.SmOK
#print axioms ATK.CookLevinMolde.sem_casoT
#print axioms ATK.CookLevinMolde.transT
#print axioms ATK.CookLevinMolde.sem_transT
#print axioms ATK.CookLevinMolde.estruturaT
#print axioms ATK.CookLevinMolde.SmOK_upd
#print axioms ATK.CookLevinMolde.sem_estruturaT
#print axioms ATK.CookLevinMolde.aceitaT
#print axioms ATK.CookLevinMolde.sem_aceitaT
#print axioms ATK.CookLevinMolde.dobro_get
#print axioms ATK.CookLevinMolde.dobro_length
#print axioms ATK.CookLevinMolde.Epre
#print axioms ATK.CookLevinMolde.Epre_length
#print axioms ATK.CookLevinMolde.celPre
#print axioms ATK.CookLevinMolde.rangeL_pre
#print axioms ATK.CookLevinMolde.sem_pre_range
#print axioms ATK.CookLevinMolde.preT
#print axioms ATK.CookLevinMolde.sem_preT
#print axioms ATK.CookLevinMolde.P2
#print axioms ATK.CookLevinMolde.P3
#print axioms ATK.CookLevinMolde.PX
#print axioms ATK.CookLevinMolde.iniT
#print axioms ATK.CookLevinMolde.sem_iniT
#print axioms ATK.CookLevinMolde.formulaT
#print axioms ATK.CookLevinMolde.RegOK
#print axioms ATK.CookLevinMolde.sem_formulaT
#print axioms ATK.CookLevinMolde.sm_not_idx
#print axioms ATK.CookLevinMolde.wf_umDeT
#print axioms ATK.CookLevinMolde.sc1
#print axioms ATK.CookLevinMolde.sc2
#print axioms ATK.CookLevinMolde.wf_linhaT
#print axioms ATK.CookLevinMolde.wf_paraT
#print axioms ATK.CookLevinMolde.premT_ok
#print axioms ATK.CookLevinMolde.wf_casoT
#print axioms ATK.CookLevinMolde.wf_transT
#print axioms ATK.CookLevinMolde.wf_estruturaT
#print axioms ATK.CookLevinMolde.wf_iniT
#print axioms ATK.CookLevinMolde.wf_aceitaT
#print axioms ATK.CookLevinMolde.wf_formulaT
