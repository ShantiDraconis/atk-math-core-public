import ATK.CookLevinVerificador
import ATK.SatNPMaquina

/-!
# ATK — Cook–Levin, marco CL4a: a redução como função `Palavra → Palavra`

* `cod`/`enc`: cada variável do tableau vira um natural cujos bits são
  `0^i 1 0^t 1 0^p 1` (`i` = índice finito do rótulo/estado/símbolo, `t` = instante, `p` = célula):
  injetiva e fácil de escrever por uma máquina (só contadores unários);
* `satisfativel_mapF`: renomear as variáveis por uma injeção preserva a satisfatibilidade;
* `mem_SAT_codCNF`: `codCNF ψ ∈ SAT ⟺ ψ` satisfatível (usa o verificador de SAT ∈ NP);
* **`fCL_correta`**: para `L ∈ NP` com verificador `V` e polinômio `q`,
  `w ∈ L ⟺ fCL V q w ∈ SAT`, onde `fCL V q w = codCNF (fórmula de Cook–Levin de w)`;
* **`cookLevin_de_computavel`**: se toda `fCL V q` é computável por uma `FinTM2` em tempo
  polinomial, então `CookLevin modeloPNP SAT` (a ponte B4).

A hipótese de `cookLevin_de_computavel` é descarregada em `ATK.CookLevinFinal.fCL_computavel`
(CL4b: a máquina que escreve a fórmula); `ATK.CookLevinFinal.cookLevin` fecha B4.
**CLOSED_MATH continua false.**
-/

namespace ATK.CookLevinReducao

open Turing Function ATK.CookLevinTableau ATK.CookLevinVerificador ATK.ModeloPNP ATK.LigacaoPNP
open Computability
open scoped Classical

set_option linter.unusedSectionVars false

noncomputable section

/-! ### Codificação unária das variáveis -/

/-- `0^n 1`. -/
def u (n : ℕ) : List Bool := List.replicate n false ++ [true]

theorem u_append_inj : ∀ {a b : ℕ} {l l' : List Bool}, u a ++ l = u b ++ l' → a = b ∧ l = l'
  | 0, 0, l, l', h => by simpa [u] using h
  | 0, b + 1, l, l', h => by simp [u, List.replicate_succ] at h
  | a + 1, 0, l, l', h => by simp [u, List.replicate_succ] at h
  | a + 1, b + 1, l, l', h => by
    simp only [u, List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    have := u_append_inj (a := a) (b := b) (l := l) (l' := l') (by simpa [u] using h)
    exact ⟨by rw [this.1], this.2⟩

variable {K : Type} [DecidableEq K] [Fintype K] {Γ : K → Type} [∀ k, Fintype (Γ k)]
  {Λ : Type} [Fintype Λ] {σ : Type} [Fintype σ]

/-- O tipo finito dos dados de uma variável (sem instante nem célula). -/
abbrev Dado (K : Type) (Γ : K → Type) (Λ σ : Type) := Option Λ ⊕ σ ⊕ (Σ k, Option (Γ k))

def dado : Var K Γ Λ σ → Dado K Γ Λ σ
  | .lab _ o => .inl o
  | .st _ v => .inr (.inl v)
  | .cel _ k _ a => .inr (.inr ⟨k, a⟩)

def inst : Var K Γ Λ σ → ℕ
  | .lab t _ => t
  | .st t _ => t
  | .cel t _ _ _ => t

def celula : Var K Γ Λ σ → ℕ
  | .cel _ _ p _ => p
  | _ => 0

theorem var_ext : ∀ {v v' : Var K Γ Λ σ}, dado v = dado v' → inst v = inst v' →
    celula v = celula v' → v = v'
  | .lab t o, .lab t' o', h1, h2, _ => by
    simp only [dado, Sum.inl.injEq] at h1; simp only [inst] at h2; subst h1 h2; rfl
  | .st t s, .st t' s', h1, h2, _ => by
    simp only [dado, Sum.inr.injEq, Sum.inl.injEq] at h1; simp only [inst] at h2; subst h1 h2; rfl
  | .cel t k p a, .cel t' k' p' a', h1, h2, h3 => by
    simp only [dado, Sum.inr.injEq] at h1
    simp only [inst] at h2
    simp only [celula] at h3
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h1
    subst h2 h3
    rw [eq_of_heq h]
  | .lab _ _, .st _ _, h, _, _ => by simp [dado] at h
  | .lab _ _, .cel _ _ _ _, h, _, _ => by simp [dado] at h
  | .st _ _, .lab _ _, h, _, _ => by simp [dado] at h
  | .st _ _, .cel _ _ _ _, h, _, _ => by simp [dado] at h
  | .cel _ _ _ _, .lab _ _, h, _, _ => by simp [dado] at h
  | .cel _ _ _ _, .st _ _, h, _, _ => by simp [dado] at h

/-- Índice do dado finito. -/
def idx (v : Var K Γ Λ σ) : ℕ := (Fintype.equivFin (Dado K Γ Λ σ) (dado v)).val

/-- Os bits da variável: `0^idx 1 0^t 1 0^p 1`. -/
def code (v : Var K Γ Λ σ) : List Bool := u (idx v) ++ u (inst v) ++ u (celula v)

/-- O natural da variável. -/
def enc (v : Var K Γ Λ σ) : ℕ := ATK.SatNPSemantica.ofBits (code v)

theorem code_canon (v : Var K Γ Λ σ) : ATK.SatNPSemantica.Canon (code v) := by
  right
  have : code v = (u (idx v) ++ u (inst v) ++ List.replicate (celula v) false) ++ [true] := by
    simp [code, u]
  rw [this, List.getLast?_concat]

theorem bits_enc (v : Var K Γ Λ σ) : (enc v).bits = code v :=
  ATK.SatNPSemantica.bits_ofBits _ (code_canon v)

theorem code_injective : Function.Injective (code (K := K) (Γ := Γ) (Λ := Λ) (σ := σ)) := by
  intro v v' h
  simp only [code, List.append_assoc] at h
  obtain ⟨h1, h⟩ := u_append_inj h
  obtain ⟨h2, h⟩ := u_append_inj h
  have h3 : celula v = celula v' := (u_append_inj (l := []) (l' := []) (by simpa using h)).1
  refine var_ext ?_ h2 h3
  have := Fin.ext (n := Fintype.card (Dado K Γ Λ σ)) h1
  exact (Fintype.equivFin _).injective this

theorem enc_injective : Function.Injective (enc (K := K) (Γ := Γ) (Λ := Λ) (σ := σ)) := by
  intro v v' h
  apply code_injective
  rw [← bits_enc, ← bits_enc, h]

/-! ### Renomear variáveis preserva a satisfatibilidade -/

/-- A fórmula com variáveis naturais. -/
def mapF {V : Type*} (e : V → ℕ) (φ : Fm V) : CNF := φ.map (List.map fun ℓ => (e ℓ.1, ℓ.2))

theorem satisfativel_mapF {V : Type*} {e : V → ℕ} (he : Function.Injective e) (φ : Fm V) :
    Satisfativel (mapF e φ) ↔ ∃ τ, Sat τ φ := by
  constructor
  · rintro ⟨τ', h⟩
    refine ⟨τ' ∘ e, fun C hC => ?_⟩
    obtain ⟨ℓ, hℓ, hτ⟩ := h _ (List.mem_map.mpr ⟨C, hC, rfl⟩)
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hℓ
    exact ⟨m, hm, hτ⟩
  · rintro ⟨τ, h⟩
    refine ⟨fun n => if hn : ∃ v, e v = n then τ hn.choose else false, fun C' hC' => ?_⟩
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hC'
    obtain ⟨m, hm, hτ⟩ := h C hC
    refine ⟨(e m.1, m.2), List.mem_map.mpr ⟨m, hm, rfl⟩, ?_⟩
    have hex : ∃ v, e v = e m.1 := ⟨m.1, rfl⟩
    simp only [hex, dite_true]
    rw [he hex.choose_spec]
    exact hτ

/-! ### `codCNF ψ ∈ SAT ⟺ ψ` satisfatível -/

theorem mem_SAT_codCNF (ψ : CNF) : codCNF ψ ∈ SAT ↔ Satisfativel ψ := by
  constructor
  · intro h
    obtain ⟨c, -, hc⟩ := (ATK.SatNPSemantica.sat_iff_verif _).mp h
    rw [ATK.SatNPSemantica.verif_codCNF, ← ATK.SatNPSemantica.satisfaz_iff] at hc
    exact ⟨_, hc⟩
  · intro h
    exact ⟨ψ, rfl, h⟩

/-! ### A redução de Cook–Levin -/

section Reducao

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable {χ : Palavra → Bool} (V : TM2ComputableInPolyTime cod encodeBool χ) (q : Polynomial ℕ)

/-- **A redução de Cook–Levin**: a codificação binária da fórmula do verificador para `w`. -/
def fCL (w : Palavra) : Palavra :=
  codCNF (mapF enc (formulaW V (q.eval w.length) w))

/-- **Correção da redução.** -/
theorem fCL_correta {L : Linguagem}
    (hL : ∀ w, w ∈ L ↔ ∃ c : Palavra, c.length ≤ q.eval w.length ∧ χ (par w c) = true)
    (w : Palavra) : w ∈ L ↔ fCL V q w ∈ SAT := by
  rw [fCL, mem_SAT_codCNF, satisfativel_mapF enc_injective, verificador_tableau, hL]

/-- Com a computabilidade de `fCL`, `L ≤p SAT`. -/
theorem red_de_computavel {L : Linguagem}
    (hL : ∀ w, w ∈ L ↔ ∃ c : Palavra, c.length ≤ q.eval w.length ∧ χ (par w c) = true)
    (hf : Nonempty (TM2ComputableInPolyTime cod cod (fCL V q))) : Red L SAT :=
  ⟨fCL V q, fCL_correta V q hL, hf⟩

end Reducao

/-- **Cook–Levin, módulo a máquina da redução (CL4b).** Se cada `fCL V q` é computável por uma
`FinTM2` em tempo polinomial, então SAT é NP-completo no modelo genuíno. -/
theorem cookLevin_de_computavel
    (hf : ∀ (χ : Palavra → Bool) (V : TM2ComputableInPolyTime cod encodeBool χ)
      (q : Polynomial ℕ), Nonempty (TM2ComputableInPolyTime cod cod (fCL V q))) :
    ATK.Conditional.PvsNP.CookLevin modeloPNP SAT := by
  refine ⟨ATK.SatNPMaquina.sat_em_NP, fun L hL => ?_⟩
  obtain ⟨Vl, ⟨χ, hχ, ⟨V⟩⟩, q, hq⟩ := hL
  exact red_de_computavel V q (fun w => by simp only [hq w, hχ]) (hf χ V q)

end

end ATK.CookLevinReducao

#print axioms ATK.CookLevinReducao.u
#print axioms ATK.CookLevinReducao.u_append_inj
#print axioms ATK.CookLevinReducao.Dado
#print axioms ATK.CookLevinReducao.dado
#print axioms ATK.CookLevinReducao.inst
#print axioms ATK.CookLevinReducao.celula
#print axioms ATK.CookLevinReducao.var_ext
#print axioms ATK.CookLevinReducao.idx
#print axioms ATK.CookLevinReducao.code
#print axioms ATK.CookLevinReducao.enc
#print axioms ATK.CookLevinReducao.code_canon
#print axioms ATK.CookLevinReducao.bits_enc
#print axioms ATK.CookLevinReducao.code_injective
#print axioms ATK.CookLevinReducao.enc_injective
#print axioms ATK.CookLevinReducao.mapF
#print axioms ATK.CookLevinReducao.satisfativel_mapF
#print axioms ATK.CookLevinReducao.mem_SAT_codCNF
#print axioms ATK.CookLevinReducao.fCL
#print axioms ATK.CookLevinReducao.fCL_correta
#print axioms ATK.CookLevinReducao.red_de_computavel
#print axioms ATK.CookLevinReducao.cookLevin_de_computavel
