import ATK.Conditional.NavierStokes
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# ATK — Ligação L1: o modelo genuíno de Navier–Stokes (enunciado (A) do Clay)

`ATK.Conditional.NavierStokes.NSModel` é uma interface. Este arquivo a preenche com os
**objetos reais** da Mathlib, seguindo o texto oficial do Clay (Fefferman, 2000), caso (A):

> Tome `ν > 0` e `n = 3`. Seja `u°(x)` um campo suave, de divergência nula, com
> `|∂ₓ^α u°(x)| ≤ C_{αK} (1 + |x|)^{−K}` para todo `α` e `K` (4). Tome `f ≡ 0`. Então existem
> funções suaves `p, u` em `ℝ³ × [0, ∞)` que satisfazem (1) `∂ₜu + (u·∇)u = νΔu − ∇p`,
> (2) `div u = 0`, (3) `u(x, 0) = u°(x)`, (6) `p, u ∈ C^∞(ℝ³ × [0, ∞))` e
> (7) `∫_{ℝ³} |u(x, t)|² dx < C` para todo `t ≥ 0`.

Tradução:

* espaço `E3 = EuclideanSpace ℝ (Fin 3)`, derivadas parciais `dX j f x = Df(x)(e_j)`;
* (4) é exatamente a classe de Schwartz `𝓢(ℝ³, ℝ³)` da Mathlib (decaimento rápido de todas as
  derivadas);
* (6) é `ContDiffOn ℝ ∞` em `ℝ³ × [0, ∞)` (suave, `∞`, não analítico `ω`);
* (1) é imposta para `t > 0`; em `t = 0` ela segue por continuidade de (6);
* (7) inclui a integrabilidade (sem ela a integral de Bochner valeria 0 por convenção).

Resultado: `clayA_iff` — o enunciado paramétrico `ClayStatementA modeloNS` **é** o enunciado (A)
do Clay. Testes de fidelidade: o dado nulo é admissível e tem solução global (`zero_global`); o
campo `x ↦ x` não é admissível (`div = 3`); o fluxo `u = t·v`, `p = −⟨v, x⟩` resolve (1)–(2) mas
viola (7) (`fluxo_sem_energia`) — a condição de energia exclui o exemplo clássico de não
unicidade.

`SmoothOn` e `enstrophy` (usados pela ponte B3 e pela obrigação O3) seguem a teoria local
clássica: solução suave em `[0, T)` com energia finita em cada `[0, T']`, `T' < T`, e enstrofia
`∫ |∇u|²`. Por unicidade (Leray; Kato) há uma só solução nessa classe; `enstrophy` toma o supremo
sobre as soluções, que então é o valor da solução.

Isto não prova nada sobre Navier–Stokes: só fixa o objeto. **CLOSED_MATH continua false.**
-/

open MeasureTheory Set
open scoped ContDiff

namespace ATK.LigacaoNS

/-- O espaço `ℝ³`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Vetor da base canônica `e_j`. -/
noncomputable abbrev e (j : Fin 3) : E3 := EuclideanSpace.single j 1

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Derivada parcial `∂_j f (x) = Df(x) e_j`. -/
noncomputable def dX (j : Fin 3) (f : E3 → V) (x : E3) : V := fderiv ℝ f x (e j)

/-- Divergência `div u = Σ_j ∂_j u_j`. -/
noncomputable def div (u : E3 → E3) (x : E3) : ℝ := ∑ j, dX j u x j

/-- Laplaciano `Δf = Σ_j ∂_j ∂_j f`. -/
noncomputable def lap (f : E3 → V) (x : E3) : V := ∑ j, dX j (dX j f) x

/-- Termo convectivo `(u·∇)u = Σ_j u_j ∂_j u`. -/
noncomputable def conv (u : E3 → E3) (x : E3) : E3 := ∑ j, u x j • dX j u x

/-- Gradiente `∇p = Σ_j (∂_j p) e_j`. -/
noncomputable def grad (p : E3 → ℝ) (x : E3) : E3 := ∑ j, dX j p x • e j

/-- `|∇u|² = Σ_j |∂_j u|²`. -/
noncomputable def gradSq (u : E3 → E3) (x : E3) : ℝ := ∑ j, ‖dX j u x‖ ^ 2

/-- Fatia no tempo `t`. -/
def fatia {W : Type*} (U : E3 × ℝ → W) (t : ℝ) : E3 → W := fun y => U (y, t)

theorem fatia_eq {W : Type*} (U : E3 × ℝ → W) (t : ℝ) : fatia U t = fun y => U (y, t) := rfl

/-- Equação (1) com `f ≡ 0`: `∂ₜu + (u·∇)u = νΔu − ∇p` no ponto `(x, t)`. -/
def NSEq (ν : ℝ) (U : E3 × ℝ → E3) (P : E3 × ℝ → ℝ) (x : E3) (t : ℝ) : Prop :=
  deriv (fun s => U (x, s)) t + conv (fatia U t) x = ν • lap (fatia U t) x - grad (fatia P t) x

/-- Energia `∫ |u(x, t)|² dx` finita e `≤ C`. -/
def EnergiaAte (U : E3 × ℝ → E3) (t C : ℝ) : Prop :=
  Integrable (fun x => ‖U (x, t)‖ ^ 2) ∧ ∫ x, ‖U (x, t)‖ ^ 2 ≤ C

/-- Solução suave global de energia limitada: (1), (2), (3), (6), (7) do Clay. -/
def SolucaoGlobal (ν : ℝ) (u₀ : E3 → E3) (U : E3 × ℝ → E3) (P : E3 × ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ U (univ ×ˢ Ici 0) ∧ ContDiffOn ℝ ∞ P (univ ×ˢ Ici 0) ∧
    (∀ x, U (x, 0) = u₀ x) ∧
    (∀ x, ∀ t, 0 < t → NSEq ν U P x t) ∧
    (∀ x, ∀ t, 0 ≤ t → div (fatia U t) x = 0) ∧
    ∃ C, ∀ t, 0 ≤ t → EnergiaAte U t C

/-- Solução suave em `[0, T)`, com energia e enstrofia finitas em cada `[0, T']`, `T' < T`. -/
def SolucaoLocal (ν : ℝ) (u₀ : E3 → E3) (T : ℝ) (U : E3 × ℝ → E3) (P : E3 × ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ U (univ ×ˢ Ico 0 T) ∧ ContDiffOn ℝ ∞ P (univ ×ˢ Ico 0 T) ∧
    (∀ x, U (x, 0) = u₀ x) ∧
    (∀ x, ∀ t ∈ Ioo 0 T, NSEq ν U P x t) ∧
    (∀ x, ∀ t ∈ Ico 0 T, div (fatia U t) x = 0) ∧
    ∀ T' < T, ∃ C, ∀ t ∈ Icc 0 T', EnergiaAte U t C ∧
      Integrable (gradSq (fatia U t)) ∧ ∫ x, gradSq (fatia U t) x ≤ C

/-- Dado inicial (4): `ν > 0`, `u°` de Schwartz e de divergência nula. -/
def Admissivel (d : ℝ × (E3 → E3)) : Prop :=
  0 < d.1 ∧ (∃ S : SchwartzMap E3 E3, ⇑S = d.2) ∧ ∀ x, div d.2 x = 0

/-- **O modelo genuíno de Navier–Stokes.** -/
noncomputable def modeloNS : ATK.Conditional.NavierStokes.NSModel.{0} where
  Data := ℝ × (E3 → E3)
  Admissible := Admissivel
  SmoothOn d T := ∃ U P, SolucaoLocal d.1 d.2 T U P
  GlobalSmooth d := ∃ U P, SolucaoGlobal d.1 d.2 U P
  enstrophy d t := sSup {E | ∃ T U P, t < T ∧ SolucaoLocal d.1 d.2 T U P ∧
    E = ∫ x, gradSq (fatia U t) x}

/-- **Fidelidade**: o enunciado paramétrico sobre `modeloNS` é o enunciado (A) do Clay. -/
theorem clayA_iff :
    ATK.Conditional.NavierStokes.ClayStatementA modeloNS ↔
      ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzMap E3 E3, (∀ x, div u₀ x = 0) →
        ∃ U P, SolucaoGlobal ν u₀ U P := by
  constructor
  · intro h ν hν u₀ hdiv
    exact h (ν, u₀) ⟨hν, ⟨u₀, rfl⟩, hdiv⟩
  · rintro h ⟨ν, u₀⟩ ⟨hν, ⟨S, rfl⟩, hdiv⟩
    exact h ν hν S hdiv

/-! ### Testes de fidelidade -/

theorem dX_const (j : Fin 3) (c : V) (x : E3) : dX j (fun _ : E3 => c) x = 0 := by
  simp [dX]

theorem dX_const_fun (j : Fin 3) (c : V) : dX j (fun _ : E3 => c) = fun _ => 0 := by
  funext x
  simp [dX]

/-- `Σ_j v_j e_j = v`. -/
theorem sum_coord (v : E3) : ∑ j, v j • e j = v := by
  have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  simpa [e] using this

/-- `∇⟨v, ·⟩ = v`. -/
theorem grad_inner (v x : E3) : grad (fun y => inner ℝ v y) x = v := by
  have hf : (fun y : E3 => inner ℝ v y) = ⇑(innerSL ℝ v) := rfl
  unfold grad dX
  rw [hf, ContinuousLinearMap.fderiv]
  have hc : ∀ j, (innerSL ℝ v) (e j) = v j := fun j => by
    simp [e, EuclideanSpace.inner_single_right]
  simp only [hc]
  exact sum_coord v

theorem div_zero (x : E3) : div (fun _ => 0) x = 0 := by
  simp [div, dX]

/-- O dado nulo é admissível. -/
theorem zero_admissivel {ν : ℝ} (hν : 0 < ν) : modeloNS.Admissible (ν, fun _ => 0) :=
  ⟨hν, ⟨0, rfl⟩, div_zero⟩

/-- O dado nulo tem solução global suave de energia limitada (`u = 0`, `p = 0`). -/
theorem zero_global (ν : ℝ) : modeloNS.GlobalSmooth (ν, fun _ => 0) := by
  refine ⟨fun _ => 0, fun _ => 0, contDiffOn_const, contDiffOn_const, fun _ => rfl,
    fun x t _ => ?_, fun x t _ => ?_, ⟨0, fun t _ => ⟨?_, ?_⟩⟩⟩
  · simp [NSEq, conv, lap, grad, fatia_eq, dX_const_fun, dX_const]
  · simpa [fatia_eq] using div_zero x
  · simp
  · simp

/-- `div (x ↦ x) = 3`. -/
theorem div_id (x : E3) : div (fun y => y) x = 3 := by
  simp [div, dX, e]

/-- O campo `x ↦ x` (com qualquer `ν`) não é admissível: a divergência não é nula. -/
theorem id_nao_admissivel (ν : ℝ) : ¬ modeloNS.Admissible (ν, fun y => y) := by
  rintro ⟨_, _, h⟩
  have := h 0
  rw [div_id] at this
  norm_num at this

/-- O volume de `ℝ³` é infinito. -/
theorem volume_univ_E3 : (volume : Measure E3) univ = ⊤ :=
  measure_univ_of_isAddLeftInvariant volume

/-- **O exemplo clássico de não unicidade viola a energia.** O fluxo uniforme acelerado
`u(x, t) = t·v`, `p(x, t) = −⟨v, x⟩` satisfaz (1) e (2) em todo ponto, mas para `v ≠ 0` e
`t > 0` a energia `∫ |u|²` não é finita: (7) o exclui. -/
theorem fluxo_sem_energia (ν : ℝ) (v : E3) :
    (∀ x t, NSEq ν (fun z => z.2 • v) (fun z => -inner ℝ v z.1) x t) ∧
      (∀ x t, div (fatia (fun z : E3 × ℝ => z.2 • v) t) x = 0) ∧
      (v ≠ 0 → ∀ t, 0 < t → ∀ C, ¬ EnergiaAte (fun z : E3 × ℝ => z.2 • v) t C) := by
  refine ⟨fun x t => ?_, fun x t => ?_, fun hv t ht C hE => ?_⟩
  · have hP : fatia (fun z : E3 × ℝ => -inner ℝ v z.1) t = fun y => -inner ℝ v y := rfl
    have hgrad : grad (fun y => -inner ℝ v y) x = -v := by
      have h1 : (fun y : E3 => -inner ℝ v y) = fun y => inner ℝ (-v) y := by
        funext y
        simp [inner_neg_left]
      rw [h1, grad_inner]
    simp only [NSEq, hP, hgrad, fatia_eq, conv, lap, dX_const_fun, dX_const, smul_zero,
      Finset.sum_const_zero, sub_neg_eq_add, zero_add, add_zero]
    simpa using ((hasDerivAt_id t).smul_const v).deriv
  · simp [div, dX, fatia_eq]
  · have hne : ‖t • v‖ ^ 2 ≠ 0 := by
      have : t • v ≠ 0 := smul_ne_zero ht.ne' hv
      positivity
    have hI : Integrable (fun _ : E3 => ‖t • v‖ ^ 2) volume := hE.1
    rw [integrable_const_iff] at hI
    rcases hI with hI | hI
    · exact hne hI
    · have := hI.measure_univ_lt_top
      rw [volume_univ_E3] at this
      exact lt_irrefl _ this

/-- `GlobalSmooth` não é trivial (contraste com `ns_toy_model_vacuous`): um dado constante
`v ≠ 0` não tem solução global de energia limitada (já em `t = 0` a energia é infinita). -/
theorem global_nao_trivial (ν : ℝ) {v : E3} (hv : v ≠ 0) :
    ¬ modeloNS.GlobalSmooth (ν, fun _ => v) := by
  rintro ⟨U, P, -, -, h0, -, -, C, hE⟩
  have hI : Integrable (fun x : E3 => ‖U (x, 0)‖ ^ 2) volume := (hE 0 le_rfl).1
  have h0' : (fun x : E3 => ‖U (x, 0)‖ ^ 2) = fun _ => ‖v‖ ^ 2 := by
    funext x
    rw [h0 x]
  rw [h0', integrable_const_iff] at hI
  rcases hI with hI | hI
  · exact hv (by simpa using hI)
  · have := hI.measure_univ_lt_top
    rw [volume_univ_E3] at this
    exact lt_irrefl _ this

/-- **Navier–Stokes de Clay (A), condicional, sobre o objeto real**: a ponte B3 e a obrigação O3
no modelo genuíno dão o enunciado oficial. -/
theorem clay_ns_condicional
    (hB3 : ATK.Conditional.NavierStokes.EnstrophyBlowupCriterion modeloNS)
    (hO3 : ATK.Conditional.NavierStokes.EnstrophyAPrioriBound modeloNS) :
    ∀ ν : ℝ, 0 < ν → ∀ u₀ : SchwartzMap E3 E3, (∀ x, div u₀ x = 0) →
      ∃ U P, SolucaoGlobal ν u₀ U P :=
  clayA_iff.mp (ATK.Conditional.NavierStokes.ns_conditional hB3 hO3)

end ATK.LigacaoNS

#print axioms ATK.LigacaoNS.fatia_eq
#print axioms ATK.LigacaoNS.clayA_iff
#print axioms ATK.LigacaoNS.dX_const
#print axioms ATK.LigacaoNS.dX_const_fun
#print axioms ATK.LigacaoNS.sum_coord
#print axioms ATK.LigacaoNS.grad_inner
#print axioms ATK.LigacaoNS.div_zero
#print axioms ATK.LigacaoNS.zero_admissivel
#print axioms ATK.LigacaoNS.zero_global
#print axioms ATK.LigacaoNS.div_id
#print axioms ATK.LigacaoNS.id_nao_admissivel
#print axioms ATK.LigacaoNS.volume_univ_E3
#print axioms ATK.LigacaoNS.fluxo_sem_energia
#print axioms ATK.LigacaoNS.global_nao_trivial
#print axioms ATK.LigacaoNS.clay_ns_condicional
