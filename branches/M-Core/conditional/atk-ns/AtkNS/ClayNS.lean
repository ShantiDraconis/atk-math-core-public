import AtkNS.FCDefinicoes
import NavierStokes.ComparatorSolution

/-!
# ATK — Verificação independente: o problema do milênio de Navier–Stokes (Clay)

O Clay pede a prova de **uma** das quatro alternativas (Fefferman, *Existence and smoothness of
the Navier–Stokes equation*):

* (A) existência global suave em `ℝ³` (sem força);
* (B) existência global suave no toro `ℝ³/ℤ³` (sem força);
* (C) explosão em `ℝ³`: existem dado inicial e força, suaves e com decaimento, sem solução suave
  global de energia limitada;
* (D) explosão no toro.

Em setembro de 2026 a OpenAI publicou uma prova formal em Lean de (C) e (D)
([`openai/NavierStokesAndEuler`](https://github.com/openai/NavierStokesAndEuler),
commit `8937a8f`). Este arquivo:

* usa as definições **copiadas do formal-conjectures** (`ATK.FC.NS`, cópia independente da da
  OpenAI) para enunciar `ClayA`, `ClayB`, `ClayC`, `ClayD` e `ClayNS := A ∨ B ∨ C ∨ D`;
* converte, campo a campo, as estruturas da OpenAI nas do formal-conjectures;
* prova `clayC`, `clayD` e **`clayNS`** a partir dos teoremas da OpenAI.

O CI deste subprojeto compila a prova da OpenAI a partir do código-fonte e audita os axiomas.

**O que isto NÃO é.** Não é trabalho do ATK: a prova é da OpenAI. Também não prova (A): a
existência global sem força continua aberta, e é ela que a obrigação O3 do ATK ataca.
-/

namespace ATK.ClayNS

open ATK.FC.NS

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## As quatro alternativas, com as definições do formal-conjectures -/

/-- (A) Existência e suavidade em `ℝ³`, sem força. -/
def ClayA : Prop :=
  ∀ nu : ℝ, nu > 0 → ∀ u₀ : ℝ³ → ℝ³, InitialVelocityConditionDecay u₀ →
    ∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ 0 v p

/-- (B) Existência e suavidade no toro, sem força. -/
def ClayB : Prop :=
  ∀ nu : ℝ, nu > 0 → ∀ u₀ : ℝ³ → ℝ³, InitialVelocityConditionPeriodic u₀ →
    ∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ 0 v p

/-- (C) Explosão em `ℝ³`, com força. -/
def ClayC : Prop :=
  ∀ nu : ℝ, nu > 0 → ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
      ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p)

/-- (D) Explosão no toro, com força. -/
def ClayD : Prop :=
  ∀ nu : ℝ, nu > 0 → ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionPeriodic u₀ ∧ ForceConditionPeriodic f ∧
      ¬ (∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p)

/-- **O problema do milênio de Navier–Stokes**: provar uma das quatro alternativas. -/
def ClayNS : Prop := ClayA ∨ ClayB ∨ ClayC ∨ ClayD

/-! ## Das estruturas da OpenAI para as do formal-conjectures -/

section Conversao

variable {u₀ : ℝ³ → ℝ³} {f : ℝ³ → ℝ → ℝ³} {nu : ℝ} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}

theorem ivcDecay (h : NavierStokes.Comparator.InitialVelocityConditionDecay u₀) :
    InitialVelocityConditionDecay u₀ :=
  { div_free := h.div_free, smooth := h.smooth, decay := h.decay }

theorem ivcPeriodic (h : NavierStokes.Comparator.InitialVelocityConditionPeriodic u₀) :
    InitialVelocityConditionPeriodic u₀ :=
  { div_free := h.div_free, smooth := h.smooth, isOnePeriodic := h.isOnePeriodic }

theorem fcDecay (h : NavierStokes.Comparator.ForceConditionDecay f) : ForceConditionDecay f :=
  { smooth := h.smooth, decay := h.decay }

theorem fcPeriodic (h : NavierStokes.Comparator.ForceConditionPeriodic f) :
    ForceConditionPeriodic f :=
  { smooth := h.smooth, isOnePeriodic := h.isOnePeriodic, decay := h.decay }

/-- No sentido contrário (o enunciado de explosão nega a existência de solução). -/
theorem solRn (h : NavierStokesExistenceAndSmoothnessRn nu u₀ f v p) :
    NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn nu u₀ f v p :=
  { navier_stokes := h.navier_stokes, div_free := h.div_free,
    initial_condition := h.initial_condition, velocity_smooth := h.velocity_smooth,
    pressure_smooth := h.pressure_smooth, integrable := h.integrable,
    globally_bounded_energy := h.globally_bounded_energy }

theorem solPeriodic (h : NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p) :
    NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p :=
  { navier_stokes := h.navier_stokes, div_free := h.div_free,
    initial_condition := h.initial_condition, velocity_smooth := h.velocity_smooth,
    pressure_smooth := h.pressure_smooth, isOnePeriodic_velocity := h.isOnePeriodic_velocity,
    isOnePeriodic_pressure := h.isOnePeriodic_pressure }

end Conversao

/-! ## (C), (D) e o problema do milênio -/

/-- **(C)**, pela prova da OpenAI, no enunciado do formal-conjectures. -/
theorem clayC : ClayC := by
  intro nu hnu
  obtain ⟨u₀, f, h₁, h₂, h₃⟩ := NavierStokes.Comparator.navier_stokes_breakdown_R3 nu hnu
  exact ⟨u₀, f, ivcDecay h₁, fcDecay h₂, fun ⟨v, p, h⟩ => h₃ ⟨v, p, solRn h⟩⟩

/-- **(D)**, pela prova da OpenAI, no enunciado do formal-conjectures. -/
theorem clayD : ClayD := by
  intro nu hnu
  obtain ⟨u₀, f, h₁, h₂, h₃⟩ := NavierStokes.Comparator.navier_stokes_breakdown_periodic nu hnu
  exact ⟨u₀, f, ivcPeriodic h₁, fcPeriodic h₂, fun ⟨v, p, h⟩ => h₃ ⟨v, p, solPeriodic h⟩⟩

/-- **O problema do milênio de Navier–Stokes, na formulação do Clay** (via (C)). -/
theorem clayNS : ClayNS := Or.inr (Or.inr (Or.inl clayC))

end ATK.ClayNS

#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_periodic
#print axioms ATK.ClayNS.ivcDecay
#print axioms ATK.ClayNS.ivcPeriodic
#print axioms ATK.ClayNS.fcDecay
#print axioms ATK.ClayNS.fcPeriodic
#print axioms ATK.ClayNS.solRn
#print axioms ATK.ClayNS.solPeriodic
#print axioms ATK.ClayNS.clayC
#print axioms ATK.ClayNS.clayD
#print axioms ATK.ClayNS.clayNS
