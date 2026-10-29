import ATK.YMReconstrucao

/-!
# ATK — Laço de Wilson no modelo de rede ℤ₂ (lei de área explícita)

`ATK.YMToy`'s docstring already states, in prose, that the Ising chain is the gauge-fixed
reduction of the 2D `ℤ₂` lattice gauge theory, and that the area-`A` Wilson loop there equals
`tanh(β)^A`. That identification was never named as a Lean definition or proved as a Lean
theorem — it lived only in a comment. This module closes that gap: it names the Wilson-loop
expectation value explicitly and proves the area law as an auditable theorem, directly from the
already-certified `ATK.YMToy`/`ATK.YMReconstrucao` facts (`correl_eq`, `razao_eq_tanh`,
`correl_exp`). No new physics is assumed; this is bookkeeping that turns a prose claim into a
kernel-checked one.

Scope: this strengthens bridge B7's formal content (Osterwalder–Schrader reconstruction, in
miniature) for the exactly solvable abelian 2D model. It does **not** touch obligation O8
(constructive 4D non-abelian Yang–Mills with a continuum mass gap), which remains `OPEN_MATH`.
-/

namespace ATK.YMWilsonLoop

open ATK.YMToy

/-- Expectation value of the rectangular Wilson loop of area `A`, in the 2D `ℤ₂` lattice gauge
theory obtained by gauge-fixing the `ATK.YMToy` chain. By the chain's own duality (stated in
`ATK.YMToy`'s module docstring), this is exactly the spin-spin correlation at distance `A`. -/
noncomputable def wilsonLoop (β : ℝ) (A : ℕ) : ℝ := correl β A

/-- **Area law**: the Wilson loop decays as `tanh(β) ^ A`, i.e. exponentially in the loop's
area — the defining signature of confinement in a 2D abelian lattice gauge theory. -/
theorem wilson_area_law (β : ℝ) (A : ℕ) : wilsonLoop β A = Real.tanh β ^ A := by
  unfold wilsonLoop
  rw [correl_eq, razao_eq_tanh]

/-- The same area law, in the form `e^{-m(β) A}` with the Yang–Mills-toy mass gap `m(β)` as the
string tension: the rate governing confinement and the rate governing the reconstructed
Hamiltonian's spectral gap (`ATK.YMReconstrucao.lacuna_igual_taxa`) are the same number. -/
theorem wilson_area_law_exp {β : ℝ} (hβ : 0 < β) (A : ℕ) :
    wilsonLoop β A = Real.exp (-(massa β) * A) := by
  unfold wilsonLoop
  exact correl_exp hβ A

end ATK.YMWilsonLoop

#print axioms ATK.YMWilsonLoop.wilson_area_law
#print axioms ATK.YMWilsonLoop.wilson_area_law_exp
