/-
ATK.Base — Teoria de calibre na rede: plaquetas, ação de Wilson e invariância de calibre.

Base que falta na Mathlib (não há teoria de calibre na rede).  É o ponto de partida rigoroso de
Yang–Mills construtivo (Wilson 1974; Osterwalder–Seiler 1978): o limite contínuo e o gap são a
parte aberta.

Rede periódica `Λ = (ℤ/L)ᵈ`, grupo de calibre `G` qualquer (para Yang–Mills, `SU(N)`):

* configuração de elos `U : Λ → Fin d → G` e transformação de calibre
  `(g • U)(x, μ) = g(x) U(x, μ) g(x + e_μ)⁻¹`; é uma **ação de grupo** (`acao_mul`, `acao_one`);
* plaqueta `U_p(x; μ, ν) = U(x,μ) U(x+e_μ, ν) U(x+e_ν, μ)⁻¹ U(x, ν)⁻¹` e a lei de transformação
  **`plaqueta_calibre`**: `(g • U)_p(x) = g(x) U_p(x) g(x)⁻¹`;
* para qualquer função de classe `χ` (`χ(g h g⁻¹) = χ(h)`), a **ação de Wilson**
  `S(U) = Σ_x Σ_{μ,ν} (1 − χ(U_p(x; μ, ν)))` é **invariante de calibre** (`wilson_invariante`);
* `χ(U) = Re tr U` é função de classe em `U(N)` (`reTr_classe`), dando a ação de Wilson usual;
* plaquetas degeneradas são triviais: `U_p(x; μ, μ) = 1`.

Nada aqui constrói Yang–Mills no contínuo nem prova gap.
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic

namespace ATK.BaseRedeCalibre

open Finset

variable {d L : ℕ} [NeZero L] {G : Type*} [Group G]

/-- Sítios da rede periódica `(ℤ/L)ᵈ`. -/
abbrev Sitio (d L : ℕ) := Fin d → ZMod L

/-- Vetor unitário na direção μ. -/
def e (μ : Fin d) : Sitio d L := fun ν => if ν = μ then 1 else 0

/-- Configuração de elos. -/
abbrev Elos (d L : ℕ) (G : Type*) := Sitio d L → Fin d → G

/-- Transformação de calibre. -/
abbrev Calibre (d L : ℕ) (G : Type*) := Sitio d L → G

/-- Ação de uma transformação de calibre nos elos. -/
def acao (g : Calibre d L G) (U : Elos d L G) : Elos d L G :=
  fun x μ => g x * U x μ * (g (x + e μ))⁻¹

theorem acao_one (U : Elos d L G) : acao (fun _ => (1 : G)) U = U := by
  funext x μ; simp [acao]

theorem acao_mul (g h : Calibre d L G) (U : Elos d L G) :
    acao g (acao h U) = acao (fun x => g x * h x) U := by
  funext x μ
  simp only [acao, mul_inv_rev]
  group

/-- Plaqueta `U_p(x; μ, ν)`. -/
def plaqueta (U : Elos d L G) (x : Sitio d L) (μ ν : Fin d) : G :=
  U x μ * U (x + e μ) ν * (U (x + e ν) μ)⁻¹ * (U x ν)⁻¹

/-- **Lei de transformação da plaqueta**: `(g • U)_p(x) = g(x) U_p(x) g(x)⁻¹`. -/
theorem plaqueta_calibre (g : Calibre d L G) (U : Elos d L G) (x : Sitio d L) (μ ν : Fin d) :
    plaqueta (acao g U) x μ ν = g x * plaqueta U x μ ν * (g x)⁻¹ := by
  simp only [plaqueta, acao, mul_inv_rev, inv_inv]
  have h : x + e μ + e ν = x + e ν + e μ := by abel
  rw [h]
  group

/-- Plaquetas degeneradas são triviais. -/
theorem plaqueta_diag (U : Elos d L G) (x : Sitio d L) (μ : Fin d) : plaqueta U x μ μ = 1 := by
  simp only [plaqueta]
  group

/-- Função de classe. -/
def Classe (χ : G → ℝ) : Prop := ∀ g h : G, χ (g * h * g⁻¹) = χ h

/-- Ação de Wilson `S(U) = Σ_x Σ_{μ,ν} (1 − χ(U_p(x; μ, ν)))`. -/
def wilson (χ : G → ℝ) (U : Elos d L G) : ℝ :=
  ∑ x : Sitio d L, ∑ μ : Fin d, ∑ ν : Fin d, (1 - χ (plaqueta U x μ ν))

/-- **A ação de Wilson é invariante de calibre.** -/
theorem wilson_invariante {χ : G → ℝ} (hχ : Classe χ) (g : Calibre d L G) (U : Elos d L G) :
    wilson χ (acao g U) = wilson χ U := by
  unfold wilson
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ =>
    Finset.sum_congr rfl fun ν _ => ?_
  rw [plaqueta_calibre, hχ]

/-- Toda observável que só depende das plaquetas via `χ` é invariante de calibre. -/
theorem observavel_invariante {χ : G → ℝ} (hχ : Classe χ) (g : Calibre d L G) (U : Elos d L G)
    (x : Sitio d L) (μ ν : Fin d) :
    χ (plaqueta (acao g U) x μ ν) = χ (plaqueta U x μ ν) := by
  rw [plaqueta_calibre, hχ]

/-! ### O caso `U(N)`: `χ = Re tr` -/

section Unitario

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- `Re tr` como função no grupo unitário. -/
noncomputable def reTr (U : Matrix.unitaryGroup N ℂ) : ℝ := (Matrix.trace (U : Matrix N N ℂ)).re

/-- **`Re tr` é função de classe** em `U(N)`. -/
theorem reTr_classe : Classe (reTr (N := N)) := by
  intro g h
  unfold reTr
  have e1 : ((g * h * g⁻¹ : Matrix.unitaryGroup N ℂ) : Matrix N N ℂ) =
      (g : Matrix N N ℂ) * (h : Matrix N N ℂ) * ((g⁻¹ : Matrix.unitaryGroup N ℂ) : Matrix N N ℂ) :=
    rfl
  have e2 : ((g⁻¹ : Matrix.unitaryGroup N ℂ) : Matrix N N ℂ) * (g : Matrix N N ℂ) = 1 := by
    have : ((g⁻¹ * g : Matrix.unitaryGroup N ℂ) : Matrix N N ℂ) = 1 := by
      rw [inv_mul_cancel]; rfl
    exact this
  rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, e2, Matrix.one_mul]

/-- Ação de Wilson para `U(N)` (a usual, com `χ = Re tr`) é invariante de calibre. -/
theorem wilson_unitario_invariante (g : Calibre d L (Matrix.unitaryGroup N ℂ))
    (U : Elos d L (Matrix.unitaryGroup N ℂ)) :
    wilson reTr (acao g U) = wilson reTr U :=
  wilson_invariante reTr_classe g U

end Unitario

end ATK.BaseRedeCalibre

#print axioms ATK.BaseRedeCalibre.acao_one
#print axioms ATK.BaseRedeCalibre.acao_mul
#print axioms ATK.BaseRedeCalibre.plaqueta_calibre
#print axioms ATK.BaseRedeCalibre.plaqueta_diag
#print axioms ATK.BaseRedeCalibre.wilson_invariante
#print axioms ATK.BaseRedeCalibre.observavel_invariante
#print axioms ATK.BaseRedeCalibre.reTr_classe
#print axioms ATK.BaseRedeCalibre.wilson_unitario_invariante
