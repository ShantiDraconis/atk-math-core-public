/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.GroupTheory.Torsion

/-!
# Cópia dos enunciados de BSD e de Hasse–Weil do formal-conjectures (Google DeepMind)

Fontes: `google-deepmind/formal-conjectures`, commit `84cf7f8`,
`FormalConjectures/Wikipedia/HasseWeil.lean`, `FormalConjectures/Millennium/BSD.lean` e
`FormalConjectures/Wikipedia/EllipticCurveRank.lean` (licença Apache 2.0, cabeçalho original mantido
acima). Copiados sem mudar o significado, dentro do namespace `ATK.FC` e sem o sistema de módulos:

* as definições `HasMeromorphicContinuation`, `HasAnalyticContinuation` e `BSD.Weak`;
* o lema de API `HasMeromorphicContinuation.unique`, **com a prova** de lá (só o lema
  `Complex.isOpen_re_gt`, que não existe na Mathlib v4.34.1, foi trocado por
  `isOpen_lt continuous_const Complex.continuous_re`);
* os enunciados (sem prova) de `exists_hasAnalyticContinuation_rat` (Hasse–Weil sobre `ℚ`,
  `research solved` lá: segue da modularidade) e de `mordell_weil` (sobre `ℚ`), como **definições**
  `HasseWeilQ` e `MordellWeilQ` (`Prop`), para servirem de hipóteses explícitas.

Os teoremas de lá que são `sorry` (as conjecturas e esses dois resultados) **não** foram copiados
como teoremas.
-/

open scoped Topology

namespace ATK.FC.HasseWeil

variable {K : Type*} [Field K] [NumberField K] {E : WeierstrassCurve K}

/-- The $L$-series of `E` has the meromorphic continuation `L`: `L` is meromorphic on
$\mathbb{C}$ and agrees with `E.LSeries` on $\operatorname{Re} s > 3/2$, where the series
converges absolutely. -/
def HasMeromorphicContinuation (E : WeierstrassCurve K) (L : ℂ → ℂ) : Prop :=
  Meromorphic L ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

/-- The $L$-series of `E` has the analytic continuation `L`: `L` is analytic on
$\mathbb{C}$ and agrees with `E.LSeries` on $\operatorname{Re} s > 3/2$, where the series
converges absolutely. -/
def HasAnalyticContinuation (E : WeierstrassCurve K) (L : ℂ → ℂ) : Prop :=
  (∀ z, AnalyticAt ℂ L z) ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

/-- An analytic continuation is a meromorphic continuation. -/
theorem HasAnalyticContinuation.hasMeromorphicContinuation {L : ℂ → ℂ}
    (hL : HasAnalyticContinuation E L) : HasMeromorphicContinuation E L :=
  ⟨fun z ↦ (hL.1 z).meromorphicAt, hL.2⟩

/-- A meromorphic continuation is unique away from isolated points: two meromorphic
continuations of the $L$-series of `E` agree on a punctured neighbourhood of every point. -/
theorem HasMeromorphicContinuation.unique {L L' : ℂ → ℂ}
    (hL : HasMeromorphicContinuation E L) (hL' : HasMeromorphicContinuation E L') (x : ℂ) :
    L =ᶠ[𝓝[≠] x] L' := by
  have h2 : meromorphicOrderAt (L - L') 2 = ⊤ := meromorphicOrderAt_eq_top_iff.2 <|
    Filter.eventually_of_mem (nhdsWithin_le_nhds <| (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num)) fun s hs ↦ sub_eq_zero.2 ((hL.2 s hs).trans (hL'.2 s hs).symm)
  have key : meromorphicOrderAt (L - L') x = ⊤ := not_not.1 fun hx ↦
    (hL.1.sub hL'.1).exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨x, hx⟩ 2 h2
  exact (meromorphicOrderAt_eq_top_iff.1 key).mono fun s hs ↦ sub_eq_zero.1 hs

/-- Enunciado de `HasseWeil.exists_hasAnalyticContinuation_rat` (lá: `research solved`, `sorry`):
a série L de toda curva elíptica sobre `ℚ` tem continuação analítica a `ℂ`. -/
def HasseWeilQ : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], ∃ L, HasAnalyticContinuation E L

end ATK.FC.HasseWeil

namespace ATK.FC.BSD

open ATK.FC.HasseWeil

/-- The **weak Birch and Swinnerton-Dyer conjecture** for a number field $K$: for every elliptic
curve $E$ over $K$, a meromorphic continuation of its $L$-series has order
$\operatorname{rank}_{\mathbb{Z}} E(K)$ at $s = 1$. The rank is `AddCommGroup.freeRank`, which
requires $E(K)$ to be finitely generated (Mordell–Weil), so it appears as a hypothesis. -/
def Weak (K : Type*) [Field K] [NumberField K] [DecidableEq K] : Prop :=
  ∀ (E : WeierstrassCurve K) [E.IsElliptic] [AddGroup.FG E.toAffine.Point] (L : ℂ → ℂ),
    HasMeromorphicContinuation E L →
      meromorphicOrderAt L 1 = AddCommGroup.freeRank E.toAffine.Point

/-- Enunciado de `EllipticCurveRank.mordell_weil` sobre `ℚ` (lá: `research solved`, `sorry`): o
grupo dos pontos racionais de uma curva elíptica é finitamente gerado. -/
def MordellWeilQ : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic], Module.Finite ℤ E.toAffine.Point

end ATK.FC.BSD
