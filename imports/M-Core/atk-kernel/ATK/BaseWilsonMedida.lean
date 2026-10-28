/-
ATK.Base (Y2) — A medida de Wilson na rede é invariante de calibre.

Continua `ATK.BaseRedeCalibre`.  Com uma medida `μ` bi-invariante no grupo de calibre `G` (a medida
de Haar de um grupo compacto, como SU(N), é bi-invariante), a medida produto
`π = ⊗_{(x,μ)} μ` sobre as configurações de elos é a medida "livre" da teoria na rede, e a medida
de Wilson é `w · π` com peso `w = exp(−β S)`.

* **`acao_preserva`**: cada transformação de calibre preserva `π`
  (`U ↦ g(x) U g(x+e_μ)⁻¹` preserva `μ` por invariância à esquerda e à direita);
* **`esperanca_invariante`**: para todo peso invariante de calibre `w` e toda observável `O`,
  `∫ O(g•U) w(U) dπ = ∫ O(U) w(U) dπ`;
* **`wilson_peso_invariante`** e **`wilson_esperanca_invariante`**: o peso de Wilson
  `exp(−β S_χ)` é invariante (para `χ` função de classe), logo as esperanças de Wilson são
  invariantes de calibre.

Positividade por reflexão, o limite termodinâmico e o gap continuam abertos.
-/
import ATK.BaseRedeCalibre
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
open scoped ENNReal

namespace ATK.BaseWilsonMedida

open ATK.BaseRedeCalibre

variable {d L : ℕ} [NeZero L] {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- Elos indexados por pares (sítio, direção). -/
abbrev ElosP (d L : ℕ) (G : Type*) := Sitio d L × Fin d → G

/-- Ação de calibre nos elos indexados por pares. -/
def acaoP (g : Calibre d L G) (V : ElosP d L G) : ElosP d L G :=
  fun p => g p.1 * V p * (g (p.1 + e p.2))⁻¹

/-- Forma "curried" (a de `BaseRedeCalibre`). -/
def curry (V : ElosP d L G) : Elos d L G := fun x μ => V (x, μ)

theorem curry_acaoP (g : Calibre d L G) (V : ElosP d L G) :
    curry (acaoP g V) = acao g (curry V) := rfl

variable (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]

/-- **Cada transformação de calibre preserva a medida produto.** -/
theorem acao_preserva (g : Calibre d L G) :
    MeasurePreserving (acaoP g) (Measure.pi fun _ : Sitio d L × Fin d => μ)
      (Measure.pi fun _ : Sitio d L × Fin d => μ) := by
  have h : ∀ p : Sitio d L × Fin d,
      MeasurePreserving (fun a : G => g p.1 * a * (g (p.1 + e p.2))⁻¹) μ μ :=
    fun p => (measurePreserving_mul_right μ _).comp (measurePreserving_mul_left μ _)
  exact measurePreserving_pi (fun _ => μ) (fun _ => μ) h

/-- Peso invariante de calibre. -/
def PesoInvariante (w : ElosP d L G → ℝ≥0∞) : Prop := ∀ g V, w (acaoP g V) = w V

/-- **Esperanças com peso invariante são invariantes de calibre.** -/
theorem esperanca_invariante {w : ElosP d L G → ℝ≥0∞} (hw : Measurable w)
    (hinv : PesoInvariante w) {O : ElosP d L G → ℝ≥0∞} (hO : Measurable O) (g : Calibre d L G) :
    ∫⁻ V, O (acaoP g V) * w V ∂(Measure.pi fun _ : Sitio d L × Fin d => μ) =
      ∫⁻ V, O V * w V ∂(Measure.pi fun _ : Sitio d L × Fin d => μ) := by
  have e : (fun V => O (acaoP g V) * w V) = fun V => (fun W => O W * w W) (acaoP g V) := by
    funext V
    simp only [hinv g V]
  rw [e]
  exact (acao_preserva μ g).lintegral_comp (hO.mul hw)

/-- Peso de Wilson `exp(−β S_χ)`. -/
noncomputable def pesoWilson (χ : G → ℝ) (β : ℝ) (V : ElosP d L G) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * wilson χ (curry V)))

theorem wilson_peso_invariante {χ : G → ℝ} (hχ : Classe χ) (β : ℝ) :
    PesoInvariante (pesoWilson (d := d) (L := L) χ β) := by
  intro g V
  unfold pesoWilson
  rw [curry_acaoP, wilson_invariante hχ]

/-- **As esperanças de Wilson são invariantes de calibre.** -/
theorem wilson_esperanca_invariante {χ : G → ℝ} (hχ : Classe χ) (β : ℝ)
    (hw : Measurable (pesoWilson (d := d) (L := L) χ β)) {O : ElosP d L G → ℝ≥0∞}
    (hO : Measurable O) (g : Calibre d L G) :
    ∫⁻ V, O (acaoP g V) * pesoWilson χ β V ∂(Measure.pi fun _ : Sitio d L × Fin d => μ) =
      ∫⁻ V, O V * pesoWilson χ β V ∂(Measure.pi fun _ : Sitio d L × Fin d => μ) :=
  esperanca_invariante μ hw (wilson_peso_invariante hχ β) hO g

end ATK.BaseWilsonMedida

#print axioms ATK.BaseWilsonMedida.curry_acaoP
#print axioms ATK.BaseWilsonMedida.acao_preserva
#print axioms ATK.BaseWilsonMedida.esperanca_invariante
#print axioms ATK.BaseWilsonMedida.wilson_peso_invariante
#print axioms ATK.BaseWilsonMedida.wilson_esperanca_invariante
