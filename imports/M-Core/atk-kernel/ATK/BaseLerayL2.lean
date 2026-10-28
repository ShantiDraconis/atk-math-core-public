/-
ATK.Base (N3b) — `L²_σ(T³)` e a projeção de Leray em `L²`.

Continua `ATK.BaseToroPoincare`.  Os campos vetoriais de quadrado integrável no toro formam o
espaço de Hilbert `L²(T³)³ = PiLp 2 (fun _ : Fin 3 => L²(T³))`.  Em Fourier, a divergência no modo
`k` é o funcional contínuo `u ↦ Σᵢ kᵢ ûᵢ(k)`:

* **`coefL_apply`**: `f ↦ f̂_k` é o funcional contínuo `⟪e_k, ·⟫`;
* `L2sigma`: `L²_σ = ⋂_k ker(div_k)` — os campos de divergência nula (no sentido das
  distribuições);
* **`isClosed_L2sigma`**: `L²_σ` é fechado (logo completo, com projeção ortogonal);
* `leray`: a projeção de Leray `P = proj_{L²_σ}` (ortogonal, contínua);
* **`leray_mem`**, **`leray_eq_self_iff`**, **`leray_idem`**, **`norm_leray_le`**:
  `P u ∈ L²_σ`, `P u = u ⟺ u ∈ L²_σ`, `P² = P`, `‖P u‖ ≤ ‖u‖`;
* **`galerkin_mem_L2sigma`**: os estados admissíveis de Galerkin (de `ATK.BaseGalerkinGlobal`) são
  campos de `L²_σ` — as trajetórias globais de N2b vivem no espaço de Leray.

A fórmula de multiplicador `P̂u(k) = û(k) − k (k·û(k))/|k|²` e a compacidade (Aubin–Lions)
continuam como próximos passos (N4).
-/
import ATK.BaseToroPoincare
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

open MeasureTheory UnitAddTorus Finset

noncomputable section

namespace ATK.BaseLerayL2

open ATK.BaseGalerkinNS ATK.BaseGalerkinGlobal ATK.BaseToroPoincare

/-- A mesma medida de Haar (massa 1) usada na Mathlib para a série de Fourier no toro. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local notation "L2T" => Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))

/-- Campos vetoriais `L²(T³)³`. -/
abbrev CampoL2 := PiLp 2 (fun _ : Fin 3 => L2T)

/-- Coeficiente de Fourier no modo `k` como funcional contínuo. -/
def coefL (k : Modo) : L2T →L[ℂ] ℂ := innerSL ℂ (mFourierLp 2 k)

theorem coefL_apply (k : Modo) (f : L2T) : coefL k f = mFourierCoeff f k := by
  rw [← mFourierBasis_repr, HilbertBasis.repr_apply_apply, coe_mFourierBasis]
  rfl

/-- Divergência no modo `k`: `u ↦ Σᵢ kᵢ ûᵢ(k)`. -/
def divL (k : Modo) : CampoL2 →L[ℂ] ℂ :=
  ∑ i : Fin 3, ((k i : ℤ) : ℂ) • (coefL k).comp (PiLp.proj 2 (fun _ : Fin 3 => L2T) i)

theorem divL_apply (k : Modo) (u : CampoL2) :
    divL k u = ∑ i : Fin 3, ((k i : ℤ) : ℂ) * mFourierCoeff (u i) k := by
  simp [divL, coefL_apply]

/-- `L²_σ(T³)`: campos de divergência nula. -/
def L2sigma : Submodule ℂ CampoL2 := ⨅ k : Modo, LinearMap.ker (divL k : CampoL2 →ₗ[ℂ] ℂ)

theorem mem_L2sigma {u : CampoL2} :
    u ∈ L2sigma ↔ ∀ k : Modo, ∑ i : Fin 3, ((k i : ℤ) : ℂ) * mFourierCoeff (u i) k = 0 := by
  simp only [L2sigma, Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    divL_apply]

/-- **`L²_σ` é fechado.** -/
theorem isClosed_L2sigma : IsClosed (L2sigma : Set CampoL2) := by
  have h : (L2sigma : Set CampoL2) =
      ⋂ k : Modo, (LinearMap.ker (divL k : CampoL2 →ₗ[ℂ] ℂ) : Set CampoL2) := by
    ext u
    simp only [L2sigma, SetLike.mem_coe, Submodule.mem_iInf, Set.mem_iInter]
  rw [h]
  exact isClosed_iInter fun k => (divL k).isClosed_ker

instance : CompleteSpace L2sigma := isClosed_L2sigma.completeSpace_coe

/-- **Projeção de Leray** `P : L²(T³)³ → L²_σ` (ortogonal). -/
def leray : CampoL2 →L[ℂ] CampoL2 := L2sigma.starProjection

theorem leray_mem (u : CampoL2) : leray u ∈ L2sigma :=
  L2sigma.starProjection_apply_mem u

theorem leray_eq_self_iff {u : CampoL2} : leray u = u ↔ u ∈ L2sigma :=
  Submodule.starProjection_eq_self_iff

theorem leray_idem (u : CampoL2) : leray (leray u) = leray u :=
  leray_eq_self_iff.mpr (leray_mem u)

theorem norm_leray_le (u : CampoL2) : ‖leray u‖ ≤ ‖u‖ :=
  L2sigma.norm_starProjection_apply_le u

/-! ### Galerkin em `L²_σ` -/

/-- O estado de Galerkin `x` como campo de `L²(T³)³`. -/
def campoV (K : Finset Modo) (x : Est K) : CampoL2 :=
  WithLp.toLp 2 fun i => campoL2 K x i

/-- **Os estados admissíveis de Galerkin estão em `L²_σ`.** -/
theorem galerkin_mem_L2sigma {K : Finset Modo} (hK : Simetrico K) {x : Est K}
    (hx : x ∈ adm K) : campoV K x ∈ L2sigma := by
  have hA := admissivel_of_mem hK hx
  rw [mem_L2sigma]
  intro k
  simp only [campoV, PiLp.toLp_apply, campoL2, coeff_trig]
  by_cases hk : k ∈ K
  · simp only [hk, ite_true]
    have h := hA.divLivre k hk
    rw [dot_comm] at h
    simpa [dot, kC] using h
  · simp [hk]

/-- Toda trajetória global de Galerkin fica em `L²_σ` e é fixada pela projeção de Leray. -/
theorem galerkin_leray {K : Finset Modo} (hK : Simetrico K) {x : Est K} (hx : x ∈ adm K) :
    leray (campoV K x) = campoV K x :=
  leray_eq_self_iff.mpr (galerkin_mem_L2sigma hK hx)

end ATK.BaseLerayL2

#print axioms ATK.BaseLerayL2.coefL_apply
#print axioms ATK.BaseLerayL2.divL_apply
#print axioms ATK.BaseLerayL2.mem_L2sigma
#print axioms ATK.BaseLerayL2.isClosed_L2sigma
#print axioms ATK.BaseLerayL2.leray_mem
#print axioms ATK.BaseLerayL2.leray_eq_self_iff
#print axioms ATK.BaseLerayL2.leray_idem
#print axioms ATK.BaseLerayL2.norm_leray_le
#print axioms ATK.BaseLerayL2.galerkin_mem_L2sigma
#print axioms ATK.BaseLerayL2.galerkin_leray
