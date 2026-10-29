import Mathlib
import ATK.Exact
import ATK.NSBridge

/-!
# ATK — Objeto genuíno de NS no kernel: o escoamento laminar de cisalhamento

A outra sessão (13/10) usou `u = (A e^{−νk²t} sin(kz), 0, 0)`, `p = 0` como "solução genuína" e
calculou `y = 2π³A²k²e^{−2νk²t}`, `Z² = 4π³A²k⁴e^{−2νk²t}`, estiramento nulo. Aqui o kernel
CERTIFICA, com as definições oficiais de `ATK.Exact`, que:

* `laminar_solution`: para quaisquer `A, k, ν` é solução clássica suave de Navier–Stokes
  (`NSClassical`) sem força, com pressão nula, em `[0,∞) × ℝ³`;
* `laminar_no_convection`: o termo não linear `(u·∇)u` é IDENTICAMENTE zero;
* `laminar_periodic`: para `k = 2πm` (`m ∈ ℤ`) é 1-periódica no espaço (classe do Clay (B)/(D)).

Leitura: o termo não linear é exatamente o que poderia produzir explosão; aqui ele vale zero.
Por isso este objeto (e toda medição feita nele) não informa nada sobre as constantes universais
`c_B, c_T, C` nem sobre (A): ele é solução da equação do calor disfarçada.

Peças gerais: `shear g (x) = g(x₃)·e₁`; `pd_shear`, `conv3_shear`, `div3_shear`, `lap3_shear`.
-/

noncomputable section

namespace ATK.NSLaminar

open Set
open scoped ContDiff
open ATK.Exact (R3 e pd div3 lap3 grad3 conv3 NSClassical SpacePeriodic)

/-- Campo de cisalhamento `x ↦ g(x₂)·e₀` (componente 0 dependendo só da coordenada 2). -/
def shear (g : ℝ → ℝ) : R3 → R3 := fun y => g (y 2) • e 0

theorem coord_hasFDerivAt (x : R3) :
    HasFDerivAt (fun y : R3 => y 2) (EuclideanSpace.proj (2 : Fin 3) : R3 →L[ℝ] ℝ) x := by
  have hfun : (fun y : R3 => y 2) = ((EuclideanSpace.proj (2 : Fin 3) : R3 →L[ℝ] ℝ) : R3 → ℝ) := by
    funext y
    first
      | rfl
      | simp
  rw [hfun]
  exact ContinuousLinearMap.hasFDerivAt _

theorem hasFDerivAt_shear {g g' : ℝ → ℝ} (hg : ∀ s, HasDerivAt g (g' s) s) (x : R3) :
    HasFDerivAt (shear g)
      ((g' (x 2) • (EuclideanSpace.proj (2 : Fin 3) : R3 →L[ℝ] ℝ)).smulRight (e 0)) x :=
  ((hg (x 2)).comp_hasFDerivAt x (coord_hasFDerivAt x)).smul_const (e 0)

/-- `∂ᵢ (g(x₂) e₀) = g'(x₂)·δᵢ₂·e₀`. -/
theorem pd_shear {g g' : ℝ → ℝ} (hg : ∀ s, HasDerivAt g (g' s) s) (i : Fin 3) :
    pd i (shear g) = shear (fun s => g' s * (e i) 2) := by
  funext x
  show fderiv ℝ (shear g) x (e i) = shear (fun s => g' s * (e i) 2) x
  rw [(hasFDerivAt_shear hg x).fderiv]
  simp [shear]

/-- O termo convectivo de um cisalhamento é zero. -/
theorem conv3_shear {g g' : ℝ → ℝ} (hg : ∀ s, HasDerivAt g (g' s) s) (x : R3) :
    conv3 (shear g) x = 0 := by
  rw [ATK.NSBridge.conv3_eq, (hasFDerivAt_shear hg x).fderiv]
  simp [shear]

/-- Um cisalhamento tem divergência nula. -/
theorem div3_shear {g g' : ℝ → ℝ} (hg : ∀ s, HasDerivAt g (g' s) s) (x : R3) :
    div3 (shear g) x = 0 := by
  have hd : DifferentiableAt ℝ (shear g) x := (hasFDerivAt_shear hg x).differentiableAt
  unfold div3
  simp only [pd]
  rw [Fin.sum_univ_three, ATK.NSBridge.fderiv_coord hd, ATK.NSBridge.fderiv_coord hd,
    ATK.NSBridge.fderiv_coord hd, (hasFDerivAt_shear hg x).fderiv]
  simp [shear]

/-- Laplaciano de um cisalhamento: `Δ(g(x₂) e₀) = g''(x₂) e₀`. -/
theorem lap3_shear {g g' g'' : ℝ → ℝ} (hg : ∀ s, HasDerivAt g (g' s) s)
    (hg' : ∀ s, HasDerivAt g' (g'' s) s) (x : R3) :
    lap3 (shear g) x = shear g'' x := by
  have h1 : ∀ i : Fin 3, pd i (pd i (shear g)) = shear (fun s => g'' s * (e i) 2 * (e i) 2) := by
    intro i
    rw [pd_shear hg i, pd_shear (fun s => (hg' s).mul_const ((e i) 2)) i]
  unfold lap3
  simp only [h1]
  rw [Fin.sum_univ_three]
  simp [shear]

/-- O escoamento laminar `u(t,x) = A e^{−νk²t} sin(k x₂) e₀`. -/
def lam (A k ν : ℝ) (t : ℝ) (x : R3) : R3 :=
  (A * Real.exp (-(ν * k ^ 2) * t) * Real.sin (k * x 2)) • e 0

theorem lam_eq_shear (A k ν t : ℝ) :
    lam A k ν t = shear (fun s => A * Real.exp (-(ν * k ^ 2) * t) * Real.sin (k * s)) := rfl

theorem hsin (c k : ℝ) (s : ℝ) :
    HasDerivAt (fun s => c * Real.sin (k * s)) (c * (Real.cos (k * s) * k)) s := by
  have h1 : HasDerivAt (fun s => k * s) k s := by
    simpa using (hasDerivAt_id s).const_mul k
  exact (h1.sin).const_mul c

theorem hcos (c k : ℝ) (s : ℝ) :
    HasDerivAt (fun s => c * (Real.cos (k * s) * k)) (c * (-Real.sin (k * s) * k * k)) s := by
  have h1 : HasDerivAt (fun s => k * s) k s := by
    simpa using (hasDerivAt_id s).const_mul k
  exact ((h1.cos).mul_const k).const_mul c

/-- O termo não linear do escoamento laminar é identicamente zero. -/
theorem laminar_no_convection (A k ν t : ℝ) (x : R3) : conv3 (lam A k ν t) x = 0 := by
  rw [lam_eq_shear]
  exact conv3_shear (hsin _ k) x

/-- **Objeto genuíno certificado:** o escoamento laminar é solução clássica suave de NS. -/
theorem laminar_solution (A k ν : ℝ) :
    NSClassical ν (lam A k ν 0) (fun _ _ => 0) (lam A k ν) (fun _ _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_, fun x => rfl⟩
  · have h2 : ContDiff ℝ ∞ (fun z : ℝ × R3 => z.2 2) := by
      have hc := (EuclideanSpace.proj (2 : Fin 3) : R3 →L[ℝ] ℝ).contDiff (n := ∞)
      exact hc.comp contDiff_snd
    have h : ContDiff ℝ ∞ (fun z : ℝ × R3 =>
        (A * Real.exp (-(ν * k ^ 2) * z.1) * Real.sin (k * z.2 2)) • e 0) := by
      first
        | fun_prop
        | exact ((contDiff_const.mul ((contDiff_const.mul contDiff_fst).exp)).mul
            ((contDiff_const.mul h2).sin)).smul_const (e 0)
    exact h.contDiffOn
  · show ContDiffOn ℝ ∞ (fun _ : ℝ × R3 => (0 : ℝ)) (Ici 0 ×ˢ univ)
    exact contDiffOn_const
  · intro t ht x
    have hdt : derivWithin (fun s => lam A k ν s x) (Ici 0) t =
        (A * (Real.exp (-(ν * k ^ 2) * t) * -(ν * k ^ 2)) * Real.sin (k * x 2)) • e 0 := by
      have h0 : HasDerivAt (fun s => -(ν * k ^ 2) * s) (-(ν * k ^ 2)) t := by
        simpa using (hasDerivAt_id t).const_mul (-(ν * k ^ 2))
      have h1 := (((h0.exp).const_mul A).mul_const (Real.sin (k * x 2))).smul_const (e 0)
      exact h1.hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici 0 t ht)
    have hlap : lap3 (lam A k ν t) x =
        (A * Real.exp (-(ν * k ^ 2) * t) * (-Real.sin (k * x 2) * k * k)) • e 0 := by
      rw [lam_eq_shear]
      exact lap3_shear (hsin _ k) (hcos _ k) x
    show derivWithin (fun s => lam A k ν s x) (Ici 0) t + conv3 (lam A k ν t) x =
      ν • lap3 (lam A k ν t) x - grad3 (fun _ => (0 : ℝ)) x + 0
    rw [hdt, laminar_no_convection, hlap, ATK.Exact.grad3_zero, smul_smul]
    simp only [add_zero, sub_zero]
    congr 1
    ring
  · intro t _ x
    rw [lam_eq_shear]
    exact div3_shear (hsin _ k) x

/-- Para `k = 2πm` o escoamento laminar é 1-periódico no espaço (com pressão nula). -/
theorem laminar_periodic (A ν : ℝ) (m : ℤ) :
    SpacePeriodic (lam A (2 * Real.pi * m) ν) (fun _ _ => 0) := by
  intro t _ x j
  refine ⟨?_, rfl⟩
  have key : ∀ i : Fin 3, (x + e i) 2 = x 2 + (if i = 2 then 1 else 0) := by
    intro i
    fin_cases i <;> simp [ATK.Exact.e]
  unfold lam
  rw [key j]
  split_ifs with hj
  · rw [show 2 * Real.pi * (m : ℝ) * (x 2 + 1) = 2 * Real.pi * (m : ℝ) * x 2 + (m : ℝ) * (2 * Real.pi) by
      ring, Real.sin_add_int_mul_two_pi]
  · rw [add_zero]

end ATK.NSLaminar

end

#print axioms ATK.NSLaminar.coord_hasFDerivAt
#print axioms ATK.NSLaminar.hasFDerivAt_shear
#print axioms ATK.NSLaminar.pd_shear
#print axioms ATK.NSLaminar.conv3_shear
#print axioms ATK.NSLaminar.div3_shear
#print axioms ATK.NSLaminar.lap3_shear
#print axioms ATK.NSLaminar.lam_eq_shear
#print axioms ATK.NSLaminar.hsin
#print axioms ATK.NSLaminar.hcos
#print axioms ATK.NSLaminar.laminar_no_convection
#print axioms ATK.NSLaminar.laminar_solution
#print axioms ATK.NSLaminar.laminar_periodic
