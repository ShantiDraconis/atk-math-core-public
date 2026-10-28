import ATK.ATKI
import ATK.LigacaoBSDTestes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic

/-!
# ATK-I — os sete cálculos concretos do texto, verificados

Cada item é um fato **local** (uma instância, um exemplo), não o enunciado universal:

| classe | cálculo | teorema |
|---|---|---|
| RH | `D N` da família do texto decresce e converge | `ATK.ATKI.texto_antitone`, `texto_converge` |
| P vs NP | `(x ∨ y) ∧ (¬x ∨ y)` é satisfatível; `(x ∨ y) ∧ (¬x ∨ z)` tem 4 de 8 atribuições | `phi_satisfativel`, `psi_conta` |
| NS | `u = (A e^{−νt} sin y, 0, 0)`, `p = 0`: o termo não linear e a divergência são nulos e `∂ₜu₁ = ν ∂²_y u₁` | `calor`, `transporte_nulo` |
| YM | `[σ₁, σ₂] = 2i σ₃`; `diag(0, 2, 5)` tem autovetores `eᵢ` e gap `2` | `comutador_pauli`, `autovetor`, `gap_dois` |
| BSD | `y² = x³ − x`: `Δ = 64`, `c₄³ = 1728·Δ` (`j = 1728`), 2-torção total, posto 0 | `c4_cubo`, `bsd_curva32_posto_zero` |
| Hodge | no modelo algébrico `ℚ[h]/(h³)`: `h³ = 0`, `⟨a h, b h⟩ = a b`, `⟨3h, 2h⟩ = 6` | `h_cubo`, `pareamento`, `pareamento_exemplo` |
| Beal | `3³ + 6³ = 3⁵`, `mdc(3, 6, 3) = 3`, valorações 3-ádicas `3, 3, 5` | `beal_exemplo`, `beal_mdc`, `beal_valoracoes` |

O modelo de Hodge é só a álgebra `ℚ[h]/(h³)`; a identificação com `H*(ℂP², ℚ)` não está na
Mathlib. O gap da matriz não é o gap de Yang–Mills. Nenhuma linha resolve a conjectura respectiva.
-/

noncomputable section

namespace ATK.ATKIExemplos

/-! ## P vs NP -/

def phi (x y : Bool) : Bool := (x || y) && (!x || y)

theorem phi_satisfativel : phi false true = true := rfl

def psi (x y z : Bool) : Bool := (x || y) && (!x || z)

theorem psi_conta :
    ((Finset.univ : Finset (Bool × Bool × Bool)).filter (fun t => psi t.1 t.2.1 t.2.2 = true)).card
      = 4 := by
  decide

/-! ## Navier–Stokes: o escoamento de cisalhamento -/

/-- Componente `x`: `f(y, t) = A e^{−νt} sin y`. -/
def f (A ν y t : ℝ) : ℝ := A * Real.exp (-ν * t) * Real.sin y

theorem f_deriv_t (A ν y t : ℝ) : HasDerivAt (fun s => f A ν y s) (-ν * f A ν y t) t := by
  have h1 : HasDerivAt (fun s => -ν * s) (-ν) t := by
    simpa using (hasDerivAt_id t).const_mul (-ν)
  have h2 : HasDerivAt (fun s => A * Real.exp (-ν * s) * Real.sin y)
      (A * (Real.exp (-ν * t) * -ν) * Real.sin y) t :=
    (((Real.hasDerivAt_exp (-ν * t)).comp t h1).const_mul A).mul_const (Real.sin y)
  exact h2.congr_deriv (by simp only [f]; ring)

theorem f_deriv_y (A ν y t : ℝ) :
    HasDerivAt (fun z => f A ν z t) (A * Real.exp (-ν * t) * Real.cos y) y :=
  (Real.hasDerivAt_sin y).const_mul (A * Real.exp (-ν * t))

theorem f_deriv_yy (A ν y t : ℝ) :
    HasDerivAt (fun z => A * Real.exp (-ν * t) * Real.cos z) (-f A ν y t) y :=
  ((Real.hasDerivAt_cos y).const_mul (A * Real.exp (-ν * t))).congr_deriv (by simp only [f]; ring)

/-- **Equação do calor**: `∂ₜ f = ν ∂²_y f`. Com `p = 0` é a equação de Navier–Stokes para
`u = (f, 0, 0)`, porque o termo `(u·∇)u = f ∂ₓ f` e a divergência `∂ₓ f` são nulos. -/
theorem calor (A ν y t : ℝ) :
    deriv (fun s => f A ν y s) t = ν * deriv (fun z => deriv (fun w => f A ν w t) z) y := by
  rw [(f_deriv_t A ν y t).deriv]
  have hd : (fun z => deriv (fun w => f A ν w t) z) = fun z => A * Real.exp (-ν * t) * Real.cos z := by
    funext z
    exact (f_deriv_y A ν z t).deriv
  rw [hd, (f_deriv_yy A ν y t).deriv]
  ring

/-- `f` não depende de `x`: `∂ₓ f = 0`, logo `(u·∇)u = 0` e `div u = 0`. -/
theorem transporte_nulo (A ν y t x : ℝ) : deriv (fun _ : ℝ => f A ν y t) x = 0 := deriv_const _ _

/-! ## Yang–Mills: comutador e gap de um operador de teste -/

open Matrix Complex in
/-- **`[σ₁, σ₂] = 2i σ₃`**. -/
theorem comutador_pauli :
    (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![0, -I; I, 0] -
        !![0, -I; I, 0] * !![0, 1; 1, 0] = (2 * I) • !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- O operador de teste `H = diag(0, 2, 5)`. -/
def H : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![0, 2, 5]

/-- Os vetores da base são autovetores, com autovalores `0, 2, 5`. -/
theorem autovetor (i : Fin 3) :
    Matrix.mulVec H (Pi.single i 1) = Pi.single i (![0, 2, 5] i) := by
  simp [H, Matrix.diagonal_mulVec_single]

/-- **Gap 2**: o menor autovalor positivo é `2`. -/
theorem gap_dois : (0 : ℝ) < 2 ∧ ∀ i : Fin 3, 0 < (![0, 2, 5] : Fin 3 → ℝ) i →
    (2 : ℝ) ≤ ![0, 2, 5] i := by
  refine ⟨by norm_num, ?_⟩
  intro i hi
  fin_cases i <;> simp_all <;> norm_num

/-! ## BSD: a curva `y² = x³ − x` -/

/-- `c₄³ = 1728·Δ`, isto é, `j(E) = 1728`. -/
theorem c4_cubo : ATK.CongruentCurve.E.c₄ ^ 3 = 1728 * ATK.CongruentCurve.E.Δ := by
  norm_num [ATK.CongruentCurve.E, WeierstrassCurve.c₄, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- `Δ = 64`, 2-torção total e **posto 0**, calculados no objeto da Mathlib. -/
theorem bsd_curva32_posto_zero :
    ATK.CongruentCurve.E.IsElliptic ∧
      (∀ P : ATK.CongruentCurve.E.toAffine.Point, P + P = 0) ∧
      ATK.LigacaoBSD.postoMW ATK.CongruentCurve.E = 0 :=
  ⟨ATK.LigacaoBSDTestes.curva32_eliptica, ATK.LigacaoBSDTestes.dois_torcao,
    ATK.LigacaoBSDTestes.posto_curva32⟩

/-! ## Hodge: o modelo algébrico `ℚ[h]/(h³)` -/

/-- Coeficientes de `1, h, h²`. -/
structure Trunc where
  c0 : ℚ
  c1 : ℚ
  c2 : ℚ

def Trunc.mul (x y : Trunc) : Trunc :=
  ⟨x.c0 * y.c0, x.c0 * y.c1 + x.c1 * y.c0, x.c0 * y.c2 + x.c1 * y.c1 + x.c2 * y.c0⟩

def h : Trunc := ⟨0, 1, 0⟩

/-- "Integração": o coeficiente de `h²`. -/
def integra (x : Trunc) : ℚ := x.c2

theorem h_cubo : Trunc.mul h (Trunc.mul h h) = ⟨0, 0, 0⟩ := by
  simp [Trunc.mul, h]

/-- `⟨a h, b h⟩ = a b`. -/
theorem pareamento (a b : ℚ) : integra (Trunc.mul ⟨0, a, 0⟩ ⟨0, b, 0⟩) = a * b := by
  simp [integra, Trunc.mul]

theorem pareamento_exemplo : integra (Trunc.mul ⟨0, 3, 0⟩ ⟨0, 2, 0⟩) = 6 := by
  rw [pareamento]; norm_num

/-! ## Beal -/

theorem beal_exemplo : (3 : ℕ) ^ 3 + 6 ^ 3 = 3 ^ 5 := by norm_num

theorem beal_mdc : Nat.gcd (Nat.gcd 3 6) 3 = 3 := by norm_num

/-- Valorações 3-ádicas `3, 3, 5`: `3³ ∥ 3³`, `3³ ∥ 6³`, `3⁵ ∥ 3⁵`; a soma tem valoração maior que
a das parcelas (cancelamento). -/
theorem beal_valoracoes :
    (3 ^ 3 ∣ (3 : ℕ) ^ 3 ∧ ¬ 3 ^ 4 ∣ (3 : ℕ) ^ 3) ∧
      (3 ^ 3 ∣ (6 : ℕ) ^ 3 ∧ ¬ 3 ^ 4 ∣ (6 : ℕ) ^ 3) ∧
      (3 ^ 5 ∣ (3 : ℕ) ^ 3 + 6 ^ 3 ∧ ¬ 3 ^ 6 ∣ (3 : ℕ) ^ 3 + 6 ^ 3) := by
  decide

end ATK.ATKIExemplos

end

#print axioms ATK.ATKIExemplos.phi_satisfativel
#print axioms ATK.ATKIExemplos.psi_conta
#print axioms ATK.ATKIExemplos.f_deriv_t
#print axioms ATK.ATKIExemplos.f_deriv_y
#print axioms ATK.ATKIExemplos.f_deriv_yy
#print axioms ATK.ATKIExemplos.calor
#print axioms ATK.ATKIExemplos.transporte_nulo
#print axioms ATK.ATKIExemplos.comutador_pauli
#print axioms ATK.ATKIExemplos.autovetor
#print axioms ATK.ATKIExemplos.gap_dois
#print axioms ATK.ATKIExemplos.c4_cubo
#print axioms ATK.ATKIExemplos.bsd_curva32_posto_zero
#print axioms ATK.ATKIExemplos.h_cubo
#print axioms ATK.ATKIExemplos.pareamento
#print axioms ATK.ATKIExemplos.pareamento_exemplo
#print axioms ATK.ATKIExemplos.beal_exemplo
#print axioms ATK.ATKIExemplos.beal_mdc
#print axioms ATK.ATKIExemplos.beal_valoracoes
