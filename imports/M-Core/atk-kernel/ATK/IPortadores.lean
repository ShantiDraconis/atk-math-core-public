import ATK.Indeterminacy
import ATK.IMathPonte
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# ATK — As definições de `I` do acervo, comparadas com o `I` do ATK

Referência: `RI = Option ℝ` com `I = none` absorvente (`ATK.Indeterminacy`, o modelo **ABS**).
Os portadores são os do catálogo `conditional/catalog/ilaws/A_algebra_of_I.md` §1, tirados de
`ShantiDraconis/The-Algebra-of-Ideterminate-I` (blobs conferidos: `f0fd5a84`, `f0e174df`,
`2f1c53a0`, `be4be255`, `242da20d`, `258c41ea`, `40a5384e`, `c641179f`, `503a118a`).

Cada portador recebe **um** veredito, com teorema:

| portador | veredito |
|---|---|
| IMath `Phi3` | QUOCIENTE: soma preservada sempre; divisão só entre finitos (`imath_divisao_nao_preservada`) |
| ABS (`ModelElement`, ℚ) | EQUIVALENTE ao `RI` sobre ℚ: mergulho que preserva `+`, `·`, `÷` |
| NexusField (N1–N15) | COMPATÍVEL: `RI` é modelo; todo NexusField tem `inv 0 = I` e `0·I = I` |
| CARD (`ℕ ∪ {I}`) | MERGULHO para `⊕`, `⊗`; INCOMPATÍVEL para `⊖` (`n ⊖ n = I`) |
| KIJ (`ℝ ∪ {I, J}`) | INCOMPATÍVEL: `0 ⊗ I = 0` com `I` absorvente na soma |
| IEA | INCOMPATÍVEL (idem); o axioma A3 é **falso** no próprio modelo |
| AEI ("`I = 1/0`") | INCOMPATÍVEL: `0·I = 1`; a multiplicação **não é associativa** |
| ZDIV | INCOMPATÍVEL: `1 ⊕ (−1) = I`; `⊕` **não é associativa**; o axioma `j_property` é **falso** |
| FLEX (`a + bI`) | INCOMPATÍVEL com `RI` (`I` tem oposto); EQUIVALENTE ao anel `ℝ × ℝ` |
| PAX (P1–P15) | INCONSISTENTE: nenhum modelo |

"INCOMPATÍVEL" é sempre o mesmo enunciado: **não existe** `f : X → RI` que fixe os números
reais (ou naturais) e preserve as operações indicadas. Não depende de escolher para onde `f` leva `I`.

Fidelidade: CARD, ABS, NexusField, ZDIV e FLEX transcrevem as definições da fonte. Em KIJ, IEA e
AEI a fonte não compila como está (padrões `real 0` sobre `ℝ`, nomes de `def` usados como padrão);
aqui está a semântica pretendida, escrita nos comentários da fonte e no catálogo (`0 ⊗ I = 0`,
`0·I = 1`), com `if a = 0` no lugar do padrão literal.
-/

noncomputable section

namespace ATK.IPortadores

open ATK.Indeterminacy (RI addI mulI divI)

/-! ## Contas em `RI` -/

theorem addI_some (a b : ℝ) : addI (some a) (some b) = some (a + b) := rfl
theorem mulI_some (a b : ℝ) : mulI (some a) (some b) = some (a * b) := rfl
theorem addI_none_right (x : RI) : addI x none = none := by cases x <;> rfl
theorem mulI_none_right (x : RI) : mulI x none = none := by cases x <;> rfl
theorem addI_none_left (x : RI) : addI none x = none := by cases x <;> rfl
theorem mulI_none_left (x : RI) : mulI none x = none := by cases x <;> rfl

/-- Subtração em `RI` (modelo ABS): `I` absorvente. -/
def subI : RI → RI → RI
  | some a, some b => some (a - b)
  | _, _ => none

/-! ## IMath: a divisão não passa ao quociente fora dos finitos -/

/-- Em `Phi3`, `1 ÷ ∞ = 0`; em `RI`, `1 ⊘ I = I`. A projeção preserva a divisão entre finitos
(`ATK.IMathPonte.pi_idiv`), **não** em geral. -/
theorem imath_divisao_nao_preservada :
    ATK.IMathPonte.proj (IMath.Phi3.idiv (.finite (1 : ℝ)) .infinity) ≠
      divI (ATK.IMathPonte.proj (.finite 1)) (ATK.IMathPonte.proj .infinity) := by
  rw [IMath.Phi3.finite_idiv_infinity]
  have h : divI (some (1 : ℝ)) none = none := rfl
  show some (0 : ℝ) ≠ divI (some 1) none
  rw [h]
  exact Option.some_ne_none _

/-! ## ABS (`lean/consistency_proofs.lean`): o próprio `RI`, sobre ℚ -/

namespace ABS

inductive ModelElement where
  | standard : ℚ → ModelElement
  | indeterminate : ModelElement

open ModelElement

def model_add : ModelElement → ModelElement → ModelElement
  | standard a, standard b => standard (a + b)
  | indeterminate, _ => indeterminate
  | _, indeterminate => indeterminate

def model_mul : ModelElement → ModelElement → ModelElement
  | standard a, standard b => standard (a * b)
  | indeterminate, _ => indeterminate
  | _, indeterminate => indeterminate

def model_div : ModelElement → ModelElement → ModelElement
  | standard a, standard b => if b = 0 then indeterminate else standard (a / b)
  | indeterminate, _ => indeterminate
  | _, indeterminate => indeterminate

/-- Mergulho em `RI`. -/
def emb : ModelElement → RI
  | standard q => some (q : ℝ)
  | indeterminate => none

theorem emb_injective : Function.Injective emb := by
  rintro (a | _) (b | _) h <;> simp_all [emb]

theorem emb_add (x y : ModelElement) : emb (model_add x y) = addI (emb x) (emb y) := by
  rcases x with a | _ <;> rcases y with b | _
  · simp [model_add, emb, addI_some]
  all_goals rfl

theorem emb_mul (x y : ModelElement) : emb (model_mul x y) = mulI (emb x) (emb y) := by
  rcases x with a | _ <;> rcases y with b | _
  · simp [model_mul, emb, mulI_some]
  all_goals rfl

theorem emb_div (x y : ModelElement) : emb (model_div x y) = divI (emb x) (emb y) := by
  rcases x with a | _ <;> rcases y with b | _
  · by_cases hb : b = 0
    · subst hb; simp [model_div, emb, divI]
    · simp [model_div, emb, divI, hb]
  all_goals rfl

end ABS

/-! ## NexusField (`lean/NexusField.lean`, axiomas N1–N15) -/

/-- Transcrição da estrutura `NexusField` da fonte. -/
structure Nexus where
  carrier : Type
  zero : carrier
  one : carrier
  I : carrier
  add : carrier → carrier → carrier
  mul : carrier → carrier → carrier
  inv : carrier → carrier
  indeterminate_identity : mul zero (inv zero) = I
  I_ne_zero : I ≠ zero
  I_ne_one : I ≠ one
  absorption_add : ∀ x : carrier, add I x = I
  absorption_mul : ∀ x : carrier, x ≠ zero → mul I x = I
  I_add_idempotent : add I I = I
  I_mul_idempotent : mul I I = I
  add_comm : ∀ a b : carrier, add a b = add b a
  add_assoc : ∀ a b c : carrier, add (add a b) c = add a (add b c)
  zero_add : ∀ a : carrier, a ≠ I → add zero a = a
  mul_comm : ∀ a b : carrier, mul a b = mul b a
  mul_assoc : ∀ a b c : carrier, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : carrier, a ≠ I → mul one a = a
  left_distrib : ∀ a b c : carrier,
    (a ≠ I ∧ b ≠ I ∧ c ≠ I) → mul a (add b c) = add (mul a b) (mul a c)
  zero_mul : ∀ a : carrier, a ≠ I → mul zero a = zero

namespace Nexus

/-- Em todo NexusField, `inv 0 = I` (N1 + N2 + N15). -/
theorem inv_zero_eq_I (K : Nexus) : K.inv K.zero = K.I := by
  by_contra h
  have h0 := K.zero_mul (K.inv K.zero) h
  rw [K.indeterminate_identity] at h0
  exact K.I_ne_zero h0

/-- Em todo NexusField, `0·I = I` — a mesma lei do `RI` (e oposta a KIJ, IEA, AEI). -/
theorem zero_mul_I (K : Nexus) : K.mul K.zero K.I = K.I := by
  have h := K.indeterminate_identity
  rwa [inv_zero_eq_I] at h

/-- Inverso em `RI`. -/
def invI : RI → RI
  | some a => if a = 0 then none else some a⁻¹
  | none => none

/-- **`RI` é um NexusField.** -/
def modeloRI : Nexus where
  carrier := RI
  zero := some 0
  one := some 1
  I := none
  add := addI
  mul := mulI
  inv := invI
  indeterminate_identity := by simp [invI, mulI_none_right]
  I_ne_zero := by simp
  I_ne_one := by simp
  absorption_add := addI_none_left
  absorption_mul := fun x _ => mulI_none_left x
  I_add_idempotent := rfl
  I_mul_idempotent := rfl
  add_comm := by
    rintro (_ | a) (_ | b)
    · rfl
    · rfl
    · rfl
    · simp only [addI_some, _root_.add_comm a b]
  add_assoc := by
    rintro (_ | a) (_ | b) (_ | c)
    all_goals first | rfl | simp only [addI_some, _root_.add_assoc]
  zero_add := by
    rintro (_ | a) h
    · exact absurd rfl h
    · simp only [addI_some, _root_.zero_add]
  mul_comm := by
    rintro (_ | a) (_ | b)
    · rfl
    · rfl
    · rfl
    · simp only [mulI_some, _root_.mul_comm a b]
  mul_assoc := by
    rintro (_ | a) (_ | b) (_ | c)
    all_goals first | rfl | simp only [mulI_some, _root_.mul_assoc]
  one_mul := by
    rintro (_ | a) h
    · exact absurd rfl h
    · simp only [mulI_some, _root_.one_mul]
  left_distrib := by
    rintro (_ | a) (_ | b) (_ | c) ⟨ha, hb, hc⟩
    all_goals first
      | exact absurd rfl ha
      | exact absurd rfl hb
      | exact absurd rfl hc
      | simp only [mulI_some, addI_some, mul_add]
  zero_mul := by
    rintro (_ | a) h
    · exact absurd rfl h
    · simp only [mulI_some, MulZeroClass.zero_mul]

end Nexus

/-! ## CARD (`lean/Indeterminate.lean`): `ℕ ∪ {I}` -/

namespace CARD

inductive Card where
  | cardinal : ℕ → Card
  | indeterminate : Card

open Card

def add : Card → Card → Card
  | cardinal n, cardinal m => cardinal (n + m)
  | indeterminate, _ => indeterminate
  | _, indeterminate => indeterminate

def mul : Card → Card → Card
  | cardinal n, cardinal m => cardinal (n * m)
  | indeterminate, _ => indeterminate
  | _, indeterminate => indeterminate

def sub : Card → Card → Card
  | cardinal n, cardinal m => if n = m then indeterminate else cardinal (n - m)
  | indeterminate, indeterminate => indeterminate
  | indeterminate, _ => indeterminate
  | _, indeterminate => indeterminate

def emb : Card → RI
  | cardinal n => some (n : ℝ)
  | indeterminate => none

theorem emb_injective : Function.Injective emb := by
  rintro (a | _) (b | _) h <;> simp_all [emb]

/-- **Mergulho para `⊕`.** -/
theorem emb_add (x y : Card) : emb (add x y) = addI (emb x) (emb y) := by
  rcases x with a | _ <;> rcases y with b | _
  · simp [add, emb, addI_some]
  all_goals rfl

/-- **Mergulho para `⊗`** (inclusive `0 ⊗ I = I`, como em `RI`). -/
theorem emb_mul (x y : Card) : emb (mul x y) = mulI (emb x) (emb y) := by
  rcases x with a | _ <;> rcases y with b | _
  · simp [mul, emb, mulI_some]
  all_goals rfl

/-- **Incompatível para `⊖`**: `n ⊖ n = I` em CARD, `n − n = 0` em `RI`. -/
theorem sub_incompativel :
    ¬ ∃ f : Card → RI, (∀ n, f (cardinal n) = some (n : ℝ)) ∧
      ∀ x y, f (sub x y) = subI (f x) (f y) := by
  rintro ⟨f, hf, hs⟩
  have e0 : sub (cardinal 0) (cardinal 0) = indeterminate := rfl
  have h1 := hs (cardinal 0) (cardinal 0)
  rw [e0, hf] at h1
  have e1 : sub indeterminate (cardinal 1) = indeterminate := rfl
  have h2 := hs indeterminate (cardinal 1)
  rw [e1, h1, hf] at h2
  simp only [subI, Nat.cast_zero, Nat.cast_one, sub_self, Option.some.injEq] at h2
  norm_num at h2

end CARD

/-! ## KIJ (`lean/IAlgebra.lean`): `ℝ ∪ {I, J}`, `0 ⊗ I = 0` -/

namespace KIJ

inductive Kij where
  | real : ℝ → Kij
  | I : Kij
  | J : Kij

open Kij

def add : Kij → Kij → Kij
  | real a, real b => real (a + b)
  | I, _ => I
  | _, I => I
  | J, _ => J
  | _, J => J

def mul : Kij → Kij → Kij
  | real a, real b => real (a * b)
  | real a, I => if a = 0 then real 0 else I
  | I, real a => if a = 0 then real 0 else I
  | real a, J => if a = 0 then real 0 else J
  | J, real a => if a = 0 then real 0 else J
  | I, _ => I
  | J, I => I
  | J, J => J

theorem zero_mul_I : mul (real 0) I = real 0 := by simp [mul]

/-- **Incompatível**: nenhuma `f` que fixe os reais preserva `⊕` e `⊗`. -/
theorem incompativel :
    ¬ ∃ f : Kij → RI, (∀ a, f (real a) = some a) ∧
      (∀ x y, f (add x y) = addI (f x) (f y)) ∧ (∀ x y, f (mul x y) = mulI (f x) (f y)) := by
  rintro ⟨f, hr, ha, hm⟩
  have hI : f I = none := by
    have h := ha I (real 1)
    have e : add I (real 1) = I := rfl
    rw [e, hr] at h
    rcases hfi : f I with _ | c
    · rfl
    · rw [hfi, addI_some, Option.some.injEq] at h
      linarith
  have h := hm (real 0) I
  rw [zero_mul_I, hr, hI, mulI_none_right] at h
  exact Option.some_ne_none _ h

end KIJ

/-! ## IEA (`lean/IEA.lean`, ramo `copilot/analyze-complex-plane-singularities`) -/

namespace IEA

inductive Singularity where
  | I | J | PosInf | NegInf | ImagInfPos | ImagInfNeg

inductive Elem where
  | real : ℝ → Elem
  | complex : ℂ → Elem
  | singularity : Singularity → Elem

open Elem

def I : Elem := singularity .I
def J : Elem := singularity .J

def add : Elem → Elem → Elem
  | real a, real b => real (a + b)
  | complex a, complex b => complex (a + b)
  | singularity .I, _ => singularity .I
  | _, singularity .I => singularity .I
  | singularity .J, _ => singularity .J
  | _, singularity .J => singularity .J
  | singularity .PosInf, singularity .NegInf => singularity .I
  | singularity .NegInf, singularity .PosInf => singularity .I
  | singularity .PosInf, _ => singularity .PosInf
  | singularity .NegInf, _ => singularity .NegInf
  | _, _ => singularity .I

def mul : Elem → Elem → Elem
  | real a, singularity .I => if a = 0 then real 0 else singularity .I
  | singularity .I, real a => if a = 0 then real 0 else singularity .I
  | real a, singularity .J => if a = 0 then real 0 else singularity .J
  | singularity .J, real a => if a = 0 then real 0 else singularity .J
  | real a, real b => real (a * b)
  | complex a, complex b => complex (a * b)
  | singularity .I, _ => singularity .I
  | _, singularity .I => singularity .I
  | singularity .J, _ => singularity .J
  | _, singularity .J => singularity .J
  | _, _ => singularity .I

theorem add_I_left (x : Elem) : add I x = I := by
  cases x with
  | real a => rfl
  | complex c => rfl
  | singularity s => cases s <;> rfl

theorem zero_mul_I : mul (real 0) I = real 0 := by simp [mul, I]

/-- **Incompatível**: nenhuma `f` que fixe os reais preserva `⊕` e `⊗`. -/
theorem incompativel :
    ¬ ∃ f : Elem → RI, (∀ a, f (real a) = some a) ∧
      (∀ x y, f (add x y) = addI (f x) (f y)) ∧ (∀ x y, f (mul x y) = mulI (f x) (f y)) := by
  rintro ⟨f, hr, ha, hm⟩
  have hI : f I = none := by
    have h := ha I (real 1)
    rw [add_I_left, hr] at h
    rcases hfi : f I with _ | c
    · rfl
    · rw [hfi, addI_some, Option.some.injEq] at h
      linarith
  have h := hm (real 0) I
  rw [zero_mul_I, hr, hI, mulI_none_right] at h
  exact Option.some_ne_none _ h

/-- **O axioma A3 (distributividade modificada) é falso no próprio modelo**, para todo `λ` e nas
duas leituras de `x ⊕ y ⊕ z`: com `a = I`, `b = 1`, `c = −1` o lado esquerdo é `0` e o direito `I`. -/
theorem A3_falso (lam : ℝ) :
    mul I (add (real 1) (real (-1))) ≠
        add (add (mul I (real 1)) (mul I (real (-1)))) (mul (real lam) J) ∧
      mul I (add (real 1) (real (-1))) ≠
        add (mul I (real 1)) (add (mul I (real (-1))) (mul (real lam) J)) := by
  have h1 : add (real 1) (real (-1)) = real 0 := by simp [add]
  have h2 : mul I (real 0) = real 0 := by simp [mul, I]
  have h3 : mul I (real 1) = I := by simp [mul, I]
  simp only [h1, h2, h3, add_I_left]
  exact ⟨by simp [I], by simp [I]⟩

end IEA

/-! ## AEI (`formalizations/lean/AlgebraIndeterminate/AEI.lean`): "`I = 1/0`", `0·I = 1` -/

namespace AEI

inductive KI where
  | fromField : ℝ → KI
  | indeterminate : KI

open KI

def add : KI → KI → KI
  | fromField a, fromField b => fromField (a + b)
  | indeterminate, _ => indeterminate
  | _, indeterminate => indeterminate

def mul : KI → KI → KI
  | fromField a, fromField b => fromField (a * b)
  | fromField a, indeterminate => if a = 0 then fromField 1 else indeterminate
  | indeterminate, fromField a => if a = 0 then fromField 1 else indeterminate
  | indeterminate, indeterminate => indeterminate

theorem zero_mul_I : mul (fromField 0) indeterminate = fromField 1 := by simp [mul]

/-- **A multiplicação de AEI não é associativa**: `(0·I)·I = I`, `0·(I·I) = 1`. -/
theorem nao_associativa :
    mul (mul (fromField 0) indeterminate) indeterminate ≠
      mul (fromField 0) (mul indeterminate indeterminate) := by
  have h1 : mul (fromField 1) indeterminate = indeterminate := by simp [mul]
  have h2 : mul indeterminate indeterminate = indeterminate := rfl
  rw [zero_mul_I, h1, h2, zero_mul_I]
  exact fun h => by cases h

/-- **Incompatível**: nenhuma `f` que fixe o corpo preserva `·`. -/
theorem incompativel :
    ¬ ∃ f : KI → RI, (∀ a, f (fromField a) = some a) ∧ ∀ x y, f (mul x y) = mulI (f x) (f y) := by
  rintro ⟨f, hr, hm⟩
  have h := hm (fromField 0) indeterminate
  rw [zero_mul_I, hr, hr] at h
  rcases hfi : f indeterminate with _ | c
  · rw [hfi, mulI_none_right] at h
    exact Option.some_ne_none _ h
  · rw [hfi, mulI_some, Option.some.injEq, zero_mul] at h
    exact one_ne_zero h

end AEI

/-! ## ZDIV (`formalizations/lean/IAlgebra.lean`): soma ou produto nulo vira `I` -/

namespace ZDIV

inductive Z where
  | real : ℝ → Z
  | indeterminate : Z
  | recipIndeterminate : Z

open Z

def eadd : Z → Z → Z
  | real a, real b => if a + b = 0 then indeterminate else real (a + b)
  | indeterminate, _ => indeterminate
  | _, indeterminate => indeterminate
  | recipIndeterminate, recipIndeterminate => recipIndeterminate
  | _, _ => indeterminate

def ediv : Z → Z → Z
  | real a, real b => if b = 0 then indeterminate else real (a / b)
  | indeterminate, _ => indeterminate
  | _, indeterminate => indeterminate
  | _, _ => indeterminate

theorem eadd_I_right (x : Z) : eadd x indeterminate = indeterminate := by cases x <;> rfl

/-- **`⊕` não é associativa**: `(1 ⊕ 1) ⊕ (−1) = 1`, `1 ⊕ (1 ⊕ (−1)) = I`. -/
theorem nao_associativa :
    eadd (eadd (real 1) (real 1)) (real (-1)) ≠ eadd (real 1) (eadd (real 1) (real (-1))) := by
  have h1 : eadd (real 1) (real 1) = real 2 := by norm_num [eadd]
  have h2 : eadd (real 2) (real (-1)) = real 1 := by norm_num [eadd]
  have h3 : eadd (real 1) (real (-1)) = indeterminate := by norm_num [eadd]
  rw [h1, h2, h3, eadd_I_right]
  exact fun h => by cases h

/-- **O axioma `j_property : J = 1 ⊘ I` é falso**: pela própria definição, `1 ⊘ I = I ≠ J`. -/
theorem j_property_falso : recipIndeterminate ≠ ediv (real 1) indeterminate := by
  have h : ediv (real 1) indeterminate = indeterminate := rfl
  rw [h]
  exact fun h => by cases h

/-- **Incompatível**: nenhuma `f` que fixe os reais preserva `⊕`. -/
theorem incompativel :
    ¬ ∃ f : Z → RI, (∀ a, f (real a) = some a) ∧ ∀ x y, f (eadd x y) = addI (f x) (f y) := by
  rintro ⟨f, hr, ha⟩
  have e1 : eadd (real 1) (real (-1)) = indeterminate := by norm_num [eadd]
  have h1 := ha (real 1) (real (-1))
  rw [e1, hr, hr, addI_some] at h1
  have e2 : eadd indeterminate (real 1) = indeterminate := rfl
  have h2 := ha indeterminate (real 1)
  rw [e2, h1, hr, addI_some, Option.some.injEq] at h2
  norm_num at h2

end ZDIV

/-! ## FLEX (`formalizations/lean/AlgebraIndeterminate/FlexibleResolution.lean`): `a + bI` -/

namespace FLEX

structure KI where
  real_part : ℝ
  indet_coeff : ℝ

def add (x y : KI) : KI :=
  { real_part := x.real_part + y.real_part, indet_coeff := x.indet_coeff + y.indet_coeff }

/-- `Ω(I) = I` (o padrão da fonte). -/
def Omega : KI := { real_part := 0, indet_coeff := 1 }

def mul (x y : KI) : KI :=
  { real_part := x.real_part * y.real_part + x.indet_coeff * y.indet_coeff * Omega.real_part,
    indet_coeff := x.real_part * y.indet_coeff + x.indet_coeff * y.real_part +
      x.indet_coeff * y.indet_coeff * Omega.indet_coeff }

def I : KI := { real_part := 0, indet_coeff := 1 }

def ofReal (a : ℝ) : KI := { real_part := a, indet_coeff := 0 }

theorem I_idempotente : mul I I = I := by norm_num [mul, I, Omega]

/-- Isomorfismo com o anel produto: `a + bI ↦ (a, a + b)`. -/
def iso (x : KI) : ℝ × ℝ := (x.real_part, x.real_part + x.indet_coeff)

theorem iso_add (x y : KI) : iso (add x y) = iso x + iso y := by
  ext <;> simp only [iso, add, Prod.fst_add, Prod.snd_add] <;> ring

theorem iso_mul (x y : KI) : iso (mul x y) = iso x * iso y := by
  ext <;> simp only [iso, mul, Omega, Prod.fst_mul, Prod.snd_mul] <;> ring

theorem iso_bijective : Function.Bijective iso := by
  constructor
  · rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [iso, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    simp only [KI.mk.injEq]
    constructor <;> linarith
  · intro p
    exact ⟨⟨p.1, p.2 - p.1⟩, by simp [iso]⟩

/-- **Incompatível com `RI`**: em FLEX, `(−1)·I + I = 0`; em `RI`, `I` não tem oposto. -/
theorem incompativel :
    ¬ ∃ f : KI → RI, (∀ a, f (ofReal a) = some a) ∧ f I = none ∧
      (∀ x y, f (add x y) = addI (f x) (f y)) ∧ (∀ x y, f (mul x y) = mulI (f x) (f y)) := by
  rintro ⟨f, hr, hI, ha, hm⟩
  have e : add (mul (ofReal (-1)) I) I = ofReal 0 := by
    norm_num [add, mul, ofReal, I, Omega]
  have h := ha (mul (ofReal (-1)) I) I
  rw [e, hr, hm, hr, hI, mulI_none_right, addI_none_right] at h
  exact Option.some_ne_none _ h

end FLEX

/-! ## PAX (`lean/AlgebraI/Basic.lean`, P1–P15): inconsistente -/

/-- **PAX não tem modelo**: P2 (associatividade), P4 (`a + 0 = a`), P5 (`a + (−a) = 0`),
P12 (`I + I = I`) e P10 (`I ≠ 0`) já se contradizem. -/
theorem PAX_inconsistente {α : Type*} (zero i : α) (add : α → α → α) (neg : α → α)
    (add_assoc : ∀ a b c, add (add a b) c = add a (add b c))
    (add_zero_right : ∀ a, add a zero = a)
    (add_neg_right : ∀ a, add a (neg a) = zero)
    (i_plus_i : add i i = i) (i_ne_zero : i ≠ zero) : False := by
  apply i_ne_zero
  calc i = add i zero := (add_zero_right i).symm
    _ = add i (add i (neg i)) := by rw [add_neg_right]
    _ = add (add i i) (neg i) := (add_assoc i i (neg i)).symm
    _ = zero := by rw [i_plus_i, add_neg_right]

end ATK.IPortadores

end

#print axioms ATK.IPortadores.imath_divisao_nao_preservada
#print axioms ATK.IPortadores.ABS.emb_injective
#print axioms ATK.IPortadores.ABS.emb_add
#print axioms ATK.IPortadores.ABS.emb_mul
#print axioms ATK.IPortadores.ABS.emb_div
#print axioms ATK.IPortadores.Nexus.inv_zero_eq_I
#print axioms ATK.IPortadores.Nexus.zero_mul_I
#print axioms ATK.IPortadores.CARD.emb_injective
#print axioms ATK.IPortadores.CARD.emb_add
#print axioms ATK.IPortadores.CARD.emb_mul
#print axioms ATK.IPortadores.CARD.sub_incompativel
#print axioms ATK.IPortadores.KIJ.zero_mul_I
#print axioms ATK.IPortadores.KIJ.incompativel
#print axioms ATK.IPortadores.IEA.add_I_left
#print axioms ATK.IPortadores.IEA.zero_mul_I
#print axioms ATK.IPortadores.IEA.incompativel
#print axioms ATK.IPortadores.IEA.A3_falso
#print axioms ATK.IPortadores.AEI.zero_mul_I
#print axioms ATK.IPortadores.AEI.nao_associativa
#print axioms ATK.IPortadores.AEI.incompativel
#print axioms ATK.IPortadores.ZDIV.eadd_I_right
#print axioms ATK.IPortadores.ZDIV.nao_associativa
#print axioms ATK.IPortadores.ZDIV.j_property_falso
#print axioms ATK.IPortadores.ZDIV.incompativel
#print axioms ATK.IPortadores.FLEX.I_idempotente
#print axioms ATK.IPortadores.FLEX.iso_add
#print axioms ATK.IPortadores.FLEX.iso_mul
#print axioms ATK.IPortadores.FLEX.iso_bijective
#print axioms ATK.IPortadores.FLEX.incompativel
#print axioms ATK.IPortadores.PAX_inconsistente
