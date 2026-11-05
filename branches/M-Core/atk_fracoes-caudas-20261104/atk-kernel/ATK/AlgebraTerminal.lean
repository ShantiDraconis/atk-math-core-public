import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# ATK — Álgebra de Terminais com Certificação

Formalização da estrutura proposta: **intervalos racionais certificados** com operações, mais
**estados de evidência** `U < A < P` e **certificados condicionais** `Cert x H` (o valor real `x`
está no intervalo **se** a hipótese `H` vale).

* Boa definição: cada operação devolve um intervalo com `lo ≤ hi` (o campo `le` da estrutura);
  a inversão só existe com um certificado de que o intervalo exclui `0`.
* Correção (axioma A2 → teorema): `mem_add`, `mem_neg`, `mem_sub`, `mem_mul`, `mem_inv`, `mem_div`.
* Imagem exata: `mem_add_iff`, `mem_mul_iff` — o intervalo calculado é **exatamente** o conjunto
  `{x ∘ y}` (via conexidade do retângulo).
* Leis: `add_comm`, `add_assoc`, `add_zero`, `mul_comm`, `mul_assoc`, `mul_one`, `neg_neg`;
  `subdistributiva`: `A(B + C) ⊆ AB + AC`.
* Refutações: `distributiva_falha` (`[-1,1]·([1,1] + [-1,-1]) ≠ [-1,1]·[1,1] + [-1,1]·[-1,-1]`),
  `dependencia` (`A − A ≠ [0,0]` se `A` não é um ponto).
* Estados (axiomas A3, A4 → teoremas): `comb_eq_P_iff`, `nao_promocao`.
* Certificados: `Cert.add`, `Cert.mul`, … conjugam as hipóteses; `Cert.descarga` exige a prova de
  `H`; `hipotese_nao_e_teorema`: um certificado condicional sozinho não garante o valor.
* Modelos: `modelo_A` (`1 − 1/4 − 1/3 = 5/12`, inverso `12/5`), `modelo_B`
  (`[0,39; 0,44]`, inverso `[25/11, 100/39]`), `leis_satisfeitas`.

Consistência relativa: tudo aqui é **definido** dentro da teoria de base do Lean/Mathlib; as leis
são teoremas sobre essas definições, então a estrutura é consistente se a base for.
-/

namespace ATK.AlgebraTerminal

open Set

/-- Intervalo racional fechado não vazio `[lo, hi]`. -/
structure Intervalo where
  lo : ℚ
  hi : ℚ
  le : lo ≤ hi

namespace Intervalo

/-- `x ∈ [lo, hi]` para `x` real. -/
def Mem (x : ℝ) (A : Intervalo) : Prop := x ∈ Icc (A.lo : ℝ) (A.hi : ℝ)

theorem mem_def {x : ℝ} {A : Intervalo} : Mem x A ↔ (A.lo : ℝ) ≤ x ∧ x ≤ A.hi := Iff.rfl

theorem ext_lohi {A B : Intervalo} (h1 : A.lo = B.lo) (h2 : A.hi = B.hi) : A = B := by
  cases A; cases B; cases h1; cases h2; rfl

theorem lo_mem (A : Intervalo) : Mem A.lo A := ⟨le_rfl, by exact_mod_cast A.le⟩

theorem hi_mem (A : Intervalo) : Mem A.hi A := ⟨by exact_mod_cast A.le, le_rfl⟩

/-- **Extensionalidade**: dois intervalos com os mesmos pontos reais são iguais. -/
theorem eq_of_mem_iff {A B : Intervalo} (h : ∀ x : ℝ, Mem x A ↔ Mem x B) : A = B := by
  have h1 := (h A.lo).1 A.lo_mem
  have h2 := (h B.lo).2 B.lo_mem
  have h3 := (h A.hi).1 A.hi_mem
  have h4 := (h B.hi).2 B.hi_mem
  apply ext_lohi
  · have : (A.lo : ℝ) = B.lo := le_antisymm h2.1 h1.1
    exact_mod_cast this
  · have : (A.hi : ℝ) = B.hi := le_antisymm h3.2 h4.2
    exact_mod_cast this

/-- O intervalo pontual `[q, q]`. -/
def ponto (q : ℚ) : Intervalo := ⟨q, q, le_rfl⟩

theorem mem_ponto {x : ℝ} {q : ℚ} : Mem x (ponto q) ↔ x = q := by
  rw [mem_def]; simp only [ponto]; constructor
  · rintro ⟨h1, h2⟩; exact le_antisymm h2 h1
  · rintro rfl; exact ⟨le_rfl, le_rfl⟩

instance : Add Intervalo := ⟨fun A B => ⟨A.lo + B.lo, A.hi + B.hi, add_le_add A.le B.le⟩⟩
instance : Neg Intervalo := ⟨fun A => ⟨-A.hi, -A.lo, neg_le_neg A.le⟩⟩
instance : Sub Intervalo := ⟨fun A B => A + -B⟩

/-- Extremo inferior do produto: o menor dos quatro produtos dos extremos. -/
def mlo (A B : Intervalo) : ℚ := min (min (A.lo * B.lo) (A.lo * B.hi)) (min (A.hi * B.lo) (A.hi * B.hi))
/-- Extremo superior do produto: o maior dos quatro produtos dos extremos. -/
def mhi (A B : Intervalo) : ℚ := max (max (A.lo * B.lo) (A.lo * B.hi)) (max (A.hi * B.lo) (A.hi * B.hi))

theorem mlo_le_mhi (A B : Intervalo) : mlo A B ≤ mhi A B :=
  le_trans (min_le_of_left_le (min_le_left _ _)) (le_max_of_le_left (le_max_left _ _))

instance : Mul Intervalo := ⟨fun A B => ⟨mlo A B, mhi A B, mlo_le_mhi A B⟩⟩

@[simp] theorem add_lo (A B : Intervalo) : (A + B).lo = A.lo + B.lo := rfl
@[simp] theorem add_hi (A B : Intervalo) : (A + B).hi = A.hi + B.hi := rfl
@[simp] theorem neg_lo (A : Intervalo) : (-A).lo = -A.hi := rfl
@[simp] theorem neg_hi (A : Intervalo) : (-A).hi = -A.lo := rfl
@[simp] theorem sub_lo (A B : Intervalo) : (A - B).lo = A.lo - B.hi := by
  show A.lo + -B.hi = _; ring
@[simp] theorem sub_hi (A B : Intervalo) : (A - B).hi = A.hi - B.lo := by
  show A.hi + -B.lo = _; ring
@[simp] theorem mul_lo (A B : Intervalo) : (A * B).lo = mlo A B := rfl
@[simp] theorem mul_hi (A B : Intervalo) : (A * B).hi = mhi A B := rfl

/-! ## Correção: as operações contêm o resultado real -/

theorem mem_add {x y : ℝ} {A B : Intervalo} (hx : Mem x A) (hy : Mem y B) : Mem (x + y) (A + B) := by
  rw [mem_def] at *; simp only [add_lo, add_hi]; push_cast
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_neg {x : ℝ} {A : Intervalo} (hx : Mem x A) : Mem (-x) (-A) := by
  rw [mem_def] at *; simp only [neg_lo, neg_hi]; push_cast
  constructor <;> linarith [hx.1, hx.2]

theorem mem_sub {x y : ℝ} {A B : Intervalo} (hx : Mem x A) (hy : Mem y B) : Mem (x - y) (A - B) := by
  rw [sub_eq_add_neg]; exact mem_add hx (mem_neg hy)

/-- `x ∈ [a,b]` ⇒ `x·y ≥ min(a·y, b·y)` (afim em `x`). -/
theorem min_le_mul_aux {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) : min (a * y) (b * y) ≤ x * y := by
  rcases le_total 0 y with hy | hy
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

theorem mul_le_max_aux {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) : x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact (by nlinarith : x * y ≤ b * y).trans (le_max_right _ _)
  · exact (by nlinarith : x * y ≤ a * y).trans (le_max_left _ _)

theorem min4_le_mul {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  have h1 := min_le_mul_aux (y := y) hx1 hx2
  have h2 : min (a * c) (a * d) ≤ a * y := by
    rw [mul_comm a c, mul_comm a d, mul_comm a y]; exact min_le_mul_aux hy1 hy2
  have h3 : min (b * c) (b * d) ≤ b * y := by
    rw [mul_comm b c, mul_comm b d, mul_comm b y]; exact min_le_mul_aux hy1 hy2
  exact (min_le_min h2 h3).trans h1

theorem mul_le_max4 {a b c d x y : ℝ} (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have h1 := mul_le_max_aux (y := y) hx1 hx2
  have h2 : a * y ≤ max (a * c) (a * d) := by
    rw [mul_comm a c, mul_comm a d, mul_comm a y]; exact mul_le_max_aux hy1 hy2
  have h3 : b * y ≤ max (b * c) (b * d) := by
    rw [mul_comm b c, mul_comm b d, mul_comm b y]; exact mul_le_max_aux hy1 hy2
  exact h1.trans (max_le_max h2 h3)

theorem cast_mlo (A B : Intervalo) : ((mlo A B : ℚ) : ℝ) =
    min (min ((A.lo : ℝ) * B.lo) ((A.lo : ℝ) * B.hi)) (min ((A.hi : ℝ) * B.lo) ((A.hi : ℝ) * B.hi)) := by
  unfold mlo; push_cast; rfl

theorem cast_mhi (A B : Intervalo) : ((mhi A B : ℚ) : ℝ) =
    max (max ((A.lo : ℝ) * B.lo) ((A.lo : ℝ) * B.hi)) (max ((A.hi : ℝ) * B.lo) ((A.hi : ℝ) * B.hi)) := by
  unfold mhi; push_cast; rfl

theorem mem_mul {x y : ℝ} {A B : Intervalo} (hx : Mem x A) (hy : Mem y B) : Mem (x * y) (A * B) := by
  rw [mem_def] at *
  simp only [mul_lo, mul_hi, cast_mlo, cast_mhi]
  exact ⟨min4_le_mul hx.1 hx.2 hy.1 hy.2, mul_le_max4 hx.1 hx.2 hy.1 hy.2⟩

/-! ## Imagem exata (conexidade do retângulo) -/

theorem preconexo_imagem (f : ℝ × ℝ → ℝ) (hf : Continuous f) (A B : Intervalo) :
    IsPreconnected (f '' (Icc (A.lo : ℝ) A.hi ×ˢ Icc (B.lo : ℝ) B.hi)) :=
  (isPreconnected_Icc.prod isPreconnected_Icc).image f hf.continuousOn

theorem canto_mem (f : ℝ × ℝ → ℝ) {A B : Intervalo} {u v : ℝ} (hu : Mem u A) (hv : Mem v B) :
    f (u, v) ∈ f '' (Icc (A.lo : ℝ) A.hi ×ˢ Icc (B.lo : ℝ) B.hi) :=
  ⟨(u, v), ⟨hu, hv⟩, rfl⟩

theorem mem_add_iff {z : ℝ} {A B : Intervalo} :
    Mem z (A + B) ↔ ∃ x y, Mem x A ∧ Mem y B ∧ z = x + y := by
  constructor
  · intro hz
    let f : ℝ × ℝ → ℝ := fun p => p.1 + p.2
    have hS := preconexo_imagem f (continuous_fst.add continuous_snd) A B
    have h1 := canto_mem f A.lo_mem B.lo_mem
    have h2 := canto_mem f A.hi_mem B.hi_mem
    have hsub := hS.Icc_subset h1 h2
    have hz' : z ∈ Icc (f ((A.lo : ℝ), (B.lo : ℝ))) (f ((A.hi : ℝ), (B.hi : ℝ))) := by
      rw [mem_def] at hz; simp only [add_lo, add_hi] at hz; push_cast at hz; exact hz
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩ := hsub hz'
    exact ⟨x, y, hx, hy, rfl⟩
  · rintro ⟨x, y, hx, hy, rfl⟩; exact mem_add hx hy

theorem min4_choice (p q r s : ℝ) :
    min (min p q) (min r s) = p ∨ min (min p q) (min r s) = q ∨
      min (min p q) (min r s) = r ∨ min (min p q) (min r s) = s := by
  rcases min_choice p q with h1 | h1 <;> rcases min_choice r s with h2 | h2 <;>
    rcases min_choice (min p q) (min r s) with h3 | h3 <;> simp_all

theorem max4_choice (p q r s : ℝ) :
    max (max p q) (max r s) = p ∨ max (max p q) (max r s) = q ∨
      max (max p q) (max r s) = r ∨ max (max p q) (max r s) = s := by
  rcases max_choice p q with h1 | h1 <;> rcases max_choice r s with h2 | h2 <;>
    rcases max_choice (max p q) (max r s) with h3 | h3 <;> simp_all

theorem mem_mul_iff {z : ℝ} {A B : Intervalo} :
    Mem z (A * B) ↔ ∃ x y, Mem x A ∧ Mem y B ∧ z = x * y := by
  constructor
  · intro hz
    let f : ℝ × ℝ → ℝ := fun p => p.1 * p.2
    set S := f '' (Icc (A.lo : ℝ) A.hi ×ˢ Icc (B.lo : ℝ) B.hi) with hSdef
    have hS : IsPreconnected S := preconexo_imagem f (continuous_fst.mul continuous_snd) A B
    have c1 : (A.lo : ℝ) * B.lo ∈ S := canto_mem f A.lo_mem B.lo_mem
    have c2 : (A.lo : ℝ) * B.hi ∈ S := canto_mem f A.lo_mem B.hi_mem
    have c3 : (A.hi : ℝ) * B.lo ∈ S := canto_mem f A.hi_mem B.lo_mem
    have c4 : (A.hi : ℝ) * B.hi ∈ S := canto_mem f A.hi_mem B.hi_mem
    have hmin : ((mlo A B : ℚ) : ℝ) ∈ S := by
      rw [cast_mlo]
      rcases min4_choice ((A.lo : ℝ) * B.lo) ((A.lo : ℝ) * B.hi) ((A.hi : ℝ) * B.lo)
        ((A.hi : ℝ) * B.hi) with h | h | h | h <;> rw [h] <;> assumption
    have hmax : ((mhi A B : ℚ) : ℝ) ∈ S := by
      rw [cast_mhi]
      rcases max4_choice ((A.lo : ℝ) * B.lo) ((A.lo : ℝ) * B.hi) ((A.hi : ℝ) * B.lo)
        ((A.hi : ℝ) * B.hi) with h | h | h | h <;> rw [h] <;> assumption
    obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩ := hS.Icc_subset hmin hmax hz
    exact ⟨x, y, hx, hy, hxy.symm⟩
  · rintro ⟨x, y, hx, hy, rfl⟩; exact mem_mul hx hy

/-! ## Leis -/

theorem add_comm (A B : Intervalo) : A + B = B + A := ext_lohi (by simp [_root_.add_comm]) (by simp [_root_.add_comm])

theorem add_assoc (A B C : Intervalo) : A + B + C = A + (B + C) :=
  ext_lohi (by simp [_root_.add_assoc]) (by simp [_root_.add_assoc])

theorem add_zero (A : Intervalo) : A + ponto 0 = A := ext_lohi (by simp [ponto]) (by simp [ponto])

theorem neg_neg (A : Intervalo) : - -A = A := ext_lohi (by simp) (by simp)

theorem mul_comm (A B : Intervalo) : A * B = B * A := by
  apply eq_of_mem_iff; intro z
  simp only [mem_mul_iff]
  constructor <;> rintro ⟨x, y, hx, hy, rfl⟩ <;> exact ⟨y, x, hy, hx, _root_.mul_comm _ _⟩

theorem mul_assoc (A B C : Intervalo) : A * B * C = A * (B * C) := by
  apply eq_of_mem_iff; intro z
  simp only [mem_mul_iff]
  constructor
  · rintro ⟨w, u, ⟨x, y, hx, hy, rfl⟩, hu, rfl⟩
    exact ⟨x, y * u, hx, ⟨y, u, hy, hu, rfl⟩, _root_.mul_assoc _ _ _⟩
  · rintro ⟨x, w, hx, ⟨y, u, hy, hu, rfl⟩, rfl⟩
    exact ⟨x * y, u, ⟨x, y, hx, hy, rfl⟩, hu, (_root_.mul_assoc _ _ _).symm⟩

theorem mul_one (A : Intervalo) : A * ponto 1 = A := by
  apply eq_of_mem_iff; intro z
  rw [mem_mul_iff]
  constructor
  · rintro ⟨x, y, hx, hy, rfl⟩
    rw [mem_ponto] at hy; rw [hy]; push_cast; rw [_root_.mul_one]; exact hx
  · intro hz; exact ⟨z, 1, hz, by rw [mem_ponto]; norm_num, (_root_.mul_one z).symm⟩

/-- **Subdistributividade**: `A(B + C) ⊆ AB + AC`. -/
theorem subdistributiva (A B C : Intervalo) {z : ℝ} (hz : Mem z (A * (B + C))) :
    Mem z (A * B + A * C) := by
  obtain ⟨x, w, hx, hw, rfl⟩ := mem_mul_iff.1 hz
  obtain ⟨y, u, hy, hu, rfl⟩ := mem_add_iff.1 hw
  rw [_root_.mul_add]
  exact mem_add (mem_mul hx hy) (mem_mul hx hu)

/-- **A distributividade falha**: `[-1,1]·([1,1] + [-1,-1]) = [0,0]`, mas
`[-1,1]·[1,1] + [-1,1]·[-1,-1] = [-2,2]`. -/
theorem distributiva_falha :
    (⟨-1, 1, by norm_num⟩ : Intervalo) * (ponto 1 + ponto (-1)) ≠
      (⟨-1, 1, by norm_num⟩ : Intervalo) * ponto 1 + (⟨-1, 1, by norm_num⟩ : Intervalo) * ponto (-1) := by
  intro h
  have := congrArg Intervalo.lo h
  simp [mlo, ponto] at this
  norm_num at this

/-- **Dependência**: `A − A` não é `[0,0]` quando `A` não é um ponto (contém `0`, mas é maior). -/
theorem dependencia (A : Intervalo) (h : A.lo < A.hi) : A - A ≠ ponto 0 := by
  intro he
  have := congrArg Intervalo.lo he
  simp [ponto] at this
  linarith

theorem zero_mem_sub_self (A : Intervalo) : Mem 0 (A - A) := by
  have := mem_sub A.lo_mem A.lo_mem; simpa using this

/-! ## Inversão e divisão -/

/-- Inverso, definido só quando o intervalo exclui `0`. -/
def inv (A : Intervalo) (h : 0 < A.lo ∨ A.hi < 0) : Intervalo :=
  ⟨A.hi⁻¹, A.lo⁻¹, by
    rcases h with h | h
    · exact inv_anti₀ h A.le
    · exact (inv_le_inv_of_neg h (by linarith [A.le])).2 A.le⟩

theorem mem_inv {x : ℝ} {A : Intervalo} (h : 0 < A.lo ∨ A.hi < 0) (hx : Mem x A) :
    Mem x⁻¹ (inv A h) := by
  rw [mem_def] at *
  simp only [inv]; push_cast
  rcases h with h | h
  · have h' : (0 : ℝ) < A.lo := by exact_mod_cast h
    have hx0 : 0 < x := by linarith [hx.1]
    exact ⟨inv_anti₀ hx0 hx.2, inv_anti₀ h' hx.1⟩
  · have h' : (A.hi : ℝ) < 0 := by exact_mod_cast h
    have hx0 : x < 0 := by linarith [hx.2]
    have hlo : (A.lo : ℝ) < 0 := by linarith [hx.1]
    exact ⟨(inv_le_inv_of_neg h' hx0).2 hx.2, (inv_le_inv_of_neg hx0 hlo).2 hx.1⟩

/-- Divisão `A / B := A · B⁻¹`, só com `0 ∉ B`. -/
def div (A B : Intervalo) (h : 0 < B.lo ∨ B.hi < 0) : Intervalo := A * inv B h

theorem mem_div {x y : ℝ} {A B : Intervalo} (h : 0 < B.lo ∨ B.hi < 0) (hx : Mem x A)
    (hy : Mem y B) : Mem (x / y) (div A B h) := by
  rw [div_eq_mul_inv]; exact mem_mul hx (mem_inv h hy)

end Intervalo

/-! ## Estados de evidência -/

/-- `U`: não certificado; `A`: válido sob hipóteses declaradas; `P`: demonstrado. -/
inductive Estado
  | U
  | A
  | P
  deriving DecidableEq, Repr

namespace Estado

/-- Força da evidência. -/
def rank : Estado → ℕ
  | U => 0
  | A => 1
  | P => 2

theorem rank_injective : Function.Injective rank := by
  intro a b h; cases a <;> cases b <;> simp_all [rank]

instance : LinearOrder Estado := LinearOrder.lift' rank rank_injective

theorem le_iff {s t : Estado} : s ≤ t ↔ s.rank ≤ t.rank := Iff.rfl

theorem le_P (s : Estado) : s ≤ P := by cases s <;> decide

theorem U_le (s : Estado) : U ≤ s := by cases s <;> decide

/-- Combinação de duas premissas: o estado resultante é o mais fraco. -/
def comb (s t : Estado) : Estado := min s t

theorem comb_le_left (s t : Estado) : comb s t ≤ s := min_le_left s t
theorem comb_le_right (s t : Estado) : comb s t ≤ t := min_le_right s t
theorem comb_comm (s t : Estado) : comb s t = comb t s := min_comm s t
theorem comb_assoc (r s t : Estado) : comb (comb r s) t = comb r (comb s t) := min_assoc r s t

/-- **A3 (conservação de evidência)**: o resultado é `P` só se as duas premissas são `P`. -/
theorem comb_eq_P_iff (s t : Estado) : comb s t = P ↔ s = P ∧ t = P := by
  cases s <;> cases t <;> decide

/-- **A4 (não promoção)**: uma premissa não certificada torna o resultado não certificado. -/
theorem nao_promocao (t : Estado) : comb U t = U := by cases t <;> decide

end Estado

/-! ## Certificados condicionais: o estado com conteúdo -/

open Intervalo

/-- `Cert x H`: um intervalo que contém `x` **sob a hipótese** `H`. Estado `P` ⟺ `H = True`;
estado `A` ⟺ `H` é uma hipótese declarada; estado `U` ⟺ não há certificado. -/
structure Cert (x : ℝ) (H : Prop) where
  I : Intervalo
  mem : H → Mem x I

namespace Cert

def add {x y : ℝ} {H₁ H₂ : Prop} (a : Cert x H₁) (b : Cert y H₂) : Cert (x + y) (H₁ ∧ H₂) :=
  ⟨a.I + b.I, fun h => mem_add (a.mem h.1) (b.mem h.2)⟩

def neg {x : ℝ} {H : Prop} (a : Cert x H) : Cert (-x) H := ⟨-a.I, fun h => mem_neg (a.mem h)⟩

def sub {x y : ℝ} {H₁ H₂ : Prop} (a : Cert x H₁) (b : Cert y H₂) : Cert (x - y) (H₁ ∧ H₂) :=
  ⟨a.I - b.I, fun h => mem_sub (a.mem h.1) (b.mem h.2)⟩

def mul {x y : ℝ} {H₁ H₂ : Prop} (a : Cert x H₁) (b : Cert y H₂) : Cert (x * y) (H₁ ∧ H₂) :=
  ⟨a.I * b.I, fun h => mem_mul (a.mem h.1) (b.mem h.2)⟩

/-- Certificado demonstrado de um racional exato. -/
def exato (q : ℚ) : Cert (q : ℝ) True := ⟨ponto q, fun _ => mem_ponto.2 rfl⟩

/-- **Descarga**: o valor só fica garantido com a prova da hipótese. -/
theorem descarga {x : ℝ} {H : Prop} (c : Cert x H) (h : H) : Mem x c.I := c.mem h

/-- Um certificado demonstrado (`H = True`) garante o valor. -/
theorem demonstrado {x : ℝ} (c : Cert x True) : Mem x c.I := c.mem trivial

/-- **Hipótese não é teorema**: um certificado condicional sozinho não garante o valor
(contraexemplo com `H = False`). -/
theorem hipotese_nao_e_teorema : ¬ ∀ (x : ℝ) (H : Prop) (c : Cert x H), Mem x c.I := by
  intro h
  have := h 0 False ⟨ponto 1, False.elim⟩
  rw [mem_ponto] at this
  norm_num at this

/-- Fortalecer a hipótese preserva o certificado. -/
def enfraquece {x : ℝ} {H H' : Prop} (c : Cert x H) (hH : H' → H) : Cert x H' :=
  ⟨c.I, fun h => c.mem (hH h)⟩

end Cert

/-! ## Modelos concretos -/

/-- **Modelo A** (margem de absorção): `1 − 1/4 − 1/3 = [5/12, 5/12]`. -/
theorem modelo_A_margem : ponto 1 - ponto (1 / 4) - ponto (1 / 3) = ponto (5 / 12) :=
  ext_lohi (by simp [ponto]; norm_num) (by simp [ponto]; norm_num)

/-- **Modelo A** (amplificação): `[5/12]⁻¹ = [12/5]`. -/
theorem modelo_A_amplificacao :
    inv (ponto (5 / 12)) (Or.inl (by simp [ponto])) = ponto (12 / 5) :=
  ext_lohi (by simp [inv, ponto]) (by simp [inv, ponto])

/-- Intervalo `[0,24; 0,26]`. -/
def cB : Intervalo := ⟨24 / 100, 26 / 100, by norm_num⟩
/-- Intervalo `[0,32; 0,35]`. -/
def cT : Intervalo := ⟨32 / 100, 35 / 100, by norm_num⟩

/-- **Modelo B** (incerteza): `1 − [0,24; 0,26] − [0,32; 0,35] = [0,39; 0,44]`. -/
theorem modelo_B_margem : ponto 1 - cB - cT = ⟨39 / 100, 44 / 100, by norm_num⟩ :=
  ext_lohi (by simp [ponto, cB, cT]; norm_num) (by simp [ponto, cB, cT]; norm_num)

/-- **Modelo B** (amplificação): `[0,39; 0,44]⁻¹ = [25/11, 100/39]`. -/
theorem modelo_B_amplificacao :
    inv ⟨39 / 100, 44 / 100, by norm_num⟩ (Or.inl (by norm_num)) =
      ⟨25 / 11, 100 / 39, by norm_num⟩ :=
  ext_lohi (by norm_num [inv]) (by norm_num [inv])

/-- A margem real fica garantida em `[0,39; 0,44]` para quaisquer constantes nos intervalos. -/
theorem margem_certificada {b t : ℝ} (hb : Mem b cB) (ht : Mem t cT) :
    (39 / 100 : ℝ) ≤ 1 - b - t ∧ 1 - b - t ≤ 44 / 100 := by
  have h := mem_sub (mem_sub (mem_ponto.2 rfl : Mem ((1 : ℚ) : ℝ) (ponto 1)) hb) ht
  rw [modelo_B_margem, mem_def] at h
  push_cast at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **As leis são satisfeitas simultaneamente pelo modelo** (consistência relativa). -/
theorem leis_satisfeitas :
    (∀ A B : Intervalo, A + B = B + A) ∧ (∀ A B C : Intervalo, A + B + C = A + (B + C)) ∧
    (∀ A B : Intervalo, A * B = B * A) ∧ (∀ A B C : Intervalo, A * B * C = A * (B * C)) ∧
    (∀ A : Intervalo, A + ponto 0 = A) ∧ (∀ A : Intervalo, A * ponto 1 = A) ∧
    (∃ A B C : Intervalo, A * (B + C) ≠ A * B + A * C) :=
  ⟨add_comm, add_assoc, mul_comm, mul_assoc, add_zero, mul_one,
    ⟨_, _, _, distributiva_falha⟩⟩

end ATK.AlgebraTerminal

#print axioms ATK.AlgebraTerminal.Intervalo.mem_def
#print axioms ATK.AlgebraTerminal.Intervalo.ext_lohi
#print axioms ATK.AlgebraTerminal.Intervalo.lo_mem
#print axioms ATK.AlgebraTerminal.Intervalo.hi_mem
#print axioms ATK.AlgebraTerminal.Intervalo.eq_of_mem_iff
#print axioms ATK.AlgebraTerminal.Intervalo.mem_ponto
#print axioms ATK.AlgebraTerminal.Intervalo.mlo_le_mhi
#print axioms ATK.AlgebraTerminal.Intervalo.add_lo
#print axioms ATK.AlgebraTerminal.Intervalo.add_hi
#print axioms ATK.AlgebraTerminal.Intervalo.neg_lo
#print axioms ATK.AlgebraTerminal.Intervalo.neg_hi
#print axioms ATK.AlgebraTerminal.Intervalo.sub_lo
#print axioms ATK.AlgebraTerminal.Intervalo.sub_hi
#print axioms ATK.AlgebraTerminal.Intervalo.mul_lo
#print axioms ATK.AlgebraTerminal.Intervalo.mul_hi
#print axioms ATK.AlgebraTerminal.Intervalo.mem_add
#print axioms ATK.AlgebraTerminal.Intervalo.mem_neg
#print axioms ATK.AlgebraTerminal.Intervalo.mem_sub
#print axioms ATK.AlgebraTerminal.Intervalo.min_le_mul_aux
#print axioms ATK.AlgebraTerminal.Intervalo.mul_le_max_aux
#print axioms ATK.AlgebraTerminal.Intervalo.min4_le_mul
#print axioms ATK.AlgebraTerminal.Intervalo.mul_le_max4
#print axioms ATK.AlgebraTerminal.Intervalo.cast_mlo
#print axioms ATK.AlgebraTerminal.Intervalo.cast_mhi
#print axioms ATK.AlgebraTerminal.Intervalo.mem_mul
#print axioms ATK.AlgebraTerminal.Intervalo.preconexo_imagem
#print axioms ATK.AlgebraTerminal.Intervalo.canto_mem
#print axioms ATK.AlgebraTerminal.Intervalo.mem_add_iff
#print axioms ATK.AlgebraTerminal.Intervalo.min4_choice
#print axioms ATK.AlgebraTerminal.Intervalo.max4_choice
#print axioms ATK.AlgebraTerminal.Intervalo.mem_mul_iff
#print axioms ATK.AlgebraTerminal.Intervalo.add_comm
#print axioms ATK.AlgebraTerminal.Intervalo.add_assoc
#print axioms ATK.AlgebraTerminal.Intervalo.add_zero
#print axioms ATK.AlgebraTerminal.Intervalo.neg_neg
#print axioms ATK.AlgebraTerminal.Intervalo.mul_comm
#print axioms ATK.AlgebraTerminal.Intervalo.mul_assoc
#print axioms ATK.AlgebraTerminal.Intervalo.mul_one
#print axioms ATK.AlgebraTerminal.Intervalo.subdistributiva
#print axioms ATK.AlgebraTerminal.Intervalo.distributiva_falha
#print axioms ATK.AlgebraTerminal.Intervalo.dependencia
#print axioms ATK.AlgebraTerminal.Intervalo.zero_mem_sub_self
#print axioms ATK.AlgebraTerminal.Intervalo.mem_inv
#print axioms ATK.AlgebraTerminal.Intervalo.mem_div
#print axioms ATK.AlgebraTerminal.Estado.rank_injective
#print axioms ATK.AlgebraTerminal.Estado.le_iff
#print axioms ATK.AlgebraTerminal.Estado.le_P
#print axioms ATK.AlgebraTerminal.Estado.U_le
#print axioms ATK.AlgebraTerminal.Estado.comb_le_left
#print axioms ATK.AlgebraTerminal.Estado.comb_le_right
#print axioms ATK.AlgebraTerminal.Estado.comb_comm
#print axioms ATK.AlgebraTerminal.Estado.comb_assoc
#print axioms ATK.AlgebraTerminal.Estado.comb_eq_P_iff
#print axioms ATK.AlgebraTerminal.Estado.nao_promocao
#print axioms ATK.AlgebraTerminal.Cert.descarga
#print axioms ATK.AlgebraTerminal.Cert.demonstrado
#print axioms ATK.AlgebraTerminal.Cert.hipotese_nao_e_teorema
#print axioms ATK.AlgebraTerminal.modelo_A_margem
#print axioms ATK.AlgebraTerminal.modelo_A_amplificacao
#print axioms ATK.AlgebraTerminal.modelo_B_margem
#print axioms ATK.AlgebraTerminal.modelo_B_amplificacao
#print axioms ATK.AlgebraTerminal.margem_certificada
#print axioms ATK.AlgebraTerminal.leis_satisfeitas
