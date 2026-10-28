import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# ATK — A roda de Carlström: `0 = [0:1]`, `1 = [1:1]`, `∞ = [1:0]`, `⊥ = 0/0 = [0:0]`

Uma **roda** (Carlström, *Wheels — on division by zero*, 2004) é a estrutura algébrica em que a
divisão é total. Para um corpo `K`, a roda `K⊙` é o quociente de `K × K` pela escala
`(a, b) ~ (u a, u b)`, `u ≠ 0`, com

  `[a:b] + [c:d] = [ad + bc : bd]`,  `[a:b] · [c:d] = [ac : bd]`,  `/[a:b] = [b:a]`.

Os quatro pontos notáveis: `0 = [0:1]`, `1 = [1:1]`, `∞ = /0 = [1:0]`, `⊥ = 0/0 = [0:0]`.
A Mathlib **não** tem rodas; este arquivo as constrói do zero e prova:

* `+` e `·` são monoides comutativos; `/` é involução e `/(xy) = /x · /y`;
* os **oito axiomas de roda** de Carlström (`roda_w1` … `roda_w8`);
* `x / x = 1 + 0·x/x` — a lei que substitui `x/x = 1`;
* `/0 = ∞`, `0/0 = ⊥`, `∞/∞ = ⊥`, `0·∞ = ⊥`, `∞ + ∞ = ⊥`, `∞ − ∞ = ⊥`, `⊥` absorvente;
* **`⊥ ≠ 0`, `⊥ ≠ 1`, `⊥ ≠ ∞`** (o "Teorema 8" do acervo) e `0, 1, ∞` dois a dois distintos;
* o mergulho `a ↦ [a:1]` de `K` respeita `+`, `·` e devolve `a · /a = 1` para `a ≠ 0`;
* o preço: `0 · x = 0` e `x − x = 0` **deixam de valer** (`zero_mul_falha`, `sub_self_falha`),
  em acordo com o no-go de `ATK.TeoriaI`/`ATK.IAlgebra`.

Matemática conhecida (Carlström 2004); nova só a formalização.
-/

namespace ATK.Roda

variable (K : Type*) [Field K]

/-- `(a, b) ~ (c, d)` se `(c, d) = u · (a, b)` com `u ≠ 0`. -/
def rel (p q : K × K) : Prop := ∃ u : K, u ≠ 0 ∧ q.1 = u * p.1 ∧ q.2 = u * p.2

theorem rel_equiv : Equivalence (rel K) where
  refl p := ⟨1, one_ne_zero, by simp, by simp⟩
  symm := by
    rintro p q ⟨u, hu, h1, h2⟩
    refine ⟨u⁻¹, inv_ne_zero hu, ?_, ?_⟩
    · rw [h1, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
    · rw [h2, ← mul_assoc, inv_mul_cancel₀ hu, one_mul]
  trans := by
    rintro p q r ⟨u, hu, h1, h2⟩ ⟨v, hv, h3, h4⟩
    refine ⟨v * u, mul_ne_zero hv hu, ?_, ?_⟩
    · rw [h3, h1, mul_assoc]
    · rw [h4, h2, mul_assoc]

instance setoid : Setoid (K × K) := ⟨rel K, rel_equiv K⟩

/-- A roda `K⊙`. -/
def RodaK : Type _ := Quotient (setoid K)

variable {K}

/-- A classe `[a:b]`. -/
def mk (a b : K) : RodaK K := Quotient.mk (setoid K) (a, b)

/-- Indução: todo elemento é `[a:b]`. -/
@[elab_as_elim]
theorem ind {P : RodaK K → Prop} (h : ∀ a b : K, P (mk a b)) (x : RodaK K) : P x :=
  Quotient.inductionOn x (fun p => h p.1 p.2)

theorem mk_eq_mk_iff {a b c d : K} :
    mk a b = mk c d ↔ ∃ u : K, u ≠ 0 ∧ c = u * a ∧ d = u * b :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

/-! ## Operações -/

/-- Soma: `[a:b] + [c:d] = [ad + bc : bd]`. -/
def add : RodaK K → RodaK K → RodaK K :=
  Quotient.map₂ (fun p q => (p.1 * q.2 + p.2 * q.1, p.2 * q.2)) (by
    rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨u, hu, h1, h2⟩ ⟨c, d⟩ ⟨c', d'⟩ ⟨v, hv, h3, h4⟩
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    exact ⟨u * v, mul_ne_zero hu hv, by ring, by ring⟩)

/-- Produto: `[a:b] · [c:d] = [ac : bd]`. -/
def mul : RodaK K → RodaK K → RodaK K :=
  Quotient.map₂ (fun p q => (p.1 * q.1, p.2 * q.2)) (by
    rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨u, hu, h1, h2⟩ ⟨c, d⟩ ⟨c', d'⟩ ⟨v, hv, h3, h4⟩
    simp only at h1 h2 h3 h4
    subst h1 h2 h3 h4
    exact ⟨u * v, mul_ne_zero hu hv, by ring, by ring⟩)

/-- Recíproco total: `/[a:b] = [b:a]`. -/
def inv : RodaK K → RodaK K :=
  Quotient.map (fun p => (p.2, p.1)) (by
    rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨u, hu, h1, h2⟩
    exact ⟨u, hu, h2, h1⟩)

/-- Oposto: `−[a:b] = [−a:b]`. -/
def neg : RodaK K → RodaK K :=
  Quotient.map (fun p => (-p.1, p.2)) (by
    rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨u, hu, h1, h2⟩
    simp only at h1 h2
    subst h1 h2
    exact ⟨u, hu, by ring, rfl⟩)

instance : Zero (RodaK K) := ⟨mk 0 1⟩
instance : One (RodaK K) := ⟨mk 1 1⟩
instance : Add (RodaK K) := ⟨add⟩
instance : Mul (RodaK K) := ⟨mul⟩
instance : Inv (RodaK K) := ⟨inv⟩
instance : Neg (RodaK K) := ⟨neg⟩
instance : Sub (RodaK K) := ⟨fun x y => x + -y⟩
instance : Div (RodaK K) := ⟨fun x y => x * y⁻¹⟩

/-- `∞ = [1:0]`. -/
def infty : RodaK K := mk 1 0

/-- `⊥ = 0/0 = [0:0]`. -/
def bot : RodaK K := mk 0 0

theorem zero_def : (0 : RodaK K) = mk 0 1 := rfl
theorem one_def : (1 : RodaK K) = mk 1 1 := rfl
theorem mk_add_mk (a b c d : K) : mk a b + mk c d = mk (a * d + b * c) (b * d) := rfl
theorem mk_mul_mk (a b c d : K) : mk a b * mk c d = mk (a * c) (b * d) := rfl
theorem inv_mk (a b : K) : (mk a b)⁻¹ = mk b a := rfl
theorem neg_mk (a b : K) : -(mk a b) = mk (-a) b := rfl
theorem sub_def (x y : RodaK K) : x - y = x + -y := rfl
theorem div_def (x y : RodaK K) : x / y = x * y⁻¹ := rfl

/-- Igualdade de representantes coordenada a coordenada. -/
theorem mk_congr {a b c d : K} (h1 : a = c) (h2 : b = d) : mk a b = mk c d := by
  rw [h1, h2]

/-! ## Monoides comutativos e involução -/

theorem roda_add_comm (x y : RodaK K) : x + y = y + x := by
  induction x using ind with | h a b => ?_
  induction y using ind with | h c d => ?_
  simp only [mk_add_mk]
  exact mk_congr (by ring) (by ring)

theorem roda_add_assoc (x y z : RodaK K) : x + y + z = x + (y + z) := by
  induction x using ind with | h a b => ?_
  induction y using ind with | h c d => ?_
  induction z using ind with | h e f => ?_
  simp only [mk_add_mk]
  exact mk_congr (by ring) (by ring)

theorem roda_zero_add (x : RodaK K) : 0 + x = x := by
  induction x using ind with | h a b => ?_
  simp only [zero_def, mk_add_mk]
  exact mk_congr (by ring) (by ring)

theorem roda_mul_comm (x y : RodaK K) : x * y = y * x := by
  induction x using ind with | h a b => ?_
  induction y using ind with | h c d => ?_
  simp only [mk_mul_mk]
  exact mk_congr (by ring) (by ring)

theorem roda_mul_assoc (x y z : RodaK K) : x * y * z = x * (y * z) := by
  induction x using ind with | h a b => ?_
  induction y using ind with | h c d => ?_
  induction z using ind with | h e f => ?_
  simp only [mk_mul_mk]
  exact mk_congr (by ring) (by ring)

theorem roda_one_mul (x : RodaK K) : 1 * x = x := by
  induction x using ind with | h a b => ?_
  simp only [one_def, mk_mul_mk]
  exact mk_congr (by ring) (by ring)

/-! ## Os oito axiomas de roda (Carlström 2004) -/

/-- (W1) `//x = x`. -/
theorem roda_w1 (x : RodaK K) : x⁻¹⁻¹ = x := by
  induction x using ind with | h a b => ?_
  rfl

/-- (W2) `/(xy) = /x · /y`. -/
theorem roda_w2 (x y : RodaK K) : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
  induction x using ind with | h a b => ?_
  induction y using ind with | h c d => ?_
  rfl

/-- (W3) `xz + yz = (x + y)z + 0z`. -/
theorem roda_w3 (x y z : RodaK K) : x * z + y * z = (x + y) * z + 0 * z := by
  induction x using ind with | h a b => ?_
  induction y using ind with | h c d => ?_
  induction z using ind with | h e f => ?_
  simp only [zero_def, mk_add_mk, mk_mul_mk]
  exact mk_congr (by ring) (by ring)

/-- (W4) `(x + yz)/y = x/y + z + 0y`. -/
theorem roda_w4 (x y z : RodaK K) : (x + y * z) / y = x / y + z + 0 * y := by
  induction x using ind with | h a b => ?_
  induction y using ind with | h c d => ?_
  induction z using ind with | h e f => ?_
  simp only [div_def, zero_def, inv_mk, mk_add_mk, mk_mul_mk]
  exact mk_congr (by ring) (by ring)

/-- (W5) `0 · 0 = 0`. -/
theorem roda_w5 : (0 : RodaK K) * 0 = 0 := by
  simp only [zero_def, mk_mul_mk]
  exact mk_congr (by ring) (by ring)

/-- (W6) `(x + 0y)z = xz + 0y`. -/
theorem roda_w6 (x y z : RodaK K) : (x + 0 * y) * z = x * z + 0 * y := by
  induction x using ind with | h a b => ?_
  induction y using ind with | h c d => ?_
  induction z using ind with | h e f => ?_
  simp only [zero_def, mk_add_mk, mk_mul_mk]
  exact mk_congr (by ring) (by ring)

/-- (W7) `/(x + 0y) = /x + 0y`. -/
theorem roda_w7 (x y : RodaK K) : (x + 0 * y)⁻¹ = x⁻¹ + 0 * y := by
  induction x using ind with | h a b => ?_
  induction y using ind with | h c d => ?_
  simp only [zero_def, inv_mk, mk_add_mk, mk_mul_mk]
  exact mk_congr (by ring) (by ring)

/-- (W8) `0/0 + x = 0/0`. -/
theorem roda_w8 (x : RodaK K) : 0 / 0 + x = 0 / 0 := by
  induction x using ind with | h a b => ?_
  simp only [div_def, zero_def, inv_mk, mk_add_mk, mk_mul_mk]
  exact mk_congr (by ring) (by ring)

/-- A lei que substitui `x/x = 1`: `x/x = 1 + 0·x/x`. -/
theorem div_self_roda (x : RodaK K) : x / x = 1 + 0 * x / x := by
  induction x using ind with | h a b => ?_
  simp only [div_def, zero_def, one_def, inv_mk, mk_add_mk, mk_mul_mk]
  exact mk_congr (by ring) (by ring)

/-! ## Os pontos notáveis -/

/-- `/0 = ∞`. -/
theorem inv_zero_eq_infty : (0 : RodaK K)⁻¹ = infty := rfl

/-- `0/0 = ⊥`. -/
theorem zero_div_zero : (0 : RodaK K) / 0 = bot := by
  simp only [div_def, zero_def, inv_mk, mk_mul_mk, bot]
  exact mk_congr (by ring) (by ring)

/-- `∞/∞ = ⊥` (a forma `∞/∞` coincide com `0/0`). -/
theorem infty_div_infty : (infty : RodaK K) / infty = bot := by
  simp only [div_def, infty, inv_mk, mk_mul_mk, bot]
  exact mk_congr (by ring) (by ring)

/-- `0 · ∞ = ⊥`. -/
theorem zero_mul_infty : (0 : RodaK K) * infty = bot := by
  simp only [zero_def, infty, mk_mul_mk, bot]
  exact mk_congr (by ring) (by ring)

/-- `∞ + ∞ = ⊥`. -/
theorem infty_add_infty : (infty : RodaK K) + infty = bot := by
  simp only [infty, mk_add_mk, bot]
  exact mk_congr (by ring) (by ring)

/-- `∞ − ∞ = ⊥`. -/
theorem infty_sub_infty : (infty : RodaK K) - infty = bot := by
  simp only [sub_def, infty, neg_mk, mk_add_mk, bot]
  exact mk_congr (by ring) (by ring)

/-- `⊥` é absorvente para `+`. -/
theorem bot_add (x : RodaK K) : bot + x = bot := by
  induction x using ind with | h a b => ?_
  simp only [bot, mk_add_mk]
  exact mk_congr (by ring) (by ring)

/-- `⊥` é absorvente para `·`. -/
theorem bot_mul (x : RodaK K) : bot * x = bot := by
  induction x using ind with | h a b => ?_
  simp only [bot, mk_mul_mk]
  exact mk_congr (by ring) (by ring)

/-- `/⊥ = ⊥`. -/
theorem inv_bot : (bot : RodaK K)⁻¹ = bot := rfl

/-! ## Distinção dos quatro pontos (o "Teorema 8" do acervo: `I ≠ 0`, `I ≠ 1`, `I ≠ ∞`) -/

theorem bot_ne_zero : (bot : RodaK K) ≠ 0 := by
  intro h
  obtain ⟨u, hu, -, h2⟩ := mk_eq_mk_iff.mp h
  simp at h2

theorem bot_ne_one : (bot : RodaK K) ≠ 1 := by
  intro h
  obtain ⟨u, hu, h1, -⟩ := mk_eq_mk_iff.mp h
  simp at h1

theorem bot_ne_infty : (bot : RodaK K) ≠ infty := by
  intro h
  obtain ⟨u, hu, h1, -⟩ := mk_eq_mk_iff.mp h
  simp at h1

theorem roda_zero_ne_one : (0 : RodaK K) ≠ 1 := by
  intro h
  obtain ⟨u, hu, h1, -⟩ := mk_eq_mk_iff.mp h
  simp at h1

theorem zero_ne_infty : (0 : RodaK K) ≠ infty := by
  intro h
  obtain ⟨u, hu, h1, -⟩ := mk_eq_mk_iff.mp h
  simp at h1

theorem one_ne_infty : (1 : RodaK K) ≠ infty := by
  intro h
  obtain ⟨u, hu, h1, h2⟩ := mk_eq_mk_iff.mp h
  simp only [mul_one] at h1 h2
  exact one_ne_zero (h1.trans h2.symm)

/-! ## O corpo dentro da roda -/

/-- Mergulho `a ↦ [a:1]`. -/
def ι (a : K) : RodaK K := mk a 1

theorem ι_injective : Function.Injective (ι : K → RodaK K) := by
  intro a c h
  obtain ⟨u, hu, h1, h2⟩ := mk_eq_mk_iff.mp h
  simp only [mul_one] at h2
  rw [h1, ← h2, one_mul]

theorem ι_zero : ι (0 : K) = 0 := rfl
theorem ι_one : ι (1 : K) = 1 := rfl

theorem ι_add (a c : K) : ι (a + c) = ι a + ι c := by
  simp only [ι, mk_add_mk]
  exact mk_congr (by ring) (by ring)

theorem ι_mul (a c : K) : ι (a * c) = ι a * ι c := by
  simp only [ι, mk_mul_mk]
  exact mk_congr (by ring) (by ring)

/-- Em `K`, a divisão por `a ≠ 0` volta a ser a usual: `a · /a = 1`. -/
theorem ι_mul_inv {a : K} (ha : a ≠ 0) : ι a * (ι a)⁻¹ = 1 := by
  simp only [ι, inv_mk, mk_mul_mk, one_def]
  exact mk_eq_mk_iff.mpr ⟨a⁻¹, inv_ne_zero ha, by field_simp, by field_simp⟩

/-! ## O preço da divisão total -/

/-- `0 · x = 0` **não** vale em toda a roda (falha em `x = ∞`). -/
theorem zero_mul_falha : ¬ ∀ x : RodaK K, 0 * x = 0 := by
  intro h
  exact bot_ne_zero ((zero_mul_infty).symm.trans (h infty))

/-- `x − x = 0` **não** vale em toda a roda (falha em `x = ∞`). -/
theorem sub_self_falha : ¬ ∀ x : RodaK K, x - x = 0 := by
  intro h
  exact bot_ne_zero ((infty_sub_infty).symm.trans (h infty))

end ATK.Roda

#print axioms ATK.Roda.rel_equiv
#print axioms ATK.Roda.mk_eq_mk_iff
#print axioms ATK.Roda.roda_add_comm
#print axioms ATK.Roda.roda_add_assoc
#print axioms ATK.Roda.roda_zero_add
#print axioms ATK.Roda.roda_mul_comm
#print axioms ATK.Roda.roda_mul_assoc
#print axioms ATK.Roda.roda_one_mul
#print axioms ATK.Roda.roda_w1
#print axioms ATK.Roda.roda_w2
#print axioms ATK.Roda.roda_w3
#print axioms ATK.Roda.roda_w4
#print axioms ATK.Roda.roda_w5
#print axioms ATK.Roda.roda_w6
#print axioms ATK.Roda.roda_w7
#print axioms ATK.Roda.roda_w8
#print axioms ATK.Roda.div_self_roda
#print axioms ATK.Roda.inv_zero_eq_infty
#print axioms ATK.Roda.zero_div_zero
#print axioms ATK.Roda.infty_div_infty
#print axioms ATK.Roda.zero_mul_infty
#print axioms ATK.Roda.infty_add_infty
#print axioms ATK.Roda.infty_sub_infty
#print axioms ATK.Roda.bot_add
#print axioms ATK.Roda.bot_mul
#print axioms ATK.Roda.inv_bot
#print axioms ATK.Roda.bot_ne_zero
#print axioms ATK.Roda.bot_ne_one
#print axioms ATK.Roda.bot_ne_infty
#print axioms ATK.Roda.roda_zero_ne_one
#print axioms ATK.Roda.zero_ne_infty
#print axioms ATK.Roda.one_ne_infty
#print axioms ATK.Roda.ι_injective
#print axioms ATK.Roda.ι_zero
#print axioms ATK.Roda.ι_one
#print axioms ATK.Roda.ι_add
#print axioms ATK.Roda.ι_mul
#print axioms ATK.Roda.ι_mul_inv
#print axioms ATK.Roda.zero_mul_falha
#print axioms ATK.Roda.sub_self_falha
