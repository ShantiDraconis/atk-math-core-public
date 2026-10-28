/-
ATK.Base (B1b, parcial) — Nagell–Lutz para a 2-torsão e `|E[2]| ≤ 4`.

Continua `ATK.BaseCurvasTorsao`.  O teorema de Nagell–Lutz diz que um ponto de torsão de uma curva
`y² = x³ + ax² + bx + c` com coeficientes inteiros tem coordenadas inteiras.  Aqui ele é provado
no caso dos pontos de ordem 2 (o caso geral exige a filtração `p`-ádica de `E(ℚ_p)` e fica como
próxima camada), junto com a cota do tamanho de `E[2]`:

* **`raiz_racional_inteira`**: uma raiz racional de `x³ + ax² + bx + c` (`a, b, c ∈ ℤ`) é um
  inteiro que divide `c` (teorema da raiz racional para cúbicas mônicas);
* **`nagellLutz_dois`**: todo ponto racional de ordem 2 de uma curva inteira tem `y = 0` e
  `x ∈ ℤ` com `x ∣ c` — há só finitos candidatos, lidos dos divisores de `c`;
* **`card_raizes_le`** e **`card_dois_torsao_le`**: sobre qualquer corpo de característica ≠ 2,
  há no máximo 3 pontos afins de ordem 2, logo `|E[2]| ≤ 4`.
-/
import ATK.BaseCurvasTorsao
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Data.Rat.Lemmas

namespace ATK.BaseNagellLutzDois

open WeierstrassCurve WeierstrassCurve.Affine Polynomial ATK.BaseCurvasTorsao

/-! ### Teorema da raiz racional para cúbicas mônicas -/

/-- **Raiz racional de cúbica mônica inteira é inteira e divide o termo constante.** -/
theorem raiz_racional_inteira {a b c : ℤ} {x : ℚ}
    (hx : x ^ 3 + a * x ^ 2 + b * x + c = 0) : ∃ n : ℤ, x = n ∧ n ∣ c := by
  have hxd : x * (x.den : ℚ) = x.num := Rat.mul_den_eq_num x
  have key : (x.num : ℚ) ^ 3 + a * x.num ^ 2 * x.den + b * x.num * x.den ^ 2 + c * x.den ^ 3 = 0 := by
    rw [← hxd]
    linear_combination ((x.den : ℚ) ^ 3) * hx
  have key' : x.num ^ 3 + a * x.num ^ 2 * x.den + b * x.num * x.den ^ 2 + c * x.den ^ 3 = 0 := by
    exact_mod_cast key
  have hd : (x.den : ℤ) ∣ x.num ^ 3 :=
    ⟨-(a * x.num ^ 2 + b * x.num * x.den + c * x.den ^ 2), by linear_combination key'⟩
  have hcop : IsCoprime (x.den : ℤ) (x.num ^ 3) := by
    have h : IsCoprime x.num (x.den : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd] using x.reduced
    exact h.symm.pow_right
  have hu : IsUnit (x.den : ℤ) := hcop.isUnit_of_dvd' dvd_rfl hd
  have h1 : x.den = 1 := by
    rcases Int.isUnit_iff.mp hu with h | h
    · exact_mod_cast h
    · have := x.den_pos
      omega
  have hxn : x = x.num := (Rat.coe_int_num_of_den_eq_one h1).symm
  refine ⟨x.num, hxn, ?_⟩
  have hint : x.num ^ 3 + a * x.num ^ 2 + b * x.num + c = 0 := by
    have : (x.num : ℚ) ^ 3 + a * x.num ^ 2 + b * x.num + c = 0 := by rw [← hxn]; exact hx
    exact_mod_cast this
  exact ⟨-(x.num ^ 2 + a * x.num + b), by linear_combination hint⟩

/-! ### Nagell–Lutz para pontos de ordem 2 -/

/-- **Nagell–Lutz (ordem 2).** Numa curva `y² = x³ + a₂x² + a₄x + a₆` sobre ℚ com `a₂, a₄, a₆`
inteiros, todo ponto afim de ordem 2 tem `y = 0` e `x` inteiro dividindo `a₆`. -/
theorem nagellLutz_dois {W : WeierstrassCurve.Affine ℚ} (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {a₂ a₄ a₆ : ℤ} (h₂ : W.a₂ = a₂) (h₄ : W.a₄ = a₄) (h₆ : W.a₆ = a₆) {x y : ℚ}
    (h : W.Nonsingular x y) (hP : Point.some x y h + Point.some x y h = 0) :
    y = 0 ∧ ∃ n : ℤ, x = n ∧ n ∣ a₆ := by
  have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
  refine ⟨(ordem_dois_iff ha₁ ha₃ h2 h).mp hP, ?_⟩
  have hr := (ordem_dois_iff_raiz ha₁ ha₃ h2 h).mp hP
  rw [h₂, h₄, h₆] at hr
  exact raiz_racional_inteira hr

/-! ### `|E[2]| ≤ 4` -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- Uma cúbica mônica tem no máximo 3 raízes. -/
theorem card_raizes_le (a b c : F) (s : Finset F)
    (hs : ∀ x ∈ s, x ^ 3 + a * x ^ 2 + b * x + c = 0) : s.card ≤ 3 := by
  set p : F[X] := C 1 * X ^ 3 + C a * X ^ 2 + C b * X + C c with hp
  have hdeg : p.natDegree = 3 := natDegree_cubic one_ne_zero
  have hp0 : p ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hdeg
    exact absurd hdeg (by norm_num)
  have hsub : s ⊆ p.roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hp0, IsRoot.def]
    simp only [hp, eval_add, eval_mul, eval_C, eval_pow, eval_X, one_mul]
    exact hs x hx
  calc s.card ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := card_roots' p
    _ = 3 := hdeg

variable {W : WeierstrassCurve.Affine F}

/-- Coordenada `x` de um ponto (valor qualquer em `O`). -/
def coordX : W.Point → F
  | .zero => 0
  | .some x _ _ => x

/-- **`|E[2]| ≤ 4`**: com `a₁ = a₃ = 0` e `2 ≠ 0`, qualquer conjunto finito de pontos com
`P + P = 0` tem no máximo 4 elementos. -/
theorem card_dois_torsao_le (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (h2 : (2 : F) ≠ 0)
    (s : Finset W.Point) (hs : ∀ P ∈ s, P + P = 0) : s.card ≤ 4 := by
  classical
  have hinj : Set.InjOn coordX (s.erase 0 : Set W.Point) := by
    intro P hP Q hQ hPQ
    simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hP hQ
    cases P with
    | zero => exact absurd rfl hP.2
    | some x y h =>
      cases Q with
      | zero => exact absurd rfl hQ.2
      | some x' y' h' =>
        have hy : y = 0 := (ordem_dois_iff ha₁ ha₃ h2 h).mp (hs _ hP.1)
        have hy' : y' = 0 := (ordem_dois_iff ha₁ ha₃ h2 h').mp (hs _ hQ.1)
        have hx : x = x' := hPQ
        subst hx hy hy'
        rfl
  have himg : ((s.erase 0).image coordX).card ≤ 3 := by
    apply card_raizes_le W.a₂ W.a₄ W.a₆
    intro x hx
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx
    cases P with
    | zero => exact absurd rfl (Finset.mem_erase.mp hP).1
    | some x y h =>
      exact (ordem_dois_iff_raiz ha₁ ha₃ h2 h).mp (hs _ (Finset.mem_erase.mp hP).2)
  have hcard : (s.erase 0).card ≤ 3 := by
    rw [← Finset.card_image_of_injOn hinj]
    exact himg
  have := Finset.pred_card_le_card_erase (s := s) (a := 0)
  omega

end ATK.BaseNagellLutzDois

#print axioms ATK.BaseNagellLutzDois.raiz_racional_inteira
#print axioms ATK.BaseNagellLutzDois.nagellLutz_dois
#print axioms ATK.BaseNagellLutzDois.card_raizes_le
#print axioms ATK.BaseNagellLutzDois.card_dois_torsao_le
