import ATK.BaseGaussCurva32
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-!
# ATK — Ponte P1 provada: a equação funcional modular de `y² = x³ − x`

`AtaqueBSD.bsd_posto_curva32` reduz BSD (posto) para `E : y² = x³ − x` a duas pontes: P1, a forma
modular com sinal `+1` — `g(1/x) = x² g(x)` para `g(x) = Σ aₙ e^{−c n x}`, `c = 2π/√32` — e P2
(`|aₙ| ≤ n`, provada em `PonteFatoresCurva32`). Este arquivo prova P1 sem hipóteses.

Pelo caráter de Hecke (`BaseGaussCurva32.coef_gauss`), `aₙ = Σ_{α primário, N α = n} α`, logo

  `g(x) = Σ_{(a, b) primário} a · e^{−c (a² + b²) x}`  (`(a, b)` primário: `b` par, `a + b ≡ 1 (4)`).

A soma dupla fatora de dois modos:
* em `(a, b) = (±(4m + 1), 2j)`: `g(x) = A(x) T(x)`, `A = Σ (4m+1) e^{−c(4m+1)²x}`,
  `T = Σ (−1)^j e^{−4cj²x}` (`fat_ab`);
* em `(u, w) = (a + b, a − b)`, ambos `≡ 1 (4)`: `g(x) = U(x) V(x)`,
  `U = Σ (4m+1) e^{−(c/2)(4m+1)²x}`, `V = Σ e^{−(c/2)(4m+1)²x}` (`fat_uw`).

`U` e `V` são os núcleos de Hurwitz `oddKernel` e `evenKernel` em `1/4`; as equações funcionais
da Mathlib os levam a `sinKernel` e `cosKernel`, que são `2A` e `T` (`sin_quarto`, `cos_quarto`).
Daí `g(1/x) = U(1/x) V(1/x) = x² A(x) T(x) = x² g(x)` (`equacao_funcional`).

Consequências:
* `ponteModular_curva32`: P1;
* `bsd_posto_curva32_incondicional`: toda continuação analítica `G` de `L(E, s)` tem `G(1) ≠ 0` e
  ordem `0 =` posto de Mordell–Weil;
* `lseriesSummable_curva32`, `existe_continuacao`: `L(E, s)` converge absolutamente em `Re s > 3/2`
  (`|aₙ| ≤ r₂(n) √n` e a soma de Eisenstein da Mathlib) e a função inteira `c^s Λ(s)/Γ(s)` a
  continua — a continuação **existe**;
* **`bsdConjecture_E32`: a conjectura de BSD (parte do posto) vale para `y² = x³ − x`** no
  enunciado por curva de `L4Base` (fiel ao do Clay por `L4Base.clayBSD_iff`), sem pontes.
-/

local notation "ℤ[i]" => GaussianInt

open Real HurwitzZeta

namespace ATK.PonteModularCurva32

open ATK.PonteCoefCurva32 ATK.PonteFatoresCurva32 ATK.BaseGaussPrimario ATK.BaseGaussCurva32
  ATK.AtaqueBSD ATK.LigacaoBSD ATK.LigacaoBSDTestes

/-! ## Formas reais dos núcleos de seno e cosseno -/

theorem hasSum_sin (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ => (n : ℝ) * Real.sin (2 * π * a * n) * rexp (-π * n ^ 2 * t))
      (sinKernel a t) := by
  have h := Complex.hasSum_re (hasSum_int_sinKernel a ht)
  rw [Complex.ofReal_re] at h
  refine h.congr_fun fun n => ?_
  have e : Complex.exp (2 * π * Complex.I * a * n) =
      Complex.exp (((2 * π * a * n : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring_nf
  rw [e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im,
    Complex.add_re, Complex.add_im]
  ring

theorem hasSum_cos (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ => Real.cos (2 * π * a * n) * rexp (-π * n ^ 2 * t)) (cosKernel a t) := by
  have h := Complex.hasSum_re (hasSum_int_cosKernel a ht)
  rw [Complex.ofReal_re] at h
  refine h.congr_fun fun n => ?_
  have e : Complex.exp (2 * π * Complex.I * a * n) =
      Complex.exp (((2 * π * a * n : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring_nf
  rw [e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im]
  ring

theorem cos_pi_int (j : ℤ) : Real.cos (π * j) = if j % 2 = 0 then 1 else -1 := by
  have hj : j = j % 2 + 2 * (j / 2) := by omega
  split_ifs with h
  · rw [hj, h]
    have : π * ((0 : ℤ) + 2 * (j / 2) : ℤ) = 0 + ((j / 2 : ℤ) : ℝ) * (2 * π) := by push_cast; ring
    rw [this, Real.cos_add_int_mul_two_pi, Real.cos_zero]
  · have h1 : j % 2 = 1 := by omega
    rw [hj, h1]
    have : π * ((1 : ℤ) + 2 * (j / 2) : ℤ) = π + ((j / 2 : ℤ) : ℝ) * (2 * π) := by push_cast; ring
    rw [this, Real.cos_add_int_mul_two_pi, Real.cos_pi]

/-- **`sinKernel(1/4)(t) = 8 · oddKernel(1/4)(16 t)`**. -/
theorem sin_quarto {t : ℝ} (ht : 0 < t) :
    sinKernel ((1 / 4 : ℝ) : UnitAddCircle) t =
      8 * oddKernel ((1 / 4 : ℝ) : UnitAddCircle) (16 * t) := by
  have h := hasSum_sin (1 / 4) ht
  set term := fun n : ℤ => (n : ℝ) * Real.sin (2 * π * (1 / 4) * n) * rexp (-π * n ^ 2 * t)
    with hterm
  let g : ℤ ⊕ ℤ → ℤ := Sum.elim (fun m => 4 * m + 1) (fun m => -(4 * m + 1))
  have hg : Function.Injective g := by
    rintro (m | m) (m' | m') hmm <;> simp only [g, Sum.elim_inl, Sum.elim_inr] at hmm
    · rw [show m = m' by omega]
    · omega
    · omega
    · rw [show m = m' by omega]
  have hsin : ∀ m : ℤ, Real.sin (2 * π * (1 / 4) * ((4 * m + 1 : ℤ) : ℝ)) = 1 := by
    intro m
    have : 2 * π * (1 / 4) * ((4 * m + 1 : ℤ) : ℝ) = π / 2 + (m : ℝ) * (2 * π) := by
      push_cast; ring
    rw [this, Real.sin_add_int_mul_two_pi, Real.sin_pi_div_two]
  have hvan : ∀ n ∉ Set.range g, term n = 0 := by
    intro n hn
    have hev : n % 2 = 0 := by
      by_contra hodd
      apply hn
      rcases (by omega : n % 4 = 1 ∨ n % 4 = 3) with h1 | h3
      · exact ⟨Sum.inl ((n - 1) / 4), by simp only [g, Sum.elim_inl]; omega⟩
      · exact ⟨Sum.inr ((-n - 1) / 4), by simp only [g, Sum.elim_inr]; omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    simp only [hterm]
    have : 2 * π * (1 / 4) * ((2 * k : ℤ) : ℝ) = (k : ℝ) * π := by push_cast; ring
    rw [this, Real.sin_int_mul_pi, mul_zero, zero_mul]
  have hodd := hasSum_int_oddKernel (1 / 4) (by positivity : 0 < 16 * t)
  have h1 : HasSum ((term ∘ g) ∘ Sum.inl) (4 * oddKernel ((1 / 4 : ℝ) : UnitAddCircle) (16 * t)) := by
    refine (hodd.mul_left 4).congr_fun fun m => ?_
    simp only [Function.comp, g, Sum.elim_inl, hterm]
    rw [hsin m]
    push_cast
    ring_nf
  have h2 : HasSum ((term ∘ g) ∘ Sum.inr) (4 * oddKernel ((1 / 4 : ℝ) : UnitAddCircle) (16 * t)) := by
    refine (hodd.mul_left 4).congr_fun fun m => ?_
    simp only [Function.comp, g, Sum.elim_inr, hterm]
    have hs : Real.sin (2 * π * (1 / 4) * ((-(4 * m + 1) : ℤ) : ℝ)) = -1 := by
      rw [Int.cast_neg, mul_neg, Real.sin_neg, hsin m]
    rw [hs]
    push_cast
    ring_nf
  have hall := (hg.hasSum_iff hvan).mp (HasSum.sum h1 h2)
  rw [h.unique hall]
  ring

/-- **`cosKernel(1/4)(t) = cosKernel(1/2)(4 t)`**. -/
theorem cos_quarto {t : ℝ} (ht : 0 < t) :
    cosKernel ((1 / 4 : ℝ) : UnitAddCircle) t = cosKernel ((1 / 2 : ℝ) : UnitAddCircle) (4 * t) := by
  have h := hasSum_cos (1 / 4) ht
  set term := fun n : ℤ => Real.cos (2 * π * (1 / 4) * n) * rexp (-π * n ^ 2 * t) with hterm
  let g : ℤ → ℤ := fun j => 2 * j
  have hg : Function.Injective g := fun j j' h => by simp only [g] at h; omega
  have hvan : ∀ n ∉ Set.range g, term n = 0 := by
    intro n hn
    have hodd : n % 2 = 1 := by
      by_contra hev
      exact hn ⟨n / 2, by simp only [g]; omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    simp only [hterm]
    have : 2 * π * (1 / 4) * ((2 * k + 1 : ℤ) : ℝ) = (k : ℝ) * π + π / 2 := by push_cast; ring
    rw [this, Real.cos_add_pi_div_two, Real.sin_int_mul_pi, neg_zero, zero_mul]
  have hc := hasSum_cos (1 / 2) (by positivity : 0 < 4 * t)
  have h1 : HasSum (term ∘ g) (cosKernel ((1 / 2 : ℝ) : UnitAddCircle) (4 * t)) := by
    refine hc.congr_fun fun j => ?_
    simp only [Function.comp, g, hterm]
    push_cast
    ring_nf
  rw [h.unique ((hg.hasSum_iff hvan).mp h1)]

/-! ## Constantes -/

/-- `c = 2π/√32`. -/
noncomputable abbrev c : ℝ := c32

/-- `K = 8c/π = 2√2`. -/
noncomputable def K : ℝ := 8 * c / π

theorem c_pos : 0 < c := c32_pos

theorem K_pos : 0 < K := div_pos (by linarith [c_pos]) pi_pos

theorem c_sq : c ^ 2 = π ^ 2 / 8 := by
  show c32 ^ 2 = _
  rw [c32, div_pow, Real.sq_sqrt (by norm_num)]
  ring

theorem K_sq : K ^ 2 = 8 := by
  have := pi_pos
  rw [K, div_pow, mul_pow, c_sq, div_eq_iff (by positivity)]
  ring

theorem pi_div_K : π / K = c := by
  have hc := c_pos
  rw [K, div_div_eq_mul_div, div_eq_iff (by positivity)]
  linear_combination (-8 : ℝ) * c_sq

/-! ## As quatro séries -/

/-- `A(x) = Σ (4m+1) e^{−c(4m+1)²x} = 4 · oddKernel(1/4)(2Kx)`. -/
noncomputable def At (x : ℝ) (m : ℤ) : ℝ := (4 * m + 1) * rexp (-(c * (4 * m + 1) ^ 2 * x))
noncomputable def A (x : ℝ) : ℝ := 4 * oddKernel ((1 / 4 : ℝ) : UnitAddCircle) (2 * K * x)

/-- `T(x) = Σ (−1)^j e^{−4cj²x} = cosKernel(1/2)(4x/K)`. -/
noncomputable def Tt (x : ℝ) (j : ℤ) : ℝ := Real.cos (π * j) * rexp (-(4 * c * j ^ 2 * x))
noncomputable def T (x : ℝ) : ℝ := cosKernel ((1 / 2 : ℝ) : UnitAddCircle) (4 * x / K)

/-- `U(y) = Σ (4m+1) e^{−(c/2)(4m+1)²y} = 4 · oddKernel(1/4)(Ky)`. -/
noncomputable def Ut (y : ℝ) (m : ℤ) : ℝ := (4 * m + 1) * rexp (-(c / 2 * (4 * m + 1) ^ 2 * y))
noncomputable def U (y : ℝ) : ℝ := 4 * oddKernel ((1 / 4 : ℝ) : UnitAddCircle) (K * y)

/-- `V(y) = Σ e^{−(c/2)(4m+1)²y} = evenKernel(1/4)(Ky)`. -/
noncomputable def Vt (y : ℝ) (m : ℤ) : ℝ := rexp (-(c / 2 * (4 * m + 1) ^ 2 * y))
noncomputable def V (y : ℝ) : ℝ := evenKernel ((1 / 4 : ℝ) : UnitAddCircle) (K * y)

theorem hasSum_A {x : ℝ} (hx : 0 < x) : HasSum (At x) (A x) := by
  have h := hasSum_int_oddKernel (1 / 4) (by have := K_pos; positivity : 0 < 2 * K * x)
  refine (h.mul_left 4).congr_fun fun m => ?_
  simp only [At]
  have hK : π * (2 * K * x) = 16 * c * x := by
    rw [K]; field_simp; ring
  rw [← mul_assoc]
  congr 1
  · ring
  · congr 1
    linear_combination (((m : ℝ) + 1 / 4) ^ 2) * hK

theorem hasSum_U {y : ℝ} (hy : 0 < y) : HasSum (Ut y) (U y) := by
  have h := hasSum_int_oddKernel (1 / 4) (by have := K_pos; positivity : 0 < K * y)
  refine (h.mul_left 4).congr_fun fun m => ?_
  simp only [Ut]
  have hK : π * (K * y) = 8 * c * y := by
    rw [K]; field_simp
  rw [← mul_assoc]
  congr 1
  · ring
  · congr 1
    linear_combination (((m : ℝ) + 1 / 4) ^ 2) * hK

theorem hasSum_V {y : ℝ} (hy : 0 < y) : HasSum (Vt y) (V y) := by
  have h := hasSum_int_evenKernel (1 / 4) (by have := K_pos; positivity : 0 < K * y)
  refine h.congr_fun fun m => ?_
  simp only [Vt]
  have hK : π * (K * y) = 8 * c * y := by
    rw [K]; field_simp
  congr 1
  linear_combination (((m : ℝ) + 1 / 4) ^ 2) * hK

theorem hasSum_T {x : ℝ} (hx : 0 < x) : HasSum (Tt x) (T x) := by
  have h := hasSum_cos (1 / 2) (by have := K_pos; positivity : 0 < 4 * x / K)
  refine h.congr_fun fun j => ?_
  simp only [Tt]
  have hK : π * (4 * x / K) = 4 * c * x := by
    rw [mul_div_assoc', mul_comm π, mul_div_assoc, pi_div_K]; ring
  congr 1
  · congr 1; ring
  · congr 1
    linear_combination ((j : ℝ) ^ 2) * hK

theorem sumAbs {f : ℤ → ℝ} {a : ℝ} (h : HasSum f a) : Summable fun n => ‖f n‖ := by
  simp only [Real.norm_eq_abs]
  exact summable_abs_iff.mpr h.summable

/-! ## A soma dupla e suas duas fatorações -/

/-- Termo `[(a, b) primário] · a · e^{−c(a² + b²)x}`. -/
noncomputable def f (x : ℝ) (p : ℤ × ℤ) : ℝ :=
  if Prim (⟨p.1, p.2⟩ : ℤ[i]) then (p.1 : ℝ) * rexp (-(c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * x))
  else 0

theorem prim_coord (a b : ℤ) : Prim (⟨a, b⟩ : ℤ[i]) ↔ b % 2 = 0 ∧ (a + b) % 4 = 1 := Iff.rfl

/-- **Fatoração em `(a, b) = (±(4m+1), 2j)`**: `g = A · T`. -/
theorem fat_ab {x : ℝ} (hx : 0 < x) : HasSum (f x) (A x * T x) := by
  let φ : ℤ × ℤ → ℤ × ℤ := fun q => (if q.2 % 2 = 0 then 4 * q.1 + 1 else -(4 * q.1 + 1), 2 * q.2)
  have hφ : Function.Injective φ := by
    rintro ⟨m, j⟩ ⟨m', j'⟩ h
    simp only [φ, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have hj : j = j' := by omega
    subst hj
    split_ifs at h1 <;> (ext <;> simp only <;> omega)
  have hvan : ∀ p ∉ Set.range φ, f x p = 0 := by
    rintro ⟨a, b⟩ hp
    simp only [f]
    rw [if_neg]
    rw [prim_coord]
    rintro ⟨hb, hab⟩
    apply hp
    by_cases hj : (b / 2) % 2 = 0
    · refine ⟨((a - 1) / 4, b / 2), ?_⟩
      simp only [φ, if_pos hj, Prod.mk.injEq]
      omega
    · refine ⟨((-a - 1) / 4, b / 2), ?_⟩
      simp only [φ, if_neg hj, Prod.mk.injEq]
      omega
  have hprod : HasSum (fun q : ℤ × ℤ => At x q.1 * Tt x q.2) (A x * T x) :=
    (hasSum_A hx).mul (hasSum_T hx)
      (summable_mul_of_summable_norm (sumAbs (hasSum_A hx)) (sumAbs (hasSum_T hx)))
  refine (hφ.hasSum_iff hvan).mp (hprod.congr_fun fun q => ?_)
  obtain ⟨m, j⟩ := q
  have key : At x m * Tt x j = (if j % 2 = 0 then 1 else -1) *
      ((4 * (m : ℝ) + 1) * rexp (-(c * ((4 * (m : ℝ) + 1) ^ 2 + (2 * (j : ℝ)) ^ 2) * x))) := by
    simp only [At, Tt, cos_pi_int]
    have he : rexp (-(c * ((4 * (m : ℝ) + 1) ^ 2 + (2 * (j : ℝ)) ^ 2) * x)) =
        rexp (-(c * (4 * (m : ℝ) + 1) ^ 2 * x)) * rexp (-(4 * c * (j : ℝ) ^ 2 * x)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [he]
    ring
  simp only [Function.comp]
  rw [key]
  simp only [φ, f]
  rw [if_pos]
  · split_ifs with hj
    · push_cast
      ring
    · push_cast
      rw [neg_sq]
      ring
  · rw [prim_coord]
    split_ifs with hj <;> omega

/-- **Fatoração em `(u, w) = (a + b, a − b)`**: `g = U · V`. -/
theorem fat_uw {y : ℝ} (hy : 0 < y) : HasSum (f y) (U y * V y) := by
  let ψ : ℤ × ℤ → ℤ × ℤ := fun q => (2 * q.1 + 2 * q.2 + 1, 2 * q.1 - 2 * q.2)
  have hψ : Function.Injective ψ := by
    rintro ⟨m, n⟩ ⟨m', n'⟩ h
    simp only [ψ, Prod.mk.injEq] at h
    ext <;> simp only <;> omega
  have hvan : ∀ p ∉ Set.range ψ, f y p = 0 := by
    rintro ⟨a, b⟩ hp
    simp only [f]
    rw [if_neg]
    rw [prim_coord]
    rintro ⟨hb, hab⟩
    apply hp
    refine ⟨((a + b - 1) / 4, (a - b - 1) / 4), ?_⟩
    simp only [ψ, Prod.mk.injEq]
    omega
  have s1 := summable_mul_of_summable_norm (sumAbs (hasSum_U hy)) (sumAbs (hasSum_V hy))
  have s2 := summable_mul_of_summable_norm (sumAbs (hasSum_V hy)) (sumAbs (hasSum_U hy))
  have h1 := (hasSum_U hy).mul (hasSum_V hy) s1
  have h2 := (hasSum_V hy).mul (hasSum_U hy) s2
  have hsum := (h1.add h2).mul_left (1 / 2)
  have he : 1 / 2 * (U y * V y + V y * U y) = U y * V y := by ring
  rw [he] at hsum
  refine (hψ.hasSum_iff hvan).mp (hsum.congr_fun fun q => ?_)
  obtain ⟨m, n⟩ := q
  simp only [Function.comp, ψ, f, Ut, Vt]
  rw [if_pos (by rw [prim_coord]; omega)]
  push_cast
  have hexp : rexp (-(c / 2 * (4 * (m : ℝ) + 1) ^ 2 * y)) * rexp (-(c / 2 * (4 * (n : ℝ) + 1) ^ 2 * y))
      = rexp (-(c * ((2 * (m : ℝ) + 2 * n + 1) ^ 2 + (2 * (m : ℝ) - 2 * n) ^ 2) * y)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc (2 * (m : ℝ) + 2 * n + 1) * rexp (-(c * ((2 * (m : ℝ) + 2 * n + 1) ^ 2 +
        (2 * (m : ℝ) - 2 * n) ^ 2) * y))
      = 1 / 2 * ((4 * m + 1) + (4 * n + 1)) * (rexp (-(c / 2 * (4 * (m : ℝ) + 1) ^ 2 * y)) *
          rexp (-(c / 2 * (4 * (n : ℝ) + 1) ^ 2 * y))) := by rw [hexp]; ring
    _ = _ := by ring

/-! ## A equação funcional -/

theorem rpow_par {X : ℝ} (hX : 0 < X) : X ^ (3 / 2 : ℝ) * X ^ (1 / 2 : ℝ) = X ^ 2 := by
  rw [← Real.rpow_add hX]
  norm_num

/-- **`U(1/x) V(1/x) = x² A(x) T(x)`** (equações funcionais de Hurwitz). -/
theorem equacao_UV {x : ℝ} (hx : 0 < x) : U (1 / x) * V (1 / x) = x ^ 2 * (A x * T x) := by
  have hK := K_pos
  have hX : 0 < K / x := div_pos hK hx
  have h1 : U (1 / x) = 4 * (1 / (K / x) ^ (3 / 2 : ℝ) *
      sinKernel ((1 / 4 : ℝ) : UnitAddCircle) (x / K)) := by
    rw [U, oddKernel_functional_equation, show K * (1 / x) = K / x by ring, one_div_div]
  have h2 : V (1 / x) = 1 / (K / x) ^ (1 / 2 : ℝ) * cosKernel ((1 / 4 : ℝ) : UnitAddCircle) (x / K) := by
    rw [V, evenKernel_functional_equation, show K * (1 / x) = K / x by ring, one_div_div]
  have h3 : sinKernel ((1 / 4 : ℝ) : UnitAddCircle) (x / K) = 2 * A x := by
    rw [sin_quarto (div_pos hx hK), A]
    have : 16 * (x / K) = 2 * K * x := by
      field_simp
      nlinarith [K_sq]
    rw [this]; ring
  have h4 : cosKernel ((1 / 4 : ℝ) : UnitAddCircle) (x / K) = T x := by
    rw [cos_quarto (div_pos hx hK), T]
    congr 1; ring
  rw [h1, h2, h3, h4]
  have hp : (K / x) ^ (3 / 2 : ℝ) * (K / x) ^ (1 / 2 : ℝ) = (K / x) ^ 2 := rpow_par hX
  have e : 4 * (1 / (K / x) ^ (3 / 2 : ℝ) * (2 * A x)) * (1 / (K / x) ^ (1 / 2 : ℝ) * T x) =
      8 * (A x * T x) * ((K / x) ^ (3 / 2 : ℝ) * (K / x) ^ (1 / 2 : ℝ))⁻¹ := by
    rw [mul_inv]; ring
  rw [e, hp, div_pow, K_sq, inv_div]
  ring

/-! ## Os coeficientes e a soma dupla -/

/-- A caixa `[−n, n]²` filtrada por `a² + b² = n`. -/
def caixa (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter fun p => p.1 ^ 2 + p.2 ^ 2 = n

theorem re_sum {ι : Type*} (s : Finset ι) (g : ι → ℤ[i]) :
    (∑ i ∈ s, g i).re = ∑ i ∈ s, (g i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Zsqrtd.re_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Zsqrtd.re_add, ih]

/-- `aₙ = Σ_{(a, b) primário, a² + b² = n} a`. -/
theorem coef_caixa (n : ℕ) :
    (ATK.CongruentCurve.E.LFunction n : ℤ) =
      ∑ p ∈ (caixa n).filter (fun p => Prim (⟨p.1, p.2⟩ : ℤ[i])), p.1 := by
  have h := congrArg Zsqrtd.re (coef_gauss n)
  rw [Zsqrtd.re_intCast] at h
  rw [h, somaPrim, re_sum]
  refine Finset.sum_nbij' (fun α => (α.re, α.im)) (fun p => ⟨p.1, p.2⟩) ?_ ?_ ?_ ?_ ?_
  · intro α hα
    rw [mem_primN] at hα
    rw [Finset.mem_filter, caixa, Finset.mem_filter]
    have hn := hα.2
    rw [norma] at hn
    refine ⟨⟨?_, by simpa using hn⟩, hα.1⟩
    have h1 := Int.le_self_sq α.re
    have h2 := Int.le_self_sq (-α.re)
    have h3 := Int.le_self_sq α.im
    have h4 := Int.le_self_sq (-α.im)
    simp only [neg_sq] at h2 h4
    simp only [Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg α.re, sq_nonneg α.im]
  · intro p hp
    rw [Finset.mem_filter, caixa, Finset.mem_filter] at hp
    rw [mem_primN]
    refine ⟨hp.2, ?_⟩
    rw [norma]
    exact hp.1.2
  · intro α _; rfl
  · intro p _; rfl
  · intro α _; rfl

theorem fibra (n : ℕ) :
    (fun p : ℤ × ℤ => (p.1 ^ 2 + p.2 ^ 2).toNat) ⁻¹' {n} = ↑(caixa n) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_singleton_iff, caixa, Finset.coe_filter,
    Finset.mem_product, Finset.mem_Icc, Set.mem_setOf_eq]
  have h0 : 0 ≤ p.1 ^ 2 + p.2 ^ 2 := by positivity
  constructor
  · intro h
    have hn : p.1 ^ 2 + p.2 ^ 2 = n := by rw [← h, Int.toNat_of_nonneg h0]
    have h1 := Int.le_self_sq p.1
    have h2 := Int.le_self_sq (-p.1)
    have h3 := Int.le_self_sq p.2
    have h4 := Int.le_self_sq (-p.2)
    simp only [neg_sq] at h2 h4
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, hn⟩ <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]
  · rintro ⟨-, h⟩
    rw [h, Int.toNat_natCast]

/-- **A série `Σ aₙ e^{−cnx}` é a soma dupla**: `HasSum (aₙ e^{−cnx}) (A x · T x)`. -/
theorem hasSum_coef {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => (ATK.CongruentCurve.E.LFunction n : ℝ) * rexp (-(c * n * x)))
      (A x * T x) := by
  have h := (fat_ab hx).tsum_fiberwise (fun p : ℤ × ℤ => (p.1 ^ 2 + p.2 ^ 2).toNat)
  refine h.congr_fun fun n => ?_
  rw [tsum_congr_set_coe (f x) (fibra n), Finset.tsum_subtype', coef_caixa, Finset.sum_filter]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [caixa, Finset.mem_filter] at hp
  simp only [f]
  split_ifs with hpr
  · rw [show ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) = (n : ℝ) by exact_mod_cast hp.2]
  · simp

/-- `g(x) = A(x) T(x)` como série complexa da `AtaqueBSD`. -/
theorem teta_eq {x : ℝ} (hx : 0 < x) : teta ATK.CongruentCurve.E c x = ((A x * T x : ℝ) : ℂ) := by
  have h := Complex.hasSum_ofReal.mpr (hasSum_coef hx)
  refine (h.congr_fun fun n => ?_).tsum_eq
  simp only [coef]
  push_cast
  rfl

/-- **Equação funcional**: `g(1/x) = x² g(x)`. -/
theorem equacao_funcional {x : ℝ} (hx : 0 < x) :
    A (1 / x) * T (1 / x) = x ^ 2 * (A x * T x) := by
  have hx' : 0 < 1 / x := by positivity
  rw [(fat_ab hx').unique (fat_uw hx')]
  exact equacao_UV hx

/-- **Ponte P1 provada**: `y² = x³ − x` é modular com sinal `+1`. -/
theorem ponteModular_curva32 : PonteModular ATK.CongruentCurve.E c32 1 := by
  intro x hx
  rw [show c32 = c from rfl, teta_eq (by positivity : 0 < 1 / x), teta_eq hx,
    equacao_funcional hx]
  push_cast
  ring

/-- **BSD (posto) para `y² = x³ − x`, incondicional**: toda continuação analítica `G` de
`L(E, s)` tem `G(1) ≠ 0` e ordem de anulação `0 =` posto de Mordell–Weil. -/
theorem bsd_posto_curva32_incondicional {G : ℂ → ℂ} (hG : Continuacao ATK.CongruentCurve.E G) :
    G 1 ≠ 0 ∧ analyticOrderAt G 1 = postoMW ATK.CongruentCurve.E :=
  bsd_posto_curva32_modP1 ponteModular_curva32 hG

/-! ## Existência da continuação: convergência em `Re s > 3/2` -/

/-- `Σ_{p ∈ ℤ²} N(p)^{−t}` converge para `t > 1` (soma de Eisenstein da Mathlib). -/
theorem summable_rede {t : ℝ} (ht : 1 < t) :
    Summable fun p : ℤ × ℤ => ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ (-t) := by
  have hE := EisensteinSeries.summable_one_div_norm_rpow (k := 2 * t) (by linarith)
  have hE' : Summable fun p : ℤ × ℤ => ‖(finTwoArrowEquiv ℤ).symm p‖ ^ (-(2 * t)) :=
    (finTwoArrowEquiv ℤ).symm.summable_iff.mpr hE
  refine hE'.of_nonneg_of_le (fun p => by positivity) fun p => ?_
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp only [finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Nat.cast_max, Nat.cast_natAbs, Int.cast_abs]
  obtain ⟨a, b⟩ := p
  simp only
  by_cases h0 : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h0
    have ht0 : (-t : ℝ) ≠ 0 := by linarith
    have ht2 : (-(2 * t) : ℝ) ≠ 0 := by linarith
    simp [Real.zero_rpow ht0, Real.zero_rpow ht2]
  · have hM : 0 < max |(a : ℝ)| |(b : ℝ)| := by
      rcases not_and_or.mp h0 with ha | hb
      · exact lt_max_of_lt_left (abs_pos.mpr (by exact_mod_cast ha))
      · exact lt_max_of_lt_right (abs_pos.mpr (by exact_mod_cast hb))
    have hle : (max |(a : ℝ)| |(b : ℝ)|) ^ 2 ≤ (a : ℝ) ^ 2 + (b : ℝ) ^ 2 := by
      rcases le_total |(a : ℝ)| |(b : ℝ)| with h | h
      · rw [max_eq_right h, sq_abs]; nlinarith [sq_nonneg (a : ℝ)]
      · rw [max_eq_left h, sq_abs]; nlinarith [sq_nonneg (b : ℝ)]
    rw [show -(2 * t) = 2 * (-t) by ring, Real.rpow_mul hM.le, Real.rpow_two]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)

/-- `|aₙ| ≤ Σ_{a² + b² = n} √n`. -/
theorem cota_caixa (n : ℕ) :
    |(ATK.CongruentCurve.E.LFunction n : ℝ)| ≤ ∑ p ∈ caixa n, Real.sqrt n := by
  rw [coef_caixa]
  push_cast
  calc |∑ p ∈ (caixa n).filter (fun p => Prim (⟨p.1, p.2⟩ : ℤ[i])), (p.1 : ℝ)|
      ≤ ∑ p ∈ (caixa n).filter (fun p => Prim (⟨p.1, p.2⟩ : ℤ[i])), |(p.1 : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ (caixa n).filter (fun p => Prim (⟨p.1, p.2⟩ : ℤ[i])), Real.sqrt n := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [Finset.mem_filter, caixa, Finset.mem_filter] at hp
        apply Real.abs_le_sqrt
        have : ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) = (n : ℝ) := by exact_mod_cast hp.1.2
        nlinarith [sq_nonneg (p.2 : ℝ)]
    _ ≤ ∑ p ∈ caixa n, Real.sqrt n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun _ _ _ => Real.sqrt_nonneg _

/-- **`L(E, s)` converge absolutamente em `Re s > 3/2`.** -/
theorem lseriesSummable_curva32 {s : ℂ} (hs : 3 / 2 < s.re) :
    LSeriesSummable (coef ATK.CongruentCurve.E) s := by
  have hsum := summable_rede (t := s.re - 1 / 2) (by linarith)
  have hfib := hsum.hasSum.tsum_fiberwise (fun p : ℤ × ℤ => (p.1 ^ 2 + p.2 ^ 2).toNat)
  have hG : Summable fun n : ℕ =>
      ∑ p ∈ caixa n, ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ (-(s.re - 1 / 2)) := by
    refine hfib.summable.congr fun n => ?_
    rw [tsum_congr_set_coe (fun p : ℤ × ℤ => ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ (-(s.re - 1 / 2)))
      (fibra n)]
    exact Finset.tsum_subtype' (caixa n)
      (fun p : ℤ × ℤ => ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ (-(s.re - 1 / 2)))
  refine Summable.of_norm_bounded hG fun n => ?_
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · exact Finset.sum_nonneg fun p _ => by positivity
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hc : ∀ p ∈ caixa n, ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) ^ (-(s.re - 1 / 2)) =
        Real.sqrt n / (n : ℝ) ^ s.re := by
      intro p hp
      rw [caixa, Finset.mem_filter] at hp
      have : ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) = (n : ℝ) := by exact_mod_cast hp.2
      rw [this, Real.sqrt_eq_rpow, ← Real.rpow_sub hnpos]
      congr 1; ring
    rw [Finset.sum_congr rfl hc, ← Finset.sum_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    simp only [coef, Complex.norm_intCast]
    exact cota_caixa n

theorem abscissa_curva32 :
    LSeries.abscissaOfAbsConv (coef ATK.CongruentCurve.E) ≤ ((3 / 2 : ℝ) : EReal) :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    lseriesSummable_curva32 (by simpa using hy)

/-- A continuação inteira de `L(E, s)` construída pela equação funcional. -/
noncomputable def Lcurva32 : ℂ → ℂ :=
  Lc c32_pos cotaCoef_curva32 one_ne_zero ponteModular_curva32

/-- **Existência**: `Lcurva32` é a continuação analítica de `L(E, s)` (coincide com a série em
`Re s > 3/2`). -/
theorem existe_continuacao : Continuacao ATK.CongruentCurve.E Lcurva32 := by
  have hd : Differentiable ℂ Lcurva32 := differentiable_Lc _ _ _ _
  refine ⟨hd, fun s hs => ?_⟩
  have hU : IsPreconnected {s : ℂ | 3 / 2 < s.re} := (convex_halfSpace_re_gt (3 / 2)).isPreconnected
  have hLa : AnalyticOnNhd ℂ Lcurva32 {s : ℂ | 3 / 2 < s.re} := fun z _ => hd.analyticAt z
  have hSa : AnalyticOnNhd ℂ (LSeries (coef ATK.CongruentCurve.E)) {s : ℂ | 3 / 2 < s.re} := by
    intro z hz
    refine LSeries_analyticOnNhd _ z ?_
    exact lt_of_le_of_lt abscissa_curva32 (by exact_mod_cast hz)
  have hopen : IsOpen {s : ℂ | 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h3 : (3 : ℂ) ∈ {s : ℂ | 2 < s.re} := by norm_num
  have heq := hLa.eqOn_of_preconnected_of_eventuallyEq hSa hU (z₀ := 3) (by norm_num) (by
    filter_upwards [hopen.mem_nhds h3] with z hz
    exact Lc_eq _ _ _ _ hz)
  exact heq hs

/-- **BSD (posto) para `y² = x³ − x`, forma completa**: `L(E, s)` tem continuação analítica
inteira, única, que não se anula em `s = 1`; a ordem de anulação `0` é o posto de Mordell–Weil. -/
theorem bsd_posto_curva32_completo :
    ∃ G : ℂ → ℂ, Continuacao ATK.CongruentCurve.E G ∧
      (∀ G' : ℂ → ℂ, Continuacao ATK.CongruentCurve.E G' → G' = G) ∧
      G 1 ≠ 0 ∧ analyticOrderAt G 1 = postoMW ATK.CongruentCurve.E :=
  ⟨Lcurva32, existe_continuacao, fun _ hG' => continuacao_unica hG' existe_continuacao,
    bsd_posto_curva32_incondicional existe_continuacao⟩

/-- **A conjectura de Birch e Swinnerton-Dyer (parte do posto) vale para `y² = x³ − x`**, no
enunciado por curva de `L4Base` (fiel ao do Clay: `L4Base.clayBSD_iff`). -/
theorem bsdConjecture_E32 : ATK.L4Base.BSDConjecture ATK.L4Base.E32 :=
  ⟨ATK.L4Base.LFunctionContinued.ofContinuacao existe_continuacao,
    (bsd_posto_curva32_incondicional existe_continuacao).2⟩

end ATK.PonteModularCurva32

#print axioms ATK.PonteModularCurva32.hasSum_sin
#print axioms ATK.PonteModularCurva32.hasSum_cos
#print axioms ATK.PonteModularCurva32.cos_pi_int
#print axioms ATK.PonteModularCurva32.sin_quarto
#print axioms ATK.PonteModularCurva32.cos_quarto
#print axioms ATK.PonteModularCurva32.c_pos
#print axioms ATK.PonteModularCurva32.K_pos
#print axioms ATK.PonteModularCurva32.c_sq
#print axioms ATK.PonteModularCurva32.K_sq
#print axioms ATK.PonteModularCurva32.pi_div_K
#print axioms ATK.PonteModularCurva32.hasSum_A
#print axioms ATK.PonteModularCurva32.hasSum_U
#print axioms ATK.PonteModularCurva32.hasSum_V
#print axioms ATK.PonteModularCurva32.hasSum_T
#print axioms ATK.PonteModularCurva32.sumAbs
#print axioms ATK.PonteModularCurva32.prim_coord
#print axioms ATK.PonteModularCurva32.fat_ab
#print axioms ATK.PonteModularCurva32.fat_uw
#print axioms ATK.PonteModularCurva32.rpow_par
#print axioms ATK.PonteModularCurva32.equacao_UV
#print axioms ATK.PonteModularCurva32.re_sum
#print axioms ATK.PonteModularCurva32.coef_caixa
#print axioms ATK.PonteModularCurva32.fibra
#print axioms ATK.PonteModularCurva32.hasSum_coef
#print axioms ATK.PonteModularCurva32.teta_eq
#print axioms ATK.PonteModularCurva32.equacao_funcional
#print axioms ATK.PonteModularCurva32.ponteModular_curva32
#print axioms ATK.PonteModularCurva32.bsd_posto_curva32_incondicional
#print axioms ATK.PonteModularCurva32.summable_rede
#print axioms ATK.PonteModularCurva32.cota_caixa
#print axioms ATK.PonteModularCurva32.lseriesSummable_curva32
#print axioms ATK.PonteModularCurva32.abscissa_curva32
#print axioms ATK.PonteModularCurva32.existe_continuacao
#print axioms ATK.PonteModularCurva32.bsd_posto_curva32_completo
#print axioms ATK.PonteModularCurva32.bsdConjecture_E32
