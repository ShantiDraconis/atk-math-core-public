import ATK.MordellWeilCorpo
import ATK.SelmerFinito
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-!
# ATK — Mordell–Weil fraco sobre corpos de números (2-torção racional completa)

Para um corpo de números `K` e `E : y² = (x − e₁)(x − e₂)(x − e₃)` com `eᵢ ∈ K` distintos, este
arquivo prova que **`E(K)/2E(K)` é finito** (`fraco_numero`).

* `par_x_menos_e`: para uma valuação `w` com `w(eᵢ) ≤ 1` e `w(eᵢ − eⱼ) = 1`, `w(x − e)` é um
  quadrado em todo ponto `(x, y)` com `x ≠ e` (ultrametricidade: se `w(x) > 1`, `w(x − eᵢ) = w(x)`
  e `w(y)² = w(x)³`; se `w(x) ≤ 1`, no máximo um `w(x − eᵢ)` é `< 1`);
* `ruins`: o conjunto finito `S` dos primos onde algum `eᵢ` não é inteiro ou algum `eᵢ − eⱼ` não é
  unidade (`HeightOneSpectrum.Support.finite`, Mathlib);
* `phiE_mem`: `φ_e(P) ∈ K⟮S, 2⟯`;
* `finito_phi`: a imagem de `φ` está em `K⟮S, 2⟯²`, finito por `ATK.SelmerFinito.selmer_finito`;
* **`fraco_numero`**: `2E(K)` tem índice finito em `E(K)`.
-/

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField WithZero

namespace ATK.MordellWeilNumero

open ATK.MordellWeilCorpo

/-! ## Paridade das valuações -/

section Paridade

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation K Γ₀)

/-- Boa redução em `w` para as raízes `e, e', e''`: inteiras e com diferenças unidades. -/
structure Boa (e e' e'' : K) : Prop where
  le₁ : w e ≤ 1
  le₂ : w e' ≤ 1
  le₃ : w e'' ≤ 1
  u₁ : w (e - e') = 1
  u₂ : w (e - e'') = 1
  u₃ : w (e' - e'') = 1

variable {w}

/-- **Paridade**: `w(x − e)` é um quadrado. -/
theorem par_x_menos_e {e e' e'' x y : K} (hb : Boa w e e' e'')
    (heq : y ^ 2 = (x - e) * (x - e') * (x - e'')) (hx : x ≠ e) :
    ∃ c : Γ₀, w (x - e) = c ^ 2 := by
  by_cases hy : y = 0
  · rw [hy] at heq
    have h0 : (x - e) * (x - e') * (x - e'') = 0 := by rw [← heq]; ring
    rcases mul_eq_zero.mp h0 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd (sub_eq_zero.mp h) hx
      · refine ⟨1, ?_⟩
        rw [sub_eq_zero.mp h, Valuation.map_sub_swap, hb.u₁, one_pow]
    · refine ⟨1, ?_⟩
      rw [sub_eq_zero.mp h, Valuation.map_sub_swap, hb.u₂, one_pow]
  have hprod : w y ^ 2 = w (x - e) * w (x - e') * w (x - e'') := by
    rw [← map_pow, heq, map_mul, map_mul]
  by_cases hxv : 1 < w x
  · have k : ∀ {a : K}, w a ≤ 1 → w (x - a) = w x := fun ha =>
      Valuation.map_sub_eq_of_lt_left w (lt_of_le_of_lt ha hxv)
    rw [k hb.le₁, k hb.le₂, k hb.le₃] at hprod
    have hx0 : w x ≠ 0 := ne_of_gt (lt_trans zero_lt_one hxv)
    refine ⟨w y / w x, ?_⟩
    rw [k hb.le₁, div_pow, eq_div_iff (pow_ne_zero 2 hx0), hprod, sq]
    ac_rfl
  · push_neg at hxv
    have k : ∀ {a : K}, w a ≤ 1 → w (x - a) ≤ 1 := fun ha => Valuation.map_sub_le w hxv ha
    by_cases hlt : w (x - e) < 1
    · have h' : w (x - e') = 1 := by
        refine le_antisymm (k hb.le₂) (not_lt.mp fun h' => ?_)
        have hlt' : w (e' - e) < 1 := by
          have := Valuation.map_sub w (x - e) (x - e')
          rw [show x - e - (x - e') = e' - e by ring] at this
          exact lt_of_le_of_lt this (max_lt hlt h')
        rw [Valuation.map_sub_swap, hb.u₁] at hlt'
        exact lt_irrefl _ hlt'
      have h'' : w (x - e'') = 1 := by
        refine le_antisymm (k hb.le₃) (not_lt.mp fun h' => ?_)
        have hlt' : w (e'' - e) < 1 := by
          have := Valuation.map_sub w (x - e) (x - e'')
          rw [show x - e - (x - e'') = e'' - e by ring] at this
          exact lt_of_le_of_lt this (max_lt hlt h')
        rw [Valuation.map_sub_swap, hb.u₂] at hlt'
        exact lt_irrefl _ hlt'
      refine ⟨w y, ?_⟩
      rw [hprod, h', h'', mul_one, mul_one]
    · exact ⟨1, by rw [one_pow]; exact le_antisymm (k hb.le₁) (not_lt.mp hlt)⟩

end Paridade

/-! ## O grupo de Selmer contém a imagem de `φ` -/

section Numero

variable {K : Type*} [Field K] [NumberField K]

/-- Uma valuação `v`-ádica que é um quadrado em `ℤᵐ⁰` é par. -/
theorem dvd_de_quadrado (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) {c : ℤᵐ⁰}
    (hc : v.valuation K (x : K) = c ^ 2) :
    (2 : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, ← valuationOfNeZero_eq] at hc
    exact WithZero.coe_ne_zero hc
  obtain ⟨m, rfl⟩ := WithZero.ne_zero_iff_exists.mp hc0
  rw [← valuationOfNeZero_eq, ← WithZero.coe_pow, WithZero.coe_inj] at hc
  rw [hc, toAdd_pow, nsmul_eq_mul]
  exact ⟨Multiplicative.toAdd m, by push_cast; ring⟩

variable (R : Raizes K)

/-- **Os primos ruins**: onde algum `eᵢ` não é inteiro ou algum `eᵢ − eⱼ` não é unidade. -/
def ruins : Set (HeightOneSpectrum (𝓞 K)) :=
  ⋃ a ∈ ({R.e₁, R.e₂, R.e₃, (R.e₁ - R.e₂)⁻¹, (R.e₁ - R.e₃)⁻¹, (R.e₂ - R.e₃)⁻¹} : Set K),
    HeightOneSpectrum.Support (𝓞 K) a

theorem ruins_finito : (ruins R).Finite :=
  Set.Finite.biUnion (Set.toFinite _) fun a _ => HeightOneSpectrum.Support.finite (𝓞 K) a

variable {R}

theorem le_um_de_fora {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ ruins R) {a : K}
    (ha : a ∈ ({R.e₁, R.e₂, R.e₃, (R.e₁ - R.e₂)⁻¹, (R.e₁ - R.e₃)⁻¹, (R.e₂ - R.e₃)⁻¹} : Set K)) :
    v.valuation K a ≤ 1 := by
  by_contra h
  exact hv (Set.mem_biUnion ha (not_le.mp h))

theorem unidade_de_fora {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ ruins R) {a b : K} (hab : a ≠ b)
    (ha : a ∈ ({R.e₁, R.e₂, R.e₃, (R.e₁ - R.e₂)⁻¹, (R.e₁ - R.e₃)⁻¹, (R.e₂ - R.e₃)⁻¹} : Set K))
    (hb : b ∈ ({R.e₁, R.e₂, R.e₃, (R.e₁ - R.e₂)⁻¹, (R.e₁ - R.e₃)⁻¹, (R.e₂ - R.e₃)⁻¹} : Set K))
    (hi : (a - b)⁻¹ ∈
      ({R.e₁, R.e₂, R.e₃, (R.e₁ - R.e₂)⁻¹, (R.e₁ - R.e₃)⁻¹, (R.e₂ - R.e₃)⁻¹} : Set K)) :
    v.valuation K (a - b) = 1 := by
  have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
  refine le_antisymm (Valuation.map_sub_le _ (le_um_de_fora hv ha) (le_um_de_fora hv hb)) ?_
  have h := le_um_de_fora hv hi
  rw [← not_lt]
  intro hlt
  have := (Valuation.one_lt_val_iff (v.valuation K) (inv_ne_zero hd)).mpr (by rwa [inv_inv])
  exact absurd h (not_le.mpr this)

/-- **Boa redução fora de `S`** para as ordens `(e₁, e₂, e₃)` e `(e₂, e₁, e₃)`. -/
theorem boa₁ {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ ruins R) :
    Boa (v.valuation K) R.e₁ R.e₂ R.e₃ :=
  ⟨le_um_de_fora hv (by simp), le_um_de_fora hv (by simp), le_um_de_fora hv (by simp),
    unidade_de_fora hv R.h₁₂ (by simp) (by simp) (by simp),
    unidade_de_fora hv R.h₁₃ (by simp) (by simp) (by simp),
    unidade_de_fora hv R.h₂₃ (by simp) (by simp) (by simp)⟩

theorem boa₂ {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ ruins R) :
    Boa (v.valuation K) R.e₂ R.e₁ R.e₃ := by
  have h := boa₁ hv
  exact ⟨h.le₂, h.le₁, h.le₃, by rw [Valuation.map_sub_swap]; exact h.u₁, h.u₃, h.u₂⟩

set_option quotPrecheck false in
local notation K "/ˣ" n => Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range

variable [DecidableEq K]

/-- **`φ_e(P)` está no grupo de Selmer `K⟮S, 2⟯`.** -/
theorem phiE_mem {e e' e'' : K} (hr : Raiz R e e' e'')
    (hb : ∀ v ∉ ruins R, Boa (v.valuation K) e e' e'') (P : Pt R) :
    ((phiE e e' e'' P : F2 K) : K /ˣ 2) ∈ @selmerGroup (𝓞 K) _ _ K _ _ _ (ruins R) 2 := by
  have hd := delta_ne_zero hr P
  have hφ : phiE e e' e'' P = mk2 (Units.mk0 _ hd) := by rw [phiE, cls_of_ne hd]
  rw [hφ]
  show (QuotientGroup.mk (Units.mk0 _ hd) : K /ˣ 2) ∈ _
  rw [ATK.SelmerFinito.mem_selmer_iff]
  intro v hv
  have hbv := hb v hv
  suffices hq : ∃ c : ℤᵐ⁰, v.valuation K (delta e e' e'' P) = c ^ 2 by
    obtain ⟨c, hc⟩ := hq
    exact dvd_de_quadrado v (Units.mk0 _ hd) (c := c) (by rw [Units.val_mk0]; exact hc)
  cases P with
  | zero => exact ⟨1, by simp [delta]⟩
  | some x y h =>
    by_cases hx : x = e
    · subst hx
      refine ⟨1, ?_⟩
      rw [delta_some_eq, dd, map_mul, hbv.u₁, hbv.u₂]
      simp
    · have heq := (equacao_iff R x y).mp h.1
      rw [hr.fat] at heq
      obtain ⟨c, hc⟩ := par_x_menos_e hbv heq hx
      exact ⟨c, by rw [delta_some_ne h hx, hc]⟩

variable [NeZero (2 : K)]

variable (R) in
/-- **A imagem de `φ` é finita**: está em `K⟮S, 2⟯²`. -/
theorem finito_phi : (Set.range (phi R)).Finite := by
  have : Finite (@selmerGroup (𝓞 K) _ _ K _ _ _ (ruins R) 2) :=
    ATK.SelmerFinito.selmer_finito K (ruins_finito R) two_pos
  have hfin : (Set.range fun p : (@selmerGroup (𝓞 K) _ _ K _ _ _ (ruins R) 2) ×
      (@selmerGroup (𝓞 K) _ _ K _ _ _ (ruins R) 2) =>
        (Additive.ofMul (((p.1 : K /ˣ 2) : F2 K), ((p.2 : K /ˣ 2) : F2 K)) :
          Additive (F2 K × F2 K))).Finite := Set.finite_range _
  refine hfin.subset ?_
  rintro _ ⟨P, rfl⟩
  exact ⟨(⟨_, phiE_mem raiz₁ (fun v hv => boa₁ hv) P⟩, ⟨_, phiE_mem raiz₂ (fun v hv => boa₂ hv) P⟩),
    rfl⟩

variable (R) in
/-- **Mordell–Weil fraco sobre um corpo de números** (2-torção completa): `E(K)/2E(K)` é finito. -/
theorem fraco_numero : (nsmulAddMonoidHom (α := Pt R) 2).range.FiniteIndex :=
  fraco_de_finito (finito_phi R)

end Numero

end ATK.MordellWeilNumero

#print axioms ATK.MordellWeilNumero.par_x_menos_e
#print axioms ATK.MordellWeilNumero.dvd_de_quadrado
#print axioms ATK.MordellWeilNumero.ruins_finito
#print axioms ATK.MordellWeilNumero.le_um_de_fora
#print axioms ATK.MordellWeilNumero.unidade_de_fora
#print axioms ATK.MordellWeilNumero.boa₁
#print axioms ATK.MordellWeilNumero.boa₂
#print axioms ATK.MordellWeilNumero.phiE_mem
#print axioms ATK.MordellWeilNumero.finito_phi
#print axioms ATK.MordellWeilNumero.fraco_numero
