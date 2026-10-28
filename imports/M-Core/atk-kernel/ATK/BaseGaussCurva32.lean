import ATK.PonteFatoresCurva32
import ATK.BaseGaussPrimario

/-!
# ATK — Base: o traço de Frobenius de `y² = x³ − x` é `π + π̄` (Gauss)

Para `p ≡ 1 (mod 4)` existe `π ∈ ℤ[i]` primário com `N π = p` e `a_p = π + π̄ = 2 re π`; para
`p ≡ 3 (mod 4)`, `a_p = 0`. Daí, com `PonteFatoresCurva32` (fatores locais da Mathlib) e
`BaseGaussPrimario` (fatoração única em `ℤ[i]`), os coeficientes de `WeierstrassCurve.LFunction`
para `y² = x³ − x` são os do caráter de Hecke de `ℚ(i)`:
`aₙ = Σ_{α primário, N α = n} α` (`coef_gauss`).

* `oito_dvd`: sobre um corpo com `i² = −1` e `2 ≠ 0`, `8 ∣ #E` — o ponto `(i, 1 − i)` tem ordem 4
  (`2(i, 1 − i) = (0, 0)`) e `(1, 0) ∉ ⟨(i, 1 − i)⟩` tem ordem 2;
* `quadrado_traco`: `a_p² + S(g)² = 4p` (somas de Jacobsthal, `BaseHasseCurva32.soma_AB`);
* `existe_pi`: de `8 ∣ p + 1 − a_p` e `a_p² + S(g)² = 4p`, `π = a_p/2 + (S(g)/2) i` é primário;
* `traco_tres`: `a_p = 0` para `p ≡ 3 (mod 4)`;
* `coef_gauss`: `aₙ = Σ_{α primário, N α = n} α` para todo `n`.
-/

local notation "ℤ[i]" => GaussianInt

namespace ATK.BaseGaussCurva32

open ATK.PonteCoefCurva32 ATK.PonteFatoresCurva32 ATK.BaseGaussPrimario WeierstrassCurve

section Pontos

variable {F : Type*} [Field F] [DecidableEq F]

theorem Δ_ne (h2 : (2 : F) ≠ 0) : (E32 F).Δ ≠ 0 := by
  rw [E32_Δ]
  have : (64 : F) = 2 ^ 6 := by norm_num
  rw [this]
  exact pow_ne_zero _ h2

theorem ns {x y : F} (h2 : (2 : F) ≠ 0) (h : y ^ 2 = x ^ 3 - x) :
    (E32 F).toAffine.Nonsingular x y :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero (Δ_ne h2)).mp ((E32_equation x y).mpr h)

theorem some_inj {x y x' y' : F} {h : (E32 F).toAffine.Nonsingular x y}
    {h' : (E32 F).toAffine.Nonsingular x' y'}
    (he : (Affine.Point.some x y h : (E32 F).toAffine.Point) = Affine.Point.some x' y' h') :
    x = x' ∧ y = y' := by
  cases he
  exact ⟨rfl, rfl⟩

/-- **`8 ∣ #E(F)`** quando `F` contém `i` (`i² = −1`) e `2 ≠ 0`. -/
theorem oito_dvd {i : F} (hi : i ^ 2 = -1) (h2 : (2 : F) ≠ 0) :
    8 ∣ Nat.card (E32 F).toAffine.Point := by
  have hi1 : i ≠ 1 := by
    rintro rfl
    apply h2
    linear_combination hi
  have hden : (1 - i) - (i - 1) ≠ 0 := by
    intro h
    apply hi1
    have : (2 : F) * (1 - i) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' h2
    · linear_combination -h'
  let P : (E32 F).toAffine.Point :=
    .some i (1 - i) (ns h2 (by linear_combination (1 - i) * hi))
  let T : (E32 F).toAffine.Point := .some 0 0 (ns h2 (by ring))
  let Q : (E32 F).toAffine.Point := .some 1 0 (ns h2 (by ring))
  have hPP : P + P = T := by
    have hy : (1 - i) ≠ (E32 F).toAffine.negY i (1 - i) := by
      simp only [Affine.negY, E32]
      intro h
      apply hden
      linear_combination h
    rw [Affine.Point.add_self_of_Y_ne hy]
    have hsl : (E32 F).toAffine.slope i i (1 - i) (1 - i) = -(1 + i) := by
      rw [Affine.slope_of_Y_ne rfl hy]
      simp only [Affine.negY, E32]
      rw [div_eq_iff (by simpa using hden)]
      linear_combination hi
    congr 1
    · rw [hsl]
      simp only [Affine.addX, E32]
      linear_combination hi
    · rw [hsl]
      simp only [Affine.addY, Affine.negAddY, Affine.addX, Affine.negY, E32]
      linear_combination i * hi
  have hTT : T + T = 0 :=
    Affine.Point.add_self_of_Y_eq (by simp [Affine.negY, E32])
  have hQQ : Q + Q = 0 :=
    Affine.Point.add_self_of_Y_eq (by simp [Affine.negY, E32])
  have hT0 : T ≠ 0 := Affine.Point.some_ne_zero _
  have hord : addOrderOf P = 4 := by
    have := addOrderOf_eq_prime_pow (p := 2) (n := 1) (x := P) ?_ ?_
    · simpa using this
    · rw [pow_one, two_nsmul, hPP]; exact hT0
    · rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, add_nsmul, two_nsmul, hPP, hTT]
  have hP4 : (4 : ℤ) • P = 0 := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, natCast_zsmul, ← hord, addOrderOf_nsmul_eq_zero]
  have hQP : Q ≠ P := fun h => hi1 (some_inj h).1.symm
  have hQ : Q ∉ AddSubgroup.zmultiples P := by
    rintro ⟨k, hk⟩
    have hk' : (k % 4) • P = Q := by
      rw [← hk]
      calc (k % 4) • P = (k % 4) • P + (k / 4) • ((4 : ℤ) • P) := by
            rw [hP4, zsmul_zero, add_zero]
        _ = k • P := by
            rw [smul_smul, ← add_zsmul]
            congr 1
            omega
    have h0 : 0 ≤ k % 4 := Int.emod_nonneg _ (by norm_num)
    have h4 : k % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
    generalize k % 4 = r at hk' h0 h4
    interval_cases r
    · rw [zero_zsmul] at hk'
      exact Affine.Point.some_ne_zero _ hk'.symm
    · rw [one_zsmul] at hk'
      exact hQP hk'.symm
    · rw [show (2 : ℤ) = 1 + 1 by norm_num, add_zsmul, one_zsmul, hPP] at hk'
      exact one_ne_zero (some_inj hk').1.symm
    · have h3 : (3 : ℤ) • P = -P := by
        rw [eq_neg_iff_add_eq_zero, ← add_one_zsmul]
        norm_num [hP4]
      rw [h3] at hk'
      have hQn : -Q = Q := neg_eq_of_add_eq_zero_left hQQ
      have : P = Q := by rw [← neg_neg P, hk', hQn]
      exact hQP this.symm
  rw [(AddSubgroup.zmultiples P).card_eq_card_quotient_mul_card_addSubgroup,
    Nat.card_zmultiples, hord]
  have h2q : 2 ∣ Nat.card ((E32 F).toAffine.Point ⧸ AddSubgroup.zmultiples P) := by
    have : addOrderOf (Q : (E32 F).toAffine.Point ⧸ AddSubgroup.zmultiples P) = 2 := by
      apply addOrderOf_eq_prime
      · rw [two_nsmul, ← QuotientAddGroup.mk_add, hQQ]
        rfl
      · rwa [ne_eq, QuotientAddGroup.eq_zero_iff]
    rw [← this]
    exact addOrderOf_dvd_natCard _
  obtain ⟨c, hc⟩ := h2q
  rw [hc]
  exact ⟨c, by ring⟩

end Pontos

/-! ## O traço sobre `𝔽_p` -/

theorem dois_ne (p : ℕ) [Fact p.Prime] (h2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact h2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp this)

/-- `#E(𝔽_p) = p + 1 − a_p`. -/
theorem card_E (p : ℕ) [Fact p.Prime] (h2 : p ≠ 2) :
    (Nat.card (E32 (ZMod p)).toAffine.Point : ℤ) = p + 1 - traco p := by
  rw [card_pontos _ (Δ_ne (dois_ne p h2)),
    Nat.card_congr (Equiv.subtypeEquivRight (α := ZMod p × ZMod p)
      fun xy => E32_equation xy.1 xy.2)]
  push_cast
  rw [card_E32_zmod _ h2]
  ring

/-- **`8 ∣ p + 1 − a_p`** para `p ≡ 1 (mod 4)`. -/
theorem oito_dvd_traco (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    (8 : ℤ) ∣ p + 1 - traco p := by
  have h2 : p ≠ 2 := by omega
  obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
  have hi : r ^ 2 = -1 := by rw [hr]; ring
  rw [← card_E p h2]
  exact_mod_cast oito_dvd hi (dois_ne p h2)

/-- **`a_p² + S(g)² = 4p`** (somas de Jacobsthal). -/
theorem quadrado_traco (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ s : ℤ, traco p ^ 2 + s ^ 2 = 4 * p := by
  have h2 : p ≠ 2 := by omega
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : (1 : ZMod p) = 0 := by linear_combination -hr
    exact one_ne_zero this
  have h1 : quadraticChar (ZMod p) (-1) = 1 :=
    (quadraticChar_one_iff_isSquare (by simp)).mpr ⟨r, hr⟩
  obtain ⟨g, hg⟩ := FiniteField.exists_nonsquare hF
  refine ⟨ATK.BaseHasseCurva32.S g, ?_⟩
  have hAB := ATK.BaseHasseCurva32.soma_AB hF h1 hg
  rw [ZMod.card] at hAB
  have hm1 : (1 : ZMod p) * r ^ 2 = -1 := by rw [one_mul, sq, ← hr]
  have hS : ATK.BaseHasseCurva32.S (-1 : ZMod p) =
      quadraticChar (ZMod p) r * ATK.BaseHasseCurva32.S (1 : ZMod p) := by
    have := ATK.BaseHasseCurva32.S_escala hr0 (1 : ZMod p)
    rwa [hm1] at this
  have htr : traco p = -ATK.BaseHasseCurva32.S (-1 : ZMod p) := by
    rw [traco, ATK.BaseHasseCurva32.S]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    ring
  rw [htr, hS]
  have hsq := quadraticChar_sq_one hr0
  linear_combination hAB + (ATK.BaseHasseCurva32.S (1 : ZMod p)) ^ 2 * hsq

/-- **Gauss**: para `p ≡ 1 (mod 4)` existe `π` primário com `N π = p` e `2 re π = a_p`. -/
theorem existe_pi (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ π : ℤ[i], Prim π ∧ π.norm = p ∧ 2 * π.re = traco p := by
  obtain ⟨s, hs⟩ := quadrado_traco p hp
  have h8 := oito_dvd_traco p hp
  generalize traco p = T at hs h8 ⊢
  have hpz : (p : ℤ) % 4 = 1 := by exact_mod_cast hp
  -- `T = 2t`, `t` ímpar
  obtain ⟨t, rfl⟩ : ∃ t, T = 2 * t := ⟨T / 2, by omega⟩
  have ht : t % 2 = 1 := by omega
  -- `s = 2s'`
  have hs2 : s % 2 = 0 := by
    rcases Int.emod_two_eq_zero_or_one s with h | h
    · exact h
    · obtain ⟨a, rfl⟩ : ∃ a, s = 2 * a + 1 := ⟨s / 2, by omega⟩
      have : 4 * (t ^ 2 + a ^ 2 + a) + 1 = 4 * p := by linear_combination hs
      omega
  obtain ⟨s', rfl⟩ : ∃ s', s = 2 * s' := ⟨s / 2, by omega⟩
  have hn : t ^ 2 + s' ^ 2 = p := by
    have h4 : 4 * (t ^ 2 + s' ^ 2) = 4 * p := by linear_combination hs
    linarith
  obtain ⟨u, rfl⟩ : ∃ u, t = 2 * u + 1 := ⟨t / 2, by omega⟩
  have hs'2 : s' % 2 = 0 := by
    rcases Int.emod_two_eq_zero_or_one s' with h | h
    · exact h
    · obtain ⟨b, rfl⟩ : ∃ b, s' = 2 * b + 1 := ⟨s' / 2, by omega⟩
      have : 4 * (u ^ 2 + u + b ^ 2 + b) + 2 = (p : ℤ) := by linear_combination hn
      omega
  obtain ⟨v, rfl⟩ : ∃ v, s' = 2 * v := ⟨s' / 2, by omega⟩
  have e8 : (p : ℤ) + 1 - 2 * (2 * u + 1) = 4 * (u ^ 2 + v ^ 2) := by
    linear_combination (-1 : ℤ) * hn
  rw [e8] at h8
  have huv : (u ^ 2 + v ^ 2) % 2 = 0 := by omega
  have eu := Int.even_mul_pred_self u
  have ev := Int.even_mul_pred_self v
  rw [Int.even_iff] at eu ev
  have e1 : u ^ 2 + v ^ 2 = (u * (u - 1) + v * (v - 1)) + (u + v) := by ring
  refine ⟨⟨2 * u + 1, 2 * v⟩, ?_, ?_, rfl⟩
  · unfold Prim
    simp only
    omega
  · rw [norma]
    simp only
    linear_combination hn

/-- **`a_p = 0`** para `p ≡ 3 (mod 4)`. -/
theorem traco_tres (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) : traco p = 0 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have h1 : quadraticChar (ZMod p) (-1) = -1 :=
    quadraticChar_neg_one_iff_not_isSquare.mpr (by rw [ZMod.exists_sq_eq_neg_one_iff]; omega)
  rw [traco, ATK.BaseHasseCurva32.traco_zero hF h1, neg_zero]

/-! ## Os coeficientes da Mathlib são os do caráter de Hecke -/

/-- `n ↦ a_n` como função aritmética com valores em `ℤ[i]`. -/
noncomputable def coefG : ArithmeticFunction ℤ[i] :=
  ⟨fun n => ((ATK.CongruentCurve.E.LFunction n : ℤ) : ℤ[i]), by simp⟩

/-- `n ↦ Σ_{α primário, N α = n} α` como função aritmética. -/
def somaG : ArithmeticFunction ℤ[i] := ⟨somaPrim, somaPrim_zero⟩

theorem coefG_mult : coefG.IsMultiplicative := by
  have h := lfun_mult ATK.CongruentCurve.E
  refine ⟨?_, fun {m n} hmn => ?_⟩
  · change ((ATK.CongruentCurve.E.LFunction 1 : ℤ) : ℤ[i]) = 1
    rw [h.map_one]; simp
  · change ((ATK.CongruentCurve.E.LFunction (m * n) : ℤ) : ℤ[i]) =
      ((ATK.CongruentCurve.E.LFunction m : ℤ) : ℤ[i]) * ((ATK.CongruentCurve.E.LFunction n : ℤ) : ℤ[i])
    rw [h.map_mul_of_coprime hmn]; push_cast; rfl

theorem somaG_mult : somaG.IsMultiplicative :=
  ⟨somaPrim_um, fun hmn => somaPrim_mul hmn⟩

/-- **`aₙ = Σ_{α primário, N α = n} α`** para `y² = x³ − x`. -/
theorem coef_gauss (n : ℕ) :
    ((ATK.CongruentCurve.E.LFunction n : ℤ) : ℤ[i]) = somaPrim n := by
  have hF := fatoresPadrao
  have key : coefG = somaG := by
    refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers coefG coefG_mult
      somaG somaG_mult).mpr fun p k hp => ?_
    change ((ATK.CongruentCurve.E.LFunction (p ^ k) : ℤ) : ℤ[i]) = somaPrim (p ^ k)
    by_cases h2 : p = 2
    · subst h2
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp only [pow_zero]
        rw [somaPrim_um, (lfun_mult _).map_one]; simp
      · rw [hF.1 k hk, somaPrim_dois hk]; simp
    · haveI : Fact p.Prime := ⟨hp⟩
      rw [hF.2 p h2 k]
      have hodd : p % 2 = 1 := (hp.eq_one_or_self_of_dvd 2 |>.mt (by omega) |> fun h => by
        rcases Nat.even_or_odd p with ⟨r, hr⟩ | ⟨r, hr⟩
        · exact absurd ⟨r, by omega⟩ h
        · omega)
      rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with h1 | h3
      · obtain ⟨π, hπ, hn, hre⟩ := existe_pi p h1
        rw [somaPrim_decomp hp hπ hn k, hre]
      · rw [somaPrim_tres p h3 k, traco_tres p h3]
  have := congrArg (fun f : ArithmeticFunction ℤ[i] => f n) key
  exact this

end ATK.BaseGaussCurva32

#print axioms ATK.BaseGaussCurva32.Δ_ne
#print axioms ATK.BaseGaussCurva32.ns
#print axioms ATK.BaseGaussCurva32.some_inj
#print axioms ATK.BaseGaussCurva32.oito_dvd
#print axioms ATK.BaseGaussCurva32.dois_ne
#print axioms ATK.BaseGaussCurva32.card_E
#print axioms ATK.BaseGaussCurva32.oito_dvd_traco
#print axioms ATK.BaseGaussCurva32.quadrado_traco
#print axioms ATK.BaseGaussCurva32.existe_pi
#print axioms ATK.BaseGaussCurva32.traco_tres
#print axioms ATK.BaseGaussCurva32.coefG_mult
#print axioms ATK.BaseGaussCurva32.somaG_mult
#print axioms ATK.BaseGaussCurva32.coef_gauss
