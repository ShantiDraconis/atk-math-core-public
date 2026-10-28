import ATK.MordellWeilDois

/-!
# ATK — Posto de Mordell–Weil `≥ 2` por 2-descida completa

Para as curvas `E : y² = (x − e₁)(x − e₂)(x − e₃)` de `ATK.MordellWeilDois`, este arquivo mostra
como a imagem do homomorfismo de descida `φ : E(ℚ) → (ℚˣ/ℚˣ²)²` dá **cotas inferiores** para o
posto (o lado algébrico da ligação L4 / produtor O6, fora de qualquer hipótese):

1. `E(ℚ)[2] = {O, T₁, T₂, T₃}` (`dois_torcao`);
2. se `|φ(E[2])| = 4`, toda a torção cai em `φ(E[2])` (`phi_torsao_mem`): `E(ℚ)_tors` é finito
   (Mathlib, `finite_torsion`) e `|φ(T)| ≤ |T/2T| = |T[2]| ≤ 4` (`card_quot_dois`);
3. **critério de independência** (`independentes`): se `φ(P₁)`, `φ(P₂)` e `φ(P₁) + φ(P₂)` estão fora
   de `φ(E[2])`, então `mP₁ + nP₂` de torção força `m = n = 0` (indução em `|m| + |n|`, dividindo
   por 2 quando `m, n` são pares);
4. logo `postoMW E ≥ 2` (`posto_ge_dois`).

**Exemplo certificado**: `y² = x(x + 30)(x + 2)` tem posto `≥ 2` (`posto_R30`), com `(−20, 60)` e
`(−16, 56)` independentes, e `E(ℚ)` é infinito (`infinito_R30`). As classes usadas são as da primeira
coordenada `[x]`: `1, 15, −30, −2` para a 2-torção e `−5, −1, 5` para `P₁, P₂, P₁ + P₂`.

Isto **não** fecha o produtor O6 (a conjectura BSD para curvas de posto `≥ 2` exige a ordem de
anulação analítica, inacessível aqui); é progresso certificado do lado algébrico.
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace ATK.PostoDois

open ATK.MordellWeilDois

variable {R : Raizes}

/-! ## Fatos gerais -/

/-- Em `ℚˣ/ℚˣ²` todo elemento tem ordem ≤ 2. -/
theorem q2_mul_self (a : Q2) : a * a = 1 := by
  induction a using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact ⟨u, by simp [sq]⟩

theorem add_self_q (x : Additive (Q2 × Q2)) : x + x = 0 := by
  change Additive.ofMul (x.toMul * x.toMul) = Additive.ofMul 1
  congr 1
  ext <;> simp [q2_mul_self]

/-- `m • x` só depende da paridade de `m` em `(ℚˣ/ℚˣ²)²`. -/
theorem zsmul_q (m : ℤ) (x : Additive (Q2 × Q2)) : m • x = (m % 2) • x := by
  have h2 : (2 * (m / 2)) • x = 0 := by
    rw [mul_comm, mul_zsmul, two_zsmul, add_self_q, zsmul_zero]
  conv_lhs => rw [← Int.mul_ediv_add_emod m 2]
  rw [add_zsmul, h2, zero_add]

/-- `φ(2Q) = 0`. -/
theorem phi_dobro (Q : Pt R) : phi R (Q + Q) = 0 := by
  rw [map_add]; exact add_self_q _

/-- Para um grupo abeliano finito, `|A/2A| = |A[2]|`. -/
theorem card_quot_dois {A : Type*} [AddCommGroup A] [Finite A] :
    Nat.card (A ⧸ (nsmulAddMonoidHom (α := A) 2).range) =
      Nat.card (nsmulAddMonoidHom (α := A) 2).ker := by
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (nsmulAddMonoidHom (α := A) 2).range
  have h2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (nsmulAddMonoidHom (α := A) 2).ker
  have h3 := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange
    (nsmulAddMonoidHom (α := A) 2)).toEquiv
  rw [h3] at h2
  have hpos : 0 < Nat.card (nsmulAddMonoidHom (α := A) 2).range := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans (h2.trans (mul_comm _ _)))


/-! ## Os pontos de 2-torção -/

variable (R) in
/-- `(e₁, 0)`. -/
noncomputable def T₁ : Pt R := .some (R.e₁ : ℚ) 0 (nonsingular_raiz raiz₁)
variable (R) in
/-- `(e₂, 0)`. -/
noncomputable def T₂ : Pt R := .some (R.e₂ : ℚ) 0 (nonsingular_raiz raiz₂)
variable (R) in
/-- `(e₃, 0)`. -/
noncomputable def T₃ : Pt R := .some (R.e₃ : ℚ) 0 (nonsingular_raiz raiz₃)

/-- **`E(ℚ)[2] = {O, T₁, T₂, T₃}`.** -/
theorem dois_torcao {P : Pt R} (h : P + P = 0) : P = 0 ∨ P = T₁ R ∨ P = T₂ R ∨ P = T₃ R := by
  cases P with
  | zero => exact Or.inl rfl
  | some x y hP =>
    right
    by_cases hy : y = (curva R).toAffine.negY x y
    · rw [negY_curva] at hy
      have hy0 : y = 0 := by linarith
      subst hy0
      have heq := (equacao_iff R x 0).mp hP.1
      simp only [f] at heq
      have h0 : (x - R.e₁) * (x - R.e₂) * (x - R.e₃) = 0 := by linear_combination -heq
      rcases mul_eq_zero.mp h0 with h12 | h3
      · rcases mul_eq_zero.mp h12 with h1 | h2
        · left
          have hx : x = R.e₁ := by linarith
          subst hx; rfl
        · right; left
          have hx : x = R.e₂ := by linarith
          subst hx; rfl
      · right; right
        have hx : x = R.e₃ := by linarith
        subst hx; rfl
    · exfalso
      rw [Point.add_self_of_Y_ne hy] at h
      exact Point.some_ne_zero _ h

theorem T_dobro {P : Pt R} (hP : P = 0 ∨ P = T₁ R ∨ P = T₂ R ∨ P = T₃ R) : P + P = 0 := by
  rcases hP with rfl | rfl | rfl | rfl
  · exact add_zero 0
  all_goals exact Point.add_self_of_Y_eq (by rw [negY_curva]; simp)

/-! ## A imagem da torção -/

open Classical in
variable (R) in
/-- `φ(E[2])`. -/
noncomputable def imT : Finset (Additive (Q2 × Q2)) :=
  {phi R 0, phi R (T₁ R), phi R (T₂ R), phi R (T₃ R)}

/-- **Se `|φ(E[2])| = 4`, então `φ(E(ℚ)_tors) = φ(E[2])`**: `|φ(T)| ≤ |T/2T| = |T[2]| ≤ 4`. -/
theorem phi_torsao_mem (h4 : (imT R).card = 4) {t : Pt R}
    (ht : t ∈ AddCommGroup.torsion (Pt R)) : phi R t ∈ imT R := by
  classical
  have hfin : Finite (AddCommGroup.torsion (Pt R)) :=
    WeierstrassCurve.Affine.finite_torsion (W := (curva R).toAffine)
  let A := ↥(AddCommGroup.torsion (Pt R))
  have : Fintype A := Fintype.ofFinite A
  let ψ : A →+ Additive (Q2 × Q2) := (phi R).comp (AddCommGroup.torsion (Pt R)).subtype
  have hker : (nsmulAddMonoidHom (α := A) 2).range ≤ ψ.ker := by
    rintro _ ⟨a, rfl⟩
    rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, map_nsmul, two_nsmul, add_self_q]
  let lift := QuotientAddGroup.lift (nsmulAddMonoidHom (α := A) 2).range ψ hker
  have : Fintype (A ⧸ (nsmulAddMonoidHom (α := A) 2).range) := Fintype.ofFinite _
  set Im : Finset (Additive (Q2 × Q2)) := Finset.univ.image ψ with hIm
  -- `|Im| ≤ |T/2T|`
  have hIm1 : Im ⊆ (Finset.univ : Finset (A ⧸ (nsmulAddMonoidHom (α := A) 2).range)).image lift := by
    intro z hz
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨QuotientAddGroup.mk a, Finset.mem_univ _, rfl⟩
  have hcard1 : Im.card ≤ Nat.card (A ⧸ (nsmulAddMonoidHom (α := A) 2).range) := by
    rw [Nat.card_eq_fintype_card]
    exact (Finset.card_le_card hIm1).trans Finset.card_image_le
  -- `|T[2]| ≤ 4`
  let S4 : Finset (Pt R) := {0, T₁ R, T₂ R, T₃ R}
  have hS4 : S4.card ≤ 4 := by
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    simp
  have hcard2 : Nat.card (nsmulAddMonoidHom (α := A) 2).ker ≤ 4 := by
    have hinj : Function.Injective (fun k : (nsmulAddMonoidHom (α := A) 2).ker =>
        (⟨(k : A).1, by
          have hk := k.2
          rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, two_nsmul] at hk
          have := congrArg Subtype.val hk
          simp only [ZeroMemClass.coe_zero] at this
          rcases dois_torcao this with h | h | h | h <;> simp [S4, h]⟩ : S4)) := by
      intro a b hab
      apply Subtype.ext; apply Subtype.ext
      simpa using congrArg Subtype.val hab
    calc Nat.card (nsmulAddMonoidHom (α := A) 2).ker ≤ Nat.card S4 := Nat.card_le_card_of_injective _ hinj
      _ = S4.card := Nat.card_eq_finsetCard S4
      _ ≤ 4 := hS4
  -- `φ(E[2]) ⊆ Im`
  have htor : ∀ P : Pt R, (P = 0 ∨ P = T₁ R ∨ P = T₂ R ∨ P = T₃ R) →
      P ∈ AddCommGroup.torsion (Pt R) := by
    intro P hP
    rw [AddCommGroup.mem_torsion]
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2, by norm_num, by rw [two_nsmul]; exact T_dobro hP⟩
  have hsub : imT R ⊆ Im := by
    intro z hz
    simp only [imT, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact Finset.mem_image.mpr ⟨⟨0, htor 0 (Or.inl rfl)⟩, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨⟨_, htor _ (Or.inr (Or.inl rfl))⟩, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨⟨_, htor _ (Or.inr (Or.inr (Or.inl rfl)))⟩, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨⟨_, htor _ (Or.inr (Or.inr (Or.inr rfl)))⟩, Finset.mem_univ _, rfl⟩
  have heq : imT R = Im := Finset.eq_of_subset_of_card_le hsub (by
    rw [h4]; exact hcard1.trans ((card_quot_dois (A := A)).le.trans hcard2))
  rw [heq]
  exact Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_univ _, rfl⟩

/-! ## Independência e posto -/

/-- **Critério de independência**: se `φ(P₁)`, `φ(P₂)` e `φ(P₁) + φ(P₂)` estão fora de `φ(E[2])`
(e `|φ(E[2])| = 4`), então `mP₁ + nP₂` de torção força `m = n = 0`. -/
theorem independentes (h4 : (imT R).card = 4) {P₁ P₂ : Pt R} (h1 : phi R P₁ ∉ imT R)
    (h2 : phi R P₂ ∉ imT R) (h12 : phi R P₁ + phi R P₂ ∉ imT R) :
    ∀ m n : ℤ, m • P₁ + n • P₂ ∈ AddCommGroup.torsion (Pt R) → m = 0 ∧ n = 0 := by
  suffices H : ∀ N : ℕ, ∀ m n : ℤ, m.natAbs + n.natAbs = N →
      m • P₁ + n • P₂ ∈ AddCommGroup.torsion (Pt R) → m = 0 ∧ n = 0 from
    fun m n h => H _ m n rfl h
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro m n hN hmn
  by_cases hev : 2 ∣ m ∧ 2 ∣ n
  · obtain ⟨⟨m', rfl⟩, ⟨n', rfl⟩⟩ := hev
    have htor : m' • P₁ + n' • P₂ ∈ AddCommGroup.torsion (Pt R) := by
      have h2t : (2 : ℕ) • (m' • P₁ + n' • P₂) = (2 * m') • P₁ + (2 * n') • P₂ := by
        simp only [two_nsmul, two_mul, add_zsmul]; abel
      rw [AddCommGroup.mem_torsion] at hmn ⊢
      rw [← h2t] at hmn
      exact (isOfFinAddOrder_nsmul.mp hmn).resolve_right (by norm_num)
    by_cases h0 : m' = 0 ∧ n' = 0
    · rw [h0.1, h0.2]; simp
    · have hlt : m'.natAbs + n'.natAbs < N := by
        rw [← hN, Int.natAbs_mul, Int.natAbs_mul]
        have : 0 < m'.natAbs + n'.natAbs := by
          by_contra hc
          push Not at hc
          exact h0 ⟨Int.natAbs_eq_zero.mp (by omega), Int.natAbs_eq_zero.mp (by omega)⟩
        simp only [Int.reduceAbs]
        omega
      exact absurd (ih _ hlt m' n' rfl htor) h0
  · have hφ := phi_torsao_mem h4 hmn
    rw [map_add, map_zsmul, map_zsmul, zsmul_q m, zsmul_q n] at hφ
    rcases Int.emod_two_eq_zero_or_one m with hm | hm <;>
      rcases Int.emod_two_eq_zero_or_one n with hn | hn
    · exact absurd ⟨Int.dvd_of_emod_eq_zero hm, Int.dvd_of_emod_eq_zero hn⟩ hev
    · rw [hm, hn, zero_zsmul, one_zsmul, zero_add] at hφ
      exact absurd hφ h2
    · rw [hm, hn, zero_zsmul, one_zsmul, add_zero] at hφ
      exact absurd hφ h1
    · rw [hm, hn, one_zsmul, one_zsmul] at hφ
      exact absurd hφ h12

/-- **Posto ≥ 2** pela 2-descida. -/
theorem posto_ge_dois (h4 : (imT R).card = 4) {P₁ P₂ : Pt R} (h1 : phi R P₁ ∉ imT R)
    (h2 : phi R P₂ ∉ imT R) (h12 : phi R P₁ + phi R P₂ ∉ imT R) :
    2 ≤ ATK.LigacaoBSD.postoMW (curva R) := by
  have hli : LinearIndependent ℤ ![P₁, P₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    exact independentes h4 h1 h2 h12 s t (by rw [hst]; exact zero_mem _)
  have hc := hli.cardinal_le_rank
  simp only [Cardinal.mk_fintype, Fintype.card_fin] at hc
  unfold ATK.LigacaoBSD.postoMW
  exact (Cardinal.enat_gc 2 _).mp (by simpa using hc)


/-! ## O exemplo `y² = x(x + 30)(x + 2)` -/

/-- Classes distintas: se `ab` não é quadrado em `ℤ`, `[a] ≠ [b]` em `ℚˣ/ℚˣ²`. -/
theorem cls_ne {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (h : ¬ IsSquare (a * b)) :
    cls (a : ℚ) ≠ cls (b : ℚ) := by
  intro hab
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have h1 : cls ((a : ℚ) * b) = 1 := by rw [cls_mul ha' hb', hab, cls_mul_self hb']
  obtain ⟨c, hc⟩ := (cls_eq_one_iff (mul_ne_zero ha' hb')).mp h1
  apply h
  rw [← Rat.isSquare_intCast_iff]
  exact ⟨c, by push_cast; rw [hc]; ring⟩

/-- Negativos não são quadrados. -/
theorem nq_neg {n : ℤ} (h : n < 0) : ¬ IsSquare n := by
  rintro ⟨r, rfl⟩
  nlinarith [mul_self_nonneg r]

/-- `k² < n < (k + 1)²` não é quadrado. -/
theorem nq_entre {n : ℤ} (k : ℤ) (hk : 0 ≤ k) (h1 : k * k < n) (h2 : n < (k + 1) * (k + 1)) :
    ¬ IsSquare n := by
  rintro ⟨r, rfl⟩
  have hr : r * r = |r| * |r| := (abs_mul_abs_self r).symm
  rw [hr] at h1 h2
  have ha := abs_nonneg r
  have hlt : k < |r| := by
    by_contra hc
    push Not at hc
    nlinarith
  have hlt2 : |r| < k + 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  omega

/-- Um não quadrado é não nulo. -/
theorem nz {a : ℤ} (h : ¬ IsSquare a) : a ≠ 0 := by
  rintro rfl
  exact h ⟨0, by ring⟩

/-- A primeira coordenada de `φ` é `[δ_{e₁}]`. -/
theorem fst_phi (P : Pt R) : (phi R P).toMul.1 = cls (delta (R.e₁ : ℚ) R.e₂ R.e₃ P) :=
  rfl

/-- As classes `[x − e₁]` da 2-torção: `1`, `(e₁ − e₂)(e₁ − e₃)`, `e₂ − e₁`, `e₃ − e₁`. -/
theorem fst_T (a b c : ℤ) (ha : a = (R.e₁ - R.e₂) * (R.e₁ - R.e₃)) (hb : b = R.e₂ - R.e₁)
    (hc : c = R.e₃ - R.e₁) :
    (phi R 0).toMul.1 = cls ((1 : ℤ) : ℚ) ∧ (phi R (T₁ R)).toMul.1 = cls (a : ℚ) ∧
      (phi R (T₂ R)).toMul.1 = cls (b : ℚ) ∧ (phi R (T₃ R)).toMul.1 = cls (c : ℚ) := by
  have n12 : (R.e₂ : ℚ) ≠ R.e₁ := by exact_mod_cast R.h₁₂.symm
  have n13 : (R.e₃ : ℚ) ≠ R.e₁ := by exact_mod_cast R.h₁₃.symm
  subst ha hb hc
  refine ⟨by rw [fst_phi]; simp [delta], ?_, ?_, ?_⟩ <;> rw [fst_phi]
  · simp [delta, T₁, dd]
  · simp [delta, T₂, n12]
  · simp [delta, T₃, n13]

/-- **`|φ(E[2])| = 4`** quando as classes `a, b, c` da 2-torção e seus produtos dois a dois não
são quadrados. -/
theorem card_imT {a b c : ℤ} (ha : a = (R.e₁ - R.e₂) * (R.e₁ - R.e₃)) (hb : b = R.e₂ - R.e₁)
    (hc : c = R.e₃ - R.e₁) (h1 : ¬ IsSquare a) (h2 : ¬ IsSquare b) (h3 : ¬ IsSquare c)
    (h4 : ¬ IsSquare (a * b)) (h5 : ¬ IsSquare (a * c)) (h6 : ¬ IsSquare (b * c)) :
    (imT R).card = 4 := by
  classical
  obtain ⟨d1, d2, d3, d4⟩ := fst_T a b c ha hb hc
  have ne : ∀ {u v : Additive (Q2 × Q2)} {a b : ℤ}, u.toMul.1 = cls (a : ℚ) →
      v.toMul.1 = cls (b : ℚ) → a ≠ 0 → b ≠ 0 → ¬ IsSquare (a * b) → u ≠ v := by
    intro u v a b hu hv ha hb hs huv
    exact cls_ne ha hb hs (hu.symm.trans (huv ▸ hv))
  unfold imT
  rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair]
  · exact ne d3 d4 (nz h2) (nz h3) h6
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne d2 d3 (nz h1) (nz h2) h4, ne d2 d4 (nz h1) (nz h3) h5⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne d1 d2 one_ne_zero (nz h1) (by rwa [one_mul]),
      ne d1 d3 one_ne_zero (nz h2) (by rwa [one_mul]),
      ne d1 d4 one_ne_zero (nz h3) (by rwa [one_mul])⟩

/-- **Fora de `φ(E[2])`**: se `[δ_{e₁}] = [d]` com `d`, `da`, `db`, `dc` não quadrados. -/
theorem fora {a b c : ℤ} (ha : a = (R.e₁ - R.e₂) * (R.e₁ - R.e₃)) (hb : b = R.e₂ - R.e₁)
    (hc : c = R.e₃ - R.e₁) {z : Additive (Q2 × Q2)} {d : ℤ} (hz : z.toMul.1 = cls (d : ℚ))
    (h0 : ¬ IsSquare d) (h1 : ¬ IsSquare (d * a)) (h2 : ¬ IsSquare (d * b))
    (h3 : ¬ IsSquare (d * c)) : z ∉ imT R := by
  obtain ⟨d1, d2, d3, d4⟩ := fst_T a b c ha hb hc
  intro hm
  simp only [imT, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact cls_ne (nz h0) one_ne_zero (by rwa [mul_one]) (hz.symm.trans d1)
  · exact cls_ne (nz h0) (right_ne_zero_of_mul (nz h1)) h1 (hz.symm.trans d2)
  · exact cls_ne (nz h0) (right_ne_zero_of_mul (nz h2)) h2 (hz.symm.trans d3)
  · exact cls_ne (nz h0) (right_ne_zero_of_mul (nz h3)) h3 (hz.symm.trans d4)

/-- **Ponto de ordem infinita**: `φ(P) ∉ φ(E[2])` (com `|φ(E[2])| = 4`) força `P` fora da torção. -/
theorem nao_torsao (h4 : (imT R).card = 4) {P : Pt R} (h : phi R P ∉ imT R) :
    P ∉ AddCommGroup.torsion (Pt R) :=
  fun ht => h (phi_torsao_mem h4 ht)

/-- **Posto ≥ 1** pela 2-descida. -/
theorem posto_ge_um (h4 : (imT R).card = 4) {P : Pt R} (h : phi R P ∉ imT R) :
    1 ≤ ATK.LigacaoBSD.postoMW (curva R) := by
  have hli : LinearIndependent ℤ ![P] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    fin_cases i
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero] at hg
    by_contra hne
    apply nao_torsao h4 h
    rw [AddCommGroup.mem_torsion]
    exact isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨g 0, hne, hg⟩
  have hc := hli.cardinal_le_rank
  simp only [Cardinal.mk_fintype, Fintype.card_fin] at hc
  unfold ATK.LigacaoBSD.postoMW
  exact (Cardinal.enat_gc 1 _).mp (by simpa using hc)

/-- Posto `≥ 1` implica `E(ℚ)` infinito. -/
theorem infinito_of_posto {R : Raizes} (h : 1 ≤ ATK.LigacaoBSD.postoMW (curva R)) :
    Infinite (Pt R) := by
  by_contra hf
  rw [not_infinite_iff_finite] at hf
  have h0 : ATK.LigacaoBSD.postoMW (curva R) = 0 := by
    unfold ATK.LigacaoBSD.postoMW
    have : Module.rank ℤ (Pt R) = 0 := by
      rw [rank_eq_zero_iff]
      intro x
      obtain ⟨n, hn, hx⟩ := (isOfFinAddOrder_of_finite x).exists_nsmul_eq_zero
      exact ⟨n, by exact_mod_cast hn.ne', by rw [natCast_zsmul]; exact hx⟩
    rw [this, map_zero]
  rw [h0] at h
  exact absurd h (by decide)

/-! ## Exemplo de posto `≥ 2`: `y² = x(x + 30)(x + 2)` -/

/-- `e₁ = 0`, `e₂ = −30`, `e₃ = −2`. -/
def R30 : Raizes := ⟨0, -30, -2, by decide, by decide, by decide⟩

theorem nsR30 {x y : ℚ} (h : y ^ 2 = x * (x + 30) * (x + 2)) :
    (curva R30).toAffine.Nonsingular x y :=
  (equation_iff_nonsingular).mp ((equacao_iff R30 x y).mpr (by
    simp only [f, R30]; push_cast; linear_combination h))

/-- `P₁ = (−20, 60)`. -/
noncomputable def P₁ : Pt R30 := .some (-20) 60 (nsR30 (by norm_num))
/-- `P₂ = (−16, 56)`. -/
noncomputable def P₂ : Pt R30 := .some (-16) 56 (nsR30 (by norm_num))

/-- Classes da 2-torção de `R30`: `60, −30, −2`. -/
theorem imT_R30 : (imT R30).card = 4 :=
  card_imT (a := 60) (b := -30) (c := -2) (by decide) (by decide) (by decide)
    (nq_entre 7 (by norm_num) (by norm_num) (by norm_num)) (nq_neg (by norm_num))
    (nq_neg (by norm_num)) (nq_neg (by norm_num)) (nq_neg (by norm_num))
    (nq_entre 7 (by norm_num) (by norm_num) (by norm_num))

/-- **A curva `y² = x(x + 30)(x + 2)` tem posto de Mordell–Weil `≥ 2`**: `(−20, 60)` e
`(−16, 56)` são independentes (2-descida completa, certificada). -/
theorem posto_R30 : 2 ≤ ATK.LigacaoBSD.postoMW (curva R30) := by
  have d1 : (phi R30 P₁).toMul.1 = cls ((-20 : ℤ) : ℚ) := by
    rw [fst_phi]; simp [delta, P₁, R30]
  have d2 : (phi R30 P₂).toMul.1 = cls ((-16 : ℤ) : ℚ) := by
    rw [fst_phi]; simp [delta, P₂, R30]
  have d12 : (phi R30 P₁ + phi R30 P₂).toMul.1 = cls ((320 : ℤ) : ℚ) := by
    change (phi R30 P₁).toMul.1 * (phi R30 P₂).toMul.1 = _
    rw [d1, d2, ← cls_mul (by norm_num) (by norm_num)]
    norm_num
  have ha : (60 : ℤ) = (R30.e₁ - R30.e₂) * (R30.e₁ - R30.e₃) := by decide
  have hb : (-30 : ℤ) = R30.e₂ - R30.e₁ := by decide
  have hc : (-2 : ℤ) = R30.e₃ - R30.e₁ := by decide
  exact posto_ge_dois imT_R30
    (fora ha hb hc d1 (nq_neg (by norm_num)) (nq_neg (by norm_num))
      (nq_entre 24 (by norm_num) (by norm_num) (by norm_num))
      (nq_entre 6 (by norm_num) (by norm_num) (by norm_num)))
    (fora ha hb hc d2 (nq_neg (by norm_num)) (nq_neg (by norm_num))
      (nq_entre 21 (by norm_num) (by norm_num) (by norm_num))
      (nq_entre 5 (by norm_num) (by norm_num) (by norm_num)))
    (fora ha hb hc d12 (nq_entre 17 (by norm_num) (by norm_num) (by norm_num))
      (nq_entre 138 (by norm_num) (by norm_num) (by norm_num))
      (nq_neg (by norm_num)) (nq_neg (by norm_num)))

/-- Em particular `E(ℚ)` é infinito. -/
theorem infinito_R30 : Infinite (Pt R30) :=
  infinito_of_posto (le_trans (by decide) posto_R30)

/-! ## Exemplo de posto `≥ 1`: a curva do número congruente `6`, `y² = x³ − 36x` -/

/-- `e₁ = 0`, `e₂ = 6`, `e₃ = −6`. -/
def R6 : Raizes := ⟨0, 6, -6, by decide, by decide, by decide⟩

theorem equacao_R6 (x y : ℚ) : (curva R6).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - 36 * x := by
  rw [equacao_iff]
  simp only [f, R6]
  push_cast
  constructor <;> intro h <;> linear_combination h

/-- `(−3, 9)` (vem do triângulo `3, 4, 5`, de área `6`). -/
noncomputable def P₆ : Pt R6 :=
  .some (-3) 9 ((equation_iff_nonsingular).mp ((equacao_R6 _ _).mpr (by norm_num)))

/-- **`y² = x³ − 36x` tem posto `≥ 1`**: `(−3, 9)` tem ordem infinita. -/
theorem posto_R6 : 1 ≤ ATK.LigacaoBSD.postoMW (curva R6) := by
  have ha : (-36 : ℤ) = (R6.e₁ - R6.e₂) * (R6.e₁ - R6.e₃) := by decide
  have hb : (6 : ℤ) = R6.e₂ - R6.e₁ := by decide
  have hc : (-6 : ℤ) = R6.e₃ - R6.e₁ := by decide
  have h4 : (imT R6).card = 4 :=
    card_imT ha hb hc (nq_neg (by norm_num)) (nq_entre 2 (by norm_num) (by norm_num) (by norm_num))
      (nq_neg (by norm_num)) (nq_neg (by norm_num))
      (nq_entre 14 (by norm_num) (by norm_num) (by norm_num)) (nq_neg (by norm_num))
  have d : (phi R6 P₆).toMul.1 = cls ((-3 : ℤ) : ℚ) := by
    rw [fst_phi]; simp [delta, P₆, R6]
  exact posto_ge_um h4 (fora ha hb hc d (nq_neg (by norm_num))
    (nq_entre 10 (by norm_num) (by norm_num) (by norm_num)) (nq_neg (by norm_num))
    (nq_entre 4 (by norm_num) (by norm_num) (by norm_num)))

theorem infinito_R6 : Infinite (Pt R6) := infinito_of_posto posto_R6

end ATK.PostoDois

#print axioms ATK.PostoDois.q2_mul_self
#print axioms ATK.PostoDois.add_self_q
#print axioms ATK.PostoDois.zsmul_q
#print axioms ATK.PostoDois.phi_dobro
#print axioms ATK.PostoDois.card_quot_dois
#print axioms ATK.PostoDois.dois_torcao
#print axioms ATK.PostoDois.T_dobro
#print axioms ATK.PostoDois.phi_torsao_mem
#print axioms ATK.PostoDois.independentes
#print axioms ATK.PostoDois.posto_ge_dois
#print axioms ATK.PostoDois.cls_ne
#print axioms ATK.PostoDois.nq_neg
#print axioms ATK.PostoDois.nq_entre
#print axioms ATK.PostoDois.nz
#print axioms ATK.PostoDois.fst_phi
#print axioms ATK.PostoDois.fst_T
#print axioms ATK.PostoDois.card_imT
#print axioms ATK.PostoDois.fora
#print axioms ATK.PostoDois.nao_torsao
#print axioms ATK.PostoDois.posto_ge_um
#print axioms ATK.PostoDois.infinito_of_posto
#print axioms ATK.PostoDois.nsR30
#print axioms ATK.PostoDois.imT_R30
#print axioms ATK.PostoDois.posto_R30
#print axioms ATK.PostoDois.infinito_R30
#print axioms ATK.PostoDois.equacao_R6
#print axioms ATK.PostoDois.posto_R6
#print axioms ATK.PostoDois.infinito_R6
