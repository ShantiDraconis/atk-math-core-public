import ATK.SophieGermain

/-!
# ATK — Ponte B2 (FLT): o critério de Germain–Legendre e o primeiro caso para `p < 300`

Generaliza `ATK.SophieGermain`: em vez de `q = 2p + 1`, basta um primo auxiliar `q = 2kp + 1` com

* (A) não há `a, b, c` com `a^{2k} = b^{2k} = c^{2k} = 1` e `a + b + c = 0` em `ℤ/q` — as
  `p`-ésimas potências não nulas mod `q` são raízes `2k`-ésimas da unidade, logo
  `xᵖ + yᵖ + zᵖ ≡ 0 (mod q)` força `q ∣ xyz`;
* (B) `p` não é uma `p`-ésima potência mod `q`: `p ≢ 0` e `p^{2k} ≢ 1 (mod q)`.

`germain`: com um tal `q`, o primeiro caso de FLT vale para `p` (Sophie Germain; Legendre, 1823).
`auxiliar_de_listaN`: (A) se verifica com uma lista explícita das `2k` raízes (o polinômio
`X^{2k} − 1` tem no máximo `2k` raízes num corpo, `raizes_na_lista`), e o kernel confere a lista e
(B) por `decide` em aritmética de `ℕ`. Para cada primo ímpar `p < 300` há um tal `q` (`q ≤ 9767`):

* `flt_caso_um_menor_300`: **para todo primo ímpar `p < 300`, `xᵖ + yᵖ ≠ zᵖ` quando `p ∤ xyz`**;
* `flt_iff_caso_dois`: para esses `p`, FLT(p) equivale ao segundo caso (`p ∣ xyz`).

B2 continua `PARCIAL_NO_MODELO_DO_LANE`: falta o segundo caso (`p ∣ xyz`) e os primos `p ≥ 300`.
-/

namespace ATK.GermainLegendre

open ATK.SophieGermain

/-- O primo auxiliar `q = 2kp + 1` do critério de Germain–Legendre. -/
structure Auxiliar (p q k : ℕ) : Prop where
  primo : q.Prime
  forma : q = 2 * k * p + 1
  semSoma : ∀ a b c : ZMod q, a ^ (2 * k) = 1 → b ^ (2 * k) = 1 → c ^ (2 * k) = 1 → a + b + c ≠ 0
  pNaoZero : (p : ZMod q) ≠ 0
  pNaoRaiz : (p : ZMod q) ^ (2 * k) ≠ 1

/-- `xᵖ` é raiz `2k`-ésima da unidade para `x ≠ 0` (pequeno teorema de Fermat). -/
theorem pot_raiz {p q k : ℕ} (A : Auxiliar p q k) {x : ZMod q} (hx : x ≠ 0) :
    (x ^ p) ^ (2 * k) = 1 := by
  have := Fact.mk A.primo
  rw [← pow_mul, show p * (2 * k) = q - 1 by rw [A.forma, Nat.add_sub_cancel]; ring]
  exact ZMod.pow_card_sub_one_eq_one hx

/-- (A) ⇒ `xᵖ + yᵖ + zᵖ = 0` em `ℤ/q` força `x`, `y` ou `z` nulo. -/
theorem zeroAux {p q k : ℕ} (A : Auxiliar p q k) {x y z : ZMod q}
    (h : x ^ p + y ^ p + z ^ p = 0) : x = 0 ∨ y = 0 ∨ z = 0 := by
  by_contra hne
  push Not at hne
  exact A.semSoma _ _ _ (pot_raiz A hne.1) (pot_raiz A hne.2.1) (pot_raiz A hne.2.2) h

theorem caso_q_dvd_aux {p q k : ℕ} (hp : p.Prime) (hodd : Odd p) (A : Auxiliar p q k)
    {a b c : ℤ} (h : a ^ p + b ^ p + c ^ p = 0)
    (hab : IsCoprime a b) (hbc : IsCoprime b c) (hca : IsCoprime c a)
    (hpa : ¬ (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) (hpc : ¬ (p : ℤ) ∣ c)
    (hqa : (q : ℤ) ∣ a) : False := by
  have hq := A.primo
  have := Fact.mk hq
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with h2 | h2
    · rw [h2] at hodd; exact absurd hodd (by decide)
    · have := hp.two_le
      by_contra hlt
      have : p = 2 := by omega
      rw [this] at hodd; exact absurd hodd (by decide)
  have cast0 : ∀ x : ℤ, (q : ℤ) ∣ x ↔ (x : ZMod q) = 0 := fun x =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd x q).symm
  obtain ⟨⟨α, hα⟩, β, hβ⟩ := fator hp hodd h hbc hpa
  obtain ⟨⟨γ, hγ⟩, δ, hδ⟩ := fator hp hodd (by linear_combination h) hca hpb
  obtain ⟨⟨ε, hε⟩, -⟩ := fator hp hodd (by linear_combination h) hab hpc
  have ha0 : (a : ZMod q) = 0 := (cast0 a).mp hqa
  -- coprimalidade mod q
  have hnz : ∀ x : ℤ, IsCoprime a x → (x : ZMod q) ≠ 0 := by
    intro x hx hx0
    have hqx : (q : ℤ) ∣ x := (cast0 x).mpr hx0
    have hu := hx.isUnit_of_dvd' hqa hqx
    rw [Int.isUnit_iff] at hu
    have : (2 : ℤ) ≤ q := by exact_mod_cast hq.two_le
    omega
  have hb0 := hnz b hab
  have hc0 := hnz c hca.symm
  -- passo 3: 2a como soma de três potências
  have hsum : (ε : ZMod q) ^ p + (γ : ZMod q) ^ p + (-(α : ZMod q)) ^ p = 0 := by
    have e1 : ((a + b : ℤ) : ZMod q) = (ε : ZMod q) ^ p := by rw [hε]; push_cast; rfl
    have e2 : ((c + a : ℤ) : ZMod q) = (γ : ZMod q) ^ p := by rw [hγ]; push_cast; rfl
    have e3 : ((b + c : ℤ) : ZMod q) = (α : ZMod q) ^ p := by rw [hα]; push_cast; rfl
    push_cast at e1 e2 e3
    rw [Odd.neg_pow hodd, ← e1, ← e2, ← e3, ha0]
    ring
  rcases zeroAux A hsum with hε0 | hγ0 | hα0
  · -- q ∣ a + b ⇒ q ∣ b
    apply hb0
    have e1 : ((a + b : ℤ) : ZMod q) = (ε : ZMod q) ^ p := by rw [hε]; push_cast; rfl
    push_cast at e1
    rw [hε0, zero_pow hp.ne_zero, ha0, zero_add] at e1
    exact e1
  · apply hc0
    have e2 : ((c + a : ℤ) : ZMod q) = (γ : ZMod q) ^ p := by rw [hγ]; push_cast; rfl
    push_cast at e2
    rw [hγ0, zero_pow hp.ne_zero, ha0, add_zero] at e2
    exact e2
  · -- b ≡ −c mod q
    have hbc' : (b : ZMod q) = -(c : ZMod q) := by
      have e3 : ((b + c : ℤ) : ZMod q) = (α : ZMod q) ^ p := by rw [hα]; push_cast; rfl
      push_cast at e3
      rw [neg_eq_zero.mp hα0, zero_pow hp.ne_zero] at e3
      linear_combination e3
    have hβ' : (β : ZMod q) ^ p = p * (c : ZMod q) ^ (p - 1) := by
      have := congrArg (fun x : ℤ => (x : ZMod q)) hβ
      rw [Q_cast, hbc', Q_neg hodd] at this
      push_cast at this
      exact this.symm
    have hδ' : (δ : ZMod q) ^ p = (c : ZMod q) ^ (p - 1) := by
      have := congrArg (fun x : ℤ => (x : ZMod q)) hδ
      rw [Q_cast, ha0, Q_zero (by omega)] at this
      push_cast at this
      exact this.symm
    have hcp : (c : ZMod q) ^ (p - 1) ≠ 0 := pow_ne_zero _ hc0
    have hδ0 : (δ : ZMod q) ≠ 0 := by
      intro h0
      rw [h0, zero_pow hp.ne_zero] at hδ'
      exact hcp hδ'.symm
    have key : ((β : ZMod q) * (δ : ZMod q)⁻¹) ^ p = p := by
      rw [mul_pow, hβ', inv_pow, hδ', mul_assoc, mul_inv_cancel₀ hcp, mul_one]
    by_cases ht : (β : ZMod q) * (δ : ZMod q)⁻¹ = 0
    · rw [ht, zero_pow hp.ne_zero] at key
      exact A.pNaoZero key.symm
    · have := pot_raiz A ht
      rw [key] at this
      exact A.pNaoRaiz this

/-- **Critério de Germain–Legendre** (forma simétrica, coprima). -/
theorem germain_coprimo {p q k : ℕ} (hp : p.Prime) (hodd : Odd p) (A : Auxiliar p q k)
    {a b c : ℤ} (h : a ^ p + b ^ p + c ^ p = 0)
    (hab : IsCoprime a b) (hbc : IsCoprime b c) (hca : IsCoprime c a) :
    (p : ℤ) ∣ a * b * c := by
  by_contra hdiv
  have hpa : ¬ (p : ℤ) ∣ a := fun h => hdiv (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)
  have hpb : ¬ (p : ℤ) ∣ b := fun h => hdiv (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _)
  have hpc : ¬ (p : ℤ) ∣ c := fun h => hdiv (dvd_mul_of_dvd_right h _)
  have hsum : (a : ZMod q) ^ p + (b : ZMod q) ^ p + (c : ZMod q) ^ p = 0 := by
    have := congrArg (fun x : ℤ => (x : ZMod q)) h
    push_cast at this
    exact this
  have cast0 : ∀ x : ℤ, (x : ZMod q) = 0 → (q : ℤ) ∣ x := fun x hx =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd x _).mp hx
  rcases zeroAux A hsum with ha | hb | hc
  · exact caso_q_dvd_aux hp hodd A h hab hbc hca hpa hpb hpc (cast0 a ha)
  · exact caso_q_dvd_aux hp hodd A (by linear_combination h) hbc hca hab hpb hpc hpa (cast0 b hb)
  · exact caso_q_dvd_aux hp hodd A (by linear_combination h) hca hab hbc hpc hpa hpb (cast0 c hc)

/-- A redução ao caso de `a, b, c` dois a dois coprimos. -/
theorem casoUm_de_coprimo {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (H : ∀ a b c : ℤ, a ^ p + b ^ p + c ^ p = 0 → IsCoprime a b → IsCoprime b c → IsCoprime c a →
      (p : ℤ) ∣ a * b * c)
    {x y z : ℤ} (hxyz : ¬ (p : ℤ) ∣ x * y * z) : x ^ p + y ^ p ≠ z ^ p := by
  intro h
  -- nenhum é zero
  have hx0 : x ≠ 0 := by rintro rfl; exact hxyz (by simp)
  have hy0 : y ≠ 0 := by rintro rfl; exact hxyz (by simp)
  -- d = mdc(x, y); d ∣ z
  obtain ⟨d, x', y', hd, hcop, rfl, rfl⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left y hx0)
  have hdz : (d : ℤ) ∣ z := by
    have : (d : ℤ) ^ p ∣ z ^ p := ⟨x' ^ p + y' ^ p, by rw [← h]; ring⟩
    exact (Int.pow_dvd_pow_iff hp.ne_zero).mp this
  obtain ⟨z', rfl⟩ := hdz
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have h' : x' ^ p + y' ^ p + (-z') ^ p = 0 := by
    rw [Odd.neg_pow hodd]
    have : (d : ℤ) ^ p * (x' ^ p + y' ^ p - z' ^ p) = 0 := by
      rw [mul_sub, mul_add]; rw [mul_pow, mul_pow, mul_pow] at h; linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (pow_eq_zero_iff hp.ne_zero |>.mp h0) hd0
    · linear_combination h0
  have hab : IsCoprime x' y' := Int.isCoprime_iff_gcd_eq_one.mpr hcop
  -- os outros pares são coprimos
  have cop3 : ∀ u v w : ℤ, u ^ p + v ^ p + w ^ p = 0 → IsCoprime u v → IsCoprime v w := by
    intro u v w huvw huv
    apply isCoprime_of_prime_dvd
    · rintro ⟨rfl, rfl⟩
      have : u = 0 := by
        have := huvw
        simp only [zero_pow hp.ne_zero, add_zero] at this
        exact pow_eq_zero_iff hp.ne_zero |>.mp this
      subst this
      exact (Prime.not_isUnit (Int.prime_two)) (huv.isUnit_of_dvd' (dvd_zero 2) (dvd_zero 2))
    · intro r hr hrv hrw
      have : r ∣ u ^ p := ⟨-(v ^ p + w ^ p) / r, by
        have h1 : r ∣ v ^ p + w ^ p := dvd_add (dvd_pow hrv hp.ne_zero) (dvd_pow hrw hp.ne_zero)
        obtain ⟨k, hk⟩ := h1
        rw [show u ^ p = -(v ^ p + w ^ p) by linear_combination huvw, hk]
        rw [show -(r * k) = r * -k by ring, Int.mul_ediv_cancel_left _ hr.ne_zero]⟩
      exact hr.not_isUnit (huv.isUnit_of_dvd' (hr.dvd_of_dvd_pow this) hrv)
  have hbc := cop3 x' y' (-z') h' hab
  have hca := cop3 y' (-z') x' (by linear_combination h') hbc
  have := H x' y' (-z') h' hab hbc hca
  apply hxyz
  have e : x' * (d : ℤ) * (y' * (d : ℤ)) * ((d : ℤ) * z') = -((d : ℤ) ^ 3 * (x' * y' * -z')) := by
    ring
  rw [e]
  exact (dvd_neg.mpr (dvd_mul_of_dvd_right this _))


/-- **Critério de Germain–Legendre**: com um primo auxiliar, o primeiro caso de FLT vale para `p`. -/
theorem germain {p q k : ℕ} (hp : p.Prime) (hodd : Odd p) (A : Auxiliar p q k)
    {x y z : ℤ} (hxyz : ¬ (p : ℤ) ∣ x * y * z) : x ^ p + y ^ p ≠ z ^ p :=
  casoUm_de_coprimo hp hodd (fun _ _ _ h hab hbc hca => germain_coprimo hp hodd A h hab hbc hca)
    hxyz

/-! ## Verificação de (A) por uma lista explícita de raízes -/

/-- Num corpo, se `L` lista `n` raízes distintas de `X^n − 1`, toda raiz está em `L`. -/
theorem raizes_na_lista {q n : ℕ} [Fact q.Prime] (L : List (ZMod q)) (hn : 0 < n)
    (hroot : ∀ t ∈ L, t ^ n = 1) (hnd : L.Nodup) (hlen : L.length = n) :
    ∀ t : ZMod q, t ^ n = 1 → t ∈ L := by
  intro t ht
  by_contra hnot
  have hnd' : (t ::ₘ (L : Multiset (ZMod q))).Nodup :=
    Multiset.nodup_cons.mpr ⟨by simpa using hnot, by simpa using hnd⟩
  have hsub : (t ::ₘ (L : Multiset (ZMod q))) ≤ Polynomial.nthRoots n (1 : ZMod q) := by
    rw [Multiset.le_iff_subset hnd']
    intro s hs
    rw [Polynomial.mem_nthRoots hn]
    rcases Multiset.mem_cons.mp hs with rfl | hs
    · exact ht
    · exact hroot s (by simpa using hs)
  have h1 := Multiset.card_le_card hsub
  have h2 := Polynomial.card_nthRoots n (1 : ZMod q)
  simp only [Multiset.card_cons, Multiset.coe_card, hlen] at h1
  omega

/-- Constrói o primo auxiliar a partir de uma lista explícita das `2k` raízes da unidade. -/
theorem auxiliar_de_lista {p q k : ℕ} (hq : q.Prime) (hform : q = 2 * k * p + 1) (hk : 0 < k)
    (L : List (ZMod q)) (hroot : ∀ t ∈ L, t ^ (2 * k) = 1) (hnd : L.Nodup)
    (hlen : L.length = 2 * k) (hsum : ∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ L, a + b + c ≠ 0)
    (hp0 : (p : ZMod q) ≠ 0) (hpr : (p : ZMod q) ^ (2 * k) ≠ 1) : Auxiliar p q k := by
  have := Fact.mk hq
  have hmem := raizes_na_lista L (by omega) hroot hnd hlen
  exact ⟨hq, hform, fun a b c ha hb hc => hsum a (hmem a ha) b (hmem b hb) c (hmem c hc), hp0, hpr⟩


/-- A mesma construção com a lista em `ℕ` (o kernel confere aritmética de `ℕ` rapidamente). -/
theorem auxiliar_de_listaN {p q k : ℕ} (hq : q.Prime) (hform : q = 2 * k * p + 1) (hk : 0 < k)
    (L : List ℕ) (hlt : ∀ t ∈ L, t < q) (hroot : ∀ t ∈ L, t ^ (2 * k) % q = 1) (hnd : L.Nodup)
    (hlen : L.length = 2 * k) (hsum : ∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ L, (a + b + c) % q ≠ 0)
    (hp0 : p % q ≠ 0) (hpr : p ^ (2 * k) % q ≠ 1) : Auxiliar p q k := by
  have hq1 : 1 < q := hq.one_lt
  refine auxiliar_de_lista hq hform hk (L.map (Nat.cast : ℕ → ZMod q)) ?_ ?_ ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    rw [← Nat.cast_pow, ← ZMod.natCast_mod, hroot s hs, Nat.cast_one]
  · refine List.Nodup.map_on (fun a ha b hb hab => ?_) hnd
    have := (ZMod.natCast_eq_natCast_iff' a b q).mp hab
    rwa [Nat.mod_eq_of_lt (hlt a ha), Nat.mod_eq_of_lt (hlt b hb)] at this
  · rw [List.length_map, hlen]
  · intro a ha b hb c hc
    obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
    rw [← Nat.cast_add, ← Nat.cast_add, Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
    exact hsum a' ha' b' hb' c' hc'
  · rw [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
    exact hp0
  · intro h
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt hq1] at h
    exact hpr h


/-! ## O primeiro caso de FLT para todo primo ímpar `p < 300` -/

/-- Primo auxiliar para `p = 3`: `q = 7 = 2·1·3 + 1`. -/
theorem aux_3 : Auxiliar 3 7 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 6] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 5`: `q = 11 = 2·1·5 + 1`. -/
theorem aux_5 : Auxiliar 5 11 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 10] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 7`: `q = 29 = 2·2·7 + 1`. -/
theorem aux_7 : Auxiliar 7 29 2 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 12, 17, 28] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 11`: `q = 23 = 2·1·11 + 1`. -/
theorem aux_11 : Auxiliar 11 23 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 22] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 13`: `q = 53 = 2·2·13 + 1`. -/
theorem aux_13 : Auxiliar 13 53 2 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 23, 30, 52] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 17`: `q = 137 = 2·4·17 + 1`. -/
theorem aux_17 : Auxiliar 17 137 4 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 10, 37, 41, 96, 100, 127, 136] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 19`: `q = 191 = 2·5·19 + 1`. -/
theorem aux_19 : Auxiliar 19 191 5 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 7, 39, 49, 82, 109, 142, 152, 184, 190] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 23`: `q = 47 = 2·1·23 + 1`. -/
theorem aux_23 : Auxiliar 23 47 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 46] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 29`: `q = 59 = 2·1·29 + 1`. -/
theorem aux_29 : Auxiliar 29 59 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 58] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 31`: `q = 311 = 2·5·31 + 1`. -/
theorem aux_31 : Auxiliar 31 311 5 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 6, 36, 52, 95, 216, 259, 275, 305, 310] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 37`: `q = 149 = 2·2·37 + 1`. -/
theorem aux_37 : Auxiliar 37 149 2 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 44, 105, 148] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 41`: `q = 83 = 2·1·41 + 1`. -/
theorem aux_41 : Auxiliar 41 83 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 82] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 43`: `q = 173 = 2·2·43 + 1`. -/
theorem aux_43 : Auxiliar 43 173 2 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 80, 93, 172] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 47`: `q = 659 = 2·7·47 + 1`. -/
theorem aux_47 : Auxiliar 47 659 7 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 12, 55, 144, 249, 270, 307, 352, 389, 410, 515, 604, 647, 658] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 53`: `q = 107 = 2·1·53 + 1`. -/
theorem aux_53 : Auxiliar 53 107 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 106] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 59`: `q = 827 = 2·7·59 + 1`. -/
theorem aux_59 : Auxiliar 59 827 7 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 20, 124, 270, 337, 389, 400, 427, 438, 490, 557, 703, 807, 826] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 61`: `q = 977 = 2·8·61 + 1`. -/
theorem aux_61 : Auxiliar 61 977 8 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 52, 80, 227, 252, 357, 403, 439, 538, 574, 620, 725, 750, 897, 925, 976] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 67`: `q = 269 = 2·2·67 + 1`. -/
theorem aux_67 : Auxiliar 67 269 2 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 82, 187, 268] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 71`: `q = 569 = 2·4·71 + 1`. -/
theorem aux_71 : Auxiliar 71 569 4 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 76, 86, 277, 292, 483, 493, 568] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 73`: `q = 293 = 2·2·73 + 1`. -/
theorem aux_73 : Auxiliar 73 293 2 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 138, 155, 292] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 79`: `q = 317 = 2·2·79 + 1`. -/
theorem aux_79 : Auxiliar 79 317 2 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 114, 203, 316] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 83`: `q = 167 = 2·1·83 + 1`. -/
theorem aux_83 : Auxiliar 83 167 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 166] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 89`: `q = 179 = 2·1·89 + 1`. -/
theorem aux_89 : Auxiliar 89 179 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 178] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 97`: `q = 389 = 2·2·97 + 1`. -/
theorem aux_97 : Auxiliar 97 389 2 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 115, 274, 388] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 101`: `q = 809 = 2·4·101 + 1`. -/
theorem aux_101 : Auxiliar 101 809 4 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 44, 239, 318, 491, 570, 765, 808] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 103`: `q = 1031 = 2·5·103 + 1`. -/
theorem aux_103 : Auxiliar 103 1031 5 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 264, 371, 412, 513, 518, 619, 660, 767, 1030] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 107`: `q = 857 = 2·4·107 + 1`. -/
theorem aux_107 : Auxiliar 107 857 4 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 188, 207, 351, 506, 650, 669, 856] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 109`: `q = 1091 = 2·5·109 + 1`. -/
theorem aux_109 : Auxiliar 109 1091 5 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 79, 93, 290, 305, 786, 801, 998, 1012, 1090] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 113`: `q = 227 = 2·1·113 + 1`. -/
theorem aux_113 : Auxiliar 113 227 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 226] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 127`: `q = 509 = 2·2·127 + 1`. -/
theorem aux_127 : Auxiliar 127 509 2 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 208, 301, 508] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 131`: `q = 263 = 2·1·131 + 1`. -/
theorem aux_131 : Auxiliar 131 263 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 262] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 137`: `q = 1097 = 2·4·137 + 1`. -/
theorem aux_137 : Auxiliar 137 1097 4 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 79, 341, 486, 611, 756, 1018, 1096] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 139`: `q = 557 = 2·2·139 + 1`. -/
theorem aux_139 : Auxiliar 139 557 2 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 118, 439, 556] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 149`: `q = 1193 = 2·4·149 + 1`. -/
theorem aux_149 : Auxiliar 149 1193 4 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 186, 362, 524, 669, 831, 1007, 1192] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 151`: `q = 1511 = 2·5·151 + 1`. -/
theorem aux_151 : Auxiliar 151 1511 5 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 423, 534, 631, 743, 768, 880, 977, 1088, 1510] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 157`: `q = 1571 = 2·5·157 + 1`. -/
theorem aux_157 : Auxiliar 157 1571 5 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 179, 382, 621, 746, 825, 950, 1189, 1392, 1570] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 163`: `q = 653 = 2·2·163 + 1`. -/
theorem aux_163 : Auxiliar 163 653 2 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 149, 504, 652] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 167`: `q = 2339 = 2·7·167 + 1`. -/
theorem aux_167 : Auxiliar 167 2339 7 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 190, 357, 1015, 1052, 1065, 1143, 1196, 1274, 1287, 1324, 1982, 2149, 2338] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 173`: `q = 347 = 2·1·173 + 1`. -/
theorem aux_173 : Auxiliar 173 347 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 346] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 179`: `q = 359 = 2·1·179 + 1`. -/
theorem aux_179 : Auxiliar 179 359 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 358] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 181`: `q = 1811 = 2·5·181 + 1`. -/
theorem aux_181 : Auxiliar 181 1811 5 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 433, 619, 771, 855, 956, 1040, 1192, 1378, 1810] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 191`: `q = 383 = 2·1·191 + 1`. -/
theorem aux_191 : Auxiliar 191 383 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 382] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 193`: `q = 773 = 2·2·193 + 1`. -/
theorem aux_193 : Auxiliar 193 773 2 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 317, 456, 772] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 197`: `q = 7487 = 2·19·197 + 1`. -/
theorem aux_197 : Auxiliar 197 7487 19 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 634, 833, 887, 1547, 1837, 2068, 2141, 2247, 2342, 2402, 2631, 2747, 2771, 2873, 3007, 3221, 3314, 3455, 4032, 4173, 4266, 4480, 4614, 4716, 4740, 4856, 5085, 5145, 5240, 5346, 5419, 5650, 5940, 6600, 6654, 6853, 7486] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 199`: `q = 797 = 2·2·199 + 1`. -/
theorem aux_199 : Auxiliar 199 797 2 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 215, 582, 796] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 211`: `q = 2111 = 2·5·211 + 1`. -/
theorem aux_211 : Auxiliar 211 2111 5 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 75, 325, 708, 957, 1154, 1403, 1786, 2036, 2110] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 223`: `q = 7583 = 2·17·223 + 1`. -/
theorem aux_223 : Auxiliar 223 7583 17 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 214, 298, 588, 815, 1058, 1078, 1262, 1491, 1885, 2192, 2758, 2920, 3074, 3079, 3108, 3202, 4381, 4475, 4504, 4509, 4663, 4825, 5391, 5698, 6092, 6321, 6505, 6525, 6768, 6995, 7285, 7369, 7582] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 227`: `q = 5903 = 2·13·227 + 1`. -/
theorem aux_227 : Auxiliar 227 5903 13 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 177, 590, 667, 1712, 1814, 1817, 1824, 1971, 2164, 2316, 2625, 2847, 3056, 3278, 3587, 3739, 3932, 4079, 4086, 4089, 4191, 5236, 5313, 5726, 5902] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 229`: `q = 5039 = 2·11·229 + 1`. -/
theorem aux_229 : Auxiliar 229 5039 11 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 115, 255, 482, 530, 903, 909, 1284, 1529, 1892, 1974, 3065, 3147, 3510, 3755, 4130, 4136, 4509, 4557, 4784, 4924, 5038] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 233`: `q = 467 = 2·1·233 + 1`. -/
theorem aux_233 : Auxiliar 233 467 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 466] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 239`: `q = 479 = 2·1·239 + 1`. -/
theorem aux_239 : Auxiliar 239 479 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 478] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 241`: `q = 2411 = 2·5·241 + 1`. -/
theorem aux_241 : Auxiliar 241 2411 5 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 13, 169, 214, 371, 2040, 2197, 2242, 2398, 2410] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 251`: `q = 503 = 2·1·251 + 1`. -/
theorem aux_251 : Auxiliar 251 503 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 502] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 257`: `q = 9767 = 2·19·257 + 1`. -/
theorem aux_257 : Auxiliar 257 9767 19 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 423, 2134, 2319, 2412, 2484, 2488, 2534, 2625, 3063, 3123, 3362, 3388, 3856, 4104, 4118, 4237, 4508, 4877, 4890, 5259, 5530, 5649, 5663, 5911, 6379, 6405, 6644, 6704, 7142, 7233, 7279, 7283, 7355, 7448, 7633, 9344, 9766] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 263`: `q = 5261 = 2·10·263 + 1`. -/
theorem aux_263 : Auxiliar 263 5261 10 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 132, 231, 279, 751, 827, 911, 1074, 1317, 1641, 3620, 3944, 4187, 4350, 4434, 4510, 4982, 5030, 5129, 5260] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 269`: `q = 2153 = 2·4·269 + 1`. -/
theorem aux_269 : Auxiliar 269 2153 4 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 232, 246, 1059, 1094, 1907, 1921, 2152] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 271`: `q = 2711 = 2·5·271 + 1`. -/
theorem aux_271 : Auxiliar 271 2711 5 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 18, 324, 410, 753, 1958, 2301, 2387, 2693, 2710] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 277`: `q = 1109 = 2·2·277 + 1`. -/
theorem aux_277 : Auxiliar 277 1109 2 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 354, 755, 1108] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 281`: `q = 563 = 2·1·281 + 1`. -/
theorem aux_281 : Auxiliar 281 563 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 562] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 283`: `q = 9623 = 2·17·283 + 1`. -/
theorem aux_283 : Auxiliar 283 9623 17 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 123, 288, 1330, 1580, 1732, 1880, 2067, 2552, 2759, 3068, 3107, 3586, 3628, 3663, 4043, 4117, 5506, 5580, 5960, 5995, 6037, 6516, 6555, 6864, 7071, 7556, 7743, 7891, 8043, 8293, 9335, 9500, 9622] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Primo auxiliar para `p = 293`: `q = 587 = 2·1·293 + 1`. -/
theorem aux_293 : Auxiliar 293 587 1 :=
  auxiliar_de_listaN (by norm_num) (by norm_num) (by norm_num) [1, 586] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem flt_caso_um_3 {x y z : ℤ} (h : ¬ (3 : ℤ) ∣ x * y * z) : x ^ 3 + y ^ 3 ≠ z ^ 3 :=
  germain (p := 3) (by norm_num) (by decide) aux_3 (by exact_mod_cast h)

theorem flt_caso_um_5 {x y z : ℤ} (h : ¬ (5 : ℤ) ∣ x * y * z) : x ^ 5 + y ^ 5 ≠ z ^ 5 :=
  germain (p := 5) (by norm_num) (by decide) aux_5 (by exact_mod_cast h)

theorem flt_caso_um_7 {x y z : ℤ} (h : ¬ (7 : ℤ) ∣ x * y * z) : x ^ 7 + y ^ 7 ≠ z ^ 7 :=
  germain (p := 7) (by norm_num) (by decide) aux_7 (by exact_mod_cast h)

theorem flt_caso_um_11 {x y z : ℤ} (h : ¬ (11 : ℤ) ∣ x * y * z) : x ^ 11 + y ^ 11 ≠ z ^ 11 :=
  germain (p := 11) (by norm_num) (by decide) aux_11 (by exact_mod_cast h)

theorem flt_caso_um_13 {x y z : ℤ} (h : ¬ (13 : ℤ) ∣ x * y * z) : x ^ 13 + y ^ 13 ≠ z ^ 13 :=
  germain (p := 13) (by norm_num) (by decide) aux_13 (by exact_mod_cast h)

theorem flt_caso_um_17 {x y z : ℤ} (h : ¬ (17 : ℤ) ∣ x * y * z) : x ^ 17 + y ^ 17 ≠ z ^ 17 :=
  germain (p := 17) (by norm_num) (by decide) aux_17 (by exact_mod_cast h)

theorem flt_caso_um_19 {x y z : ℤ} (h : ¬ (19 : ℤ) ∣ x * y * z) : x ^ 19 + y ^ 19 ≠ z ^ 19 :=
  germain (p := 19) (by norm_num) (by decide) aux_19 (by exact_mod_cast h)

theorem flt_caso_um_23 {x y z : ℤ} (h : ¬ (23 : ℤ) ∣ x * y * z) : x ^ 23 + y ^ 23 ≠ z ^ 23 :=
  germain (p := 23) (by norm_num) (by decide) aux_23 (by exact_mod_cast h)

theorem flt_caso_um_29 {x y z : ℤ} (h : ¬ (29 : ℤ) ∣ x * y * z) : x ^ 29 + y ^ 29 ≠ z ^ 29 :=
  germain (p := 29) (by norm_num) (by decide) aux_29 (by exact_mod_cast h)

theorem flt_caso_um_31 {x y z : ℤ} (h : ¬ (31 : ℤ) ∣ x * y * z) : x ^ 31 + y ^ 31 ≠ z ^ 31 :=
  germain (p := 31) (by norm_num) (by decide) aux_31 (by exact_mod_cast h)

theorem flt_caso_um_37 {x y z : ℤ} (h : ¬ (37 : ℤ) ∣ x * y * z) : x ^ 37 + y ^ 37 ≠ z ^ 37 :=
  germain (p := 37) (by norm_num) (by decide) aux_37 (by exact_mod_cast h)

theorem flt_caso_um_41 {x y z : ℤ} (h : ¬ (41 : ℤ) ∣ x * y * z) : x ^ 41 + y ^ 41 ≠ z ^ 41 :=
  germain (p := 41) (by norm_num) (by decide) aux_41 (by exact_mod_cast h)

theorem flt_caso_um_43 {x y z : ℤ} (h : ¬ (43 : ℤ) ∣ x * y * z) : x ^ 43 + y ^ 43 ≠ z ^ 43 :=
  germain (p := 43) (by norm_num) (by decide) aux_43 (by exact_mod_cast h)

theorem flt_caso_um_47 {x y z : ℤ} (h : ¬ (47 : ℤ) ∣ x * y * z) : x ^ 47 + y ^ 47 ≠ z ^ 47 :=
  germain (p := 47) (by norm_num) (by decide) aux_47 (by exact_mod_cast h)

theorem flt_caso_um_53 {x y z : ℤ} (h : ¬ (53 : ℤ) ∣ x * y * z) : x ^ 53 + y ^ 53 ≠ z ^ 53 :=
  germain (p := 53) (by norm_num) (by decide) aux_53 (by exact_mod_cast h)

theorem flt_caso_um_59 {x y z : ℤ} (h : ¬ (59 : ℤ) ∣ x * y * z) : x ^ 59 + y ^ 59 ≠ z ^ 59 :=
  germain (p := 59) (by norm_num) (by decide) aux_59 (by exact_mod_cast h)

theorem flt_caso_um_61 {x y z : ℤ} (h : ¬ (61 : ℤ) ∣ x * y * z) : x ^ 61 + y ^ 61 ≠ z ^ 61 :=
  germain (p := 61) (by norm_num) (by decide) aux_61 (by exact_mod_cast h)

theorem flt_caso_um_67 {x y z : ℤ} (h : ¬ (67 : ℤ) ∣ x * y * z) : x ^ 67 + y ^ 67 ≠ z ^ 67 :=
  germain (p := 67) (by norm_num) (by decide) aux_67 (by exact_mod_cast h)

theorem flt_caso_um_71 {x y z : ℤ} (h : ¬ (71 : ℤ) ∣ x * y * z) : x ^ 71 + y ^ 71 ≠ z ^ 71 :=
  germain (p := 71) (by norm_num) (by decide) aux_71 (by exact_mod_cast h)

theorem flt_caso_um_73 {x y z : ℤ} (h : ¬ (73 : ℤ) ∣ x * y * z) : x ^ 73 + y ^ 73 ≠ z ^ 73 :=
  germain (p := 73) (by norm_num) (by decide) aux_73 (by exact_mod_cast h)

theorem flt_caso_um_79 {x y z : ℤ} (h : ¬ (79 : ℤ) ∣ x * y * z) : x ^ 79 + y ^ 79 ≠ z ^ 79 :=
  germain (p := 79) (by norm_num) (by decide) aux_79 (by exact_mod_cast h)

theorem flt_caso_um_83 {x y z : ℤ} (h : ¬ (83 : ℤ) ∣ x * y * z) : x ^ 83 + y ^ 83 ≠ z ^ 83 :=
  germain (p := 83) (by norm_num) (by decide) aux_83 (by exact_mod_cast h)

theorem flt_caso_um_89 {x y z : ℤ} (h : ¬ (89 : ℤ) ∣ x * y * z) : x ^ 89 + y ^ 89 ≠ z ^ 89 :=
  germain (p := 89) (by norm_num) (by decide) aux_89 (by exact_mod_cast h)

theorem flt_caso_um_97 {x y z : ℤ} (h : ¬ (97 : ℤ) ∣ x * y * z) : x ^ 97 + y ^ 97 ≠ z ^ 97 :=
  germain (p := 97) (by norm_num) (by decide) aux_97 (by exact_mod_cast h)

theorem flt_caso_um_101 {x y z : ℤ} (h : ¬ (101 : ℤ) ∣ x * y * z) : x ^ 101 + y ^ 101 ≠ z ^ 101 :=
  germain (p := 101) (by norm_num) (by decide) aux_101 (by exact_mod_cast h)

theorem flt_caso_um_103 {x y z : ℤ} (h : ¬ (103 : ℤ) ∣ x * y * z) : x ^ 103 + y ^ 103 ≠ z ^ 103 :=
  germain (p := 103) (by norm_num) (by decide) aux_103 (by exact_mod_cast h)

theorem flt_caso_um_107 {x y z : ℤ} (h : ¬ (107 : ℤ) ∣ x * y * z) : x ^ 107 + y ^ 107 ≠ z ^ 107 :=
  germain (p := 107) (by norm_num) (by decide) aux_107 (by exact_mod_cast h)

theorem flt_caso_um_109 {x y z : ℤ} (h : ¬ (109 : ℤ) ∣ x * y * z) : x ^ 109 + y ^ 109 ≠ z ^ 109 :=
  germain (p := 109) (by norm_num) (by decide) aux_109 (by exact_mod_cast h)

theorem flt_caso_um_113 {x y z : ℤ} (h : ¬ (113 : ℤ) ∣ x * y * z) : x ^ 113 + y ^ 113 ≠ z ^ 113 :=
  germain (p := 113) (by norm_num) (by decide) aux_113 (by exact_mod_cast h)

theorem flt_caso_um_127 {x y z : ℤ} (h : ¬ (127 : ℤ) ∣ x * y * z) : x ^ 127 + y ^ 127 ≠ z ^ 127 :=
  germain (p := 127) (by norm_num) (by decide) aux_127 (by exact_mod_cast h)

theorem flt_caso_um_131 {x y z : ℤ} (h : ¬ (131 : ℤ) ∣ x * y * z) : x ^ 131 + y ^ 131 ≠ z ^ 131 :=
  germain (p := 131) (by norm_num) (by decide) aux_131 (by exact_mod_cast h)

theorem flt_caso_um_137 {x y z : ℤ} (h : ¬ (137 : ℤ) ∣ x * y * z) : x ^ 137 + y ^ 137 ≠ z ^ 137 :=
  germain (p := 137) (by norm_num) (by decide) aux_137 (by exact_mod_cast h)

theorem flt_caso_um_139 {x y z : ℤ} (h : ¬ (139 : ℤ) ∣ x * y * z) : x ^ 139 + y ^ 139 ≠ z ^ 139 :=
  germain (p := 139) (by norm_num) (by decide) aux_139 (by exact_mod_cast h)

theorem flt_caso_um_149 {x y z : ℤ} (h : ¬ (149 : ℤ) ∣ x * y * z) : x ^ 149 + y ^ 149 ≠ z ^ 149 :=
  germain (p := 149) (by norm_num) (by decide) aux_149 (by exact_mod_cast h)

theorem flt_caso_um_151 {x y z : ℤ} (h : ¬ (151 : ℤ) ∣ x * y * z) : x ^ 151 + y ^ 151 ≠ z ^ 151 :=
  germain (p := 151) (by norm_num) (by decide) aux_151 (by exact_mod_cast h)

theorem flt_caso_um_157 {x y z : ℤ} (h : ¬ (157 : ℤ) ∣ x * y * z) : x ^ 157 + y ^ 157 ≠ z ^ 157 :=
  germain (p := 157) (by norm_num) (by decide) aux_157 (by exact_mod_cast h)

theorem flt_caso_um_163 {x y z : ℤ} (h : ¬ (163 : ℤ) ∣ x * y * z) : x ^ 163 + y ^ 163 ≠ z ^ 163 :=
  germain (p := 163) (by norm_num) (by decide) aux_163 (by exact_mod_cast h)

theorem flt_caso_um_167 {x y z : ℤ} (h : ¬ (167 : ℤ) ∣ x * y * z) : x ^ 167 + y ^ 167 ≠ z ^ 167 :=
  germain (p := 167) (by norm_num) (by decide) aux_167 (by exact_mod_cast h)

theorem flt_caso_um_173 {x y z : ℤ} (h : ¬ (173 : ℤ) ∣ x * y * z) : x ^ 173 + y ^ 173 ≠ z ^ 173 :=
  germain (p := 173) (by norm_num) (by decide) aux_173 (by exact_mod_cast h)

theorem flt_caso_um_179 {x y z : ℤ} (h : ¬ (179 : ℤ) ∣ x * y * z) : x ^ 179 + y ^ 179 ≠ z ^ 179 :=
  germain (p := 179) (by norm_num) (by decide) aux_179 (by exact_mod_cast h)

theorem flt_caso_um_181 {x y z : ℤ} (h : ¬ (181 : ℤ) ∣ x * y * z) : x ^ 181 + y ^ 181 ≠ z ^ 181 :=
  germain (p := 181) (by norm_num) (by decide) aux_181 (by exact_mod_cast h)

theorem flt_caso_um_191 {x y z : ℤ} (h : ¬ (191 : ℤ) ∣ x * y * z) : x ^ 191 + y ^ 191 ≠ z ^ 191 :=
  germain (p := 191) (by norm_num) (by decide) aux_191 (by exact_mod_cast h)

theorem flt_caso_um_193 {x y z : ℤ} (h : ¬ (193 : ℤ) ∣ x * y * z) : x ^ 193 + y ^ 193 ≠ z ^ 193 :=
  germain (p := 193) (by norm_num) (by decide) aux_193 (by exact_mod_cast h)

theorem flt_caso_um_197 {x y z : ℤ} (h : ¬ (197 : ℤ) ∣ x * y * z) : x ^ 197 + y ^ 197 ≠ z ^ 197 :=
  germain (p := 197) (by norm_num) (by decide) aux_197 (by exact_mod_cast h)

theorem flt_caso_um_199 {x y z : ℤ} (h : ¬ (199 : ℤ) ∣ x * y * z) : x ^ 199 + y ^ 199 ≠ z ^ 199 :=
  germain (p := 199) (by norm_num) (by decide) aux_199 (by exact_mod_cast h)

theorem flt_caso_um_211 {x y z : ℤ} (h : ¬ (211 : ℤ) ∣ x * y * z) : x ^ 211 + y ^ 211 ≠ z ^ 211 :=
  germain (p := 211) (by norm_num) (by decide) aux_211 (by exact_mod_cast h)

theorem flt_caso_um_223 {x y z : ℤ} (h : ¬ (223 : ℤ) ∣ x * y * z) : x ^ 223 + y ^ 223 ≠ z ^ 223 :=
  germain (p := 223) (by norm_num) (by decide) aux_223 (by exact_mod_cast h)

theorem flt_caso_um_227 {x y z : ℤ} (h : ¬ (227 : ℤ) ∣ x * y * z) : x ^ 227 + y ^ 227 ≠ z ^ 227 :=
  germain (p := 227) (by norm_num) (by decide) aux_227 (by exact_mod_cast h)

theorem flt_caso_um_229 {x y z : ℤ} (h : ¬ (229 : ℤ) ∣ x * y * z) : x ^ 229 + y ^ 229 ≠ z ^ 229 :=
  germain (p := 229) (by norm_num) (by decide) aux_229 (by exact_mod_cast h)

theorem flt_caso_um_233 {x y z : ℤ} (h : ¬ (233 : ℤ) ∣ x * y * z) : x ^ 233 + y ^ 233 ≠ z ^ 233 :=
  germain (p := 233) (by norm_num) (by decide) aux_233 (by exact_mod_cast h)

theorem flt_caso_um_239 {x y z : ℤ} (h : ¬ (239 : ℤ) ∣ x * y * z) : x ^ 239 + y ^ 239 ≠ z ^ 239 :=
  germain (p := 239) (by norm_num) (by decide) aux_239 (by exact_mod_cast h)

theorem flt_caso_um_241 {x y z : ℤ} (h : ¬ (241 : ℤ) ∣ x * y * z) : x ^ 241 + y ^ 241 ≠ z ^ 241 :=
  germain (p := 241) (by norm_num) (by decide) aux_241 (by exact_mod_cast h)

theorem flt_caso_um_251 {x y z : ℤ} (h : ¬ (251 : ℤ) ∣ x * y * z) : x ^ 251 + y ^ 251 ≠ z ^ 251 :=
  germain (p := 251) (by norm_num) (by decide) aux_251 (by exact_mod_cast h)

theorem flt_caso_um_257 {x y z : ℤ} (h : ¬ (257 : ℤ) ∣ x * y * z) : x ^ 257 + y ^ 257 ≠ z ^ 257 :=
  germain (p := 257) (by norm_num) (by decide) aux_257 (by exact_mod_cast h)

theorem flt_caso_um_263 {x y z : ℤ} (h : ¬ (263 : ℤ) ∣ x * y * z) : x ^ 263 + y ^ 263 ≠ z ^ 263 :=
  germain (p := 263) (by norm_num) (by decide) aux_263 (by exact_mod_cast h)

theorem flt_caso_um_269 {x y z : ℤ} (h : ¬ (269 : ℤ) ∣ x * y * z) : x ^ 269 + y ^ 269 ≠ z ^ 269 :=
  germain (p := 269) (by norm_num) (by decide) aux_269 (by exact_mod_cast h)

theorem flt_caso_um_271 {x y z : ℤ} (h : ¬ (271 : ℤ) ∣ x * y * z) : x ^ 271 + y ^ 271 ≠ z ^ 271 :=
  germain (p := 271) (by norm_num) (by decide) aux_271 (by exact_mod_cast h)

theorem flt_caso_um_277 {x y z : ℤ} (h : ¬ (277 : ℤ) ∣ x * y * z) : x ^ 277 + y ^ 277 ≠ z ^ 277 :=
  germain (p := 277) (by norm_num) (by decide) aux_277 (by exact_mod_cast h)

theorem flt_caso_um_281 {x y z : ℤ} (h : ¬ (281 : ℤ) ∣ x * y * z) : x ^ 281 + y ^ 281 ≠ z ^ 281 :=
  germain (p := 281) (by norm_num) (by decide) aux_281 (by exact_mod_cast h)

theorem flt_caso_um_283 {x y z : ℤ} (h : ¬ (283 : ℤ) ∣ x * y * z) : x ^ 283 + y ^ 283 ≠ z ^ 283 :=
  germain (p := 283) (by norm_num) (by decide) aux_283 (by exact_mod_cast h)

theorem flt_caso_um_293 {x y z : ℤ} (h : ¬ (293 : ℤ) ∣ x * y * z) : x ^ 293 + y ^ 293 ≠ z ^ 293 :=
  germain (p := 293) (by norm_num) (by decide) aux_293 (by exact_mod_cast h)

/-- **Primeiro caso do último teorema de Fermat para todo primo ímpar `p < 300`** (critério de
Sophie Germain e Legendre): `xᵖ + yᵖ ≠ zᵖ` sempre que `p ∤ xyz`. -/
theorem flt_caso_um_menor_300 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp300 : p < 300)
    {x y z : ℤ} (h : ¬ (p : ℤ) ∣ x * y * z) : x ^ p + y ^ p ≠ z ^ p := by
  have hmem : p ∈ [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293] := by
    interval_cases p <;> first | decide | (exfalso; norm_num at hp; done) | exact absurd rfl hp2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact flt_caso_um_3 (by exact_mod_cast h)
  · exact flt_caso_um_5 (by exact_mod_cast h)
  · exact flt_caso_um_7 (by exact_mod_cast h)
  · exact flt_caso_um_11 (by exact_mod_cast h)
  · exact flt_caso_um_13 (by exact_mod_cast h)
  · exact flt_caso_um_17 (by exact_mod_cast h)
  · exact flt_caso_um_19 (by exact_mod_cast h)
  · exact flt_caso_um_23 (by exact_mod_cast h)
  · exact flt_caso_um_29 (by exact_mod_cast h)
  · exact flt_caso_um_31 (by exact_mod_cast h)
  · exact flt_caso_um_37 (by exact_mod_cast h)
  · exact flt_caso_um_41 (by exact_mod_cast h)
  · exact flt_caso_um_43 (by exact_mod_cast h)
  · exact flt_caso_um_47 (by exact_mod_cast h)
  · exact flt_caso_um_53 (by exact_mod_cast h)
  · exact flt_caso_um_59 (by exact_mod_cast h)
  · exact flt_caso_um_61 (by exact_mod_cast h)
  · exact flt_caso_um_67 (by exact_mod_cast h)
  · exact flt_caso_um_71 (by exact_mod_cast h)
  · exact flt_caso_um_73 (by exact_mod_cast h)
  · exact flt_caso_um_79 (by exact_mod_cast h)
  · exact flt_caso_um_83 (by exact_mod_cast h)
  · exact flt_caso_um_89 (by exact_mod_cast h)
  · exact flt_caso_um_97 (by exact_mod_cast h)
  · exact flt_caso_um_101 (by exact_mod_cast h)
  · exact flt_caso_um_103 (by exact_mod_cast h)
  · exact flt_caso_um_107 (by exact_mod_cast h)
  · exact flt_caso_um_109 (by exact_mod_cast h)
  · exact flt_caso_um_113 (by exact_mod_cast h)
  · exact flt_caso_um_127 (by exact_mod_cast h)
  · exact flt_caso_um_131 (by exact_mod_cast h)
  · exact flt_caso_um_137 (by exact_mod_cast h)
  · exact flt_caso_um_139 (by exact_mod_cast h)
  · exact flt_caso_um_149 (by exact_mod_cast h)
  · exact flt_caso_um_151 (by exact_mod_cast h)
  · exact flt_caso_um_157 (by exact_mod_cast h)
  · exact flt_caso_um_163 (by exact_mod_cast h)
  · exact flt_caso_um_167 (by exact_mod_cast h)
  · exact flt_caso_um_173 (by exact_mod_cast h)
  · exact flt_caso_um_179 (by exact_mod_cast h)
  · exact flt_caso_um_181 (by exact_mod_cast h)
  · exact flt_caso_um_191 (by exact_mod_cast h)
  · exact flt_caso_um_193 (by exact_mod_cast h)
  · exact flt_caso_um_197 (by exact_mod_cast h)
  · exact flt_caso_um_199 (by exact_mod_cast h)
  · exact flt_caso_um_211 (by exact_mod_cast h)
  · exact flt_caso_um_223 (by exact_mod_cast h)
  · exact flt_caso_um_227 (by exact_mod_cast h)
  · exact flt_caso_um_229 (by exact_mod_cast h)
  · exact flt_caso_um_233 (by exact_mod_cast h)
  · exact flt_caso_um_239 (by exact_mod_cast h)
  · exact flt_caso_um_241 (by exact_mod_cast h)
  · exact flt_caso_um_251 (by exact_mod_cast h)
  · exact flt_caso_um_257 (by exact_mod_cast h)
  · exact flt_caso_um_263 (by exact_mod_cast h)
  · exact flt_caso_um_269 (by exact_mod_cast h)
  · exact flt_caso_um_271 (by exact_mod_cast h)
  · exact flt_caso_um_277 (by exact_mod_cast h)
  · exact flt_caso_um_281 (by exact_mod_cast h)
  · exact flt_caso_um_283 (by exact_mod_cast h)
  · exact flt_caso_um_293 (by exact_mod_cast h)

/-- Para todo primo ímpar `p < 300`, **FLT(p) equivale ao segundo caso** (`p ∣ xyz`). -/
theorem flt_iff_caso_dois {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp300 : p < 300) :
    FermatLastTheoremFor p ↔
      ∀ x y z : ℤ, x ≠ 0 → y ≠ 0 → z ≠ 0 → (p : ℤ) ∣ x * y * z → x ^ p + y ^ p ≠ z ^ p := by
  rw [fermatLastTheoremFor_iff_int]
  constructor
  · intro h x y z hx hy hz _
    exact h x y z hx hy hz
  · intro h x y z hx hy hz
    by_cases hd : (p : ℤ) ∣ x * y * z
    · exact h x y z hx hy hz hd
    · exact flt_caso_um_menor_300 hp hp2 hp300 hd

end ATK.GermainLegendre

#print axioms ATK.GermainLegendre.pot_raiz
#print axioms ATK.GermainLegendre.zeroAux
#print axioms ATK.GermainLegendre.caso_q_dvd_aux
#print axioms ATK.GermainLegendre.germain_coprimo
#print axioms ATK.GermainLegendre.casoUm_de_coprimo
#print axioms ATK.GermainLegendre.germain
#print axioms ATK.GermainLegendre.raizes_na_lista
#print axioms ATK.GermainLegendre.auxiliar_de_lista
#print axioms ATK.GermainLegendre.auxiliar_de_listaN
#print axioms ATK.GermainLegendre.aux_3
#print axioms ATK.GermainLegendre.aux_5
#print axioms ATK.GermainLegendre.aux_7
#print axioms ATK.GermainLegendre.aux_11
#print axioms ATK.GermainLegendre.aux_13
#print axioms ATK.GermainLegendre.aux_17
#print axioms ATK.GermainLegendre.aux_19
#print axioms ATK.GermainLegendre.aux_23
#print axioms ATK.GermainLegendre.aux_29
#print axioms ATK.GermainLegendre.aux_31
#print axioms ATK.GermainLegendre.aux_37
#print axioms ATK.GermainLegendre.aux_41
#print axioms ATK.GermainLegendre.aux_43
#print axioms ATK.GermainLegendre.aux_47
#print axioms ATK.GermainLegendre.aux_53
#print axioms ATK.GermainLegendre.aux_59
#print axioms ATK.GermainLegendre.aux_61
#print axioms ATK.GermainLegendre.aux_67
#print axioms ATK.GermainLegendre.aux_71
#print axioms ATK.GermainLegendre.aux_73
#print axioms ATK.GermainLegendre.aux_79
#print axioms ATK.GermainLegendre.aux_83
#print axioms ATK.GermainLegendre.aux_89
#print axioms ATK.GermainLegendre.aux_97
#print axioms ATK.GermainLegendre.aux_101
#print axioms ATK.GermainLegendre.aux_103
#print axioms ATK.GermainLegendre.aux_107
#print axioms ATK.GermainLegendre.aux_109
#print axioms ATK.GermainLegendre.aux_113
#print axioms ATK.GermainLegendre.aux_127
#print axioms ATK.GermainLegendre.aux_131
#print axioms ATK.GermainLegendre.aux_137
#print axioms ATK.GermainLegendre.aux_139
#print axioms ATK.GermainLegendre.aux_149
#print axioms ATK.GermainLegendre.aux_151
#print axioms ATK.GermainLegendre.aux_157
#print axioms ATK.GermainLegendre.aux_163
#print axioms ATK.GermainLegendre.aux_167
#print axioms ATK.GermainLegendre.aux_173
#print axioms ATK.GermainLegendre.aux_179
#print axioms ATK.GermainLegendre.aux_181
#print axioms ATK.GermainLegendre.aux_191
#print axioms ATK.GermainLegendre.aux_193
#print axioms ATK.GermainLegendre.aux_197
#print axioms ATK.GermainLegendre.aux_199
#print axioms ATK.GermainLegendre.aux_211
#print axioms ATK.GermainLegendre.aux_223
#print axioms ATK.GermainLegendre.aux_227
#print axioms ATK.GermainLegendre.aux_229
#print axioms ATK.GermainLegendre.aux_233
#print axioms ATK.GermainLegendre.aux_239
#print axioms ATK.GermainLegendre.aux_241
#print axioms ATK.GermainLegendre.aux_251
#print axioms ATK.GermainLegendre.aux_257
#print axioms ATK.GermainLegendre.aux_263
#print axioms ATK.GermainLegendre.aux_269
#print axioms ATK.GermainLegendre.aux_271
#print axioms ATK.GermainLegendre.aux_277
#print axioms ATK.GermainLegendre.aux_281
#print axioms ATK.GermainLegendre.aux_283
#print axioms ATK.GermainLegendre.aux_293
#print axioms ATK.GermainLegendre.flt_caso_um_3
#print axioms ATK.GermainLegendre.flt_caso_um_5
#print axioms ATK.GermainLegendre.flt_caso_um_7
#print axioms ATK.GermainLegendre.flt_caso_um_11
#print axioms ATK.GermainLegendre.flt_caso_um_13
#print axioms ATK.GermainLegendre.flt_caso_um_17
#print axioms ATK.GermainLegendre.flt_caso_um_19
#print axioms ATK.GermainLegendre.flt_caso_um_23
#print axioms ATK.GermainLegendre.flt_caso_um_29
#print axioms ATK.GermainLegendre.flt_caso_um_31
#print axioms ATK.GermainLegendre.flt_caso_um_37
#print axioms ATK.GermainLegendre.flt_caso_um_41
#print axioms ATK.GermainLegendre.flt_caso_um_43
#print axioms ATK.GermainLegendre.flt_caso_um_47
#print axioms ATK.GermainLegendre.flt_caso_um_53
#print axioms ATK.GermainLegendre.flt_caso_um_59
#print axioms ATK.GermainLegendre.flt_caso_um_61
#print axioms ATK.GermainLegendre.flt_caso_um_67
#print axioms ATK.GermainLegendre.flt_caso_um_71
#print axioms ATK.GermainLegendre.flt_caso_um_73
#print axioms ATK.GermainLegendre.flt_caso_um_79
#print axioms ATK.GermainLegendre.flt_caso_um_83
#print axioms ATK.GermainLegendre.flt_caso_um_89
#print axioms ATK.GermainLegendre.flt_caso_um_97
#print axioms ATK.GermainLegendre.flt_caso_um_101
#print axioms ATK.GermainLegendre.flt_caso_um_103
#print axioms ATK.GermainLegendre.flt_caso_um_107
#print axioms ATK.GermainLegendre.flt_caso_um_109
#print axioms ATK.GermainLegendre.flt_caso_um_113
#print axioms ATK.GermainLegendre.flt_caso_um_127
#print axioms ATK.GermainLegendre.flt_caso_um_131
#print axioms ATK.GermainLegendre.flt_caso_um_137
#print axioms ATK.GermainLegendre.flt_caso_um_139
#print axioms ATK.GermainLegendre.flt_caso_um_149
#print axioms ATK.GermainLegendre.flt_caso_um_151
#print axioms ATK.GermainLegendre.flt_caso_um_157
#print axioms ATK.GermainLegendre.flt_caso_um_163
#print axioms ATK.GermainLegendre.flt_caso_um_167
#print axioms ATK.GermainLegendre.flt_caso_um_173
#print axioms ATK.GermainLegendre.flt_caso_um_179
#print axioms ATK.GermainLegendre.flt_caso_um_181
#print axioms ATK.GermainLegendre.flt_caso_um_191
#print axioms ATK.GermainLegendre.flt_caso_um_193
#print axioms ATK.GermainLegendre.flt_caso_um_197
#print axioms ATK.GermainLegendre.flt_caso_um_199
#print axioms ATK.GermainLegendre.flt_caso_um_211
#print axioms ATK.GermainLegendre.flt_caso_um_223
#print axioms ATK.GermainLegendre.flt_caso_um_227
#print axioms ATK.GermainLegendre.flt_caso_um_229
#print axioms ATK.GermainLegendre.flt_caso_um_233
#print axioms ATK.GermainLegendre.flt_caso_um_239
#print axioms ATK.GermainLegendre.flt_caso_um_241
#print axioms ATK.GermainLegendre.flt_caso_um_251
#print axioms ATK.GermainLegendre.flt_caso_um_257
#print axioms ATK.GermainLegendre.flt_caso_um_263
#print axioms ATK.GermainLegendre.flt_caso_um_269
#print axioms ATK.GermainLegendre.flt_caso_um_271
#print axioms ATK.GermainLegendre.flt_caso_um_277
#print axioms ATK.GermainLegendre.flt_caso_um_281
#print axioms ATK.GermainLegendre.flt_caso_um_283
#print axioms ATK.GermainLegendre.flt_caso_um_293
#print axioms ATK.GermainLegendre.flt_caso_um_menor_300
#print axioms ATK.GermainLegendre.flt_iff_caso_dois
