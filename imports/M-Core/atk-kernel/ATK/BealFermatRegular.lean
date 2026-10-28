import ATK.BealSeisSeisDois
import ATK.FermatRegular

/-!
# ATK — Beal com fator comum 5, 7, 11, 13, 17 ou 19 nos expoentes, incondicionalmente

Com FLT(5), FLT(7), FLT(11), FLT(13), FLT(17) e FLT(19) (`ATK.FermatRegular`) e o argumento de
`ATK.BealPartial.sem_solucao_de_flt_divisor`:

* `beal_igual_cinco`, …, `beal_igual_dezenove`: Beal com expoentes iguais;
* `beal_expoentes_mult`: Beal para todo triplo com `d ∣ x, y, z`, `d ∈ {5, 7, 11, 13, 17, 19}` — não há
  solução alguma; `beal_mdc_regular`: a forma via `mdc(x, y, z)`;
* `beal_iff_residual_regular`: **`BealConjecture ↔ ExclusaoResidualRegular`**, sem pontes — o
  residual incondicional perde os triplos com `5, 7, 11, 13, 17` ou `19` dividindo `mdc(x, y, z)`.

Cobertura incondicional dos triplos de expoentes em `3..200` (7.762.392): 799.326 (10,30%) →
**887.152 (11,43%)**. Estes triplos têm `mdc ≥ 5`, fora do domínio de O2 (`mdc ≤ 2`); sob a ponte
B2 já estavam cobertos. **O2 continua aberta.**
-/

namespace ATK.BealFermatRegular

open ATK.Conditional.Beal ATK.BealPartial ATK.BealFermatDescent ATK.BealSeisSeisDois
  ATK.FermatRegular

/-- Beal com `x = y = z = 5`. -/
theorem beal_igual_cinco : BealIgual 5 := beal_expoentes_iguais_de_flt flt_cinco

/-- Beal com `x = y = z = 7`. -/
theorem beal_igual_sete : BealIgual 7 := beal_expoentes_iguais_de_flt flt_sete

/-- Beal com `x = y = z = 11`. -/
theorem beal_igual_onze : BealIgual 11 := beal_expoentes_iguais_de_flt flt_onze

/-- Beal com `x = y = z = 13`. -/
theorem beal_igual_treze : BealIgual 13 := beal_expoentes_iguais_de_flt flt_treze

/-- Beal com `x = y = z = 17`. -/
theorem beal_igual_dezessete : BealIgual 17 := beal_expoentes_iguais_de_flt flt_dezessete

/-- Beal com `x = y = z = 19`. -/
theorem beal_igual_dezenove : BealIgual 19 := beal_expoentes_iguais_de_flt flt_dezenove

/-- FLT para `d ∈ {5, 7, 11, 13, 17, 19}`. -/
theorem flt_regulares {d : ℕ} (hd : d = 5 ∨ d = 7 ∨ d = 11 ∨ d = 13 ∨ d = 17 ∨ d = 19) : FermatLastTheoremFor d := by
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact flt_cinco
  · exact flt_sete
  · exact flt_onze
  · exact flt_treze
  · exact flt_dezessete
  · exact flt_dezenove

/-- **Incondicional**: Beal para todo triplo com `d ∣ x, y, z`, `d ∈ {5, 7, 11, 13, 17, 19}`. -/
theorem beal_expoentes_mult {d x y z : ℕ} (hd : d = 5 ∨ d = 7 ∨ d = 11 ∨ d = 13 ∨ d = 17 ∨ d = 19) (hx : d ∣ x)
    (hy : d ∣ y) (hz : d ∣ z) : BealFor x y z :=
  fun _ _ _ ha hb hc heq =>
    absurd heq (sem_solucao_de_flt_divisor (flt_regulares hd) hx hy hz ha hb hc)

/-- Forma via mdc. -/
theorem beal_mdc_regular {d x y z : ℕ} (hd : d = 5 ∨ d = 7 ∨ d = 11 ∨ d = 13 ∨ d = 17 ∨ d = 19)
    (h : d ∣ Nat.gcd x (Nat.gcd y z)) : BealFor x y z :=
  beal_expoentes_mult hd (h.trans (Nat.gcd_dvd_left _ _))
    (h.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)))
    (h.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)))

/-- Residual incondicional após FLT(3, 4, 5, 7, 11, 13, 17, 19), `(4,4,2)`, `(4,2,4)`, `(2,4,4)` e
`(6,6,2)`. -/
def ExclusaoResidualRegular : Prop :=
  ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    ¬ 3 ∣ Nat.gcd x (Nat.gcd y z) → ¬ 4 ∣ Nat.gcd x (Nat.gcd y z) →
    ¬ 5 ∣ Nat.gcd x (Nat.gcd y z) → ¬ 7 ∣ Nat.gcd x (Nat.gcd y z) →
    ¬ 11 ∣ Nat.gcd x (Nat.gcd y z) → ¬ 13 ∣ Nat.gcd x (Nat.gcd y z) →
    ¬ 17 ∣ Nat.gcd x (Nat.gcd y z) → ¬ 19 ∣ Nat.gcd x (Nat.gcd y z) →
    ¬ (4 ∣ x ∧ 4 ∣ y ∧ 2 ∣ z) → ¬ (4 ∣ x ∧ 2 ∣ y ∧ 4 ∣ z) → ¬ (2 ∣ x ∧ 4 ∣ y ∧ 4 ∣ z) →
    ¬ (6 ∣ x ∧ 6 ∣ y ∧ 2 ∣ z) →
    Nat.Coprime a b → a ^ x + b ^ y ≠ c ^ z

theorem seis_iff_regular : ExclusaoResidualSeis ↔ ExclusaoResidualRegular := by
  constructor
  · intro h a b c x y z ha hb hc hx hy hz h3 h4 _ _ _ _ _ _ h1 h2 h5 h6 hab
    exact h a b c x y z ha hb hc hx hy hz h3 h4 h1 h2 h5 h6 hab
  · intro h a b c x y z ha hb hc hx hy hz h3 h4 h1 h2 h5 h6 hab heq
    by_cases hd : ∃ d, (d = 5 ∨ d = 7 ∨ d = 11 ∨ d = 13 ∨ d = 17 ∨ d = 19) ∧ d ∣ Nat.gcd x (Nat.gcd y z)
    · obtain ⟨d, hd, hdg⟩ := hd
      obtain ⟨p, hp, hpa, hpb, -⟩ := beal_mdc_regular hd hdg a b c ha hb hc heq
      have h1' : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
      rw [Nat.Coprime.gcd_eq_one hab] at h1'
      exact hp.ne_one (Nat.dvd_one.mp h1')
    · push Not at hd
      exact h a b c x y z ha hb hc hx hy hz h3 h4 (hd 5 (Or.inl rfl)) (hd 7 (by simp))
        (hd 11 (by simp)) (hd 13 (by simp)) (hd 17 (by simp))
        (hd 19 (by simp)) h1 h2 h5 h6 hab heq

/-- **Beal ⟺ residual reduzido** (incondicional, sem pontes). -/
theorem beal_iff_residual_regular : BealConjecture ↔ ExclusaoResidualRegular :=
  beal_iff_residual_seis.trans seis_iff_regular

/-- Instâncias com expoentes distintos: `(5, 10, 15)`, `(7, 14, 21)`, `(11, 22, 33)`, `(13, 26, 39)`,
`(17, 34, 51)`, `(19, 38, 57)`. -/
theorem exemplos_regulares :
    BealFor 5 10 15 ∧ BealFor 7 14 21 ∧ BealFor 11 22 33 ∧ BealFor 13 26 39 ∧
      BealFor 17 34 51 ∧ BealFor 19 38 57 :=
  ⟨beal_expoentes_mult (by simp) (dvd_refl 5) ⟨2, rfl⟩ ⟨3, rfl⟩,
    beal_expoentes_mult (by simp) (dvd_refl 7) ⟨2, rfl⟩ ⟨3, rfl⟩,
    beal_expoentes_mult (by simp) (dvd_refl 11) ⟨2, rfl⟩ ⟨3, rfl⟩,
    beal_expoentes_mult (by simp) (dvd_refl 13) ⟨2, rfl⟩ ⟨3, rfl⟩,
    beal_expoentes_mult (by simp) (dvd_refl 17) ⟨2, rfl⟩ ⟨3, rfl⟩,
    beal_expoentes_mult (by simp) (dvd_refl 19) ⟨2, rfl⟩ ⟨3, rfl⟩⟩

end ATK.BealFermatRegular

#print axioms ATK.BealFermatRegular.beal_igual_cinco
#print axioms ATK.BealFermatRegular.beal_igual_sete
#print axioms ATK.BealFermatRegular.beal_igual_onze
#print axioms ATK.BealFermatRegular.beal_igual_treze
#print axioms ATK.BealFermatRegular.beal_igual_dezessete
#print axioms ATK.BealFermatRegular.beal_igual_dezenove
#print axioms ATK.BealFermatRegular.flt_regulares
#print axioms ATK.BealFermatRegular.beal_expoentes_mult
#print axioms ATK.BealFermatRegular.beal_mdc_regular
#print axioms ATK.BealFermatRegular.seis_iff_regular
#print axioms ATK.BealFermatRegular.beal_iff_residual_regular
#print axioms ATK.BealFermatRegular.exemplos_regulares
