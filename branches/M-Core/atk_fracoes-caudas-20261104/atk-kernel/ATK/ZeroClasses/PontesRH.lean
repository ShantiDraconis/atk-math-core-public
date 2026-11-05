import ATK.ZeroCritico

/-!
# ATK — As seis "pontes" para RH: o que é teorema, o que é equivalente a RH, o que é mal posto (rodada 102)

Auditoria formal das seis "pontes" propostas para fechar RH a partir da verificação até
`C₀ = 6 000 362 444 943/2`. Tudo aqui usa só a Mathlib e o kernel do ATK (o zero certificado de
`ATK.ZeroCritico`); nenhuma hipótese nomeada de cálculo externo entra.

* **§1, a constante sem `½`.** `c := inf {θ : ζ ≠ 0 em Re s > θ}` (a abscissa sem zeros; `SemZeros θ`).
  Teoremas: `c_le_um` (`c ≤ 1`, Mathlib), `meio_le_c` (`½ ≤ c`, pelo zero certificado perto de
  `½ + 14,1347i`), `semZeros_c` (o ínfimo é atingido), `c_eq_sSup` (`c = sup Re ρ` sobre os zeros não
  triviais) e **`rh_iff_c : RH ⟺ c = ½`**. Provar `c = ½` é provar RH: o que falta é exatamente `c ≤ ½`.
* **§2, ponte 5 (`C₀ → ∞`).** `RHAte T`: todo zero não trivial com `|Im ρ| ≤ T` está na reta.
  `rh_iff_forall`: `RH ⟺ ∀ T, RHAte T`; **`passo_iff_rh`**: para qualquer `δ > 0`, o passo de indução
  `RHAte T → RHAte (T + δ)` (para todo `T`) é equivalente a RH. Não há indução a partir de um `C₀` finito:
  o passo é o problema inteiro.
* **§3, ponte 2 (`s` ⇒ `Re` pontual).** `media_tautologica`: para **quaisquer** números `g₁, …, gₙ` (de
  qualquer origem) e qualquer `b`, a média de `½ + (gᵢ/ḡ − 1) b` é `½` — a "média ½" não depende de `ζ`.
  `gap_novo_derivado`: `9 585/5 777 953 = (71/10 000)·(1 350 000/5 777 953)` é o `s` arredondado vezes a média,
  não um gap medido; `gap_real_ne`: com as bolas da Arb do par (hipóteses), o gap real difere desse valor em
  mais de `8·10⁻⁶`. `reabs_valor`: `½ + (71/10 000 − 1)·3/5 000 = 24 970 213/50 000 000` é uma definição.
* **§4, ponte 6 (toro/esfera).** `theta_valor`: `360(s − 1)/(s + 1) = −397 160/1 119` em `s = 71/10 000`;
  `M_tensao`: a simetria `s ↦ 1 − s` transportada por `M(s) = (s − 1)/(s + 1)` é outra Möbius
  `J(w) = −(w + 1)/(1 − 3w)`, com `M(½) = −⅓` ponto fixo de `J`: a geometria renomeia a equação funcional.
* **§5, ponte 1 (Euler).** `euler_meio_diverge`: `Σ_p p^{−½}` diverge (Mathlib). A forma correta da ponte é a
  abscissa de convergência (ver `ATK.ZeroClasses.PontesRHAbscissa`).
* **§6, ponte 3 (`Λ`).** `Φ`, `H_t`, `ΛdBN` definidos; de Bruijn–Newman (`RH ⟺ Λ ≤ 0`), Rodgers–Tao (`Λ ≥ 0`) e
  Platt–Trudgian (`Λ ≤ 1/5`) como hipóteses nomeadas (publicadas); `rh_iff_lambda_zero`: com as duas
  primeiras, `RH ⟺ Λ = 0`. Falta `Λ ≤ 0`, que é RH.
* **§7, ponte 4 (Hilbert–Pólya).** `rh_of_hilbertPolya`: um operador simétrico cujos autovalores incluem
  `−i(ρ − ½)` para todo zero não trivial dá RH (autovalores de operadores simétricos são reais).
  Nenhum operador assim é conhecido.

Classificação: **reformulação** (§1, §2, §5–§7) e **auditoria** (§3, §4). Nada aqui prova ou refuta RH;
RH continua `OPEN_MATH`.
-/

open Complex Set Filter
open scoped InnerProductSpace Real

namespace ATK.ZeroClasses.PontesRH

open ATK.ZetaSimetria

/-! ## 0. Zeros não triviais -/

/-- **RH na forma `Z`**: todo zero da faixa aberta está na reta. -/
theorem rh_iff_Z : RiemannHypothesis ↔ ∀ ρ ∈ Z, ρ.re = 1 / 2 := by
  constructor
  · intro hRH ρ hρ
    refine hRH ρ hρ.1 (fun ht => absurd (re_trivial ht) (not_lt.mpr hρ.2.1.le)) ?_
    rintro rfl
    exact absurd hρ.2.2 (by simp)
  · intro h s hz htriv _
    exact h s ((mem_Z_iff_nao_trivial s).mpr ⟨hz, htriv⟩)

/-! ## 1. A abscissa sem zeros `c`, definida sem `½` -/

/-- `ζ` não se anula em `Re s > θ`. -/
def SemZeros (θ : ℝ) : Prop := ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

theorem semZeros_mono {θ θ' : ℝ} (h : θ ≤ θ') (hθ : SemZeros θ) : SemZeros θ' :=
  fun s hs => hθ s (lt_of_le_of_lt h hs)

/-- `ζ ≠ 0` em `Re s > 1` (Mathlib). -/
theorem semZeros_um : SemZeros 1 := fun _ hs => riemannZeta_ne_zero_of_one_le_re hs.le

/-- Um zero na reta, certificado no kernel (`ATK.ZeroCert.zero_na_linha`, perto de `½ + 14,1347i`). -/
theorem existe_zero_meio : ∃ ρ : ℂ, ρ ∈ Z ∧ ρ.re = 1 / 2 := by
  obtain ⟨ρ, hρ, hre, -⟩ := ATK.ZeroCert.zero_na_linha
  exact ⟨ρ, hρ, hre⟩

theorem meio_le_of_semZeros {θ : ℝ} (h : SemZeros θ) : 1 / 2 ≤ θ := by
  obtain ⟨ρ, hρ, hre⟩ := existe_zero_meio
  by_contra hlt
  rw [not_le] at hlt
  exact h ρ (by rw [hre]; exact hlt) hρ.1

/-- **A abscissa sem zeros**: `c = inf {θ : ζ ≠ 0 em Re s > θ}` (sem `½` na definição). -/
noncomputable def c : ℝ := sInf {θ : ℝ | SemZeros θ}

theorem bdd : BddBelow {θ : ℝ | SemZeros θ} := ⟨1 / 2, fun _ hθ => meio_le_of_semZeros hθ⟩

theorem nonempty : ({θ : ℝ | SemZeros θ}).Nonempty := ⟨1, semZeros_um⟩

/-- `c ≤ 1`. -/
theorem c_le_um : c ≤ 1 := csInf_le bdd semZeros_um

/-- `½ ≤ c` (incondicional: há um zero na reta). -/
theorem meio_le_c : 1 / 2 ≤ c := le_csInf nonempty fun _ hθ => meio_le_of_semZeros hθ

/-- O ínfimo é atingido: `ζ ≠ 0` em `Re s > c`. -/
theorem semZeros_c : SemZeros c := by
  intro s hs
  obtain ⟨θ, hθ, hθs⟩ := exists_lt_of_csInf_lt nonempty hs
  exact hθ s hθs

theorem semZeros_iff (θ : ℝ) : SemZeros θ ↔ c ≤ θ :=
  ⟨fun h => csInf_le bdd h, fun h => semZeros_mono h semZeros_c⟩

/-- `SemZeros ½ ⟺ RH`. -/
theorem semZeros_meio_iff_rh : SemZeros (1 / 2) ↔ RiemannHypothesis := by
  constructor
  · intro h
    exact ATK.BaezDuarteBridge.riemannHypothesis_of_strip fun s hs _ => h s hs
  · intro hRH s hs hz
    have hre1 : s.re < 1 := by
      by_contra h1
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h1) hz
    have hZ : s ∈ Z := ⟨hz, by linarith, hre1⟩
    have := (rh_iff_Z.mp hRH) s hZ
    linarith

/-- **RH ⟺ `c = ½`.** -/
theorem rh_iff_c : RiemannHypothesis ↔ c = 1 / 2 := by
  rw [← semZeros_meio_iff_rh, semZeros_iff]
  exact ⟨fun h => le_antisymm h meio_le_c, fun h => h.le⟩

/-- **RH ⟺ `c ≤ ½`**: o único passo que falta. -/
theorem rh_iff_c_le : RiemannHypothesis ↔ c ≤ 1 / 2 := by
  rw [← semZeros_meio_iff_rh, semZeros_iff]

/-- `c` é o supremo das partes reais dos zeros não triviais. -/
theorem c_eq_sSup : c = sSup (Complex.re '' Z) := by
  obtain ⟨ρ₀, hρ₀, hre₀⟩ := existe_zero_meio
  have hne : (Complex.re '' Z).Nonempty := ⟨ρ₀.re, ρ₀, hρ₀, rfl⟩
  have hbdd : BddAbove (Complex.re '' Z) := ⟨1, by rintro _ ⟨ρ, hρ, rfl⟩; exact hρ.2.2.le⟩
  have hsup : 1 / 2 ≤ sSup (Complex.re '' Z) := hre₀ ▸ le_csSup hbdd ⟨ρ₀, hρ₀, rfl⟩
  apply le_antisymm
  · rw [← semZeros_iff]
    intro s hs hz
    by_cases h1 : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re h1 hz
    · have hZ : s ∈ Z := ⟨hz, by linarith, not_le.mp h1⟩
      exact absurd (le_csSup hbdd ⟨s, hZ, rfl⟩) (not_le.mpr hs)
  · refine csSup_le hne ?_
    rintro _ ⟨ρ, hρ, rfl⟩
    by_contra hlt
    exact semZeros_c ρ (not_le.mp hlt) hρ.1

/-! ## 2. Ponte 5: `C₀ → ∞` -/

/-- **RH até a altura `T`**: todo zero não trivial com `|Im ρ| ≤ T` está na reta. -/
def RHAte (T : ℝ) : Prop := ∀ ρ ∈ Z, |ρ.im| ≤ T → ρ.re = 1 / 2

theorem rh_iff_forall : RiemannHypothesis ↔ ∀ T, RHAte T := by
  rw [rh_iff_Z]
  exact ⟨fun h _ ρ hρ _ => h ρ hρ, fun h ρ hρ => h |ρ.im| ρ hρ le_rfl⟩

theorem RHAte.mono {T T' : ℝ} (h : T ≤ T') (hT' : RHAte T') : RHAte T :=
  fun ρ hρ hT => hT' ρ hρ (hT.trans h)

theorem rhAte_neg {T : ℝ} (hT : T < 0) : RHAte T :=
  fun _ _ h => absurd ((abs_nonneg _).trans h) (not_le.mpr hT)

/-- **O passo de indução é RH**: para qualquer `δ > 0`, `(∀ T, RHAte T → RHAte (T + δ)) ⟺ RH`. Nenhuma
verificação até um `C₀` finito, por maior que seja, fornece o passo. -/
theorem passo_iff_rh {δ : ℝ} (hδ : 0 < δ) :
    (∀ T, RHAte T → RHAte (T + δ)) ↔ RiemannHypothesis := by
  rw [rh_iff_forall]
  constructor
  · intro hstep T
    have hn : ∀ n : ℕ, RHAte (-1 + n * δ) := by
      intro n
      induction n with
      | zero => simpa using rhAte_neg (T := -1) (by norm_num)
      | succ n ih =>
        have h := hstep _ ih
        have e : -1 + (n : ℝ) * δ + δ = -1 + ((n + 1 : ℕ) : ℝ) * δ := by push_cast; ring
        rw [e] at h
        exact h
    obtain ⟨n, hn'⟩ := exists_nat_gt ((T + 1) / δ)
    rw [div_lt_iff₀ hδ] at hn'
    exact RHAte.mono (by linarith) (hn n)
  · intro h T _
    exact h (T + δ)

/-! ## 3. Ponte 2: estatística de `s` não dá `Re` pontual -/

/-- **A "média ½" é tautológica**: para quaisquer números `g₁, …, gₙ` com soma não nula e qualquer `b`,
a média de `½ + (gᵢ/ḡ − 1) b`, com `ḡ` a média dos `gᵢ`, é `½`. Não depende de `ζ` nem dos zeros. -/
theorem media_tautologica {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ) (hg : (∑ i, g i) ≠ 0) (b : ℝ) :
    (∑ i, (1 / 2 + (g i / ((∑ j, g j) / n) - 1) * b)) / n = 1 / 2 := by
  set S := ∑ j, g j with hS
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have key : ∑ i, (g i / (S / n) - 1) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← hS]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
    ring
  have e : ∑ i, (1 / 2 + (g i / (S / n) - 1) * b) = n / 2 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, key, zero_mul, add_zero]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [e]
  field_simp

/-- O "gap novo" `9 585/5 777 953` é `s = 71/10 000` (arredondado) vezes a média
`1 350 000/5 777 953 = 5 400 000/23 111 812`: é derivado de `s`, não medido. -/
theorem gap_novo_derivado : (9585 : ℚ) / 5777953 = 71 / 10000 * (1350000 / 5777953) ∧
    (1350000 : ℚ) / 5777953 = 5400000 / 23111812 := by
  constructor <;> norm_num

/-- `Re_abs` em `s = 71/10 000`, `b = 3/5 000`: uma definição, não a parte real de um zero. -/
theorem reabs_valor : (1 / 2 : ℚ) + (71 / 10000 - 1) * (3 / 5000) = 24970213 / 50000000 := by
  norm_num

/-- **O gap real do par não é `9 585/5 777 953`**: com as bolas da Arb de `par_mais_fragil_continuacao4`
(hipóteses), a diferença passa de `8·10⁻⁶`. -/
theorem gap_real_ne {γ₁ γ₂ : ℝ}
    (h₁ : |γ₁ - 300018051927946511944262498325 / 10 ^ 17| ≤ 285 / 10 ^ 20)
    (h₂ : |γ₂ - 300018051927946678691400506282 / 10 ^ 17| ≤ 449 / 10 ^ 20) :
    8 / 10 ^ 6 < (γ₂ - γ₁) - 9585 / 5777953 := by
  rw [abs_le] at h₁ h₂
  obtain ⟨a1, b1⟩ := h₁
  obtain ⟨a2, b2⟩ := h₂
  norm_num at a1 b1 a2 b2 ⊢
  linarith

/-! ## 4. Ponte 6: a geometria só renomeia -/

/-- O ângulo `360(s − 1)/(s + 1)` em `s = 71/10 000`. -/
theorem theta_valor : (360 : ℚ) * (71 / 10000 - 1) / (71 / 10000 + 1) = -397160 / 1119 := by
  norm_num

/-- A transformação de Möbius do "toro/esfera". -/
noncomputable def M (s : ℂ) : ℂ := (s - 1) / (s + 1)

/-- A simetria `s ↦ 1 − s` vista do outro lado de `M`. -/
noncomputable def J (w : ℂ) : ℂ := -(w + 1) / (1 - 3 * w)

/-- **`M` conjuga `s ↦ 1 − s` em `J`**: a equação funcional é "preservada" por qualquer bijeção, por
conjugação; não há conteúdo novo. -/
theorem M_tensao {s : ℂ} (h1 : s + 1 ≠ 0) (h2 : 2 - s ≠ 0) : M (1 - s) = J (M s) := by
  unfold M J
  have e1 : (1 : ℂ) - s + 1 = 2 - s := by ring
  have e2 : (1 : ℂ) - 3 * ((s - 1) / (s + 1)) = 2 * (2 - s) / (s + 1) := by
    field_simp
    ring
  have e3 : (s - 1) / (s + 1) + 1 = 2 * s / (s + 1) := by
    field_simp
    ring
  rw [e1, e2, e3]
  field_simp
  ring

/-- O centro vai para o ponto fixo de `J`. -/
theorem M_meio : M (1 / 2) = -1 / 3 := by
  unfold M
  norm_num

theorem J_fixo : J (-1 / 3) = -1 / 3 := by
  unfold J
  norm_num

/-! ## 5. Ponte 1: o produto de Euler em `½` -/

/-- **`Σ_p p^{−½}` diverge** (Mathlib: `Σ_p p^r < ∞ ⟺ r < −1`). -/
theorem euler_meio_diverge : ¬ Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(1 / 2 : ℝ))) := by
  rw [Nat.Primes.summable_rpow]
  norm_num

/-! ## 6. Ponte 3: a constante de de Bruijn–Newman -/

/-- `Φ(u) = Σ_{n ≥ 1} (2π²n⁴e^{9u} − 3πn²e^{5u}) e^{−πn²e^{4u}}`. -/
noncomputable def Φ (u : ℝ) : ℝ :=
  ∑' n : ℕ, (2 * π ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u) -
    3 * π * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u)) * Real.exp (-(π * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u)))

/-- `H_t(z) = ∫₀^∞ e^{t u²} Φ(u) cos(z u) du`. -/
noncomputable def H (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), ((Real.exp (t * u ^ 2) * Φ u : ℝ) : ℂ) * Complex.cos (z * u)

/-- `H_t` só tem zeros reais. -/
def ZerosReais (t : ℝ) : Prop := ∀ z : ℂ, H t z = 0 → z.im = 0

/-- **A constante de de Bruijn–Newman** `Λ = inf {t : H_t só tem zeros reais}`. -/
noncomputable def ΛdBN : ℝ := sInf {t : ℝ | ZerosReais t}

/-- Ponte (de Bruijn 1950, Newman 1976; publicada, não formalizada): `RH ⟺ Λ ≤ 0`. -/
def PonteDeBruijnNewman : Prop := RiemannHypothesis ↔ ΛdBN ≤ 0

/-- Ponte (Rodgers–Tao 2020; publicada, não formalizada): `Λ ≥ 0`. -/
def PonteRodgersTao : Prop := 0 ≤ ΛdBN

/-- Ponte (Platt–Trudgian 2021; publicada, não formalizada): `Λ ≤ 1/5`. -/
def PontePlattTrudgianLambda : Prop := ΛdBN ≤ 1 / 5

/-- **Com de Bruijn–Newman e Rodgers–Tao, `RH ⟺ Λ = 0`.** O que falta é `Λ ≤ 0`, que é RH. -/
theorem rh_iff_lambda_zero (h1 : PonteDeBruijnNewman) (h2 : PonteRodgersTao) :
    RiemannHypothesis ↔ ΛdBN = 0 :=
  (show RiemannHypothesis ↔ ΛdBN ≤ 0 from h1).trans ⟨fun h => le_antisymm h h2, fun h => h.le⟩

/-- Com as três pontes, `0 ≤ Λ ≤ 1/5`, e RH é a cota superior `Λ ≤ 0`. -/
theorem lambda_entre (h2 : PonteRodgersTao) (h3 : PontePlattTrudgianLambda) :
    0 ≤ ΛdBN ∧ ΛdBN ≤ 1 / 5 := ⟨h2, h3⟩

/-! ## 7. Ponte 4: Hilbert–Pólya -/

/-- **Hilbert–Pólya (forma de autovalores)**: um operador simétrico num espaço com produto interno cujos
autovalores incluem `−i(ρ − ½)` para todo zero não trivial `ρ`. -/
def HilbertPolya : Prop :=
  ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (T : E →ₗ[ℂ] E),
    (∀ u v : E, ⟪T u, v⟫_ℂ = ⟪u, T v⟫_ℂ) ∧
      ∀ ρ ∈ Z, ∃ v : E, v ≠ 0 ∧ T v = (-I * (ρ - 1 / 2)) • v

/-- Autovalores de um operador simétrico são reais. -/
theorem autovalor_real {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {T : E →ₗ[ℂ] E}
    (hT : ∀ u v : E, ⟪T u, v⟫_ℂ = ⟪u, T v⟫_ℂ) {v : E} (hv : v ≠ 0) {μ : ℂ} (hμ : T v = μ • v) :
    μ.im = 0 := by
  have h := hT v v
  rw [hμ, inner_smul_left, inner_smul_right] at h
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv
  have h' : (starRingEnd ℂ) μ = μ := mul_right_cancel₀ hvv h
  have := congrArg Complex.im h'
  rw [Complex.conj_im] at this
  linarith

/-- **Hilbert–Pólya ⟹ RH.** -/
theorem rh_of_hilbertPolya : HilbertPolya → RiemannHypothesis := by
  rintro ⟨E, _, _, T, hT, hρ⟩
  rw [rh_iff_Z]
  intro ρ hρZ
  obtain ⟨v, hv, hTv⟩ := hρ ρ hρZ
  have him := autovalor_real hT hv hTv
  have e : (-I * (ρ - 1 / 2)).im = -(ρ.re - 1 / 2) := by simp
  rw [e] at him
  linarith

/-! ## 8. O estado -/

/-- **O estado das seis pontes**, numa linha. -/
theorem estado :
    (RiemannHypothesis ↔ c = 1 / 2) ∧ (1 / 2 ≤ c ∧ c ≤ 1) ∧
      (RiemannHypothesis ↔ ∀ T, RHAte T) ∧
      (∀ δ : ℝ, 0 < δ → ((∀ T, RHAte T → RHAte (T + δ)) ↔ RiemannHypothesis)) ∧
      (HilbertPolya → RiemannHypothesis) ∧
      (PonteDeBruijnNewman → PonteRodgersTao → (RiemannHypothesis ↔ ΛdBN = 0)) :=
  ⟨rh_iff_c, ⟨meio_le_c, c_le_um⟩, rh_iff_forall, fun _ hδ => passo_iff_rh hδ, rh_of_hilbertPolya,
    rh_iff_lambda_zero⟩

end ATK.ZeroClasses.PontesRH

#print axioms ATK.ZeroClasses.PontesRH.rh_iff_Z
#print axioms ATK.ZeroClasses.PontesRH.semZeros_mono
#print axioms ATK.ZeroClasses.PontesRH.semZeros_um
#print axioms ATK.ZeroClasses.PontesRH.existe_zero_meio
#print axioms ATK.ZeroClasses.PontesRH.meio_le_of_semZeros
#print axioms ATK.ZeroClasses.PontesRH.bdd
#print axioms ATK.ZeroClasses.PontesRH.nonempty
#print axioms ATK.ZeroClasses.PontesRH.c_le_um
#print axioms ATK.ZeroClasses.PontesRH.meio_le_c
#print axioms ATK.ZeroClasses.PontesRH.semZeros_c
#print axioms ATK.ZeroClasses.PontesRH.semZeros_iff
#print axioms ATK.ZeroClasses.PontesRH.semZeros_meio_iff_rh
#print axioms ATK.ZeroClasses.PontesRH.rh_iff_c
#print axioms ATK.ZeroClasses.PontesRH.rh_iff_c_le
#print axioms ATK.ZeroClasses.PontesRH.c_eq_sSup
#print axioms ATK.ZeroClasses.PontesRH.rh_iff_forall
#print axioms ATK.ZeroClasses.PontesRH.RHAte.mono
#print axioms ATK.ZeroClasses.PontesRH.rhAte_neg
#print axioms ATK.ZeroClasses.PontesRH.passo_iff_rh
#print axioms ATK.ZeroClasses.PontesRH.media_tautologica
#print axioms ATK.ZeroClasses.PontesRH.gap_novo_derivado
#print axioms ATK.ZeroClasses.PontesRH.reabs_valor
#print axioms ATK.ZeroClasses.PontesRH.gap_real_ne
#print axioms ATK.ZeroClasses.PontesRH.theta_valor
#print axioms ATK.ZeroClasses.PontesRH.M_tensao
#print axioms ATK.ZeroClasses.PontesRH.M_meio
#print axioms ATK.ZeroClasses.PontesRH.J_fixo
#print axioms ATK.ZeroClasses.PontesRH.euler_meio_diverge
#print axioms ATK.ZeroClasses.PontesRH.rh_iff_lambda_zero
#print axioms ATK.ZeroClasses.PontesRH.lambda_entre
#print axioms ATK.ZeroClasses.PontesRH.autovalor_real
#print axioms ATK.ZeroClasses.PontesRH.rh_of_hilbertPolya
#print axioms ATK.ZeroClasses.PontesRH.estado
