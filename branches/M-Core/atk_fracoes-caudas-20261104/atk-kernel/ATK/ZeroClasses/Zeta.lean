import ATK.ZeroClasses.Symmetry
import ATK.ZeroClasses.Multiplicity
import ATK.ZerosFora
import ATK.XiAnalitica
import ATK.BLJensen
import ATK.TruncamentoZero
import ATK.XiMomentos
import ATK.ZeroCritico

/-!
# ATK-ZERO-CLASSES — especialização à `riemannZeta` da Mathlib

Classes de `ζ`: **triviais** (`s = −2(n+1)`), **não triviais** (`ATK.ZetaSimetria.Z`: zeros com
`0 < Re s < 1`), **críticos** (`Re s = 1/2`) e **fora da reta**. Reutiliza a definição oficial
`RiemannHypothesis`. Tudo incondicional, exceto onde a equivalência com RH é o próprio enunciado.

* **dicotomia** (`dicotomia`): todo zero é trivial ou não trivial, e não ambos;
* **natureza** (`classificacao_natureza`): real puro ⟺ trivial; nenhum imaginário puro; misto ⟺ não
  trivial. Os triviais são reais, de partes real e imaginária racionais, **simples** (`trivial_classes`);
* **posição** (`linhas`): nenhum zero em `Re s ≥ 1` nem em `Re s = 0`; na reta `Re s = −2(n+1)` há
  exatamente um zero; em `Re s = c ≤ 0` fora dos pares negativos, nenhum; zeros com `Re s = c ∈ (0,1)`
  são não triviais com `(Im s)² ≥ 3/4`;
* **multiplicidade e isolamento** (`zeros_isolados`, `sem_acumulacao_zeta`): todo zero de `ζ` tem
  multiplicidade finita e é isolado; **nenhum ponto de `ℂ` acumula zeros** (nem `s = 1`, pelo resíduo);
* **ocupação** (`ocupacao`): as classes trivial, crítica, mista e "parte real racional" **têm zeros**
  (a crítica pelo zero certificado `ATK.ZeroCert.zero_na_linha`, §4f); imaginária pura e real na faixa
  **não têm**; fora da reta e "parte real irracional" ficam em aberto (são ¬RH);
* **existência sem cálculo** (`existe_nao_trivial`): uma segunda prova, estrutural, de que `ζ` tem zero
  não trivial — se `B(w) = Σaₙwⁿ` não tivesse zeros, Hadamard de gênero 0 do kernel (`coef_eq_lim`) daria
  `aₙ = 0` para `n ≥ 1`, contra `a₁ > 0` (`aXi_pos`); daí outra prova de que o eixo de simetria é único
  (`eixo_unico'`; a primeira, via o zero certificado, é `ATK.ZeroCertAplicado.eixo_unico`);
* **simetrias** (`xi_conjEquiv`, `xi_reflZeros`): a camada genérica instancia-se em `ξ` com `c = 1/2`;
  `ζ` é equivariante mas **não** preserva zeros por `s ↦ 1 − s` (`zeta_nao_reflZeros`: `ζ(−2) = 0`,
  `ζ(3) ≠ 0`);
* **aritmética e RH** (`rh_iff_classes`, `nao_rh_iff_aritm`): RH ⟺ todo não trivial é crítico;
  ¬RH ⟺ existe não trivial de parte real irracional ou racional `≠ 1/2`;
* **informação** (`indeterminados_eq`): relativamente a `Kcert` (três regiões que o kernel certifica livres de
  zeros não triviais), a classe dos zeros de localização indeterminada é **exatamente** a dos não triviais.
  A classe muda com `K`: o disco do zero certificado (§4f) já determina um deles.

Nada aqui prova RH.
-/

open Complex ComplexConjugate Set Filter Topology

namespace ATK.ZeroClasses.Zeta

open ATK.ZeroClasses
open ATK.ZetaSimetria (Trivial re_trivial zero_na_faixa zero_trivial_de_re_nao_pos
  mem_Z_iff_nao_trivial im_ne_zero_of_mem_Z espelho_mem_Z)

/-- Zero não trivial: `ζ s = 0` com `0 < Re s < 1`. -/
abbrev NaoTrivial (s : ℂ) : Prop := s ∈ ATK.ZetaSimetria.Z

/-- Zero crítico. -/
def Critico (s : ℂ) : Prop := NaoTrivial s ∧ s.re = 1 / 2

/-- Zero não trivial fora da reta crítica. -/
def ForaCritico (s : ℂ) : Prop := NaoTrivial s ∧ s.re ≠ 1 / 2

/-! ## 1. Dicotomia -/

theorem trivial_zero {s : ℂ} (h : Trivial s) : IsZero riemannZeta s := by
  obtain ⟨n, rfl⟩ := h
  exact riemannZeta_neg_two_mul_nat_add_one n

theorem dicotomia {s : ℂ} (hz : IsZero riemannZeta s) : Trivial s ∨ NaoTrivial s := by
  by_cases ht : Trivial s
  · exact Or.inl ht
  · exact Or.inr ((mem_Z_iff_nao_trivial s).mpr ⟨hz, ht⟩)

theorem dicotomia_exclusiva (s : ℂ) : ¬ (Trivial s ∧ NaoTrivial s) :=
  fun ⟨ht, hn⟩ => absurd hn.2.1 (not_lt.mpr (re_trivial ht).le)

/-! ## 2. Natureza -/

/-- Os zeros triviais: reais puros, partes real e imaginária racionais, à esquerda de `0`, **simples**. -/
theorem trivial_classes {s : ℂ} (h : Trivial s) :
    PureReal riemannZeta s ∧ RatRe riemannZeta s ∧ RatIm riemannZeta s ∧ LeftOf riemannZeta 0 s ∧
      Simples riemannZeta s ∧ analyticOrderAt riemannZeta s = 1 := by
  have hz := trivial_zero h
  obtain ⟨n, rfl⟩ := h
  have hs := ATK.XiAnalitica.zeros_triviais_simples (n + 1) (by omega)
  push_cast at hs
  refine ⟨⟨hz, by simp⟩, ⟨hz, -2 * (n + 1), by simp⟩, ⟨hz, 0, by simp⟩,
    ⟨hz, re_trivial ⟨n, rfl⟩⟩, ⟨hz, hs.1⟩, hs.2⟩

/-- Os não triviais são **mistos**, à direita de `0` e à esquerda de `1`. -/
theorem naoTrivial_classes {s : ℂ} (h : NaoTrivial s) :
    Mixed riemannZeta s ∧ RightOf riemannZeta 0 s ∧ LeftOf riemannZeta 1 s :=
  ⟨⟨h.1, h.2.1.ne', im_ne_zero_of_mem_Z h⟩, ⟨h.1, h.2.1⟩, ⟨h.1, h.2.2⟩⟩

/-- **Classificação da natureza dos zeros de `ζ`.** -/
theorem classificacao_natureza {s : ℂ} (hz : IsZero riemannZeta s) :
    (PureReal riemannZeta s ↔ Trivial s) ∧ ¬ PureImaginary riemannZeta s ∧
      (Mixed riemannZeta s ↔ NaoTrivial s) := by
  rcases dicotomia hz with ht | hn
  · have hr := (trivial_classes ht).1
    refine ⟨⟨fun _ => ht, fun _ => hr⟩, fun hi => (natureza_exclusiva s).1 ⟨hr, hi⟩,
      ⟨fun hm => absurd ⟨hr, hm⟩ (natureza_exclusiva s).2.1,
        fun hn => absurd ⟨ht, hn⟩ (dicotomia_exclusiva s)⟩⟩
  · have hm := (naoTrivial_classes hn).1
    refine ⟨⟨fun hr => absurd ⟨hr, hm⟩ (natureza_exclusiva s).2.1,
        fun ht => absurd ⟨ht, hn⟩ (dicotomia_exclusiva s)⟩,
      fun hi => (natureza_exclusiva s).2.2 ⟨hi, hm⟩, ⟨fun _ => hn, fun _ => hm⟩⟩

theorem sem_imaginarios_puros (s : ℂ) : ¬ PureImaginary riemannZeta s :=
  fun h => (classificacao_natureza h.1).2.1 h

/-! ## 3. Posição -/

theorem sem_zeros_re_ge_one {c : ℝ} (hc : 1 ≤ c) (s : ℂ) : ¬ OnLine riemannZeta c s :=
  fun ⟨hz, he⟩ => riemannZeta_ne_zero_of_one_le_re (he ▸ hc) hz

theorem sem_zeros_re_zero (s : ℂ) : ¬ OnLine riemannZeta 0 s := by
  rintro ⟨hz, he⟩
  rcases dicotomia hz with ht | hn
  · have := re_trivial ht; linarith
  · have := hn.2.1; linarith

/-- Na reta `Re s = −2(n+1)` há **exatamente um** zero. -/
theorem linha_trivial (n : ℕ) :
    {s | OnLine riemannZeta (-2 * ((n : ℝ) + 1)) s} = {(-2 * ((n : ℂ) + 1))} := by
  ext s
  simp only [mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hz, he⟩
    obtain ⟨m, rfl⟩ := zero_trivial_de_re_nao_pos hz (by
      rw [he]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    have hre : (-2 * ((m : ℝ) + 1)) = -2 * ((n : ℝ) + 1) := by simpa using he
    have : (m : ℝ) = n := by linarith
    have hmn : m = n := by exact_mod_cast this
    rw [hmn]
  · rintro rfl
    exact ⟨trivial_zero ⟨n, rfl⟩, by simp⟩

/-- Fora dos pares negativos, nenhuma reta `Re s = c ≤ 0` tem zeros. -/
theorem linha_vazia {c : ℝ} (hc : c ≤ 0) (hpar : ∀ n : ℕ, c ≠ -2 * ((n : ℝ) + 1)) (s : ℂ) :
    ¬ OnLine riemannZeta c s := by
  rintro ⟨hz, he⟩
  obtain ⟨m, rfl⟩ := zero_trivial_de_re_nao_pos hz (he ▸ hc)
  exact hpar m (by rw [← he]; simp)

/-- Zeros com `Re s = c ∈ (0,1)` são não triviais e estão acima da altura `√3/2`. -/
theorem linha_faixa {c : ℝ} (hc : 0 < c) {s : ℂ} (h : OnLine riemannZeta c s) :
    NaoTrivial s ∧ c < 1 ∧ 3 / 4 ≤ s.im ^ 2 := by
  obtain ⟨hz, he⟩ := h
  have hn : NaoTrivial s := by
    rcases dicotomia hz with ht | hn
    · have := re_trivial ht; linarith
    · exact hn
  exact ⟨hn, he ▸ hn.2.2, ATK.ZetaRetangulo.sem_zeros_ate_altura s hn⟩

/-! ## 4. Multiplicidade, isolamento, acumulação -/

theorem zero_ne_one {s : ℂ} (hz : IsZero riemannZeta s) : s ≠ 1 := by
  rintro rfl
  exact riemannZeta_ne_zero_of_one_le_re (by simp) hz

/-- **Todo zero de `ζ` tem multiplicidade finita e é isolado.** -/
theorem zeros_isolados {s : ℂ} (hz : IsZero riemannZeta s) :
    MultFinita riemannZeta s ∧ Isolado riemannZeta s := by
  have hs1 := zero_ne_one hz
  have ha : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have hm : MultFinita riemannZeta s := ⟨hz, ha, ATK.BLJensen.zeta_order_ne_top hs1⟩
  exact ⟨hm, (multFinita_iff_isolado ha hz).mp hm⟩

/-- **Nenhum ponto de `ℂ` acumula zeros de `ζ`** (em `s = 1`, pelo resíduo `(s − 1)ζ(s) → 1`). -/
theorem sem_acumulacao_zeta (z : ℂ) : ¬ Acumulacao riemannZeta z := by
  by_cases h1 : z = 1
  · subst h1
    rw [nao_acumulacao_iff]
    have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) * riemannZeta s ≠ 0 :=
      riemannZeta_residue_one.eventually_ne one_ne_zero
    filter_upwards [hev] with s hs h0
    exact hs (by rw [h0, mul_zero])
  · by_cases hz : riemannZeta z = 0
    · exact isolado_nao_acumulacao (zeros_isolados hz).2
    · intro h
      exact hz (acumulacao_zero (differentiableAt_riemannZeta h1).continuousAt h)

/-! ## 5. Existência de um zero não trivial -/

section Existencia

open ATK.Edrei ATK.Hadamard

theorem passo_sem_zeros {c : ℕ → ℝ} (hnz : ∀ w, ev c w ≠ 0) : ATK.Hadamard.passo c = (c, 0) := by
  have h : ¬ ∃ w, ZeroMin c w := fun ⟨w, hw, _⟩ => hnz w hw
  unfold ATK.Hadamard.passo
  simp [h]

theorem seqH_sem_zeros {c : ℕ → ℝ} (hnz : ∀ w, ev c w ≠ 0) : ∀ k, seqH c k = c
  | 0 => rfl
  | k + 1 => by
    show (ATK.Hadamard.passo (seqH c k)).1 = c
    rw [seqH_sem_zeros hnz k, passo_sem_zeros hnz]

theorem alphaH_sem_zeros {c : ℕ → ℝ} (hnz : ∀ w, ev c w ≠ 0) : alphaH c = fun _ => 0 := by
  funext k
  show (ATK.Hadamard.passo (seqH c k)).2 = 0
  rw [seqH_sem_zeros hnz k, passo_sem_zeros hnz]

theorem prodCoef_zero (a0 : ℝ) : ∀ N n, 1 ≤ n → prodCoef a0 (fun _ => 0) N n = 0
  | 0, n, hn => by
    simp only [prodCoef]
    split_ifs with h
    · omega
    · rfl
  | N + 1, n, hn => by simp only [prodCoef]; rw [prodCoef_zero a0 N n hn]; ring

/-- **Hadamard sem zeros**: uma função inteira `Σcₙwⁿ` de ordem `< 1`, `c₀ > 0`, sem zeros, é constante. -/
theorem sem_zeros_constante {c : ℕ → ℝ} (hc : Inteira c) (h0 : 0 < c 0) {A σ : ℝ} (hA : 0 < A)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hgr : ∀ w, ‖ev c w‖ ≤ A * Real.exp (A * ‖w‖ ^ σ))
    (hnz : ∀ w, ev c w ≠ 0) {n : ℕ} (hn : 1 ≤ n) : c n = 0 := by
  have hz : ZerosNeg c := fun w hw => absurd hw (hnz w)
  have hl := coef_eq_lim hc h0 hz hA hσ0 hσ1 hgr n
  rw [alphaH_sem_zeros hnz] at hl
  have : (fun k => prodCoef (c 0) (fun _ => (0 : ℝ)) k n) = fun _ => 0 :=
    funext fun k => prodCoef_zero _ k n hn
  rw [this] at hl
  exact (tendsto_nhds_unique tendsto_const_nhds hl).symm

/-- `B(w) = Σaₙwⁿ` tem um zero. -/
theorem existe_zero_B : ∃ w, ev ATK.XiTP.aXi w = 0 := by
  by_contra h'
  have h : ∀ w, ev ATK.XiTP.aXi w ≠ 0 := fun w hw => h' ⟨w, hw⟩
  have := sem_zeros_constante ATK.XiTP.inteira_aXi ATK.XiTP.aXi_zero_pos (A := 320) (σ := 3 / 4)
    (by norm_num) (by norm_num) (by norm_num) ATK.XiCresc.crescimento_B h (n := 1) le_rfl
  exact (ATK.XiMom.aXi_pos 1).ne' this

end Existencia

/-- Os zeros de `ξ` são exatamente os zeros não triviais de `ζ`. -/
theorem xi_zero_iff (s : ℂ) : IsZero ATK.BaseRiemannXi.riemannXi s ↔ NaoTrivial s := by
  constructor
  · intro h
    obtain ⟨h0, h1⟩ := ATK.BaseRiemannXi.riemannXi_zero_mem_strip h
    have hs1 : s ≠ 1 := by rintro rfl; simp at h1
    exact ⟨(ATK.BaseRiemannXi.riemannXi_eq_zero_iff h0 hs1).mp h, h0, h1⟩
  · rintro ⟨hz, h0, h1⟩
    have hs1 : s ≠ 1 := by rintro rfl; simp at h1
    exact (ATK.BaseRiemannXi.riemannXi_eq_zero_iff h0 hs1).mpr hz

/-- **Existe um zero não trivial de `ζ`** (incondicional). -/
theorem existe_nao_trivial : ∃ s, NaoTrivial s := by
  obtain ⟨w, hw⟩ := existe_zero_B
  obtain ⟨z, rfl⟩ := ATK.XiCresc.existe_raiz w
  rw [ATK.XiTP.ev_aXi] at hw
  exact ⟨_, (xi_zero_iff _).mp hw⟩

/-- …e um com `Im s > 0`. -/
theorem existe_nao_trivial_im_pos : ∃ s, NaoTrivial s ∧ 0 < s.im := by
  obtain ⟨s, hs⟩ := existe_nao_trivial
  rcases lt_or_gt_of_ne (im_ne_zero_of_mem_Z hs) with h | h
  · refine ⟨conj s, espelho_mem_Z hs, ?_⟩
    simp; linarith
  · exact ⟨s, hs, h⟩

/-- **O eixo de simetria é único** (`κ = 1/2`), com o zero vindo de Hadamard e não do certificado
numérico. -/
theorem eixo_unico' {κ : ℝ}
    (hsim : ∀ ρ ∈ ATK.ZetaSimetria.Z, ATK.TruncamentoZero.refl κ ρ ∈ ATK.ZetaSimetria.Z) : κ = 1 / 2 :=
  ATK.TruncamentoZero.eixo_unico existe_nao_trivial hsim

/-- **A classe crítica não é vazia** (zero certificado perto de `1/2 + 14,1347 i`). -/
theorem existe_critico : ∃ s, Critico s := by
  obtain ⟨ρ, hρ, hre, _⟩ := ATK.ZeroCert.zero_na_linha
  exact ⟨ρ, hρ, hre⟩

/-- **Ocupação das classes**: triviais, críticos, mistos e de parte real racional existem; imaginários
puros e reais na faixa não existem. -/
theorem ocupacao :
    (∃ s, Trivial s ∧ IsZero riemannZeta s) ∧ (∃ s, Critico s) ∧
      (∃ s, Mixed riemannZeta s ∧ RatRe riemannZeta s) ∧ (∀ s, ¬ PureImaginary riemannZeta s) ∧
      (∀ s, NaoTrivial s → ¬ PureReal riemannZeta s) := by
  refine ⟨⟨_, ⟨0, rfl⟩, trivial_zero ⟨0, rfl⟩⟩, existe_critico, ?_, sem_imaginarios_puros,
    fun s hs hr => (natureza_exclusiva s).2.1 ⟨hr, (naoTrivial_classes hs).1⟩⟩
  obtain ⟨s, hs, hre⟩ := existe_critico
  exact ⟨s, (naoTrivial_classes hs).1, hs.1, 1 / 2, by rw [hre]; norm_num⟩

/-! ## 6. Simetrias: a camada genérica em `ξ` -/

theorem zeta_conjEquiv : ConjEquiv riemannZeta := riemannZeta_conj

theorem xi_conjEquiv : ConjEquiv ATK.BaseRiemannXi.riemannXi := ATK.BaseRiemannXi.riemannXi_conj

theorem xi_reflZeros : ReflZeros ATK.BaseRiemannXi.riemannXi (1 / 2) := by
  intro z hz
  have : 2 * (((1 / 2 : ℝ)) : ℂ) - z = 1 - z := by push_cast; ring
  rw [this, ATK.BaseRiemannXi.riemannXi_one_sub, hz]

/-- `ζ` **não** preserva zeros por `s ↦ 1 − s`: `ζ(−2) = 0` e `ζ(3) ≠ 0`. -/
theorem zeta_nao_reflZeros : ¬ ReflZeros riemannZeta (1 / 2) := by
  intro h
  have h2 := h _ (riemannZeta_neg_two_mul_nat_add_one 0)
  have : 2 * (((1 / 2 : ℝ)) : ℂ) - -2 * ((0 : ℕ) + 1) = 3 := by push_cast; ring
  rw [this] at h2
  exact riemannZeta_ne_zero_of_one_le_re (by norm_num) h2

/-- A órbita de um zero não trivial é feita de zeros não triviais. -/
theorem orbita_nao_trivial {s : ℂ} (h : NaoTrivial s) : ∀ w ∈ orbita (1 / 2) s, NaoTrivial w :=
  fun w hw => (xi_zero_iff w).mp (orbita_sub xi_conjEquiv xi_reflZeros ((xi_zero_iff s).mpr h) w hw)

/-- Um zero fora da reta crítica traz **quatro** zeros fora da reta; um zero crítico, **dois**. -/
theorem quarteto_ou_par {s : ℂ} (h : NaoTrivial s) :
    (s.re ≠ 1 / 2 → (orbita (1 / 2) s).card = 4 ∧ ∀ w ∈ orbita (1 / 2) s, ForaCritico w) ∧
      (s.re = 1 / 2 → (orbita (1 / 2) s).card = 2) := by
  have him := im_ne_zero_of_mem_Z h
  refine ⟨fun hre => ?_, fun hre => card_dois_linha hre him⟩
  obtain ⟨h4, hoff⟩ := quarteto_de_zero xi_conjEquiv xi_reflZeros ((xi_zero_iff s).mpr h) hre him
  exact ⟨h4, fun w hw => ⟨orbita_nao_trivial h w hw, (hoff w hw).2⟩⟩

/-! ## 7. Aritmética e RH -/

/-- **RH na linguagem das classes**: todo não trivial está na reta `x = 1/2`. -/
theorem rh_iff_classes : RiemannHypothesis ↔ ∀ s, NaoTrivial s → OnLine riemannZeta (1 / 2) s := by
  constructor
  · intro hrh s hs
    refine ⟨hs.1, hrh s hs.1 ((mem_Z_iff_nao_trivial s).mp hs).2 ?_⟩
    rintro rfl; exact absurd hs.2.2 (by simp)
  · intro h s hz hnt hs1
    exact (h s ((mem_Z_iff_nao_trivial s).mpr ⟨hz, fun ⟨n, hn⟩ => hnt ⟨n, hn⟩⟩)).2

theorem nao_rh_iff_fora : ¬ RiemannHypothesis ↔ ∃ s, ForaCritico s := by
  rw [rh_iff_classes]
  constructor
  · intro h
    by_contra hc
    exact h fun s hs => ⟨hs.1, by by_contra hne; exact hc ⟨s, hs, hne⟩⟩
  · rintro ⟨s, hs, hne⟩ h
    exact hne (h s hs).2

/-- Sob RH, todo não trivial tem parte real racional (`1/2`). -/
theorem rh_ratRe (hrh : RiemannHypothesis) {s : ℂ} (hs : NaoTrivial s) : RatRe riemannZeta s :=
  onLine_ratRe (1 / 2) (by simpa using (rh_iff_classes.mp hrh s hs))

/-- **Um zero não trivial de parte real irracional refutaria RH.** -/
theorem irr_refuta {s : ℂ} (hs : NaoTrivial s) (hi : IrrRe riemannZeta s) : ¬ RiemannHypothesis :=
  fun hrh => ratRe_irrRe_exclusivo s ⟨rh_ratRe hrh hs, hi⟩

/-- **¬RH ⟺ existe não trivial de parte real irracional, ou racional `≠ 1/2`.** -/
theorem nao_rh_iff_aritm :
    ¬ RiemannHypothesis ↔
      ∃ s, NaoTrivial s ∧ (IrrRe riemannZeta s ∨ (RatRe riemannZeta s ∧ s.re ≠ 1 / 2)) := by
  rw [nao_rh_iff_fora]
  constructor
  · rintro ⟨s, hs, hne⟩
    refine ⟨s, hs, ?_⟩
    rcases ratRe_or_irrRe (f := riemannZeta) hs.1 with h | h
    · exact Or.inr ⟨h, hne⟩
    · exact Or.inl h
  · rintro ⟨s, hs, h | ⟨_, hne⟩⟩
    · exact ⟨s, hs, fun he => h.2 ⟨1 / 2, by rw [he]; norm_num⟩⟩
    · exact ⟨s, hs, hne⟩

/-- **RH ⟺ toda reta `Re s = c ≠ 1/2`, `c > 0`, é vazia de zeros.** -/
theorem rh_iff_linhas_vazias :
    RiemannHypothesis ↔ ∀ c : ℝ, 0 < c → c ≠ 1 / 2 → ∀ s, ¬ OnLine riemannZeta c s := by
  rw [rh_iff_classes]
  constructor
  · rintro h c hc hne s ⟨hz, he⟩
    exact hne (he ▸ (h s (linha_faixa hc ⟨hz, he⟩).1).2)
  · intro h s hs
    by_contra hn
    exact h s.re hs.2.1 (fun he => hn ⟨hs.1, he⟩) s ⟨hs.1, rfl⟩

/-! ## 8. Informação incompleta, relativa ao kernel -/

/-- Três regiões em que o kernel **determina** a localização dos zeros: `Re s ≤ 0` (só triviais),
`Re s ≥ 1` (nenhum) e a faixa baixa `(Im s)² < 3/4` (nenhum). Não é a única escolha: as bordas `c(t)` e o
disco do zero certificado também determinam. -/
def Kcert : Set ℂ := {s | s.re ≤ 0 ∨ 1 ≤ s.re ∨ s.im ^ 2 < 3 / 4}

/-- Nos zeros de `Kcert`, a localização é conhecida: são exatamente os triviais. -/
theorem determinados {s : ℂ} (hz : IsZero riemannZeta s) (hK : s ∈ Kcert) : Trivial s := by
  rcases dicotomia hz with ht | hn
  · exact ht
  · exfalso
    rcases hK with h | h | h
    · linarith [hn.2.1]
    · linarith [hn.2.2]
    · linarith [ATK.ZetaRetangulo.sem_zeros_ate_altura s hn]

/-- **A classe "localização indeterminada" é exatamente a dos zeros não triviais.** -/
theorem indeterminados_eq : {s | Indeterminado riemannZeta Kcert s} = {s | NaoTrivial s} := by
  ext s
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hz, hK⟩
    rcases dicotomia hz with ht | hn
    · exact absurd (Or.inl (re_trivial ht).le) hK
    · exact hn
  · intro hn
    refine ⟨hn.1, ?_⟩
    rintro (h | h | h)
    · linarith [hn.2.1]
    · linarith [hn.2.2]
    · linarith [ATK.ZetaRetangulo.sem_zeros_ate_altura s hn]

end ATK.ZeroClasses.Zeta

#print axioms ATK.ZeroClasses.Zeta.trivial_zero
#print axioms ATK.ZeroClasses.Zeta.dicotomia
#print axioms ATK.ZeroClasses.Zeta.dicotomia_exclusiva
#print axioms ATK.ZeroClasses.Zeta.trivial_classes
#print axioms ATK.ZeroClasses.Zeta.naoTrivial_classes
#print axioms ATK.ZeroClasses.Zeta.classificacao_natureza
#print axioms ATK.ZeroClasses.Zeta.sem_imaginarios_puros
#print axioms ATK.ZeroClasses.Zeta.sem_zeros_re_ge_one
#print axioms ATK.ZeroClasses.Zeta.sem_zeros_re_zero
#print axioms ATK.ZeroClasses.Zeta.linha_trivial
#print axioms ATK.ZeroClasses.Zeta.linha_vazia
#print axioms ATK.ZeroClasses.Zeta.linha_faixa
#print axioms ATK.ZeroClasses.Zeta.zero_ne_one
#print axioms ATK.ZeroClasses.Zeta.zeros_isolados
#print axioms ATK.ZeroClasses.Zeta.sem_acumulacao_zeta
#print axioms ATK.ZeroClasses.Zeta.passo_sem_zeros
#print axioms ATK.ZeroClasses.Zeta.seqH_sem_zeros
#print axioms ATK.ZeroClasses.Zeta.alphaH_sem_zeros
#print axioms ATK.ZeroClasses.Zeta.prodCoef_zero
#print axioms ATK.ZeroClasses.Zeta.sem_zeros_constante
#print axioms ATK.ZeroClasses.Zeta.existe_zero_B
#print axioms ATK.ZeroClasses.Zeta.xi_zero_iff
#print axioms ATK.ZeroClasses.Zeta.existe_nao_trivial
#print axioms ATK.ZeroClasses.Zeta.existe_nao_trivial_im_pos
#print axioms ATK.ZeroClasses.Zeta.eixo_unico'
#print axioms ATK.ZeroClasses.Zeta.existe_critico
#print axioms ATK.ZeroClasses.Zeta.ocupacao
#print axioms ATK.ZeroClasses.Zeta.zeta_conjEquiv
#print axioms ATK.ZeroClasses.Zeta.xi_conjEquiv
#print axioms ATK.ZeroClasses.Zeta.xi_reflZeros
#print axioms ATK.ZeroClasses.Zeta.zeta_nao_reflZeros
#print axioms ATK.ZeroClasses.Zeta.orbita_nao_trivial
#print axioms ATK.ZeroClasses.Zeta.quarteto_ou_par
#print axioms ATK.ZeroClasses.Zeta.rh_iff_classes
#print axioms ATK.ZeroClasses.Zeta.nao_rh_iff_fora
#print axioms ATK.ZeroClasses.Zeta.rh_ratRe
#print axioms ATK.ZeroClasses.Zeta.irr_refuta
#print axioms ATK.ZeroClasses.Zeta.nao_rh_iff_aritm
#print axioms ATK.ZeroClasses.Zeta.rh_iff_linhas_vazias
#print axioms ATK.ZeroClasses.Zeta.determinados
#print axioms ATK.ZeroClasses.Zeta.indeterminados_eq
