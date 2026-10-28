import ATK.ZeroClasses.Hipotetico
import ATK.ZerosFora
import ATK.BLProva
import ATK.ZeroIncognito

/-!
# ATK-ZERO-CLASSES — o mundo com zeros fora da linha: a linha não cai, e os zeros fora a seguram

No universo hipotético (`HFora`), um zero fora da linha **refuta o enunciado universal** RH, mas **não destrói
a linha**. O que o kernel prova, sem hipótese salvo onde indicado:

* **a linha sobrevive** (`linha_sobrevive`, `coexistencia`): em qualquer mundo a linha tem zeros (o zero
  certificado), e sob `HFora` linha e fora **coexistem**;
* **a linha é o espelho** (`linha_espelho`): é exatamente o conjunto fixo da torção `s ↦ 1 − s̄`, que leva
  cada zero fora em outro zero fora, distinto; **o ponto médio** de cada par está na linha (`ponto_medio`);
* **os zeros fora fixam o eixo** (`fora_fixa_eixo`): se o conjunto dos zeros fora da linha é não vazio e
  simétrico em torno de `Re s = κ`, então `κ = 1/2` — **só os zeros fora já determinam a linha**;
* **equilíbrio exato** (`equilibrio`, `centro_fora`): em toda altura `T`, os desvios `β − 1/2` dos zeros fora
  somam **exatamente zero**, e a média das suas partes reais é **exatamente `1/2`**; as contagens à direita de
  `1/2 + δ` e à esquerda de `1/2 − δ` são iguais (`contagem_espelhada`);
* **esparsidade** (`esparsidade`, Bohr–Landau, incondicional): para cada `δ > 0`, até a altura `T` há no
  máximo `C·T` zeros a distância `> δ` da linha; com `N(T)/T → ∞` (B10) a proporção deles tende a zero
  (`quase_todos_perto`): **a linha segura quase todos os zeros**, em qualquer mundo;
* **a dicotomia do mundo** (`dicotomia_mundo`): os zeros fora são finitos — e então, acima de uma altura,
  **todos** os zeros estão na linha (`rh_acima`) — ou infinitos, em alturas arbitrariamente grandes.

O que **não** está aqui: que esse mundo exista (é `¬RH`, `OPEN_MATH`), nem que a linha "dependa" dos zeros fora
— ela é fixada pela equação funcional; os zeros fora, se existirem, são obrigados a equilibrar-se em torno dela.
-/

open Complex ComplexConjugate Set Filter Topology

namespace ATK.ZeroClasses.MundoFora

open ATK.ZeroClasses ATK.ZeroClasses.Zeta ATK.ZeroClasses.Hipotetico
open ATK.ZetaSimetria (torcao torcao_mem_Z re_torcao torcao_fixo_iff)

/-- A linha crítica (os zeros críticos). -/
def Linha : Set ℂ := {s | Critico s}

/-- Os zeros fora da linha. -/
def ForaSet : Set ℂ := {s | ForaCritico s}

theorem foraSet_eq : ForaSet = ATK.ZerosFora.Fora := by
  ext s; rfl

/-- **A linha sobrevive** — em qualquer mundo, com ou sem `H_fora`. -/
theorem linha_sobrevive : Linha.Nonempty := existe_critico

/-- **Coexistência**: sob `H_fora`, linha e fora estão ambas ocupadas. -/
theorem coexistencia (H : HFora) : Linha.Nonempty ∧ ForaSet.Nonempty :=
  ⟨linha_sobrevive, hFora_iff_fora.mp H⟩

theorem torcao_fora {ρ : ℂ} (h : ForaCritico ρ) : ForaCritico (torcao ρ) :=
  ⟨torcao_mem_Z h.1, by rw [re_torcao]; intro he; exact h.2 (by linarith)⟩

/-- **A linha é o espelho**: o conjunto fixo da torção é a linha, e a torção leva cada zero fora em outro
zero fora, distinto. -/
theorem linha_espelho :
    (∀ s, torcao s = s ↔ s.re = 1 / 2) ∧ ∀ ρ ∈ ForaSet, torcao ρ ∈ ForaSet ∧ torcao ρ ≠ ρ :=
  ⟨torcao_fixo_iff, fun ρ h => ⟨torcao_fora h, fun he => h.2 ((torcao_fixo_iff ρ).mp he)⟩⟩

/-- **Ponto médio na linha**: `(ρ + (1 − ρ̄))/2 = 1/2 + i·Im ρ`. -/
theorem ponto_medio (ρ : ℂ) : ((ρ + torcao ρ) / 2).re = 1 / 2 ∧ ((ρ + torcao ρ) / 2).im = ρ.im := by
  unfold torcao
  constructor <;> simp

/-- **Os zeros fora fixam o eixo**: não vazio e simétrico em torno de `Re s = κ` ⇒ `κ = 1/2`. -/
theorem fora_fixa_eixo {κ : ℝ} (hne : ForaSet.Nonempty)
    (hsim : ∀ ρ ∈ ForaSet, ATK.TruncamentoZero.refl κ ρ ∈ ForaSet) : κ = 1 / 2 := by
  obtain ⟨ρ, hρ⟩ := hne
  have htr : ∀ s ∈ ForaSet, s + ((1 - 2 * κ : ℝ) : ℂ) ∈ ForaSet := by
    intro s hs
    have h := torcao_fora (hsim s hs)
    have e : torcao (ATK.TruncamentoZero.refl κ s) = s + ((1 - 2 * κ : ℝ) : ℂ) := by
      unfold torcao ATK.TruncamentoZero.refl
      apply Complex.ext <;> simp; ring
    rw [e] at h
    exact h
  have hn : ∀ n : ℕ, ρ + (((n : ℝ) * (1 - 2 * κ) : ℝ) : ℂ) ∈ ForaSet := by
    intro n
    induction n with
    | zero => simpa using hρ
    | succ n ih =>
      have := htr _ ih
      convert this using 1
      push_cast; ring
  by_contra hκ
  have hc : 1 - 2 * κ ≠ 0 := by intro h; apply hκ; linarith
  have hpos : 0 < |1 - 2 * κ| := abs_pos.mpr hc
  obtain ⟨n, hnbig⟩ := exists_nat_gt (1 / |1 - 2 * κ|)
  have habs : 1 < (n : ℝ) * |1 - 2 * κ| := by rwa [div_lt_iff₀ hpos] at hnbig
  obtain ⟨⟨-, h0, h1⟩, -⟩ := hn n
  obtain ⟨⟨-, r0, r1⟩, -⟩ := hρ
  have hre : (ρ + (((n : ℝ) * (1 - 2 * κ) : ℝ) : ℂ)).re = ρ.re + n * (1 - 2 * κ) := by simp
  rw [hre] at h0 h1
  rcases lt_or_gt_of_ne hc with hneg | hpos'
  · rw [abs_of_neg hneg] at habs; nlinarith
  · rw [abs_of_pos hpos'] at habs; nlinarith

/-! ## Equilíbrio -/

open ATK.ZeroIncognito (F)

/-- Os zeros fora da linha com `0 < Im ρ ≤ T`. -/
noncomputable def Ffora (T : ℝ) : Finset ℂ := open Classical in (F T).filter fun ρ => ρ.re ≠ 1 / 2

/-- **Equilíbrio exato**: `Σ_{ρ fora, 0 < γ ≤ T} (β − 1/2) = 0`, para todo `T`. -/
theorem equilibrio (T : ℝ) : ∑ ρ ∈ Ffora T, (ρ.re - 1 / 2) = 0 := by
  classical
  have h := ATK.ZeroIncognito.soma_desvio_meio T
  rw [← Finset.sum_filter_ne_zero] at h
  have e : (F T).filter (fun ρ => ρ.re - 1 / 2 ≠ 0) = Ffora T := by
    unfold Ffora
    congr 1
    funext ρ
    simp only [ne_eq, sub_eq_zero]
  rw [e] at h
  exact h

/-- **O centro dos zeros fora é exatamente `1/2`** (em toda altura em que há algum). -/
theorem centro_fora (T : ℝ) (hne : (Ffora T).Nonempty) :
    (∑ ρ ∈ Ffora T, ρ.re) / (Ffora T).card = 1 / 2 := by
  have hc : (0 : ℝ) < (Ffora T).card := by exact_mod_cast Finset.card_pos.mpr hne
  have h := equilibrio T
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h
  rw [div_eq_iff hc.ne']
  linarith

/-- **Contagem espelhada**: tantos zeros à direita de `1/2 + δ` quanto à esquerda de `1/2 − δ`. -/
theorem contagem_espelhada (δ T : ℝ) :
    (ATK.BohrLandau.direita (1 / 2 + δ) T).ncard = (ATK.BohrLandau.esquerda (1 / 2 - δ) T).ncard :=
  ATK.BohrLandau.simetria_contagem δ T

/-! ## Esparsidade -/

/-- **Bohr–Landau (incondicional)**: a distância `> δ` da linha há no máximo `C·T` zeros até a altura `T`. -/
theorem esparsidade (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ T : ℝ, 2 ≤ T →
      ((ATK.BohrLandau.direita (1 / 2 + δ) T).ncard : ℝ) +
        (ATK.BohrLandau.esquerda (1 / 2 - δ) T).ncard ≤ C * T :=
  ATK.BLProva.fora_da_faixa δ hδ

/-- **Quase todos os zeros perto da linha**, condicional só a `N(T)/T → ∞` (B10). -/
theorem quase_todos_perto (hN : ATK.BohrLandau.CrescimentoN) : ATK.BohrLandau.Densidade :=
  ATK.BLProva.densidade_de_crescimento hN

/-! ## A dicotomia do mundo -/

/-- **Finitos ou infinitos**: os zeros fora são finitos (todos abaixo de uma altura) ou aparecem em alturas
arbitrariamente grandes. -/
theorem dicotomia_mundo :
    (ForaSet.Finite ∧ ∃ T : ℝ, ∀ ρ ∈ ForaSet, |ρ.im| ≤ T) ∨
      (ForaSet.Infinite ∧ ∀ T : ℝ, ∃ ρ ∈ ForaSet, T < |ρ.im|) := by
  rw [foraSet_eq]
  by_cases hf : ATK.ZerosFora.Fora.Finite
  · exact Or.inl ⟨hf, let ⟨T, hT⟩ := ATK.ZerosFora.finitos_iff.mp hf; ⟨T, fun ρ hρ => hT hρ⟩⟩
  · exact Or.inr ⟨hf, ATK.ZerosFora.infinitos_iff.mp hf⟩

/-- **Se os zeros fora são finitos, acima de uma altura todos os zeros estão na linha.** -/
theorem rh_acima (hf : ForaSet.Finite) :
    ∃ T : ℝ, ∀ s, NaoTrivial s → T < |s.im| → s.re = 1 / 2 := by
  rw [foraSet_eq] at hf
  obtain ⟨T, hT⟩ := ATK.ZerosFora.finitos_iff.mp hf
  refine ⟨T, fun s hs hT' => ?_⟩
  by_contra hne
  have := hT (show s ∈ ATK.ZerosFora.Fora from ⟨hs, hne⟩)
  simp only [mem_ofPred_eq] at this
  linarith

/-- Sob `H_fora`, com finitos zeros fora, o mundo é "RH acima de uma altura e falsa abaixo". -/
theorem mundo_finito (H : HFora) (hf : ForaSet.Finite) :
    ¬ RiemannHypothesis ∧ ∃ T : ℝ, ∀ s, NaoTrivial s → T < |s.im| → s.re = 1 / 2 :=
  ⟨hFora_iff.mp H, rh_acima hf⟩

end ATK.ZeroClasses.MundoFora

#print axioms ATK.ZeroClasses.MundoFora.foraSet_eq
#print axioms ATK.ZeroClasses.MundoFora.linha_sobrevive
#print axioms ATK.ZeroClasses.MundoFora.coexistencia
#print axioms ATK.ZeroClasses.MundoFora.torcao_fora
#print axioms ATK.ZeroClasses.MundoFora.linha_espelho
#print axioms ATK.ZeroClasses.MundoFora.ponto_medio
#print axioms ATK.ZeroClasses.MundoFora.fora_fixa_eixo
#print axioms ATK.ZeroClasses.MundoFora.equilibrio
#print axioms ATK.ZeroClasses.MundoFora.centro_fora
#print axioms ATK.ZeroClasses.MundoFora.contagem_espelhada
#print axioms ATK.ZeroClasses.MundoFora.esparsidade
#print axioms ATK.ZeroClasses.MundoFora.quase_todos_perto
#print axioms ATK.ZeroClasses.MundoFora.dicotomia_mundo
#print axioms ATK.ZeroClasses.MundoFora.rh_acima
#print axioms ATK.ZeroClasses.MundoFora.mundo_finito
