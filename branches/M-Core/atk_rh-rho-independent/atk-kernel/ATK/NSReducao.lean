import ATK.LigacaoNS

/-!
# ATK — A ponte B3 reduzida a quatro teoremas clássicos da teoria local

A ponte B3 (`ATK.Conditional.NavierStokes.EnstrophyBlowupCriterion`) no modelo genuíno
`ATK.LigacaoNS.modeloNS` diz: se o dado admissível `(ν, u₀)` não tem solução suave global de
energia limitada, então existe `T > 0` até onde há solução suave e a enstrofia `∫ |∇u|²` é
ilimitada em `[0, T)`.

Aqui ela é **provada a partir de quatro enunciados clássicos** sobre o mesmo modelo, cada um com
nome:

* `ExistenciaLocal`: todo dado admissível tem solução suave em algum `[0, T)`, `T > 0`
  (Leray 1934; Kato–Fujita);
* `Unicidade`: duas soluções suaves (classe `SolucaoLocal`) com o mesmo dado coincidem onde ambas
  existem (unicidade fraca–forte);
* `Continuacao`: uma solução em `[0, T)` com enstrofia limitada continua além de `T` (critério de
  Leray);
* `DesigualdadeEnergia`: `∫ |u(t)|² ≤ ∫ |u₀|²`.

A prova (`b3_de_classicos`) constrói a **solução maximal**: as soluções locais são coladas
(`colagem`), com a pressão normalizada `P(x, t) − P(0, t)` (`normP`; o gradiente da pressão é
determinado pela equação, então duas pressões diferem por uma função só de `t`, `normP_eq`). Se o
tempo maximal é infinito, a colagem é uma solução global de energia limitada (contradição); se é
finito, a enstrofia, que pela unicidade é a da solução maximal, não pode ser limitada (senão
`Continuacao` ultrapassa o tempo maximal).

Versão mais fina (`b3_de_classe`): para qualquer classe **local** `R` de soluções (`Local R`: só
depende da solução em `ℝ³ × [0, T']`), basta existência, continuação e energia **dentro da
classe** e a unicidade fraca–forte (solução da classe contra qualquer solução suave). Com `R` =
"todas as derivadas em `L²`" a continuação e a energia ficam bem mais fáceis; a unicidade
fraca–forte (sem nenhuma hipótese sobre a pressão da outra solução) é o núcleo.

Os enunciados **não** são provados aqui; são as camadas seguintes do ataque a B3.
**CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace ATK.NSReducao

open ATK.LigacaoNS

/-! ### Os quatro enunciados clássicos -/

/-- **Existência local**: todo dado admissível tem solução suave em algum `[0, T)`, `T > 0`. -/
def ExistenciaLocal : Prop :=
  ∀ d : ℝ × (E3 → E3), Admissivel d → ∃ T : ℝ, 0 < T ∧ ∃ U P, SolucaoLocal d.1 d.2 T U P

/-- **Unicidade**: duas soluções suaves com o mesmo dado coincidem onde ambas existem. -/
def Unicidade : Prop :=
  ∀ d : ℝ × (E3 → E3), Admissivel d →
    ∀ (T₁ T₂ : ℝ) (U₁ U₂ : E3 × ℝ → E3) (P₁ P₂ : E3 × ℝ → ℝ),
      SolucaoLocal d.1 d.2 T₁ U₁ P₁ → SolucaoLocal d.1 d.2 T₂ U₂ P₂ →
      ∀ (x : E3) (t : ℝ), 0 ≤ t → t < T₁ → t < T₂ → U₁ (x, t) = U₂ (x, t)

/-- **Continuação (critério de Leray)**: uma solução em `[0, T)` com enstrofia limitada continua
além de `T`. -/
def Continuacao : Prop :=
  ∀ d : ℝ × (E3 → E3), Admissivel d →
    ∀ (T : ℝ) (U : E3 × ℝ → E3) (P : E3 × ℝ → ℝ), 0 < T → SolucaoLocal d.1 d.2 T U P →
      (∃ B : ℝ, ∀ t ∈ Ico 0 T, ∫ x, gradSq (fatia U t) x ≤ B) →
      ∃ T₂ : ℝ, T < T₂ ∧ ∃ U₂ P₂, SolucaoLocal d.1 d.2 T₂ U₂ P₂

/-- **Desigualdade de energia**: `∫ |u(x, t)|² dx ≤ ∫ |u₀|²`. -/
def DesigualdadeEnergia : Prop :=
  ∀ d : ℝ × (E3 → E3), Admissivel d →
    ∀ (T : ℝ) (U : E3 × ℝ → E3) (P : E3 × ℝ → ℝ), SolucaoLocal d.1 d.2 T U P →
      ∀ t ∈ Ico 0 T, ∫ x, ‖U (x, t)‖ ^ 2 ≤ ∫ x, ‖d.2 x‖ ^ 2

/-! ### Fatias e derivadas parciais -/

theorem contDiff_fatia {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {F : E3 × ℝ → W}
    {s : Set ℝ} (hF : ContDiffOn ℝ ∞ F (univ ×ˢ s)) {t : ℝ} (ht : t ∈ s) :
    ContDiff ℝ ∞ (fatia F t) := by
  rw [← contDiffOn_univ]
  exact hF.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun y _ => ⟨mem_univ _, ht⟩)

/-- A coordenada `j` de `Σ_i a_i e_i` é `a_j`. -/
theorem coord_sum (a : Fin 3 → ℝ) (j : Fin 3) : (∑ i, a i • e i) j = a j := by
  simp [e, Pi.single_apply, PiLp.single_apply]

theorem dX_eq_of_grad_eq {f g : E3 → ℝ} {x : E3} (h : grad f x = grad g x) (j : Fin 3) :
    dX j f x = dX j g x := by
  have hf : (grad f x) j = dX j f x := coord_sum (fun i => dX i f x) j
  have hg : (grad g x) j = dX j g x := coord_sum (fun i => dX i g x) j
  rw [← hf, ← hg, h]

theorem fderiv_eq_of_dX_eq {f g : E3 → ℝ} {x : E3} (h : ∀ j, dX j f x = dX j g x) :
    fderiv ℝ f x = fderiv ℝ g x := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [← sum_coord v, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul]
  exact congrArg _ (h j)

theorem dX_sub_const (f : E3 → ℝ) (c : ℝ) (j : Fin 3) (x : E3) :
    dX j (fun y => f y - c) x = dX j f x := by
  simp only [dX, fderiv_sub_const]

theorem grad_sub_const (f : E3 → ℝ) (c : ℝ) (x : E3) :
    grad (fun y => f y - c) x = grad f x := by
  simp only [grad, dX_sub_const]

/-! ### Pressão normalizada -/

/-- Pressão normalizada `P(x, t) − P(0, t)`. -/
noncomputable def normP (P : E3 × ℝ → ℝ) : E3 × ℝ → ℝ := fun z => P z - P (0, z.2)

theorem fatia_normP (P : E3 × ℝ → ℝ) (t : ℝ) :
    fatia (normP P) t = fun y => fatia P t y - P (0, t) := rfl

theorem contDiffOn_normP {P : E3 × ℝ → ℝ} {s : Set ℝ} (hP : ContDiffOn ℝ ∞ P (univ ×ˢ s)) :
    ContDiffOn ℝ ∞ (normP P) (univ ×ˢ s) := by
  have hc : ContDiffOn ℝ ∞ (fun z : E3 × ℝ => P (0, z.2)) (univ ×ˢ s) :=
    hP.comp (contDiff_const.prodMk contDiff_snd).contDiffOn (fun z hz => ⟨mem_univ _, hz.2⟩)
  exact hP.sub hc

theorem solucaoLocal_normP {ν : ℝ} {u₀ : E3 → E3} {T : ℝ} {U : E3 × ℝ → E3}
    {P : E3 × ℝ → ℝ} (h : SolucaoLocal ν u₀ T U P) : SolucaoLocal ν u₀ T U (normP P) := by
  obtain ⟨hU, hP, h0, hns, hdiv, hE⟩ := h
  refine ⟨hU, contDiffOn_normP hP, h0, fun x t ht => ?_, hdiv, hE⟩
  have := hns x t ht
  unfold NSEq at this ⊢
  rw [fatia_normP, grad_sub_const]
  exact this

/-- O gradiente da pressão é determinado pela equação. -/
theorem grad_eq_of_NSEq {ν : ℝ} {U : E3 × ℝ → E3} {P : E3 × ℝ → ℝ} {x : E3} {t : ℝ}
    (h : NSEq ν U P x t) :
    grad (fatia P t) x = ν • lap (fatia U t) x -
      (deriv (fun s => U (x, s)) t + conv (fatia U t) x) := by
  unfold NSEq at h
  rw [h]
  abel

/-- **Duas pressões da mesma velocidade, normalizadas, coincidem** (para `t > 0`). -/
theorem normP_eq_pos {ν : ℝ} {u₀ : E3 → E3} {T₁ T₂ : ℝ} {U₁ U₂ : E3 × ℝ → E3}
    {P₁ P₂ : E3 × ℝ → ℝ} (h₁ : SolucaoLocal ν u₀ T₁ U₁ P₁) (h₂ : SolucaoLocal ν u₀ T₂ U₂ P₂)
    (hU : ∀ x t, 0 ≤ t → t < T₁ → t < T₂ → U₁ (x, t) = U₂ (x, t))
    (x : E3) {t : ℝ} (ht0 : 0 < t) (ht1 : t < T₁) (ht2 : t < T₂) :
    normP P₁ (x, t) = normP P₂ (x, t) := by
  have hsl : fatia U₁ t = fatia U₂ t := funext fun y => hU y t ht0.le ht1 ht2
  have hgrad : ∀ y, grad (fatia P₁ t) y = grad (fatia P₂ t) y := by
    intro y
    have hd : deriv (fun s => U₁ (y, s)) t = deriv (fun s => U₂ (y, s)) t := by
      refine Filter.EventuallyEq.deriv_eq ?_
      have hmem : Ioo 0 (min T₁ T₂) ∈ 𝓝 t := Ioo_mem_nhds ht0 (lt_min ht1 ht2)
      filter_upwards [hmem] with s hs
      exact hU y s hs.1.le (lt_of_lt_of_le hs.2 (min_le_left _ _))
        (lt_of_lt_of_le hs.2 (min_le_right _ _))
    rw [grad_eq_of_NSEq (h₁.2.2.2.1 y t ⟨ht0, ht1⟩), grad_eq_of_NSEq (h₂.2.2.2.1 y t ⟨ht0, ht2⟩),
      hsl, hd]
  have hd1 : Differentiable ℝ (fatia P₁ t) :=
    (contDiff_fatia h₁.2.1 ⟨ht0.le, ht1⟩).differentiable (by simp)
  have hd2 : Differentiable ℝ (fatia P₂ t) :=
    (contDiff_fatia h₂.2.1 ⟨ht0.le, ht2⟩).differentiable (by simp)
  have hconst := is_const_of_fderiv_eq_zero (hd1.sub hd2) (fun y => by
    rw [fderiv_sub (hd1 y) (hd2 y),
      fderiv_eq_of_dX_eq (fun j => dX_eq_of_grad_eq (hgrad y) j), sub_self]) x 0
  simp only [Pi.sub_apply, fatia] at hconst
  simp only [normP]
  linarith

/-- **Duas pressões da mesma velocidade, normalizadas, coincidem** (inclusive em `t = 0`, por
continuidade). -/
theorem normP_eq {ν : ℝ} {u₀ : E3 → E3} {T₁ T₂ : ℝ} {U₁ U₂ : E3 × ℝ → E3}
    {P₁ P₂ : E3 × ℝ → ℝ} (h₁ : SolucaoLocal ν u₀ T₁ U₁ P₁) (h₂ : SolucaoLocal ν u₀ T₂ U₂ P₂)
    (hU : ∀ x t, 0 ≤ t → t < T₁ → t < T₂ → U₁ (x, t) = U₂ (x, t))
    (x : E3) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < T₁) (ht2 : t < T₂) :
    normP P₁ (x, t) = normP P₂ (x, t) := by
  rcases ht0.lt_or_eq with hpos | hzero
  · exact normP_eq_pos h₁ h₂ hU x hpos ht1 ht2
  subst hzero
  set m := min T₁ T₂ with hm
  have hm0 : 0 < m := lt_min ht1 ht2
  set g : ℝ → ℝ := fun s => normP P₁ (x, s) - normP P₂ (x, s) with hg
  have hcont : ContinuousOn g (Ico 0 m) := by
    have c1 : ContinuousOn (normP P₁) (univ ×ˢ Ico 0 T₁) :=
      (contDiffOn_normP h₁.2.1).continuousOn
    have c2 : ContinuousOn (normP P₂) (univ ×ˢ Ico 0 T₂) :=
      (contDiffOn_normP h₂.2.1).continuousOn
    have hmap1 : MapsTo (fun s : ℝ => (x, s)) (Ico 0 m) (univ ×ˢ Ico 0 T₁) :=
      fun s hs => ⟨mem_univ _, hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
    have hmap2 : MapsTo (fun s : ℝ => (x, s)) (Ico 0 m) (univ ×ˢ Ico 0 T₂) :=
      fun s hs => ⟨mem_univ _, hs.1, lt_of_lt_of_le hs.2 (min_le_right _ _)⟩
    exact (c1.comp (continuousOn_const.prodMk continuousOn_id) hmap1).sub
      (c2.comp (continuousOn_const.prodMk continuousOn_id) hmap2)
  have hzero_on : ∀ s ∈ Ioo 0 m, g s = 0 := by
    intro s hs
    simp only [hg]
    rw [normP_eq_pos h₁ h₂ hU x hs.1 (lt_of_lt_of_le hs.2 (min_le_left _ _))
      (lt_of_lt_of_le hs.2 (min_le_right _ _)), sub_self]
  have hcl : (0 : ℝ) ∈ closure (Ioo 0 m) := by
    rw [closure_Ioo hm0.ne]; exact ⟨le_rfl, hm0.le⟩
  have := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have ht1 : Tendsto g (𝓝[Ioo 0 m] 0) (𝓝 (g 0)) :=
    ((hcont 0 ⟨le_rfl, hm0⟩).mono Ioo_subset_Ico_self).tendsto
  have ht2 : Tendsto g (𝓝[Ioo 0 m] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => (hzero_on s hs).symm)
  have := tendsto_nhds_unique ht1 ht2
  simp only [hg] at this
  linarith

/-! ### Colagem das soluções locais -/

/-- **Colagem.** Se cada ponto de `I` (com `0 ∈ I ⊆ [0, ∞)`) está antes do fim de uma solução local
cujo intervalo fica em `I`, e as soluções coincidem onde ambas existem, então há um único campo
suave em `ℝ³ × I` que resolve a equação e coincide com cada solução local. -/
theorem colagem {ν : ℝ} {u₀ : E3 → E3}
    {Boa : ℝ → (E3 × ℝ → E3) → (E3 × ℝ → ℝ) → Prop}
    (hBoa : ∀ T U P, Boa T U P → SolucaoLocal ν u₀ T U P)
    (hun : ∀ (T₁ T₂ : ℝ) (U₁ U₂ : E3 × ℝ → E3) (P₁ P₂ : E3 × ℝ → ℝ),
      Boa T₁ U₁ P₁ → SolucaoLocal ν u₀ T₂ U₂ P₂ →
      ∀ (x : E3) (t : ℝ), 0 ≤ t → t < T₁ → t < T₂ → U₁ (x, t) = U₂ (x, t))
    {I : Set ℝ} (hI0 : (0 : ℝ) ∈ I) (hIpos : I ⊆ Ici 0)
    (hcov : ∀ t ∈ I, ∃ T, t < T ∧ Ico 0 T ⊆ I ∧ ∃ U P, Boa T U P) :
    ∃ (U : E3 × ℝ → E3) (P : E3 × ℝ → ℝ), ContDiffOn ℝ ∞ U (univ ×ˢ I) ∧
      ContDiffOn ℝ ∞ P (univ ×ˢ I) ∧ (∀ x, U (x, 0) = u₀ x) ∧
      (∀ x, ∀ t ∈ I, 0 < t → NSEq ν U P x t) ∧ (∀ x, ∀ t ∈ I, div (fatia U t) x = 0) ∧
      (∀ t ∈ I, ∀ (T : ℝ) (U' : E3 × ℝ → E3) (P' : E3 × ℝ → ℝ),
        SolucaoLocal ν u₀ T U' P' → t < T → fatia U t = fatia U' t) := by
  classical
  choose! Tf hTf hTfI Uf Pf hboa using hcov
  have hsol : ∀ t ∈ I, SolucaoLocal ν u₀ (Tf t) (Uf t) (Pf t) := fun t ht => hBoa _ _ _ (hboa t ht)
  set U : E3 × ℝ → E3 := fun z => Uf z.2 z with hUdef
  set P : E3 × ℝ → ℝ := fun z => normP (Pf z.2) z with hPdef
  -- o valor em `(x, s)` é o de qualquer solução que exista em `s`
  have hkey : ∀ s ∈ I, ∀ (T : ℝ) (U' : E3 × ℝ → E3) (P' : E3 × ℝ → ℝ),
      SolucaoLocal ν u₀ T U' P' → s < T → ∀ x, U (x, s) = U' (x, s) := by
    intro s hs T U' P' h' hsT x
    exact hun _ _ _ _ _ _ (hboa s hs) h' x s (hIpos hs) (hTf s hs) hsT
  have hkeyP : ∀ s ∈ I, ∀ (T : ℝ) (U' : E3 × ℝ → E3) (P' : E3 × ℝ → ℝ),
      SolucaoLocal ν u₀ T U' P' → s < T → ∀ x, P (x, s) = normP P' (x, s) := by
    intro s hs T U' P' h' hsT x
    exact normP_eq (hsol s hs) h' (hun _ _ _ _ _ _ (hboa s hs) h') x (hIpos hs) (hTf s hs) hsT
  -- igualdade local perto de cada `t ∈ I`
  have hloc : ∀ t ∈ I, ∀ z ∈ ((univ : Set E3) ×ˢ I) ∩ ((univ : Set E3) ×ˢ Iio (Tf t)),
      U z = Uf t z ∧ P z = normP (Pf t) z := by
    intro t ht z hz
    obtain ⟨⟨-, hzI⟩, ⟨-, hzT⟩⟩ := hz
    have e1 := hkey z.2 hzI (Tf t) (Uf t) (Pf t) (hsol t ht) hzT z.1
    have e2 := hkeyP z.2 hzI (Tf t) (Uf t) (Pf t) (hsol t ht) hzT z.1
    exact ⟨e1, e2⟩
  have hsub : ∀ t ∈ I, ((univ : Set E3) ×ˢ I) ∩ ((univ : Set E3) ×ˢ Iio (Tf t)) ⊆
      (univ : Set E3) ×ˢ Ico 0 (Tf t) := by
    intro t _ z hz
    exact ⟨mem_univ _, hIpos hz.1.2, hz.2.2⟩
  refine ⟨U, P, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
    refine ⟨univ ×ˢ Iio (Tf z.2), isOpen_univ.prod isOpen_Iio, ⟨mem_univ _, hTf z.2 hz.2⟩, ?_⟩
    exact ((hsol z.2 hz.2).1.mono (hsub z.2 hz.2)).congr fun w hw => (hloc z.2 hz.2 w hw).1
  · refine contDiffOn_of_locally_contDiffOn fun z hz => ?_
    refine ⟨univ ×ˢ Iio (Tf z.2), isOpen_univ.prod isOpen_Iio, ⟨mem_univ _, hTf z.2 hz.2⟩, ?_⟩
    exact ((contDiffOn_normP (hsol z.2 hz.2).2.1).mono (hsub z.2 hz.2)).congr
      fun w hw => (hloc z.2 hz.2 w hw).2
  · intro x
    rw [hkey 0 hI0 (Tf 0) (Uf 0) (Pf 0) (hsol 0 hI0) (hTf 0 hI0) x]
    exact (hsol 0 hI0).2.2.1 x
  · intro x t ht htpos
    have hS := solucaoLocal_normP (hsol t ht)
    have hns := hS.2.2.2.1 x t ⟨htpos, hTf t ht⟩
    have hsl : fatia U t = fatia (Uf t) t := funext fun y => rfl
    have hslP : fatia P t = fatia (normP (Pf t)) t := funext fun y => rfl
    have hd : deriv (fun s => U (x, s)) t = deriv (fun s => Uf t (x, s)) t := by
      refine Filter.EventuallyEq.deriv_eq ?_
      have hmem : Ioo 0 (Tf t) ∈ 𝓝 t := Ioo_mem_nhds htpos (hTf t ht)
      filter_upwards [hmem] with s hs
      have hsI : s ∈ I := hTfI t ht ⟨hs.1.le, hs.2⟩
      exact hkey s hsI (Tf t) (Uf t) (Pf t) (hsol t ht) hs.2 x
    unfold NSEq at hns ⊢
    rw [hsl, hslP, hd]
    exact hns
  · intro x t ht
    have hsl : fatia U t = fatia (Uf t) t := funext fun y => rfl
    rw [hsl]
    exact (hsol t ht).2.2.2.2.1 x t ⟨hIpos ht, hTf t ht⟩
  · intro t ht T U' P' h' htT
    exact funext fun y => hkey t ht T U' P' h' htT y

/-! ### A ponte B3 a partir dos quatro enunciados -/

/-- Transporte da energia e da enstrofia por igualdade de fatias. -/
theorem energia_de_fatia {U U' : E3 × ℝ → E3} {t C : ℝ} (h : fatia U t = fatia U' t)
    (hE : EnergiaAte U' t C ∧ Integrable (gradSq (fatia U' t)) ∧
      ∫ x, gradSq (fatia U' t) x ≤ C) :
    EnergiaAte U t C ∧ Integrable (gradSq (fatia U t)) ∧ ∫ x, gradSq (fatia U t) x ≤ C := by
  have hpt : (fun x => ‖U (x, t)‖ ^ 2) = fun x => ‖U' (x, t)‖ ^ 2 := by
    funext x
    rw [show U (x, t) = U' (x, t) from congrFun h x]
  unfold EnergiaAte
  rw [hpt, h]
  exact hE

/-! ### A redução, para uma classe local de soluções -/

/-- Uma propriedade `R T' U` das soluções é **local** se só depende de `U` em `ℝ³ × [0, T']`. -/
def Local (R : ℝ → (E3 × ℝ → E3) → Prop) : Prop :=
  ∀ (T' : ℝ) (U V : E3 × ℝ → E3), (∀ x t, 0 ≤ t → t ≤ T' → U (x, t) = V (x, t)) →
    R T' U → R T' V

/-- Solução local na classe `R`: `R T' U` para todo `T' ∈ [0, T)`. -/
def SolR (R : ℝ → (E3 × ℝ → E3) → Prop) (ν : ℝ) (u₀ : E3 → E3) (T : ℝ) (U : E3 × ℝ → E3)
    (P : E3 × ℝ → ℝ) : Prop :=
  SolucaoLocal ν u₀ T U P ∧ ∀ T', 0 ≤ T' → T' < T → R T' U

/-- Existência local na classe `R`. -/
def ExistenciaLocalR (R : ℝ → (E3 × ℝ → E3) → Prop) : Prop :=
  ∀ d : ℝ × (E3 → E3), Admissivel d → ∃ T : ℝ, 0 < T ∧ ∃ U P, SolR R d.1 d.2 T U P

/-- Unicidade fraca–forte: uma solução da classe `R` coincide com qualquer solução suave. -/
def UnicidadeR (R : ℝ → (E3 × ℝ → E3) → Prop) : Prop :=
  ∀ d : ℝ × (E3 → E3), Admissivel d →
    ∀ (T₁ T₂ : ℝ) (U₁ U₂ : E3 × ℝ → E3) (P₁ P₂ : E3 × ℝ → ℝ),
      SolR R d.1 d.2 T₁ U₁ P₁ → SolucaoLocal d.1 d.2 T₂ U₂ P₂ →
      ∀ (x : E3) (t : ℝ), 0 ≤ t → t < T₁ → t < T₂ → U₁ (x, t) = U₂ (x, t)

/-- Continuação na classe `R`. -/
def ContinuacaoR (R : ℝ → (E3 × ℝ → E3) → Prop) : Prop :=
  ∀ d : ℝ × (E3 → E3), Admissivel d →
    ∀ (T : ℝ) (U : E3 × ℝ → E3) (P : E3 × ℝ → ℝ), 0 < T → SolR R d.1 d.2 T U P →
      (∃ B : ℝ, ∀ t ∈ Ico 0 T, ∫ x, gradSq (fatia U t) x ≤ B) →
      ∃ T₂ : ℝ, T < T₂ ∧ ∃ U₂ P₂, SolR R d.1 d.2 T₂ U₂ P₂

/-- Desigualdade de energia na classe `R`. -/
def DesigualdadeEnergiaR (R : ℝ → (E3 × ℝ → E3) → Prop) : Prop :=
  ∀ d : ℝ × (E3 → E3), Admissivel d →
    ∀ (T : ℝ) (U : E3 × ℝ → E3) (P : E3 × ℝ → ℝ), SolR R d.1 d.2 T U P →
      ∀ t ∈ Ico 0 T, ∫ x, ‖U (x, t)‖ ^ 2 ≤ ∫ x, ‖d.2 x‖ ^ 2

/-- **A ponte B3 a partir dos quatro enunciados, numa classe local `R` de soluções.** Basta
existência, continuação e energia **na classe** e a unicidade fraca–forte (classe contra qualquer
solução suave). -/
theorem b3_de_classe (R : ℝ → (E3 × ℝ → E3) → Prop) (hR : Local R)
    (hEx : ExistenciaLocalR R) (hUn : UnicidadeR R) (hCo : ContinuacaoR R)
    (hEn : DesigualdadeEnergiaR R) :
    ATK.Conditional.NavierStokes.EnstrophyBlowupCriterion modeloNS := by
  rintro ⟨ν, u₀⟩ hd hng
  have hd' : Admissivel (ν, u₀) := hd
  have hun := hUn (ν, u₀) hd'
  set A : Set ℝ := {T | 0 < T ∧ ∃ U P, SolR R ν u₀ T U P} with hA
  obtain ⟨T₀, hT₀, U₀, P₀, h₀⟩ := hEx (ν, u₀) hd'
  have hT₀A : T₀ ∈ A := ⟨hT₀, U₀, P₀, h₀⟩
  -- a classe `R` passa para a colagem
  have hRglue : ∀ (I : Set ℝ) (U : E3 × ℝ → E3), I ⊆ Ici 0 →
      (∀ t ∈ I, ∀ (T : ℝ) (U' : E3 × ℝ → E3) (P' : E3 × ℝ → ℝ),
        SolucaoLocal ν u₀ T U' P' → t < T → fatia U t = fatia U' t) →
      (∀ t ∈ I, ∃ T, t < T ∧ Ico 0 T ⊆ I ∧ ∃ U P, SolR R ν u₀ T U P) →
      ∀ T', T' ∈ I → R T' U := by
    intro I U hIpos hsl hcov T' hT'
    obtain ⟨T, hT'T, hTI, U', P', h'⟩ := hcov T' hT'
    refine hR T' U' U (fun x t ht0 htT' => ?_) (h'.2 T' (hIpos hT') hT'T)
    have htI : t ∈ I := hTI ⟨ht0, lt_of_le_of_lt htT' hT'T⟩
    exact (congrFun (hsl t htI T U' P' h'.1 (lt_of_le_of_lt htT' hT'T)) x).symm
  by_cases hbdd : BddAbove A
  · -- tempo maximal finito
    set Ts := sSup A with hTs
    have hTspos : 0 < Ts := lt_of_lt_of_le hT₀ (le_csSup hbdd hT₀A)
    have hcov : ∀ t ∈ Ico 0 Ts, ∃ T, t < T ∧ Ico 0 T ⊆ Ico 0 Ts ∧
        ∃ U P, SolR R ν u₀ T U P := by
      intro t ht
      obtain ⟨T, ⟨hTpos, hsol⟩, htT⟩ := exists_lt_of_lt_csSup ⟨T₀, hT₀A⟩ ht.2
      exact ⟨T, htT, Ico_subset_Ico_right (le_csSup hbdd ⟨hTpos, hsol⟩), hsol⟩
    obtain ⟨U, P, hUc, hPc, h0, hns, hdiv, hsl⟩ :=
      colagem (Boa := SolR R ν u₀) (fun T U P h => h.1) hun (I := Ico 0 Ts)
        ⟨le_rfl, hTspos⟩ (fun t ht => ht.1) hcov
    have hSol0 : SolucaoLocal ν u₀ Ts U P := by
      refine ⟨hUc, hPc, h0, fun x t ht => hns x t ⟨ht.1.le, ht.2⟩ ht.1, hdiv, fun T' hT' => ?_⟩
      rcases lt_or_ge T' 0 with hneg | hnn
      · refine ⟨0, fun t ht => absurd (ht.1.trans ht.2) (not_le.mpr hneg)⟩
      · obtain ⟨T, hT'T, -, U', P', h'⟩ := hcov T' ⟨hnn, hT'⟩
        obtain ⟨C, hC⟩ := h'.1.2.2.2.2.2 T' hT'T
        exact ⟨C, fun t ht => energia_de_fatia
          (hsl t ⟨ht.1, lt_of_le_of_lt ht.2 hT'⟩ T U' P' h'.1 (lt_of_le_of_lt ht.2 hT'T))
          (hC t ht)⟩
    have hSol : SolR R ν u₀ Ts U P :=
      ⟨hSol0, fun T' hT'0 hT' => hRglue (Ico 0 Ts) U (fun t ht => ht.1) hsl hcov T' ⟨hT'0, hT'⟩⟩
    refine ⟨Ts, hTspos, ⟨U, P, hSol0⟩, fun B => ?_⟩
    by_contra hcon
    push_neg at hcon
    -- a enstrofia do modelo é a da solução maximal
    have hens : ∀ t ∈ Ico 0 Ts,
        modeloNS.enstrophy (ν, u₀) t = ∫ x, gradSq (fatia U t) x := by
      intro t ht
      have hset : {E | ∃ T U' P', t < T ∧ SolucaoLocal ν u₀ T U' P' ∧
          E = ∫ x, gradSq (fatia U' t) x} = {∫ x, gradSq (fatia U t) x} := by
        ext E
        constructor
        · rintro ⟨T, U', P', htT, h', rfl⟩
          rw [mem_singleton_iff, hsl t ht T U' P' h' htT]
        · intro hE
          rw [mem_singleton_iff] at hE
          exact ⟨Ts, U, P, ht.2, hSol0, hE⟩
      show sSup {E | ∃ T U' P', t < T ∧ SolucaoLocal ν u₀ T U' P' ∧
          E = ∫ x, gradSq (fatia U' t) x} = _
      rw [hset, csSup_singleton]
    obtain ⟨T₂, hT₂, U₂, P₂, h₂⟩ := hCo (ν, u₀) hd' Ts U P hTspos hSol
      ⟨B, fun t ht => (hens t ht) ▸ hcon t ht⟩
    have : T₂ ≤ Ts := le_csSup hbdd ⟨by linarith, U₂, P₂, h₂⟩
    linarith
  · -- tempo maximal infinito: solução global
    exfalso
    apply hng
    have hcov : ∀ t ∈ Ici (0 : ℝ), ∃ T, t < T ∧ Ico 0 T ⊆ Ici 0 ∧
        ∃ U P, SolR R ν u₀ T U P := by
      intro t _
      obtain ⟨T, ⟨_, hsol⟩, htT⟩ := not_bddAbove_iff.mp hbdd t
      exact ⟨T, htT, Ico_subset_Ici_self, hsol⟩
    obtain ⟨U, P, hUc, hPc, h0, hns, hdiv, hsl⟩ :=
      colagem (Boa := SolR R ν u₀) (fun T U P h => h.1) hun (I := Ici 0)
        (mem_Ici.mpr le_rfl) (fun t ht => ht) hcov
    refine ⟨U, P, hUc, hPc, h0, fun x t ht => hns x t ht.le ht, fun x t ht => hdiv x t ht,
      ∫ x, ‖u₀ x‖ ^ 2, fun t ht => ?_⟩
    obtain ⟨T, htT, -, U', P', h'⟩ := hcov t ht
    have hs := hsl t ht T U' P' h'.1 htT
    obtain ⟨C, hC⟩ := h'.1.2.2.2.2.2 t htT
    have hE := (energia_de_fatia hs (hC t ⟨ht, le_rfl⟩)).1
    have hEn' := hEn (ν, u₀) hd' T U' P' h' t ⟨ht, htT⟩
    refine ⟨hE.1, ?_⟩
    have hpt : (fun x => ‖U (x, t)‖ ^ 2) = fun x => ‖U' (x, t)‖ ^ 2 := by
      funext x
      rw [show U (x, t) = U' (x, t) from congrFun hs x]
    rw [hpt]
    exact hEn'

/-- **A ponte B3 a partir dos quatro enunciados clássicos** (classe de todas as soluções). -/
theorem b3_de_classicos (hEx : ExistenciaLocal) (hUn : Unicidade) (hCo : Continuacao)
    (hEn : DesigualdadeEnergia) :
    ATK.Conditional.NavierStokes.EnstrophyBlowupCriterion modeloNS := by
  refine b3_de_classe (fun _ _ => True) (fun _ _ _ _ h => h) (fun d hd => ?_)
    (fun d hd T₁ T₂ U₁ U₂ P₁ P₂ h₁ h₂ => hUn d hd T₁ T₂ U₁ U₂ P₁ P₂ h₁.1 h₂)
    (fun d hd T U P hT h hB => ?_) (fun d hd T U P h => hEn d hd T U P h.1)
  · obtain ⟨T, hT, U, P, h⟩ := hEx d hd
    exact ⟨T, hT, U, P, h, fun _ _ _ => trivial⟩
  · obtain ⟨T₂, hT₂, U₂, P₂, h₂⟩ := hCo d hd T U P hT h.1 hB
    exact ⟨T₂, hT₂, U₂, P₂, h₂, fun _ _ _ => trivial⟩

end ATK.NSReducao

#print axioms ATK.NSReducao.contDiff_fatia
#print axioms ATK.NSReducao.coord_sum
#print axioms ATK.NSReducao.dX_eq_of_grad_eq
#print axioms ATK.NSReducao.fderiv_eq_of_dX_eq
#print axioms ATK.NSReducao.dX_sub_const
#print axioms ATK.NSReducao.grad_sub_const
#print axioms ATK.NSReducao.fatia_normP
#print axioms ATK.NSReducao.contDiffOn_normP
#print axioms ATK.NSReducao.solucaoLocal_normP
#print axioms ATK.NSReducao.grad_eq_of_NSEq
#print axioms ATK.NSReducao.normP_eq_pos
#print axioms ATK.NSReducao.normP_eq
#print axioms ATK.NSReducao.colagem
#print axioms ATK.NSReducao.energia_de_fatia
#print axioms ATK.NSReducao.b3_de_classe
#print axioms ATK.NSReducao.b3_de_classicos
