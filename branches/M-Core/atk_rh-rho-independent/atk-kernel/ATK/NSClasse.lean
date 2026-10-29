import ATK.NSEnergia

/-!
# ATK — B3: a classe de Fourier e a desigualdade de energia

Camada 11 do ataque a B3.

* `b3_de_classeD`: a redução `ATK.NSReducao.b3_de_classe` com uma classe **dependente do dado**
  `R d` (mesma prova; a classe de Fourier depende de `ν`);
* `ClasseF ν`: em `[0, T']`, `U = Re V[â]` para uma amplitude `â` boa (contínua, decaimento
  rápido), hermitiana, de divergência nula, solução branda com viscosidade `ν`;
* **`existenciaLocalF`**: existência local **na classe** (a solução construída em
  `ATK.NSExistencia` está na classe);
* **`desigualdadeEnergiaF`**: a desigualdade de energia `∫ |u(t)|² ≤ ∫ |u₀|²` **na classe**
  (Plancherel + `ATK.NSEnergia.energia_decresce`).

Restam, para fechar B3 via `b3_de_classeD`: a continuação na classe e a unicidade fraca–forte
(classe contra qualquer solução suave). **CLOSED_MATH continua false.**
-/

open MeasureTheory Set Filter Topology ComplexConjugate
open scoped Real ContDiff

namespace ATK.NSClasse

open ATK.LigacaoNS ATK.NSReducao ATK.NSFourierBase ATK.NSPicard ATK.NSMild ATK.NSSuave
  ATK.NSTempo ATK.NSSimetria ATK.NSFisico ATK.NSPressao ATK.NSDado ATK.NSPlancherel
  ATK.NSExistencia ATK.NSEnergia

/-! ### A redução com classe dependente do dado -/

/-- Existência local na classe `R d`. -/
def ExistenciaLocalD (R : ℝ × (E3 → E3) → ℝ → (E3 × ℝ → E3) → Prop) : Prop :=
  ∀ d : ℝ × (E3 → E3), Admissivel d → ∃ T : ℝ, 0 < T ∧ ∃ U P, SolR (R d) d.1 d.2 T U P

/-- Unicidade fraca–forte: uma solução da classe `R d` coincide com qualquer solução suave. -/
def UnicidadeD (R : ℝ × (E3 → E3) → ℝ → (E3 × ℝ → E3) → Prop) : Prop :=
  ∀ d : ℝ × (E3 → E3), Admissivel d →
    ∀ (T₁ T₂ : ℝ) (U₁ U₂ : E3 × ℝ → E3) (P₁ P₂ : E3 × ℝ → ℝ),
      SolR (R d) d.1 d.2 T₁ U₁ P₁ → SolucaoLocal d.1 d.2 T₂ U₂ P₂ →
      ∀ (x : E3) (t : ℝ), 0 ≤ t → t < T₁ → t < T₂ → U₁ (x, t) = U₂ (x, t)

/-- Continuação na classe `R d`. -/
def ContinuacaoD (R : ℝ × (E3 → E3) → ℝ → (E3 × ℝ → E3) → Prop) : Prop :=
  ∀ d : ℝ × (E3 → E3), Admissivel d →
    ∀ (T : ℝ) (U : E3 × ℝ → E3) (P : E3 × ℝ → ℝ), 0 < T → SolR (R d) d.1 d.2 T U P →
      (∃ B : ℝ, ∀ t ∈ Ico 0 T, ∫ x, gradSq (fatia U t) x ≤ B) →
      ∃ T₂ : ℝ, T < T₂ ∧ ∃ U₂ P₂, SolR (R d) d.1 d.2 T₂ U₂ P₂

/-- Desigualdade de energia na classe `R d`. -/
def DesigualdadeEnergiaD (R : ℝ × (E3 → E3) → ℝ → (E3 × ℝ → E3) → Prop) : Prop :=
  ∀ d : ℝ × (E3 → E3), Admissivel d →
    ∀ (T : ℝ) (U : E3 × ℝ → E3) (P : E3 × ℝ → ℝ), SolR (R d) d.1 d.2 T U P →
      ∀ t ∈ Ico 0 T, ∫ x, ‖U (x, t)‖ ^ 2 ≤ ∫ x, ‖d.2 x‖ ^ 2

/-- **A ponte B3 a partir dos quatro enunciados, numa classe local `R d` dependente do dado.**
(A prova é a de `ATK.NSReducao.b3_de_classe`.) -/
theorem b3_de_classeD (R : ℝ × (E3 → E3) → ℝ → (E3 × ℝ → E3) → Prop)
    (hR : ∀ d, Local (R d)) (hEx : ExistenciaLocalD R) (hUn : UnicidadeD R)
    (hCo : ContinuacaoD R) (hEn : DesigualdadeEnergiaD R) :
    ATK.Conditional.NavierStokes.EnstrophyBlowupCriterion modeloNS := by
  rintro ⟨ν, u₀⟩ hd hng
  have hd' : Admissivel (ν, u₀) := hd
  have hun := hUn (ν, u₀) hd'
  set A : Set ℝ := {T | 0 < T ∧ ∃ U P, SolR (R (ν, u₀)) ν u₀ T U P} with hA
  obtain ⟨T₀, hT₀, U₀, P₀, h₀⟩ := hEx (ν, u₀) hd'
  have hT₀A : T₀ ∈ A := ⟨hT₀, U₀, P₀, h₀⟩
  -- a classe `R` passa para a colagem
  have hRglue : ∀ (I : Set ℝ) (U : E3 × ℝ → E3), I ⊆ Ici 0 →
      (∀ t ∈ I, ∀ (T : ℝ) (U' : E3 × ℝ → E3) (P' : E3 × ℝ → ℝ),
        SolucaoLocal ν u₀ T U' P' → t < T → fatia U t = fatia U' t) →
      (∀ t ∈ I, ∃ T, t < T ∧ Ico 0 T ⊆ I ∧ ∃ U P, SolR (R (ν, u₀)) ν u₀ T U P) →
      ∀ T', T' ∈ I → R (ν, u₀) T' U := by
    intro I U hIpos hsl hcov T' hT'
    obtain ⟨T, hT'T, hTI, U', P', h'⟩ := hcov T' hT'
    refine hR (ν, u₀) T' U' U (fun x t ht0 htT' => ?_) (h'.2 T' (hIpos hT') hT'T)
    have htI : t ∈ I := hTI ⟨ht0, lt_of_le_of_lt htT' hT'T⟩
    exact (congrFun (hsl t htI T U' P' h'.1 (lt_of_le_of_lt htT' hT'T)) x).symm
  by_cases hbdd : BddAbove A
  · -- tempo maximal finito
    set Ts := sSup A with hTs
    have hTspos : 0 < Ts := lt_of_lt_of_le hT₀ (le_csSup hbdd hT₀A)
    have hcov : ∀ t ∈ Ico 0 Ts, ∃ T, t < T ∧ Ico 0 T ⊆ Ico 0 Ts ∧
        ∃ U P, SolR (R (ν, u₀)) ν u₀ T U P := by
      intro t ht
      obtain ⟨T, ⟨hTpos, hsol⟩, htT⟩ := exists_lt_of_lt_csSup ⟨T₀, hT₀A⟩ ht.2
      exact ⟨T, htT, Ico_subset_Ico_right (le_csSup hbdd ⟨hTpos, hsol⟩), hsol⟩
    obtain ⟨U, P, hUc, hPc, h0, hns, hdiv, hsl⟩ :=
      colagem (Boa := SolR (R (ν, u₀)) ν u₀) (fun T U P h => h.1) hun (I := Ico 0 Ts)
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
    have hSol : SolR (R (ν, u₀)) ν u₀ Ts U P :=
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
        ∃ U P, SolR (R (ν, u₀)) ν u₀ T U P := by
      intro t _
      obtain ⟨T, ⟨_, hsol⟩, htT⟩ := not_bddAbove_iff.mp hbdd t
      exact ⟨T, htT, Ico_subset_Ici_self, hsol⟩
    obtain ⟨U, P, hUc, hPc, h0, hns, hdiv, hsl⟩ :=
      colagem (Boa := SolR (R (ν, u₀)) ν u₀) (fun T U P h => h.1) hun (I := Ici 0)
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


/-! ### A classe de Fourier -/

/-- **A classe de Fourier** (viscosidade `ν`): em `[0, T']`, `U = Re V[â]` para uma amplitude
`â` boa, hermitiana, de divergência nula, solução branda de Navier–Stokes. -/
def ClasseF (ν T' : ℝ) (U : E3 × ℝ → E3) : Prop :=
  ∃ a : ℝ → E3 → C3, BoaW a ∧ (∀ t, Herm (a t)) ∧ (∀ t ξ, inner ℂ (cpx ξ) (a t ξ) = 0) ∧
    (∀ t ∈ Icc 0 T', ∀ ξ, a t ξ = heat ν t ξ • a 0 ξ - ∫ s in (0 : ℝ)..t, duhI ν a a t s ξ) ∧
    ∀ x t, 0 ≤ t → t ≤ T' → U (x, t) = Uf ν a (x, t)

theorem local_ClasseF (ν : ℝ) : Local (ClasseF ν) := by
  intro T' U V hUV ⟨a, ha, hh, hd, hm, hU⟩
  exact ⟨a, ha, hh, hd, hm, fun x t ht0 ht => (hUV x t ht0 ht).symm.trans (hU x t ht0 ht)⟩

/-- **Existência local na classe de Fourier.** -/
theorem existenciaLocalF : ExistenciaLocalD fun d => ClasseF d.1 := by
  rintro ⟨ν, u₀f⟩ ⟨hν, ⟨u₀, hu₀⟩, hdiv⟩
  simp only at hν hdiv hu₀ ⊢
  subst hu₀
  obtain ⟨M, hM⟩ := ahat_dado u₀
  obtain ⟨T, hT, a, ha4, hmild, hdivF, -, hbnd, hherm⟩ :=
    existe_branda_herm hν hM (ahat_div u₀ hdiv) (ahat_herm u₀)
  have haW : BoaW a := by
    refine ⟨ha4.cont, fun m => ?_⟩
    obtain ⟨C0, -, hC0⟩ := ahat_bound u₀ m
    obtain ⟨C, hC⟩ := hbnd m C0 hC0
    refine ⟨max C 0, le_max_right _ _, fun t ξ => (hC t ξ).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_pos.mpr (w_pos m ξ)).le
  have hb := amp_ader haW hmild
  have hp := amp_pk haW hmild
  obtain ⟨A, hA0, hA⟩ := haW.bound 5
  have hsub : univ ×ˢ Ico 0 T ⊆ (univ : Set E3) ×ˢ Icc 0 T :=
    prod_mono subset_rfl Ico_subset_Icc_self
  have ha0 : a 0 = ahat u₀ := by
    funext ξ
    rw [hmild 0 ⟨le_rfl, hT.le⟩ ξ, heat_zero, one_smul, intervalIntegral.integral_same,
      sub_zero]
  refine ⟨T, hT, Uf ν a, Pf ν a, ⟨?_, ?_, fun x => ?_, fun x t ht => ?_, fun x t ht => ?_,
    fun T' hT' => ?_⟩, fun T' hT'0 hT' => ?_⟩
  · exact (re3L.contDiff.comp_contDiffOn (hb.contDiffOn_V_infty hT)).mono hsub
  · exact (re0L.contDiff.comp_contDiffOn (hp.contDiffOn_V_infty hT)).mono hsub
  · show re3 (V (ader ν a 0) (x, 0)) = u₀ x
    simp only [V, ader_zero, ha0, Vf_ahat, re3_cpx]
  · exact NSEq_Uf haW hmild hherm hdivF ht x
  · exact div_Uf haW hmild hdivF (Ico_subset_Icc_self ht) x
  · refine ⟨A ^ 2 * I4 + 3 * ((2 * π * A) ^ 2 * I4), fun t ht => ?_⟩
    have htT : t ∈ Icc 0 T := ⟨ht.1, ht.2.trans hT'.le⟩
    have hI4 := I4_nonneg
    obtain ⟨hE1, hE2⟩ := energia_Uf haW hmild hA0 hA htT
    obtain ⟨hG1, hG2⟩ := enstrofia_Uf haW hmild hA0 hA htT
    refine ⟨⟨hE1, hE2.trans ?_⟩, hG1, hG2.trans ?_⟩
    · have : 0 ≤ 3 * ((2 * π * A) ^ 2 * I4) := by positivity
      linarith
    · have : 0 ≤ A ^ 2 * I4 := by positivity
      linarith
  · refine ⟨a, haW, hherm, hdivF, fun t ht ξ => ?_, fun x t _ _ => rfl⟩
    rw [ha0]
    exact hmild t ⟨ht.1, ht.2.trans hT'.le⟩ ξ

/-! ### A desigualdade de energia na classe -/

theorem norm_re3_of_real {v : C3} (hv : cj3 v = v) : ‖re3 v‖ = ‖v‖ := by
  rw [← norm_cpx, cpx_re3 hv]

/-- **Desigualdade de energia na classe de Fourier**: `∫ |u(x, t)|² dx ≤ ∫ |u₀|²`. -/
theorem desigualdadeEnergiaF : DesigualdadeEnergiaD fun d => ClasseF d.1 := by
  rintro ⟨ν, u₀⟩ ⟨hν, -, -⟩ T U P ⟨hsol, hR⟩ t ht
  simp only at hν hsol hR ⊢
  obtain ⟨a, ha, hh, hd, hm, hU⟩ := hR t ht.1 ht.2
  obtain ⟨A, hA0, hA⟩ := ha.bound 4
  -- `U(·, t) = Re V[â(t)]` e `U(·, 0) = V[â(0)] = u₀`
  have eUt : ∀ x, U (x, t) = re3 (Vf (a t) x) := fun x => by
    rw [hU x t ht.1 le_rfl]; simp [Uf, V, ader_zero]
  have eU0 : ∀ x, ‖u₀ x‖ = ‖Vf (a 0) x‖ := fun x => by
    rw [← hsol.2.2.1 x, hU x 0 le_rfl ht.1]
    simp only [Uf, V, ader_zero]
    exact norm_re3_of_real (Vf_real (hh 0) x)
  obtain ⟨hIt, hEt⟩ := integral_norm_sq_Vf (ha.cont_s t).aestronglyMeasurable (hA t)
  obtain ⟨hI0, hE0⟩ := integral_norm_sq_Vf (ha.cont_s 0).aestronglyMeasurable (hA 0)
  have hcU : Continuous fun x => U (x, t) := by
    have e : (fun x => U (x, t)) = fun x => re3L (V (ader ν a 0) (x, t)) :=
      funext fun x => hU x t ht.1 le_rfl
    rw [e]
    exact re3L.continuous.comp (continuous_fatia_V (amp_ader ha hm) ⟨ht.1, le_rfl⟩)
  have hle : ∀ x, ‖U (x, t)‖ ^ 2 ≤ ‖Vf (a t) x‖ ^ 2 := fun x => by
    rw [eUt]; exact pow_le_pow_left₀ (norm_nonneg _) (norm_re3_le _) 2
  have hUi : Integrable fun x => ‖U (x, t)‖ ^ 2 :=
    hIt.mono' (hcU.norm.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (by positivity)]; exact hle x)
  calc ∫ x, ‖U (x, t)‖ ^ 2 ≤ ∫ x, ‖Vf (a t) x‖ ^ 2 := integral_mono hUi hIt hle
    _ = ∫ ξ, ‖a t ξ‖ ^ 2 := hEt
    _ ≤ ∫ ξ, ‖a 0 ξ‖ ^ 2 := energia_decresce hν.le ha hm hh hd ⟨ht.1, le_rfl⟩
    _ = ∫ x, ‖Vf (a 0) x‖ ^ 2 := hE0.symm
    _ = ∫ x, ‖u₀ x‖ ^ 2 := by simp_rw [eU0]

end ATK.NSClasse

#print axioms ATK.NSClasse.b3_de_classeD
#print axioms ATK.NSClasse.local_ClasseF
#print axioms ATK.NSClasse.existenciaLocalF
#print axioms ATK.NSClasse.norm_re3_of_real
#print axioms ATK.NSClasse.desigualdadeEnergiaF
