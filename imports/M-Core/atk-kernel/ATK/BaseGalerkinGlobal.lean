/-
ATK.Base (N2b) — Soluções globais do sistema de Galerkin de Navier–Stokes em T³.

Junta `ATK.BaseGalerkinNS` (cancelamento do termo não linear, identidade de energia) com
`ATK.BaseEDODissipativa` (existência global para campos dissipativos localmente Lipschitz).

Estado: `Est K = ℓ²` sobre os índices `(k, i)`, `k ∈ K`, `i ∈ Fin 3`, com valores em ℂ (espaço de
Hilbert real).  Subespaço admissível `adm K`: divergência nula e realidade `û_{−k} = conj û_k`.

* `campoE_mem_adm`: **o campo de Galerkin preserva o subespaço admissível** (Leray zera a componente
  ao longo de `k`; o termo convectivo comuta com a conjugação graças à simetria `K = −K`);
* `campoE_contDiff`: o campo é polinomial, logo `C^∞`; em dimensão finita isso dá Lipschitz em
  cada bola (`lipschitzOnWith_bola`);
* `campoE_dissipativo`: `⟪V(u), u⟫ = −ν Σ |2πk|²|û_k|² ≤ 0` em `adm K`;
* **`galerkin_global`**: para todo dado inicial admissível e todo `T ≥ 0` existe solução do sistema
  de Galerkin em `[0, T]`, admissível em todo instante, com `‖u(t)‖ ≤ ‖u(0)‖`.

É o passo N2b de `BASES.md`.  A passagem ao limite `N → ∞` (soluções fracas de Leray) é N3–N5.
-/
import ATK.BaseGalerkinNS
import ATK.BaseEDODissipativa
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue

open Finset Complex ComplexConjugate Metric Set
open scoped NNReal RealInnerProductSpace

namespace ATK.BaseGalerkinGlobal

open ATK.BaseGalerkinNS

variable (K : Finset Modo)

/-- Índices `(k, i)` com `k ∈ K`. -/
abbrev Ind := {k // k ∈ K} × Fin 3

/-- Espaço de estados `ℓ²(Ind K; ℂ)`, visto como espaço de Hilbert real. -/
abbrev Est := PiLp 2 (fun _ : Ind K => ℂ)

/-- Leitura de uma função de coordenadas como campo de Fourier (zero fora de `K`). -/
def toCampoF (y : Ind K → ℂ) : Campo := fun k i => if hk : k ∈ K then y (⟨k, hk⟩, i) else 0

/-- Leitura de um estado como campo de Fourier. -/
def toCampo (x : Est K) : Campo := toCampoF K (fun p => x p)

theorem toCampo_apply_mem (x : Est K) {k : Modo} (hk : k ∈ K) (i : Fin 3) :
    toCampo K x k i = x (⟨k, hk⟩, i) := by
  simp [toCampo, toCampoF, hk]

/-- Campo de Galerkin sem força nas coordenadas planas. -/
noncomputable def campoF (ν : ℝ) (y : Ind K → ℂ) : Ind K → ℂ :=
  fun p => campoG K ν (fun _ _ => 0) (toCampoF K y) p.1.1 p.2

/-- Campo de Galerkin sem força no espaço de estados. -/
noncomputable def campoE (ν : ℝ) (x : Est K) : Est K :=
  WithLp.toLp 2 (campoF K ν (fun p => x p))

theorem toCampo_campoE (ν : ℝ) (x : Est K) {k : Modo} (hk : k ∈ K) (i : Fin 3) :
    toCampo K (campoE K ν x) k i = campoG K ν (fun _ _ => 0) (toCampo K x) k i := by
  rw [toCampo_apply_mem K _ hk]
  rfl

/-! ### Subespaço admissível -/

/-- Simetria `K = −K`. -/
def Simetrico : Prop := ∀ k ∈ K, -k ∈ K

theorem dot_add_left (a b c : Vec) : dot (a + b) c = dot a c + dot b c := by
  unfold dot; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => add_mul _ _ _

theorem dot_smul_left (r : ℝ) (a c : Vec) : dot (fun i => (r : ℂ) * a i) c = (r : ℂ) * dot a c := by
  unfold dot; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

theorem toCampo_add (x y : Est K) : toCampo K (x + y) = fun k i => toCampo K x k i + toCampo K y k i := by
  funext k i
  by_cases hk : k ∈ K
  · simp [toCampo, toCampoF, hk]
  · simp [toCampo, toCampoF, hk]

theorem toCampo_smul (r : ℝ) (x : Est K) :
    toCampo K (r • x) = fun k i => (r : ℂ) * toCampo K x k i := by
  funext k i
  by_cases hk : k ∈ K
  · simp [toCampo, toCampoF, hk, Complex.real_smul]
  · simp [toCampo, toCampoF, hk]

/-- O subespaço admissível (real-linear). -/
def adm : Submodule ℝ (Est K) where
  carrier := {x | (∀ k ∈ K, dot (toCampo K x k) (kC k) = 0) ∧
    (∀ k ∈ K, toCampo K x (-k) = cj (toCampo K x k))}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [toCampo_add]
      have := dot_add_left (toCampo K x k) (toCampo K y k) (kC k)
      simp only [Pi.add_def] at this
      rw [this, hx1 k hk, hy1 k hk, add_zero]
    · rw [toCampo_add]
      funext i
      simp only [cj]
      rw [congrFun (hx2 k hk) i, congrFun (hy2 k hk) i, map_add]
      rfl
  zero_mem' := by
    refine ⟨fun k _ => ?_, fun k _ => ?_⟩
    · unfold dot; simp [toCampo, toCampoF]
    · funext i; simp [toCampo, toCampoF, cj]
  smul_mem' := by
    rintro r x ⟨hx1, hx2⟩
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [toCampo_smul, dot_smul_left, hx1 k hk, mul_zero]
    · rw [toCampo_smul]
      funext i
      simp only [cj]
      rw [congrFun (hx2 k hk) i, map_mul, conj_ofReal]
      rfl

theorem admissivel_of_mem {K : Finset Modo} (hK : Simetrico K) {x : Est K} (hx : x ∈ adm K) :
    Admissivel K (toCampo K x) :=
  ⟨hK, hx.1, hx.2⟩

/-! ### Invariância -/

theorem kC_neg (k : Modo) : kC (-k) = fun i => -kC k i := by
  funext i; simp [kC]

theorem dot_kC_self_eq_zero {k : Modo} (h : dot (kC k) (kC k) = 0) : kC k = 0 := by
  have hr : ∑ i, ((k i : ℝ)) ^ 2 = 0 := by
    have := congrArg Complex.re h
    unfold dot kC at this
    simp only [Complex.re_sum, ← Complex.ofReal_intCast, ← Complex.ofReal_mul, Complex.ofReal_re,
      Complex.zero_re] at this
    simpa [sq] using this
  have hi : ∀ i, ((k i : ℝ)) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hr |> fun h i => h i (mem_univ i)
  funext i
  have := hi i
  simp only [kC, Pi.zero_apply]
  have h0 : (k i : ℝ) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  exact_mod_cast h0

/-- Leray zera a componente ao longo de `k`. -/
theorem dot_leray_kC (k : Modo) (w : Vec) : dot (leray k w) (kC k) = 0 := by
  by_cases h : dot (kC k) (kC k) = 0
  · rw [dot_kC_self_eq_zero h]; unfold dot; simp
  · have e : dot (leray k w) (kC k) = dot w (kC k) - dot w (kC k) / dot (kC k) (kC k) *
        dot (kC k) (kC k) := by
      simp only [leray, dot]
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, div_mul_cancel₀ _ h, sub_self]

theorem lam_neg (k : Modo) : lam (-k) = lam k := by
  unfold lam; simp

theorem leray_neg_cj (k : Modo) (w : Vec) : leray (-k) (cj w) = cj (leray k w) := by
  funext i
  simp only [leray, cj, dot, kC, Pi.neg_apply, Int.cast_neg, map_sub, map_mul, map_div₀, map_sum,
    map_intCast]
  have e1 : ∑ x, conj (w x) * -((k x : ℤ) : ℂ) = -∑ x, conj (w x) * ((k x : ℤ) : ℂ) := by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun x _ => by ring
  have e2 : ∑ x, -((k x : ℤ) : ℂ) * -((k x : ℤ) : ℂ) = ∑ x, ((k x : ℤ) : ℂ) * ((k x : ℤ) : ℂ) :=
    Finset.sum_congr rfl fun x _ => by ring
  rw [e1, e2]
  ring

/-- O termo convectivo comuta com a conjugação (truncamento simétrico, realidade). -/
theorem conv_neg {K : Finset Modo} {u : Campo} (hA : Admissivel K u) {k : Modo} :
    conv K u (-k) = cj (conv K u k) := by
  funext i
  simp only [conv, cj, map_sum]
  -- lado direito: reindexar l ↦ −l
  have hR : ∑ l ∈ K, conj (if k - l ∈ K then 2 * (Real.pi : ℂ) * I * dot (u (k - l)) (kC l) * u l i
      else 0) =
      ∑ l ∈ K, if -k - l ∈ K then 2 * (Real.pi : ℂ) * I * dot (u (-k - l)) (kC l) * u l i else 0 := by
    refine Finset.sum_nbij' (fun l => -l) (fun l => -l) (fun l hl => hA.simetrico l hl)
      (fun l hl => hA.simetrico l hl) (fun l _ => neg_neg l) (fun l _ => neg_neg l) ?_
    intro l hl
    have hlK : -l ∈ K := hA.simetrico l hl
    have hcond : (k - l ∈ K) ↔ (-k - -l ∈ K) := by
      constructor
      · intro h; have := hA.simetrico _ h; simpa [sub_eq_add_neg, add_comm] using this
      · intro h; have := hA.simetrico _ h; simpa [sub_eq_add_neg, add_comm] using this
    by_cases hc : k - l ∈ K
    · rw [if_pos hc, if_pos (hcond.mp hc)]
      have hu1 : u (-k - -l) = cj (u (k - l)) := by
        have := hA.real _ hc
        rw [show -(k - l) = -k - -l by abel] at this
        exact this
      have hl' : u (-l) = cj (u l) := hA.real l hl
      rw [hu1, hl', dot_kC_neg]
      simp only [map_mul, map_ofNat, conj_ofReal, conj_I, conj_dot, cj_kC, cj]
      ring
    · rw [if_neg hc, if_neg (fun h => hc (hcond.mpr h)), map_zero]
  rw [hR]

/-- **O campo de Galerkin preserva o subespaço admissível.** -/
theorem campoE_mem_adm {K : Finset Modo} (hK : Simetrico K) (ν : ℝ) {x : Est K} (hx : x ∈ adm K) :
    campoE K ν x ∈ adm K := by
  have hA := admissivel_of_mem hK hx
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have e : toCampo K (campoE K ν x) k = campoG K ν (fun _ _ => 0) (toCampo K x) k := by
      funext i; exact toCampo_campoE K ν x hk i
    rw [e]
    have h1 := hx.1 k hk
    have h2 := dot_leray_kC k (conv K (toCampo K x) k)
    simp only [campoG, dot, add_zero] at h1 h2 ⊢
    have : ∑ i, (-(((ν * lam k : ℝ)) : ℂ) * toCampo K x k i - leray k (conv K (toCampo K x) k) i) *
        kC k i = -(((ν * lam k : ℝ)) : ℂ) * ∑ i, toCampo K x k i * kC k i -
          ∑ i, leray k (conv K (toCampo K x) k) i * kC k i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this, h1, h2]; ring
  · have hnk : -k ∈ K := hK k hk
    have e1 : toCampo K (campoE K ν x) (-k) = campoG K ν (fun _ _ => 0) (toCampo K x) (-k) := by
      funext i; exact toCampo_campoE K ν x hnk i
    have e2 : toCampo K (campoE K ν x) k = campoG K ν (fun _ _ => 0) (toCampo K x) k := by
      funext i; exact toCampo_campoE K ν x hk i
    rw [e1, e2]
    funext i
    simp only [campoG, cj, add_zero]
    rw [lam_neg, hA.real k hk, conv_neg hA, leray_neg_cj]
    simp only [cj, map_sub, map_mul, map_neg, conj_ofReal]

/-! ### Regularidade e Lipschitz -/

theorem contDiff_toCampoF (k : Modo) (i : Fin 3) :
    ContDiff ℝ ⊤ (fun y : Ind K → ℂ => toCampoF K y k i) := by
  by_cases hk : k ∈ K
  · simp only [toCampoF, hk, dite_true]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Ind K => ℂ) (⟨k, hk⟩, i)).contDiff
  · simp only [toCampoF, hk, dite_false]
    exact contDiff_const

theorem contDiff_campoF (ν : ℝ) : ContDiff ℝ ⊤ (campoF K ν) := by
  refine contDiff_pi.mpr fun p => ?_
  simp only [campoF, campoG, leray, conv, dot, add_zero]
  refine ((contDiff_const.mul (contDiff_toCampoF K _ _)).sub ?_)
  refine ContDiff.sub ?_ ?_
  · refine ContDiff.sum fun l _ => ?_
    split_ifs
    · exact (contDiff_const.mul (ContDiff.sum fun j _ =>
        (contDiff_toCampoF K _ _).mul contDiff_const)).mul (contDiff_toCampoF K _ _)
    · exact contDiff_const
  · refine ContDiff.mul (ContDiff.div_const (ContDiff.sum fun j _ => ?_) _) contDiff_const
    refine ContDiff.mul (ContDiff.sum fun l _ => ?_) contDiff_const
    split_ifs
    · exact (contDiff_const.mul (ContDiff.sum fun j _ =>
        (contDiff_toCampoF K _ _).mul contDiff_const)).mul (contDiff_toCampoF K _ _)
    · exact contDiff_const

theorem campoE_contDiff (ν : ℝ) : ContDiff ℝ ⊤ (campoE K ν) := by
  have h1 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Ind K => ℂ)).contDiff (n := ⊤)
  have h2 := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Ind K => ℂ)).symm.contDiff (n := ⊤)
  have := h2.comp ((contDiff_campoF K ν).comp h1)
  exact this

/-- Em dimensão finita, `C¹` ⇒ Lipschitz em cada bola fechada. -/
theorem lipschitzOnWith_bola {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F}
    (hf : ContDiff ℝ 1 f) (R : ℝ) : ∃ C : ℝ≥0, LipschitzOnWith C f (closedBall 0 R) := by
  have hcomp : IsCompact (closedBall (0 : E) R) := isCompact_closedBall 0 R
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn
    ((hf.continuous_fderiv one_ne_zero).continuousOn)
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  refine (convex_closedBall (0 : E) R).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => hf.differentiable one_ne_zero x) fun x hx => ?_
  apply NNReal.coe_le_coe.mp
  simp only [coe_nnnorm, NNReal.coe_mk]
  exact (hC x hx).trans (le_max_left _ _)

/-! ### Dissipação e existência global -/

theorem inner_campoE {K : Finset Modo} (hK : Simetrico K) (ν : ℝ) {x : Est K} (hx : x ∈ adm K) :
    ⟪campoE K ν x, x⟫ = -∑ k ∈ K, ν * lam k * (nsq (toCampo K x k)).re := by
  have hA := admissivel_of_mem hK hx
  have hest := energia_estatica hA ν (fun _ _ => 0)
  have hz : ∑ k ∈ K, dot ((fun _ _ => 0 : Campo) k) (cj (toCampo K x k)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_; unfold dot; simp
  rw [hz, add_zero] at hest
  -- ⟪V, x⟫_ℝ = Re Σ_p x_p conj(V_p) = Re Σ_k dot(V_k, cj u_k)
  have e1 : ⟪campoE K ν x, x⟫ = (∑ k ∈ K, dot (campoG K ν (fun _ _ => 0) (toCampo K x) k)
      (cj (toCampo K x k))).re := by
    rw [PiLp.inner_apply]
    simp only [Complex.inner]
    rw [← Complex.re_sum, ← Complex.conj_re (∑ k ∈ K, _)]
    congr 1
    rw [map_sum, Fintype.sum_prod_type, ← Finset.sum_coe_sort K]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [dot, cj, map_sum, map_mul, conj_conj]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← toCampo_campoE K ν x k.2 i, toCampo_apply_mem K _ k.2 i, toCampo_apply_mem K x k.2 i]
    ring
  rw [e1, hest]
  simp only [Complex.neg_re, Complex.re_sum, Complex.re_ofReal_mul]

theorem campoE_dissipativo {K : Finset Modo} (hK : Simetrico K) {ν : ℝ} (hν : 0 ≤ ν)
    {x : Est K} (hx : x ∈ adm K) : ⟪campoE K ν x, x⟫ ≤ 0 := by
  rw [inner_campoE hK ν hx, neg_nonpos]
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (mul_nonneg hν (lam_nonneg k)) (nsq_re_nonneg _)

/-- O campo restrito ao subespaço admissível. -/
noncomputable def campoA {K : Finset Modo} (hK : Simetrico K) (ν : ℝ) (a : adm K) : adm K :=
  ⟨campoE K ν a, campoE_mem_adm hK ν a.2⟩

/-- **Existência global de Galerkin.** -/
theorem galerkin_global {K : Finset Modo} (hK : Simetrico K) {ν : ℝ} (hν : 0 ≤ ν)
    {x₀ : Est K} (hx₀ : x₀ ∈ adm K) {T : ℝ} (hT : 0 ≤ T) :
    ∃ u : ℝ → Est K, u 0 = x₀ ∧
      (∀ t ∈ Icc 0 T, u t ∈ adm K ∧ HasDerivWithinAt u (campoE K ν (u t)) (Icc 0 T) t) ∧
      ∀ t ∈ Icc 0 T, ‖u t‖ ≤ ‖x₀‖ := by
  haveI : CompleteSpace (adm K) := FiniteDimensional.complete ℝ (adm K)
  have hlip : ∀ R : ℝ≥0, ∃ C : ℝ≥0, LipschitzOnWith C (campoA hK ν) (closedBall 0 R) := by
    intro R
    obtain ⟨C, hC⟩ := lipschitzOnWith_bola ((campoE_contDiff K ν).of_le le_top) R
    refine ⟨C, LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_⟩
    have ha' : (a : Est K) ∈ closedBall (0 : Est K) R := by
      simpa [mem_closedBall, dist_zero_right] using ha
    have hb' : (b : Est K) ∈ closedBall (0 : Est K) R := by
      simpa [mem_closedBall, dist_zero_right] using hb
    have := hC.dist_le_mul a ha' b hb'
    simpa [Subtype.dist_eq, campoA] using this
  have hdiss : ∀ a : adm K, ⟪campoA hK ν a, a⟫ ≤ 0 := fun a =>
    campoE_dissipativo hK hν a.2
  obtain ⟨v, hv0, hv, hvb⟩ :=
    ATK.BaseEDODissipativa.existencia_global hlip hdiss ⟨x₀, hx₀⟩ hT
  refine ⟨fun t => (v t : Est K), ?_, fun t ht => ⟨(v t).2, ?_⟩, fun t ht => ?_⟩
  · show ((v 0 : adm K) : Est K) = x₀
    rw [hv0]
  · have h := (adm K).subtypeL.hasFDerivAt.comp_hasDerivWithinAt t (hv t ht)
    exact h
  · have := hvb t ht
    simpa using this

end ATK.BaseGalerkinGlobal

#print axioms ATK.BaseGalerkinGlobal.toCampo_apply_mem
#print axioms ATK.BaseGalerkinGlobal.toCampo_campoE
#print axioms ATK.BaseGalerkinGlobal.dot_add_left
#print axioms ATK.BaseGalerkinGlobal.dot_smul_left
#print axioms ATK.BaseGalerkinGlobal.toCampo_add
#print axioms ATK.BaseGalerkinGlobal.toCampo_smul
#print axioms ATK.BaseGalerkinGlobal.admissivel_of_mem
#print axioms ATK.BaseGalerkinGlobal.kC_neg
#print axioms ATK.BaseGalerkinGlobal.dot_kC_self_eq_zero
#print axioms ATK.BaseGalerkinGlobal.dot_leray_kC
#print axioms ATK.BaseGalerkinGlobal.lam_neg
#print axioms ATK.BaseGalerkinGlobal.leray_neg_cj
#print axioms ATK.BaseGalerkinGlobal.conv_neg
#print axioms ATK.BaseGalerkinGlobal.campoE_mem_adm
#print axioms ATK.BaseGalerkinGlobal.contDiff_toCampoF
#print axioms ATK.BaseGalerkinGlobal.contDiff_campoF
#print axioms ATK.BaseGalerkinGlobal.campoE_contDiff
#print axioms ATK.BaseGalerkinGlobal.lipschitzOnWith_bola
#print axioms ATK.BaseGalerkinGlobal.inner_campoE
#print axioms ATK.BaseGalerkinGlobal.campoE_dissipativo
#print axioms ATK.BaseGalerkinGlobal.galerkin_global
