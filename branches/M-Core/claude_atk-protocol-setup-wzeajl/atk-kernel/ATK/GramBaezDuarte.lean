/-
ATK-RH — A fórmula de Gram de D_N, certificada para a família concreta de Báez-Duarte.

Objeto: `DN N = inf_c ∫_{(0,∞)} (χ − Σ_{k<N} c_k ρ_{k+1})²`, com `ρ_k(t) = {1/(k t)}` e
`χ = 𝟙_(0,1]` (definido em `ATK.Conditional.Riemann`).  Até aqui o kernel tinha a fórmula
`1 − bᵀG⁻¹b` só para matrizes abstratas (`ATK.Riemann.gram_complete_square`), e o valor numérico
de `D_N` (usado em `ContracaoDN.cert_Dinf_numerico`) vinha de `numerics/nb_gram.py`.  Este arquivo
liga as duas coisas ao objeto real, sem hipóteses:

* `gram_posDef`   : a matriz de Gram `G_{jk} = ∫_0^∞ ρ_{j+1} ρ_{k+1}` é **definida positiva**
                     para todo N (independência de `{1/(kt)}` em L²(0,∞));
* `DN_eq_gram`    : **`D_N = 1 − b ⬝ G⁻¹ b`**, com `b_k = ∫_0^∞ χ ρ_{k+1} = ∫_0^1 ρ_{k+1}`;
* `DN_attained`   : o ínfimo é atingido em `c* = G⁻¹ b`;
* `minimizer_unique`: `c*` é o único coeficiente que atinge `D_N`;
* `rho_eq_nb_add` : ponte entre as duas famílias do projeto:
                     `{1/(kt)} = ρ^{NB}_k(t) + (1/k){1/t}` (Nyman–Beurling + termo de Báez-Duarte).

Prova de `gram_posDef`: se `∫_0^∞ F² = 0` com `F = Σ c_k ρ_{k+1}`, a cauda `(1,∞)` dá
`F = S/t` com `S = Σ c_k/(k+1)` e `∫_1^∞ F² = S²`, logo `S = 0`; então em `(0,1]`
`F = Σ c_k ρ^{NB}_{k+1}` e `ATK.OmegaGramL2.integral_sq_pos` força `c_k = 0` para `k ≥ 1`;
por fim `S = c_0 = 0`.

Nada aqui decide se `D_N → 0` (obrigação O1).  OPEN_MATH continua true.
-/
import ATK.RiemannFaithful
import ATK.OmegaGramL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace ATK.GramBaezDuarte

open MeasureTheory Set Filter Topology Finset Matrix
open ATK.Conditional.Riemann (chi rho residualSq DN)
open ATK.RiemannFaithful (rho_nonneg rho_le_one rho_le_inv measurable_rho measurable_chi
  integrableOn_sq_of_bounds abs_sum_le integrable_chi_sq integral_chi_sq)
open ATK.OmegaGramRho (SemiInner gram bvec comb err quad PosDefQ)

/-! ### Ponte entre as duas famílias -/

/-- `{1/(kt)} = ({1/(kt)} − (1/k){1/t}) + (1/k){1/t}`: a família de Báez-Duarte é a de
Nyman–Beurling mais um múltiplo de `{1/t}`. -/
theorem rho_eq_nb_add (k : ℕ) (t : ℝ) :
    rho k t = ATK.RhoIndependente.rho (K := ℝ) k t + (1 / (k : ℝ)) * Int.fract (1 / t) := by
  unfold rho ATK.RhoIndependente.rho
  ring

/-- `ρ^{NB}_1 ≡ 0`. -/
theorem nb_rho_one (t : ℝ) : ATK.RhoIndependente.rho (K := ℝ) 1 t = 0 := by
  unfold ATK.RhoIndependente.rho
  simp

/-- Para `t > 1`, `ρ_k(t) = 1/(kt)`. -/
theorem rho_of_gt_one {k : ℕ} (hk : 1 ≤ k) {t : ℝ} (ht : 1 < t) :
    rho k t = 1 / ((k : ℝ) * t) := by
  unfold rho
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < (k : ℝ) * t := mul_pos (by linarith) (by linarith)
  rw [Int.fract_eq_self]
  constructor
  · exact le_of_lt (one_div_pos.mpr hpos)
  · rw [div_lt_one hpos]; nlinarith

/-! ### O subespaço L²(0,∞) e o produto interno -/

/-- Funções reais de quadrado integrável em `(0,∞)` (representantes). -/
def L2 : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | MemLp f 2 (volume.restrict (Ioi (0 : ℝ)))}
  add_mem' := fun hf hg => MemLp.add hf hg
  zero_mem' := MemLp.zero
  smul_mem' := fun a _ hf => MemLp.const_smul hf a

theorem mem_L2 {f : ℝ → ℝ} : f ∈ L2 ↔ MemLp f 2 (volume.restrict (Ioi (0 : ℝ))) := Iff.rfl

/-- Produto de duas funções L² é integrável (polarização, sem Hölder). -/
theorem integrable_mul {f g : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ))))
    (hg : MemLp g 2 (volume.restrict (Ioi (0 : ℝ)))) :
    IntegrableOn (fun t => f t * g t) (Ioi 0) := by
  have h1 := (hf.add hg).integrable_sq
  have h2 := hf.integrable_sq
  have h3 := hg.integrable_sq
  have e : (fun t => f t * g t) = fun t => ((f + g) t ^ 2 - f t ^ 2 - g t ^ 2) / 2 := by
    funext t; simp only [Pi.add_apply]; ring
  rw [IntegrableOn, e]
  exact ((h1.sub h2).sub h3).div_const 2

/-- O produto interno de L²(0,∞) como forma semidefinida sobre `L2`. -/
noncomputable def ip : SemiInner L2 where
  B f g := ∫ t in Ioi (0 : ℝ), (f : ℝ → ℝ) t * (g : ℝ → ℝ) t
  symm f g := by
    show ∫ t in Ioi (0 : ℝ), (f : ℝ → ℝ) t * (g : ℝ → ℝ) t = ∫ t in Ioi (0 : ℝ), (g : ℝ → ℝ) t * (f : ℝ → ℝ) t
    congr 1; funext t; exact mul_comm _ _
  add_left f g h := by
    simp only [Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (integrable_mul f.2 h.2) (integrable_mul g.2 h.2)
  smul_left a f g := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul a _
  nonneg f := integral_nonneg fun t => mul_self_nonneg _

/-! ### Os elementos χ e ρ_k -/

theorem integrable_rho_sq {k : ℕ} (hk : 1 ≤ k) : IntegrableOn (fun t => rho k t ^ 2) (Ioi 0) :=
  integrableOn_sq_of_bounds (measurable_rho k) (B := 1)
    (fun t _ => by rw [abs_of_nonneg (rho_nonneg k t)]; exact rho_le_one k t)
    (fun t ht => by
      rw [abs_of_nonneg (rho_nonneg k t), one_mul]
      exact rho_le_inv hk (lt_trans zero_lt_one ht))

theorem memLp_rho {k : ℕ} (hk : 1 ≤ k) : MemLp (rho k) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (memLp_two_iff_integrable_sq (measurable_rho k).aestronglyMeasurable).mpr (integrable_rho_sq hk)

theorem memLp_chi : MemLp chi 2 (volume.restrict (Ioi (0 : ℝ))) :=
  (memLp_two_iff_integrable_sq measurable_chi.aestronglyMeasurable).mpr integrable_chi_sq

/-- χ como elemento de L². -/
noncomputable def chiL : L2 := ⟨chi, memLp_chi⟩

/-- ρ_{k+1} como elemento de L², `k < N`. -/
noncomputable def rhoL (N : ℕ) : Fin N → L2 := fun k => ⟨rho (k.val + 1), memLp_rho (Nat.succ_pos _)⟩

/-! ### Gram, b e o resíduo -/

/-- `G_{jk} = ∫_0^∞ ρ_{j+1} ρ_{k+1}`. -/
noncomputable def G (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun j k => ∫ t in Ioi (0 : ℝ), rho (j.val + 1) t * rho (k.val + 1) t

/-- `b_k = ∫_0^∞ χ ρ_{k+1}`. -/
noncomputable def b (N : ℕ) : Fin N → ℝ :=
  fun k => ∫ t in Ioi (0 : ℝ), chi t * rho (k.val + 1) t

theorem gram_eq (N : ℕ) : gram ip (rhoL N) = G N := rfl

theorem bvec_eq (N : ℕ) : bvec ip (rhoL N) chiL = b N := rfl

theorem G_symm (N : ℕ) (j k : Fin N) : G N j k = G N k j := ip.symm (rhoL N j) (rhoL N k)

theorem ip_chi : ip.B chiL chiL = 1 := by
  rw [← integral_chi_sq]
  show ∫ t in Ioi (0 : ℝ), chi t * chi t = ∫ t in Ioi (0 : ℝ), chi t ^ 2
  congr 1; funext t; ring

/-- `F_c = Σ c_k ρ_{k+1}`. -/
noncomputable def F {N : ℕ} (c : Fin N → ℝ) (t : ℝ) : ℝ := ∑ k : Fin N, c k * rho (k.val + 1) t

/-- `S_c = Σ c_k/(k+1)`. -/
noncomputable def S {N : ℕ} (c : Fin N → ℝ) : ℝ := ∑ k : Fin N, c k / ((k.val : ℝ) + 1)

theorem coe_comb {N : ℕ} (c : Fin N → ℝ) : ((comb (rhoL N) c : L2) : ℝ → ℝ) = F c := by
  funext t
  simp [comb, rhoL, F, Submodule.coe_sum, Finset.sum_apply, smul_eq_mul]

theorem err_eq {N : ℕ} (c : Fin N → ℝ) : err ip (rhoL N) chiL c = residualSq N c := by
  unfold err residualSq
  show ∫ t in Ioi (0 : ℝ), ((chiL - comb (rhoL N) c : L2) : ℝ → ℝ) t
      * ((chiL - comb (rhoL N) c : L2) : ℝ → ℝ) t = _
  congr 1; funext t
  rw [Submodule.coe_sub, coe_comb]
  simp only [Pi.sub_apply, chiL, F]
  ring

theorem quad_eq {N : ℕ} (c : Fin N → ℝ) : quad (G N) c = ∫ t in Ioi (0 : ℝ), F c t ^ 2 := by
  rw [← gram_eq, ATK.OmegaGramRho.quad_gram_eq]
  show ∫ t in Ioi (0 : ℝ), ((comb (rhoL N) c : L2) : ℝ → ℝ) t
      * ((comb (rhoL N) c : L2) : ℝ → ℝ) t = _
  rw [coe_comb]
  congr 1; funext t; ring

/-! ### Positividade de Gram -/

theorem integrable_F_sq {N : ℕ} (c : Fin N → ℝ) : IntegrableOn (fun t => F c t ^ 2) (Ioi 0) := by
  refine integrableOn_sq_of_bounds
    (Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_rho _))
    (B := ∑ k : Fin N, |c k|) ?_ ?_
  · intro t _
    have h := abs_sum_le c t 1 fun k => by
      rw [abs_of_nonneg (rho_nonneg _ _)]; exact rho_le_one _ _
    rw [mul_one] at h
    exact h
  · intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    exact abs_sum_le c t (1 / t) fun k => by
      rw [abs_of_nonneg (rho_nonneg _ _)]; exact rho_le_inv (Nat.succ_pos _) ht0

/-- Na cauda, `F_c(t) = S_c/t`. -/
theorem F_of_gt_one {N : ℕ} (c : Fin N → ℝ) {t : ℝ} (ht : 1 < t) : F c t = S c / t := by
  have ht0 : (0 : ℝ) < t := by linarith
  unfold F S
  have hk : ∀ k : Fin N, c k * rho (k.val + 1) t = c k / ((k.val : ℝ) + 1) / t := by
    intro k
    rw [rho_of_gt_one (Nat.succ_pos _) ht]
    have hk1 : ((k.val : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
  rw [Finset.sum_congr rfl fun k _ => hk k, ← Finset.sum_div]

/-- `∫_1^∞ F_c² = S_c²`. -/
theorem integral_tail_F {N : ℕ} (c : Fin N → ℝ) : ∫ t in Ioi (1 : ℝ), F c t ^ 2 = S c ^ 2 := by
  have hpt : ∀ t ∈ Ioi (1 : ℝ), F c t ^ 2 = S c ^ 2 * t ^ (-2 : ℝ) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    rw [F_of_gt_one c ht, Real.rpow_neg ht0.le, Real.rpow_two]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
  norm_num

/-- Decomposição `F_c = Σ c_k ρ^{NB}_{k+1} + S_c · {1/t}`. -/
theorem F_decomp {N : ℕ} (c : Fin N → ℝ) (t : ℝ) :
    F c t = (∑ k : Fin N, c k * ATK.RhoIndependente.rho (K := ℝ) (k.val + 1) t)
      + S c * Int.fract (1 / t) := by
  unfold F S
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [rho_eq_nb_add]
  push_cast
  ring

/-- **Gram de Báez-Duarte é definida positiva** (incondicional, todo N). -/
theorem gram_posDef (N : ℕ) : PosDefQ (G N) := by
  classical
  refine ⟨fun c => by rw [← gram_eq]; exact ATK.OmegaGramRho.quad_gram_nonneg ip _ c, ?_⟩
  intro c hc
  rw [quad_eq] at hc
  have hint := integrable_F_sq c
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun t => F c t ^ 2 :=
    Eventually.of_forall fun t => sq_nonneg _
  -- (1) S = 0 pela cauda
  have hS : S c = 0 := by
    have h1 : ∫ t in Ioi (1 : ℝ), F c t ^ 2 ≤ ∫ t in Ioi (0 : ℝ), F c t ^ 2 :=
      setIntegral_mono_set hint hnn (Set.Ioi_subset_Ioi zero_le_one).eventuallyLE
    rw [integral_tail_F, hc] at h1
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h1 (sq_nonneg _))
  -- (2) em (0,1], F = Σ c_k ρ^{NB}_{k+1}, e sua integral do quadrado é 0
  let I : Finset ℕ := (univ.filter fun k : Fin N => 1 ≤ k.val).image fun k => k.val + 1
  let c' : ℕ → ℝ := fun n => if h : n - 1 < N then c ⟨n - 1, h⟩ else 0
  have hI : ∀ n ∈ I, 2 ≤ n := by
    intro n hn
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
    have := (Finset.mem_filter.mp hk).2
    omega
  have hc'k : ∀ k : Fin N, c' (k.val + 1) = c k := by
    intro k
    simp [c', k.isLt]
  have hsum : ∀ t : ℝ, (∑ k : Fin N, c k * ATK.RhoIndependente.rho (K := ℝ) (k.val + 1) t)
      = ∑ n ∈ I, c' n * ATK.RhoIndependente.rho (K := ℝ) n t := by
    intro t
    rw [Finset.sum_image (fun a _ b _ hab => Fin.ext (by simpa using hab)), Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hc'k k]
    split_ifs with hk
    · rfl
    · have : k.val = 0 := by omega
      rw [this, zero_add, nb_rho_one, mul_zero]
  have h01 : ∫ t in Ioc (0 : ℝ) 1, (∑ n ∈ I, c' n * ATK.RhoIndependente.rho (K := ℝ) n t) ^ 2
      ≤ 0 := by
    have h2 : ∫ t in Ioc (0 : ℝ) 1, F c t ^ 2 ≤ ∫ t in Ioi (0 : ℝ), F c t ^ 2 :=
      setIntegral_mono_set hint hnn Set.Ioc_subset_Ioi_self.eventuallyLE
    rw [hc] at h2
    have e : ∀ t, F c t ^ 2 = (∑ n ∈ I, c' n * ATK.RhoIndependente.rho (K := ℝ) n t) ^ 2 := by
      intro t; rw [F_decomp, hS, zero_mul, add_zero, hsum]
    simp_rw [e] at h2
    exact h2
  have hzero : ∀ n ∈ I, c' n = 0 := by
    intro n hn
    by_contra hne
    have := ATK.OmegaGramL2.integral_sq_pos I c' hI ⟨n, hn, hne⟩
    linarith
  -- (3) c_k = 0 para k ≥ 1, e então S = c_0 = 0
  have hpos : ∀ k : Fin N, k.val ≠ 0 → c k = 0 := by
    intro k hk
    rw [← hc'k k]
    exact hzero _ (Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, rfl⟩)
  funext k
  by_cases hk : k.val = 0
  · have hSk : S c = c k / ((k.val : ℝ) + 1) := by
      unfold S
      refine Finset.sum_eq_single k (fun j _ hjk => ?_) (fun h => absurd (Finset.mem_univ k) h)
      have : j.val ≠ 0 := fun hj => hjk (Fin.ext (by omega))
      rw [hpos j this, zero_div]
    rw [hS, hk] at hSk
    simp at hSk
    simpa using hSk.symm
  · simpa using hpos k hk

/-! ### D_N = 1 − bᵀ G⁻¹ b -/

theorem residualSq_nonneg {N : ℕ} (c : Fin N → ℝ) : 0 ≤ residualSq N c :=
  integral_nonneg fun _ => sq_nonneg _

theorem DN_le {N : ℕ} (c : Fin N → ℝ) : DN N ≤ residualSq N c :=
  ciInf_le ⟨0, by rintro _ ⟨c, rfl⟩; exact residualSq_nonneg c⟩ c

/-- `G·(G⁻¹ b) = b`. -/
theorem G_mulVec_inv (N : ℕ) : G N *ᵥ ((G N)⁻¹ *ᵥ b N) = b N := by
  have hu := ATK.OmegaGramRho.isUnit_of_posDef (gram_posDef N)
  rw [mulVec_mulVec, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hu), one_mulVec]

/-- **O ínfimo é atingido** em `c* = G⁻¹ b`. -/
theorem DN_attained (N : ℕ) : DN N = residualSq N ((G N)⁻¹ *ᵥ b N) := by
  have hcs : (gram ip (rhoL N)).mulVec ((G N)⁻¹ *ᵥ b N) = bvec ip (rhoL N) chiL := by
    rw [gram_eq, bvec_eq]; exact G_mulVec_inv N
  refine le_antisymm (DN_le _) (le_ciInf fun c => ?_)
  rw [← err_eq, ← err_eq]
  exact ATK.OmegaGramRho.err_min ip (rhoL N) chiL c _ hcs

/-- **Fórmula de Gram certificada: `D_N = 1 − b ⬝ G⁻¹ b`.** -/
theorem DN_eq_gram (N : ℕ) : DN N = 1 - b N ⬝ᵥ ((G N)⁻¹ *ᵥ b N) := by
  have hcs : (gram ip (rhoL N)).mulVec ((G N)⁻¹ *ᵥ b N) = bvec ip (rhoL N) chiL := by
    rw [gram_eq, bvec_eq]; exact G_mulVec_inv N
  rw [DN_attained, ← err_eq, ATK.OmegaGramRho.err_at_normal ip (rhoL N) chiL _ hcs, ip_chi,
    bvec_eq]
  rfl

/-- **Unicidade**: só `c* = G⁻¹ b` atinge `D_N`. -/
theorem minimizer_unique {N : ℕ} (c : Fin N → ℝ) (hc : residualSq N c = DN N) :
    c = (G N)⁻¹ *ᵥ b N := by
  have hcs : (gram ip (rhoL N)).mulVec ((G N)⁻¹ *ᵥ b N) = bvec ip (rhoL N) chiL := by
    rw [gram_eq, bvec_eq]; exact G_mulVec_inv N
  refine ATK.OmegaGramRho.minimizer_unique ip (rhoL N) chiL ?_ c _ hcs ?_
  · rw [gram_eq]; exact gram_posDef N
  · rw [err_eq, err_eq, hc, DN_attained]

/-- `b_k = ∫_0^1 ρ_{k+1}` (a forma usada em `numerics/nb_gram.py`). -/
theorem b_eq_integral_Ioc (N : ℕ) (k : Fin N) :
    b N k = ∫ t in Ioc (0 : ℝ) 1, rho (k.val + 1) t := by
  unfold b
  have e : (fun t => chi t * rho (k.val + 1) t)
      = Set.indicator (Ioc (0 : ℝ) 1) (fun t => rho (k.val + 1) t) := by
    funext t
    unfold chi
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [ht]
  rw [e, integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
  have : Set.Ioc (0 : ℝ) 1 ∩ Set.Ioi 0 = Set.Ioc 0 1 := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]; constructor
    · rintro ⟨h, -⟩; exact h
    · intro h; exact ⟨h, h.1⟩
  rw [this]

end ATK.GramBaezDuarte

#print axioms ATK.GramBaezDuarte.rho_eq_nb_add
#print axioms ATK.GramBaezDuarte.nb_rho_one
#print axioms ATK.GramBaezDuarte.rho_of_gt_one
#print axioms ATK.GramBaezDuarte.mem_L2
#print axioms ATK.GramBaezDuarte.integrable_mul
#print axioms ATK.GramBaezDuarte.integrable_rho_sq
#print axioms ATK.GramBaezDuarte.memLp_rho
#print axioms ATK.GramBaezDuarte.memLp_chi
#print axioms ATK.GramBaezDuarte.gram_eq
#print axioms ATK.GramBaezDuarte.bvec_eq
#print axioms ATK.GramBaezDuarte.G_symm
#print axioms ATK.GramBaezDuarte.ip_chi
#print axioms ATK.GramBaezDuarte.coe_comb
#print axioms ATK.GramBaezDuarte.err_eq
#print axioms ATK.GramBaezDuarte.quad_eq
#print axioms ATK.GramBaezDuarte.integrable_F_sq
#print axioms ATK.GramBaezDuarte.F_of_gt_one
#print axioms ATK.GramBaezDuarte.integral_tail_F
#print axioms ATK.GramBaezDuarte.F_decomp
#print axioms ATK.GramBaezDuarte.gram_posDef
#print axioms ATK.GramBaezDuarte.residualSq_nonneg
#print axioms ATK.GramBaezDuarte.DN_le
#print axioms ATK.GramBaezDuarte.G_mulVec_inv
#print axioms ATK.GramBaezDuarte.DN_attained
#print axioms ATK.GramBaezDuarte.DN_eq_gram
#print axioms ATK.GramBaezDuarte.minimizer_unique
#print axioms ATK.GramBaezDuarte.b_eq_integral_Ioc
