/-
ATK-RH — Matriz de Gram, mínimos quadrados e erro residual, em dimensão finita.

Formaliza o bloco "parâmetros da matriz de Gram" dos textos ATK-RH:

* `quad_pos`: para um produto interno abstrato B que detecta os pontos 1/k
  (B f f = 0 ⇒ f(1/k) = 0 para todo k ≥ 1), a matriz de Gram de ρ_{m_1},…,ρ_{m_N}
  com índices distintos ≥ 2 é definida positiva.  Em L²(0,1) a hipótese vale
  porque cada degrau tem medida positiva (não formalizado aqui).
* `exists_normal_solution`: G definida positiva é invertível; c* = G⁻¹ b resolve
  as equações normais G c* = b.
* `complete_square`: E(c) = E(c*) + (c − c*)ᵀ G (c − c*); logo c* é o único
  minimizador e D = E(c*) = ‖χ‖² − bᵀ c*.
* `truncation_bound`: Σ_{k=K+1}^{L} 1/(k(k+1)) = 1/(K+1) − 1/(L+1), cota de
  truncamento das séries de Gram (termos em [0,1]).

Tudo incondicional e sem `sorry`.  Nada aqui decide se D_N → 0.
-/
import ATK.RhoIndependente
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ATK.OmegaGramRho

open Finset Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Forma bilinear simétrica e não negativa (produto interno semidefinido). -/
structure SemiInner (V : Type*) [AddCommGroup V] [Module ℝ V] where
  B : V → V → ℝ
  symm : ∀ f g, B f g = B g f
  add_left : ∀ f g h, B (f + g) h = B f h + B g h
  smul_left : ∀ (a : ℝ) f g, B (a • f) g = a * B f g
  nonneg : ∀ f, 0 ≤ B f f

namespace SemiInner

variable (ip : SemiInner V)

theorem add_right (f g h : V) : ip.B f (g + h) = ip.B f g + ip.B f h := by
  rw [ip.symm, ip.add_left, ip.symm g, ip.symm h]

theorem smul_right (a : ℝ) (f g : V) : ip.B f (a • g) = a * ip.B f g := by
  rw [ip.symm, ip.smul_left, ip.symm]

theorem sum_left {ι : Type*} (s : Finset ι) (f : ι → V) (g : V) :
    ip.B (∑ i ∈ s, f i) g = ∑ i ∈ s, ip.B (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    have := ip.smul_left 0 0 g; simp at this; exact this
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, ip.add_left, ih]

theorem sum_right {ι : Type*} (s : Finset ι) (f : V) (g : ι → V) :
    ip.B f (∑ i ∈ s, g i) = ∑ i ∈ s, ip.B f (g i) := by
  rw [ip.symm, ip.sum_left]; simp_rw [ip.symm]

theorem neg_left (f g : V) : ip.B (-f) g = - ip.B f g := by
  have := ip.smul_left (-1) f g; simpa using this

theorem sub_left (f g h : V) : ip.B (f - g) h = ip.B f h - ip.B g h := by
  rw [sub_eq_add_neg, ip.add_left, ip.neg_left, sub_eq_add_neg]

theorem sub_right (f g h : V) : ip.B f (g - h) = ip.B f g - ip.B f h := by
  rw [ip.symm, ip.sub_left, ip.symm g, ip.symm h]

end SemiInner

/-! ### Gram e forma quadrática -/

variable {N : ℕ}

/-- Matriz de Gram de uma família v. -/
def gram (ip : SemiInner V) (v : Fin N → V) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => ip.B (v i) (v j)

/-- Forma quadrática cᵀ G c. -/
def quad (G : Matrix (Fin N) (Fin N) ℝ) (c : Fin N → ℝ) : ℝ :=
  ∑ i, ∑ j, c i * G i j * c j

/-- Combinação linear Σ c_i v_i. -/
def comb (v : Fin N → V) (c : Fin N → ℝ) : V := ∑ i, c i • v i

theorem quad_gram_eq (ip : SemiInner V) (v : Fin N → V) (c : Fin N → ℝ) :
    quad (gram ip v) c = ip.B (comb v c) (comb v c) := by
  unfold quad gram comb
  rw [ip.sum_left]
  refine sum_congr rfl fun i _ => ?_
  rw [ip.smul_left, ip.sum_right, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [ip.smul_right]; ring

theorem quad_gram_nonneg (ip : SemiInner V) (v : Fin N → V) (c : Fin N → ℝ) :
    0 ≤ quad (gram ip v) c := by
  rw [quad_gram_eq]; exact ip.nonneg _

/-- Definida positiva: cᵀGc > 0 para c ≠ 0. -/
def PosDefQ (G : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  (∀ c, 0 ≤ quad G c) ∧ ∀ c, quad G c = 0 → c = 0

theorem quad_pos_of_posDef {G : Matrix (Fin N) (Fin N) ℝ} (h : PosDefQ G) {c : Fin N → ℝ}
    (hc : c ≠ 0) : 0 < quad G c :=
  lt_of_le_of_ne (h.1 c) fun h0 => hc (h.2 c h0.symm)

/-- Gram é definida positiva assim que B f f = 0 força f = 0 no span. -/
theorem gram_posDef (ip : SemiInner V) (v : Fin N → V)
    (hv : ∀ c : Fin N → ℝ, ip.B (comb v c) (comb v c) = 0 → c = 0) :
    PosDefQ (gram ip v) :=
  ⟨quad_gram_nonneg ip v, fun c hc => hv c (by rwa [quad_gram_eq] at hc)⟩

/-! ### Aplicação a ρ_m -/

section Rho

/-- Espaço das funções reais; ρ_m como elemento. -/
abbrev Fun := ℝ → ℝ

/-- Produto interno abstrato que detecta os pontos 1/k. -/
def DetectsSteps (ip : SemiInner Fun) : Prop :=
  ∀ f : Fun, ip.B f f = 0 → ∀ k : ℕ, 1 ≤ k → f (1 / (k : ℝ)) = 0

/-- **Gram de ρ é definida positiva** para índices distintos ≥ 2, sob um produto
interno que detecta os degraus (como o de L²(0,1)). -/
theorem gram_rho_posDef (ip : SemiInner Fun) (hip : DetectsSteps ip)
    (m : Fin N → ℕ) (hm : ∀ i, 2 ≤ m i) (hinj : Function.Injective m) :
    PosDefQ (gram ip (fun i => ATK.RhoIndependente.rho (m i))) := by
  classical
  apply gram_posDef
  intro c hc
  have hpts := hip _ hc
  -- transporta para a forma Σ_{m ∈ I} c' m ρ_m
  let I : Finset ℕ := univ.image m
  let c' : ℕ → ℝ := fun n => if h : ∃ i, m i = n then c h.choose else 0
  have hI : ∀ n ∈ I, 2 ≤ n := by
    intro n hn; obtain ⟨i, _, rfl⟩ := mem_image.mp hn; exact hm i
  have hcomb : ∀ x : ℝ, comb (fun i => ATK.RhoIndependente.rho (m i)) c x
      = ∑ n ∈ I, c' n * ATK.RhoIndependente.rho n x := by
    intro x
    simp only [comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_image (fun a _ b _ hab => hinj hab)]
    refine sum_congr rfl fun i _ => ?_
    have h : ∃ j, m j = m i := ⟨i, rfl⟩
    have : h.choose = i := hinj h.choose_spec
    simp [c', h, this]
  have hzero : ∀ k : ℕ, 1 ≤ k → ∑ n ∈ I, c' n * ATK.RhoIndependente.rho n (1 / (k : ℝ)) = 0 := by
    intro k hk; rw [← hcomb]; exact hpts k hk
  have := ATK.RhoIndependente.coeffs_eq_zero_of_points I c' hI hzero
  funext i
  have hi : m i ∈ I := mem_image_of_mem m (mem_univ i)
  have h := this (m i) hi
  have hex : ∃ j, m j = m i := ⟨i, rfl⟩
  have hch : hex.choose = i := hinj hex.choose_spec
  simp [c', hex, hch] at h
  simpa using h

end Rho

/-! ### Equações normais e mínimos quadrados -/

/-- Definida positiva ⇒ G·c injetiva ⇒ G inversível. -/
theorem isUnit_of_posDef {G : Matrix (Fin N) (Fin N) ℝ} (h : PosDefQ G) : IsUnit G := by
  rw [← mulVec_injective_iff_isUnit]
  intro c d hcd
  have key : ∀ x : Fin N → ℝ, G.mulVec x = 0 → x = 0 := by
    intro x hx
    apply h.2
    have : quad G x = ∑ i, x i * (G.mulVec x) i := by
      unfold quad; refine sum_congr rfl fun i _ => ?_
      simp only [mulVec, dotProduct, mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
    rw [this, hx]; simp
  have : G.mulVec (c - d) = 0 := by rw [mulVec_sub, hcd, sub_self]
  exact sub_eq_zero.mp (key _ this)

/-- Solução das equações normais G c* = b. -/
theorem exists_normal_solution {G : Matrix (Fin N) (Fin N) ℝ} (h : PosDefQ G) (b : Fin N → ℝ) :
    ∃ cs : Fin N → ℝ, G.mulVec cs = b := by
  have hu := isUnit_of_posDef h
  refine ⟨G⁻¹.mulVec b, ?_⟩
  rw [mulVec_mulVec, mul_nonsing_inv G ((isUnit_iff_isUnit_det G).mp hu), one_mulVec]

/-- Unicidade da solução normal. -/
theorem normal_solution_unique {G : Matrix (Fin N) (Fin N) ℝ} (h : PosDefQ G) {b c d : Fin N → ℝ}
    (hc : G.mulVec c = b) (hd : G.mulVec d = b) : c = d :=
  (mulVec_injective_iff_isUnit.mpr (isUnit_of_posDef h)) (hc.trans hd.symm)

/-- Erro quadrático E(c) = ‖χ − Σ c_i v_i‖². -/
def err (ip : SemiInner V) (v : Fin N → V) (χ : V) (c : Fin N → ℝ) : ℝ :=
  ip.B (χ - comb v c) (χ - comb v c)

/-- Vetor de projeção b_i = ⟨χ, v_i⟩. -/
def bvec (ip : SemiInner V) (v : Fin N → V) (χ : V) : Fin N → ℝ := fun i => ip.B χ (v i)

/-- Expansão E(c) = ‖χ‖² − 2 b·c + cᵀGc. -/
theorem err_expand (ip : SemiInner V) (v : Fin N → V) (χ : V) (c : Fin N → ℝ) :
    err ip v χ c = ip.B χ χ - 2 * ∑ i, bvec ip v χ i * c i + quad (gram ip v) c := by
  unfold err
  rw [ip.sub_left, ip.sub_right, ip.sub_right, quad_gram_eq, ip.symm (comb v c) χ]
  have hb : ip.B χ (comb v c) = ∑ i, bvec ip v χ i * c i := by
    unfold comb bvec; rw [ip.sum_right]; refine sum_congr rfl fun i _ => ?_
    rw [ip.smul_right]; ring
  rw [hb]; ring

/-- Completar o quadrado: se G c* = b então E(c) = E(c*) + (c − c*)ᵀ G (c − c*). -/
theorem complete_square (ip : SemiInner V) (v : Fin N → V) (χ : V) (c cs : Fin N → ℝ)
    (hcs : (gram ip v).mulVec cs = bvec ip v χ) :
    err ip v χ c = err ip v χ cs + quad (gram ip v) (c - cs) := by
  rw [err_expand, err_expand]
  -- quad (c − c*) = quad c − 2 c·(G c*) + quad c*, e G c* = b
  have hGsymm : ∀ i j, gram ip v i j = gram ip v j i := fun i j => ip.symm _ _
  have hb : ∀ i, bvec ip v χ i = ∑ j, gram ip v i j * cs j := by
    intro i; rw [← hcs]; rfl
  have expand : quad (gram ip v) (c - cs)
      = quad (gram ip v) c - 2 * ∑ i, (∑ j, gram ip v i j * cs j) * c i + quad (gram ip v) cs := by
    unfold quad
    simp only [Pi.sub_apply]
    have e1 : ∑ i, ∑ j, (c i - cs i) * gram ip v i j * (c j - cs j)
        = ∑ i, ∑ j, c i * gram ip v i j * c j - ∑ i, ∑ j, c i * gram ip v i j * cs j
          - ∑ i, ∑ j, cs i * gram ip v i j * c j + ∑ i, ∑ j, cs i * gram ip v i j * cs j := by
      simp only [← sum_sub_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_; ring
    have e2 : ∑ i, ∑ j, cs i * gram ip v i j * c j = ∑ i, ∑ j, c i * gram ip v i j * cs j := by
      rw [sum_comm]; refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      rw [hGsymm j i]; ring
    have e3 : ∑ i, (∑ j, gram ip v i j * cs j) * c i = ∑ i, ∑ j, c i * gram ip v i j * cs j := by
      refine sum_congr rfl fun i _ => ?_; rw [sum_mul]
      refine sum_congr rfl fun j _ => ?_; ring
    rw [e1, e2, e3]; ring
  have hq : quad (gram ip v) cs = ∑ i, (∑ j, gram ip v i j * cs j) * cs i := by
    unfold quad; refine sum_congr rfl fun i _ => ?_
    rw [sum_mul]; refine sum_congr rfl fun j _ => ?_; ring
  rw [expand]
  simp_rw [hb]
  rw [hq]
  ring

/-- Consequência: c* minimiza E, e o mínimo D = E(c*) = ‖χ‖² − b·c*. -/
theorem err_min (ip : SemiInner V) (v : Fin N → V) (χ : V) (c cs : Fin N → ℝ)
    (hcs : (gram ip v).mulVec cs = bvec ip v χ) :
    err ip v χ cs ≤ err ip v χ c := by
  rw [complete_square ip v χ c cs hcs]
  have := quad_gram_nonneg ip v (c - cs); linarith

theorem err_at_normal (ip : SemiInner V) (v : Fin N → V) (χ : V) (cs : Fin N → ℝ)
    (hcs : (gram ip v).mulVec cs = bvec ip v χ) :
    err ip v χ cs = ip.B χ χ - ∑ i, bvec ip v χ i * cs i := by
  rw [err_expand]
  have hb : ∀ i, bvec ip v χ i = ∑ j, gram ip v i j * cs j := by
    intro i; rw [← hcs]; rfl
  have : quad (gram ip v) cs = ∑ i, bvec ip v χ i * cs i := by
    unfold quad; refine sum_congr rfl fun i _ => ?_
    rw [hb i, sum_mul]; refine sum_congr rfl fun j _ => ?_; ring
  rw [this]; ring

/-- Unicidade do minimizador quando G é definida positiva. -/
theorem minimizer_unique (ip : SemiInner V) (v : Fin N → V) (χ : V) (hG : PosDefQ (gram ip v))
    (c cs : Fin N → ℝ) (hcs : (gram ip v).mulVec cs = bvec ip v χ)
    (hmin : err ip v χ c ≤ err ip v χ cs) : c = cs := by
  have h := complete_square ip v χ c cs hcs
  have hq : quad (gram ip v) (c - cs) = 0 := by
    have := quad_gram_nonneg ip v (c - cs); linarith
  exact sub_eq_zero.mp (hG.2 _ hq)

/-! ### Cota de truncamento das séries de Gram -/

/-- Σ_{k=K+1}^{L} 1/(k(k+1)) = 1/(K+1) − 1/(L+1) (soma telescópica). -/
theorem telescoping (K L : ℕ) (hKL : K ≤ L) :
    ∑ k ∈ Ico (K + 1) (L + 1), (1 : ℝ) / ((k : ℝ) * (k + 1)) = 1 / (K + 1) - 1 / (L + 1) := by
  induction L, hKL using Nat.le_induction with
  | base => simp
  | succ L hKL ih =>
    rw [Finset.sum_Ico_succ_top (by omega), ih]
    push_cast
    field_simp
    ring

/-- Termos de Gram em [0,1]: a cauda truncada em K é no máximo 1/(K+1) − 1/(L+1). -/
theorem truncation_bound (a : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k) (ha1 : ∀ k, a k ≤ 1) (K L : ℕ)
    (hKL : K ≤ L) :
    0 ≤ ∑ k ∈ Ico (K + 1) (L + 1), a k / ((k : ℝ) * (k + 1)) ∧
    ∑ k ∈ Ico (K + 1) (L + 1), a k / ((k : ℝ) * (k + 1)) ≤ 1 / (K + 1) - 1 / (L + 1) := by
  constructor
  · apply sum_nonneg; intro k hk
    have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by simp [mem_Ico] at hk; omega)
    exact div_nonneg (ha0 k) (by positivity)
  · rw [← telescoping K L hKL]
    apply sum_le_sum; intro k hk
    have hk' : (0 : ℝ) < (k : ℝ) * (k + 1) := by
      have : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by simp [mem_Ico] at hk; omega)
      positivity
    rw [div_le_div_iff_of_pos_right hk']; exact ha1 k

/-- Produto de partes fracionárias está em [0,1]: os termos {k/m}{k/n} são admissíveis. -/
theorem fract_mul_fract_mem (x y : ℝ) : 0 ≤ Int.fract x * Int.fract y ∧ Int.fract x * Int.fract y ≤ 1 := by
  have h1 := Int.fract_nonneg x; have h2 := Int.fract_nonneg y
  have h3 := Int.fract_lt_one x; have h4 := Int.fract_lt_one y
  constructor
  · positivity
  · calc Int.fract x * Int.fract y ≤ 1 * 1 := mul_le_mul h3.le h4.le h2 zero_le_one
      _ = 1 := one_mul _

end ATK.OmegaGramRho

#print axioms ATK.OmegaGramRho.SemiInner.add_right
#print axioms ATK.OmegaGramRho.SemiInner.smul_right
#print axioms ATK.OmegaGramRho.SemiInner.sum_left
#print axioms ATK.OmegaGramRho.SemiInner.sum_right
#print axioms ATK.OmegaGramRho.SemiInner.neg_left
#print axioms ATK.OmegaGramRho.SemiInner.sub_left
#print axioms ATK.OmegaGramRho.SemiInner.sub_right
#print axioms ATK.OmegaGramRho.quad_gram_eq
#print axioms ATK.OmegaGramRho.quad_gram_nonneg
#print axioms ATK.OmegaGramRho.quad_pos_of_posDef
#print axioms ATK.OmegaGramRho.gram_posDef
#print axioms ATK.OmegaGramRho.gram_rho_posDef
#print axioms ATK.OmegaGramRho.isUnit_of_posDef
#print axioms ATK.OmegaGramRho.exists_normal_solution
#print axioms ATK.OmegaGramRho.normal_solution_unique
#print axioms ATK.OmegaGramRho.err_expand
#print axioms ATK.OmegaGramRho.complete_square
#print axioms ATK.OmegaGramRho.err_min
#print axioms ATK.OmegaGramRho.err_at_normal
#print axioms ATK.OmegaGramRho.minimizer_unique
#print axioms ATK.OmegaGramRho.telescoping
#print axioms ATK.OmegaGramRho.truncation_bound
#print axioms ATK.OmegaGramRho.fract_mul_fract_mem
