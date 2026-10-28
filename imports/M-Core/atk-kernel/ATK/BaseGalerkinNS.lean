/-
ATK.Base — Navier–Stokes de Galerkin no toro T³: o cancelamento do termo não linear e a
identidade de energia.

Base que falta na Mathlib (que tem a base de Fourier de L²(Tᵈ), `UnitAddTorus.mFourierBasis`,
mas nenhum modelo de Navier–Stokes).  Em variáveis de Fourier, com um conjunto finito simétrico
de modos `K ⊆ ℤ³` (truncamento de Galerkin):

* campo `u : ℤ³ → ℂ³` **admissível**: `K = −K`, divergência nula `k · û_k = 0` e realidade
  `û_{−k} = conj û_k`;
* termo convectivo truncado `N(u)_k = Σ_{l ∈ K, k−l ∈ K} 2πi (û_{k−l} · l) û_l`  (é `(u·∇)u`);
* **`par_conv_zero`**: `Σ_{k∈K} N(u)_k · conj û_k = 0` — o termo não linear **não troca energia**,
  exatamente, para todo truncamento simétrico (simetrização l ↔ m + divergência nula);
* projeção de Leray `P_k` e **`leray_par`**: `P_k` não altera o emparelhamento com campos de
  divergência nula;
* campo de Galerkin `V(u)_k = −ν|2πk|² û_k − P_k N(u)_k + f̂_k` e **`energia_estatica`**:
  `Σ V(u)_k · conj û_k = −ν Σ |2πk|² |û_k|² + Σ f̂_k · conj û_k`;
* **`identidade_energia`**: ao longo de uma solução, `dE/dt = 2 Re(−ν Σ|2πk|²|û_k|² + ⟨f, u⟩)`;
* **`energia_decresce`**: sem força, com `ν ≥ 0`, `E(t) ≤ E(0)`.

É a estimativa de energia de Leray no nível de Galerkin; a passagem ao limite (soluções fracas) e
a regularidade 3D continuam em aberto.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Finset Complex ComplexConjugate

namespace ATK.BaseGalerkinNS

/-- Modos de Fourier em `ℤ³`. -/
abbrev Modo := Fin 3 → ℤ

/-- Vetores em `ℂ³`. -/
abbrev Vec := Fin 3 → ℂ

/-- Campo em variáveis de Fourier. -/
abbrev Campo := Modo → Vec

/-- Produto bilinear (sem conjugação). -/
def dot (a b : Vec) : ℂ := ∑ i, a i * b i

/-- Conjugação componente a componente. -/
def cj (a : Vec) : Vec := fun i => conj (a i)

/-- O modo como vetor complexo. -/
def kC (k : Modo) : Vec := fun i => ((k i : ℤ) : ℂ)

/-- `|a|² = a · conj a` (real). -/
def nsq (a : Vec) : ℂ := dot a (cj a)

/-- Campo admissível em `K`. -/
structure Admissivel (K : Finset Modo) (u : Campo) : Prop where
  simetrico : ∀ k ∈ K, -k ∈ K
  divLivre : ∀ k ∈ K, dot (u k) (kC k) = 0
  real : ∀ k ∈ K, u (-k) = cj (u k)

/-! ### Álgebra do produto -/

theorem dot_comm (a b : Vec) : dot a b = dot b a := by
  unfold dot; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem dot_kC_add (a : Vec) (l m : Modo) : dot a (kC (l + m)) = dot a (kC l) + dot a (kC m) := by
  unfold dot kC
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  push_cast
  ring

theorem dot_kC_neg (a : Vec) (l : Modo) : dot a (kC (-l)) = -dot a (kC l) := by
  unfold dot kC
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.neg_apply]
  push_cast
  ring

theorem conj_dot (a b : Vec) : conj (dot a b) = dot (cj a) (cj b) := by
  unfold dot cj
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => map_mul _ _ _

theorem cj_kC (k : Modo) : cj (kC k) = kC k := by
  funext i
  simp [cj, kC]

theorem cj_cj (a : Vec) : cj (cj a) = a := by
  funext i; simp [cj]

theorem nsq_im (a : Vec) : (nsq a).im = 0 := by
  unfold nsq dot cj
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Complex.mul_conj]
  simp

theorem nsq_re_nonneg (a : Vec) : 0 ≤ (nsq a).re := by
  unfold nsq dot cj
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Complex.mul_conj]
  simp only [ofReal_re]
  exact Complex.normSq_nonneg _

/-! ### O termo convectivo e o cancelamento -/

/-- `N(u)_k = Σ_{l ∈ K, k−l ∈ K} 2πi (û_{k−l} · l) û_l`. -/
noncomputable def conv (K : Finset Modo) (u : Campo) (k : Modo) : Vec := fun i =>
  ∑ l ∈ K, if k - l ∈ K then 2 * Real.pi * I * dot (u (k - l)) (kC l) * u l i else 0

/-- Emparelhamento de energia do termo não linear: `Σ_{k∈K} N(u)_k · conj û_k`. -/
noncomputable def parConv (K : Finset Modo) (u : Campo) : ℂ :=
  ∑ k ∈ K, dot (conv K u k) (cj (u k))

theorem dot_conv (K : Finset Modo) (u : Campo) (k : Modo) (w : Vec) :
    dot (conv K u k) w =
      ∑ l ∈ K, if k - l ∈ K then 2 * Real.pi * I * dot (u (k - l)) (kC l) * dot (u l) w else 0 := by
  unfold conv
  unfold dot
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs with h
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp

/-- **O termo não linear não troca energia** (truncamento simétrico, divergência nula, realidade). -/
theorem parConv_zero {K : Finset Modo} {u : Campo} (hA : Admissivel K u) : parConv K u = 0 := by
  classical
  -- H(l, m) = [−(l+m) ∈ K] 2πi (û_{−(l+m)} · l)(û_l · û_m)
  set H : Modo → Modo → ℂ := fun l m =>
    if -(l + m) ∈ K then 2 * Real.pi * I * dot (u (-(l + m))) (kC l) * dot (u l) (u m) else 0
    with hH
  -- passo 1: reescrever com conj û_k = û_{−k} e k = −m
  have step1 : parConv K u = ∑ m ∈ K, ∑ l ∈ K, H l m := by
    unfold parConv
    have e : ∀ k ∈ K, dot (conv K u k) (cj (u k)) = ∑ l ∈ K, H l (-k) := by
      intro k hk
      rw [dot_conv, ← hA.real k hk]
      refine Finset.sum_congr rfl fun l _ => ?_
      have : -(l + -k) = k - l := by abel
      simp only [hH, this]
    rw [Finset.sum_congr rfl e]
    refine Finset.sum_nbij' (fun k => -k) (fun m => -m) (fun k hk => hA.simetrico k hk)
      (fun m hm => hA.simetrico m hm) (fun k _ => neg_neg k) (fun m _ => neg_neg m) ?_
    intro k _
    rfl
  -- passo 2: H(l,m) + H(m,l) = 0
  have par : ∀ l m, H l m + H m l = 0 := by
    intro l m
    simp only [hH]
    have hc : -(m + l) = -(l + m) := by rw [add_comm]
    rw [hc]
    split_ifs with hj
    · have hdiv := hA.divLivre _ hj
      rw [dot_kC_neg, dot_kC_add] at hdiv
      rw [dot_comm (u m) (u l)]
      have : dot (u (-(l + m))) (kC l) + dot (u (-(l + m))) (kC m) = 0 := by
        linear_combination -hdiv
      linear_combination (2 * Real.pi * I * dot (u l) (u m)) * this
    · simp
  -- passo 3: S = Σ_m Σ_l H l m;  S + S = 0
  rw [step1]
  have hS : (∑ m ∈ K, ∑ l ∈ K, H l m) + (∑ m ∈ K, ∑ l ∈ K, H l m) = 0 := by
    conv_lhs => arg 2; rw [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun l _ => par l m
  have h2 : (2 : ℂ) * (∑ m ∈ K, ∑ l ∈ K, H l m) = 0 := by rw [two_mul]; exact hS
  rcases mul_eq_zero.mp h2 with h | h
  · norm_num at h
  · exact h

/-! ### Projeção de Leray -/

/-- `P_k v = v − (v·k / k·k) k`. -/
noncomputable def leray (k : Modo) (v : Vec) : Vec := fun i =>
  v i - dot v (kC k) / dot (kC k) (kC k) * kC k i

theorem dot_kC_cj {K : Finset Modo} {u : Campo} (hA : Admissivel K u) {k : Modo} (hk : k ∈ K) :
    dot (kC k) (cj (u k)) = 0 := by
  have h := hA.divLivre k hk
  have : conj (dot (u k) (kC k)) = 0 := by rw [h, map_zero]
  rw [conj_dot, cj_kC, dot_comm] at this
  exact this

/-- **Leray não altera o emparelhamento** com campos de divergência nula. -/
theorem leray_par {K : Finset Modo} {u : Campo} (hA : Admissivel K u) {k : Modo} (hk : k ∈ K)
    (v : Vec) : dot (leray k v) (cj (u k)) = dot v (cj (u k)) := by
  have h0 := dot_kC_cj hA hk
  have e : dot (leray k v) (cj (u k)) =
      dot v (cj (u k)) - (dot v (kC k) / dot (kC k) (kC k)) * dot (kC k) (cj (u k)) := by
    simp only [leray, dot]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [e, h0, mul_zero, sub_zero]

/-! ### O campo de Galerkin e a energia -/

/-- `|2πk|²`. -/
noncomputable def lam (k : Modo) : ℝ := 4 * Real.pi ^ 2 * ∑ i, ((k i : ℤ) : ℝ) ^ 2

theorem lam_nonneg (k : Modo) : 0 ≤ lam k := by
  unfold lam; positivity

/-- `V(u)_k = −ν|2πk|² û_k − P_k N(u)_k + f̂_k`. -/
noncomputable def campoG (K : Finset Modo) (ν : ℝ) (f u : Campo) (k : Modo) : Vec := fun i =>
  -((ν * lam k : ℝ) : ℂ) * u k i - leray k (conv K u k) i + f k i

/-- **Identidade de energia estática.** -/
theorem energia_estatica {K : Finset Modo} {u : Campo} (hA : Admissivel K u) (ν : ℝ) (f : Campo) :
    ∑ k ∈ K, dot (campoG K ν f u k) (cj (u k)) =
      -(∑ k ∈ K, ((ν * lam k : ℝ) : ℂ) * nsq (u k)) + ∑ k ∈ K, dot (f k) (cj (u k)) := by
  have e : ∀ k ∈ K, dot (campoG K ν f u k) (cj (u k)) =
      -(((ν * lam k : ℝ) : ℂ) * nsq (u k)) - dot (conv K u k) (cj (u k)) + dot (f k) (cj (u k)) := by
    intro k hk
    rw [← leray_par hA hk (conv K u k)]
    simp only [dot, campoG, nsq]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h0 : ∑ k ∈ K, dot (conv K u k) (cj (u k)) = 0 := parConv_zero hA
  rw [h0, sub_zero, Finset.sum_neg_distrib]

/-- Energia `E(u) = Σ_{k∈K} |û_k|²`. -/
noncomputable def energia (K : Finset Modo) (u : Campo) : ℂ := ∑ k ∈ K, nsq (u k)

theorem energia_im (K : Finset Modo) (u : Campo) : (energia K u).im = 0 := by
  unfold energia; rw [Complex.im_sum]; exact Finset.sum_eq_zero fun k _ => nsq_im _

/-- Derivada da energia ao longo de uma trajetória diferenciável. -/
theorem hasDerivAt_energia (K : Finset Modo) (u : ℝ → Campo) (u' : Campo) (t : ℝ)
    (hu : ∀ k i, HasDerivAt (fun s => u s k i) (u' k i) t) :
    HasDerivAt (fun s => energia K (u s))
      (∑ k ∈ K, (dot (u' k) (cj (u t k)) + dot (u t k) (cj (u' k)))) t := by
  unfold energia nsq dot cj
  have hk : ∀ k ∈ K, HasDerivAt (fun s => ∑ i, u s k i * conj (u s k i))
      (∑ i, u' k i * conj (u t k i) + ∑ i, u t k i * conj (u' k i)) t := by
    intro k _
    rw [← Finset.sum_add_distrib]
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin 3)), HasDerivAt (fun s => u s k i * conj (u s k i))
        (u' k i * conj (u t k i) + u t k i * conj (u' k i)) t := by
      intro i _
      have h1 := hu k i
      have h2 : HasDerivAt (fun s => conj (u s k i)) (conj (u' k i)) t := by
        have h3 := HasDerivAt.star (𝕜 := ℝ) (F := ℂ) h1
        simpa using h3
      have := h1.mul h2
      convert this using 1
    exact HasDerivAt.fun_sum hi
  exact HasDerivAt.fun_sum hk

/-- **Identidade de energia de Galerkin**: ao longo de uma solução admissível,
`dE/dt = X + conj X` com `X = −Σ ν|2πk|²|û_k|² + Σ f̂_k · conj û_k`. -/
theorem identidade_energia (K : Finset Modo) (ν : ℝ) (f : Campo) (u : ℝ → Campo) (t : ℝ)
    (hA : Admissivel K (u t))
    (hu : ∀ k i, HasDerivAt (fun s => u s k i) (campoG K ν f (u t) k i) t) :
    HasDerivAt (fun s => energia K (u s))
      ((-(∑ k ∈ K, ((ν * lam k : ℝ) : ℂ) * nsq (u t k)) + ∑ k ∈ K, dot (f k) (cj (u t k))) +
        conj (-(∑ k ∈ K, ((ν * lam k : ℝ) : ℂ) * nsq (u t k)) + ∑ k ∈ K, dot (f k) (cj (u t k))))
      t := by
  have h := hasDerivAt_energia K u (campoG K ν f (u t)) t hu
  convert h using 1
  rw [Finset.sum_add_distrib, energia_estatica hA ν f]
  congr 1
  rw [← energia_estatica hA ν f, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [conj_dot, cj_cj, dot_comm]

/-- Sem força e com `ν ≥ 0`, a derivada da energia (parte real) é `≤ 0`. -/
theorem derivada_energia_nonpos (K : Finset Modo) {ν : ℝ} (hν : 0 ≤ ν) (u : Campo) :
    ((-(∑ k ∈ K, ((ν * lam k : ℝ) : ℂ) * nsq (u k)) + ∑ k ∈ K, dot ((fun _ _ => 0 : Campo) k) (cj (u k))) +
      conj (-(∑ k ∈ K, ((ν * lam k : ℝ) : ℂ) * nsq (u k)) +
        ∑ k ∈ K, dot ((fun _ _ => 0 : Campo) k) (cj (u k)))).re ≤ 0 := by
  have hz : ∀ k, dot ((fun _ _ => 0 : Campo) k) (cj (u k)) = 0 := by
    intro k; unfold dot; simp
  simp only [hz, Finset.sum_const_zero, add_zero, map_neg, map_sum, Complex.add_re,
    Complex.neg_re, Complex.re_sum, Complex.conj_re]
  have : ∀ k ∈ K, 0 ≤ (((ν * lam k : ℝ) : ℂ) * nsq (u k)).re := by
    intro k _
    rw [Complex.re_ofReal_mul]
    exact mul_nonneg (mul_nonneg hν (lam_nonneg k)) (nsq_re_nonneg _)
  have h1 := Finset.sum_nonneg this
  linarith

/-- **A energia decresce** (sem força, `ν ≥ 0`): ao longo de uma solução admissível, `E(t) ≤ E(0)` para `t ≥ 0`. -/
theorem energia_decresce (K : Finset Modo) {ν : ℝ} (hν : 0 ≤ ν) (u : ℝ → Campo)
    (hA : ∀ t, Admissivel K (u t))
    (hu : ∀ t k i, HasDerivAt (fun s => u s k i) (campoG K ν (fun _ _ => 0) (u t) k i) t)
    {t : ℝ} (ht0 : 0 ≤ t) :
    (energia K (u t)).re ≤ (energia K (u 0)).re := by
  have hd : ∀ s, HasDerivAt (fun r => (energia K (u r)).re)
      ((-(∑ k ∈ K, ((ν * lam k : ℝ) : ℂ) * nsq (u s k)) +
          ∑ k ∈ K, dot ((fun _ _ => 0 : Campo) k) (cj (u s k))) +
        conj (-(∑ k ∈ K, ((ν * lam k : ℝ) : ℂ) * nsq (u s k)) +
          ∑ k ∈ K, dot ((fun _ _ => 0 : Campo) k) (cj (u s k)))).re s := by
    intro s
    have h := identidade_energia K ν _ u s (hA s) (hu s)
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h
    have e1 : (⇑Complex.reCLM ∘ fun s => energia K (u s)) = fun r => (energia K (u r)).re := by
      funext r; simp
    rw [e1, Complex.reCLM_apply] at h2
    exact h2
  have hanti : Antitone (fun r => (energia K (u r)).re) := by
    refine antitone_of_deriv_nonpos (fun s => (hd s).differentiableAt) fun s => ?_
    rw [(hd s).deriv]
    exact derivada_energia_nonpos K hν (u s)
  exact hanti ht0

end ATK.BaseGalerkinNS

#print axioms ATK.BaseGalerkinNS.dot_comm
#print axioms ATK.BaseGalerkinNS.dot_kC_add
#print axioms ATK.BaseGalerkinNS.dot_kC_neg
#print axioms ATK.BaseGalerkinNS.conj_dot
#print axioms ATK.BaseGalerkinNS.cj_kC
#print axioms ATK.BaseGalerkinNS.cj_cj
#print axioms ATK.BaseGalerkinNS.nsq_im
#print axioms ATK.BaseGalerkinNS.nsq_re_nonneg
#print axioms ATK.BaseGalerkinNS.dot_conv
#print axioms ATK.BaseGalerkinNS.parConv_zero
#print axioms ATK.BaseGalerkinNS.dot_kC_cj
#print axioms ATK.BaseGalerkinNS.leray_par
#print axioms ATK.BaseGalerkinNS.lam_nonneg
#print axioms ATK.BaseGalerkinNS.energia_estatica
#print axioms ATK.BaseGalerkinNS.energia_im
#print axioms ATK.BaseGalerkinNS.hasDerivAt_energia
#print axioms ATK.BaseGalerkinNS.identidade_energia
#print axioms ATK.BaseGalerkinNS.derivada_energia_nonpos
#print axioms ATK.BaseGalerkinNS.energia_decresce
