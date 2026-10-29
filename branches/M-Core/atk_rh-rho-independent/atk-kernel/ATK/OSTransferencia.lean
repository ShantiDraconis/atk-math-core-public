import ATK.OSLacuna
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
# ATK — B7: reconstrução de Osterwalder–Schrader no tempo (espaço de Hilbert e transferência)

Camadas OS-1…OS-3 do ataque a B7. Dados de Osterwalder–Schrader no tempo (`DadosOS`): um espaço
vetorial complexo `V` (observáveis de tempo positivo), a forma `B(f, g) = ⟨Θf, g⟩` — hermitiana e
**positiva por reflexão** (`Re B(f, f) ≥ 0`) —, as translações temporais `S(t)`, `t ≥ 0`
(semigrupo, simétricas para `B`, com crescimento no máximo polinomial em `t`) e um vácuo invariante `Ω`.

* **OS-1** (`Hil`): o espaço de Hilbert físico é o completamento do espaço pré-hilbertiano
  `(V, B)` (o quociente pelos vetores nulos está embutido no completamento); `ι : V → Hil` tem
  imagem densa e `⟪ι f, ι g⟫ = B(f, g)`.
* **OS-2** (`norm_S_le`): `‖S(t) f‖ ≤ ‖f‖` — a contração vem só da positividade e do
  crescimento polinomial em `t` (temperança): iteração de Cauchy–Schwarz `‖S(t) f‖² ≤ ‖f‖ ‖S(2t) f‖`
  e o duplo exponencial vence o exponencial (`dupla_exp`).
* **OS-3** (`P`): a matriz de transferência `P(t) = e^{−tH}` em `Hil`: semigrupo, autoadjunta,
  contração, positiva, `P(t) Ω = Ω`.
* **Lacuna** (`lacuna_OS`): se as correlações conexas decaem como `e^{−m t}`, então
  `‖P(t) w‖ ≤ e^{−m t} ‖w‖` para todo `w ⊥ Ω` — a segunda metade da ponte `OSReconstruction`
  (`ATK.OSLacuna`).

O que falta para a ponte B7 completa: as translações espaciais e as rotações (covariância
euclidiana ⇒ Poincaré por continuação analítica), os campos (distribuições de Wightman) e o
modelo genuíno de L5. **CLOSED_MATH continua false.**
-/

open scoped InnerProductSpace ComplexConjugate

namespace ATK.OSTransferencia

/-! ### Uma iteração de Cauchy–Schwarz -/

/-- O duplo exponencial vence o exponencial: `A Bⁿ < L^{2ⁿ}` para algum `n`. -/
theorem dupla_exp {L A B : ℝ} (hL : 1 < L) (hB : 1 ≤ B) : ∃ n : ℕ, A * B ^ n < L ^ (2 ^ n) := by
  -- `L^{2^m} ≥ 2B`
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * B / (L - 1))
  have hL0 : 0 < L - 1 := by linarith
  have hQ : 2 * B ≤ L ^ (2 ^ m) := by
    have h1 : 1 + (m : ℝ) * (L - 1) ≤ L ^ m := by
      have := one_add_mul_le_pow (a := L - 1) (by linarith) m
      simpa using this
    have h2 : L ^ m ≤ L ^ (2 ^ m) := pow_le_pow_right₀ hL.le (Nat.lt_two_pow_self).le
    rw [div_lt_iff₀ hL0] at hm
    nlinarith
  set Q : ℝ := L ^ (2 ^ m) with hQdef
  have hQ1 : 1 ≤ Q := by linarith
  -- `2^j > A B^m`
  obtain ⟨j, hj⟩ := exists_nat_gt (A * B ^ m)
  have hj2 : (j : ℝ) < 2 ^ j := by exact_mod_cast Nat.lt_two_pow_self
  refine ⟨m + j, ?_⟩
  have e1 : L ^ (2 ^ (m + j)) = Q ^ (2 ^ j) := by rw [hQdef, ← pow_mul, pow_add]
  have h3 : Q ^ (j + 1) ≤ Q ^ (2 ^ j) := pow_le_pow_right₀ hQ1 (Nat.lt_two_pow_self)
  have h4 : (2 * B) ^ j ≤ Q ^ j := pow_le_pow_left₀ (by linarith) hQ j
  have hBj : 0 < B ^ j := pow_pos (by linarith) j
  have h5 : A * B ^ (m + j) < 2 ^ j * B ^ j := by
    rw [pow_add, ← mul_assoc]
    exact mul_lt_mul_of_pos_right (hj.trans hj2) hBj
  rw [e1]
  calc A * B ^ (m + j) < 2 ^ j * B ^ j := h5
    _ = (2 * B) ^ j := by rw [mul_pow]
    _ ≤ Q ^ j := h4
    _ ≤ Q ^ (j + 1) := pow_le_pow_right₀ hQ1 (Nat.le_succ j)
    _ ≤ Q ^ (2 ^ j) := h3

/-- Se `aₙ² ≤ c aₙ₊₁` e `aₙ² ≤ M Rⁿ` (crescimento no máximo exponencial em `n`, isto é,
polinomial no tempo `2ⁿ t`), então `a₀ ≤ c`. -/
theorem contracao_iter {a : ℕ → ℝ} {c M R : ℝ} (hc : 0 ≤ c) (ha : ∀ n, 0 ≤ a n)
    (h : ∀ n, a n ^ 2 ≤ c * a (n + 1)) (hR : 1 ≤ R) (hM : ∀ n, a n ^ 2 ≤ M * R ^ n) :
    a 0 ≤ c := by
  by_contra hlt
  push_neg at hlt
  rcases hc.eq_or_lt with hc0 | hcpos
  · have h0 := h 0
    rw [← hc0, zero_mul] at h0
    have : a 0 = 0 := pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h0 (sq_nonneg _))
    rw [← hc0] at hlt
    linarith
  set q : ℝ := a 0 / c with hq
  have hq1 : 1 < q := by rw [hq, one_lt_div hcpos]; exact hlt
  have hlow : ∀ n, q ^ (2 ^ n) * c ≤ a n := by
    intro n
    induction n with
    | zero => rw [hq]; simp; field_simp; rfl
    | succ n ih =>
      have h1 := h n
      have h2 : (q ^ (2 ^ n) * c) ^ 2 ≤ a n ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (pow_nonneg (by linarith) _) hc) ih 2
      have h3 : (q ^ (2 ^ n) * c) ^ 2 = (q ^ (2 ^ (n + 1)) * c) * c := by
        rw [pow_succ 2 n, pow_mul]; ring
      rw [h3] at h2
      have := h2.trans h1
      rw [mul_comm c (a (n + 1))] at this
      exact le_of_mul_le_mul_right this hcpos
  have hL : 1 < q ^ 2 := by nlinarith
  obtain ⟨n, hn⟩ := dupla_exp (A := M / c ^ 2) hL hR
  have hc2 : 0 < c ^ 2 := by positivity
  have h1 : (q ^ (2 ^ n) * c) ^ 2 ≤ a n ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (pow_nonneg (by linarith) _) hc) (hlow n) 2
  have h2 : (q ^ (2 ^ n) * c) ^ 2 = (q ^ 2) ^ (2 ^ n) * c ^ 2 := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (2 ^ n) 2]
  have h3 : (q ^ 2) ^ (2 ^ n) * c ^ 2 ≤ M * R ^ n := by
    rw [← h2]; exact h1.trans (hM n)
  have h4 : M / c ^ 2 * R ^ n * c ^ 2 = M * R ^ n := by field_simp
  have h5 := mul_lt_mul_of_pos_right hn hc2
  rw [h4] at h5
  linarith

/-! ### Os dados -/

/-- **Dados de Osterwalder–Schrader no tempo.** `B(f, g) = ⟨Θf, g⟩` é hermitiana e positiva por
reflexão; `S(t)` são as translações temporais (`t ≥ 0`); `Ω` é o vácuo. -/
structure DadosOS (V : Type*) [AddCommGroup V] [Module ℂ V] where
  /-- A forma de reflexão `⟨Θf, g⟩`. -/
  B : V → V → ℂ
  conj_symm : ∀ f g, conj (B g f) = B f g
  /-- **Positividade por reflexão.** -/
  pos : ∀ f, 0 ≤ (B f f).re
  add_left : ∀ f f' g, B (f + f') g = B f g + B f' g
  smul_left : ∀ (c : ℂ) f g, B (c • f) g = conj c * B f g
  /-- As translações temporais. -/
  S : ℝ → V →ₗ[ℂ] V
  S_zero : S 0 = LinearMap.id
  S_add : ∀ s t, 0 ≤ s → 0 ≤ t → S (s + t) = (S s).comp (S t)
  S_symm : ∀ t, 0 ≤ t → ∀ f g, B f (S t g) = B (S t f) g
  /-- Crescimento no máximo polinomial (temperança). -/
  S_bdd : ∀ f, ∃ M : ℝ, ∃ N : ℕ, ∀ t, 0 ≤ t → (B (S t f) (S t f)).re ≤ M * (1 + t) ^ N
  /-- O vácuo. -/
  Ω : V
  S_Ω : ∀ t, 0 ≤ t → S t Ω = Ω
  B_ΩΩ : B Ω Ω = 1

namespace DadosOS

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (D : DadosOS V)

/-- A estrutura pré-hilbertiana `(V, B)`. -/
def core : PreInnerProductSpace.Core ℂ V where
  inner := D.B
  conj_inner_symm := D.conj_symm
  re_inner_nonneg := D.pos
  add_left := D.add_left
  smul_left := fun x y r => D.smul_left r x y

theorem B_add_right (f g g' : V) : D.B f (g + g') = D.B f g + D.B f g' := by
  rw [← D.conj_symm, D.add_left, map_add, D.conj_symm, D.conj_symm]

theorem B_smul_right (c : ℂ) (f g : V) : D.B f (c • g) = c * D.B f g := by
  rw [← D.conj_symm, D.smul_left, map_mul, Complex.conj_conj, D.conj_symm]

theorem B_sub_left (f f' g : V) : D.B (f - f') g = D.B f g - D.B f' g := by
  have e : f - f' = f + (-1 : ℂ) • f' := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, D.add_left, D.smul_left, map_neg, map_one]
  ring

theorem B_sub_right (f g g' : V) : D.B f (g - g') = D.B f g - D.B f g' := by
  have e : g - g' = g + (-1 : ℂ) • g' := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, B_add_right, B_smul_right]
  ring

/-- O espaço pré-hilbertiano `(V, B)` (sinônimo de tipo). -/
def Pre (_D : DadosOS V) : Type _ := V

instance : AddCommGroup D.Pre := inferInstanceAs (AddCommGroup V)

instance : Module ℂ D.Pre := inferInstanceAs (Module ℂ V)

noncomputable instance : SeminormedAddCommGroup D.Pre :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ D.Pre _ _ _ D.core

noncomputable instance : InnerProductSpace ℂ D.Pre := InnerProductSpace.ofCore D.core

instance : IsBoundedSMul ℂ D.Pre := NormedSpace.toIsBoundedSMul

/-- `V` visto em `(V, B)`. -/
def toP (f : V) : D.Pre := f

theorem toP_sub (f g : V) : D.toP (f - g) = D.toP f - D.toP g := rfl

theorem toP_smul (c : ℂ) (f : V) : D.toP (c • f) = c • D.toP f := rfl

/-- **OS-1: o espaço de Hilbert físico.** -/
abbrev Hil : Type _ := UniformSpace.Completion D.Pre

/-- A aplicação canônica `V → Hil`. -/
noncomputable def ι (f : V) : D.Hil := ((D.toP f : D.Pre) : UniformSpace.Completion D.Pre)

theorem inner_pre (f g : V) : ⟪D.toP f, D.toP g⟫_ℂ = D.B f g := rfl

theorem inner_ι (f g : V) : ⟪D.ι f, D.ι g⟫_ℂ = D.B f g := by
  unfold ι
  rw [UniformSpace.Completion.inner_coe, inner_pre]

theorem norm_pre_sq (f : V) : ‖D.toP f‖ ^ 2 = (D.B f f).re :=
  norm_sq_eq_re_inner (𝕜 := ℂ) (D.toP f)

theorem ι_sub (f g : V) : D.ι (f - g) = D.ι f - D.ι g := by
  unfold ι
  rw [toP_sub, UniformSpace.Completion.coe_sub]

theorem ι_smul (c : ℂ) (f : V) : D.ι (c • f) = c • D.ι f := by
  unfold ι
  rw [toP_smul, UniformSpace.Completion.coe_smul]

theorem denseRange_ι : DenseRange D.ι :=
  UniformSpace.Completion.denseRange_coe (α := D.Pre)

theorem norm_ιΩ : ‖D.ι D.Ω‖ = 1 := by
  have h : ‖D.ι D.Ω‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_ι, D.B_ΩΩ]
    rfl
  have h0 := norm_nonneg (D.ι D.Ω)
  nlinarith [sq_nonneg (‖D.ι D.Ω‖ - 1)]

/-! ### OS-2: contração -/

theorem S_S (t : ℝ) (ht : 0 ≤ t) (f : V) : D.S t (D.S t f) = D.S (2 * t) f := by
  rw [two_mul, D.S_add t t ht ht, LinearMap.comp_apply]

theorem normS_sq (t : ℝ) (ht : 0 ≤ t) (f : V) :
    ‖D.toP (D.S t f)‖ ^ 2 = (D.B f (D.S (2 * t) f)).re := by
  rw [norm_pre_sq, ← S_S D t ht, D.S_symm t ht f (D.S t f)]

/-- **OS-2: as translações temporais são contrações** para a norma de reflexão. -/
theorem norm_S_le (t : ℝ) (ht : 0 ≤ t) (f : V) : ‖D.toP (D.S t f)‖ ≤ ‖D.toP f‖ := by
  obtain ⟨M, N, hM⟩ := D.S_bdd f
  set a : ℕ → ℝ := fun n => ‖D.toP (D.S ((2 : ℝ) ^ n * t) f)‖ with ha
  have hn : ∀ n : ℕ, 0 ≤ (2 : ℝ) ^ n * t := fun n => mul_nonneg (pow_nonneg (by norm_num) _) ht
  have h0 : a 0 = ‖D.toP (D.S t f)‖ := by simp [ha]
  rw [← h0]
  have hR : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
  refine contracao_iter (M := max M 0 * (1 + t) ^ N) (R := (2 : ℝ) ^ N) (norm_nonneg _)
    (fun n => norm_nonneg _) (fun n => ?_) hR (fun n => ?_)
  · -- `aₙ² ≤ ‖f‖ aₙ₊₁`
    show ‖D.toP (D.S ((2 : ℝ) ^ n * t) f)‖ ^ 2 ≤
      ‖D.toP f‖ * ‖D.toP (D.S ((2 : ℝ) ^ (n + 1) * t) f)‖
    rw [normS_sq D _ (hn n)]
    have e : 2 * ((2 : ℝ) ^ n * t) = (2 : ℝ) ^ (n + 1) * t := by rw [pow_succ]; ring
    rw [e, ← inner_pre]
    exact (Complex.re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)
  · -- crescimento polinomial
    show ‖D.toP (D.S ((2 : ℝ) ^ n * t) f)‖ ^ 2 ≤ max M 0 * (1 + t) ^ N * ((2 : ℝ) ^ N) ^ n
    rw [norm_pre_sq]
    have h1 := hM _ (hn n)
    have h2 : (1 + (2 : ℝ) ^ n * t) ^ N ≤ ((1 + t) * 2 ^ n) ^ N := by
      have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      exact pow_le_pow_left₀ (by positivity) (by nlinarith) N
    have h3 : ((1 + t) * 2 ^ n) ^ N = (1 + t) ^ N * ((2 : ℝ) ^ N) ^ n := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n N]
    calc (D.B (D.S ((2 : ℝ) ^ n * t) f) (D.S ((2 : ℝ) ^ n * t) f)).re
        ≤ M * (1 + (2 : ℝ) ^ n * t) ^ N := h1
      _ ≤ max M 0 * (1 + (2 : ℝ) ^ n * t) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max M 0 * (((1 + t) * 2 ^ n) ^ N) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = max M 0 * (1 + t) ^ N * ((2 : ℝ) ^ N) ^ n := by rw [h3]; ring

/-- `S(t)` como operador contínuo em `(V, B)` (zero para `t < 0`). -/
noncomputable def SL (t : ℝ) : D.Pre →L[ℂ] D.Pre :=
  if ht : 0 ≤ t then
    LinearMap.mkContinuous (D.S t : D.Pre →ₗ[ℂ] D.Pre) 1 (fun f => by
      rw [one_mul]; exact norm_S_le D t ht f)
  else 0

theorem SL_apply {t : ℝ} (ht : 0 ≤ t) (f : V) : D.SL t (D.toP f) = D.toP (D.S t f) := by
  rw [SL, dif_pos ht]
  rfl

/-! ### OS-3: a matriz de transferência -/

/-- **A matriz de transferência** `P(t) = e^{−tH}` em `Hil`. -/
noncomputable def P (t : ℝ) : D.Hil →L[ℂ] D.Hil := (D.SL t).completion

theorem P_ι {t : ℝ} (ht : 0 ≤ t) (f : V) : D.P t (D.ι f) = D.ι (D.S t f) := by
  unfold P ι
  rw [ContinuousLinearMap.completion_apply_coe, SL_apply D ht]

/-- Igualdade de operadores contínuos em `Hil` testada em `ι(V)`. -/
theorem ext_ι {A B : D.Hil →L[ℂ] D.Hil} (h : ∀ f : V, A (D.ι f) = B (D.ι f)) : A = B := by
  ext w
  exact D.denseRange_ι.induction_on w (isClosed_eq A.continuous B.continuous) h

theorem P_zero : D.P 0 = ContinuousLinearMap.id ℂ D.Hil := by
  refine ext_ι D (fun f => ?_)
  rw [P_ι D le_rfl, D.S_zero, LinearMap.id_apply, ContinuousLinearMap.id_apply]

theorem P_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) : D.P (s + t) = (D.P s).comp (D.P t) := by
  refine ext_ι D (fun f => ?_)
  rw [P_ι D (add_nonneg hs ht), ContinuousLinearMap.comp_apply, P_ι D ht, P_ι D hs,
    D.S_add s t hs ht, LinearMap.comp_apply]

theorem P_symm (t : ℝ) (ht : 0 ≤ t) (u v : D.Hil) : ⟪D.P t u, v⟫_ℂ = ⟪u, D.P t v⟫_ℂ := by
  refine D.denseRange_ι.induction_on₂ (p := fun u v => ⟪D.P t u, v⟫_ℂ = ⟪u, D.P t v⟫_ℂ)
    (isClosed_eq (by fun_prop) (by fun_prop)) (fun f g => ?_) u v
  rw [P_ι D ht, P_ι D ht, inner_ι, inner_ι, D.S_symm t ht]

theorem norm_P_le (t : ℝ) (ht : 0 ≤ t) (w : D.Hil) : ‖D.P t w‖ ≤ ‖w‖ := by
  refine D.denseRange_ι.induction_on w
    (isClosed_le (D.P t).continuous.norm continuous_norm) (fun f => ?_)
  rw [P_ι D ht]
  unfold ι
  rw [UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  exact norm_S_le D t ht f

theorem P_pos (t : ℝ) (ht : 0 ≤ t) (w : D.Hil) : 0 ≤ (⟪w, D.P t w⟫_ℂ).re := by
  have e : D.P t = (D.P (t / 2)).comp (D.P (t / 2)) := by
    rw [← P_add D _ _ (by linarith) (by linarith)]; congr 1; ring
  rw [e, ContinuousLinearMap.comp_apply, ← P_symm D _ (by linarith)]
  have h : (⟪D.P (t / 2) w, D.P (t / 2) w⟫_ℂ).re = ‖D.P (t / 2) w‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  rw [h]
  exact sq_nonneg _

theorem P_Ω (t : ℝ) (ht : 0 ≤ t) : D.P t (D.ι D.Ω) = D.ι D.Ω := by
  rw [P_ι D ht, D.S_Ω t ht]

/-! ### Lacuna -/

/-- **Decaimento exponencial das correlações conexas ⇒ lacuna `≥ m`** para a matriz de
transferência reconstruída: `‖P(t) w‖ ≤ e^{−m t} ‖w‖` para todo `w ⊥ Ω`. -/
theorem lacuna_OS {m : ℝ}
    (hclu : ∀ f : V, ∃ C, ∀ t, 0 ≤ t →
      ‖D.B f (D.S t f) - D.B f D.Ω * D.B D.Ω f‖ ≤ C * Real.exp (-(m * t)))
    (w : D.Hil) (hw : ⟪D.ι D.Ω, w⟫_ℂ = 0) (t : ℝ) (ht : 0 ≤ t) :
    ‖D.P t w‖ ≤ Real.exp (-(m * t)) * ‖w‖ := by
  set e : D.Hil := D.ι D.Ω with he
  set Pr : D.Hil → D.Hil := fun x => x - ⟪e, x⟫_ℂ • e with hPr
  set Dset : Set D.Hil := Pr '' Set.range D.ι with hDset
  -- `Pr (ι f) = ι (f − B(Ω, f) Ω)` e a correlação conexa
  have hdec : ∀ v ∈ Dset, ∃ C, ∀ t, 0 ≤ t → (⟪v, D.P t v⟫_ℂ).re ≤ C * Real.exp (-(m * t)) := by
    rintro v ⟨_, ⟨f, rfl⟩, rfl⟩
    obtain ⟨C, hC⟩ := hclu f
    refine ⟨C, fun t ht => ?_⟩
    set c : ℂ := D.B D.Ω f with hc
    have hv : Pr (D.ι f) = D.ι (f - c • D.Ω) := by
      simp only [hPr]
      rw [he, inner_ι, ι_sub, ι_smul]
    have hΩf : D.B D.Ω (D.S t f) = c := by rw [D.S_symm t ht, D.S_Ω t ht]
    have hcorr : D.B (f - c • D.Ω) (D.S t (f - c • D.Ω)) =
        D.B f (D.S t f) - D.B f D.Ω * D.B D.Ω f := by
      rw [map_sub, map_smul, D.S_Ω t ht, B_sub_left, B_sub_right, B_sub_right, D.smul_left,
        D.smul_left, B_smul_right, B_smul_right, D.B_ΩΩ, hΩf]
      ring
    rw [hv, P_ι D ht, inner_ι, hcorr]
    exact (Complex.re_le_norm _).trans (hC t ht)
  -- `w = Pr w` está no fecho de `Dset`
  have hPrc : Continuous Pr := by
    simp only [hPr]
    fun_prop
  have hwPr : Pr w = w := by simp only [hPr, hw, zero_smul, sub_zero]
  have hmem : w ∈ closure Dset := by
    have h1 : Pr '' closure (Set.range D.ι) ⊆ closure Dset :=
      image_closure_subset_closure_image hPrc
    rw [(denseRange_ι D).closure_range] at h1
    exact h1 ⟨w, Set.mem_univ _, hwPr⟩
  exact ATK.OSLacuna.lacuna_de_decaimento (P_zero D) (P_add D) (P_symm D) hdec w hmem t ht

/-- **Unicidade do vácuo**: com decaimento de taxa `m > 0`, todo vetor invariante por algum
`P(t)`, `t > 0`, é múltiplo de `Ω`. -/
theorem vacuo_unico {m : ℝ} (hm : 0 < m)
    (hclu : ∀ f : V, ∃ C, ∀ t, 0 ≤ t →
      ‖D.B f (D.S t f) - D.B f D.Ω * D.B D.Ω f‖ ≤ C * Real.exp (-(m * t)))
    (w : D.Hil) {t : ℝ} (ht : 0 < t) (hw : D.P t w = w) :
    w = ⟪D.ι D.Ω, w⟫_ℂ • D.ι D.Ω := by
  set e : D.Hil := D.ι D.Ω with he
  set w' : D.Hil := w - ⟪e, w⟫_ℂ • e with hw'
  have hee : ⟪e, e⟫_ℂ = 1 := by rw [he, inner_ι, D.B_ΩΩ]
  set c : ℂ := ⟪e, w⟫_ℂ with hc
  have h1 : ⟪e, w - c • e⟫_ℂ = ⟪e, w⟫_ℂ - ⟪e, c • e⟫_ℂ := inner_sub_right e w (c • e)
  have h2 : ⟪e, c • e⟫_ℂ = c * ⟪e, e⟫_ℂ := inner_smul_right e e c
  have horth : ⟪e, w'⟫_ℂ = 0 := by
    rw [hw', h1, h2, hee, mul_one, sub_self]
  have h3 : D.P t (c • e) = c • D.P t e := (D.P t).map_smul c e
  have hinv : D.P t w' = w' := by
    rw [hw', map_sub, h3, hw, P_Ω D t ht.le]
  have hb := lacuna_OS D hclu w' horth t ht.le
  rw [hinv] at hb
  have hlt : Real.exp (-(m * t)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have h0 : ‖w'‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖w'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    nlinarith
  have : w' = 0 := norm_eq_zero.mp h0
  rw [hw', sub_eq_zero] at this
  exact this


end DadosOS

end ATK.OSTransferencia

#print axioms ATK.OSTransferencia.dupla_exp
#print axioms ATK.OSTransferencia.contracao_iter
#print axioms ATK.OSTransferencia.DadosOS.B_add_right
#print axioms ATK.OSTransferencia.DadosOS.B_smul_right
#print axioms ATK.OSTransferencia.DadosOS.B_sub_left
#print axioms ATK.OSTransferencia.DadosOS.B_sub_right
#print axioms ATK.OSTransferencia.DadosOS.toP_sub
#print axioms ATK.OSTransferencia.DadosOS.toP_smul
#print axioms ATK.OSTransferencia.DadosOS.inner_pre
#print axioms ATK.OSTransferencia.DadosOS.inner_ι
#print axioms ATK.OSTransferencia.DadosOS.norm_pre_sq
#print axioms ATK.OSTransferencia.DadosOS.ι_sub
#print axioms ATK.OSTransferencia.DadosOS.ι_smul
#print axioms ATK.OSTransferencia.DadosOS.denseRange_ι
#print axioms ATK.OSTransferencia.DadosOS.norm_ιΩ
#print axioms ATK.OSTransferencia.DadosOS.S_S
#print axioms ATK.OSTransferencia.DadosOS.normS_sq
#print axioms ATK.OSTransferencia.DadosOS.norm_S_le
#print axioms ATK.OSTransferencia.DadosOS.SL_apply
#print axioms ATK.OSTransferencia.DadosOS.P_ι
#print axioms ATK.OSTransferencia.DadosOS.ext_ι
#print axioms ATK.OSTransferencia.DadosOS.P_zero
#print axioms ATK.OSTransferencia.DadosOS.P_add
#print axioms ATK.OSTransferencia.DadosOS.P_symm
#print axioms ATK.OSTransferencia.DadosOS.norm_P_le
#print axioms ATK.OSTransferencia.DadosOS.P_pos
#print axioms ATK.OSTransferencia.DadosOS.P_Ω
#print axioms ATK.OSTransferencia.DadosOS.lacuna_OS
#print axioms ATK.OSTransferencia.DadosOS.vacuo_unico
