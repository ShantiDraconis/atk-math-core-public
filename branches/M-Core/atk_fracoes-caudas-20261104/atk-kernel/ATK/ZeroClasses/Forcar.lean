import ATK.ZeroClasses.Componentes

/-!
# ATK-ZERO-CLASSES — forçar um zero: o quarteto construído, o certificado de módulo mínimo, caudas e zeros booleanos

Rodada 23. O que se pode **forçar** e onde.

**1. O quarteto construído** (`Pq_eq_Q`, `Pq_zero_iff`, `Pq_refl`, `Pq_conj`, `quarteto_gigante`). O polinômio
`P(s) = ((s − ½)² − δ² + T²)² + 4T²δ²` é exatamente o `Q δ T` da rodada 19; seus zeros são **exatamente**
`½ ± δ ± iT`, ele tem as simetrias de `ξ`, e com `δ = 1/(2·10¹⁰⁰⁰+1)`, `T = 10¹⁰⁰` os quatro estão fora da linha.

**2. Somar não força** (`Xi_lambda_conj`, `Xi_lambda_refl`, `somar_nao_forca`). `Ξ_λ = ξ + λP` preserva as
simetrias (`λ` real), mas em cada zero `ρ` de `P`, `Ξ_λ(ρ) = ξ(ρ)`: `Ξ_λ(ρ) = 0 ⟺ ζ(ρ) = 0`.

**3. O certificado de módulo mínimo** (`certificado_modulo_minimo`, `certificado_E1`, `certificado_E1_refuta`).
Sem Rouché (ausente da Mathlib): se `‖f′(z) − f′(c)‖ ≤ L` no disco e `2|f(c)| + L·r < r|f′(c)|`, há um zero no disco
aberto. Com `‖f″‖ ≤ M₂`: `2|f(c)| + M₂r² < r|f′(c)|`. (A forma afiada `|f(c)| + M₂r²/2 < r|f′(c)|`, com unicidade,
precisa de Rouché: BUILD_PENDING.) Para `ζ` num disco fora da linha, o certificado refuta RH. Exemplos:
`exemplo_linear`, `exemplo_quadratico` (zero certificado em `Re > ½` para a função auxiliar), `contraexemplo`.

**4. Cauda por certificados** (`cauda_por_certificados`, `Hext`, `hext_iff`, `hext_refuta`,
`hext_quartetos`, `teoria_conjunta`). Infinitos certificados em discos disjuntos fora da linha ⟹ infinitos zeros
externos. `H_ext` (alturas ilimitadas) ⟺ conjunto externo infinito; `H_ext ⟹ ¬RH`; quartetos acima de toda altura.
Uma hipótese adicional `Q` (por exemplo `SAT ∉ P`) só se **compõe**: `H_ext → Q → ¬RH ∧ Q`.

**5. Zeros booleanos e aritméticos** (`viol_eq_prod`, `R_zero_iff`, `sat_iff_zero`, `lacuna`, `lacuna_min`,
`exemplo_sat`, `exemplo_unsat`, `div_iff_zero`, `exemplo_84`). `R_φ(x) = Σ q_C(x)` com `q_C = ∏(1 − ℓ)`:
`φ ∈ SAT ⟺ ∃x, R_φ(x) = 0`, e **`R_φ(x) < 1 ⟹ R_φ(x) = 0`** (lacuna discreta — o que a `ζ` não tem).
`b ∣ a ⟺ ∃k, a − bk = 0`.

**6. Zero assintótico ≠ zero** (`limite_sem_zero`, `quase_polinomial`). `1/(n+1) → 0` sem nunca ser `0`;
`(log n)²/n → 0`, mas `n^{log n}` não é `O(nᵏ)` para nenhum `k`.
-/

open Complex ComplexConjugate Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.Forcar

open ATK.ZeroClasses ATK.ZeroClasses.Zeta ATK.ZeroClasses.Hipotetico ATK.ZeroClasses.Encontro
open ATK.BaseRiemannXi

/-! ## 1. O quarteto construído -/

/-- `P(s) = ((s − ½)² − δ² + T²)² + 4T²δ²`. -/
noncomputable def Pq (δ T : ℝ) (s : ℂ) : ℂ :=
  ((s - 1 / 2) ^ 2 - (δ : ℂ) ^ 2 + (T : ℂ) ^ 2) ^ 2 + 4 * (T : ℂ) ^ 2 * (δ : ℂ) ^ 2

/-- `P` é o `Q δ T` da rodada 19. -/
theorem Pq_eq_Q (δ T : ℝ) (s : ℂ) : Pq δ T s = ATK.ZeroClasses.Construcao.Q δ T s := by
  unfold Pq ATK.ZeroClasses.Construcao.Q; ring

/-- Os zeros de `P` são **exatamente** `½ ± δ ± iT`. -/
theorem Pq_zero_iff (δ T : ℝ) (s : ℂ) :
    Pq δ T s = 0 ↔ (s = 1 / 2 + δ + (T : ℂ) * I ∨ s = 1 / 2 + δ - (T : ℂ) * I) ∨
      (s = 1 / 2 - δ + (T : ℂ) * I ∨ s = 1 / 2 - δ - (T : ℂ) * I) := by
  rw [Pq_eq_Q]; exact ATK.ZeroClasses.Construcao.Q_zero_iff δ T s

theorem Pq_refl (δ T : ℝ) (s : ℂ) : Pq δ T (1 - s) = Pq δ T s := by
  rw [Pq_eq_Q, Pq_eq_Q]; exact ATK.ZeroClasses.Construcao.Q_eq_func δ T s

theorem Pq_conj (δ T : ℝ) (s : ℂ) : Pq δ T (conj s) = conj (Pq δ T s) := by
  rw [Pq_eq_Q, Pq_eq_Q]; exact ATK.ZeroClasses.Construcao.Q_conj δ T s

/-- Os quatro zeros de `P` estão fora da linha sempre que `δ ≠ 0`, nas alturas `±T`. -/
theorem quarteto_fora {δ T : ℝ} (hδ : δ ≠ 0) {s : ℂ} (h : Pq δ T s = 0) :
    s.re ≠ 1 / 2 ∧ (s.im = T ∨ s.im = -T) := by
  rcases (Pq_zero_iff δ T s).mp h with (rfl | rfl) | (rfl | rfl) <;> exact ⟨by simp [hδ], by simp⟩

/-- **O quarteto gigante**: com `δ = 1/(2·10¹⁰⁰⁰+1)`, `T = 10¹⁰⁰`, os quatro zeros de `P` estão fora da linha. -/
theorem quarteto_gigante {s : ℂ} (h : Pq (1 / (2 * 10 ^ 1000 + 1)) (10 ^ 100) s = 0) :
    s.re ≠ 1 / 2 ∧ (s.im = 10 ^ 100 ∨ s.im = -10 ^ 100) :=
  quarteto_fora (by positivity) h

/-! ## 2. Somar não força -/

/-- `Ξ_λ = ξ + λP`. -/
noncomputable def XiL (l δ T : ℝ) (s : ℂ) : ℂ := riemannXi s + (l : ℂ) * Pq δ T s

theorem Xi_lambda_refl (l δ T : ℝ) (s : ℂ) : XiL l δ T (1 - s) = XiL l δ T s := by
  unfold XiL; rw [riemannXi_one_sub, Pq_refl]

theorem Xi_lambda_conj (l δ T : ℝ) (s : ℂ) : XiL l δ T (conj s) = conj (XiL l δ T s) := by
  unfold XiL; rw [riemannXi_conj, Pq_conj, map_add, map_mul, Complex.conj_ofReal]

/-- **Somar não força**: num zero `ρ` de `P` na faixa, `Ξ_λ(ρ) = ξ(ρ)` e `Ξ_λ(ρ) = 0 ⟺ ζ(ρ) = 0`. -/
theorem somar_nao_forca {l δ T : ℝ} {ρ : ℂ} (hP : Pq δ T ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    XiL l δ T ρ = riemannXi ρ ∧ (XiL l δ T ρ = 0 ↔ riemannZeta ρ = 0) := by
  have hx : XiL l δ T ρ = riemannXi ρ := by unfold XiL; rw [hP, mul_zero, add_zero]
  have hs1 : ρ ≠ 1 := by intro h; rw [h, one_re] at h1; exact lt_irrefl _ h1
  exact ⟨hx, by rw [hx]; exact riemannXi_eq_zero_iff h0 hs1⟩

/-! ## 3. O certificado de módulo mínimo -/

/-- Cota inferior na fronteira: `‖f(z)‖ ≥ r‖f′(c)‖ − ‖f(c)‖ − L·r` para `‖z − c‖ = r`. -/
theorem cota_fronteira {f : ℂ → ℂ} {c : ℂ} {r L : ℝ}
    (hd : ∀ z ∈ closedBall c r, DifferentiableAt ℂ f z)
    (hL : ∀ z ∈ closedBall c r, ‖deriv f z - deriv f c‖ ≤ L) {z : ℂ} (hz : ‖z - c‖ = r) :
    r * ‖deriv f c‖ - ‖f c‖ - L * r ≤ ‖f z‖ := by
  set g : ℂ → ℂ := fun w => f w - deriv f c * w
  have hgd : ∀ w ∈ closedBall c r, DifferentiableAt ℂ g w := fun w hw =>
    (hd w hw).sub ((differentiableAt_id).const_mul _)
  have hgder : ∀ w ∈ closedBall c r, ‖deriv g w‖ ≤ L := by
    intro w hw
    have h : HasDerivAt (fun w => f w - deriv f c * w) (deriv f w - deriv f c) w := by
      convert (hd w hw).hasDerivAt.sub ((hasDerivAt_id w).const_mul (deriv f c)) using 1
      · rfl
      · ring
    show ‖deriv (fun w => f w - deriv f c * w) w‖ ≤ L
    rw [h.deriv]; exact hL w hw
  have hr : 0 ≤ r := hz ▸ norm_nonneg _
  have hzB : z ∈ closedBall c r := by rw [mem_closedBall, dist_eq_norm, hz]
  have hmv := (convex_closedBall c r).norm_image_sub_le_of_norm_deriv_le hgd hgder
    (mem_closedBall_self hr) hzB
  have e : f z = f c + deriv f c * (z - c) + (g z - g c) := by simp only [g]; ring
  rw [hz] at hmv
  have h1 : ‖deriv f c * (z - c)‖ = r * ‖deriv f c‖ := by rw [norm_mul, hz, mul_comm]
  have h2 : ‖deriv f c * (z - c)‖ ≤ ‖f z‖ + ‖f c‖ + ‖g z - g c‖ := by
    have : deriv f c * (z - c) = f z - f c - (g z - g c) := by rw [e]; ring
    rw [this]
    calc ‖f z - f c - (g z - g c)‖ ≤ ‖f z - f c‖ + ‖g z - g c‖ := norm_sub_le _ _
      _ ≤ ‖f z‖ + ‖f c‖ + ‖g z - g c‖ := by linarith [norm_sub_le (f z) (f c)]
  linarith

/-- **Certificado de módulo mínimo**: se `‖f′(z) − f′(c)‖ ≤ L` no disco fechado e `2|f(c)| + L·r < r|f′(c)|`, então
`f` tem um zero no disco **aberto** `B(c, r)`. -/
theorem certificado_modulo_minimo {f : ℂ → ℂ} {c : ℂ} {r L : ℝ} (hr : 0 < r)
    (hd : ∀ z ∈ closedBall c r, DifferentiableAt ℂ f z)
    (hL : ∀ z ∈ closedBall c r, ‖deriv f z - deriv f c‖ ≤ L)
    (h : 2 * ‖f c‖ + L * r < r * ‖deriv f c‖) :
    ∃ ρ ∈ ball c r, f ρ = 0 := by
  set B := r * ‖deriv f c‖ - ‖f c‖ - L * r with hB
  have hBc : ‖f c‖ < B := by rw [hB]; linarith
  have hfront : ∀ z, ‖z - c‖ = r → B ≤ ‖f z‖ := fun z hz => cota_fronteira hd hL hz
  by_contra hno
  push Not at hno
  have hne : ∀ z ∈ closedBall c r, f z ≠ 0 := by
    intro z hz h0
    rcases (mem_closedBall.mp hz).lt_or_eq with hlt | heq
    · exact hno z (mem_ball.mpr hlt) h0
    · have := hfront z (by rw [← dist_eq_norm]; exact heq)
      rw [h0, norm_zero] at this
      linarith [norm_nonneg (f c)]
  have hc0 : f c ≠ 0 := hne c (mem_closedBall_self hr.le)
  have hinv : DiffContOnCl ℂ (fun z => (f z)⁻¹) (ball c r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball c hr.ne']
    intro z hz
    exact ((hd z hz).inv (hne z hz)).differentiableWithinAt
  have hBpos : 0 < B := lt_of_le_of_lt (norm_nonneg _) hBc
  have hbound : ∀ z ∈ frontier (ball c r), ‖(fun z => (f z)⁻¹) z‖ ≤ B⁻¹ := by
    intro z hz
    rw [frontier_ball c hr.ne', mem_sphere, dist_eq_norm] at hz
    have h1 := hfront z hz
    simp only [norm_inv]
    exact inv_anti₀ hBpos h1
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hinv hbound
    (subset_closure (mem_ball_self hr))
  simp only [norm_inv] at hmax
  have hfcpos : 0 < ‖f c‖ := norm_pos_iff.mpr hc0
  have := (inv_le_inv₀ hfcpos hBpos).mp hmax
  linarith

/-- **Forma `E1`** com a segunda derivada: se `‖f″‖ ≤ M₂` no disco e `2|f(c)| + M₂r² < r|f′(c)|`, há um zero no disco. -/
theorem certificado_E1 {f : ℂ → ℂ} {c : ℂ} {r M₂ : ℝ} (hr : 0 < r)
    (hd : ∀ z ∈ closedBall c r, DifferentiableAt ℂ f z)
    (hd2 : ∀ z ∈ closedBall c r, DifferentiableAt ℂ (deriv f) z)
    (hM : ∀ z ∈ closedBall c r, ‖deriv (deriv f) z‖ ≤ M₂)
    (h : 2 * ‖f c‖ + M₂ * r ^ 2 < r * ‖deriv f c‖) :
    ∃ ρ ∈ ball c r, f ρ = 0 := by
  refine certificado_modulo_minimo (L := M₂ * r) hr hd (fun z hz => ?_) (by nlinarith)
  have := (convex_closedBall c r).norm_image_sub_le_of_norm_deriv_le hd2 hM (mem_closedBall_self hr.le) hz
  have hzr : ‖z - c‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hz
  have hM0 : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM c (mem_closedBall_self hr.le))
  calc ‖deriv f z - deriv f c‖ ≤ M₂ * ‖z - c‖ := this
    _ ≤ M₂ * r := mul_le_mul_of_nonneg_left hzr hM0

/-- **Para `ζ`**: um disco fora da linha que passa o certificado de módulo mínimo **refuta RH**. -/
theorem certificado_E1_refuta {c : ℂ} {r L : ℝ} (hr : 0 < r) (hD : DiscoFora c r)
    (hL : ∀ z ∈ closedBall c r, ‖deriv riemannZeta z - deriv riemannZeta c‖ ≤ L)
    (h : 2 * ‖riemannZeta c‖ + L * r < r * ‖deriv riemannZeta c‖) :
    (∃ ρ ∈ ball c r, ForaCritico ρ) ∧ ¬ RiemannHypothesis := by
  have hd : ∀ z ∈ closedBall c r, DifferentiableAt ℂ riemannZeta z := fun z hz =>
    differentiableAt_riemannZeta fun h1 => by
      have := (discoFora_pontos hD hz).2.1
      rw [h1, one_re] at this
      exact lt_irrefl _ this
  obtain ⟨ρ, hρ, h0⟩ := certificado_modulo_minimo hr hd hL h
  obtain ⟨a, b, e⟩ := discoFora_pontos hD (ball_subset_closedBall hρ)
  exact ⟨⟨ρ, hρ, ⟨⟨h0, a, b⟩, e⟩⟩, hFora_iff.mp ⟨ρ, h0, a, b, e⟩⟩

/-- O centro dos exemplos, `c = ¾ + 10i`. -/
noncomputable def cEx : ℂ := 3 / 4 + 10 * I

/-- **Exemplo linear**: `f(z) = z − (4/5 + 10i)` passa o certificado em `B(c, 1/8)`; o zero tem `Re > ½`. -/
theorem exemplo_linear :
    ∃ ρ ∈ ball cEx (1 / 8), ρ - (4 / 5 + 10 * I) = 0 ∧ 1 / 2 < ρ.re := by
  have hdf : ∀ z, HasDerivAt (fun z : ℂ => z - (4 / 5 + 10 * I)) 1 z := fun z =>
    (hasDerivAt_id z).sub_const _
  obtain ⟨ρ, hρ, h0⟩ := certificado_modulo_minimo (f := fun z => z - (4 / 5 + 10 * I)) (c := cEx) (r := 1 / 8) (L := 0)
    (by norm_num) (fun z _ => (hdf z).differentiableAt)
    (fun z _ => by rw [(hdf z).deriv, (hdf cEx).deriv]; simp) (by
      rw [(hdf cEx).deriv, norm_one]
      have e : cEx - (4 / 5 + 10 * I) = ((-1 / 20 : ℝ) : ℂ) := by
        unfold cEx; push_cast; ring
      simp only [e, Complex.norm_real, Real.norm_eq_abs]
      norm_num)
  refine ⟨ρ, hρ, h0, ?_⟩
  have : ρ = 4 / 5 + 10 * I := by linear_combination h0
  rw [this]; simp; norm_num

/-- **Exemplo quadrático**: `f(z) = (z − c) + ¼(z − c)² + 1/20` passa o certificado em `B(c, 1/8)` (`L = 1/16`). -/
theorem exemplo_quadratico :
    ∃ ρ ∈ ball cEx (1 / 8), (ρ - cEx) + 1 / 4 * (ρ - cEx) ^ 2 + 1 / 20 = 0 ∧ 1 / 2 < ρ.re := by
  set f : ℂ → ℂ := fun z => (z - cEx) + 1 / 4 * (z - cEx) ^ 2 + 1 / 20 with hf
  have hdf : ∀ z, HasDerivAt f (1 + 1 / 2 * (z - cEx)) z := by
    intro z
    have h1 := (hasDerivAt_id z).sub_const cEx
    have h2 := (h1.pow 2).const_mul (1 / 4 : ℂ)
    have h3 := (h1.add h2).add_const (1 / 20 : ℂ)
    convert h3 using 1
    · funext w; simp [hf]
    · simp; ring
  obtain ⟨ρ, hρ, h0⟩ := certificado_modulo_minimo (f := f) (c := cEx) (r := 1 / 8) (L := 1 / 16) (by norm_num)
    (fun z _ => (hdf z).differentiableAt)
    (fun z hz => by
      rw [(hdf z).deriv, (hdf cEx).deriv]
      rw [mem_closedBall, dist_eq_norm] at hz
      have e : 1 + 1 / 2 * (z - cEx) - (1 + 1 / 2 * (cEx - cEx)) = 1 / 2 * (z - cEx) := by ring
      rw [e, norm_mul]
      have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
      rw [this]; linarith)
    (by
      rw [(hdf cEx).deriv]
      simp only [hf, sub_self, mul_zero, add_zero, zero_add]
      norm_num)
  refine ⟨ρ, hρ, h0, ?_⟩
  have := Complex.abs_re_le_norm (ρ - cEx)
  rw [mem_ball, dist_eq_norm] at hρ
  have hre : (ρ - cEx).re = ρ.re - 3 / 4 := by simp [cEx]
  rw [hre, abs_le] at this
  linarith [this.1]

/-- **Contraexemplo**: `g(z) = 1 + (z − c)` não passa o certificado em `B(c, 1/8)`, e não tem zero lá. -/
theorem contraexemplo : ¬ (2 * ‖(1 : ℂ) + (cEx - cEx)‖ + 0 * (1 / 8) < 1 / 8 * ‖(1 : ℂ)‖) ∧
    ∀ z ∈ closedBall cEx (1 / 8), 1 + (z - cEx) ≠ 0 := by
  refine ⟨by simp; norm_num, fun z hz h => ?_⟩
  have e : z - cEx = -1 := by linear_combination h
  rw [mem_closedBall, dist_eq_norm, e] at hz
  norm_num at hz

/-! ## 4. Cauda por certificados e o mundo `H_ext` -/

/-- **Infinitos certificados em discos disjuntos fora da linha ⟹ infinitos zeros externos.** -/
theorem cauda_por_certificados {c : ℕ → ℂ} {r L : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hD : ∀ n, DiscoFora (c n) (r n))
    (hL : ∀ n, ∀ z ∈ closedBall (c n) (r n),
      ‖deriv riemannZeta z - deriv riemannZeta (c n)‖ ≤ L n)
    (h : ∀ n, 2 * ‖riemannZeta (c n)‖ + L n * r n < r n * ‖deriv riemannZeta (c n)‖)
    (hdisj : Pairwise fun m n => Disjoint (ball (c m) (r m)) (ball (c n) (r n))) :
    ATK.ZeroClasses.MundoFora.ForaSet.Infinite := by
  choose ρ hρ using fun n => (certificado_E1_refuta (hr n) (hD n) (hL n) (h n)).1
  refine Set.infinite_of_injective_forall_mem (f := ρ) (fun m n hmn => ?_) fun n => (hρ n).2
  by_contra hne
  exact Set.disjoint_left.mp (hdisj hne) (hρ m).1 (hmn ▸ (hρ n).1)

/-- `H_ext`: zeros fora da linha em alturas arbitrariamente grandes. -/
def Hext : Prop := ∀ T : ℝ, ∃ ρ, ForaCritico ρ ∧ T < ρ.im

/-- **`H_ext` ⟺ o conjunto de zeros externos é infinito.** -/
theorem hext_iff : Hext ↔ ATK.ZeroClasses.MundoFora.ForaSet.Infinite := by
  rw [ATK.ZeroClasses.Componentes.cauda_iff]
  constructor
  · intro h T
    obtain ⟨ρ, hρ, hT⟩ := h T
    exact ⟨ρ, hρ, lt_of_lt_of_le hT (le_abs_self _)⟩
  · intro h T
    obtain ⟨ρ, hρ, hT⟩ := h T
    rcases le_or_gt 0 ρ.im with hp | hn
    · exact ⟨ρ, hρ, by rwa [abs_of_nonneg hp] at hT⟩
    · refine ⟨conj ρ, ⟨ATK.ZetaSimetria.espelho_mem_Z hρ.1, by simpa using hρ.2⟩, ?_⟩
      rw [abs_of_neg hn] at hT
      simpa using hT

theorem hext_refuta (h : Hext) : ¬ RiemannHypothesis := by
  obtain ⟨ρ, hρ, -⟩ := h 0
  exact hFora_iff.mp (hFora_iff_fora.mpr ⟨ρ, hρ⟩)

/-- **Sob `H_ext`, há quartetos externos acima de toda altura.** -/
theorem hext_quartetos (h : Hext) (T : ℝ) : ∃ ρ, ForaCritico ρ ∧ T < ρ.im ∧
    ForaCritico (ATK.ZetaSimetria.torcao ρ) ∧ ForaCritico (conj ρ) ∧ ForaCritico (1 - ρ) := by
  obtain ⟨ρ, hρ, hT⟩ := h T
  refine ⟨ρ, hρ, hT, ATK.ZeroClasses.MundoFora.torcao_fora hρ,
    ⟨ATK.ZetaSimetria.espelho_mem_Z hρ.1, by simpa using hρ.2⟩, ⟨ATK.ZetaSimetria.tensao_mem_Z hρ.1, ?_⟩⟩
  show (ATK.ZetaSimetria.tensao ρ).re ≠ 1 / 2
  rw [ATK.ZetaSimetria.re_tensao]
  intro e; exact hρ.2 (by linarith)

/-- **Teoria conjunta**: uma hipótese independente `Q` (por exemplo `SAT ∉ P`) só se compõe com `H_ext`. -/
theorem teoria_conjunta {Q : Prop} (h : Hext) (hQ : Q) : ¬ RiemannHypothesis ∧ Q := ⟨hext_refuta h, hQ⟩

/-! ## 5. Zeros booleanos e aritméticos -/

/-- Literal: variável e polaridade. -/
abbrev Lit (n : ℕ) := Fin n × Bool

/-- Valor de um literal numa atribuição. -/
def litVal {n : ℕ} (x : Fin n → Bool) (l : Lit n) : Bool := x l.1 == l.2

/-- Violação de uma cláusula: `0` se satisfeita, `1` se violada. -/
def viol {n : ℕ} (x : Fin n → Bool) (C : List (Lit n)) : ℕ := if C.any (litVal x) then 0 else 1

/-- `R_φ(x) = Σ_C q_C(x)`. -/
def Rphi {n : ℕ} (φ : List (List (Lit n))) (x : Fin n → Bool) : ℕ := (φ.map (viol x)).sum

/-- `q_C = ∏_{ℓ ∈ C} (1 − ℓ(x))`. -/
theorem viol_eq_prod {n : ℕ} (x : Fin n → Bool) (C : List (Lit n)) :
    viol x C = (C.map fun l => if litVal x l then 0 else 1).prod := by
  induction C with
  | nil => simp [viol]
  | cons l C ih =>
    simp only [viol, List.any_cons, List.map_cons, List.prod_cons] at ih ⊢
    by_cases hl : litVal x l = true
    · simp [hl]
    · simp only [Bool.not_eq_true] at hl
      simp only [hl, Bool.false_or, Bool.false_eq_true, ↓reduceIte, one_mul]
      exact ih

theorem R_zero_iff {n : ℕ} (φ : List (List (Lit n))) (x : Fin n → Bool) :
    Rphi φ x = 0 ↔ ∀ C ∈ φ, C.any (litVal x) = true := by
  unfold Rphi
  rw [List.sum_eq_zero_iff]
  constructor
  · intro h C hC
    have := h (viol x C) (List.mem_map.mpr ⟨C, hC, rfl⟩)
    unfold viol at this
    by_contra hc
    simp [hc] at this
  · intro h k hk
    obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hk
    simp [viol, h C hC]

/-- `φ ∈ SAT`. -/
def Sat {n : ℕ} (φ : List (List (Lit n))) : Prop := ∃ x : Fin n → Bool, ∀ C ∈ φ, C.any (litVal x) = true

/-- **`φ ∈ SAT ⟺ ∃x, R_φ(x) = 0`.** -/
theorem sat_iff_zero {n : ℕ} (φ : List (List (Lit n))) : Sat φ ↔ ∃ x, Rphi φ x = 0 :=
  exists_congr fun x => (R_zero_iff φ x).symm

/-- **Lacuna discreta**: `R_φ(x) < 1 ⟹ R_φ(x) = 0` (a `ζ` não tem lacuna assim). -/
theorem lacuna {n : ℕ} (φ : List (List (Lit n))) (x : Fin n → Bool) (h : Rphi φ x < 1) : Rphi φ x = 0 := by
  omega

/-- **`m(φ) = 0` ou `m(φ) ≥ 1`.** -/
theorem lacuna_min {n : ℕ} (φ : List (List (Lit n))) : Sat φ ∨ ∀ x, 1 ≤ Rphi φ x := by
  by_cases h : Sat φ
  · exact Or.inl h
  · right; intro x
    by_contra hc
    exact h ((sat_iff_zero φ).mpr ⟨x, by omega⟩)

/-- `(x₀ ∨ ¬x₁)` é satisfatível. -/
theorem exemplo_sat : Sat [[((0 : Fin 2), true), ((1 : Fin 2), false)]] :=
  ⟨fun _ => true, by decide⟩

/-- `x₀ ∧ ¬x₀` não é satisfatível: `R ≥ 1` em toda atribuição. -/
theorem exemplo_unsat : ∀ x : Fin 1 → Bool, 1 ≤ Rphi [[((0 : Fin 1), true)], [((0 : Fin 1), false)]] x := by
  decide

/-- **Divisibilidade como zero**: `b ∣ a ⟺ ∃k, a − bk = 0`. -/
theorem div_iff_zero (a b : ℤ) : b ∣ a ↔ ∃ k, a - b * k = 0 :=
  ⟨fun ⟨k, hk⟩ => ⟨k, by rw [hk]; ring⟩, fun ⟨k, hk⟩ => ⟨k, by linarith⟩⟩

theorem exemplo_84 : (84 : ℤ) - 7 * 12 = 0 ∧ ¬ (7 : ℤ) ∣ 85 := ⟨by norm_num, by decide⟩

/-! ## 6. Zero assintótico ≠ zero -/

/-- `1/(n+1) → 0` e nunca é `0`. -/
theorem limite_sem_zero :
    Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) ∧ ∀ n : ℕ, (1 : ℝ) / (n + 1) ≠ 0 :=
  ⟨tendsto_one_div_add_atTop_nhds_zero_nat, fun n => by positivity⟩

/-- **Quase polinomial não é polinomial**: `(log n)²/n → 0`, mas `n^{log n}` supera `C·nᵏ` para todo `k`, `C`. -/
theorem quase_polinomial :
    Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (𝓝 0) ∧
      ∀ k : ℕ, ∀ C : ℝ, ∃ x : ℝ, 1 < x ∧ C * x ^ k < x ^ Real.log x := by
  refine ⟨?_, fun k C => ?_⟩
  · have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
    simpa using this
  · -- x = max(e^{k+1}, |C| + 2): x^{log x} ≥ x^{k+1} = x·x^k > C·x^k
    set x := max (Real.exp (k + 1)) (|C| + 2) with hx
    have hx1 : 1 < x := lt_of_lt_of_le (by linarith [abs_nonneg C]) (le_max_right _ _)
    have hxpos : 0 < x := by linarith
    have hlog : (k : ℝ) + 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le hxpos]; exact le_max_left _ _
    have hpow : x ^ ((k : ℝ) + 1) ≤ x ^ Real.log x := Real.rpow_le_rpow_of_exponent_le hx1.le hlog
    have e : x ^ ((k : ℝ) + 1) = x * x ^ k := by
      rw [Real.rpow_add hxpos, Real.rpow_one, Real.rpow_natCast]; ring
    have hxk : 0 < x ^ k := pow_pos hxpos k
    have hCx : C < x := lt_of_lt_of_le (by linarith [le_abs_self C]) (le_max_right _ _)
    refine ⟨x, hx1, ?_⟩
    calc C * x ^ k < x * x ^ k := by nlinarith
      _ = x ^ ((k : ℝ) + 1) := e.symm
      _ ≤ x ^ Real.log x := hpow

end ATK.ZeroClasses.Forcar

#print axioms ATK.ZeroClasses.Forcar.Pq_eq_Q
#print axioms ATK.ZeroClasses.Forcar.Pq_zero_iff
#print axioms ATK.ZeroClasses.Forcar.Pq_refl
#print axioms ATK.ZeroClasses.Forcar.Pq_conj
#print axioms ATK.ZeroClasses.Forcar.quarteto_fora
#print axioms ATK.ZeroClasses.Forcar.quarteto_gigante
#print axioms ATK.ZeroClasses.Forcar.Xi_lambda_refl
#print axioms ATK.ZeroClasses.Forcar.Xi_lambda_conj
#print axioms ATK.ZeroClasses.Forcar.somar_nao_forca
#print axioms ATK.ZeroClasses.Forcar.cota_fronteira
#print axioms ATK.ZeroClasses.Forcar.certificado_modulo_minimo
#print axioms ATK.ZeroClasses.Forcar.certificado_E1
#print axioms ATK.ZeroClasses.Forcar.certificado_E1_refuta
#print axioms ATK.ZeroClasses.Forcar.exemplo_linear
#print axioms ATK.ZeroClasses.Forcar.exemplo_quadratico
#print axioms ATK.ZeroClasses.Forcar.contraexemplo
#print axioms ATK.ZeroClasses.Forcar.cauda_por_certificados
#print axioms ATK.ZeroClasses.Forcar.hext_iff
#print axioms ATK.ZeroClasses.Forcar.hext_refuta
#print axioms ATK.ZeroClasses.Forcar.hext_quartetos
#print axioms ATK.ZeroClasses.Forcar.teoria_conjunta
#print axioms ATK.ZeroClasses.Forcar.viol_eq_prod
#print axioms ATK.ZeroClasses.Forcar.R_zero_iff
#print axioms ATK.ZeroClasses.Forcar.sat_iff_zero
#print axioms ATK.ZeroClasses.Forcar.lacuna
#print axioms ATK.ZeroClasses.Forcar.lacuna_min
#print axioms ATK.ZeroClasses.Forcar.exemplo_sat
#print axioms ATK.ZeroClasses.Forcar.exemplo_unsat
#print axioms ATK.ZeroClasses.Forcar.div_iff_zero
#print axioms ATK.ZeroClasses.Forcar.exemplo_84
#print axioms ATK.ZeroClasses.Forcar.limite_sem_zero
#print axioms ATK.ZeroClasses.Forcar.quase_polinomial
