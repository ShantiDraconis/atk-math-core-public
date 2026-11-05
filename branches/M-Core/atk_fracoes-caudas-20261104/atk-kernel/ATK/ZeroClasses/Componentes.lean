import ATK.ZeroClasses.Encontro
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# ATK-ZERO-CLASSES — onde o real encontra o imaginário: componentes, mínimos, caudas e o infinito

Rodada 22. Escrevemos `ζ(σ + it) = u + iv`. O kernel separa três fenômenos — componentes iguais, troca de
componentes, anulação simultânea — e acrescenta o que decide o "quase zero".

**1. Curvas e rotação** (`diagonais`, `cruzam_so_no_zero`, `curvas_C`, `igual_nao_e_zero`, `rotacao`).
`C₊ = {u = v}` e `C₋ = {u = −v}` cruzam-se **exatamente** nos zeros; `u = v` sozinho não é zero (`1 + i`). A troca
`(u, v) ↦ (−v, u)` é a multiplicação por `i`: `J = A(i)`, `J² = −1`, `J⁴ = 1`, `|iz| = |z|` — não cria zero.

**2. Cauchy–Riemann e o cruzamento perpendicular** (`cauchy_riemann`, `cruzamento_perpendicular`).
`∂σu = Re ζ′`, `∂σv = Im ζ′`, `∂tu = −Im ζ′`, `∂tv = Re ζ′`; logo `uσ = vt`, `ut = −vσ`. Os gradientes de `u` e `v`
(e os de `u − v` e `u + v`) são **ortogonais** e de mesma norma `|ζ′|`: num zero simples, as curvas cruzam-se em
ângulo reto.

**3. Não existe "quase zero" que seja mínimo** (`minimo_local_e_zero`, `sem_maximo_local`, `minimo_na_fronteira`).
Princípio do módulo mínimo: **todo mínimo local de `|ζ|` (fora do polo) é um zero exato**; `|ζ|` não tem máximo
local; num compacto sem zeros o mínimo de `|ζ|` está na **fronteira**. (A varredura da rodada 21 achou o mínimo
fora da linha em `σ = 0,55`, a borda da região: exatamente o que este teorema prevê numa região sem zeros.)

**4. A cauda de influência** (`residuo_logderiv`, `residuo_primeiro_zero`, `residuo_triviais`). Num zero de ordem
`m`, `(s − ρ)·f′(s)/f(s) → m`: a parcela `m/(s − ρ)` é a influência do zero, e ela **não** cria zeros.

**5. Caudas de zeros** (`sem_curva_de_zeros`, `sem_curva_unitInterval`, `cauda_iff`, `triviais_ilimitados`).
Nenhuma curva contínua não constante é feita de zeros de `ζ`. Infinitos zeros fora da linha ⟺ alturas
**ilimitadas** (`cauda_iff`) — compatível com o isolamento, como os triviais `−2n` mostram; não demonstrado.

**6. Simetria sem zeros fora** (`Fch_refl`, `Fch_conj`, `Fch_zero_iff`, `Fch_na_linha`, `simetria_sem_fora`).
`cosh(s − ½)` tem as duas simetrias de `ξ`, infinitos zeros em alturas ilimitadas, e **todos** na linha.

**7. Depois do infinito** (`arquimediano`, `altura_infinita`, `deslocamento_infinitesimal`, `ordinal_sucessor`).
Nos reais não há deslocamento infinitesimal; nos hiper-reais, `½ + ε > ½` e `½ + ε < ½ + r` para todo real
`r > 0`, e `ω` é maior que todo real; nos ordinais, `1 + ω = ω < ω + 1`. Nada disso é um argumento de `ζ`: a
pergunta clássica não muda (a transferência para `*ζ` não está no kernel).
-/

open Complex ComplexConjugate Set Filter Topology Metric
open scoped Real

namespace ATK.ZeroClasses.Componentes

open ATK.ZeroClasses ATK.ZeroClasses.Zeta ATK.ZeroClasses.Hipotetico ATK.ZeroClasses.Encontro

/-! ## 1. Curvas `u = ±v` e a rotação por `i` -/

theorem diagonais (w : ℂ) : w.re ^ 2 = w.im ^ 2 ↔ w.re = w.im ∨ w.re = -w.im := sq_eq_sq_iff_eq_or_eq_neg

/-- As diagonais `u = v` e `u = −v` cruzam-se **só** na origem. -/
theorem cruzam_so_no_zero (w : ℂ) : (w.re = w.im ∧ w.re = -w.im) ↔ w = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    have him : w.im = 0 := by linarith
    have hre : w.re = 0 := by linarith
    exact Complex.ext hre him
  · rintro rfl; simp

/-- **`C₊ ∩ C₋` = zeros de `ζ`.** -/
theorem curvas_C (s : ℂ) :
    ((riemannZeta s).re = (riemannZeta s).im ∧ (riemannZeta s).re = -(riemannZeta s).im) ↔
      riemannZeta s = 0 :=
  cruzam_so_no_zero _

/-- Componentes iguais **não** é zero: `1 + i`. -/
theorem igual_nao_e_zero : ∃ w : ℂ, w.re = w.im ∧ w ≠ 0 :=
  ⟨1 + I, by simp, fun h => by have := congrArg Complex.re h; simp at this⟩

/-- **A troca real ↔ imaginário é a rotação `J = A(i)`**: `J² = −1`, `J⁴ = 1`, `|iz| = |z|`, `iz = 0 ⟺ z = 0`. -/
theorem rotacao :
    matA I = !![0, -1; 1, 0] ∧ matA I * matA I = -1 ∧ matA I ^ 4 = 1 ∧
      ∀ z : ℂ, ‖I * z‖ = ‖z‖ ∧ (I * z = 0 ↔ z = 0) := by
  have hJ : matA I = !![0, -1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [matA]
  have hJ2 : matA I * matA I = -1 := by
    rw [hJ]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨hJ, hJ2, ?_, fun z => ⟨by simp, by simp [I_ne_zero]⟩⟩
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, hJ2]; simp

/-! ## 2. Cauchy–Riemann e o cruzamento perpendicular -/

/-- **Cauchy–Riemann para `ζ`** em `s = σ + it ≠ 1`: `∂σu = Re ζ′`, `∂σv = Im ζ′`, `∂tu = −Im ζ′`, `∂tv = Re ζ′`. -/
theorem cauchy_riemann {σ t : ℝ} (hs : (σ : ℂ) + t * I ≠ 1) :
    HasDerivAt (fun x : ℝ => (riemannZeta (x + t * I)).re) (deriv riemannZeta (σ + t * I)).re σ ∧
    HasDerivAt (fun x : ℝ => (riemannZeta (x + t * I)).im) (deriv riemannZeta (σ + t * I)).im σ ∧
    HasDerivAt (fun y : ℝ => (riemannZeta (σ + y * I)).re) (-(deriv riemannZeta (σ + t * I)).im) t ∧
    HasDerivAt (fun y : ℝ => (riemannZeta (σ + y * I)).im) (deriv riemannZeta (σ + t * I)).re t := by
  set w := deriv riemannZeta (σ + t * I)
  have hz : HasDerivAt riemannZeta w (σ + t * I) := (differentiableAt_riemannZeta hs).hasDerivAt
  -- direção σ
  have h1 : HasDerivAt (fun x : ℂ => riemannZeta (x + t * I)) w (σ : ℂ) :=
    hz.comp_add_const (σ : ℂ) (t * I)
  have h2 : HasDerivAt (fun y : ℂ => riemannZeta (σ + y * I)) (w * I) (t : ℂ) := by
    have hl : HasDerivAt (fun y : ℂ => (σ : ℂ) + y * I) I (t : ℂ) := by
      simpa using ((hasDerivAt_id' (t : ℂ)).mul_const I).const_add (σ : ℂ)
    exact hz.comp (t : ℂ) hl
  have hre1 := h1.real_of_complex
  have him1 := (h1.const_mul (-I)).real_of_complex
  have hre2 := h2.real_of_complex
  have him2 := (h2.const_mul (-I)).real_of_complex
  refine ⟨hre1, ?_, ?_, ?_⟩
  · convert him1 using 1
    · funext x; simp
    · simp
  · convert hre2 using 1; simp
  · convert him2 using 1
    · funext y; simp
    · simp

/-- **Cruzamento perpendicular**: com `ζ′ = a + ib`, `∇u = (a, −b)`, `∇v = (b, a)`, `∇(u−v) = (a−b, −a−b)`,
`∇(u+v) = (a+b, a−b)`; ambos os pares são ortogonais e `|∇u|² = |∇v|² = |ζ′|²`. -/
theorem cruzamento_perpendicular (w : ℂ) :
    w.re * w.im + (-w.im) * w.re = 0 ∧
      (w.re - w.im) * (w.re + w.im) + (-w.im - w.re) * (w.re - w.im) = 0 ∧
      w.re ^ 2 + (-w.im) ^ 2 = ‖w‖ ^ 2 ∧ w.im ^ 2 + w.re ^ 2 = ‖w‖ ^ 2 := by
  refine ⟨by ring, by ring, ?_, ?_⟩ <;> rw [Complex.sq_norm, normSq_apply] <;> ring

/-! ## 3. Princípio do módulo mínimo: não há "quase zero" que seja mínimo -/

/-- `ζ` não é localmente constante em nenhum ponto `z ≠ 1`. -/
theorem nao_localmente_constante {z : ℂ} (hz : z ≠ 1) : ¬ ∀ᶠ s in 𝓝 z, riemannZeta s = riemannZeta z := by
  intro hc
  have hU : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [rank_real_complex]; norm_num) 1).isPreconnected
  have heq := analyticOn_riemannZeta.eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_const (v := riemannZeta z)) hU hz hc
  have h2 := heq (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
  have h4 := heq (show (4 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
  exact zero_coletivo_zeta.2.1 (by simp only at h2 h4; rw [h2, h4, sub_self])

theorem diferenciavel_perto {z : ℂ} (hz : z ≠ 1) : ∀ᶠ s in 𝓝 z, DifferentiableAt ℂ riemannZeta s := by
  filter_upwards [isOpen_compl_singleton.mem_nhds hz] with s hs using differentiableAt_riemannZeta hs

/-- **Todo mínimo local de `|ζ|` é um zero exato** (princípio do módulo mínimo). -/
theorem minimo_local_e_zero {z : ℂ} (hz : z ≠ 1) (h : IsLocalMin (fun s => ‖riemannZeta s‖) z) :
    riemannZeta z = 0 := by
  rcases Complex.eventually_eq_or_eq_zero_of_isLocalMin_norm (diferenciavel_perto hz) h with hc | h0
  · exact absurd hc (nao_localmente_constante hz)
  · exact h0

/-- **`|ζ|` não tem máximo local** (princípio do módulo máximo). -/
theorem sem_maximo_local {z : ℂ} (hz : z ≠ 1) : ¬ IsLocalMax (fun s => ‖riemannZeta s‖) z := fun h =>
  nao_localmente_constante hz (Complex.eventually_eq_of_isLocalMax_norm (diferenciavel_perto hz) h)

/-- **Num compacto sem zeros (e sem o polo), o mínimo de `|ζ|` é atingido na fronteira.** -/
theorem minimo_na_fronteira {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) (h1 : (1 : ℂ) ∉ K)
    (h0 : ∀ s ∈ K, riemannZeta s ≠ 0) :
    ∃ z ∈ K, z ∉ interior K ∧ ∀ s ∈ K, ‖riemannZeta z‖ ≤ ‖riemannZeta s‖ := by
  have hcont : ContinuousOn (fun s => ‖riemannZeta s‖) K := fun s hs =>
    (differentiableAt_riemannZeta (fun h => h1 (h ▸ hs))).continuousAt.norm.continuousWithinAt
  obtain ⟨z, hzK, hmin⟩ := hK.exists_isMinOn hne hcont
  refine ⟨z, hzK, fun hint => ?_, fun s hs => hmin hs⟩
  have hloc : IsLocalMin (fun s => ‖riemannZeta s‖) z :=
    Filter.mem_of_superset (mem_interior_iff_mem_nhds.mp hint) fun s hs => hmin hs
  exact h0 z hzK (minimo_local_e_zero (fun h => h1 (h ▸ hzK)) hloc)

/-! ## 4. A cauda de influência: o resíduo da derivada logarítmica -/

/-- **Resíduo**: num zero de ordem `m` de `f` analítica, `(s − ρ)·f′(s)/f(s) → m`. -/
theorem residuo_logderiv {f : ℂ → ℂ} {ρ : ℂ} {m : ℕ} (hf : AnalyticAt ℂ f ρ)
    (hm : analyticOrderAt f ρ = m) :
    Tendsto (fun s => (s - ρ) * deriv f s / f s) (𝓝[≠] ρ) (𝓝 (m : ℂ)) := by
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp hm
  have hfg' : ∀ᶠ s in 𝓝 ρ, f s = (s - ρ) ^ m * g s := by simpa [smul_eq_mul] using hfg
  have hd : ∀ᶠ s in 𝓝 ρ, deriv f s = m * (s - ρ) ^ (m - 1) * g s + (s - ρ) ^ m * deriv g s := by
    have hev : ∀ᶠ s in 𝓝 ρ, f =ᶠ[𝓝 s] fun z => (z - ρ) ^ m * g z := hfg'.eventually_nhds
    filter_upwards [hev, hg.eventually_analyticAt] with s hs hgs
    rw [hs.deriv_eq]
    have h1 : HasDerivAt (fun z => (z - ρ) ^ m) (m * (s - ρ) ^ (m - 1)) s := by
      have := (hasDerivAt_pow m (s - ρ)).comp s ((hasDerivAt_id' s).sub_const ρ)
      simpa [Function.comp_def] using this
    exact (h1.mul hgs.differentiableAt.hasDerivAt).deriv
  have hg0' : ∀ᶠ s in 𝓝 ρ, g s ≠ 0 := hg.continuousAt.eventually_ne hg0
  have key : ∀ᶠ s in 𝓝[≠] ρ, (m : ℂ) + (s - ρ) * deriv g s / g s = (s - ρ) * deriv f s / f s := by
    filter_upwards [nhdsWithin_le_nhds hfg', nhdsWithin_le_nhds hd, nhdsWithin_le_nhds hg0',
      self_mem_nhdsWithin] with s h1 h2 h3 h4
    have hs : s - ρ ≠ 0 := sub_ne_zero.mpr h4
    rw [h1, h2]
    cases m with
    | zero => simp
    | succ k =>
      simp only [Nat.add_sub_cancel, pow_succ]
      field_simp
  have hc : ContinuousAt (fun s => (m : ℂ) + (s - ρ) * deriv g s / g s) ρ :=
    continuousAt_const.add (((continuousAt_id.sub continuousAt_const).mul
      hg.deriv.continuousAt).div hg.continuousAt hg0)
  have hlim := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {ρ}ᶜ))
  simp only [sub_self, zero_mul, zero_div, add_zero] at hlim
  exact hlim.congr' key

/-- No primeiro zero certificado (simples), `(s − ρ₁)ζ′/ζ → 1`. -/
theorem residuo_primeiro_zero : ∃ ρ ∈ ATK.ZetaSimetria.Z, ρ.re = 1 / 2 ∧
    Tendsto (fun s => (s - ρ) * deriv riemannZeta s / riemannZeta s) (𝓝[≠] ρ) (𝓝 1) := by
  obtain ⟨ρ, hρ, hre, -, hd⟩ := ATK.ZeroClasses.Escalas.primeiro_zero_simples
  have hρ1 : ρ ≠ 1 := by intro h; rw [h, one_re] at hre; norm_num at hre
  have ha : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  have hord := ((simples_iff ha).mp ⟨hρ.1, hd⟩).2
  have := residuo_logderiv ha (m := 1) (by rw [hord]; rfl)
  exact ⟨ρ, hρ, hre, by simpa using this⟩

/-- Nos zeros triviais (simples), `(s + 2(n+1))ζ′/ζ → 1`. -/
theorem residuo_triviais (n : ℕ) :
    Tendsto (fun s => (s - (-2 * ((n : ℂ) + 1))) * deriv riemannZeta s / riemannZeta s)
      (𝓝[≠] (-2 * ((n : ℂ) + 1))) (𝓝 1) := by
  have ht : ATK.ZetaSimetria.Trivial (-2 * ((n : ℂ) + 1)) := ⟨n, rfl⟩
  obtain ⟨-, -, -, -, -, hord⟩ := trivial_classes ht
  have h1 : (-2 * ((n : ℂ) + 1)) ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have := residuo_logderiv (analyticOn_riemannZeta _ h1) (m := 1) (by rw [hord]; rfl)
  simpa using this

/-! ## 5. Caudas de zeros -/

/-- **Nenhuma curva contínua não constante é feita de zeros de `ζ`** (num espaço pré-conexo qualquer). -/
theorem sem_curva_de_zeros {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {c : X → ℂ}
    (hc : Continuous c) (h0 : ∀ x, riemannZeta (c x) = 0) (x y : X) : c x = c y := by
  have hloc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hiso := (zeros_isolados (h0 x)).2.2
    rw [eventually_nhdsWithin_iff] at hiso
    have h1 : ∀ᶠ w in 𝓝 (c x), riemannZeta w = 0 → w = c x := by
      filter_upwards [hiso] with w hw hz
      by_contra hne
      exact hw hne hz
    filter_upwards [hc.continuousAt.eventually h1] with y hy using hy (h0 y)
  exact hloc.apply_eq_of_preconnectedSpace x y

/-- O caso `c : [0, 1] → ℂ`. -/
theorem sem_curva_unitInterval {c : unitInterval → ℂ} (hc : Continuous c) (h0 : ∀ x, riemannZeta (c x) = 0)
    (x y : unitInterval) : c x = c y :=
  sem_curva_de_zeros hc h0 x y

/-- **Cauda de zeros fora da linha**: o conjunto é infinito ⟺ as alturas são ilimitadas. -/
theorem cauda_iff : ATK.ZeroClasses.MundoFora.ForaSet.Infinite ↔ ∀ T : ℝ, ∃ ρ, ForaCritico ρ ∧ T < |ρ.im| := by
  constructor
  · intro hinf T
    by_contra hc
    push Not at hc
    exact hinf ((finitos_abaixo T).subset fun ρ hρ => ⟨hρ, hc ρ hρ⟩)
  · intro h hfin
    obtain ⟨M, hM⟩ := (hfin.image fun ρ => |ρ.im|).bddAbove
    obtain ⟨ρ, hρ, hlt⟩ := h M
    have := hM ⟨ρ, hρ, rfl⟩
    linarith

/-- Os zeros triviais formam uma sequência **ilimitada** de zeros distintos: compatível com o isolamento. -/
theorem triviais_ilimitados : ∀ T : ℝ, ∃ n : ℕ, riemannZeta (-2 * ((n : ℂ) + 1)) = 0 ∧
    T < ‖(-2 * ((n : ℂ) + 1))‖ := by
  intro T
  obtain ⟨n, hn⟩ := exists_nat_gt T
  refine ⟨n, riemannZeta_neg_two_mul_nat_add_one n, ?_⟩
  have e : ‖(-2 * ((n : ℂ) + 1))‖ = 2 * ((n : ℝ) + 1) := by
    rw [norm_mul, norm_neg, show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; norm_num
  rw [e]; linarith

/-! ## 6. Simetria sem zeros fora: `cosh(s − ½)` -/

/-- Modelo `F(s) = cosh(s − ½)`. -/
noncomputable def Fch (s : ℂ) : ℂ := cosh (s - 1 / 2)

theorem Fch_refl (s : ℂ) : Fch (1 - s) = Fch s := by
  unfold Fch; rw [show 1 - s - 1 / 2 = -(s - 1 / 2) by ring, Complex.cosh_neg]

theorem Fch_conj (s : ℂ) : Fch (conj s) = conj (Fch s) := by
  unfold Fch
  rw [← Complex.cosh_conj, map_sub]
  congr 2
  simp only [map_div₀, map_one, map_ofNat]

theorem Fch_zero_iff (s : ℂ) : Fch s = 0 ↔ ∃ k : ℤ, (s - 1 / 2) * I = (2 * k + 1) * π / 2 := by
  unfold Fch; rw [← Complex.cos_mul_I, Complex.cos_eq_zero_iff]

/-- **Todos os zeros do modelo estão na linha.** -/
theorem Fch_na_linha {s : ℂ} (h : Fch s = 0) : s.re = 1 / 2 := by
  obtain ⟨k, hk⟩ := (Fch_zero_iff s).mp h
  have := congrArg Complex.im hk
  simp at this
  linarith

/-- **As simetrias de `ξ` não obrigam zeros fora**: `cosh(s − ½)` tem `F(1 − s) = F(s)`, `F(s̄) = conj F(s)`, zeros
em alturas ilimitadas, e **nenhum** fora da linha. -/
theorem simetria_sem_fora : ∃ F : ℂ → ℂ, (∀ s, F (1 - s) = F s) ∧ (∀ s, F (conj s) = conj (F s)) ∧
    (∀ s, F s = 0 → s.re = 1 / 2) ∧ ∀ T : ℝ, ∃ s, F s = 0 ∧ T < s.im := by
  refine ⟨Fch, Fch_refl, Fch_conj, fun s => Fch_na_linha, fun T => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt T
  refine ⟨1 / 2 + ((2 * (n : ℝ) + 1) * π / 2 : ℝ) * I, ?_, ?_⟩
  · rw [Fch_zero_iff]
    refine ⟨-(n : ℤ) - 1, ?_⟩
    push_cast
    ring_nf
    rw [I_sq]
    ring
  · simp
    have hp := Real.pi_gt_three
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-! ## 7. Depois do infinito -/

/-- **Nos reais não há deslocamento infinitesimal**: todo `δ > 0` real é maior que algum `1/(2n+1)`. -/
theorem arquimediano {δ : ℝ} (hδ : 0 < δ) : ∃ n : ℕ, 1 / (2 * (n : ℝ) + 1) < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  refine ⟨n, ?_⟩
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hδ] at hn
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- **Altura hiper-real infinita**: `ω` é maior que todo real. -/
theorem altura_infinita (r : ℝ) : (r : Hyperreal) < Hyperreal.omega := Hyperreal.coe_lt_omega r

/-- **Deslocamento infinitesimal hiper-real**: `½ < ½ + ε < ½ + r` para todo real `r > 0`. -/
theorem deslocamento_infinitesimal :
    (1 / 2 : Hyperreal) < 1 / 2 + Hyperreal.epsilon ∧
      ∀ r : ℝ, 0 < r → (1 / 2 : Hyperreal) + Hyperreal.epsilon < 1 / 2 + (r : Hyperreal) :=
  ⟨lt_add_of_pos_right _ Hyperreal.epsilon_pos, fun _ hr => by
    have := Hyperreal.epsilon_lt_of_pos hr
    linarith⟩

/-- **Ordinais**: `1 + ω = ω`, mas `ω < ω + 1`. -/
theorem ordinal_sucessor : (1 : Ordinal) + Ordinal.omega0 = Ordinal.omega0 ∧
    Ordinal.omega0 < Ordinal.omega0 + 1 :=
  ⟨Ordinal.one_add_omega0, Order.lt_add_one_iff.mpr le_rfl⟩

end ATK.ZeroClasses.Componentes

#print axioms ATK.ZeroClasses.Componentes.diagonais
#print axioms ATK.ZeroClasses.Componentes.cruzam_so_no_zero
#print axioms ATK.ZeroClasses.Componentes.curvas_C
#print axioms ATK.ZeroClasses.Componentes.igual_nao_e_zero
#print axioms ATK.ZeroClasses.Componentes.rotacao
#print axioms ATK.ZeroClasses.Componentes.cauchy_riemann
#print axioms ATK.ZeroClasses.Componentes.cruzamento_perpendicular
#print axioms ATK.ZeroClasses.Componentes.nao_localmente_constante
#print axioms ATK.ZeroClasses.Componentes.diferenciavel_perto
#print axioms ATK.ZeroClasses.Componentes.minimo_local_e_zero
#print axioms ATK.ZeroClasses.Componentes.sem_maximo_local
#print axioms ATK.ZeroClasses.Componentes.minimo_na_fronteira
#print axioms ATK.ZeroClasses.Componentes.residuo_logderiv
#print axioms ATK.ZeroClasses.Componentes.residuo_primeiro_zero
#print axioms ATK.ZeroClasses.Componentes.residuo_triviais
#print axioms ATK.ZeroClasses.Componentes.sem_curva_de_zeros
#print axioms ATK.ZeroClasses.Componentes.sem_curva_unitInterval
#print axioms ATK.ZeroClasses.Componentes.cauda_iff
#print axioms ATK.ZeroClasses.Componentes.triviais_ilimitados
#print axioms ATK.ZeroClasses.Componentes.Fch_refl
#print axioms ATK.ZeroClasses.Componentes.Fch_conj
#print axioms ATK.ZeroClasses.Componentes.Fch_zero_iff
#print axioms ATK.ZeroClasses.Componentes.Fch_na_linha
#print axioms ATK.ZeroClasses.Componentes.simetria_sem_fora
#print axioms ATK.ZeroClasses.Componentes.arquimediano
#print axioms ATK.ZeroClasses.Componentes.altura_infinita
#print axioms ATK.ZeroClasses.Componentes.deslocamento_infinitesimal
#print axioms ATK.ZeroClasses.Componentes.ordinal_sucessor
