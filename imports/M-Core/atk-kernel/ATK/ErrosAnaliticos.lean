import ATK.XiAnalitica
import ATK.GeometriaExtra
import ATK.ZeroCritico
import ATK.BaseRiemannTeta
import ATK.BaseRiemannXiSinal
import ATK.NecessidadeRH

/-!
# ATK — Erros dos textos (parte analítica): explicação, correção e teoremas

* **E5 (56e0dfa6), `B(d,t) = d∫₀¹ Re F′`.** Pelas equações de Cauchy–Riemann na direção horizontal,
  `∂_d Im F(d+it) = Im F′` e `∂_d Re F = Re F′` (`cauchy_riemann_horizontal`): o `B = Im F` pede `Im F′`.
  Além do contraexemplo `F = z²` (`contraexemplo_derivada`), a versão do texto é falsa **para o próprio
  `F(z) = ξ(½+z)`**: no eixo, `Re F′(it) = 0`, então ela daria `∂_d B(0,t) = 0` para todo `t`, o que
  forçaria `Ξ` constante — mas `Ξ(0) > 0` e `Ξ(γ₁) = 0` (`texto_Re_falso_para_xi`).
* **E6 (8af24fb4 / bef58a09), multiplicidades.** A tabela completa para o zero `½ + λ + iγ` de `G_λ`:
  `1` se `λ ≠ 0 ∧ γ ≠ 0`, `2` se exatamente um é `0`, `4` se ambos (`multiplicidade_tabela`).
* **E7 (f1754ca5), Jensen com `aₙ`.** Turán para `γₙ = n!aₙ` implica Turán para `aₙ`
  (`turan_gamma_implica_a`), mas não o contrário (`turan_a_nao_implica_gamma`): o teste com `aₙ` é
  **mais fraco**. Para `Θ = 1 + x + x²` (zeros não reais), o polinômio montado com `a` é hiperbólico e o
  montado com `γ` não (`jensen_a_falha_gamma_detecta`).
* **E8 (0e761a7c), `TP∞(γ)`.** Para `(1+x)³`: `γ = (1,3,6,6)` satisfaz **todos** os menores 2×2
  (Turán) e ainda assim `D₃,₁(γ) = −3`; `a = (1,3,3,1)` tem todos os 2×2 `≥ 0` e `D₃,₁(a) = 10`
  (`tp_binomial`). A positividade total (Aissen–Schoenberg–Whitney–Edrei) é sobre `aₙ`, não `γₙ`
  (o teorema geral não está no Mathlib).
* **E9 (e1644f4c / f1754ca5), fator 2.** A substituição `x = e^{2u}` na fórmula de Riemann dá
  `Ξ(t) = ½ − 2(t² + ¼)∫₀^∞ ψ(e^{2u})e^{u/2}cos(tu)du` (`Xi_forma_u`; o `2` é o jacobiano `dx = 2e^{2u}du`);
  sem o `2` a fórmula é falsa (`fator_um_falso`). Duas integrações por partes (`ibp_cos`) levam, com
  `g(u) = ψ(e^{2u})e^{u/2}`, a `Ξ(t) = (½ + 2g′(0)) + 2∫₀^∞ (g″ − g/4)cos(tu)du` (`Xi_forma_Phi`,
  **condicional** à regularidade/decaimento de `g`, `g′`, `g″`, não formalizados aqui); a identificação
  `g″ − g/4 = Φ` termo a termo e `½ + 2g′(0) = 0` (equação funcional de `θ`) também não estão aqui.
  O teorema `integral_par` mostra que `∫_ℝ Φ cos = 2∫₀^∞ Φ cos` para `Φ` par.
* **E10 (48cacf85), `M₊(T)`.** Para `0 < T < 4` a região `½ + 1/T ≤ σ ≤ 1 − 1/T` é **vazia**
  (`R_vazio`), `M₊(T) = inf ∅ = 0` (`Mplus_vazio`), logo "`∀T > 2, M₊(T) > 0`" é falso
  (`texto_M_falso`) e a equivalência do texto implicaria `¬HR` (`texto_equivalencia_daria_nao_rh`).
  Correção: **`HR ⟺ ∀T ≥ 4, M₊(T) > 0`** (`rh_iff_Mplus`).
* **E11 (425e4bc1).** O alvo correto: `O1 ⇒ HR`, `HR ⟺ D_N → 0`, `O1 ⇒ D_N → 0`; e "provar HR ⇏ O1"
  provaria HR (`alvo_correto`).
-/

open Complex Filter Topology Set MeasureTheory
open scoped Real

namespace ATK.ErrosAnaliticos

open ATK.XiAnalitica (F differentiable_F)

/-! ## E5. Cauchy–Riemann horizontal -/

theorem hasDerivAt_F_horizontal (d t : ℝ) :
    HasDerivAt (fun v : ℝ => F ((v : ℂ) + t * I)) (deriv F ((d : ℂ) + t * I)) d := by
  have hl : HasDerivAt (fun v : ℝ => ((v : ℂ) + t * I)) 1 d := by
    have := ((hasDerivAt_id (d : ℂ)).add_const ((t : ℂ) * I)).comp_ofReal
    simpa using this
  exact ((differentiable_F _).hasDerivAt.comp d hl).congr_deriv (mul_one _)

/-- **Cauchy–Riemann horizontal**: `∂_d Im F(d+it) = Im F′(d+it)`, `∂_d Re F(d+it) = Re F′(d+it)`. -/
theorem cauchy_riemann_horizontal (d t : ℝ) :
    HasDerivAt (fun v : ℝ => (F ((v : ℂ) + t * I)).im) (deriv F ((d : ℂ) + t * I)).im d ∧
      HasDerivAt (fun v : ℝ => (F ((v : ℂ) + t * I)).re) (deriv F ((d : ℂ) + t * I)).re d := by
  have h := hasDerivAt_F_horizontal d t
  exact ⟨Complex.imCLM.hasFDerivAt.comp_hasDerivAt d h, Complex.reCLM.hasFDerivAt.comp_hasDerivAt d h⟩

/-- **Contraexemplo na forma derivada** (`F = z²`, `d = 0`, `t = 1`): `∂_d Im F = 2`, `Re F′ = 0`. -/
theorem contraexemplo_derivada :
    HasDerivAt (fun v : ℝ => (((v : ℂ) + I) ^ 2).im) 2 0 ∧ (2 * (((0 : ℝ) : ℂ) + I)).re = 0 ∧
      (2 * (((0 : ℝ) : ℂ) + I)).im = 2 := by
  refine ⟨?_, by simp, by simp⟩
  have e : (fun v : ℝ => (((v : ℂ) + I) ^ 2).im) = fun v => 2 * v := by
    funext v; simp [sq]; ring
  rw [e]
  simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)

/-- `F(it) = Ξ(t)`. -/
theorem F_eixo (t : ℝ) : F ((t : ℂ) * I) = (ATK.BaseRiemannXi.Xi t : ℂ) :=
  ATK.BaseRiemannXi.riemannXi_critical t

/-- **A versão do texto é falsa para o próprio `ξ`**: existe `t` com `∂_d B(0,t) = Im F′(it) ≠ Re F′(it)`.
Se fosse `Im F′(it) = Re F′(it) (= 0)` para todo `t`, então `F′(it) = 0`, `t ↦ F(it) = Ξ(t)` seria
constante, contra `Ξ(0) > 0 = Ξ(γ₁)`. -/
theorem texto_Re_falso_para_xi : ∃ t : ℝ, (deriv F ((t : ℂ) * I)).im ≠ (deriv F ((t : ℂ) * I)).re := by
  by_contra h
  push Not at h
  have hz : ∀ t : ℝ, deriv F ((t : ℂ) * I) = 0 := by
    intro t
    have hr := ATK.XiAnalitica.deriv_F_imag t
    exact Complex.ext (by rw [hr]; rfl) (by rw [h t, hr]; rfl)
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => F ((s : ℂ) * I)) (deriv F ((t : ℂ) * I) * I) t := by
    intro t
    have hl : HasDerivAt (fun s : ℝ => (s : ℂ) * I) I t := by
      have := ((hasDerivAt_id (t : ℂ)).mul_const I).comp_ofReal
      simpa using this
    exact (differentiable_F _).hasDerivAt.comp t hl
  have hd : Differentiable ℝ (fun s : ℝ => F ((s : ℂ) * I)) := fun s => (hg s).differentiableAt
  have hc : ∀ t : ℝ, F ((t : ℂ) * I) = F (((0 : ℝ) : ℂ) * I) := fun t =>
    is_const_of_deriv_eq_zero hd (fun s => by rw [(hg s).deriv, hz s, zero_mul]) t 0
  obtain ⟨γ₁, h1, -⟩ := ATK.ZeroCert.primeiro_zero
  have hz1 : ATK.BaseRiemannXi.Xi γ₁ = 0 := (ATK.BaseRiemannXi.zeta_critical_zero_iff γ₁).mp h1
  have h0 := ATK.BaseRiemannXiSinal.Xi_zero_pos
  have := hc γ₁
  rw [F_eixo, F_eixo, hz1] at this
  have h00 : ATK.BaseRiemannXi.Xi 0 = 0 := by exact_mod_cast this.symm
  linarith

/-! ## E6. Tabela completa de multiplicidades -/

/-- **Multiplicidade de `½ + λ + iγ` em `G_λ`**: `4` se `λ = γ = 0`, `2` se exatamente um é `0`,
`1` caso contrário. -/
theorem multiplicidade_tabela (l g : ℝ) :
    (ATK.ClosedMath.Gpoly l g).rootMultiplicity ((1 / 2 : ℂ) + l + g * I) =
      if l = 0 ∧ g = 0 then 4 else if l = 0 ∨ g = 0 then 2 else 1 := by
  by_cases hl : l = 0 <;> by_cases hg : g = 0
  · subst hl; subst hg
    have e : ((1 / 2 : ℂ) + ((0 : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * I) = 1 / 2 := by simp
    rw [e, ATK.GeometriaExtra.cruzamento_tudo_zero]; simp
  · subst hl
    have e : ((1 / 2 : ℂ) + ((0 : ℝ) : ℂ) + (g : ℂ) * I) = 1 / 2 + g * I := by simp
    rw [e, ATK.ClosedMath.T7_multiplicidade_dois hg]; simp [hg]
  · subst hg
    have e : ((1 / 2 : ℂ) + (l : ℂ) + ((0 : ℝ) : ℂ) * I) = (1 / 2 : ℂ) + (l : ℂ) := by simp
    rw [e, ATK.GeometriaExtra.cruzamento_gamma_zero hl]; simp [hl]
  · rw [ATK.ClosedMath.zero_simples hl hg]; simp [hl, hg]

/-! ## E7. Jensen com `aₙ` × `γₙ = n!aₙ` -/

open ATK.ClosedMath.Jensen (gam turan_normalizacao jensen_grau2 Dmin Dmin_dois Dmin_tres_um)

/-- **Turán para `γ` implica Turán para `a`** (sempre). -/
theorem turan_gamma_implica_a (a : ℕ → ℝ) (k : ℕ)
    (h : gam a k * gam a (k + 2) ≤ gam a (k + 1) ^ 2) : a k * a (k + 2) ≤ a (k + 1) ^ 2 := by
  rw [turan_normalizacao] at h
  by_contra hc
  push Not at hc
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have hq : 0 ≤ a (k + 1) ^ 2 := sq_nonneg _
  have hP : 0 < a k * a (k + 2) := lt_of_le_of_lt hq hc
  have h1 : ((k : ℝ) + 1) * a (k + 1) ^ 2 ≤ ((k : ℝ) + 1) * (a k * a (k + 2)) :=
    mul_le_mul_of_nonneg_left hc.le (by linarith)
  have h2 : ((k : ℝ) + 2) * a k * a (k + 2) = ((k : ℝ) + 1) * (a k * a (k + 2)) + a k * a (k + 2) := by
    ring
  linarith

/-- **A recíproca é falsa**: `a = (1,1,1)` satisfaz Turán, `γ = (1,1,2)` não. -/
theorem turan_a_nao_implica_gamma :
    let a : ℕ → ℝ := fun n => if n ≤ 2 then 1 else 0
    a 0 * a 2 ≤ a 1 ^ 2 ∧ ¬ (gam a 0 * gam a 2 ≤ gam a 1 ^ 2) := by
  intro a
  simp [a, gam, Nat.factorial]

/-- **`Θ = 1 + x + x²`**: tem zeros não reais; o polinômio de grau 2 montado com `a = (1,1,1)`,
`z² + 2z + 1`, é hiperbólico (o teste do texto passa); o montado com `γ = (1,1,2)`, `2z² + 2z + 1`, não
(o teste correto detecta). -/
theorem jensen_a_falha_gamma_detecta :
    (∀ z : ℂ, ((1 : ℝ) : ℂ) * z ^ 2 + 2 * ((1 : ℝ) : ℂ) * z + ((1 : ℝ) : ℂ) = 0 → z.im = 0) ∧
      ¬ (∀ z : ℂ, ((2 : ℝ) : ℂ) * z ^ 2 + 2 * ((1 : ℝ) : ℂ) * z + ((1 : ℝ) : ℂ) = 0 → z.im = 0) ∧
      ∃ x : ℂ, 1 + x + x ^ 2 = 0 ∧ x.im ≠ 0 := by
  refine ⟨(jensen_grau2 (g0 := 1) (g1 := 1) (g2 := 1) one_ne_zero).mpr (by norm_num), ?_, ?_⟩
  · intro h
    have := (jensen_grau2 (g0 := 1) (g1 := 1) (g2 := 2) two_ne_zero).mp h
    norm_num at this
  · set s := Real.sqrt 3 with hs
    have hs2 : (s : ℂ) ^ 2 = 3 := by
      have : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      exact_mod_cast this
    refine ⟨(-1 + (s : ℂ) * I) / 2, ?_, ?_⟩
    · linear_combination ((s : ℂ) ^ 2 / 4) * I_sq - (1 / 4 : ℂ) * hs2
    · have hpos : 0 < s := Real.sqrt_pos.mpr (by norm_num)
      simp [Complex.div_ofNat_im]
      exact hpos.ne'

/-! ## E8. `TP∞(γ)` × `TP∞(a)` para `(1 + x)³` -/

/-- **`(1+x)³`**: `a = (1,3,3,1)` e `γ = (1,3,6,6)` satisfazem **todos** os menores 2×2 (Turán), mas
`D₃,₁(a) = 10` e `D₃,₁(γ) = −3`: Turán para `γ` não dá positividade total de `γ`. -/
theorem tp_binomial :
    (∀ k : ℕ, 0 ≤ Dmin (fun n => ((Nat.choose 3 n : ℕ) : ℝ)) 2 ((k : ℤ) + 1)) ∧
      (∀ k : ℕ, 0 ≤ Dmin (gam fun n => ((Nat.choose 3 n : ℕ) : ℝ)) 2 ((k : ℤ) + 1)) ∧
      Dmin (fun n => ((Nat.choose 3 n : ℕ) : ℝ)) 3 1 = 10 ∧
      Dmin (gam fun n => ((Nat.choose 3 n : ℕ) : ℝ)) 3 1 = -3 := by
  refine ⟨fun k => ?_, fun k => ?_, ATK.ClosedMath.Jensen.tp_a_nao_passa_gamma.1,
    ATK.ClosedMath.Jensen.tp_a_nao_passa_gamma.2⟩
  · rw [Dmin_dois, sub_nonneg]
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k <;> simp [Nat.choose] <;> norm_num
    · have h0 : Nat.choose 3 (k + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp only [h0, Nat.cast_zero, mul_zero]
      positivity
  · rw [Dmin_dois, sub_nonneg]
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k <;> simp [gam, Nat.choose, Nat.factorial] <;> norm_num
    · have h0 : Nat.choose 3 (k + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp only [gam, h0, Nat.cast_zero, mul_zero]
      positivity

/-! ## E9. O fator 2 em `Ξ(t) = 2∫₀^∞ Φ(u)cos(tu)du` -/

open ATK.BaseRiemannTeta (psi)

/-- **Para `Φ` par**: `∫_ℝ Φ(u)cos(tu)du = 2∫₀^∞ Φ(u)cos(tu)du`. -/
theorem integral_par {Φ : ℝ → ℝ} (hΦ : ∀ u, Φ (-u) = Φ u) (t : ℝ) :
    ∫ u, Φ u * Real.cos (t * u) = 2 * ∫ u in Ioi (0 : ℝ), Φ u * Real.cos (t * u) := by
  calc ∫ u, Φ u * Real.cos (t * u) = ∫ u, (fun v => Φ v * Real.cos (t * v)) |u| := by
        congr 1
        funext u
        rcases le_or_gt 0 u with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_neg h]
          show Φ u * Real.cos (t * u) = Φ (-u) * Real.cos (t * -u)
          rw [hΦ, mul_neg, Real.cos_neg]
    _ = 2 * ∫ u in Ioi (0 : ℝ), Φ u * Real.cos (t * u) :=
        integral_comp_abs (f := fun v => Φ v * Real.cos (t * v))

/-- **Substituição `x = e^{2u}`** (o jacobiano dá o fator `2`):
`∫₁^∞ ψ(x)x^{−3/4}cos(t/2·log x)dx = 2∫₀^∞ ψ(e^{2u})e^{u/2}cos(tu)du`. -/
theorem integral_u (t : ℝ) :
    ∫ x in Ioi (1 : ℝ), psi x * x ^ (-(3 / 4 : ℝ)) * Real.cos (t / 2 * Real.log x) =
      2 * ∫ u in Ioi (0 : ℝ), psi (Real.exp (2 * u)) * Real.exp (u / 2) * Real.cos (t * u) := by
  have h1 := integral_comp_exp_Ioi
    (fun x => psi x * x ^ (-(3 / 4 : ℝ)) * Real.cos (t / 2 * Real.log x)) 0
  rw [Real.exp_zero] at h1
  rw [← h1]
  have h2 := integral_comp_mul_left_Ioi
    (fun v => Real.exp v • (psi (Real.exp v) * Real.exp v ^ (-(3 / 4 : ℝ)) *
      Real.cos (t / 2 * Real.log (Real.exp v)))) 0 (two_pos : (0 : ℝ) < 2)
  rw [mul_zero] at h2
  have hpt : ∀ u : ℝ, Real.exp (2 * u) • (psi (Real.exp (2 * u)) * Real.exp (2 * u) ^ (-(3 / 4 : ℝ)) *
      Real.cos (t / 2 * Real.log (Real.exp (2 * u)))) =
      psi (Real.exp (2 * u)) * Real.exp (u / 2) * Real.cos (t * u) := by
    intro u
    rw [smul_eq_mul, ← Real.exp_mul, Real.log_exp]
    have he : Real.exp (2 * u) * Real.exp (2 * u * (-(3 / 4))) = Real.exp (u / 2) := by
      rw [← Real.exp_add]; ring_nf
    calc Real.exp (2 * u) * (psi (Real.exp (2 * u)) * Real.exp (2 * u * (-(3 / 4))) *
          Real.cos (t / 2 * (2 * u)))
        = psi (Real.exp (2 * u)) * (Real.exp (2 * u) * Real.exp (2 * u * (-(3 / 4)))) *
          Real.cos (t / 2 * (2 * u)) := by ring
      _ = psi (Real.exp (2 * u)) * Real.exp (u / 2) * Real.cos (t * u) := by
          rw [he, show t / 2 * (2 * u) = t * u by ring]
  have h3 : ∫ x in Ioi (0 : ℝ), Real.exp x • (psi (Real.exp x) * Real.exp x ^ (-(3 / 4 : ℝ)) *
      Real.cos (t / 2 * Real.log (Real.exp x))) =
      2 * ∫ u in Ioi (0 : ℝ), psi (Real.exp (2 * u)) * Real.exp (u / 2) * Real.cos (t * u) := by
    have h4 : ∫ x in Ioi (0 : ℝ), Real.exp (2 * x) • (psi (Real.exp (2 * x)) *
        Real.exp (2 * x) ^ (-(3 / 4 : ℝ)) * Real.cos (t / 2 * Real.log (Real.exp (2 * x)))) =
        ∫ u in Ioi (0 : ℝ), psi (Real.exp (2 * u)) * Real.exp (u / 2) * Real.cos (t * u) := by
      congr 1
      funext u
      exact hpt u
    rw [← h4, h2, smul_eq_mul]
    ring
  exact h3

/-- **Fórmula de Riemann na variável `u`**: `Ξ(t) = ½ − 2(t² + ¼)∫₀^∞ ψ(e^{2u})e^{u/2}cos(tu)du`. -/
theorem Xi_forma_u (t : ℝ) :
    ATK.BaseRiemannXi.Xi t = 1 / 2 - 2 * (t ^ 2 + 1 / 4) *
      ∫ u in Ioi (0 : ℝ), psi (Real.exp (2 * u)) * Real.exp (u / 2) * Real.cos (t * u) := by
  rw [ATK.BaseRiemannTeta.Xi_riemann, integral_u]
  ring

/-- **Sem o fator 2 a fórmula é falsa** (daria `Ξ(γ₁) = ½`, mas `Ξ(γ₁) = 0`). -/
theorem fator_um_falso :
    ¬ ∀ t : ℝ, ATK.BaseRiemannXi.Xi t = 1 / 2 - (t ^ 2 + 1 / 4) *
      ∫ u in Ioi (0 : ℝ), psi (Real.exp (2 * u)) * Real.exp (u / 2) * Real.cos (t * u) := by
  intro h
  obtain ⟨γ₁, h1, -⟩ := ATK.ZeroCert.primeiro_zero
  have hz : ATK.BaseRiemannXi.Xi γ₁ = 0 := (ATK.BaseRiemannXi.zeta_critical_zero_iff γ₁).mp h1
  set K := ∫ u in Ioi (0 : ℝ), psi (Real.exp (2 * u)) * Real.exp (u / 2) * Real.cos (γ₁ * u)
  have a := h γ₁
  have b : ATK.BaseRiemannXi.Xi γ₁ = 1 / 2 - 2 * ((γ₁ ^ 2 + 1 / 4) * K) := by
    rw [Xi_forma_u]; ring
  linarith

/-- Se `Ξ = 2I` para alguma `I`, então `Ξ = I` é falso (pois `Ξ(0) > 0`). -/
theorem fator_dois_essencial (J : ℝ → ℝ) (h : ∀ t, ATK.BaseRiemannXi.Xi t = 2 * J t) :
    ¬ ∀ t, ATK.BaseRiemannXi.Xi t = J t := by
  intro h'
  have h0 := ATK.BaseRiemannXiSinal.Xi_zero_pos
  have a := h 0
  have b := h' 0
  linarith

theorem integrableOn_mul_cos {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (c t : ℝ) :
    IntegrableOn (fun u => f u * (c * Real.cos (t * u))) (Ioi 0) := by
  refine Integrable.mul_bdd (c := |c|) hf ?_ (Eventually.of_forall fun u => ?_)
  · exact (by fun_prop : Continuous fun u => c * Real.cos (t * u)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg c) (Real.abs_cos_le_one _)

theorem integrableOn_mul_sin {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (c t : ℝ) :
    IntegrableOn (fun u => f u * (c * Real.sin (t * u))) (Ioi 0) := by
  refine Integrable.mul_bdd (c := |c|) hf ?_ (Eventually.of_forall fun u => ?_)
  · exact (by fun_prop : Continuous fun u => c * Real.sin (t * u)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg c) (Real.abs_sin_le_one _)

/-- **Duas integrações por partes**: se `g, g′, g″` são integráveis em `(0,∞)` e `g, g′ → 0`, então
`t²∫₀^∞ g cos(tu) = −g′(0) − ∫₀^∞ g″ cos(tu)`. -/
theorem ibp_cos {g g' g'' : ℝ → ℝ} (t : ℝ)
    (hg : ∀ u ∈ Ici (0 : ℝ), HasDerivAt g (g' u) u) (hg' : ∀ u ∈ Ici (0 : ℝ), HasDerivAt g' (g'' u) u)
    (i0 : IntegrableOn g (Ioi 0)) (i1 : IntegrableOn g' (Ioi 0)) (i2 : IntegrableOn g'' (Ioi 0))
    (l0 : Tendsto g atTop (𝓝 0)) (l1 : Tendsto g' atTop (𝓝 0)) :
    t ^ 2 * ∫ u in Ioi (0 : ℝ), g u * Real.cos (t * u) =
      -g' 0 - ∫ u in Ioi (0 : ℝ), g'' u * Real.cos (t * u) := by
  have hs : ∀ u : ℝ, HasDerivAt (fun u => t * Real.sin (t * u)) (t ^ 2 * Real.cos (t * u)) u := by
    intro u
    exact ((((hasDerivAt_id' u).const_mul t).sin).const_mul t).congr_deriv (by ring)
  have hc : ∀ u : ℝ, HasDerivAt (fun u => -Real.cos (t * u)) (t * Real.sin (t * u)) u := by
    intro u
    exact ((((hasDerivAt_id' u).const_mul t).cos).neg).congr_deriv (by ring)
  have bs : IsBoundedUnder (· ≤ ·) atTop (fun u => ‖t * Real.sin (t * u)‖) :=
    isBoundedUnder_of ⟨|t|, fun u => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg t) (Real.abs_sin_le_one _)⟩
  have bc : IsBoundedUnder (· ≤ ·) atTop (fun u => ‖-Real.cos (t * u)‖) :=
    isBoundedUnder_of ⟨1, fun u => by
      rw [norm_neg, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _⟩
  -- primeira integração por partes
  have zA : Tendsto (fun x => g x * (t * Real.sin (t * x))) (𝓝[>] 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun x => g x * (t * Real.sin (t * x))) 0 :=
      (hg 0 self_mem_Ici).continuousAt.mul (by fun_prop)
    have := hcont.tendsto
    have hv : g 0 * (t * Real.sin (t * 0)) = 0 := by simp
    rw [hv] at this
    exact this.mono_left nhdsWithin_le_nhds
  have iA : Tendsto (fun x => g x * (t * Real.sin (t * x))) atTop (𝓝 0) :=
    l0.zero_mul_isBoundedUnder_le bs
  have hA := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (u := g) (u' := g')
    (v := fun u => t * Real.sin (t * u)) (v' := fun u => t ^ 2 * Real.cos (t * u))
    (fun x hx => hg x (mem_Ici.mpr (mem_Ioi.mp hx).le)) (fun x _ => hs x) (integrableOn_mul_cos i0 (t ^ 2) t)
    (integrableOn_mul_sin i1 t t) zA iA
  -- segunda integração por partes
  have zB : Tendsto (fun x => g' x * -Real.cos (t * x)) (𝓝[>] 0) (𝓝 (-g' 0)) := by
    have hcont : ContinuousAt (fun x => g' x * -Real.cos (t * x)) 0 :=
      (hg' 0 self_mem_Ici).continuousAt.mul (by fun_prop)
    have := hcont.tendsto
    have hv : g' 0 * -Real.cos (t * 0) = -g' 0 := by simp
    rw [hv] at this
    exact this.mono_left nhdsWithin_le_nhds
  have iB : Tendsto (fun x => g' x * -Real.cos (t * x)) atTop (𝓝 0) :=
    l1.zero_mul_isBoundedUnder_le bc
  have iB2 : IntegrableOn (fun x => g'' x * -Real.cos (t * x)) (Ioi 0) := by
    have := integrableOn_mul_cos i2 (-1) t
    refine this.congr_fun (fun x _ => by ring) measurableSet_Ioi
  have hB := integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (u := g') (u' := g'')
    (v := fun u => -Real.cos (t * u)) (v' := fun u => t * Real.sin (t * u))
    (fun x hx => hg' x (mem_Ici.mpr (mem_Ioi.mp hx).le)) (fun x _ => hc x) (integrableOn_mul_sin i1 t t) iB2 zB iB
  have e1 : t ^ 2 * ∫ u in Ioi (0 : ℝ), g u * Real.cos (t * u) =
      ∫ u in Ioi (0 : ℝ), g u * (t ^ 2 * Real.cos (t * u)) := by
    rw [← integral_const_mul]; congr 1; funext u; ring
  have e2 : ∫ u in Ioi (0 : ℝ), g'' u * -Real.cos (t * u) =
      -∫ u in Ioi (0 : ℝ), g'' u * Real.cos (t * u) := by
    rw [← integral_neg]; congr 1; funext u; ring
  rw [e1, hA, hB, e2]
  ring

/-- **Forma `2∫₀^∞(g″ − g/4)cos`** (condicional): com `g(u) = ψ(e^{2u})e^{u/2}` e as hipóteses de
regularidade/decaimento, `Ξ(t) = (½ + 2g′(0)) + 2∫₀^∞ (g″(u) − g(u)/4)cos(tu)du`. O fator `2` multiplica
a integral em `(0, ∞)`. -/
theorem Xi_forma_Phi {g' g'' : ℝ → ℝ}
    (hg : ∀ u ∈ Ici (0 : ℝ),
      HasDerivAt (fun u => psi (Real.exp (2 * u)) * Real.exp (u / 2)) (g' u) u)
    (hg' : ∀ u ∈ Ici (0 : ℝ), HasDerivAt g' (g'' u) u)
    (i0 : IntegrableOn (fun u => psi (Real.exp (2 * u)) * Real.exp (u / 2)) (Ioi 0))
    (i1 : IntegrableOn g' (Ioi 0)) (i2 : IntegrableOn g'' (Ioi 0))
    (l0 : Tendsto (fun u => psi (Real.exp (2 * u)) * Real.exp (u / 2)) atTop (𝓝 0))
    (l1 : Tendsto g' atTop (𝓝 0)) (t : ℝ) :
    ATK.BaseRiemannXi.Xi t = (1 / 2 + 2 * g' 0) +
      2 * ∫ u in Ioi (0 : ℝ),
        (g'' u - psi (Real.exp (2 * u)) * Real.exp (u / 2) / 4) * Real.cos (t * u) := by
  have h := ibp_cos t hg hg' i0 i1 i2 l0 l1
  rw [Xi_forma_u]
  have ia : IntegrableOn (fun u => g'' u * Real.cos (t * u)) (Ioi 0) := by
    have := integrableOn_mul_cos i2 1 t
    exact this.congr_fun (fun x _ => by ring) measurableSet_Ioi
  have ib : IntegrableOn (fun u => 1 / 4 * (psi (Real.exp (2 * u)) * Real.exp (u / 2) *
      Real.cos (t * u))) (Ioi 0) := by
    have := integrableOn_mul_cos i0 (1 / 4) t
    exact this.congr_fun (fun x _ => by ring) measurableSet_Ioi
  have e : ∫ u in Ioi (0 : ℝ),
      (g'' u - psi (Real.exp (2 * u)) * Real.exp (u / 2) / 4) * Real.cos (t * u) =
      (∫ u in Ioi (0 : ℝ), g'' u * Real.cos (t * u)) - 1 / 4 *
        ∫ u in Ioi (0 : ℝ), psi (Real.exp (2 * u)) * Real.exp (u / 2) * Real.cos (t * u) := by
    rw [← integral_const_mul, ← integral_sub ia ib]
    congr 1; funext u; ring
  rw [e]
  linear_combination (-2 : ℝ) * h

/-! ## E10. `M₊(T)` e a região vazia -/

open ATK.ClosedMath.Jensen (xiE)

/-- `R(T) = [½ + 1/T, 1 − 1/T] × [−T, T]`. -/
def R (T : ℝ) : Set ℂ := Icc (1 / 2 + 1 / T) (1 - 1 / T) ×ℂ Icc (-T) T

/-- `M₊(T) = inf_{R(T)} |ξ|`. -/
noncomputable def Mplus (T : ℝ) : ℝ := sInf ((fun s => ‖xiE s‖) '' R T)

/-- **Para `0 < T < 4` a região é vazia.** -/
theorem R_vazio {T : ℝ} (h0 : 0 < T) (h4 : T < 4) : R T = ∅ := by
  ext s
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, h2⟩, -⟩
  have : 1 / 4 < 1 / T := one_div_lt_one_div_of_lt h0 h4
  linarith

theorem Mplus_vazio {T : ℝ} (h0 : 0 < T) (h4 : T < 4) : Mplus T = 0 := by
  unfold Mplus; rw [R_vazio h0 h4, Set.image_empty, Real.sInf_empty]

/-- **"`∀T > 2, M₊(T) > 0`" é falso** (em `T = 3`), qualquer que seja HR. -/
theorem texto_M_falso : ¬ ∀ T > (2 : ℝ), 0 < Mplus T := by
  intro h
  have := h 3 (by norm_num)
  rw [Mplus_vazio (by norm_num) (by norm_num)] at this
  exact lt_irrefl _ this

/-- A equivalência do texto implicaria `¬HR`. -/
theorem texto_equivalencia_daria_nao_rh :
    (RiemannHypothesis ↔ ∀ T > (2 : ℝ), 0 < Mplus T) → ¬ RiemannHypothesis :=
  fun h hRH => texto_M_falso (h.mp hRH)

theorem R_compacto (T : ℝ) : IsCompact (R T) := isCompact_Icc.reProdIm isCompact_Icc

theorem R_nao_vazio {T : ℝ} (h : 4 ≤ T) : (R T).Nonempty := by
  have hT : 0 < T := by linarith
  have h14 : 1 / T ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) h
  refine ⟨((3 / 4 : ℝ) : ℂ), ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [Complex.ofReal_re]; linarith
  · simp only [Complex.ofReal_re]; linarith
  · simp only [Complex.ofReal_im]; linarith
  · simp only [Complex.ofReal_im]; linarith

/-- **Correção: `HR ⟺ ∀T ≥ 4, M₊(T) > 0`.** -/
theorem rh_iff_Mplus : RiemannHypothesis ↔ ∀ T ≥ (4 : ℝ), 0 < Mplus T := by
  constructor
  · intro hRH T hT
    have hcont : Continuous fun s => ‖xiE s‖ :=
      continuous_norm.comp ATK.XiAnalitica.differentiable_xiE.continuous
    obtain ⟨x, hx, hmin⟩ := (R_compacto T).exists_isMinOn (R_nao_vazio hT) hcont.continuousOn
    have hle : IsLeast ((fun s => ‖xiE s‖) '' R T) ‖xiE x‖ :=
      ⟨⟨x, hx, rfl⟩, by rintro _ ⟨y, hy, rfl⟩; exact hmin hy⟩
    unfold Mplus
    rw [hle.csInf_eq]
    have hre : 1 / 2 < x.re := by
      have h1 := hx.1.1
      have : 0 < 1 / T := by have : (0 : ℝ) < T := by linarith
                             positivity
      linarith
    exact norm_pos_iff.mpr ((ATK.XiAnalitica.rh_iff_xiE_direita.mp hRH) x hre)
  · intro h
    rw [ATK.XiAnalitica.rh_iff_xiE_direita]
    intro s hs hz
    have h1 : s.re < 1 := by
      by_contra hc
      exact ATK.ClosedMath.Jensen.xiE_ne_zero_of_one_le_re (not_lt.mp hc) hz
    have hd1 : 0 < s.re - 1 / 2 := by linarith
    have hd2 : 0 < 1 - s.re := by linarith
    set T := max 4 (max |s.im| (max (1 / (s.re - 1 / 2)) (1 / (1 - s.re)))) with hT
    have hT4 : 4 ≤ T := le_max_left _ _
    have hTpos : 0 < T := by linarith
    have hTa : 1 / (s.re - 1 / 2) ≤ T :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    have hTb : 1 / (1 - s.re) ≤ T :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
    have hTi : |s.im| ≤ T := le_trans (le_max_left _ _) (le_max_right _ _)
    have ha : 1 / T ≤ s.re - 1 / 2 := by
      rw [div_le_iff₀ hd1] at hTa
      rw [div_le_iff₀ hTpos]
      have := mul_comm T (s.re - 1 / 2)
      linarith
    have hb : 1 / T ≤ 1 - s.re := by
      rw [div_le_iff₀ hd2] at hTb
      rw [div_le_iff₀ hTpos]
      have := mul_comm T (1 - s.re)
      linarith
    have hmem : s ∈ R T := by
      obtain ⟨hi1, hi2⟩ := abs_le.mp hTi
      exact ⟨⟨by linarith, by linarith⟩, hi1, hi2⟩
    have hle : Mplus T ≤ ‖xiE s‖ :=
      csInf_le ⟨0, by rintro _ ⟨y, -, rfl⟩; exact norm_nonneg _⟩ ⟨s, hmem, rfl⟩
    rw [hz, norm_zero] at hle
    have := h T hT4
    linarith

/-! ## E11. O alvo correto -/

/-- **`O1 ⇒ HR`, `HR ⟺ D_N → 0`, `O1 ⇒ D_N → 0`; provar `¬(HR → Q)` provaria HR.** -/
theorem alvo_correto :
    (ATK.Conditional.Riemann.UniformLogBound → RiemannHypothesis) ∧
      (RiemannHypothesis ↔ Tendsto ATK.Conditional.Riemann.DN atTop (𝓝 0)) ∧
      (ATK.Conditional.Riemann.UniformLogBound → Tendsto ATK.Conditional.Riemann.DN atTop (𝓝 0)) ∧
      (∀ Q : Prop, ¬ (RiemannHypothesis → Q) → RiemannHypothesis) :=
  ⟨ATK.BaezDuarteBridge.riemann_of_uniformLogBound, ATK.NecessidadeRH.rh_iff_DN,
    ATK.Conditional.Riemann.DN_tendsto_zero,
    fun Q h => (ATK.GeometriaExtra.nao_implica_prova_rh Q h).1⟩

end ATK.ErrosAnaliticos

-- Auditoria de axiomas (kernel)
#print axioms ATK.ErrosAnaliticos.hasDerivAt_F_horizontal
#print axioms ATK.ErrosAnaliticos.cauchy_riemann_horizontal
#print axioms ATK.ErrosAnaliticos.contraexemplo_derivada
#print axioms ATK.ErrosAnaliticos.F_eixo
#print axioms ATK.ErrosAnaliticos.texto_Re_falso_para_xi
#print axioms ATK.ErrosAnaliticos.multiplicidade_tabela
#print axioms ATK.ErrosAnaliticos.turan_gamma_implica_a
#print axioms ATK.ErrosAnaliticos.turan_a_nao_implica_gamma
#print axioms ATK.ErrosAnaliticos.jensen_a_falha_gamma_detecta
#print axioms ATK.ErrosAnaliticos.tp_binomial
#print axioms ATK.ErrosAnaliticos.integral_par
#print axioms ATK.ErrosAnaliticos.integral_u
#print axioms ATK.ErrosAnaliticos.Xi_forma_u
#print axioms ATK.ErrosAnaliticos.fator_um_falso
#print axioms ATK.ErrosAnaliticos.fator_dois_essencial
#print axioms ATK.ErrosAnaliticos.integrableOn_mul_cos
#print axioms ATK.ErrosAnaliticos.integrableOn_mul_sin
#print axioms ATK.ErrosAnaliticos.ibp_cos
#print axioms ATK.ErrosAnaliticos.Xi_forma_Phi
#print axioms ATK.ErrosAnaliticos.R_vazio
#print axioms ATK.ErrosAnaliticos.Mplus_vazio
#print axioms ATK.ErrosAnaliticos.texto_M_falso
#print axioms ATK.ErrosAnaliticos.texto_equivalencia_daria_nao_rh
#print axioms ATK.ErrosAnaliticos.R_compacto
#print axioms ATK.ErrosAnaliticos.R_nao_vazio
#print axioms ATK.ErrosAnaliticos.rh_iff_Mplus
#print axioms ATK.ErrosAnaliticos.alvo_correto
