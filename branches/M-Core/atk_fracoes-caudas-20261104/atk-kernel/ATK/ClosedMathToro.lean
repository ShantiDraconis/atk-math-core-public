import ATK.ClosedMathCompleto

/-!
# ATK — Closed Math no toro, fluxos, tempos verbais e o modelo com zeros triviais

1. **Toro** `𝕋(s) = ((R + r cos 2πσ) cos(2πt/T), (R + r cos 2πσ) sin(2πt/T), r sin 2πσ)`:
   superfície exata, dupla periodicidade (perde `Re mod 1` e `Im mod T`), operadores como isometrias
   de `ℝ³` (`R` = espelho `z ↦ −z`, `J` = espelho `y ↦ −y`, `S = 1 − s` = rotação de `π` em torno
   do eixo `x`, com exatamente os pontos fixos `σ ∈ ½ℤ, t ∈ (T/2)ℤ`), linha crítica = **equador
   interno** de raio `R − r`, **HR ⟺ todo zero não trivial cai no plano equatorial**, distância do par
   `2r|sin 2πδ|`, **reencontro artificial** em `λ = ½` (no plano os zeros seguem simples), toro elevado
   injetivo na faixa; métrica `E = r², F = 0, G = (R + r cos θ)²` derivada da imersão, curvatura
   `K = cos θ / (r(R + r cos θ))`: a linha crítica cai no mínimo `−1/(r(R − r)) < 0`, a faixa central
   `¼ < σ < ¾` é exatamente a região de curvatura negativa; área `4π²Rr`; curvatura total `0`
   (Gauss–Bonnet, `χ = 0`).
2. **Fluxos**: `Φ_λ(s) = s + λ` (grupo a um parâmetro), os zeros de `G_λ` são as órbitas dos zeros
   críticos; no toro o fluxo atravessa o equador interno **transversalmente** com velocidade
   vertical `−2πr`; conjugado por `T` vira translação vertical.
3. **Tempos verbais**: cada afirmação carrega o tempo (`perfeito` = foi provado, `negado` = foi
   refutado, `condicional` = seria, se `H`, `futuro` = aberto, `presente` = observado numericamente)
   e o tipo **exige** a testemunha correspondente.
4. **Modelo `H_{d,γ}`** com zeros triviais `−2, −4, …` (via `1/Γ(1 + s/2)`), zeros críticos e
   externos, **ordem 3** no encontro, **princípio do argumento para multiconjuntos** e a contagem
   `(1/2πi)∮ H'/H = 6` antes e no encontro.
5. **Pontes**: transporte de zeros `G(φ s) = u(s) F(s)` (com e sem `u ≠ 0`), preservação de
   multiplicidade por fator holomorfo não nulo (B17), singularidade removível, `ξ(1 − s) = ξ(s)`,
   `ξ = 0 ⟺ ζ = 0` na faixa (B20).
-/

open Complex Filter Topology Set

namespace ATK.ClosedMath

open ATK.CEZ ATK.ZetaSimetria ATK.ModeloParametrico

/-! ## 1. Toro -/

/-- Imersão no toro de raios `R > r > 0` e período vertical `T`. -/
noncomputable def tor (R r T : ℝ) (s : ℂ) : ℝ × ℝ × ℝ :=
  ((R + r * Real.cos (2 * Real.pi * s.re)) * Real.cos (2 * Real.pi * s.im / T),
   (R + r * Real.cos (2 * Real.pi * s.re)) * Real.sin (2 * Real.pi * s.im / T),
   r * Real.sin (2 * Real.pi * s.re))

theorem raio_pos {R r : ℝ} (hr : 0 ≤ r) (hRr : r < R) (θ : ℝ) : 0 < R + r * Real.cos θ := by
  have := Real.neg_one_le_cos θ
  nlinarith

/-- A imagem está na superfície do toro `(√(x² + y²) − R)² + z² = r²`. -/
theorem tor_superficie {R r : ℝ} (T : ℝ) (hr : 0 ≤ r) (hRr : r < R) (s : ℂ) :
    (Real.sqrt ((tor R r T s).1 ^ 2 + (tor R r T s).2.1 ^ 2) - R) ^ 2 + (tor R r T s).2.2 ^ 2 =
      r ^ 2 := by
  unfold tor
  simp only
  have hp := raio_pos hr hRr (2 * Real.pi * s.re)
  have e : ((R + r * Real.cos (2 * Real.pi * s.re)) * Real.cos (2 * Real.pi * s.im / T)) ^ 2 +
      ((R + r * Real.cos (2 * Real.pi * s.re)) * Real.sin (2 * Real.pi * s.im / T)) ^ 2 =
        (R + r * Real.cos (2 * Real.pi * s.re)) ^ 2 := by
    have := Real.cos_sq_add_sin_sq (2 * Real.pi * s.im / T)
    linear_combination (R + r * Real.cos (2 * Real.pi * s.re)) ^ 2 * this
  rw [e, Real.sqrt_sq hp.le]
  have := Real.cos_sq_add_sin_sq (2 * Real.pi * s.re)
  linear_combination r ^ 2 * this

/-- Dupla periodicidade: o toro esquece `Re mod 1` … -/
theorem tor_periodo_re (R r T : ℝ) (s : ℂ) : tor R r T (s + 1) = tor R r T s := by
  unfold tor
  simp only [add_re, one_re, add_im, one_im, add_zero]
  rw [show 2 * Real.pi * (s.re + 1) = 2 * Real.pi * s.re + 2 * Real.pi by ring, Real.cos_add_two_pi,
    Real.sin_add_two_pi]

/-- … e `Im mod T`. -/
theorem tor_periodo_im (R r : ℝ) {T : ℝ} (hT : T ≠ 0) (s : ℂ) :
    tor R r T (s + T * I) = tor R r T s := by
  unfold tor
  simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add]
  rw [show 2 * Real.pi * (s.im + T) / T = 2 * Real.pi * s.im / T + 2 * Real.pi by field_simp,
    Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- `R = 1 − s̄` age como o espelho `z ↦ −z`. -/
theorem tor_R (R r T : ℝ) (s : ℂ) :
    tor R r T (torcao s) = ((tor R r T s).1, (tor R r T s).2.1, -(tor R r T s).2.2) := by
  unfold tor
  rw [re_torcao, EixoDeslocado.im_torcao]
  rw [show 2 * Real.pi * (1 - s.re) = 2 * Real.pi - 2 * Real.pi * s.re by ring,
    Real.cos_two_pi_sub, Real.sin_two_pi_sub]
  simp only [mul_neg]

/-- `J = s̄` age como o espelho `y ↦ −y`. -/
theorem tor_J (R r T : ℝ) (s : ℂ) :
    tor R r T (opJ s) = ((tor R r T s).1, -(tor R r T s).2.1, (tor R r T s).2.2) := by
  unfold tor opJ
  simp only [conj_re, conj_im]
  rw [show 2 * Real.pi * -s.im / T = -(2 * Real.pi * s.im / T) by ring, Real.cos_neg, Real.sin_neg]
  simp only [mul_neg]

/-- `S = 1 − s` age como a rotação de `π` em torno do eixo `x`: `(x, y, z) ↦ (x, −y, −z)`. -/
theorem tor_S (R r T : ℝ) (s : ℂ) :
    tor R r T (opS s) = ((tor R r T s).1, -(tor R r T s).2.1, -(tor R r T s).2.2) := by
  have : opS s = opJ (torcao s) := (J_R s).symm
  rw [this, tor_J, tor_R]

/-- A linha crítica vai para o **equador interno**, círculo de raio `R − r` no plano `z = 0`. -/
theorem tor_linha (R r T t : ℝ) :
    tor R r T ((1 / 2 : ℂ) + t * I) =
      ((R - r) * Real.cos (2 * Real.pi * t / T), (R - r) * Real.sin (2 * Real.pi * t / T), 0) := by
  unfold tor
  simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add]
  have h1 : (2 : ℝ) * Real.pi * (1 / 2 : ℂ).re = Real.pi := by simp; ring
  have h2 : (1 / 2 : ℂ).im = 0 := by simp
  rw [h1, h2, zero_add, Real.cos_pi, Real.sin_pi]
  simp only [mul_neg, mul_one, mul_zero]
  constructor <;> ring

theorem sin_dois_pi_faixa {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    Real.sin (2 * Real.pi * σ) = 0 ↔ σ = 1 / 2 := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
    have hpi := Real.pi_pos
    have e : (n : ℝ) = 2 * σ := by
      have := hn; field_simp at this ⊢; nlinarith [this]
    have a : (0 : ℝ) < n := by rw [e]; linarith
    have b : (n : ℝ) < 2 := by rw [e]; linarith
    have hn1 : n = 1 := by
      have a' : 0 < n := by exact_mod_cast a
      have b' : n < 2 := by exact_mod_cast b
      omega
    rw [hn1] at e
    push_cast at e
    linarith
  · rintro rfl
    rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring, Real.sin_pi]

/-- Na faixa `0 < Re s < 1`, um ponto está no plano do espelho (`z = 0`) **sse** está na linha. -/
theorem tor_plano_iff {R r T : ℝ} (hr : r ≠ 0) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    (tor R r T s).2.2 = 0 ↔ s.re = 1 / 2 := by
  unfold tor
  simp only [mul_eq_zero, hr, false_or]
  exact sin_dois_pi_faixa h0 h1

/-- … equivalentemente, sse é fixado pelo espelho `R`. -/
theorem tor_R_fixo_iff {R r T : ℝ} (hr : r ≠ 0) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    tor R r T (torcao s) = tor R r T s ↔ s.re = 1 / 2 := by
  rw [tor_R, ← tor_plano_iff (T := T) (R := R) hr h0 h1]
  constructor
  · intro h
    have := congrArg (fun p => p.2.2) h
    simp only at this
    linarith
  · intro h
    exact Prod.ext rfl (Prod.ext rfl (by simp [h]))

/-- **HR no toro**: a Hipótese de Riemann equivale a todo zero não trivial cair no plano equatorial
(o equador interno). -/
theorem rh_iff_equador {R r T : ℝ} (hr : r ≠ 0) :
    RiemannHypothesis ↔ ∀ ρ ∈ Z, (tor R r T ρ).2.2 = 0 := by
  rw [rh_iff_externa_vazia]
  constructor
  · intro h ρ hρ
    rw [tor_plano_iff hr hρ.2.1 hρ.2.2]
    by_contra hne
    have : ρ ∈ ZE := ⟨hρ, hne⟩
    rw [h] at this
    exact this
  · intro h
    ext ρ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hρ, hne⟩
    exact hne ((tor_plano_iff hr hρ.2.1 hρ.2.2).mp (h ρ hρ))

/-- Pontos fixos de `S` no toro: exatamente `σ ∈ ½ℤ` e `t ∈ (T/2)ℤ` (quatro pontos por célula). -/
theorem tor_S_fixo_iff {R r T : ℝ} (hr : 0 < r) (hRr : r < R) (hT : T ≠ 0) (s : ℂ) :
    tor R r T (opS s) = tor R r T s ↔
      (∃ m : ℤ, s.re = m / 2) ∧ ∃ n : ℤ, s.im = n * T / 2 := by
  rw [tor_S]
  have hp := raio_pos hr.le hRr (2 * Real.pi * s.re)
  have hpi := Real.pi_pos
  constructor
  · intro h
    have hy := congrArg (fun p => p.2.1) h
    have hz := congrArg (fun p => p.2.2) h
    simp only [tor] at hy hz
    have sy : Real.sin (2 * Real.pi * s.im / T) = 0 := by
      have : (R + r * Real.cos (2 * Real.pi * s.re)) * Real.sin (2 * Real.pi * s.im / T) = 0 := by
        linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact h
    have sz : Real.sin (2 * Real.pi * s.re) = 0 := by
      have : r * Real.sin (2 * Real.pi * s.re) = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · exact h
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp sz
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp sy
    refine ⟨⟨m, ?_⟩, ⟨n, ?_⟩⟩
    · field_simp; nlinarith [hm]
    · field_simp at hn ⊢; nlinarith [hn]
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    have sz : Real.sin (2 * Real.pi * s.re) = 0 := by
      rw [hm, show 2 * Real.pi * (m / 2) = m * Real.pi by ring]; exact Real.sin_int_mul_pi m
    have sy : Real.sin (2 * Real.pi * s.im / T) = 0 := by
      rw [hn, show 2 * Real.pi * (n * T / 2) / T = n * Real.pi by field_simp]
      exact Real.sin_int_mul_pi n
    unfold tor
    simp only [sz, sy, mul_zero, neg_zero]

/-- Distância do par simétrico no toro: `|𝕋(s₊) − 𝕋(s₋)|² = (2r sin 2πδ)²`. -/
theorem tor_dist_par (R r T d t : ℝ) :
    ((tor R r T (((1 / 2 + d : ℝ) : ℂ) + t * I)).1 - (tor R r T (((1 / 2 - d : ℝ) : ℂ) + t * I)).1) ^ 2 +
      ((tor R r T (((1 / 2 + d : ℝ) : ℂ) + t * I)).2.1 -
          (tor R r T (((1 / 2 - d : ℝ) : ℂ) + t * I)).2.1) ^ 2 +
      ((tor R r T (((1 / 2 + d : ℝ) : ℂ) + t * I)).2.2 -
          (tor R r T (((1 / 2 - d : ℝ) : ℂ) + t * I)).2.2) ^ 2 =
      (2 * r * Real.sin (2 * Real.pi * d)) ^ 2 := by
  unfold tor
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add]
  rw [show 2 * Real.pi * (1 / 2 + d) = 2 * Real.pi * d + Real.pi by ring, Real.cos_add_pi,
    Real.sin_add_pi, show 2 * Real.pi * (1 / 2 - d) = Real.pi - 2 * Real.pi * d by ring,
    Real.cos_pi_sub, Real.sin_pi_sub]
  ring

/-- **Reencontro artificial**: em `λ = ½` os ramos `0 + iγ` e `1 + iγ` coincidem no toro, embora no
plano sejam zeros distintos e simples de `G_{½,γ}`. -/
theorem tor_reencontro (R r T : ℝ) {g : ℝ} (hg : g ≠ 0) :
    tor R r T (1 / 2 + ((1 / 2 : ℝ) : ℂ) + g * I) = tor R r T (1 / 2 - ((1 / 2 : ℝ) : ℂ) + g * I) ∧
      (1 / 2 + ((1 / 2 : ℝ) : ℂ) + g * I) ≠ 1 / 2 - ((1 / 2 : ℝ) : ℂ) + g * I ∧
      (Gpoly (1 / 2) g).rootMultiplicity (1 / 2 + ((1 / 2 : ℝ) : ℂ) + g * I) = 1 := by
  refine ⟨?_, ?_, zero_simples (by norm_num) hg⟩
  · have : (1 / 2 + ((1 / 2 : ℝ) : ℂ) + g * I) = (1 / 2 - ((1 / 2 : ℝ) : ℂ) + g * I) + 1 := by
      push_cast; ring
    rw [this, tor_periodo_re]
  · intro h
    have := congrArg Complex.re h
    norm_num at this

/-- O toro esquece a altura: `𝕋(s + iT) = 𝕋(s)`; o **toro elevado** `(𝕋(s), Im s)` é injetivo na faixa. -/
theorem tor_elevado_injOn {R r T : ℝ} (hr : 0 < r) (hRr : r < R) :
    Set.InjOn (fun s : ℂ => (tor R r T s, s.im)) {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  intro s hs w hw h
  simp only [Prod.mk.injEq] at h
  obtain ⟨ht, him⟩ := h
  apply Cil_injOn hs hw
  unfold Cil
  have hz := congrArg (fun p => p.2.2) ht
  unfold tor at hz
  simp only at hz
  have hsin : Real.sin (2 * Real.pi * s.re) = Real.sin (2 * Real.pi * w.re) :=
    mul_left_cancel₀ hr.ne' hz
  have hxy : ((tor R r T s).1) ^ 2 + ((tor R r T s).2.1) ^ 2 =
      ((tor R r T w).1) ^ 2 + ((tor R r T w).2.1) ^ 2 := by rw [ht]
  unfold tor at hxy
  simp only at hxy
  rw [him] at hxy
  have c1 := Real.cos_sq_add_sin_sq (2 * Real.pi * w.im / T)
  have e1 : (R + r * Real.cos (2 * Real.pi * s.re)) ^ 2 = (R + r * Real.cos (2 * Real.pi * w.re)) ^ 2 := by
    linear_combination hxy + ((R + r * Real.cos (2 * Real.pi * w.re)) ^ 2 -
      (R + r * Real.cos (2 * Real.pi * s.re)) ^ 2) * c1
  have p1 := raio_pos hr.le hRr (2 * Real.pi * s.re)
  have p2 := raio_pos hr.le hRr (2 * Real.pi * w.re)
  have e2 : R + r * Real.cos (2 * Real.pi * s.re) = R + r * Real.cos (2 * Real.pi * w.re) := by
    nlinarith [e1]
  have hcos : Real.cos (2 * Real.pi * s.re) = Real.cos (2 * Real.pi * w.re) :=
    mul_left_cancel₀ hr.ne' (by linarith)
  rw [hcos, hsin, him]

/-! ### Métrica e curvatura do toro -/

/-- Parametrização `X(θ, φ)`. -/
noncomputable def X (R r θ φ : ℝ) : ℝ × ℝ × ℝ :=
  ((R + r * Real.cos θ) * Real.cos φ, (R + r * Real.cos θ) * Real.sin φ, r * Real.sin θ)

theorem dX_dθ (R r θ φ : ℝ) :
    HasDerivAt (fun θ => (R + r * Real.cos θ) * Real.cos φ) (-r * Real.sin θ * Real.cos φ) θ ∧
    HasDerivAt (fun θ => (R + r * Real.cos θ) * Real.sin φ) (-r * Real.sin θ * Real.sin φ) θ ∧
    HasDerivAt (fun θ => r * Real.sin θ) (r * Real.cos θ) θ := by
  have h := ((Real.hasDerivAt_cos θ).const_mul r).const_add R
  refine ⟨?_, ?_, ?_⟩
  · convert h.mul_const (Real.cos φ) using 1; ring
  · convert h.mul_const (Real.sin φ) using 1; ring
  · exact (Real.hasDerivAt_sin θ).const_mul r

theorem dX_dφ (R r θ φ : ℝ) :
    HasDerivAt (fun φ => (R + r * Real.cos θ) * Real.cos φ) (-(R + r * Real.cos θ) * Real.sin φ) φ ∧
    HasDerivAt (fun φ => (R + r * Real.cos θ) * Real.sin φ) ((R + r * Real.cos θ) * Real.cos φ) φ := by
  refine ⟨?_, (Real.hasDerivAt_sin φ).const_mul _⟩
  convert (Real.hasDerivAt_cos φ).const_mul (R + r * Real.cos θ) using 1; ring

/-- Primeira forma fundamental: `E = r²`, `F = 0`, `G = (R + r cos θ)²`. -/
theorem metrica (R r θ φ : ℝ) :
    (-r * Real.sin θ * Real.cos φ) ^ 2 + (-r * Real.sin θ * Real.sin φ) ^ 2 + (r * Real.cos θ) ^ 2 = r ^ 2 ∧
    (-r * Real.sin θ * Real.cos φ) * (-(R + r * Real.cos θ) * Real.sin φ) +
      (-r * Real.sin θ * Real.sin φ) * ((R + r * Real.cos θ) * Real.cos φ) + r * Real.cos θ * 0 = 0 ∧
    (-(R + r * Real.cos θ) * Real.sin φ) ^ 2 + ((R + r * Real.cos θ) * Real.cos φ) ^ 2 + 0 ^ 2 =
      (R + r * Real.cos θ) ^ 2 := by
  have a := Real.cos_sq_add_sin_sq θ
  have b := Real.cos_sq_add_sin_sq φ
  refine ⟨?_, by ring, ?_⟩
  · linear_combination r ^ 2 * (Real.sin θ) ^ 2 * b + r ^ 2 * a
  · linear_combination (R + r * Real.cos θ) ^ 2 * b

/-- Curvatura de Gauss do toro. -/
noncomputable def Kg (R r θ : ℝ) : ℝ := Real.cos θ / (r * (R + r * Real.cos θ))

/-- **Brioschi** (métrica ortogonal `E dθ² + G dφ²`, `E = r²`): `K = −(1/√(EG)) ∂θ(∂θ√G / √E)`,
com `√G = R + r cos θ`: `∂θ√G = −r sin θ`, `∂θ(−sin θ) = −cos θ`. -/
theorem curvatura_brioschi {R r : ℝ} (hr : 0 < r) (hRr : r < R) (θ : ℝ) :
    HasDerivAt (fun θ => R + r * Real.cos θ) (-r * Real.sin θ) θ ∧
    HasDerivAt (fun θ => (-r * Real.sin θ) / r) (-Real.cos θ) θ ∧
    Kg R r θ = -(1 / (r * (R + r * Real.cos θ))) * (-Real.cos θ) := by
  refine ⟨?_, ?_, ?_⟩
  · convert ((Real.hasDerivAt_cos θ).const_mul r).const_add R using 1; ring
  · have : (fun θ => (-r * Real.sin θ) / r) = fun θ => -Real.sin θ := by
      funext θ; field_simp
    rw [this]
    exact (Real.hasDerivAt_sin θ).neg
  · unfold Kg
    have := raio_pos hr.le hRr θ
    field_simp

/-- Na linha crítica (`θ = π`) a curvatura é mínima e negativa: `K = −1/(r(R − r))`. -/
theorem curvatura_linha {R r : ℝ} (hr : 0 < r) (hRr : r < R) :
    Kg R r Real.pi = -1 / (r * (R - r)) ∧ Kg R r Real.pi < 0 ∧ Kg R r 0 = 1 / (r * (R + r)) := by
  unfold Kg
  rw [Real.cos_pi, Real.cos_zero]
  have h1 : 0 < R - r := by linarith
  refine ⟨by ring_nf, ?_, by ring_nf⟩
  rw [show R + r * -1 = R - r by ring]
  apply div_neg_of_neg_of_pos (by norm_num)
  positivity

/-- `K ≥ −1/(r(R − r))` em todo o toro: a linha crítica realiza o mínimo. -/
theorem curvatura_minima {R r : ℝ} (hr : 0 < r) (hRr : r < R) (θ : ℝ) :
    -1 / (r * (R - r)) ≤ Kg R r θ := by
  unfold Kg
  have hp := raio_pos hr.le hRr θ
  have h1 : 0 < R - r := by linarith
  have hc := Real.neg_one_le_cos θ
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hR : 0 < R := by linarith
  nlinarith [mul_nonneg (by linarith : 0 ≤ Real.cos θ + 1) (mul_pos hr hR).le]

/-- A região de curvatura negativa é exatamente a faixa central `¼ < σ < ¾`. -/
theorem curvatura_negativa_iff {R r : ℝ} (hr : 0 < r) (hRr : r < R) {σ : ℝ} (h0 : 0 ≤ σ)
    (h1 : σ ≤ 1) : Kg R r (2 * Real.pi * σ) < 0 ↔ 1 / 4 < σ ∧ σ < 3 / 4 := by
  unfold Kg
  have hp := raio_pos hr.le hRr (2 * Real.pi * σ)
  have hden : 0 < r * (R + r * Real.cos (2 * Real.pi * σ)) := by positivity
  rw [div_neg_iff]
  have hpi := Real.pi_pos
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · linarith
    · by_contra hn
      rcases not_and_or.mp hn with hσ | hσ
      · push Not at hσ
        have : 0 ≤ Real.cos (2 * Real.pi * σ) :=
          Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
        linarith
      · push Not at hσ
        have e : Real.cos (2 * Real.pi * σ) = Real.cos (2 * Real.pi - 2 * Real.pi * σ) := by
          rw [Real.cos_two_pi_sub]
        have : 0 ≤ Real.cos (2 * Real.pi - 2 * Real.pi * σ) :=
          Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
        linarith
  · rintro ⟨a, b⟩
    right
    exact ⟨Real.cos_neg_of_pi_div_two_lt_of_lt (by nlinarith) (by nlinarith), hden⟩

/-- Área: `∫₀^{2π}∫₀^{2π} r(R + r cos θ) dθ dφ = 4π²Rr`. -/
theorem area_toro (R r : ℝ) :
    ∫ _φ in (0 : ℝ)..2 * Real.pi, ∫ θ in (0 : ℝ)..2 * Real.pi, r * (R + r * Real.cos θ) =
      4 * Real.pi ^ 2 * R * r := by
  have inner : ∫ θ in (0 : ℝ)..2 * Real.pi, r * (R + r * Real.cos θ) = 2 * Real.pi * r * R := by
    have : (fun θ => r * (R + r * Real.cos θ)) = fun θ => r * R + r ^ 2 * Real.cos θ := by
      funext θ; ring
    rw [this, intervalIntegral.integral_add intervalIntegrable_const
      (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_cos]
    simp
    ring
  rw [inner, intervalIntegral.integral_const]
  simp
  ring

/-- **Gauss–Bonnet** (`χ(𝕋²) = 0`): `∫∫ K dA = ∫∫ cos θ dθ dφ = 0`. -/
theorem curvatura_total {R r : ℝ} (hr : 0 < r) (hRr : r < R) :
    ∫ _φ in (0 : ℝ)..2 * Real.pi, ∫ θ in (0 : ℝ)..2 * Real.pi,
      Kg R r θ * (r * (R + r * Real.cos θ)) = 0 := by
  have : (fun θ => Kg R r θ * (r * (R + r * Real.cos θ))) = Real.cos := by
    funext θ
    unfold Kg
    exact div_mul_cancel₀ _ (mul_ne_zero hr.ne' (raio_pos hr.le hRr θ).ne')
  rw [this, integral_cos]
  simp

/-! ## 2. Fluxos -/

/-- Fluxo de cruzamento `Φ_λ(s) = s + λ`. -/
def Φ (l : ℝ) (s : ℂ) : ℂ := s + l

theorem Φ_grupo (l m : ℝ) (s : ℂ) : Φ (l + m) s = Φ l (Φ m s) := by
  unfold Φ; push_cast; ring

theorem Φ_zero (s : ℂ) : Φ 0 s = s := by simp [Φ]

/-- Os zeros de `G_λ` são as órbitas `Φ_{±λ}` dos zeros críticos `½ ± iγ`. -/
theorem zeros_sao_orbitas (l g : ℝ) (s : ℂ) :
    G l g s = 0 ↔ (s = Φ l (1 / 2 + g * I) ∨ s = Φ l (1 / 2 - g * I) ∨
      s = Φ (-l) (1 / 2 + g * I) ∨ s = Φ (-l) (1 / 2 - g * I)) := by
  rw [G_zeros]
  unfold Φ
  push_cast
  constructor <;> rintro (h | h | h | h) <;> [left; (right; left); (right; right; left);
    (right; right; right); left; (right; left); (right; right; left); (right; right; right)] <;>
    rw [h] <;> ring

/-- No toro, o fluxo atravessa o equador interno **transversalmente**: a velocidade vertical em
`σ = ½` é `−2πr ≠ 0`. -/
theorem fluxo_transversal (R r T t : ℝ) :
    HasDerivAt (fun l : ℝ => (tor R r T (Φ l ((1 / 2 : ℂ) + t * I))).2.2) (-(2 * Real.pi * r)) 0 := by
  unfold tor Φ
  simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero]
  have h1 : HasDerivAt (fun l : ℝ => 2 * Real.pi * ((1 / 2 : ℂ).re + l)) (2 * Real.pi) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add ((1 / 2 : ℂ).re)).const_mul (2 * Real.pi)
    simpa using this
  have := (h1.sin).const_mul r
  convert this using 1
  have : (2 : ℝ) * Real.pi * ((1 / 2 : ℂ).re + 0) = Real.pi := by simp; ring
  rw [this, Real.cos_pi]
  ring

/-- Conjugado pela troca `T`, o fluxo horizontal vira translação vertical. -/
theorem troca_fluxo (l : ℝ) (w : ℂ) : troca (Φ l (troca w)) = w + l * I := by
  unfold troca Φ
  simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_conj]
  ring_nf
  rw [I_sq]
  ring

/-! ## 3. Tempos verbais -/

/-- Tempo verbal de uma afirmação. -/
inductive Tempo
  /-- *foi provado* -/
  | perfeito
  /-- *foi refutado* -/
  | negado
  /-- *seria verdadeiro, se a hipótese valesse* -/
  | condicional
  /-- *será decidido* (aberto) -/
  | futuro
  /-- *é observado numericamente* (sem prova no kernel) -/
  | presente
  deriving DecidableEq, Repr

/-- O que cada tempo exige como testemunha. -/
def Exige : Tempo → Prop → Prop → Prop
  | .perfeito, p, _ => p
  | .negado, p, _ => ¬ p
  | .condicional, p, h => h → p
  | .futuro, _, _ => True
  | .presente, _, _ => True

/-- Uma afirmação tipada: enunciado, tempo, hipótese e a testemunha que o tempo exige. -/
structure Afirmacao where
  enunciado : Prop
  tempo : Tempo
  hipotese : Prop := True
  testemunha : Exige tempo enunciado hipotese

/-- Uma afirmação no **perfeito** é verdadeira (o tipo obriga a prova). -/
theorem perfeito_verdadeiro (a : Afirmacao) (h : a.tempo = .perfeito) : a.enunciado := by
  have := a.testemunha; rw [h] at this; exact this

theorem negado_falso (a : Afirmacao) (h : a.tempo = .negado) : ¬ a.enunciado := by
  have := a.testemunha; rw [h] at this; exact this

/-- O **futuro** não transporta informação: `P` e `¬P` cabem no mesmo tempo. -/
theorem futuro_vazio (P : Prop) :
    ∃ a b : Afirmacao, a.enunciado = P ∧ b.enunciado = ¬ P ∧ a.tempo = .futuro ∧ b.tempo = .futuro :=
  ⟨⟨P, .futuro, True, trivial⟩, ⟨¬ P, .futuro, True, trivial⟩, rfl, rfl, rfl, rfl⟩

/-- Catálogo: a classificação **foi provada**. -/
def a_classificacao : Afirmacao :=
  ⟨∀ (F : ℂ → ℂ) (s : ℂ), Critico F s ∨ Externo F s ∨ NaoZeroC F s ∨ NaoZeroE F s, .perfeito, True,
    classificacao⟩

/-- "A simetria força a linha" **foi refutado**. -/
def a_simetria : Afirmacao :=
  ⟨∀ F : ℂ → ℂ, (∀ s, F (1 - s) = F s) → (∀ s, F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (F s)) →
      ∀ s, F s = 0 → s.re = 1 / 2, .negado, True, by
    intro h
    obtain ⟨F, h1, h2, s, hs, hne⟩ := (simetria_compativel_com_ambos (γ := 1) one_ne_zero).2
    exact hne (h F h1 h2 s hs)⟩

/-- "HR ⟺ não há zeros externos" **foi provado**. -/
def a_rh_externa : Afirmacao := ⟨RiemannHypothesis ↔ ZE = ∅, .perfeito, True, rh_iff_externa_vazia⟩

/-- "Os zeros caem no equador interno do toro" **seria** verdadeiro **se** HR valesse. -/
def a_toro_condicional : Afirmacao :=
  ⟨∀ ρ ∈ Z, (tor 2 1 1 ρ).2.2 = 0, .condicional, RiemannHypothesis,
    fun h => (rh_iff_equador (R := 2) (r := 1) (T := 1) one_ne_zero).mp h⟩

/-- HR **será** decidida (aberta). -/
def a_rh : Afirmacao := ⟨RiemannHypothesis, .futuro, True, trivial⟩

/-! ## 4. Modelo `H_{d,γ}` com zeros triviais -/

/-- `q_a(s) = (s − a)² + γ²`. -/
noncomputable def q (a γ : ℝ) (s : ℂ) : ℂ := (s - a) ^ 2 + (γ : ℂ) ^ 2

theorem q_fatora (a γ : ℝ) (s : ℂ) : q a γ s = (s - (a + γ * I)) * (s - (a - γ * I)) := by
  unfold q; ring_nf; rw [I_sq]; ring

/-- `H_{d,γ}(s) = q_{½} q_{½+d} q_{½−d} / Γ(1 + s/2)` (inteira). -/
noncomputable def H (d γ : ℝ) (s : ℂ) : ℂ :=
  q (1 / 2) γ s * q (1 / 2 + d) γ s * q (1 / 2 - d) γ s * (Complex.Gamma (1 + s / 2))⁻¹

theorem gInv_diff : Differentiable ℂ (fun s : ℂ => (Complex.Gamma (1 + s / 2))⁻¹) := by
  have h1 : Differentiable ℂ (fun s : ℂ => 1 + s / 2) := by fun_prop
  exact Complex.differentiable_one_div_Gamma.comp h1

theorem H_inteira (d γ : ℝ) : Differentiable ℂ (H d γ) := by
  have hg := gInv_diff
  unfold H q
  fun_prop

/-- **Zeros triviais** `−2, −4, −6, …`. -/
theorem H_trivial (d γ : ℝ) (n : ℕ) : H d γ (-2 * ((n : ℂ) + 1)) = 0 := by
  unfold H
  have : (1 : ℂ) + -2 * ((n : ℂ) + 1) / 2 = -(n : ℂ) := by ring
  rw [this, Complex.Gamma_neg_nat_eq_zero, inv_zero, mul_zero]

theorem q_zero_iff (a γ : ℝ) (s : ℂ) : q a γ s = 0 ↔ s = a + γ * I ∨ s = a - γ * I := by
  rw [q_fatora, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- **Todos os zeros de `H`**: triviais, críticos `½ ± iγ` e externos `½ ± d ± iγ`. -/
theorem H_zero_iff (d γ : ℝ) (s : ℂ) :
    H d γ s = 0 ↔ (s = 1 / 2 + γ * I ∨ s = 1 / 2 - γ * I) ∨
      (s = 1 / 2 + d + γ * I ∨ s = 1 / 2 + d - γ * I) ∨
      (s = 1 / 2 - d + γ * I ∨ s = 1 / 2 - d - γ * I) ∨ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
  unfold H
  rw [mul_eq_zero, mul_eq_zero, mul_eq_zero, inv_eq_zero, Complex.Gamma_eq_zero_iff,
    q_zero_iff, q_zero_iff, q_zero_iff]
  push_cast
  have e : ∀ m : ℕ, (1 + s / 2 = -(m : ℂ) ↔ s = -2 * ((m : ℂ) + 1)) := by
    intro m; constructor
    · intro h; linear_combination 2 * h
    · intro h; linear_combination (1 / 2 : ℂ) * h
  simp only [e]
  tauto

/-- Valor exato: `H_{¼,1}(½) = 289/(256 Γ(5/4)) ≠ 0` (não zero na linha). -/
theorem H_meio : H (1 / 4) 1 (1 / 2) = 289 / 256 * (Complex.Gamma (5 / 4))⁻¹ ∧
    H (1 / 4) 1 (1 / 2) ≠ 0 := by
  have e : H (1 / 4) 1 (1 / 2) = 289 / 256 * (Complex.Gamma (5 / 4))⁻¹ := by
    unfold H q
    push_cast
    rw [show (1 : ℂ) + 1 / 2 / 2 = 5 / 4 by norm_num]
    ring
  refine ⟨e, ?_⟩
  rw [e]
  apply mul_ne_zero (by norm_num)
  apply inv_ne_zero
  apply Complex.Gamma_ne_zero_of_re_pos
  norm_num

/-- Os zeros triviais **não** são preservados pela reflexão: `R(−2) = 3` e `H(3) ≠ 0`. -/
theorem reflexao_nao_preserva_triviais (d : ℝ) {γ : ℝ} (hγ : γ ≠ 0) :
    H d γ (-2) = 0 ∧ torcao (-2) = 3 ∧ H d γ 3 ≠ 0 := by
  refine ⟨by simpa using H_trivial d γ 0, by simp only [torcao, map_neg, map_ofNat]; norm_num, ?_⟩
  unfold H
  have hq : ∀ a : ℝ, q a γ 3 ≠ 0 := by
    intro a
    unfold q
    have : (3 : ℂ) - a = ((3 - a : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact fator_real_ne hγ
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (hq _) (hq _)) (hq _)) (inv_ne_zero ?_)
  apply Complex.Gamma_ne_zero_of_re_pos
  norm_num

/-- `1/Γ(1 + s/2)` é analítica e não se anula em `½ ± iγ`. -/
theorem gInv_analytic (z : ℂ) : AnalyticAt ℂ (fun s : ℂ => (Complex.Gamma (1 + s / 2))⁻¹) z :=
  gInv_diff.analyticAt z

theorem gInv_ne (γ : ℝ) : (Complex.Gamma (1 + (1 / 2 + γ * I) / 2))⁻¹ ≠ 0 := by
  apply inv_ne_zero
  apply Complex.Gamma_ne_zero_of_re_pos
  simp; norm_num

/-- **Ordem 3 no encontro** (`d = 0`). -/
theorem H_ordem_tres {γ : ℝ} (hγ : γ ≠ 0) : analyticOrderAt (H 0 γ) (1 / 2 + γ * I) = 3 := by
  have hA : AnalyticAt ℂ (H 0 γ) (1 / 2 + γ * I) := (H_inteira 0 γ).analyticAt _
  have e3 : (3 : ℕ∞) = ((3 : ℕ) : ℕ∞) := by norm_num
  rw [e3, hA.analyticOrderAt_eq_natCast]
  refine ⟨fun s => (s - (1 / 2 - γ * I)) ^ 3 * (Complex.Gamma (1 + s / 2))⁻¹, ?_, ?_, ?_⟩
  · exact (by fun_prop : AnalyticAt ℂ (fun s : ℂ => (s - (1 / 2 - γ * I)) ^ 3) _).mul
      (gInv_analytic _)
  · apply mul_ne_zero _ (gInv_ne γ)
    apply pow_ne_zero
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hγ (by linarith)
  · refine Eventually.of_forall fun s => ?_
    simp only [smul_eq_mul, H]
    rw [q_fatora, q_fatora, q_fatora]
    push_cast
    ring

/-- Fora do encontro (`d ≠ 0`), `½ + iγ` é **simples**. -/
theorem H_ordem_um {d γ : ℝ} (hd : d ≠ 0) (hγ : γ ≠ 0) :
    analyticOrderAt (H d γ) (1 / 2 + γ * I) = 1 := by
  have hA : AnalyticAt ℂ (H d γ) (1 / 2 + γ * I) := (H_inteira d γ).analyticAt _
  have e1 : (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) := by norm_num
  rw [e1, hA.analyticOrderAt_eq_natCast]
  refine ⟨fun s => (s - (1 / 2 - γ * I)) * q (1 / 2 + d) γ s * q (1 / 2 - d) γ s *
      (Complex.Gamma (1 + s / 2))⁻¹, ?_, ?_, ?_⟩
  · unfold q
    exact (by fun_prop : AnalyticAt ℂ (fun s : ℂ => (s - (1 / 2 - γ * I)) *
      ((s - ((1 / 2 + d : ℝ) : ℂ)) ^ 2 + (γ : ℂ) ^ 2) *
      ((s - ((1 / 2 - d : ℝ) : ℂ)) ^ 2 + (γ : ℂ) ^ 2)) _).mul (gInv_analytic _)
  · refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) (gInv_ne γ)
    · intro h
      have := congrArg Complex.im h
      simp at this
      exact hγ (by linarith)
    · have e : q (1 / 2 + d) γ (1 / 2 + γ * I) = ((d ^ 2 : ℝ) : ℂ) - 2 * d * γ * I := by
        unfold q; push_cast; linear_combination (γ : ℂ) ^ 2 * I_sq
      rw [e]
      intro h
      have := congrArg Complex.re h
      simp at this
      exact hd (by simpa [sq] using this)
    · have e : q (1 / 2 - d) γ (1 / 2 + γ * I) = ((d ^ 2 : ℝ) : ℂ) + 2 * d * γ * I := by
        unfold q; push_cast; linear_combination (γ : ℂ) ^ 2 * I_sq
      rw [e]
      intro h
      have := congrArg Complex.re h
      simp at this
      exact hd (by simpa [sq] using this)
  · refine Eventually.of_forall fun s => ?_
    simp only [smul_eq_mul, H, pow_one]
    rw [q_fatora (1 / 2)]
    push_cast
    ring

/-! ### Princípio do argumento para multiconjuntos -/

theorem hasDerivAt_prod_lin (A : Multiset ℂ) {z : ℂ} (hz : ∀ a ∈ A, z ≠ a) :
    HasDerivAt (fun w => (A.map (fun a => w - a)).prod)
      ((A.map (fun a => z - a)).prod * (A.map (fun a => (z - a)⁻¹)).sum) z := by
  induction A using Multiset.induction_on with
  | empty => simpa using hasDerivAt_const z (1 : ℂ)
  | cons a A ih =>
    have ha : z - a ≠ 0 := sub_ne_zero.mpr (hz a (Multiset.mem_cons_self a A))
    have ih' := ih (fun b hb => hz b (Multiset.mem_cons_of_mem hb))
    have h1 := ((hasDerivAt_id z).sub_const a).mul ih'
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    convert h1 using 1
    · funext w; simp
    · simp only [id]
      field_simp
      try ring

theorem integral_soma_inv (A : Multiset ℂ) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hA : ∀ a ∈ A, a ∈ Metric.ball c R) :
    ∮ z in C(c, R), (A.map (fun a => (z - a)⁻¹)).sum = 2 * Real.pi * I * Multiset.card A := by
  induction A using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | cons a A ih =>
    have ha := hA a (Multiset.mem_cons_self a A)
    have ih' := ih (fun b hb => hA b (Multiset.mem_cons_of_mem hb))
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have i1 : CircleIntegrable (fun z => (z - a)⁻¹) c R :=
      circleIntegrable_sub_inv_iff.mpr (Or.inr (by
        intro h
        rw [Metric.mem_sphere, abs_of_pos hR] at h
        rw [Metric.mem_ball] at ha
        linarith))
    have i2 : CircleIntegrable (fun z => (A.map (fun a => (z - a)⁻¹)).sum) c R := by
      apply ContinuousOn.circleIntegrable hR.le
      apply continuousOn_multiset_sum
      intro b hb
      apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
      intro z hz h
      have h' : z = b := sub_eq_zero.mp (by simpa using h)
      subst h'
      have hb' := hA z (Multiset.mem_cons_of_mem hb)
      rw [Metric.mem_sphere] at hz
      rw [Metric.mem_ball] at hb'
      linarith
    rw [circleIntegral.integral_add i1 i2, circleIntegral.integral_sub_inv_of_mem_ball ha, ih']
    push_cast
    ring

/-- **Princípio do argumento** para `f = (∏_{a∈A} (z − a)) · g`, `g` holomorfa sem zeros no disco:
`∮ f'/f = 2πi · #A` (com multiplicidade). -/
theorem argumento_multiconjunto {g : ℂ → ℂ} {c : ℂ} {R R' : ℝ} (A : Multiset ℂ) (hR : 0 < R)
    (hRR : R < R') (hg : DifferentiableOn ℂ g (Metric.ball c R'))
    (hg0 : ∀ z ∈ Metric.closedBall c R, g z ≠ 0) (hA : ∀ a ∈ A, a ∈ Metric.ball c R) :
    ∮ z in C(c, R), deriv (fun w => (A.map (fun a => w - a)).prod * g w) z /
        ((A.map (fun a => z - a)).prod * g z) = 2 * Real.pi * I * Multiset.card A := by
  have hsub : Metric.closedBall c R ⊆ Metric.ball c R' := Metric.closedBall_subset_ball hRR
  have hdg : DifferentiableOn ℂ (deriv g) (Metric.ball c R') := hg.deriv Metric.isOpen_ball
  have hEq : Set.EqOn (fun z => deriv (fun w => (A.map (fun a => w - a)).prod * g w) z /
        ((A.map (fun a => z - a)).prod * g z))
      (fun z => (A.map (fun a => (z - a)⁻¹)).sum + deriv g z / g z) (Metric.sphere c R) := by
    intro z hz
    have hzb : z ∈ Metric.closedBall c R := Metric.sphere_subset_closedBall hz
    have hza : ∀ a ∈ A, z ≠ a := by
      rintro a ha rfl
      have := hA z ha
      rw [Metric.mem_sphere] at hz
      rw [Metric.mem_ball] at this
      linarith
    have hgd : HasDerivAt g (deriv g z) z :=
      ((hg z (hsub hzb)).differentiableAt (Metric.isOpen_ball.mem_nhds (hsub hzb))).hasDerivAt
    have hd : HasDerivAt (fun w => (A.map (fun a => w - a)).prod * g w)
        ((A.map (fun a => z - a)).prod * (A.map (fun a => (z - a)⁻¹)).sum * g z +
          (A.map (fun a => z - a)).prod * deriv g z) z := (hasDerivAt_prod_lin A hza).mul hgd
    have hP : (A.map (fun a => z - a)).prod ≠ 0 := by
      apply Multiset.prod_ne_zero
      simp only [Multiset.mem_map, not_exists, not_and]
      intro a ha h
      exact hza a ha (sub_eq_zero.mp h)
    have hgz := hg0 z hzb
    simp only
    rw [hd.deriv]
    field_simp
    try ring
  rw [circleIntegral.integral_congr hR.le hEq]
  have hcont : ContinuousOn (fun z => deriv g z / g z) (Metric.closedBall c R) :=
    ContinuousOn.div (hdg.continuousOn.mono hsub) (hg.continuousOn.mono hsub) hg0
  have i2 : CircleIntegrable (fun z => deriv g z / g z) c R :=
    ContinuousOn.circleIntegrable hR.le (hcont.mono Metric.sphere_subset_closedBall)
  have i1 : CircleIntegrable (fun z => (A.map (fun a => (z - a)⁻¹)).sum) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    apply continuousOn_multiset_sum
    intro b hb
    apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
    intro z hz h
    have h' : z = b := sub_eq_zero.mp (by simpa using h)
    subst h'
    have hb' := hA z hb
    rw [Metric.mem_sphere] at hz
    rw [Metric.mem_ball] at hb'
    linarith
  rw [circleIntegral.integral_add i1 i2, integral_soma_inv A hR hA]
  have h0 : ∮ z in C(c, R), deriv g z / g z = 0 := by
    apply circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le Set.countable_empty hcont
    intro z hz
    have hzb : z ∈ Metric.ball c R' := hsub (Metric.ball_subset_closedBall hz.1)
    have hn := Metric.isOpen_ball.mem_nhds hzb
    exact ((hdg z hzb).differentiableAt hn).div ((hg z hzb).differentiableAt hn)
      (hg0 z (Metric.ball_subset_closedBall hz.1))
  rw [h0, add_zero]

/-- Raízes não triviais de `H_{d,γ}`. -/
noncomputable def raizesH (d γ : ℝ) : Multiset ℂ :=
  {1 / 2 + γ * I, 1 / 2 - γ * I, 1 / 2 + d + γ * I, 1 / 2 + d - γ * I, 1 / 2 - d + γ * I,
    1 / 2 - d - γ * I}

theorem H_prod (d γ : ℝ) :
    H d γ = fun s => ((raizesH d γ).map (fun a => s - a)).prod * (Complex.Gamma (1 + s / 2))⁻¹ := by
  funext s
  simp only [H, raizesH, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton]
  rw [q_fatora, q_fatora, q_fatora]
  push_cast
  ring

theorem Gamma_ne_bola {z : ℂ} (hz : z ∈ Metric.closedBall (1 / 2 : ℂ) 2) :
    (Complex.Gamma (1 + z / 2))⁻¹ ≠ 0 := by
  apply inv_ne_zero
  apply Complex.Gamma_ne_zero
  intro m hm
  have hz' : z = -2 - 2 * (m : ℂ) := by linear_combination 2 * hm
  rw [Metric.mem_closedBall, dist_eq_norm, hz'] at hz
  have hre := Complex.abs_re_le_norm (-2 - 2 * (m : ℂ) - 1 / 2)
  simp at hre
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  rw [abs_of_neg (by linarith)] at hre
  linarith

theorem norm_lt_dois {x y : ℝ} (h : x ^ 2 + y ^ 2 < 4) : ‖(x : ℂ) + y * I‖ < 2 := by
  have e : ‖(x : ℂ) + y * I‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  nlinarith [norm_nonneg ((x : ℂ) + y * I)]

/-- **Contagem conservada** `(1/2πi)∮_{|s−½|=2} H'/H = 6`, para `d = ¼` (seis zeros simples) e para
`d = 0` (dois zeros triplos). Os zeros triviais ficam fora (`|−2 − ½| = 5/2 > 2`). -/
theorem H_contagem (d : ℝ) (hd : d = 1 / 4 ∨ d = 0) :
    (2 * Real.pi * I)⁻¹ * ∮ z in C((1 / 2 : ℂ), 2), deriv (H d 1) z / H d 1 z = 6 := by
  have hA : ∀ a ∈ raizesH d 1, a ∈ Metric.ball (1 / 2 : ℂ) 2 := by
    have hd2 : d ^ 2 + 1 < 4 := by rcases hd with rfl | rfl <;> norm_num
    intro a ha
    simp only [raizesH, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at ha
    rw [Metric.mem_ball, dist_eq_norm]
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
    · have := norm_lt_dois (x := 0) (y := 1) (by norm_num); simpa using this
    · have := norm_lt_dois (x := 0) (y := -1) (by norm_num); simpa [sub_eq_add_neg] using this
    · have := norm_lt_dois (x := d) (y := 1) (by nlinarith)
      convert this using 2; push_cast; ring
    · have := norm_lt_dois (x := d) (y := -1) (by nlinarith)
      convert this using 2; push_cast; ring
    · have := norm_lt_dois (x := -d) (y := 1) (by nlinarith)
      convert this using 2; push_cast; ring
    · have := norm_lt_dois (x := -d) (y := -1) (by nlinarith)
      convert this using 2; push_cast; ring
  have hg : DifferentiableOn ℂ (fun s : ℂ => (Complex.Gamma (1 + s / 2))⁻¹)
      (Metric.ball (1 / 2 : ℂ) 3) := gInv_diff.differentiableOn
  have key := argumento_multiconjunto (raizesH d 1) (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) < 3) hg (fun z hz => Gamma_ne_bola hz) hA
  rw [H_prod]
  simp only at key ⊢
  rw [key]
  have : Multiset.card (raizesH d 1) = 6 := by simp [raizesH]
  rw [this]
  have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp
  push_cast
  ring

/-! ## 5. Pontes -/

/-- Transporte de zeros `G(φ s) = u(s) F(s)` (B06). -/
def TransporteZero (F G φ u : ℂ → ℂ) : Prop := ∀ s, G (φ s) = u s * F s

theorem transporte_zero {F G φ u : ℂ → ℂ} (h : TransporteZero F G φ u) {s : ℂ} (hz : F s = 0) :
    G (φ s) = 0 := by rw [h s, hz, mul_zero]

theorem transporte_zero_iff {F G φ u : ℂ → ℂ} (h : TransporteZero F G φ u) {s : ℂ}
    (hu : u s ≠ 0) : F s = 0 ↔ G (φ s) = 0 :=
  ⟨transporte_zero h, fun hz => by rw [h s] at hz; exact (mul_eq_zero.mp hz).resolve_left hu⟩

/-- Sem `u ≠ 0` a recíproca falha. -/
theorem transporte_falha :
    ∃ F G φ u : ℂ → ℂ, TransporteZero F G φ u ∧ G (φ 0) = 0 ∧ F 0 ≠ 0 :=
  ⟨fun _ => 1, fun z => z, id, fun z => z, fun s => by simp, rfl, one_ne_zero⟩

/-- **B17**: multiplicar por um fator analítico que não se anula preserva a ordem do zero. -/
theorem ordem_preservada {F u : ℂ → ℂ} {a : ℂ} (hF : AnalyticAt ℂ F a) (hu : AnalyticAt ℂ u a)
    (hua : u a ≠ 0) : analyticOrderAt (fun z => u z * F z) a = analyticOrderAt F a := by
  have := analyticOrderAt_mul hu hF
  rw [show (fun z => u z * F z) = u * F from rfl, this,
    (hu.analyticOrderAt_eq_zero).mpr hua, zero_add]

/-- **Singularidade removível**: `(z² − 1)/(z − 1)` estendida por `2` em `1` é `z + 1`, inteira. -/
theorem removivel :
    Function.update (fun z : ℂ => (z ^ 2 - 1) / (z - 1)) 1 2 = fun z => z + 1 := by
  funext z
  by_cases h : z = 1
  · subst h; simp; norm_num
  · rw [Function.update_of_ne h]
    have : z - 1 ≠ 0 := sub_ne_zero.mpr h
    field_simp
    ring

/-- `ξ(s) = s(s − 1)/2 · Λ(s)`. -/
noncomputable def xi (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta s

/-- Equação funcional `ξ(1 − s) = ξ(s)`. -/
theorem xi_um_menos (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi; rw [completedRiemannZeta_one_sub]; ring

/-- **B20**: na faixa (`Re s > 0`, `s ≠ 1`), `ξ(s) = 0 ⟺ ζ(s) = 0`. -/
theorem xi_zero_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s ≠ 1) : xi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at h0
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h0
  have hz : riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs0
  unfold xi
  have hc : s * (s - 1) / 2 ≠ 0 := by
    apply div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr h1)) two_ne_zero
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hc
    · rw [hz, h, zero_div]
  · intro h
    rw [hz, div_eq_zero_iff] at h
    rcases h with h | h
    · rw [h, mul_zero]
    · exact absurd h hG

end ATK.ClosedMath

-- Auditoria de axiomas (kernel): cada teorema deve depender só de propext, Classical.choice, Quot.sound.
#print axioms ATK.ClosedMath.raio_pos
#print axioms ATK.ClosedMath.tor_superficie
#print axioms ATK.ClosedMath.tor_periodo_re
#print axioms ATK.ClosedMath.tor_periodo_im
#print axioms ATK.ClosedMath.tor_R
#print axioms ATK.ClosedMath.tor_J
#print axioms ATK.ClosedMath.tor_S
#print axioms ATK.ClosedMath.tor_linha
#print axioms ATK.ClosedMath.sin_dois_pi_faixa
#print axioms ATK.ClosedMath.tor_plano_iff
#print axioms ATK.ClosedMath.tor_R_fixo_iff
#print axioms ATK.ClosedMath.rh_iff_equador
#print axioms ATK.ClosedMath.tor_S_fixo_iff
#print axioms ATK.ClosedMath.tor_dist_par
#print axioms ATK.ClosedMath.tor_reencontro
#print axioms ATK.ClosedMath.tor_elevado_injOn
#print axioms ATK.ClosedMath.dX_dθ
#print axioms ATK.ClosedMath.dX_dφ
#print axioms ATK.ClosedMath.metrica
#print axioms ATK.ClosedMath.curvatura_brioschi
#print axioms ATK.ClosedMath.curvatura_linha
#print axioms ATK.ClosedMath.curvatura_minima
#print axioms ATK.ClosedMath.curvatura_negativa_iff
#print axioms ATK.ClosedMath.area_toro
#print axioms ATK.ClosedMath.curvatura_total
#print axioms ATK.ClosedMath.Φ_grupo
#print axioms ATK.ClosedMath.Φ_zero
#print axioms ATK.ClosedMath.zeros_sao_orbitas
#print axioms ATK.ClosedMath.fluxo_transversal
#print axioms ATK.ClosedMath.troca_fluxo
#print axioms ATK.ClosedMath.perfeito_verdadeiro
#print axioms ATK.ClosedMath.negado_falso
#print axioms ATK.ClosedMath.futuro_vazio
#print axioms ATK.ClosedMath.q_fatora
#print axioms ATK.ClosedMath.gInv_diff
#print axioms ATK.ClosedMath.H_inteira
#print axioms ATK.ClosedMath.H_trivial
#print axioms ATK.ClosedMath.q_zero_iff
#print axioms ATK.ClosedMath.H_zero_iff
#print axioms ATK.ClosedMath.H_meio
#print axioms ATK.ClosedMath.reflexao_nao_preserva_triviais
#print axioms ATK.ClosedMath.gInv_analytic
#print axioms ATK.ClosedMath.gInv_ne
#print axioms ATK.ClosedMath.H_ordem_tres
#print axioms ATK.ClosedMath.H_ordem_um
#print axioms ATK.ClosedMath.hasDerivAt_prod_lin
#print axioms ATK.ClosedMath.integral_soma_inv
#print axioms ATK.ClosedMath.argumento_multiconjunto
#print axioms ATK.ClosedMath.H_prod
#print axioms ATK.ClosedMath.Gamma_ne_bola
#print axioms ATK.ClosedMath.norm_lt_dois
#print axioms ATK.ClosedMath.H_contagem
#print axioms ATK.ClosedMath.transporte_zero
#print axioms ATK.ClosedMath.transporte_zero_iff
#print axioms ATK.ClosedMath.transporte_falha
#print axioms ATK.ClosedMath.ordem_preservada
#print axioms ATK.ClosedMath.removivel
#print axioms ATK.ClosedMath.xi_um_menos
#print axioms ATK.ClosedMath.xi_zero_iff
