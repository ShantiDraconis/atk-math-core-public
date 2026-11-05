import ATK.RHTerminal

/-!
# ATK — Closed Math em hélices, parábolas, hipérboles, toros e a ponte espectral

* Parametrizações de `ℂ ⊇ S → ℝ³`: helicoide `(σ cos t, σ sin t, t)`, cilindro parabólico
  `(σ, t, σ²)`, paraboloide hiperbólico `(σ, t, σ² − t²)` e hiperboloide
  `(cosh t cos σ, cosh t sin σ, sinh t)` são **injetivas** (as duas primeiras globalmente ou em
  `σ > 0`, a última na faixa `0 < σ < 1`): o transporte `F̃(Φ s) = F s` é bem definido e preserva
  zeros, multiplicidades e classes.
* **A margem não muda com a geometria**: o conjunto dos valores `|F̃|` sobre `Φ(K)` é o mesmo de
  `|F|` sobre `K`, logo `inf_{Φ(K)} |F̃| = inf_K |F|` (`margem_invariante`).
* **O toro não admite transporte** de `G_{0,1}`: dois pontos com estados diferentes têm a mesma
  imagem (`toro_sem_transporte`); é preciso guardar o rótulo (toro elevado).
* **Ponte espectral (Hilbert–Pólya), condicional**: se todo zero não trivial for `½ + iμ` com `μ`
  autovalor de um operador simétrico, então HR (`hilbert_polya`). A hipótese é aberta: nenhum
  operador desses é conhecido. `μ = (ρ − ½)/i` é real ⟺ `Re ρ = ½` (`mu_real_iff`).
-/

open Complex Set

namespace ATK.ClosedMath.Geometrias

open ATK.ZetaSimetria ATK.CEZ ATK.ClosedMath

/-- Dois ângulos com mesmo cosseno e seno e diferença menor que `2π` são iguais. -/
theorem angulo_inj {a b : ℝ} (hab : |a - b| < 2 * Real.pi) (hc : Real.cos a = Real.cos b)
    (hs : Real.sin a = Real.sin b) : a = b := by
  have he : Complex.exp ((a : ℂ) * I) = Complex.exp ((b : ℂ) * I) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hn' := congrArg Complex.im hn
  simp at hn'
  have hpi := Real.pi_pos
  have hd : a - b = n * (2 * Real.pi) := by linarith
  rw [hd, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hab
  have h1 : |(n : ℝ)| < 1 := by
    by_contra hc'
    push Not at hc'
    nlinarith
  have hn0 : n = 0 := by
    have : |n| < 1 := by exact_mod_cast h1
    rw [abs_lt] at this
    omega
  rw [hn0] at hd
  simp at hd
  linarith

/-! ## Superfícies -/

/-- Helicoide. -/
noncomputable def helicoide (s : ℂ) : ℝ × ℝ × ℝ := (s.re * Real.cos s.im, s.re * Real.sin s.im, s.im)
/-- Cilindro parabólico. -/
def cilParabolico (s : ℂ) : ℝ × ℝ × ℝ := (s.re, s.im, s.re ^ 2)
/-- Paraboloide hiperbólico (sela). -/
def sela (s : ℂ) : ℝ × ℝ × ℝ := (s.re, s.im, s.re ^ 2 - s.im ^ 2)
/-- Hiperboloide de uma folha. -/
noncomputable def hiperboloide (s : ℂ) : ℝ × ℝ × ℝ :=
  (Real.cosh s.im * Real.cos s.re, Real.cosh s.im * Real.sin s.re, Real.sinh s.im)

/-- Na linha crítica, o helicoide desenha a hélice de raio `½`. -/
theorem helicoide_linha (t : ℝ) :
    helicoide ((1 / 2 : ℂ) + t * I) = (1 / 2 * Real.cos t, 1 / 2 * Real.sin t, t) := by
  simp [helicoide]

theorem helicoide_injOn : InjOn helicoide {s : ℂ | 0 < s.re} := by
  intro s hs w hw h
  simp only [helicoide, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [h3] at h1 h2
  have hc := Real.cos_sq_add_sin_sq w.im
  have e : s.re ^ 2 = w.re ^ 2 := by
    have : (s.re * Real.cos w.im) ^ 2 + (s.re * Real.sin w.im) ^ 2 =
        (w.re * Real.cos w.im) ^ 2 + (w.re * Real.sin w.im) ^ 2 := by rw [h1, h2]
    linear_combination this - (s.re ^ 2 - w.re ^ 2) * hc
  have hs' : (0 : ℝ) < s.re := hs
  have hw' : (0 : ℝ) < w.re := hw
  have : (s.re - w.re) * (s.re + w.re) = 0 := by linear_combination e
  rcases mul_eq_zero.mp this with h | h
  · exact Complex.ext (by linarith) h3
  · linarith

theorem cilParabolico_injetivo : Function.Injective cilParabolico := by
  intro s w h
  simp only [cilParabolico, Prod.mk.injEq] at h
  exact Complex.ext h.1 h.2.1

theorem sela_injetiva : Function.Injective sela := by
  intro s w h
  simp only [sela, Prod.mk.injEq] at h
  exact Complex.ext h.1 h.2.1

theorem hiperboloide_injOn : InjOn hiperboloide {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  intro s hs w hw h
  simp only [hiperboloide, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have ht : s.im = w.im := Real.sinh_injective h3
  rw [ht] at h1 h2
  have hpos := Real.cosh_pos w.im
  have hc : Real.cos s.re = Real.cos w.re := mul_left_cancel₀ hpos.ne' h1
  have hsn : Real.sin s.re = Real.sin w.re := mul_left_cancel₀ hpos.ne' h2
  have hab : |s.re - w.re| < 2 * Real.pi := by
    have := Real.pi_gt_three
    rw [abs_lt]; constructor <;> linarith [hs.1, hs.2, hw.1, hw.2]
  exact Complex.ext (angulo_inj hab hc hsn) ht

/-! ## Transporte e invariância da margem -/

/-- Transporte bem definido por uma parametrização injetiva: zeros ⟺ zeros. -/
theorem transporte_zero_superficie {α : Type*} {Φ : ℂ → α} {F : ℂ → ℂ} {Ft : α → ℂ} {K : Set ℂ}
    (h : ∀ s ∈ K, Ft (Φ s) = F s) {s : ℂ} (hs : s ∈ K) : Ft (Φ s) = 0 ↔ F s = 0 := by
  rw [h s hs]

/-- **A margem não muda com a geometria**: `|F̃|` sobre `Φ(K)` tem os mesmos valores de `|F|`
sobre `K`. -/
theorem margem_invariante {α : Type*} (Φ : ℂ → α) (F : ℂ → ℂ) (Ft : α → ℂ) (K : Set ℂ)
    (h : ∀ s ∈ K, Ft (Φ s) = F s) :
    (fun p => ‖Ft p‖) '' (Φ '' K) = (fun s => ‖F s‖) '' K := by
  rw [Set.image_image]
  exact Set.image_congr fun s hs => by simp only [h s hs]

theorem margem_invariante_inf {α : Type*} (Φ : ℂ → α) (F : ℂ → ℂ) (Ft : α → ℂ) (K : Set ℂ)
    (h : ∀ s ∈ K, Ft (Φ s) = F s) :
    sInf ((fun p => ‖Ft p‖) '' (Φ '' K)) = sInf ((fun s => ‖F s‖) '' K) := by
  rw [margem_invariante Φ F Ft K h]

/-- **O toro sobrepõe rótulos**: com `T = 1`, nenhuma `F̃` no toro reproduz `G_{0,1}`
(`½ + i` é zero, `½ + 2i` não é, e ambos têm a mesma imagem). -/
theorem toro_sem_transporte (R r : ℝ) :
    ¬ ∃ Ft : ℝ × ℝ × ℝ → ℂ, ∀ s : ℂ, Ft (tor R r 1 s) = G 0 1 s := by
  rintro ⟨Ft, hF⟩
  have z1 : G 0 1 (1 / 2 + I) = 0 := by simpa using (P2_critico 1).1
  have z2 : G 0 1 (1 / 2 + 2 * I) ≠ 0 := by
    rw [G_zero_quadrado]
    have : ((1 / 2 + 2 * I : ℂ) - 1 / 2) ^ 2 + ((1 : ℝ) : ℂ) ^ 2 = -3 := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [this]; norm_num
  have e : tor R r 1 (1 / 2 + 2 * I) = tor R r 1 (1 / 2 + I) := by
    have : (1 / 2 + 2 * I : ℂ) = (1 / 2 + I) + ((1 : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, tor_periodo_im R r one_ne_zero]
  apply z2
  rw [← hF, e, hF, z1]

/-! ## Ponte espectral (Hilbert–Pólya), condicional -/

/-- `μ = (ρ − ½)/i` é real ⟺ `Re ρ = ½`. -/
theorem mu_real_iff (ρ : ℂ) : ((ρ - 1 / 2) / I).im = 0 ↔ ρ.re = 1 / 2 := by
  rw [div_I]
  simp only [mul_im, sub_re, sub_im, neg_re, neg_im, I_re, I_im]
  norm_num
  constructor <;> intro h <;> linarith

/-- **Hilbert–Pólya (condicional)**: se todo zero não trivial `ρ` é `½ + iμ` com `μ` autovalor de
um operador simétrico num espaço com produto interno, então HR. A hipótese é aberta. -/
theorem hilbert_polya {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (h : ∀ ρ ∈ Z, ∃ μ : ℂ, Module.End.HasEigenvalue T μ ∧ ρ = 1 / 2 + I * μ) :
    RiemannHypothesis := by
  rw [rh_iff_externa_vazia]
  ext ρ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hρ, hne⟩
  obtain ⟨μ, hμ, rfl⟩ := h ρ hρ
  have hreal : (starRingEnd ℂ) μ = μ := hT.conj_eigenvalue_eq_self hμ
  have him : μ.im = 0 := Complex.conj_eq_iff_im.mp hreal
  apply hne
  simp [him]

end ATK.ClosedMath.Geometrias

-- Auditoria de axiomas (kernel)
#print axioms ATK.ClosedMath.Geometrias.angulo_inj
#print axioms ATK.ClosedMath.Geometrias.helicoide_linha
#print axioms ATK.ClosedMath.Geometrias.helicoide_injOn
#print axioms ATK.ClosedMath.Geometrias.cilParabolico_injetivo
#print axioms ATK.ClosedMath.Geometrias.sela_injetiva
#print axioms ATK.ClosedMath.Geometrias.hiperboloide_injOn
#print axioms ATK.ClosedMath.Geometrias.transporte_zero_superficie
#print axioms ATK.ClosedMath.Geometrias.margem_invariante
#print axioms ATK.ClosedMath.Geometrias.margem_invariante_inf
#print axioms ATK.ClosedMath.Geometrias.toro_sem_transporte
#print axioms ATK.ClosedMath.Geometrias.mu_real_iff
#print axioms ATK.ClosedMath.Geometrias.hilbert_polya
