import ATK.ClosedMathGeometrias

/-!
# ATK — O laplaciano do toro plano: autofunções, espectro real e a ponte que falta

No toro plano `𝕋² = (ℝ/2πℤ)²`, as funções de Fourier `e_{m,n}(x, y) = e^{i(mx + ny)}` são
`2π`-periódicas e satisfazem `−Δ e_{m,n} = (m² + n²) e_{m,n}`: autovalores reais `≥ 0`
(`autofuncao_toro`). A autoadjunção abstrata entra pela ponte já provada `hilbert_polya`
(`ATK/ClosedMathGeometrias.lean`): **operador simétrico + cada zero não trivial como
`½ + iμ` com `μ` autovalor ⇒ HR**. O que falta é a correspondência espectral completa, que este
operador **não** tem: seus autovalores são inteiros, e `μ ∈ ℤ` forçaria `γ ∈ ℤ` para cada zero
(`espectro_inteiro_forca`), o que nada indica valer (γ₁ = 14,1347…).
-/

open Complex

namespace ATK.ClosedMath.EspectroToro

/-- Autofunção de Fourier do toro. -/
noncomputable def e (m n : ℤ) (x y : ℝ) : ℂ := Complex.exp (I * ((m : ℂ) * x + (n : ℂ) * y))

/-- Periodicidade `2π` nas duas variáveis. -/
theorem e_periodica (m n : ℤ) (x y : ℝ) :
    e m n (x + 2 * Real.pi) y = e m n x y ∧ e m n x (y + 2 * Real.pi) = e m n x y := by
  unfold e
  constructor
  · rw [show I * ((m : ℂ) * ((x + 2 * Real.pi : ℝ) : ℂ) + (n : ℂ) * y) =
        I * ((m : ℂ) * x + (n : ℂ) * y) + (m : ℂ) * (2 * Real.pi * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · rw [show I * ((m : ℂ) * x + (n : ℂ) * ((y + 2 * Real.pi : ℝ) : ℂ)) =
        I * ((m : ℂ) * x + (n : ℂ) * y) + (n : ℂ) * (2 * Real.pi * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Primeira derivada em `x`. -/
theorem dx (m n : ℤ) (x y : ℝ) :
    HasDerivAt (fun x => e m n x y) (I * m * e m n x y) x := by
  unfold e
  have h : HasDerivAt (fun x : ℝ => I * ((m : ℂ) * (x : ℂ) + (n : ℂ) * y)) (I * m) x := by
    have := (((hasDerivAt_id x).ofReal_comp).const_mul (m : ℂ)).add_const ((n : ℂ) * y) |>.const_mul I
    simpa using this
  convert h.cexp using 1
  ring

/-- Primeira derivada em `y`. -/
theorem dy (m n : ℤ) (x y : ℝ) :
    HasDerivAt (fun y => e m n x y) (I * n * e m n x y) y := by
  unfold e
  have h : HasDerivAt (fun y : ℝ => I * ((m : ℂ) * x + (n : ℂ) * (y : ℂ))) (I * n) y := by
    have := (((hasDerivAt_id y).ofReal_comp).const_mul (n : ℂ)).const_add ((m : ℂ) * x) |>.const_mul I
    simpa using this
  convert h.cexp using 1
  ring

/-- Segundas derivadas: `∂²ₓ e = −m² e` e `∂²_y e = −n² e`. -/
theorem d2 (m n : ℤ) (x y : ℝ) :
    HasDerivAt (fun x => I * m * e m n x y) (-(m : ℂ) ^ 2 * e m n x y) x ∧
      HasDerivAt (fun y => I * n * e m n x y) (-(n : ℂ) ^ 2 * e m n x y) y := by
  constructor
  · convert (dx m n x y).const_mul (I * m) using 1
    ring_nf; rw [I_sq]; ring
  · convert (dy m n x y).const_mul (I * n) using 1
    ring_nf; rw [I_sq]; ring

/-- **Autofunção do laplaciano**: `−Δ e_{m,n} = (m² + n²) e_{m,n}`, autovalor real `≥ 0`. -/
theorem autofuncao_toro (m n : ℤ) (x y : ℝ) :
    -((-(m : ℂ) ^ 2 * e m n x y) + (-(n : ℂ) ^ 2 * e m n x y)) =
      (((m : ℝ) ^ 2 + (n : ℝ) ^ 2 : ℝ) : ℂ) * e m n x y ∧ 0 ≤ (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by
  refine ⟨by push_cast; ring, by positivity⟩

/-- Se cada zero `ρ` fosse `½ + iμ` com `μ` inteiro (espectro deste laplaciano), então `Im ρ ∈ ℤ`
e `Re ρ = ½`: a correspondência com o toro plano exigiria ordenadas inteiras. -/
theorem espectro_inteiro_forca {ρ : ℂ} {k : ℤ} (h : ρ = 1 / 2 + I * k) :
    ρ.re = 1 / 2 ∧ ρ.im = k := by
  subst h
  simp

end ATK.ClosedMath.EspectroToro

-- Auditoria de axiomas (kernel)
#print axioms ATK.ClosedMath.EspectroToro.e_periodica
#print axioms ATK.ClosedMath.EspectroToro.dx
#print axioms ATK.ClosedMath.EspectroToro.dy
#print axioms ATK.ClosedMath.EspectroToro.d2
#print axioms ATK.ClosedMath.EspectroToro.autofuncao_toro
#print axioms ATK.ClosedMath.EspectroToro.espectro_inteiro_forca
