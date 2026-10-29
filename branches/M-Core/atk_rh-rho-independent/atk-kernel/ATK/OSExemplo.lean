import ATK.OSTransferencia

/-!
# ATK — B7: teste de sanidade da reconstrução no tempo

Um exemplo explícito de dados de Osterwalder–Schrader (`exemplo m`): `V = ℂ²`, a forma
`B(f, g) = conj f₀ g₀ + conj f₁ g₁`, as translações `S(t) = diag(1, e^{−m t})` e o vácuo
`Ω = (1, 0)`. As hipóteses de `DadosOS` são satisfeitas (não são vácuas), as correlações conexas
decaem exatamente como `e^{−m t}`, e a cota de lacuna é **atingida**:

* `exemplo_lacuna`: `‖P(t) w‖ ≤ e^{−m t} ‖w‖` para todo `w ⊥ Ω` (de `lacuna_OS`);
* `exemplo_otimo`: para `w = ι(0, 1) ⊥ Ω`, `w ≠ 0` e `‖P(t) w‖ = e^{−m t} ‖w‖` — a taxa `m` não pode
  ser melhorada.

**CLOSED_MATH continua false.**
-/

open scoped ComplexConjugate InnerProductSpace

namespace ATK.OSExemplo

open ATK.OSTransferencia

/-- As translações `diag(1, e^{−m t})` em `ℂ²`. -/
noncomputable def Sx (m t : ℝ) : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun f := fun i => (if i = 0 then (1 : ℂ) else (Real.exp (-(m * t)) : ℂ)) * f i
  map_add' f g := by funext i; simp only [Pi.add_apply]; ring
  map_smul' c f := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem Sx_apply (m t : ℝ) (f : Fin 2 → ℂ) :
    Sx m t f = ![f 0, (Real.exp (-(m * t)) : ℂ) * f 1] := by
  funext i
  fin_cases i <;> simp [Sx]

theorem re_conj_mul_self (z : ℂ) : 0 ≤ (conj z * z).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg z.re, sq_nonneg z.im]

/-- **O exemplo**: dados OS em `ℂ²` com taxa `m ≥ 0`. -/
noncomputable def exemplo (m : ℝ) (hm : 0 ≤ m) : DadosOS (Fin 2 → ℂ) where
  B f g := conj (f 0) * g 0 + conj (f 1) * g 1
  conj_symm f g := by simp only [map_add, map_mul, Complex.conj_conj]; ring
  pos f := by
    rw [Complex.add_re]
    exact add_nonneg (re_conj_mul_self _) (re_conj_mul_self _)
  add_left f f' g := by simp only [Pi.add_apply, map_add]; ring
  smul_left c f g := by simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
  S := Sx m
  S_zero := by
    ext f i
    fin_cases i <;> simp [Sx]
  S_add s t _ _ := by
    refine LinearMap.ext fun f => funext fun i => ?_
    rw [LinearMap.comp_apply, Sx_apply, Sx_apply, Sx_apply]
    fin_cases i
    · simp
    · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 3
      ring
  S_symm t _ f g := by
    rw [Sx_apply, Sx_apply]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul,
      Complex.conj_ofReal]
    ring
  S_bdd f := by
    refine ⟨(conj (f 0) * f 0 + conj (f 1) * f 1).re, 0, fun t ht => ?_⟩
    rw [pow_zero, mul_one, Sx_apply]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, map_mul,
      Complex.conj_ofReal, Complex.add_re]
    have he : Real.exp (-(m * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have he0 : 0 ≤ Real.exp (-(m * t)) := (Real.exp_pos _).le
    have e1 : ((Real.exp (-(m * t)) : ℂ) * conj (f 1) * ((Real.exp (-(m * t)) : ℂ) * f 1)).re =
        Real.exp (-(m * t)) ^ 2 * (conj (f 1) * f 1).re := by
      rw [show (Real.exp (-(m * t)) : ℂ) * conj (f 1) * ((Real.exp (-(m * t)) : ℂ) * f 1) =
          ((Real.exp (-(m * t)) ^ 2 : ℝ) : ℂ) * (conj (f 1) * f 1) by push_cast; ring,
        Complex.re_ofReal_mul]
    rw [e1]
    have h1 := re_conj_mul_self (f 1)
    have h2 : Real.exp (-(m * t)) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  Ω := ![1, 0]
  S_Ω t _ := by
    rw [Sx_apply]
    funext i
    fin_cases i <;> simp
  B_ΩΩ := by simp

variable {m : ℝ} (hm : 0 ≤ m)

theorem exemplo_clu (f : Fin 2 → ℂ) : ∃ C, ∀ t, 0 ≤ t →
    ‖(exemplo m hm).B f ((exemplo m hm).S t f) -
      (exemplo m hm).B f (exemplo m hm).Ω * (exemplo m hm).B (exemplo m hm).Ω f‖ ≤
      C * Real.exp (-(m * t)) := by
  refine ⟨‖conj (f 1) * f 1‖, fun t _ => le_of_eq ?_⟩
  show ‖conj (f 0) * (Sx m t f) 0 + conj (f 1) * (Sx m t f) 1 -
      (conj (f 0) * (![1, 0] : Fin 2 → ℂ) 0 + conj (f 1) * (![1, 0] : Fin 2 → ℂ) 1) *
        (conj ((![1, 0] : Fin 2 → ℂ) 0) * f 0 + conj ((![1, 0] : Fin 2 → ℂ) 1) * f 1)‖ = _
  rw [Sx_apply]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    map_one, map_zero, mul_one, mul_zero, add_zero, one_mul, zero_mul]
  have e : conj (f 0) * f 0 + conj (f 1) * ((Real.exp (-(m * t)) : ℂ) * f 1) -
      conj (f 0) * f 0 = (Real.exp (-(m * t)) : ℂ) * (conj (f 1) * f 1) := by ring
  rw [e, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]

/-- **A lacuna do exemplo** (de `lacuna_OS`). -/
theorem exemplo_lacuna (w : (exemplo m hm).Hil)
    (hw : ⟪(exemplo m hm).ι (exemplo m hm).Ω, w⟫_ℂ = 0) (t : ℝ) (ht : 0 ≤ t) :
    ‖(exemplo m hm).P t w‖ ≤ Real.exp (-(m * t)) * ‖w‖ :=
  (exemplo m hm).lacuna_OS (exemplo_clu hm) w hw t ht

/-- **A cota é atingida**: `w = ι(0, 1)` é ortogonal ao vácuo, não nulo, e
`‖P(t) w‖ = e^{−m t} ‖w‖`. -/
theorem norm_ι_sq (g : Fin 2 → ℂ) :
    ‖(exemplo m hm).ι g‖ ^ 2 = (conj (g 0) * g 0 + conj (g 1) * g 1).re :=
  (norm_sq_eq_re_inner (𝕜 := ℂ) ((exemplo m hm).ι g)).trans (by rw [DadosOS.inner_ι]; rfl)

/-- **A cota é atingida**: `w = ι(0, 1)` é ortogonal ao vácuo, não nulo, e
`‖P(t) w‖ = e^{−m t} ‖w‖`. -/
theorem exemplo_otimo (t : ℝ) (ht : 0 ≤ t) :
    ⟪(exemplo m hm).ι (exemplo m hm).Ω, (exemplo m hm).ι ![0, 1]⟫_ℂ = 0 ∧
      (exemplo m hm).ι ![0, 1] ≠ 0 ∧
      ‖(exemplo m hm).P t ((exemplo m hm).ι ![0, 1])‖ =
        Real.exp (-(m * t)) * ‖(exemplo m hm).ι ![0, 1]‖ := by
  set D := exemplo m hm with hD
  have hn2 : ‖D.ι ![0, 1]‖ ^ 2 = 1 := by
    rw [hD, norm_ι_sq]
    simp
  have hn : ‖D.ι ![0, 1]‖ = 1 := by
    have h0 := norm_nonneg (D.ι ![0, 1])
    nlinarith [sq_nonneg (‖D.ι ![0, 1]‖ - 1)]
  refine ⟨?_, ?_, ?_⟩
  · rw [DadosOS.inner_ι]
    show conj ((![1, 0] : Fin 2 → ℂ) 0) * (![0, 1] : Fin 2 → ℂ) 0 +
      conj ((![1, 0] : Fin 2 → ℂ) 1) * (![0, 1] : Fin 2 → ℂ) 1 = 0
    simp
  · intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  · rw [DadosOS.P_ι D ht, hn, mul_one]
    have hS : D.S t ![0, 1] = ![0, (Real.exp (-(m * t)) : ℂ)] := by
      show Sx m t ![0, 1] = _
      rw [Sx_apply]
      funext i
      fin_cases i <;> simp
    rw [hS]
    have h2 : ‖D.ι ![0, (Real.exp (-(m * t)) : ℂ)]‖ ^ 2 = Real.exp (-(m * t)) ^ 2 := by
      rw [hD, norm_ι_sq]
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, map_zero, mul_zero,
        zero_add, Complex.conj_ofReal]
      rw [← Complex.ofReal_mul, Complex.ofReal_re, sq]
    exact (pow_left_inj₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).mp h2

end ATK.OSExemplo

#print axioms ATK.OSExemplo.Sx_apply
#print axioms ATK.OSExemplo.re_conj_mul_self
#print axioms ATK.OSExemplo.exemplo_clu
#print axioms ATK.OSExemplo.exemplo_lacuna
#print axioms ATK.OSExemplo.norm_ι_sq
#print axioms ATK.OSExemplo.exemplo_otimo
