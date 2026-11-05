import ATK.EspectroToro

/-!
# ATK — Hexagrama, grafo completo `K₆` e energia horizontal

* Hexagrama: `V_k = R e^{ikπ/3}`; vértices opostos `V_{k+3} = −V_k`, três eixos pelo centro,
  `Σ V_k = 0`; pentagrama: `Σ ζ^k = 0` para `ζ = e^{2πi/5}`.
* `K₆`: `15 = C(6,2)` arestas, `20` triângulos, `15` quadriláteros, `3` retângulos (pares de
  diâmetros). Adjacência `A = J − I`: `A·1 = 5·1` e `A v = −v` se `Σ v = 0`; laplaciano
  `L = 5I − A`: `L·1 = 0`, `L v = 6 v` se `Σ v = 0`.
* Energia: `E = ½ Σ_{i,j} |z_i − z_j|² = 6 Σ_j |z_j − z̄|²` (exata, para seis pontos).
* Pontos `½ ± d ± it` e `½ ± it` (relativos ao centro): `E = 24d² + 36t²` (**não** `16d² + 24t²`)
  e energia horizontal `E_x = 24d²`, nula ⟺ `d = 0`.
* `rh_iff_energia`: HR ⟺ `24 (Re ρ − ½)² = 0` para todo zero não trivial — uma **reformulação**
  exata; a positividade da energia não força seu anulamento.
-/

open Complex Finset

namespace ATK.ClosedMath.Hexagrama

open ATK.ZetaSimetria ATK.CEZ

/-- Vértices do hexagrama. -/
noncomputable def V (R : ℝ) (k : ℕ) : ℂ := R * Complex.exp ((k : ℂ) * (Real.pi / 3) * I)

theorem V_oposto (R : ℝ) (k : ℕ) : V R (k + 3) = -V R k := by
  unfold V
  have e : ((k + 3 : ℕ) : ℂ) * (Real.pi / 3) * I = (k : ℂ) * (Real.pi / 3) * I + Real.pi * I := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

theorem eixo (R : ℝ) (k : ℕ) : V R k + V R (k + 3) = 0 := by
  rw [V_oposto]; ring

/-- As seis pontas somam zero: o centro é o baricentro. -/
theorem soma_seis (R : ℝ) : ∑ k ∈ range 6, V R k = 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h0 := eixo R 0
  have h1 := eixo R 1
  have h2 := eixo R 2
  norm_num at h0 h1 h2
  linear_combination h0 + h1 + h2

/-- Pentagrama: as cinco raízes quintas da unidade somam zero. -/
theorem soma_pentagrama :
    ∑ k ∈ range 5, Complex.exp (2 * Real.pi * I / 5) ^ k = 0 :=
  (Complex.isPrimitiveRoot_exp 5 (by norm_num)).geom_sum_eq_zero (by norm_num)

/-- Contagens do `K₆`: arestas, triângulos, quadriláteros e retângulos. -/
theorem contagens : Nat.choose 6 2 = 15 ∧ Nat.choose 6 3 = 20 ∧ Nat.choose 6 4 = 15 ∧
    Nat.choose 3 2 = 3 := by decide

/-- Adjacência do grafo completo `K₆`. -/
def A : Matrix (Fin 6) (Fin 6) ℝ := Matrix.of fun i j => if i = j then 0 else 1

theorem A_mulVec (v : Fin 6 → ℝ) (i : Fin 6) : (A.mulVec v) i = (∑ j, v j) - v i := by
  fin_cases i <;> simp [A, Matrix.mulVec, dotProduct, Fin.sum_univ_six] <;> ring

/-- `A·1 = 5·1`. -/
theorem A_um (i : Fin 6) : (A.mulVec fun _ => (1 : ℝ)) i = 5 := by
  rw [A_mulVec]; simp; norm_num

/-- `A v = −v` quando `Σ v = 0`. -/
theorem A_soma_zero {v : Fin 6 → ℝ} (hv : ∑ j, v j = 0) (i : Fin 6) : (A.mulVec v) i = -v i := by
  rw [A_mulVec, hv]; ring

/-- Laplaciano `L = 5I − A`: `L·1 = 0` e `L v = 6v` para `Σ v = 0`. -/
theorem laplaciano (v : Fin 6 → ℝ) (hv : ∑ j, v j = 0) (i : Fin 6) :
    5 * (1 : ℝ) - (A.mulVec fun _ => (1 : ℝ)) i = 0 ∧ 5 * v i - (A.mulVec v) i = 6 * v i := by
  refine ⟨by rw [A_um]; norm_num, by rw [A_soma_zero hv]; ring⟩

/-- Energia `E = ½ Σ_{i,j} |z_i − z_j|²`. -/
noncomputable def energia (z : Fin 6 → ℂ) : ℝ := (∑ i, ∑ j, ‖z i - z j‖ ^ 2) / 2

/-- **Identidade da energia**: `E = 6 Σ_j |z_j − z̄|²`. -/
theorem energia_identidade (z : Fin 6 → ℂ) :
    energia z = 6 * ∑ j, ‖z j - (∑ k, z k) / 6‖ ^ 2 := by
  unfold energia
  simp only [Complex.sq_norm, Complex.normSq_apply, Fin.sum_univ_six, sub_re, sub_im, div_re,
    div_im, add_re, add_im]
  norm_num
  ring

/-- Os seis pontos `±d ± it`, `±it` (relativos ao centro ½). -/
noncomputable def pontos (d t : ℝ) : Fin 6 → ℂ :=
  ![d + t * I, -d + t * I, -d - t * I, d - t * I, t * I, -(t * I)]

theorem pontos_val (d t : ℝ) :
    pontos d t 0 = d + t * I ∧ pontos d t 1 = -d + t * I ∧ pontos d t 2 = -d - t * I ∧
      pontos d t 3 = d - t * I ∧ pontos d t 4 = t * I ∧ pontos d t 5 = -(t * I) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Energia total**: `24d² + 36t²` (a conta `16d² + 24t²` está errada). -/
theorem energia_pontos (d t : ℝ) : energia (pontos d t) = 24 * d ^ 2 + 36 * t ^ 2 := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := pontos_val d t
  unfold energia
  simp only [Fin.sum_univ_six, h0, h1, h2, h3, h4, h5, Complex.sq_norm, Complex.normSq_apply,
    sub_re, sub_im, add_re, add_im, neg_re, neg_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im]
  ring

/-- **Energia horizontal**: `E_x = ½ Σ (x_i − x_j)² = 24 d²`, nula ⟺ `d = 0`. -/
theorem energia_horizontal (d : ℝ) :
    (∑ i : Fin 6, ∑ j : Fin 6, (((pontos d 0) i).re - ((pontos d 0) j).re) ^ 2) / 2 = 24 * d ^ 2 ∧
      (24 * d ^ 2 = 0 ↔ d = 0) := by
  refine ⟨?_, by constructor <;> intro h <;> [nlinarith [sq_nonneg d]; (subst h; ring)]⟩
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := pontos_val d 0
  simp only [Fin.sum_univ_six, h0, h1, h2, h3, h4, h5, sub_re, add_re, neg_re, ofReal_re, mul_re,
    I_re, I_im, ofReal_im]
  ring

/-- Energia horizontal de um zero: `24 (Re ρ − ½)²`. -/
noncomputable def Eh (ρ : ℂ) : ℝ := 24 * (ρ.re - 1 / 2) ^ 2

/-- **HR ⟺ energia horizontal nula em todo zero não trivial** (reformulação exata). -/
theorem rh_iff_energia : RiemannHypothesis ↔ ∀ ρ ∈ Z, Eh ρ = 0 := by
  rw [rh_iff_externa_vazia]
  constructor
  · intro h ρ hρ
    unfold Eh
    by_contra hne
    have : ρ.re ≠ 1 / 2 := by
      intro h'; apply hne; rw [h']; ring
    have hm : ρ ∈ ZE := ⟨hρ, this⟩
    rw [h] at hm
    exact hm
  · intro h
    ext ρ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hρ, hne⟩
    have := h ρ hρ
    unfold Eh at this
    have : (ρ.re - 1 / 2) ^ 2 = 0 := by linarith
    exact hne (by nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp this])

/-- A energia é sempre `≥ 0`: positividade não decide HR. -/
theorem Eh_nonneg (ρ : ℂ) : 0 ≤ Eh ρ := by unfold Eh; positivity

end ATK.ClosedMath.Hexagrama

-- Auditoria de axiomas (kernel)
#print axioms ATK.ClosedMath.Hexagrama.V_oposto
#print axioms ATK.ClosedMath.Hexagrama.eixo
#print axioms ATK.ClosedMath.Hexagrama.soma_seis
#print axioms ATK.ClosedMath.Hexagrama.soma_pentagrama
#print axioms ATK.ClosedMath.Hexagrama.contagens
#print axioms ATK.ClosedMath.Hexagrama.A_mulVec
#print axioms ATK.ClosedMath.Hexagrama.A_um
#print axioms ATK.ClosedMath.Hexagrama.A_soma_zero
#print axioms ATK.ClosedMath.Hexagrama.laplaciano
#print axioms ATK.ClosedMath.Hexagrama.energia_identidade
#print axioms ATK.ClosedMath.Hexagrama.pontos_val
#print axioms ATK.ClosedMath.Hexagrama.energia_pontos
#print axioms ATK.ClosedMath.Hexagrama.energia_horizontal
#print axioms ATK.ClosedMath.Hexagrama.rh_iff_energia
#print axioms ATK.ClosedMath.Hexagrama.Eh_nonneg
