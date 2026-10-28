import ATK.ZeroClasses.LittlewoodPiIncond
import ATK.ZeroClasses.PiLi

/-!
# `Θ` lido por cotas de um lado de `θ(x) − x` e de `π(x) − Li(x)` (rodada 97)

A rodada 87 (`Unilateral`) leu `Θ = sup Re ρ` em cotas **de um lado só** de `ψ(x) − x` e de `M(x)`; a rodada 60
(`PiLi`), em cotas **bilaterais** de `θ(x) − x` e `π(x) − Li(x)`. Aqui fecham-se os dois casos que faltavam,
com `Li(x) = ∫₂ˣ dt/log t`:

* `CimaTheta b`, `BaixoTheta b`, `CimaPi b`, `BaixoPi b`: `θ(x) − x ≤ A x^b + K`, `θ(x) − x ≥ −(A x^b) − K`,
  e o mesmo para `π(x) − Li(x)`, em `x ≥ 2`;
* **`semZeros_of_cimaTheta`**, **`semZeros_of_baixoTheta`**: um lado de `θ(x) − x` com expoente `θ ∈ [½, 1)` já dá
  `ζ ≠ 0` em `Re s > θ` (via `ψ − θ ≤ C√x`, da Mathlib, e Landau para `ψ`, rodada 87);
* **`semZeros_of_cimaPi`**, **`semZeros_of_baixoPi`**: o mesmo para `π(x) − Li(x)` (via `a(N) = π(N) − Li(N) + O(√N)`
  e Landau para `log ζ`, rodada 96);
* **`Teta_le_iff_theta_le`**, **`_theta_ge`**, **`_pi_le`**, **`_pi_ge`**: `Θ ≤ θ` ⟺ a cota de um lado com expoente
  `θ + ε` para todo `ε > 0`;
* **`rh_iff_theta_le`**, **`_theta_ge`**, **`rh_iff_pi_le`**, **`rh_iff_pi_ge`**: RH ⟺ von Koch de um lado só — por
  exemplo, **RH ⟺ `π(x) ≤ Li(x) + O(x^{½+ε})`** para todo `ε > 0`, e também ⟺ `π(x) ≥ Li(x) − O(x^{½+ε})`;
* `nao_cimaTheta`, …, `nao_baixoPi`: para `½ ≤ θ < Θ`, nenhuma das quatro cotas vale (`Ω±(x^θ)`).

Com isto `ψ`, `θ`, `π − Li` e `M` medem o mesmo `Θ` por cima e por baixo.

Classificação: **reformulação** (`Θ` e RH por cotas unilaterais) — resultados clássicos (Landau 1905; Ingham,
*The Distribution of Prime Numbers*, cap. V), aqui só formalizados. RH continua OPEN_MATH.
-/

open Filter
open scoped Real

namespace ATK.ZeroClasses.PiUnilateral

open ATK.ZeroClasses.QuasiRH (SemZeros)
open ATK.ZeroClasses.BDTheta (Teta Teta_le_iff Teta_le_um meio_le_Teta rh_iff_Teta)
open ATK.ZeroClasses.PiLi (Li ErroPi ErroTheta semZeros_iff_pi semZeros_iff_theta)
open ATK.ZeroClasses.LittlewoodPiIncond (aPi aPi_bounds aPi_pequeno sqrt_le_rpow semZeros_of_aPi_le
  semZeros_of_aPi_ge)

/-! ## 1. As quatro cotas de um lado -/

/-- `θ(x) − x ≤ A x^b + K` para `x ≥ 2`. -/
def CimaTheta (b : ℝ) : Prop :=
  ∃ A K : ℝ, ∀ x : ℝ, 2 ≤ x → Chebyshev.theta x - x ≤ A * x ^ b + K

/-- `θ(x) − x ≥ −(A x^b) − K` para `x ≥ 2`. -/
def BaixoTheta (b : ℝ) : Prop :=
  ∃ A K : ℝ, ∀ x : ℝ, 2 ≤ x → -(A * x ^ b) - K ≤ Chebyshev.theta x - x

/-- `π(x) − Li(x) ≤ A x^b + K` para `x ≥ 2`. -/
def CimaPi (b : ℝ) : Prop :=
  ∃ A K : ℝ, ∀ x : ℝ, 2 ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x ≤ A * x ^ b + K

/-- `π(x) − Li(x) ≥ −(A x^b) − K` para `x ≥ 2`. -/
def BaixoPi (b : ℝ) : Prop :=
  ∃ A K : ℝ, ∀ x : ℝ, 2 ≤ x → -(A * x ^ b) - K ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) - Li x

theorem cimaTheta_of_erro {b : ℝ} (h : ErroTheta b) : CimaTheta b := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, 0, fun x hx => by rw [add_zero]; exact (le_abs_self _).trans (hC x hx)⟩

theorem baixoTheta_of_erro {b : ℝ} (h : ErroTheta b) : BaixoTheta b := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, 0, fun x hx => by rw [sub_zero]; exact neg_le_of_abs_le (hC x hx)⟩

theorem cimaPi_of_erro {b : ℝ} (h : ErroPi b) : CimaPi b := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, 0, fun x hx => by rw [add_zero]; exact (le_abs_self _).trans (hC x hx)⟩

theorem baixoPi_of_erro {b : ℝ} (h : ErroPi b) : BaixoPi b := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, 0, fun x hx => by rw [sub_zero]; exact neg_le_of_abs_le (hC x hx)⟩

/-- `A N^b ≤ max A 0 · (N + 1)^b`. -/
theorem pot_le {A b : ℝ} (hb : 0 ≤ b) (N : ℕ) :
    A * (N : ℝ) ^ b ≤ max A 0 * ((N : ℝ) + 1) ^ b := by
  have h0 : (0 : ℝ) ≤ N := N.cast_nonneg
  have h1 : (N : ℝ) ^ b ≤ ((N : ℝ) + 1) ^ b := Real.rpow_le_rpow h0 (by linarith) hb
  have h2 : 0 ≤ (N : ℝ) ^ b := Real.rpow_nonneg h0 b
  calc A * (N : ℝ) ^ b ≤ max A 0 * (N : ℝ) ^ b := mul_le_mul_of_nonneg_right (le_max_left _ _) h2
    _ ≤ max A 0 * ((N : ℝ) + 1) ^ b := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)

/-! ## 2. Um lado basta: Landau -/

/-- **Um lado de `θ(x) − x` por cima dá `ζ ≠ 0` em `Re s > θ`.** -/
theorem semZeros_of_cimaTheta {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (h : CimaTheta θ) : SemZeros θ := by
  obtain ⟨A, K, hAK⟩ := h
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ATK.ZeroClasses.Unilateral.semZeros_of_psi_le (A := max A 0 + max C 0) (K := max K 0) (by linarith) hθ1
    fun N => ?_
  have hp : 0 ≤ ((N : ℝ) + 1) ^ θ := by positivity
  have hA0 : 0 ≤ max A 0 * ((N : ℝ) + 1) ^ θ := mul_nonneg (le_max_right _ _) hp
  have hC0 : 0 ≤ max C 0 * ((N : ℝ) + 1) ^ θ := mul_nonneg (le_max_right _ _) hp
  have hK := le_max_left K 0
  have hK0 := le_max_right K 0
  rw [add_mul]
  rcases lt_or_ge N 2 with hN | hN
  · have hN1 : (N : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hN
    rw [Chebyshev.psi_eq_zero_of_le_one hN1]
    linarith [N.cast_nonneg (α := ℝ)]
  · have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have h1 := hAK N hN2
    have h2 := pot_le (A := A) (b := θ) (by linarith) N
    have h3 : C * √(N : ℝ) ≤ max C 0 * ((N : ℝ) + 1) ^ θ :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (sqrt_le_rpow hθ N) (le_max_right _ _))
    linarith [hC N]

/-- **Um lado de `θ(x) − x` por baixo dá `ζ ≠ 0` em `Re s > θ`.** -/
theorem semZeros_of_baixoTheta {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (h : BaixoTheta θ) : SemZeros θ := by
  obtain ⟨A, K, hAK⟩ := h
  refine ATK.ZeroClasses.Unilateral.semZeros_of_psi_ge (A := max A 0) (K := max K 0 + 1) (by linarith) hθ1
    fun N => ?_
  have hp : 0 ≤ ((N : ℝ) + 1) ^ θ := by positivity
  have hA0 : 0 ≤ max A 0 * ((N : ℝ) + 1) ^ θ := mul_nonneg (le_max_right _ _) hp
  have hK := le_max_left K 0
  have hK0 := le_max_right K 0
  have hψ := Chebyshev.psi_nonneg (N : ℝ)
  rcases lt_or_ge N 2 with hN | hN
  · have hN1 : (N : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hN
    linarith
  · have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have h1 := hAK N hN2
    have h2 := pot_le (A := A) (b := θ) (by linarith) N
    linarith [Chebyshev.theta_le_psi (N : ℝ)]

/-- **Um lado de `π(x) − Li(x)` por cima dá `ζ ≠ 0` em `Re s > θ`.** -/
theorem semZeros_of_cimaPi {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (h : CimaPi θ) : SemZeros θ := by
  obtain ⟨A, K, hAK⟩ := h
  obtain ⟨C, hC0, hC⟩ := aPi_bounds
  refine semZeros_of_aPi_le (A := max A 0 + C) (K := max K 0 + 6) (by linarith) hθ1 fun N => ?_
  have hp : 0 ≤ ((N : ℝ) + 1) ^ θ := by positivity
  have hA0 : 0 ≤ max A 0 * ((N : ℝ) + 1) ^ θ := mul_nonneg (le_max_right _ _) hp
  have hCp : 0 ≤ C * ((N : ℝ) + 1) ^ θ := mul_nonneg hC0 hp
  have hK := le_max_left K 0
  have hK0 := le_max_right K 0
  rw [add_mul]
  rcases lt_or_ge N 2 with hN | hN
  · linarith [(aPi_pequeno hN).2]
  · have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have h1 := hAK N hN2
    rw [Nat.floor_natCast] at h1
    have h2 := pot_le (A := A) (b := θ) (by linarith) N
    have h3 : C * √(N : ℝ) ≤ C * ((N : ℝ) + 1) ^ θ := mul_le_mul_of_nonneg_left (sqrt_le_rpow hθ N) hC0
    linarith [(hC N hN).1]

/-- **Um lado de `π(x) − Li(x)` por baixo dá `ζ ≠ 0` em `Re s > θ`.** -/
theorem semZeros_of_baixoPi {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (h : BaixoPi θ) : SemZeros θ := by
  obtain ⟨A, K, hAK⟩ := h
  obtain ⟨C, hC0, hC⟩ := aPi_bounds
  have hl2 : 0 < 1 / Real.log 2 := one_div_pos.mpr (Real.log_pos (by norm_num))
  refine semZeros_of_aPi_ge (A := max A 0) (K := max K 0 + 1 / Real.log 2 + 6) (by linarith) hθ1 fun N => ?_
  have hp : 0 ≤ ((N : ℝ) + 1) ^ θ := by positivity
  have hA0 : 0 ≤ max A 0 * ((N : ℝ) + 1) ^ θ := mul_nonneg (le_max_right _ _) hp
  have hK := le_max_left K 0
  have hK0 := le_max_right K 0
  rcases lt_or_ge N 2 with hN | hN
  · linarith [(aPi_pequeno hN).1]
  · have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have h1 := hAK N hN2
    rw [Nat.floor_natCast] at h1
    have h2 := pot_le (A := A) (b := θ) (by linarith) N
    linarith [(hC N hN).2]

/-! ## 3. `Θ` e RH por um lado -/

open ATK.ZeroClasses.Unilateral (Teta_le_of_unilateral nao_semZeros)

/-- **`Θ ≤ θ` ⟺ `θ(x) − x ≤ A x^{θ+ε} + K` para todo `ε > 0`** (`½ ≤ θ < 1`). -/
theorem Teta_le_iff_theta_le {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    Teta ≤ θ ↔ ∀ ε : ℝ, 0 < ε → CimaTheta (θ + ε) :=
  ⟨fun hT ε hε => cimaTheta_of_erro ((semZeros_iff_theta hθ hθ1).mp ((Teta_le_iff hθ).mp hT) ε hε),
    fun h => Teta_le_of_unilateral hθ fun ε hε h1 => semZeros_of_cimaTheta (by linarith) h1 (h ε hε)⟩

/-- **`Θ ≤ θ` ⟺ `θ(x) − x ≥ −(A x^{θ+ε}) − K` para todo `ε > 0`**. -/
theorem Teta_le_iff_theta_ge {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    Teta ≤ θ ↔ ∀ ε : ℝ, 0 < ε → BaixoTheta (θ + ε) :=
  ⟨fun hT ε hε => baixoTheta_of_erro ((semZeros_iff_theta hθ hθ1).mp ((Teta_le_iff hθ).mp hT) ε hε),
    fun h => Teta_le_of_unilateral hθ fun ε hε h1 => semZeros_of_baixoTheta (by linarith) h1 (h ε hε)⟩

/-- **`Θ ≤ θ` ⟺ `π(x) − Li(x) ≤ A x^{θ+ε} + K` para todo `ε > 0`**. -/
theorem Teta_le_iff_pi_le {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    Teta ≤ θ ↔ ∀ ε : ℝ, 0 < ε → CimaPi (θ + ε) :=
  ⟨fun hT ε hε => cimaPi_of_erro ((semZeros_iff_pi hθ hθ1).mp ((Teta_le_iff hθ).mp hT) ε hε),
    fun h => Teta_le_of_unilateral hθ fun ε hε h1 => semZeros_of_cimaPi (by linarith) h1 (h ε hε)⟩

/-- **`Θ ≤ θ` ⟺ `π(x) − Li(x) ≥ −(A x^{θ+ε}) − K` para todo `ε > 0`**. -/
theorem Teta_le_iff_pi_ge {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) :
    Teta ≤ θ ↔ ∀ ε : ℝ, 0 < ε → BaixoPi (θ + ε) :=
  ⟨fun hT ε hε => baixoPi_of_erro ((semZeros_iff_pi hθ hθ1).mp ((Teta_le_iff hθ).mp hT) ε hε),
    fun h => Teta_le_of_unilateral hθ fun ε hε h1 => semZeros_of_baixoPi (by linarith) h1 (h ε hε)⟩

theorem rh_iff_Teta_le : RiemannHypothesis ↔ Teta ≤ 1 / 2 :=
  rh_iff_Teta.trans ⟨fun h => h.le, fun h => le_antisymm h meio_le_Teta⟩

/-- **RH ⟺ `θ(x) ≤ x + O(x^{½+ε})`** (um lado só). -/
theorem rh_iff_theta_le : RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → CimaTheta (1 / 2 + ε) :=
  rh_iff_Teta_le.trans (Teta_le_iff_theta_le le_rfl (by norm_num))

/-- **RH ⟺ `θ(x) ≥ x − O(x^{½+ε})`** (um lado só). -/
theorem rh_iff_theta_ge : RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → BaixoTheta (1 / 2 + ε) :=
  rh_iff_Teta_le.trans (Teta_le_iff_theta_ge le_rfl (by norm_num))

/-- **RH ⟺ `π(x) ≤ Li(x) + O(x^{½+ε})`** (von Koch de um lado só). -/
theorem rh_iff_pi_le : RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → CimaPi (1 / 2 + ε) :=
  rh_iff_Teta_le.trans (Teta_le_iff_pi_le le_rfl (by norm_num))

/-- **RH ⟺ `π(x) ≥ Li(x) − O(x^{½+ε})`** (von Koch de um lado só). -/
theorem rh_iff_pi_ge : RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → BaixoPi (1 / 2 + ε) :=
  rh_iff_Teta_le.trans (Teta_le_iff_pi_ge le_rfl (by norm_num))

/-! ## 4. Abaixo de `Θ`, nenhum dos lados vale -/

theorem nao_cimaTheta {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hlt : θ < Teta) : ¬ CimaTheta θ := fun h =>
  nao_semZeros hlt (semZeros_of_cimaTheta hθ (hlt.trans_le Teta_le_um) h)

theorem nao_baixoTheta {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hlt : θ < Teta) : ¬ BaixoTheta θ := fun h =>
  nao_semZeros hlt (semZeros_of_baixoTheta hθ (hlt.trans_le Teta_le_um) h)

theorem nao_cimaPi {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hlt : θ < Teta) : ¬ CimaPi θ := fun h =>
  nao_semZeros hlt (semZeros_of_cimaPi hθ (hlt.trans_le Teta_le_um) h)

theorem nao_baixoPi {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hlt : θ < Teta) : ¬ BaixoPi θ := fun h =>
  nao_semZeros hlt (semZeros_of_baixoPi hθ (hlt.trans_le Teta_le_um) h)

end ATK.ZeroClasses.PiUnilateral

#print axioms ATK.ZeroClasses.PiUnilateral.cimaTheta_of_erro
#print axioms ATK.ZeroClasses.PiUnilateral.baixoTheta_of_erro
#print axioms ATK.ZeroClasses.PiUnilateral.cimaPi_of_erro
#print axioms ATK.ZeroClasses.PiUnilateral.baixoPi_of_erro
#print axioms ATK.ZeroClasses.PiUnilateral.pot_le
#print axioms ATK.ZeroClasses.PiUnilateral.semZeros_of_cimaTheta
#print axioms ATK.ZeroClasses.PiUnilateral.semZeros_of_baixoTheta
#print axioms ATK.ZeroClasses.PiUnilateral.semZeros_of_cimaPi
#print axioms ATK.ZeroClasses.PiUnilateral.semZeros_of_baixoPi
#print axioms ATK.ZeroClasses.PiUnilateral.Teta_le_iff_theta_le
#print axioms ATK.ZeroClasses.PiUnilateral.Teta_le_iff_theta_ge
#print axioms ATK.ZeroClasses.PiUnilateral.Teta_le_iff_pi_le
#print axioms ATK.ZeroClasses.PiUnilateral.Teta_le_iff_pi_ge
#print axioms ATK.ZeroClasses.PiUnilateral.rh_iff_Teta_le
#print axioms ATK.ZeroClasses.PiUnilateral.rh_iff_theta_le
#print axioms ATK.ZeroClasses.PiUnilateral.rh_iff_theta_ge
#print axioms ATK.ZeroClasses.PiUnilateral.rh_iff_pi_le
#print axioms ATK.ZeroClasses.PiUnilateral.rh_iff_pi_ge
#print axioms ATK.ZeroClasses.PiUnilateral.nao_cimaTheta
#print axioms ATK.ZeroClasses.PiUnilateral.nao_baixoTheta
#print axioms ATK.ZeroClasses.PiUnilateral.nao_cimaPi
#print axioms ATK.ZeroClasses.PiUnilateral.nao_baixoPi
