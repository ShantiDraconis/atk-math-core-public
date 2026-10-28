import ATK.ATKINormal

/-!
# ATK-I — a álgebra relacional completa

Sobre os pares `(a = b)` de `ATK.ATKINormal.Par` (o objeto, não a sua verdade):

* operações componente a componente (soma, produto, negação, troca) e as leis de anel
  comutativo; as relações verdadeiras (a diagonal) são fechadas por soma, produto e escala;
* leis do defeito `d(a = b) = |a − b|`: simetria, desigualdade triangular, propagação no produto
  `d(R ⊗ S) ≤ |c|·d(R) + |b|·d(S)` e a fatoração exata da potência
  `d(Rⁿ) = d(R)·|Σ aⁱ bⁿ⁻¹⁻ⁱ|`; a potência pode apagar o defeito: `(−1 = 1)² = (1 = 1)`;
* o quociente por "mesmo defeito" não preserva a soma (contraexemplo);
* três estados por tolerância (verdade / aproximada / longe);
* defeito infinitesimal não é defeito zero (hiper-reais);
* fechamento simultâneo: `Σ wᵢ dᵢ/(1+dᵢ) = 0 ⟺ ∀ i, dᵢ = 0` e `Σ wᵢ (aᵢ − bᵢ)² = 0 ⟺ ∀ i, aᵢ = bᵢ`.

Tudo isto é álgebra das relações; nada aqui decide a verdade de uma relação aberta.
-/

open Finset

namespace ATK.ATKIAlgebra

open ATK.ATKINormal

noncomputable section

/-! ## 1. Operações e leis de anel -/

def soma (R S : Par) : Par := ⟨R.a + S.a, R.b + S.b⟩

def prod (R S : Par) : Par := ⟨R.a * S.a, R.b * S.b⟩

def neg (R : Par) : Par := ⟨-R.a, -R.b⟩

def troca (R : Par) : Par := ⟨R.b, R.a⟩

def zero : Par := ⟨0, 0⟩

def um : Par := ⟨1, 1⟩

theorem ext {R S : Par} (h1 : R.a = S.a) (h2 : R.b = S.b) : R = S := by
  cases R
  cases S
  exact congrArg₂ Par.mk h1 h2

theorem soma_comm (R S : Par) : soma R S = soma S R := ext (add_comm _ _) (add_comm _ _)

theorem soma_assoc (R S U : Par) : soma (soma R S) U = soma R (soma S U) :=
  ext (add_assoc _ _ _) (add_assoc _ _ _)

theorem prod_comm (R S : Par) : prod R S = prod S R := ext (mul_comm _ _) (mul_comm _ _)

theorem prod_assoc (R S U : Par) : prod (prod R S) U = prod R (prod S U) :=
  ext (mul_assoc _ _ _) (mul_assoc _ _ _)

theorem distrib (R S U : Par) : prod R (soma S U) = soma (prod R S) (prod R U) :=
  ext (mul_add _ _ _) (mul_add _ _ _)

theorem soma_zero (R : Par) : soma R zero = R := ext (add_zero _) (add_zero _)

theorem prod_um (R : Par) : prod R um = R := ext (mul_one _) (mul_one _)

theorem soma_neg (R : Par) : soma R (neg R) = zero := ext (add_neg_cancel _) (add_neg_cancel _)

theorem troca_troca (R : Par) : troca (troca R) = R := rfl

/-! ## 2. As relações verdadeiras formam uma subestrutura -/

theorem vale_soma {R S : Par} (hR : R.vale) (hS : S.vale) : (soma R S).vale :=
  show R.a + S.a = R.b + S.b by
    rw [show R.a = R.b from hR, show S.a = S.b from hS]

theorem vale_prod {R S : Par} (hR : R.vale) (hS : S.vale) : (prod R S).vale :=
  show R.a * S.a = R.b * S.b by
    rw [show R.a = R.b from hR, show S.a = S.b from hS]

theorem vale_escala {R : Par} (hR : R.vale) (k : ℝ) : (Par.escala k R).vale :=
  show k * R.a = k * R.b by rw [show R.a = R.b from hR]

theorem vale_um : um.vale := rfl

theorem vale_zero : zero.vale := rfl

/-! ## 3. Leis do defeito -/

theorem defeito_troca (R : Par) : (troca R).defeito = R.defeito :=
  show |R.b - R.a| = |R.a - R.b| from abs_sub_comm _ _

theorem defeito_soma_le (R S : Par) : (soma R S).defeito ≤ R.defeito + S.defeito := by
  show |R.a + S.a - (R.b + S.b)| ≤ |R.a - R.b| + |S.a - S.b|
  have h : R.a + S.a - (R.b + S.b) = (R.a - R.b) + (S.a - S.b) := by ring
  rw [h]
  exact abs_add_le _ _

/-- Propagação no produto: `d(R ⊗ S) ≤ |c|·d(R) + |b|·d(S)` com `R = (a = b)`, `S = (c = d)`. -/
theorem defeito_prod_le (R S : Par) :
    (prod R S).defeito ≤ |S.a| * R.defeito + |R.b| * S.defeito := by
  show |R.a * S.a - R.b * S.b| ≤ |S.a| * |R.a - R.b| + |R.b| * |S.a - S.b|
  have h : R.a * S.a - R.b * S.b = (R.a - R.b) * S.a + R.b * (S.a - S.b) := by ring
  rw [h]
  calc |(R.a - R.b) * S.a + R.b * (S.a - S.b)|
      ≤ |(R.a - R.b) * S.a| + |R.b * (S.a - S.b)| := abs_add_le _ _
    _ = |S.a| * |R.a - R.b| + |R.b| * |S.a - S.b| := by rw [abs_mul, abs_mul]; ring

/-- Fatoração exata da potência: `d(Rⁿ) = d(R)·|Σ_{i<n} aⁱ bⁿ⁻¹⁻ⁱ|`. -/
theorem defeito_pot (n : ℕ) (R : Par) :
    (Par.pot n R).defeito = R.defeito * |∑ i ∈ range n, R.a ^ i * R.b ^ (n - 1 - i)| := by
  show |R.a ^ n - R.b ^ n| = |R.a - R.b| * |∑ i ∈ range n, R.a ^ i * R.b ^ (n - 1 - i)|
  rw [← abs_mul, ← geom_sum₂_mul]
  exact congrArg abs (mul_comm _ _)

/-- O exemplo do texto: `|2 − 1|·(2² + 2·1 + 1²) = 7 = d(8 = 1)`. -/
theorem fatoracao_exemplo : |(2 : ℝ) - 1| * (2 ^ 2 + 2 * 1 + 1 ^ 2) = 7 := by norm_num

/-- A potência pode apagar o defeito: `(−1 = 1)` é falsa e `(−1 = 1)² = (1 = 1)` vale. -/
theorem pot_apaga_defeito : ¬ (⟨-1, 1⟩ : Par).vale ∧ (Par.pot 2 ⟨-1, 1⟩).vale := by
  constructor
  · show ¬ ((-1 : ℝ) = 1)
    norm_num
  · show ((-1 : ℝ)) ^ 2 = (1 : ℝ) ^ 2
    norm_num

/-! ## 4. O quociente por defeito não preserva a soma -/

theorem quociente_nao_preserva_soma :
    (⟨1, 0⟩ : Par).defeito = (⟨0, 1⟩ : Par).defeito ∧
      (soma ⟨1, 0⟩ ⟨1, 0⟩).defeito ≠ (soma ⟨0, 1⟩ ⟨1, 0⟩).defeito := by
  constructor
  · show |(1 : ℝ) - 0| = |(0 : ℝ) - 1|
    norm_num
  · show |(1 : ℝ) + 1 - (0 + 0)| ≠ |(0 : ℝ) + 1 - (1 + 0)|
    norm_num

/-! ## 5. Três estados por tolerância -/

inductive Estado3
  | verdade
  | aproximada
  | longe
  deriving DecidableEq

open Classical in
/-- `TRUE` se o defeito é `0`, `APPROX` se `0 < d ≤ τ`, `FAR` se `d > τ`. -/
def estado (τ : ℝ) (R : Par) : Estado3 :=
  if R.defeito = 0 then .verdade else if R.defeito ≤ τ then .aproximada else .longe

theorem estado_verdade_iff (τ : ℝ) (R : Par) : estado τ R = .verdade ↔ R.vale := by
  rw [Par.vale_iff_defeito]
  unfold estado
  by_cases h1 : R.defeito = 0
  · simp [h1]
  · by_cases h2 : R.defeito ≤ τ <;> simp [h1, h2]

/-- `(0 = 1)` com tolerância `1/4` está longe. -/
theorem exemplo_longe : estado (1 / 4) ⟨0, 1⟩ = .longe := by
  have hd : (⟨0, 1⟩ : Par).defeito = 1 := by
    show |(0 : ℝ) - 1| = 1
    norm_num
  unfold estado
  rw [hd]
  norm_num

/-! ## 6. Defeito infinitesimal não é defeito zero -/

/-- `(ε = 0)` nos hiper-reais: o defeito `|ε − 0|` é positivo, mas menor que todo real
positivo (infinitesimal). -/
theorem defeito_infinitesimal :
    0 < |Hyperreal.epsilon - 0| ∧ ∀ r : ℝ, 0 < r → |Hyperreal.epsilon - 0| < (r : Hyperreal) := by
  rw [sub_zero, abs_of_pos Hyperreal.epsilon_pos]
  exact ⟨Hyperreal.epsilon_pos, fun r hr => Hyperreal.epsilon_lt_of_pos hr⟩

/-! ## 7. Fechamento simultâneo -/

/-- `Σ wᵢ dᵢ/(1+dᵢ) = 0 ⟺ ∀ i, dᵢ = 0` (pesos positivos, defeitos não negativos). -/
theorem fechamento_simultaneo {ι : Type*} (s : Finset ι) (w d : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hd : ∀ i ∈ s, 0 ≤ d i) :
    ∑ i ∈ s, w i * (d i / (1 + d i)) = 0 ↔ ∀ i ∈ s, d i = 0 := by
  have hnn : ∀ i ∈ s, 0 ≤ w i * (d i / (1 + d i)) := fun i hi =>
    mul_nonneg (hw i hi).le (div_nonneg (hd i hi) (by linarith [hd i hi]))
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn]
  refine forall₂_congr fun i hi => ?_
  have h1 : 0 < 1 + d i := by linarith [hd i hi]
  rw [mul_eq_zero, div_eq_zero_iff]
  constructor
  · rintro (h | h | h)
    · exact absurd h (hw i hi).ne'
    · exact h
    · exact absurd h h1.ne'
  · intro h
    exact Or.inr (Or.inl h)

/-- As sete conjecturas: `U = Σ wᵢ dᵢ/(1+dᵢ) = 0 ⟺ os sete defeitos são zero`. -/
theorem universal_sete (w d : Fin 7 → ℝ) (hw : ∀ i, 0 < w i) (hd : ∀ i, 0 ≤ d i) :
    ∑ i, w i * (d i / (1 + d i)) = 0 ↔ ∀ i, d i = 0 := by
  rw [fechamento_simultaneo Finset.univ w d (fun i _ => hw i) (fun i _ => hd i)]
  simp

/-- `F = Σ wᵢ (aᵢ − bᵢ)² = 0 ⟺ ∀ i, aᵢ = bᵢ`. -/
theorem fechamento_quadratico (w a b : Fin 7 → ℝ) (hw : ∀ i, 0 < w i) :
    ∑ i, w i * (a i - b i) ^ 2 = 0 ↔ ∀ i, a i = b i := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hw i).le (sq_nonneg _))]
  constructor
  · intro h i
    have h0 := h i (Finset.mem_univ i)
    have h2 : (a i - b i) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h0 with h3 | h3
      · exact absurd h3 (hw i).ne'
      · exact h3
    exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  · intro h i _
    rw [h i, sub_self]
    ring

end

end ATK.ATKIAlgebra

#print axioms ATK.ATKIAlgebra.ext
#print axioms ATK.ATKIAlgebra.soma_comm
#print axioms ATK.ATKIAlgebra.soma_assoc
#print axioms ATK.ATKIAlgebra.prod_comm
#print axioms ATK.ATKIAlgebra.prod_assoc
#print axioms ATK.ATKIAlgebra.distrib
#print axioms ATK.ATKIAlgebra.soma_zero
#print axioms ATK.ATKIAlgebra.prod_um
#print axioms ATK.ATKIAlgebra.soma_neg
#print axioms ATK.ATKIAlgebra.troca_troca
#print axioms ATK.ATKIAlgebra.vale_soma
#print axioms ATK.ATKIAlgebra.vale_prod
#print axioms ATK.ATKIAlgebra.vale_escala
#print axioms ATK.ATKIAlgebra.vale_um
#print axioms ATK.ATKIAlgebra.vale_zero
#print axioms ATK.ATKIAlgebra.defeito_troca
#print axioms ATK.ATKIAlgebra.defeito_soma_le
#print axioms ATK.ATKIAlgebra.defeito_prod_le
#print axioms ATK.ATKIAlgebra.defeito_pot
#print axioms ATK.ATKIAlgebra.fatoracao_exemplo
#print axioms ATK.ATKIAlgebra.pot_apaga_defeito
#print axioms ATK.ATKIAlgebra.quociente_nao_preserva_soma
#print axioms ATK.ATKIAlgebra.estado_verdade_iff
#print axioms ATK.ATKIAlgebra.exemplo_longe
#print axioms ATK.ATKIAlgebra.defeito_infinitesimal
#print axioms ATK.ATKIAlgebra.fechamento_simultaneo
#print axioms ATK.ATKIAlgebra.universal_sete
#print axioms ATK.ATKIAlgebra.fechamento_quadratico
