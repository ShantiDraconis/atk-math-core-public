import ATK.CongruentCurve

/-!
# ATK — Números congruentes: triângulos de área `n` ⟷ pontos de `y² = x³ − n²x` com `y ≠ 0`

Bijeção clássica (ver Koblitz, *Introduction to Elliptic Curves and Modular Forms*, cap. I §2),
provada aqui **só com álgebra de corpos**, para todo `n : ℚ` com `n ≠ 0`:

* triângulo → ponto: `(a, b, c) ↦ (n·b/(c − a), 2n²/(c − a))`;
* ponto → triângulo: `(x, y) ↦ ((x² − n²)/y, 2n·x/y, (x² + n²)/y)`;
* `ponto_de_triangulo_de_ponto`, `triangulo_de_ponto_de_triangulo`: as duas composições são a
  identidade;
* `congruente_iff_ponto`: `n` é congruente ⟺ `y² = x³ − n²x` tem ponto racional com `y ≠ 0`.

Nada aqui usa a descida de Fermat. Por isso a equivalência é **não circular**: para `n = 1`,
`um_nao_congruente_iff_y_eq_zero` mostra que "1 não é congruente" e "todo ponto racional de
`y² = x³ − x` tem `y = 0`" são o mesmo enunciado, e o único conteúdo aritmético está em
`ATK.FermatRightTriangle.one_not_congruent` (descida). Já `ATK.CongruentCurve.E_point_cases` é
**derivado** de `one_not_congruent`; citá-lo para provar que 1 não é congruente seria circular.

A Mathlib não define posto nem torção de `E(ℚ)`; "pontos com `y ≠ 0`" são exatamente os pontos
afins fora da 2-torção. Status: clássico. Não é a conjectura BSD (O6/O7 continuam abertas) e não
decide nenhum `n` além do que a descida já decide.
-/

namespace ATK.CongruentBijection

/-- `(a, b, c)` é um triângulo retângulo racional de área `n`. -/
def Triangulo (n a b c : ℚ) : Prop :=
  a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = n

/-- `(x, y)` é um ponto racional de `y² = x³ − n²x` com `y ≠ 0`. -/
def PontoYNaoNulo (n x y : ℚ) : Prop :=
  y ^ 2 = x ^ 3 - n ^ 2 * x ∧ y ≠ 0

/-- Em um triângulo de área `n ≠ 0`, a hipotenusa difere do cateto `a`. -/
theorem sub_ne_zero_de_triangulo {n a b c : ℚ} (hn : n ≠ 0) (h : Triangulo n a b c) :
    c - a ≠ 0 := by
  intro hca
  have hc : c = a := by linarith
  have hb2 : b ^ 2 = 0 := by
    have := h.1
    rw [hc] at this
    linarith
  have hb : b = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hb2
  apply hn
  rw [← h.2, hb]
  ring

/-- **Triângulo → ponto**: `(n·b/(c − a), 2n²/(c − a))` está em `y² = x³ − n²x`, com `y ≠ 0`. -/
theorem ponto_de_triangulo {n a b c : ℚ} (hn : n ≠ 0) (h : Triangulo n a b c) :
    PontoYNaoNulo n (n * b / (c - a)) (2 * n ^ 2 / (c - a)) := by
  have hd := sub_ne_zero_de_triangulo hn h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, div_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero 2 hn)) hd⟩
  have hab : a * b = 2 * n := by linarith
  field_simp
  linear_combination (-b) * h1 + (-2 * (c - a)) * hab

/-- **Ponto → triângulo**: `((x² − n²)/y, 2n·x/y, (x² + n²)/y)` é um triângulo de área `n`. -/
theorem triangulo_de_ponto {n x y : ℚ} (h : PontoYNaoNulo n x y) :
    Triangulo n ((x ^ 2 - n ^ 2) / y) (2 * n * x / y) ((x ^ 2 + n ^ 2) / y) := by
  obtain ⟨h1, hy⟩ := h
  refine ⟨?_, ?_⟩
  · field_simp
    ring
  · field_simp
    linear_combination (-n) * h1

/-- ponto → triângulo → ponto é a identidade. -/
theorem ponto_de_triangulo_de_ponto {n x y : ℚ} (hn : n ≠ 0) (h : PontoYNaoNulo n x y) :
    n * (2 * n * x / y) / ((x ^ 2 + n ^ 2) / y - (x ^ 2 - n ^ 2) / y) = x ∧
      2 * n ^ 2 / ((x ^ 2 + n ^ 2) / y - (x ^ 2 - n ^ 2) / y) = y := by
  have hy := h.2
  have e : (x ^ 2 + n ^ 2) / y - (x ^ 2 - n ^ 2) / y = 2 * n ^ 2 / y := by
    field_simp
    ring
  rw [e]
  have hn2 : (2 : ℚ) * n ^ 2 ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero 2 hn)
  constructor
  · field_simp
  · field_simp

/-- triângulo → ponto → triângulo é a identidade. -/
theorem triangulo_de_ponto_de_triangulo {n a b c : ℚ} (hn : n ≠ 0) (h : Triangulo n a b c) :
    ((n * b / (c - a)) ^ 2 - n ^ 2) / (2 * n ^ 2 / (c - a)) = a ∧
      2 * n * (n * b / (c - a)) / (2 * n ^ 2 / (c - a)) = b ∧
      ((n * b / (c - a)) ^ 2 + n ^ 2) / (2 * n ^ 2 / (c - a)) = c := by
  have hd := sub_ne_zero_de_triangulo hn h
  obtain ⟨h1, _⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    linear_combination h1
  · field_simp
  · field_simp
    linear_combination h1

/-- **`n` é congruente ⟺ `y² = x³ − n²x` tem ponto racional com `y ≠ 0`** (sem descida). -/
theorem congruente_iff_ponto {n : ℚ} (hn : n ≠ 0) :
    (∃ a b c : ℚ, Triangulo n a b c) ↔ (∃ x y : ℚ, PontoYNaoNulo n x y) := by
  constructor
  · rintro ⟨a, b, c, h⟩
    exact ⟨_, _, ponto_de_triangulo hn h⟩
  · rintro ⟨x, y, h⟩
    exact ⟨_, _, _, triangulo_de_ponto h⟩

/-- Para `n = 1`: "1 não é congruente" ⟺ "todo ponto racional de `y² = x³ − x` tem `y = 0`",
sem usar a descida. -/
theorem um_nao_congruente_iff_y_eq_zero :
    (∀ a b c : ℚ, a ^ 2 + b ^ 2 = c ^ 2 → a * b / 2 ≠ 1) ↔
      (∀ x y : ℚ, y ^ 2 = x ^ 3 - x → y = 0) := by
  constructor
  · intro h x y hxy
    by_contra hy
    have hP : PontoYNaoNulo 1 x y := ⟨by linear_combination hxy, hy⟩
    have hT := triangulo_de_ponto hP
    exact h _ _ _ hT.1 hT.2
  · intro h a b c habc harea
    have hP := ponto_de_triangulo one_ne_zero ⟨habc, harea⟩
    exact hP.2 (h (1 * b / (c - a)) (2 * 1 ^ 2 / (c - a)) (by linear_combination hP.1))

/-- O mesmo, no objeto da Mathlib: `1` é congruente ⟺ `E` (`ATK.CongruentCurve.E`) tem ponto
afim com `y ≠ 0`. -/
theorem um_congruente_iff_ponto_E :
    (∃ a b c : ℚ, a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = 1) ↔
      (∃ x y : ℚ, y ≠ 0 ∧ ATK.CongruentCurve.E.toAffine.Equation x y) := by
  constructor
  · rintro ⟨a, b, c, habc, harea⟩
    have hP := ponto_de_triangulo one_ne_zero ⟨habc, harea⟩
    exact ⟨1 * b / (c - a), 2 * 1 ^ 2 / (c - a), hP.2,
      (ATK.CongruentCurve.E_equation_iff _ _).mpr (by linear_combination hP.1)⟩
  · rintro ⟨x, y, hy, hE⟩
    have hP : PontoYNaoNulo 1 x y :=
      ⟨by linear_combination (ATK.CongruentCurve.E_equation_iff x y).mp hE, hy⟩
    exact ⟨_, _, _, triangulo_de_ponto hP⟩

end ATK.CongruentBijection

#print axioms ATK.CongruentBijection.sub_ne_zero_de_triangulo
#print axioms ATK.CongruentBijection.ponto_de_triangulo
#print axioms ATK.CongruentBijection.triangulo_de_ponto
#print axioms ATK.CongruentBijection.ponto_de_triangulo_de_ponto
#print axioms ATK.CongruentBijection.triangulo_de_ponto_de_triangulo
#print axioms ATK.CongruentBijection.congruente_iff_ponto
#print axioms ATK.CongruentBijection.um_nao_congruente_iff_y_eq_zero
#print axioms ATK.CongruentBijection.um_congruente_iff_ponto_E
