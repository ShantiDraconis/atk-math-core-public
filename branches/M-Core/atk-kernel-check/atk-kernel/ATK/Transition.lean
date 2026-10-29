import Mathlib
import ATK.Closure

/-!
# ATK — Operador de transição `OPEN → CLOSED`: leis, limites e a linha crítica

Resposta formal às propostas de 13/10 ("OPEN_MATH tende a ¬OPEN_MATH", operadores
D·R·C·B·K·E·V, matriz 7×7, "o que acontece quando o limite é passado ou na linha do limite").

## 1. A bandeira não é um operador

* `no_universal_flip`: não existe transição `¬P → P` válida para toda `P`.
* `flag_flip_never_settles`: iterar a negação de uma bandeira nunca converge (oscila para sempre).
  "OPEN_MATH → ¬OPEN_MATH" não é progresso; `OPEN_MATH = false` só pode ser CONSEQUÊNCIA de provas.

## 2. Os operadores D, R, C, B, K, E (o V é o portão `closure/closure_gate.py`)

`Pipeline P` empacota os seis operadores como obrigações tipadas: espaço `X`, defeito `D`,
compacidade (K), semicontinuidade (C), controle/aproximação (B), ponte (R+E) até `P`.
* `Pipeline.closes`: um pipeline completo PROVA `P` (pela lei de extração de `ATK.Closure`).
* `pipeline_iff`: `Nonempty (Pipeline P) ↔ P` — os operadores não acrescentam força lógica.
  Toda a dificuldade está em instanciar os campos com `X`, `D` não triviais. As 49 posições da
  matriz 7×7 organizam o trabalho; não o substituem.
* `transport_comp`: as constantes de transporte se MULTIPLICAM ao longo de uma cadeia; uma constante
  não uniforme em qualquer elo destrói a cadeia (`ATK.Closure.transport_fails_nonuniform`).

## 3. A linha do limite (desigualdade crítica de energia)

Para soluções suaves de NS, com `E = ‖u‖²_{Ḣ^{1/2}}`, `Z = ‖u‖²_{Ḣ^{3/2}}` e a constante de produto
`C`, vale `½E' + νZ ≤ C·E^{1/2}·Z`, i.e. `E' ≤ 2(C√E − ν)Z`. O número crítico é
`R = C√E/ν` e a linha é `R = 1`. Os teoremas abaixo são sobre funções reais quaisquer que satisfazem
essa desigualdade (a desigualdade para NS é análise harmônica padrão, não formalizada aqui):

* **Dentro** (`R(0) < 1`): `absorption_inside` — `E(t) ≤ E(0)` para todo `t`, sem nenhuma cota em `Z`.
* **Sobre a linha** (`R(0) = 1`): o argumento de contato ingênuo é FALSO (`tangent_escape`: `t³`
  toca a barreira com derivada 0 e escapa). Mas com `Z` limitado no intervalo (verdade para
  soluções suaves em tempo compacto) a linha ainda aprisiona: `absorption_on_line` (barreira de
  Grönwall `θ + ε·e^{Lt}`). Na linha a dinâmica de comparação é estacionária (`on_line_equilibrium`).
* **Além da linha** (`R(0) > 1`): a desigualdade não controla nada — `beyond_line_growth` exibe
  `E = (2+t)²`, `Z = (2+t)/(1+t) ≤ 2` satisfazendo-a com igualdade e `E → ∞`.
* `criticalNumber_invariant`: `R` é invariante por `(E, ν) ↦ (a²E, aν)` (a reescala de
  `ATK.Closure.ns_rescale`) e `E` é invariante pela escala espaço-tempo de NS: **nenhuma simetria
  move um dado através da linha.** Dados grandes não podem ser reescalados para dados pequenos.

O regime `R > 1` é exatamente onde mora a pergunta (A) do Clay; dentro da linha o resultado é o de
Fujita–Kato (dados pequenos ⇒ global).
-/

noncomputable section

namespace ATK.Transition

open Set Filter
open scoped Topology

/-! ## 1. A bandeira não é um operador -/

/-- Não há transição universal `¬P → P`: inverter a bandeira não é inferência. -/
theorem no_universal_flip : ¬ ∀ P : Prop, ¬ P → P := fun h => h False id

/-- Dupla negação devolve a proposição original: nenhum progresso. -/
theorem double_negation_no_progress (P : Prop) : ¬¬P ↔ P := not_not

/-- Iterar a negação de uma bandeira nunca estabiliza: "OPEN_MATH tende a ¬OPEN_MATH" não tem
limite. -/
theorem flag_flip_never_settles (b : Bool) :
    ¬ ∃ N : ℕ, ∀ n ≥ N, (Bool.not)^[n] b = (Bool.not)^[N] b := by
  rintro ⟨N, hN⟩
  have h := hN (N + 1) (Nat.le_succ N)
  rw [Function.iterate_succ_apply'] at h
  generalize (Bool.not)^[N] b = c at h
  cases c <;> simp at h

/-! ## 2. Os operadores como obrigações tipadas -/

/-- Os operadores D·R·C·B·K·E para um alvo `P`: espaço de estados, defeito, compacidade (K),
semicontinuidade (C), não negatividade, controle que aproxima defeito zero (B), e a ponte
"defeito zero ⇒ P" (R+E). O operador V é a verificação pelo kernel. -/
structure Pipeline (P : Prop) where
  X : Type
  top : TopologicalSpace X
  K : Set X
  D : X → ℝ
  compact : @IsCompact X top K
  nonempty : K.Nonempty
  lsc : @LowerSemicontinuousOn X ℝ top _ D K
  nonneg : ∀ x ∈ K, 0 ≤ D x
  approx : ∀ ε > 0, ∃ x ∈ K, D x < ε
  bridge : (∃ x ∈ K, D x = 0) → P

/-- Um pipeline completo fecha `P` (lei de extração + ponte). -/
theorem Pipeline.closes {P : Prop} (π : Pipeline P) : P := by
  letI := π.top
  exact π.bridge (ATK.Closure.extraction_law π.compact π.nonempty π.lsc π.nonneg π.approx)

/-- **Lei do pipeline:** existir um pipeline para `P` é exatamente `P`. Os operadores não
acrescentam força lógica; o conteúdo está em construir `X`, `D`, `K` não triviais. -/
theorem pipeline_iff (P : Prop) : Nonempty (Pipeline P) ↔ P := by
  constructor
  · rintro ⟨π⟩
    exact π.closes
  · intro h
    refine ⟨⟨Unit, inferInstance, univ, (fun _ => 0), isCompact_univ, univ_nonempty,
      lowerSemicontinuous_const.lowerSemicontinuousOn _, (fun _ _ => le_rfl),
      (fun ε hε => ⟨(), mem_univ _, hε⟩), (fun _ => h)⟩⟩

/-- **Engenharia das constantes:** ao longo de uma cadeia de transportes as constantes se
multiplicam. -/
theorem transport_comp {X Y W : Type*} {T₁ : X → Y} {T₂ : Y → W} {DX : X → ℝ} {DY : Y → ℝ}
    {DW : W → ℝ} {C₁ C₂ : ℝ} (hC₂ : 0 ≤ C₂) (h₁ : ∀ x, DY (T₁ x) ≤ C₁ * DX x)
    (h₂ : ∀ y, DW (T₂ y) ≤ C₂ * DY y) : ∀ x, DW (T₂ (T₁ x)) ≤ (C₂ * C₁) * DX x := by
  intro x
  calc DW (T₂ (T₁ x)) ≤ C₂ * DY (T₁ x) := h₂ _
    _ ≤ C₂ * (C₁ * DX x) := mul_le_mul_of_nonneg_left (h₁ x) hC₂
    _ = (C₂ * C₁) * DX x := by ring

/-! ## 3. A linha do limite -/

/-- Número crítico `R = C√E/ν`. -/
def criticalNumber (C E ν : ℝ) : ℝ := C * Real.sqrt E / ν

/-- `R` é invariante por `(E, ν) ↦ (a²E, aν)`: nenhuma simetria atravessa a linha `R = 1`. -/
theorem criticalNumber_invariant {C E ν a : ℝ} (ha : 0 < a) (hν : ν ≠ 0) :
    criticalNumber C (a ^ 2 * E) (a * ν) = criticalNumber C E ν := by
  unfold criticalNumber
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le,
    show C * (a * Real.sqrt E) = a * (C * Real.sqrt E) by ring, mul_div_mul_left _ _ ha.ne']

/-- **Dentro da linha.** Se `E' ≤ 2(C√E − ν)Z` e `Z > 0` sempre que `E > 0`, e o nível
`c ≥ E(0)` satisfaz `C√c < ν`, então `E(t) ≤ c` em todo `[0, T]` — sem cota nenhuma em `Z`. -/
theorem absorption_inside {E E' Z : ℝ → ℝ} {C ν T c : ℝ}
    (hcont : ContinuousOn E (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt E (E' t) (Ici t) t)
    (hineq : ∀ t ∈ Ico 0 T, E' t ≤ 2 * (C * Real.sqrt (E t) - ν) * Z t)
    (hZ : ∀ t ∈ Ico 0 T, 0 < E t → 0 < Z t)
    (hc0 : E 0 ≤ c) (hcpos : 0 < c) (hcθ : C * Real.sqrt c < ν) :
    ∀ t ∈ Icc 0 T, E t ≤ c := by
  have hbound : ∀ t ∈ Ico 0 T, E t = c → E' t < 0 := by
    intro t ht hEt
    have hZt : 0 < Z t := hZ t ht (by rw [hEt]; exact hcpos)
    have hneg : 2 * (C * Real.sqrt (E t) - ν) < 0 := by
      rw [hEt]
      linarith
    calc E' t ≤ 2 * (C * Real.sqrt (E t) - ν) * Z t := hineq t ht
      _ < 0 := mul_neg_of_neg_of_pos hneg hZt
  have key := image_le_of_deriv_right_lt_deriv_boundary (B := fun _ => c) (B' := fun _ => 0)
    hcont hderiv hc0 (fun x => hasDerivAt_const x c) hbound
  exact fun t ht => key ht

/-- Corolário dentro da linha: com `0 < E(0)` e `R(0) < 1`, a energia crítica nunca passa de `E(0)`. -/
theorem absorption_inside_initial {E E' Z : ℝ → ℝ} {C ν T : ℝ}
    (hcont : ContinuousOn E (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt E (E' t) (Ici t) t)
    (hineq : ∀ t ∈ Ico 0 T, E' t ≤ 2 * (C * Real.sqrt (E t) - ν) * Z t)
    (hZ : ∀ t ∈ Ico 0 T, 0 < E t → 0 < Z t)
    (hE0 : 0 < E 0) (hR : C * Real.sqrt (E 0) < ν) :
    ∀ t ∈ Icc 0 T, E t ≤ E 0 :=
  absorption_inside hcont hderiv hineq hZ le_rfl hE0 hR

/-- **Sobre a linha, o argumento de contato ingênuo é falso.** `f(t) = t³` começa na barreira
`B = 0`, tem derivada `0 ≤ 0` em todo ponto de contato em `[0,1)`, e mesmo assim `f(1) > 0`. -/
theorem tangent_escape :
    (∀ t : ℝ, HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t) ∧
    (∀ t ∈ Ico (0 : ℝ) 1, t ^ 3 = 0 → 3 * t ^ 2 ≤ 0) ∧ (0 : ℝ) ^ 3 ≤ 0 ∧ ¬ ((1 : ℝ) ^ 3 ≤ 0) := by
  refine ⟨fun t => ?_, fun t _ ht => ?_, by norm_num, by norm_num⟩
  · simpa using hasDerivAt_pow 3 t
  · have h0 : t = 0 := pow_eq_zero_iff (n := 3) (by norm_num) |>.mp ht
    rw [h0]
    norm_num

/-- Na linha, `E ≡ θ` é equilíbrio da dinâmica de comparação `E' = 2(C√E − ν)Z`. -/
theorem on_line_equilibrium {C ν : ℝ} (hC : 0 < C) (hν : 0 < ν) (Z : ℝ) :
    2 * (C * Real.sqrt ((ν / C) ^ 2) - ν) * Z = 0 := by
  rw [Real.sqrt_sq (div_pos hν hC).le, mul_div_cancel₀ ν hC.ne', sub_self, mul_zero, zero_mul]

/-- Desigualdade algébrica da barreira: `√E − s ≤ (E − s²)/(2s)` para `E ≥ 0`, `s > 0`. -/
theorem sqrt_sub_le {E s : ℝ} (hE : 0 ≤ E) (hs : 0 < s) :
    Real.sqrt E - s ≤ (E - s ^ 2) / (2 * s) := by
  rw [le_div_iff₀ (by linarith)]
  have h1 := Real.sq_sqrt hE
  nlinarith [sq_nonneg (Real.sqrt E - s)]

/-- **Sobre a linha, com `Z` limitado, a linha ainda aprisiona.** Se `R(0) ≤ 1` (isto é,
`E(0) ≤ (ν/C)²`) e `0 ≤ Z ≤ M` em `[0, T)`, então `E(t) ≤ (ν/C)²` em `[0, T]`.
Prova: barreira `θ + ε·e^{Lt}` com `L = CM/s + 1`, `s = ν/C`, e `ε → 0`. -/
theorem absorption_on_line {E E' Z : ℝ → ℝ} {C ν T M : ℝ} (hC : 0 < C) (hν : 0 < ν)
    (hM : 0 ≤ M) (hcont : ContinuousOn E (Icc 0 T))
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt E (E' t) (Ici t) t)
    (hineq : ∀ t ∈ Ico 0 T, E' t ≤ 2 * (C * Real.sqrt (E t) - ν) * Z t)
    (hZ0 : ∀ t ∈ Ico 0 T, 0 ≤ Z t) (hZM : ∀ t ∈ Ico 0 T, Z t ≤ M)
    (h0 : E 0 ≤ (ν / C) ^ 2) :
    ∀ t ∈ Icc 0 T, E t ≤ (ν / C) ^ 2 := by
  set s := ν / C with hs_def
  have hs : 0 < s := div_pos hν hC
  have hνs : ν = C * s := (mul_div_cancel₀ ν hC.ne').symm
  set L := C * M / s + 1 with hL_def
  have hCMs : 0 ≤ C * M / s := div_nonneg (mul_nonneg hC.le hM) hs.le
  have hLgt : C * M / s < L := by rw [hL_def]; linarith
  intro t ht
  apply le_of_forall_pos_le_add
  intro ε hε
  set δ := ε / Real.exp (L * t) with hδ_def
  have hδ : 0 < δ := div_pos hε (Real.exp_pos _)
  have hB0 : E 0 ≤ s ^ 2 + δ * Real.exp (L * 0) := by
    have : 0 < δ * Real.exp (L * 0) := mul_pos hδ (Real.exp_pos _)
    linarith
  have hBd : ∀ x, HasDerivAt (fun τ => s ^ 2 + δ * Real.exp (L * τ))
      (δ * (Real.exp (L * x) * L)) x := by
    intro x
    have h1 : HasDerivAt (fun τ => L * τ) L x := by
      simpa using (hasDerivAt_id x).const_mul L
    exact ((h1.exp).const_mul δ).const_add (s ^ 2)
  have hbound : ∀ τ ∈ Ico 0 T, E τ = s ^ 2 + δ * Real.exp (L * τ) →
      E' τ < δ * (Real.exp (L * τ) * L) := by
    intro τ hτ hEτ
    have hpos : 0 < δ * Real.exp (L * τ) := mul_pos hδ (Real.exp_pos _)
    have hE0 : 0 ≤ E τ := by
      have := sq_nonneg s
      rw [hEτ]
      linarith
    have hgap : E τ - s ^ 2 = δ * Real.exp (L * τ) := by rw [hEτ]; ring
    have hgap0 : 0 ≤ E τ - s ^ 2 := by rw [hgap]; exact hpos.le
    have hsq := sqrt_sub_le hE0 hs
    have hZτ := hZ0 τ hτ
    have hZMτ := hZM τ hτ
    have h2C : 0 ≤ 2 * C := by linarith
    have hCs : 0 ≤ C / s := div_nonneg hC.le hs.le
    calc E' τ ≤ 2 * (C * Real.sqrt (E τ) - ν) * Z τ := hineq τ hτ
      _ = 2 * C * (Real.sqrt (E τ) - s) * Z τ := by rw [hνs]; ring
      _ ≤ 2 * C * ((E τ - s ^ 2) / (2 * s)) * Z τ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq h2C) hZτ
      _ = (C / s) * (E τ - s ^ 2) * Z τ := by first | ring | field_simp
      _ ≤ (C / s) * (E τ - s ^ 2) * M :=
          mul_le_mul_of_nonneg_left hZMτ (mul_nonneg hCs hgap0)
      _ = (C * M / s) * (δ * Real.exp (L * τ)) := by rw [hgap]; ring
      _ < L * (δ * Real.exp (L * τ)) := mul_lt_mul_of_pos_right hLgt hpos
      _ = δ * (Real.exp (L * τ) * L) := by ring
  have key := image_le_of_deriv_right_lt_deriv_boundary
    (B := fun τ => s ^ 2 + δ * Real.exp (L * τ))
    (B' := fun τ => δ * (Real.exp (L * τ) * L)) hcont hderiv hB0 hBd hbound ht
  calc E t ≤ s ^ 2 + δ * Real.exp (L * t) := key
    _ = s ^ 2 + ε := by
      rw [hδ_def, div_mul_cancel₀ _ (Real.exp_pos _).ne']

/-- Modelo **além da linha**: `E(t) = (2+t)²`. -/
def beyondE (t : ℝ) : ℝ := (2 + t) ^ 2

/-- `Z(t) = (2+t)/(1+t)`, limitado por 2 em `t ≥ 0`. -/
def beyondZ (t : ℝ) : ℝ := (2 + t) / (1 + t)

/-- **Além da linha a desigualdade não controla nada.** Com `C = ν = 1` (linha `E = 1`) e
`E(0) = 4` (`R(0) = 2 > 1`), o par `(E, Z)` satisfaz `E' = 2(C√E − ν)Z` com IGUALDADE,
`0 ≤ Z ≤ 2`, `Z > 0`, e mesmo assim `E` cresce sem limite. -/
theorem beyond_line_growth :
    (∀ t : ℝ, HasDerivAt beyondE (2 * (2 + t)) t) ∧
    (∀ t : ℝ, 0 ≤ t → 2 * (2 + t) = 2 * (1 * Real.sqrt (beyondE t) - 1) * beyondZ t) ∧
    (∀ t : ℝ, 0 ≤ t → 0 < beyondZ t ∧ beyondZ t ≤ 2) ∧
    1 * Real.sqrt (beyondE 0) > 1 ∧
    (∀ K : ℝ, ∃ t : ℝ, 0 ≤ t ∧ K < beyondE t) := by
  refine ⟨fun t => ?_, fun t ht => ?_, fun t ht => ⟨?_, ?_⟩, ?_, fun K => ?_⟩
  · show HasDerivAt (fun s : ℝ => (2 + s) ^ 2) (2 * (2 + t)) t
    simpa using ((hasDerivAt_id t).const_add 2).fun_pow 2
  · have h1 : (1 : ℝ) + t ≠ 0 := by linarith
    unfold beyondE beyondZ
    rw [Real.sqrt_sq (by linarith),
      show 2 * (1 * (2 + t) - 1) * ((2 + t) / (1 + t)) = 2 * (2 + t) * ((1 + t) / (1 + t)) by ring,
      div_self h1, mul_one]
  · unfold beyondZ
    exact div_pos (by linarith) (by linarith)
  · unfold beyondZ
    rw [div_le_iff₀ (by linarith)]
    linarith
  · unfold beyondE
    rw [Real.sqrt_sq (by norm_num)]
    norm_num
  · refine ⟨|K| + 1, by positivity, ?_⟩
    unfold beyondE
    nlinarith [abs_nonneg K, le_abs_self K, sq_nonneg |K|]

end ATK.Transition

end

#print axioms ATK.Transition.no_universal_flip
#print axioms ATK.Transition.double_negation_no_progress
#print axioms ATK.Transition.flag_flip_never_settles
#print axioms ATK.Transition.Pipeline.closes
#print axioms ATK.Transition.pipeline_iff
#print axioms ATK.Transition.transport_comp
#print axioms ATK.Transition.criticalNumber_invariant
#print axioms ATK.Transition.absorption_inside
#print axioms ATK.Transition.absorption_inside_initial
#print axioms ATK.Transition.tangent_escape
#print axioms ATK.Transition.on_line_equilibrium
#print axioms ATK.Transition.sqrt_sub_le
#print axioms ATK.Transition.absorption_on_line
#print axioms ATK.Transition.beyond_line_growth
