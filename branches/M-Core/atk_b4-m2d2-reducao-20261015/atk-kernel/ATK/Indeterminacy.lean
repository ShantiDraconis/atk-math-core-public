import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Order.Field

/-!
# ATK — Indeterminações como pontos de 3 estados (formalização da proposta do autor)

A proposta: cada indeterminação é um **ponto com 3 estados**; as interações entre pontos são
de novo pontos com 3 estados (ou mais); o estado é **resolvido e medido por L'Hôpital**, e a
medida é uma **constante**. Aqui isso vira matemática verificada pelo kernel do Lean:

1. `Ponto` = germe orientado `a·tᵐ` (a ≠ 0, m ∈ ℤ) em `t → 0⁺`, com 3 estados
   (`zero`, `finito`, `infinito`) decididos pela ordem `m`.
   Interações (`mul`, `div`, `inv`) fecham: produto e quociente de pontos são pontos.
2. Medida: quando o estado do quociente é `finito`, o limite existe e vale a constante `a/b`
   (`medida_finita`). Versão L'Hôpital: `f(0)=g(0)=0`, `f'(0)=a`, `g'(0)=b≠0` ⇒ `f/g → a/b`
   (`lhopital_mede`). Para `0⁰`: `(tᵐ)^(c/|log t|) = e^(−mc)` exatamente — a forma mede a
   multiplicidade `m` como constante (`zero_pow_zero_mede`).
3. `0/0` sozinho não tem valor: os 3 estados ocorrem (`zero_div_zero_tres_estados`) e todo
   real é limite de algum `0/0` (`zero_div_zero_qualquer_valor`). A informação está na ordem.
4. A constante `I = 0 ⊘ 0` existe numa extensão (`RI = Option ℝ`), preserva ℝ, é absorvente,
   não admite cancelamento e é incompatível com as leis de anel.
5. Lógica de 4 estados (Belnap): contradição local sem explosão.
6. Certificado de fechamento: `ClosedMath P ↔ P` — uma flag booleana não é prova.

## O que o kernel também prova (limites honestos)

* `RH_I_iff`: a Hipótese de Riemann reescrita na extensão com `I` **é** a Hipótese de Riemann;
  a constante `I` não move nenhum zero.
* `sem_cancelamento`: `I·D = I·0` para todo `D`, logo nenhuma regra com `I` deduz `D = 0`.
* `monotona_nao_basta`: decrescer e ser positiva não dá `D_N → 0` nem majorante `K/log(N+2)`.

Portanto este módulo **não altera `OPEN_MATH`**: é infraestrutura certificada, não produtor
de nenhuma das obrigações O1–O8.
-/

open Filter Topology Set

namespace ATK.Indeterminacy

/-! ## 1. Pontos de 3 estados -/

/-- Os 3 estados de um ponto singular em `t → 0⁺`. -/
inductive Estado
  | zero
  | finito
  | infinito
  deriving DecidableEq, Repr

/-- Estado decidido pela ordem `m` do germe `tᵐ`. -/
def estadoOrdem (m : ℤ) : Estado :=
  if 0 < m then .zero else if m = 0 then .finito else .infinito

/-- Ponto singular orientado: o germe `a·tᵐ`, com coeficiente `a ≠ 0` e ordem `m ∈ ℤ`. -/
structure Ponto where
  a : ℝ
  m : ℤ
  a_ne : a ≠ 0

namespace Ponto

/-- Estado do ponto. -/
def estado (p : Ponto) : Estado := estadoOrdem p.m

/-- O germe representado. -/
noncomputable def germe (p : Ponto) (t : ℝ) : ℝ := p.a * t ^ p.m

/-- Interação produto. -/
def mul (p q : Ponto) : Ponto := ⟨p.a * q.a, p.m + q.m, mul_ne_zero p.a_ne q.a_ne⟩

/-- Interação quociente. -/
noncomputable def div (p q : Ponto) : Ponto := ⟨p.a / q.a, p.m - q.m, div_ne_zero p.a_ne q.a_ne⟩

/-- Inversão (troca numerador e denominador). -/
noncomputable def inv (p : Ponto) : Ponto := ⟨p.a⁻¹, -p.m, inv_ne_zero p.a_ne⟩

/-- Unidade. -/
def um : Ponto := ⟨1, 0, one_ne_zero⟩

theorem germe_mul (p q : Ponto) {t : ℝ} (ht : t ≠ 0) :
    (p.mul q).germe t = p.germe t * q.germe t := by
  simp only [germe, mul, zpow_add₀ ht]
  ring

theorem germe_div (p q : Ponto) {t : ℝ} (ht : t ≠ 0) :
    (p.div q).germe t = p.germe t / q.germe t := by
  simp only [germe, div, zpow_sub₀ ht]
  field_simp

theorem germe_inv (p : Ponto) (t : ℝ) : p.inv.germe t = (p.germe t)⁻¹ := by
  simp only [germe, inv, zpow_neg, mul_inv]

theorem mul_inv_eq_um (p : Ponto) : p.mul p.inv = um := by
  simp only [mul, inv, um, add_neg_cancel, mul_inv_cancel₀ p.a_ne]

theorem estadoOrdem_zero_iff (m : ℤ) : estadoOrdem m = .zero ↔ 0 < m := by
  unfold estadoOrdem
  by_cases h1 : 0 < m
  · simp [h1]
  · by_cases h2 : m = 0 <;> simp [h2]

theorem estadoOrdem_finito_iff (m : ℤ) : estadoOrdem m = .finito ↔ m = 0 := by
  unfold estadoOrdem
  by_cases h1 : 0 < m
  · simp [h1]; omega
  · by_cases h2 : m = 0 <;> simp [h1, h2]

theorem estadoOrdem_infinito_iff (m : ℤ) : estadoOrdem m = .infinito ↔ m < 0 := by
  unfold estadoOrdem
  by_cases h1 : 0 < m
  · simp [h1]; omega
  · by_cases h2 : m = 0
    · simp [h2]
    · simp [h1, h2]; omega

/-- O estado do quociente é decidido pela ordem relativa `m − n` (3 casos). -/
theorem estado_div_zero_iff (p q : Ponto) : (p.div q).estado = .zero ↔ q.m < p.m := by
  show estadoOrdem (p.m - q.m) = .zero ↔ _
  rw [estadoOrdem_zero_iff]; omega

theorem estado_div_finito_iff (p q : Ponto) : (p.div q).estado = .finito ↔ p.m = q.m := by
  show estadoOrdem (p.m - q.m) = .finito ↔ _
  rw [estadoOrdem_finito_iff]; omega

theorem estado_div_infinito_iff (p q : Ponto) : (p.div q).estado = .infinito ↔ p.m < q.m := by
  show estadoOrdem (p.m - q.m) = .infinito ↔ _
  rw [estadoOrdem_infinito_iff]; omega

/-- Inverter troca `zero` ↔ `infinito` e fixa `finito`. -/
theorem estado_inv_infinito_iff (p : Ponto) : p.inv.estado = .infinito ↔ p.estado = .zero := by
  show estadoOrdem (-p.m) = .infinito ↔ estadoOrdem p.m = .zero
  rw [estadoOrdem_infinito_iff, estadoOrdem_zero_iff]; omega

theorem estado_inv_zero_iff (p : Ponto) : p.inv.estado = .zero ↔ p.estado = .infinito := by
  show estadoOrdem (-p.m) = .zero ↔ estadoOrdem p.m = .infinito
  rw [estadoOrdem_zero_iff, estadoOrdem_infinito_iff]; omega

theorem estado_inv_finito_iff (p : Ponto) : p.inv.estado = .finito ↔ p.estado = .finito := by
  show estadoOrdem (-p.m) = .finito ↔ estadoOrdem p.m = .finito
  rw [estadoOrdem_finito_iff, estadoOrdem_finito_iff]; omega

/-! ### Medida (a constante) -/

/-- **Medida no estado finito**: se as ordens coincidem, `p/q → a/b`. -/
theorem medida_finita (p q : Ponto) (h : p.m = q.m) :
    Tendsto (fun t => p.germe t / q.germe t) (𝓝[>] 0) (𝓝 (p.a / q.a)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ^ q.m ≠ 0 := zpow_ne_zero _ (ne_of_gt ht)
  simp only [germe, h]
  rw [mul_div_mul_right _ _ ht0]

/-- Estado `zero` significa de fato `germe → 0`. -/
theorem estado_zero_tendsto (p : Ponto) (h : 0 < p.m) :
    Tendsto p.germe (𝓝[>] 0) (𝓝 0) := by
  have hc : ContinuousAt (fun t : ℝ => t ^ p.m) 0 := continuousAt_zpow₀ 0 p.m (Or.inr h.le)
  have h0 : (0 : ℝ) ^ p.m = 0 := zero_zpow _ (ne_of_gt h)
  have : Tendsto (fun t : ℝ => p.a * t ^ p.m) (𝓝 0) (𝓝 (p.a * (0 : ℝ) ^ p.m)) :=
    tendsto_const_nhds.mul hc.tendsto
  rw [h0, mul_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- Estado `infinito` (com `a > 0`) significa `germe → +∞`. -/
theorem estado_infinito_tendsto (p : Ponto) (h : p.m < 0) (ha : 0 < p.a) :
    Tendsto p.germe (𝓝[>] 0) atTop := by
  set n : ℕ := (-p.m).toNat with hn
  have hnpos : 0 < n := by omega
  have hm : p.m = -(n : ℤ) := by omega
  have hpow : Tendsto (fun t : ℝ => t ^ n) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun t : ℝ => t ^ n) (𝓝 0) (𝓝 ((0 : ℝ) ^ n)) :=
        (continuous_pow n).continuousAt.tendsto
      rw [zero_pow (ne_of_gt hnpos)] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact pow_pos (show (0 : ℝ) < t from ht) n
  have hinv : Tendsto (fun t : ℝ => (t ^ n)⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero.comp hpow
  have := hinv.const_mul_atTop ha
  refine this.congr' ?_
  filter_upwards with t
  simp only [germe, hm, zpow_neg, zpow_natCast]

end Ponto

/-- **`0/0` tem os 3 estados**: o estado do numerador e do denominador não decide o quociente. -/
theorem zero_div_zero_tres_estados (e : Estado) :
    ∃ p q : Ponto, p.estado = .zero ∧ q.estado = .zero ∧ (p.div q).estado = e := by
  cases e
  · exact ⟨⟨1, 2, one_ne_zero⟩, ⟨1, 1, one_ne_zero⟩, by decide, by decide, by decide⟩
  · exact ⟨⟨1, 1, one_ne_zero⟩, ⟨1, 1, one_ne_zero⟩, by decide, by decide, by decide⟩
  · exact ⟨⟨1, 1, one_ne_zero⟩, ⟨1, 2, one_ne_zero⟩, by decide, by decide, by decide⟩

/-- **`∞/∞` também tem os 3 estados.** -/
theorem inf_div_inf_tres_estados (e : Estado) :
    ∃ p q : Ponto, p.estado = .infinito ∧ q.estado = .infinito ∧ (p.div q).estado = e := by
  cases e
  · exact ⟨⟨1, -1, one_ne_zero⟩, ⟨1, -2, one_ne_zero⟩, by decide, by decide, by decide⟩
  · exact ⟨⟨1, -1, one_ne_zero⟩, ⟨1, -1, one_ne_zero⟩, by decide, by decide, by decide⟩
  · exact ⟨⟨1, -2, one_ne_zero⟩, ⟨1, -1, one_ne_zero⟩, by decide, by decide, by decide⟩

/-- **Todo real é a medida de algum `0/0`**: não existe um valor universal para `0/0`. -/
theorem zero_div_zero_qualquer_valor (c : ℝ) :
    ∃ f g : ℝ → ℝ, Tendsto f (𝓝[>] 0) (𝓝 0) ∧ Tendsto g (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun t => f t / g t) (𝓝[>] 0) (𝓝 c) := by
  refine ⟨fun t => c * t, fun t => t, ?_, ?_, ?_⟩
  · have : Tendsto (fun t : ℝ => c * t) (𝓝 0) (𝓝 (c * 0)) := tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at this; exact this.mono_left nhdsWithin_le_nhds
  · exact tendsto_id.mono_left nhdsWithin_le_nhds
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [mul_div_assoc, div_self (ne_of_gt ht), mul_one]

/-- Perda de informação: só o limite não distingue `t` de `t²`, mas a razão distingue. -/
theorem limite_perde_ordem :
    let p : Ponto := ⟨1, 1, one_ne_zero⟩
    let q : Ponto := ⟨1, 2, one_ne_zero⟩
    p.estado = q.estado ∧ p.m ≠ q.m ∧ (q.div p).estado = .zero ∧ (p.div q).estado = .infinito := by
  decide

/-! ## 2. L'Hôpital como medida -/

/-- **L'Hôpital mede `0/0`**: `f(0) = g(0) = 0`, `f'(0) = a`, `g'(0) = b ≠ 0` ⇒ `f/g → a/b`. -/
theorem lhopital_mede {f g : ℝ → ℝ} {a b : ℝ} (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0) (hb : b ≠ 0) :
    Tendsto (fun t => f t / g t) (𝓝[≠] 0) (𝓝 (a / b)) := by
  have h1 := hasDerivAt_iff_tendsto_slope.mp hf
  have h2 := hasDerivAt_iff_tendsto_slope.mp hg
  refine (h1.div h2 hb).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  show slope f 0 t / slope g 0 t = f t / g t
  rw [slope_def_field, slope_def_field, hf0, hg0, sub_zero, sub_zero, sub_zero]
  exact div_div_div_cancel_right₀ ht0 _ _

/-- Exemplo medido: `(eᵗ − 1)/t → 1`. -/
theorem exp_sub_one_div_mede :
    Tendsto (fun t => (Real.exp t - 1) / t) (𝓝[≠] 0) (𝓝 1) := by
  have hf : HasDerivAt (fun t => Real.exp t - 1) 1 0 := by
    simpa using (Real.hasDerivAt_exp 0).sub_const 1
  have := lhopital_mede (f := fun t => Real.exp t - 1) (g := id) (by simp) rfl hf
    (hasDerivAt_id 0) one_ne_zero
  simpa using this

/-- **`0⁰` mede a multiplicidade**: para `t ∈ (0,1)`, `(tᵐ)^(c/(−log t)) = e^(−mc)` exatamente. -/
theorem zero_pow_zero_mede (m : ℕ) (c : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (t ^ m) ^ (c / -Real.log t) = Real.exp (-(m * c)) := by
  have hlog : Real.log t ≠ 0 := ne_of_lt (Real.log_neg ht0 ht1)
  rw [Real.rpow_def_of_pos (pow_pos ht0 m), Real.log_pow]
  congr 1
  field_simp

/-- Versão limite: a forma `0⁰` acima tende à constante `e^(−mc)`. -/
theorem zero_pow_zero_tendsto (m : ℕ) (c : ℝ) :
    Tendsto (fun t : ℝ => (t ^ m) ^ (c / -Real.log t)) (𝓝[>] 0) (𝓝 (Real.exp (-(m * c)))) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
  exact (zero_pow_zero_mede m c ht.1 ht.2).symm

/-! ## 3. A constante `I = 0 ⊘ 0` -/

/-- Reais estendidos com a constante de indeterminação `I` (= `none`). -/
abbrev RI := Option ℝ

/-- A constante `I`. -/
def I : RI := none

/-- Inclusão de ℝ. -/
def ι (x : ℝ) : RI := some x

/-- Divisão estendida: total, com `x ⊘ 0 = I`. -/
noncomputable def divI : RI → RI → RI
  | some a, some b => if b = 0 then none else some (a / b)
  | _, _ => none

/-- Soma estendida (`I` absorvente). -/
def addI : RI → RI → RI
  | some a, some b => some (a + b)
  | _, _ => none

/-- Produto estendido (`I` absorvente). -/
def mulI : RI → RI → RI
  | some a, some b => some (a * b)
  | _, _ => none

/-- **`0 ⊘ 0 = I`.** -/
theorem zero_divI_zero : divI (ι 0) (ι 0) = I := by simp [divI, ι, I]

theorem divI_of_ne {a b : ℝ} (hb : b ≠ 0) : divI (ι a) (ι b) = ι (a / b) := by
  simp [divI, ι, hb]

theorem ι_injective : Function.Injective ι := Option.some_injective ℝ

theorem I_ne_ι (x : ℝ) : I ≠ ι x := by simp [I, ι]

theorem ι_add (a b : ℝ) : ι (a + b) = addI (ι a) (ι b) := rfl

theorem ι_mul (a b : ℝ) : ι (a * b) = mulI (ι a) (ι b) := rfl

theorem mulI_I (x : RI) : mulI I x = I := by cases x <;> rfl

theorem addI_I (x : RI) : addI I x = I := by cases x <;> rfl

/-- **Sem cancelamento**: `I·D = I·0` para todo `D` — nenhuma regra com `I` força `D = 0`. -/
theorem sem_cancelamento (d : ℝ) : mulI I (ι d) = mulI I (ι 0) := rfl

/-- **Incompatível com anel**: em anel `0·x = 0`; aqui `0·I = I ≠ 0`. -/
theorem nao_anel : mulI (ι 0) I ≠ ι 0 := by
  unfold mulI ι I; simp

/-- Hipótese de Riemann enunciada na extensão com `I` (zeros lidos via `ι`). -/
def RiemannHypothesisI : Prop :=
  ∀ s : ℂ, (some (riemannZeta s) : Option ℂ) = some 0 →
    (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2

/-- **A constante `I` não move nenhum zero**: RH na extensão é exatamente RH. -/
theorem RH_I_iff : RiemannHypothesisI ↔ RiemannHypothesis := by
  constructor
  · intro h s hs htriv hs1
    exact h s (congrArg some hs) htriv hs1
  · intro h s hs htriv hs1
    exact h s (Option.some_injective _ hs) htriv hs1

/-! ## 4. Lógica de 4 estados (Belnap–Dunn) -/

/-- Estado de evidência: (positiva, negativa). -/
structure Quatro where
  pos : Bool
  neg : Bool
  deriving DecidableEq, Repr

namespace Quatro

def T : Quatro := ⟨true, false⟩
def F : Quatro := ⟨false, true⟩
def B : Quatro := ⟨true, true⟩
def N : Quatro := ⟨false, false⟩

/-- Negação troca as componentes. -/
def nao (s : Quatro) : Quatro := ⟨s.neg, s.pos⟩

/-- Acúmulo de evidência. -/
def junta (s r : Quatro) : Quatro := ⟨s.pos || r.pos, s.neg || r.neg⟩

/-- Designado = tem evidência positiva. -/
def designado (s : Quatro) : Prop := s.pos = true

instance : DecidablePred designado := fun s => inferInstanceAs (Decidable (s.pos = true))

theorem nao_B : nao B = B := rfl
theorem nao_N : nao N = N := rfl
theorem nao_T : nao T = F := rfl
theorem nao_nao (s : Quatro) : nao (nao s) = s := rfl

theorem junta_comm (s r : Quatro) : junta s r = junta r s := by
  cases s; cases r; simp [junta, Bool.or_comm]

theorem junta_assoc (s r u : Quatro) : junta (junta s r) u = junta s (junta r u) := by
  cases s; cases r; cases u; simp [junta, Bool.or_assoc]

theorem junta_idem (s : Quatro) : junta s s = s := by
  cases s; simp [junta]

/-- **Sem explosão**: `P` e `¬P` designados (estado `B`) não tornam `Q` designado. -/
theorem nao_explode : ∃ p q : Quatro, designado p ∧ designado (nao p) ∧ ¬ designado q :=
  ⟨B, F, rfl, rfl, by decide⟩

end Quatro

/-! ## 5. Certificado de fechamento -/

/-- Um certificado de `P` contém uma prova de `P` (nada mais, nada menos). -/
structure Certificado (P : Prop) : Prop where
  prova : P

/-- Fechamento certificado. -/
def ClosedMath (P : Prop) : Prop := Certificado P

/-- **`ClosedMath P ↔ P`**: fechar é provar. -/
theorem closedMath_iff (P : Prop) : ClosedMath P ↔ P :=
  ⟨fun h => h.prova, fun h => ⟨h⟩⟩

/-- Fechado e refutado ao mesmo tempo é impossível (no nível de prova). -/
theorem closed_e_refutado_impossivel (P : Prop) : ¬ (ClosedMath P ∧ ClosedMath (¬ P)) :=
  fun ⟨h1, h2⟩ => h2.prova h1.prova

/-- A flag booleana `CLOSED_MATH := !false`. -/
def flagClosedMath : Bool := !false

/-- **Flag não é prova**: a flag vale `true`, e mesmo assim `False` não está fechado. -/
theorem flag_nao_e_prova : flagClosedMath = true ∧ ¬ ClosedMath False :=
  ⟨rfl, fun h => h.prova⟩

/-! ## 6. Rota de Riemann: o que o kernel fecha e o que não -/

/-- Melhor coeficiente para um gerador: `E(c) = 1 − 2bc + ac²` com `a > 0`. -/
theorem um_gerador_quadrado {a b : ℝ} (ha : 0 < a) (c : ℝ) :
    1 - 2 * b * c + a * c ^ 2 = (1 - b ^ 2 / a) + a * (c - b / a) ^ 2 := by
  field_simp
  ring

theorem um_gerador_otimo {a b : ℝ} (ha : 0 < a) (c : ℝ) :
    1 - 2 * b * (b / a) + a * (b / a) ^ 2 ≤ 1 - 2 * b * c + a * c ^ 2 := by
  rw [um_gerador_quadrado ha c, um_gerador_quadrado ha (b / a), sub_self]
  have : 0 ≤ a * (c - b / a) ^ 2 := mul_nonneg ha.le (sq_nonneg _)
  nlinarith

/-- Majorante logarítmico ⇒ limite zero (para qualquer sequência não negativa). -/
theorem log_majorante_tendsto {D : ℕ → ℝ} (h0 : ∀ N, 0 ≤ D N)
    (h : ∃ K : ℝ, ∀ N : ℕ, D N ≤ K / Real.log ((N : ℝ) + 2)) : Tendsto D atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := h
  have hlog : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 2)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_nhds.div_atTop hlog) h0 hK

/-- Sequência-teste: decrescente e positiva, com limite `1/2`. -/
noncomputable def Dteste (N : ℕ) : ℝ := 1 / 2 + 1 / (2 * ((N : ℝ) + 1))

/-- **Monotonicidade não basta**: `Dteste` é antítona e não negativa, mas não tende a 0 e não
admite majorante `K / log(N+2)`. -/
theorem monotona_nao_basta :
    Antitone Dteste ∧ (∀ N, 0 ≤ Dteste N) ∧ ¬ Tendsto Dteste atTop (𝓝 0) ∧
      ¬ ∃ K : ℝ, ∀ N : ℕ, Dteste N ≤ K / Real.log ((N : ℝ) + 2) := by
  have hge : ∀ N, (1 : ℝ) / 2 ≤ Dteste N := fun N => by
    unfold Dteste; have : 0 ≤ 1 / (2 * ((N : ℝ) + 1)) := by positivity
    linarith
  have hnt : ¬ Tendsto Dteste atTop (𝓝 0) := fun ht => by
    have := ge_of_tendsto' ht hge; norm_num at this
  refine ⟨?_, fun N => le_trans (by norm_num) (hge N), hnt, ?_⟩
  · intro m n hmn
    unfold Dteste
    have hm : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have h1 : (0 : ℝ) < 2 * ((m : ℝ) + 1) := by positivity
    have h2 : 2 * ((m : ℝ) + 1) ≤ 2 * ((n : ℝ) + 1) := by linarith
    have := one_div_le_one_div_of_le h1 h2
    linarith
  · intro hK
    exact hnt (log_majorante_tendsto (fun N => le_trans (by norm_num) (hge N)) hK)

end ATK.Indeterminacy

#print axioms ATK.Indeterminacy.Ponto.germe_mul
#print axioms ATK.Indeterminacy.Ponto.germe_div
#print axioms ATK.Indeterminacy.Ponto.germe_inv
#print axioms ATK.Indeterminacy.Ponto.mul_inv_eq_um
#print axioms ATK.Indeterminacy.Ponto.estado_div_zero_iff
#print axioms ATK.Indeterminacy.Ponto.estado_div_finito_iff
#print axioms ATK.Indeterminacy.Ponto.estado_div_infinito_iff
#print axioms ATK.Indeterminacy.Ponto.estadoOrdem_zero_iff
#print axioms ATK.Indeterminacy.Ponto.estadoOrdem_finito_iff
#print axioms ATK.Indeterminacy.Ponto.estadoOrdem_infinito_iff
#print axioms ATK.Indeterminacy.Ponto.estado_inv_infinito_iff
#print axioms ATK.Indeterminacy.Ponto.estado_inv_zero_iff
#print axioms ATK.Indeterminacy.Ponto.estado_inv_finito_iff
#print axioms ATK.Indeterminacy.Ponto.medida_finita
#print axioms ATK.Indeterminacy.Ponto.estado_zero_tendsto
#print axioms ATK.Indeterminacy.Ponto.estado_infinito_tendsto
#print axioms ATK.Indeterminacy.zero_div_zero_tres_estados
#print axioms ATK.Indeterminacy.inf_div_inf_tres_estados
#print axioms ATK.Indeterminacy.zero_div_zero_qualquer_valor
#print axioms ATK.Indeterminacy.limite_perde_ordem
#print axioms ATK.Indeterminacy.lhopital_mede
#print axioms ATK.Indeterminacy.exp_sub_one_div_mede
#print axioms ATK.Indeterminacy.zero_pow_zero_mede
#print axioms ATK.Indeterminacy.zero_pow_zero_tendsto
#print axioms ATK.Indeterminacy.zero_divI_zero
#print axioms ATK.Indeterminacy.divI_of_ne
#print axioms ATK.Indeterminacy.ι_injective
#print axioms ATK.Indeterminacy.I_ne_ι
#print axioms ATK.Indeterminacy.ι_add
#print axioms ATK.Indeterminacy.ι_mul
#print axioms ATK.Indeterminacy.mulI_I
#print axioms ATK.Indeterminacy.addI_I
#print axioms ATK.Indeterminacy.sem_cancelamento
#print axioms ATK.Indeterminacy.nao_anel
#print axioms ATK.Indeterminacy.RH_I_iff
#print axioms ATK.Indeterminacy.Quatro.nao_B
#print axioms ATK.Indeterminacy.Quatro.nao_N
#print axioms ATK.Indeterminacy.Quatro.nao_T
#print axioms ATK.Indeterminacy.Quatro.nao_nao
#print axioms ATK.Indeterminacy.Quatro.junta_comm
#print axioms ATK.Indeterminacy.Quatro.junta_assoc
#print axioms ATK.Indeterminacy.Quatro.junta_idem
#print axioms ATK.Indeterminacy.Quatro.nao_explode
#print axioms ATK.Indeterminacy.closedMath_iff
#print axioms ATK.Indeterminacy.closed_e_refutado_impossivel
#print axioms ATK.Indeterminacy.flag_nao_e_prova
#print axioms ATK.Indeterminacy.um_gerador_quadrado
#print axioms ATK.Indeterminacy.um_gerador_otimo
#print axioms ATK.Indeterminacy.log_majorante_tendsto
#print axioms ATK.Indeterminacy.monotona_nao_basta
