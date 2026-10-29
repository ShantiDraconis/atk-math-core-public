import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# ATK — Geometria de `I`: início fechado e fim fechado tendendo ao mesmo meio

Modelo canônico (reconstruído do acervo): o segmento `[0, 1]`, extremos fechados `0` e `1`, o
**neutro** `1/2`.

* **tensão** `ρ(x) = 1 − x`: involução cujo único ponto fixo é o neutro; troca as metades
  meio-fechadas `[0, 1/2)` e `(1/2, 1]`, cujos fechos só se tocam no neutro;
* **compressão** `D_λ(x) = 1/2 + λ(x − 1/2)`: fixa o neutro, compõe multiplicativamente, comuta com a
  tensão; iterada com `|λ| < 1` converge ao neutro; com `|λ| > 1` (tração) afasta-se dele;
* **torção** (no plano) `R_θ(s) = 1/2 + e^{iθ}(s − 1/2)`: rotação em torno do neutro, `R_π` é a
  tensão;
* **rigidez do neutro**: toda aplicação que comuta com a tensão fixa `1/2`;
* **o processo**: intervalos fechados `[1/2 − 1/(n+1), 1/2]` (início fechado) e
  `[1/2, 1/2 + 1/(n+1)]` (fim fechado) convergem ao **mesmo** ponto `{1/2}`; os meio-abertos
  `[1/2 − 1/(n+1), 1/2)` convergem ao **vazio** — o neutro só é alcançado pelo fechado;
* **conjugações**: `x ↦ 1 − x` em `[0,1]` ≅ `u ↦ −u` (neutro 0) ≅ `y ↦ 1/y` em `(0, ∞)` (neutro 1);
* **lógica K3** com estado neutro `N`: `N` é o único ponto fixo da negação, vale De Morgan e a lei
  de Kleene, o terceiro excluído falha exatamente em `N`, e `K3 ↪ [0,1]` leva `N ↦ 1/2`,
  negação ↦ tensão.
-/

open Set Filter Topology

namespace ATK.IGeometria

/-! ## Tensão e compressão em `ℝ` -/

/-- Tensão. -/
def ρ (x : ℝ) : ℝ := 1 - x

/-- Compressão (`|λ| < 1`) ou tração (`|λ| > 1`) em direção ao neutro. -/
noncomputable def D (l x : ℝ) : ℝ := 1 / 2 + l * (x - 1 / 2)

theorem rho_rho (x : ℝ) : ρ (ρ x) = x := by unfold ρ; ring

theorem rho_fixo_iff (x : ℝ) : ρ x = x ↔ x = 1 / 2 := by
  unfold ρ; constructor <;> intro h <;> linarith

theorem rho_Icc : ρ '' Icc 0 1 = Icc 0 1 := by
  ext y
  simp only [mem_image, mem_Icc, ρ]
  constructor
  · rintro ⟨x, ⟨h0, h1⟩, rfl⟩; constructor <;> linarith
  · rintro ⟨h0, h1⟩; exact ⟨1 - y, ⟨by linarith, by linarith⟩, by ring⟩

/-- A tensão troca as duas metades meio-fechadas. -/
theorem rho_troca_metades : ρ '' Ico 0 (1 / 2) = Ioc (1 / 2) 1 := by
  ext y
  simp only [mem_image, mem_Ico, mem_Ioc, ρ]
  constructor
  · rintro ⟨x, ⟨h0, h1⟩, rfl⟩; constructor <;> linarith
  · rintro ⟨h0, h1⟩; exact ⟨1 - y, ⟨by linarith, by linarith⟩, by ring⟩

theorem metades_disjuntas : Ico (0 : ℝ) (1 / 2) ∩ Ioc (1 / 2) 1 = ∅ := by
  ext x; simp only [mem_inter_iff, mem_Ico, mem_Ioc, mem_empty_iff_false, iff_false]
  rintro ⟨⟨_, h1⟩, h2, _⟩; linarith

theorem metades_uniao : Ico (0 : ℝ) (1 / 2) ∪ {1 / 2} ∪ Ioc (1 / 2) 1 = Icc 0 1 := by
  ext x
  simp only [mem_union, mem_Ico, mem_singleton_iff, mem_Ioc, mem_Icc]
  constructor
  · rintro ((⟨h0, h1⟩ | h) | ⟨h0, h1⟩)
    · constructor <;> linarith
    · subst h; constructor <;> norm_num
    · constructor <;> linarith
  · rintro ⟨h0, h1⟩
    rcases lt_trichotomy x (1 / 2) with h | h | h
    · exact Or.inl (Or.inl ⟨h0, h⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨h, h1⟩

/-- Os fechos das duas metades só se tocam no neutro. -/
theorem fechos_metades : closure (Ico (0 : ℝ) (1 / 2)) ∩ closure (Ioc (1 / 2) 1) = {1 / 2} := by
  rw [closure_Ico (by norm_num), closure_Ioc (by norm_num)]
  ext x
  simp only [mem_inter_iff, mem_Icc, mem_singleton_iff]
  constructor
  · rintro ⟨⟨_, h1⟩, h2, _⟩; linarith
  · rintro rfl; norm_num

theorem D_neutro (l : ℝ) : D l (1 / 2) = 1 / 2 := by unfold D; ring

theorem D_comp (l m x : ℝ) : D l (D m x) = D (l * m) x := by unfold D; ring

theorem D_rho (l x : ℝ) : D l (ρ x) = ρ (D l x) := by unfold D ρ; ring

/-- O neutro é o único ponto fixo comum de todas as compressões. -/
theorem fixo_comum_iff (x : ℝ) : (∀ l, D l x = x) ↔ x = 1 / 2 := by
  constructor
  · intro h; have := h 0; unfold D at this; linarith
  · rintro rfl l; exact D_neutro l

/-- **Rigidez do neutro**: quem comuta com a tensão fixa `1/2`. -/
theorem rigidez_neutro (f : ℝ → ℝ) (hf : ∀ x, f (ρ x) = ρ (f x)) : f (1 / 2) = 1 / 2 := by
  have h := hf (1 / 2)
  rw [show ρ (1 / 2) = 1 / 2 by unfold ρ; norm_num] at h
  exact (rho_fixo_iff _).mp h.symm

theorem D_iterate (l x : ℝ) (n : ℕ) : (D l)^[n] x = 1 / 2 + l ^ n * (x - 1 / 2) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih]; unfold D; ring

/-- **Compressão iterada converge ao neutro** (`|λ| < 1`). -/
theorem compressao_converge {l : ℝ} (hl : |l| < 1) (x : ℝ) :
    Tendsto (fun n => (D l)^[n] x) atTop (𝓝 (1 / 2)) := by
  simp only [D_iterate]
  have h := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hl).mul_const (x - 1 / 2)
  simpa using h.const_add (1 / 2 : ℝ)

/-- **Tração iterada afasta do neutro** (`|λ| > 1`, `x ≠ 1/2`). -/
theorem tracao_diverge {l : ℝ} (hl : 1 < |l|) {x : ℝ} (hx : x ≠ 1 / 2) :
    Tendsto (fun n => |(D l)^[n] x - 1 / 2|) atTop atTop := by
  have hpos : 0 < |x - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hx)
  have e : (fun n => |(D l)^[n] x - 1 / 2|) = fun n => |l| ^ n * |x - 1 / 2| := by
    funext n; rw [D_iterate, add_sub_cancel_left, abs_mul, abs_pow]
  rw [e]
  exact (tendsto_pow_atTop_atTop_of_one_lt hl).atTop_mul_const hpos

/-! ## O processo: fechados → neutro, meio-abertos → vazio -/

theorem inv_succ_pos (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity

/-- Se `0 ≤ d ≤ 1/(n+1)` para todo `n`, então `d = 0`. -/
theorem zero_de_cotas {d : ℝ} (h0 : 0 ≤ d) (h : ∀ n : ℕ, d ≤ 1 / ((n : ℝ) + 1)) : d = 0 := by
  by_contra hne
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_of_le_of_ne h0 (Ne.symm hne))
  exact absurd (h n) (not_le.mpr hn)

/-- **Compressão por fechados simétricos**: `⋂ [1/2 − 1/(n+1), 1/2 + 1/(n+1)] = {1/2}`. -/
theorem fechados_encaixados :
    ⋂ n : ℕ, Icc (1 / 2 - 1 / ((n : ℝ) + 1)) (1 / 2 + 1 / ((n : ℝ) + 1)) = {1 / 2} := by
  ext x
  simp only [mem_iInter, mem_Icc, mem_singleton_iff]
  constructor
  · intro h
    have := zero_de_cotas (abs_nonneg (x - 1 / 2)) fun n => by
      rw [abs_le]; constructor <;> linarith [(h n).1, (h n).2]
    have := abs_eq_zero.mp this
    linarith
  · rintro rfl n; constructor <;> linarith [inv_succ_pos n]

/-- **Início fechado → meio**: `⋂ [1/2 − 1/(n+1), 1/2] = {1/2}`. -/
theorem inicio_fechado_meio : ⋂ n : ℕ, Icc (1 / 2 - 1 / ((n : ℝ) + 1)) (1 / 2) = {1 / 2} := by
  ext x
  simp only [mem_iInter, mem_Icc, mem_singleton_iff]
  constructor
  · intro h
    have hx : x ≤ 1 / 2 := (h 0).2
    have := zero_de_cotas (d := 1 / 2 - x) (by linarith) fun n => by linarith [(h n).1]
    linarith
  · rintro rfl n; constructor <;> linarith [inv_succ_pos n]

/-- **Fim fechado → o mesmo meio**: `⋂ [1/2, 1/2 + 1/(n+1)] = {1/2}`. -/
theorem fim_fechado_meio : ⋂ n : ℕ, Icc (1 / 2) (1 / 2 + 1 / ((n : ℝ) + 1)) = {1 / 2} := by
  ext x
  simp only [mem_iInter, mem_Icc, mem_singleton_iff]
  constructor
  · intro h
    have hx : 1 / 2 ≤ x := (h 0).1
    have := zero_de_cotas (d := x - 1 / 2) (by linarith) fun n => by linarith [(h n).2]
    linarith
  · rintro rfl n; constructor <;> linarith [inv_succ_pos n]

/-- **Meio aberto não alcança o neutro**: `⋂ [1/2 − 1/(n+1), 1/2) = ∅`. -/
theorem meio_aberto_esquerda : ⋂ n : ℕ, Ico (1 / 2 - 1 / ((n : ℝ) + 1)) (1 / 2) = ∅ := by
  ext x
  simp only [mem_iInter, mem_Ico, mem_empty_iff_false, iff_false]
  intro h
  have hx : x < 1 / 2 := (h 0).2
  have := zero_de_cotas (d := 1 / 2 - x) (by linarith) fun n => by linarith [(h n).1]
  linarith

theorem meio_aberto_direita : ⋂ n : ℕ, Ioc (1 / 2) (1 / 2 + 1 / ((n : ℝ) + 1)) = ∅ := by
  ext x
  simp only [mem_iInter, mem_Ioc, mem_empty_iff_false, iff_false]
  intro h
  have hx : 1 / 2 < x := (h 0).1
  have := zero_de_cotas (d := x - 1 / 2) (by linarith) fun n => by linarith [(h n).2]
  linarith

/-! ## Torção no plano -/

/-- Torção: rotação de ângulo `θ` em torno do neutro `1/2`. -/
noncomputable def R (θ : ℝ) (s : ℂ) : ℂ := 1 / 2 + Complex.exp (θ * Complex.I) * (s - 1 / 2)

theorem R_neutro (θ : ℝ) : R θ (1 / 2) = 1 / 2 := by unfold R; ring

theorem R_comp (θ φ : ℝ) (s : ℂ) : R θ (R φ s) = R (θ + φ) s := by
  unfold R
  push_cast
  rw [add_mul, Complex.exp_add]
  ring

theorem R_zero (s : ℂ) : R 0 s = s := by unfold R; simp

/-- **Meia volta = tensão**: `R_π(s) = 1 − s`. -/
theorem R_pi (s : ℂ) : R Real.pi s = 1 - s := by
  unfold R
  rw [Complex.exp_pi_mul_I]
  ring

/-! ## Conjugações (a mesma involução em três cartas) -/

/-- Carta afim `u = 2x − 1`: a tensão vira negação. -/
theorem conj_afim (x : ℝ) : 2 * ρ x - 1 = -(2 * x - 1) := by unfold ρ; ring

/-- Carta logarítmica: `y ↦ 1/y` em `(0, ∞)` vira `u ↦ −u`. -/
theorem conj_log (y : ℝ) : Real.log y⁻¹ = -Real.log y := Real.log_inv y

/-- O neutro de `y ↦ 1/y` em `(0, ∞)` é `1`. -/
theorem inv_fixo_iff {y : ℝ} (hy : 0 < y) : y⁻¹ = y ↔ y = 1 := by
  constructor
  · intro h
    have h2 : y * y = 1 := by
      calc y * y = y * y⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel₀ hy.ne'
    nlinarith
  · rintro rfl; simp


/-! ## O medidor de torção `𝕋(x) = |x − 1/2| / |x + 1/2|` (acervo: "torque") -/

/-- Medidor de torção: `1` nos extremos `0` e `∞`, `0` no neutro. -/
noncomputable def T (x : ℝ) : ℝ := |x - 1 / 2| / |x + 1 / 2|

theorem T_neutro : T (1 / 2) = 0 := by unfold T; norm_num

theorem T_zero : T 0 = 1 := by unfold T; norm_num

theorem T_lt_one {x : ℝ} (hx : 0 < x) : T x < 1 := by
  unfold T
  have hp : 0 < x + 1 / 2 := by linarith
  rw [abs_of_pos hp, div_lt_one hp, abs_sub_lt_iff]
  constructor <;> linarith

theorem T_eq_zero_iff {x : ℝ} (hx : 0 ≤ x) : T x = 0 ↔ x = 1 / 2 := by
  unfold T
  have hp : 0 < x + 1 / 2 := by linarith
  rw [div_eq_zero_iff, abs_eq_zero, abs_eq_zero]
  constructor
  · rintro (h | h)
    · linarith
    · linarith
  · intro h; left; linarith

/-- **Simetria de inversão**: `𝕋(1/(4x)) = 𝕋(x)` — a inversão `x ↦ 1/(4x)` troca o início `0` e o
fim `∞` e fixa o neutro. -/
theorem T_inversao {x : ℝ} (hx : 0 < x) : T (1 / (4 * x)) = T x := by
  unfold T
  have hx' := hx.ne'
  have e1 : 1 / (4 * x) - 1 / 2 = -(x - 1 / 2) / (2 * x) := by field_simp; ring
  have e2 : 1 / (4 * x) + 1 / 2 = (x + 1 / 2) / (2 * x) := by field_simp; ring
  have h2 : 0 < 2 * x := by linarith
  have hp : 0 < x + 1 / 2 := by linarith
  rw [e1, e2, abs_div, abs_div, abs_neg, abs_of_pos h2, abs_of_pos hp]
  field_simp

theorem inversao_fixo_iff {x : ℝ} (hx : 0 < x) : 1 / (4 * x) = x ↔ x = 1 / 2 := by
  have hx' := hx.ne'
  constructor
  · intro h
    have h2 : 4 * x * x = 1 := by field_simp at h; linarith
    nlinarith
  · rintro rfl; norm_num

theorem T_tendsto_um : Tendsto T atTop (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => 1 - (x + 1 / 2)⁻¹) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_id))
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 / 2 : ℝ)] with x hx
  unfold T
  have hp : 0 < x + 1 / 2 := by linarith
  rw [abs_of_pos (by linarith : (0 : ℝ) < x - 1 / 2), abs_of_pos hp]
  field_simp
  ring

/-- Refutação da faixa alegada em toda a reta: `𝕋(−1) = 3`. -/
theorem T_menos_um : T (-1) = 3 := by unfold T; norm_num

/-- **No plano**: torção `< 1` ⟺ semiplano direito; o início fechado `Re z = 0` tem torção `1`. -/
theorem torcao_plano (z : ℂ) : ‖z - 1 / 2‖ < ‖z + 1 / 2‖ ↔ 0 < z.re := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp
  constructor <;> intro h <;> nlinarith

/-! ## Lógica K3 com estado neutro -/

/-- Valores de Kleene: falso, **neutro**, verdadeiro. -/
inductive K3
  | F
  | N
  | T
  deriving DecidableEq, Repr

namespace K3

def neg : K3 → K3
  | F => T
  | N => N
  | T => F

def e : K3 → K3 → K3
  | F, _ => F
  | _, F => F
  | N, _ => N
  | _, N => N
  | T, T => T

def ou : K3 → K3 → K3
  | T, _ => T
  | _, T => T
  | N, _ => N
  | _, N => N
  | F, F => F

/-- Ordem de verdade `F < N < T`. -/
def nivel : K3 → ℕ
  | F => 0
  | N => 1
  | T => 2

/-- Mergulho em `[0, 1]`. -/
noncomputable def val : K3 → ℝ
  | F => 0
  | N => 1 / 2
  | T => 1

theorem neg_neg (a : K3) : neg (neg a) = a := by cases a <;> rfl

/-- **O neutro é o único ponto fixo da negação.** -/
theorem neg_fixo_iff (a : K3) : neg a = a ↔ a = N := by cases a <;> simp [neg]

theorem de_morgan_e (a b : K3) : neg (e a b) = ou (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

theorem de_morgan_ou (a b : K3) : neg (ou a b) = e (neg a) (neg b) := by
  cases a <;> cases b <;> rfl

theorem e_comm (a b : K3) : e a b = e b a := by cases a <;> cases b <;> rfl

theorem ou_comm (a b : K3) : ou a b = ou b a := by cases a <;> cases b <;> rfl

theorem e_assoc (a b c : K3) : e (e a b) c = e a (e b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem ou_assoc (a b c : K3) : ou (ou a b) c = ou a (ou b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem e_ou_distrib (a b c : K3) : e a (ou b c) = ou (e a b) (e a c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- **Lei de Kleene**: `a ∧ ¬a ≤ b ∨ ¬b`. -/
theorem kleene (a b : K3) : nivel (e a (neg a)) ≤ nivel (ou b (neg b)) := by
  cases a <;> cases b <;> decide

/-- **O terceiro excluído falha exatamente no neutro.** -/
theorem terceiro_excluido_iff (a : K3) : ou a (neg a) = T ↔ a ≠ N := by
  cases a <;> simp [ou, neg]

/-- O neutro é fechado pelos conectivos (por isso K3 não tem tautologias). -/
theorem neutro_fechado : neg N = N ∧ e N N = N ∧ ou N N = N := ⟨rfl, rfl, rfl⟩

/-- Em K3 (designado `{T}`), `a ∧ ¬a` nunca é designado: a explosão vale. -/
theorem K3_explosao (a : K3) : e a (neg a) ≠ T := by cases a <;> decide

/-- Em LP (designados `{T, N}`), `N ∧ ¬N` é designado mas `F` não: LP **não** explode. -/
theorem LP_nao_explosivo : e N (neg N) ≠ F ∧ ¬ (F ≠ F) := ⟨by decide, fun h => h rfl⟩

theorem val_neg (a : K3) : val (neg a) = ρ (val a) := by
  cases a <;> norm_num [val, neg, ρ]

theorem val_e (a b : K3) : val (e a b) = min (val a) (val b) := by
  cases a <;> cases b <;> norm_num [val, e]

theorem val_ou (a b : K3) : val (ou a b) = max (val a) (val b) := by
  cases a <;> cases b <;> norm_num [val, ou]

/-- **O neutro lógico é o neutro geométrico.** -/
theorem val_N : val N = 1 / 2 := rfl

end K3

end ATK.IGeometria

#print axioms ATK.IGeometria.rho_rho
#print axioms ATK.IGeometria.rho_fixo_iff
#print axioms ATK.IGeometria.rho_Icc
#print axioms ATK.IGeometria.rho_troca_metades
#print axioms ATK.IGeometria.metades_disjuntas
#print axioms ATK.IGeometria.metades_uniao
#print axioms ATK.IGeometria.fechos_metades
#print axioms ATK.IGeometria.D_neutro
#print axioms ATK.IGeometria.D_comp
#print axioms ATK.IGeometria.D_rho
#print axioms ATK.IGeometria.fixo_comum_iff
#print axioms ATK.IGeometria.rigidez_neutro
#print axioms ATK.IGeometria.D_iterate
#print axioms ATK.IGeometria.compressao_converge
#print axioms ATK.IGeometria.tracao_diverge
#print axioms ATK.IGeometria.inv_succ_pos
#print axioms ATK.IGeometria.zero_de_cotas
#print axioms ATK.IGeometria.fechados_encaixados
#print axioms ATK.IGeometria.inicio_fechado_meio
#print axioms ATK.IGeometria.fim_fechado_meio
#print axioms ATK.IGeometria.meio_aberto_esquerda
#print axioms ATK.IGeometria.meio_aberto_direita
#print axioms ATK.IGeometria.R_neutro
#print axioms ATK.IGeometria.R_comp
#print axioms ATK.IGeometria.R_zero
#print axioms ATK.IGeometria.R_pi
#print axioms ATK.IGeometria.conj_afim
#print axioms ATK.IGeometria.conj_log
#print axioms ATK.IGeometria.inv_fixo_iff
#print axioms ATK.IGeometria.T_neutro
#print axioms ATK.IGeometria.T_zero
#print axioms ATK.IGeometria.T_lt_one
#print axioms ATK.IGeometria.T_eq_zero_iff
#print axioms ATK.IGeometria.T_inversao
#print axioms ATK.IGeometria.inversao_fixo_iff
#print axioms ATK.IGeometria.T_tendsto_um
#print axioms ATK.IGeometria.T_menos_um
#print axioms ATK.IGeometria.torcao_plano
#print axioms ATK.IGeometria.K3.neg_neg
#print axioms ATK.IGeometria.K3.neg_fixo_iff
#print axioms ATK.IGeometria.K3.de_morgan_e
#print axioms ATK.IGeometria.K3.de_morgan_ou
#print axioms ATK.IGeometria.K3.e_comm
#print axioms ATK.IGeometria.K3.ou_comm
#print axioms ATK.IGeometria.K3.e_assoc
#print axioms ATK.IGeometria.K3.ou_assoc
#print axioms ATK.IGeometria.K3.e_ou_distrib
#print axioms ATK.IGeometria.K3.kleene
#print axioms ATK.IGeometria.K3.terceiro_excluido_iff
#print axioms ATK.IGeometria.K3.neutro_fechado
#print axioms ATK.IGeometria.K3.K3_explosao
#print axioms ATK.IGeometria.K3.LP_nao_explosivo
#print axioms ATK.IGeometria.K3.val_neg
#print axioms ATK.IGeometria.K3.val_e
#print axioms ATK.IGeometria.K3.val_ou
#print axioms ATK.IGeometria.K3.val_N
