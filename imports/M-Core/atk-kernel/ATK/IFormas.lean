import ATK.IndeterminacyStates
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# ATK — O conjunto `I` materializado: as sete formas indeterminadas e seus conjuntos de valores

Para cada forma clássica, o **conjunto de valores** é o conjunto dos limites (em `[−∞, +∞]`)
atingíveis por pares de funções com os comportamentos prescritos quando `t → 0⁺`:

| forma | conjunto de valores (provado) |
|---|---|
| `0/0`, `0·∞`, `∞ − ∞` | `[−∞, +∞]` inteiro |
| `∞/∞`, `1^∞`, `0^0`, `∞^0` | `[0, +∞]` |

Cada uma também realiza o estado `oscila` (sem limite). Uma forma é **indeterminada** quando seu
conjunto de valores tem mais de um ponto; as sete são indeterminadas. Contraste (formas
**determinadas**, conjunto unitário): `a + b`, `∞ + ∞ = ∞`, `∞·∞ = ∞`, `a/∞ = 0`, `0^∞ = 0`.

Este é o conteúdo rigoroso de "I = conjunto dos números indeterminados": cada forma indeterminada
é um ponto de `I`, e o seu "valor" é um conjunto, não um número. As afirmações do acervo
"`lim x/x = I`" e "todo limite `0/0` é `I`" são **falsas** (`x/x → 1`: forma determinada após
simplificar); a afirmação "0/0 pode valer qualquer coisa" é **verdadeira** e está provada aqui.
-/

open Filter Topology Set Real

namespace ATK.IFormas

open ATK.IndeterminacyStates

/-- O limite `t → 0⁺`. -/
abbrev l0 : Filter ℝ := 𝓝[>] (0 : ℝ)

/-- Conjunto de valores de `op (f, g)` quando `f → F`, `g → G` (com a restrição `R`). -/
def Valores (F G : Filter ℝ) (R : ℝ → ℝ → Prop) (op : ℝ → ℝ → ℝ) : Set EReal :=
  {L | ∃ f g : ℝ → ℝ, Tendsto f l0 F ∧ Tendsto g l0 G ∧ (∀ᶠ t in l0, R (f t) (g t)) ∧
    Tendsto (fun t => ((op (f t) (g t) : ℝ) : EReal)) l0 (𝓝 L)}

/-- A forma também realiza o estado `oscila`. -/
def Oscila (F G : Filter ℝ) (R : ℝ → ℝ → Prop) (op : ℝ → ℝ → ℝ) : Prop :=
  ∃ f g : ℝ → ℝ, Tendsto f l0 F ∧ Tendsto g l0 G ∧ (∀ᶠ t in l0, R (f t) (g t)) ∧
    Comporta l0 (fun t => op (f t) (g t)) Estado7.oscila

/-- Uma forma é **indeterminada** quando seu conjunto de valores tem mais de um ponto. -/
def Indeterminada (V : Set EReal) : Prop := ¬ V.Subsingleton

/-! ## As sete formas -/

def div00 : Set EReal := Valores (𝓝 0) (𝓝 0) (fun _ y => y ≠ 0) (fun x y => x / y)
def mul0Inf : Set EReal := Valores (𝓝 0) atTop (fun _ _ => True) (fun x y => x * y)
def subInf : Set EReal := Valores atTop atTop (fun _ _ => True) (fun x y => x - y)
def divInf : Set EReal := Valores atTop atTop (fun _ _ => True) (fun x y => x / y)
def pow1Inf : Set EReal := Valores (𝓝 1) atTop (fun x _ => 0 < x) (fun x y => x ^ y)
def pow00 : Set EReal := Valores (𝓝 0) (𝓝 0) (fun x _ => 0 < x) (fun x y => x ^ y)
def powInf0 : Set EReal := Valores atTop (𝓝 0) (fun _ _ => True) (fun x y => x ^ y)

/-! ## Ferramentas -/

theorem ev_pos : ∀ᶠ t in l0, 0 < t := self_mem_nhdsWithin

theorem t_id : Tendsto (fun t : ℝ => t) l0 (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds

theorem t_inv : Tendsto (fun t : ℝ => t⁻¹) l0 atTop := tendsto_inv_nhdsGT_zero

theorem t_inv2 : Tendsto (fun t : ℝ => t⁻¹ * t⁻¹) l0 atTop := t_inv.atTop_mul_atTop₀ t_inv

theorem t_neg_inv : Tendsto (fun t : ℝ => -t⁻¹) l0 atBot := tendsto_neg_atTop_atBot.comp t_inv

theorem exp_rpow (a b : ℝ) : (rexp a) ^ b = rexp (a * b) := (Real.exp_mul a b).symm

theorem mem_coe {F G : Filter ℝ} {R : ℝ → ℝ → Prop} {op : ℝ → ℝ → ℝ} {f g : ℝ → ℝ} {x : ℝ}
    (hf : Tendsto f l0 F) (hg : Tendsto g l0 G) (hR : ∀ᶠ t in l0, R (f t) (g t))
    (h : Tendsto (fun t => op (f t) (g t)) l0 (𝓝 x)) : (x : EReal) ∈ Valores F G R op :=
  ⟨f, g, hf, hg, hR, EReal.tendsto_coe.mpr h⟩

theorem mem_top {F G : Filter ℝ} {R : ℝ → ℝ → Prop} {op : ℝ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hf : Tendsto f l0 F) (hg : Tendsto g l0 G) (hR : ∀ᶠ t in l0, R (f t) (g t))
    (h : Tendsto (fun t => op (f t) (g t)) l0 atTop) : (⊤ : EReal) ∈ Valores F G R op :=
  ⟨f, g, hf, hg, hR, EReal.tendsto_coe_nhds_top_iff.mpr h⟩

theorem mem_bot {F G : Filter ℝ} {R : ℝ → ℝ → Prop} {op : ℝ → ℝ → ℝ} {f g : ℝ → ℝ}
    (hf : Tendsto f l0 F) (hg : Tendsto g l0 G) (hR : ∀ᶠ t in l0, R (f t) (g t))
    (h : Tendsto (fun t => op (f t) (g t)) l0 atBot) : (⊥ : EReal) ∈ Valores F G R op :=
  ⟨f, g, hf, hg, hR, EReal.tendsto_coe_nhds_bot_iff.mpr h⟩

/-- Constante eventual ⇒ limite. -/
theorem tendsto_of_ev_eq {h : ℝ → ℝ} {c : ℝ} (he : ∀ᶠ t in l0, h t = c) :
    Tendsto h l0 (𝓝 c) :=
  tendsto_const_nhds.congr' (by filter_upwards [he] with t ht; rw [ht])

/-- Valores não negativos eventualmente ⇒ conjunto de valores em `[0, +∞]`. -/
theorem sub_Ici {F G : Filter ℝ} {R : ℝ → ℝ → Prop} {op : ℝ → ℝ → ℝ}
    (hpos : ∀ f g : ℝ → ℝ, Tendsto f l0 F → Tendsto g l0 G → (∀ᶠ t in l0, R (f t) (g t)) →
      ∀ᶠ t in l0, 0 ≤ op (f t) (g t)) :
    Valores F G R op ⊆ Ici 0 := by
  rintro L ⟨f, g, hf, hg, hR, hL⟩
  show (0 : EReal) ≤ L
  refine ge_of_tendsto hL ?_
  filter_upwards [hpos f g hf hg hR] with t ht
  exact EReal.coe_nonneg.mpr ht

theorem bot_nao_Ici : (⊥ : EReal) ∉ Ici (0 : EReal) := by simp

/-! ## `0/0`, `0·∞`, `∞ − ∞`: todo valor em `[−∞, +∞]` -/

theorem div00_eq : div00 = univ := by
  refine eq_univ_of_forall fun L => ?_
  unfold div00
  cases L with
  | bot =>
    refine mem_bot (f := fun t => -t) (g := fun t => t * t) (by simpa using t_id.neg)
      (by simpa using t_id.mul t_id) ?_ (t_neg_inv.congr' ?_)
    · filter_upwards [ev_pos] with t ht; exact (mul_pos ht ht).ne'
    · filter_upwards [ev_pos] with t ht; have := ht.ne'; field_simp
  | coe x =>
    refine mem_coe (f := fun t => x * t) (g := fun t => t) (by simpa using t_id.const_mul x) t_id
      ?_ (tendsto_of_ev_eq ?_)
    · filter_upwards [ev_pos] with t ht; exact ht.ne'
    · filter_upwards [ev_pos] with t ht; have := ht.ne'; field_simp
  | top =>
    refine mem_top (f := fun t => t) (g := fun t => t * t) t_id (by simpa using t_id.mul t_id) ?_
      (t_inv.congr' ?_)
    · filter_upwards [ev_pos] with t ht; exact (mul_pos ht ht).ne'
    · filter_upwards [ev_pos] with t ht; have := ht.ne'; field_simp

theorem mul0Inf_eq : mul0Inf = univ := by
  refine eq_univ_of_forall fun L => ?_
  unfold mul0Inf
  cases L with
  | bot =>
    refine mem_bot (f := fun t => -t) (g := fun t => t⁻¹ * t⁻¹) (by simpa using t_id.neg) t_inv2
      (Eventually.of_forall fun _ => trivial) (t_neg_inv.congr' ?_)
    filter_upwards [ev_pos] with t ht; have := ht.ne'; field_simp
  | coe x =>
    refine mem_coe (f := fun t => x * t) (g := fun t => t⁻¹) (by simpa using t_id.const_mul x) t_inv
      (Eventually.of_forall fun _ => trivial) (tendsto_of_ev_eq ?_)
    filter_upwards [ev_pos] with t ht; have := ht.ne'; field_simp
  | top =>
    refine mem_top (f := fun t => t) (g := fun t => t⁻¹ * t⁻¹) t_id t_inv2
      (Eventually.of_forall fun _ => trivial) (t_inv.congr' ?_)
    filter_upwards [ev_pos] with t ht; have := ht.ne'; field_simp

theorem t_two_inv : Tendsto (fun t : ℝ => 2 * t⁻¹) l0 atTop :=
  Tendsto.const_mul_atTop (by norm_num) t_inv

theorem subInf_eq : subInf = univ := by
  refine eq_univ_of_forall fun L => ?_
  unfold subInf
  cases L with
  | bot =>
    refine mem_bot (f := fun t => t⁻¹) (g := fun t => 2 * t⁻¹) t_inv t_two_inv
      (Eventually.of_forall fun _ => trivial) (t_neg_inv.congr' (Eventually.of_forall fun t => ?_))
    ring
  | coe x =>
    refine mem_coe (f := fun t => t⁻¹ + x) (g := fun t => t⁻¹)
      (tendsto_atTop_add_const_right _ x t_inv) t_inv (Eventually.of_forall fun _ => trivial)
      (tendsto_of_ev_eq (Eventually.of_forall fun t => ?_))
    ring
  | top =>
    refine mem_top (f := fun t => 2 * t⁻¹) (g := fun t => t⁻¹) t_two_inv t_inv
      (Eventually.of_forall fun _ => trivial) (t_inv.congr' (Eventually.of_forall fun t => ?_))
    ring

/-! ## `∞/∞`, `1^∞`, `0^0`, `∞^0`: exatamente `[0, +∞]` -/

theorem divInf_eq : divInf = Ici 0 := by
  unfold divInf
  refine Subset.antisymm (sub_Ici fun f g hf hg _ => ?_) fun L hL => ?_
  · filter_upwards [hf.eventually_gt_atTop 0, hg.eventually_gt_atTop 0] with t h1 h2
    exact (div_pos h1 h2).le
  cases L with
  | bot => exact absurd hL bot_nao_Ici
  | coe x =>
    have hx : 0 ≤ x := EReal.coe_nonneg.mp hL
    refine mem_coe (f := fun t => (x + t) * (t⁻¹ * t⁻¹)) (g := fun t => t⁻¹ * t⁻¹) ?_ t_inv2
      (Eventually.of_forall fun _ => trivial) ?_
    · refine tendsto_atTop_mono' _ ?_ t_inv
      filter_upwards [ev_pos] with t ht
      have ht' := ht.ne'
      have e : (x + t) * (t⁻¹ * t⁻¹) = x * (t⁻¹ * t⁻¹) + t⁻¹ := by field_simp
      have h0 : 0 ≤ x * (t⁻¹ * t⁻¹) := mul_nonneg hx (by positivity)
      show t⁻¹ ≤ (x + t) * (t⁻¹ * t⁻¹)
      rw [e]; linarith
    · have hlim : Tendsto (fun t : ℝ => x + t) l0 (𝓝 x) := by
        simpa using (tendsto_const_nhds (x := x)).add t_id
      refine hlim.congr' ?_
      filter_upwards [ev_pos] with t ht; have := ht.ne'; field_simp
  | top =>
    refine mem_top (f := fun t => t⁻¹ * t⁻¹) (g := fun t => t⁻¹) t_inv2 t_inv
      (Eventually.of_forall fun _ => trivial) (t_inv.congr' ?_)
    filter_upwards [ev_pos] with t ht; have := ht.ne'; field_simp

theorem exp_lin_tendsto (a : ℝ) : Tendsto (fun t : ℝ => rexp (a * t)) l0 (𝓝 1) := by
  have h : Tendsto (fun t : ℝ => rexp (a * t)) (𝓝 0) (𝓝 (rexp (a * 0))) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto 0
  simpa using h.mono_left nhdsWithin_le_nhds

theorem exp_neg_inv : Tendsto (fun t : ℝ => rexp (-t⁻¹)) l0 (𝓝 0) :=
  tendsto_exp_neg_atTop_nhds_zero.comp t_inv

theorem exp_neg_inv2 : Tendsto (fun t : ℝ => rexp (-(t⁻¹ * t⁻¹))) l0 (𝓝 0) :=
  tendsto_exp_neg_atTop_nhds_zero.comp t_inv2

theorem exp_inv_top : Tendsto (fun t : ℝ => rexp t⁻¹) l0 atTop := tendsto_exp_atTop.comp t_inv

theorem exp_inv2_top : Tendsto (fun t : ℝ => rexp (t⁻¹ * t⁻¹)) l0 atTop :=
  tendsto_exp_atTop.comp t_inv2

theorem pow1Inf_eq : pow1Inf = Ici 0 := by
  unfold pow1Inf
  refine Subset.antisymm (sub_Ici fun f g _ _ hR => ?_) fun L hL => ?_
  · filter_upwards [hR] with t ht
    exact (Real.rpow_pos_of_pos ht _).le
  cases L with
  | bot => exact absurd hL bot_nao_Ici
  | coe x =>
    have hx : 0 ≤ x := EReal.coe_nonneg.mp hL
    rcases hx.lt_or_eq with hx | hx
    · refine mem_coe (f := fun t => rexp (Real.log x * t)) (g := fun t => t⁻¹) (exp_lin_tendsto _)
        t_inv (Eventually.of_forall fun t => exp_pos _) (tendsto_of_ev_eq ?_)
      filter_upwards [ev_pos] with t ht
      have := ht.ne'
      show rexp (Real.log x * t) ^ t⁻¹ = x
      rw [exp_rpow, show Real.log x * t * t⁻¹ = Real.log x by field_simp, Real.exp_log hx]
    · subst hx
      refine mem_coe (f := fun t => rexp (-1 * t)) (g := fun t => t⁻¹ * t⁻¹) (exp_lin_tendsto _)
        t_inv2 (Eventually.of_forall fun t => exp_pos _) (exp_neg_inv.congr' ?_)
      filter_upwards [ev_pos] with t ht
      have := ht.ne'
      show rexp (-t⁻¹) = rexp (-1 * t) ^ (t⁻¹ * t⁻¹)
      rw [exp_rpow]; congr 1; field_simp
  | top =>
    refine mem_top (f := fun t => rexp (1 * t)) (g := fun t => t⁻¹ * t⁻¹) (exp_lin_tendsto _) t_inv2
      (Eventually.of_forall fun t => exp_pos _) (exp_inv_top.congr' ?_)
    filter_upwards [ev_pos] with t ht
    have := ht.ne'
    show rexp t⁻¹ = rexp (1 * t) ^ (t⁻¹ * t⁻¹)
    rw [exp_rpow]; congr 1; field_simp

theorem pow00_eq : pow00 = Ici 0 := by
  unfold pow00
  refine Subset.antisymm (sub_Ici fun f g _ _ hR => ?_) fun L hL => ?_
  · filter_upwards [hR] with t ht
    exact (Real.rpow_pos_of_pos ht _).le
  cases L with
  | bot => exact absurd hL bot_nao_Ici
  | coe x =>
    have hx : 0 ≤ x := EReal.coe_nonneg.mp hL
    rcases hx.lt_or_eq with hx | hx
    · refine mem_coe (f := fun t => rexp (-t⁻¹)) (g := fun t => -(t * Real.log x)) exp_neg_inv
        (by simpa using (t_id.mul_const (Real.log x)).neg) (Eventually.of_forall fun t => exp_pos _)
        (tendsto_of_ev_eq ?_)
      filter_upwards [ev_pos] with t ht
      have := ht.ne'
      show rexp (-t⁻¹) ^ (-(t * Real.log x)) = x
      rw [exp_rpow, show -t⁻¹ * -(t * Real.log x) = Real.log x by field_simp, Real.exp_log hx]
    · subst hx
      refine mem_coe (f := fun t => rexp (-(t⁻¹ * t⁻¹))) (g := fun t => t) exp_neg_inv2 t_id
        (Eventually.of_forall fun t => exp_pos _) (exp_neg_inv.congr' ?_)
      filter_upwards [ev_pos] with t ht
      have := ht.ne'
      show rexp (-t⁻¹) = rexp (-(t⁻¹ * t⁻¹)) ^ t
      rw [exp_rpow]; congr 1; field_simp
  | top =>
    refine mem_top (f := fun t => rexp (-(t⁻¹ * t⁻¹))) (g := fun t => -t) exp_neg_inv2
      (by simpa using t_id.neg) (Eventually.of_forall fun t => exp_pos _) (exp_inv_top.congr' ?_)
    filter_upwards [ev_pos] with t ht
    have := ht.ne'
    show rexp t⁻¹ = rexp (-(t⁻¹ * t⁻¹)) ^ (-t)
    rw [exp_rpow]; congr 1; field_simp

theorem powInf0_eq : powInf0 = Ici 0 := by
  unfold powInf0
  refine Subset.antisymm (sub_Ici fun f g hf _ _ => ?_) fun L hL => ?_
  · filter_upwards [hf.eventually_gt_atTop 0] with t ht
    exact (Real.rpow_pos_of_pos ht _).le
  cases L with
  | bot => exact absurd hL bot_nao_Ici
  | coe x =>
    have hx : 0 ≤ x := EReal.coe_nonneg.mp hL
    rcases hx.lt_or_eq with hx | hx
    · refine mem_coe (f := fun t => rexp t⁻¹) (g := fun t => t * Real.log x) exp_inv_top
        (by simpa using t_id.mul_const (Real.log x)) (Eventually.of_forall fun _ => trivial)
        (tendsto_of_ev_eq ?_)
      filter_upwards [ev_pos] with t ht
      have := ht.ne'
      show rexp t⁻¹ ^ (t * Real.log x) = x
      rw [exp_rpow, show t⁻¹ * (t * Real.log x) = Real.log x by field_simp, Real.exp_log hx]
    · subst hx
      refine mem_coe (f := fun t => rexp (t⁻¹ * t⁻¹)) (g := fun t => -t) exp_inv2_top
        (by simpa using t_id.neg) (Eventually.of_forall fun _ => trivial) (exp_neg_inv.congr' ?_)
      filter_upwards [ev_pos] with t ht
      have := ht.ne'
      show rexp (-t⁻¹) = rexp (t⁻¹ * t⁻¹) ^ (-t)
      rw [exp_rpow]; congr 1; field_simp
  | top =>
    refine mem_top (f := fun t => rexp (t⁻¹ * t⁻¹)) (g := fun t => t) exp_inv2_top t_id
      (Eventually.of_forall fun _ => trivial) (exp_inv_top.congr' ?_)
    filter_upwards [ev_pos] with t ht
    have := ht.ne'
    show rexp t⁻¹ = rexp (t⁻¹ * t⁻¹) ^ t
    rw [exp_rpow]; congr 1; field_simp

/-! ## As sete são indeterminadas -/

theorem indeterminada_de_zero_top {V : Set EReal} (h0 : (0 : EReal) ∈ V) (ht : (⊤ : EReal) ∈ V) :
    Indeterminada V := fun h => EReal.zero_ne_top (h h0 ht)

theorem indeterminada_univ : Indeterminada univ :=
  indeterminada_de_zero_top (mem_univ _) (mem_univ _)

theorem indeterminada_Ici : Indeterminada (Ici (0 : EReal)) :=
  indeterminada_de_zero_top (mem_Ici.mpr le_rfl) (mem_Ici.mpr le_top)

/-- **As sete formas clássicas são indeterminadas.** -/
theorem sete_indeterminadas :
    Indeterminada div00 ∧ Indeterminada mul0Inf ∧ Indeterminada subInf ∧ Indeterminada divInf ∧
      Indeterminada pow1Inf ∧ Indeterminada pow00 ∧ Indeterminada powInf0 := by
  rw [div00_eq, mul0Inf_eq, subInf_eq, divInf_eq, pow1Inf_eq, pow00_eq, powInf0_eq]
  exact ⟨indeterminada_univ, indeterminada_univ, indeterminada_univ, indeterminada_Ici,
    indeterminada_Ici, indeterminada_Ici, indeterminada_Ici⟩

/-- As formas de potência e `∞/∞` nunca valem `−∞` (o estado `menosInf` é inalcançável). -/
theorem sem_menosInf : (⊥ : EReal) ∉ divInf ∧ (⊥ : EReal) ∉ pow1Inf ∧ (⊥ : EReal) ∉ pow00 ∧
    (⊥ : EReal) ∉ powInf0 := by
  rw [divInf_eq, pow1Inf_eq, pow00_eq, powInf0_eq]
  exact ⟨bot_nao_Ici, bot_nao_Ici, bot_nao_Ici, bot_nao_Ici⟩

/-! ## O estado `oscila` em cada forma -/

theorem norm_sinalAlt (t : ℝ) : ‖sinalAlt t‖ = 1 := by simp [sinalAlt, norm_pow]

theorem sinalAlt_ge (t : ℝ) : -1 ≤ sinalAlt t := by
  have h := norm_sinalAlt t
  rw [Real.norm_eq_abs] at h
  linarith [neg_abs_le (sinalAlt t)]

theorem sinalAlt_le (t : ℝ) : sinalAlt t ≤ 1 := by
  have h := norm_sinalAlt t
  rw [Real.norm_eq_abs] at h
  linarith [le_abs_self (sinalAlt t)]

/-- `φ ∘ sinalAlt` oscila sempre que `φ 1 ≠ φ (−1)`. -/
theorem oscila_phi (φ : ℝ → ℝ) (hφ : φ 1 ≠ φ (-1)) :
    Comporta l0 (fun t => φ (sinalAlt t)) Estado7.oscila := by
  have hp : Tendsto (fun n : ℕ => φ (sinalAlt (((2 * n + 1 + 1 : ℕ) : ℝ))⁻¹)) atTop (𝓝 (φ 1)) := by
    simp only [sinalAlt_par]; exact tendsto_const_nhds
  have hi : Tendsto (fun n : ℕ => φ (sinalAlt (((2 * n + 2 + 1 : ℕ) : ℝ))⁻¹)) atTop
      (𝓝 (φ (-1))) := by
    simp only [sinalAlt_impar]; exact tendsto_const_nhds
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨L, hL⟩
    have h1 := tendsto_nhds_unique (hL.comp (seq_tendsto 1)) hp
    have h2 := tendsto_nhds_unique (hL.comp (seq_tendsto 2)) hi
    exact hφ (h1.symm.trans h2)
  · intro ht
    exact nao_lim_maisInf hp (ht.comp (seq_tendsto 1))
  · intro hb
    exact nao_lim_menosInf hp (hb.comp (seq_tendsto 1))

theorem t_mul_sinal : Tendsto (fun t : ℝ => t * sinalAlt t) l0 (𝓝 0) := by
  refine squeeze_zero_norm (a := fun t => ‖t‖) (fun t => ?_) (tendsto_norm_zero.mono_left
    nhdsWithin_le_nhds)
  rw [norm_mul, norm_sinalAlt, mul_one]

theorem oscila_congr {h : ℝ → ℝ} (φ : ℝ → ℝ) (hφ : φ 1 ≠ φ (-1))
    (he : ∀ᶠ t in l0, φ (sinalAlt t) = h t) : Comporta l0 h Estado7.oscila :=
  comporta_congr he (oscila_phi φ hφ)

theorem div00_oscila : Oscila (𝓝 0) (𝓝 0) (fun _ y => y ≠ 0) (fun x y => x / y) := by
  refine ⟨fun t => t * sinalAlt t, fun t => t, t_mul_sinal, t_id, ?_, oscila_congr id
    (by norm_num) ?_⟩
  · filter_upwards [ev_pos] with t ht; exact ht.ne'
  · filter_upwards [ev_pos] with t ht; have := ht.ne'; simp only [id]; field_simp

theorem mul0Inf_oscila : Oscila (𝓝 0) atTop (fun _ _ => True) (fun x y => x * y) := by
  refine ⟨fun t => t * sinalAlt t, fun t => t⁻¹, t_mul_sinal, t_inv,
    Eventually.of_forall fun _ => trivial, oscila_congr id (by norm_num) ?_⟩
  filter_upwards [ev_pos] with t ht; have := ht.ne'; simp only [id]; field_simp

theorem subInf_oscila : Oscila atTop atTop (fun _ _ => True) (fun x y => x - y) := by
  refine ⟨fun t => t⁻¹ + sinalAlt t, fun t => t⁻¹, ?_, t_inv, Eventually.of_forall fun _ => trivial,
    oscila_congr id (by norm_num) (Eventually.of_forall fun t => by simp)⟩
  refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-1) t_inv)
  linarith [sinalAlt_ge t]

theorem divInf_oscila : Oscila atTop atTop (fun _ _ => True) (fun x y => x / y) := by
  refine ⟨fun t => (2 + sinalAlt t) * t⁻¹, fun t => t⁻¹, ?_, t_inv,
    Eventually.of_forall fun _ => trivial, oscila_congr (fun x => 2 + x) (by norm_num) ?_⟩
  · refine tendsto_atTop_mono' _ ?_ t_inv
    filter_upwards [ev_pos] with t ht
    have h1 : 1 ≤ 2 + sinalAlt t := by linarith [sinalAlt_ge t]
    have h2 : 0 < t⁻¹ := inv_pos.mpr ht
    show t⁻¹ ≤ (2 + sinalAlt t) * t⁻¹
    nlinarith
  · filter_upwards [ev_pos] with t ht; have := ht.ne'; field_simp

theorem exp_ne : rexp 1 ≠ rexp (-1) := fun h => by
  have := Real.exp_injective h; norm_num at this

theorem pow1Inf_oscila : Oscila (𝓝 1) atTop (fun x _ => 0 < x) (fun x y => x ^ y) := by
  refine ⟨fun t => rexp (t * sinalAlt t), fun t => t⁻¹, ?_, t_inv,
    Eventually.of_forall fun t => exp_pos _, oscila_congr rexp exp_ne ?_⟩
  · have := (Real.continuous_exp.tendsto 0).comp t_mul_sinal
    rw [Real.exp_zero] at this
    exact this
  · filter_upwards [ev_pos] with t ht
    have := ht.ne'
    show rexp (sinalAlt t) = rexp (t * sinalAlt t) ^ t⁻¹
    rw [exp_rpow]; congr 1; field_simp

theorem pow00_oscila : Oscila (𝓝 0) (𝓝 0) (fun x _ => 0 < x) (fun x y => x ^ y) := by
  refine ⟨fun t => rexp (-t⁻¹), fun t => -(t * sinalAlt t), exp_neg_inv,
    by simpa using t_mul_sinal.neg, Eventually.of_forall fun t => exp_pos _,
    oscila_congr rexp exp_ne ?_⟩
  filter_upwards [ev_pos] with t ht
  have := ht.ne'
  show rexp (sinalAlt t) = rexp (-t⁻¹) ^ (-(t * sinalAlt t))
  rw [exp_rpow]; congr 1; field_simp

theorem powInf0_oscila : Oscila atTop (𝓝 0) (fun _ _ => True) (fun x y => x ^ y) := by
  refine ⟨fun t => rexp t⁻¹, fun t => t * sinalAlt t, exp_inv_top, t_mul_sinal,
    Eventually.of_forall fun _ => trivial, oscila_congr rexp exp_ne ?_⟩
  filter_upwards [ev_pos] with t ht
  have := ht.ne'
  show rexp (sinalAlt t) = rexp t⁻¹ ^ (t * sinalAlt t)
  rw [exp_rpow]; congr 1; field_simp

/-! ## Contraste: formas determinadas (conjunto unitário) -/

def addFin (a b : ℝ) : Set EReal := Valores (𝓝 a) (𝓝 b) (fun _ _ => True) (fun x y => x + y)
def addInfInf : Set EReal := Valores atTop atTop (fun _ _ => True) (fun x y => x + y)
def mulInfInf : Set EReal := Valores atTop atTop (fun _ _ => True) (fun x y => x * y)
def divFinInf (a : ℝ) : Set EReal := Valores (𝓝 a) atTop (fun _ _ => True) (fun x y => x / y)
def pow0Inf : Set EReal := Valores (𝓝 0) atTop (fun x _ => 0 < x) (fun x y => x ^ y)

theorem addFin_eq (a b : ℝ) : addFin a b = {((a + b : ℝ) : EReal)} := by
  ext L
  rw [mem_singleton_iff]
  constructor
  · rintro ⟨f, g, hf, hg, -, hL⟩
    exact tendsto_nhds_unique hL (EReal.tendsto_coe.mpr (hf.add hg))
  · rintro rfl
    exact mem_coe (f := fun _ => a) (g := fun _ => b) tendsto_const_nhds tendsto_const_nhds
      (Eventually.of_forall fun _ => trivial) tendsto_const_nhds

theorem addInfInf_eq : addInfInf = {⊤} := by
  ext L
  rw [mem_singleton_iff]
  constructor
  · rintro ⟨f, g, hf, hg, -, hL⟩
    exact tendsto_nhds_unique hL (EReal.tendsto_coe_nhds_top_iff.mpr (hf.atTop_add_atTop hg))
  · rintro rfl
    exact mem_top (f := fun t => t⁻¹) (g := fun t => t⁻¹) t_inv t_inv
      (Eventually.of_forall fun _ => trivial) (t_inv.atTop_add_atTop t_inv)

theorem mulInfInf_eq : mulInfInf = {⊤} := by
  ext L
  rw [mem_singleton_iff]
  constructor
  · rintro ⟨f, g, hf, hg, -, hL⟩
    exact tendsto_nhds_unique hL (EReal.tendsto_coe_nhds_top_iff.mpr (hf.atTop_mul_atTop₀ hg))
  · rintro rfl
    exact mem_top (f := fun t => t⁻¹) (g := fun t => t⁻¹) t_inv t_inv
      (Eventually.of_forall fun _ => trivial) t_inv2

theorem divFinInf_eq (a : ℝ) : divFinInf a = {((0 : ℝ) : EReal)} := by
  ext L
  rw [mem_singleton_iff]
  constructor
  · rintro ⟨f, g, hf, hg, -, hL⟩
    exact tendsto_nhds_unique hL (EReal.tendsto_coe.mpr (hf.div_atTop hg))
  · rintro rfl
    exact mem_coe (f := fun _ => a) (g := fun t => t⁻¹) tendsto_const_nhds t_inv
      (Eventually.of_forall fun _ => trivial) (tendsto_const_nhds.div_atTop t_inv)

/-- `0^∞ → 0`: toda realização tende a `0`. -/
theorem pow0Inf_tendsto {f g : ℝ → ℝ} (hf : Tendsto f l0 (𝓝 0)) (hg : Tendsto g l0 atTop)
    (hR : ∀ᶠ t in l0, 0 < f t) : Tendsto (fun t => f t ^ g t) l0 (𝓝 0) := by
  have hf' : Tendsto f l0 (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hf, hR⟩
  have hlog : Tendsto (fun t => Real.log (f t) * g t) l0 atBot :=
    (tendsto_log_nhdsGT_zero.comp hf').atBot_mul_atTop₀ hg
  refine (tendsto_exp_atBot.comp hlog).congr' ?_
  filter_upwards [hR] with t ht
  simp [Function.comp, Real.rpow_def_of_pos ht]

theorem pow0Inf_eq : pow0Inf = {((0 : ℝ) : EReal)} := by
  ext L
  rw [mem_singleton_iff]
  constructor
  · rintro ⟨f, g, hf, hg, hR, hL⟩
    exact tendsto_nhds_unique hL (EReal.tendsto_coe.mpr (pow0Inf_tendsto hf hg hR))
  · rintro rfl
    exact mem_coe (f := fun t => t) (g := fun t => t⁻¹) t_id t_inv ev_pos
      (pow0Inf_tendsto t_id t_inv ev_pos)

/-- **As formas determinadas não pertencem a `I`**: seu conjunto de valores é unitário. -/
theorem determinadas :
    (∀ a b : ℝ, ¬ Indeterminada (addFin a b)) ∧ ¬ Indeterminada addInfInf ∧
      ¬ Indeterminada mulInfInf ∧ (∀ a : ℝ, ¬ Indeterminada (divFinInf a)) ∧
      ¬ Indeterminada pow0Inf := by
  refine ⟨fun a b h => h ?_, fun h => h ?_, fun h => h ?_, fun a h => h ?_, fun h => h ?_⟩
  · rw [addFin_eq]; exact subsingleton_singleton
  · rw [addInfInf_eq]; exact subsingleton_singleton
  · rw [mulInfInf_eq]; exact subsingleton_singleton
  · rw [divFinInf_eq]; exact subsingleton_singleton
  · rw [pow0Inf_eq]; exact subsingleton_singleton

/-- **`lim x/x` não é `I`**: `x/x → 1` (refuta a afirmação do acervo). -/
theorem x_div_x : Tendsto (fun t : ℝ => t / t) l0 (𝓝 1) :=
  tendsto_of_ev_eq (by filter_upwards [ev_pos] with t ht; exact div_self ht.ne')

/-- E `x²/x → 0`: a mesma forma `0/0` com outro germe dá outro valor. -/
theorem x2_div_x : Tendsto (fun t : ℝ => t ^ 2 / t) l0 (𝓝 0) :=
  t_id.congr' (by filter_upwards [ev_pos] with t ht; have := ht.ne'; field_simp)

end ATK.IFormas

#print axioms ATK.IFormas.ev_pos
#print axioms ATK.IFormas.t_id
#print axioms ATK.IFormas.t_inv
#print axioms ATK.IFormas.t_inv2
#print axioms ATK.IFormas.t_neg_inv
#print axioms ATK.IFormas.exp_rpow
#print axioms ATK.IFormas.mem_coe
#print axioms ATK.IFormas.mem_top
#print axioms ATK.IFormas.mem_bot
#print axioms ATK.IFormas.tendsto_of_ev_eq
#print axioms ATK.IFormas.sub_Ici
#print axioms ATK.IFormas.bot_nao_Ici
#print axioms ATK.IFormas.div00_eq
#print axioms ATK.IFormas.mul0Inf_eq
#print axioms ATK.IFormas.t_two_inv
#print axioms ATK.IFormas.subInf_eq
#print axioms ATK.IFormas.divInf_eq
#print axioms ATK.IFormas.exp_lin_tendsto
#print axioms ATK.IFormas.exp_neg_inv
#print axioms ATK.IFormas.exp_neg_inv2
#print axioms ATK.IFormas.exp_inv_top
#print axioms ATK.IFormas.exp_inv2_top
#print axioms ATK.IFormas.pow1Inf_eq
#print axioms ATK.IFormas.pow00_eq
#print axioms ATK.IFormas.powInf0_eq
#print axioms ATK.IFormas.indeterminada_de_zero_top
#print axioms ATK.IFormas.indeterminada_univ
#print axioms ATK.IFormas.indeterminada_Ici
#print axioms ATK.IFormas.sete_indeterminadas
#print axioms ATK.IFormas.sem_menosInf
#print axioms ATK.IFormas.norm_sinalAlt
#print axioms ATK.IFormas.sinalAlt_ge
#print axioms ATK.IFormas.sinalAlt_le
#print axioms ATK.IFormas.oscila_phi
#print axioms ATK.IFormas.t_mul_sinal
#print axioms ATK.IFormas.oscila_congr
#print axioms ATK.IFormas.div00_oscila
#print axioms ATK.IFormas.mul0Inf_oscila
#print axioms ATK.IFormas.subInf_oscila
#print axioms ATK.IFormas.divInf_oscila
#print axioms ATK.IFormas.exp_ne
#print axioms ATK.IFormas.pow1Inf_oscila
#print axioms ATK.IFormas.pow00_oscila
#print axioms ATK.IFormas.powInf0_oscila
#print axioms ATK.IFormas.addFin_eq
#print axioms ATK.IFormas.addInfInf_eq
#print axioms ATK.IFormas.mulInfInf_eq
#print axioms ATK.IFormas.divFinInf_eq
#print axioms ATK.IFormas.pow0Inf_tendsto
#print axioms ATK.IFormas.pow0Inf_eq
#print axioms ATK.IFormas.determinadas
#print axioms ATK.IFormas.x_div_x
#print axioms ATK.IFormas.x2_div_x
