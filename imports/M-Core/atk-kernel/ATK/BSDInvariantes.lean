import ATK.L4Base
import ATK.LigacaoBSDTestes
import Mathlib.NumberTheory.Height.EllipticCurve
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Northcott
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.GroupTheory.Descent
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# ATK — Ligação L4: os invariantes da fórmula refinada de BSD

A fórmula refinada de Birch e Swinnerton-Dyer (convenções da LMFDB):

  `L^{(r)}(E, 1) / r! = Ω_E · Reg_E · ∏_p c_p · #Ш(E) / #E(ℚ)_tors²`

Este arquivo define, sobre os objetos da Mathlib, os invariantes do lado direito que não dependem de
cohomologia de Galois, e prova as propriedades que os caracterizam:

* `coefLider`: `L^{(r)}(E, 1) / r!` para a continuação analítica (`r` = ordem do zero em `s = 1`);
  `coefLider_of_ne_zero`: se `L(E, 1) ≠ 0`, é `L(E, 1)`;
* `periodo`: `Ω_E = ∫_{E(ℝ)} |dx / (2y + a₁x + a₃)|` no modelo minimal global;
  `quadrado`: nos pontos da curva, `(2y + a₁x + a₃)² = 4x³ + b₂x² + 2b₄x + b₆`;
* `ordemTorsao`: `#E(ℚ)_tors` (`ordemTorsao_pos`: é ≥ 1, a torção sendo finita pela Mathlib);
  teste: `ordemTorsao_E32 = 4` para `y² = x³ − x`;
* `mordellWeil_of_fraco`: a hipótese `MordellWeil` da ligação L4 (posto finito) segue do teorema
  de Mordell–Weil **fraco** (`E(ℚ)/2E(ℚ)` finito), pela descida da Mathlib com a altura ingênua;
* `alturaCanonica`: a altura de Néron–Tate `ĥ(P) = lim h(x(2ⁿP)) / 4ⁿ`, com o **limite provado**
  (`tendsto_alturaCanonica`, a partir da lei do paralelogramo aproximada da Mathlib), a **lei do
  paralelogramo exata** (`paralelogramo`), `ĥ(nP) = n² ĥ(P)`, `|ĥ − h| ≤ C` e o **teorema de
  Néron–Tate** `ĥ(P) = 0 ⟺ P de torção` (`alturaCanonica_eq_zero_iff`, via Northcott);
* `emparelhamento`: `⟨P, Q⟩ = (ĥ(P + Q) − ĥ(P) − ĥ(Q)) / 2`, simétrico, aditivo e nulo na torção;
* `regulador`: `|det ⟨Pᵢ, Pⱼ⟩|` para uma base de `E(ℚ)/torção`; teste: `regulador_E32 = 1`.

Os números de Tamagawa e o grupo de Tate–Shafarevich estão em `ATK.BSDRefinada`.
Nada aqui prova BSD nem a fórmula refinada (obrigação O7, `OPEN_MATH`).
-/

open WeierstrassCurve Filter Topology MeasureTheory

namespace ATK.BSDInvariantes

/-! ## O coeficiente líder `L^{(r)}(E, 1) / r!` -/

section lider
variable {E : WeierstrassCurve ℚ}

/-- A ordem do zero em `s = 1`, como número natural. -/
noncomputable def ordem (Lc : ATK.L4Base.LFunctionContinued E) : ℕ :=
  (analyticOrderAt Lc.L 1).toNat

/-- O coeficiente líder da expansão de Taylor em `s = 1`: `L^{(r)}(E, 1) / r!`. -/
noncomputable def coefLider (Lc : ATK.L4Base.LFunctionContinued E) : ℂ :=
  iteratedDeriv (ordem Lc) Lc.L 1 / (ordem Lc).factorial

/-- Se `L(E, 1) ≠ 0`, o coeficiente líder é `L(E, 1)`. -/
theorem coefLider_of_ne_zero (Lc : ATK.L4Base.LFunctionContinued E) (h : Lc.L 1 ≠ 0) :
    coefLider Lc = Lc.L 1 := by
  have h0 : analyticOrderAt Lc.L 1 = 0 := by
    rw [analyticOrderAt_eq_zero]; exact Or.inr h
  simp [coefLider, ordem, h0]

end lider

/-! ## O período real -/

/-- `g(x) = 4x³ + b₂x² + 2b₄x + b₆`, com `(2y + a₁x + a₃)² = g(x)` sobre a curva. -/
noncomputable def gR (W : WeierstrassCurve ℚ) (x : ℝ) : ℝ :=
  4 * x ^ 3 + (W.b₂ : ℝ) * x ^ 2 + 2 * (W.b₄ : ℝ) * x + (W.b₆ : ℝ)

/-- Completando o quadrado: nos pontos da curva, `(2y + a₁x + a₃)² = g(x)`. -/
theorem quadrado (W : WeierstrassCurve ℚ) {x y : ℚ} (h : W.toAffine.Equation x y) :
    ((2 * y + W.a₁ * x + W.a₃ : ℚ) : ℝ) ^ 2 = gR W x := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [gR, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  push_cast
  have h' : ((y : ℝ) ^ 2 + W.a₁ * x * y + W.a₃ * y) =
      (x : ℝ) ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by
    exact_mod_cast h
  linear_combination 4 * h'

/-- `∫_{W(ℝ)} |ω|` com `ω = dx / (2y + a₁x + a₃)`: cada `x` com `g(x) > 0` tem dois pontos reais,
com `2y + a₁x + a₃ = ±√g(x)`, logo a integral é `∫_{g > 0} 2 / √g`. -/
noncomputable def periodoModelo (W : WeierstrassCurve ℚ) : ℝ :=
  ∫ x in {x : ℝ | 0 < gR W x}, 2 / Real.sqrt (gR W x)

open IsDedekindDomain NumberField in
/-- `W` é um modelo minimal global: minimal em todo primo de `ℚ`. -/
def MinimalGlobal (W : WeierstrassCurve ℚ) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 ℚ),
    (W.baseChange (v.adicCompletion ℚ)).IsMinimal (v.adicCompletionIntegers ℚ)

open Classical in
/-- **O período real** `Ω_E`: `∫_{E(ℝ)} |ω|` para a diferencial invariante de um modelo minimal
global (sobre `ℚ`, dois modelos minimais globais diferem por `u = ±1`, e `Ω` não muda). -/
noncomputable def periodo (E : WeierstrassCurve ℚ) : ℝ :=
  if h : ∃ C : VariableChange ℚ, MinimalGlobal (C • E) then periodoModelo (h.choose • E) else 0

/-- Teste: para `y² = x³ − x`, `g(x) = 4x³ − 4x`. -/
theorem gR_E32 (x : ℝ) : gR ATK.L4Base.E32 x = 4 * x ^ 3 - 4 * x := by
  simp only [gR, ATK.L4Base.E32, ATK.CongruentCurve.E, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆]
  push_cast; ring

/-! ## A torção -/

/-- A ordem do subgrupo de torção de `E(ℚ)`. -/
noncomputable def ordemTorsao (E : WeierstrassCurve ℚ) : ℕ :=
  Nat.card (AddCommGroup.torsion E.toAffine.Point)

/-- Teste: `#E(ℚ)_tors = 4` para `y² = x³ − x` (os pontos `O, (0,0), (1,0), (−1,0)`). -/
theorem ordemTorsao_E32 : ordemTorsao ATK.L4Base.E32 = 4 := by
  have htop : AddCommGroup.torsion ATK.CongruentCurve.E.toAffine.Point = ⊤ := by
    ext P
    simp only [AddSubgroup.mem_top, iff_true, AddCommGroup.mem_torsion]
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨2, by norm_num, by rw [two_nsmul]; exact ATK.LigacaoBSDTestes.dois_torcao P⟩
  obtain ⟨h0, h1, hm⟩ := ATK.CongruentCurve.E_torsion_points
  let f : Fin 4 → ATK.CongruentCurve.E.toAffine.Point :=
    ![0, .some 0 0 h0, .some 1 0 h1, .some (-1) 0 hm]
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;> norm_num at hij
    · intro P
      rcases ATK.CongruentCurve.E_point_cases P with rfl | ⟨x, h, rfl, hx⟩
      · exact ⟨0, rfl⟩
      · rcases hx with rfl | rfl | rfl
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩
  rw [ordemTorsao, ATK.L4Base.E32, htop, AddSubgroup.card_top, ← Nat.card_eq_of_bijective f hf,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/-- `#E(ℚ)_tors ≥ 1`: a torção é finita (Mathlib, via Northcott) e contém `O`. -/
theorem ordemTorsao_pos (E : WeierstrassCurve ℚ) [E.IsElliptic] : 0 < ordemTorsao E := by
  have := WeierstrassCurve.Affine.finite_torsion (W := E.toAffine)
  exact Nat.card_pos

/-! ## Mordell–Weil a partir do Mordell–Weil fraco -/

/-- O teorema de Mordell–Weil **fraco**: `E(ℚ)/2E(ℚ)` é finito. -/
def MordellWeilFraco : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic →
    (nsmulAddMonoidHom (α := E.toAffine.Point) 2).range.FiniteIndex

/-- **Descida**: se `E(ℚ)/2E(ℚ)` é finito, `E(ℚ)` é finitamente gerado (`AddCommGroup.fg_of_descent'`
da Mathlib, com a altura ingênua: não negativa, lei do paralelogramo aproximada e Northcott). -/
theorem fg_of_fraco (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : (nsmulAddMonoidHom (α := E.toAffine.Point) 2).range.FiniteIndex) :
    AddGroup.FG E.toAffine.Point := by
  classical
  obtain ⟨C, hC⟩ := WeierstrassCurve.Affine.approx_parallelogram_law E.toAffine
  exact AddCommGroup.fg_of_descent' (h := WeierstrassCurve.Affine.Point.naiveHeight) h
    (fun x => Height.logHeight_nonneg _) hC

/-- **Mordell–Weil fraco ⇒ Mordell–Weil** (a hipótese `MordellWeil` da ligação L4): o posto de
`E(ℚ)` é finito. -/
theorem mordellWeil_of_fraco (h : MordellWeilFraco) : ATK.LigacaoBSD.MordellWeil := by
  intro E hE
  have hfg := fg_of_fraco E (h E hE)
  have : Module.Finite ℤ E.toAffine.Point := Module.Finite.iff_addGroup_fg.mpr hfg
  unfold ATK.LigacaoBSD.postoMW
  rw [Ne, Cardinal.toENat_eq_top, not_le]
  exact Module.rank_lt_aleph0 ℤ _

/-! ## A altura canônica de Néron–Tate -/

section altura

variable {E : WeierstrassCurve ℚ}

/-- **A altura canônica** (de Néron–Tate): `ĥ(P) = lim h(x(2ⁿP)) / 4ⁿ`, com `h` a altura de Weil
da coordenada `x` (a normalização da LMFDB, usada na conjectura de BSD). -/
noncomputable def alturaCanonica (P : E.toAffine.Point) : ℝ :=
  limUnder atTop fun n : ℕ => ((2 ^ n) • P).naiveHeight / 4 ^ n

/-- Duplicação: `|h(2Q) − 4 h(Q)| ≤ C`, da lei do paralelogramo aproximada (Mathlib). -/
theorem duplicacao [E.IsElliptic] :
    ∃ C, ∀ Q : E.toAffine.Point, |(2 • Q).naiveHeight - 4 * Q.naiveHeight| ≤ C := by
  classical
  obtain ⟨C, hC⟩ := WeierstrassCurve.Affine.approx_parallelogram_law E.toAffine
  refine ⟨C + |(0 : E.toAffine.Point).naiveHeight|, fun Q => ?_⟩
  have := hC Q Q
  rw [sub_self, ← two_nsmul] at this
  calc |(2 • Q).naiveHeight - 4 * Q.naiveHeight|
      = |((2 • Q).naiveHeight + (0 : E.toAffine.Point).naiveHeight
            - 2 * (Q.naiveHeight + Q.naiveHeight)) - (0 : E.toAffine.Point).naiveHeight| := by
        ring_nf
    _ ≤ |(2 • Q).naiveHeight + (0 : E.toAffine.Point).naiveHeight
            - 2 * (Q.naiveHeight + Q.naiveHeight)| + |(0 : E.toAffine.Point).naiveHeight| :=
        abs_sub _ _
    _ ≤ C + |(0 : E.toAffine.Point).naiveHeight| := by linarith

/-- O passo de Tate: `|h(2ⁿP)/4ⁿ − h(2ⁿ⁺¹P)/4ⁿ⁺¹| ≤ (C/4)(1/4)ⁿ`. -/
theorem passo {C : ℝ} (hC : ∀ Q : E.toAffine.Point, |(2 • Q).naiveHeight - 4 * Q.naiveHeight| ≤ C)
    (P : E.toAffine.Point) (n : ℕ) :
    dist (((2 ^ n) • P).naiveHeight / 4 ^ n) (((2 ^ (n + 1)) • P).naiveHeight / 4 ^ (n + 1)) ≤
      C / 4 * (1 / 4) ^ n := by
  rw [Real.dist_eq]
  have hq := hC ((2 ^ n) • P)
  rw [← mul_nsmul', ← pow_succ'] at hq
  have e : ((2 ^ n) • P).naiveHeight / 4 ^ n - ((2 ^ (n + 1)) • P).naiveHeight / 4 ^ (n + 1) =
      -(((2 ^ (n + 1)) • P).naiveHeight - 4 * ((2 ^ n) • P).naiveHeight) / 4 ^ (n + 1) := by
    field_simp; ring
  rw [e, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ (n + 1)),
    div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ (n + 1))]
  calc |((2 ^ (n + 1)) • P).naiveHeight - 4 * ((2 ^ n) • P).naiveHeight| ≤ C := hq
    _ = C / 4 * (1 / 4) ^ n * 4 ^ (n + 1) := by
        rw [one_div_pow, pow_succ]; field_simp

/-- **Existência do limite** (Tate): `h(2ⁿP)/4ⁿ` é de Cauchy. -/
theorem tendsto_alturaCanonica [E.IsElliptic] (P : E.toAffine.Point) :
    Tendsto (fun n : ℕ => ((2 ^ n) • P).naiveHeight / 4 ^ n) atTop (𝓝 (alturaCanonica P)) := by
  obtain ⟨C, hC⟩ := duplicacao (E := E)
  exact (cauchySeq_of_le_geometric (1 / 4) (C / 4) (by norm_num) (passo hC P)).tendsto_limUnder

/-- `ĥ` difere da altura ingênua por uma constante: `|ĥ(P) − h(P)| ≤ C`. -/
theorem abs_alturaCanonica_sub_le [E.IsElliptic] :
    ∃ C, ∀ P : E.toAffine.Point, |alturaCanonica P - P.naiveHeight| ≤ C := by
  obtain ⟨C, hC⟩ := duplicacao (E := E)
  refine ⟨C / 4 / (1 - 1 / 4), fun P => ?_⟩
  have := dist_le_of_le_geometric_of_tendsto₀ (1 / 4) (C / 4) (by norm_num) (passo hC P)
    (tendsto_alturaCanonica P)
  rw [Real.dist_eq] at this
  simpa [abs_sub_comm] using this

/-- `ĥ ≥ 0`. -/
theorem alturaCanonica_nonneg [E.IsElliptic] (P : E.toAffine.Point) : 0 ≤ alturaCanonica P :=
  ge_of_tendsto' (tendsto_alturaCanonica P) fun n =>
    div_nonneg (Height.logHeight_nonneg _) (by positivity)

/-- **A lei do paralelogramo exata**: `ĥ(P + Q) + ĥ(P − Q) = 2(ĥ(P) + ĥ(Q))`. -/
theorem paralelogramo [E.IsElliptic] (P Q : E.toAffine.Point) :
    alturaCanonica (P + Q) + alturaCanonica (P - Q) =
      2 * (alturaCanonica P + alturaCanonica Q) := by
  classical
  obtain ⟨C, hC⟩ := WeierstrassCurve.Affine.approx_parallelogram_law E.toAffine
  set a : E.toAffine.Point → ℕ → ℝ := fun X n => ((2 ^ n) • X).naiveHeight / 4 ^ n with ha
  have hlim : Tendsto (fun n => a (P + Q) n + a (P - Q) n - 2 * (a P n + a Q n)) atTop
      (𝓝 (alturaCanonica (P + Q) + alturaCanonica (P - Q) -
        2 * (alturaCanonica P + alturaCanonica Q))) :=
    (((tendsto_alturaCanonica _).add (tendsto_alturaCanonica _)).sub
      (((tendsto_alturaCanonica _).add (tendsto_alturaCanonica _)).const_mul 2))
  have hzero : Tendsto (fun n => a (P + Q) n + a (P - Q) n - 2 * (a P n + a Q n)) atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ => C * (1 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
        (by norm_num)).const_mul C
    refine squeeze_zero_norm (fun n => ?_) hg
    have hb := hC ((2 ^ n) • P) ((2 ^ n) • Q)
    rw [← smul_add, ← smul_sub] at hb
    have e : a (P + Q) n + a (P - Q) n - 2 * (a P n + a Q n) =
        (((2 ^ n) • (P + Q)).naiveHeight + ((2 ^ n) • (P - Q)).naiveHeight -
          2 * (((2 ^ n) • P).naiveHeight + ((2 ^ n) • Q).naiveHeight)) / 4 ^ n := by
      simp only [ha]; field_simp
    rw [Real.norm_eq_abs, e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 ^ n),
      div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ n)]
    calc _ ≤ C := hb
      _ = C * (1 / 4) ^ n * 4 ^ n := by rw [one_div_pow]; field_simp
  have := tendsto_nhds_unique hlim hzero
  linarith

theorem alturaCanonica_zero [E.IsElliptic] : alturaCanonica (0 : E.toAffine.Point) = 0 := by
  have := paralelogramo (0 : E.toAffine.Point) 0
  simp only [add_zero, sub_zero] at this
  linarith

theorem alturaCanonica_neg [E.IsElliptic] (P : E.toAffine.Point) :
    alturaCanonica (-P) = alturaCanonica P := by
  have := paralelogramo (0 : E.toAffine.Point) P
  simp only [zero_add, zero_sub, alturaCanonica_zero] at this
  linarith

/-- `ĥ(nP) = n² ĥ(P)`. -/
theorem alturaCanonica_nsmul [E.IsElliptic] (P : E.toAffine.Point) (n : ℕ) :
    alturaCanonica (n • P) = (n : ℝ) ^ 2 * alturaCanonica P := by
  suffices h : ∀ n : ℕ, alturaCanonica (n • P) = (n : ℝ) ^ 2 * alturaCanonica P ∧
      alturaCanonica ((n + 1) • P) = ((n + 1 : ℕ) : ℝ) ^ 2 * alturaCanonica P from (h n).1
  intro n
  induction n with
  | zero => simp [alturaCanonica_zero]
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hp := paralelogramo ((k + 1) • P) P
    rw [← succ_nsmul, show (k + 1) • P - P = k • P by rw [succ_nsmul, add_sub_cancel_right],
      ih.1, ih.2] at hp
    push_cast at hp ⊢
    linarith

/-- **Teorema de Néron–Tate**: `ĥ(P) = 0` exatamente nos pontos de torção (pela propriedade de
Northcott de `ℚ`, que a Mathlib prova para corpos de números). -/
theorem alturaCanonica_eq_zero_iff [E.IsElliptic] (P : E.toAffine.Point) :
    alturaCanonica P = 0 ↔ P ∈ AddCommGroup.torsion E.toAffine.Point := by
  rw [AddCommGroup.mem_torsion]
  constructor
  · intro h0
    obtain ⟨C, hC⟩ := abs_alturaCanonica_sub_le (E := E)
    have hfin := WeierstrassCurve.Affine.finite_naiveHeight_le E.toAffine C
    have hb : ∀ n : ℕ, n • P ∈ {Q : E.toAffine.Point | Q.naiveHeight ≤ C} := by
      intro n
      have h1 := hC (n • P)
      rw [alturaCanonica_nsmul, h0, mul_zero, zero_sub, abs_neg] at h1
      exact (le_abs_self _).trans h1
    have := hfin.to_subtype
    obtain ⟨m, n, hmn, he⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => (⟨n • P, hb n⟩ : {Q : E.toAffine.Point | Q.naiveHeight ≤ C}))
    have he' : m • P = n • P := congrArg Subtype.val he
    rcases lt_or_gt_of_ne hmn with h | h
    · refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n - m, by omega, ?_⟩
      have : n • P = (n - m) • P + m • P := by rw [← add_nsmul, Nat.sub_add_cancel h.le]
      rw [this] at he'
      simpa using (congrArg (· - m • P) he').symm
    · refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨m - n, by omega, ?_⟩
      have : m • P = (m - n) • P + n • P := by rw [← add_nsmul, Nat.sub_add_cancel h.le]
      rw [this] at he'
      simpa using congrArg (· - n • P) he'
  · intro h
    obtain ⟨n, hn, hP⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp h
    have := alturaCanonica_nsmul P n
    rw [hP, alturaCanonica_zero] at this
    have hn' : (n : ℝ) ^ 2 ≠ 0 := by positivity
    exact (mul_eq_zero.mp this.symm).resolve_left hn'

/-! ### O emparelhamento de Néron–Tate -/

/-- O emparelhamento de Néron–Tate `⟨P, Q⟩ = (ĥ(P + Q) − ĥ(P) − ĥ(Q)) / 2`. -/
noncomputable def emparelhamento (P Q : E.toAffine.Point) : ℝ :=
  (alturaCanonica (P + Q) - alturaCanonica P - alturaCanonica Q) / 2

theorem emparelhamento_comm (P Q : E.toAffine.Point) :
    emparelhamento P Q = emparelhamento Q P := by
  simp only [emparelhamento, add_comm P Q]; ring

theorem emparelhamento_self [E.IsElliptic] (P : E.toAffine.Point) :
    emparelhamento P P = alturaCanonica P := by
  have := alturaCanonica_nsmul P 2
  rw [two_nsmul] at this
  simp only [emparelhamento, this]; push_cast; ring

/-- **Bilinearidade**: `⟨P + P', Q⟩ = ⟨P, Q⟩ + ⟨P', Q⟩` (da lei do paralelogramo exata). -/
theorem emparelhamento_add_left [E.IsElliptic] (P P' Q : E.toAffine.Point) :
    emparelhamento (P + P') Q = emparelhamento P Q + emparelhamento P' Q := by
  have h1 := paralelogramo (P + Q) P'
  have h2 := paralelogramo (P' + Q) P
  have h3 := paralelogramo Q (P - P')
  have h4 := paralelogramo P P'
  rw [show P + Q + P' = P + P' + Q by abel, show P + Q - P' = Q + (P - P') by abel] at h1
  rw [show P' + Q + P = P + P' + Q by abel, show P' + Q - P = Q - (P - P') by abel] at h2
  simp only [emparelhamento]
  linarith

/-- O emparelhamento se anula na torção: ele desce a `E(ℚ)/torção`. -/
theorem emparelhamento_torsao [E.IsElliptic] {P : E.toAffine.Point}
    (hP : P ∈ AddCommGroup.torsion E.toAffine.Point) (Q : E.toAffine.Point) :
    emparelhamento P Q = 0 := by
  have h0 : alturaCanonica P = 0 := (alturaCanonica_eq_zero_iff P).mpr hP
  have hn : ∀ n : ℕ, emparelhamento (n • P) Q = n * emparelhamento P Q := by
    intro n
    induction n with
    | zero =>
      simp only [zero_nsmul, Nat.cast_zero, zero_mul, emparelhamento, zero_add,
        alturaCanonica_zero]; ring
    | succ k ih => rw [succ_nsmul, emparelhamento_add_left, ih]; push_cast; ring
  obtain ⟨n, hn0, hnP⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp ((AddCommGroup.mem_torsion _).mp hP)
  have := hn n
  rw [hnP] at this
  have hz : emparelhamento (0 : E.toAffine.Point) Q = 0 := by
    simp only [emparelhamento, zero_add, alturaCanonica_zero]; ring
  rw [hz] at this
  have hn' : (n : ℝ) ≠ 0 := by positivity
  exact (mul_eq_zero.mp this.symm).resolve_left hn'

end altura

/-! ## O regulador -/

section regulador

variable {E : WeierstrassCurve ℚ}

/-- `E(ℚ)/torção`. -/
abbrev Livre (E : WeierstrassCurve ℚ) := E.toAffine.Point ⧸ AddCommGroup.torsion E.toAffine.Point

/-- `P : Fin r → E(ℚ)` induz uma base (sobre `ℤ`) de `E(ℚ)/torção`. -/
def BaseLivre {r : ℕ} (P : Fin r → E.toAffine.Point) : Prop :=
  LinearIndependent ℤ (fun i => (QuotientAddGroup.mk (P i) : Livre E)) ∧
    AddSubgroup.closure (Set.range fun i => (QuotientAddGroup.mk (P i) : Livre E)) = ⊤

open Classical in
/-- O regulador para uma família de tamanho `r`: `|det ⟨Pᵢ, Pⱼ⟩|` para uma base de `E(ℚ)/torção`
(com `r` elementos), e `0` se não houver base de tamanho `r`. -/
noncomputable def reguladorN (E : WeierstrassCurve ℚ) (r : ℕ) : ℝ :=
  if h : ∃ P : Fin r → E.toAffine.Point, BaseLivre P then
    |(Matrix.of fun i j => emparelhamento (h.choose i) (h.choose j)).det|
  else 0

/-- **O regulador de Néron–Tate** `Reg_E = |det ⟨Pᵢ, Pⱼ⟩|`, para uma base `P₁, …, P_r` de
`E(ℚ)/torção`, `r` o posto de Mordell–Weil. -/
noncomputable def regulador (E : WeierstrassCurve ℚ) : ℝ :=
  reguladorN E (ATK.LigacaoBSD.postoMW E).toNat

/-- Posto 0 e grupo todo de torção: `Reg = 1` (determinante da matriz vazia). -/
theorem regulador_of_torsao (h0 : (ATK.LigacaoBSD.postoMW E).toNat = 0)
    (ht : ∀ P : E.toAffine.Point, P ∈ AddCommGroup.torsion E.toAffine.Point) :
    regulador E = 1 := by
  have hb : BaseLivre (E := E) (Fin.elim0 : Fin 0 → E.toAffine.Point) := by
    refine ⟨linearIndependent_empty_type, ?_⟩
    rw [Set.range_eq_empty, AddSubgroup.closure_empty, eq_top_iff]
    intro x _
    induction x using QuotientAddGroup.induction_on with
    | H P => rw [(QuotientAddGroup.eq_zero_iff P).mpr (ht P)]; exact zero_mem _
  unfold regulador
  rw [h0, reguladorN, dite_eq_left ⟨_, hb⟩, Matrix.det_isEmpty, abs_one]

/-- Teste: `Reg = 1` para `y² = x³ − x` (posto 0). -/
theorem regulador_E32 : regulador ATK.L4Base.E32 = 1 := by
  refine regulador_of_torsao ?_ fun P => ?_
  · rw [ATK.L4Base.E32, ATK.LigacaoBSDTestes.posto_curva32]; rfl
  · rw [AddCommGroup.mem_torsion]
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨2, by norm_num, by rw [two_nsmul]; exact ATK.LigacaoBSDTestes.dois_torcao P⟩

end regulador

end ATK.BSDInvariantes

#print axioms ATK.BSDInvariantes.coefLider_of_ne_zero
#print axioms ATK.BSDInvariantes.quadrado
#print axioms ATK.BSDInvariantes.gR_E32
#print axioms ATK.BSDInvariantes.ordemTorsao_E32
#print axioms ATK.BSDInvariantes.ordemTorsao_pos
#print axioms ATK.BSDInvariantes.fg_of_fraco
#print axioms ATK.BSDInvariantes.mordellWeil_of_fraco
#print axioms ATK.BSDInvariantes.duplicacao
#print axioms ATK.BSDInvariantes.passo
#print axioms ATK.BSDInvariantes.tendsto_alturaCanonica
#print axioms ATK.BSDInvariantes.abs_alturaCanonica_sub_le
#print axioms ATK.BSDInvariantes.alturaCanonica_nonneg
#print axioms ATK.BSDInvariantes.paralelogramo
#print axioms ATK.BSDInvariantes.alturaCanonica_zero
#print axioms ATK.BSDInvariantes.alturaCanonica_neg
#print axioms ATK.BSDInvariantes.alturaCanonica_nsmul
#print axioms ATK.BSDInvariantes.alturaCanonica_eq_zero_iff
#print axioms ATK.BSDInvariantes.emparelhamento_comm
#print axioms ATK.BSDInvariantes.emparelhamento_self
#print axioms ATK.BSDInvariantes.emparelhamento_add_left
#print axioms ATK.BSDInvariantes.emparelhamento_torsao
#print axioms ATK.BSDInvariantes.regulador_of_torsao
#print axioms ATK.BSDInvariantes.regulador_E32
