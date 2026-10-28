import ATK.ForaDaLinha
import ATK.BealFLT
import ATK.YMToy
import ATK.Shannon
import ATK.NSPequeno
import ATK.CongruentCurve
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# ATK — Fichas das conjecturas: parte provada, parte refutada, lacuna e parâmetros

Cada conjectura `C` se decompõe em:

* **parte provada** — um teorema certificado (fronteira atual);
* **parte refutada** — um reforço ou variante natural de `C` que é **falso** (provado `¬`);
* **lacuna** (a parte de "erro") — um enunciado com `C ⟺ lacuna`, exatamente o que falta.

E dois objetos de contabilidade, com os metateoremas **corretos**:

* `Produto H Q` (condicional material: `H → Q`) e `AntiProduto Q` (testemunhas que refutam `Q`,
  completo quando `¬Q ⇒ existe testemunha`): `Q ⟺ testemunhas vazias` (`AntiProduto.iff_vazio`),
  e um produto com hipótese habitada esvazia o anti-produto (`descarga`).
* `metateorema_falso`: a regra "`H` habitada ⟺ testemunhas vazias", proposta como lei geral, é
  **falsa** (contraexemplo `H = False`, `Q = True`).

Parâmetros materializados aqui e nos módulos citados:

| parâmetro | onde | teorema |
|---|---|---|
| indeterminação | estados de `D_N` | `RiemannStates.estado_DN_dicotomia` (só `zero`/`finito`) |
| tensão / torção | zeros de ζ | `ForaDaLinha.quarteto_fora` |
| condensação | piso de `D_N` | `ForaDaLinha.piso_DN`, `condensacao` |
| materialização | zero fora ⇒ estado finito | `ForaDaLinha.finito_de_zero_fora` |
| explosão | enstrofia com dado grande | `explosao_dado_grande` (tempo `T*` explícito) |
| criticidade | limiar `√(a/b)` | `critico_estacionario`, `NSPequeno.enstrofia_limitada` |
| condicionamento | pontes | `BealFLT.beal_iff_mdc_pequeno` (com FLT) |
-/

open Complex Set Filter Topology Real

namespace ATK.Fichas

/-! ## Produtos e anti-produtos -/

/-- Produto material condicional. -/
structure Produto (H Q : Prop) : Prop where
  imp : H → Q

/-- Anti-produto: testemunhas que refutam `Q`, completo (`¬Q ⇒ existe testemunha`). -/
structure AntiProduto (Q : Prop) where
  W : Type
  refuta : W → ¬ Q
  completo : ¬ Q → Nonempty W

/-- **`Q ⟺ não há testemunha`** (anti-produto completo). -/
theorem AntiProduto.iff_vazio {Q : Prop} (A : AntiProduto Q) : Q ↔ IsEmpty A.W := by
  constructor
  · intro hQ; exact ⟨fun w => A.refuta w hQ⟩
  · intro hE; by_contra hQ; obtain ⟨w⟩ := A.completo hQ; exact hE.false w

/-- Um produto cuja hipótese é habitada esvazia o anti-produto. -/
theorem descarga {H Q : Prop} (P : Produto H Q) (A : AntiProduto Q) (h : H) : IsEmpty A.W :=
  (A.iff_vazio).mp (P.imp h)

/-- Uma testemunha refuta a hipótese de todo produto (contrapositivo material). -/
theorem contrapositivo {H Q : Prop} (P : Produto H Q) (A : AntiProduto Q) (w : A.W) : ¬ H :=
  fun h => A.refuta w (P.imp h)

/-- **A "lei" `Nonempty H ↔ IsEmpty W` não vale em geral.** -/
theorem metateorema_falso :
    ¬ ∀ (H Q : Prop) (_ : Produto H Q) (A : AntiProduto Q), (Nonempty H ↔ IsEmpty A.W) := by
  intro h
  have hP : Produto False True := ⟨fun _ => trivial⟩
  let A : AntiProduto True := ⟨Empty, fun w => Empty.elim w, fun h => absurd trivial h⟩
  have := (h False True hP A).mpr (inferInstanceAs (IsEmpty Empty))
  exact (not_nonempty_iff.mpr inferInstance) this

/-! ## Fichas -/

/-- Ficha exata de uma conjectura. -/
structure Ficha (C : Prop) where
  provado : Prop
  prova : provado
  refutado : Prop
  refutacao : ¬ refutado
  lacuna : Prop
  reducao : C ↔ lacuna

/-- Ficha parcial (quando a conjectura depende de um modelo ausente da Mathlib). -/
structure FichaParcial where
  provado : Prop
  prova : provado
  refutado : Prop
  refutacao : ¬ refutado

/-! ### Riemann -/

open ATK.ZetaSimetria ATK.ZetaRetangulo ATK.ZetaRegiao ATK.ForaDaLinha in
/-- Anti-produto de RH: os zeros fora da linha. -/
def antiRiemann : AntiProduto RiemannHypothesis where
  W := ZeroFora
  refuta := fun ρ h => (riemann_iff_vazio.mp h).false ρ
  completo := nao_riemann_iff.mp

/-- Parte refutada de RH: "todo zero de ζ tem parte real 1/2" é falso (`ζ(−2) = 0`). -/
theorem todo_zero_na_reta_falso : ¬ ∀ s : ℂ, riemannZeta s = 0 → s.re = 1 / 2 := by
  intro h
  have hz := riemannZeta_neg_two_mul_nat_add_one 0
  have := h _ hz
  norm_num at this

open ATK.ZetaSimetria ATK.ZetaRetangulo ATK.ZetaRegiao ATK.ForaDaLinha in
/-- **Ficha de Riemann.** -/
def fichaRiemann : Ficha RiemannHypothesis where
  provado := (∀ s ∈ Z, 1 / (256 * A s.im) < s.re ∧ s.re < 1 - 1 / (256 * A s.im)) ∧
    (∀ s ∈ Z, 3 / 4 ≤ s.im ^ 2)
  prova := ⟨faixa_estreitada, sem_zeros_ate_altura⟩
  refutado := ∀ s : ℂ, riemannZeta s = 0 → s.re = 1 / 2
  refutacao := todo_zero_na_reta_falso
  lacuna := IsEmpty ZeroFora
  reducao := riemann_iff_vazio

/-! ### Beal -/

open ATK.Conditional.Beal ATK.BealResidual ATK.BealReduction in
/-- Anti-produto de Beal: os contraexemplos primitivos. -/
def antiBeal : AntiProduto BealConjecture where
  W := {t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ //
    0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 2 < t.2.2.2.1 ∧ 2 < t.2.2.2.2.1 ∧ 2 < t.2.2.2.2.2 ∧
      Nat.Coprime t.1 t.2.1 ∧ t.1 ^ t.2.2.2.1 + t.2.1 ^ t.2.2.2.2.1 = t.2.2.1 ^ t.2.2.2.2.2}
  refuta := fun t h => by
    obtain ⟨ha, hb, hc, hx, hy, hz, hab, heq⟩ := t.2
    exact (beal_iff_primitive.mp h) _ _ _ _ _ _ ha hb hc hx hy hz hab heq
  completo := fun h => by
    rw [beal_iff_primitive] at h
    simp only [BealPrimitive, not_forall] at h
    obtain ⟨a, b, c, x, y, z, ha, hb, hc, hx, hy, hz, hab, heq⟩ := h
    exact ⟨⟨(a, b, c, x, y, z), ha, hb, hc, hx, hy, hz, hab, not_not.mp heq⟩⟩

/-- Parte refutada de Beal: "não há solução nenhuma com expoentes `> 2`" é falso
(`2³ + 2³ = 2⁴`): a conclusão de Beal (fator primo comum) não pode ser trocada por inexistência. -/
theorem sem_solucao_alguma_falso :
    ¬ ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z → a ^ x + b ^ y ≠ c ^ z :=
  fun h => h 2 2 2 3 3 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

open ATK.Conditional.Beal ATK.BealResidual ATK.BealReduction in
/-- **Ficha de Beal.** -/
def fichaBeal : Ficha BealConjecture where
  provado := ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c →
    (3 ∣ Nat.gcd x (Nat.gcd y z) ∨ 4 ∣ Nat.gcd x (Nat.gcd y z)) → a ^ x + b ^ y ≠ c ^ z
  prova := fun _ _ _ _ _ _ ha hb hc h => sem_solucao_mdc ha hb hc h
  refutado := ∀ a b c x y z : ℕ, 0 < a → 0 < b → 0 < c → 2 < x → 2 < y → 2 < z →
    a ^ x + b ^ y ≠ c ^ z
  refutacao := sem_solucao_alguma_falso
  lacuna := ExclusaoResidualPairwise
  reducao := beal_iff_residual_pairwise

/-! ### Yang–Mills (modelo de rede) -/

open ATK.YMToy in
/-- Parte refutada: **não existe gap uniforme** em `β` na rede. -/
theorem gap_uniforme_falso : ¬ ∃ Δ : ℝ, 0 < Δ ∧ ∀ β : ℝ, 0 < β → Δ ≤ massa β := by
  rintro ⟨Δ, hΔ, h⟩
  obtain ⟨β, h1, h2⟩ :=
    ((massa_tende_zero.eventually (gt_mem_nhds hΔ)).and (eventually_gt_atTop 0)).exists
  exact absurd (h β h2) (not_le.mpr h1)

open ATK.YMToy in
def fichaYM : FichaParcial where
  provado := ∀ β : ℝ, 0 < β → 0 < massa β
  prova := fun _ hβ => massa_pos hβ
  refutado := ∃ Δ : ℝ, 0 < Δ ∧ ∀ β : ℝ, 0 < β → Δ ≤ massa β
  refutacao := gap_uniforme_falso

/-! ### P vs NP (circuitos) -/

open ATK.Shannon in
/-- Parte refutada: "toda família de funções booleanas tem circuitos polinomiais" é falso. -/
theorem tudo_em_Ppoly_falso :
    ¬ ∀ f : ∀ n : ℕ, (Fin n → Bool) → Bool, ∃ k : ℕ, ∀ᶠ n in atTop, TemCircuito (f n) (n ^ k) := by
  intro h
  obtain ⟨f, hf⟩ := familia_fora_de_Ppoly
  obtain ⟨k, hk⟩ := h f
  obtain ⟨n, h1, h2⟩ := (hk.and (hf k)).exists
  exact h2 h1

open ATK.Shannon in
def fichaPNP : FichaParcial where
  provado := ∀ n : ℕ, 4 ≤ n → ∃ f : (Fin n → Bool) → Bool, ¬ TemCircuito f (2 ^ n / (8 * n))
  prova := shannon
  refutado := ∀ f : ∀ n : ℕ, (Fin n → Bool) → Bool, ∃ k : ℕ, ∀ᶠ n in atTop,
    TemCircuito (f n) (n ^ k)
  refutacao := tudo_em_Ppoly_falso

/-! ### BSD (curvas congruentes) -/

/-- Parte refutada: "toda curva `y² = x³ − n²x` só tem pontos racionais com `y = 0`" é falso
(`n = 6`, ponto `(−3, 9)`), ao contrário de `n = 1`. -/
theorem so_dois_torcao_falso :
    ¬ ∀ n : ℚ, n ≠ 0 → ∀ x y : ℚ, y ^ 2 = x ^ 3 - n ^ 2 * x → y = 0 := by
  intro h
  have := h 6 (by norm_num) (-3) 9 (by norm_num)
  norm_num at this

def fichaBSD : FichaParcial where
  provado := ∀ x y : ℚ, y ^ 2 = x ^ 3 - x → y = 0
  prova := fun _ _ h => ATK.CongruentCurve.y_eq_zero h
  refutado := ∀ n : ℚ, n ≠ 0 → ∀ x y : ℚ, y ^ 2 = x ^ 3 - n ^ 2 * x → y = 0
  refutacao := so_dois_torcao_falso


/-! ### Condicionamento: a ponte B2 reduzida aos primos `≥ 5` -/

/-- **FLT ⟺ FLT para todo primo `p ≥ 5`** (FLT(3), FLT(4) da Mathlib). -/
theorem flt_iff_primos_ge_cinco :
    FermatLastTheorem ↔ ∀ p : ℕ, p.Prime → 5 ≤ p → FermatLastTheoremFor p := by
  constructor
  · intro h p _ hp5
    exact h p (by omega)
  · intro h
    refine FermatLastTheorem.of_odd_primes fun p hp hodd => ?_
    by_cases h3 : p = 3
    · subst h3; exact fermatLastTheoremThree
    · have h2 := hp.two_le
      have hne2 : p ≠ 2 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hodd) even_two
      have hne4 : p ≠ 4 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hodd) ⟨2, rfl⟩
      exact h p hp (by omega)

/-! ### Navier–Stokes: o parâmetro de explosão -/

/-- `D(t) = b − k e^{2at}`. -/
noncomputable def Dexp (a b k t : ℝ) : ℝ := b - k * rexp (2 * a * t)

/-- Solução explícita de `y' = −a y + b y³`: `y(t) = √(a / (b − k e^{2at}))`. -/
noncomputable def yExp (a b k t : ℝ) : ℝ := Real.sqrt (a / Dexp a b k t)

/-- Tempo de explosão `T* = log(b/k)/(2a)`. -/
noncomputable def Tstar (a b k : ℝ) : ℝ := Real.log (b / k) / (2 * a)

theorem Dexp_pos {a b k t : ℝ} (ha : 0 < a) (hk : 0 < k) (hkb : k < b) (ht : t < Tstar a b k) :
    0 < Dexp a b k t := by
  unfold Dexp Tstar at *
  have h1 : 2 * a * t < Real.log (b / k) := by
    rw [lt_div_iff₀ (by linarith)] at ht; linarith
  have h2 : rexp (2 * a * t) < b / k := by
    calc rexp (2 * a * t) < rexp (Real.log (b / k)) := Real.exp_lt_exp.mpr h1
      _ = b / k := Real.exp_log (div_pos (by linarith) hk)
  rw [lt_div_iff₀ hk] at h2
  linarith

theorem Dexp_Tstar {a b k : ℝ} (ha : 0 < a) (hk : 0 < k) (hkb : k < b) :
    Dexp a b k (Tstar a b k) = 0 := by
  unfold Dexp Tstar
  rw [show 2 * a * (Real.log (b / k) / (2 * a)) = Real.log (b / k) by field_simp,
    Real.exp_log (div_pos (by linarith) hk)]
  field_simp
  ring

/-- `yExp` resolve `y' = −a y + b y³` antes de `T*`. -/
theorem yExp_deriv {a b k t : ℝ} (ha : 0 < a) (hk : 0 < k) (hkb : k < b) (ht : t < Tstar a b k) :
    HasDerivAt (yExp a b k) (-a * yExp a b k t + b * yExp a b k t ^ 3) t := by
  have hD := Dexp_pos ha hk hkb ht
  have hDd : HasDerivAt (Dexp a b k) (-(k * (rexp (2 * a * t) * (2 * a)))) t := by
    unfold Dexp
    have h1 : HasDerivAt (fun s => 2 * a * s) (2 * a) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * a)
    simpa using (h1.exp.const_mul k).const_sub b
  have hz : HasDerivAt (fun s => a / Dexp a b k s)
      ((0 * Dexp a b k t - a * (-(k * (rexp (2 * a * t) * (2 * a))))) / Dexp a b k t ^ 2) t :=
    (hasDerivAt_const t a).div hDd hD.ne'
  have hzpos : 0 < a / Dexp a b k t := div_pos ha hD
  have hy := hz.sqrt hzpos.ne'
  unfold yExp
  convert hy using 1
  set w := Real.sqrt (a / Dexp a b k t) with hw
  have hw0 : 0 < w := Real.sqrt_pos.mpr hzpos
  have hw2 : w ^ 2 = a / Dexp a b k t := Real.sq_sqrt hzpos.le
  have hE : k * (rexp (2 * a * t) * (2 * a)) = 2 * a * (b - Dexp a b k t) := by unfold Dexp; ring
  have hD' := hD.ne'
  rw [eq_div_iff (by positivity), show (-a * w + b * w ^ 3) * (2 * w) = 2 * w ^ 2 * (-a + b * w ^ 2) by
    ring, hw2, hE]
  field_simp
  ring

/-- **Explosão**: `yExp → +∞` quando `t → T*⁻`. -/
theorem yExp_explode {a b k : ℝ} (ha : 0 < a) (hk : 0 < k) (hkb : k < b) :
    Tendsto (yExp a b k) (𝓝[<] Tstar a b k) atTop := by
  have hcont : Continuous (Dexp a b k) := by unfold Dexp; fun_prop
  have h0 : Tendsto (Dexp a b k) (𝓝[<] Tstar a b k) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := (hcont.tendsto (Tstar a b k)).mono_left
        (nhdsWithin_le_nhds : 𝓝[<] Tstar a b k ≤ 𝓝 (Tstar a b k))
      rwa [Dexp_Tstar ha hk hkb] at this
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact Dexp_pos ha hk hkb ht
  have h1 : Tendsto (fun t => a / Dexp a b k t) (𝓝[<] Tstar a b k) atTop := by
    have := (h0.inv_tendsto_nhdsGT_zero).const_mul_atTop ha
    simpa [div_eq_mul_inv] using this
  exact tendsto_sqrt_atTop.comp h1

/-- **Explosão com dado grande**: se `b y₀² > a`, há solução de `y' = −a y + b y³` com `y(0) = y₀`
que explode no tempo finito `T* = log(b y₀²/(b y₀² − a))/(2a)`. A desigualdade de enstrofia
sozinha **não** dá regularidade global para dados grandes. -/
theorem explosao_dado_grande {a b y0 : ℝ} (ha : 0 < a) (hy0 : 0 < y0)
    (hbig : a < b * y0 ^ 2) :
    ∃ k : ℝ, 0 < k ∧ k < b ∧ 0 < Tstar a b k ∧ yExp a b k 0 = y0 ∧
      (∀ t, t < Tstar a b k → HasDerivAt (yExp a b k) (-a * yExp a b k t + b * yExp a b k t ^ 3) t) ∧
      Tendsto (yExp a b k) (𝓝[<] Tstar a b k) atTop := by
  set k := b - a / y0 ^ 2 with hkdef
  have hy2 : 0 < y0 ^ 2 := by positivity
  have hk : 0 < k := by
    rw [hkdef, sub_pos, div_lt_iff₀ hy2]; linarith
  have hkb : k < b := by
    have : 0 < a / y0 ^ 2 := by positivity
    rw [hkdef]; linarith
  refine ⟨k, hk, hkb, ?_, ?_, fun t ht => yExp_deriv ha hk hkb ht, yExp_explode ha hk hkb⟩
  · unfold Tstar
    have : 1 < b / k := by rw [one_lt_div hk]; exact hkb
    exact div_pos (Real.log_pos this) (by linarith)
  · unfold yExp Dexp
    rw [mul_zero, Real.exp_zero, mul_one, hkdef, show b - (b - a / y0 ^ 2) = a / y0 ^ 2 by ring,
      div_div_cancel₀ ha.ne', Real.sqrt_sq hy0.le]

/-- **Criticidade**: com `b y₀² = a`, a constante `y₀` é solução estacionária. -/
theorem critico_estacionario {a b y0 : ℝ} (hcrit : b * y0 ^ 2 = a) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => y0) (-a * y0 + b * y0 ^ 3) t := by
  have : -a * y0 + b * y0 ^ 3 = 0 := by rw [← hcrit]; ring
  rw [this]; exact hasDerivAt_const t y0

/-- Ficha de Navier–Stokes no nível da desigualdade de enstrofia. -/
def fichaNS (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : FichaParcial where
  provado := ∀ (y y' : ℝ → ℝ) (M : ℝ), 0 < M → y 0 < M → b * M ^ 2 < a →
    (∀ t, HasDerivAt y (y' t) t) → (∀ t, 0 ≤ t → y' t ≤ -a * y t + b * y t ^ 3) →
      ∀ t, 0 ≤ t → y t ≤ M
  prova := fun _ _ _ hM0 hy0 hMa hd hi => ATK.NSPequeno.enstrofia_limitada hb.le hM0 hy0 hMa hd hi
  refutado := ∀ y0 : ℝ, 0 < y0 → ∀ k : ℝ, 0 < k → k < b →
    ∃ C : ℝ, ∀ t, 0 ≤ t → t < Tstar a b k → yExp a b k t ≤ C
  refutacao := by
    intro h
    obtain ⟨C, hC⟩ := h 1 one_pos (b / 2) (by linarith) (by linarith)
    have hT : 0 < Tstar a b (b / 2) := by
      unfold Tstar
      have : (1 : ℝ) < b / (b / 2) := by rw [div_div_eq_mul_div]; field_simp; linarith
      exact div_pos (Real.log_pos this) (by linarith)
    have hev : ∀ᶠ t in 𝓝[<] Tstar a b (b / 2), C < yExp a b (b / 2) t :=
      (yExp_explode ha (by linarith) (by linarith)).eventually (eventually_gt_atTop C)
    have hev2 : ∀ᶠ t in 𝓝[<] Tstar a b (b / 2), 0 < t := by
      have : Ioo 0 (Tstar a b (b / 2)) ∈ 𝓝[<] Tstar a b (b / 2) := Ioo_mem_nhdsLT hT
      filter_upwards [this] with t ht using ht.1
    have hev3 : ∀ᶠ t in 𝓝[<] Tstar a b (b / 2), t ∈ Iio (Tstar a b (b / 2)) := self_mem_nhdsWithin
    obtain ⟨t, ⟨h1, h2⟩, h3⟩ := ((hev.and hev2).and hev3).exists
    exact absurd (hC t h2.le h3) (not_le.mpr h1)

end ATK.Fichas

#print axioms ATK.Fichas.AntiProduto.iff_vazio
#print axioms ATK.Fichas.descarga
#print axioms ATK.Fichas.contrapositivo
#print axioms ATK.Fichas.metateorema_falso
#print axioms ATK.Fichas.todo_zero_na_reta_falso
#print axioms ATK.Fichas.sem_solucao_alguma_falso
#print axioms ATK.Fichas.gap_uniforme_falso
#print axioms ATK.Fichas.tudo_em_Ppoly_falso
#print axioms ATK.Fichas.so_dois_torcao_falso
#print axioms ATK.Fichas.flt_iff_primos_ge_cinco
#print axioms ATK.Fichas.Dexp_pos
#print axioms ATK.Fichas.Dexp_Tstar
#print axioms ATK.Fichas.yExp_deriv
#print axioms ATK.Fichas.yExp_explode
#print axioms ATK.Fichas.explosao_dado_grande
#print axioms ATK.Fichas.critico_estacionario
#print axioms ATK.Fichas.antiRiemann
#print axioms ATK.Fichas.fichaRiemann
#print axioms ATK.Fichas.antiBeal
#print axioms ATK.Fichas.fichaBeal
#print axioms ATK.Fichas.fichaYM
#print axioms ATK.Fichas.fichaPNP
#print axioms ATK.Fichas.fichaBSD
#print axioms ATK.Fichas.fichaNS
