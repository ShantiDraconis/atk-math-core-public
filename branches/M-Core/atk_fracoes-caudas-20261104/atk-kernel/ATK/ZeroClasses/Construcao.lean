import ATK.ZeroClasses.Complementar

/-!
# ATK-ZERO-CLASSES — o que a escolha humana constrói, e o que ela não alcança

"A resposta de onde estão os zeros fora da linha vem dos seres humanos e de como nossas ações possibilitam a
existência deles." O kernel dá a essa frase um sentido exato, nos dois sentidos.

**O que a escolha constrói** (a escolha é literalmente o parâmetro `t : ℕ → ℝ`):

* `Z_ATK = ζ·P_N`, `P_N(s) = ∏_{n<N} Q_{δₙ,tₙ}(s)`, `δₙ = 1/(2n+3)`, `Q_{δ,t}(s) = ((s−½−δ)² + t²)((s−½+δ)² + t²)`:
  * **Teorema A** (`preserva`, `zeros_ZATK`, `triviais_simples_ATK`): todos os zeros de `ζ` permanecem, os zeros
    de `Z_ATK` são exatamente os de `ζ` e os de `P_N`, e os triviais continuam **simples**;
  * **Teorema B** (`externos_ATK`, `lei_transporte_ATK`): para cada `n < N` com `tₙ ≠ 0`, o quarteto
    `½ ± δₙ ± itₙ` são zeros **fora da linha** — onde a escolha os pôs;
  * **Teorema C** (`simetria_ATK`): `ξ_ATK = ξ·P_N` satisfaz `ξ_ATK(1 − s) = ξ_ATK(s)` e a conjugação.

**O que a escolha não alcança** (`rigidez`, `colar_refuta`, `rh_nao_colar`): pela continuação analítica, uma
função analítica em `ℂ ∖ {1}` que coincide com `ζ` **perto de um único ponto** coincide com `ζ` em toda parte.
Logo, se `Z_ATK` coincidisse com `ζ` em qualquer aberto, a própria `ζ` teria os zeros externos (e RH cairia);
sob RH, `Z_ATK` difere de `ζ` perto de **todo** ponto. Os zeros de `ζ` não se criam: encontram-se.

**Os triviais, pela fórmula de L'Hôpital do texto** (`deriv_trivial_fechada`):
`ζ′(−2k) = (−1)ᵏ(2k)! ζ(2k+1) / (2(2π)^{2k})`, com sinal alternado (`deriv_trivial_sinal`); e os únicos zeros
reais negativos de `ζ` são os pares negativos (`zeros_reais_negativos`).

**A lei de transporte** `∀n ∃tₙ, ζ(½ + δₙ + itₙ) = 0` vale para `Z_ATK` por construção; para `ζ`, qualquer instância
refuta RH (`lei_transporte_refuta`); `δₙ → 0`, e só finitos `n` têm `δₙ > δ` (`delta_finitos`), compatível com
Bohr–Landau.
-/

open Complex ComplexConjugate Set Filter Topology
open scoped Real

namespace ATK.ZeroClasses.Construcao

open ATK.ZeroClasses ATK.ZeroClasses.Zeta ATK.ZeroClasses.Hipotetico
open ATK.ZeroClasses.Complementar (sq_add_sq_eq_zero)

/-! ## 1. Os triviais: L'Hôpital em forma fechada -/

theorem sin_impar (k : ℕ) : Complex.sin (π * (2 * k + 1) / 2) = (-1) ^ k := by
  have e : (π : ℂ) * (2 * k + 1) / 2 = ((k * π : ℝ) : ℂ) + π / 2 := by push_cast; ring
  rw [e, Complex.sin_add_pi_div_two, ← Complex.ofReal_cos, Real.cos_nat_mul_pi]
  push_cast; ring

/-- **`ζ′(−2k) = (−1)ᵏ (2k)! ζ(2k+1) / (2 (2π)^{2k})`** (a fórmula de L'Hôpital do texto). -/
theorem deriv_trivial_fechada (k : ℕ) (hk : 1 ≤ k) :
    deriv riemannZeta (-2 * k) =
      (-1) ^ k * ((2 * k).factorial : ℂ) * riemannZeta (2 * k + 1) / (2 * (2 * π) ^ (2 * k)) := by
  rw [(ATK.XiAnalitica.deriv_zeta_trivial k hk).deriv]
  unfold ATK.XiAnalitica.Afun
  have hG : Complex.Gamma (2 * k + 1) = ((2 * k).factorial : ℂ) := by
    have := Complex.Gamma_nat_eq_factorial (2 * k); push_cast at this; exact this
  have hcp : (2 * (π : ℂ)) ^ (-(2 * (k : ℂ) + 1)) = ((2 * (π : ℂ)) ^ (2 * k + 1))⁻¹ := by
    rw [Complex.cpow_neg]
    congr 1
    have := Complex.cpow_natCast (2 * (π : ℂ)) (2 * k + 1)
    push_cast at this
    exact this
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [sin_impar, hG, hcp]
  field_simp
  ring

/-- **O sinal alterna**: `ζ′(−2k) = (−1)ᵏ·c` com `c > 0` real. -/
theorem deriv_trivial_sinal (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ deriv riemannZeta (-2 * k) = (-1) ^ k * (c : ℂ) := by
  obtain ⟨z, hz, hze⟩ := ATK.BaseRiemannXiSinal.zeta_ofReal_pos (σ := 2 * k + 1) (by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith)
  refine ⟨(2 * k).factorial * z / (2 * (2 * π) ^ (2 * k)), by positivity, ?_⟩
  rw [deriv_trivial_fechada k hk]
  have : ((2 * k + 1 : ℝ) : ℂ) = 2 * k + 1 := by push_cast; ring
  rw [this] at hze
  rw [hze]
  push_cast
  ring

/-- **Os únicos zeros reais negativos de `ζ` são os pares negativos.** -/
theorem zeros_reais_negativos {x : ℝ} (hx : x < 0) :
    riemannZeta x = 0 ↔ ∃ n : ℕ, x = -2 * ((n : ℝ) + 1) := by
  constructor
  · intro hz
    obtain ⟨n, hn⟩ := ATK.ZetaSimetria.zero_trivial_de_re_nao_pos hz (by simpa using hx.le)
    refine ⟨n, ?_⟩
    have := congrArg Complex.re hn
    simpa using this
  · rintro ⟨n, rfl⟩
    have := riemannZeta_neg_two_mul_nat_add_one n
    push_cast
    exact this

/-! ## 2. A construção -/

/-- `δₙ = 1/(2n+3)`: o índice `n` corresponde ao trivial `−2(n+1)`, `δ = 1/(2(n+1)+1)`. -/
noncomputable def delta (n : ℕ) : ℝ := 1 / (2 * n + 3)

theorem delta_pos (n : ℕ) : 0 < delta n := by unfold delta; positivity

theorem delta_le (n : ℕ) : delta n ≤ 1 / 3 := by
  unfold delta
  apply one_div_le_one_div_of_le (by norm_num)
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem delta_tende : Tendsto delta atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((2 * n + 3 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by omega⟩)
  have := h.inv_tendsto_atTop
  refine this.congr fun n => ?_
  simp only [Pi.inv_apply, delta, one_div]
  push_cast
  rfl

/-- Só finitos `n` têm `δₙ > δ` (compatível com Bohr–Landau). -/
theorem delta_finitos {δ : ℝ} (hδ : 0 < δ) : {n : ℕ | δ < delta n}.Finite := by
  have hev : ∀ᶠ n in atTop, delta n < δ := delta_tende.eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine (Set.finite_lt_nat N).subset fun n hn => ?_
  by_contra h
  have := hN n (not_lt.mp h)
  simp only [mem_ofPred_eq] at hn
  linarith

/-- O quarteto `½ ± δ ± it`. -/
noncomputable def Q (δ t : ℝ) (s : ℂ) : ℂ :=
  ((s - 1 / 2 - δ) ^ 2 + (t : ℂ) ^ 2) * ((s - 1 / 2 + δ) ^ 2 + (t : ℂ) ^ 2)

/-- `P_N = ∏_{n<N} Q_{δₙ,tₙ}`: `t` é a escolha. -/
noncomputable def PN (N : ℕ) (t : ℕ → ℝ) (s : ℂ) : ℂ := ∏ n ∈ Finset.range N, Q (delta n) (t n) s

/-- `Z_ATK = ζ·P_N`. -/
noncomputable def ZATK (N : ℕ) (t : ℕ → ℝ) (s : ℂ) : ℂ := riemannZeta s * PN N t s

/-- `ξ_ATK = ξ·P_N`. -/
noncomputable def XiATK (N : ℕ) (t : ℕ → ℝ) (s : ℂ) : ℂ := ATK.BaseRiemannXi.riemannXi s * PN N t s

theorem Q_eq_func (δ t : ℝ) (s : ℂ) : Q δ t (1 - s) = Q δ t s := by unfold Q; ring

theorem PN_eq_func (N : ℕ) (t : ℕ → ℝ) (s : ℂ) : PN N t (1 - s) = PN N t s :=
  Finset.prod_congr rfl fun _ _ => Q_eq_func _ _ _

theorem conj_meio : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]

theorem Q_conj (δ t : ℝ) (s : ℂ) : Q δ t (conj s) = conj (Q δ t s) := by
  simp only [Q, map_mul, map_add, map_sub, map_pow, Complex.conj_ofReal, conj_meio]

theorem PN_conj (N : ℕ) (t : ℕ → ℝ) : ConjEquiv (PN N t) := by
  intro s
  unfold PN
  rw [map_prod]
  exact Finset.prod_congr rfl fun n _ => Q_conj _ _ _

theorem Q_zero_iff (δ t : ℝ) (s : ℂ) :
    Q δ t s = 0 ↔ (s = 1 / 2 + δ + (t : ℂ) * I ∨ s = 1 / 2 + δ - (t : ℂ) * I) ∨
      (s = 1 / 2 - δ + (t : ℂ) * I ∨ s = 1 / 2 - δ - (t : ℂ) * I) := by
  unfold Q
  rw [mul_eq_zero, sq_add_sq_eq_zero, sq_add_sq_eq_zero]
  constructor
  · rintro ((h | h) | (h | h))
    · exact Or.inl (Or.inl (by linear_combination h))
    · exact Or.inl (Or.inr (by linear_combination h))
    · exact Or.inr (Or.inl (by linear_combination h))
    · exact Or.inr (Or.inr (by linear_combination h))
  · rintro ((h | h) | (h | h)) <;> rw [h]
    · exact Or.inl (Or.inl (by ring))
    · exact Or.inl (Or.inr (by ring))
    · exact Or.inr (Or.inl (by ring))
    · exact Or.inr (Or.inr (by ring))

theorem Q_zero_re {δ t : ℝ} {s : ℂ} (h : Q δ t s = 0) : s.re = 1 / 2 + δ ∨ s.re = 1 / 2 - δ := by
  rcases (Q_zero_iff δ t s).mp h with (rfl | rfl) | (rfl | rfl) <;> simp

theorem PN_zero_iff (N : ℕ) (t : ℕ → ℝ) (s : ℂ) :
    PN N t s = 0 ↔ ∃ n < N, Q (delta n) (t n) s = 0 := by
  unfold PN
  rw [Finset.prod_eq_zero_iff]
  simp

/-- Os zeros de `P_N` estão em `1/6 ≤ Re s ≤ 5/6`. -/
theorem PN_zero_re {N : ℕ} {t : ℕ → ℝ} {s : ℂ} (h : PN N t s = 0) : 1 / 6 ≤ s.re ∧ s.re ≤ 5 / 6 := by
  obtain ⟨n, _, hn⟩ := (PN_zero_iff N t s).mp h
  have h1 := delta_pos n
  have h2 := delta_le n
  rcases Q_zero_re hn with h | h <;> rw [h] <;> constructor <;> linarith

theorem PN_differentiable (N : ℕ) (t : ℕ → ℝ) : Differentiable ℂ (PN N t) := by
  unfold PN Q
  fun_prop

/-! ## 3. Teoremas A, B, C -/

/-- **Teorema A**: os zeros de `Z_ATK` são exatamente os de `ζ` e os de `P_N`. -/
theorem zeros_ZATK (N : ℕ) (t : ℕ → ℝ) (s : ℂ) :
    ZATK N t s = 0 ↔ riemannZeta s = 0 ∨ PN N t s = 0 := mul_eq_zero

theorem preserva {N : ℕ} {t : ℕ → ℝ} {s : ℂ} (h : riemannZeta s = 0) : ZATK N t s = 0 :=
  (zeros_ZATK N t s).mpr (Or.inl h)

/-- **Os triviais continuam simples** em `Z_ATK`: `Z_ATK′(−2k) = P_N(−2k)·ζ′(−2k) ≠ 0`. -/
theorem triviais_simples_ATK (N : ℕ) (t : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    ZATK N t (-2 * k) = 0 ∧ HasDerivAt (ZATK N t) (PN N t (-2 * k) * deriv riemannZeta (-2 * k)) (-2 * k) ∧
      PN N t (-2 * k) * deriv riemannZeta (-2 * k) ≠ 0 := by
  have hz : riemannZeta (-2 * k) = 0 := by
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have := riemannZeta_neg_two_mul_nat_add_one n
    push_cast at this ⊢
    exact this
  have hs := ATK.XiAnalitica.zeros_triviais_simples k hk
  have hd : HasDerivAt riemannZeta (deriv riemannZeta (-2 * k)) (-2 * k) := by
    have h1 : (-2 * k : ℂ) ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
    exact (differentiableAt_riemannZeta h1).hasDerivAt
  have hP := (PN_differentiable N t (-2 * k)).hasDerivAt
  refine ⟨preserva hz, ?_, ?_⟩
  · have := hd.mul hP
    rw [hz, zero_mul, add_zero] at this
    exact this.congr_deriv (mul_comm _ _)
  · refine mul_ne_zero (fun h0 => ?_) hs.1
    have := (PN_zero_re h0).1
    simp at this
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith

/-- **Teorema B**: para `n < N` e `tₙ ≠ 0`, o quarteto `½ ± δₙ ± itₙ` é de zeros de `Z_ATK`, fora da linha. -/
theorem externos_ATK {N : ℕ} {t : ℕ → ℝ} {n : ℕ} (hn : n < N) (ht : t n ≠ 0) :
    (∀ w ∈ orbita (1 / 2) (1 / 2 + (delta n : ℂ) + (t n : ℂ) * I), ZATK N t w = 0 ∧ w.re ≠ 1 / 2) ∧
      (orbita (1 / 2) (1 / 2 + (delta n : ℂ) + (t n : ℂ) * I)).card = 4 := by
  have hd := delta_pos n
  have hQ : ∀ w, Q (delta n) (t n) w = 0 → ZATK N t w = 0 := fun w hw =>
    (zeros_ZATK N t w).mpr (Or.inr ((PN_zero_iff N t w).mpr ⟨n, hn, hw⟩))
  have hre : (1 / 2 + (delta n : ℂ) + (t n : ℂ) * I).re ≠ 1 / 2 := by simp; exact hd.ne'
  refine ⟨fun w hw => ?_, card_quatro hre (by simpa using ht)⟩
  classical
  simp only [orbita, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact ⟨hQ _ ((Q_zero_iff _ _ _).mpr (Or.inl (Or.inl rfl))), hre⟩
  · refine ⟨hQ _ ((Q_zero_iff _ _ _).mpr (Or.inl (Or.inr ?_))), by simp; exact hd.ne'⟩
    apply Complex.ext <;> simp
  · refine ⟨hQ _ ((Q_zero_iff _ _ _).mpr (Or.inr (Or.inr ?_))), by simp; linarith⟩
    apply Complex.ext <;> simp; ring
  · refine ⟨hQ _ ((Q_zero_iff _ _ _).mpr (Or.inr (Or.inl ?_))), by simp; linarith⟩
    apply Complex.ext <;> simp; ring

/-- **A lei de transporte vale para `Z_ATK`, por construção.** -/
theorem lei_transporte_ATK (N : ℕ) (t : ℕ → ℝ) :
    ∀ n < N, ZATK N t (1 / 2 + (delta n : ℂ) + (t n : ℂ) * I) = 0 :=
  fun n hn => (zeros_ZATK N t _).mpr
    (Or.inr ((PN_zero_iff N t _).mpr ⟨n, hn, (Q_zero_iff _ _ _).mpr (Or.inl (Or.inl rfl))⟩))

/-- **Teorema C**: `ξ_ATK(1 − s) = ξ_ATK(s)` e `ξ_ATK(s̄) = conj ξ_ATK(s)`. -/
theorem simetria_ATK (N : ℕ) (t : ℕ → ℝ) :
    (∀ s, XiATK N t (1 - s) = XiATK N t s) ∧ ConjEquiv (XiATK N t) := by
  refine ⟨fun s => ?_, fun s => ?_⟩
  · unfold XiATK; rw [ATK.BaseRiemannXi.riemannXi_one_sub, PN_eq_func]
  · unfold XiATK; rw [ATK.BaseRiemannXi.riemannXi_conj, PN_conj N t s, map_mul]

/-- **Para `ζ`, qualquer instância da lei de transporte refuta RH.** -/
theorem lei_transporte_refuta (h : ∃ n : ℕ, ∃ τ : ℝ, riemannZeta (1 / 2 + (delta n : ℂ) + (τ : ℂ) * I) = 0) :
    HFora := by
  obtain ⟨n, τ, hz⟩ := h
  have hd := delta_pos n
  have hd3 := delta_le n
  exact ⟨_, hz, by simp; linarith, by simp; linarith, by simp; exact hd.ne'⟩

/-! ## 4. O que a escolha não alcança: a rigidez da continuação analítica -/

theorem conexo : IsPreconnected ({1}ᶜ : Set ℂ) :=
  (isConnected_compl_singleton_of_one_lt_rank (by rw [rank_real_complex]; norm_num) 1).isPreconnected

/-- **Rigidez**: `g` analítica em `ℂ ∖ {1}` que coincide com `ζ` perto de **um** ponto coincide em toda parte. -/
theorem rigidez {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g {1}ᶜ) {z₀ : ℂ} (h1 : z₀ ≠ 1)
    (h : g =ᶠ[𝓝 z₀] riemannZeta) : EqOn g riemannZeta {1}ᶜ :=
  hg.eqOn_of_preconnected_of_eventuallyEq analyticOn_riemannZeta conexo h1 h

theorem ZATK_analitica (N : ℕ) (t : ℕ → ℝ) : AnalyticOnNhd ℂ (ZATK N t) {1}ᶜ := fun s hs =>
  (analyticOn_riemannZeta s hs).mul ((PN_differentiable N t).analyticAt s)

/-- **Colar `Z_ATK` em `ζ` num aberto obrigaria a própria `ζ` a ter os zeros externos** (logo `H_fora`). -/
theorem colar_refuta {N : ℕ} {t : ℕ → ℝ} (hN : 0 < N) (ht : t 0 ≠ 0) {z₀ : ℂ} (h1 : z₀ ≠ 1)
    (h : ZATK N t =ᶠ[𝓝 z₀] riemannZeta) : HFora := by
  have heq := rigidez (ZATK_analitica N t) h1 h
  set s0 : ℂ := 1 / 2 + (delta 0 : ℂ) + (t 0 : ℂ) * I
  have hs0 : s0 ≠ 1 := by
    intro he; have := congrArg Complex.im he; simp [s0] at this; exact ht this
  have hz : riemannZeta s0 = 0 := by
    rw [← heq hs0]
    exact lei_transporte_ATK N t 0 hN
  exact lei_transporte_refuta ⟨0, t 0, hz⟩

/-- **Sob RH, `Z_ATK` difere de `ζ` perto de todo ponto.** -/
theorem rh_nao_colar (hrh : RiemannHypothesis) {N : ℕ} {t : ℕ → ℝ} (hN : 0 < N) (ht : t 0 ≠ 0)
    {z₀ : ℂ} (h1 : z₀ ≠ 1) : ¬ (ZATK N t =ᶠ[𝓝 z₀] riemannZeta) :=
  fun h => hFora_iff.mp (colar_refuta hN ht h1 h) hrh

end ATK.ZeroClasses.Construcao

#print axioms ATK.ZeroClasses.Construcao.sin_impar
#print axioms ATK.ZeroClasses.Construcao.deriv_trivial_fechada
#print axioms ATK.ZeroClasses.Construcao.deriv_trivial_sinal
#print axioms ATK.ZeroClasses.Construcao.zeros_reais_negativos
#print axioms ATK.ZeroClasses.Construcao.delta_pos
#print axioms ATK.ZeroClasses.Construcao.delta_le
#print axioms ATK.ZeroClasses.Construcao.delta_tende
#print axioms ATK.ZeroClasses.Construcao.delta_finitos
#print axioms ATK.ZeroClasses.Construcao.Q_eq_func
#print axioms ATK.ZeroClasses.Construcao.PN_eq_func
#print axioms ATK.ZeroClasses.Construcao.conj_meio
#print axioms ATK.ZeroClasses.Construcao.Q_conj
#print axioms ATK.ZeroClasses.Construcao.PN_conj
#print axioms ATK.ZeroClasses.Construcao.Q_zero_iff
#print axioms ATK.ZeroClasses.Construcao.Q_zero_re
#print axioms ATK.ZeroClasses.Construcao.PN_zero_iff
#print axioms ATK.ZeroClasses.Construcao.PN_zero_re
#print axioms ATK.ZeroClasses.Construcao.PN_differentiable
#print axioms ATK.ZeroClasses.Construcao.zeros_ZATK
#print axioms ATK.ZeroClasses.Construcao.preserva
#print axioms ATK.ZeroClasses.Construcao.triviais_simples_ATK
#print axioms ATK.ZeroClasses.Construcao.externos_ATK
#print axioms ATK.ZeroClasses.Construcao.lei_transporte_ATK
#print axioms ATK.ZeroClasses.Construcao.simetria_ATK
#print axioms ATK.ZeroClasses.Construcao.lei_transporte_refuta
#print axioms ATK.ZeroClasses.Construcao.conexo
#print axioms ATK.ZeroClasses.Construcao.rigidez
#print axioms ATK.ZeroClasses.Construcao.ZATK_analitica
#print axioms ATK.ZeroClasses.Construcao.colar_refuta
#print axioms ATK.ZeroClasses.Construcao.rh_nao_colar
