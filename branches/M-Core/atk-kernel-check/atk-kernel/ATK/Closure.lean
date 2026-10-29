import Mathlib
import ATK.Exact

/-!
# ATK — Fechamento de OPEN_MATH: o que é, onde mora, e o que o tornaria falso

Resposta formal (verificada pelo kernel) às propostas de 12–13/10 (`TerminalCertificates`,
`ClosedMath := Nonempty TerminalCertificates`, `OpenMath := ¬ ClosedMath`, AGOT V1–V4).

## 1. Fechamento é DECISÃO, e mora no nível META

* `resolution_nonempty`: toda proposição `P` tem `Nonempty (Resolution P)` (terceiro excluído).
  Logo "existe uma resolução" não fecha nada.
* `clayA_or_clayC`: **a disjunção oficial de Navier–Stokes `(A) ∨ (C)` é um TEOREMA do kernel**
  (por reescala `v(t,x) = a·u(a t, x)`, viscosidade `a ν`). Portanto `NavierStokes := A ∨ B ∨ C ∨ D`
  não pode ser alvo de fechamento: o problema do Clay é decidir **qual** disjunto, i.e. provar
  `ClayA` ou provar `¬ ClayA` (que implica `ClayC`).
* `exactCertificate_iff`: por isso o certificado exato de `ATK.Exact` se reduz a
  `RH ∧ Beal ∧ P ≠ NP` — o campo de NS era vazio de conteúdo.
* `openMath_prop_iff`: a proposta `OpenMath := ¬ ClosedMath` como `Prop` **não** significa
  "ainda não sabemos": significa `¬RH ∨ ¬Beal ∨ P = NP` — é ela mesma uma conjectura, e seria
  FALSA se as conjecturas forem verdadeiras, hoje, sem ninguém ter provado nada.

Conclusão: `OPEN_MATH` é um estado de CONHECIMENTO, não uma proposição matemática. O critério
proposto (executado por `closure/closure_gate.py`) é:

  `OPEN_MATH = false` ⇔ para cada um dos 7 problemas existe, no ambiente do kernel, uma declaração
  nomeada cujo tipo é EXATAMENTE o alvo oficial ou sua negação, com axiomas ⊆
  {propext, Classical.choice, Quot.sound}.

BSD, Yang–Mills e Hodge não são enunciáveis na Mathlib v4.34.1 ⇒ hoje `OPEN_MATH = true`
**necessariamente**, independentemente de qualquer prova.

## 2. O que tornaria cada fechamento FALSO (falsificadores exatos)

* `rh_false_iff`, `rh_counterexample_in_open_strip`: RH é falsa ⇔ existe zero não trivial com
  `Re s ≠ 1/2`; e todo tal zero tem `0 < Re s < 1` (provado aqui a partir da equação funcional e
  de `ζ ≠ 0` em `Re ≥ 1`).
* `beal_false_iff`: Beal é falsa ⇔ existe `Aˣ + Bʸ = Cᶻ`, `x,y,z > 2`, `gcd(A,B,C) = 1`.
  Um contraexemplo é um certificado FINITO verificável pelo kernel (`beal_refuted_by_witness`).
  `fermat_catalan_boundary`: as soluções primitivas conhecidas têm um expoente 2 — não contam.
* `pnp_false_iff`: P ≠ NP é falsa ⇔ P = NP (todo NP tem máquina `TM2` polinomial).
* `clayA_false_iff`: (A) é falsa ⇔ existe ν > 0 e dado suave, de divergência nula e decaimento
  rápido sem solução suave de energia limitada — e então (C) vale (`clayA_or_clayC`).

## 3. Leis AGOT: provadas, e falsificadas quando se tira uma hipótese

* `extraction_law` (Lei III / extração): compacto + semicontínua inferior + `inf D = 0` ⇒ zero
  atingido. `Ioc_not_compact` / `extraction_fails_without_compactness` e `jumpDefect_not_lsc` /
  `extraction_fails_without_lsc`: sem compacidade ou sem semicontinuidade, a lei é FALSA.
* `transport_law` (transporte quantitativo com constante uniforme) e
  `transport_fails_nonuniform`: com `Cₙ = n + 1` a lei é FALSA.

Nenhuma conjectura é provada. Nenhum `axiom`, nenhum `sorry`.
-/

noncomputable section

namespace ATK.Closure

open MeasureTheory Set Filter
open scoped ContDiff Topology Pointwise
open ATK.Exact

/-! ## 1. Fechamento = decisão; vacuidade do nível `Prop` -/

/-- Uma decisão de `P`: uma prova ou uma refutação. -/
inductive Resolution (P : Prop) : Type
  | proved : P → Resolution P
  | refuted : ¬ P → Resolution P

/-- **Vacuidade.** Toda proposição tem uma `Resolution` (terceiro excluído). Logo
`Nonempty (Resolution P)` — ou qualquer `Prop` do tipo "o problema tem solução" — não é fechamento. -/
theorem resolution_nonempty (P : Prop) : Nonempty (Resolution P) := by
  by_cases h : P
  · exact ⟨.proved h⟩
  · exact ⟨.refuted h⟩

/-! ### Navier–Stokes: a disjunção oficial é um teorema (reescala tempo–amplitude) -/

/-- `∂ᵢ (c·f) = c·∂ᵢ f` (sem hipótese de diferenciabilidade). -/
theorem pd_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (i : Fin 3) (c : ℝ)
    (f : R3 → F) : pd i (fun y => c • f y) = fun x => c • pd i f x := by
  funext x
  show fderiv ℝ (c • f) x (e i) = c • fderiv ℝ f x (e i)
  rw [fderiv_const_smul_field]
  rfl

/-- `∂ᵢ (c·q) = c·∂ᵢ q` para `q` escalar. -/
theorem pd_mul (i : Fin 3) (c : ℝ) (q : R3 → ℝ) :
    pd i (fun y => c * q y) = fun x => c * pd i q x :=
  pd_smul i c q

theorem div3_smul (c : ℝ) (v : R3 → R3) (x : R3) :
    div3 (fun y => c • v y) x = c * div3 v x := by
  simp only [div3, PiLp.smul_apply, smul_eq_mul, pd_mul, Finset.mul_sum]

theorem lap3_smul (c : ℝ) (v : R3 → R3) (x : R3) :
    lap3 (fun y => c • v y) x = c • lap3 v x := by
  simp only [lap3, pd_smul, Finset.smul_sum]

theorem grad3_mul (c : ℝ) (q : R3 → ℝ) (x : R3) :
    grad3 (fun y => c * q y) x = c • grad3 q x := by
  simp only [grad3, pd_mul, Finset.smul_sum, smul_smul]

theorem conv3_smul (c : ℝ) (v : R3 → R3) (x : R3) :
    conv3 (fun y => c • v y) x = (c * c) • conv3 v x := by
  simp only [conv3, pd_smul, PiLp.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  first
    | module
    | (simp only [smul_eq_mul, smul_smul]; congr 1; ring)

/-- Derivada temporal da reescala: `∂ₜ [a·g(a t)] = a²·g'(a t)` (em `[0, ∞)`). -/
theorem derivWithin_rescale {a : ℝ} (ha : 0 < a) (g : ℝ → R3) (t : ℝ) :
    derivWithin (fun s => a • g (a * s)) (Ici 0) t = (a * a) • derivWithin g (Ici 0) (a * t) := by
  rw [derivWithin_fun_const_smul_field, derivWithin_comp_mul_left,
    LinearOrderedField.smul_Ici ha, mul_zero, smul_smul]

/-- **Reescala de Navier–Stokes** (sem força): se `(u, p)` resolve com viscosidade `ν` e dado `u0`,
então `v(t,x) = a·u(a t, x)`, `q(t,x) = a²·p(a t, x)` resolve com viscosidade `a ν` e dado `a·u0`. -/
theorem ns_rescale {ν ν' a : ℝ} (ha : 0 < a) (hν : ν' = a * ν) {u0 w0 : R3 → R3}
    (hw : ∀ x, w0 x = a • u0 x) {u : ℝ → R3 → R3} {p : ℝ → R3 → ℝ}
    (h : NSClassical ν u0 (fun _ _ => 0) u p) :
    NSClassical ν' w0 (fun _ _ => 0) (fun t x => a • u (a * t) x)
      (fun t x => a * a * p (a * t) x) := by
  subst hν
  have hmaps : MapsTo (fun z : ℝ × R3 => (a * z.1, z.2)) (Ici 0 ×ˢ univ) (Ici 0 ×ˢ univ) := by
    rintro ⟨t, x⟩ ⟨ht, -⟩
    exact Set.mk_mem_prod (mul_nonneg ha.le ht) (mem_univ x)
  have hL : ContDiffOn ℝ ∞ (fun z : ℝ × R3 => (a * z.1, z.2)) (Ici 0 ×ˢ univ) :=
    (((contDiff_const (c := a)).mul contDiff_fst).prodMk contDiff_snd).contDiffOn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (h.smooth_u.comp hL hmaps).const_smul a
  · exact (contDiffOn_const (c := a * a)).mul (h.smooth_p.comp hL hmaps)
  · intro t ht x
    have hm := h.momentum (a * t) (mul_nonneg ha.le ht) x
    simp only [add_zero] at hm ⊢
    rw [derivWithin_rescale ha (fun s => u s x) t, conv3_smul, lap3_smul, grad3_mul]
    rw [eq_sub_of_add_eq hm]
    module
  · intro t ht x
    show div3 (fun y => a • u (a * t) y) x = 0
    rw [div3_smul, h.incompressible _ (mul_nonneg ha.le ht), mul_zero]
  · intro x
    simp only [mul_zero, h.initial, hw]

/-- A reescala preserva energia limitada. -/
theorem energy_rescale {a : ℝ} (ha : 0 < a) {u : ℝ → R3 → R3} (h : BoundedEnergy u) :
    BoundedEnergy (fun t x => a • u (a * t) x) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨a ^ 2 * C, fun t ht => ?_⟩
  have h1 : ∀ x, ‖a • u (a * t) x‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) * ‖u (a * t) x‖ₑ ^ 2 := by
    intro x
    rw [enorm_smul, Real.enorm_eq_ofReal ha.le, mul_pow, ← ENNReal.ofReal_pow ha.le]
  simp only [h1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (sq_nonneg a)]
  gcongr
  exact hC (a * t) (mul_nonneg ha.le ht)

/-- O dado reescalado continua com decaimento rápido. -/
theorem rapidDecay_smul (c : ℝ) {u0 : R3 → R3} (hs : ContDiff ℝ ∞ u0) (h : RapidDecay u0) :
    RapidDecay (fun x => c • u0 x) := by
  intro k K
  obtain ⟨C, hC⟩ := h k K
  refine ⟨|c| * C, fun x => ?_⟩
  have hk : ContDiffAt ℝ k u0 x := (contDiff_infty.1 hs k).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' hk, norm_smul, Real.norm_eq_abs]
  calc (1 + ‖x‖) ^ K * (|c| * ‖iteratedFDeriv ℝ k u0 x‖)
      = |c| * ((1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ k u0 x‖) := by ring
    _ ≤ |c| * C := mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)

/-- A força nula é admissível em (C). -/
theorem smoothForce_zero : SmoothForce (fun _ _ => 0) := by
  show ContDiffOn ℝ ∞ (fun _ : ℝ × R3 => (0 : R3)) (Ici 0 ×ˢ univ)
  exact contDiffOn_const

theorem forceDecay_zero : ForceDecay (fun _ _ => 0) := by
  intro k K
  refine ⟨0, fun t _ x => ?_⟩
  simp

/-- **Falsificador exato de (A).** -/
theorem clayA_false_iff : ¬ ClayA ↔ ∃ ν : ℝ, 0 < ν ∧ ∃ u0 : R3 → R3, ContDiff ℝ ∞ u0 ∧
    (∀ x, div3 u0 x = 0) ∧ RapidDecay u0 ∧
    ¬ ∃ u p, NSClassical ν u0 (fun _ _ => 0) u p ∧ BoundedEnergy u := by
  constructor
  · intro hA
    by_contra hc
    apply hA
    intro ν hν u0 h1 h2 h3
    by_contra hn
    exact hc ⟨ν, hν, u0, h1, h2, h3, hn⟩
  · rintro ⟨ν, hν, u0, h1, h2, h3, hn⟩ hA
    exact hn (hA ν hν u0 h1 h2 h3)

/-- **(A) ∨ (C) é um teorema.** Se (A) falha para algum `ν₀` e dado `u₀`, então para todo `ν > 0`
o dado `(ν/ν₀)·u₀` com força nula não tem solução suave de energia limitada (senão, reescalando
por `a = ν₀/ν`, `u₀` teria). Isso NÃO resolve Navier–Stokes: mostra que a disjunção não é alvo. -/
theorem clayA_or_clayC : ClayA ∨ ClayC := by
  by_cases hA : ClayA
  · exact Or.inl hA
  · right
    obtain ⟨ν0, hν0, u0, hs, hdiv, hdec, hno⟩ := clayA_false_iff.mp hA
    intro ν hν
    refine ⟨fun x => (ν / ν0) • u0 x, fun _ _ => 0, hs.const_smul _, fun x => ?_,
      rapidDecay_smul _ hs hdec, smoothForce_zero, forceDecay_zero, ?_⟩
    · rw [div3_smul, hdiv, mul_zero]
    · rintro ⟨u, p, hns, hbe⟩
      apply hno
      have ha : 0 < ν0 / ν := div_pos hν0 hν
      have h1 := ns_rescale (ν' := ν0) (w0 := u0) ha (div_mul_cancel₀ ν0 hν.ne').symm
        (fun x => by
          show u0 x = (ν0 / ν) • ((ν / ν0) • u0 x)
          rw [smul_smul, div_mul_div_comm, mul_comm ν0 ν,
            div_self (mul_ne_zero hν.ne' hν0.ne'), one_smul]) hns
      exact ⟨_, _, h1, energy_rescale ha hbe⟩

/-- Consequência: o `Prop` `NavierStokes := A ∨ B ∨ C ∨ D` é demonstrável — e por isso inútil como
alvo de fechamento. O alvo correto é uma declaração de tipo `ClayA`, `ClayB`, `ClayC`, `ClayD`
ou `¬ ClayA`. -/
theorem navierStokes_disjunction : NavierStokes := by
  rcases clayA_or_clayC with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))

/-- O certificado exato de `ATK.Exact` reduz-se a RH ∧ Beal ∧ P ≠ NP (o campo NS é vazio). -/
theorem exactCertificate_iff : ExactCertificate ↔ RH ∧ Beal ∧ P_ne_NP :=
  ⟨fun c => ⟨c.rh, c.beal, c.pNeNP⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, navierStokes_disjunction, h2, h3⟩⟩

/-- **`OpenMath := ¬ ClosedMath` não é "em aberto".** Como `Prop`, afirma que alguma conjectura é
FALSA. Se RH, Beal e P ≠ NP forem verdadeiras, essa `OpenMath` é falsa hoje. -/
theorem openMath_prop_iff : ¬ ExactCertificate ↔ ¬ RH ∨ ¬ Beal ∨ P_eq_NP := by
  rw [exactCertificate_iff, P_ne_NP_iff]
  tauto

/-! ## 2. Falsificadores exatos -/

/-- RH é falsa ⇔ existe zero não trivial fora da reta crítica. -/
theorem rh_false_iff : ¬ RH ↔ ∃ s : ℂ, riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧
    s ≠ 1 ∧ s.re ≠ 1 / 2 := by
  rw [RH_iff]
  constructor
  · intro h
    by_contra hc
    apply h
    intro s hs ht h1
    by_contra hre
    exact hc ⟨s, hs, ht, h1, hre⟩
  · rintro ⟨s, hs, ht, h1, hre⟩ h
    exact hre (h s hs ht h1)

/-- Todo zero não trivial tem `Re s < 1` (não anulação em `Re s ≥ 1`, Mathlib). -/
theorem rh_counterexample_re_lt_one {s : ℂ} (hs : riemannZeta s = 0) : s.re < 1 := by
  by_contra h
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hs

/-- Todo zero não trivial tem `Re s > 0` (equação funcional + `Γ ≠ 0` + `ζ ≠ 0` em `Re ≥ 1`). -/
theorem rh_counterexample_re_pos {s : ℂ} (hs : riemannZeta s = 0)
    (ht : ¬∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re := by
  by_contra hre
  push_neg at hre
  have hwre : 1 ≤ (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hs
    norm_num at hs
  have hwn : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
    intro n hn
    have hre' := congrArg Complex.re hn
    rw [Complex.neg_re, Complex.natCast_re] at hre'
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hw1 : (1 - s) ≠ 1 := by
    intro h
    apply hs0
    linear_combination -h
  have hfe := riemannZeta_one_sub hwn hw1
  rw [sub_sub_cancel, hs] at hfe
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hcpow : (2 * (Real.pi : ℂ)) ^ (-(1 - s)) ≠ 0 := fun h0 =>
    mul_ne_zero two_ne_zero hπ ((Complex.cpow_eq_zero_iff _ _).mp h0).1
  have hG : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
  have hZ : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
  have hC : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) ≠ 0 := by
    rw [Complex.cos_ne_zero_iff]
    intro k hk
    have h2 : (Real.pi : ℂ) * (1 - s) = (Real.pi : ℂ) * (2 * k + 1) := by
      linear_combination 2 * hk
    have h3 := mul_left_cancel₀ hπ h2
    have hsk : s = -2 * (k : ℂ) := by linear_combination -h3
    have hkre : (0 : ℝ) ≤ k := by
      have h4 := congrArg Complex.re hsk
      simp at h4
      linarith
    have hk0 : 0 ≤ k := by exact_mod_cast hkre
    lift k to ℕ using hk0
    cases k with
    | zero =>
      apply hs0
      rw [hsk]
      simp
    | succ n =>
      apply ht
      exact ⟨n, by rw [hsk]; push_cast; ring⟩
  have hprod : (2 : ℂ) * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
      Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) * riemannZeta (1 - s) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hcpow) hG) hC) hZ
  exact hprod hfe.symm

/-- **Onde mora um contraexemplo de RH:** na faixa crítica aberta `0 < Re s < 1`, fora de `Re = 1/2`. -/
theorem rh_counterexample_in_open_strip {s : ℂ} (hs : riemannZeta s = 0)
    (ht : ¬∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re ∧ s.re < 1 :=
  ⟨rh_counterexample_re_pos hs ht, rh_counterexample_re_lt_one hs⟩

/-- Beal é falsa ⇔ existe solução primitiva com expoentes > 2. -/
theorem beal_false_iff : ¬ Beal ↔ ∃ A B C x y z : ℕ, 0 < A ∧ 0 < B ∧ 0 < C ∧ 2 < x ∧ 2 < y ∧
    2 < z ∧ A ^ x + B ^ y = C ^ z ∧ Nat.gcd A (Nat.gcd B C) = 1 := by
  constructor
  · intro h
    by_contra hc
    apply h
    intro A B C x y z hA hB hC hx hy hz heq
    by_contra hg
    have hpos : 0 < Nat.gcd A (Nat.gcd B C) := Nat.gcd_pos_of_pos_left _ hA
    exact hc ⟨A, B, C, x, y, z, hA, hB, hC, hx, hy, hz, heq, by omega⟩
  · rintro ⟨A, B, C, x, y, z, hA, hB, hC, hx, hy, hz, heq, hg⟩ h
    have h1 := h A B C x y z hA hB hC hx hy hz heq
    omega

/-- Um contraexemplo de Beal é um certificado finito: basta exibi-lo. -/
theorem beal_refuted_by_witness (A B C x y z : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hx : 2 < x) (hy : 2 < y) (hz : 2 < z) (heq : A ^ x + B ^ y = C ^ z)
    (hg : Nat.gcd A (Nat.gcd B C) = 1) : ¬ Beal :=
  beal_false_iff.mpr ⟨A, B, C, x, y, z, hA, hB, hC, hx, hy, hz, heq, hg⟩

/-- Fronteira: soluções primitivas de Fermat–Catalan conhecidas têm SEMPRE um expoente 2, logo
não são contraexemplos (2 < 2 é falso). -/
theorem fermat_catalan_boundary :
    (2 ^ 5 + 7 ^ 2 = 3 ^ 4 ∧ Nat.gcd 2 (Nat.gcd 7 3) = 1) ∧
    (13 ^ 2 + 7 ^ 3 = 2 ^ 9 ∧ Nat.gcd 13 (Nat.gcd 7 2) = 1) ∧
    (2 ^ 7 + 17 ^ 3 = 71 ^ 2 ∧ Nat.gcd 2 (Nat.gcd 17 71) = 1) ∧
    (3 ^ 5 + 11 ^ 4 = 122 ^ 2 ∧ Nat.gcd 3 (Nat.gcd 11 122) = 1) ∧ ¬ (2 < 2) := by
  norm_num

/-- P ≠ NP é falsa ⇔ P = NP. -/
theorem pnp_false_iff : ¬ P_ne_NP ↔ P_eq_NP := by
  rw [P_ne_NP_iff, not_not]

/-! ## 3. Leis AGOT: provadas, e falsificadas sem suas hipóteses -/

/-- **Lei de extração (AGOT, Lei III).** Compacto não vazio, defeito semicontínuo inferior e não
negativo, com ínfimo 0 ⇒ existe ponto de defeito exatamente 0. -/
theorem extraction_law {X : Type*} [TopologicalSpace X] {K : Set X} {D : X → ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (hD : LowerSemicontinuousOn D K)
    (hnn : ∀ x ∈ K, 0 ≤ D x) (happrox : ∀ ε > 0, ∃ x ∈ K, D x < ε) :
    ∃ x ∈ K, D x = 0 := by
  obtain ⟨x, hx, hmin⟩ := hD.exists_isMinOn hne hK
  refine ⟨x, hx, le_antisymm ?_ (hnn x hx)⟩
  by_contra hpos
  push_neg at hpos
  obtain ⟨y, hy, hlt⟩ := happrox (D x) hpos
  exact absurd (isMinOn_iff.mp hmin y hy) (not_le.mpr hlt)

/-- Sem compacidade a lei é FALSA: em `(0,1]`, `D x = x` tem ínfimo 0 e nunca vale 0. -/
theorem extraction_fails_without_compactness :
    (∀ x ∈ Ioc (0 : ℝ) 1, 0 ≤ x) ∧ ContinuousOn (fun x : ℝ => x) (Ioc 0 1) ∧
    (∀ ε > 0, ∃ x ∈ Ioc (0 : ℝ) 1, x < ε) ∧ ¬ ∃ x ∈ Ioc (0 : ℝ) 1, x = 0 := by
  refine ⟨fun x hx => hx.1.le, continuousOn_id, fun ε hε => ?_, ?_⟩
  · have hpos : 0 < min (ε / 2) 1 := lt_min (by linarith) one_pos
    refine ⟨min (ε / 2) 1, ⟨hpos, min_le_right _ _⟩, ?_⟩
    calc min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
      _ < ε := by linarith
  · rintro ⟨x, hx, rfl⟩
    exact lt_irrefl _ hx.1

/-- Consequência da lei: `(0,1]` não é compacto (a lei identifica a hipótese que falha). -/
theorem Ioc_not_compact : ¬ IsCompact (Ioc (0 : ℝ) 1) := by
  intro hK
  obtain ⟨hnn, hc, happ, hno⟩ := extraction_fails_without_compactness
  exact hno (extraction_law hK ⟨1, by norm_num, le_rfl⟩ hc.lowerSemicontinuousOn hnn happ)

/-- Defeito com salto: `1` em `0`, `x` fora de `0`. -/
def jumpDefect (x : ℝ) : ℝ := if x = 0 then 1 else x

/-- Sem semicontinuidade a lei é FALSA: em `[0,1]` (compacto), `jumpDefect` tem ínfimo 0 e
nunca vale 0. -/
theorem extraction_fails_without_lsc :
    IsCompact (Icc (0 : ℝ) 1) ∧ (∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ jumpDefect x) ∧
    (∀ ε > 0, ∃ x ∈ Icc (0 : ℝ) 1, jumpDefect x < ε) ∧ ¬ ∃ x ∈ Icc (0 : ℝ) 1, jumpDefect x = 0 := by
  refine ⟨isCompact_Icc, fun x hx => ?_, fun ε hε => ?_, ?_⟩
  · unfold jumpDefect
    split_ifs <;> linarith [hx.1]
  · have hpos : 0 < min (ε / 2) 1 := lt_min (by linarith) one_pos
    refine ⟨min (ε / 2) 1, ⟨hpos.le, min_le_right _ _⟩, ?_⟩
    unfold jumpDefect
    rw [if_neg hpos.ne']
    calc min (ε / 2) 1 ≤ ε / 2 := min_le_left _ _
      _ < ε := by linarith
  · rintro ⟨x, hx, hD⟩
    unfold jumpDefect at hD
    split_ifs at hD with h0
    · norm_num at hD
    · exact h0 hD

/-- Consequência da lei: `jumpDefect` não é semicontínua inferior em `[0,1]`. -/
theorem jumpDefect_not_lsc : ¬ LowerSemicontinuousOn jumpDefect (Icc 0 1) := by
  intro hl
  obtain ⟨hK, hnn, happ, hno⟩ := extraction_fails_without_lsc
  exact hno (extraction_law hK ⟨0, le_rfl, zero_le_one⟩ hl hnn happ)

/-- **Lei de transporte quantitativo (AGOT V2).** `D_Y(T x) ≤ C·D_X(x)` com `C` uniforme e
`D_Y ≥ 0`: `D_X(xₙ) → 0 ⇒ D_Y(T xₙ) → 0`. -/
theorem transport_law {ι X Y : Type*} {l : Filter ι} {T : X → Y} {DX : X → ℝ} {DY : Y → ℝ}
    {C : ℝ} (hT : ∀ x, DY (T x) ≤ C * DX x) (hY : ∀ y, 0 ≤ DY y) {xs : ι → X}
    (hx : Tendsto (fun n => DX (xs n)) l (𝓝 0)) :
    Tendsto (fun n => DY (T (xs n))) l (𝓝 0) := by
  have hC : Tendsto (fun n => C * DX (xs n)) l (𝓝 0) := by
    simpa using hx.const_mul C
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hC
    (fun n => hY _) (fun n => hT _)

/-- Com constante NÃO uniforme (`Cₙ = n + 1`) a lei é FALSA: `D_X = 1/(n+1) → 0`, mas
`D_Y = Cₙ·D_X = 1` não tende a 0. -/
theorem transport_fails_nonuniform :
    Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) ∧
    (∀ n : ℕ, ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) = 1) ∧
    ¬ Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
  refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, fun n => ?_, ?_⟩
  · exact mul_one_div_cancel (by positivity)
  · intro h
    have h01 := tendsto_nhds_unique h tendsto_const_nhds
    norm_num at h01

end ATK.Closure

end

#print axioms ATK.Closure.resolution_nonempty
#print axioms ATK.Closure.pd_smul
#print axioms ATK.Closure.pd_mul
#print axioms ATK.Closure.div3_smul
#print axioms ATK.Closure.lap3_smul
#print axioms ATK.Closure.grad3_mul
#print axioms ATK.Closure.conv3_smul
#print axioms ATK.Closure.derivWithin_rescale
#print axioms ATK.Closure.ns_rescale
#print axioms ATK.Closure.energy_rescale
#print axioms ATK.Closure.rapidDecay_smul
#print axioms ATK.Closure.smoothForce_zero
#print axioms ATK.Closure.forceDecay_zero
#print axioms ATK.Closure.clayA_false_iff
#print axioms ATK.Closure.clayA_or_clayC
#print axioms ATK.Closure.navierStokes_disjunction
#print axioms ATK.Closure.exactCertificate_iff
#print axioms ATK.Closure.openMath_prop_iff
#print axioms ATK.Closure.rh_false_iff
#print axioms ATK.Closure.rh_counterexample_re_lt_one
#print axioms ATK.Closure.rh_counterexample_re_pos
#print axioms ATK.Closure.rh_counterexample_in_open_strip
#print axioms ATK.Closure.beal_false_iff
#print axioms ATK.Closure.beal_refuted_by_witness
#print axioms ATK.Closure.fermat_catalan_boundary
#print axioms ATK.Closure.pnp_false_iff
#print axioms ATK.Closure.extraction_law
#print axioms ATK.Closure.extraction_fails_without_compactness
#print axioms ATK.Closure.Ioc_not_compact
#print axioms ATK.Closure.extraction_fails_without_lsc
#print axioms ATK.Closure.jumpDefect_not_lsc
#print axioms ATK.Closure.transport_law
#print axioms ATK.Closure.transport_fails_nonuniform
