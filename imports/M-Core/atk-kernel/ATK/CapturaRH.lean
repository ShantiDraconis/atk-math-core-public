import ATK.ContracaoDN

/-!
# Captura relativa acumulada na família genuína de Báez-Duarte

Para a sequência concreta `D_N = inf_c ‖χ − Σ_{k≤N} c_k ρ_k‖²` (`ATK.Conditional.Riemann.DN`):

* `q N = D_N − D_{N+1}` (decremento) e `η N = q N / D_N` (captura relativa);
* `passo`: `D_{N+1} = (1 − η N) · D_N`, **sem hipóteses** (se `D_N = 0`, os dois lados são 0);
* `produto`: `D_N = D_0 · ∏_{j<N} (1 − η j)`, sem hipóteses;
* `captura_suficiente`: se `Σ_{j<N} η j ≥ log log (N+2) − C` para todo `N`, vale a obrigação O1
  (`UniformLogBound`, com `K = D_0 · e^C`);
* `captura_log_iff`: com `D_N > 0` para todo `N`, **O1 é equivalente** a
  `Σ_{j<N} −log(1 − η j) ≥ log log (N+2) − C` — a "captura angular acumulada" na forma
  logarítmica *é* a obrigação O1, não uma redução dela;
* `positiva_de_piso` e `captura_teto`: o piso de Báez-Duarte–Balazard–Landreau–Saias (`PisoLog`)
  dá `D_N > 0` e impede a captura acumulada de crescer mais rápido que `log log N`.

Consequência: a próxima obrigação proposta para a rota de Riemann ("um limite inferior acumulado
para os decrementos relativos") é, na forma exata, a própria O1; e O1 implica RH (Báez-Duarte).
Nada aqui assume RH e nada aqui prova O1.
-/

open Filter Topology Finset

namespace ATK.CapturaRH

open ATK.Conditional.Riemann ATK.RiemannConcrete ATK.ContracaoDN

/-- Decremento `q_N = D_N − D_{N+1}`. -/
noncomputable def q (N : ℕ) : ℝ := DN N - DN (N + 1)

/-- Captura relativa `η_N = q_N / D_N` (convenção de Lean: `x / 0 = 0`). -/
noncomputable def η (N : ℕ) : ℝ := q N / DN N

theorem q_nonneg (N : ℕ) : 0 ≤ q N := sub_nonneg.mpr (DN_antitone (Nat.le_succ N))

theorem q_le (N : ℕ) : q N ≤ DN N := by
  unfold q; linarith [DN_nonneg (N + 1)]

theorem η_nonneg (N : ℕ) : 0 ≤ η N := div_nonneg (q_nonneg N) (DN_nonneg N)

theorem η_le_one (N : ℕ) : η N ≤ 1 := by
  unfold η
  rcases (DN_nonneg N).lt_or_eq with h | h
  · exact (div_le_one h).mpr (q_le N)
  · rw [← h, div_zero]; exact zero_le_one

/-- **Passo exato**, sem hipóteses: `D_{N+1} = (1 − η_N) · D_N`. -/
theorem passo (N : ℕ) : DN (N + 1) = (1 - η N) * DN N := by
  rcases (DN_nonneg N).lt_or_eq with h | h
  · unfold η q
    field_simp
    ring
  · have h1 : DN (N + 1) = 0 :=
      le_antisymm (h ▸ DN_antitone (Nat.le_succ N)) (DN_nonneg (N + 1))
    rw [h1, ← h, mul_zero]

/-- **Produto exato**, sem hipóteses: `D_N = D_0 · ∏_{j<N} (1 − η_j)`. -/
theorem produto (N : ℕ) : DN N = DN 0 * ∏ j ∈ range N, (1 - η j) := by
  induction N with
  | zero => simp
  | succ n ih => rw [passo, ih, prod_range_succ]; ring

/-- Telescópio: `D_N = D_0 − Σ_{j<N} q_j`. -/
theorem telescopio (N : ℕ) : DN N = DN 0 - ∑ j ∈ range N, q j := by
  induction N with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ← sub_sub, ← ih]; unfold q; ring

/-- `D_N ≤ D_0 · exp(−Σ_{j<N} η_j)`. -/
theorem le_exp (N : ℕ) : DN N ≤ DN 0 * Real.exp (-∑ j ∈ range N, η j) := by
  rw [produto N, ← sum_neg_distrib, Real.exp_sum]
  refine mul_le_mul_of_nonneg_left ?_ (DN_nonneg 0)
  refine prod_le_prod₀ (fun j _ => sub_nonneg.mpr (η_le_one j)) (fun j _ => ?_)
  linarith [Real.add_one_le_exp (-η j)]

theorem log_pos_N (N : ℕ) : 0 < Real.log ((N : ℝ) + 2) :=
  Real.log_pos (by have := N.cast_nonneg (α := ℝ); linarith)

/-- **Suficiência**: captura acumulada `Σ_{j<N} η_j ≥ log log (N+2) − C` ⇒ O1. -/
theorem captura_suficiente {C : ℝ}
    (h : ∀ N : ℕ, Real.log (Real.log ((N : ℝ) + 2)) - C ≤ ∑ j ∈ range N, η j) :
    UniformLogBound := by
  refine ⟨DN 0 * Real.exp C, fun N => ?_⟩
  have hl := log_pos_N N
  calc DN N ≤ DN 0 * Real.exp (-∑ j ∈ range N, η j) := le_exp N
    _ ≤ DN 0 * Real.exp (C - Real.log (Real.log ((N : ℝ) + 2))) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (DN_nonneg 0)
        linarith [h N]
    _ = DN 0 * Real.exp C / Real.log ((N : ℝ) + 2) := by
        rw [Real.exp_sub, Real.exp_log hl]; ring

/-- Com `D_N > 0`, a captura logarítmica acumulada é `log (D_0 / D_N)`. -/
theorem soma_log (hpos : ∀ N, 0 < DN N) (N : ℕ) :
    ∑ j ∈ range N, -Real.log (1 - η j) = Real.log (DN 0 / DN N) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hn := hpos n
    have hn1 := hpos (n + 1)
    have hfac : 1 - η n = DN (n + 1) / DN n := by
      rw [passo n, mul_div_assoc, div_self hn.ne', mul_one]
    rw [sum_range_succ, ih, hfac, Real.log_div hn1.ne' hn.ne',
      Real.log_div (hpos 0).ne' hn.ne', Real.log_div (hpos 0).ne' hn1.ne']
    ring

/-- **Equivalência exata**: com `D_N > 0`, O1 ⟺ captura logarítmica acumulada
`Σ_{j<N} −log(1 − η_j) ≥ log log (N+2) − C`. A forma "angular" é a própria O1. -/
theorem captura_log_iff (hpos : ∀ N, 0 < DN N) :
    UniformLogBound ↔ ∃ C : ℝ, ∀ N : ℕ,
      Real.log (Real.log ((N : ℝ) + 2)) - C ≤ ∑ j ∈ range N, -Real.log (1 - η j) := by
  have h0 := hpos 0
  constructor
  · rintro ⟨K, hK⟩
    have hK0 : 0 < K := by
      have := hK 0
      have hl := log_pos_N 0
      by_contra hk
      have : K / Real.log ((0 : ℕ) + 2 : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (not_lt.mp hk) hl.le
      linarith [hpos 0]
    refine ⟨Real.log K - Real.log (DN 0), fun N => ?_⟩
    rw [soma_log hpos N]
    have hl := log_pos_N N
    have hN := hpos N
    have hb : DN N * Real.log ((N : ℝ) + 2) ≤ K := by
      have := hK N
      rwa [le_div_iff₀ hl] at this
    have hll : Real.log (Real.log ((N : ℝ) + 2)) + Real.log (DN N) ≤ Real.log K := by
      rw [← Real.log_mul hl.ne' hN.ne']
      exact Real.log_le_log (mul_pos hl hN) (by linarith)
    rw [Real.log_div h0.ne' hN.ne']
    linarith
  · rintro ⟨C, hC⟩
    refine ⟨DN 0 * Real.exp C, fun N => ?_⟩
    have hl := log_pos_N N
    have hN := hpos N
    have h1 := hC N
    rw [soma_log hpos N, Real.log_div h0.ne' hN.ne'] at h1
    have h2 : Real.log (Real.log ((N : ℝ) + 2) * DN N) ≤ Real.log (DN 0 * Real.exp C) := by
      rw [Real.log_mul hl.ne' hN.ne', Real.log_mul h0.ne' (Real.exp_pos C).ne', Real.log_exp]
      linarith
    have h3 := (Real.log_le_log_iff (mul_pos hl hN) (mul_pos h0 (Real.exp_pos C))).mp h2
    rw [le_div_iff₀ hl]
    linarith

/-- **Cadeia certificada até RH**: a cota de captura acumulada implica a Hipótese de Riemann,
com todas as pontes já provadas no kernel (O1 ⇒ `D_N → 0` ⇒ RH pelo critério de Báez-Duarte,
`ATK.BaezDuarteBridge.baezDuarteCriterion`). Esta desigualdade sobre a família genuína é, portanto,
um produtor suficiente de RH — tão difícil quanto RH, ou mais. -/
theorem riemann_de_captura {C : ℝ}
    (h : ∀ N : ℕ, Real.log (Real.log ((N : ℝ) + 2)) - C ≤ ∑ j ∈ range N, η j) :
    RiemannHypothesis :=
  ATK.BaezDuarteBridge.baezDuarteCriterion (DN_tendsto_zero (captura_suficiente h))

/-- O piso logarítmico (Báez-Duarte–Balazard–Landreau–Saias) dá `D_N > 0` para todo `N`. -/
theorem positiva_de_piso (hP : PisoLog) (N : ℕ) : 0 < DN N := by
  obtain ⟨c, hc, N₁, hN₁⟩ := hP
  have hM := hN₁ (max N N₁) (le_max_right _ _)
  have hpos : 0 < DN (max N N₁) :=
    lt_of_lt_of_le (div_pos hc (log_pos_N _)) hM
  exact lt_of_lt_of_le hpos (DN_antitone (le_max_left _ _))

/-- **Teto da captura**: sob o piso logarítmico, a captura logarítmica acumulada cresce no
máximo como `log log N` — nenhuma rota pode capturar mais rápido (contração geométrica, etc.). -/
theorem captura_teto (hP : PisoLog) : ∃ C : ℝ, ∃ N₁ : ℕ, ∀ N ≥ N₁,
    ∑ j ∈ range N, -Real.log (1 - η j) ≤ Real.log (Real.log ((N : ℝ) + 2)) + C := by
  have hpos := positiva_de_piso hP
  obtain ⟨c, hc, N₁, hN₁⟩ := hP
  refine ⟨Real.log (DN 0) - Real.log c, N₁, fun N hN => ?_⟩
  rw [soma_log hpos N, Real.log_div (hpos 0).ne' (hpos N).ne']
  have hl := log_pos_N N
  have h1 : c / Real.log ((N : ℝ) + 2) ≤ DN N := hN₁ N hN
  have h2 : Real.log c - Real.log (Real.log ((N : ℝ) + 2)) ≤ Real.log (DN N) := by
    rw [← Real.log_div hc.ne' hl.ne']
    exact Real.log_le_log (div_pos hc hl) h1
  linarith

end ATK.CapturaRH

#print axioms ATK.CapturaRH.q_nonneg
#print axioms ATK.CapturaRH.q_le
#print axioms ATK.CapturaRH.η_nonneg
#print axioms ATK.CapturaRH.η_le_one
#print axioms ATK.CapturaRH.passo
#print axioms ATK.CapturaRH.produto
#print axioms ATK.CapturaRH.telescopio
#print axioms ATK.CapturaRH.le_exp
#print axioms ATK.CapturaRH.log_pos_N
#print axioms ATK.CapturaRH.captura_suficiente
#print axioms ATK.CapturaRH.soma_log
#print axioms ATK.CapturaRH.captura_log_iff
#print axioms ATK.CapturaRH.riemann_de_captura
#print axioms ATK.CapturaRH.positiva_de_piso
#print axioms ATK.CapturaRH.captura_teto
