import ATK.BSDInvariantes

/-!
# ATK — BSD: o coeficiente líder `L^{(r)}(E,1)/r!` é não nulo

Para `f` analítica em `a` com ordem finita `r`:

* **ordem por derivadas** (`derivadas_ordem`, `ordem_iff_derivadas`): `ord_a f = r` ⟺ `f^{(k)}(a) = 0`
  para `k < r` e `f^{(r)}(a) ≠ 0`;
* para uma `L`-função continuada (inteira) que não é identicamente nula, a ordem em `s = 1` é finita
  (`ordem_finita`, princípio da identidade) e o **coeficiente líder `L^{(r)}(E,1)/r!` é ≠ 0**
  (`coefLider_ne_zero`), e as derivadas de ordem `< r` se anulam (`derivadas_abaixo`).

É o que dá sentido ao lado esquerdo da fórmula refinada de BSD. Nada aqui prova BSD (O7, `OPEN_MATH`).
-/

open Filter Topology

namespace ATK.BSDCoefLider

open ATK.BSDInvariantes

/-- **Ordem por derivadas.** -/
theorem derivadas_ordem {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) {r : ℕ}
    (hr : analyticOrderAt f a = r) :
    (∀ k < r, iteratedDeriv k f a = 0) ∧ iteratedDeriv r f a ≠ 0 := by
  constructor
  · have := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf (n := r)).mp (by rw [hr])
    exact this
  · intro h0
    have hle : ((r + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f a := by
      refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf (n := r + 1)).mpr ?_
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf (n := r)).mp (by rw [hr]) k h
      · rw [h]; exact h0
    rw [hr] at hle
    exact absurd (ENat.natCast_le_natCast.mp hle) (by omega)

/-- Recíproca: o padrão de derivadas determina a ordem. -/
theorem ordem_iff_derivadas {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (r : ℕ) :
    analyticOrderAt f a = r ↔ (∀ k < r, iteratedDeriv k f a = 0) ∧ iteratedDeriv r f a ≠ 0 := by
  refine ⟨derivadas_ordem hf, fun ⟨h1, h2⟩ => ?_⟩
  have hge : (r : ℕ∞) ≤ analyticOrderAt f a :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf (n := r)).mpr h1
  have hlt : ¬ ((r + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f a := by
    intro h
    exact h2 ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf (n := r + 1)).mp h r (by omega))
  by_cases ht : analyticOrderAt f a = ⊤
  · exact absurd (by rw [ht]; exact le_top) hlt
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp ht
    rw [← hm] at hge hlt ⊢
    have h1' : r ≤ m := ENat.natCast_le_natCast.mp hge
    have h2' : ¬ r + 1 ≤ m := fun h => hlt (ENat.natCast_le_natCast.mpr h)
    congr 1
    omega

variable {E : WeierstrassCurve ℚ}

/-- Uma `L`-função continuada não identicamente nula tem ordem finita em `s = 1`. -/
theorem ordem_finita (Lc : ATK.L4Base.LFunctionContinued E) (h : ∃ s, Lc.L s ≠ 0) :
    analyticOrderAt Lc.L 1 ≠ ⊤ := by
  intro htop
  obtain ⟨s, hs⟩ := h
  have hev : Lc.L =ᶠ[𝓝 1] 0 := analyticOrderAt_eq_top.mp htop
  have han : AnalyticOnNhd ℂ Lc.L Set.univ := fun z _ => Lc.entire.analyticAt z
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 1) hev
  exact hs (this (Set.mem_univ s))

theorem ordem_spec (Lc : ATK.L4Base.LFunctionContinued E) (h : analyticOrderAt Lc.L 1 ≠ ⊤) :
    analyticOrderAt Lc.L 1 = (ordem Lc : ℕ∞) := by
  unfold ordem
  exact (ENat.natCast_toNat h).symm

/-- As derivadas de ordem `< r` se anulam em `s = 1`. -/
theorem derivadas_abaixo (Lc : ATK.L4Base.LFunctionContinued E) (h : analyticOrderAt Lc.L 1 ≠ ⊤) :
    ∀ k < ordem Lc, iteratedDeriv k Lc.L 1 = 0 :=
  (derivadas_ordem (Lc.entire.analyticAt 1) (ordem_spec Lc h)).1

/-- **O coeficiente líder `L^{(r)}(E,1)/r!` é não nulo.** -/
theorem coefLider_ne_zero (Lc : ATK.L4Base.LFunctionContinued E) (h : analyticOrderAt Lc.L 1 ≠ ⊤) :
    coefLider Lc ≠ 0 := by
  unfold coefLider
  refine div_ne_zero (derivadas_ordem (Lc.entire.analyticAt 1) (ordem_spec Lc h)).2 ?_
  exact_mod_cast (Nat.factorial_pos _).ne'

theorem coefLider_ne_zero' (Lc : ATK.L4Base.LFunctionContinued E) (h : ∃ s, Lc.L s ≠ 0) :
    coefLider Lc ≠ 0 :=
  coefLider_ne_zero Lc (ordem_finita Lc h)

end ATK.BSDCoefLider

-- Auditoria de axiomas (kernel)
#print axioms ATK.BSDCoefLider.derivadas_ordem
#print axioms ATK.BSDCoefLider.ordem_iff_derivadas
#print axioms ATK.BSDCoefLider.ordem_finita
#print axioms ATK.BSDCoefLider.ordem_spec
#print axioms ATK.BSDCoefLider.derivadas_abaixo
#print axioms ATK.BSDCoefLider.coefLider_ne_zero
#print axioms ATK.BSDCoefLider.coefLider_ne_zero'
