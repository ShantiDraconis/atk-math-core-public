import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# ATK-Discovery — A melhoria ortogonal do defeito, exata, e por que ela não é automática

Num espaço com produto interno real `E`, para um subespaço `K` e um alvo `v`,
`D(K) = inf_{q ∈ K} ‖v − q‖²` (`defeito`).

* **melhoria por um vetor unitário** (`melhor_coef`, `melhor_coef_minimo`):
  `‖r − c e‖² = ‖r‖² − 2c⟨r,e⟩ + c²`, mínimo `‖r‖² − ⟨r,e⟩²` em `c = ⟨r,e⟩`;
* `D` é não negativo e decresce quando `K` cresce (`defeito_nonneg`, `defeito_mono`); se `v − p ⊥ K` com
  `p ∈ K`, então `D(K) = ‖v − p‖²` (`defeito_eq_of_orth`);
* **desigualdade de melhoria** (`melhoria_le`): `p ∈ K ⊆ K'`, `e ∈ K'` unitário ⟹
  `D(K') ≤ ‖v − p‖² − ⟨v − p, e⟩²`;
* **identidade exata** (`melhoria_exata`): se `p` é a projeção (`v − p ⊥ K`) e `e ⊥ K` é unitário, então
  `D(K ⊕ ℝe) = D(K) − ⟨r, e⟩²` com `r = v − p`: o ganho de cada passo é **exatamente** a correlação ao
  quadrado do resíduo com a nova direção;
* **contraexemplo à contração automática** (`contraexemplo_correlacao`): em `ℝ³`, `v = e₂`,
  `K = ℝe₀`, nova direção `e₁`: `D(K) = 1`, ganho `0`, `D(K ⊕ ℝe₁) = 1`; a desigualdade
  `⟨r, e⟩² ≥ D/3` (forma `D_n/(n+2)` com `n = 1`) **falha**. A correlação quantitativa tem de vir da
  família específica, não da geometria.

Nada aqui é sobre a família de Nyman–Beurling; é a geometria que qualquer prova por ganhos usa.
-/

namespace ATK.Discovery.Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `‖r − c e‖² = ‖r‖² − 2c⟨r,e⟩ + c²` para `‖e‖ = 1`. -/
theorem norm_sub_smul_sq (r e : E) (he : ‖e‖ = 1) (c : ℝ) :
    ‖r - c • e‖ ^ 2 = ‖r‖ ^ 2 - 2 * c * inner ℝ r e + c ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, norm_smul, he, Real.norm_eq_abs, mul_one, sq_abs]
  ring

/-- O melhor coeficiente `c = ⟨r,e⟩` dá `‖r‖² − ⟨r,e⟩²`. -/
theorem melhor_coef (r e : E) (he : ‖e‖ = 1) :
    ‖r - (inner ℝ r e) • e‖ ^ 2 = ‖r‖ ^ 2 - (inner ℝ r e) ^ 2 := by
  rw [norm_sub_smul_sq r e he]; ring

/-- Nenhum coeficiente faz melhor que `c = ⟨r,e⟩`. -/
theorem melhor_coef_minimo (r e : E) (he : ‖e‖ = 1) (c : ℝ) :
    ‖r‖ ^ 2 - (inner ℝ r e) ^ 2 ≤ ‖r - c • e‖ ^ 2 := by
  rw [norm_sub_smul_sq r e he]
  nlinarith [sq_nonneg (c - inner ℝ r e)]

/-- Defeito: quadrado da distância de `v` a `K`. -/
noncomputable def defeito (K : Submodule ℝ E) (v : E) : ℝ := ⨅ q : K, ‖v - (q : E)‖ ^ 2

theorem defeito_bdd (K : Submodule ℝ E) (v : E) :
    BddBelow (Set.range fun q : K => ‖v - (q : E)‖ ^ 2) :=
  ⟨0, by rintro _ ⟨q, rfl⟩; positivity⟩

theorem defeito_nonneg (K : Submodule ℝ E) (v : E) : 0 ≤ defeito K v :=
  le_ciInf fun _ => by positivity

theorem defeito_le {K : Submodule ℝ E} (v : E) {q : E} (hq : q ∈ K) :
    defeito K v ≤ ‖v - q‖ ^ 2 :=
  ciInf_le (defeito_bdd K v) ⟨q, hq⟩

/-- O defeito decresce quando o subespaço cresce. -/
theorem defeito_mono {K K' : Submodule ℝ E} (h : K ≤ K') (v : E) : defeito K' v ≤ defeito K v :=
  le_ciInf fun q => defeito_le v (h q.2)

/-- Se `p ∈ K` e `v − p ⊥ K`, o defeito é `‖v − p‖²` (o ínfimo é atingido em `p`). -/
theorem defeito_eq_of_orth {K : Submodule ℝ E} {v p : E} (hp : p ∈ K)
    (horth : ∀ q ∈ K, inner ℝ (v - p) q = 0) : defeito K v = ‖v - p‖ ^ 2 := by
  refine le_antisymm (defeito_le v hp) (le_ciInf fun q => ?_)
  have hpq : p - (q : E) ∈ K := K.sub_mem hp q.2
  have : v - (q : E) = (v - p) + (p - q) := by abel
  rw [this, norm_add_sq_real, horth _ hpq]
  nlinarith [sq_nonneg ‖p - (q : E)‖]

/-- **Desigualdade de melhoria**: `D(K') ≤ ‖v − p‖² − ⟨v − p, e⟩²` para `p ∈ K ⊆ K'`, `e ∈ K'` unitário. -/
theorem melhoria_le {K K' : Submodule ℝ E} (hK : K ≤ K') {v p e : E} (hp : p ∈ K)
    (he' : e ∈ K') (he : ‖e‖ = 1) :
    defeito K' v ≤ ‖v - p‖ ^ 2 - (inner ℝ (v - p) e) ^ 2 := by
  have hmem : p + (inner ℝ (v - p) e) • e ∈ K' := K'.add_mem (hK hp) (K'.smul_mem _ he')
  have h := defeito_le v hmem
  have : v - (p + (inner ℝ (v - p) e) • e) = (v - p) - (inner ℝ (v - p) e) • e := by abel
  rw [this, melhor_coef _ _ he] at h
  exact h

/-- **Identidade exata da melhoria**: com `p` a projeção sobre `K` e `e ⊥ K` unitário,
`D(K ⊔ ℝe) = D(K) − ⟨v − p, e⟩²`. -/
theorem melhoria_exata {K : Submodule ℝ E} {v p e : E} (hp : p ∈ K)
    (horth : ∀ q ∈ K, inner ℝ (v - p) q = 0) (he : ‖e‖ = 1)
    (heK : ∀ q ∈ K, inner ℝ e q = 0) :
    defeito (K ⊔ Submodule.span ℝ {e}) v = defeito K v - (inner ℝ (v - p) e) ^ 2 := by
  set a := inner ℝ (v - p) e with ha
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hp' : p + a • e ∈ K ⊔ Submodule.span ℝ {e} :=
    Submodule.add_mem _ (Submodule.mem_sup_left hp)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)))
  have horth' : ∀ q ∈ K ⊔ Submodule.span ℝ {e}, inner ℝ (v - (p + a • e)) q = 0 := by
    intro q hq
    obtain ⟨k, hk, y, hy, rfl⟩ := Submodule.mem_sup.mp hq
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have h1 : v - (p + a • e) = (v - p) - a • e := by abel
    rw [h1, inner_add_right, inner_smul_right]
    have hk' : inner ℝ ((v - p) - a • e) k = 0 := by
      rw [inner_sub_left, real_inner_smul_left, horth k hk, heK k hk]; ring
    have he' : inner ℝ ((v - p) - a • e) e = 0 := by
      rw [inner_sub_left, real_inner_smul_left, hee, ← ha]; ring
    rw [hk', he']; ring
  rw [defeito_eq_of_orth hp' horth', defeito_eq_of_orth hp horth]
  have : v - (p + a • e) = (v - p) - a • e := by abel
  rw [this, ha, melhor_coef _ _ he]

/-! ## Contraexemplo em `ℝ³` -/

/-- Em `ℝ³`, com `v = e₂`, `K = ℝe₀` e a nova direção `e₁`: `D(K) = 1`, a correlação é `0`,
`D(K ⊕ ℝe₁) = 1`, e a desigualdade `⟨r, e⟩² ≥ D(K)/3` falha. -/
theorem contraexemplo_correlacao :
    let v : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 2 1
    let e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 1 1
    let K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.span ℝ {EuclideanSpace.single 0 1}
    defeito K v = 1 ∧ inner ℝ (v - 0) e = 0 ∧
      defeito (K ⊔ Submodule.span ℝ {e}) v = 1 ∧ ¬ (defeito K v / 3 ≤ (inner ℝ (v - 0) e) ^ 2) := by
  intro v e K
  have hve : inner ℝ (v - 0) e = 0 := by
    simp [v, e, EuclideanSpace.inner_single_left]
  have horth : ∀ q ∈ K, inner ℝ (v - 0) q = 0 := by
    intro q hq
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hq
    simp [v, inner_smul_right, EuclideanSpace.inner_single_left]
  have heK : ∀ q ∈ K, inner ℝ e q = 0 := by
    intro q hq
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hq
    simp [e, inner_smul_right, EuclideanSpace.inner_single_left]
  have he : ‖e‖ = 1 := by simp [e]
  have hD : defeito K v = 1 := by
    rw [defeito_eq_of_orth K.zero_mem horth]
    simp [v]
  refine ⟨hD, hve, ?_, ?_⟩
  · rw [melhoria_exata K.zero_mem horth he heK, hD, hve]; norm_num
  · rw [hD, hve]; norm_num

end ATK.Discovery.Hilbert

#print axioms ATK.Discovery.Hilbert.norm_sub_smul_sq
#print axioms ATK.Discovery.Hilbert.melhor_coef
#print axioms ATK.Discovery.Hilbert.melhor_coef_minimo
#print axioms ATK.Discovery.Hilbert.defeito_nonneg
#print axioms ATK.Discovery.Hilbert.defeito_mono
#print axioms ATK.Discovery.Hilbert.defeito_eq_of_orth
#print axioms ATK.Discovery.Hilbert.melhoria_le
#print axioms ATK.Discovery.Hilbert.melhoria_exata
#print axioms ATK.Discovery.Hilbert.contraexemplo_correlacao
