import ATK.Discovery.Infinitesimal

/-!
# ATK-Discovery — Leis do dígito na posição infinita

Para cada posição hiperinteira `H = [n ↦ f n]` com `f n → ∞`, o valor `ε(f) = 10⁻ᴴ ∈ ℝ*`
(`eps f`; `eps id` é o `ε_H = 10⁻ᴴ` de `ATK.Discovery.Infinitesimal`):

| Lei | Enunciado | Teorema |
|---|---|---|
| positividade | `0 < ε(f)` | `eps_pos` |
| abaixo de toda posição finita | `ε(f) < 10⁻ⁿ` e `ε(f) < r` para todo real `r > 0` | `eps_lt_pot`, `eps_lt_real` |
| parte padrão | `st ε(f) = 0`, `st(1 ± ε(f)) = 1` | `stdPart_eps`, `stdPart_um_mais`, `stdPart_um_menos` |
| posição | `f < g ⟹ ε(g) < ε(f)` (dígito mais distante, diferença menor) | `eps_lt_of_lt` |
| produto de posições | `ε(f)·ε(g) = ε(f + g)`; `10⁻²ᴴ = (10⁻ᴴ)² < 10⁻ᴴ` | `eps_mul`, `dois_H` |
| soma | `(1 + ε(f)) + (1 + ε(g)) > 2` com parte padrão `2` | `lei_soma` |
| produto | `(1 + ε(f))(1 + ε(g)) = 1 + ε(f) + ε(g) + ε(f + g) > 1` com parte padrão `1` | `lei_produto` |
| mesma parte padrão, ordem estrita | `0 < ε(g) < ε(f)` com `st = 0` para os três | `mesma_classe_ordem_estrita` |

Toda lei vem de uma sequência real convergente: `st(ofSeq u) = lim u` (`stdPart_ofSeq`).
-/

namespace ATK.Discovery.Leis

open Filter Topology ArchimedeanClass Hyperreal

/-- Um limite em `atTop` dá o limite do germe ao longo do hiperfiltro. -/
theorem germe_tende {u : ℕ → ℝ} {r : ℝ} (h : Tendsto u atTop (𝓝 r)) : (ofSeq u).Tendsto (𝓝 r) := by
  rw [Hyperreal.tendsto_ofSeq]
  exact h.mono_left (Filter.hyperfilter_le_cofinite.trans Nat.cofinite_eq_atTop.le)

/-- `st(ofSeq u) = lim u`. -/
theorem stdPart_ofSeq {u : ℕ → ℝ} {r : ℝ} (h : Tendsto u atTop (𝓝 r)) : stdPart (ofSeq u) = r :=
  stdPart_of_tendsto (germe_tende h)

/-- Uma sequência que tende a `0` dá um infinitesimal (classe arquimediana positiva). -/
theorem mk_pos_ofSeq {u : ℕ → ℝ} (h : Tendsto u atTop (𝓝 0)) : 0 < mk (ofSeq u) :=
  archimedeanClassMk_pos_of_tendsto (germe_tende h)

/-- `10⁻ᴴ` na posição hiperinteira `H = [n ↦ f n]`. -/
noncomputable def eps (f : ℕ → ℕ) : ℝ* := ofSeq fun n => ((1 : ℝ) / 10) ^ (f n)

theorem eps_id : eps id = ATK.TerceiroTemplo.dezMenosH := rfl

theorem tende_pot {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) :
    Tendsto (fun n => ((1 : ℝ) / 10) ^ (f n)) atTop (𝓝 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp hf

theorem eps_pos (f : ℕ → ℕ) : 0 < eps f := by
  have h0 : (0 : ℝ*) = ofSeq (fun _ => 0) := rfl
  rw [eps, h0, ofSeq_lt_ofSeq]
  exact Eventually.of_forall fun n => by positivity

theorem stdPart_eps {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) : stdPart (eps f) = 0 :=
  stdPart_ofSeq (tende_pot hf)

theorem mk_eps_pos {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) : 0 < mk (eps f) :=
  mk_pos_ofSeq (tende_pot hf)

/-- `ε(f)` está abaixo de todo real positivo. -/
theorem eps_lt_real {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) {r : ℝ} (hr : 0 < r) :
    eps f < (r : ℝ*) :=
  lt_of_pos_of_archimedean Hyperreal.coeRingHom (mk_eps_pos hf) hr

/-- `ε(f) < 10⁻ⁿ` para todo `n` natural. -/
theorem eps_lt_pot {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) (n : ℕ) :
    eps f < ((((1 : ℝ) / 10) ^ n : ℝ) : ℝ*) :=
  eps_lt_real hf (by positivity)

/-- **Lei da posição**: dígito mais distante, diferença menor. -/
theorem eps_lt_of_lt {f g : ℕ → ℕ} (h : ∀ n, f n < g n) : eps g < eps f := by
  rw [eps, eps, ofSeq_lt_ofSeq]
  exact Eventually.of_forall fun n =>
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (h n)

/-- **Produto de posições**: `10⁻ᶠ · 10⁻ᵍ = 10⁻⁽ᶠ⁺ᵍ⁾`. -/
theorem eps_mul (f g : ℕ → ℕ) : eps f * eps g = eps (f + g) := by
  have h : (fun n => ((1 : ℝ) / 10) ^ ((f + g) n)) =
      (fun n => ((1 : ℝ) / 10) ^ (f n)) * (fun n => ((1 : ℝ) / 10) ^ (g n)) := by
    funext n; simp [pow_add]
  rw [eps, eps, eps, h]
  rfl

/-- `10⁻²ᴴ = (10⁻ᴴ)² < 10⁻ᴴ`, com `H = [n ↦ n + 1]`. -/
theorem dois_H :
    eps (fun n => n + 1) * eps (fun n => n + 1) = eps (fun n => 2 * (n + 1)) ∧
      eps (fun n => 2 * (n + 1)) < eps (fun n => n + 1) := by
  refine ⟨?_, eps_lt_of_lt fun n => by omega⟩
  rw [eps_mul]
  congr 1
  funext n
  simp only [Pi.add_apply]
  ring

theorem um_mais_eq (f : ℕ → ℕ) : 1 + eps f = ofSeq fun n => 1 + ((1 : ℝ) / 10) ^ (f n) := rfl

theorem um_menos_eq (f : ℕ → ℕ) : 1 - eps f = ofSeq fun n => 1 - ((1 : ℝ) / 10) ^ (f n) := rfl

theorem stdPart_um_mais {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) : stdPart (1 + eps f) = 1 := by
  rw [um_mais_eq]
  have := (tendsto_const_nhds (x := (1 : ℝ))).add (tende_pot hf)
  rw [add_zero] at this
  exact stdPart_ofSeq this

theorem stdPart_um_menos {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) : stdPart (1 - eps f) = 1 := by
  rw [um_menos_eq]
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub (tende_pot hf)
  rw [sub_zero] at this
  exact stdPart_ofSeq this

/-- `1 − ε(f) < 1 < 1 + ε(f)` em qualquer posição, os três com parte padrão `1`. -/
theorem unidade_em_posicao {f : ℕ → ℕ} (hf : Tendsto f atTop atTop) :
    1 - eps f < 1 ∧ (1 : ℝ*) < 1 + eps f ∧
      stdPart (1 - eps f) = 1 ∧ stdPart (1 + eps f) = 1 := by
  have := eps_pos f
  exact ⟨by linarith, by linarith, stdPart_um_menos hf, stdPart_um_mais hf⟩

/-- **Lei da soma**: `(1 + ε(f)) + (1 + ε(g)) > 2`, com parte padrão `2`. -/
theorem lei_soma {f g : ℕ → ℕ} (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) :
    (2 : ℝ*) < (1 + eps f) + (1 + eps g) ∧ stdPart ((1 + eps f) + (1 + eps g)) = 2 := by
  have h1 := eps_pos f
  have h2 := eps_pos g
  refine ⟨by linarith, ?_⟩
  have hs : (1 + eps f) + (1 + eps g) =
      ofSeq fun n => (1 + ((1 : ℝ) / 10) ^ (f n)) + (1 + ((1 : ℝ) / 10) ^ (g n)) := rfl
  rw [hs]
  have := ((tendsto_const_nhds (x := (1 : ℝ))).add (tende_pot hf)).add
    ((tendsto_const_nhds (x := (1 : ℝ))).add (tende_pot hg))
  norm_num at this
  exact stdPart_ofSeq this

/-- **Lei do produto**: `(1 + ε(f))(1 + ε(g)) = 1 + ε(f) + ε(g) + ε(f + g) > 1`, parte padrão `1`. -/
theorem lei_produto {f g : ℕ → ℕ} (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop) :
    (1 + eps f) * (1 + eps g) = 1 + eps f + eps g + eps (f + g) ∧
      (1 : ℝ*) < (1 + eps f) * (1 + eps g) ∧ stdPart ((1 + eps f) * (1 + eps g)) = 1 := by
  have hexp : (1 + eps f) * (1 + eps g) = 1 + eps f + eps g + eps (f + g) := by
    rw [← eps_mul]; ring
  have h1 := eps_pos f
  have h2 := eps_pos g
  have h3 := eps_pos (f + g)
  refine ⟨hexp, by rw [hexp]; linarith, ?_⟩
  have hs : (1 + eps f) * (1 + eps g) =
      ofSeq fun n => (1 + ((1 : ℝ) / 10) ^ (f n)) * (1 + ((1 : ℝ) / 10) ^ (g n)) := rfl
  rw [hs]
  have := ((tendsto_const_nhds (x := (1 : ℝ))).add (tende_pot hf)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).add (tende_pot hg))
  norm_num at this
  exact stdPart_ofSeq this

/-- **Mesma parte padrão, ordem estrita**: com `f < g`, `0 < ε(g) < ε(f)` e os três têm
parte padrão `0`. -/
theorem mesma_classe_ordem_estrita {f g : ℕ → ℕ} (hf : Tendsto f atTop atTop)
    (hg : Tendsto g atTop atTop) (h : ∀ n, f n < g n) :
    (0 : ℝ*) < eps g ∧ eps g < eps f ∧
      stdPart (0 : ℝ*) = 0 ∧ stdPart (eps g) = 0 ∧ stdPart (eps f) = 0 :=
  ⟨eps_pos g, eps_lt_of_lt h, by simp, stdPart_eps hg, stdPart_eps hf⟩

end ATK.Discovery.Leis

#print axioms ATK.Discovery.Leis.germe_tende
#print axioms ATK.Discovery.Leis.stdPart_ofSeq
#print axioms ATK.Discovery.Leis.mk_pos_ofSeq
#print axioms ATK.Discovery.Leis.eps_id
#print axioms ATK.Discovery.Leis.tende_pot
#print axioms ATK.Discovery.Leis.eps_pos
#print axioms ATK.Discovery.Leis.stdPart_eps
#print axioms ATK.Discovery.Leis.mk_eps_pos
#print axioms ATK.Discovery.Leis.eps_lt_real
#print axioms ATK.Discovery.Leis.eps_lt_pot
#print axioms ATK.Discovery.Leis.eps_lt_of_lt
#print axioms ATK.Discovery.Leis.eps_mul
#print axioms ATK.Discovery.Leis.dois_H
#print axioms ATK.Discovery.Leis.um_mais_eq
#print axioms ATK.Discovery.Leis.um_menos_eq
#print axioms ATK.Discovery.Leis.stdPart_um_mais
#print axioms ATK.Discovery.Leis.stdPart_um_menos
#print axioms ATK.Discovery.Leis.unidade_em_posicao
#print axioms ATK.Discovery.Leis.lei_soma
#print axioms ATK.Discovery.Leis.lei_produto
#print axioms ATK.Discovery.Leis.mesma_classe_ordem_estrita
