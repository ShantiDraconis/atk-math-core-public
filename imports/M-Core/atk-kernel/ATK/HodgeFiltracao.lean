import ATK.L3Base
import Mathlib.Order.CompactlyGenerated.Basic

/-!
# ATK — Ponte B5 (casos conhecidos de Hodge): classes de Hodge e a filtração de Hodge

Para uma estrutura de Hodge racional pura de peso `2p` (`ATK.L3Base.HodgeStructure`), a
**filtração de Hodge** é `F^p = ⨁_{q ≥ p} H^{q, 2p−q}`. Este arquivo prova:

* `conj_filtracao`: a conjugação leva `F^p` em `F̄^p = ⨁_{q ≤ n−p} H^{q, n−q}`;
* `inter_filtracao`: `F^p ∩ F̄^p = H^{p,p}` (pela independência da decomposição);
* `isHodgeClass_iff_filtracao`: **um vetor racional é classe de Hodge sse está em `F^p`**
  (a formulação de Deligne `Hdg^p = V_ℚ ∩ F^p`). Para `p = 1` é a metade de álgebra linear do
  teorema de Lefschetz (1,1): a classe é de Hodge sse a sua componente em `H^{0,2}`
  (`= H²(X, 𝒪_X)`) se anula;
* `hodgeClasses_eq_top`: se `H^{q, 2p−q} = 0` para todo `q > p`, **toda classe racional é de
  Hodge** (para `p = 1`: `p_g = h^{2,0} = 0`).

O resto da ponte B5 (a classe de Hodge vir de um divisor, via a sequência exponencial) e a
obrigação O5 dependem da cohomologia de variedades projetivas, ausente da Mathlib: B5 continua
`PUBLICADA_NAO_FORMALIZADA` e O5 `OPEN_MATH`.
-/

open TensorProduct ATK.L3Base

namespace ATK.HodgeFiltracao

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A filtração de Hodge `F^p = ⨁_{q ≥ p} H^{q, n−q}`. -/
noncomputable def filtracao {n : ℤ} (h : HodgeStructure V n) (p : ℤ) : Submodule ℂ (ℂ ⊗[ℚ] V) :=
  ⨆ q ∈ {q : ℤ | p ≤ q}, h.H q

/-- A filtração conjugada `F̄^p = ⨁_{q ≤ n−p} H^{q, n−q}`. -/
noncomputable def filtracaoConj {n : ℤ} (h : HodgeStructure V n) (p : ℤ) : Submodule ℂ (ℂ ⊗[ℚ] V) :=
  ⨆ q ∈ {q : ℤ | q ≤ n - p}, h.H q

theorem conj_mem_H {n : ℤ} (h : HodgeStructure V n) {q : ℤ} {x : ℂ ⊗[ℚ] V} (hx : x ∈ h.H q) :
    conjV V x ∈ h.H (n - q) := by
  have : conjV V x ∈ conjV V '' (h.H q : Set (ℂ ⊗[ℚ] V)) := ⟨x, hx, rfl⟩
  rw [h.conj_eq q] at this
  exact this

/-- A conjugação leva `F^p` em `F̄^p`. -/
theorem conj_filtracao {n : ℤ} (h : HodgeStructure V n) (p : ℤ) {x : ℂ ⊗[ℚ] V}
    (hx : x ∈ filtracao h p) : conjV V x ∈ filtracaoConj h p := by
  unfold filtracao at hx
  induction hx using Submodule.iSup_induction' with
  | mem q y hy =>
    induction hy using Submodule.iSup_induction' with
    | mem hq z hz =>
      exact Submodule.mem_iSup_of_mem (n - q)
        (Submodule.mem_iSup_of_mem (show n - q ∈ {q : ℤ | q ≤ n - p} by
          simp only [Set.mem_ofPred_eq] at hq ⊢; omega) (conj_mem_H h hz))
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb

/-- `F^p ∩ F̄^p = H^{p,p}` em peso `2p`. -/
theorem inter_filtracao {p : ℤ} (h : HodgeStructure V (2 * p)) {x : ℂ ⊗[ℚ] V}
    (h1 : x ∈ filtracao h p) (h2 : x ∈ filtracaoConj h p) : x ∈ h.H p := by
  have hind : iSupIndep h.H :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp h.isInternal |>.1
  -- `F^p = H p ⊔ ⨆_{q > p}` e `F̄^p = H p ⊔ ⨆_{q < p}`
  have split1 : filtracao h p ≤ h.H p ⊔ ⨆ q ∈ {q : ℤ | p < q}, h.H q := by
    refine iSup₂_le fun q hq => ?_
    simp only [Set.mem_ofPred_eq] at hq
    rcases eq_or_lt_of_le hq with rfl | hlt
    · exact le_sup_left
    · exact le_sup_of_le_right (le_biSup h.H (show q ∈ {q : ℤ | p < q} from hlt))
  have split2 : filtracaoConj h p ≤ h.H p ⊔ ⨆ q ∈ {q : ℤ | q < p}, h.H q := by
    refine iSup₂_le fun q hq => ?_
    simp only [Set.mem_ofPred_eq] at hq
    rcases eq_or_lt_of_le (show q ≤ p by omega) with rfl | hlt
    · exact le_sup_left
    · exact le_sup_of_le_right (le_biSup h.H (show q ∈ {q : ℤ | q < p} from hlt))
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (split1 h1)
  obtain ⟨a', ha', c, hc, hac⟩ := Submodule.mem_sup.mp (split2 h2)
  -- `b − c ∈ H p ∩ ⨆_{q ≠ p} = 0`
  have hne : ∀ S : Set ℤ, p ∉ S → (⨆ q ∈ S, h.H q) ≤ ⨆ (q) (_ : q ≠ p), h.H q := fun S hS =>
    iSup₂_le fun q hq => le_biSup h.H (show q ≠ p from fun e => hS (e ▸ hq))
  have hbc : b - c = a' - a := by rw [sub_eq_sub_iff_add_eq_add, add_comm b a, ← hac, add_comm]
  have hd := Submodule.disjoint_def.mp ((iSupIndep_def.mp hind) p) (a' - a) (sub_mem ha' ha)
    (hbc ▸ sub_mem (hne _ (by simp) hb) (hne _ (by simp) hc))
  have hbc' : b = c := by rw [← sub_eq_zero, hbc, hd]
  -- `b ∈ ⨆_{q > p} ∩ ⨆_{q < p} = 0`
  have hdisj := hind.disjoint_biSup_biSup (s := {q : ℤ | p < q}) (t := {q : ℤ | q < p})
    (Set.disjoint_left.mpr fun q h1 h2 => by simp only [Set.mem_ofPred_eq] at h1 h2; omega)
  have hb0 : b = 0 := Submodule.disjoint_def.mp hdisj b hb (hbc' ▸ hc)
  rw [hb0, add_zero]
  exact ha

/-- **Classe de Hodge ⟺ vetor racional em `F^p`** (Deligne: `Hdg^p = V_ℚ ∩ F^p`). Para `p = 1`:
a classe é de Hodge sse a componente em `H^{0,2}` se anula (Lefschetz (1,1), parte linear). -/
theorem isHodgeClass_iff_filtracao {p : ℤ} (h : HodgeStructure V (2 * p)) (v : V) :
    IsHodgeClass h v ↔ (1 : ℂ) ⊗ₜ[ℚ] v ∈ filtracao h p := by
  constructor
  · intro hv
    exact le_biSup h.H (show p ∈ {q : ℤ | p ≤ q} from le_refl p) hv
  · intro hv
    have hc := conj_filtracao h p hv
    rw [conjV_tmul, map_one] at hc
    exact inter_filtracao h hv (by simpa [filtracaoConj, show 2 * p - p = p by ring] using hc)

/-- **`H^{q, 2p−q} = 0` para `q > p` ⇒ toda classe racional é de Hodge** (para `p = 1`, superfícies
com `p_g = 0`: todo `H²(X, ℚ)` é de tipo `(1,1)`). -/
theorem hodgeClasses_eq_top {p : ℤ} (h : HodgeStructure V (2 * p))
    (hz : ∀ q, p < q → h.H q = ⊥) : hodgeClasses h = ⊤ := by
  have htop : (⨆ q, h.H q) = ⊤ :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp h.isInternal |>.2
  have hle : ∀ q, h.H q ≤ h.H p := by
    intro q
    rcases lt_trichotomy q p with hlt | rfl | hgt
    · -- `H q = conj H (2p − q)` e `2p − q > p`
      have h0 := hz (2 * p - q) (by omega)
      intro x hx
      have := conj_mem_H h hx
      rw [h0, Submodule.mem_bot] at this
      have : x = 0 := by rw [← conjV_conjV V x, this, map_zero]
      rw [this]; exact zero_mem _
    · exact le_refl _
    · rw [hz q hgt]; exact bot_le
  have hp : h.H p = ⊤ := eq_top_iff.mpr (htop ▸ iSup_le hle)
  exact eq_top_iff.mpr fun v _ => by
    show (1 : ℂ) ⊗ₜ[ℚ] v ∈ h.H p
    rw [hp]; exact Submodule.mem_top

end ATK.HodgeFiltracao

#print axioms ATK.HodgeFiltracao.conj_mem_H
#print axioms ATK.HodgeFiltracao.conj_filtracao
#print axioms ATK.HodgeFiltracao.inter_filtracao
#print axioms ATK.HodgeFiltracao.isHodgeClass_iff_filtracao
#print axioms ATK.HodgeFiltracao.hodgeClasses_eq_top
