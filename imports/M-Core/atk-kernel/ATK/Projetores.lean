import Mathlib

/-!
# ATK — Simetrias, projetores, estrela de Hodge, gap 2×2, descida e limites

Itens das mensagens de "produtores materiais" (Hodge, Yang–Mills, geral) que faltavam:

* **Involução** (`S² = 1`, `2` invertível): `P± = (1 ± S)/2` são projetores complementares, ortogonais,
  com `S P± = ±P±`, e a decomposição `v = v₊ + v₋` (`S v± = ±v±`) é **única**.
* **Ordem `m`** (`S^m = 1`, `ω` raiz primitiva, `m ≠ 0` no corpo): `P_j = (1/m) Σ_k ω^{−jk} S^k`
  dão `Σ_j P_j = 1`, `S P_j = ω^j P_j`, `P_j P_l = δ_{jl} P_j` (a transformada de Fourier discreta).
* **Estrela de Hodge em `Λ²ℝ⁴ ≅ ℝ⁶`** (base `e12, e13, e14, e23, e24, e34`): `⋆⋆ = 1`, `⋆` simétrica e
  isométrica, `F = F₊ + F₋` com `⋆F± = ±F±`, `⟨F₊, F₋⟩ = 0`, `|F|² = |F₊|² + |F₋|²`,
  `⟨F, ⋆F⟩ = |F₊|² − |F₋|²` e a **cota de Bogomolny pontual** `|⟨F, ⋆F⟩| ≤ |F|²`, com igualdade
  ⟺ `F = ⋆F` ou `F = −⋆F` (auto-dual / anti-auto-dual).
* **Gap 2×2**: `Δ(a, b, c) = √((a − c)² + 4b²)` é a diferença dos autovalores de `[[a, b], [b, c]]`;
  `Δ(H + V) ≥ Δ(H) − Δ(V)` e, se os autovalores de `V` estão em `[−ε, ε]`, `Δ(V) ≤ 2ε`.
* **Descida infinita abstrata**: `h : S → ℕ` que sempre desce ⇒ `S` vazio.
* **Somas sobre pares**: `2 Σ_{i<j} f(i, j) = Σ_{i≠j} f(i, j)` para `f` simétrica.
* **Limites iterados não comutam**: `F(n, m) = (n + 1)/(n + m + 2)`.
* **Solução fundamental radial**: `g(r) = r^{2−d}` resolve `g'' + ((d − 1)/r) g' = 0` (todo `d` real), e
  `log r` resolve o caso `d = 2`.
-/

open Finset Filter Topology

namespace ATK.Projetores

/-! ## 1. Involuções -/

section Involucao

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- `P₊ = (1 + S)/2`. -/
def Pmais (S : A) : A := (2⁻¹ : K) • (1 + S)
/-- `P₋ = (1 − S)/2`. -/
def Pmenos (S : A) : A := (2⁻¹ : K) • (1 - S)

variable (h2 : (2 : K) ≠ 0) {S : A} (hS : S * S = 1)
include h2 hS

theorem Pmais_idem : Pmais (K := K) S * Pmais (K := K) S = Pmais (K := K) S := by
  unfold Pmais
  rw [smul_mul_smul_comm, show (1 + S) * (1 + S) = (2 : K) • (1 + S) by
    rw [two_smul]
    calc (1 + S) * (1 + S) = 1 + S + S + S * S := by noncomm_ring
      _ = (1 + S) + (1 + S) := by rw [hS]; abel]
  rw [smul_smul]
  congr 1
  field_simp

theorem Pmenos_idem : Pmenos (K := K) S * Pmenos (K := K) S = Pmenos (K := K) S := by
  unfold Pmenos
  rw [smul_mul_smul_comm, show (1 - S) * (1 - S) = (2 : K) • (1 - S) by
    rw [two_smul]
    calc (1 - S) * (1 - S) = 1 - S - S + S * S := by noncomm_ring
      _ = (1 - S) + (1 - S) := by rw [hS]; abel]
  rw [smul_smul]
  congr 1
  field_simp

theorem Pmais_Pmenos : Pmais (K := K) S * Pmenos (K := K) S = 0 := by
  unfold Pmais Pmenos
  rw [smul_mul_smul_comm, show (1 + S) * (1 - S) = 0 by
    calc (1 + S) * (1 - S) = 1 - S * S := by noncomm_ring
      _ = 0 := by rw [hS, sub_self], smul_zero]

theorem Pmenos_Pmais : Pmenos (K := K) S * Pmais (K := K) S = 0 := by
  unfold Pmais Pmenos
  rw [smul_mul_smul_comm, show (1 - S) * (1 + S) = 0 by
    calc (1 - S) * (1 + S) = 1 - S * S := by noncomm_ring
      _ = 0 := by rw [hS, sub_self], smul_zero]

theorem Pmais_add_Pmenos : Pmais (K := K) S + Pmenos (K := K) S = 1 := by
  unfold Pmais Pmenos
  rw [← smul_add, show (1 + S) + (1 - S) = (2 : K) • (1 : A) by rw [two_smul]; abel, smul_smul,
    inv_mul_cancel₀ h2, one_smul]

theorem S_Pmais : S * Pmais (K := K) S = Pmais (K := K) S := by
  unfold Pmais
  rw [mul_smul_comm, mul_add, hS, mul_one, add_comm]

theorem S_Pmenos : S * Pmenos (K := K) S = -Pmenos (K := K) S := by
  unfold Pmenos
  rw [mul_smul_comm, mul_sub, hS, mul_one, ← smul_neg, neg_sub]

end Involucao

/-- **Decomposição única**: para uma involução linear `S`, todo `v` é `v₊ + v₋` com `S v± = ±v±`,
e a decomposição é única. -/
theorem decomposicao_unica {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (h2 : (2 : K) ≠ 0) (S : V →ₗ[K] V) (hS : ∀ v, S (S v) = v) (v : V) :
    (∃ a b : V, v = a + b ∧ S a = a ∧ S b = -b) ∧
      ∀ a b a' b' : V, a + b = a' + b' → S a = a → S b = -b → S a' = a' → S b' = -b' →
        a = a' ∧ b = b' := by
  refine ⟨⟨(2⁻¹ : K) • (v + S v), (2⁻¹ : K) • (v - S v), ?_, ?_, ?_⟩, ?_⟩
  · rw [← smul_add, show (v + S v) + (v - S v) = (2 : K) • v by rw [two_smul]; abel, smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  · rw [map_smul, map_add, hS, add_comm]
  · rw [map_smul, map_sub, hS, ← smul_neg, neg_sub]
  · intro a b a' b' he ha hb ha' hb'
    have h1 : S (a + b) = S (a' + b') := by rw [he]
    rw [map_add, map_add, ha, hb, ha', hb'] at h1
    have hsum : (a - a') + (b - b') = 0 := by
      rw [sub_add_sub_comm, he, sub_self]
    have hdif : (a - a') - (b - b') = 0 := by
      have : a - b = a' - b' := by
        have := h1; rw [← sub_eq_add_neg, ← sub_eq_add_neg] at this; exact this
      rw [sub_sub_sub_comm, this, sub_self]
    have h2a : (2 : K) • (a - a') = 0 := by
      rw [two_smul]
      have := congrArg₂ (· + ·) hsum hdif
      simp only [add_zero] at this
      rw [← this]; abel
    have h2b : (2 : K) • (b - b') = 0 := by
      rw [two_smul]
      have := congrArg₂ (· - ·) hsum hdif
      simp only [sub_zero] at this
      rw [← this]; abel
    have ea := (smul_eq_zero.mp h2a).resolve_left h2
    have eb := (smul_eq_zero.mp h2b).resolve_left h2
    exact ⟨sub_eq_zero.mp ea, sub_eq_zero.mp eb⟩

/-! ## 2. Ordem `m`: projetores de Fourier discretos -/

section OrdemM

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- `P_j = (1/m) Σ_{k<m} ω^{−jk} S^k`. -/
def Pj (m : ℕ) (ω : K) (S : A) (j : ℕ) : A :=
  (m : K)⁻¹ • ∑ k ∈ range m, ((ω⁻¹) ^ (j * k)) • S ^ k

theorem geom_zero {x : K} {m : ℕ} (hx : x ^ m = 1) (h1 : x ≠ 1) : ∑ j ∈ range m, x ^ j = 0 := by
  rw [geom_sum_eq h1, hx, sub_self, zero_div]

variable {m : ℕ} {ω : K} (hω : IsPrimitiveRoot ω m) (hm : (m : K) ≠ 0) {S : A} (hS : S ^ m = 1)
include hω hm hS

theorem m_pos : 0 < m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h; simp at hm
  · exact h

theorem omega_ne : ω ≠ 0 := hω.ne_zero (m_pos hω hm hS).ne'

/-- `Σ_j P_j = 1`. -/
theorem soma_Pj : ∑ j ∈ range m, Pj m ω S j = 1 := by
  have hm0 := m_pos hω hm hS
  have hω0 := omega_ne hω hm hS
  unfold Pj
  rw [← Finset.smul_sum, Finset.sum_comm]
  have key : ∀ k ∈ range m, (∑ j ∈ range m, ((ω⁻¹) ^ (j * k)) • S ^ k) =
      if k = 0 then (m : K) • (1 : A) else 0 := by
    intro k hk
    rw [← Finset.sum_smul]
    split_ifs with h0
    · subst h0; simp
    · have hk' : k < m := Finset.mem_range.mp hk
      have hne : (ω⁻¹) ^ k ≠ 1 := by
        rw [inv_pow]
        intro h
        exact hω.pow_ne_one_of_pos_of_lt h0 hk' (inv_eq_one.mp h)
      have hpow : ((ω⁻¹) ^ k) ^ m = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, inv_pow, hω.pow_eq_one, inv_one, one_pow]
      have : ∑ j ∈ range m, (ω⁻¹) ^ (j * k) = 0 := by
        simp_rw [mul_comm _ k, pow_mul]
        exact geom_zero hpow hne
      rw [this, zero_smul]
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq' (range m) 0, if_pos (Finset.mem_range.mpr hm0),
    smul_smul, inv_mul_cancel₀ hm, one_smul]

/-- `S P_j = ω^j P_j`. -/
theorem S_Pj (j : ℕ) : S * Pj m ω S j = ω ^ j • Pj m ω S j := by
  have hω0 := omega_ne hω hm hS
  unfold Pj
  rw [mul_smul_comm, smul_comm (ω ^ j)]
  congr 1
  rw [Finset.mul_sum]
  set b : ℕ → A := fun k => ((ω⁻¹) ^ (j * k)) • S ^ k with hb
  have hstep : ∀ k, S * (((ω⁻¹) ^ (j * k)) • S ^ k) = ω ^ j • b (k + 1) := by
    intro k
    have hc : ω ^ j * (ω⁻¹) ^ (j * (k + 1)) = (ω⁻¹) ^ (j * k) := by
      rw [mul_add, mul_one, pow_add, ← mul_assoc, mul_comm (ω ^ j), mul_assoc, ← mul_pow,
        mul_inv_cancel₀ hω0, one_pow, mul_one]
    rw [mul_smul_comm, ← pow_succ', hb]
    simp only
    rw [smul_smul, hc]
  simp_rw [hstep]
  rw [← Finset.smul_sum]
  congr 1
  have hbm : b m = b 0 := by
    simp only [hb, pow_zero, mul_zero, one_smul, hS]
    rw [mul_comm, pow_mul, inv_pow, hω.pow_eq_one, inv_one, one_pow, one_smul]
  have h1 := Finset.sum_range_succ' b m
  have h2 := Finset.sum_range_succ b m
  rw [hbm] at h2
  exact add_right_cancel (h1.symm.trans h2)

theorem pow_S_Pj (j k : ℕ) : S ^ k * Pj m ω S j = (ω ^ j) ^ k • Pj m ω S j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm, S_Pj hω hm hS, smul_smul, pow_succ, mul_comm]

/-- `P_j P_l = δ_{jl} P_j`. -/
theorem Pj_mul {j l : ℕ} (hj : j < m) (hl : l < m) :
    Pj m ω S j * Pj m ω S l = if j = l then Pj m ω S l else 0 := by
  have hω0 := omega_ne hω hm hS
  conv_lhs => rw [Pj]
  rw [smul_mul_assoc, Finset.sum_mul]
  simp_rw [smul_mul_assoc, pow_S_Pj hω hm hS, smul_smul]
  rw [← Finset.sum_smul, smul_smul]
  have hx : ∀ k, (ω⁻¹) ^ (j * k) * (ω ^ l) ^ k = ((ω⁻¹) ^ j * ω ^ l) ^ k := by
    intro k; rw [mul_pow, pow_mul]
  simp_rw [hx]
  split_ifs with hjl
  · subst hjl
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hω0)]
    simp [inv_mul_cancel₀ hm]
  · have hne : (ω⁻¹) ^ j * ω ^ l ≠ 1 := by
      intro h
      rw [inv_pow, inv_mul_eq_one₀ (pow_ne_zero _ hω0)] at h
      exact hjl (hω.pow_inj hj hl h)
    have hpow : ((ω⁻¹) ^ j * ω ^ l) ^ m = 1 := by
      rw [mul_pow, ← pow_mul, mul_comm j m, pow_mul, inv_pow, hω.pow_eq_one, inv_one, one_pow,
        one_mul, ← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    rw [geom_zero hpow hne, mul_zero, zero_smul]

end OrdemM

/-! ## 3. Estrela de Hodge em `Λ²ℝ⁴ ≅ ℝ⁶` -/

/-- `⋆` na base `e12, e13, e14, e23, e24, e34`: `⋆e12 = e34`, `⋆e13 = −e24`, `⋆e14 = e23`. -/
def hstar (F : Fin 6 → ℝ) : Fin 6 → ℝ := ![F 5, -F 4, F 3, F 2, -F 1, F 0]

/-- Produto interno `⟨F, G⟩ = Σ F_i G_i`. -/
def ip (F G : Fin 6 → ℝ) : ℝ := ∑ i, F i * G i

theorem hstar_hstar (F : Fin 6 → ℝ) : hstar (hstar F) = F := by
  funext i; fin_cases i <;> simp [hstar]

theorem hstar_simetrica (F G : Fin 6 → ℝ) : ip (hstar F) G = ip F (hstar G) := by
  simp [ip, hstar, Fin.sum_univ_six]; ring

theorem hstar_isometria (F : Fin 6 → ℝ) : ip (hstar F) (hstar F) = ip F F := by
  simp [ip, hstar, Fin.sum_univ_six]; ring

/-- Partes auto-dual e anti-auto-dual. -/
noncomputable def Fmais (F : Fin 6 → ℝ) : Fin 6 → ℝ := fun i => (F i + hstar F i) / 2
noncomputable def Fmenos (F : Fin 6 → ℝ) : Fin 6 → ℝ := fun i => (F i - hstar F i) / 2

theorem hstar_Fmais (F : Fin 6 → ℝ) : hstar (Fmais F) = Fmais F := by
  funext i; fin_cases i <;> simp [hstar, Fmais] <;> ring

theorem hstar_Fmenos (F : Fin 6 → ℝ) : hstar (Fmenos F) = fun i => -Fmenos F i := by
  funext i; fin_cases i <;> simp [hstar, Fmenos] <;> ring

theorem F_decomp (F : Fin 6 → ℝ) : F = fun i => Fmais F i + Fmenos F i := by
  funext i; simp [Fmais, Fmenos]; ring

theorem Fmais_Fmenos_orto (F : Fin 6 → ℝ) : ip (Fmais F) (Fmenos F) = 0 := by
  simp [ip, Fmais, Fmenos, hstar, Fin.sum_univ_six]; ring

theorem norma_decomp (F : Fin 6 → ℝ) : ip F F = ip (Fmais F) (Fmais F) + ip (Fmenos F) (Fmenos F) := by
  simp [ip, Fmais, Fmenos, hstar, Fin.sum_univ_six]; ring

theorem topologico (F : Fin 6 → ℝ) :
    ip F (hstar F) = ip (Fmais F) (Fmais F) - ip (Fmenos F) (Fmenos F) := by
  simp [ip, Fmais, Fmenos, hstar, Fin.sum_univ_six]; ring

theorem ip_self_nonneg (F : Fin 6 → ℝ) : 0 ≤ ip F F := by
  simp only [ip]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- `|F|² − ⟨F, ⋆F⟩ = ½ Σ (F − ⋆F)²` e `|F|² + ⟨F, ⋆F⟩ = ½ Σ (F + ⋆F)²`. -/
theorem defeitos (F : Fin 6 → ℝ) :
    ip F F - ip F (hstar F) = (∑ i, (F i - hstar F i) ^ 2) / 2 ∧
      ip F F + ip F (hstar F) = (∑ i, (F i + hstar F i) ^ 2) / 2 := by
  constructor <;> simp [ip, hstar, Fin.sum_univ_six] <;> ring

/-- **Bogomolny pontual**: `|⟨F, ⋆F⟩| ≤ |F|²`. -/
theorem bogomolny (F : Fin 6 → ℝ) : |ip F (hstar F)| ≤ ip F F := by
  obtain ⟨h1, h2⟩ := defeitos F
  have a : 0 ≤ (∑ i, (F i - hstar F i) ^ 2) / 2 := by positivity
  have b : 0 ≤ (∑ i, (F i + hstar F i) ^ 2) / 2 := by positivity
  rw [abs_le]; constructor <;> linarith

/-- **Igualdade**: `⟨F, ⋆F⟩ = |F|² ⟺ F = ⋆F` (auto-dual). -/
theorem bogomolny_igual_autodual (F : Fin 6 → ℝ) : ip F (hstar F) = ip F F ↔ hstar F = F := by
  obtain ⟨h1, -⟩ := defeitos F
  constructor
  · intro h
    have hs : ∑ i, (F i - hstar F i) ^ 2 = 0 := by linarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (F i - hstar F i))).mp hs
    funext i
    have := hz i (Finset.mem_univ i)
    have : F i - hstar F i = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · intro h
    have : ∑ i, (F i - hstar F i) ^ 2 = 0 := by simp [h]
    linarith

/-- `−⟨F, ⋆F⟩ = |F|² ⟺ F = −⋆F` (anti-auto-dual). -/
theorem bogomolny_igual_anti (F : Fin 6 → ℝ) :
    -ip F (hstar F) = ip F F ↔ hstar F = fun i => -F i := by
  obtain ⟨-, h2⟩ := defeitos F
  constructor
  · intro h
    have hs : ∑ i, (F i + hstar F i) ^ 2 = 0 := by linarith
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (F i + hstar F i))).mp hs
    funext i
    have := hz i (Finset.mem_univ i)
    have : F i + hstar F i = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  · intro h
    have : ∑ i, (F i + hstar F i) ^ 2 = 0 := by simp [h]
    linarith

/-! ## 4. Gap espectral 2×2 -/

/-- `Δ(a, b, c) = √((a − c)² + 4b²)`, a diferença dos autovalores de `[[a, b], [b, c]]`. -/
noncomputable def gap (a b c : ℝ) : ℝ := Real.sqrt ((a - c) ^ 2 + 4 * b ^ 2)

theorem gap_eq_norm (a b c : ℝ) : gap a b c = ‖((a - c : ℝ) : ℂ) + ((2 * b : ℝ) : ℂ) * Complex.I‖ := by
  rw [gap, Complex.norm_eq_sqrt_sq_add_sq]
  simp
  ring_nf

/-- Os autovalores `(a + c ± Δ)/2` anulam o polinômio característico. -/
theorem autovalores (a b c : ℝ) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    let l := (a + c + s * gap a b c) / 2
    (a - l) * (c - l) - b ^ 2 = 0 := by
  intro l
  have hg : gap a b c ^ 2 = (a - c) ^ 2 + 4 * b ^ 2 := Real.sq_sqrt (by positivity)
  have hs2 : s ^ 2 = 1 := by rcases hs with h | h <;> simp [h]
  simp only [l]
  nlinarith [hg, hs2]

/-- **Estabilidade**: `Δ(H + V) ≥ Δ(H) − Δ(V)`. -/
theorem gap_estavel (a b c p q r : ℝ) : gap a b c - gap p q r ≤ gap (a + p) (b + q) (c + r) := by
  rw [gap_eq_norm, gap_eq_norm, gap_eq_norm]
  have e : ((a + p - (c + r) : ℝ) : ℂ) + ((2 * (b + q) : ℝ) : ℂ) * Complex.I =
      (((a - c : ℝ) : ℂ) + ((2 * b : ℝ) : ℂ) * Complex.I) +
        (((p - r : ℝ) : ℂ) + ((2 * q : ℝ) : ℂ) * Complex.I) := by push_cast; ring
  rw [e]
  have := norm_sub_norm_le (((a - c : ℝ) : ℂ) + ((2 * b : ℝ) : ℂ) * Complex.I +
      (((p - r : ℝ) : ℂ) + ((2 * q : ℝ) : ℂ) * Complex.I)) (((p - r : ℝ) : ℂ) + ((2 * q : ℝ) : ℂ) * Complex.I)
  rw [add_sub_cancel_right] at this
  have h2 := norm_sub_norm_le (((a - c : ℝ) : ℂ) + ((2 * b : ℝ) : ℂ) * Complex.I)
    (-(((p - r : ℝ) : ℂ) + ((2 * q : ℝ) : ℂ) * Complex.I))
  rw [sub_neg_eq_add, norm_neg] at h2
  linarith

/-- Se os autovalores de `V` estão em `[−ε, ε]`, então `Δ(V) ≤ 2ε`; logo `Δ(H + V) ≥ Δ(H) − 2ε`. -/
theorem gap_perturbado (a b c p q r ε : ℝ)
    (hmax : (p + r + gap p q r) / 2 ≤ ε) (hmin : -ε ≤ (p + r - gap p q r) / 2) :
    gap a b c - 2 * ε ≤ gap (a + p) (b + q) (c + r) := by
  have hV : gap p q r ≤ 2 * ε := by linarith
  have := gap_estavel a b c p q r
  linarith

/-! ## 5. Descida, pares, limites iterados -/

/-- **Descida infinita**: se `h : S → ℕ` sempre admite um valor menor, `S` é vazio. -/
theorem descida {S : Type*} (h : S → ℕ) (d : ∀ x, ∃ y, h y < h x) : IsEmpty S := by
  refine ⟨fun x => ?_⟩
  have key : ∀ n : ℕ, ∀ x : S, h x ≠ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro x hx
      obtain ⟨y, hy⟩ := d x
      exact ih (h y) (hx ▸ hy) y rfl
  exact key (h x) x rfl

/-- `2 Σ_{i<j} f(i, j) = Σ_{i≠j} f(i, j)` para `f` simétrica. -/
theorem soma_pares {n : ℕ} {R : Type*} [CommRing R] (f : Fin n → Fin n → R)
    (hf : ∀ i j, f i j = f j i) :
    2 * ∑ i, ∑ j, (if i < j then f i j else 0) = ∑ i, ∑ j, (if i ≠ j then f i j else 0) := by
  have hsplit : ∀ i j : Fin n, (if i ≠ j then f i j else 0) =
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hswap : ∑ i, ∑ j, (if j < i then f i j else 0) = ∑ i, ∑ j, (if i < j then f i j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hf]
  rw [hswap]; ring

/-- **Limites iterados não comutam**: `F(n, m) = (n + 1)/(n + m + 2)`. -/
theorem limites_iterados :
    (∀ n : ℕ, Tendsto (fun m : ℕ => ((n : ℝ) + 1) / (n + m + 2)) atTop (𝓝 0)) ∧
      ∀ m : ℕ, Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n + m + 2)) atTop (𝓝 1) := by
  constructor
  · intro n
    have h : Tendsto (fun m : ℕ => ((n : ℝ) + 2) + (m : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    have := h.inv_tendsto_atTop.const_mul ((n : ℝ) + 1)
    rw [mul_zero] at this
    refine this.congr fun m => ?_
    simp only [Pi.inv_apply]
    rw [div_eq_mul_inv]; ring_nf
  · intro m
    have h : Tendsto (fun n : ℕ => (n : ℝ) + ((m : ℝ) + 2)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 := (h.inv_tendsto_atTop.const_mul ((m : ℝ) + 1)).const_sub 1
    rw [mul_zero, sub_zero] at h2
    refine h2.congr fun n => ?_
    simp only [Pi.inv_apply]
    have hpos : (0 : ℝ) < (n : ℝ) + ((m : ℝ) + 2) := by positivity
    field_simp
    ring

/-! ## 6. Solução fundamental radial -/

/-- `g(r) = r^{2−d}`: `g' = (2 − d) r^{1−d}`, `g'' = (2 − d)(1 − d) r^{−d}` e
`g'' + ((d − 1)/r) g' = 0` para `r > 0` (qualquer `d` real). -/
theorem radial (d r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun x : ℝ => x ^ (2 - d)) ((2 - d) * r ^ (1 - d)) r ∧
      HasDerivAt (fun x : ℝ => (2 - d) * x ^ (1 - d)) ((2 - d) * ((1 - d) * r ^ (-d))) r ∧
      (2 - d) * ((1 - d) * r ^ (-d)) + (d - 1) / r * ((2 - d) * r ^ (1 - d)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · have := Real.hasDerivAt_rpow_const (x := r) (p := 2 - d) (Or.inl hr.ne')
    convert this using 2; ring_nf
  · have := (Real.hasDerivAt_rpow_const (x := r) (p := 1 - d) (Or.inl hr.ne')).const_mul (2 - d)
    convert this using 2; ring_nf
  · have e : r ^ (1 - d) = r * r ^ (-d) := by
      rw [show (1 : ℝ) - d = 1 + (-d) by ring, Real.rpow_add hr, Real.rpow_one]
    rw [e]
    field_simp
    ring

/-- Caso `d = 2`: `g = log r`, `g'' + g'/r = 0`. -/
theorem radial_log (r : ℝ) (hr : 0 < r) :
    HasDerivAt Real.log r⁻¹ r ∧ HasDerivAt (fun x : ℝ => x⁻¹) (-(r ^ 2)⁻¹) r ∧
      -(r ^ 2)⁻¹ + 1 / r * r⁻¹ = 0 := by
  refine ⟨Real.hasDerivAt_log hr.ne', hasDerivAt_inv hr.ne', ?_⟩
  field_simp
  ring

end ATK.Projetores

-- Auditoria de axiomas (kernel)
#print axioms ATK.Projetores.Pmais_idem
#print axioms ATK.Projetores.Pmenos_idem
#print axioms ATK.Projetores.Pmais_Pmenos
#print axioms ATK.Projetores.Pmenos_Pmais
#print axioms ATK.Projetores.Pmais_add_Pmenos
#print axioms ATK.Projetores.S_Pmais
#print axioms ATK.Projetores.S_Pmenos
#print axioms ATK.Projetores.decomposicao_unica
#print axioms ATK.Projetores.geom_zero
#print axioms ATK.Projetores.soma_Pj
#print axioms ATK.Projetores.S_Pj
#print axioms ATK.Projetores.pow_S_Pj
#print axioms ATK.Projetores.Pj_mul
#print axioms ATK.Projetores.hstar_hstar
#print axioms ATK.Projetores.hstar_simetrica
#print axioms ATK.Projetores.hstar_isometria
#print axioms ATK.Projetores.hstar_Fmais
#print axioms ATK.Projetores.hstar_Fmenos
#print axioms ATK.Projetores.F_decomp
#print axioms ATK.Projetores.Fmais_Fmenos_orto
#print axioms ATK.Projetores.norma_decomp
#print axioms ATK.Projetores.topologico
#print axioms ATK.Projetores.defeitos
#print axioms ATK.Projetores.bogomolny
#print axioms ATK.Projetores.bogomolny_igual_autodual
#print axioms ATK.Projetores.bogomolny_igual_anti
#print axioms ATK.Projetores.gap_eq_norm
#print axioms ATK.Projetores.autovalores
#print axioms ATK.Projetores.gap_estavel
#print axioms ATK.Projetores.gap_perturbado
#print axioms ATK.Projetores.descida
#print axioms ATK.Projetores.soma_pares
#print axioms ATK.Projetores.limites_iterados
#print axioms ATK.Projetores.radial
#print axioms ATK.Projetores.radial_log
