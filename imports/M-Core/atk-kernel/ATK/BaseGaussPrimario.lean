import ATK.PonteCoefCurva32
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity

/-!
# ATK — Base: inteiros de Gauss primários e a série `Σ α q^{N(α)}`

Para a ponte P1 (modularidade de `y² = x³ − x`) a função `L` da curva é a de um caráter de Hecke
de `ℚ(i)`: `aₙ = Σ_{α primário, N(α) = n} α`, onde `α` é **primário** se `α ≡ 1 (mod 2 + 2i)`,
isto é, `im α` par e `re α + im α ≡ 1 (mod 4)`. Este arquivo prova, sobre `GaussianInt` da Mathlib:

* `prim_mul`, `prim_unidade`, `existe_prim`, `prim_assoc`: os primários formam um monoide; todo
  `α` de norma ímpar tem exatamente um associado primário;
* `somaPrim_mul`: `n ↦ Σ_{α primário, N α = n} α` é multiplicativa (fatoração única em `ℤ[i]`);
* `somaPrim_dois`, `somaPrim_tres`, `somaPrim_um`: os valores em potências de primos — `0` em
  `2^k` (`k ≥ 1`); `c_k(0, p)` se `p ≡ 3 (mod 4)` (`p` inerte); `c_k(2 re π, p)` se `p = π π̄`
  com `π` primário (`p` decomposto), onde `c_k` é a recursão de Hecke de `PonteCoefCurva32`.
-/

local notation "ℤ[i]" => GaussianInt

namespace ATK.BaseGaussPrimario

open ATK.PonteCoefCurva32 Zsqrtd

/-- **Primário**: `α ≡ 1 (mod 2 + 2i)`, i.e. `im α` par e `re α + im α ≡ 1 (mod 4)`. -/
def Prim (α : ℤ[i]) : Prop := α.im % 2 = 0 ∧ (α.re + α.im) % 4 = 1

instance : DecidablePred Prim := fun α => by unfold Prim; infer_instance

theorem prim_iff (α : ℤ[i]) :
    Prim α ↔ ∃ b k : ℤ, α.im = 2 * b ∧ α.re = 1 - 2 * b + 4 * k := by
  unfold Prim
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨α.im / 2, (α.re + α.im - 1) / 4, by omega, by omega⟩
  · rintro ⟨b, k, h1, h2⟩
    omega

theorem prim_one : Prim 1 := by
  unfold Prim
  simp

theorem prim_mul {α β : ℤ[i]} (hα : Prim α) (hβ : Prim β) : Prim (α * β) := by
  obtain ⟨b, k, hb, ha⟩ := (prim_iff α).mp hα
  obtain ⟨d, l, hd, hc⟩ := (prim_iff β).mp hβ
  refine (prim_iff _).mpr ⟨d + b - 4 * b * d + 4 * k * d + 4 * b * l,
    l + k + 4 * k * l - 2 * b * d, ?_, ?_⟩
  · rw [Zsqrtd.im_mul, ha, hb, hc, hd]; ring
  · rw [Zsqrtd.re_mul, ha, hb, hc, hd]; ring

theorem prim_pow {α : ℤ[i]} (hα : Prim α) (k : ℕ) : Prim (α ^ k) := by
  induction k with
  | zero => simpa using prim_one
  | succ k ih => rw [pow_succ]; exact prim_mul ih hα

theorem prim_star {α : ℤ[i]} (hα : Prim α) : Prim (star α) := by
  obtain ⟨b, k, hb, ha⟩ := (prim_iff α).mp hα
  refine (prim_iff _).mpr ⟨-b, k - b, ?_, ?_⟩
  · rw [Zsqrtd.im_star, hb]; ring
  · rw [Zsqrtd.re_star, ha]; ring

theorem norma (α : ℤ[i]) : α.norm = α.re ^ 2 + α.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

theorem prim_norma_impar {α : ℤ[i]} (hα : Prim α) : α.norm % 2 = 1 := by
  obtain ⟨b, k, hb, ha⟩ := (prim_iff α).mp hα
  rw [norma, ha, hb]
  have : (1 - 2 * b + 4 * k) ^ 2 + (2 * b) ^ 2 =
      1 + 2 * (-2 * b + 4 * k + 2 * b ^ 2 - 8 * b * k + 8 * k ^ 2 + 2 * b ^ 2) := by ring
  rw [this, Int.add_mul_emod_self_left]
  rfl

theorem prim_ne_zero {α : ℤ[i]} (hα : Prim α) : α ≠ 0 := by
  rintro rfl
  have := prim_norma_impar hα
  simp at this

/-- As unidades de `ℤ[i]` são `±1, ±i`. -/
theorem unidade_coord {u : ℤ[i]} (hu : IsUnit u) :
    (u.re = 1 ∧ u.im = 0) ∨ (u.re = -1 ∧ u.im = 0) ∨ (u.re = 0 ∧ u.im = 1) ∨
      (u.re = 0 ∧ u.im = -1) := by
  have h := (Zsqrtd.norm_eq_one_iff' (by norm_num) u).mpr hu
  rw [norma] at h
  have h1 : -1 ≤ u.re ∧ u.re ≤ 1 := by constructor <;> nlinarith [sq_nonneg u.im, sq_nonneg u.re]
  have h2 : -1 ≤ u.im ∧ u.im ≤ 1 := by constructor <;> nlinarith [sq_nonneg u.im, sq_nonneg u.re]
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  generalize u.re = r at *
  generalize u.im = s at *
  interval_cases r <;> interval_cases s <;> simp_all

/-- **Unicidade**: se `α` e `u α` são primários (`u` unidade), então `u = 1`. -/
theorem prim_unidade {α u : ℤ[i]} (hu : IsUnit u) (hα : Prim α) (huα : Prim (u * α)) : u = 1 := by
  obtain ⟨b, k, hb, ha⟩ := (prim_iff α).mp hα
  obtain ⟨h1, h2⟩ := huα
  simp only [Zsqrtd.im_mul, Zsqrtd.re_mul] at h1 h2
  rw [ha, hb] at h1 h2
  rcases unidade_coord hu with ⟨hr, hs⟩ | ⟨hr, hs⟩ | ⟨hr, hs⟩ | ⟨hr, hs⟩
  · exact Zsqrtd.ext (by simp [hr]) (by simp [hs])
  all_goals rw [hr, hs] at h1 h2; omega

theorem isUnit_i : IsUnit (⟨0, 1⟩ : ℤ[i]) :=
  (Zsqrtd.norm_eq_one_iff' (by norm_num) _).mp (by rw [norma]; norm_num)

theorem isUnit_menos_i : IsUnit (⟨0, -1⟩ : ℤ[i]) :=
  (Zsqrtd.norm_eq_one_iff' (by norm_num) _).mp (by rw [norma]; norm_num)

/-- **Existência**: todo `α` de norma ímpar tem um associado primário. -/
theorem existe_prim {α : ℤ[i]} (h : α.norm % 2 = 1) : ∃ u : ℤ[i], IsUnit u ∧ Prim (u * α) := by
  rw [norma] at h
  have hpar : (α.re + α.im) % 2 = 1 := by
    have e1 := Int.even_mul_pred_self α.re
    have e2 := Int.even_mul_pred_self α.im
    rw [Int.even_iff] at e1 e2
    have : α.re ^ 2 + α.im ^ 2 = (α.re * (α.re - 1) + α.im * (α.im - 1)) + (α.re + α.im) := by
      ring
    omega
  unfold Prim
  by_cases hb : α.im % 2 = 0
  · by_cases h4 : (α.re + α.im) % 4 = 1
    · exact ⟨1, isUnit_one, by simp only [one_mul]; exact ⟨hb, h4⟩⟩
    · refine ⟨-1, isUnit_one.neg, ?_⟩
      simp only [neg_mul, one_mul, Zsqrtd.re_neg, Zsqrtd.im_neg]
      omega
  · by_cases h4 : (α.re - α.im) % 4 = 1
    · refine ⟨⟨0, 1⟩, isUnit_i, ?_⟩
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
      omega
    · refine ⟨⟨0, -1⟩, isUnit_menos_i, ?_⟩
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
      omega

/-- Primários associados são iguais. -/
theorem prim_assoc {β γ : ℤ[i]} (hβ : Prim β) (hγ : Prim γ) (h : Associated β γ) : β = γ := by
  obtain ⟨u, rfl⟩ := h
  have := prim_unidade u.isUnit hβ (by rwa [mul_comm] at hγ)
  rw [this, mul_one]

/-- Se `β` e `β γ` são primários e `N γ` é ímpar, `γ` é primário. -/
theorem prim_de_mul {β γ : ℤ[i]} (hβ : Prim β) (hβγ : Prim (β * γ)) (hγ : γ.norm % 2 = 1) :
    Prim γ := by
  obtain ⟨w, hw, hwγ⟩ := existe_prim hγ
  have h1 : Prim (w * (β * γ)) := by
    have := prim_mul hβ hwγ
    rwa [mul_left_comm] at this
  rw [prim_unidade hw hβγ h1, one_mul] at hwγ
  exact hwγ

theorem norma_unidade {u : ℤ[i]} (hu : IsUnit u) : u.norm = 1 :=
  (Zsqrtd.norm_eq_one_iff' (by norm_num) u).mpr hu

theorem norma_nonneg (α : ℤ[i]) : 0 ≤ α.norm := by
  rw [norma]; positivity

/-! ## A soma `Σ_{α primário, N α = n} α` -/

/-- Os primários de norma `n`. -/
def primN (n : ℕ) : Finset ℤ[i] :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).image
    (fun p : ℤ × ℤ => (⟨p.1, p.2⟩ : ℤ[i]))).filter (fun α => Prim α ∧ α.norm = n)

theorem mem_primN {n : ℕ} {α : ℤ[i]} : α ∈ primN n ↔ Prim α ∧ α.norm = n := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨hp, hn⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(α.re, α.im), ?_, rfl⟩, hp, hn⟩
    rw [norma] at hn
    have h1 := Int.le_self_sq α.re
    have h2 := Int.le_self_sq (-α.re)
    have h3 := Int.le_self_sq α.im
    have h4 := Int.le_self_sq (-α.im)
    simp only [neg_sq] at h2 h4
    simp only [Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [sq_nonneg α.re, sq_nonneg α.im]

/-- `Σ_{α primário, N α = n} α`. -/
def somaPrim (n : ℕ) : ℤ[i] := ∑ α ∈ primN n, α

theorem primN_zero : primN 0 = ∅ := by
  ext α
  simp only [mem_primN, Finset.notMem_empty, iff_false, not_and]
  intro hα h0
  have := prim_norma_impar hα
  rw [h0] at this
  simp at this

theorem primN_um : primN 1 = {1} := by
  ext α
  rw [mem_primN, Finset.mem_singleton]
  constructor
  · rintro ⟨hα, h1⟩
    have hu : IsUnit α := (Zsqrtd.norm_eq_one_iff' (by norm_num) α).mp (by exact_mod_cast h1)
    have := prim_unidade (α := 1) hu prim_one (by rwa [mul_one])
    exact this
  · rintro rfl
    exact ⟨prim_one, by simp⟩

theorem somaPrim_zero : somaPrim 0 = 0 := by simp [somaPrim, primN_zero]

theorem somaPrim_um : somaPrim 1 = 1 := by simp [somaPrim, primN_um]

/-- Normas coprimas ⇒ elementos coprimos em `ℤ[i]`. -/
theorem coprimo_de_normas {β γ : ℤ[i]} {m n : ℕ} (hmn : m.Coprime n) (hβ : β.norm = m)
    (hγ : γ.norm = n) : IsCoprime β γ := by
  obtain ⟨x, y, hxy⟩ := Nat.isCoprime_iff_coprime.mpr hmn
  refine ⟨(x : ℤ[i]) * star β, (y : ℤ[i]) * star γ, ?_⟩
  have e1 : ((β.norm : ℤ) : ℤ[i]) = β * star β := Zsqrtd.norm_eq_mul_conj β
  have e2 : ((γ.norm : ℤ) : ℤ[i]) = γ * star γ := Zsqrtd.norm_eq_mul_conj γ
  rw [hβ] at e1
  rw [hγ] at e2
  have : ((x * m + y * n : ℤ) : ℤ[i]) = 1 := by rw [hxy]; simp
  push_cast at this
  calc (x : ℤ[i]) * star β * β + (y : ℤ[i]) * star γ * γ
      = (x : ℤ[i]) * (β * star β) + (y : ℤ[i]) * (γ * star γ) := by ring
    _ = 1 := by rw [← e1, ← e2]; push_cast; exact this

theorem norma_dvd {β δ : ℤ[i]} (h : β ∣ δ) : β.norm ∣ δ.norm := by
  obtain ⟨c, rfl⟩ := h
  rw [Zsqrtd.norm_mul]
  exact dvd_mul_right _ _

/-- **Multiplicatividade**: `Σ_{N α = mn} α = (Σ_{N β = m} β)(Σ_{N γ = n} γ)` para `m ⊥ n`. -/
theorem somaPrim_mul {m n : ℕ} (hmn : m.Coprime n) :
    somaPrim (m * n) = somaPrim m * somaPrim n := by
  rw [somaPrim, somaPrim, somaPrim, Finset.sum_mul_sum, ← Finset.sum_product']
  symm
  refine Finset.sum_bij (fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_
  · rintro ⟨β, γ⟩ hp
    rw [Finset.mem_product, mem_primN, mem_primN] at hp
    rw [mem_primN]
    refine ⟨prim_mul hp.1.1 hp.2.1, ?_⟩
    rw [Zsqrtd.norm_mul, hp.1.2, hp.2.2]
    push_cast; ring
  · rintro ⟨β, γ⟩ hp ⟨β', γ'⟩ hp' heq
    rw [Finset.mem_product, mem_primN, mem_primN] at hp hp'
    simp only at heq
    have c1 := coprimo_de_normas hmn hp.1.2 hp'.2.2
    have c2 := coprimo_de_normas hmn hp'.1.2 hp.2.2
    have d1 : β ∣ β' := c1.dvd_of_dvd_mul_right ⟨γ, by rw [← heq]⟩
    have d2 : β' ∣ β := c2.dvd_of_dvd_mul_right ⟨γ', by rw [heq]⟩
    have hb : β = β' := prim_assoc hp.1.1 hp'.1.1 (associated_of_dvd_dvd d1 d2)
    subst hb
    have hg : γ = γ' := mul_left_cancel₀ (prim_ne_zero hp.1.1) heq
    rw [hg]
  · intro α hα
    rw [mem_primN] at hα
    obtain ⟨hpα, hnα⟩ := hα
    have himp := prim_norma_impar hpα
    rw [hnα] at himp
    have hm0 : (m : ℤ) % 2 = 1 := by
      have : ((m : ℤ) * n) % 2 = 1 := by exact_mod_cast himp
      rcases Int.emod_two_eq_zero_or_one (m : ℤ) with h | h
      · rw [Int.mul_emod, h] at this; simp at this
      · exact h
    have hn0 : (n : ℤ) % 2 = 1 := by
      have : ((m : ℤ) * n) % 2 = 1 := by exact_mod_cast himp
      rcases Int.emod_two_eq_zero_or_one (n : ℤ) with h | h
      · rw [Int.mul_emod, h] at this; simp at this
      · exact h
    -- α ∣ m n
    have hdiv : α ∣ (m : ℤ[i]) * n := by
      refine ⟨star α, ?_⟩
      rw [← Zsqrtd.norm_eq_mul_conj, hnα]
      push_cast; ring
    obtain ⟨β₁, β₂, h1, h2, hα⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
    have hN : β₁.norm * β₂.norm = m * n := by
      rw [← Zsqrtd.norm_mul, ← hα, hnα]; push_cast; ring
    have hcop : IsCoprime (m : ℤ) n := Nat.isCoprime_iff_coprime.mpr hmn
    have d1 : β₁.norm ∣ (m : ℤ) := by
      have hd := norma_dvd h1
      rw [Zsqrtd.norm_natCast] at hd
      have hc : IsCoprime β₁.norm n := (hcop.mul_left hcop).of_isCoprime_of_dvd_left hd
      exact hc.dvd_of_dvd_mul_right ⟨β₂.norm, by rw [hN]⟩
    have d2 : β₂.norm ∣ (n : ℤ) := by
      have hd := norma_dvd h2
      rw [Zsqrtd.norm_natCast] at hd
      have hc : IsCoprime β₂.norm m := (hcop.symm.mul_left hcop.symm).of_isCoprime_of_dvd_left hd
      exact hc.dvd_of_dvd_mul_right ⟨β₁.norm, by linear_combination (-1 : ℤ) * hN⟩
    have hmpos : (0 : ℤ) < m := by omega
    have hnpos : (0 : ℤ) < n := by omega
    have p1 : 0 < β₁.norm := by
      rcases (norma_nonneg β₁).lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at hN; nlinarith
    have p2 : 0 < β₂.norm := by
      rcases (norma_nonneg β₂).lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hN; nlinarith
    have l1 := Int.le_of_dvd hmpos d1
    have l2 := Int.le_of_dvd hnpos d2
    have e1 : β₁.norm = m := by nlinarith
    have e2 : β₂.norm = n := by
      rw [e1] at hN
      exact mul_left_cancel₀ hmpos.ne' hN
    obtain ⟨u, hu, hpu⟩ := existe_prim (α := β₁) (by rw [e1]; exact hm0)
    obtain ⟨U, rfl⟩ := hu
    have hγ : Prim ((↑U⁻¹ : ℤ[i]) * β₂) := by
      apply prim_de_mul hpu
      · have : (U : ℤ[i]) * β₁ * ((↑U⁻¹ : ℤ[i]) * β₂) = α := by
          rw [hα, mul_mul_mul_comm, Units.mul_inv, one_mul]
        rw [this]; exact hpα
      · rw [Zsqrtd.norm_mul, norma_unidade (Units.isUnit _), one_mul, e2]; exact hn0
    refine ⟨((U : ℤ[i]) * β₁, (↑U⁻¹ : ℤ[i]) * β₂), ?_, ?_⟩
    · rw [Finset.mem_product, mem_primN, mem_primN]
      refine ⟨⟨hpu, ?_⟩, hγ, ?_⟩
      · rw [Zsqrtd.norm_mul, norma_unidade (Units.isUnit _), one_mul, e1]
      · rw [Zsqrtd.norm_mul, norma_unidade (Units.isUnit _), one_mul, e2]
    · simp only
      rw [hα, mul_mul_mul_comm, Units.mul_inv, one_mul]
  · intro p _
    rfl

/-! ## Potências de primos -/

theorem norma_pow (α : ℤ[i]) (j : ℕ) : (α ^ j).norm = α.norm ^ j := by
  induction j with
  | zero => simp [Zsqrtd.norm_one]
  | succ j ih => rw [pow_succ, Zsqrtd.norm_mul, ih, pow_succ]

theorem norma_assoc {α β : ℤ[i]} (h : Associated α β) : α.norm = β.norm := by
  obtain ⟨u, rfl⟩ := h
  rw [Zsqrtd.norm_mul, norma_unidade u.isUnit, mul_one]

theorem norma_natCast (p : ℕ) : ((p : ℤ[i])).norm = (p : ℤ) ^ 2 := by
  rw [Zsqrtd.norm_natCast]; ring

/-- Em `2^k` (`k ≥ 1`) não há primários: a norma de um primário é ímpar. -/
theorem somaPrim_dois {k : ℕ} (hk : 1 ≤ k) : somaPrim (2 ^ k) = 0 := by
  have : primN (2 ^ k) = ∅ := by
    ext α
    simp only [mem_primN, Finset.notMem_empty, iff_false, not_and]
    intro hα hn
    have h := prim_norma_impar hα
    rw [hn] at h
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    push_cast at h
    rw [pow_succ] at h
    simp at h
  rw [somaPrim, this, Finset.sum_empty]

theorem hecke_zero_par (p : ℤ) (j : ℕ) : hecke 0 p (2 * j) = (-p) ^ j := by
  induction j with
  | zero => norm_num [hecke]
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 2 by ring, hecke, ih]
    ring

theorem hecke_zero_impar (p : ℤ) (j : ℕ) : hecke 0 p (2 * j + 1) = 0 := by
  induction j with
  | zero => norm_num [hecke]
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, hecke, ih]
    ring

theorem prim_menos_p {p : ℕ} (hp : p % 4 = 3) : Prim (-(p : ℤ[i])) := by
  unfold Prim
  simp only [Zsqrtd.re_neg, Zsqrtd.im_neg, Zsqrtd.re_natCast, Zsqrtd.im_natCast]
  omega

/-- **Primo inerte** (`p ≡ 3 mod 4`): os primários de norma `p^k` são `(−p)^{k/2}` (`k` par). -/
theorem somaPrim_tres (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) (k : ℕ) :
    somaPrim (p ^ k) = ((hecke 0 p k : ℤ) : ℤ[i]) := by
  have hpr : Prime (p : ℤ[i]) := GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p hp
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have key : ∀ α ∈ primN (p ^ k), ∃ j, k = 2 * j ∧ α = (-(p : ℤ[i])) ^ j := by
    intro α hα
    rw [mem_primN] at hα
    have hdiv : α ∣ (p : ℤ[i]) ^ k := by
      refine ⟨star α, ?_⟩
      rw [← Zsqrtd.norm_eq_mul_conj, hα.2]
      push_cast; ring
    obtain ⟨j, -, hj⟩ := (dvd_prime_pow hpr k).mp hdiv
    have hn := norma_assoc hj
    rw [hα.2, norma_pow, norma_natCast] at hn
    have hk : k = 2 * j := by
      have : ((p ^ k : ℕ) : ℤ) = ((p ^ (2 * j) : ℕ) : ℤ) := by
        push_cast at hn ⊢; rw [hn, ← pow_mul]
      exact Nat.pow_right_injective hp2 (by exact_mod_cast this)
    refine ⟨j, hk, prim_assoc hα.1 (prim_pow (prim_menos_p hp) j) ?_⟩
    refine hj.trans ⟨(-1) ^ j, ?_⟩
    rw [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← mul_pow, mul_neg_one]
  have mem : ∀ j, (-(p : ℤ[i])) ^ j ∈ primN (p ^ (2 * j)) := by
    intro j
    rw [mem_primN]
    refine ⟨prim_pow (prim_menos_p hp) j, ?_⟩
    rw [norma_pow, Zsqrtd.norm_neg, norma_natCast]
    push_cast; ring
  rcases Nat.even_or_odd' k with ⟨j, rfl | rfl⟩
  · have hs : primN (p ^ (2 * j)) = {(-(p : ℤ[i])) ^ j} := by
      ext α
      rw [Finset.mem_singleton]
      constructor
      · intro hα
        obtain ⟨j', hk, he⟩ := key α hα
        obtain rfl : j' = j := by omega
        exact he
      · rintro rfl
        exact mem j
    rw [somaPrim, hs, Finset.sum_singleton, hecke_zero_par]
    push_cast; ring
  · have hs : primN (p ^ (2 * j + 1)) = ∅ := by
      ext α
      simp only [Finset.notMem_empty, iff_false]
      intro hα
      obtain ⟨j', hk, -⟩ := key α hα
      omega
    rw [somaPrim, hs, Finset.sum_empty, hecke_zero_impar]
    simp

/-- Norma prima ⇒ irredutível. -/
theorem irred_de_norma {π : ℤ[i]} {p : ℕ} (hp : p.Prime) (hn : π.norm = p) : Irreducible π := by
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · rw [norma_unidade hu] at hn
    have : p = 1 := by exact_mod_cast hn.symm
    exact hp.one_lt.ne' this
  · have hN : a.norm * b.norm = p := by rw [← Zsqrtd.norm_mul, ← hab, hn]
    have ha := norma_nonneg a
    have hb := norma_nonneg b
    have hd : a.norm.toNat ∣ p := ⟨b.norm.toNat, by
      have : ((a.norm.toNat * b.norm.toNat : ℕ) : ℤ) = p := by
        push_cast; rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb, hN]
      exact_mod_cast this.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hd with h | h
    · left
      apply (Zsqrtd.norm_eq_one_iff' (by norm_num) a).mp
      rw [← Int.toNat_of_nonneg ha, h]; rfl
    · right
      apply (Zsqrtd.norm_eq_one_iff' (by norm_num) b).mp
      rw [← Int.toNat_of_nonneg ha, h] at hN
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have := mul_left_cancel₀ hp0 (hN.trans (mul_one _).symm)
      exact this

/-- Soma "geométrica" `s_k = Σ_{j ≤ k} π^j π̄^{k−j}`. -/
def somaGeo (π ρ : ℤ[i]) (k : ℕ) : ℤ[i] := ∑ j ∈ Finset.range (k + 1), π ^ j * ρ ^ (k - j)

theorem somaGeo_succ (π ρ : ℤ[i]) (k : ℕ) :
    somaGeo π ρ (k + 1) = π ^ (k + 1) + ρ * somaGeo π ρ k := by
  rw [somaGeo, Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, add_comm, somaGeo,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [show k + 1 - j = (k - j) + 1 by omega, pow_succ]
  ring

theorem somaGeo_hecke (π ρ : ℤ[i]) (a q : ℤ) (ha : π + ρ = a) (hq : π * ρ = q) (k : ℕ) :
    somaGeo π ρ k = ((hecke a q k : ℤ) : ℤ[i]) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [somaGeo, hecke]
    | 1 =>
      simp only [somaGeo, Finset.sum_range_succ, Finset.sum_range_zero, hecke]
      rw [← ha]; ring
    | k + 2 =>
      rw [hecke]
      push_cast
      rw [← ih (k + 1) (by omega), ← ih k (by omega), ← ha, ← hq, somaGeo_succ, somaGeo_succ]
      ring

/-- **Primo decomposto** (`p = π π̄`, `π` primário): `Σ_{N α = p^k} α = c_k(2 re π, p)`. -/
theorem somaPrim_decomp {p : ℕ} (hp : p.Prime) {π : ℤ[i]} (hπ : Prim π) (hn : π.norm = p)
    (k : ℕ) : somaPrim (p ^ k) = ((hecke (2 * π.re) p k : ℤ) : ℤ[i]) := by
  set ρ := star π with hρ
  have hρp : Prim ρ := prim_star hπ
  have hρn : ρ.norm = p := by rw [hρ, Zsqrtd.norm_conj, hn]
  have iπ := irred_de_norma hp hn
  have iρ := irred_de_norma hp hρn
  have pπ := iπ.prime
  have pρ := iρ.prime
  have hpp : (p : ℤ[i]) = π * ρ := by
    rw [hρ, ← Zsqrtd.norm_eq_mul_conj, hn]; push_cast; rfl
  have hp2 : 2 ≤ p := hp.two_le
  have hne : ¬ Associated π ρ := by
    intro h
    have he := prim_assoc hπ hρp h
    have him : π.im = 0 := by
      have := congrArg Zsqrtd.im he
      rw [hρ, Zsqrtd.im_star] at this
      omega
    rw [norma, him] at hn
    have hsq : (π.re.natAbs) * (π.re.natAbs) = p := by
      have : ((π.re.natAbs * π.re.natAbs : ℕ) : ℤ) = p := by
        push_cast; rw [abs_mul_abs_self, ← hn]; ring
      exact_mod_cast this
    have hd : π.re.natAbs ∣ p := ⟨π.re.natAbs, hsq.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hd with h | h
    · rw [h] at hsq; exact hp.one_lt.ne' hsq.symm
    · rw [h] at hsq
      have : p * p = p * 1 := by rw [hsq, mul_one]
      have := Nat.eq_of_mul_eq_mul_left hp.pos this
      exact hp.one_lt.ne' this
  have key : ∀ α ∈ primN (p ^ k), ∃ j ∈ Finset.range (k + 1), α = π ^ j * ρ ^ (k - j) := by
    intro α hα
    rw [mem_primN] at hα
    have hdiv : α ∣ π ^ k * ρ ^ k := by
      refine ⟨star α, ?_⟩
      rw [← mul_pow, ← hpp, ← Zsqrtd.norm_eq_mul_conj, hα.2]
      push_cast; rfl
    obtain ⟨α₁, α₂, h1, h2, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
    obtain ⟨j, hj, a1⟩ := (dvd_prime_pow pπ k).mp h1
    obtain ⟨l, hl, a2⟩ := (dvd_prime_pow pρ k).mp h2
    have a12 := a1.mul_mul a2
    have hN := norma_assoc a12
    rw [hα.2, Zsqrtd.norm_mul, norma_pow, norma_pow, hn, hρn, ← pow_add] at hN
    have hjl : k = j + l := by
      have : ((p ^ k : ℕ) : ℤ) = ((p ^ (j + l) : ℕ) : ℤ) := by push_cast; exact hN
      exact Nat.pow_right_injective hp2 (by exact_mod_cast this)
    refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
    rw [show k - j = l by omega]
    exact prim_assoc hα.1 (prim_mul (prim_pow hπ j) (prim_pow hρp l)) a12
  have mem : ∀ j ∈ Finset.range (k + 1), π ^ j * ρ ^ (k - j) ∈ primN (p ^ k) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [mem_primN]
    refine ⟨prim_mul (prim_pow hπ j) (prim_pow hρp (k - j)), ?_⟩
    rw [Zsqrtd.norm_mul, norma_pow, norma_pow, hn, hρn, ← pow_add, show j + (k - j) = k by omega]
    push_cast; rfl
  have hπ0 : π ≠ 0 := prim_ne_zero hπ
  have hρ0 : ρ ≠ 0 := prim_ne_zero hρp
  have inj : Set.InjOn (fun j => π ^ j * ρ ^ (k - j)) (Finset.range (k + 1) : Set ℕ) := by
    intro j hj j' hj' he
    simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
    simp only at he
    by_contra hjj
    -- wlog j < j'
    have aux : ∀ a b, a < b → b < k + 1 → π ^ a * ρ ^ (k - a) = π ^ b * ρ ^ (k - b) → False := by
      intro a b hab hb hab'
      obtain ⟨d, rfl⟩ : ∃ d, b = a + (d + 1) := ⟨b - a - 1, by omega⟩
      have e1 : π ^ a * ρ ^ (k - a) = (π ^ a * ρ ^ (k - (a + (d + 1)))) * ρ ^ (d + 1) := by
        rw [mul_assoc, ← pow_add, show k - (a + (d + 1)) + (d + 1) = k - a by omega]
      have e2 : π ^ (a + (d + 1)) * ρ ^ (k - (a + (d + 1))) =
          (π ^ a * ρ ^ (k - (a + (d + 1)))) * π ^ (d + 1) := by
        rw [pow_add]; ring
      rw [e1, e2] at hab'
      have hc := mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ hπ0) (pow_ne_zero _ hρ0)) hab'
      have hdv : π ∣ ρ ^ (d + 1) := by rw [hc]; exact dvd_pow_self π (by omega)
      exact hne (iπ.associated_of_dvd iρ (pπ.dvd_of_dvd_pow hdv))
    rcases lt_or_gt_of_ne hjj with h | h
    · exact aux j j' h hj' he
    · exact aux j' j h hj he.symm
  have hset : primN (p ^ k) = (Finset.range (k + 1)).image (fun j => π ^ j * ρ ^ (k - j)) := by
    ext α
    rw [Finset.mem_image]
    constructor
    · intro hα
      obtain ⟨j, hj, rfl⟩ := key α hα
      exact ⟨j, hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact mem j hj
  rw [somaPrim, hset, Finset.sum_image inj]
  apply somaGeo_hecke
  · rw [hρ]
    apply Zsqrtd.ext
    · simp [Zsqrtd.re_star, Zsqrtd.re_intCast]; ring
    · simp [Zsqrtd.im_star, Zsqrtd.im_intCast]
  · rw [← hpp]; push_cast; rfl

end ATK.BaseGaussPrimario

#print axioms ATK.BaseGaussPrimario.prim_iff
#print axioms ATK.BaseGaussPrimario.prim_one
#print axioms ATK.BaseGaussPrimario.prim_mul
#print axioms ATK.BaseGaussPrimario.prim_pow
#print axioms ATK.BaseGaussPrimario.prim_star
#print axioms ATK.BaseGaussPrimario.norma
#print axioms ATK.BaseGaussPrimario.prim_norma_impar
#print axioms ATK.BaseGaussPrimario.prim_ne_zero
#print axioms ATK.BaseGaussPrimario.unidade_coord
#print axioms ATK.BaseGaussPrimario.prim_unidade
#print axioms ATK.BaseGaussPrimario.isUnit_i
#print axioms ATK.BaseGaussPrimario.isUnit_menos_i
#print axioms ATK.BaseGaussPrimario.existe_prim
#print axioms ATK.BaseGaussPrimario.prim_assoc
#print axioms ATK.BaseGaussPrimario.prim_de_mul
#print axioms ATK.BaseGaussPrimario.norma_unidade
#print axioms ATK.BaseGaussPrimario.norma_nonneg
#print axioms ATK.BaseGaussPrimario.mem_primN
#print axioms ATK.BaseGaussPrimario.primN_zero
#print axioms ATK.BaseGaussPrimario.primN_um
#print axioms ATK.BaseGaussPrimario.somaPrim_zero
#print axioms ATK.BaseGaussPrimario.somaPrim_um
#print axioms ATK.BaseGaussPrimario.coprimo_de_normas
#print axioms ATK.BaseGaussPrimario.norma_dvd
#print axioms ATK.BaseGaussPrimario.somaPrim_mul
#print axioms ATK.BaseGaussPrimario.norma_pow
#print axioms ATK.BaseGaussPrimario.norma_assoc
#print axioms ATK.BaseGaussPrimario.norma_natCast
#print axioms ATK.BaseGaussPrimario.somaPrim_dois
#print axioms ATK.BaseGaussPrimario.hecke_zero_par
#print axioms ATK.BaseGaussPrimario.hecke_zero_impar
#print axioms ATK.BaseGaussPrimario.prim_menos_p
#print axioms ATK.BaseGaussPrimario.somaPrim_tres
#print axioms ATK.BaseGaussPrimario.irred_de_norma
#print axioms ATK.BaseGaussPrimario.somaGeo_succ
#print axioms ATK.BaseGaussPrimario.somaGeo_hecke
#print axioms ATK.BaseGaussPrimario.somaPrim_decomp
