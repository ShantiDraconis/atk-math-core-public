import ATK.ZeroClasses.PiUnilateral

/-!
# `Θ` é o expoente exato de `ψ(x) − x`, `θ(x) − x`, `π(x) − Li(x)` e `M(x)`, de cada lado (rodada 98)

Para `E : ℕ → ℝ`, `Expoentes E = {θ : E(N) ≤ N^θ para todo N grande}`. Então

  **`Θ = inf Expoentes E`**

para cada uma das doze funções `E = ψ(N) − N`, `N − ψ(N)`, `|ψ(N) − N|`, e o mesmo com `θ(N)` no lugar de `ψ(N)`,
com `π(N) − Li(N)` e com `M(N)` (`Teta_eq_psi_cima`, …, `Teta_eq_mertens`). Isto é, `Θ = sup Re ρ` é o expoente de
crescimento de cada uma, e **de cada lado separadamente**.

* `eq_sInf_of`: se todo `θ > c` está em `S` e todo elemento de `S` é `≥ c`, então `c = inf S`.
* `ev_pot`: `A(N + 1)^b + K ≤ N^θ` para `N` grande, se `0 ≤ b < θ`; com isso as cotas de um lado das rodadas 87 e 97
  (`Teta_le_iff_psi_le`, …, `Teta_le_iff_pi_ge`) e as cotas triviais (`ψ(N) ≤ (log 4 + 4)N`, `π(N) ≤ N + 1`,
  `Li(N) ≤ 2N`, `|M(N)| ≤ N + 1`) põem todo `θ > Θ` em `Expoentes E` (`mem_of_Teta`).
* `freq_of_omega`: uma família `Ω₊` com `K` livre dá `E(N) > N^θ` infinitas vezes (o truque de `K` = soma dos
  `|E(n)|` iniciais). Para `ψ`, `M` e os lados de baixo de `θ − N` e `π − Li`, isso vale em `0 ≤ θ < Θ` (Landau, rodadas
  87 e 96). Para os lados de cima de `θ(x) − x` e `π(x) − Li(x)`, Landau só cobre `½ ≤ θ < Θ` (o viés `O(√x)`), e
  `θ < ½` vem de Littlewood (rodadas 93 e 96; `freq_meio`).

Classificação: **reformulação** (`Θ` como expoente exato; clássico). RH continua OPEN_MATH.
-/

open Filter
open scoped Real

namespace ATK.ZeroClasses.TetaExpoente

open ATK.ZeroClasses.BDTheta (Teta meio_le_Teta Teta_le_um rh_iff_Teta)
open ATK.ZeroClasses.Mertens (M)
open ATK.ZeroClasses.PiLi (Li intervalIntegrable_inv_log)
open ATK.ZeroClasses.LittlewoodPiIncond (aPi aPi_bounds aPi_pequeno sqrt_le_rpow semZeros_of_aPi_ge
  um_le_log_eee tres_le_eee)
open ATK.ZeroClasses.LittlewoodTeta (lll_ge)

/-! ## 1. O conjunto dos expoentes e o ínfimo -/

/-- Os expoentes `θ` com `E(N) ≤ N^θ` para todo `N` grande. -/
def Expoentes (E : ℕ → ℝ) : Set ℝ := {θ | ∀ᶠ N : ℕ in atTop, E N ≤ (N : ℝ) ^ θ}

theorem eq_sInf_of {S : Set ℝ} {c : ℝ} (hmem : ∀ θ, c < θ → θ ∈ S) (hlow : ∀ θ ∈ S, c ≤ θ) : c = sInf S :=
  le_antisymm (le_csInf ⟨c + 1, hmem _ (by linarith)⟩ hlow)
    (le_of_forall_gt_imp_ge_of_dense fun θ hθ => csInf_le ⟨c, hlow⟩ (hmem θ hθ))

/-- `A(N + 1)^b + K ≤ N^θ` para `N` grande, se `0 ≤ b < θ`. -/
theorem ev_pot {A K b θ : ℝ} (hb : 0 ≤ b) (hbθ : b < θ) :
    ∀ᶠ N : ℕ in atTop, A * ((N : ℝ) + 1) ^ b + K ≤ (N : ℝ) ^ θ := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (θ - b)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually_ge_atTop (|A| * 2 ^ b + |K|), eventually_ge_atTop 1] with N hN hN1
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have h0 : (0 : ℝ) < N := by linarith
  have hNb : 1 ≤ (N : ℝ) ^ b := Real.one_le_rpow hN1' hb
  have h2 : ((N : ℝ) + 1) ^ b ≤ 2 ^ b * (N : ℝ) ^ b := by
    rw [← Real.mul_rpow (by norm_num) h0.le]
    exact Real.rpow_le_rpow (by linarith) (by linarith) hb
  have hsplit : (N : ℝ) ^ θ = (N : ℝ) ^ (θ - b) * (N : ℝ) ^ b := by
    rw [← Real.rpow_add h0]
    ring_nf
  have hA : A * ((N : ℝ) + 1) ^ b ≤ |A| * (2 ^ b * (N : ℝ) ^ b) :=
    (mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg A))
  have hK : K ≤ |K| * (N : ℝ) ^ b := (le_abs_self K).trans (le_mul_of_one_le_right (abs_nonneg K) hNb)
  have h3 : (|A| * 2 ^ b + |K|) * (N : ℝ) ^ b ≤ (N : ℝ) ^ (θ - b) * (N : ℝ) ^ b :=
    mul_le_mul_of_nonneg_right hN (by positivity)
  have e : (|A| * 2 ^ b + |K|) * (N : ℝ) ^ b = |A| * (2 ^ b * (N : ℝ) ^ b) + |K| * (N : ℝ) ^ b := by ring
  rw [hsplit]
  linarith

theorem mem_of_cota {E : ℕ → ℝ} {θ b A K : ℝ} (hb : 0 ≤ b) (hbθ : b < θ)
    (h : ∀ᶠ N : ℕ in atTop, E N ≤ A * ((N : ℝ) + 1) ^ b + K) : θ ∈ Expoentes E :=
  (h.and (ev_pot hb hbθ)).mono fun _ hN => hN.1.trans hN.2

/-- Cotas `A(N + 1)^{t+ε} + K` para `Θ ≤ t < 1` e uma cota linear põem todo `θ > Θ` em `Expoentes E`. -/
theorem mem_of_Teta {E : ℕ → ℝ}
    (hT : ∀ t : ℝ, 1 / 2 ≤ t → t < 1 → Teta ≤ t → ∀ ε : ℝ, 0 < ε →
      ∃ A K : ℝ, ∀ᶠ N : ℕ in atTop, E N ≤ A * ((N : ℝ) + 1) ^ (t + ε) + K)
    (h1 : ∃ A K : ℝ, ∀ᶠ N : ℕ in atTop, E N ≤ A * ((N : ℝ) + 1) ^ (1 : ℝ) + K) :
    ∀ θ : ℝ, Teta < θ → θ ∈ Expoentes E := by
  intro θ hθ
  rcases lt_or_ge 1 θ with h | h
  · obtain ⟨A, K, hAK⟩ := h1
    exact mem_of_cota zero_le_one h hAK
  · have hm := meio_le_Teta
    obtain ⟨A, K, hAK⟩ := hT ((Teta + θ) / 2) (by linarith) (by linarith) (by linarith)
      ((θ - (Teta + θ) / 2) / 2) (by linarith)
    exact mem_of_cota (by linarith) (by linarith) hAK

theorem low_of_freq {E : ℕ → ℝ} (h : ∀ θ : ℝ, θ < Teta → ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < E N) :
    ∀ θ ∈ Expoentes E, Teta ≤ θ := by
  intro θ hθ
  by_contra hlt
  push Not at hlt
  obtain ⟨N, h1, h2⟩ := ((h θ hlt).and_eventually hθ).exists
  linarith

/-- **O truque de `K`**: se `E(N) > (N + 1)^{θ'} + K` para algum `N`, qualquer que seja `K`, então
`E(N) > N^θ` infinitas vezes, para todo `θ ≤ θ'`. -/
theorem freq_of_omega {E : ℕ → ℝ} {θ' : ℝ} (hθ' : 0 ≤ θ')
    (h : ∀ K : ℝ, ∃ N : ℕ, ((N : ℝ) + 1) ^ θ' + K < E N) {θ : ℝ} (hθ : θ ≤ θ') :
    ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < E N := by
  rw [frequently_atTop]
  intro X
  set K := ∑ n ∈ Finset.range (X + 1), |E n| with hKdef
  obtain ⟨N, hN⟩ := h K
  have hp : 0 < ((N : ℝ) + 1) ^ θ' := by positivity
  have hNX : X < N := by
    by_contra hle
    push Not at hle
    have : |E N| ≤ K := Finset.single_le_sum (f := fun n => |E n|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
    linarith [le_abs_self (E N)]
  refine ⟨N, hNX.le, ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_of_lt hNX
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc (N : ℝ) ^ θ ≤ (N : ℝ) ^ θ' := Real.rpow_le_rpow_of_exponent_le hN1 hθ
    _ ≤ ((N : ℝ) + 1) ^ θ' := Real.rpow_le_rpow (by linarith) (by linarith) hθ'
    _ < E N := by linarith

/-- Uma família `Ω₊` em todo `0 ≤ θ' < Θ` dá a frequência em todo `θ < Θ`. -/
theorem freq_of_omega0 {E : ℕ → ℝ}
    (h : ∀ θ' : ℝ, 0 ≤ θ' → θ' < Teta → ∀ K : ℝ, ∃ N : ℕ, ((N : ℝ) + 1) ^ θ' + K < E N) :
    ∀ θ : ℝ, θ < Teta → ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < E N := fun θ hθ =>
  freq_of_omega (le_max_right θ 0)
    (h _ (le_max_right _ _) (max_lt hθ (by linarith [meio_le_Teta]))) (le_max_left θ 0)

/-- Uma família `Ω₊` em `½ ≤ θ' < Θ`, mais a frequência abaixo de `½`, dão a frequência em todo `θ < Θ`. -/
theorem freq_of_omega_meio {E : ℕ → ℝ}
    (h : ∀ θ' : ℝ, 1 / 2 ≤ θ' → θ' < Teta → ∀ K : ℝ, ∃ N : ℕ, ((N : ℝ) + 1) ^ θ' + K < E N)
    (hL : ∀ θ : ℝ, θ < 1 / 2 → ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < E N) :
    ∀ θ : ℝ, θ < Teta → ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < E N := by
  intro θ hθ
  rcases lt_or_ge θ (1 / 2) with h1 | h1
  · exact hL θ h1
  · exact freq_of_omega (by linarith) (h θ h1 hθ) le_rfl

theorem freq_mono {E F : ℕ → ℝ} (hEF : ∀ N, E N ≤ F N) {θ : ℝ}
    (h : ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < E N) : ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < F N :=
  h.mono fun N hN => hN.trans_le (hEF N)

/-- **Escala de Littlewood**: se `c√x log log log x/log x ≤ E(⌊x⌋)` para `x` arbitrariamente grande, então
`E(N) > N^θ` infinitas vezes, para todo `θ < ½`. -/
theorem freq_meio {E : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : ∀ X : ℝ, ∃ x : ℝ, X ≤ x ∧ c * √x * Real.log (Real.log (Real.log x)) / Real.log x ≤ E ⌊x⌋₊)
    {θ : ℝ} (hθ : θ < 1 / 2) : ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < E N := by
  set θ' := max θ 0 with hθ'
  set δ := 1 / 2 - θ' with hδdef
  have hθ'0 : 0 ≤ θ' := le_max_right _ _
  have hδ : 0 < δ := by rw [hδdef]; linarith [max_lt hθ (by norm_num : (0 : ℝ) < 1 / 2)]
  have hcδ : 0 < c * δ := mul_pos hc hδ
  rw [frequently_atTop]
  intro X₀
  obtain ⟨x, hx, hE⟩ := h (max ((X₀ : ℝ) + 1) (Real.exp (Real.exp (Real.exp (2 / (c * δ))))))
  have hxe : Real.exp (Real.exp (Real.exp (2 / (c * δ)))) ≤ x := le_trans (le_max_right _ _) hx
  have hl : 2 / (c * δ) ≤ Real.log (Real.log (Real.log x)) := lll_ge hxe
  have hx3 : Real.exp (Real.exp (Real.exp 0)) ≤ x := by
    refine le_trans ?_ hxe
    gcongr
    positivity
  have hlog : 1 ≤ Real.log x := um_le_log_eee hx3
  have hx0 : 0 < x := by linarith [tres_le_eee]
  have hX : (X₀ : ℝ) ≤ x := by linarith [le_max_left ((X₀ : ℝ) + 1) (Real.exp (Real.exp (Real.exp (2 / (c * δ))))) ]
  refine ⟨⌊x⌋₊, Nat.le_floor hX, ?_⟩
  have hN1 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor (by norm_num; linarith [tres_le_eee])
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have h1 : (⌊x⌋₊ : ℝ) ^ θ ≤ (⌊x⌋₊ : ℝ) ^ θ' := Real.rpow_le_rpow_of_exponent_le hN1 (le_max_left _ _)
  have h2 : (⌊x⌋₊ : ℝ) ^ θ' ≤ x ^ θ' := Real.rpow_le_rpow (by linarith) hNx hθ'0
  -- `x^{θ'} < c√x lll x/log x`
  set P := x ^ θ' with hP
  set Q := x ^ δ with hQ
  set L := Real.log x with hL
  set l := Real.log (Real.log (Real.log x)) with hldef
  have hP0 : 0 < P := Real.rpow_pos_of_pos hx0 _
  have hL0 : 0 < L := by linarith
  have hsq : √x = P * Q := by
    rw [hP, hQ, ← Real.rpow_add hx0, hδdef, Real.sqrt_eq_rpow]
    ring_nf
  have hLQ : δ * L ≤ Q := by
    have := Real.log_le_rpow_div hx0.le hδ
    rw [le_div_iff₀ hδ] at this
    linarith
  have hcl : 2 ≤ c * δ * l := by
    rw [div_le_iff₀ hcδ] at hl
    linarith
  have hl0 : 0 ≤ l := le_trans (by positivity) hl
  have h3 : P < c * √x * l / L := by
    rw [lt_div_iff₀ hL0, hsq]
    have hPL : 0 < P * L := mul_pos hP0 hL0
    have hcPl : 0 ≤ c * P * l := by positivity
    calc P * L < 2 * (P * L) := by linarith
      _ ≤ (c * δ * l) * (P * L) := mul_le_mul_of_nonneg_right hcl hPL.le
      _ = c * P * l * (δ * L) := by ring
      _ ≤ c * P * l * Q := mul_le_mul_of_nonneg_left hLQ hcPl
      _ = c * (P * Q) * l := by ring
  linarith

/-- O `Θ` como ínfimo, a partir das duas metades. -/
theorem Teta_eq_of {E : ℕ → ℝ} (hmem : ∀ θ : ℝ, Teta < θ → θ ∈ Expoentes E)
    (hfreq : ∀ θ : ℝ, θ < Teta → ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < E N) : Teta = sInf (Expoentes E) :=
  eq_sInf_of hmem (low_of_freq hfreq)

/-- Os dois lados juntos dão o mesmo `Θ` para `|E|`. -/
theorem Teta_eq_abs {E G : ℕ → ℝ} (hG : ∀ N, G N = -E N) (hmemE : ∀ θ : ℝ, Teta < θ → θ ∈ Expoentes E)
    (hmemG : ∀ θ : ℝ, Teta < θ → θ ∈ Expoentes G)
    (hfreq : ∀ θ : ℝ, θ < Teta → ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < E N) :
    Teta = sInf (Expoentes fun N => |E N|) := by
  refine Teta_eq_of (fun θ hθ => ?_) fun θ hθ => freq_mono (fun N => le_abs_self (E N)) (hfreq θ hθ)
  filter_upwards [hmemE θ hθ, hmemG θ hθ] with N h1 h2
  rw [hG] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

/-! ## 2. Cotas triviais -/

theorem Li_le_Li {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) : Li a ≤ Li b := by
  unfold Li
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_inv_log (a := 2) (b := a) (by norm_num) (by linarith))
    (intervalIntegrable_inv_log (a := a) (b := b) (by linarith) (by linarith))
  have : 0 ≤ ∫ t in a..b, 1 / Real.log t :=
    intervalIntegral.integral_nonneg hab fun t ht => one_div_nonneg.mpr (Real.log_nonneg (by linarith [ht.1]))
  linarith

theorem Li_nonneg {x : ℝ} (hx : 2 ≤ x) : 0 ≤ Li x := by
  have h := Li_le_Li le_rfl hx
  have h2 : Li 2 = 0 := by unfold Li; simp
  linarith

theorem Li_le {x : ℝ} (hx : 2 ≤ x) : Li x ≤ 2 * x := by
  have hl2 : 0.69 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have h := intervalIntegral.integral_mono_on hx (intervalIntegrable_inv_log (by norm_num) (by linarith))
    intervalIntegrable_const (fun t ht => one_div_le_one_div_of_le (by linarith)
      (Real.log_le_log (by norm_num) ht.1) : ∀ t ∈ Set.Icc (2 : ℝ) x, 1 / Real.log t ≤ 1 / Real.log 2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  unfold Li
  have : (x - 2) * (1 / Real.log 2) ≤ 2 * x := by
    rw [mul_one_div, div_le_iff₀ (by linarith)]
    nlinarith
  linarith

theorem pi_le (N : ℕ) : (Nat.primeCounting N : ℝ) ≤ N + 1 := by
  have : Nat.primeCounting N ≤ N + 1 := by
    unfold Nat.primeCounting Nat.primeCounting'
    exact Nat.count_le _
  exact_mod_cast this

theorem abs_M_le (N : ℕ) : |M N| ≤ N + 1 := by
  unfold M
  calc |∑ n ∈ Finset.range (N + 1), (ArithmeticFunction.moebius n : ℝ)|
      ≤ ∑ n ∈ Finset.range (N + 1), |(ArithmeticFunction.moebius n : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range (N + 1), (1 : ℝ) := Finset.sum_le_sum fun n _ => by
        rw [← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = N + 1 := by simp

theorem pot_um (N : ℕ) : ((N : ℝ) + 1) ^ (1 : ℝ) = N + 1 := Real.rpow_one _

/-! ## 3. `ψ(x) − x` -/

theorem mem_psi_cima : ∀ θ : ℝ, Teta < θ → θ ∈ Expoentes fun N => Chebyshev.psi N - N :=
  mem_of_Teta (fun t ht1 ht2 hT ε hε => by
      obtain ⟨A, K, h⟩ := (ATK.ZeroClasses.Unilateral.Teta_le_iff_psi_le ht1 ht2).mp hT ε hε
      exact ⟨A, K, Eventually.of_forall h⟩)
    ⟨Real.log 4 + 4, 0, Eventually.of_forall fun N => by
      have h1 := Chebyshev.psi_le_const_mul_self (N.cast_nonneg (α := ℝ))
      have h2 : 0 ≤ Real.log 4 + 4 := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
      have h3 : (Real.log 4 + 4) * (N : ℝ) ≤ (Real.log 4 + 4) * ((N : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) h2
      rw [pot_um]
      linarith [N.cast_nonneg (α := ℝ)]⟩

theorem mem_psi_baixo : ∀ θ : ℝ, Teta < θ → θ ∈ Expoentes fun N => (N : ℝ) - Chebyshev.psi N :=
  mem_of_Teta (fun t ht1 ht2 hT ε hε => by
      obtain ⟨A, K, h⟩ := (ATK.ZeroClasses.Unilateral.Teta_le_iff_psi_ge ht1 ht2).mp hT ε hε
      exact ⟨A, K, Eventually.of_forall fun N => by linarith [h N]⟩)
    ⟨1, 0, Eventually.of_forall fun N => by
      rw [pot_um]
      linarith [Chebyshev.psi_nonneg (N : ℝ)]⟩

theorem freq_psi_cima : ∀ θ : ℝ, θ < Teta → ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < Chebyshev.psi N - N :=
  freq_of_omega0 fun _ h0 hlt K => by
    obtain ⟨N, hN⟩ := ATK.ZeroClasses.Unilateral.psi_omega_mais h0 hlt 1 K
    exact ⟨N, by linarith⟩

theorem freq_psi_baixo : ∀ θ : ℝ, θ < Teta → ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < (N : ℝ) - Chebyshev.psi N :=
  freq_of_omega0 fun _ h0 hlt K => by
    obtain ⟨N, hN⟩ := ATK.ZeroClasses.Unilateral.psi_omega_menos h0 hlt 1 K
    exact ⟨N, by linarith⟩

/-- **`Θ = inf{θ : ψ(N) − N ≤ N^θ para N grande}`**. -/
theorem Teta_eq_psi_cima : Teta = sInf (Expoentes fun N => Chebyshev.psi N - N) :=
  Teta_eq_of mem_psi_cima freq_psi_cima

/-- **`Θ = inf{θ : N − ψ(N) ≤ N^θ para N grande}`**. -/
theorem Teta_eq_psi_baixo : Teta = sInf (Expoentes fun N => (N : ℝ) - Chebyshev.psi N) :=
  Teta_eq_of mem_psi_baixo freq_psi_baixo

/-- **`Θ = inf{θ : |ψ(N) − N| ≤ N^θ para N grande}`**. -/
theorem Teta_eq_psi : Teta = sInf (Expoentes fun N => |Chebyshev.psi N - N|) :=
  Teta_eq_abs (fun N => by ring) mem_psi_cima mem_psi_baixo freq_psi_cima

/-! ## 4. `θ(x) − x` -/

theorem mem_theta_cima : ∀ θ : ℝ, Teta < θ → θ ∈ Expoentes fun N => Chebyshev.theta N - N := fun θ hθ =>
  (mem_psi_cima θ hθ).mono fun N hN => le_trans (by linarith [Chebyshev.theta_le_psi (N : ℝ)]) hN

theorem mem_theta_baixo : ∀ θ : ℝ, Teta < θ → θ ∈ Expoentes fun N => (N : ℝ) - Chebyshev.theta N := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine mem_of_Teta (fun t ht1 ht2 hT ε hε => ?_) ⟨1, 0, Eventually.of_forall fun N => ?_⟩
  · obtain ⟨A, K, h⟩ := (ATK.ZeroClasses.Unilateral.Teta_le_iff_psi_ge ht1 ht2).mp hT ε hε
    refine ⟨A + max C 0, K, Eventually.of_forall fun N => ?_⟩
    have hs : C * √(N : ℝ) ≤ max C 0 * ((N : ℝ) + 1) ^ (t + ε) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (sqrt_le_rpow (by linarith) N) (le_max_right _ _))
    have e : (A + max C 0) * ((N : ℝ) + 1) ^ (t + ε) =
        A * ((N : ℝ) + 1) ^ (t + ε) + max C 0 * ((N : ℝ) + 1) ^ (t + ε) := by ring
    linarith [h N, hC N]
  · rw [pot_um]
    linarith [Chebyshev.theta_nonneg (N : ℝ)]

theorem freq_theta_baixo : ∀ θ : ℝ, θ < Teta → ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < (N : ℝ) - Chebyshev.theta N :=
  fun θ hθ => freq_mono (fun N => by linarith [Chebyshev.theta_le_psi (N : ℝ)]) (freq_psi_baixo θ hθ)

theorem freq_theta_cima : ∀ θ : ℝ, θ < Teta → ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < Chebyshev.theta N - N := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine freq_of_omega_meio (fun θ' h1 hlt K => ?_) fun θ hθ => ?_
  · obtain ⟨N, hN⟩ := ATK.ZeroClasses.Unilateral.psi_omega_mais (by linarith) hlt (1 + max C 0) K
    refine ⟨N, ?_⟩
    have hs : C * √(N : ℝ) ≤ max C 0 * ((N : ℝ) + 1) ^ θ' :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (sqrt_le_rpow h1 N) (le_max_right _ _))
    have e : (1 + max C 0) * ((N : ℝ) + 1) ^ θ' = ((N : ℝ) + 1) ^ θ' + max C 0 * ((N : ℝ) + 1) ^ θ' := by ring
    linarith [hC N]
  · obtain ⟨c, hc, -, h2⟩ := ATK.ZeroClasses.LittlewoodTeta.theta_littlewood
    refine freq_meio hc (fun X => ?_) hθ
    obtain ⟨x, hx, hθx⟩ := h2 (max X (Real.exp (Real.exp (Real.exp 0))))
    have hxe : Real.exp (Real.exp (Real.exp 0)) ≤ x := le_trans (le_max_right _ _) hx
    have hl := lll_ge hxe
    have hlog := um_le_log_eee hxe
    have hx0 : 0 ≤ x := by linarith [tres_le_eee]
    refine ⟨x, le_trans (le_max_left _ _) hx, ?_⟩
    have hd : c * √x * Real.log (Real.log (Real.log x)) / Real.log x ≤ c * √x * Real.log (Real.log (Real.log x)) :=
      div_le_self (by positivity) hlog
    have hfl : Chebyshev.theta x = Chebyshev.theta ⌊x⌋₊ := Chebyshev.theta_eq_theta_coe_floor x
    have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
    linarith

/-- **`Θ = inf{θ : θ(N) − N ≤ N^θ para N grande}`**. -/
theorem Teta_eq_theta_cima : Teta = sInf (Expoentes fun N => Chebyshev.theta N - N) :=
  Teta_eq_of mem_theta_cima freq_theta_cima

/-- **`Θ = inf{θ : N − θ(N) ≤ N^θ para N grande}`**. -/
theorem Teta_eq_theta_baixo : Teta = sInf (Expoentes fun N => (N : ℝ) - Chebyshev.theta N) :=
  Teta_eq_of mem_theta_baixo freq_theta_baixo

/-- **`Θ = inf{θ : |θ(N) − N| ≤ N^θ para N grande}`**. -/
theorem Teta_eq_theta : Teta = sInf (Expoentes fun N => |Chebyshev.theta N - N|) :=
  Teta_eq_abs (fun N => by ring) mem_theta_cima mem_theta_baixo freq_theta_cima

/-! ## 5. `π(x) − Li(x)` -/

theorem mem_pi_cima : ∀ θ : ℝ, Teta < θ → θ ∈ Expoentes fun N => (Nat.primeCounting N : ℝ) - Li N :=
  mem_of_Teta (fun t ht1 ht2 hT ε hε => by
      obtain ⟨A, K, h⟩ := (ATK.ZeroClasses.PiUnilateral.Teta_le_iff_pi_le ht1 ht2).mp hT ε hε
      refine ⟨max A 0, K, (eventually_ge_atTop 2).mono fun N hN => ?_⟩
      have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have h1 := h N hN2
      rw [Nat.floor_natCast] at h1
      linarith [ATK.ZeroClasses.PiUnilateral.pot_le (A := A) (b := t + ε) (by linarith) N])
    ⟨1, 0, (eventually_ge_atTop 2).mono fun N hN => by
      have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      rw [pot_um]
      linarith [pi_le N, Li_nonneg hN2]⟩

theorem mem_pi_baixo : ∀ θ : ℝ, Teta < θ → θ ∈ Expoentes fun N => Li N - (Nat.primeCounting N : ℝ) :=
  mem_of_Teta (fun t ht1 ht2 hT ε hε => by
      obtain ⟨A, K, h⟩ := (ATK.ZeroClasses.PiUnilateral.Teta_le_iff_pi_ge ht1 ht2).mp hT ε hε
      refine ⟨max A 0, K, (eventually_ge_atTop 2).mono fun N hN => ?_⟩
      have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have h1 := h N hN2
      rw [Nat.floor_natCast] at h1
      linarith [ATK.ZeroClasses.PiUnilateral.pot_le (A := A) (b := t + ε) (by linarith) N])
    ⟨2, 0, (eventually_ge_atTop 2).mono fun N hN => by
      have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      rw [pot_um]
      linarith [Li_le hN2, (Nat.primeCounting N).cast_nonneg (α := ℝ)]⟩

/-- O lado de baixo de `π − Li` vale em todo `0 ≤ θ < Θ`: o viés `Π − π ≥ 0` joga a favor. -/
theorem freq_pi_baixo : ∀ θ : ℝ, θ < Teta → ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < Li N - (Nat.primeCounting N : ℝ) :=
  freq_of_omega0 fun θ' h0 hlt K => by
    by_contra hne
    push Not at hne
    obtain ⟨C, hC0, hC⟩ := aPi_bounds
    have hl2 : 0 < 1 / Real.log 2 := one_div_pos.mpr (Real.log_pos (by norm_num))
    refine ATK.ZeroClasses.Unilateral.nao_semZeros hlt
      (semZeros_of_aPi_ge (A := 1) (K := max K 0 + 1 / Real.log 2 + 6) h0 (hlt.trans_le Teta_le_um) fun N => ?_)
    have hp : 0 ≤ ((N : ℝ) + 1) ^ θ' := by positivity
    have hK := le_max_left K 0
    have hK0 := le_max_right K 0
    rcases lt_or_ge N 2 with h | h
    · linarith [(aPi_pequeno h).1]
    · linarith [(hC N h).2, hne N]

theorem freq_pi_cima : ∀ θ : ℝ, θ < Teta → ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < (Nat.primeCounting N : ℝ) - Li N := by
  refine freq_of_omega_meio (fun θ' h1 hlt K => ?_) fun θ hθ => ?_
  · obtain ⟨N, -, hN⟩ := ATK.ZeroClasses.LittlewoodPiIncond.pi_omega_mais h1 hlt 1 K
    exact ⟨N, by linarith⟩
  · obtain ⟨c, hc, -, h2⟩ := ATK.ZeroClasses.LittlewoodPiIncond.pi_littlewood
    refine freq_meio hc (fun X => ?_) hθ
    obtain ⟨x, hx, hπ⟩ := h2 (max X 3)
    have hx3 : 3 ≤ x := le_trans (le_max_right _ _) hx
    refine ⟨x, le_trans (le_max_left _ _) hx, ?_⟩
    have hN2 : (2 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor (by norm_num; linarith)
    have hLi := Li_le_Li hN2 (Nat.floor_le (by linarith))
    linarith

/-- **`Θ = inf{θ : π(N) − Li(N) ≤ N^θ para N grande}`** — o lado "difícil" (`π > Li`). -/
theorem Teta_eq_pi_cima : Teta = sInf (Expoentes fun N => (Nat.primeCounting N : ℝ) - Li N) :=
  Teta_eq_of mem_pi_cima freq_pi_cima

/-- **`Θ = inf{θ : Li(N) − π(N) ≤ N^θ para N grande}`**. -/
theorem Teta_eq_pi_baixo : Teta = sInf (Expoentes fun N => Li N - (Nat.primeCounting N : ℝ)) :=
  Teta_eq_of mem_pi_baixo freq_pi_baixo

/-- **`Θ = inf{θ : |π(N) − Li(N)| ≤ N^θ para N grande}`**. -/
theorem Teta_eq_pi : Teta = sInf (Expoentes fun N => |(Nat.primeCounting N : ℝ) - Li N|) :=
  Teta_eq_abs (fun N => by ring) mem_pi_cima mem_pi_baixo freq_pi_cima

/-! ## 6. `M(x)` -/

theorem mem_mertens_cima : ∀ θ : ℝ, Teta < θ → θ ∈ Expoentes fun N => M N :=
  mem_of_Teta (fun t ht1 ht2 hT ε hε => by
      obtain ⟨A, K, h⟩ := (ATK.ZeroClasses.Unilateral.Teta_le_iff_mertens_le ht1 ht2).mp hT ε hε
      exact ⟨A, K, Eventually.of_forall h⟩)
    ⟨1, 0, Eventually.of_forall fun N => by
      rw [pot_um]
      linarith [abs_M_le N, le_abs_self (M N)]⟩

theorem mem_mertens_baixo : ∀ θ : ℝ, Teta < θ → θ ∈ Expoentes fun N => -M N :=
  mem_of_Teta (fun t ht1 ht2 hT ε hε => by
      obtain ⟨A, K, h⟩ := (ATK.ZeroClasses.Unilateral.Teta_le_iff_mertens_ge ht1 ht2).mp hT ε hε
      exact ⟨A, K, Eventually.of_forall fun N => by linarith [h N]⟩)
    ⟨1, 0, Eventually.of_forall fun N => by
      rw [pot_um]
      linarith [abs_M_le N, neg_abs_le (M N)]⟩

theorem freq_mertens_cima : ∀ θ : ℝ, θ < Teta → ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < M N :=
  freq_of_omega0 fun _ h0 hlt K => by
    obtain ⟨N, hN⟩ := ATK.ZeroClasses.Unilateral.mertens_omega_mais h0 hlt 1 K
    exact ⟨N, by linarith⟩

theorem freq_mertens_baixo : ∀ θ : ℝ, θ < Teta → ∃ᶠ N : ℕ in atTop, (N : ℝ) ^ θ < -M N :=
  freq_of_omega0 fun _ h0 hlt K => by
    obtain ⟨N, hN⟩ := ATK.ZeroClasses.Unilateral.mertens_omega_menos h0 hlt 1 K
    exact ⟨N, by linarith⟩

/-- **`Θ = inf{θ : M(N) ≤ N^θ para N grande}`**. -/
theorem Teta_eq_mertens_cima : Teta = sInf (Expoentes fun N => M N) :=
  Teta_eq_of mem_mertens_cima freq_mertens_cima

/-- **`Θ = inf{θ : −M(N) ≤ N^θ para N grande}`**. -/
theorem Teta_eq_mertens_baixo : Teta = sInf (Expoentes fun N => -M N) :=
  Teta_eq_of mem_mertens_baixo freq_mertens_baixo

/-- **`Θ = inf{θ : |M(N)| ≤ N^θ para N grande}`**. -/
theorem Teta_eq_mertens : Teta = sInf (Expoentes fun N => |M N|) :=
  Teta_eq_abs (fun _ => rfl) mem_mertens_cima mem_mertens_baixo freq_mertens_cima

/-! ## 7. RH -/

/-- **RH ⟺ o expoente de `π(N) − Li(N)` (só o lado de cima) é `½`**. -/
theorem rh_iff_expoente_pi_cima :
    RiemannHypothesis ↔ sInf (Expoentes fun N => (Nat.primeCounting N : ℝ) - Li N) = 1 / 2 := by
  rw [rh_iff_Teta, Teta_eq_pi_cima]

/-- **RH ⟺ o expoente de `|ψ(N) − N|` é `½`**. -/
theorem rh_iff_expoente_psi : RiemannHypothesis ↔ sInf (Expoentes fun N => |Chebyshev.psi N - N|) = 1 / 2 := by
  rw [rh_iff_Teta, Teta_eq_psi]

/-- **RH ⟺ o expoente de `|M(N)|` é `½`**. -/
theorem rh_iff_expoente_mertens : RiemannHypothesis ↔ sInf (Expoentes fun N => |M N|) = 1 / 2 := by
  rw [rh_iff_Teta, Teta_eq_mertens]

end ATK.ZeroClasses.TetaExpoente

#print axioms ATK.ZeroClasses.TetaExpoente.eq_sInf_of
#print axioms ATK.ZeroClasses.TetaExpoente.ev_pot
#print axioms ATK.ZeroClasses.TetaExpoente.mem_of_cota
#print axioms ATK.ZeroClasses.TetaExpoente.mem_of_Teta
#print axioms ATK.ZeroClasses.TetaExpoente.low_of_freq
#print axioms ATK.ZeroClasses.TetaExpoente.freq_of_omega
#print axioms ATK.ZeroClasses.TetaExpoente.freq_of_omega0
#print axioms ATK.ZeroClasses.TetaExpoente.freq_of_omega_meio
#print axioms ATK.ZeroClasses.TetaExpoente.freq_mono
#print axioms ATK.ZeroClasses.TetaExpoente.freq_meio
#print axioms ATK.ZeroClasses.TetaExpoente.Teta_eq_of
#print axioms ATK.ZeroClasses.TetaExpoente.Teta_eq_abs
#print axioms ATK.ZeroClasses.TetaExpoente.Li_le_Li
#print axioms ATK.ZeroClasses.TetaExpoente.Li_nonneg
#print axioms ATK.ZeroClasses.TetaExpoente.Li_le
#print axioms ATK.ZeroClasses.TetaExpoente.pi_le
#print axioms ATK.ZeroClasses.TetaExpoente.abs_M_le
#print axioms ATK.ZeroClasses.TetaExpoente.pot_um
#print axioms ATK.ZeroClasses.TetaExpoente.mem_psi_cima
#print axioms ATK.ZeroClasses.TetaExpoente.mem_psi_baixo
#print axioms ATK.ZeroClasses.TetaExpoente.freq_psi_cima
#print axioms ATK.ZeroClasses.TetaExpoente.freq_psi_baixo
#print axioms ATK.ZeroClasses.TetaExpoente.Teta_eq_psi_cima
#print axioms ATK.ZeroClasses.TetaExpoente.Teta_eq_psi_baixo
#print axioms ATK.ZeroClasses.TetaExpoente.Teta_eq_psi
#print axioms ATK.ZeroClasses.TetaExpoente.mem_theta_cima
#print axioms ATK.ZeroClasses.TetaExpoente.mem_theta_baixo
#print axioms ATK.ZeroClasses.TetaExpoente.freq_theta_baixo
#print axioms ATK.ZeroClasses.TetaExpoente.freq_theta_cima
#print axioms ATK.ZeroClasses.TetaExpoente.Teta_eq_theta_cima
#print axioms ATK.ZeroClasses.TetaExpoente.Teta_eq_theta_baixo
#print axioms ATK.ZeroClasses.TetaExpoente.Teta_eq_theta
#print axioms ATK.ZeroClasses.TetaExpoente.mem_pi_cima
#print axioms ATK.ZeroClasses.TetaExpoente.mem_pi_baixo
#print axioms ATK.ZeroClasses.TetaExpoente.freq_pi_baixo
#print axioms ATK.ZeroClasses.TetaExpoente.freq_pi_cima
#print axioms ATK.ZeroClasses.TetaExpoente.Teta_eq_pi_cima
#print axioms ATK.ZeroClasses.TetaExpoente.Teta_eq_pi_baixo
#print axioms ATK.ZeroClasses.TetaExpoente.Teta_eq_pi
#print axioms ATK.ZeroClasses.TetaExpoente.mem_mertens_cima
#print axioms ATK.ZeroClasses.TetaExpoente.mem_mertens_baixo
#print axioms ATK.ZeroClasses.TetaExpoente.freq_mertens_cima
#print axioms ATK.ZeroClasses.TetaExpoente.freq_mertens_baixo
#print axioms ATK.ZeroClasses.TetaExpoente.Teta_eq_mertens_cima
#print axioms ATK.ZeroClasses.TetaExpoente.Teta_eq_mertens_baixo
#print axioms ATK.ZeroClasses.TetaExpoente.Teta_eq_mertens
#print axioms ATK.ZeroClasses.TetaExpoente.rh_iff_expoente_pi_cima
#print axioms ATK.ZeroClasses.TetaExpoente.rh_iff_expoente_psi
#print axioms ATK.ZeroClasses.TetaExpoente.rh_iff_expoente_mertens
