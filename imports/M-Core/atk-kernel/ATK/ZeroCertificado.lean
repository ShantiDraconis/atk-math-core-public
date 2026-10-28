import ATK.Cert.Transc
import ATK.EMGeral
import ATK.ZetaSimetria

/-!
# ATK — Um zero não trivial certificado na linha crítica (fase 3)

**Teorema** (`zero_na_linha`): existe `ρ` com `ζ(ρ) = 0`, `0 < Re ρ < 1` e **`Re ρ = ½`**, com
`|Im ρ − 14,1347251417| ≤ 10⁻⁶`; e é o **único** zero de `ζ` no disco `|s − z₀| ≤ 10⁻⁶`.

Cadeia, toda no kernel:

1. **Avaliação certificada de `ζ(½ + it)`** (`mem_zetaI`): Euler–Maclaurin `EM_{30,10}` com o resto
   explícito de `ATK/EMGeral.lean` (≈ 5,5·10⁻⁹), e cada `n^{−s} = n^{−½} e^{−it log n}` por
   intervalos racionais (`log n` pela série de `atanh`, `e^{iθ}` por Taylor com redução por `2π`,
   `√n` por certificado). Os retângulos são calculados por `decide +kernel`.
2. **Cota grosseira** `|ζ| ≤ 230` no disco `|s − z₀| ≤ 2/5` (`EM_{1,1}` e seu resto).
3. **Cauchy** (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) duas vezes: `|ζ''| ≤ F₂`.
4. **Quociente de diferenças** `c` de `ζ(z₀ + iδ)` e `ζ(z₀)` certificados: `|c − ζ'(z₀)| ≤ δF₂ + …`.
5. **Contração** `g(z) = z − ζ(z)/c` em `B = closedBall(z₀, r)` (valor médio + Banach): ponto fixo
   ⇒ zero; dois zeros em `B` seriam dois pontos fixos ⇒ **unicidade**.
6. **Simetria** `ρ ↦ 1 − ρ̄` (`torcao_mem_Z`): preserva `B` e os zeros, logo fixa o único zero:
   `Re ρ = ½`.

Consequência: o conjunto `Z` dos zeros não triviais **não é vazio** — a hipótese `hne` dos teoremas
de `ATK/LinhaIncognita.lean`, `ATK/TruncamentoZero.lean` e `ATK/ZeroIncognito.lean` é descarregada
(`ATK/ZeroCertificadoAplicado.lean`). Isto **não** é HR: é um zero, não todos.
-/

open Complex Metric Set

namespace ATK.ZeroCert

open ATK.Cert ATK.EMGeral

/-! ## 1. Definições computáveis -/

/-- Raiz inteira por Newton com combustível (recursão estrutural). -/
def isqrtAux (n : ℕ) : ℕ → ℕ → ℕ
  | 0, g => g
  | k + 1, g => if (g + n / g) / 2 < g then isqrtAux n k ((g + n / g) / 2) else g

def isqrt (n : ℕ) : ℕ := if n ≤ 1 then n else isqrtAux n 256 n

/-- Intervalo candidato para `√m` com `p` bits (verificado por `sqrtOk`). -/
def sqI (p m : ℕ) : IR := ⟨(isqrt (m * 4 ^ p) : ℚ) / 2 ^ p, ((isqrt (m * 4 ^ p) : ℚ) + 1) / 2 ^ p⟩

/-- `log n` com arredondamento para fora. -/
def Lg (K p : ℕ) : ℕ → IR
  | 0 => ⟨0, 0⟩
  | 1 => ⟨0, 0⟩
  | j + 2 => IR.round p (IR.add (Lg K p (j + 1)) (dLog K (j + 1)))

/-- Fase `θ = −t log m`. -/
def fase (K p : ℕ) (t : ℚ) (m : ℕ) : IR := IR.mul (IR.pt (-t)) (Lg K p m)

/-- Retângulo para `m^{−(½ + it)} = m^{−½} e^{−it log m}`. -/
def termo (K nT p : ℕ) (t : ℚ) (m : ℕ) : IC :=
  IC.round p (IC.smul (IR.inv (sqI p m)) (expIAuto nT p (fase K p t m)))

def somaT (K nT p : ℕ) (t : ℚ) : ℕ → IC
  | 0 => IC.pt 0 0
  | n + 1 => IC.round p (IC.add (somaT K nT p t n) (termo K nT p t (n + 1)))

/-- Bernoulli `B₀,…,B₁₀` (convenção do Mathlib, `B₁ = −½`). -/
def Btab : ℕ → ℚ
  | 0 => 1 | 1 => -1 / 2 | 2 => 1 / 6 | 4 => -1 / 30 | 6 => 1 / 42 | 8 => -1 / 30
  | 10 => 5 / 66 | _ => 0

/-- `(s)_m` para `s = a + ib`, como (re, im). -/
def pochQ (a b : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | m + 1 => ((pochQ a b m).1 * (a + m) - (pochQ a b m).2 * b,
      (pochQ a b m).1 * b + (pochQ a b m).2 * (a + m))

/-- `P_M = Σ_{j ∈ [2, M]} B_j/j! (s)_{j−1} N^{−(j−1)}`. -/
def PcR (N : ℕ) (a b : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0, 0)
  | 1 => (0, 0)
  | M + 2 =>
    ((PcR N a b (M + 1)).1 + Btab (M + 2) / ((M + 2).factorial : ℚ) / (N : ℚ) ^ (M + 1) *
        (pochQ a b (M + 1)).1,
     (PcR N a b (M + 1)).2 + Btab (M + 2) / ((M + 2).factorial : ℚ) / (N : ℚ) ^ (M + 1) *
        (pochQ a b (M + 1)).2)

/-- `Q = N/(s−1) − ½ + P_M`. -/
def Qcoef (N M : ℕ) (a b : ℚ) : ℚ × ℚ :=
  ((N : ℚ) * (a - 1) / ((a - 1) ^ 2 + b ^ 2) - 1 / 2 + (PcR N a b M).1,
   -(N : ℚ) * b / ((a - 1) ^ 2 + b ^ 2) + (PcR N a b M).2)

/-- `Σ_{i<k} |B_i| C(M,i)`. -/
def CbR (M : ℕ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => CbR M k + |Btab k| * (M.choose k : ℚ)

/-- Cota do resto de EM: `(|Re|+|Im|)((s)_M)/M! · C_M · √N/N^M / (M − ½)`. -/
def errQ (N M p : ℕ) (b : ℚ) : ℚ :=
  (|(pochQ (1 / 2) b M).1| + |(pochQ (1 / 2) b M).2|) / (M.factorial : ℚ) * CbR M (M + 1) *
    (sqI p N).hi / (N : ℚ) ^ M / ((M : ℚ) - 1 / 2)

/-- Retângulo final para `ζ(½ + it)`. -/
def zetaI (N M K nT p : ℕ) (t : ℚ) : IC :=
  IC.widen (IC.round p (IC.add (somaT K nT p t N) (IC.mul (termo K nT p t N)
    (IC.pt (Qcoef N M (1 / 2) t).1 (Qcoef N M (1 / 2) t).2)))) (errQ N M p t)

/-- Condições verificáveis por `decide` para cada `m`. -/
def okT (K nT p : ℕ) (t : ℚ) (m : ℕ) : Bool :=
  expIAuto_ok nT p (fase K p t m) && sqrtOk m (sqI p m).lo (sqI p m).hi && decide (0 < (sqI p m).lo)

def okAll (N K nT p : ℕ) (t : ℚ) : Bool := (List.range N).all fun k => okT K nT p t (k + 1)

/-! ## 2. Correção das peças -/

theorem mem_Lg (K p : ℕ) : ∀ n : ℕ, 1 ≤ n → IR.mem (Real.log n) (Lg K p n)
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp [Lg, IR.mem]
  | j + 2, _ => by
    have ih := mem_Lg K p (j + 1) (by omega)
    have hd := mem_dLog K (j := j + 1) (by omega)
    have e : Real.log ((j + 2 : ℕ) : ℝ) =
        Real.log ((j + 1 : ℕ) : ℝ) + (Real.log ((j + 1 : ℕ) + 1) - Real.log ((j + 1 : ℕ) : ℝ)) := by
      push_cast; ring_nf
    rw [e]
    simp only [Lg]
    exact IR.mem_round p (IR.mem_add ih (by push_cast at hd ⊢; exact hd))

theorem mem_sqI {p m : ℕ} (h : sqrtOk m (sqI p m).lo (sqI p m).hi = true) :
    IR.mem (Real.sqrt m) (sqI p m) :=
  mem_sqrtI h

/-- `m^{−(½ + it)} = m^{−½} e^{i(−t log m)}`. -/
theorem cpow_meio {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    (m : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I)) =
      (((Real.sqrt m)⁻¹ : ℝ) : ℂ) * Complex.exp (I * ((-t * Real.log m : ℝ) : ℂ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hlog : Complex.log (m : ℂ) = ((Real.log m : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hm0.le, Complex.ofReal_natCast]
  have hsq : ((Real.sqrt m)⁻¹ : ℝ) = Real.exp (-(Real.log m / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hm0, ← Real.exp_neg]
    ring_nf
  rw [Complex.cpow_def_of_ne_zero hmC, hlog, hsq, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem mem_termo {K nT p : ℕ} {t : ℚ} {m : ℕ} (hm : 1 ≤ m) (hok : okT K nT p t m = true) :
    IC.mem ((m : ℂ) ^ (-((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I))) (termo K nT p t m) := by
  simp only [okT, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hexp, hsq⟩, hpos⟩ := hok
  rw [cpow_meio hm]
  unfold termo
  refine IC.mem_round p (IC.mem_smul (IR.mem_inv (mem_sqI hsq) hpos) ?_)
  have hθ : IR.mem (-(t : ℝ) * Real.log m) (fase K p t m) := by
    have := IR.mem_mul (IR.mem_pt (-t)) (mem_Lg K p m hm)
    push_cast at this
    exact this
  exact mem_expIAuto hexp hθ

theorem mem_somaT {K nT p : ℕ} {t : ℚ} :
    ∀ n : ℕ, (∀ m, 1 ≤ m → m ≤ n → okT K nT p t m = true) →
      IC.mem (∑ k ∈ Finset.range n, ((k : ℂ) + 1) ^ (-((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I)))
        (somaT K nT p t n)
  | 0, _ => by
    simp only [Finset.range_zero, Finset.sum_empty, somaT]
    simpa using IC.mem_pt 0 0
  | n + 1, h => by
    rw [Finset.sum_range_succ]
    simp only [somaT]
    refine IC.mem_round p (IC.mem_add (mem_somaT n fun m h1 h2 => h m h1 (by omega)) ?_)
    have := mem_termo (K := K) (nT := nT) (p := p) (t := t) (m := n + 1) (by omega)
      (h (n + 1) (by omega) le_rfl)
    push_cast at this
    exact this

theorem okAll_spec {N K nT p : ℕ} {t : ℚ} (h : okAll N K nT p t = true) :
    ∀ m, 1 ≤ m → m ≤ N → okT K nT p t m = true := by
  intro m h1 h2
  unfold okAll at h
  rw [List.all_eq_true] at h
  have := h (m - 1) (List.mem_range.mpr (by omega))
  rwa [show m - 1 + 1 = m by omega] at this

/-! ### Bernoulli -/

theorem bp6 : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four,
    bernoulli'_eq_zero_of_odd (n := 5) ⟨2, rfl⟩ (by norm_num)]
  norm_num [Nat.choose]

theorem bp8 : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bp6,
    bernoulli'_eq_zero_of_odd (n := 5) ⟨2, rfl⟩ (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 7) ⟨3, rfl⟩ (by norm_num)]
  norm_num [Nat.choose]

theorem bp10 : bernoulli' 10 = 5 / 66 := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bp6, bp8,
    bernoulli'_eq_zero_of_odd (n := 5) ⟨2, rfl⟩ (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 7) ⟨3, rfl⟩ (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 9) ⟨4, rfl⟩ (by norm_num)]
  norm_num [Nat.choose]

theorem bern_eq {j : ℕ} (hj : j ≤ 10) : bernoulli j = Btab j := by
  have odd0 : ∀ n, Odd n → 1 < n → bernoulli n = 0 := fun n h1 h2 => bernoulli_eq_zero_of_odd h1 h2
  have ev : ∀ n, n ≠ 1 → bernoulli n = bernoulli' n := fun n h => bernoulli_eq_bernoulli'_of_ne_one h
  interval_cases j
  · simp [Btab]
  · simp [Btab]
  · simp [Btab]
  · rw [odd0 3 ⟨1, rfl⟩ (by norm_num)]; rfl
  · rw [ev 4 (by norm_num), bernoulli'_four]; rfl
  · rw [odd0 5 ⟨2, rfl⟩ (by norm_num)]; rfl
  · rw [ev 6 (by norm_num), bp6]; rfl
  · rw [odd0 7 ⟨3, rfl⟩ (by norm_num)]; rfl
  · rw [ev 8 (by norm_num), bp8]; rfl
  · rw [odd0 9 ⟨4, rfl⟩ (by norm_num)]; rfl
  · rw [ev 10 (by norm_num), bp10]; rfl

/-! ### Pochhammer, `P`, `C_M` -/

theorem pochQ_spec (a b : ℚ) : ∀ m : ℕ,
    (((pochQ a b m).1 : ℚ) : ℂ) + (((pochQ a b m).2 : ℚ) : ℂ) * I = poch ((a : ℂ) + (b : ℂ) * I) m
  | 0 => by simp [pochQ, poch]
  | m + 1 => by
    rw [poch, ← pochQ_spec a b m]
    simp only [pochQ]
    push_cast
    ring_nf
    rw [I_sq]
    ring

theorem PcR_spec (N : ℕ) (a b : ℚ) : ∀ M : ℕ, M ≤ 10 →
    (((PcR N a b M).1 : ℚ) : ℂ) + (((PcR N a b M).2 : ℚ) : ℂ) * I =
      ∑ j ∈ Finset.Ico 2 (M + 1), (bernoulli j : ℂ) / (j.factorial : ℂ) *
        poch ((a : ℂ) + (b : ℂ) * I) (j - 1) * ((N : ℂ) ^ (j - 1))⁻¹
  | 0, _ => by simp [PcR]
  | 1, _ => by simp [PcR]
  | M + 2, hM => by
    rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ M + 2), ← PcR_spec N a b (M + 1) (by omega)]
    simp only [PcR]
    rw [show M + 2 - 1 = M + 1 by omega, ← pochQ_spec a b (M + 1), bern_eq (by omega : M + 2 ≤ 10)]
    push_cast
    ring

theorem CbR_spec (M : ℕ) (hM : M ≤ 10) : ∀ k : ℕ, k ≤ M + 1 →
    ((CbR M k : ℚ) : ℝ) = ∑ i ∈ Finset.range k, |(bernoulli i : ℝ)| * (M.choose i : ℝ)
  | 0, _ => by simp [CbR]
  | k + 1, hk => by
    rw [Finset.sum_range_succ, ← CbR_spec M hM k (by omega)]
    simp only [CbR]
    rw [bern_eq (by omega : k ≤ 10)]
    push_cast
    ring

/-! ### Decomposição de EM -/

theorem EM_decomp {N : ℕ} (hN : 1 ≤ N) (M : ℕ) (s : ℂ) :
    EM N M s = (∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-s)) + (N : ℂ) ^ (-s) *
      ((N : ℂ) / (s - 1) - 1 / 2 + ∑ j ∈ Finset.Ico 2 (M + 1), (bernoulli j : ℂ) /
        (j.factorial : ℂ) * poch s (j - 1) * ((N : ℂ) ^ (j - 1))⁻¹) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have h1 : (N : ℂ) ^ (1 - s) = N * (N : ℂ) ^ (-s) := by
    rw [show 1 - s = 1 + (-s) by ring, Complex.cpow_add _ _ hN0, Complex.cpow_one]
  have h2 : ∀ j : ℕ, (N : ℂ) ^ (-s - ((j - 1 : ℕ) : ℂ)) = (N : ℂ) ^ (-s) * ((N : ℂ) ^ (j - 1))⁻¹ := by
    intro j
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hN0]
    congr 1
    rw [Complex.cpow_neg, Complex.cpow_natCast]
  unfold EM
  rw [h1]
  have h3 : ∑ j ∈ Finset.Ico 2 (M + 1), (bernoulli j : ℂ) / (j.factorial : ℂ) * poch s (j - 1) *
      (N : ℂ) ^ (-s - ((j - 1 : ℕ) : ℂ)) = (N : ℂ) ^ (-s) * ∑ j ∈ Finset.Ico 2 (M + 1),
        (bernoulli j : ℂ) / (j.factorial : ℂ) * poch s (j - 1) * ((N : ℂ) ^ (j - 1))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h2]
    ring
  rw [h3]
  ring

/-- `N/(s − 1)` para `s = ½ + it` em forma retangular. -/
theorem N_div (N : ℕ) (t : ℚ) :
    (N : ℂ) / (((1 / 2 : ℚ) : ℂ) + ((t : ℚ) : ℂ) * I - 1) =
      ((((N : ℚ) * (1 / 2 - 1) / ((1 / 2 - 1) ^ 2 + t ^ 2) : ℚ) : ℂ) +
        (((-(N : ℚ) * t / ((1 / 2 - 1) ^ 2 + t ^ 2)) : ℚ) : ℂ) * I) := by
  have hd : ((1 / 2 - 1 : ℝ)) ^ 2 + (t : ℝ) ^ 2 ≠ 0 := by positivity
  have hne : (((1 / 2 : ℚ) : ℂ) + ((t : ℚ) : ℂ) * I - 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    norm_num at this
  rw [div_eq_iff hne]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.ratCast_re, Complex.ratCast_im, Complex.mul_im, I_re, I_im, Complex.one_re,
      Complex.one_im, Complex.natCast_re]
    push_cast
    field_simp
    ring
  · simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.ratCast_re, Complex.ratCast_im, Complex.mul_im, I_re, I_im, Complex.one_re,
      Complex.one_im, Complex.natCast_im]
    push_cast
    field_simp
    ring

/-! ### O resto -/

theorem rpow_meio (N M : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (1 - (1 / 2 : ℝ) - M) = Real.sqrt N * ((N : ℝ) ^ M)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show (1 : ℝ) - 1 / 2 - M = 1 / 2 + (-(M : ℝ)) by ring, Real.rpow_add hN0, Real.rpow_neg hN0.le,
    Real.rpow_natCast, Real.sqrt_eq_rpow]

theorem resto_le {N M p : ℕ} (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hM : M ≤ 10) (t : ℚ)
    (hsq : sqrtOk N (sqI p N).lo (sqI p N).hi = true) :
    ‖riemannZeta ((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I) - EM N M ((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I)‖ ≤
      (errQ N M p t : ℝ) := by
  set s : ℂ := (1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I with hs
  have hre : s.re = 1 / 2 := by simp [hs]
  have hs0 : 0 < s.re := by rw [hre]; norm_num
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hE := norm_zeta_sub_EM_le hs0 hs1 hN hM1
  rw [hre, rpow_meio N M hN] at hE
  refine hE.trans ?_
  have hpoch : ‖poch s M‖ ≤ |((pochQ (1 / 2) t M).1 : ℝ)| + |((pochQ (1 / 2) t M).2 : ℝ)| := by
    have e := pochQ_spec (1 / 2) t M
    have e2 : ((((1 / 2 : ℚ)) : ℂ) + ((t : ℚ) : ℂ) * I) = s := by rw [hs]; push_cast; ring
    rw [e2] at e
    rw [← e]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
    simp
  have hCb : Cb M = ((CbR M (M + 1) : ℚ) : ℝ) := by rw [CbR_spec M hM (M + 1) le_rfl]; rfl
  have hsqN := (mem_sqI hsq).2
  have hM2 : (0 : ℝ) < (M : ℝ) - 1 / 2 := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    linarith
  have hNM : (0 : ℝ) < ((N : ℝ) ^ M)⁻¹ := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hfac : (0 : ℝ) < M.factorial := by exact_mod_cast Nat.factorial_pos M
  have hCb0 : 0 ≤ Cb M := Cb_nonneg M
  rw [show (1 / 2 : ℝ) + M - 1 = M - 1 / 2 by ring]
  calc ‖poch s M‖ / (M.factorial : ℝ) * (Cb M * (Real.sqrt N * ((N : ℝ) ^ M)⁻¹) / ((M : ℝ) - 1 / 2))
      ≤ (|((pochQ (1 / 2) t M).1 : ℝ)| + |((pochQ (1 / 2) t M).2 : ℝ)|) / (M.factorial : ℝ) *
          (Cb M * (((sqI p N).hi : ℝ) * ((N : ℝ) ^ M)⁻¹) / ((M : ℝ) - 1 / 2)) := by
        gcongr
    _ = (errQ N M p t : ℝ) := by
        rw [hCb]
        unfold errQ
        push_cast
        field_simp

/-! ### O retângulo de `ζ` -/

/-- **`ζ(½ + it)` está no retângulo `zetaI`** (dadas as verificações `okAll`). -/
theorem mem_zetaI {N M K nT p : ℕ} (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hM : M ≤ 10) (t : ℚ)
    (hok : okAll N K nT p t = true) :
    IC.mem (riemannZeta ((1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I)) (zetaI N M K nT p t) := by
  set s : ℂ := (1 / 2 : ℂ) + ((t : ℝ) : ℂ) * I with hs
  have hall := okAll_spec hok
  have hS := mem_somaT (K := K) (nT := nT) (p := p) (t := t) N hall
  have hT := mem_termo (K := K) (nT := nT) (p := p) (t := t) hN (hall N hN le_rfl)
  have hsN : sqrtOk N (sqI p N).lo (sqI p N).hi = true := by
    have := hall N hN le_rfl
    simp only [okT, Bool.and_eq_true] at this
    exact this.1.2
  have hQ : IC.mem ((N : ℂ) / (s - 1) - 1 / 2 + ∑ j ∈ Finset.Ico 2 (M + 1), (bernoulli j : ℂ) /
      (j.factorial : ℂ) * poch s (j - 1) * ((N : ℂ) ^ (j - 1))⁻¹)
      (IC.pt (Qcoef N M (1 / 2) t).1 (Qcoef N M (1 / 2) t).2) := by
    have e1 : s = ((1 / 2 : ℚ) : ℂ) + ((t : ℚ) : ℂ) * I := by rw [hs]; push_cast; ring
    have hP := PcR_spec N (1 / 2) t M hM
    rw [← e1] at hP
    rw [← hP, e1, N_div N t]
    have := IC.mem_pt (Qcoef N M (1 / 2) t).1 (Qcoef N M (1 / 2) t).2
    convert this using 1
    simp only [Qcoef]
    push_cast
    ring
  have hEM : IC.mem (EM N M s) (IC.round p (IC.add (somaT K nT p t N) (IC.mul (termo K nT p t N)
      (IC.pt (Qcoef N M (1 / 2) t).1 (Qcoef N M (1 / 2) t).2)))) := by
    rw [EM_decomp hN M s]
    exact IC.mem_round p (IC.mem_add hS (IC.mem_mul hT hQ))
  exact IC.mem_widen_of_norm hEM (resto_le hN hM1 hM t hsN)

end ATK.ZeroCert

-- Auditoria de axiomas (kernel)
#print axioms ATK.ZeroCert.mem_Lg
#print axioms ATK.ZeroCert.mem_sqI
#print axioms ATK.ZeroCert.cpow_meio
#print axioms ATK.ZeroCert.mem_termo
#print axioms ATK.ZeroCert.mem_somaT
#print axioms ATK.ZeroCert.okAll_spec
#print axioms ATK.ZeroCert.bp6
#print axioms ATK.ZeroCert.bp8
#print axioms ATK.ZeroCert.bp10
#print axioms ATK.ZeroCert.bern_eq
#print axioms ATK.ZeroCert.pochQ_spec
#print axioms ATK.ZeroCert.PcR_spec
#print axioms ATK.ZeroCert.CbR_spec
#print axioms ATK.ZeroCert.EM_decomp
#print axioms ATK.ZeroCert.N_div
#print axioms ATK.ZeroCert.rpow_meio
#print axioms ATK.ZeroCert.resto_le
#print axioms ATK.ZeroCert.mem_zetaI
