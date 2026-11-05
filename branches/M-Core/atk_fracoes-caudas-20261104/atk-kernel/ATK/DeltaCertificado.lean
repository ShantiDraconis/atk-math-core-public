import ATK.ZeroCertificado
import ATK.RHTerminal

/-!
# ATK — `δ₅ > 0` certificado: `ζ` não se anula em `K₅`

`K₅ = {7/10 ≤ Re s ≤ 4/5, |Im s| ≤ 5}` (`ATK/RHTerminal.lean`). Teorema (`zeta_K5`): `|ζ(s)| ≥ 1/10` em todo
`K₅`; daí `|η(s)| ≥ (2^{1/5} − 1)/10` e **`δ₅ > 0`** (`delta_cinco_pos`), e o mínimo de `rh_iff_minimos` existe
para `n = 5` (`minimo_K5`). É um caso finito de `rh_iff_delta` (HR ⟺ `δ_n > 0` para **todo** `n ≥ 5`), não HR.

Método (tudo no kernel):
* `K₅ ∩ {Im ≥ 0}` é coberto por 450 discos de raio `3/125`, centros `σ_c ∈ {43/60, 45/60, 47/60}`,
  `t_c = (2k+1)/60`, `k < 150` (`cobertura`); `Im < 0` vem de `ζ(s̄) = conj ζ(s)`.
* Em cada disco: `ζ = A + corr + R` com `A = EM_{10,1}`, `corr = EM_{10,4} − EM_{10,1}` (termos de
  Bernoulli) e `R = ζ − EM_{10,4}` (resto de `ATK/EMGeral.lean`);
  `|ζ(s)| ≥ |A(c)| − ρ·L − |corr| − |R|`, com `|A(c)|²` por intervalos racionais, `L` pela desigualdade do
  valor médio termo a termo (`|d/dw n^{−w}| = log n · n^{−Re w}`), e `n^{−σ}` por certificados de raiz
  (`lo^q n^p ≤ 1 ≤ hi^q n^p`).
* `cert_0_0` … `cert_2_5` (18 blocos de 25): nos 450 discos, `(1/10 + ρL + |corr| + |R|)² ≤ |A(c)|²`, verificado por `decide +kernel`.
-/

open Complex Metric Set

namespace ATK.DeltaCert

open ATK.Cert ATK.EMGeral ATK.ZeroCert ATK.ClosedMath.Terminal

/-! ## 1. Potências reais por certificado de raiz -/

/-- `0 ≤ lo`, `lo^q m^p ≤ 1 ≤ hi^q m^p`, `0 ≤ hi`. -/
def rootOk (q p m : ℕ) (lo hi : ℚ) : Bool :=
  decide (0 ≤ lo ∧ lo ^ q * (m : ℚ) ^ p ≤ 1 ∧ 1 ≤ hi ^ q * (m : ℚ) ^ p ∧ 0 ≤ hi)

theorem mem_root {q p m : ℕ} {lo hi : ℚ} (hq : 0 < q) (hm : 1 ≤ m)
    (h : rootOk q p m lo hi = true) : IR.mem ((m : ℝ) ^ (-((p : ℝ) / q))) ⟨lo, hi⟩ := by
  simp only [rootOk, decide_eq_true_eq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set y := (m : ℝ) ^ (-((p : ℝ) / q)) with hy
  have hypos : 0 < y := Real.rpow_pos_of_pos hm0 _
  have hq0 : q ≠ 0 := by omega
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
  have hmp : (0 : ℝ) < (m : ℝ) ^ p := by positivity
  have hyq : y ^ q * (m : ℝ) ^ p = 1 := by
    rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
    have e : -((p : ℝ) / q) * (q : ℝ) = -(p : ℝ) := by field_simp
    rw [e, Real.rpow_neg hm0.le, Real.rpow_natCast, inv_mul_cancel₀ hmp.ne']
  have h1' : ((lo : ℝ)) ^ q * (m : ℝ) ^ p ≤ 1 := by exact_mod_cast h1
  have h2' : 1 ≤ ((hi : ℝ)) ^ q * (m : ℝ) ^ p := by exact_mod_cast h2
  have h0' : (0 : ℝ) ≤ lo := by exact_mod_cast h0
  have h3' : (0 : ℝ) ≤ hi := by exact_mod_cast h3
  constructor
  · have : ((lo : ℝ)) ^ q ≤ y ^ q := le_of_mul_le_mul_right (h1'.trans hyq.symm.le) hmp
    exact (pow_le_pow_iff_left₀ h0' hypos.le hq0).mp this
  · have : y ^ q ≤ ((hi : ℝ)) ^ q := le_of_mul_le_mul_right (hyq.le.trans h2') hmp
    exact (pow_le_pow_iff_left₀ hypos.le h3' hq0).mp this

/-- `m^{−(σ + it)} = m^{−σ} e^{i(−t log m)}`. -/
theorem cpow_gen {m : ℕ} (hm : 1 ≤ m) (σ t : ℝ) :
    (m : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) =
      (((m : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (I * ((-t * Real.log m : ℝ) : ℂ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hlog : Complex.log (m : ℂ) = ((Real.log m : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hm0.le, Complex.ofReal_natCast]
  rw [Complex.cpow_def_of_ne_zero hmC, hlog, Real.rpow_def_of_pos hm0, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## 2. Tabelas e parâmetros -/

/-- `⌊m^{−σ_c}·2⁴⁸⌋` e `+1`, `σ_c = 43/60, 45/60, 47/60` (m = 1..10 em cada). -/
def tabC : List (ℕ × ℕ) :=
  [(281474976710656, 281474976710657), (171278017833608, 171278017833609),
   (128086362580900, 128086362580901), (104222974759017, 104222974759018),
   (88820106333037, 88820106333038), (77940776657120, 77940776657121),
   (69788874838181, 69788874838182), (63419863243462, 63419863243463),
   (58286233721126, 58286233721127), (54047190745951, 54047190745952),
   (281474976710656, 281474976710657), (167366022499768, 167366022499769),
   (123480634048434, 123480634048435), (99516432383215, 99516432383216),
   (84180652673710, 84180652673711), (73422024287722, 73422024287723),
   (65405799974569, 65405799974570), (59172824724903, 59172824724904),
   (54169884524680, 54169884524681), (50054115552574, 50054115552575),
   (281474976710656, 281474976710657), (163543377262839, 163543377262840),
   (119040518270420, 119040518270421), (95022429912231, 95022429912232),
   (79783537502206, 79783537502207), (69165254462657, 69165254462658),
   (61298003159278, 61298003159279), (55210197670759, 55210197670760),
   (50344244293719, 50344244293720), (46356053833161, 46356053833162)]

/-- `⌈m^{−13/20}·2⁴⁸⌉` (m = 1..10). -/
def tabMin : List ℕ :=
  [281474976710657, 179378461445505, 137819597205858, 114314362173773, 98880189272054,
   87829716135793, 79455884370717, 72850292581903, 67481101147795, 63014398034018]

def K0 : ℕ := 10
def nT0 : ℕ := 20
def p0 : ℕ := 32
def rho : ℚ := 3 / 125
def smin : ℚ := 13 / 20

/-- `σ_c` da coluna. -/
def sig (col : ℕ) : ℚ := 43 / 60 + col / 30
/-- Expoente inteiro `p` com `σ_c = p/60`. -/
def pcol (col : ℕ) : ℕ := 43 + 2 * col
/-- `t_c = (2k+1)/60`. -/
def tc (k : ℕ) : ℚ := (2 * k + 1) / 60

def powI (col m : ℕ) : IR :=
  ⟨((tabC.getD (10 * col + (m - 1)) (0, 0)).1 : ℚ) / 2 ^ 48,
   ((tabC.getD (10 * col + (m - 1)) (0, 0)).2 : ℚ) / 2 ^ 48⟩

def powMin (m : ℕ) : ℚ := (tabMin.getD (m - 1) 0 : ℚ) / 2 ^ 48

/-- Retângulo para `m^{−(σ_c + i t_c)}`. -/
def termoG (col k m : ℕ) : IC :=
  IC.round p0 (IC.smul (powI col m) (expIAuto nT0 p0 (fase K0 p0 (tc k) m)))

def somaG (col k : ℕ) : ℕ → IC
  | 0 => IC.pt 0 0
  | n + 1 => IC.round p0 (IC.add (somaG col k n) (termoG col k (n + 1)))

/-- `Q = N/(c − 1) − ½` com `N = 10`, `c = σ_c + i t_c`. -/
def QG (col k : ℕ) : ℚ × ℚ :=
  ((10 : ℚ) * (sig col - 1) / ((sig col - 1) ^ 2 + tc k ^ 2) - 1 / 2,
   -(10 : ℚ) * tc k / ((sig col - 1) ^ 2 + tc k ^ 2))

/-- Retângulo para `A(c) = EM_{10,1}(c)`. -/
def AI (col k : ℕ) : IC :=
  IC.round p0 (IC.add (somaG col k 10) (IC.mul (termoG col k 10) (IC.pt (QG col k).1 (QG col k).2)))

def minAbs (J : IR) : ℚ := if 0 < J.lo then J.lo else if J.hi < 0 then -J.hi else 0

/-- `Σ_{m ≤ 10} log m · m^{−σ_min}` (cota superior). -/
def Lsum : ℚ := ((List.range 10).map fun i => (Lg K0 p0 (i + 1)).hi * powMin (i + 1)).sum

/-- `d ≤ |w − 1|` no disco. -/
def dB (col k : ℕ) : ℚ := max (1 - sig col - rho) (tc k - rho)
/-- `W ≥ |w|` no disco. -/
def WB (col k : ℕ) : ℚ := sig col + tc k + 2 * rho

/-- Constante de Lipschitz de `A` no disco. -/
def LB (col k : ℕ) : ℚ :=
  Lsum + powMin 10 * ((Lg K0 p0 10).hi * (10 / dB col k + 1 / 2) + 10 / dB col k ^ 2)

def pochB (W : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => pochB W k * (W + k)

/-- `|B₂|/2!·|w|·N^{−σ−1} + |B₄|/4!·|w(w+1)(w+2)|·N^{−σ−3}`. -/
def corrQ (W : ℚ) : ℚ := 1 / 12 * pochB W 1 * powMin 10 / 10 + 1 / 720 * pochB W 3 * powMin 10 / 1000

/-- Resto de `EM_{10,4}`. -/
def RQ (W : ℚ) : ℚ := pochB W 4 / 24 * CbR 4 5 * (powMin 10 / 1000) / (smin + 3)

/-- Perdas: `ρ·L + |corr| + |R|`, mais a margem `1/10`. -/
def perda (col k : ℕ) : ℚ := 1 / 10 + rho * LB col k + corrQ (WB col k) + RQ (WB col k)

/-- `|A(c)|² ≥ (min|Re|)² + (min|Im|)²`. -/
def quadInf (J : IC) : ℚ := minAbs J.re ^ 2 + minAbs J.im ^ 2

def okBox (col k : ℕ) : Bool :=
  (List.range 10).all (fun i => expIAuto_ok nT0 p0 (fase K0 p0 (tc k) (i + 1))) &&
    decide (perda col k ^ 2 ≤ quadInf (AI col k)) && decide (0 < dB col k)

def okTabs : Bool :=
  (List.range 3).all (fun col => (List.range 10).all fun i =>
    rootOk 60 (pcol col) (i + 1) (powI col (i + 1)).lo (powI col (i + 1)).hi) &&
  (List.range 10).all (fun i => rootOk 20 13 (i + 1) 0 (powMin (i + 1)))

/-- Os discos `25j ≤ k < 25j + 25` da coluna `col`. -/
def okRange (col j : ℕ) : Bool := (List.range 25).all fun i => okBox col (25 * j + i)

set_option maxRecDepth 100000 in
theorem okTabs_ok : okTabs = true := by decide +kernel

/-! O certificado, em 18 blocos de 25 discos (cada bloco é uma verificação do kernel). -/

set_option maxRecDepth 100000 in
theorem cert_0_0 : okRange 0 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_0_1 : okRange 0 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_0_2 : okRange 0 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_0_3 : okRange 0 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_0_4 : okRange 0 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_0_5 : okRange 0 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_1_0 : okRange 1 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_1_1 : okRange 1 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_1_2 : okRange 1 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_1_3 : okRange 1 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_1_4 : okRange 1 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_1_5 : okRange 1 5 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_2_0 : okRange 2 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_2_1 : okRange 2 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_2_2 : okRange 2 2 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_2_3 : okRange 2 3 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_2_4 : okRange 2 4 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem cert_2_5 : okRange 2 5 = true := by decide +kernel

theorem okRange_all {col j : ℕ} (hc : col < 3) (hj : j < 6) : okRange col j = true := by
  interval_cases col <;> interval_cases j
  · exact cert_0_0
  · exact cert_0_1
  · exact cert_0_2
  · exact cert_0_3
  · exact cert_0_4
  · exact cert_0_5
  · exact cert_1_0
  · exact cert_1_1
  · exact cert_1_2
  · exact cert_1_3
  · exact cert_1_4
  · exact cert_1_5
  · exact cert_2_0
  · exact cert_2_1
  · exact cert_2_2
  · exact cert_2_3
  · exact cert_2_4
  · exact cert_2_5

theorem okBox_ok {col k : ℕ} (hc : col < 3) (hk : k < 150) : okBox col k = true := by
  have h := okRange_all hc (by omega : k / 25 < 6)
  simp only [okRange, List.all_eq_true, List.mem_range] at h
  have := h (k % 25) (Nat.mod_lt _ (by norm_num))
  rwa [Nat.div_add_mod] at this

/-! ## 3. Peças -/

theorem mem_powI {col m : ℕ} (hc : col < 3) (hm1 : 1 ≤ m) (hm : m ≤ 10) :
    IR.mem ((m : ℝ) ^ (-((sig col : ℚ) : ℝ))) (powI col m) := by
  have h := okTabs_ok
  simp only [okTabs, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have hr := h.1 col hc (m - 1) (by omega)
  rw [show m - 1 + 1 = m by omega] at hr
  have := mem_root (by norm_num) hm1 hr
  have e : ((sig col : ℚ) : ℝ) = ((pcol col : ℕ) : ℝ) / ((60 : ℕ) : ℝ) := by
    simp only [sig, pcol]; push_cast; ring
  rw [e]
  exact this

theorem powMin_ge {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 10) :
    (m : ℝ) ^ (-((13 : ℝ) / 20)) ≤ ((powMin m : ℚ) : ℝ) := by
  have h := okTabs_ok
  simp only [okTabs, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have hr := h.2 (m - 1) (by omega)
  rw [show m - 1 + 1 = m by omega] at hr
  have := (mem_root (q := 20) (p := 13) (by norm_num) hm1 hr).2
  simpa using this

/-- `m^{−Re w} ≤ m^{−13/20}` quando `Re w ≥ 13/20`. -/
theorem rpow_le_min {m : ℕ} (hm : 1 ≤ m) {x : ℝ} (hx : (13 : ℝ) / 20 ≤ x) :
    (m : ℝ) ^ (-x) ≤ (m : ℝ) ^ (-((13 : ℝ) / 20)) :=
  Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by linarith)

theorem mem_termoG {col k m : ℕ} (hc : col < 3) (hm1 : 1 ≤ m) (hm : m ≤ 10)
    (hok : expIAuto_ok nT0 p0 (fase K0 p0 (tc k) m) = true) :
    IC.mem ((m : ℂ) ^ (-((((sig col : ℚ) : ℝ) : ℂ) + (((tc k : ℚ) : ℝ) : ℂ) * I))) (termoG col k m) := by
  rw [cpow_gen hm1]
  unfold termoG
  refine IC.mem_round p0 (IC.mem_smul (mem_powI hc hm1 hm) ?_)
  have hθ : IR.mem (-((tc k : ℚ) : ℝ) * Real.log m) (fase K0 p0 (tc k) m) := by
    have := IR.mem_mul (IR.mem_pt (-(tc k))) (mem_Lg K0 p0 m hm1)
    push_cast at this
    exact this
  exact mem_expIAuto hok hθ

theorem okBox_exp {col k : ℕ} (h : okBox col k = true) :
    ∀ m, 1 ≤ m → m ≤ 10 → expIAuto_ok nT0 p0 (fase K0 p0 (tc k) m) = true := by
  intro m h1 h2
  simp only [okBox, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.1.1 (m - 1) (by omega)
  rwa [show m - 1 + 1 = m by omega] at this

theorem mem_somaG {col k : ℕ} (hc : col < 3) (h : okBox col k = true) :
    ∀ n : ℕ, n ≤ 10 →
      IC.mem (∑ i ∈ Finset.range n,
        ((i : ℂ) + 1) ^ (-((((sig col : ℚ) : ℝ) : ℂ) + (((tc k : ℚ) : ℝ) : ℂ) * I))) (somaG col k n)
  | 0, _ => by
    simp only [Finset.range_zero, Finset.sum_empty, somaG]
    simpa using IC.mem_pt 0 0
  | n + 1, hn => by
    rw [Finset.sum_range_succ]
    simp only [somaG]
    refine IC.mem_round p0 (IC.mem_add (mem_somaG hc h n (by omega)) ?_)
    have := mem_termoG (k := k) (m := n + 1) hc (by omega) hn (okBox_exp h (n + 1) (by omega) hn)
    push_cast at this
    exact this

/-- `N/(c − 1)` em forma retangular (σ qualquer, `σ ≠ 1`). -/
theorem N_divG (N : ℕ) (a t : ℚ) (ha : a ≠ 1) :
    (N : ℂ) / (((a : ℚ) : ℂ) + ((t : ℚ) : ℂ) * I - 1) =
      ((((N : ℚ) * (a - 1) / ((a - 1) ^ 2 + t ^ 2) : ℚ) : ℂ) +
        (((-(N : ℚ) * t / ((a - 1) ^ 2 + t ^ 2)) : ℚ) : ℂ) * I) := by
  have ha' : (a : ℝ) - 1 ≠ 0 := by
    intro h; apply ha; exact_mod_cast (sub_eq_zero.mp h)
  have hd : ((a : ℝ) - 1) ^ 2 + (t : ℝ) ^ 2 ≠ 0 := by positivity
  have hne : (((a : ℚ) : ℂ) + ((t : ℚ) : ℂ) * I - 1) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact ha' (by linarith)
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

/-- Centro do disco. -/
noncomputable def cen (col k : ℕ) : ℂ := (((sig col : ℚ) : ℝ) : ℂ) + (((tc k : ℚ) : ℝ) : ℂ) * I

theorem sig_ne_one {col : ℕ} (hc : col < 3) : sig col ≠ 1 := by
  interval_cases col <;> norm_num [sig]

/-- `EM_{10,1}(w) = Σ_{m≤10} m^{−w} + 10^{−w}(10/(w−1) − ½)`. -/
theorem EM_um_decomp (w : ℂ) :
    EM 10 1 w = (∑ n ∈ Finset.range 10, ((n : ℂ) + 1) ^ (-w)) +
      (10 : ℂ) ^ (-w) * ((10 : ℂ) / (w - 1) - 1 / 2) := by
  have := EM_decomp (N := 10) (by norm_num) 1 w
  simpa using this

theorem mem_AI {col k : ℕ} (hc : col < 3) (h : okBox col k = true) :
    IC.mem (EM 10 1 (cen col k)) (AI col k) := by
  rw [EM_um_decomp]
  have hS := mem_somaG hc h 10 le_rfl
  have hT := mem_termoG (k := k) (m := 10) hc (by norm_num) le_rfl (okBox_exp h 10 (by norm_num) le_rfl)
  have hQ : IC.mem ((10 : ℂ) / (cen col k - 1) - 1 / 2) (IC.pt (QG col k).1 (QG col k).2) := by
    have e1 : cen col k = (((sig col : ℚ) : ℂ)) + ((tc k : ℚ) : ℂ) * I := by
      simp only [cen]; push_cast; ring
    rw [e1]
    have hN := N_divG 10 (sig col) (tc k) (sig_ne_one hc)
    push_cast at hN
    rw [hN]
    have := IC.mem_pt (QG col k).1 (QG col k).2
    convert this using 1
    simp only [QG]
    push_cast
    ring
  unfold AI
  refine IC.mem_round p0 (IC.mem_add ?_ (IC.mem_mul ?_ hQ))
  · simpa [cen] using hS
  · have e : ((10 : ℕ) : ℂ) = (10 : ℂ) := by norm_num
    simpa [cen, e] using hT

theorem minAbs_spec {x : ℝ} {J : IR} (hx : IR.mem x J) : (minAbs J : ℝ) ≤ |x| ∧ 0 ≤ (minAbs J : ℝ) := by
  obtain ⟨h1, h2⟩ := hx
  unfold minAbs
  split_ifs with ha hb
  · have : (0 : ℝ) < J.lo := by exact_mod_cast ha
    exact ⟨by rw [abs_of_pos (by linarith)]; exact h1, this.le⟩
  · have : (J.hi : ℝ) < 0 := by exact_mod_cast hb
    refine ⟨?_, ?_⟩
    · rw [abs_of_neg (by linarith)]; push_cast; linarith
    · push_cast; linarith
  · simp

theorem quadInf_le {z : ℂ} {J : IC} (h : IC.mem z J) : (quadInf J : ℝ) ≤ ‖z‖ ^ 2 := by
  obtain ⟨a1, a2⟩ := minAbs_spec h.1
  obtain ⟨b1, b2⟩ := minAbs_spec h.2
  have ha : (minAbs J.re : ℝ) ^ 2 ≤ z.re ^ 2 := by
    rw [← sq_abs z.re]; exact pow_le_pow_left₀ a2 a1 2
  have hb : (minAbs J.im : ℝ) ^ 2 ≤ z.im ^ 2 := by
    rw [← sq_abs z.im]; exact pow_le_pow_left₀ b2 b1 2
  rw [Complex.sq_norm, Complex.normSq_apply]
  unfold quadInf
  push_cast
  nlinarith

/-! ## 4. Valor médio -/

theorem norm_cpow_neg {m : ℕ} (hm : 1 ≤ m) (w : ℂ) : ‖(m : ℂ) ^ (-w)‖ = (m : ℝ) ^ (-w.re) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]; simp

/-- `|m^{−w} − m^{−c}| ≤ log m · m^{−13/20} |w − c|` num convexo com `Re ≥ 13/20`. -/
theorem lip_cpow {m : ℕ} (hm : 1 ≤ m) {S : Set ℂ} (hS : Convex ℝ S)
    (hre : ∀ u ∈ S, (13 : ℝ) / 20 ≤ u.re) {w c : ℂ} (hw : w ∈ S) (hc : c ∈ S) :
    ‖(m : ℂ) ^ (-w) - (m : ℂ) ^ (-c)‖ ≤ Real.log m * (m : ℝ) ^ (-((13 : ℝ) / 20)) * ‖w - c‖ := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hd : ∀ u, HasDerivAt (fun u : ℂ => (m : ℂ) ^ (-u)) ((m : ℂ) ^ (-u) * Complex.log m * (-1)) u :=
    fun u => ((hasDerivAt_id u).neg).const_cpow (Or.inl hm0)
  refine hS.norm_image_sub_le_of_norm_deriv_le (fun u _ => (hd u).differentiableAt) ?_ hc hw
  intro u hu
  rw [(hd u).deriv, norm_mul, norm_mul, norm_neg, norm_one, mul_one, norm_cpow_neg hm,
    ← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hm))]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (rpow_le_min hm (hre u hu)) (Real.log_nonneg (by exact_mod_cast hm))

/-- O termo `f(w) = 10^{−w}(10/(w−1) − ½)`. -/
noncomputable def fpol (w : ℂ) : ℂ := (10 : ℂ) ^ (-w) * ((10 : ℂ) / (w - 1) - 1 / 2)

theorem lip_fpol {S : Set ℂ} (hS : Convex ℝ S) {d : ℝ} (hd0 : 0 < d)
    (hre : ∀ u ∈ S, (13 : ℝ) / 20 ≤ u.re) (hdist : ∀ u ∈ S, d ≤ ‖u - 1‖) {w c : ℂ} (hw : w ∈ S)
    (hc : c ∈ S) :
    ‖fpol w - fpol c‖ ≤ (10 : ℝ) ^ (-((13 : ℝ) / 20)) *
      (Real.log 10 * (10 / d + 1 / 2) + 10 / d ^ 2) * ‖w - c‖ := by
  have h10 : (10 : ℂ) ≠ 0 := by norm_num
  have hderiv : ∀ u ∈ S, HasDerivAt fpol
      ((10 : ℂ) ^ (-u) * Complex.log 10 * (-1) * ((10 : ℂ) / (u - 1) - 1 / 2) +
        (10 : ℂ) ^ (-u) * (-(10 : ℂ) / (u - 1) ^ 2)) u := by
    intro u hu
    have hu1 : u - 1 ≠ 0 := by
      intro h0; have := hdist u hu; rw [h0, norm_zero] at this; linarith
    have h1 : HasDerivAt (fun u : ℂ => (10 : ℂ) ^ (-u)) ((10 : ℂ) ^ (-u) * Complex.log 10 * (-1)) u :=
      ((hasDerivAt_id u).neg).const_cpow (Or.inl h10)
    have h2 : HasDerivAt (fun u : ℂ => (10 : ℂ) / (u - 1) - 1 / 2) (-(10 : ℂ) / (u - 1) ^ 2) u := by
      have := (((hasDerivAt_id u).sub_const 1).inv hu1).const_mul (10 : ℂ)
      have h3 := this.sub_const (1 / 2 : ℂ)
      convert h3 using 1
      · funext x; simp [div_eq_mul_inv]
      · simp; ring
    exact h1.mul h2
  refine hS.norm_image_sub_le_of_norm_deriv_le (fun u hu => (hderiv u hu).differentiableAt) ?_ hc hw
  intro u hu
  rw [(hderiv u hu).deriv]
  have hu1 := hdist u hu
  have hun : 0 < ‖u - 1‖ := lt_of_lt_of_le hd0 hu1
  have hp : ‖(10 : ℂ) ^ (-u)‖ ≤ (10 : ℝ) ^ (-((13 : ℝ) / 20)) := by
    have := norm_cpow_neg (m := 10) (by norm_num) u
    push_cast at this
    rw [this]
    exact rpow_le_min (m := 10) (by norm_num) (hre u hu) |>.trans_eq (by norm_num)
  have hlog : ‖Complex.log 10‖ = Real.log 10 := by
    have := (Complex.natCast_log (n := 10)).symm
    push_cast at this
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by norm_num))]
  have hg : ‖(10 : ℂ) / (u - 1) - 1 / 2‖ ≤ 10 / d + 1 / 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_div]
    have : ‖(10 : ℂ)‖ / ‖u - 1‖ ≤ 10 / d := by
      rw [show ‖(10 : ℂ)‖ = 10 by norm_num]
      exact div_le_div_of_nonneg_left (by norm_num) hd0 hu1
    have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    linarith
  have hq : ‖-(10 : ℂ) / (u - 1) ^ 2‖ ≤ 10 / d ^ 2 := by
    rw [norm_div, norm_neg, norm_pow, show ‖(10 : ℂ)‖ = 10 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hd0.le hu1 2)
  have hP0 : 0 ≤ (10 : ℝ) ^ (-((13 : ℝ) / 20)) := by positivity
  have hl0 : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
  calc ‖(10 : ℂ) ^ (-u) * Complex.log 10 * (-1) * ((10 : ℂ) / (u - 1) - 1 / 2) +
        (10 : ℂ) ^ (-u) * (-(10 : ℂ) / (u - 1) ^ 2)‖
      ≤ ‖(10 : ℂ) ^ (-u)‖ * Real.log 10 * ‖(10 : ℂ) / (u - 1) - 1 / 2‖ +
          ‖(10 : ℂ) ^ (-u)‖ * ‖-(10 : ℂ) / (u - 1) ^ 2‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, norm_one, hlog, mul_one]
    _ ≤ (10 : ℝ) ^ (-((13 : ℝ) / 20)) * Real.log 10 * (10 / d + 1 / 2) +
          (10 : ℝ) ^ (-((13 : ℝ) / 20)) * (10 / d ^ 2) := by
        gcongr
    _ = (10 : ℝ) ^ (-((13 : ℝ) / 20)) * (Real.log 10 * (10 / d + 1 / 2) + 10 / d ^ 2) := by ring

/-! ## 5. Correções de Bernoulli e resto -/

theorem norm_poch_le {w : ℂ} {W : ℚ} (hW : ‖w‖ ≤ (W : ℝ)) :
    ∀ k : ℕ, ‖poch w k‖ ≤ ((pochB W k : ℚ) : ℝ)
  | 0 => by simp [poch, pochB]
  | k + 1 => by
    simp only [poch, pochB]
    push_cast
    rw [norm_mul]
    have ih := norm_poch_le hW k
    have h1 : ‖w + (k : ℂ)‖ ≤ (W : ℝ) + k := by
      refine (norm_add_le _ _).trans ?_
      simp only [Complex.norm_natCast]
      linarith
    have h0 : 0 ≤ ‖poch w k‖ := norm_nonneg _
    exact mul_le_mul ih h1 (norm_nonneg _) (h0.trans ih)

theorem norm_ten_pow {w : ℂ} (hre : (13 : ℝ) / 20 ≤ w.re) (j : ℕ) :
    ‖(10 : ℂ) ^ (-w - (j : ℂ))‖ ≤ ((powMin 10 : ℚ) : ℝ) / 10 ^ j := by
  have h := Complex.norm_natCast_cpow_of_pos (n := 10) (by norm_num) (-w - (j : ℂ))
  push_cast at h
  rw [h]
  have e : (-w - (j : ℂ)).re = -w.re + (-(j : ℝ)) := by simp; ring
  rw [e, Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num) (j : ℝ), Real.rpow_natCast]
  have h1 : (10 : ℝ) ^ (-w.re) ≤ ((powMin 10 : ℚ) : ℝ) := by
    have := (rpow_le_min (m := 10) (by norm_num) hre)
    push_cast at this
    exact this.trans (by simpa using powMin_ge (m := 10) (by norm_num) le_rfl)
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

theorem corr_le {w : ℂ} {W : ℚ} (hW : ‖w‖ ≤ (W : ℝ)) (hre : (13 : ℝ) / 20 ≤ w.re) :
    ‖EM 10 4 w - EM 10 1 w‖ ≤ (corrQ W : ℝ) := by
  have e : EM 10 4 w - EM 10 1 w =
      (bernoulli 2 : ℂ) / ((2 : ℕ).factorial : ℂ) * poch w 1 * (10 : ℂ) ^ (-w - ((1 : ℕ) : ℂ)) +
      (bernoulli 3 : ℂ) / ((3 : ℕ).factorial : ℂ) * poch w 2 * (10 : ℂ) ^ (-w - ((2 : ℕ) : ℂ)) +
      (bernoulli 4 : ℂ) / ((4 : ℕ).factorial : ℂ) * poch w 3 * (10 : ℂ) ^ (-w - ((3 : ℕ) : ℂ)) := by
    simp only [EM, Finset.sum_Ico_succ_top (by norm_num : 2 ≤ 2),
      Finset.sum_Ico_succ_top (by norm_num : 2 ≤ 3), Finset.sum_Ico_succ_top (by norm_num : 2 ≤ 4),
      Finset.Ico_self, Finset.sum_empty]
    push_cast
    ring
  have hb2 : (bernoulli 2 : ℂ) / ((2 : ℕ).factorial : ℂ) = 1 / 12 := by
    rw [bern_eq (by norm_num)]; simp [Btab, Nat.factorial]; norm_num
  have hb3 : (bernoulli 3 : ℂ) / ((3 : ℕ).factorial : ℂ) = 0 := by
    rw [bern_eq (by norm_num)]; simp [Btab]
  have hb4 : (bernoulli 4 : ℂ) / ((4 : ℕ).factorial : ℂ) = -1 / 720 := by
    rw [bern_eq (by norm_num)]; simp [Btab, Nat.factorial]; norm_num
  rw [e, hb2, hb3, hb4, zero_mul, zero_mul, add_zero]
  have p1 := norm_poch_le hW 1
  have p3 := norm_poch_le hW 3
  have n1 := norm_ten_pow hre 1
  have n3 := norm_ten_pow hre 3
  have hpm0 : (0 : ℝ) ≤ ((powMin 10 : ℚ) : ℝ) :=
    (by positivity : (0 : ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-((13 : ℝ) / 20))).trans (powMin_ge (by norm_num) le_rfl)
  have a1 : ‖(1 / 12 : ℂ) * poch w 1 * (10 : ℂ) ^ (-w - ((1 : ℕ) : ℂ))‖ ≤
      1 / 12 * ((pochB W 1 : ℚ) : ℝ) * (((powMin 10 : ℚ) : ℝ) / 10) := by
    rw [norm_mul, norm_mul, show ‖(1 / 12 : ℂ)‖ = 1 / 12 by norm_num]
    have h10 : ((powMin 10 : ℚ) : ℝ) / 10 ^ 1 = ((powMin 10 : ℚ) : ℝ) / 10 := by norm_num
    rw [h10] at n1
    exact mul_le_mul (mul_le_mul_of_nonneg_left p1 (by norm_num)) n1 (norm_nonneg _)
      (mul_nonneg (by norm_num) ((norm_nonneg _).trans p1))
  have a3 : ‖(-1 / 720 : ℂ) * poch w 3 * (10 : ℂ) ^ (-w - ((3 : ℕ) : ℂ))‖ ≤
      1 / 720 * ((pochB W 3 : ℚ) : ℝ) * (((powMin 10 : ℚ) : ℝ) / 1000) := by
    rw [norm_mul, norm_mul, show ‖(-1 / 720 : ℂ)‖ = 1 / 720 by norm_num]
    have h10 : ((powMin 10 : ℚ) : ℝ) / 10 ^ 3 = ((powMin 10 : ℚ) : ℝ) / 1000 := by norm_num
    rw [h10] at n3
    exact mul_le_mul (mul_le_mul_of_nonneg_left p3 (by norm_num)) n3 (norm_nonneg _)
      (mul_nonneg (by norm_num) ((norm_nonneg _).trans p3))
  have hc : (corrQ W : ℝ) = 1 / 12 * ((pochB W 1 : ℚ) : ℝ) * (((powMin 10 : ℚ) : ℝ) / 10) +
      1 / 720 * ((pochB W 3 : ℚ) : ℝ) * (((powMin 10 : ℚ) : ℝ) / 1000) := by
    unfold corrQ; push_cast; ring
  rw [hc]
  exact (norm_add_le _ _).trans (add_le_add a1 a3)

theorem resto_le' {w : ℂ} {W : ℚ} (hW : ‖w‖ ≤ (W : ℝ)) (hre : (13 : ℝ) / 20 ≤ w.re) (hw1 : w ≠ 1) :
    ‖riemannZeta w - EM 10 4 w‖ ≤ (RQ W : ℝ) := by
  have hs : 0 < w.re := by linarith
  have hE := norm_zeta_sub_EM_le hs hw1 (N := 10) (by norm_num) (M := 4) (by norm_num)
  refine hE.trans ?_
  have hCb : Cb 4 = ((CbR 4 5 : ℚ) : ℝ) := by rw [CbR_spec 4 (by norm_num) 5 le_rfl]; rfl
  have hp := norm_poch_le hW 4
  have hN : ((10 : ℕ) : ℝ) ^ (1 - w.re - ((4 : ℕ) : ℝ)) ≤ ((powMin 10 : ℚ) : ℝ) / 1000 := by
    have e : (1 : ℝ) - w.re - ((4 : ℕ) : ℝ) = -w.re + (-(3 : ℝ)) := by push_cast; ring
    rw [e, Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num) (3 : ℝ)]
    have h1 : ((10 : ℕ) : ℝ) ^ (-w.re) ≤ ((powMin 10 : ℚ) : ℝ) :=
      (rpow_le_min (by norm_num) hre).trans (powMin_ge (by norm_num) le_rfl)
    have h3 : ((((10 : ℕ) : ℝ) ^ (3 : ℝ))⁻¹) = 1 / 1000 := by norm_num
    rw [h3]
    calc _ ≤ ((powMin 10 : ℚ) : ℝ) * (1 / 1000) := mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ = ((powMin 10 : ℚ) : ℝ) / 1000 := by ring
  have hden : (smin : ℝ) + 3 ≤ w.re + ((4 : ℕ) : ℝ) - 1 := by
    simp only [smin]; push_cast; linarith
  have hCb0 : 0 ≤ Cb 4 := ATK.EMGeral.Cb_nonneg 4
  have hs3 : (0 : ℝ) < (smin : ℝ) + 3 := by simp only [smin]; push_cast; norm_num
  have hNpos : 0 ≤ ((10 : ℕ) : ℝ) ^ (1 - w.re - ((4 : ℕ) : ℝ)) := by positivity
  have hf : (0 : ℝ) < ((4 : ℕ).factorial : ℝ) := by norm_num [Nat.factorial]
  have hden0 : (0 : ℝ) < w.re + ((4 : ℕ) : ℝ) - 1 := by linarith
  have hq1 : ‖poch w 4‖ / ((4 : ℕ).factorial : ℝ) ≤ ((pochB W 4 : ℚ) : ℝ) / ((4 : ℕ).factorial : ℝ) :=
    div_le_div_of_nonneg_right hp hf.le
  have hq2 : Cb 4 * ((10 : ℕ) : ℝ) ^ (1 - w.re - ((4 : ℕ) : ℝ)) / (w.re + ((4 : ℕ) : ℝ) - 1) ≤
      Cb 4 * (((powMin 10 : ℚ) : ℝ) / 1000) / ((smin : ℝ) + 3) := by
    calc Cb 4 * ((10 : ℕ) : ℝ) ^ (1 - w.re - ((4 : ℕ) : ℝ)) / (w.re + ((4 : ℕ) : ℝ) - 1)
        ≤ Cb 4 * (((powMin 10 : ℚ) : ℝ) / 1000) / (w.re + ((4 : ℕ) : ℝ) - 1) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN hCb0) hden0.le
      _ ≤ Cb 4 * (((powMin 10 : ℚ) : ℝ) / 1000) / ((smin : ℝ) + 3) :=
          div_le_div_of_nonneg_left (mul_nonneg hCb0 (hNpos.trans hN)) hs3 hden
  have hA0 : 0 ≤ Cb 4 * ((10 : ℕ) : ℝ) ^ (1 - w.re - ((4 : ℕ) : ℝ)) / (w.re + ((4 : ℕ) : ℝ) - 1) :=
    div_nonneg (mul_nonneg hCb0 hNpos) hden0.le
  have hB0 : 0 ≤ ((pochB W 4 : ℚ) : ℝ) / ((4 : ℕ).factorial : ℝ) :=
    div_nonneg ((norm_nonneg _).trans hp) hf.le
  calc ‖poch w 4‖ / ((4 : ℕ).factorial : ℝ) *
        (Cb 4 * ((10 : ℕ) : ℝ) ^ (1 - w.re - ((4 : ℕ) : ℝ)) / (w.re + ((4 : ℕ) : ℝ) - 1))
      ≤ ((pochB W 4 : ℚ) : ℝ) / ((4 : ℕ).factorial : ℝ) *
          (Cb 4 * (((powMin 10 : ℚ) : ℝ) / 1000) / ((smin : ℝ) + 3)) := mul_le_mul hq1 hq2 hA0 hB0
    _ = (RQ W : ℝ) := by
        rw [hCb]; unfold RQ; simp only [Nat.factorial]; push_cast; ring

/-! ## 6. Um disco -/

theorem disco {col k : ℕ} (hc : col < 3) (hk : k < 150) {s : ℂ}
    (hs : s ∈ closedBall (cen col k) (rho : ℝ)) : 1 / 10 ≤ ‖riemannZeta s‖ := by
  have hok := okBox_ok hc hk
  have hlow : perda col k ^ 2 ≤ quadInf (AI col k) := by
    simp only [okBox, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.1.2
  have hd0 : (0 : ℚ) < dB col k := by
    simp only [okBox, Bool.and_eq_true, decide_eq_true_eq] at hok; exact hok.2
  set B := closedBall (cen col k) (rho : ℝ)
  have hcB : cen col k ∈ B := mem_closedBall_self (by simp [rho]; norm_num)
  have hcre : (cen col k).re = ((sig col : ℚ) : ℝ) := by simp [cen]
  have hcim : (cen col k).im = ((tc k : ℚ) : ℝ) := by simp [cen]
  have hsig : (43 : ℝ) / 60 ≤ ((sig col : ℚ) : ℝ) ∧ ((sig col : ℚ) : ℝ) ≤ 47 / 60 := by
    interval_cases col <;> simp [sig] <;> norm_num
  have htc : (0 : ℝ) ≤ ((tc k : ℚ) : ℝ) := by simp [tc]; positivity
  -- propriedades dos pontos do disco
  have hpts : ∀ u ∈ B, |u.re - ((sig col : ℚ) : ℝ)| ≤ 3 / 125 ∧ |u.im - ((tc k : ℚ) : ℝ)| ≤ 3 / 125 := by
    intro u hu
    rw [mem_closedBall, dist_eq_norm] at hu
    have hr : ((rho : ℚ) : ℝ) = 3 / 125 := by norm_num [rho]
    rw [hr] at hu
    constructor
    · have := Complex.abs_re_le_norm (u - cen col k); rw [sub_re, hcre] at this; linarith
    · have := Complex.abs_im_le_norm (u - cen col k); rw [sub_im, hcim] at this; linarith
  have hre : ∀ u ∈ B, (13 : ℝ) / 20 ≤ u.re := by
    intro u hu; have := (hpts u hu).1; rw [abs_le] at this; linarith [hsig.1, this.1]
  have hdist : ∀ u ∈ B, ((dB col k : ℚ) : ℝ) ≤ ‖u - 1‖ := by
    intro u hu
    obtain ⟨h1, h2⟩ := hpts u hu
    rw [abs_le] at h1 h2
    have hr1 : 1 - u.re ≤ ‖u - 1‖ := by
      have := Complex.abs_re_le_norm (u - 1)
      rw [sub_re, one_re] at this
      linarith [neg_abs_le (u.re - 1)]
    have hr2 : u.im ≤ ‖u - 1‖ := by
      have := Complex.abs_im_le_norm (u - 1)
      rw [sub_im, one_im, sub_zero] at this
      linarith [le_abs_self u.im]
    simp only [dB, rho]
    push_cast
    apply max_le <;> linarith [h1.2, h2.1]
  have hnorm : ∀ u ∈ B, ‖u‖ ≤ ((WB col k : ℚ) : ℝ) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hpts u hu
    rw [abs_le] at h1 h2
    refine (Complex.norm_le_abs_re_add_abs_im u).trans ?_
    have a1 : |u.re| ≤ ((sig col : ℚ) : ℝ) + 3 / 125 := by
      rw [abs_le]; constructor <;> linarith [hsig.1]
    have a2 : |u.im| ≤ ((tc k : ℚ) : ℝ) + 3 / 125 := by
      rw [abs_le]; constructor <;> linarith
    simp only [WB, rho]; push_cast; linarith
  have hsB := hs
  have hs1 : s ≠ 1 := by
    intro h; have := hdist s hsB; rw [h, sub_self, norm_zero] at this
    have : (0 : ℝ) < (dB col k : ℝ) := by exact_mod_cast hd0
    linarith
  -- as três estimativas
  have hconv : Convex ℝ B := convex_closedBall _ _
  have hsc : ‖s - cen col k‖ ≤ (rho : ℝ) := by rwa [mem_closedBall, dist_eq_norm] at hsB
  have hdpos : (0 : ℝ) < (dB col k : ℝ) := by exact_mod_cast hd0
  have hLip : ‖EM 10 1 s - EM 10 1 (cen col k)‖ ≤ (LB col k : ℝ) * (rho : ℝ) := by
    rw [EM_um_decomp, EM_um_decomp]
    have e : (∑ n ∈ Finset.range 10, ((n : ℂ) + 1) ^ (-s)) + fpol s -
        ((∑ n ∈ Finset.range 10, ((n : ℂ) + 1) ^ (-cen col k)) + fpol (cen col k)) =
        (∑ n ∈ Finset.range 10, (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-cen col k))) +
          (fpol s - fpol (cen col k)) := by
      rw [Finset.sum_sub_distrib]; push_cast; ring
    rw [show (10 : ℂ) ^ (-s) * ((10 : ℂ) / (s - 1) - 1 / 2) = fpol s from rfl,
      show (10 : ℂ) ^ (-cen col k) * ((10 : ℂ) / (cen col k - 1) - 1 / 2) = fpol (cen col k) from rfl,
      e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖∑ n ∈ Finset.range 10, (((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-cen col k))‖ ≤
        (Lsum : ℝ) * (rho : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ n ∈ Finset.range 10,
          ‖((n + 1 : ℕ) : ℂ) ^ (-s) - ((n + 1 : ℕ) : ℂ) ^ (-cen col k)‖ ≤
            ((Lg K0 p0 (n + 1)).hi : ℝ) * ((powMin (n + 1) : ℚ) : ℝ) * (rho : ℝ) := by
        intro n hn
        have hn10 : n + 1 ≤ 10 := by simp at hn; omega
        have hl := lip_cpow (m := n + 1) (by omega) hconv hre hsB hcB
        have hlog := (mem_Lg K0 p0 (n + 1) (by omega)).2
        have hpm := powMin_ge (m := n + 1) (by omega) hn10
        have hlog0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n + 1))
        have hp0 : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ (-((13 : ℝ) / 20)) := by positivity
        refine hl.trans ?_
        have : Real.log ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (-((13 : ℝ) / 20)) ≤
            ((Lg K0 p0 (n + 1)).hi : ℝ) * ((powMin (n + 1) : ℚ) : ℝ) :=
          mul_le_mul hlog hpm hp0 (hlog0.trans hlog)
        exact mul_le_mul this hsc (norm_nonneg _) (mul_nonneg (hlog0.trans hlog) (hp0.trans hpm))
      refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
      rw [← Finset.sum_mul]
      congr 1
      simp only [Lsum]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      simp [List.range_succ]
      ring
    have h2 := lip_fpol hconv hdpos hre hdist hsB hcB
    have h2' : (10 : ℝ) ^ (-((13 : ℝ) / 20)) * (Real.log 10 * (10 / (dB col k : ℝ) + 1 / 2) +
        10 / (dB col k : ℝ) ^ 2) * ‖s - cen col k‖ ≤
        ((powMin 10 : ℚ) : ℝ) * (((Lg K0 p0 10).hi : ℝ) * (10 / (dB col k : ℝ) + 1 / 2) +
          10 / (dB col k : ℝ) ^ 2) * (rho : ℝ) := by
      have hpm : (10 : ℝ) ^ (-((13 : ℝ) / 20)) ≤ ((powMin 10 : ℚ) : ℝ) := by
        simpa using powMin_ge (m := 10) (by norm_num) le_rfl
      have hlog := (mem_Lg K0 p0 10 (by norm_num)).2
      push_cast at hlog
      have hl0 : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
      have hx : 0 ≤ 10 / (dB col k : ℝ) + 1 / 2 := by positivity
      have hpm0 : (0 : ℝ) ≤ ((powMin 10 : ℚ) : ℝ) := (by positivity : (0 : ℝ) ≤ (10 : ℝ) ^ (-((13 : ℝ) / 20))).trans hpm
      have hX : Real.log 10 * (10 / (dB col k : ℝ) + 1 / 2) + 10 / (dB col k : ℝ) ^ 2 ≤
          ((Lg K0 p0 10).hi : ℝ) * (10 / (dB col k : ℝ) + 1 / 2) + 10 / (dB col k : ℝ) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_right hlog hx) le_rfl
      have hX0 : 0 ≤ Real.log 10 * (10 / (dB col k : ℝ) + 1 / 2) + 10 / (dB col k : ℝ) ^ 2 := by positivity
      exact mul_le_mul (mul_le_mul hpm hX hX0 hpm0) hsc (norm_nonneg _) (mul_nonneg hpm0 (hX0.trans hX))
    have := h2.trans h2'
    have hLB : (LB col k : ℝ) * (rho : ℝ) = (Lsum : ℝ) * (rho : ℝ) +
        ((powMin 10 : ℚ) : ℝ) * (((Lg K0 p0 10).hi : ℝ) * (10 / (dB col k : ℝ) + 1 / 2) +
          10 / (dB col k : ℝ) ^ 2) * (rho : ℝ) := by
      unfold LB; push_cast; ring
    linarith
  have hcorr := corr_le (hnorm s hsB) (hre s hsB)
  have hR := resto_le' (hnorm s hsB) (hre s hsB) hs1
  have hA2 := quadInf_le (mem_AI hc hok)
  have hlow' : ((perda col k : ℚ) : ℝ) ^ 2 ≤ ((quadInf (AI col k) : ℚ) : ℝ) := by exact_mod_cast hlow
  have hLB0 : (0 : ℝ) ≤ (LB col k : ℝ) * (rho : ℝ) := le_trans (norm_nonneg _) hLip
  have hc0 : (0 : ℝ) ≤ (corrQ (WB col k) : ℝ) := le_trans (norm_nonneg _) hcorr
  have hR0 : (0 : ℝ) ≤ (RQ (WB col k) : ℝ) := le_trans (norm_nonneg _) hR
  have hpe : ((perda col k : ℚ) : ℝ) = 1 / 10 + (rho : ℝ) * (LB col k : ℝ) + (corrQ (WB col k) : ℝ) +
      (RQ (WB col k) : ℝ) := by unfold perda; push_cast; ring
  have hp0 : (0 : ℝ) ≤ ((perda col k : ℚ) : ℝ) := by rw [hpe]; nlinarith
  have hAge : ((perda col k : ℚ) : ℝ) ≤ ‖EM 10 1 (cen col k)‖ :=
    (pow_le_pow_iff_left₀ hp0 (norm_nonneg _) (by norm_num)).mp (hlow'.trans hA2)
  have tri : ‖EM 10 1 (cen col k)‖ ≤ ‖riemannZeta s‖ + ‖EM 10 1 s - EM 10 1 (cen col k)‖ +
      ‖EM 10 4 s - EM 10 1 s‖ + ‖riemannZeta s - EM 10 4 s‖ := by
    have e : EM 10 1 (cen col k) = riemannZeta s - (EM 10 1 s - EM 10 1 (cen col k)) -
        (EM 10 4 s - EM 10 1 s) - (riemannZeta s - EM 10 4 s) := by ring
    have t1 := norm_sub_le (riemannZeta s - (EM 10 1 s - EM 10 1 (cen col k)) - (EM 10 4 s - EM 10 1 s))
      (riemannZeta s - EM 10 4 s)
    have t2 := norm_sub_le (riemannZeta s - (EM 10 1 s - EM 10 1 (cen col k))) (EM 10 4 s - EM 10 1 s)
    have t3 := norm_sub_le (riemannZeta s) (EM 10 1 s - EM 10 1 (cen col k))
    calc ‖EM 10 1 (cen col k)‖ = ‖riemannZeta s - (EM 10 1 s - EM 10 1 (cen col k)) -
          (EM 10 4 s - EM 10 1 s) - (riemannZeta s - EM 10 4 s)‖ := congrArg norm e
      _ ≤ _ := by linarith
  rw [hpe] at hAge
  nlinarith

/-! ## 7. Cobertura e conclusão -/

theorem cobertura {s : ℂ} (hs : s ∈ Kn 5) (him : 0 ≤ s.im) :
    ∃ col < 3, ∃ k < 150, s ∈ closedBall (cen col k) (rho : ℝ) := by
  obtain ⟨h1, h2, h3⟩ := hs
  norm_num at h1 h2 h3
  rw [abs_le] at h3
  set col : ℕ := min ⌊30 * (s.re - 7 / 10)⌋₊ 2 with hcol
  set k : ℕ := min ⌊30 * s.im⌋₊ 149 with hk
  refine ⟨col, by omega, k, by omega, ?_⟩
  have hx0 : (0 : ℝ) ≤ 30 * (s.re - 7 / 10) := by linarith
  have hf1 := Nat.floor_le hx0
  have hf2 := Nat.lt_floor_add_one (30 * (s.re - 7 / 10))
  have hre : |s.re - ((sig col : ℚ) : ℝ)| ≤ 1 / 60 := by
    simp only [sig]
    push_cast
    rw [abs_le]
    by_cases hc : ⌊30 * (s.re - 7 / 10)⌋₊ ≤ 2
    · have : col = ⌊30 * (s.re - 7 / 10)⌋₊ := by simp only [hcol]; omega
      rw [this]
      constructor <;> linarith
    · push Not at hc
      have : col = 2 := by simp only [hcol]; omega
      rw [this]
      have : (2 : ℝ) < ⌊30 * (s.re - 7 / 10)⌋₊ := by exact_mod_cast hc
      push_cast
      constructor <;> linarith
  have hy0 : (0 : ℝ) ≤ 30 * s.im := by linarith
  have hg1 := Nat.floor_le hy0
  have hg2 := Nat.lt_floor_add_one (30 * s.im)
  have him' : |s.im - ((tc k : ℚ) : ℝ)| ≤ 1 / 60 := by
    simp only [tc]
    push_cast
    rw [abs_le]
    by_cases hc : ⌊30 * s.im⌋₊ ≤ 149
    · have : k = ⌊30 * s.im⌋₊ := by simp only [hk]; omega
      rw [this]
      constructor <;> linarith
    · push Not at hc
      have : k = 149 := by simp only [hk]; omega
      rw [this]
      have : (149 : ℝ) < ⌊30 * s.im⌋₊ := by exact_mod_cast hc
      push_cast
      constructor <;> linarith
  rw [mem_closedBall, dist_eq_norm]
  have hsq : ‖s - cen col k‖ ^ 2 ≤ ((rho : ℚ) : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have e1 : (s - cen col k).re = s.re - ((sig col : ℚ) : ℝ) := by simp [cen]
    have e2 : (s - cen col k).im = s.im - ((tc k : ℚ) : ℝ) := by simp [cen]
    rw [e1, e2]
    have a := abs_le.mp hre
    have b := abs_le.mp him'
    have hr : ((rho : ℚ) : ℝ) = 3 / 125 := by norm_num [rho]
    rw [hr]
    nlinarith
  have hr0 : (0 : ℝ) ≤ ((rho : ℚ) : ℝ) := by norm_num [rho]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr0 (by norm_num)).mp hsq

/-- **`|ζ(s)| ≥ 1/10` em todo `K₅`.** -/
theorem zeta_K5 {s : ℂ} (hs : s ∈ Kn 5) : 1 / 10 ≤ ‖riemannZeta s‖ := by
  by_cases him : 0 ≤ s.im
  · obtain ⟨col, hc, k, hk, hB⟩ := cobertura hs him
    exact disco hc hk hB
  · push Not at him
    have hs' : (starRingEnd ℂ) s ∈ Kn 5 := by
      obtain ⟨h1, h2, h3⟩ := hs
      exact ⟨by simpa using h1, by simpa using h2, by simpa using h3⟩
    obtain ⟨col, hc, k, hk, hB⟩ := cobertura hs' (by simp; linarith)
    have := disco hc hk hB
    rwa [riemannZeta_conj, Complex.norm_conj] at this

/-- O mínimo de `rh_iff_minimos` para `n = 5`. -/
theorem minimo_K5 : ∃ m > 0, ∀ s ∈ Kn 5, m ≤ ‖riemannZeta s‖ :=
  ⟨1 / 10, by norm_num, fun _ hs => zeta_K5 hs⟩

/-- `|η(s)| ≥ (2^{1/5} − 1)/10` em `K₅`. -/
theorem eta_K5 {s : ℂ} (hs : s ∈ Kn 5) :
    ((2 : ℝ) ^ ((1 : ℝ) / 5) - 1) / 10 ≤ ‖ATK.ClosedMath.Terminal.eta s‖ := by
  have hz := zeta_K5 hs
  obtain ⟨h1, h2, -⟩ := hs
  norm_num at h1 h2
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hpow : ‖(2 : ℂ) ^ (1 - s)‖ = (2 : ℝ) ^ (1 - s.re) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos h2pos (1 - s)
    push_cast at this
    simpa using this
  have hge : (2 : ℝ) ^ ((1 : ℝ) / 5) ≤ (2 : ℝ) ^ (1 - s.re) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hf : (2 : ℝ) ^ ((1 : ℝ) / 5) - 1 ≤ ‖1 - (2 : ℂ) ^ (1 - s)‖ := by
    have := norm_sub_norm_le ((2 : ℂ) ^ (1 - s)) 1
    rw [hpow, norm_one] at this
    rw [norm_sub_rev]
    linarith
  have hpos : 0 ≤ (2 : ℝ) ^ ((1 : ℝ) / 5) - 1 := by
    have := Real.one_lt_rpow (x := 2) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 5)
    linarith
  unfold ATK.ClosedMath.Terminal.eta
  rw [norm_mul]
  calc ((2 : ℝ) ^ ((1 : ℝ) / 5) - 1) / 10 = ((2 : ℝ) ^ ((1 : ℝ) / 5) - 1) * (1 / 10) := by ring
    _ ≤ ‖1 - (2 : ℂ) ^ (1 - s)‖ * ‖riemannZeta s‖ := mul_le_mul hf hz (by norm_num) (by positivity)

/-- **`δ₅ > 0`** (incondicional): o primeiro caso de `rh_iff_delta`. -/
theorem delta_cinco_pos : 0 < delta 5 := by
  obtain ⟨⟨s₀, hs₀, he⟩, -⟩ := delta_atingido (n := 5) le_rfl
  rw [he]
  have h := eta_K5 hs₀
  have hpos : 0 < (2 : ℝ) ^ ((1 : ℝ) / 5) - 1 := by
    have := Real.one_lt_rpow (x := 2) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 5)
    linarith
  linarith

end ATK.DeltaCert

-- Auditoria de axiomas (kernel)
#print axioms ATK.DeltaCert.mem_root
#print axioms ATK.DeltaCert.cpow_gen
#print axioms ATK.DeltaCert.okTabs_ok
#print axioms ATK.DeltaCert.okRange_all
#print axioms ATK.DeltaCert.okBox_ok
#print axioms ATK.DeltaCert.mem_AI
#print axioms ATK.DeltaCert.quadInf_le
#print axioms ATK.DeltaCert.lip_cpow
#print axioms ATK.DeltaCert.lip_fpol
#print axioms ATK.DeltaCert.corr_le
#print axioms ATK.DeltaCert.resto_le'
#print axioms ATK.DeltaCert.disco
#print axioms ATK.DeltaCert.cobertura
#print axioms ATK.DeltaCert.zeta_K5
#print axioms ATK.DeltaCert.minimo_K5
#print axioms ATK.DeltaCert.eta_K5
#print axioms ATK.DeltaCert.delta_cinco_pos
