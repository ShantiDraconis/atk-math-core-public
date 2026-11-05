import ATK.ZeroCritico

/-!
# Avaliação certificada de `ζ(¼ + it)` (rodada 28)

Extensão de `ATK/ZeroCertificado.lean` (reta crítica `σ = ½`) para a reta `σ = ¼`: Euler–Maclaurin
`EM_{N,M}` com o resto explícito de `ATK/EMGeral.lean`, `n^{−(¼+it)} = n^{−¼} e^{−it log n}` com `n^{¼}`
certificado por intervalos racionais (`lo⁴ ≤ n ≤ hi⁴`), `log n` pela série de `atanh` e `e^{iθ}` por Taylor
com redução por `2π`. Resultado: `mem_zetaI4` — `ζ(¼ + it)` está no retângulo `zetaI4 N M K nT p t`, dadas as
verificações `okAll4` (decididas pelo kernel).
-/

open Complex Metric Set

namespace ATK.ZeroClasses.Quarto

open ATK.Cert ATK.EMGeral ATK.ZeroCert

/-! ## 1. Raiz quarta certificada -/

/-- Intervalo candidato para `m^{1/4}` com `p` bits. -/
def qI (p m : ℕ) : IR :=
  ⟨(isqrt (isqrt (m * 2 ^ (4 * p))) : ℚ) / 2 ^ p, ((isqrt (isqrt (m * 2 ^ (4 * p))) : ℚ) + 1) / 2 ^ p⟩

/-- Verificação `0 ≤ lo`, `lo⁴ ≤ m ≤ hi⁴`. -/
def qrtOk (m : ℕ) (lo hi : ℚ) : Bool := decide (0 ≤ lo ∧ lo ^ 4 ≤ m ∧ (m : ℚ) ≤ hi ^ 4 ∧ 0 ≤ hi)

theorem mem_qrt {m : ℕ} {lo hi : ℚ} (h : qrtOk m lo hi = true) :
    IR.mem ((m : ℝ) ^ (1 / 4 : ℝ)) ⟨lo, hi⟩ := by
  simp only [qrtOk, decide_eq_true_eq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hx0 : 0 ≤ (m : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hm _
  have hx4 : ((m : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm]
    norm_num
  have h0' : (0 : ℝ) ≤ lo := by exact_mod_cast h0
  have h3' : (0 : ℝ) ≤ hi := by exact_mod_cast h3
  have h1' : (lo : ℝ) ^ 4 ≤ ((m : ℝ) ^ (1 / 4 : ℝ)) ^ 4 := by rw [hx4]; exact_mod_cast h1
  have h2' : ((m : ℝ) ^ (1 / 4 : ℝ)) ^ 4 ≤ (hi : ℝ) ^ 4 := by rw [hx4]; exact_mod_cast h2
  exact ⟨(pow_le_pow_iff_left₀ h0' hx0 (by norm_num)).mp h1',
    (pow_le_pow_iff_left₀ hx0 h3' (by norm_num)).mp h2'⟩

/-- `m^{−(¼ + it)} = m^{−¼} e^{i(−t log m)}`. -/
theorem cpow_quarto {m : ℕ} (hm : 1 ≤ m) (t : ℝ) :
    (m : ℂ) ^ (-((1 / 4 : ℂ) + (t : ℂ) * I)) =
      ((((m : ℝ) ^ (1 / 4 : ℝ))⁻¹ : ℝ) : ℂ) * Complex.exp (I * ((-t * Real.log m : ℝ) : ℂ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hlog : Complex.log (m : ℂ) = ((Real.log m : ℝ) : ℂ) := by
    rw [Complex.ofReal_log hm0.le, Complex.ofReal_natCast]
  have hq : (((m : ℝ) ^ (1 / 4 : ℝ))⁻¹ : ℝ) = Real.exp (-(Real.log m / 4)) := by
    rw [Real.rpow_def_of_pos hm0, ← Real.exp_neg]
    ring_nf
  rw [Complex.cpow_def_of_ne_zero hmC, hlog, hq, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## 2. Os termos e a soma -/

/-- Retângulo para `m^{−(¼ + it)}`. -/
def termo4 (K nT p : ℕ) (t : ℚ) (m : ℕ) : IC :=
  IC.round p (IC.smul (IR.inv (qI p m)) (expIAuto nT p (fase K p t m)))

def somaT4 (K nT p : ℕ) (t : ℚ) : ℕ → IC
  | 0 => IC.pt 0 0
  | n + 1 => IC.round p (IC.add (somaT4 K nT p t n) (termo4 K nT p t (n + 1)))

def okT4 (K nT p : ℕ) (t : ℚ) (m : ℕ) : Bool :=
  expIAuto_ok nT p (fase K p t m) && qrtOk m (qI p m).lo (qI p m).hi && decide (0 < (qI p m).lo)

def okAll4 (N K nT p : ℕ) (t : ℚ) : Bool := (List.range N).all fun k => okT4 K nT p t (k + 1)

/-- Cota do resto: `(|Re|+|Im|)((s)_M)/M! · C_M · N^{3/4}/N^M / (M − ¾)`. -/
def errQ4 (N M p : ℕ) (b : ℚ) : ℚ :=
  (|(pochQ (1 / 4) b M).1| + |(pochQ (1 / 4) b M).2|) / (M.factorial : ℚ) * CbR M (M + 1) *
    (qI p N).hi ^ 3 / (N : ℚ) ^ M / ((M : ℚ) - 3 / 4)

/-- Retângulo final para `ζ(¼ + it)`. -/
def zetaI4 (N M K nT p : ℕ) (t : ℚ) : IC :=
  IC.widen (IC.round p (IC.add (somaT4 K nT p t N) (IC.mul (termo4 K nT p t N)
    (IC.pt (Qcoef N M (1 / 4) t).1 (Qcoef N M (1 / 4) t).2)))) (errQ4 N M p t)

theorem mem_termo4 {K nT p : ℕ} {t : ℚ} {m : ℕ} (hm : 1 ≤ m) (hok : okT4 K nT p t m = true) :
    IC.mem ((m : ℂ) ^ (-((1 / 4 : ℂ) + ((t : ℝ) : ℂ) * I))) (termo4 K nT p t m) := by
  simp only [okT4, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hexp, hq⟩, hpos⟩ := hok
  rw [cpow_quarto hm]
  unfold termo4
  refine IC.mem_round p (IC.mem_smul (IR.mem_inv (mem_qrt hq) hpos) ?_)
  have hθ : IR.mem (-(t : ℝ) * Real.log m) (fase K p t m) := by
    have := IR.mem_mul (IR.mem_pt (-t)) (mem_Lg K p m hm)
    push_cast at this
    exact this
  exact mem_expIAuto hexp hθ

theorem mem_somaT4 {K nT p : ℕ} {t : ℚ} :
    ∀ n : ℕ, (∀ m, 1 ≤ m → m ≤ n → okT4 K nT p t m = true) →
      IC.mem (∑ k ∈ Finset.range n, ((k : ℂ) + 1) ^ (-((1 / 4 : ℂ) + ((t : ℝ) : ℂ) * I)))
        (somaT4 K nT p t n)
  | 0, _ => by
    simp only [Finset.range_zero, Finset.sum_empty, somaT4]
    simpa using IC.mem_pt 0 0
  | n + 1, h => by
    rw [Finset.sum_range_succ]
    simp only [somaT4]
    refine IC.mem_round p (IC.mem_add (mem_somaT4 n fun m h1 h2 => h m h1 (by omega)) ?_)
    have := mem_termo4 (K := K) (nT := nT) (p := p) (t := t) (m := n + 1) (by omega)
      (h (n + 1) (by omega) le_rfl)
    push_cast at this
    exact this

theorem okAll4_spec {N K nT p : ℕ} {t : ℚ} (h : okAll4 N K nT p t = true) :
    ∀ m, 1 ≤ m → m ≤ N → okT4 K nT p t m = true := by
  intro m h1 h2
  unfold okAll4 at h
  rw [List.all_eq_true] at h
  have := h (m - 1) (List.mem_range.mpr (by omega))
  rwa [show m - 1 + 1 = m by omega] at this

/-! ## 3. A parte explícita e o resto -/

/-- `N/(s − 1)` para `s = ¼ + it` em forma retangular. -/
theorem N_div4 (N : ℕ) (t : ℚ) :
    (N : ℂ) / (((1 / 4 : ℚ) : ℂ) + ((t : ℚ) : ℂ) * I - 1) =
      ((((N : ℚ) * (1 / 4 - 1) / ((1 / 4 - 1) ^ 2 + t ^ 2) : ℚ) : ℂ) +
        (((-(N : ℚ) * t / ((1 / 4 - 1) ^ 2 + t ^ 2)) : ℚ) : ℂ) * I) := by
  have hd : ((1 / 4 - 1 : ℝ)) ^ 2 + (t : ℝ) ^ 2 ≠ 0 := by positivity
  have hne : (((1 / 4 : ℚ) : ℂ) + ((t : ℚ) : ℂ) * I - 1) ≠ 0 := by
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

theorem rpow_quarto (N M : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (1 - (1 / 4 : ℝ) - M) = ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 3 * ((N : ℝ) ^ M)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show (1 : ℝ) - 1 / 4 - M = (1 / 4) * (3 : ℕ) + (-(M : ℝ)) by push_cast; ring,
    Real.rpow_add hN0, Real.rpow_neg hN0.le, Real.rpow_natCast, Real.rpow_mul hN0.le, Real.rpow_natCast]

theorem resto_le4 {N M p : ℕ} (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hM : M ≤ 10) (t : ℚ)
    (hq : qrtOk N (qI p N).lo (qI p N).hi = true) :
    ‖riemannZeta ((1 / 4 : ℂ) + ((t : ℝ) : ℂ) * I) - EM N M ((1 / 4 : ℂ) + ((t : ℝ) : ℂ) * I)‖ ≤
      (errQ4 N M p t : ℝ) := by
  set s : ℂ := (1 / 4 : ℂ) + ((t : ℝ) : ℂ) * I with hs
  have hre : s.re = 1 / 4 := by simp [hs]
  have hs0 : 0 < s.re := by rw [hre]; norm_num
  have hs1 : s ≠ 1 := by
    intro h; have := congrArg Complex.re h; rw [hre] at this; norm_num at this
  have hE := norm_zeta_sub_EM_le hs0 hs1 hN hM1
  rw [hre, rpow_quarto N M hN] at hE
  refine hE.trans ?_
  have hpoch : ‖poch s M‖ ≤ |((pochQ (1 / 4) t M).1 : ℝ)| + |((pochQ (1 / 4) t M).2 : ℝ)| := by
    have e := pochQ_spec (1 / 4) t M
    have e2 : ((((1 / 4 : ℚ)) : ℂ) + ((t : ℚ) : ℂ) * I) = s := by rw [hs]; push_cast; ring
    rw [e2] at e
    rw [← e]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
    simp
  have hCb : Cb M = ((CbR M (M + 1) : ℚ) : ℝ) := by rw [CbR_spec M hM (M + 1) le_rfl]; rfl
  have hqN := mem_qrt hq
  have hx0 : 0 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hcube : ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 3 ≤ (((qI p N).hi : ℚ) : ℝ) ^ 3 :=
    pow_le_pow_left₀ hx0 hqN.2 3
  have hM2 : (0 : ℝ) < (M : ℝ) - 3 / 4 := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    linarith
  have hNM : (0 : ℝ) < ((N : ℝ) ^ M)⁻¹ := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hfac : (0 : ℝ) < M.factorial := by exact_mod_cast Nat.factorial_pos M
  have hCb0 : 0 ≤ Cb M := Cb_nonneg M
  rw [show (1 / 4 : ℝ) + M - 1 = M - 3 / 4 by ring]
  calc ‖poch s M‖ / (M.factorial : ℝ) * (Cb M * (((N : ℝ) ^ (1 / 4 : ℝ)) ^ 3 * ((N : ℝ) ^ M)⁻¹) /
        ((M : ℝ) - 3 / 4))
      ≤ (|((pochQ (1 / 4) t M).1 : ℝ)| + |((pochQ (1 / 4) t M).2 : ℝ)|) / (M.factorial : ℝ) *
          (Cb M * ((((qI p N).hi : ℚ) : ℝ) ^ 3 * ((N : ℝ) ^ M)⁻¹) / ((M : ℝ) - 3 / 4)) := by
        gcongr
    _ = (errQ4 N M p t : ℝ) := by
        rw [hCb]
        unfold errQ4
        push_cast
        field_simp

/-- **`ζ(¼ + it)` está no retângulo `zetaI4`** (dadas as verificações `okAll4`). -/
theorem mem_zetaI4 {N M K nT p : ℕ} (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hM : M ≤ 10) (t : ℚ)
    (hok : okAll4 N K nT p t = true) :
    IC.mem (riemannZeta ((1 / 4 : ℂ) + ((t : ℝ) : ℂ) * I)) (zetaI4 N M K nT p t) := by
  set s : ℂ := (1 / 4 : ℂ) + ((t : ℝ) : ℂ) * I with hs
  have hall := okAll4_spec hok
  have hS := mem_somaT4 (K := K) (nT := nT) (p := p) (t := t) N hall
  have hT := mem_termo4 (K := K) (nT := nT) (p := p) (t := t) hN (hall N hN le_rfl)
  have hqN : qrtOk N (qI p N).lo (qI p N).hi = true := by
    have := hall N hN le_rfl
    simp only [okT4, Bool.and_eq_true] at this
    exact this.1.2
  have hQ : IC.mem ((N : ℂ) / (s - 1) - 1 / 2 + ∑ j ∈ Finset.Ico 2 (M + 1), (bernoulli j : ℂ) /
      (j.factorial : ℂ) * poch s (j - 1) * ((N : ℂ) ^ (j - 1))⁻¹)
      (IC.pt (Qcoef N M (1 / 4) t).1 (Qcoef N M (1 / 4) t).2) := by
    have e1 : s = ((1 / 4 : ℚ) : ℂ) + ((t : ℚ) : ℂ) * I := by rw [hs]; push_cast; ring
    have hP := PcR_spec N (1 / 4) t M hM
    rw [← e1] at hP
    rw [← hP, e1, N_div4 N t]
    have := IC.mem_pt (Qcoef N M (1 / 4) t).1 (Qcoef N M (1 / 4) t).2
    convert this using 1
    simp only [Qcoef]
    push_cast
    ring
  have hEM : IC.mem (EM N M s) (IC.round p (IC.add (somaT4 K nT p t N) (IC.mul (termo4 K nT p t N)
      (IC.pt (Qcoef N M (1 / 4) t).1 (Qcoef N M (1 / 4) t).2)))) := by
    rw [EM_decomp hN M s]
    exact IC.mem_round p (IC.mem_add hS (IC.mem_mul hT hQ))
  exact IC.mem_widen_of_norm hEM (resto_le4 hN hM1 hM t hqN)

/-! ## 4. Cota inferior da norma de um retângulo -/

/-- Distância de um intervalo a `0`. -/
def dz (J : IR) : ℚ := if 0 < J.lo then J.lo else if J.hi < 0 then -J.hi else 0

/-- `dz(Re)² + dz(Im)²`, cota inferior de `‖z‖²` no retângulo. -/
def nMinSq (J : IC) : ℚ := dz J.re ^ 2 + dz J.im ^ 2

theorem dz_le {x : ℝ} {J : IR} (h : IR.mem x J) : 0 ≤ (dz J : ℝ) ∧ (dz J : ℝ) ≤ |x| := by
  obtain ⟨h1, h2⟩ := h
  unfold dz
  split_ifs with ha hb
  · have : (0 : ℝ) < J.lo := by exact_mod_cast ha
    exact ⟨this.le, by rw [abs_of_pos (by linarith)]; exact h1⟩
  · have : (J.hi : ℝ) < 0 := by exact_mod_cast hb
    refine ⟨by push_cast; linarith, ?_⟩
    rw [abs_of_neg (by linarith)]
    push_cast
    linarith
  · simp

theorem nMinSq_le {z : ℂ} {J : IC} (h : IC.mem z J) : (nMinSq J : ℝ) ≤ ‖z‖ ^ 2 := by
  obtain ⟨a0, a1⟩ := dz_le h.1
  obtain ⟨b0, b1⟩ := dz_le h.2
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  unfold nMinSq
  push_cast
  have e1 : (dz J.re : ℝ) ^ 2 ≤ z.re * z.re := by
    rw [← sq, ← sq_abs z.re]
    exact pow_le_pow_left₀ a0 a1 2
  have e2 : (dz J.im : ℝ) ^ 2 ≤ z.im * z.im := by
    rw [← sq, ← sq_abs z.im]
    exact pow_le_pow_left₀ b0 b1 2
  linarith

/-- **Cota inferior certificada**: `0 ≤ v` e `v² ≤ nMinSq J` ⟹ `v ≤ ‖z‖`. -/
theorem le_norm_de {z : ℂ} {J : IC} {v : ℚ} (h : IC.mem z J) (h0 : 0 ≤ v) (hv : v ^ 2 ≤ nMinSq J) :
    (v : ℝ) ≤ ‖z‖ := by
  have h1 : ((v : ℚ) : ℝ) ^ 2 ≤ ‖z‖ ^ 2 := by
    have := nMinSq_le h
    have hv' : ((v ^ 2 : ℚ) : ℝ) ≤ (nMinSq J : ℝ) := by exact_mod_cast hv
    push_cast at hv'
    linarith
  have h0' : (0 : ℝ) ≤ v := by exact_mod_cast h0
  exact (pow_le_pow_iff_left₀ h0' (norm_nonneg z) (by norm_num)).mp h1

end ATK.ZeroClasses.Quarto

#print axioms ATK.ZeroClasses.Quarto.mem_qrt
#print axioms ATK.ZeroClasses.Quarto.cpow_quarto
#print axioms ATK.ZeroClasses.Quarto.mem_termo4
#print axioms ATK.ZeroClasses.Quarto.mem_somaT4
#print axioms ATK.ZeroClasses.Quarto.okAll4_spec
#print axioms ATK.ZeroClasses.Quarto.N_div4
#print axioms ATK.ZeroClasses.Quarto.rpow_quarto
#print axioms ATK.ZeroClasses.Quarto.resto_le4
#print axioms ATK.ZeroClasses.Quarto.mem_zetaI4
#print axioms ATK.ZeroClasses.Quarto.dz_le
#print axioms ATK.ZeroClasses.Quarto.nMinSq_le
#print axioms ATK.ZeroClasses.Quarto.le_norm_de
