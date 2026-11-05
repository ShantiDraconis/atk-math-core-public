import ATK.ZeroClasses.QuartoGeral
import ATK.DeltaCertificado

/-!
# Avaliação certificada de `ζ(σ + it)` para `σ` racional qualquer (rodada 29)

Generaliza `QuartoAval` (`σ = ¼`) e a reta crítica (`σ = ½`): `m^{−σ}`, com `σ = p/q`, vem de um certificado de
raiz (`lo^q m^p ≤ 1 ≤ hi^q m^p`, `ATK.DeltaCert.rootOk`), cujo candidato é calculado pelo kernel por bissecção
inteira (`iroot`); o resto de Euler–Maclaurin usa `N^{1−σ−M} = N · N^{−σ} · N^{−M}`. Resultado: `mem_zetaIG`.
-/

open Complex Metric Set

namespace ATK.ZeroClasses.Faixa

open ATK.Cert ATK.EMGeral ATK.ZeroCert ATK.ZeroClasses.Quarto

/-! ## 1. Potências racionais certificadas -/

/-- Bissecção: maior `y ∈ [lo, hi)` com `y^q ≤ x` (invariante `lo^q ≤ x < hi^q`). -/
def irootAux (x q : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | f + 1, lo, hi =>
    if hi ≤ lo + 1 then lo else
      if ((lo + hi) / 2) ^ q ≤ x then irootAux x q f ((lo + hi) / 2) hi
      else irootAux x q f lo ((lo + hi) / 2)

/-- `⌊x^{1/q}⌋` (candidato; a correção é verificada à parte). -/
def iroot (x q : ℕ) : ℕ := irootAux x q 256 0 (2 ^ (Nat.log2 x / q + 1))

/-- Candidato para `m^{−σ}` com `P` bits, `σ = num/den`. -/
def powIG (P : ℕ) (σ : ℚ) (m : ℕ) : IR :=
  ⟨(iroot (2 ^ (P * σ.den) / m ^ σ.num.toNat) σ.den : ℚ) / 2 ^ P,
   ((iroot (2 ^ (P * σ.den) / m ^ σ.num.toNat) σ.den : ℚ) + 1) / 2 ^ P⟩

def powOk (P : ℕ) (σ : ℚ) (m : ℕ) : Bool :=
  ATK.DeltaCert.rootOk σ.den σ.num.toNat m (powIG P σ m).lo (powIG P σ m).hi

theorem razao_sigma {σ : ℚ} (h : 0 ≤ σ) : ((σ.num.toNat : ℕ) : ℝ) / (σ.den : ℝ) = (σ : ℝ) := by
  have hn : (0 : ℤ) ≤ σ.num := Rat.num_nonneg.mpr h
  have e : ((σ.num.toNat : ℕ) : ℝ) = (σ.num : ℝ) := by
    have := Int.toNat_of_nonneg hn
    exact_mod_cast this
  rw [e, Rat.cast_def]

theorem mem_powIG {P : ℕ} {σ : ℚ} {m : ℕ} (hσ : 0 ≤ σ) (hm : 1 ≤ m) (h : powOk P σ m = true) :
    IR.mem ((m : ℝ) ^ (-(σ : ℝ))) (powIG P σ m) := by
  have := ATK.DeltaCert.mem_root (Rat.den_pos σ) hm h
  rw [razao_sigma hσ] at this
  exact this

/-! ## 2. Termos, soma e resto -/

def termoG (K nT p : ℕ) (σ t : ℚ) (m : ℕ) : IC :=
  IC.round p (IC.smul (powIG p σ m) (expIAuto nT p (fase K p t m)))

def somaG (K nT p : ℕ) (σ t : ℚ) : ℕ → IC
  | 0 => IC.pt 0 0
  | n + 1 => IC.round p (IC.add (somaG K nT p σ t n) (termoG K nT p σ t (n + 1)))

def okTG (K nT p : ℕ) (σ t : ℚ) (m : ℕ) : Bool :=
  expIAuto_ok nT p (fase K p t m) && powOk p σ m

def okAllG (N K nT p : ℕ) (σ t : ℚ) : Bool := (List.range N).all fun k => okTG K nT p σ t (k + 1)

/-- Cota do resto: `(|Re|+|Im|)((s)_M)/M! · C_M · N · N^{−σ}/N^M / (σ + M − 1)`. -/
def errQG (N M p : ℕ) (σ b : ℚ) : ℚ :=
  (|(pochQ σ b M).1| + |(pochQ σ b M).2|) / (M.factorial : ℚ) * CbR M (M + 1) *
    ((N : ℚ) * (powIG p σ N).hi) / (N : ℚ) ^ M / (σ + M - 1)

/-- Retângulo final para `ζ(σ + it)`. -/
def zetaIG (N M K nT p : ℕ) (σ t : ℚ) : IC :=
  IC.widen (IC.round p (IC.add (somaG K nT p σ t N) (IC.mul (termoG K nT p σ t N)
    (IC.pt (Qcoef N M σ t).1 (Qcoef N M σ t).2)))) (errQG N M p σ t)

theorem mem_termoG {K nT p : ℕ} {σ t : ℚ} {m : ℕ} (hσ : 0 ≤ σ) (hm : 1 ≤ m)
    (hok : okTG K nT p σ t m = true) :
    IC.mem ((m : ℂ) ^ (-(((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I))) (termoG K nT p σ t m) := by
  simp only [okTG, Bool.and_eq_true] at hok
  obtain ⟨hexp, hq⟩ := hok
  rw [ATK.DeltaCert.cpow_gen hm]
  unfold termoG
  refine IC.mem_round p (IC.mem_smul (mem_powIG hσ hm hq) ?_)
  have hθ : IR.mem (-(t : ℝ) * Real.log m) (fase K p t m) := by
    have := IR.mem_mul (IR.mem_pt (-t)) (mem_Lg K p m hm)
    push_cast at this
    exact this
  exact mem_expIAuto hexp hθ

theorem mem_somaG {K nT p : ℕ} {σ t : ℚ} (hσ : 0 ≤ σ) :
    ∀ n : ℕ, (∀ m, 1 ≤ m → m ≤ n → okTG K nT p σ t m = true) →
      IC.mem (∑ k ∈ Finset.range n, ((k : ℂ) + 1) ^ (-(((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I)))
        (somaG K nT p σ t n)
  | 0, _ => by
    simp only [Finset.range_zero, Finset.sum_empty, somaG]
    simpa using IC.mem_pt 0 0
  | n + 1, h => by
    rw [Finset.sum_range_succ]
    simp only [somaG]
    refine IC.mem_round p (IC.mem_add (mem_somaG hσ n fun m h1 h2 => h m h1 (by omega)) ?_)
    have := mem_termoG (K := K) (nT := nT) (p := p) (σ := σ) (t := t) (m := n + 1) hσ (by omega)
      (h (n + 1) (by omega) le_rfl)
    push_cast at this
    exact this

theorem okAllG_spec {N K nT p : ℕ} {σ t : ℚ} (h : okAllG N K nT p σ t = true) :
    ∀ m, 1 ≤ m → m ≤ N → okTG K nT p σ t m = true := by
  intro m h1 h2
  unfold okAllG at h
  rw [List.all_eq_true] at h
  have := h (m - 1) (List.mem_range.mpr (by omega))
  rwa [show m - 1 + 1 = m by omega] at this

/-- `N/(s − 1)` em forma retangular. -/
theorem N_divG (N : ℕ) (σ t : ℚ) (ht : t ≠ 0) :
    (N : ℂ) / ((σ : ℂ) + ((t : ℚ) : ℂ) * I - 1) =
      ((((N : ℚ) * (σ - 1) / ((σ - 1) ^ 2 + t ^ 2) : ℚ) : ℂ) +
        (((-(N : ℚ) * t / ((σ - 1) ^ 2 + t ^ 2)) : ℚ) : ℂ) * I) := by
  have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  have hd : ((σ : ℝ) - 1) ^ 2 + (t : ℝ) ^ 2 ≠ 0 := by positivity
  have hne : ((σ : ℂ) + ((t : ℚ) : ℂ) * I - 1) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact ht this
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

theorem rpow_geral (N M : ℕ) (hN : 1 ≤ N) (σ : ℝ) :
    (N : ℝ) ^ (1 - σ - M) = N * (N : ℝ) ^ (-σ) * ((N : ℝ) ^ M)⁻¹ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [show (1 : ℝ) - σ - M = 1 + (-σ) + (-(M : ℝ)) by ring, Real.rpow_add hN0, Real.rpow_add hN0,
    Real.rpow_one, Real.rpow_neg hN0.le (M : ℝ), Real.rpow_natCast]

theorem resto_leG {N M p : ℕ} (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hM : M ≤ 10) {σ : ℚ} (hσ : 0 < σ) (t : ℚ)
    (ht : t ≠ 0) (hq : powOk p σ N = true) :
    ‖riemannZeta (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I) - EM N M (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I)‖ ≤
      (errQG N M p σ t : ℝ) := by
  set s : ℂ := ((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I with hs
  have hre : s.re = σ := by simp [hs]
  have hσ' : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hs0 : 0 < s.re := by rw [hre]; exact hσ'
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [hs] at this
    exact ht this
  have hE := norm_zeta_sub_EM_le hs0 hs1 hN hM1
  rw [hre, rpow_geral N M hN] at hE
  refine hE.trans ?_
  have hpoch : ‖poch s M‖ ≤ |((pochQ σ t M).1 : ℝ)| + |((pochQ σ t M).2 : ℝ)| := by
    have e := pochQ_spec σ t M
    have e2 : (((σ : ℚ) : ℂ) + ((t : ℚ) : ℂ) * I) = s := by rw [hs]; push_cast; ring
    rw [e2] at e
    rw [← e]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
    simp
  have hCb : Cb M = ((CbR M (M + 1) : ℚ) : ℝ) := by rw [CbR_spec M hM (M + 1) le_rfl]; rfl
  have hpw := (mem_powIG hσ.le hN hq).2
  have hM2 : (0 : ℝ) < (σ : ℝ) + M - 1 := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNM : (0 : ℝ) < ((N : ℝ) ^ M)⁻¹ := by positivity
  have hfac : (0 : ℝ) < M.factorial := by exact_mod_cast Nat.factorial_pos M
  have hCb0 : 0 ≤ Cb M := Cb_nonneg M
  calc ‖poch s M‖ / (M.factorial : ℝ) * (Cb M * (N * (N : ℝ) ^ (-(σ : ℝ)) * ((N : ℝ) ^ M)⁻¹) /
        ((σ : ℝ) + M - 1))
      ≤ (|((pochQ σ t M).1 : ℝ)| + |((pochQ σ t M).2 : ℝ)|) / (M.factorial : ℝ) *
          (Cb M * (N * (((powIG p σ N).hi : ℚ) : ℝ) * ((N : ℝ) ^ M)⁻¹) / ((σ : ℝ) + M - 1)) := by
        gcongr
    _ = (errQG N M p σ t : ℝ) := by
        rw [hCb]
        unfold errQG
        push_cast
        field_simp

/-- **`ζ(σ + it)` está no retângulo `zetaIG`** (`σ > 0` racional, `t ≠ 0`, verificações `okAllG`). -/
theorem mem_zetaIG {N M K nT p : ℕ} (hN : 1 ≤ N) (hM1 : 1 ≤ M) (hM : M ≤ 10) {σ : ℚ} (hσ : 0 < σ)
    (t : ℚ) (ht : t ≠ 0) (hok : okAllG N K nT p σ t = true) :
    IC.mem (riemannZeta (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I)) (zetaIG N M K nT p σ t) := by
  set s : ℂ := ((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * I with hs
  have hall := okAllG_spec hok
  have hS := mem_somaG (K := K) (nT := nT) (p := p) (σ := σ) (t := t) hσ.le N hall
  have hT := mem_termoG (K := K) (nT := nT) (p := p) (σ := σ) (t := t) hσ.le hN (hall N hN le_rfl)
  have hqN : powOk p σ N = true := by
    have := hall N hN le_rfl
    simp only [okTG, Bool.and_eq_true] at this
    exact this.2
  have hQ : IC.mem ((N : ℂ) / (s - 1) - 1 / 2 + ∑ j ∈ Finset.Ico 2 (M + 1), (bernoulli j : ℂ) /
      (j.factorial : ℂ) * poch s (j - 1) * ((N : ℂ) ^ (j - 1))⁻¹)
      (IC.pt (Qcoef N M σ t).1 (Qcoef N M σ t).2) := by
    have e1 : s = ((σ : ℚ) : ℂ) + ((t : ℚ) : ℂ) * I := by rw [hs]; push_cast; ring
    have hP := PcR_spec N σ t M hM
    rw [← e1] at hP
    rw [← hP, e1, N_divG N σ t ht]
    have := IC.mem_pt (Qcoef N M σ t).1 (Qcoef N M σ t).2
    convert this using 1
    simp only [Qcoef]
    push_cast
    ring
  have hEM : IC.mem (EM N M s) (IC.round p (IC.add (somaG K nT p σ t N) (IC.mul (termoG K nT p σ t N)
      (IC.pt (Qcoef N M σ t).1 (Qcoef N M σ t).2)))) := by
    rw [EM_decomp hN M s]
    exact IC.mem_round p (IC.mem_add hS (IC.mem_mul hT hQ))
  exact IC.mem_widen_of_norm hEM (resto_leG hN hM1 hM hσ t ht hqN)

end ATK.ZeroClasses.Faixa

#print axioms ATK.ZeroClasses.Faixa.razao_sigma
#print axioms ATK.ZeroClasses.Faixa.mem_powIG
#print axioms ATK.ZeroClasses.Faixa.mem_termoG
#print axioms ATK.ZeroClasses.Faixa.mem_somaG
#print axioms ATK.ZeroClasses.Faixa.okAllG_spec
#print axioms ATK.ZeroClasses.Faixa.N_divG
#print axioms ATK.ZeroClasses.Faixa.rpow_geral
#print axioms ATK.ZeroClasses.Faixa.resto_leG
#print axioms ATK.ZeroClasses.Faixa.mem_zetaIG
