import ATK.ZeroClasses.FaixaAval

/-!
# Certificado de `|ζ| ≥ δ` num retângulo (rodada 29)

Versão bidimensional de `QuartoGeral`: retângulo `ret s0 s1 a b = [s0, s1] × [a, b]`, região de Cauchy
`[s0 − r, s1 + r] × [a − r, b + r]` (com `r < s0`, `r < a`), cota grosseira `cotaQ`, Cauchy `‖ζ′‖ ≤ B/r`, malha
`nσ × nt` de centros `(s0 + hσ(2i+1), a + ht(2j+1))` com raio de cobertura `h ≥ √(hσ² + ht²)`, e a verificação
de todos os centros pelo kernel (`chkR`). Resultado: `peca_ret`.
-/

open Complex Metric Set

namespace ATK.ZeroClasses.Faixa

open ATK.Cert ATK.EMGeral ATK.ZeroCert ATK.ZeroClasses.Regions ATK.ZeroClasses.Quarto

/-- O retângulo `[s0, s1] × [a, b]`. -/
def ret (s0 s1 a b : ℝ) : Set ℂ := {z | s0 ≤ z.re ∧ z.re ≤ s1 ∧ a ≤ z.im ∧ z.im ≤ b}

theorem convex_ret (s0 s1 a b : ℝ) : Convex ℝ (ret s0 s1 a b) := by
  intro x hx y hy u v hu hv huv
  obtain ⟨x1, x2, x3, x4⟩ := hx
  obtain ⟨y1, y2, y3, y4⟩ := hy
  simp only [ret, mem_ofPred_eq, add_re, add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  have l1 := mul_le_mul_of_nonneg_left x1 hu
  have l2 := mul_le_mul_of_nonneg_left y1 hv
  have l3 := mul_le_mul_of_nonneg_left x2 hu
  have l4 := mul_le_mul_of_nonneg_left y2 hv
  have l5 := mul_le_mul_of_nonneg_left x3 hu
  have l6 := mul_le_mul_of_nonneg_left y3 hv
  have l7 := mul_le_mul_of_nonneg_left x4 hu
  have l8 := mul_le_mul_of_nonneg_left y4 hv
  have e : ∀ c : ℝ, u * c + v * c = c := fun c => by rw [← add_mul, huv, one_mul]
  have := e s0
  have := e s1
  have := e a
  have := e b
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Geometria da região de Cauchy. -/
theorem reg_ret {s0 s1 a b r R d : ℝ} (hrs : r < s0) (hra : r < a)
    (hR : (s1 + r) ^ 2 + (b + r) ^ 2 ≤ R ^ 2) (hR0 : 0 ≤ R) (hd0 : 0 < d) (hd : d ≤ a - r) {w : ℂ}
    (h1 : s0 - r ≤ w.re) (h2 : w.re ≤ s1 + r) (h3 : a - r ≤ w.im) (h4 : w.im ≤ b + r) :
    0 < w.re ∧ w ≠ 1 ∧ ‖w‖ ≤ R ∧ d ≤ ‖w - 1‖ := by
  have hre0 : 0 < w.re := by linarith
  have him0 : 0 < w.im := by linarith
  refine ⟨hre0, ?_, ?_, ?_⟩
  · intro e
    rw [e, one_im] at him0
    exact lt_irrefl _ him0
  · have hsq : ‖w‖ ^ 2 ≤ R ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      have e1 : w.re * w.re ≤ (s1 + r) ^ 2 := by nlinarith
      have e2 : w.im * w.im ≤ (b + r) ^ 2 := by nlinarith
      linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg w) hR0 (by norm_num)).mp hsq
  · have := Complex.abs_im_le_norm (w - 1)
    rw [sub_im, one_im, sub_zero, abs_of_pos him0] at this
    linarith

/-- **Cauchy no retângulo**: `‖ζ′‖ ≤ B/r` se `‖ζ‖ ≤ B` na região. -/
theorem deriv_cota_ret {s0 s1 a b r B : ℝ} (hr : 0 < r) (hra : r < a)
    (hB : ∀ w : ℂ, s0 - r ≤ w.re → w.re ≤ s1 + r → a - r ≤ w.im → w.im ≤ b + r → ‖riemannZeta w‖ ≤ B)
    {x : ℂ} (hx : x ∈ ret s0 s1 a b) : ‖deriv riemannZeta x‖ ≤ B / r := by
  obtain ⟨hx1, hx2, hx3, hx4⟩ := hx
  have prox : ∀ y ∈ closedBall x r,
      s0 - r ≤ y.re ∧ y.re ≤ s1 + r ∧ a - r ≤ y.im ∧ y.im ≤ b + r := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have e1 := Complex.abs_re_le_norm (y - x)
    have e2 := Complex.abs_im_le_norm (y - x)
    rw [sub_re] at e1
    rw [sub_im] at e2
    obtain ⟨f1, f2⟩ := abs_le.mp (e1.trans hy)
    obtain ⟨g1, g2⟩ := abs_le.mp (e2.trans hy)
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
  · apply difOn_zeta.diffContOnCl_ball
    intro y hy
    obtain ⟨-, -, p3, -⟩ := prox y hy
    simp only [mem_compl_iff, mem_singleton_iff]
    intro e
    rw [e, one_im] at p3
    linarith
  · intro y hy
    obtain ⟨p1, p2, p3, p4⟩ := prox y (sphere_subset_closedBall hy)
    exact hB y p1 p2 p3 p4

/-- Os centros `(s0 + hσ(2i+1)) + i(a + ht(2j+1))`. -/
noncomputable def centrosR (s0 hs a ht : ℚ) (ns nt : ℕ) : Finset ℂ :=
  ((Finset.range ns) ×ˢ (Finset.range nt)).image fun ij : ℕ × ℕ =>
    (((s0 + hs * (2 * (ij.1 : ℚ) + 1) : ℚ) : ℝ) : ℂ) + (((a + ht * (2 * (ij.2 : ℚ) + 1) : ℚ) : ℝ) : ℂ) * I

theorem cobre_ret {s0 hs a ht h : ℚ} {ns nt : ℕ} (hns : 1 ≤ ns) (hnt : 1 ≤ nt) (hhs : 0 < hs)
    (hht : 0 < ht) (hh0 : 0 ≤ h) (hh : hs ^ 2 + ht ^ 2 ≤ h ^ 2) {s1 b : ℝ}
    (hs1 : s1 ≤ (s0 : ℝ) + 2 * hs * ns) (hb : b ≤ (a : ℝ) + 2 * ht * nt) :
    ∀ z ∈ ret s0 s1 a b, ∃ c ∈ centrosR s0 hs a ht ns nt, ‖z - c‖ ≤ h := by
  intro z ⟨z1, z2, z3, z4⟩
  have hhs' : (0 : ℝ) < hs := by exact_mod_cast hhs
  have hht' : (0 : ℝ) < ht := by exact_mod_cast hht
  obtain ⟨i, hi, hzi⟩ := cobre hns hhs' hs1 z1 z2
  obtain ⟨j, hj, hzj⟩ := cobre hnt hht' hb z3 z4
  refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_product.mpr
    (show (i, j).1 ∈ Finset.range ns ∧ (i, j).2 ∈ Finset.range nt from
      ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩)), ?_⟩
  set c : ℂ := (((s0 + hs * (2 * (i : ℚ) + 1) : ℚ) : ℝ) : ℂ) +
    (((a + ht * (2 * (j : ℚ) + 1) : ℚ) : ℝ) : ℂ) * I
  have hcre : c.re = (s0 : ℝ) + hs * (2 * i + 1) := by simp [c]
  have hcim : c.im = (a : ℝ) + ht * (2 * j + 1) := by simp [c]
  have hsq : ‖z - c‖ ^ 2 ≤ (h : ℝ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, sub_re, sub_im, hcre, hcim]
    have e1 : (z.re - ((s0 : ℝ) + hs * (2 * i + 1))) * (z.re - ((s0 : ℝ) + hs * (2 * i + 1))) ≤
        (hs : ℝ) ^ 2 := by
      rw [← sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hzi 2
    have e2 : (z.im - ((a : ℝ) + ht * (2 * j + 1))) * (z.im - ((a : ℝ) + ht * (2 * j + 1))) ≤
        (ht : ℝ) ^ 2 := by
      rw [← sq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hzj 2
    have hh' : (hs : ℝ) ^ 2 + (ht : ℝ) ^ 2 ≤ (h : ℝ) ^ 2 := by exact_mod_cast hh
    linarith
  have hh0' : (0 : ℝ) ≤ h := by exact_mod_cast hh0
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hh0' (by norm_num)).mp hsq

theorem centrosR_ret {s0 hs a ht : ℚ} {ns nt : ℕ} (hhs : 0 ≤ hs) (hht : 0 ≤ ht) {s1 b : ℝ}
    (hs1 : (s0 : ℝ) + 2 * hs * ns ≤ s1) (hb : (a : ℝ) + 2 * ht * nt ≤ b) :
    ∀ c ∈ centrosR s0 hs a ht ns nt, c ∈ ret s0 s1 a b := by
  intro c hc
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
  have hi' : (i : ℝ) + 1 ≤ ns := by
    have := Finset.mem_range.mp hi
    exact_mod_cast this
  have hj' : (j : ℝ) + 1 ≤ nt := by
    have := Finset.mem_range.mp hj
    exact_mod_cast this
  have hhs' : (0 : ℝ) ≤ hs := by exact_mod_cast hhs
  have hht' : (0 : ℝ) ≤ ht := by exact_mod_cast hht
  simp only [ret, mem_ofPred_eq, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im,
    mul_zero, mul_one, sub_zero, zero_add, add_zero]
  push_cast
  have a1 : (0 : ℝ) ≤ hs * (2 * i + 1) := mul_nonneg hhs' (by positivity)
  have a2 : (hs : ℝ) * (2 * i + 1) ≤ 2 * hs * ns := by nlinarith
  have a3 : (0 : ℝ) ≤ ht * (2 * j + 1) := mul_nonneg hht' (by positivity)
  have a4 : (ht : ℝ) * (2 * j + 1) ≤ 2 * ht * nt := by nlinarith
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Verificação de todos os centros pelo kernel. -/
def chkR (N M K nT p : ℕ) (s0 hs a ht v : ℚ) (ns nt : ℕ) : Bool :=
  (List.range ns).all fun i : ℕ => (List.range nt).all fun j : ℕ =>
    okAllG N K nT p (s0 + hs * (2 * (i : ℚ) + 1)) (a + ht * (2 * (j : ℚ) + 1)) &&
      decide (v ^ 2 ≤ nMinSq (zetaIG N M K nT p (s0 + hs * (2 * (i : ℚ) + 1)) (a + ht * (2 * (j : ℚ) + 1))))

theorem chkR_spec {N M K nT p : ℕ} {s0 hs a ht v : ℚ} {ns nt : ℕ} (hN : 1 ≤ N) (hM1 : 1 ≤ M)
    (hM : M ≤ 10) (hs0 : 0 < s0) (hhs : 0 ≤ hs) (ha : 0 < a) (hht : 0 ≤ ht) (hv : 0 ≤ v)
    (hc : chkR N M K nT p s0 hs a ht v ns nt = true) :
    ∀ c ∈ centrosR s0 hs a ht ns nt, (v : ℝ) ≤ ‖riemannZeta c‖ := by
  intro c hcen
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hcen
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
  unfold chkR at hc
  rw [List.all_eq_true] at hc
  have h1 := hc i (List.mem_range.mpr (Finset.mem_range.mp hi))
  rw [List.all_eq_true] at h1
  have h2 := h1 j (List.mem_range.mpr (Finset.mem_range.mp hj))
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  obtain ⟨hok, hle⟩ := h2
  have hσ : 0 < s0 + hs * (2 * (i : ℚ) + 1) := by positivity
  have ht : a + ht * (2 * (j : ℚ) + 1) ≠ 0 := by positivity
  exact le_norm_de (mem_zetaIG hN hM1 hM hσ _ ht hok) hv hle

/-- **Uma peça retangular a partir de dados racionais.** -/
theorem peca_ret {s0 s1 a b r B hs ht h δ v R d : ℚ} {ns nt Nc Mc Ne Me K nT p : ℕ}
    (hr : 0 < r) (hrs : r < s0) (hra : r < a) (hns : 1 ≤ ns) (hnt : 1 ≤ nt) (hhs : 0 < hs)
    (hht : 0 < ht) (hs1 : s0 + 2 * hs * ns = s1) (hb : a + 2 * ht * nt = b) (hh0 : 0 ≤ h)
    (hh : hs ^ 2 + ht ^ 2 ≤ h ^ 2)
    (hR : (s1 + r) ^ 2 + (b + r) ^ 2 ≤ R ^ 2) (hR0 : 0 ≤ R) (hd0 : 0 < d) (hd : d ≤ a - r)
    (hNc : 1 ≤ Nc) (hMc : 2 ≤ Mc) (hMc10 : Mc ≤ 10) (hBq : cotaQ Nc Mc R d ≤ B) (hB0 : 0 ≤ B)
    (hv : B / r * h + δ = v) (hv0 : 0 ≤ v)
    (hNe : 1 ≤ Ne) (hMe : 1 ≤ Me) (hMe10 : Me ≤ 10) (hchk : chkR Ne Me K nT p s0 hs a ht v ns nt = true) :
    ∀ z ∈ ret s0 s1 a b, (δ : ℝ) ≤ ‖riemannZeta z‖ := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have castle : ∀ {x y : ℚ}, x ≤ y → (x : ℝ) ≤ y := fun h => by exact_mod_cast h
  have hB : ∀ w : ℂ, (s0 : ℝ) - r ≤ w.re → w.re ≤ (s1 : ℝ) + r → (a : ℝ) - r ≤ w.im →
      w.im ≤ (b : ℝ) + r → ‖riemannZeta w‖ ≤ (B : ℝ) := by
    intro w h1 h2 h3 h4
    have hR' : ((s1 : ℝ) + r) ^ 2 + ((b : ℝ) + r) ^ 2 ≤ (R : ℝ) ^ 2 := by
      have := castle hR
      push_cast at this
      exact this
    have hd' : (d : ℝ) ≤ (a : ℝ) - r := by
      have := castle hd
      push_cast at this
      exact this
    obtain ⟨p0, p1, p2, p3⟩ := reg_ret (by exact_mod_cast hrs) (by exact_mod_cast hra) hR'
      (by exact_mod_cast hR0) (by exact_mod_cast hd0) hd' h1 h2 h3 h4
    have hc := cota_geral hNc hMc p0 p1 p2 (by exact_mod_cast hd0) p3
    rw [← cotaQ_spec hMc10] at hc
    exact hc.trans (castle hBq)
  have hs1' : ((s0 : ℚ) : ℝ) + 2 * ((hs : ℚ) : ℝ) * ns = ((s1 : ℚ) : ℝ) := by
    rw [← hs1]; push_cast; ring
  have hb' : ((a : ℚ) : ℝ) + 2 * ((ht : ℚ) : ℝ) * nt = ((b : ℚ) : ℝ) := by
    rw [← hb]; push_cast; ring
  have hs0 : 0 < s0 := lt_trans hr hrs
  have ha : 0 < a := lt_trans hr hra
  have hval : ∀ c ∈ centrosR s0 hs a ht ns nt, (B : ℝ) / r * h + δ ≤ ‖riemannZeta c‖ := by
    intro c hc
    have := chkR_spec hNe hMe hMe10 hs0 hhs.le ha hht.le hv0 hchk c hc
    rw [← hv] at this
    push_cast at this
    exact this
  refine certificado_derivada (convex_ret s0 s1 a b) subset_rfl
    (centrosR_ret hhs.le hht.le hs1'.le hb'.le) (fun x hx => ?_)
    (fun x hx => deriv_cota_ret hr' (by exact_mod_cast hra) hB hx) (div_nonneg (by exact_mod_cast hB0) hr'.le)
    (cobre_ret hns hnt hhs hht hh0 hh hs1'.ge hb'.ge) hval
  apply differentiableAt_riemannZeta
  intro e
  have := hx.2.2.1
  rw [e, one_im] at this
  have : (0 : ℝ) < a := by exact_mod_cast ha
  linarith

/-! ## Divisões de retângulos -/

theorem ret_split_re {s0 sm s1 a b : ℝ} {P : ℂ → Prop} (hl : ∀ z ∈ ret s0 sm a b, P z)
    (hr : ∀ z ∈ ret sm s1 a b, P z) : ∀ z ∈ ret s0 s1 a b, P z := by
  intro z ⟨h1, h2, h3, h4⟩
  rcases le_total z.re sm with h | h
  · exact hl z ⟨h1, h, h3, h4⟩
  · exact hr z ⟨h, h2, h3, h4⟩

theorem ret_split_im {s0 s1 a tm b : ℝ} {P : ℂ → Prop} (hl : ∀ z ∈ ret s0 s1 a tm, P z)
    (hr : ∀ z ∈ ret s0 s1 tm b, P z) : ∀ z ∈ ret s0 s1 a b, P z := by
  intro z ⟨h1, h2, h3, h4⟩
  rcases le_total z.im tm with h | h
  · exact hl z ⟨h1, h2, h3, h⟩
  · exact hr z ⟨h1, h2, h, h4⟩

end ATK.ZeroClasses.Faixa

#print axioms ATK.ZeroClasses.Faixa.convex_ret
#print axioms ATK.ZeroClasses.Faixa.reg_ret
#print axioms ATK.ZeroClasses.Faixa.deriv_cota_ret
#print axioms ATK.ZeroClasses.Faixa.cobre_ret
#print axioms ATK.ZeroClasses.Faixa.centrosR_ret
#print axioms ATK.ZeroClasses.Faixa.chkR_spec
#print axioms ATK.ZeroClasses.Faixa.peca_ret
#print axioms ATK.ZeroClasses.Faixa.ret_split_re
#print axioms ATK.ZeroClasses.Faixa.ret_split_im
