import ATK.ZeroCertificado

/-!
# ATK — O terceiro zero, certificado e na linha crítica

Parte analítica da fase 3 (a avaliação certificada está em `ATK/ZeroCertificado.lean`):
cota grosseira, Cauchy, quociente de diferenças, contração, unicidade e simetria.
Mesmo método de `ATK/ZeroCritico.lean` (o primeiro zero), com `t₀ = 25,0108575801`, `N = 40` termos de
Euler–Maclaurin e a cota grosseira `|ζ| ≤ 420` em `|s − z₀| ≤ 2/5`.
Resultado: `zero_na_linha` e `terceiro_zero`.
-/

open Complex Metric Set

namespace ATK.ZeroCert3

open ATK.Cert ATK.EMGeral ATK.ZetaSimetria ATK.ZeroCert

/-! ## Constantes -/

/-- `t₀ = 25,0108575801`. -/
def t0 : ℚ := 250108575801 / 10 ^ 10
/-- Passo do quociente de diferenças. -/
def dl : ℚ := 1 / 10 ^ 5
/-- Raio da bola de contração. -/
def rr : ℚ := 1 / 10 ^ 6
/-- Cota de `|ζ''|`: `420/(19/100)²`. -/
def F2 : ℚ := 420 / (19 / 100) / (19 / 100)

noncomputable def z0 : ℂ := (1 / 2 : ℂ) + (((t0 : ℚ) : ℝ) : ℂ) * I
noncomputable def z1 : ℂ := (1 / 2 : ℂ) + (((t0 + dl : ℚ) : ℝ) : ℂ) * I

theorem z0_re : z0.re = 1 / 2 := by simp [z0]
theorem z0_im : z0.im = ((t0 : ℚ) : ℝ) := by simp [z0]
theorem z1_sub_z0 : z1 - z0 = (((dl : ℚ) : ℝ) : ℂ) * I := by
  simp only [z1, z0]; push_cast; ring

theorem t0_val : ((t0 : ℚ) : ℝ) = 250108575801 / 10 ^ 10 := by simp [t0]

/-! ## Centros e raios de retângulos -/

def cen (J : IR) : ℚ := (J.lo + J.hi) / 2
def rad (J : IR) : ℚ := (J.hi - J.lo) / 2
def radC (J : IC) : ℚ := rad J.re + rad J.im
noncomputable def cenC (J : IC) : ℂ := (((cen J.re : ℚ) : ℝ) : ℂ) + (((cen J.im : ℚ) : ℝ) : ℂ) * I

theorem abs_sub_cen {x : ℝ} {J : IR} (h : IR.mem x J) : |x - (cen J : ℝ)| ≤ (rad J : ℝ) := by
  obtain ⟨h1, h2⟩ := h
  unfold cen rad
  push_cast
  rw [abs_le]
  constructor <;> linarith

theorem norm_sub_cenC {z : ℂ} {J : IC} (h : IC.mem z J) : ‖z - cenC J‖ ≤ (radC J : ℝ) := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  have e1 : (z - cenC J).re = z.re - (cen J.re : ℝ) := by simp [cenC]
  have e2 : (z - cenC J).im = z.im - (cen J.im : ℝ) := by simp [cenC]
  rw [e1, e2]
  unfold radC
  push_cast
  exact add_le_add (abs_sub_cen h.1) (abs_sub_cen h.2)

theorem norm_cenC_le (J : IC) : ‖cenC J‖ ≤ |(cen J.re : ℝ)| + |(cen J.im : ℝ)| := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
  simp [cenC]

/-! ## Os dois retângulos e o certificado -/

def J0 : IC := zetaI 40 10 16 34 44 t0
def J1 : IC := zetaI 40 10 16 34 44 (t0 + dl)

/-- `c = (A₁ − A₀)/(iδ)` em racionais: `(v/δ, −u/δ)`. -/
def cQ : ℚ × ℚ := ((cen J1.im - cen J0.im) / dl, -(cen J1.re - cen J0.re) / dl)

/-- **O certificado** (verificado pelo kernel). -/
def cert : Bool :=
  okAll 40 16 34 44 t0 && okAll 40 16 34 44 (t0 + dl) &&
    decide (0 < cQ.1 ∧ (radC J0 + radC J1) / dl + F2 * (dl + rr) ≤ cQ.1 / 2 ∧
      |cen J0.re| + |cen J0.im| + radC J0 ≤ rr * cQ.1 / 2)

set_option maxRecDepth 100000 in
theorem cert_ok : cert = true := by decide +kernel

theorem cert_parts : okAll 40 16 34 44 t0 = true ∧ okAll 40 16 34 44 (t0 + dl) = true ∧
    (0 < cQ.1 ∧ (radC J0 + radC J1) / dl + F2 * (dl + rr) ≤ cQ.1 / 2 ∧
      |cen J0.re| + |cen J0.im| + radC J0 ≤ rr * cQ.1 / 2) := by
  have h := cert_ok
  simp only [cert, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem mem_J0 : IC.mem (riemannZeta z0) J0 :=
  mem_zetaI (by norm_num) (by norm_num) (by norm_num) t0 cert_parts.1

theorem mem_J1 : IC.mem (riemannZeta z1) J1 :=
  mem_zetaI (by norm_num) (by norm_num) (by norm_num) (t0 + dl) cert_parts.2.1

/-! ## Geometria do disco -/

theorem re_im_prox {w : ℂ} {R : ℝ} (hw : w ∈ closedBall z0 R) :
    |w.re - 1 / 2| ≤ R ∧ |w.im - ((t0 : ℚ) : ℝ)| ≤ R := by
  rw [mem_closedBall, dist_eq_norm] at hw
  constructor
  · have := Complex.abs_re_le_norm (w - z0)
    rw [sub_re, z0_re] at this
    linarith
  · have := Complex.abs_im_le_norm (w - z0)
    rw [sub_im, z0_im] at this
    linarith

theorem ne_um {w : ℂ} (hw : w ∈ closedBall z0 (2 / 5)) : w ≠ 1 := by
  intro h
  have := (re_im_prox hw).2
  rw [h, t0_val] at this
  simp at this
  rw [abs_le] at this
  linarith [this.1]

theorem bola_sub {a b : ℝ} {w x : ℂ} (hw : w ∈ closedBall z0 a) (hx : x ∈ closedBall w b) :
    x ∈ closedBall z0 (a + b) := by
  rw [mem_closedBall] at *
  calc dist x z0 ≤ dist x w + dist w z0 := dist_triangle _ _ _
    _ ≤ b + a := add_le_add hx hw
    _ = a + b := by ring

theorem sub_bola {u : ℂ} {a : ℝ} (ha : a ≤ 2 / 5) (hu : u ∈ closedBall z0 a) :
    u ∈ closedBall z0 (2 / 5) :=
  closedBall_subset_closedBall ha hu

/-! ## Cota grosseira `|ζ| ≤ 420` em `|s − z₀| ≤ 2/5` -/

theorem EM_um (w : ℂ) : EM 1 1 w = 1 / 2 + 1 / (w - 1) := by
  simp [EM, Complex.one_cpow]
  ring

theorem Cb_um : Cb 1 = 3 / 2 := by
  have := CbR_spec 1 (by norm_num) 2 (by norm_num)
  rw [show Cb 1 = ∑ i ∈ Finset.range 2, |(bernoulli i : ℝ)| * ((Nat.choose 1 i : ℕ) : ℝ) from rfl,
    ← this]
  norm_num [CbR, Btab]

theorem cota_grosseira {w : ℂ} (hw : w ∈ closedBall z0 (2 / 5)) : ‖riemannZeta w‖ ≤ 420 := by
  obtain ⟨hre, him⟩ := re_im_prox hw
  rw [t0_val] at him
  rw [abs_le] at hre him
  have hσ : 1 / 10 ≤ w.re := by linarith [hre.1]
  have hσ0 : 0 < w.re := by linarith
  have hτ : 24 ≤ w.im := by linarith [him.1]
  have hw1 := ne_um hw
  have hE := norm_zeta_sub_EM_le hσ0 hw1 le_rfl le_rfl
  have hpoch : poch w 1 = w := by simp [poch]
  rw [hpoch, Cb_um, EM_um] at hE
  simp only [Nat.factorial_one, Nat.cast_one, div_one, Real.one_rpow] at hE
  have hnw : ‖w‖ ≤ 27 := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [abs_of_pos hσ0, abs_of_pos (by linarith : (0 : ℝ) < w.im)]
    linarith [hre.2, him.2]
  have hw1n : 1 ≤ ‖w - 1‖ := by
    have := Complex.abs_im_le_norm (w - 1)
    simp only [sub_im, one_im, sub_zero] at this
    rw [abs_of_pos (by linarith : (0 : ℝ) < w.im)] at this
    linarith
  have hinv : ‖1 / (w - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr hw1n
  have hEM : ‖1 / 2 + 1 / (w - 1)‖ ≤ 3 / 2 := by
    refine (norm_add_le _ _).trans ?_
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    linarith
  have hfr : ‖w‖ * (3 / 2 * 1 / (w.re + 1 - 1)) ≤ 27 * 15 := by
    rw [show w.re + 1 - 1 = w.re by ring]
    have h1 : 3 / 2 * 1 / w.re ≤ 15 := by
      rw [div_le_iff₀ hσ0]; linarith
    have h2 : 0 ≤ 3 / 2 * 1 / w.re := by positivity
    exact mul_le_mul hnw h1 h2 (by norm_num)
  have htri : ‖riemannZeta w‖ ≤ ‖riemannZeta w - (1 / 2 + 1 / (w - 1))‖ + ‖1 / 2 + 1 / (w - 1)‖ := by
    have := norm_add_le (riemannZeta w - (1 / 2 + 1 / (w - 1))) (1 / 2 + 1 / (w - 1))
    rwa [sub_add_cancel] at this
  linarith

/-! ## Cauchy: `|ζ'|` e `|ζ''|` -/

theorem difOn_zeta : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun _ hs =>
  (differentiableAt_riemannZeta hs).differentiableWithinAt

theorem difOn_dzeta : DifferentiableOn ℂ (deriv riemannZeta) {1}ᶜ :=
  difOn_zeta.deriv isOpen_compl_singleton

theorem cota_deriv {w : ℂ} (hw : w ∈ closedBall z0 (21 / 100)) :
    ‖deriv riemannZeta w‖ ≤ 420 / (19 / 100) := by
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num)
  · apply difOn_zeta.diffContOnCl_ball
    intro x hx
    have := bola_sub hw hx
    exact ne_um (by convert this using 1; norm_num)
  · intro x hx
    apply cota_grosseira
    have := bola_sub hw (sphere_subset_closedBall hx)
    convert this using 1; norm_num

theorem cota_deriv2 {z : ℂ} (hz : z ∈ closedBall z0 (1 / 50)) :
    ‖deriv (deriv riemannZeta) z‖ ≤ (F2 : ℝ) := by
  have hF : ((F2 : ℚ) : ℝ) = 420 / (19 / 100) / (19 / 100) := by simp [F2]
  rw [hF]
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num)
  · apply difOn_dzeta.diffContOnCl_ball
    intro x hx
    exact ne_um (sub_bola (by norm_num) (bola_sub hz hx))
  · intro x hx
    apply cota_deriv
    have := bola_sub hz (sphere_subset_closedBall hx)
    convert this using 1; norm_num

theorem dif_at {u : ℂ} (hu : u ∈ closedBall z0 (2 / 5)) : DifferentiableAt ℂ riemannZeta u :=
  differentiableAt_riemannZeta (ne_um hu)

theorem dif_at' {u : ℂ} (hu : u ∈ closedBall z0 (2 / 5)) :
    DifferentiableAt ℂ (deriv riemannZeta) u :=
  difOn_dzeta.differentiableAt (isOpen_compl_singleton.mem_nhds (ne_um hu))

/-- `ζ'` é `F₂`-Lipschitz em `|s − z₀| ≤ 1/50`. -/
theorem lip_deriv {x y : ℂ} (hx : x ∈ closedBall z0 (1 / 50)) (hy : y ∈ closedBall z0 (1 / 50)) :
    ‖deriv riemannZeta y - deriv riemannZeta x‖ ≤ (F2 : ℝ) * ‖y - x‖ :=
  (convex_closedBall z0 (1 / 50)).norm_image_sub_le_of_norm_deriv_le
    (fun u hu => dif_at' (sub_bola (by norm_num) hu)) (fun u hu => cota_deriv2 hu) hx hy

/-! ## Quociente de diferenças -/

theorem dl_pos : (0 : ℝ) < ((dl : ℚ) : ℝ) := by simp [dl]

theorem norm_z1_sub : ‖z1 - z0‖ = ((dl : ℚ) : ℝ) := by
  rw [z1_sub_z0, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos dl_pos]

theorem z1_mem {a : ℝ} (ha : ((dl : ℚ) : ℝ) ≤ a) : z1 ∈ closedBall z0 a := by
  rw [mem_closedBall, dist_eq_norm, norm_z1_sub]; exact ha

theorem dl_le : ((dl : ℚ) : ℝ) ≤ 1 / 50 := by simp [dl]; norm_num

/-- `|ζ(z₁) − ζ(z₀) − (z₁ − z₀)ζ'(z₀)| ≤ F₂ δ |z₁ − z₀|`. -/
theorem dq_le : ‖riemannZeta z1 - riemannZeta z0 - (z1 - z0) * deriv riemannZeta z0‖ ≤
    (F2 : ℝ) * ((dl : ℚ) : ℝ) * ‖z1 - z0‖ := by
  set c := deriv riemannZeta z0
  set φ : ℂ → ℂ := fun u => riemannZeta u - u * c with hφ
  have hd : ∀ u ∈ closedBall z0 ((dl : ℚ) : ℝ), HasDerivAt φ (deriv riemannZeta u - c) u := by
    intro u hu
    have h1 := (dif_at (sub_bola (dl_le.trans (by norm_num)) hu)).hasDerivAt
    have h2 := (hasDerivAt_id u).mul_const c
    have h3 : HasDerivAt (fun u => riemannZeta u - u * c) (deriv riemannZeta u - 1 * c) u :=
      h1.sub h2
    rw [one_mul] at h3
    exact h3
  have hb : ∀ u ∈ closedBall z0 ((dl : ℚ) : ℝ), ‖deriv φ u‖ ≤ (F2 : ℝ) * ((dl : ℚ) : ℝ) := by
    intro u hu
    rw [(hd u hu).deriv]
    have hu' : u ∈ closedBall z0 (1 / 50) := closedBall_subset_closedBall dl_le hu
    have hz0 : z0 ∈ closedBall z0 (1 / 50) := mem_closedBall_self (by norm_num)
    have := lip_deriv hz0 hu'
    rw [mem_closedBall, dist_eq_norm] at hu
    have hF : (0 : ℝ) ≤ (F2 : ℝ) := by simp [F2]; norm_num
    calc ‖deriv riemannZeta u - c‖ ≤ (F2 : ℝ) * ‖u - z0‖ := this
      _ ≤ (F2 : ℝ) * ((dl : ℚ) : ℝ) := mul_le_mul_of_nonneg_left hu hF
  have hm := (convex_closedBall z0 ((dl : ℚ) : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (hd u hu).differentiableAt) hb (mem_closedBall_self dl_pos.le) (z1_mem le_rfl)
  have e : φ z1 - φ z0 = riemannZeta z1 - riemannZeta z0 - (z1 - z0) * c := by
    simp only [hφ]; ring
  rw [e] at hm
  exact hm

/-! ## A constante `c` e a derivada -/

noncomputable def cC : ℂ := (((cQ.1 : ℚ) : ℝ) : ℂ) + (((cQ.2 : ℚ) : ℝ) : ℂ) * I

theorem cC_mul : cC * (z1 - z0) = cenC J1 - cenC J0 := by
  rw [z1_sub_z0]
  simp only [cC, cenC, cQ, dl]
  push_cast
  linear_combination (-(((cen J1.re : ℚ) : ℂ) - ((cen J0.re : ℚ) : ℂ))) * I_sq

theorem cC_re : cC.re = ((cQ.1 : ℚ) : ℝ) := by simp [cC]

theorem cC_norm_ge : ((cQ.1 : ℚ) : ℝ) ≤ ‖cC‖ := cC_re ▸ Complex.re_le_norm cC

theorem cQ1_pos : (0 : ℝ) < ((cQ.1 : ℚ) : ℝ) := by exact_mod_cast cert_parts.2.2.1

theorem cC_ne : cC ≠ 0 := by
  intro h
  have := cC_norm_ge
  rw [h, norm_zero] at this
  linarith [cQ1_pos]

/-- `|ζ'(z₀) − c| ≤ F₂δ + (r₀ + r₁)/δ`. -/
theorem deriv_menos_c : ‖deriv riemannZeta z0 - cC‖ ≤
    (F2 : ℝ) * ((dl : ℚ) : ℝ) + ((radC J0 : ℝ) + (radC J1 : ℝ)) / ((dl : ℚ) : ℝ) := by
  have hz : z1 - z0 ≠ 0 := by
    intro h; have := norm_z1_sub; rw [h, norm_zero] at this; linarith [dl_pos]
  have hn := norm_z1_sub
  have key : deriv riemannZeta z0 - cC =
      -((riemannZeta z1 - riemannZeta z0 - (z1 - z0) * deriv riemannZeta z0) / (z1 - z0)) +
        ((riemannZeta z1 - cenC J1) - (riemannZeta z0 - cenC J0)) / (z1 - z0) := by
    have := cC_mul
    field_simp
    linear_combination (-1 : ℂ) * this
  rw [key]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg, norm_div, norm_div, hn]
  have h1 : ‖riemannZeta z1 - riemannZeta z0 - (z1 - z0) * deriv riemannZeta z0‖ /
      ((dl : ℚ) : ℝ) ≤ (F2 : ℝ) * ((dl : ℚ) : ℝ) := by
    rw [div_le_iff₀ dl_pos]
    have := dq_le
    rw [hn] at this
    linarith
  have h2 : ‖(riemannZeta z1 - cenC J1) - (riemannZeta z0 - cenC J0)‖ ≤
      (radC J1 : ℝ) + (radC J0 : ℝ) :=
    (norm_sub_le _ _).trans (add_le_add (norm_sub_cenC mem_J1) (norm_sub_cenC mem_J0))
  have h3 : ‖(riemannZeta z1 - cenC J1) - (riemannZeta z0 - cenC J0)‖ / ((dl : ℚ) : ℝ) ≤
      ((radC J0 : ℝ) + (radC J1 : ℝ)) / ((dl : ℚ) : ℝ) := by
    apply div_le_div_of_nonneg_right _ dl_pos.le
    linarith
  linarith

/-! ## Contração -/

noncomputable def g (z : ℂ) : ℂ := z - riemannZeta z / cC

theorem rr_le : ((rr : ℚ) : ℝ) ≤ 1 / 50 := by simp [rr]; norm_num

theorem rr_pos : (0 : ℝ) < ((rr : ℚ) : ℝ) := by simp [rr]

theorem B_sub {z : ℂ} (hz : z ∈ closedBall z0 ((rr : ℚ) : ℝ)) : z ∈ closedBall z0 (1 / 50) :=
  closedBall_subset_closedBall rr_le hz

theorem hasDerivAt_g {z : ℂ} (hz : z ∈ closedBall z0 (2 / 5)) :
    HasDerivAt g (1 - deriv riemannZeta z / cC) z := by
  have h := ((dif_at hz).hasDerivAt.div_const cC)
  exact (hasDerivAt_id z).sub h

theorem norm_deriv_g {z : ℂ} (hz : z ∈ closedBall z0 ((rr : ℚ) : ℝ)) : ‖deriv g z‖ ≤ 1 / 2 := by
  have hz' := B_sub hz
  rw [(hasDerivAt_g (sub_bola (by norm_num) hz')).deriv]
  have hc := cert_parts.2.2.2.1
  have hc' : ((radC J0 : ℝ) + (radC J1 : ℝ)) / ((dl : ℚ) : ℝ) + (F2 : ℝ) * (((dl : ℚ) : ℝ) +
      ((rr : ℚ) : ℝ)) ≤ ((cQ.1 : ℚ) : ℝ) / 2 := by exact_mod_cast hc
  have e : 1 - deriv riemannZeta z / cC = (cC - deriv riemannZeta z) / cC := by
    field_simp [cC_ne]
  rw [e, norm_div]
  have hcn := cC_norm_ge
  have hcpos : 0 < ‖cC‖ := lt_of_lt_of_le cQ1_pos hcn
  rw [div_le_iff₀ hcpos]
  have hl := lip_deriv (mem_closedBall_self (by norm_num)) hz'
  have hzr : ‖z - z0‖ ≤ ((rr : ℚ) : ℝ) := by rwa [mem_closedBall, dist_eq_norm] at hz
  have hF : (0 : ℝ) ≤ (F2 : ℝ) := by simp [F2]; norm_num
  have hdz := deriv_menos_c
  have : ‖cC - deriv riemannZeta z‖ ≤
      ‖deriv riemannZeta z - deriv riemannZeta z0‖ + ‖deriv riemannZeta z0 - cC‖ := by
    rw [norm_sub_rev cC]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h4 : ‖deriv riemannZeta z - deriv riemannZeta z0‖ ≤ (F2 : ℝ) * ((rr : ℚ) : ℝ) :=
    hl.trans (mul_le_mul_of_nonneg_left hzr hF)
  nlinarith

theorem lip_g : LipschitzOnWith (1 / 2) g (closedBall z0 ((rr : ℚ) : ℝ)) := by
  apply (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_deriv_le
  · intro u hu
    exact (hasDerivAt_g (sub_bola (by norm_num) (B_sub hu))).differentiableAt
  · intro u hu
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    have := norm_deriv_g hu
    simpa using this

theorem g_z0 : ‖g z0 - z0‖ ≤ ((rr : ℚ) : ℝ) / 2 := by
  have e : g z0 - z0 = -(riemannZeta z0 / cC) := by simp [g]
  rw [e, norm_neg, norm_div]
  have hcn := cC_norm_ge
  have hcpos : 0 < ‖cC‖ := lt_of_lt_of_le cQ1_pos hcn
  rw [div_le_iff₀ hcpos]
  have h3 := cert_parts.2.2.2.2
  have h3' : |((cen J0.re : ℚ) : ℝ)| + |((cen J0.im : ℚ) : ℝ)| + (radC J0 : ℝ) ≤
      ((rr : ℚ) : ℝ) * ((cQ.1 : ℚ) : ℝ) / 2 := by exact_mod_cast h3
  have hz : ‖riemannZeta z0‖ ≤ ‖cenC J0‖ + (radC J0 : ℝ) := by
    have := norm_sub_cenC mem_J0
    calc ‖riemannZeta z0‖ = ‖(riemannZeta z0 - cenC J0) + cenC J0‖ := by ring_nf
      _ ≤ ‖riemannZeta z0 - cenC J0‖ + ‖cenC J0‖ := norm_add_le _ _
      _ ≤ (radC J0 : ℝ) + ‖cenC J0‖ := by linarith
      _ = ‖cenC J0‖ + (radC J0 : ℝ) := by ring
  have hc0 := norm_cenC_le J0
  have hr := rr_pos
  nlinarith

theorem g_maps : MapsTo g (closedBall z0 ((rr : ℚ) : ℝ)) (closedBall z0 ((rr : ℚ) : ℝ)) := by
  intro z hz
  have hz0 : z0 ∈ closedBall z0 ((rr : ℚ) : ℝ) := mem_closedBall_self rr_pos.le
  have hl := lip_g.dist_le_mul z hz z0 hz0
  rw [mem_closedBall] at hz ⊢
  have h1 : dist (g z0) z0 ≤ ((rr : ℚ) : ℝ) / 2 := by rw [dist_eq_norm]; exact g_z0
  calc dist (g z) z0 ≤ dist (g z) (g z0) + dist (g z0) z0 := dist_triangle _ _ _
    _ ≤ (1 / 2 : NNReal) * dist z z0 + ((rr : ℚ) : ℝ) / 2 := add_le_add hl h1
    _ ≤ (1 / 2 : ℝ) * ((rr : ℚ) : ℝ) + ((rr : ℚ) : ℝ) / 2 := by
        push_cast; gcongr
    _ = ((rr : ℚ) : ℝ) := by ring

/-- Ponto fixo de `g` ⟺ zero de `ζ`. -/
theorem fixo_iff (z : ℂ) : g z = z ↔ riemannZeta z = 0 := by
  unfold g
  constructor
  · intro h
    have : riemannZeta z / cC = 0 := by linear_combination -h
    rcases div_eq_zero_iff.mp this with h' | h'
    · exact h'
    · exact absurd h' cC_ne
  · intro h; rw [h]; simp

/-! ## O zero -/

theorem torcao_z0 : torcao z0 = z0 := (torcao_fixo_iff z0).mpr z0_re

theorem torcao_bola {y : ℂ} {R : ℝ} (hy : y ∈ closedBall z0 R) : torcao y ∈ closedBall z0 R := by
  rw [mem_closedBall, dist_eq_norm] at hy ⊢
  have e : torcao y - z0 = -(starRingEnd ℂ) (y - z0) := by
    conv_lhs => rw [← torcao_z0]
    unfold torcao
    simp only [map_sub]
    ring
  rw [e, norm_neg, Complex.norm_conj]
  exact hy

/-- **Existe um zero não trivial de `ζ` na linha crítica**, a menos de `10⁻⁶` de
`½ + 25,0108575801 i`, e ele é o único zero nesse disco. -/
theorem zero_na_linha : ∃ ρ ∈ Z, ρ.re = 1 / 2 ∧ ρ ∈ closedBall z0 ((rr : ℚ) : ℝ) ∧
    ∀ w ∈ closedBall z0 ((rr : ℚ) : ℝ), riemannZeta w = 0 → w = ρ := by
  set B := closedBall z0 ((rr : ℚ) : ℝ)
  have hz0 : z0 ∈ B := mem_closedBall_self rr_pos.le
  have hK : ContractingWith (1 / 2) (g_maps.restrict g B B) :=
    ⟨by rw [← NNReal.coe_lt_coe]; norm_num,
      lip_g.mapsToRestrict g_maps⟩
  obtain ⟨y, hyB, hyfix, -⟩ := hK.exists_fixedPoint' isClosed_closedBall.isComplete g_maps hz0
    (edist_ne_top _ _)
  have hy0 : riemannZeta y = 0 := (fixo_iff y).mp hyfix
  have uniq : ∀ w ∈ B, riemannZeta w = 0 → w = y := by
    intro w hw hw0
    have hwf := (fixo_iff w).mpr hw0
    have hl := lip_g.dist_le_mul w hw y hyB
    rw [hwf, show g y = y from hyfix] at hl
    have : dist w y = 0 := by
      have := dist_nonneg (x := w) (y := y)
      push_cast at hl
      linarith
    exact dist_eq_zero.mp this
  have hyZ : y ∈ Z := by
    obtain ⟨hre, -⟩ := re_im_prox hyB
    rw [abs_le] at hre
    have := rr_le
    exact ⟨hy0, by linarith [hre.1], by linarith [hre.2]⟩
  have htZ := torcao_mem_Z hyZ
  have ht : torcao y = y := uniq _ (torcao_bola hyB) htZ.1
  exact ⟨y, hyZ, (torcao_fixo_iff y).mp ht, hyB, uniq⟩

/-- **`Z` não é vazio** (incondicional). -/
theorem Z_nao_vazio : ∃ ρ, ρ ∈ Z := by
  obtain ⟨ρ, hρ, -⟩ := zero_na_linha
  exact ⟨ρ, hρ⟩

/-- Forma explícita: `ρ = ½ + iγ` com `|γ − 25,0108575801| ≤ 10⁻⁶`. -/
theorem terceiro_zero : ∃ γ : ℝ, riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * I) = 0 ∧
    |γ - 250108575801 / 10 ^ 10| ≤ 1 / 10 ^ 6 := by
  obtain ⟨ρ, hρ, hre, hB, -⟩ := zero_na_linha
  refine ⟨ρ.im, ?_, ?_⟩
  · have e : (1 / 2 : ℂ) + (ρ.im : ℂ) * I = ρ := by
      apply Complex.ext <;> simp [hre]
    rw [e]; exact hρ.1
  · have := (re_im_prox hB).2
    rw [t0_val] at this
    have hr : ((rr : ℚ) : ℝ) = 1 / 10 ^ 6 := by simp [rr]
    rw [hr] at this
    exact this

end ATK.ZeroCert3

-- Auditoria de axiomas (kernel)
#print axioms ATK.ZeroCert3.cert_ok
#print axioms ATK.ZeroCert3.mem_J0
#print axioms ATK.ZeroCert3.mem_J1
#print axioms ATK.ZeroCert3.cota_grosseira
#print axioms ATK.ZeroCert3.cota_deriv
#print axioms ATK.ZeroCert3.cota_deriv2
#print axioms ATK.ZeroCert3.lip_deriv
#print axioms ATK.ZeroCert3.dq_le
#print axioms ATK.ZeroCert3.deriv_menos_c
#print axioms ATK.ZeroCert3.norm_deriv_g
#print axioms ATK.ZeroCert3.lip_g
#print axioms ATK.ZeroCert3.g_maps
#print axioms ATK.ZeroCert3.fixo_iff
#print axioms ATK.ZeroCert3.torcao_bola
#print axioms ATK.ZeroCert3.zero_na_linha
#print axioms ATK.ZeroCert3.Z_nao_vazio
#print axioms ATK.ZeroCert3.terceiro_zero
