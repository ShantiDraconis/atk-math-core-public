import ATK.ZeroClasses.QuartoGeral

/-!
# `m₄ > 0`: o primeiro ponto aberto do `FinalAudit`, fechado no kernel (rodada 28)

`K₄ = {¼ + it : ¼ ≤ t ≤ 4}` e `m₄ = inf_{K₄} |ζ|`. O `FinalAudit` registrava `m₄ > 0` como o primeiro ponto em
que uma prova incondicional não se completava (BUILD_PENDING, afirmação finita). Aqui ele é **provado**:

* `peca_cert`: uma peça `seg a b` é certificada por dados racionais — cota grosseira `cotaQ ≤ B` na região
  `|Re w − ¼| ≤ r`, `a − r ≤ Im w ≤ b + r`; Cauchy dá `‖ζ′‖ ≤ B/r` no segmento; `n` centros com passo
  `h = (b − a)/(2n)` e, em cada um, o retângulo certificado de `ζ(¼ + it)` com norma `≥ (B/r)h + δ`;
* `peca1`–`peca4`: as quatro peças `[¼, 1]`, `[1, 2]`, `[2, 3]`, `[3, 4]` (`r = 6/25`, `δ = 1/20`; 20 + 27 + 24 + 24
  = 95 centros, todos verificados pelo kernel com `decide +kernel`);
* **`cota_K4`: `|ζ(s)| ≥ 1/20` em todo `K₄`**; **`m4_cota`: `m₄ ≥ 1/20`**; `m4_pos`; `K4_sem_zeros`;
* `m4_menor_um`: `m₄ < 1` (pelo retângulo em `¼ + 2i`); numericamente `m₄ ≈ 0,4611` em `t ≈ 2,175`;
* `espelho_sem_zeros`: pela torção `s ↦ 1 − s̄`, também `ζ(¾ + it) ≠ 0` para `¼ ≤ t ≤ 4`;
* `novo_primeiro_ponto`: o primeiro ponto aberto passa a ser `m₅ > 0` (`K₅ = [⅕, 3/10] × [⅕, 5]`), com
  `m₅ > 0 ⟺ ζ` sem zeros em `K₅`, e `RH ⟹ m₅ > 0`.

Classificação: **parcial** (classe 3) — um pedaço finito de RH provado sem hipótese. Não é RH: o universal
`∀ n ≥ 4, m_n > 0` continua equivalente a RH.
-/

open Complex Metric Set

namespace ATK.ZeroClasses.Quarto

open ATK.Cert ATK.EMGeral ATK.ZeroCert ATK.ZeroClasses.Regions

/-! ## 9. O certificado de uma peça a partir de dados racionais -/

theorem peca_cert {a b r B h δ v R d : ℚ} {n Nc Mc Ne Me K nT p : ℕ}
    (hr : 0 < r) (hr4 : r < 1 / 4) (ha : r ≤ a) (hn : 1 ≤ n) (hh : 0 < h) (hab : a + 2 * h * n = b)
    (hR : (1 / 4 + r) ^ 2 + (b + r) ^ 2 ≤ R ^ 2) (hR0 : 0 ≤ R) (hd0 : 0 < d)
    (hdd : d ^ 2 ≤ (3 / 4 - r) ^ 2 + (a - r) ^ 2)
    (hNc : 1 ≤ Nc) (hMc : 2 ≤ Mc) (hMc10 : Mc ≤ 10) (hBq : cotaQ Nc Mc R d ≤ B) (hB0 : 0 ≤ B)
    (hv : B / r * h + δ = v) (hv0 : 0 ≤ v)
    (hNe : 1 ≤ Ne) (hMe : 1 ≤ Me) (hMe10 : Me ≤ 10) (hchk : chk Ne Me K nT p a h v n = true) :
    ∀ z ∈ seg a b, (δ : ℝ) ≤ ‖riemannZeta z‖ := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hr4' : (r : ℝ) < 1 / 4 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hr4
    push_cast at this
    exact this
  have hB : ∀ w : ℂ, |w.re - 1 / 4| ≤ (r : ℝ) → (a : ℝ) - r ≤ w.im → w.im ≤ (b : ℝ) + r →
      ‖riemannZeta w‖ ≤ (B : ℝ) := by
    intro w h1 h2 h3
    have hR' : (1 / 4 + (r : ℝ)) ^ 2 + ((b : ℝ) + r) ^ 2 ≤ (R : ℝ) ^ 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr hR
      push_cast at this
      exact this
    have hdd' : (d : ℝ) ^ 2 ≤ (3 / 4 - (r : ℝ)) ^ 2 + ((a : ℝ) - r) ^ 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr hdd
      push_cast at this
      exact this
    obtain ⟨p0, p1, p2, p3⟩ := reg_props hr4' (by exact_mod_cast ha) hR' (by exact_mod_cast hR0)
      (by exact_mod_cast hd0) hdd' h1 h2 h3
    have hc := cota_geral hNc hMc p0 p1 p2 (by exact_mod_cast hd0) p3
    rw [← cotaQ_spec hMc10] at hc
    exact hc.trans (by exact_mod_cast hBq)
  have hb : ((a : ℚ) : ℝ) + 2 * ((h : ℚ) : ℝ) * n = ((b : ℚ) : ℝ) := by
    rw [← hab]
    push_cast
    ring
  have hval : ∀ c ∈ centros a h n, (B : ℝ) / r * h + δ ≤ ‖riemannZeta c‖ := by
    intro c hc
    have := chk_spec hNe hMe hMe10 hv0 hchk c hc
    rw [← hv] at this
    push_cast at this
    exact this
  exact peca hr' hr4' (by exact_mod_cast hB0) hB (centros_seg hh.le hb.le) (cobre_seg hn hh hb.ge) hval

/-! ## 10. As quatro peças -/

set_option maxRecDepth 100000 in
/-- **`[¼, 1]`**: 20 centros. -/
theorem peca1 : ∀ z ∈ seg (1 / 4) 1, ((1 / 20 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ := by
  have := peca_cert (a := 1 / 4) (b := 1) (r := 6 / 25) (B := 611 / 100) (h := 3 / 160) (δ := 1 / 20)
    (v := 611 / 100 / (6 / 25) * (3 / 160) + 1 / 20) (R := 667 / 500) (d := 51 / 100) (n := 20)
    (Nc := 1) (Mc := 4) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  simpa using this

set_option maxRecDepth 100000 in
/-- **`[1, 2]`**: 27 centros. -/
theorem peca2 : ∀ z ∈ seg 1 2, ((1 / 20 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ := by
  have := peca_cert (a := 1) (b := 2) (r := 6 / 25) (B := 491 / 100) (h := 1 / 54) (δ := 1 / 20)
    (v := 491 / 100 / (6 / 25) * (1 / 54) + 1 / 20) (R := 2293 / 1000) (d := 183 / 200) (n := 27)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  simpa using this

set_option maxRecDepth 100000 in
/-- **`[2, 3]`**: 24 centros. -/
theorem peca3 : ∀ z ∈ seg 2 3, ((1 / 20 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ := by
  have := peca_cert (a := 2) (b := 3) (r := 6 / 25) (B := 87 / 20) (h := 1 / 48) (δ := 1 / 20)
    (v := 87 / 20 / (6 / 25) * (1 / 48) + 1 / 20) (R := 3277 / 1000) (d := 229 / 125) (n := 24)
    (Nc := 2) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  simpa using this

set_option maxRecDepth 100000 in
/-- **`[3, 4]`**: 24 centros. -/
theorem peca4 : ∀ z ∈ seg 3 4, ((1 / 20 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ := by
  have := peca_cert (a := 3) (b := 4) (r := 6 / 25) (B := 119 / 25) (h := 1 / 48) (δ := 1 / 20)
    (v := 119 / 25 / (6 / 25) * (1 / 48) + 1 / 20) (R := 4269 / 1000) (d := 1403 / 500) (n := 24)
    (Nc := 3) (Mc := 10) (Ne := 6) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel) (by norm_num) rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by decide +kernel)
  simpa using this

/-! ## 11. `K₄`, `m₄` e o novo primeiro ponto aberto -/

theorem K4_eq : K 4 = seg (1 / 4) 4 := by
  ext s
  simp only [K, seg, mem_ofPred_eq]
  push_cast
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **`|ζ(s)| ≥ 1/20` em todo `K₄`.** -/
theorem cota_K4 : ∀ s ∈ K 4, (1 / 20 : ℝ) ≤ ‖riemannZeta s‖ := by
  rw [K4_eq]
  rintro s ⟨h1, h2, h3⟩
  have e : ((1 / 20 : ℚ) : ℝ) = 1 / 20 := by norm_num
  rw [← e]
  rcases le_total s.im 1 with c1 | c1
  · exact peca1 s ⟨h1, h2, c1⟩
  rcases le_total s.im 2 with c2 | c2
  · exact peca2 s ⟨h1, by exact_mod_cast c1, by exact_mod_cast c2⟩
  rcases le_total s.im 3 with c3 | c3
  · exact peca3 s ⟨h1, by exact_mod_cast c2, by exact_mod_cast c3⟩
  · exact peca4 s ⟨h1, by exact_mod_cast c3, by exact_mod_cast h3⟩

/-- **`m₄ ≥ 1/20`.** -/
theorem m4_cota : (1 / 20 : ℝ) ≤ m 4 :=
  le_csInf ((K_nonempty le_rfl).image _) (by rintro _ ⟨w, hw, rfl⟩; exact cota_K4 w hw)

theorem m4_pos : 0 < m 4 := lt_of_lt_of_le (by norm_num) m4_cota

/-- **`ζ` não se anula em `K₄`.** -/
theorem K4_sem_zeros : ∀ s ∈ K 4, riemannZeta s ≠ 0 := (m_pos_iff le_rfl).mp m4_pos

set_option maxRecDepth 100000 in
/-- **`m₄ < 1`**, pelo retângulo certificado de `ζ(¼ + 2i)`. -/
theorem m4_menor_um : m 4 < 1 := by
  have hok : okAll4 6 16 24 32 2 = true := by decide +kernel
  have hmem := mem_zetaI4 (N := 6) (M := 8) (K := 16) (nT := 24) (p := 32) (by norm_num) (by norm_num)
    (by norm_num) 2 hok
  have hn := IC.norm_le_normMax hmem
  have hlt : IC.normMax (zetaI4 6 8 16 24 32 2) < 1 := by decide +kernel
  have hK : (1 / 4 : ℂ) + (((2 : ℚ) : ℝ) : ℂ) * I ∈ K 4 := by
    rw [K4_eq]
    refine ⟨by simp, by simp; norm_num, by simp; norm_num⟩
  have h1 := m_le hK
  have h2 : ((IC.normMax (zetaI4 6 8 16 24 32 2) : ℚ) : ℝ) < 1 := by exact_mod_cast hlt
  linarith

/-- **Pela torção, também `ζ(¾ + it) ≠ 0` para `¼ ≤ t ≤ 4`.** -/
theorem espelho_sem_zeros {t : ℝ} (h1 : 1 / 4 ≤ t) (h2 : t ≤ 4) :
    riemannZeta ((3 / 4 : ℂ) + t * I) ≠ 0 := by
  intro h0
  have hZ : (3 / 4 : ℂ) + t * I ∈ ATK.ZetaSimetria.Z := ⟨h0, by norm_num, by norm_num⟩
  have hT := ATK.ZetaSimetria.torcao_mem_Z hZ
  have e : ATK.ZetaSimetria.torcao ((3 / 4 : ℂ) + t * I) = (1 / 4 : ℂ) + t * I := by
    unfold ATK.ZetaSimetria.torcao
    apply Complex.ext <;> simp [map_ofNat]; norm_num
  rw [e] at hT
  have hK : (1 / 4 : ℂ) + t * I ∈ K 4 := by
    rw [K4_eq]
    exact ⟨by simp, by simpa using h1, by simpa using h2⟩
  exact K4_sem_zeros _ hK hT.1

/-- **O novo primeiro ponto aberto é `m₅ > 0`.** -/
theorem novo_primeiro_ponto :
    (1 / 20 : ℝ) ≤ m 4 ∧ m 4 < 1 ∧ (0 < m 5 ↔ ∀ s ∈ K 5, riemannZeta s ≠ 0) ∧
      (RiemannHypothesis → 0 < m 5) :=
  ⟨m4_cota, m4_menor_um, m_pos_iff (by norm_num), fun h => rh_iff_m_pos.mp h 5 (by norm_num)⟩

end ATK.ZeroClasses.Quarto

#print axioms ATK.ZeroClasses.Quarto.peca_cert
#print axioms ATK.ZeroClasses.Quarto.peca1
#print axioms ATK.ZeroClasses.Quarto.peca2
#print axioms ATK.ZeroClasses.Quarto.peca3
#print axioms ATK.ZeroClasses.Quarto.peca4
#print axioms ATK.ZeroClasses.Quarto.K4_eq
#print axioms ATK.ZeroClasses.Quarto.cota_K4
#print axioms ATK.ZeroClasses.Quarto.m4_cota
#print axioms ATK.ZeroClasses.Quarto.m4_pos
#print axioms ATK.ZeroClasses.Quarto.K4_sem_zeros
#print axioms ATK.ZeroClasses.Quarto.m4_menor_um
#print axioms ATK.ZeroClasses.Quarto.espelho_sem_zeros
#print axioms ATK.ZeroClasses.Quarto.novo_primeiro_ponto
