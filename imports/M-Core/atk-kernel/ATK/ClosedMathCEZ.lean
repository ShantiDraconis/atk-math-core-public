import ATK.CaudaMeio

/-!
# ATK-CEZ — Completude dos Estados dos Zeros ("Closed Math"), formalizada

Tudo o que os textos de 22/10 classificam como `PROVEN`, aqui com prova no kernel:

1. **Classificação** (`exaustivo`, `estado_*`): para qualquer `F : ℂ → ℂ` e qualquer `s`, exatamente um de
   `C` (zero na linha), `E` (zero fora), `NC` (não zero na linha), `NE` (não zero fora). O estado
   "indeterminado" é de **conhecimento**: um disco `F(s) ∈ B(m, r)` com `r < |m|` certifica `F(s) ≠ 0`
   (`cert_nao_zero`); com `|m| ≤ r` ambos são possíveis (`indeterminado_real`).
2. **Operadores** `T(s) = i s̄`, `R(s) = 1 − s̄`, `C(s) = s̄`, `D(s) = Re s − 1/2`, `M(a,b) = (a+b)/2`:
   `T² = R² = C² = id`, `T` isometria, `D(R s) = −D s`, `T∘R∘T(w) = w̄ + i` (a linha crítica vira
   `Im w = 1/2`), `R` fixa exatamente a linha.
3. **Simetria não força a linha** (`simetria_nao_basta`): `f(s) = (s − 1/2)² − a²` tem as simetrias de `ζ`
   e zeros `1/2 ± a`.
4. **Família de cruzamento** `G_λ(s) = ((s−1/2)² − λ² + γ²)² + 4γ²λ²` (`G_fatora`, `G_zeros`):
   zeros `1/2 ± λ ± iγ`; em `λ = 0` encontram-se na linha (raiz dupla, `G_zero_quadrado`); com `λ ≠ 0` ficam
   fora (`G_externo`); estado "ambos" para a família (`G_ambos`).
5. **Geometrias**: esfera de Riemann (`P_esfera`, `P_injetiva`), cilindro (`Cil_linha`, `Cil_par`,
   `Cil_R`), cone (`K_cone`, `K_vertice`).
6. **Para `ζ`**: todo zero é trivial, crítico ou externo (`zeta_tres_classes`); **RH ⟺ classe externa
   vazia** (`rh_iff_externa_vazia`); zeros externos vêm em pares de centro `1/2`.

Nada aqui produz um zero externo de `ζ`.
-/

open Complex

namespace ATK.CEZ

open ATK.ZetaSimetria ATK.ForaDaLinha ATK.EixoDeslocado ATK.ModeloParametrico

/-! ### 1. Classificação -/

inductive Estado
  | C | E | NC | NE
  deriving DecidableEq, Repr

open Classical in
/-- O estado de um ponto `s` para a função `F`. -/
noncomputable def estado (F : ℂ → ℂ) (s : ℂ) : Estado :=
  if F s = 0 then (if s.re = 1 / 2 then .C else .E) else (if s.re = 1 / 2 then .NC else .NE)

theorem exaustivo (F : ℂ → ℂ) (s : ℂ) :
    (F s = 0 ∧ s.re = 1 / 2) ∨ (F s = 0 ∧ s.re ≠ 1 / 2) ∨
      (F s ≠ 0 ∧ s.re = 1 / 2) ∨ (F s ≠ 0 ∧ s.re ≠ 1 / 2) := by
  by_cases h1 : F s = 0 <;> by_cases h2 : s.re = 1 / 2 <;> tauto

theorem estado_C (F : ℂ → ℂ) (s : ℂ) : estado F s = .C ↔ F s = 0 ∧ s.re = 1 / 2 := by
  unfold estado; split_ifs <;> simp_all

theorem estado_E (F : ℂ → ℂ) (s : ℂ) : estado F s = .E ↔ F s = 0 ∧ s.re ≠ 1 / 2 := by
  unfold estado; split_ifs <;> simp_all

theorem estado_NC (F : ℂ → ℂ) (s : ℂ) : estado F s = .NC ↔ F s ≠ 0 ∧ s.re = 1 / 2 := by
  unfold estado; split_ifs <;> simp_all

theorem estado_NE (F : ℂ → ℂ) (s : ℂ) : estado F s = .NE ↔ F s ≠ 0 ∧ s.re ≠ 1 / 2 := by
  unfold estado; split_ifs <;> simp_all

/-- **Certificação de não zero**: `F(s) ∈ B(m, r)` com `r < |m|` ⇒ `F(s) ≠ 0`. -/
theorem cert_nao_zero {F : ℂ → ℂ} {s m : ℂ} {r : ℝ} (h : ‖F s - m‖ ≤ r) (hr : r < ‖m‖) :
    F s ≠ 0 := by
  intro h0; rw [h0, zero_sub, norm_neg] at h; linarith

/-- **Indeterminação é de conhecimento**: o mesmo disco `B(0, r)` é compatível com `F(s) = 0` e com
`F(s) ≠ 0`. -/
theorem indeterminado_real {r : ℝ} (hr : 0 < r) (s : ℂ) :
    ∃ F G : ℂ → ℂ, ‖F s - 0‖ ≤ r ∧ ‖G s - 0‖ ≤ r ∧ F s = 0 ∧ G s ≠ 0 := by
  refine ⟨fun _ => 0, fun _ => (r : ℂ), by simp; linarith, by simp [abs_of_pos hr], rfl, ?_⟩
  simp; exact hr.ne'

/-- Estado "ambos" para uma família `F_λ` e um ramo `ρ(λ)`. -/
def Ambos (F : ℝ → ℂ → ℂ) (ρ : ℝ → ℂ) : Prop :=
  ∃ l₁ l₂ : ℝ, F l₁ (ρ l₁) = 0 ∧ (ρ l₁).re = 1 / 2 ∧ F l₂ (ρ l₂) = 0 ∧ (ρ l₂).re ≠ 1 / 2

/-! ### 2. Operadores -/

/-- Deslocamento `D(s) = Re s − 1/2`. -/
noncomputable def D (s : ℂ) : ℝ := s.re - 1 / 2

theorem conj_conj' (s : ℂ) : (starRingEnd ℂ) ((starRingEnd ℂ) s) = s := by simp

theorem R_R (s : ℂ) : torcao (torcao s) = s := ZetaSimetria.torcao_torcao s

theorem T_T (s : ℂ) : troca (troca s) = s := troca_troca s

theorem T_isometria (s₁ s₂ : ℂ) : ‖troca s₁ - troca s₂‖ = ‖s₁ - s₂‖ := by
  unfold troca
  rw [← mul_sub, ← map_sub, norm_mul, Complex.norm_I, one_mul, Complex.norm_conj]

theorem D_R (s : ℂ) : D (torcao s) = -D s := by unfold D; rw [re_torcao]; ring

/-- Na geometria trocada, a reflexão crítica vira `w ↦ w̄ + i`. -/
theorem TRT (w : ℂ) : troca (torcao (troca w)) = (starRingEnd ℂ) w + I := by
  apply Complex.ext <;> simp [troca, torcao] <;> ring

/-- A linha crítica vira a reta horizontal `Im w = 1/2`. -/
theorem TRT_fixo (w : ℂ) : troca (torcao (troca w)) = w ↔ w.im = 1 / 2 := by
  rw [TRT]
  constructor
  · intro h; have := congrArg Complex.im h; simp at this; linarith
  · intro h; apply Complex.ext <;> simp; linarith

theorem R_fixo (s : ℂ) : torcao s = s ↔ s.re = 1 / 2 := torcao_fixo_iff s

/-! ### 3. Simetria não força a linha -/

/-- `f_a(s) = (s − 1/2)² − a²`. -/
noncomputable def fa (a : ℝ) (s : ℂ) : ℂ := (s - ((1 / 2 : ℝ) : ℂ)) ^ 2 - (a : ℂ) ^ 2

theorem fa_R (a : ℝ) (s : ℂ) : fa a (1 - s) = fa a s := by unfold fa; push_cast; ring

theorem fa_conj (a : ℝ) (s : ℂ) : fa a ((starRingEnd ℂ) s) = (starRingEnd ℂ) (fa a s) := by
  unfold fa; simp only [map_sub, map_pow, Complex.conj_ofReal]

theorem fa_zeros (a : ℝ) : fa a ((1 / 2 + a : ℝ) : ℂ) = 0 ∧ fa a ((1 / 2 - a : ℝ) : ℂ) = 0 := by
  unfold fa; constructor <;> push_cast <;> ring

/-- **Simetria funcional não força a linha**: há funções com as simetrias de `ζ` e zeros fora dela. -/
theorem simetria_nao_basta :
    ∃ f : ℂ → ℂ, (∀ s, f (1 - s) = f s) ∧ (∀ s, f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (f s)) ∧
      ∃ ρ, f ρ = 0 ∧ ρ.re ≠ 1 / 2 :=
  ⟨fa 1, fa_R 1, fa_conj 1, ((1 / 2 + 1 : ℝ) : ℂ), (fa_zeros 1).1, by norm_num⟩

/-! ### 4. Família de cruzamento -/

/-- `G_λ(s) = ((s−1/2)² − λ² + γ²)² + 4γ²λ²`. -/
noncomputable def G (l g : ℝ) (s : ℂ) : ℂ :=
  ((s - ((1 / 2 : ℝ) : ℂ)) ^ 2 - (l : ℂ) ^ 2 + (g : ℂ) ^ 2) ^ 2 + 4 * (g : ℂ) ^ 2 * (l : ℂ) ^ 2

theorem G_fatora (l g : ℝ) (s : ℂ) :
    G l g s = ((s - 1 / 2 - l) ^ 2 + (g : ℂ) ^ 2) * ((s - 1 / 2 + l) ^ 2 + (g : ℂ) ^ 2) := by
  unfold G; push_cast; ring

theorem sq_add_sq_eq_zero {u : ℂ} {g : ℝ} : u ^ 2 + (g : ℂ) ^ 2 = 0 ↔ u = g * I ∨ u = -(g * I) := by
  have e : u ^ 2 + (g : ℂ) ^ 2 = (u - g * I) * (u + g * I) := by ring_nf; rw [I_sq]; ring
  rw [e, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

/-- **Zeros de `G_λ`**: `1/2 ± λ ± iγ`. -/
theorem G_zeros (l g : ℝ) (s : ℂ) :
    G l g s = 0 ↔ s = 1 / 2 + l + g * I ∨ s = 1 / 2 + l - g * I ∨
      s = 1 / 2 - l + g * I ∨ s = 1 / 2 - l - g * I := by
  rw [G_fatora, mul_eq_zero, sq_add_sq_eq_zero, sq_add_sq_eq_zero]
  constructor
  · rintro ((h | h) | (h | h))
    · left; linear_combination h
    · right; left; linear_combination h
    · right; right; left; linear_combination h
    · right; right; right; linear_combination h
  · rintro (h | h | h | h)
    · left; left; linear_combination h
    · left; right; linear_combination h
    · right; left; linear_combination h
    · right; right; linear_combination h

theorem G_R (l g : ℝ) (s : ℂ) : G l g (1 - s) = G l g s := by unfold G; push_cast; ring

theorem G_conj (l g : ℝ) (s : ℂ) : G l g ((starRingEnd ℂ) s) = (starRingEnd ℂ) (G l g s) := by
  unfold G; simp only [map_sub, map_add, map_mul, map_pow, Complex.conj_ofReal, map_ofNat]

/-- Em `λ = 0` os ramos se encontram na linha com multiplicidade dois. -/
theorem G_zero_quadrado (g : ℝ) (s : ℂ) : G 0 g s = ((s - 1 / 2) ^ 2 + (g : ℂ) ^ 2) ^ 2 := by
  unfold G; push_cast; ring

/-- Com `λ ≠ 0` os quatro zeros ficam fora da linha. -/
theorem G_externo {l g : ℝ} (hl : l ≠ 0) {s : ℂ} (hs : G l g s = 0) : s.re ≠ 1 / 2 := by
  rcases (G_zeros l g s).mp hs with h | h | h | h <;> rw [h] <;> simp <;> intro h' <;>
    apply hl <;> linarith

/-- **Estado "ambos"** para o ramo `ρ(λ) = 1/2 + λ + iγ`: crítico em `λ = 0`, externo em `λ = 1`. -/
theorem G_ambos (g : ℝ) : Ambos (fun l s => G l g s) (fun l => 1 / 2 + l + g * I) := by
  refine ⟨0, 1, ?_, by simp, ?_, by simp⟩
  · exact (G_zeros 0 g _).mpr (Or.inl rfl)
  · exact (G_zeros 1 g _).mpr (Or.inl rfl)

/-! ### 5. Geometrias -/

/-- Projeção estereográfica inversa `ℂ → S²`. -/
noncomputable def P (s : ℂ) : ℝ × ℝ × ℝ :=
  (2 * s.re / (1 + Complex.normSq s), 2 * s.im / (1 + Complex.normSq s),
    (Complex.normSq s - 1) / (1 + Complex.normSq s))

theorem P_esfera (s : ℂ) : (P s).1 ^ 2 + (P s).2.1 ^ 2 + (P s).2.2 ^ 2 = 1 := by
  unfold P
  have hA : 0 < 1 + Complex.normSq s := by have := Complex.normSq_nonneg s; linarith
  simp only
  rw [Complex.normSq_apply]
  field_simp
  ring

theorem P_injetiva : Function.Injective P := by
  intro s s' h
  unfold P at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hA : 0 < 1 + Complex.normSq s := by have := Complex.normSq_nonneg s; linarith
  have hB : 0 < 1 + Complex.normSq s' := by have := Complex.normSq_nonneg s'; linarith
  have hAB : Complex.normSq s = Complex.normSq s' := by
    rw [div_eq_div_iff hA.ne' hB.ne'] at h3; linarith
  rw [hAB] at h1 h2
  have hB' : (1 + Complex.normSq s') ≠ 0 := hB.ne'
  apply Complex.ext
  · have := (div_left_inj' hB').mp h1; linarith
  · have := (div_left_inj' hB').mp h2; linarith

/-- Cilindro: `C(s) = (cos 2πσ, sin 2πσ, t)`. -/
noncomputable def Cil (s : ℂ) : ℝ × ℝ × ℝ :=
  (Real.cos (2 * Real.pi * s.re), Real.sin (2 * Real.pi * s.re), s.im)

theorem Cil_linha (t : ℝ) : Cil ((1 / 2 : ℂ) + t * I) = (-1, 0, t) := by
  unfold Cil; simp
  constructor <;> rw [show (2 : ℝ) * Real.pi * 2⁻¹ = Real.pi by ring] <;> simp

theorem Cil_par (d t : ℝ) :
    Cil (((1 / 2 + d : ℝ) : ℂ) + t * I) =
        (-Real.cos (2 * Real.pi * d), -Real.sin (2 * Real.pi * d), t) ∧
      Cil (((1 / 2 - d : ℝ) : ℂ) + t * I) =
        (-Real.cos (2 * Real.pi * d), Real.sin (2 * Real.pi * d), t) := by
  unfold Cil
  constructor
  · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add]
    rw [show 2 * Real.pi * (1 / 2 + d) = 2 * Real.pi * d + Real.pi by ring, Real.cos_add_pi,
      Real.sin_add_pi]
  · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add]
    rw [show 2 * Real.pi * (1 / 2 - d) = Real.pi - 2 * Real.pi * d by ring, Real.cos_pi_sub,
      Real.sin_pi_sub]

/-- No cilindro, a reflexão crítica é `(X, Y, Z) ↦ (X, −Y, Z)`. -/
theorem Cil_R (s : ℂ) :
    Cil (torcao s) = ((Cil s).1, -(Cil s).2.1, (Cil s).2.2) := by
  unfold Cil
  rw [re_torcao, EixoDeslocado.im_torcao]
  rw [show 2 * Real.pi * (1 - s.re) = 2 * Real.pi - 2 * Real.pi * s.re by ring,
    Real.cos_two_pi_sub, Real.sin_two_pi_sub]

/-- Cone duplo: `K(δ, θ) = (|δ| cos θ, |δ| sin θ, δ)`. -/
noncomputable def Kc (δ θ : ℝ) : ℝ × ℝ × ℝ := (|δ| * Real.cos θ, |δ| * Real.sin θ, δ)

theorem K_cone (δ θ : ℝ) : (Kc δ θ).1 ^ 2 + (Kc δ θ).2.1 ^ 2 = (Kc δ θ).2.2 ^ 2 := by
  unfold Kc
  simp only
  have := Real.cos_sq_add_sin_sq θ
  rw [mul_pow, mul_pow, sq_abs]
  nlinarith [this]

theorem K_vertice (θ : ℝ) : Kc 0 θ = (0, 0, 0) := by unfold Kc; simp

/-! ### 6. Para a zeta -/

/-- **Três classes**: todo zero de `ζ` é trivial, crítico ou externo. -/
theorem zeta_tres_classes {s : ℂ} (hz : riemannZeta s = 0) :
    Trivial s ∨ (s ∈ Z ∧ s.re = 1 / 2) ∨ (s ∈ Z ∧ s.re ≠ 1 / 2) := by
  by_cases ht : Trivial s
  · exact Or.inl ht
  · have hZ : s ∈ Z := (mem_Z_iff_nao_trivial s).mpr ⟨hz, ht⟩
    by_cases h : s.re = 1 / 2
    · exact Or.inr (Or.inl ⟨hZ, h⟩)
    · exact Or.inr (Or.inr ⟨hZ, h⟩)

/-- A classe externa de `ζ`. -/
def ZE : Set ℂ := {s | s ∈ Z ∧ s.re ≠ 1 / 2}

/-- **RH ⟺ classe externa vazia.** -/
theorem rh_iff_externa_vazia : RiemannHypothesis ↔ ZE = ∅ := by
  rw [riemann_iff_vazio, Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h s hs; exact h.false ⟨s, hs⟩
  · intro h; exact ⟨fun ρ => h ρ.1 ρ.2⟩

/-- Zeros externos vêm em pares, com centro exatamente `1/2`, e nenhum dos dois na linha. -/
theorem externos_em_pares {s : ℂ} (hs : s ∈ ZE) :
    torcao s ∈ ZE ∧ (s.re + (torcao s).re) / 2 = 1 / 2 ∧ (torcao s).im = s.im := by
  obtain ⟨hZ, hne⟩ := hs
  refine ⟨⟨torcao_mem_Z hZ, ?_⟩, by rw [re_torcao]; ring, EixoDeslocado.im_torcao s⟩
  rw [re_torcao]; intro h; apply hne; linarith

/-- A troca de coordenadas transporta a classificação: `estado (F ∘ T) (T s) = estado F s` quando
o eixo é transportado junto (a linha `Re = 1/2` vira `Im = 1/2`). -/
theorem troca_transporta (F : ℂ → ℂ) (s : ℂ) :
    (F ∘ troca) (troca s) = F s ∧ ((troca s).im = 1 / 2 ↔ s.re = 1 / 2) := by
  refine ⟨by simp [Function.comp, troca_troca], ?_⟩
  rw [troca_im]

end ATK.CEZ

#print axioms ATK.CEZ.exaustivo
#print axioms ATK.CEZ.estado_C
#print axioms ATK.CEZ.estado_E
#print axioms ATK.CEZ.estado_NC
#print axioms ATK.CEZ.estado_NE
#print axioms ATK.CEZ.cert_nao_zero
#print axioms ATK.CEZ.indeterminado_real
#print axioms ATK.CEZ.conj_conj'
#print axioms ATK.CEZ.R_R
#print axioms ATK.CEZ.T_T
#print axioms ATK.CEZ.T_isometria
#print axioms ATK.CEZ.D_R
#print axioms ATK.CEZ.TRT
#print axioms ATK.CEZ.TRT_fixo
#print axioms ATK.CEZ.R_fixo
#print axioms ATK.CEZ.fa_R
#print axioms ATK.CEZ.fa_conj
#print axioms ATK.CEZ.fa_zeros
#print axioms ATK.CEZ.simetria_nao_basta
#print axioms ATK.CEZ.G_fatora
#print axioms ATK.CEZ.sq_add_sq_eq_zero
#print axioms ATK.CEZ.G_zeros
#print axioms ATK.CEZ.G_R
#print axioms ATK.CEZ.G_conj
#print axioms ATK.CEZ.G_zero_quadrado
#print axioms ATK.CEZ.G_externo
#print axioms ATK.CEZ.G_ambos
#print axioms ATK.CEZ.P_esfera
#print axioms ATK.CEZ.P_injetiva
#print axioms ATK.CEZ.Cil_linha
#print axioms ATK.CEZ.Cil_par
#print axioms ATK.CEZ.Cil_R
#print axioms ATK.CEZ.K_cone
#print axioms ATK.CEZ.K_vertice
#print axioms ATK.CEZ.zeta_tres_classes
#print axioms ATK.CEZ.rh_iff_externa_vazia
#print axioms ATK.CEZ.externos_em_pares
#print axioms ATK.CEZ.troca_transporta
