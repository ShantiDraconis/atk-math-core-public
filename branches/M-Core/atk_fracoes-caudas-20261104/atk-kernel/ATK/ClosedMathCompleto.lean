import ATK.ClosedMathCEZ
import ATK.Cert.Intervalo

/-!
# ATK — Closed Math completo

Fecha no kernel o escopo **modelo** da teoria ATK–Closed Math proposta pelo usuário
(especificação formal, geometrias, taxonomia ampliada e porta "Universal Green"):

1. **Semântica**: os quatro estados pontuais `C, E, N_C, N_E`, exaustivos e exclusivos; o estado
   "ambos" só existe para famílias; "indeterminado" é um estado do *verificador*, não do ponto.
2. **Verificador** `checar`: devolve `naoZero` com prova ou `indeterminado`; nunca `zero`
   (um invólucro numérico não prova igualdade). Versão racional `checarIC`, decidida pelo kernel.
3. **Operadores** `I, J, R, S = R∘J, T`: grupo de Klein `{I, J, R, S}`, involuções, isometria,
   centro, separação, coincidência, transporte por bijeções.
4. **Modelo** `G_{d,γ}` e produtores **P1–P5**: habitantes crítico, externo, "ambos", não zero na
   linha e fora dela; `G_{d,γ}(1−s) = G_{d,γ}(s)`, `G(s̄) = conj G(s)`.
5. **Cruzamento**: expansão quártica, velocidades `±1`, separação `2|λ|` não diferenciável em `0`,
   **conservação da contagem** (`card roots = 4` para todo `λ`), multiplicidade `2` no encontro e
   `1` fora dele.
6. **Geometrias**: corda esférica exata, cilindro injetivo na faixa `0 < Re < 1` e periódico fora,
   distância cilíndrica `2|sin 2πδ|` com derivada `4π`, cone que perde a ordenada e cone elevado
   `K̃` injetivo; teorema de que o estado de zero **não** é função da imagem no cone.
7. **Taxonomia ampliada**: multiplicidade por derivadas, zeros `±a, ±ib`, infinitos zeros de
   `sin πz`, zero de ordem 2 no infinito de `1/z²`, cancelamento `(x²−1)/(x−1) → 2` (direto e por
   L'Hôpital), derivada logarítmica `m/(z−a) + g'/g`, **princípio do argumento** para um zero de
   ordem `m` e o exemplo `(1/2πi)∮ f'/f = 5 − 2 = 3`, truncamentos decimais que nunca são zeros,
   teorema da identidade e multiplicidade infinita.
8. **Registro de zero** multidimensional e a porta **`UGModelo`**, provada.

Nada aqui é afirmado sobre zeros externos de `ζ`: `simetria_compativel_com_ambos` mostra que as
simetrias de `ζ` são compatíveis com as duas respostas; o escopo zeta continua sendo a HR.
-/

open Complex Polynomial Filter Topology Set

namespace ATK.ClosedMath

open ATK.CEZ ATK.ZetaSimetria ATK.ModeloParametrico

/-! ## 1. Semântica: estados pontuais -/

/-- Zero crítico. -/
def Critico (F : ℂ → ℂ) (s : ℂ) : Prop := F s = 0 ∧ s.re = 1 / 2
/-- Zero externo. -/
def Externo (F : ℂ → ℂ) (s : ℂ) : Prop := F s = 0 ∧ s.re ≠ 1 / 2
/-- Não zero situado na linha. -/
def NaoZeroC (F : ℂ → ℂ) (s : ℂ) : Prop := F s ≠ 0 ∧ s.re = 1 / 2
/-- Não zero fora da linha. -/
def NaoZeroE (F : ℂ → ℂ) (s : ℂ) : Prop := F s ≠ 0 ∧ s.re ≠ 1 / 2

/-- **T2 — exaustividade**. -/
theorem classificacao (F : ℂ → ℂ) (s : ℂ) :
    Critico F s ∨ Externo F s ∨ NaoZeroC F s ∨ NaoZeroE F s := by
  by_cases hz : F s = 0 <;> by_cases hl : s.re = 1 / 2
  · exact Or.inl ⟨hz, hl⟩
  · exact Or.inr (Or.inl ⟨hz, hl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hz, hl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hz, hl⟩))

/-- **T1 — exclusividade** (os seis pares). -/
theorem exclusivos (F : ℂ → ℂ) (s : ℂ) :
    ¬ (Critico F s ∧ Externo F s) ∧ ¬ (Critico F s ∧ NaoZeroC F s) ∧
    ¬ (Critico F s ∧ NaoZeroE F s) ∧ ¬ (Externo F s ∧ NaoZeroC F s) ∧
    ¬ (Externo F s ∧ NaoZeroE F s) ∧ ¬ (NaoZeroC F s ∧ NaoZeroE F s) := by
  unfold Critico Externo NaoZeroC NaoZeroE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro ⟨⟨a, b⟩, c, d⟩ <;> tauto

/-- "Ambos" num mesmo ponto é contraditório: o estado `B` só faz sentido para famílias. -/
theorem ambos_pontual_impossivel (F : ℂ → ℂ) (s : ℂ) : ¬ (Critico F s ∧ Externo F s) :=
  (exclusivos F s).1

/-- Os predicados coincidem com a função de estado de `ATK.CEZ`. -/
theorem critico_iff_estado (F : ℂ → ℂ) (s : ℂ) : Critico F s ↔ estado F s = .C :=
  (estado_C F s).symm

theorem externo_iff_estado (F : ℂ → ℂ) (s : ℂ) : Externo F s ↔ estado F s = .E :=
  (estado_E F s).symm

/-! ## 2. Verificador: `Zero`, `NaoZero`, `Indeterminado` (produtor P6) -/

/-- Veredito de um verificador. -/
inductive Veredito
  | zero
  | naoZero
  | indeterminado
  deriving DecidableEq, Repr

/-- O que cada veredito obriga: `zero` exige igualdade, `naoZero` desigualdade, `indeterminado`
nada. -/
def Certificado (F : ℂ → ℂ) (s : ℂ) : Veredito → Prop
  | .zero => F s = 0
  | .naoZero => F s ≠ 0
  | .indeterminado => True

/-- Verificador de disco: sabe-se apenas que `F s ∈ B(m, r)`. -/
noncomputable def checar (m : ℂ) (r : ℝ) : Veredito :=
  if r < ‖m‖ then .naoZero else .indeterminado

/-- **Correção do verificador**: todo veredito vem com sua prova. -/
theorem checar_correto {F : ℂ → ℂ} {s m : ℂ} {r : ℝ} (h : ‖F s - m‖ ≤ r) :
    Certificado F s (checar m r) := by
  unfold checar
  split_ifs with hr
  · exact cert_nao_zero h hr
  · trivial

/-- Um invólucro nunca certifica igualdade. -/
theorem checar_nunca_zero (m : ℂ) (r : ℝ) : checar m r ≠ .zero := by
  unfold checar; split_ifs <;> simp

/-- Com o centro exato, `indeterminado ↔ ‖F s‖ ≤ r`. -/
theorem checar_exato_indet (z : ℂ) (r : ℝ) : checar z r = .indeterminado ↔ ‖z‖ ≤ r := by
  unfold checar; split_ifs with h
  · simp only [reduceCtorEq, false_iff, not_le]; exact h
  · simp only [true_iff]; exact not_lt.mp h

/-- **Não zero é semi-decidível**: todo valor não nulo é certificado com precisão suficiente. -/
theorem nao_zero_certificavel {z : ℂ} (hz : z ≠ 0) : ∃ r > 0, checar z r = .naoZero := by
  refine ⟨‖z‖ / 2, by positivity, ?_⟩
  unfold checar
  rw [if_pos]
  have := norm_pos_iff.mpr hz
  linarith

/-- **Zero nunca sai do indeterminado**: para `F s = 0`, todo invólucro exato fica indeterminado. -/
theorem zero_sempre_indeterminado {r : ℝ} (hr : 0 ≤ r) : checar 0 r = .indeterminado :=
  (checar_exato_indet 0 r).mpr (by simpa using hr)

/-- `indeterminado` não é propriedade do ponto: o mesmo invólucro serve a um zero e a um não zero. -/
theorem indeterminado_nao_e_estado :
    ∃ (F₁ F₂ : ℂ → ℂ) (s m : ℂ) (r : ℝ), ‖F₁ s - m‖ ≤ r ∧ ‖F₂ s - m‖ ≤ r ∧
      F₁ s = 0 ∧ F₂ s ≠ 0 ∧ checar m r = .indeterminado := by
  refine ⟨fun _ => 0, fun _ => 1 / 2, 0, 0, 1, by simp, ?_, rfl, by norm_num, ?_⟩
  · simp only [sub_zero]; rw [norm_div]; norm_num
  · rw [checar_exato_indet]; simp

/-! ### Verificador racional decidido pelo kernel -/

open ATK.Cert in
/-- Exclusão de `0` por um retângulo racional. -/
def excluiZero (B : IC) : Bool :=
  decide (0 < B.re.lo) || decide (B.re.hi < 0) || decide (0 < B.im.lo) || decide (B.im.hi < 0)

open ATK.Cert in
/-- Verificador racional (computável). -/
def checarIC (B : IC) : Veredito := if excluiZero B then .naoZero else .indeterminado

open ATK.Cert in
theorem checarIC_correto {z : ℂ} {B : IC} (h : IC.mem z B) (hc : checarIC B = .naoZero) :
    z ≠ 0 := by
  unfold checarIC at hc
  split_ifs at hc with hx
  · intro hz
    subst hz
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
    simp only [excluiZero, Bool.or_eq_true, decide_eq_true_eq] at hx
    simp only [zero_re, zero_im] at h1 h2 h3 h4
    rcases hx with ((hx | hx) | hx) | hx
    · have : (0 : ℝ) < B.re.lo := by exact_mod_cast hx
      linarith
    · have : (B.re.hi : ℝ) < 0 := by exact_mod_cast hx
      linarith
    · have : (0 : ℝ) < B.im.lo := by exact_mod_cast hx
      linarith
    · have : (B.im.hi : ℝ) < 0 := by exact_mod_cast hx
      linarith

open ATK.Cert in
theorem checarIC_correto' {F : ℂ → ℂ} {s : ℂ} {B : IC} (h : IC.mem (F s) B) :
    Certificado F s (checarIC B) := by
  cases hc : checarIC B with
  | zero => simp [checarIC] at hc; split_ifs at hc
  | naoZero => exact checarIC_correto h hc
  | indeterminado => trivial

/-! ## 3. Operadores -/

/-- Conjugação `J`. -/
noncomputable def opJ (s : ℂ) : ℂ := (starRingEnd ℂ) s
/-- `S = R ∘ J : s ↦ 1 − s`. -/
def opS (s : ℂ) : ℂ := 1 - s

theorem J_J (s : ℂ) : opJ (opJ s) = s := by simp [opJ]
theorem S_S (s : ℂ) : opS (opS s) = s := by simp [opS]
theorem R_J (s : ℂ) : torcao (opJ s) = opS s := by simp [torcao, opJ, opS]
theorem J_R (s : ℂ) : opJ (torcao s) = opS s := by simp [torcao, opJ, opS]
theorem R_S (s : ℂ) : torcao (opS s) = opJ s := by simp [torcao, opJ, opS]
theorem S_R (s : ℂ) : opS (torcao s) = opJ s := by simp [torcao, opJ, opS]
theorem J_S (s : ℂ) : opJ (opS s) = torcao s := by simp [torcao, opJ, opS]

/-- **Grupo de Klein** `{I, J, R, S}`: fechado, comutativo, toda involução. -/
theorem klein (s : ℂ) :
    opJ (opJ s) = s ∧ torcao (torcao s) = s ∧ opS (opS s) = s ∧
    torcao (opJ s) = opJ (torcao s) ∧ torcao (opJ s) = opS s ∧
    torcao (opS s) = opJ s ∧ opJ (opS s) = torcao s :=
  ⟨J_J s, R_R s, S_S s, by rw [R_J, J_R], R_J s, R_S s, J_S s⟩

/-- `T` é involução e isometria, mas **não** comuta com `R`. -/
theorem T_nao_comuta_R : troca (torcao 0) ≠ torcao (troca 0) := by
  simp only [troca, torcao, map_zero, sub_zero, mul_zero, map_one, mul_one]
  intro h
  have := congrArg Complex.re h
  simp at this

/-- Deslocamento `D(R s) = −D(s)` (T3). -/
theorem T3 (s : ℂ) : D (torcao s) = -D s := D_R s

/-- **T4 — centro do par**. -/
theorem T4_centro (d t : ℝ) :
    (((1 / 2 + d : ℂ) + t * I) + ((1 / 2 - d : ℂ) + t * I)) / 2 = 1 / 2 + t * I := by ring

/-- **T5 — separação do par** `= 2|d|`. -/
theorem T5_separacao (d t : ℝ) :
    ‖((1 / 2 + d : ℂ) + t * I) - ((1 / 2 - d : ℂ) + t * I)‖ = 2 * |d| := by
  have : ((1 / 2 + d : ℂ) + t * I) - ((1 / 2 - d : ℂ) + t * I) = ((2 * d : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  norm_num

/-- **T6 — coincidência** `s₊ = s₋ ↔ d = 0`. -/
theorem T6_coincidencia (d t : ℝ) :
    ((1 / 2 + d : ℂ) + t * I) = (1 / 2 - d : ℂ) + t * I ↔ d = 0 := by
  constructor
  · intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  · rintro rfl; simp

/-- A troca de eixos leva o centro do par a `t + i/2` e preserva a separação. -/
theorem troca_par (d t : ℝ) :
    (troca ((1 / 2 + d : ℂ) + t * I) + troca ((1 / 2 - d : ℂ) + t * I)) / 2 = t + I / 2 ∧
      ‖troca ((1 / 2 + d : ℂ) + t * I) - troca ((1 / 2 - d : ℂ) + t * I)‖ = 2 * |d| := by
  refine ⟨?_, by rw [T_isometria]; exact T5_separacao d t⟩
  unfold troca
  simp only [map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I]
  ring_nf
  rw [I_sq]
  ring

/-- **Regra de transporte**: para uma bijeção `H`, `F s = 0 ↔ (F ∘ H⁻¹)(H s) = 0`. -/
theorem transporte (H : ℂ ≃ ℂ) (F : ℂ → ℂ) (s : ℂ) : F s = 0 ↔ (F ∘ H.symm) (H s) = 0 := by
  simp

/-! ## 4. Modelo `G_{d,γ}` e produtores P1–P5 -/

theorem fator_real_ne {x y : ℝ} (hy : y ≠ 0) : ((x : ℂ)) ^ 2 + (y : ℂ) ^ 2 ≠ 0 := by
  have : ((x : ℂ)) ^ 2 + (y : ℂ) ^ 2 = ((x ^ 2 + y ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.ofReal_ne_zero]
  have := pow_pos (abs_pos.mpr hy) 2
  rw [sq_abs] at this
  positivity

/-- **P1** — os quatro zeros `½ + εd + iηγ`. -/
theorem P1 (d γ : ℝ) :
    G d γ (1 / 2 + d + γ * I) = 0 ∧ G d γ (1 / 2 + d - γ * I) = 0 ∧
      G d γ (1 / 2 - d + γ * I) = 0 ∧ G d γ (1 / 2 - d - γ * I) = 0 :=
  ⟨(G_zeros d γ _).mpr (Or.inl rfl), (G_zeros d γ _).mpr (Or.inr (Or.inl rfl)),
    (G_zeros d γ _).mpr (Or.inr (Or.inr (Or.inl rfl))),
    (G_zeros d γ _).mpr (Or.inr (Or.inr (Or.inr rfl)))⟩

/-- **P2** — habitante crítico `½ + iγ` de `G_{0,γ}`. -/
theorem P2_critico (γ : ℝ) : Critico (G 0 γ) (1 / 2 + γ * I) := by
  refine ⟨?_, by simp⟩
  have := (P1 0 γ).1
  simpa using this

/-- **P3** — habitante externo `½ + d + iγ` de `G_{d,γ}`, `d ≠ 0`. -/
theorem P3_externo {d : ℝ} (hd : d ≠ 0) (γ : ℝ) : Externo (G d γ) (1 / 2 + d + γ * I) :=
  ⟨(P1 d γ).1, G_externo hd (P1 d γ).1⟩

/-- **P4** — trajetória "ambos" `ρ(λ) = ½ + λ + iγ`, `λ ∈ [0, ¼]`. -/
theorem P4_ambos (γ : ℝ) :
    (∀ l : ℝ, G l γ (1 / 2 + l + γ * I) = 0) ∧
      (1 / 2 + ((0 : ℝ) : ℂ) + γ * I).re = 1 / 2 ∧ (1 / 2 + ((1 / 4 : ℝ) : ℂ) + γ * I).re = 3 / 4 := by
  refine ⟨fun l => (P1 l γ).1, by simp, ?_⟩
  simp; norm_num

/-- **P5** — não zero fora da linha: `2 ∈ N_E`. -/
theorem P5_NE (d : ℝ) {γ : ℝ} (hγ : γ ≠ 0) : NaoZeroE (G d γ) 2 := by
  refine ⟨?_, by norm_num⟩
  rw [G_fatora]
  have e1 : (2 : ℂ) - 1 / 2 - d = ((3 / 2 - d : ℝ) : ℂ) := by push_cast; ring
  have e2 : (2 : ℂ) - 1 / 2 + d = ((3 / 2 + d : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2]
  exact mul_ne_zero (fator_real_ne hγ) (fator_real_ne hγ)

/-- **P5** — não zero na linha: `½ ∈ N_C`, com `G(½) = (d² + γ²)²`. -/
theorem P5_NC (d : ℝ) {γ : ℝ} (hγ : γ ≠ 0) : NaoZeroC (G d γ) (1 / 2) := by
  refine ⟨?_, by norm_num⟩
  rw [G_fatora]
  have e1 : (1 / 2 : ℂ) - 1 / 2 - d = ((-d : ℝ) : ℂ) := by push_cast; ring
  have e2 : (1 / 2 : ℂ) - 1 / 2 + d = ((d : ℝ) : ℂ) := by push_cast; ring
  rw [e1, e2]
  exact mul_ne_zero (fator_real_ne hγ) (fator_real_ne hγ)

theorem G_meio (d γ : ℝ) : G d γ (1 / 2) = (((d ^ 2 + γ ^ 2) ^ 2 : ℝ) : ℂ) := by
  rw [G_fatora]; push_cast; ring

/-- Os quatro estados pontuais têm habitantes no modelo (T8). -/
theorem T8_habitantes {γ : ℝ} (hγ : γ ≠ 0) :
    (∃ F s, Critico F s) ∧ (∃ F s, Externo F s) ∧ (∃ F s, NaoZeroC F s) ∧ (∃ F s, NaoZeroE F s) :=
  ⟨⟨_, _, P2_critico γ⟩, ⟨_, _, P3_externo one_ne_zero γ⟩, ⟨_, _, P5_NC 0 hγ⟩,
    ⟨_, _, P5_NE 0 hγ⟩⟩

/-- Os operadores preservam o conjunto de zeros do modelo. -/
theorem zeros_invariantes (d γ : ℝ) (s : ℂ) (hs : G d γ s = 0) :
    G d γ (opJ s) = 0 ∧ G d γ (opS s) = 0 ∧ G d γ (torcao s) = 0 := by
  have hJ : G d γ (opJ s) = 0 := by simp [opJ, G_conj, hs]
  refine ⟨hJ, ?_, ?_⟩
  · simp only [opS]; rw [G_R]; exact hs
  · rw [show torcao s = 1 - opJ s by simp [torcao, opJ], G_R]; exact hJ

/-- As simetrias de `ζ` (`F(1−s) = F(s)`, `F(s̄) = conj F(s)`) são compatíveis com **as duas**
respostas: sem zeros externos (`G_{0,γ}`) e com zeros externos (`G_{1,γ}`). -/
theorem simetria_compativel_com_ambos {γ : ℝ} (hγ : γ ≠ 0) :
    (∃ F : ℂ → ℂ, (∀ s, F (1 - s) = F s) ∧ (∀ s, F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (F s)) ∧
        (∃ s, F s = 0) ∧ ∀ s, F s = 0 → s.re = 1 / 2) ∧
      (∃ F : ℂ → ℂ, (∀ s, F (1 - s) = F s) ∧
        (∀ s, F ((starRingEnd ℂ) s) = (starRingEnd ℂ) (F s)) ∧ ∃ s, F s = 0 ∧ s.re ≠ 1 / 2) := by
  refine ⟨⟨G 0 γ, G_R 0 γ, G_conj 0 γ, ⟨_, (P2_critico γ).1⟩, ?_⟩,
    ⟨G 1 γ, G_R 1 γ, G_conj 1 γ, _, (P3_externo one_ne_zero γ)⟩⟩
  intro s hs
  rcases (G_zeros 0 γ s).mp hs with h | h | h | h <;> rw [h] <;> simp

/-! ## 5. Cruzamento -/

/-- Expansão quártica com `x = s − ½`. -/
theorem G_quartica (l g : ℝ) (s : ℂ) :
    G l g s = (s - 1 / 2) ^ 4 + 2 * ((g : ℂ) ^ 2 - (l : ℂ) ^ 2) * (s - 1 / 2) ^ 2 +
      ((g : ℂ) ^ 2 + (l : ℂ) ^ 2) ^ 2 := by
  unfold G; push_cast; ring

/-- Velocidade dos ramos `s±(λ) = ½ ± λ + iγ`: `ds±/dλ = ±1`. -/
theorem ramo_mais_deriv (g l : ℝ) :
    HasDerivAt (fun l : ℝ => (1 / 2 : ℂ) + (l : ℂ) + g * I) 1 l := by
  have := ((hasDerivAt_id l).ofReal_comp).const_add (1 / 2 : ℂ) |>.add_const ((g : ℂ) * I)
  simpa using this

theorem ramo_menos_deriv (g l : ℝ) :
    HasDerivAt (fun l : ℝ => (1 / 2 : ℂ) - (l : ℂ) + g * I) (-1) l := by
  have := ((hasDerivAt_id l).ofReal_comp).const_sub (1 / 2 : ℂ) |>.add_const ((g : ℂ) * I)
  simpa using this

/-- Aceleração nula: `d²s±/dλ² = 0`. -/
theorem ramo_aceleracao (g l : ℝ) :
    deriv (deriv (fun l : ℝ => (1 / 2 : ℂ) + (l : ℂ) + g * I)) l = 0 := by
  have : deriv (fun l : ℝ => (1 / 2 : ℂ) + (l : ℂ) + g * I) = fun _ => 1 := by
    funext x; exact (ramo_mais_deriv g x).deriv
  rw [this]; simp

/-- A separação `2|λ|` não é diferenciável no encontro (singularidade da representação). -/
theorem separacao_nao_diferenciavel : ¬ DifferentiableAt ℝ (fun l : ℝ => 2 * |l|) 0 := by
  intro h
  apply not_differentiableAt_abs_zero
  have := h.const_mul (1 / 2 : ℝ)
  convert this using 1
  funext l; ring

theorem separacao_deriv_pos {l : ℝ} (hl : 0 < l) : HasDerivAt (fun l : ℝ => 2 * |l|) 2 l := by
  have e : (fun l : ℝ => 2 * |l|) =ᶠ[𝓝 l] (fun l => 2 * l) := by
    filter_upwards [lt_mem_nhds hl] with x hx; rw [abs_of_pos hx]
  have := (hasDerivAt_id l).const_mul (2 : ℝ)
  simp only [mul_one] at this
  exact this.congr_of_eventuallyEq e

theorem separacao_deriv_neg {l : ℝ} (hl : l < 0) : HasDerivAt (fun l : ℝ => 2 * |l|) (-2) l := by
  have e : (fun l : ℝ => 2 * |l|) =ᶠ[𝓝 l] (fun l => -2 * l) := by
    filter_upwards [gt_mem_nhds hl] with x hx; rw [abs_of_neg hx]; ring
  have := (hasDerivAt_id l).const_mul (-2 : ℝ)
  simp only [mul_one] at this
  exact this.congr_of_eventuallyEq e

/-- Multiconjunto das quatro raízes. -/
noncomputable def raizes (l g : ℝ) : Multiset ℂ :=
  {1 / 2 + l + g * I, 1 / 2 + l - g * I, 1 / 2 - l + g * I, 1 / 2 - l - g * I}

/-- `G_λ` como polinômio. -/
noncomputable def Gpoly (l g : ℝ) : ℂ[X] := ((raizes l g).map fun a => X - C a).prod

theorem Gpoly_eval (l g : ℝ) (s : ℂ) : (Gpoly l g).eval s = G l g s := by
  simp only [Gpoly, raizes, Multiset.insert_eq_cons,
    Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton,
    eval_mul, eval_sub, eval_X, eval_C]
  rw [G_fatora]
  have hI : I ^ 2 = -1 := I_sq
  linear_combination (-(g : ℂ) ^ 2 * (((s - 1 / 2 - l) ^ 2 + (g : ℂ) ^ 2) +
      ((s - 1 / 2 + l) ^ 2 + (g : ℂ) ^ 2)) + (g : ℂ) ^ 4 * (I ^ 2 + 1)) * hI

theorem Gpoly_roots (l g : ℝ) : (Gpoly l g).roots = raizes l g :=
  Polynomial.roots_multiset_prod_X_sub_C _

/-- **Lei de conservação**: contados com multiplicidade, há sempre `4` zeros, para todo `λ`. -/
theorem conservacao_contagem (l g : ℝ) : (Gpoly l g).roots.card = 4 := by
  rw [Gpoly_roots]; simp [raizes]

theorem Gpoly_ne_zero (l g : ℝ) : Gpoly l g ≠ 0 := by
  intro h
  have := conservacao_contagem l g
  rw [h, Polynomial.roots_zero] at this
  simp at this

/-- **T7 — multiplicidade no encontro**: em `λ = 0` o zero `½ + iγ` tem multiplicidade `2`. -/
theorem T7_multiplicidade_dois {g : ℝ} (hg : g ≠ 0) :
    (Gpoly 0 g).rootMultiplicity (1 / 2 + g * I) = 2 := by
  classical
  rw [← Polynomial.count_roots, Gpoly_roots]
  have hne : (1 / 2 + g * I : ℂ) ≠ 1 / 2 - g * I := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hg (by linarith)
  simp only [raizes, Complex.ofReal_zero, add_zero, sub_zero, Multiset.insert_eq_cons,
    Multiset.count_cons, Multiset.count_singleton, if_neg hne]
  simp

/-- Fora do encontro (`λ ≠ 0`, `γ ≠ 0`), cada zero é simples. -/
theorem zero_simples {l g : ℝ} (hl : l ≠ 0) (hg : g ≠ 0) :
    (Gpoly l g).rootMultiplicity (1 / 2 + l + g * I) = 1 := by
  classical
  rw [← Polynomial.count_roots, Gpoly_roots]
  have h2 : (1 / 2 + l + g * I : ℂ) ≠ 1 / 2 + l - g * I := by
    intro h; have := congrArg Complex.im h; simp at this; exact hg (by linarith)
  have h3 : (1 / 2 + l + g * I : ℂ) ≠ 1 / 2 - l + g * I := by
    intro h; have := congrArg Complex.re h; simp at this; exact hl (by linarith)
  have h4 : (1 / 2 + l + g * I : ℂ) ≠ 1 / 2 - l - g * I := by
    intro h; have := congrArg Complex.re h; simp at this; exact hl (by linarith)
  simp only [raizes, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton,
    if_neg h2, if_neg h3, if_neg h4]
  simp

/-! ## 6. Geometrias -/

/-- **Corda esférica exata**: `|P(s) − P(w)|² = 4|s − w|² / ((1 + |s|²)(1 + |w|²))`. -/
theorem P_corda (s w : ℂ) :
    ((CEZ.P s).1 - (CEZ.P w).1) ^ 2 + ((CEZ.P s).2.1 - (CEZ.P w).2.1) ^ 2 +
        ((CEZ.P s).2.2 - (CEZ.P w).2.2) ^ 2 =
      4 * Complex.normSq (s - w) / ((1 + Complex.normSq s) * (1 + Complex.normSq w)) := by
  unfold CEZ.P
  have hA : 0 < 1 + Complex.normSq s := by have := Complex.normSq_nonneg s; linarith
  have hB : 0 < 1 + Complex.normSq w := by have := Complex.normSq_nonneg w; linarith
  simp only
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply] at *
  simp only [sub_re, sub_im]
  field_simp
  ring

/-- O cilindro é periódico em `Re`: não é injetivo no plano. -/
theorem Cil_periodico (s : ℂ) : Cil (s + 1) = Cil s := by
  unfold Cil
  simp only [add_re, one_re, add_im, one_im, add_zero]
  rw [show 2 * Real.pi * (s.re + 1) = 2 * Real.pi * s.re + 2 * Real.pi by ring, Real.cos_add_two_pi,
    Real.sin_add_two_pi]

/-- … mas é **injetivo na faixa** `0 < Re < 1`. -/
theorem Cil_injOn : Set.InjOn Cil {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  intro s hs w hw h
  unfold Cil at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hc, hsn, him⟩ := h
  have he : Complex.exp (((2 * Real.pi * s.re : ℝ) : ℂ) * I) =
      Complex.exp (((2 * Real.pi * w.re : ℝ) : ℂ) * I) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hsn]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hn' := congrArg Complex.im hn
  simp at hn'
  have hpi : 0 < Real.pi := Real.pi_pos
  have hdiff : s.re - w.re = n := by
    have : 2 * Real.pi * (s.re - w.re) = 2 * Real.pi * n := by linarith
    exact mul_left_cancel₀ (by positivity) this
  have h1 : (n : ℝ) < 1 := by rw [← hdiff]; linarith [hs.1, hs.2, hw.1, hw.2]
  have h2 : (-1 : ℝ) < n := by rw [← hdiff]; linarith [hs.1, hs.2, hw.1, hw.2]
  have hn0 : n = 0 := by
    have a : n < 1 := by exact_mod_cast h1
    have b : -1 < n := by exact_mod_cast h2
    omega
  rw [hn0] at hdiff
  apply Complex.ext
  · simp at hdiff; linarith
  · exact him

/-- Distância cilíndrica do par simétrico: `d_C² = (2 sin 2πδ)²`. -/
theorem Cil_dist_par (d t : ℝ) :
    ((Cil (((1 / 2 + d : ℝ) : ℂ) + t * I)).1 - (Cil (((1 / 2 - d : ℝ) : ℂ) + t * I)).1) ^ 2 +
        ((Cil (((1 / 2 + d : ℝ) : ℂ) + t * I)).2.1 - (Cil (((1 / 2 - d : ℝ) : ℂ) + t * I)).2.1) ^ 2 =
      (2 * Real.sin (2 * Real.pi * d)) ^ 2 := by
  rw [(Cil_par d t).1, (Cil_par d t).2]
  simp only
  ring

/-- Amplificação: `d_C(δ) = 2 sin 2πδ` tem derivada `4π` em `δ = 0` e `|d_C| ≤ 4π|δ|`. -/
theorem Cil_amplifica :
    HasDerivAt (fun δ : ℝ => 2 * Real.sin (2 * Real.pi * δ)) (4 * Real.pi) 0 ∧
      ∀ δ : ℝ, |2 * Real.sin (2 * Real.pi * δ)| ≤ 4 * Real.pi * |δ| := by
  refine ⟨?_, fun δ => ?_⟩
  · have h1 : HasDerivAt (fun δ : ℝ => 2 * Real.pi * δ) (2 * Real.pi) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * Real.pi)
    have := (h1.sin).const_mul (2 : ℝ)
    convert this using 1
    simp only [mul_zero, Real.cos_zero, one_mul]
    ring
  · rw [abs_mul, abs_two]
    have := Real.abs_sin_le_abs (x := 2 * Real.pi * δ)
    rw [abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos] at this
    nlinarith

/-- Cone elevado `K̃(δ, t) = (|δ| cos θ(t), |δ| sin θ(t), δ, t)`, `θ(t) = 2πt/T`. -/
noncomputable def Kt (T δ t : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (|δ| * Real.cos (2 * Real.pi * t / T), |δ| * Real.sin (2 * Real.pi * t / T), δ, t)

theorem Kt_injetiva (T : ℝ) : Function.Injective (fun p : ℝ × ℝ => Kt T p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Kt, Prod.mk.injEq] at h
  obtain ⟨-, -, h1, h2⟩ := h
  rw [h1, h2]

theorem Kt_linha (T t : ℝ) : Kt T 0 t = (0, 0, 0, t) := by simp [Kt]

/-- Como mapa de `ℂ`, `s ↦ K̃(Re s − ½, Im s)` é injetivo. -/
theorem Kt_injetiva_C (T : ℝ) : Function.Injective (fun s : ℂ => Kt T (D s) s.im) := by
  intro s w h
  simp only [Kt, Prod.mk.injEq, D] at h
  obtain ⟨-, -, h1, h2⟩ := h
  exact Complex.ext (by linarith) h2

/-- O cone tridimensional manda toda a linha crítica ao vértice. -/
theorem K_perde (θ₁ θ₂ : ℝ) : Kc 0 θ₁ = Kc 0 θ₂ := by rw [K_vertice, K_vertice]

/-- **Perda de informação**: ser zero de `G_{0,1}` não é função da imagem no cone. -/
theorem cone_nao_decide_zero :
    ¬ ∃ φ : ℝ × ℝ × ℝ → Prop, ∀ s : ℂ, (G 0 1 s = 0 ↔ φ (Kc (D s) s.im)) := by
  rintro ⟨φ, hφ⟩
  have z1 : G 0 1 (1 / 2 + I) = 0 := by simpa using (P2_critico 1).1
  have z2 : G 0 1 (1 / 2 + 2 * I) ≠ 0 := by
    rw [G_zero_quadrado]
    have : ((1 / 2 + 2 * I : ℂ) - 1 / 2) ^ 2 + ((1 : ℝ) : ℂ) ^ 2 = -3 := by
      push_cast; ring_nf; rw [I_sq]; ring
    rw [this]; norm_num
  have d1 : D (1 / 2 + I) = 0 := by simp [D]
  have d2 : D (1 / 2 + 2 * I) = 0 := by simp [D]
  have a := (hφ (1 / 2 + I)).mp z1
  rw [d1, K_perde _ (1 / 2 + 2 * I : ℂ).im, ← d2, ← hφ] at a
  exact z2 a

/-! ## 7. Taxonomia ampliada -/

/-- **Ordem por derivadas** (polinômios): se `mult_a p = m` então `p^{(k)}(a) = 0` para `k < m` e
`p^{(m)}(a) ≠ 0`. -/
theorem ordem_por_derivadas {p : ℂ[X]} (hp : p ≠ 0) {a : ℂ} {m : ℕ}
    (h : p.rootMultiplicity a = m) :
    (∀ k < m, (derivative^[k] p).IsRoot a) ∧ ¬ (derivative^[m] p).IsRoot a := by
  have low : ∀ k < m, (derivative^[k] p).IsRoot a := by
    intro k hk
    exact (Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hp).mp (h ▸ hk) k le_rfl
  refine ⟨low, fun hm => ?_⟩
  have : m < p.rootMultiplicity a := by
    apply (Polynomial.lt_rootMultiplicity_iff_isRoot_iterate_derivative hp).mpr
    intro k hk
    rcases lt_or_eq_of_le hk with hk | rfl
    · exact low k hk
    · exact hm
  omega

/-- **P-MULT**: `(z − 2)^m` tem zero de ordem exatamente `m` em `2`. -/
theorem P_mult (m : ℕ) :
    ((X - C (2 : ℂ)) ^ m).rootMultiplicity 2 = m ∧
      (∀ k < m, (derivative^[k] ((X - C (2 : ℂ)) ^ m)).IsRoot 2) ∧
        ¬ (derivative^[m] ((X - C (2 : ℂ)) ^ m)).IsRoot 2 := by
  have h := Polynomial.rootMultiplicity_X_sub_C_pow (2 : ℂ) m
  exact ⟨h, ordem_por_derivadas (pow_ne_zero _ (X_sub_C_ne_zero 2)) h⟩

/-- Forma local: `f(a + h) = hᵐ g(a + h)`. -/
theorem forma_local (q : ℂ[X]) (a h : ℂ) (m : ℕ) :
    ((X - C a) ^ m * q).eval (a + h) = h ^ m * q.eval (a + h) := by
  simp

/-- **P-POSNEG**: `(z² − a²)(z² + b²)` tem zeros `{a, −a, ib, −ib}`. -/
theorem P_posneg (a b z : ℂ) :
    (z ^ 2 - a ^ 2) * (z ^ 2 + b ^ 2) = 0 ↔ z = a ∨ z = -a ∨ z = b * I ∨ z = -(b * I) := by
  have e : (z ^ 2 - a ^ 2) * (z ^ 2 + b ^ 2) = (z - a) * (z + a) * ((z - b * I) * (z + b * I)) := by
    ring_nf; rw [I_sq]; ring
  rw [e, mul_eq_zero, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero,
    add_eq_zero_iff_eq_neg, add_eq_zero_iff_eq_neg]
  tauto

/-- **P-INFINITE**: `sin(πz) = 0 ↔ z ∈ ℤ`. -/
theorem sin_pi_zero_iff (z : ℂ) : Complex.sin (Real.pi * z) = 0 ↔ ∃ k : ℤ, z = k := by
  rw [Complex.sin_eq_zero_iff]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, mul_left_cancel₀ hπ (by rw [hk]; ring)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩

theorem sin_pi_infinitos : {z : ℂ | Complex.sin (Real.pi * z) = 0}.Infinite := by
  have hsub : Set.range (fun k : ℤ => (k : ℂ)) ⊆ {z : ℂ | Complex.sin (Real.pi * z) = 0} := by
    rintro _ ⟨k, rfl⟩
    exact (sin_pi_zero_iff _).mpr ⟨k, rfl⟩
  exact Set.Infinite.mono hsub (Set.infinite_range_of_injective Int.cast_injective)

/-- **P-INFINITY**: `f(z) = 1/z²` satisfaz `f(1/w) = w²`: zero de ordem `2` no infinito. -/
theorem zero_no_infinito (w : ℂ) : (fun z : ℂ => 1 / z ^ 2) (1 / w) = w ^ 2 := by
  simp

theorem ordem_no_infinito : (X ^ 2 : ℂ[X]).rootMultiplicity 0 = 2 := by
  simpa using Polynomial.rootMultiplicity_X_sub_C_pow (0 : ℂ) 2

/-- **P-LIMIT**: `(x² − 1)/(x − 1) → 2` quando `x → 1`, `x ≠ 1`. -/
theorem limite_cancelamento :
    Tendsto (fun x : ℝ => (x ^ 2 - 1) / (x - 1)) (𝓝[≠] 1) (𝓝 2) := by
  have h : (fun x : ℝ => x + 1) =ᶠ[𝓝[≠] (1 : ℝ)] (fun x : ℝ => (x ^ 2 - 1) / (x - 1)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    field_simp
    ring
  have t : Tendsto (fun x : ℝ => x + 1) (𝓝[≠] 1) (𝓝 2) := by
    have := ((continuous_id.add continuous_const).tendsto (1 : ℝ) : Tendsto (fun x : ℝ => x + 1) _ _)
    norm_num at this
    exact this.mono_left nhdsWithin_le_nhds
  exact t.congr' h

/-- … enquanto o valor convencional de `0/0` em Lean é `0 ≠ 2`: `0/0` não é o limite. -/
theorem zero_sobre_zero : ((1 : ℝ) ^ 2 - 1) / (1 - 1) = 0 := by norm_num

/-- O mesmo limite pela **regra de L'Hôpital**, com suas hipóteses explícitas. -/
theorem limite_lhopital :
    Tendsto (fun x : ℝ => (x ^ 2 - 1) / (x - 1)) (𝓝[≠] 1) (𝓝 2) := by
  apply HasDerivAt.lhopital_zero_nhds (f' := fun x => 2 * x) (g' := fun _ => 1)
  · exact Eventually.of_forall fun x => by simpa using (hasDerivAt_pow 2 x).sub_const 1
  · exact Eventually.of_forall fun x => by simpa using (hasDerivAt_id x).sub_const 1
  · exact Eventually.of_forall fun _ => one_ne_zero
  · have hc : Continuous (fun x : ℝ => x ^ 2 - 1) := by fun_prop
    simpa using hc.tendsto 1
  · have hc : Continuous (fun x : ℝ => x - 1) := by fun_prop
    simpa using hc.tendsto 1
  · have hc : Continuous (fun x : ℝ => 2 * x / 1) := by fun_prop
    simpa using hc.tendsto 1

/-- **P-DERIVATIVE**: derivada logarítmica de `f = (z − a)ᵐ g`: `f'/f = m/(z − a) + g'/g`. -/
theorem logDeriv_ordem {g : ℂ → ℂ} {g' a z : ℂ} (m : ℕ) (hg : HasDerivAt g g' z)
    (hz : z ≠ a) (hgz : g z ≠ 0) :
    HasDerivAt (fun w => (w - a) ^ m * g w)
      ((z - a) ^ m * g z * ((m : ℂ) / (z - a) + g' / g z)) z := by
  have h1 := ((hasDerivAt_id z).sub_const a).pow m
  have h := h1.mul hg
  have hza : z - a ≠ 0 := sub_ne_zero.mpr hz
  convert h using 1
  · funext w; simp
  · simp only [id, Pi.pow_apply, mul_one]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [pow_zero, Nat.cast_zero, zero_div, zero_add, one_mul, zero_mul]
      field_simp
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      field_simp
      try ring

/-- **Princípio do argumento** para um zero de ordem `m`: se `g` é holomorfa numa bola aberta que
contém o disco fechado `|z − c| ≤ R` e não se anula nele, e `|a − c| < R`, então
`∮ f'/f = 2πi·m` para `f = (z − a)ᵐ g`. -/
theorem argumento_ordem {g : ℂ → ℂ} {c a : ℂ} {R R' : ℝ} (m : ℕ) (hR : 0 < R) (hRR : R < R')
    (hg : DifferentiableOn ℂ g (Metric.ball c R'))
    (hg0 : ∀ z ∈ Metric.closedBall c R, g z ≠ 0) (ha : a ∈ Metric.ball c R) :
    ∮ z in C(c, R), deriv (fun w => (w - a) ^ m * g w) z / ((z - a) ^ m * g z) =
      2 * Real.pi * I * m := by
  have hsub : Metric.closedBall c R ⊆ Metric.ball c R' := Metric.closedBall_subset_ball hRR
  have hdg : DifferentiableOn ℂ (deriv g) (Metric.ball c R') := hg.deriv Metric.isOpen_ball
  -- no círculo, f'/f = m/(z − a) + g'/g
  have hEq : Set.EqOn (fun z => deriv (fun w => (w - a) ^ m * g w) z / ((z - a) ^ m * g z))
      (fun z => (m : ℂ) * (z - a)⁻¹ + deriv g z / g z) (Metric.sphere c R) := by
    intro z hz
    have hzb : z ∈ Metric.closedBall c R := Metric.sphere_subset_closedBall hz
    have hza : z ≠ a := by
      rintro rfl
      rw [Metric.mem_sphere] at hz
      rw [Metric.mem_ball] at ha
      linarith
    have hgd : HasDerivAt g (deriv g z) z :=
      ((hg z (hsub hzb)).differentiableAt (Metric.isOpen_ball.mem_nhds (hsub hzb))).hasDerivAt
    have hd := logDeriv_ordem m hgd hza (hg0 z hzb)
    simp only
    rw [hd.deriv]
    have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
    have hgz := hg0 z hzb
    field_simp
    try ring
  rw [circleIntegral.integral_congr hR.le hEq]
  have hc1 : CircleIntegrable (fun z => (m : ℂ) * (z - a)⁻¹) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    apply continuousOn_const.mul
    apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
    intro z hz h
    have h' : z = a := sub_eq_zero.mp (by simpa using h)
    subst h'
    rw [Metric.mem_sphere] at hz
    rw [Metric.mem_ball] at ha
    linarith
  have hcont : ContinuousOn (fun z => deriv g z / g z) (Metric.closedBall c R) := by
    apply ContinuousOn.div (hdg.continuousOn.mono hsub) (hg.continuousOn.mono hsub) hg0
  have hc2 : CircleIntegrable (fun z => deriv g z / g z) c R :=
    ContinuousOn.circleIntegrable hR.le (hcont.mono Metric.sphere_subset_closedBall)
  rw [circleIntegral.integral_add hc1 hc2, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_inv_of_mem_ball ha]
  have h0 : ∮ z in C(c, R), deriv g z / g z = 0 := by
    apply circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le Set.countable_empty hcont
    intro z hz
    have hzb : z ∈ Metric.ball c R' := hsub (Metric.ball_subset_closedBall hz.1)
    have hn := Metric.isOpen_ball.mem_nhds hzb
    exact ((hdg z hzb).differentiableAt hn).div ((hg z hzb).differentiableAt hn)
      (hg0 z (Metric.ball_subset_closedBall hz.1))
  rw [h0]
  ring

/-! ### Exemplo do princípio do argumento: `N_Z − N_P = 5 − 2 = 3` -/

/-- `f(z) = (z − 1)³(z + 2)² / (z²(z − 4))`. -/
noncomputable def fArg (z : ℂ) : ℂ := (z - 1) ^ 3 * (z + 2) ^ 2 / (z ^ 2 * (z - 4))

/-- Derivada logarítmica `3/(z−1) + 2/(z+2) − 2/z − 1/(z−4)`. -/
noncomputable def Larg (z : ℂ) : ℂ := 3 / (z - 1) + 2 / (z + 2) - 2 / z - 1 / (z - 4)

theorem fArg_hasDerivAt {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) (h2 : z ≠ -2) (h4 : z ≠ 4) :
    HasDerivAt fArg (fArg z * Larg z) z := by
  have hu : HasDerivAt (fun z : ℂ => (z - 1) ^ 3 * (z + 2) ^ 2)
      (3 * (z - 1) ^ 2 * (z + 2) ^ 2 + (z - 1) ^ 3 * (2 * (z + 2))) z := by
    have a := ((hasDerivAt_id z).sub_const 1).pow 3
    have b := ((hasDerivAt_id z).add_const 2).pow 2
    convert a.mul b using 1
    · funext w; simp
    · simp
      try ring
  have hv : HasDerivAt (fun z : ℂ => z ^ 2 * (z - 4)) (2 * z * (z - 4) + z ^ 2) z := by
    have a := (hasDerivAt_id z).pow 2
    have b := (hasDerivAt_id z).sub_const 4
    convert a.mul b using 1
    · funext w; simp
    · simp
      try ring
  have hz4 : z - 4 ≠ 0 := sub_ne_zero.mpr h4
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hz2 : z + 2 ≠ 0 := by intro h; apply h2; linear_combination h
  have hvne : z ^ 2 * (z - 4) ≠ 0 := mul_ne_zero (pow_ne_zero 2 h0) hz4
  convert hu.div hv hvne using 1
  · funext w; simp [fArg]
  · unfold fArg Larg
    field_simp
    try ring

theorem fArg_ne {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) (h2 : z ≠ -2) (h4 : z ≠ 4) : fArg z ≠ 0 := by
  have hz4 : z - 4 ≠ 0 := sub_ne_zero.mpr h4
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hz2 : z + 2 ≠ 0 := by intro h; apply h2; linear_combination h
  unfold fArg
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ hz1) (pow_ne_zero _ hz2))
    (mul_ne_zero (pow_ne_zero _ h0) hz4)

theorem esfera3 {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) 3) :
    z ≠ 0 ∧ z ≠ 1 ∧ z ≠ -2 ∧ z ≠ 4 := by
  rw [mem_sphere_zero_iff_norm] at hz
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> norm_num at hz

theorem ci_termo (c w : ℂ) (hw : ‖w‖ ≠ 3) : CircleIntegrable (fun z => c * (z - w)⁻¹) 0 3 := by
  apply ContinuousOn.circleIntegrable (by norm_num)
  apply continuousOn_const.mul
  apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
  intro z hz h
  have h' : z = w := sub_eq_zero.mp (by simpa using h)
  subst h'
  rw [mem_sphere_zero_iff_norm] at hz
  exact hw hz

theorem integral_fora : ∮ z in C(0, 3), (z - 4)⁻¹ = 0 := by
  have hc : ContinuousOn (fun z : ℂ => (z - 4)⁻¹) (Metric.closedBall 0 3) := by
    apply ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const)
    intro z hz h
    have h' : z = 4 := sub_eq_zero.mp (by simpa using h)
    subst h'
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    norm_num at hz
  apply circleIntegral_eq_zero_of_differentiable_on_off_countable (by norm_num)
    Set.countable_empty hc
  intro z hz
  have hz' : ‖z‖ < 3 := by simpa using hz.1
  have : z - 4 ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; subst h; norm_num at hz'
  exact (differentiableAt_id.sub_const 4).inv this

theorem integral_Larg : ∮ z in C(0, 3), Larg z = 2 * Real.pi * I * 3 := by
  have e : ∀ z, Larg z = ((3 : ℂ) * (z - 1)⁻¹ + (2 : ℂ) * (z - (-2))⁻¹) - (2 : ℂ) * (z - 0)⁻¹ -
      (1 : ℂ) * (z - 4)⁻¹ := by
    intro z; unfold Larg; simp only [sub_neg_eq_add, sub_zero, div_eq_mul_inv]
  simp_rw [e]
  have i1 := ci_termo 3 1 (by norm_num)
  have i2 := ci_termo 2 (-2) (by norm_num)
  have i3 := ci_termo 2 0 (by norm_num)
  have i4 := ci_termo 1 4 (by norm_num)
  have i12 : CircleIntegrable (fun z : ℂ => 3 * (z - 1)⁻¹ + 2 * (z - -2)⁻¹) 0 3 := i1.add i2
  have i123 : CircleIntegrable
      (fun z : ℂ => 3 * (z - 1)⁻¹ + 2 * (z - -2)⁻¹ - 2 * (z - 0)⁻¹) 0 3 := i12.sub i3
  rw [circleIntegral.integral_sub i123 i4, circleIntegral.integral_sub i12 i3,
    circleIntegral.integral_add i1 i2]
  simp only [circleIntegral.integral_const_mul]
  have b1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) 3 := by norm_num [Metric.mem_ball]
  have b2 : (-2 : ℂ) ∈ Metric.ball (0 : ℂ) 3 := by norm_num [Metric.mem_ball]
  have b3 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 3 := by simp [Metric.mem_ball]
  rw [circleIntegral.integral_sub_inv_of_mem_ball b1,
    circleIntegral.integral_sub_inv_of_mem_ball b2,
    circleIntegral.integral_sub_inv_of_mem_ball b3, integral_fora]
  ring

/-- Zeros dentro de `|z| = 3` (com multiplicidade) e polos dentro. -/
def zerosDentro : Multiset ℂ := {1, 1, 1, -2, -2}
def polosDentro : Multiset ℂ := {0, 0}

/-- **Exemplo do princípio do argumento**: `(1/2πi) ∮_{|z|=3} f'/f = N_Z − N_P = 5 − 2 = 3`. -/
theorem principio_argumento_exemplo :
    (2 * Real.pi * I)⁻¹ * ∮ z in C(0, 3), deriv fArg z / fArg z =
      (Multiset.card zerosDentro : ℂ) - Multiset.card polosDentro ∧
    (Multiset.card zerosDentro : ℂ) - Multiset.card polosDentro = 3 := by
  have hEq : Set.EqOn (fun z => deriv fArg z / fArg z) Larg (Metric.sphere 0 3) := by
    intro z hz
    obtain ⟨h0, h1, h2, h4⟩ := esfera3 hz
    simp only
    rw [(fArg_hasDerivAt h0 h1 h2 h4).deriv]
    field_simp [fArg_ne h0 h1 h2 h4]
  have hc : (Multiset.card zerosDentro : ℂ) - Multiset.card polosDentro = 3 := by
    simp [zerosDentro, polosDentro]; norm_num
  refine ⟨?_, hc⟩
  rw [hc, circleIntegral.integral_congr (by norm_num) hEq, integral_Larg]
  have : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp

/-- **P-TRUNCATION**: `f(x) = x − 1/3` em `0,33` vale `−1/300 ≠ 0`. -/
theorem truncamento_033 : (33 / 100 : ℚ) - 1 / 3 = -1 / 300 := by norm_num

/-- Nenhum truncamento decimal de `1/3` é zero exato de `x − 1/3`. -/
theorem truncamento_nunca_zero (n : ℕ) : ((⌊(10 : ℚ) ^ n / 3⌋ : ℚ) / 10 ^ n) ≠ 1 / 3 := by
  intro h
  set q := ⌊(10 : ℚ) ^ n / 3⌋
  have h10 : (10 : ℚ) ^ n ≠ 0 := by positivity
  have hq : (3 * q : ℚ) = 10 ^ n := by
    field_simp at h
    linarith
  have hz : (3 * q : ℤ) = ((10 ^ n : ℕ) : ℤ) := by exact_mod_cast hq
  have hd : ((3 : ℕ) : ℤ) ∣ ((10 ^ n : ℕ) : ℤ) := ⟨q, by rw [← hz]; norm_num⟩
  have h3 : 3 ∣ 10 ^ n := Int.natCast_dvd_natCast.mp hd
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  norm_num at this

/-- Zeros aparentes: `f_N(x) = x − 1/N` tem zero `1/N ≠ 0`, e `1/N → 0`, o zero de `f(x) = x`. -/
theorem zeros_aparentes :
    (∀ N : ℕ, 0 < N → (1 / (N : ℝ)) - 1 / N = 0 ∧ (1 / (N : ℝ)) ≠ 0) ∧
      Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
  ⟨fun N hN => ⟨sub_self _, by positivity⟩, tendsto_one_div_atTop_nhds_zero_nat⟩

/-- **Teorema da identidade**: zeros que se acumulam forçam `f ≡ 0` (função inteira). -/
theorem zeros_acumulam {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) {z₀ : ℂ}
    (h : ∃ᶠ z in 𝓝[≠] z₀, f z = 0) : f = 0 := by
  funext z
  exact hf.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ _) h
    (Set.mem_univ z)

/-- **Multiplicidade infinita** de função inteira ⇒ `f ≡ 0`. -/
theorem multiplicidade_infinita {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) {z₀ : ℂ}
    (h : analyticOrderAt f z₀ = ⊤) : f = 0 := by
  rw [analyticOrderAt_eq_top] at h
  exact zeros_acumulam hf (z₀ := z₀) (h.filter_mono nhdsWithin_le_nhds).frequently

/-! ## 8. Registro de zero e porta Universal Green -/

/-- Registro multidimensional de um zero de um polinômio: existência, posição, ordem, parceiro
simétrico, todos com prova. -/
structure RegistroZero (p : ℂ[X]) (z : ℂ) where
  naLinha : Bool
  ordem : ℕ
  parceiro : ℂ
  h_zero : p.eval z = 0
  h_linha : naLinha = true ↔ z.re = 1 / 2
  h_ordem : p.rootMultiplicity z = ordem
  h_parceiro : parceiro = torcao z ∧ p.eval parceiro = 0

/-- Registro de um zero **externo simples** de `G_{d,γ}`. -/
noncomputable def registroExterno {d γ : ℝ} (hd : d ≠ 0) (hg : γ ≠ 0) :
    RegistroZero (Gpoly d γ) (1 / 2 + d + γ * I) where
  naLinha := false
  ordem := 1
  parceiro := 1 / 2 - d + γ * I
  h_zero := by rw [Gpoly_eval]; exact (P1 d γ).1
  h_linha := by
    simp only [Bool.false_eq_true, false_iff]
    exact G_externo hd (P1 d γ).1
  h_ordem := zero_simples hd hg
  h_parceiro := by
    refine ⟨?_, by rw [Gpoly_eval]; exact (P1 d γ).2.2.1⟩
    simp only [torcao, map_add, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, map_mul,
      Complex.conj_I]
    ring

/-- Registro do zero **crítico duplo** de `G_{0,γ}` no encontro. -/
noncomputable def registroCriticoDuplo {γ : ℝ} (hg : γ ≠ 0) :
    RegistroZero (Gpoly 0 γ) (1 / 2 + γ * I) where
  naLinha := true
  ordem := 2
  parceiro := 1 / 2 + γ * I
  h_zero := by rw [Gpoly_eval]; exact (P2_critico γ).1
  h_linha := by simp
  h_ordem := T7_multiplicidade_dois hg
  h_parceiro := by
    refine ⟨?_, by rw [Gpoly_eval]; exact (P2_critico γ).1⟩
    simp only [torcao, map_add, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, map_mul,
      Complex.conj_I]
    ring

/-- **Porta `UG_modelo`**: conjunção dos resultados do escopo do modelo. -/
def UGModelo : Prop :=
  (∀ (F : ℂ → ℂ) (s : ℂ), Critico F s ∨ Externo F s ∨ NaoZeroC F s ∨ NaoZeroE F s) ∧
  (∀ (F : ℂ → ℂ) (s : ℂ), ¬ (Critico F s ∧ Externo F s)) ∧
  (∀ γ : ℝ, γ ≠ 0 → Critico (G 0 γ) (1 / 2 + γ * I) ∧ Externo (G 1 γ) (1 / 2 + 1 + γ * I) ∧
    NaoZeroC (G 0 γ) (1 / 2) ∧ NaoZeroE (G 0 γ) 2) ∧
  (∀ (F : ℂ → ℂ) (s m : ℂ) (r : ℝ), ‖F s - m‖ ≤ r → Certificado F s (checar m r)) ∧
  (∀ l g : ℝ, (Gpoly l g).roots.card = 4) ∧
  (∀ g : ℝ, g ≠ 0 → (Gpoly 0 g).rootMultiplicity (1 / 2 + g * I) = 2) ∧
  Function.Injective CEZ.P ∧ Set.InjOn Cil {s : ℂ | 0 < s.re ∧ s.re < 1} ∧
  (∀ T : ℝ, Function.Injective (fun s : ℂ => Kt T (D s) s.im)) ∧
  (¬ ∃ φ : ℝ × ℝ × ℝ → Prop, ∀ s : ℂ, (G 0 1 s = 0 ↔ φ (Kc (D s) s.im))) ∧
  ((2 * Real.pi * I)⁻¹ * ∮ z in C(0, 3), deriv fArg z / fArg z = 3)

theorem ug_modelo : UGModelo := by
  refine ⟨classificacao, ambos_pontual_impossivel, fun γ hγ => ⟨P2_critico γ, ?_, P5_NC 0 hγ,
    P5_NE 0 hγ⟩, fun F s m r h => checar_correto h, conservacao_contagem,
    fun g hg => T7_multiplicidade_dois hg, P_injetiva, Cil_injOn, Kt_injetiva_C,
    cone_nao_decide_zero, ?_⟩
  · simpa using P3_externo one_ne_zero γ
  · rw [principio_argumento_exemplo.1, principio_argumento_exemplo.2]

/-- **Escopo zeta**: a completude classificatória é uma tautologia (`HR ∨ ¬HR`) e não decide nada;
o conteúdo do escopo zeta é exatamente `HR ↔ ZE = ∅`. -/
theorem escopo_zeta : (RiemannHypothesis ∨ ¬ RiemannHypothesis) ∧
    (RiemannHypothesis ↔ ZE = ∅) :=
  ⟨em _, rh_iff_externa_vazia⟩

end ATK.ClosedMath

-- Auditoria de axiomas (kernel): cada teorema deve depender só de propext, Classical.choice, Quot.sound.
#print axioms ATK.ClosedMath.classificacao
#print axioms ATK.ClosedMath.exclusivos
#print axioms ATK.ClosedMath.ambos_pontual_impossivel
#print axioms ATK.ClosedMath.critico_iff_estado
#print axioms ATK.ClosedMath.externo_iff_estado
#print axioms ATK.ClosedMath.checar_correto
#print axioms ATK.ClosedMath.checar_nunca_zero
#print axioms ATK.ClosedMath.checar_exato_indet
#print axioms ATK.ClosedMath.nao_zero_certificavel
#print axioms ATK.ClosedMath.zero_sempre_indeterminado
#print axioms ATK.ClosedMath.indeterminado_nao_e_estado
#print axioms ATK.ClosedMath.checarIC_correto
#print axioms ATK.ClosedMath.checarIC_correto'
#print axioms ATK.ClosedMath.J_J
#print axioms ATK.ClosedMath.S_S
#print axioms ATK.ClosedMath.R_J
#print axioms ATK.ClosedMath.J_R
#print axioms ATK.ClosedMath.R_S
#print axioms ATK.ClosedMath.S_R
#print axioms ATK.ClosedMath.J_S
#print axioms ATK.ClosedMath.klein
#print axioms ATK.ClosedMath.T_nao_comuta_R
#print axioms ATK.ClosedMath.T3
#print axioms ATK.ClosedMath.T4_centro
#print axioms ATK.ClosedMath.T5_separacao
#print axioms ATK.ClosedMath.T6_coincidencia
#print axioms ATK.ClosedMath.troca_par
#print axioms ATK.ClosedMath.transporte
#print axioms ATK.ClosedMath.fator_real_ne
#print axioms ATK.ClosedMath.P1
#print axioms ATK.ClosedMath.P2_critico
#print axioms ATK.ClosedMath.P3_externo
#print axioms ATK.ClosedMath.P4_ambos
#print axioms ATK.ClosedMath.P5_NE
#print axioms ATK.ClosedMath.P5_NC
#print axioms ATK.ClosedMath.G_meio
#print axioms ATK.ClosedMath.T8_habitantes
#print axioms ATK.ClosedMath.zeros_invariantes
#print axioms ATK.ClosedMath.simetria_compativel_com_ambos
#print axioms ATK.ClosedMath.G_quartica
#print axioms ATK.ClosedMath.ramo_mais_deriv
#print axioms ATK.ClosedMath.ramo_menos_deriv
#print axioms ATK.ClosedMath.ramo_aceleracao
#print axioms ATK.ClosedMath.separacao_nao_diferenciavel
#print axioms ATK.ClosedMath.separacao_deriv_pos
#print axioms ATK.ClosedMath.separacao_deriv_neg
#print axioms ATK.ClosedMath.Gpoly_eval
#print axioms ATK.ClosedMath.Gpoly_roots
#print axioms ATK.ClosedMath.conservacao_contagem
#print axioms ATK.ClosedMath.Gpoly_ne_zero
#print axioms ATK.ClosedMath.T7_multiplicidade_dois
#print axioms ATK.ClosedMath.zero_simples
#print axioms ATK.ClosedMath.P_corda
#print axioms ATK.ClosedMath.Cil_periodico
#print axioms ATK.ClosedMath.Cil_injOn
#print axioms ATK.ClosedMath.Cil_dist_par
#print axioms ATK.ClosedMath.Cil_amplifica
#print axioms ATK.ClosedMath.Kt_injetiva
#print axioms ATK.ClosedMath.Kt_linha
#print axioms ATK.ClosedMath.Kt_injetiva_C
#print axioms ATK.ClosedMath.K_perde
#print axioms ATK.ClosedMath.cone_nao_decide_zero
#print axioms ATK.ClosedMath.ordem_por_derivadas
#print axioms ATK.ClosedMath.P_mult
#print axioms ATK.ClosedMath.forma_local
#print axioms ATK.ClosedMath.P_posneg
#print axioms ATK.ClosedMath.sin_pi_zero_iff
#print axioms ATK.ClosedMath.sin_pi_infinitos
#print axioms ATK.ClosedMath.zero_no_infinito
#print axioms ATK.ClosedMath.ordem_no_infinito
#print axioms ATK.ClosedMath.limite_cancelamento
#print axioms ATK.ClosedMath.zero_sobre_zero
#print axioms ATK.ClosedMath.limite_lhopital
#print axioms ATK.ClosedMath.logDeriv_ordem
#print axioms ATK.ClosedMath.argumento_ordem
#print axioms ATK.ClosedMath.fArg_hasDerivAt
#print axioms ATK.ClosedMath.fArg_ne
#print axioms ATK.ClosedMath.esfera3
#print axioms ATK.ClosedMath.ci_termo
#print axioms ATK.ClosedMath.integral_fora
#print axioms ATK.ClosedMath.integral_Larg
#print axioms ATK.ClosedMath.principio_argumento_exemplo
#print axioms ATK.ClosedMath.truncamento_033
#print axioms ATK.ClosedMath.truncamento_nunca_zero
#print axioms ATK.ClosedMath.zeros_aparentes
#print axioms ATK.ClosedMath.zeros_acumulam
#print axioms ATK.ClosedMath.multiplicidade_infinita
#print axioms ATK.ClosedMath.ug_modelo
#print axioms ATK.ClosedMath.escopo_zeta
