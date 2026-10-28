/-
ATK-I — Transformações certificadas: fidelidade semântica, cinco classes, não colapso,
controle ω, composição, cota uniforme, obstrução modular e famílias de transformações.

Formaliza os textos "Transformações que preservam a verdade e podem produzir certificados" e
"Famílias de transformações matemáticas":

* §1 fidelidade `∀ x, P x ⟺ Q (T x)` e **transporte de provas**: `∀ y ∈ T(X), Q y ⇒ ∀ x, P x`;
* §2 cinco classes — equivalência = suficiência ∧ necessidade; contração; **obstrução**
     (necessidade + `¬Q(Tx)` ⇒ `¬P x`);
* §3 **não colapso** `d(Tx) ≥ c·d(x)`, c > 0 ⇒ `d(Tx) = 0 → d(x) = 0`; o colapso constante não informa;
* §4 **controle ω** (`ω 0 = 0`, `ω r > 0` para r > 0): `d_Y(Tx) ≥ ω(d_X x)` ⇒ mesmo fechamento;
* §8 **composição**: não colapso com c₁, c₂ ⇒ não colapso com c₁c₂; controles ω compõem
     (com ω₂ monótona); fidelidade compõe;
* exemplo `R(3,5)`: `d = 2`, `T_3 R = R(9,15)` com `d = 6`, `R(0,3; 0,5)` com `d = 1/5`, e
  `T_n R = R(3/n, 5/n)` com `d = 2/n > 0 → 0` mas `R(3,5)` falsa — e **nenhuma** cota uniforme
  `d(T_n R) ≥ c·d(R)` com c > 0 vale; **com** cota uniforme, `d(T_n x) → 0` ⇒ `d(x) = 0`;
* exemplo A (Beal): `2³ + 3³ = 35 ≢ 27 = 3³ (mod 3)` — obstrução modular; a redução mod m é
  necessária, não fiel;
* famílias: `f` aplicada aos dois lados é sempre **necessária**, e é **fiel ⟺ f injetiva**
  (no domínio): translação, escala, afim, potências ímpares, exp, log em (0,∞), isometrias,
  homeomorfismos, lineares injetivas; potências pares e redução modular não são fiéis;
* objeto `TransformacaoCertificada (X, Y, P, Q, T, π)` com composição e transporte.

Nada aqui fecha uma conjectura: o que o kernel certifica é a lógica do transporte.
Certificados terminais: 0/7.
-/
import ATK.RelacionalI
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Algebra.Order.Ring.Abs

namespace ATK.RelacionalTransporte

open Filter Topology ATK.RelacionalI

section Classes

variable {X Y Z : Type*}

/-! ### §1–2 Fidelidade e as cinco classes -/

/-- Equivalência (fidelidade semântica): `∀ x, P x ⟺ Q (T x)`. -/
def Fiel (P : X → Prop) (Q : Y → Prop) (T : X → Y) : Prop := ∀ x, P x ↔ Q (T x)

/-- Suficiência: `Q (T x) ⇒ P x`. -/
def Suficiente (P : X → Prop) (Q : Y → Prop) (T : X → Y) : Prop := ∀ x, Q (T x) → P x

/-- Necessidade: `P x ⇒ Q (T x)`. -/
def Necessaria (P : X → Prop) (Q : Y → Prop) (T : X → Y) : Prop := ∀ x, P x → Q (T x)

theorem fiel_iff (P : X → Prop) (Q : Y → Prop) (T : X → Y) :
    Fiel P Q T ↔ Suficiente P Q T ∧ Necessaria P Q T :=
  ⟨fun h => ⟨fun x hx => (h x).mpr hx, fun x hx => (h x).mp hx⟩,
    fun h x => ⟨h.2 x, h.1 x⟩⟩

/-- **Transporte de provas**: se `Q` vale em toda a imagem de `T`, então `P` vale em todo `X`. -/
theorem transporte_prova {P : X → Prop} {Q : Y → Prop} {T : X → Y} (h : Fiel P Q T)
    (hQ : ∀ y ∈ Set.range T, Q y) : ∀ x, P x :=
  fun x => (h x).mpr (hQ (T x) ⟨x, rfl⟩)

/-- Suficiência basta para provar o original por uma condição mais forte. -/
theorem transporte_suficiente {P : X → Prop} {Q : Y → Prop} {T : X → Y} (h : Suficiente P Q T)
    (hQ : ∀ x, Q (T x)) : ∀ x, P x :=
  fun x => h x (hQ x)

/-- **Obstrução**: necessidade + `¬Q(Tx)` exclui `x`. -/
theorem obstrucao {P : X → Prop} {Q : Y → Prop} {T : X → Y} (h : Necessaria P Q T) {x : X}
    (hx : ¬ Q (T x)) : ¬ P x :=
  fun hp => hx (h x hp)

theorem fiel_comp {P : X → Prop} {Q : Y → Prop} {W : Z → Prop} {T : X → Y} {S : Y → Z}
    (hT : Fiel P Q T) (hS : Fiel Q W S) : Fiel P W (S ∘ T) :=
  fun x => (hT x).trans (hS (T x))

theorem suficiente_comp {P : X → Prop} {Q : Y → Prop} {W : Z → Prop} {T : X → Y} {S : Y → Z}
    (hT : Suficiente P Q T) (hS : Suficiente Q W S) : Suficiente P W (S ∘ T) :=
  fun x h => hT x (hS (T x) h)

theorem necessaria_comp {P : X → Prop} {Q : Y → Prop} {W : Z → Prop} {T : X → Y} {S : Y → Z}
    (hT : Necessaria P Q T) (hS : Necessaria Q W S) : Necessaria P W (S ∘ T) :=
  fun x h => hS (T x) (hT x h)

/-! ### §3–4 Não colapso e controle ω -/

/-- Não colapso com constante c: `c · d_X x ≤ d_Y (T x)`. -/
def NaoColapso (dX : X → ℝ) (dY : Y → ℝ) (T : X → Y) (c : ℝ) : Prop :=
  ∀ x, c * dX x ≤ dY (T x)

/-- **Lei de não colapso**: c > 0 e `d_Y(Tx) = 0` ⇒ `d_X(x) = 0`. -/
theorem nao_colapso_fecha {dX : X → ℝ} {dY : Y → ℝ} {T : X → Y} {c : ℝ} (hc : 0 < c)
    (hX : ∀ x, 0 ≤ dX x) (h : NaoColapso dX dY T c) {x : X} (h0 : dY (T x) = 0) : dX x = 0 := by
  have h1 := h x
  rw [h0] at h1
  have h2 := hX x
  nlinarith

/-- O colapso constante (`d_Y ∘ T ≡ 0`) não informa nada: ele satisfaz `d_Y(Tx) = 0` para
todo x, inclusive para x com defeito positivo. -/
theorem colapso_nao_informa {dX : X → ℝ} {dY : Y → ℝ} {T : X → Y} (h : ∀ x, dY (T x) = 0)
    {x : X} (hx : 0 < dX x) : dY (T x) = 0 ∧ dX x ≠ 0 :=
  ⟨h x, hx.ne'⟩

/-- **Composição** de não colapsos: `c₁, c₂` ⇒ `c₁ c₂`. -/
theorem nao_colapso_comp {dX : X → ℝ} {dY : Y → ℝ} {dZ : Z → ℝ} {T : X → Y} {S : Y → Z}
    {c₁ c₂ : ℝ} (hc₂ : 0 ≤ c₂) (h₁ : NaoColapso dX dY T c₁) (h₂ : NaoColapso dY dZ S c₂) :
    NaoColapso dX dZ (S ∘ T) (c₁ * c₂) := by
  intro x
  have a := h₁ x
  have b := h₂ (T x)
  calc c₁ * c₂ * dX x = c₂ * (c₁ * dX x) := by ring
    _ ≤ c₂ * dY (T x) := mul_le_mul_of_nonneg_left a hc₂
    _ ≤ dZ (S (T x)) := b

/-- Função de controle: `ω 0 = 0` e `ω r > 0` para `r > 0`. -/
def Controle (ω : ℝ → ℝ) : Prop := ω 0 = 0 ∧ ∀ r, 0 < r → 0 < ω r

/-- **Lei de não colapso generalizada**: `d_Y(Tx) ≥ ω(d_X x)` ⇒ `d_Y(Tx) = 0 → d_X x = 0`. -/
theorem controle_fecha {dX : X → ℝ} {dY : Y → ℝ} {T : X → Y} {ω : ℝ → ℝ} (hω : Controle ω)
    (hX : ∀ x, 0 ≤ dX x) (h : ∀ x, ω (dX x) ≤ dY (T x)) {x : X} (h0 : dY (T x) = 0) :
    dX x = 0 := by
  by_contra hne
  have hpos : 0 < dX x := lt_of_le_of_ne (hX x) (Ne.symm hne)
  have := hω.2 _ hpos
  have h1 := h x
  rw [h0] at h1
  linarith

/-- Controles compõem quando `ω₂` é monótona. -/
theorem controle_comp {ω₁ ω₂ : ℝ → ℝ} (h₁ : Controle ω₁) (h₂ : Controle ω₂) :
    Controle (ω₂ ∘ ω₁) :=
  ⟨by simp [Function.comp, h₁.1, h₂.1], fun r hr => h₂.2 _ (h₁.2 r hr)⟩

theorem controle_cadeia {dX : X → ℝ} {dY : Y → ℝ} {dZ : Z → ℝ} {T : X → Y} {S : Y → Z}
    {ω₁ ω₂ : ℝ → ℝ} (hmono : Monotone ω₂) (h₁ : ∀ x, ω₁ (dX x) ≤ dY (T x))
    (h₂ : ∀ y, ω₂ (dY y) ≤ dZ (S y)) : ∀ x, (ω₂ ∘ ω₁) (dX x) ≤ dZ ((S ∘ T) x) :=
  fun x => (hmono (h₁ x)).trans (h₂ (T x))

/-- **Cota uniforme**: se `d(T_n x) ≥ c·d(x)` para todo n, com c > 0 independente de n, e
`d(T_n x) → 0`, então `d(x) = 0`. -/
theorem cota_uniforme {dX : X → ℝ} {dY : Y → ℝ} {T : ℕ → X → Y} {c : ℝ} (hc : 0 < c)
    {x : X} (hX : 0 ≤ dX x) (h : ∀ n, c * dX x ≤ dY (T n x))
    (hlim : Tendsto (fun n => dY (T n x)) atTop (𝓝 0)) : dX x = 0 := by
  have : c * dX x ≤ 0 := ge_of_tendsto' hlim h
  nlinarith

end Classes

/-! ### Exemplo calculado R(3,5) -/

/-- `d R(3,5) = 2`; `T_3 R = R(9,15)` com `d = 6 = 3·2`; `R(0,3; 0,5)` com `d = 1/5`. -/
theorem exemplo_3_5 :
    d ((3 : ℝ), (5 : ℝ)) = 2 ∧ escala (3 : ℝ) (3, 5) = (9, 15) ∧ d (escala (3 : ℝ) (3, 5)) = 6 ∧
      d (escala (1 / 10 : ℝ) (3, 5)) = 1 / 5 ∧ ¬ Verdadeira ((3 : ℝ), (5 : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold d; norm_num
  · unfold escala; norm_num
  · rw [d_escala]; unfold d; norm_num
  · rw [d_escala]; unfold d; norm_num
  · unfold Verdadeira; norm_num

/-- `T_n R = R(3/(n+1), 5/(n+1))`: defeito `2/(n+1) > 0`, tende a 0, e `R(3,5)` é falsa. -/
theorem escalas_degeneram :
    (∀ n : ℕ, d (escala (1 / ((n : ℝ) + 1)) ((3 : ℝ), (5 : ℝ))) = 2 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, 0 < d (escala (1 / ((n : ℝ) + 1)) ((3 : ℝ), (5 : ℝ)))) ∧
      Tendsto (fun n : ℕ => d (escala (1 / ((n : ℝ) + 1)) ((3 : ℝ), (5 : ℝ)))) atTop (𝓝 0) ∧
      ¬ Verdadeira ((3 : ℝ), (5 : ℝ)) := by
  have hd : ∀ n : ℕ, d (escala (1 / ((n : ℝ) + 1)) ((3 : ℝ), (5 : ℝ))) = 2 / ((n : ℝ) + 1) := by
    intro n
    rw [d_escala]
    have h1 : d ((3 : ℝ), (5 : ℝ)) = 2 := by unfold d; norm_num
    rw [h1, Real.norm_eq_abs, abs_of_pos (by positivity)]
    ring
  refine ⟨hd, fun n => by rw [hd]; positivity, ?_, by unfold Verdadeira; norm_num⟩
  simp_rw [hd]
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 := h1.const_mul 2
  rw [mul_zero] at h2
  refine h2.congr fun n => ?_
  ring

/-- … e **nenhuma** cota uniforme `d(T_n R) ≥ c·d(R)` com `c > 0` vale para essa família. -/
theorem sem_cota_uniforme :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
      c * d ((3 : ℝ), (5 : ℝ)) ≤ d (escala (1 / ((n : ℝ) + 1)) ((3 : ℝ), (5 : ℝ))) := by
  rintro ⟨c, hc, h⟩
  obtain ⟨-, -, hlim, hfalse⟩ := escalas_degeneram
  have h0 := cota_uniforme (dX := d) (dY := d)
    (T := fun n => escala (1 / ((n : ℝ) + 1))) hc (d_nonneg _) h hlim
  exact hfalse ((d_eq_zero_iff _).mp h0)

/-! ### Exemplo A — Beal: obstrução modular -/

/-- A redução mod m é **necessária**: `a = b ⇒ a ≡ b (mod m)`. -/
theorem reducao_modular_necessaria (m : ℕ) :
    Necessaria (fun R : ℤ × ℤ => R.1 = R.2) (fun R : ZMod m × ZMod m => R.1 = R.2)
      (fun R => ((R.1 : ZMod m), (R.2 : ZMod m))) :=
  fun R h => by simp only; rw [h]

/-- … mas **não fiel** (m ≥ 2): `0 ≢ m` como inteiros, `0 ≡ m (mod m)`. -/
theorem reducao_modular_nao_fiel (m : ℕ) (hm : 2 ≤ m) :
    ¬ Fiel (fun R : ℤ × ℤ => R.1 = R.2) (fun R : ZMod m × ZMod m => R.1 = R.2)
      (fun R => ((R.1 : ZMod m), (R.2 : ZMod m))) := by
  intro h
  have := (h (0, (m : ℤ))).mpr (by simp)
  simp only at this
  omega

/-- **Obstrução modular**: `a ≢ b (mod m)` ⇒ `a ≠ b`. -/
theorem obstrucao_modular {a b : ℤ} (m : ℕ) (h : (a : ZMod m) ≠ (b : ZMod m)) : a ≠ b :=
  obstrucao (P := fun R : ℤ × ℤ => R.1 = R.2) (reducao_modular_necessaria m) (x := (a, b)) h

/-- Exemplo do texto: `2³ + 3³ = 35`, `3³ = 27`, e `35 ≢ 27 (mod 3)`; logo `2³ + 3³ ≠ 3³`. -/
theorem beal_exemplo :
    (2 : ℤ) ^ 3 + 3 ^ 3 = 35 ∧ (3 : ℤ) ^ 3 = 27 ∧
      (((2 : ℤ) ^ 3 + 3 ^ 3 : ℤ) : ZMod 3) ≠ (((3 : ℤ) ^ 3 : ℤ) : ZMod 3) ∧
      (2 : ℤ) ^ 3 + 3 ^ 3 ≠ 3 ^ 3 := by
  have hmod : (((2 : ℤ) ^ 3 + 3 ^ 3 : ℤ) : ZMod 3) ≠ (((3 : ℤ) ^ 3 : ℤ) : ZMod 3) := by decide
  exact ⟨by norm_num, by norm_num, hmod, obstrucao_modular 3 hmod⟩

/-! ### Famílias: aplicar f aos dois lados -/

section Familias

variable {α β : Type*}

/-- Aplicar `f` aos dois lados é sempre **necessário**. -/
theorem aplicar_necessaria (f : α → β) :
    Necessaria (fun R : α × α => R.1 = R.2) (fun R : β × β => R.1 = R.2)
      (fun R => (f R.1, f R.2)) :=
  fun R h => by simp only; rw [h]

/-- **Lei das famílias**: aplicar `f` é fiel ⟺ `f` é injetiva. -/
theorem aplicar_fiel_iff (f : α → β) :
    Fiel (fun R : α × α => R.1 = R.2) (fun R : β × β => R.1 = R.2) (fun R => (f R.1, f R.2)) ↔
      Function.Injective f := by
  constructor
  · intro h a b hab
    exact (h (a, b)).mpr hab
  · intro hf R
    exact ⟨fun h => by simp only; rw [h], fun h => hf h⟩

/-- Versão com domínio: fiel em `D × D` ⟺ `f` injetiva em `D`. -/
theorem aplicar_fiel_on_iff (f : α → β) (D : Set α) :
    (∀ a ∈ D, ∀ b ∈ D, (a = b ↔ f a = f b)) ↔ Set.InjOn f D := by
  constructor
  · intro h a ha b hb hab
    exact (h a ha b hb).mpr hab
  · intro hf a ha b hb
    exact ⟨fun h => by rw [h], fun h => hf ha hb h⟩

/-- Família 11: isometrias são fiéis. -/
theorem fiel_isometria {α β : Type*} [MetricSpace α] [MetricSpace β] {f : α → β}
    (hf : Isometry f) : Function.Injective f := hf.injective

/-- Família 12: homeomorfismos são fiéis. -/
theorem fiel_homeomorfismo {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (h : α ≃ₜ β) : Function.Injective h := h.injective

end Familias

/-- Famílias 1–3, 7, 4 (ímpar), 8 em ℝ: translação, escala (k ≠ 0), afim (k ≠ 0), exponencial,
potência ímpar e logaritmo em `(0,∞)` são fiéis. -/
theorem familias_fieis (c k : ℝ) (hk : k ≠ 0) (n : ℕ) (hn : Odd n) :
    Function.Injective (fun x : ℝ => x + c) ∧
      Function.Injective (fun x : ℝ => k * x) ∧
      Function.Injective (fun x : ℝ => k * x + c) ∧
      Function.Injective Real.exp ∧
      Function.Injective (fun x : ℝ => x ^ n) ∧
      Set.InjOn Real.log (Set.Ioi 0) := by
  refine ⟨add_left_injective c, mul_right_injective₀ hk, ?_, Real.exp_injective,
    hn.strictMono_pow.injective, Real.log_injOn_pos⟩
  intro x y h
  simp only at h
  exact mul_right_injective₀ hk (add_right_cancel h)

/-- Família 4 (par) e família 9: potência par e redução mod 2 **não** são fiéis. -/
theorem familias_nao_fieis :
    ¬ Function.Injective (fun x : ℝ => x ^ 2) ∧ ¬ Function.Injective (fun x : ℤ => (x : ZMod 2)) := by
  constructor
  · intro h
    have := @h (-1) 1 (by norm_num)
    norm_num at this
  · intro h
    have := @h 0 2 (by decide)
    omega

/-! ### O objeto de transformação certificada -/

/-- `𝒞 = (X, Y, P, Q, T, π)`: transformação acompanhada da prova de preservação semântica. -/
structure TransformacaoCertificada (X Y : Type*) where
  P : X → Prop
  Q : Y → Prop
  T : X → Y
  π : Fiel P Q T

namespace TransformacaoCertificada

variable {X Y Z : Type*}

/-- Composição de certificados (com domínios compatíveis: `Q` de uma é `P` da outra). -/
def comp (C₂ : TransformacaoCertificada Y Z) (C₁ : TransformacaoCertificada X Y)
    (h : C₂.P = C₁.Q) : TransformacaoCertificada X Z :=
  ⟨C₁.P, C₂.Q, C₂.T ∘ C₁.T, fun x => (C₁.π x).trans (by rw [← h]; exact C₂.π (C₁.T x))⟩

/-- **Fluxo de certificação**: prova independente de `Q` na imagem ⇒ certificado de `P`. -/
theorem certifica (C : TransformacaoCertificada X Y) (hQ : ∀ x, C.Q (C.T x)) : ∀ x, C.P x :=
  fun x => (C.π x).mpr (hQ x)

/-- E nenhum certificado de `P` sai se `Q` falha em algum ponto da imagem. -/
theorem nao_certifica (C : TransformacaoCertificada X Y) {x : X} (hx : ¬ C.Q (C.T x)) :
    ¬ C.P x :=
  fun hp => hx ((C.π x).mp hp)

end TransformacaoCertificada

end ATK.RelacionalTransporte

#print axioms ATK.RelacionalTransporte.fiel_iff
#print axioms ATK.RelacionalTransporte.transporte_prova
#print axioms ATK.RelacionalTransporte.transporte_suficiente
#print axioms ATK.RelacionalTransporte.obstrucao
#print axioms ATK.RelacionalTransporte.fiel_comp
#print axioms ATK.RelacionalTransporte.suficiente_comp
#print axioms ATK.RelacionalTransporte.necessaria_comp
#print axioms ATK.RelacionalTransporte.nao_colapso_fecha
#print axioms ATK.RelacionalTransporte.colapso_nao_informa
#print axioms ATK.RelacionalTransporte.nao_colapso_comp
#print axioms ATK.RelacionalTransporte.controle_fecha
#print axioms ATK.RelacionalTransporte.controle_comp
#print axioms ATK.RelacionalTransporte.controle_cadeia
#print axioms ATK.RelacionalTransporte.cota_uniforme
#print axioms ATK.RelacionalTransporte.exemplo_3_5
#print axioms ATK.RelacionalTransporte.escalas_degeneram
#print axioms ATK.RelacionalTransporte.sem_cota_uniforme
#print axioms ATK.RelacionalTransporte.reducao_modular_necessaria
#print axioms ATK.RelacionalTransporte.reducao_modular_nao_fiel
#print axioms ATK.RelacionalTransporte.obstrucao_modular
#print axioms ATK.RelacionalTransporte.beal_exemplo
#print axioms ATK.RelacionalTransporte.aplicar_necessaria
#print axioms ATK.RelacionalTransporte.aplicar_fiel_iff
#print axioms ATK.RelacionalTransporte.aplicar_fiel_on_iff
#print axioms ATK.RelacionalTransporte.fiel_isometria
#print axioms ATK.RelacionalTransporte.fiel_homeomorfismo
#print axioms ATK.RelacionalTransporte.familias_fieis
#print axioms ATK.RelacionalTransporte.familias_nao_fieis
#print axioms ATK.RelacionalTransporte.TransformacaoCertificada.certifica
#print axioms ATK.RelacionalTransporte.TransformacaoCertificada.nao_certifica
