import ATK.IGeometria
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic

/-!
# ATK-I — estados, certificados, fechamento por defeito e números relacionais

Formalização das partes demonstráveis da proposta ATK-I:

1. **A classe de três estados** `Nada < I < Todo`: inversão involutiva (troca `Todo` e `Nada`,
   fixa `I`), `⊕ = máx`, `⊗ = mín`, De Morgan; é a K3 do kernel (`paraK3`).
2. **Detecção de defeito** `Δ(d)` e o **defeito global** `Q = máx qⱼ`: `Q = 0 ⟺ todos os qⱼ = 0`.
3. **Certificados** `Cert P` (provado / refutado / aberto): o estado `Todo` **só** sai de uma prova
   (`sound_todo`), `aberto` nunca é `Todo`, a conjunção de certificados tem o estado `⊗` de Kleene, e
   sete certificados `Todo` dão os sete enunciados (`universal`).
4. **Fechamento por defeito majorado**: `T ↔ d = 0`, `0 ≤ d ≤ εₙ → 0` ⟹ `T`.
5. **Números relacionais** `(a R b)`: inversão `J`, troca de lados, escala, translação; leis
   `J² = id`, `SₖSₗ = Sₖₗ`, `TₐT_b = T_{a+b}`, preservação da verdade, ação de `ℝ` por translações,
   `J` e `Sₖ` como `Equiv` da Mathlib, o ciclo de período 4 do texto, e **retorno ≠ verdade**:
   `(0 > 1)` volta a si mesmo e é falso.
6. **Lei de compatibilidade** `interpretar ∘ J = interpretar`.
7. **Defeitos de aproximação** `D N = inf_c Σ wₖ (1 − Σ cₘ gₘ(k))²`: não negativos, decrescentes,
   convergentes, e `D∞ = 0 ⟺ ∀ ε > 0, ∃ N, D N < ε`; instância com a família do texto
   `ρₘ(k) = (k mod m)/m`, pesos `1/(k(k+1))`.

Nada aqui prova uma conjectura. Não há ponte provada entre o `D∞` da família discreta do texto e
RH (a ponte B1 do kernel usa o `D_N` de Báez-Duarte em `L²`, outro objeto).
-/

noncomputable section

namespace ATK.ATKI

open Filter Topology

/-! ## 1. A classe de três estados -/

inductive Estado where
  | nada
  | ind
  | todo
  deriving DecidableEq, Repr

namespace Estado

/-- Inversão: troca `Todo` e `Nada`, fixa `I`. -/
def inv : Estado → Estado
  | nada => todo
  | ind => ind
  | todo => nada

/-- Ordem `Nada < I < Todo`. -/
def nivel : Estado → ℕ
  | nada => 0
  | ind => 1
  | todo => 2

/-- `⊕ = máx`. -/
def oplus (a b : Estado) : Estado := if nivel a ≤ nivel b then b else a

/-- `⊗ = mín`. -/
def otimes (a b : Estado) : Estado := if nivel a ≤ nivel b then a else b

theorem inv_inv (a : Estado) : inv (inv a) = a := by cases a <;> rfl

theorem inv_fixo_iff (a : Estado) : inv a = a ↔ a = ind := by cases a <;> decide

theorem de_morgan_otimes (a b : Estado) : inv (otimes a b) = oplus (inv a) (inv b) := by
  cases a <;> cases b <;> decide

theorem de_morgan_oplus (a b : Estado) : inv (oplus a b) = otimes (inv a) (inv b) := by
  cases a <;> cases b <;> decide

theorem otimes_idem (a : Estado) : otimes a a = a := by cases a <;> decide

theorem oplus_idem (a : Estado) : oplus a a = a := by cases a <;> decide

theorem otimes_comm (a b : Estado) : otimes a b = otimes b a := by
  cases a <;> cases b <;> decide

theorem oplus_comm (a b : Estado) : oplus a b = oplus b a := by
  cases a <;> cases b <;> decide

theorem otimes_assoc (a b c : Estado) : otimes (otimes a b) c = otimes a (otimes b c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem distrib (a b c : Estado) : otimes a (oplus b c) = oplus (otimes a b) (otimes a c) := by
  cases a <;> cases b <;> cases c <;> decide

/-- A classe é a lógica K3 do kernel (`Nada ↦ F`, `I ↦ N`, `Todo ↦ T`). -/
def paraK3 : Estado → ATK.IGeometria.K3
  | nada => .F
  | ind => .N
  | todo => .T

theorem paraK3_inv (a : Estado) : paraK3 (inv a) = ATK.IGeometria.K3.neg (paraK3 a) := by
  cases a <;> rfl

theorem paraK3_otimes (a b : Estado) :
    paraK3 (otimes a b) = ATK.IGeometria.K3.e (paraK3 a) (paraK3 b) := by
  cases a <;> cases b <;> decide

theorem paraK3_oplus (a b : Estado) :
    paraK3 (oplus a b) = ATK.IGeometria.K3.ou (paraK3 a) (paraK3 b) := by
  cases a <;> cases b <;> decide

end Estado

/-! ## 2. Detecção de defeito e defeito global -/

/-- `Δ(d)`: `Nada` (defeito nulo) se `d = 0`, `Todo` caso contrário. -/
def detecta (d : ℝ) : Estado := if d = 0 then .nada else .todo

theorem detecta_nada_iff (d : ℝ) : detecta d = .nada ↔ d = 0 := by
  unfold detecta
  split_ifs with h <;> simp [h]

/-- **Defeito global**: com defeitos não negativos, `máx qⱼ = 0 ⟺ todos os qⱼ = 0`. -/
theorem defeito_global_zero_iff {n : ℕ} (q : Fin (n + 1) → ℝ) (hq : ∀ j, 0 ≤ q j) :
    Finset.univ.sup' Finset.univ_nonempty q = 0 ↔ ∀ j, q j = 0 := by
  constructor
  · intro h j
    have h1 : q j ≤ Finset.univ.sup' Finset.univ_nonempty q :=
      Finset.le_sup' q (Finset.mem_univ j)
    rw [h] at h1
    exact le_antisymm h1 (hq j)
  · intro h
    apply le_antisymm
    · exact (Finset.sup'_le_iff _ _).mpr (fun j _ => (h j).le)
    · have h0 : q 0 ≤ Finset.univ.sup' Finset.univ_nonempty q :=
        Finset.le_sup' q (Finset.mem_univ 0)
      rw [h 0] at h0
      exact h0

/-! ## 3. Certificados: `Todo` só com prova -/

/-- Estado de certificação de uma proposição. -/
inductive Cert (P : Prop) where
  | provado : P → Cert P
  | refutado : ¬ P → Cert P
  | aberto : Cert P

namespace Cert

def estado {P : Prop} : Cert P → Estado
  | provado _ => .todo
  | refutado _ => .nada
  | aberto => .ind

/-- **Correção**: o estado `Todo` só existe com uma prova. -/
theorem sound_todo {P : Prop} {c : Cert P} (h : c.estado = .todo) : P := by
  cases c with
  | provado hp => exact hp
  | refutado _ => cases h
  | aberto => cases h

/-- **Correção**: o estado `Nada` só existe com uma refutação. -/
theorem sound_nada {P : Prop} {c : Cert P} (h : c.estado = .nada) : ¬ P := by
  cases c with
  | provado _ => cases h
  | refutado hn => exact hn
  | aberto => cases h

/-- Um certificado aberto nunca é `Todo`: classificar não prova. -/
theorem aberto_nao_todo {P : Prop} : (aberto : Cert P).estado ≠ .todo := fun h => by cases h

/-- Conjunção de certificados. -/
def and {P Q : Prop} : Cert P → Cert Q → Cert (P ∧ Q)
  | provado hp, provado hq => provado ⟨hp, hq⟩
  | refutado hp, _ => refutado (fun h => hp h.1)
  | _, refutado hq => refutado (fun h => hq h.2)
  | _, _ => aberto

/-- O estado da conjunção é o `⊗` (mínimo) de Kleene. -/
theorem estado_and {P Q : Prop} (c : Cert P) (d : Cert Q) :
    (c.and d).estado = Estado.otimes c.estado d.estado := by
  cases c <;> cases d <;> rfl

/-- **A regra do portão**: sete certificados no estado `Todo` dão os sete enunciados. -/
theorem universal {P : Fin 7 → Prop} (c : ∀ j, Cert (P j)) (h : ∀ j, (c j).estado = .todo) :
    ∀ j, P j :=
  fun j => sound_todo (h j)

end Cert

/-! ## 4. Fechamento por defeito majorado, transferência e pontes -/

/-- **Fechamento por defeito majorado**: `T ↔ d = 0`, `0 ≤ d` e `d ≤ εₙ → 0` provam `T`. -/
theorem fechamento_por_defeito {T : Prop} {d : ℝ} {ε : ℕ → ℝ} (ponte : T ↔ d = 0) (h0 : 0 ≤ d)
    (hd : ∀ n, d ≤ ε n) (hε : Tendsto ε atTop (𝓝 0)) : T := by
  apply ponte.mpr
  have h1 : d ≤ 0 := ge_of_tendsto' hε hd
  exact le_antisymm h1 h0

/-- Transferência: um teorema provado e uma ponte provada dão o alvo. -/
theorem transferencia {A B : Prop} (hA : A) (ponte : A → B) : B := ponte hA

/-- Composição de pontes. -/
theorem ponte_composta {A B C : Prop} {d : ℝ} (h1 : A ↔ B) (h2 : B ↔ C) (h3 : C ↔ d = 0) :
    A ↔ d = 0 :=
  h1.trans (h2.trans h3)

/-! ## 5. Números relacionais -/

/-- As seis relações. -/
inductive Rel where
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  deriving DecidableEq, Repr

namespace Rel

/-- Inversão de orientação: `< ↔ >`, `≤ ↔ ≥`; `=` e `≠` ficam. -/
def flip : Rel → Rel
  | eq => eq
  | ne => ne
  | lt => gt
  | le => ge
  | gt => lt
  | ge => le

theorem flip_flip (r : Rel) : flip (flip r) = r := by cases r <;> rfl

def eval : Rel → ℝ → ℝ → Prop
  | eq, a, b => a = b
  | ne, a, b => a ≠ b
  | lt, a, b => a < b
  | le, a, b => a ≤ b
  | gt, a, b => a > b
  | ge, a, b => a ≥ b

end Rel

/-- Um número relacional: a expressão inteira `(a R b)`. -/
structure RelNum where
  lhs : ℝ
  rel : Rel
  rhs : ℝ

namespace RelNum

/-- A validade da expressão. -/
def holds (x : RelNum) : Prop := x.rel.eval x.lhs x.rhs

/-- `J(a R b) = (−a R* −b)`. -/
def neg (x : RelNum) : RelNum := ⟨-x.lhs, x.rel.flip, -x.rhs⟩

/-- Troca de lados: `(a R b) ↦ (b R* a)`. -/
def swap (x : RelNum) : RelNum := ⟨x.rhs, x.rel.flip, x.lhs⟩

/-- Escala `Sₖ`. -/
def scale (k : ℝ) (x : RelNum) : RelNum := ⟨k * x.lhs, x.rel, k * x.rhs⟩

/-- Translação `Tₐ`. -/
def transl (a : ℝ) (x : RelNum) : RelNum := ⟨x.lhs + a, x.rel, x.rhs + a⟩

theorem neg_neg (x : RelNum) : neg (neg x) = x := by
  obtain ⟨a, r, b⟩ := x
  simp [neg, Rel.flip_flip]

theorem swap_swap (x : RelNum) : swap (swap x) = x := by
  obtain ⟨a, r, b⟩ := x
  simp [swap, Rel.flip_flip]

theorem scale_scale (k l : ℝ) (x : RelNum) : scale k (scale l x) = scale (k * l) x := by
  obtain ⟨a, r, b⟩ := x
  simp [scale, mul_assoc]

theorem scale_one (x : RelNum) : scale 1 x = x := by
  obtain ⟨a, r, b⟩ := x
  simp [scale]

theorem scale_inv_scale {k : ℝ} (hk : k ≠ 0) (x : RelNum) : scale k⁻¹ (scale k x) = x := by
  rw [scale_scale, inv_mul_cancel₀ hk, scale_one]

theorem scale_scale_inv {k : ℝ} (hk : k ≠ 0) (x : RelNum) : scale k (scale k⁻¹ x) = x := by
  rw [scale_scale, mul_inv_cancel₀ hk, scale_one]

theorem transl_zero (x : RelNum) : transl 0 x = x := by
  obtain ⟨a, r, b⟩ := x
  simp [transl]

theorem transl_transl (a b : ℝ) (x : RelNum) : transl a (transl b x) = transl (a + b) x := by
  obtain ⟨c, r, d⟩ := x
  simp only [transl, RelNum.mk.injEq, true_and]
  constructor <;> ring

/-- `J` como bijeção (`Equiv` da Mathlib). -/
def negEquiv : RelNum ≃ RelNum := ⟨neg, neg, neg_neg, neg_neg⟩

/-- `Sₖ` como bijeção, para `k ≠ 0`. -/
def scaleEquiv {k : ℝ} (hk : k ≠ 0) : RelNum ≃ RelNum :=
  ⟨scale k, scale k⁻¹, scale_inv_scale hk, scale_scale_inv hk⟩

/-- `ℝ` age por translações. -/
instance : AddAction ℝ RelNum where
  vadd := transl
  zero_vadd := transl_zero
  add_vadd a b x := (transl_transl a b x).symm

/-- `J` preserva a verdade. -/
theorem holds_neg (x : RelNum) : holds (neg x) ↔ holds x := by
  obtain ⟨a, r, b⟩ := x
  cases r <;> simp [holds, neg, Rel.flip, Rel.eval]

/-- A troca de lados preserva a verdade. -/
theorem holds_swap (x : RelNum) : holds (swap x) ↔ holds x := by
  obtain ⟨a, r, b⟩ := x
  cases r <;> simp [holds, swap, Rel.flip, Rel.eval, eq_comm, ne_comm]

/-- A translação preserva a verdade. -/
theorem holds_transl (c : ℝ) (x : RelNum) : holds (transl c x) ↔ holds x := by
  obtain ⟨a, r, b⟩ := x
  cases r <;> simp [holds, transl, Rel.eval]

/-- A escala positiva preserva a verdade. -/
theorem holds_scale {k : ℝ} (hk : 0 < k) (x : RelNum) : holds (scale k x) ↔ holds x := by
  obtain ⟨a, r, b⟩ := x
  have e : k * a = k * b ↔ a = b := ⟨fun h => mul_left_cancel₀ hk.ne' h, fun h => by rw [h]⟩
  have l : k * a < k * b ↔ a < b := ⟨fun h => by nlinarith, fun h => by nlinarith⟩
  have l' : k * b < k * a ↔ b < a := ⟨fun h => by nlinarith, fun h => by nlinarith⟩
  have q : k * a ≤ k * b ↔ a ≤ b := ⟨fun h => by nlinarith, fun h => by nlinarith⟩
  have q' : k * b ≤ k * a ↔ b ≤ a := ⟨fun h => by nlinarith, fun h => by nlinarith⟩
  cases r
  · exact e
  · exact not_congr e
  · exact l
  · exact q
  · exact l'
  · exact q'

/-- **Retorno não implica verdade**: `(0 > 1)` é falso e volta a si mesmo por `J²`. -/
def exemploFalso : RelNum := ⟨0, .gt, 1⟩

theorem exemploFalso_falso : ¬ holds exemploFalso := by
  simp [holds, exemploFalso, Rel.eval]

theorem retorno_nao_implica_verdade : ∃ x : RelNum, neg (neg x) = x ∧ ¬ holds x :=
  ⟨exemploFalso, neg_neg _, exemploFalso_falso⟩

/-- O ciclo de período 4 do texto: `(3 > 0) → (6 > 0) → (−6 < 0) → (−3 < 0) → (3 > 0)`. -/
def N0 : RelNum := ⟨3, .gt, 0⟩

theorem ciclo_quatro : neg (scale (1 / 2) (neg (scale 2 N0))) = N0 := by
  norm_num [N0, neg, scale, Rel.flip]

/-- Cada passo do ciclo preserva a verdade, e `N0` é verdadeiro. -/
theorem ciclo_preserva_verdade :
    holds (neg (scale (1 / 2) (neg (scale 2 N0)))) ↔ holds N0 := by
  rw [holds_neg, holds_scale (by norm_num), holds_neg, holds_scale (by norm_num)]

theorem N0_verdadeiro : holds N0 := by
  norm_num [holds, N0, Rel.eval]

end RelNum

/-! ## 6. Lei de compatibilidade `interpretar ∘ J = interpretar` -/

/-- Interpretação de uma proposição na classe de estados (`Todo` se vale, `Nada` se não). -/
def interpretarP (P : Prop) : Estado := by
  classical
  exact if P then .todo else .nada

/-- Interpretação de um número relacional. -/
def interpretar (x : RelNum) : Estado := interpretarP x.holds

/-- **Compatibilidade**: operar com `J` e depois interpretar = interpretar. -/
theorem compat_neg (x : RelNum) : interpretar (RelNum.neg x) = interpretar x :=
  congrArg interpretarP (propext (RelNum.holds_neg x))

/-- O mesmo para escala positiva. -/
theorem compat_scale {k : ℝ} (hk : 0 < k) (x : RelNum) :
    interpretar (RelNum.scale k x) = interpretar x :=
  congrArg interpretarP (propext (RelNum.holds_scale hk x))

/-! ## 7. Defeitos de aproximação -/

/-- `D N = inf_c Σ' k, w k · (1 − Σ_{m<N} c m · g m k)²`. -/
def Defeito (w : ℕ → ℝ) (g : ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  ⨅ c : Fin N → ℝ, ∑' k, w k * (1 - ∑ m : Fin N, c m * g m k) ^ 2

variable {w : ℕ → ℝ} {g : ℕ → ℕ → ℝ}

theorem defeito_nonneg (hw : ∀ k, 0 ≤ w k) (N : ℕ) : 0 ≤ Defeito w g N :=
  le_ciInf (fun _ => tsum_nonneg (fun k => mul_nonneg (hw k) (sq_nonneg _)))

/-- **Monotonia**: um gerador a mais nunca piora (coeficiente `0` no novo gerador). -/
theorem defeito_antitone (hw : ∀ k, 0 ≤ w k) : Antitone (Defeito w g) := by
  apply antitone_nat_of_succ_le
  intro N
  unfold Defeito
  apply le_ciInf
  intro c
  have hbdd : BddBelow (Set.range fun c : Fin (N + 1) → ℝ =>
      ∑' k, w k * (1 - ∑ m : Fin (N + 1), c m * g m k) ^ 2) :=
    ⟨0, by
      rintro _ ⟨c, rfl⟩
      exact tsum_nonneg (fun k => mul_nonneg (hw k) (sq_nonneg _))⟩
  refine (ciInf_le hbdd (Fin.snoc (α := fun _ => ℝ) c 0)).trans (le_of_eq ?_)
  simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, zero_mul, add_zero,
    Fin.val_castSucc]

/-- **Convergência**: `D N → D∞ = inf_N D N`. -/
theorem defeito_converge (hw : ∀ k, 0 ≤ w k) :
    Tendsto (Defeito w g) atTop (𝓝 (⨅ N, Defeito w g N)) :=
  tendsto_atTop_ciInf (defeito_antitone hw)
    ⟨0, by
      rintro _ ⟨N, rfl⟩
      exact defeito_nonneg hw N⟩

/-- `D∞ = 0 ⟺ ∀ ε > 0, ∃ N, D N < ε`: a obrigação terminal na forma do texto. -/
theorem defeito_limite_zero_iff (hw : ∀ k, 0 ≤ w k) :
    (⨅ N, Defeito w g N) = 0 ↔ ∀ ε > 0, ∃ N, Defeito w g N < ε := by
  have hb : BddBelow (Set.range (Defeito w g)) :=
    ⟨0, by
      rintro _ ⟨N, rfl⟩
      exact defeito_nonneg hw N⟩
  have h0 : 0 ≤ ⨅ N, Defeito w g N := le_ciInf (defeito_nonneg hw)
  constructor
  · intro h ε hε
    have hlt : (⨅ N, Defeito w g N) < ε := by rw [h]; exact hε
    exact exists_lt_of_ciInf_lt hlt
  · intro h
    rcases le_or_gt (⨅ N, Defeito w g N) 0 with hle | hpos
    · exact le_antisymm hle h0
    · obtain ⟨N, hN⟩ := h _ hpos
      exact absurd (ciInf_le hb N) (not_le.mpr hN)

/-- A família do texto: pesos `1/(k(k+1))` e geradores `ρₘ(k) = (k mod m)/m`, `m ≥ 2`
(índices deslocados: `k ↦ k + 1`, `m ↦ m + 2`). -/
def wTexto (k : ℕ) : ℝ := 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))

def gTexto (m k : ℕ) : ℝ := (((k + 1) % (m + 2) : ℕ) : ℝ) / ((m : ℝ) + 2)

theorem wTexto_nonneg (k : ℕ) : 0 ≤ wTexto k := by
  unfold wTexto
  positivity

/-- Na família do texto: `D N` decresce e converge; `D∞ = 0` é a obrigação em aberto. -/
theorem texto_converge :
    Tendsto (Defeito wTexto gTexto) atTop (𝓝 (⨅ N, Defeito wTexto gTexto N)) :=
  defeito_converge wTexto_nonneg

theorem texto_antitone : Antitone (Defeito wTexto gTexto) := defeito_antitone wTexto_nonneg

end ATK.ATKI

end

#print axioms ATK.ATKI.Estado.inv_inv
#print axioms ATK.ATKI.Estado.inv_fixo_iff
#print axioms ATK.ATKI.Estado.de_morgan_otimes
#print axioms ATK.ATKI.Estado.de_morgan_oplus
#print axioms ATK.ATKI.Estado.otimes_idem
#print axioms ATK.ATKI.Estado.oplus_idem
#print axioms ATK.ATKI.Estado.otimes_comm
#print axioms ATK.ATKI.Estado.oplus_comm
#print axioms ATK.ATKI.Estado.otimes_assoc
#print axioms ATK.ATKI.Estado.distrib
#print axioms ATK.ATKI.Estado.paraK3_inv
#print axioms ATK.ATKI.Estado.paraK3_otimes
#print axioms ATK.ATKI.Estado.paraK3_oplus
#print axioms ATK.ATKI.detecta_nada_iff
#print axioms ATK.ATKI.defeito_global_zero_iff
#print axioms ATK.ATKI.Cert.sound_todo
#print axioms ATK.ATKI.Cert.sound_nada
#print axioms ATK.ATKI.Cert.aberto_nao_todo
#print axioms ATK.ATKI.Cert.estado_and
#print axioms ATK.ATKI.Cert.universal
#print axioms ATK.ATKI.fechamento_por_defeito
#print axioms ATK.ATKI.transferencia
#print axioms ATK.ATKI.ponte_composta
#print axioms ATK.ATKI.Rel.flip_flip
#print axioms ATK.ATKI.RelNum.neg_neg
#print axioms ATK.ATKI.RelNum.swap_swap
#print axioms ATK.ATKI.RelNum.scale_scale
#print axioms ATK.ATKI.RelNum.scale_one
#print axioms ATK.ATKI.RelNum.scale_inv_scale
#print axioms ATK.ATKI.RelNum.scale_scale_inv
#print axioms ATK.ATKI.RelNum.transl_zero
#print axioms ATK.ATKI.RelNum.transl_transl
#print axioms ATK.ATKI.RelNum.holds_neg
#print axioms ATK.ATKI.RelNum.holds_swap
#print axioms ATK.ATKI.RelNum.holds_transl
#print axioms ATK.ATKI.RelNum.holds_scale
#print axioms ATK.ATKI.RelNum.exemploFalso_falso
#print axioms ATK.ATKI.RelNum.retorno_nao_implica_verdade
#print axioms ATK.ATKI.RelNum.ciclo_quatro
#print axioms ATK.ATKI.RelNum.ciclo_preserva_verdade
#print axioms ATK.ATKI.RelNum.N0_verdadeiro
#print axioms ATK.ATKI.compat_neg
#print axioms ATK.ATKI.compat_scale
#print axioms ATK.ATKI.defeito_nonneg
#print axioms ATK.ATKI.defeito_antitone
#print axioms ATK.ATKI.defeito_converge
#print axioms ATK.ATKI.defeito_limite_zero_iff
#print axioms ATK.ATKI.wTexto_nonneg
#print axioms ATK.ATKI.texto_converge
#print axioms ATK.ATKI.texto_antitone
