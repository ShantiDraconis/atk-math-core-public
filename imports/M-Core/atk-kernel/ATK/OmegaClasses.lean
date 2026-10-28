/-
ATK-Ω — As oito classes estruturais (R, P, N, Y, B, H, E, T) e suas leis.

Cada classe é definida pela sua assinatura.  Os teoremas abaixo são leis de
fechamento das operações e os exemplos calculados do texto.  Nenhum deles afirma
que os objetos dos sete problemas originais têm essas assinaturas.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

namespace ATK.OmegaClasses

/-! ### R — anulação assintótica -/

/-- Sequências não negativas que tendem a zero (definição ε–N, sem topologia). -/
structure ClasseR where
  seq : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ seq n
  vanish : ∀ ε > 0, ∃ N, ∀ n ≥ N, seq n < ε

namespace ClasseR

def add (r s : ClasseR) : ClasseR where
  seq n := r.seq n + s.seq n
  nonneg n := add_nonneg (r.nonneg n) (s.nonneg n)
  vanish ε hε := by
    obtain ⟨N₁, h₁⟩ := r.vanish (ε / 2) (by positivity)
    obtain ⟨N₂, h₂⟩ := s.vanish (ε / 2) (by positivity)
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have := h₁ n (le_of_max_le_left hn)
    have := h₂ n (le_of_max_le_right hn)
    linarith

def mul (r s : ClasseR) : ClasseR where
  seq n := r.seq n * s.seq n
  nonneg n := mul_nonneg (r.nonneg n) (s.nonneg n)
  vanish ε hε := by
    obtain ⟨N₁, h₁⟩ := r.vanish 1 one_pos
    obtain ⟨N₂, h₂⟩ := s.vanish ε hε
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    have ha := h₁ n (le_of_max_le_left hn)
    have hb := h₂ n (le_of_max_le_right hn)
    calc r.seq n * s.seq n ≤ 1 * s.seq n :=
          mul_le_mul_of_nonneg_right ha.le (s.nonneg n)
      _ = s.seq n := one_mul _
      _ < ε := hb

/-- Exemplo do texto: r_n = 1/(n+1). -/
noncomputable def exemplo : ClasseR where
  seq n := 1 / ((n : ℝ) + 1)
  nonneg n := by positivity
  vanish ε hε := by
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, fun n hn => ?_⟩
    have hn' : (1 / ε : ℝ) < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hn'
    linarith

end ClasseR

/-! ### P — crescimento superpolinomial -/

/-- T : ℕ → ℝ supera todo polinômio: ∀ k, ∀ C, ∃ N, ∀ n ≥ N, C · n^k < T n. -/
def Superpoly (T : ℕ → ℝ) : Prop :=
  ∀ (k : ℕ) (C : ℝ), ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * (n : ℝ) ^ k < T n

theorem Superpoly.add_of_nonneg {T S : ℕ → ℝ} (hT : Superpoly T) (hS : ∀ n, 0 ≤ S n) :
    Superpoly (fun n => T n + S n) := by
  intro k C
  obtain ⟨N, hN⟩ := hT k C
  exact ⟨N, fun n hn => by have := hN n hn; have := hS n; linarith⟩

theorem Superpoly.mul_of_one_le {T S : ℕ → ℝ} (hT : Superpoly T) (hS : ∀ n, 1 ≤ S n) :
    Superpoly (fun n => T n * S n) := by
  intro k C
  obtain ⟨N, hN⟩ := hT k (max C 0)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  have hTn : 0 < T n := lt_of_le_of_lt (by positivity) h1
  calc C * (n : ℝ) ^ k ≤ max C 0 * (n : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ < T n := h1
    _ = T n * 1 := (mul_one _).symm
    _ ≤ T n * S n := mul_le_mul_of_nonneg_left (hS n) hTn.le

/-! ### N — contrações afins -/

/-- Contração afim x ↦ a x + C com 0 ≤ a < 1. -/
structure Contracao where
  a : ℝ
  C : ℝ
  a_nonneg : 0 ≤ a
  a_lt_one : a < 1

namespace Contracao

def apply (f : Contracao) (x : ℝ) : ℝ := f.a * x + f.C

/-- Lei de composição (a, C) ⋆ (b, D) = (ab, aD + C). -/
def comp (f g : Contracao) : Contracao where
  a := f.a * g.a
  C := f.a * g.C + f.C
  a_nonneg := mul_nonneg f.a_nonneg g.a_nonneg
  a_lt_one := by
    calc f.a * g.a ≤ f.a * 1 := mul_le_mul_of_nonneg_left g.a_lt_one.le f.a_nonneg
      _ = f.a := mul_one _
      _ < 1 := f.a_lt_one

theorem comp_apply (f g : Contracao) (x : ℝ) : (f.comp g).apply x = f.apply (g.apply x) := by
  simp [apply, comp]; ring

theorem comp_assoc (f g h : Contracao) : (f.comp g).comp h = f.comp (g.comp h) := by
  simp only [comp, mk.injEq]; constructor <;> ring

/-- Ponto fixo x* = C/(1 − a). -/
noncomputable def fixo (f : Contracao) : ℝ := f.C / (1 - f.a)

theorem apply_fixo (f : Contracao) : f.apply f.fixo = f.fixo := by
  have h : (1 - f.a) ≠ 0 := by have := f.a_lt_one; intro h; linarith
  simp only [apply, fixo]
  field_simp
  ring

/-- Órbita x_{n+1} = f(x_n): |x_n − x*| = a^n |x_0 − x*|. -/
theorem orbita_sub_fixo (f : Contracao) (x₀ : ℝ) (n : ℕ) :
    f.apply^[n] x₀ - f.fixo = f.a ^ n * (x₀ - f.fixo) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    have := f.apply_fixo
    simp only [apply] at this ⊢
    linear_combination f.a * ih + this

/-- Exemplo calculado: A = (1/4, 1/5), B = (1/3, 2/5); A⋆B ≠ B⋆A; ponto fixo 4/15. -/
noncomputable def exA : Contracao := ⟨1/4, 1/5, by norm_num, by norm_num⟩
noncomputable def exB : Contracao := ⟨1/3, 2/5, by norm_num, by norm_num⟩

theorem exA_comp_exB : (exA.comp exB).a = 1/12 ∧ (exA.comp exB).C = 3/10 := by
  simp [comp, exA, exB]; norm_num

theorem exB_comp_exA : (exB.comp exA).a = 1/12 ∧ (exB.comp exA).C = 7/15 := by
  simp [comp, exA, exB]; norm_num

theorem exA_fixo : exA.fixo = 4/15 := by
  simp [fixo, exA]; norm_num

/-- Exemplo do simulador: a = 1/4, C = 3/10 → x* = 2/5 e |x₉ − x*| = 3/1310720. -/
theorem exemplo_simulador :
    (⟨1/4, 3/10, by norm_num, by norm_num⟩ : Contracao).fixo = 2/5 ∧
    (1/4 : ℝ) ^ 9 * (1 - 2/5) = 3 / 1310720 := by
  constructor
  · simp [fixo]; norm_num
  · norm_num

end Contracao

/-! ### Y — gap espectral (espectros finitos) -/

/-- Espectro finito contendo 0; gap = menor elemento positivo. -/
structure EspectroFinito where
  S : Finset ℝ
  zero_mem : (0 : ℝ) ∈ S

namespace EspectroFinito

/-- Gap: ínfimo dos elementos positivos (0 se não houver). -/
noncomputable def gap (σ : EspectroFinito) : ℝ :=
  if h : (σ.S.filter (fun x => 0 < x)).Nonempty then (σ.S.filter (fun x => 0 < x)).min' h else 0

/-- Soma direta: união dos espectros. -/
noncomputable def somaDireta (σ τ : EspectroFinito) : EspectroFinito :=
  ⟨σ.S ∪ τ.S, Finset.mem_union_left _ σ.zero_mem⟩

/-- O gap da soma direta é o menor dos gaps (quando ambos têm parte positiva). -/
theorem gap_somaDireta (σ τ : EspectroFinito)
    (hσ : (σ.S.filter (fun x => 0 < x)).Nonempty)
    (hτ : (τ.S.filter (fun x => 0 < x)).Nonempty) :
    (σ.somaDireta τ).gap = min σ.gap τ.gap := by
  classical
  have key : (σ.somaDireta τ).S.filter (fun x => 0 < x)
      = σ.S.filter (fun x => 0 < x) ∪ τ.S.filter (fun x => 0 < x) := by
    simp only [somaDireta]; exact Finset.filter_union _ _ _
  have hu : ((σ.somaDireta τ).S.filter (fun x => 0 < x)).Nonempty := by
    rw [key]; exact hσ.mono Finset.subset_union_left
  rw [gap, gap, gap, dif_pos hσ, dif_pos hτ, dif_pos hu]
  apply le_antisymm
  · apply le_min
    · apply Finset.min'_subset hσ; rw [key]; exact Finset.subset_union_left
    · apply Finset.min'_subset hτ; rw [key]; exact Finset.subset_union_right
  · apply Finset.le_min'
    intro y hy
    rw [key] at hy
    rcases Finset.mem_union.mp hy with h | h
    · exact (min_le_left _ _).trans (Finset.min'_le _ _ h)
    · exact (min_le_right _ _).trans (Finset.min'_le _ _ h)

/-- Exemplo: {0,2,5} ⊕ {0,3} tem gap 2. -/
theorem exemplo :
    (EspectroFinito.somaDireta ⟨{0, 2, 5}, by simp⟩ ⟨{0, 3}, by simp⟩).gap = 2 := by
  classical
  have h1 : (EspectroFinito.somaDireta ⟨{0, 2, 5}, by simp⟩ ⟨{0, 3}, by simp⟩).S.filter
      (fun x : ℝ => 0 < x) = {2, 5, 3} := by
    simp only [somaDireta]
    ext x; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h, hx⟩; rcases h with (rfl | rfl | rfl) | (rfl | rfl) <;> norm_num at hx <;> norm_num
    · rintro (rfl | rfl | rfl) <;> norm_num
  have hne : ({2, 5, 3} : Finset ℝ).Nonempty := by simp
  rw [gap, dif_pos (by rw [h1]; exact hne)]
  have hmin : ∀ (h : ((EspectroFinito.somaDireta ⟨{0, 2, 5}, by simp⟩ ⟨{0, 3}, by simp⟩).S.filter
      (fun x : ℝ => 0 < x)).Nonempty),
      ((EspectroFinito.somaDireta ⟨{0, 2, 5}, by simp⟩ ⟨{0, 3}, by simp⟩).S.filter
      (fun x : ℝ => 0 < x)).min' h = ({2, 5, 3} : Finset ℝ).min' hne := by
    intro h; congr 1
  rw [hmin]
  apply le_antisymm
  · exact Finset.min'_le _ _ (by simp)
  · apply Finset.le_min'; intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl <;> norm_num

end EspectroFinito

/-! ### B — identidades de invariantes -/

/-- Número estrutural (a, a, b, b): as igualdades 1=2 e 3=4 são a assinatura. -/
structure NumeroB where
  v : Fin 4 → ℝ
  h12 : v 0 = v 1
  h34 : v 2 = v 3

def NumeroB.add (x y : NumeroB) : NumeroB :=
  ⟨fun i => x.v i + y.v i, by simp [x.h12, y.h12], by simp [x.h34, y.h34]⟩

theorem NumeroB.exemplo :
    ((⟨![2, 2, 5, 5], rfl, rfl⟩ : NumeroB).add ⟨![3, 3, 7, 7], rfl, rfl⟩).v = ![5, 5, 12, 12] := by
  ext i; fin_cases i <;> simp [NumeroB.add] <;> norm_num

/-- Invariância do determinante sob mudança de base unimodular: det(Uᵀ G U) = det G
quando det U = ±1. -/
theorem det_conj_unimodular {n : Type*} [Fintype n] [DecidableEq n]
    (G U : Matrix n n ℝ) (hU : U.det = 1 ∨ U.det = -1) :
    (U.transpose * G * U).det = G.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rcases hU with h | h <;> rw [h] <;> ring

theorem det_exemplo :
    (!![2, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ).det = 5 ∧
    (!![2, 3; 3, 7] : Matrix (Fin 2) (Fin 2) ℝ).det = 5 := by
  constructor <;> simp [Matrix.det_fin_two] <;> norm_num

/-! ### H — quocientes nulos -/

/-- O quociente V/A é trivial exatamente quando A = V. -/
theorem quociente_trivial_iff {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    (A : Submodule R V) : Subsingleton (V ⧸ A) ↔ A = ⊤ :=
  Submodule.Quotient.subsingleton_iff

/-! ### E — conjuntos de exclusão -/

/-- Universo + conjunto proibido; assinatura = proibido vazio. -/
structure Exclusao (α : Type*) where
  U : Set α
  F : Set α
  F_sub : F ⊆ U

def Exclusao.disjUnion {α β : Type*} (x : Exclusao α) (y : Exclusao β) : Exclusao (α ⊕ β) :=
  ⟨Sum.inl '' x.U ∪ Sum.inr '' y.U, Sum.inl '' x.F ∪ Sum.inr '' y.F,
    Set.union_subset_union (Set.image_mono x.F_sub) (Set.image_mono y.F_sub)⟩

theorem Exclusao.disjUnion_F_empty_iff {α β : Type*} (x : Exclusao α) (y : Exclusao β) :
    (x.disjUnion y).F = ∅ ↔ x.F = ∅ ∧ y.F = ∅ := by
  simp [disjUnion, Set.union_empty_iff, Set.image_eq_empty]

/-! ### T — Poincaré (interface de certificado) -/

/-- Interface: uma classe de 3-variedades com um certificado abstrato de que toda
variedade admissível é homeomorfa a S³.  Isto NÃO formaliza a prova de Perelman;
registra apenas onde ela entraria. -/
structure CertificadoPoincare (M : Type*) where
  admissivel : M → Prop
  homeoS3 : M → Prop
  certificado : ∀ m, admissivel m → homeoS3 m

/-- Com o certificado, o defeito topológico é zero: nenhuma variedade admissível
escapa. -/
theorem CertificadoPoincare.defeito_zero {M : Type*} (c : CertificadoPoincare M) :
    ¬ ∃ m, c.admissivel m ∧ ¬ c.homeoS3 m := by
  rintro ⟨m, hm, hn⟩; exact hn (c.certificado m hm)

/-- Característica de Euler de S³ a partir dos números de Betti (1, 0, 0, 1). -/
theorem euler_S3 : (1 : ℤ) - 0 + 0 - 1 = 0 := by norm_num

end ATK.OmegaClasses

#print axioms ATK.OmegaClasses.Superpoly.add_of_nonneg
#print axioms ATK.OmegaClasses.Superpoly.mul_of_one_le
#print axioms ATK.OmegaClasses.Contracao.comp_apply
#print axioms ATK.OmegaClasses.Contracao.comp_assoc
#print axioms ATK.OmegaClasses.Contracao.apply_fixo
#print axioms ATK.OmegaClasses.Contracao.orbita_sub_fixo
#print axioms ATK.OmegaClasses.Contracao.exA_comp_exB
#print axioms ATK.OmegaClasses.Contracao.exB_comp_exA
#print axioms ATK.OmegaClasses.Contracao.exA_fixo
#print axioms ATK.OmegaClasses.Contracao.exemplo_simulador
#print axioms ATK.OmegaClasses.EspectroFinito.gap_somaDireta
#print axioms ATK.OmegaClasses.EspectroFinito.exemplo
#print axioms ATK.OmegaClasses.NumeroB.exemplo
#print axioms ATK.OmegaClasses.det_conj_unimodular
#print axioms ATK.OmegaClasses.det_exemplo
#print axioms ATK.OmegaClasses.quociente_trivial_iff
#print axioms ATK.OmegaClasses.Exclusao.disjUnion_F_empty_iff
#print axioms ATK.OmegaClasses.CertificadoPoincare.defeito_zero
#print axioms ATK.OmegaClasses.euler_S3
