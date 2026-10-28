import ATK.TerceiroTemploII
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Teorema 3 no caso geral: gap espectral de todo grafo finito conexo

Para um grafo finito conexo `G` com `n` vértices e pesos `w ≥ 0` com `w u v ≥ c > 0` em toda
aresta:

  `∑ᵥ (f v − f̄)² ≤ (n² / c) · E(f)`  (`poincare_grafo`),

logo, fora das constantes, `E(f) ≥ (c / n²) · ∑ (f − f̄)²`: **`λ₂ ≥ c / n² > 0`** (`gap_grafo`).

Prova (sem compacidade, com constante explícita):

* `quadrado_caminho`: por Cauchy–Schwarz ao longo de um passeio `p` de `u` a `v`,
  `(f v − f u)² ≤ |p| · ∑_{arestas de p} (Δf)²` (indução no passeio, `desigualdade_passo`);
* `somaDarts_le`: num caminho (sem vértice repetido) as arestas são distintas, então a soma ao
  longo dele é `≤ E(f) / c`;
* um caminho tem comprimento `< n` (`IsPath.length_lt`); somando sobre os `n` vértices e usando que
  a média minimiza o desvio (`desvio_minimo`), sai a constante `n² / c`.

Com isso o Teorema 3 do documento fica demonstrado no caso geral; a Árvore (`poincare_arvore`,
constante `10`) é um caso com constante melhor.
-/

open ATK.TerceiroTemplo SimpleGraph

namespace ATK.GapGrafo

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- `∑` dos quadrados das diferenças ao longo de uma lista de arestas orientadas. -/
def somaDarts (f : V → ℝ) (l : List G.Dart) : ℝ := (l.map fun d => (f d.fst - f d.snd) ^ 2).sum

omit [Fintype V] [DecidableEq V] in
theorem somaDarts_nonneg (f : V → ℝ) (l : List G.Dart) : 0 ≤ somaDarts f l :=
  List.sum_nonneg fun _ h => by
    obtain ⟨d, _, rfl⟩ := List.mem_map.1 h
    exact sq_nonneg _

/-- Passo de Cauchy–Schwarz: `b² ≤ L S ⟹ (a + b)² ≤ (L + 1)(a² + S)`. -/
theorem desigualdade_passo (a b L S : ℝ) (hL : 0 ≤ L) (hS : 0 ≤ S) (hb : b ^ 2 ≤ L * S) :
    (a + b) ^ 2 ≤ (L + 1) * (a ^ 2 + S) := by
  rcases hL.lt_or_eq with h | h
  · have key : 0 ≤ L * (L * a ^ 2 + S - 2 * a * b) := by
      nlinarith [sq_nonneg (L * a - b)]
    have h2 : 0 ≤ L * a ^ 2 + S - 2 * a * b := (mul_nonneg_iff_of_pos_left h).mp key
    nlinarith
  · subst h
    have hb0 : b = 0 := by nlinarith [sq_nonneg b]
    subst hb0
    nlinarith

/-- **Cauchy–Schwarz ao longo de um passeio.** -/
theorem quadrado_caminho (f : V → ℝ) : ∀ {u v : V} (p : G.Walk u v),
    (f v - f u) ^ 2 ≤ p.length * somaDarts f p.darts
  | _, _, .nil => by simp [somaDarts]
  | u, v, .cons (v := x) h q => by
    have ih := quadrado_caminho f q
    have hS := somaDarts_nonneg f q.darts
    have e : f v - f u = (f x - f u) + (f v - f x) := by ring
    have hstep := desigualdade_passo (f x - f u) (f v - f x) q.length (somaDarts f q.darts)
      (Nat.cast_nonneg _) hS ih
    have hdarts : somaDarts f (Walk.cons h q).darts = (f u - f x) ^ 2 + somaDarts f q.darts := by
      simp [somaDarts, Walk.darts_cons]
    rw [hdarts, Walk.length_cons, e]
    push_cast
    have : (f u - f x) ^ 2 = (f x - f u) ^ 2 := by ring
    rw [this]
    exact hstep

section Pesos

variable [DecidableRel G.Adj] {w : V → V → ℝ} {c : ℝ}

/-- A soma ao longo de um caminho é `≤ E(f) / c`. -/
theorem somaDarts_le (hw0 : ∀ u v, 0 ≤ w u v) (hc : 0 < c)
    (hadj : ∀ u v, G.Adj u v → c ≤ w u v) (f : V → ℝ) {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) : somaDarts f p.darts ≤ energia w f / c := by
  have hnd : p.darts.Nodup := Walk.darts_nodup_of_support_nodup hp.support_nodup
  have h1 : somaDarts f p.darts = ∑ d ∈ p.darts.toFinset, (f d.fst - f d.snd) ^ 2 := by
    rw [somaDarts, List.sum_toFinset _ hnd]
  have h2 : ∑ d ∈ p.darts.toFinset, (f d.fst - f d.snd) ^ 2 ≤
      ∑ d : G.Dart, (f d.fst - f d.snd) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  have h3 : ∑ d : G.Dart, (f d.fst - f d.snd) ^ 2 ≤
      ∑ x : V × V, w x.1 x.2 / c * (f x.1 - f x.2) ^ 2 := by
    have hinj : Function.Injective (fun d : G.Dart => d.toProd) := fun d₁ d₂ h => Dart.ext _ _ h
    calc ∑ d : G.Dart, (f d.fst - f d.snd) ^ 2
        = ∑ x ∈ Finset.univ.image (fun d : G.Dart => d.toProd), (f x.1 - f x.2) ^ 2 := by
          rw [Finset.sum_image fun a _ b _ h => hinj h]
      _ ≤ ∑ x ∈ Finset.univ.image (fun d : G.Dart => d.toProd), w x.1 x.2 / c * (f x.1 - f x.2) ^ 2 := by
          refine Finset.sum_le_sum fun x hx => ?_
          obtain ⟨d, _, rfl⟩ := Finset.mem_image.1 hx
          have hcw : 1 ≤ w d.fst d.snd / c := by
            rw [le_div_iff₀ hc, one_mul]
            exact hadj _ _ d.adj
          nlinarith [sq_nonneg (f d.fst - f d.snd)]
      _ ≤ ∑ x : V × V, w x.1 x.2 / c * (f x.1 - f x.2) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ =>
            mul_nonneg (div_nonneg (hw0 _ _) hc.le) (sq_nonneg _)
  have h4 : ∑ x : V × V, w x.1 x.2 / c * (f x.1 - f x.2) ^ 2 = energia w f / c := by
    rw [Fintype.sum_prod_type, energia, div_eq_inv_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    ring
  linarith

/-- **Desigualdade de Poincaré em todo grafo finito conexo**: `∑ (f − f̄)² ≤ (n²/c) · E(f)`. -/
theorem poincare_grafo (hconn : G.Connected) (hw0 : ∀ u v, 0 ≤ w u v) (hc : 0 < c)
    (hadj : ∀ u v, G.Adj u v → c ≤ w u v) (f : V → ℝ) :
    haveI : Nonempty V := hconn.nonempty
    ∑ v, (f v - media f) ^ 2 ≤ (Fintype.card V : ℝ) ^ 2 / c * energia w f := by
  have : Nonempty V := hconn.nonempty
  set r : V := Classical.arbitrary V
  set n : ℝ := (Fintype.card V : ℝ)
  have hE : 0 ≤ energia w f := energia_nonneg hw0 f
  have hv : ∀ v, (f v - f r) ^ 2 ≤ n * (energia w f / c) := by
    intro v
    obtain ⟨p⟩ := hconn.preconnected r v
    let q := p.toPath
    have hq : (q : G.Walk r v).IsPath := q.property
    have hlen : ((q : G.Walk r v).length : ℝ) ≤ n := by
      simp only [n]
      exact_mod_cast (hq.length_lt).le
    calc (f v - f r) ^ 2 ≤ (q : G.Walk r v).length * somaDarts f (q : G.Walk r v).darts :=
          quadrado_caminho f _
      _ ≤ n * (energia w f / c) :=
          mul_le_mul hlen (somaDarts_le hw0 hc hadj f _ hq) (somaDarts_nonneg _ _)
            (Nat.cast_nonneg _)
  calc ∑ v, (f v - media f) ^ 2 ≤ ∑ v, (f v - f r) ^ 2 := desvio_minimo f (f r)
    _ ≤ ∑ _v : V, n * (energia w f / c) := Finset.sum_le_sum fun v _ => hv v
    _ = n ^ 2 / c * energia w f := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- **Gap espectral** de todo grafo finito conexo: `E(f) ≥ (c / n²) · ∑ (f − f̄)²`. -/
theorem gap_grafo (hconn : G.Connected) (hw0 : ∀ u v, 0 ≤ w u v) (hc : 0 < c)
    (hadj : ∀ u v, G.Adj u v → c ≤ w u v) (f : V → ℝ) :
    haveI : Nonempty V := hconn.nonempty
    c / (Fintype.card V : ℝ) ^ 2 * ∑ v, (f v - media f) ^ 2 ≤ energia w f := by
  have : Nonempty V := hconn.nonempty
  have h := poincare_grafo hconn hw0 hc hadj f
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 := by
    have : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hn]
  calc c * ∑ v, (f v - media f) ^ 2 ≤ c * ((Fintype.card V : ℝ) ^ 2 / c * energia w f) :=
        mul_le_mul_of_nonneg_left h hc.le
    _ = energia w f * (Fintype.card V : ℝ) ^ 2 := by field_simp

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A constante do gap é positiva. -/
theorem constante_gap_pos (hconn : G.Connected) (hc : 0 < c) :
    0 < c / (Fintype.card V : ℝ) ^ 2 := by
  have : Nonempty V := hconn.nonempty
  have : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  positivity

end Pesos

end ATK.GapGrafo

#print axioms ATK.GapGrafo.somaDarts_nonneg
#print axioms ATK.GapGrafo.desigualdade_passo
#print axioms ATK.GapGrafo.quadrado_caminho
#print axioms ATK.GapGrafo.somaDarts_le
#print axioms ATK.GapGrafo.poincare_grafo
#print axioms ATK.GapGrafo.gap_grafo
#print axioms ATK.GapGrafo.constante_gap_pos
