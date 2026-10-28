import ATK.Conditional.YangMills
import ATK.YMOficial

/-!
# F.1/O8: `ConstructiveYM4D` é paramétrica

`ConstructiveYM4D M` só fala de campos abstratos de `M : YMModel` (`OSAxioms`, `ClusterRate`), sem
nenhum dos axiomas de Osterwalder–Schrader escrito. O kernel mostra que ela **não tem conteúdo
fixo**: num modelo ela vale (junto com `ClayYM`), noutro ela falha. Ela só passa a ser sobre
Yang–Mills quando o modelo é fixado, e o kernel não fixa nenhum.

A obrigação O8 contada por `OPEN_MATH` não é esta, é `ATK.YMOficial.YMNucleo`.

Ponto (iii) da auditoria de `YMNucleo`: a fórmula `ATK.YMOficial.wick` coincide com a de
Wick/Isserlis ordenada (pares na ordem original): `wick_dois`, `wick_tres` (ímpar ⇒ 0),
`wick_quatro` (os três emparelhamentos).
-/

namespace ATK.F1YM

open ATK.Conditional.YangMills

/-- Modelo com `OSAxioms` e `ClusterRate` sempre verdadeiros. -/
def modeloVacuo : YMModel.{0, 0, 0} where
  Group := Unit
  CompactSimple := fun _ => True
  Euclidean := Unit
  OSAxioms := fun _ _ => True
  ClusterRate := fun _ _ => True
  Quantum := Unit
  reconstruct := fun _ => ()
  IsQuantumYM := fun _ _ => True
  GapAtLeast := fun _ _ => True

/-- Modelo com `OSAxioms` sempre falso. -/
def modeloVazio : YMModel.{0, 0, 0} :=
  { modeloVacuo with OSAxioms := fun _ _ => False }

/-- **Num modelo, `ConstructiveYM4D`, a ponte e o enunciado "Clay" valem trivialmente.** -/
theorem vale_no_vacuo :
    ConstructiveYM4D modeloVacuo ∧ OSReconstruction modeloVacuo ∧ ClayYM modeloVacuo :=
  ⟨fun _ _ => ⟨(), trivial, 1, one_pos, trivial⟩,
   fun _ _ _ => ⟨trivial, fun _ _ => trivial⟩,
   fun _ _ => ⟨(), trivial, 1, one_pos, trivial⟩⟩

/-- **Noutro, falha.** -/
theorem falha_no_vazio : ¬ ConstructiveYM4D modeloVazio := fun h => by
  obtain ⟨_, hOS, _⟩ := h () trivial
  exact hOS

/-- **Veredito**: o valor de `ConstructiveYM4D` depende só do modelo; sem fixar o modelo ela não é
um enunciado sobre Yang–Mills. -/
theorem parametrica :
    (∃ M : YMModel.{0, 0, 0}, ConstructiveYM4D M) ∧ (∃ M : YMModel.{0, 0, 0}, ¬ ConstructiveYM4D M) :=
  ⟨⟨_, vale_no_vacuo.1⟩, ⟨_, falha_no_vazio⟩⟩

section Wick

open ATK.YMOficial

variable {S : Type*} (w : S → S → ℂ) (a b c d : S)

theorem wick_dois : wick w [a, b] = w a b := by simp [wick]

theorem wick_tres : wick w [a, b, c] = 0 := by simp [wick, Fin.sum_univ_succ]

theorem wick_quatro : wick w [a, b, c, d] = w a b * w c d + w a c * w b d + w a d * w b c := by
  simp only [wick, List.length_cons, List.length_nil, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  rw [wick_dois w c d, wick_dois w b d, wick_dois w b c]
  ring

end Wick

section ForaDeD

/-! ### Os axiomas de `Wightman` do kernel só usam `φ` em `D`

O kernel pede `φ f : H →ₗ H` (definido em todo `H`), enquanto os textos têm operadores ilimitados
definidos só em `D`. `troca_fora_de_D`: mudar `φ` fora de `D` preserva todos os campos de
`Wightman` e as funções `wfun` (logo `NaoTrivial`); `GapMassa` só usa `U`. `extensao_de_D`: todo
campo definido em `D` estende-se a `H`, linearmente em `f`. Juntos: a exigência de domínio total
não exclui nenhuma teoria de Wightman clássica (Hellinger–Toeplitz não se aplica, porque
`hermitiano` só quantifica sobre `D × D`). -/

open scoped InnerProductSpace
open ATK.L5Base ATK.YMOficial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem foldr_mem (W : Wightman H) (fs : List (SchwartzMap ET ℂ)) :
    fs.foldr (fun f v => W.φ f v) W.Ω ∈ W.D := by
  induction fs with
  | nil => exact W.Ω_mem
  | cons f fs ih => exact W.φ_D f _ ih

/-- **Os axiomas só usam `φ` em `D`**: trocar `φ` fora de `D` dá outra teoria de Wightman. -/
theorem troca_fora_de_D (W : Wightman H) (φ' : SchwartzMap ET ℂ →ₗ[ℂ] H →ₗ[ℂ] H)
    (h : ∀ f, ∀ ψ ∈ W.D, φ' f ψ = W.φ f ψ) :
    ∃ W' : Wightman H, W'.φ = φ' ∧ W'.U = W.U ∧ W'.Ω = W.Ω ∧ W'.D = W.D ∧
      wfun W' = wfun W := by
  have hfold : ∀ fs : List (SchwartzMap ET ℂ),
      fs.foldr (fun f v => φ' f v) W.Ω = fs.foldr (fun f v => W.φ f v) W.Ω := by
    intro fs
    induction fs with
    | nil => rfl
    | cons f fs ih => simp only [List.foldr_cons, ih]; exact h f _ (foldr_mem W fs)
  let W' : Wightman H :=
    { W with
      φ := φ'
      φ_D := fun f ψ hψ => by rw [h f ψ hψ]; exact W.φ_D f ψ hψ
      temperado := fun ψ hψ χ hχ => by
        have : (fun f : SchwartzMap ET ℂ => ⟪χ, φ' f ψ⟫_ℂ) = fun f => ⟪χ, W.φ f ψ⟫_ℂ := by
          funext f; rw [h f ψ hψ]
        rw [this]; exact W.temperado ψ hψ χ hχ
      hermitiano := fun f f' hf ψ hψ χ hχ => by
        rw [h f ψ hψ, h f' χ hχ]; exact W.hermitiano f f' hf ψ hψ χ hχ
      covariante := fun a Λ f f' hf ψ hψ => by
        rw [h f ψ hψ, h f' _ (W.U_D a Λ ψ hψ)]; exact W.covariante a Λ f f' hf ψ hψ
      localidade := fun f g hfg ψ hψ => by
        rw [h g ψ hψ, h f _ (W.φ_D g ψ hψ), h f ψ hψ, h g _ (W.φ_D f ψ hψ)]
        exact W.localidade f g hfg ψ hψ
      ciclico := by
        have : {v : H | ∃ fs : List (SchwartzMap ET ℂ), v = fs.foldr (fun f v => φ' f v) W.Ω} =
            {v : H | ∃ fs : List (SchwartzMap ET ℂ), v = fs.foldr (fun f v => W.φ f v) W.Ω} := by
          ext v; simp only [Set.mem_ofPred_eq, hfold]
        rw [this]; exact W.ciclico }
  refine ⟨W', rfl, rfl, rfl, rfl, ?_⟩
  have hvev : ∀ f, vev W' f = vev W f := fun f => by
    simp only [vev]; exact congrArg _ (h f _ W.Ω_mem)
  have hC : ∀ f, ∀ ψ ∈ W.D, campoC W' f ψ = campoC W f ψ := fun f ψ hψ => by
    simp only [campoC, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hvev]
    exact congrArg (· - _) (h f ψ hψ)
  have hCD : ∀ f, ∀ ψ ∈ W.D, campoC W f ψ ∈ W.D := fun f ψ hψ => by
    simp only [campoC, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact W.D.sub_mem (W.φ_D f ψ hψ) (W.D.smul_mem _ hψ)
  have hmem : ∀ fs : List (SchwartzMap ET ℂ), fs.foldr (fun f v => campoC W f v) W.Ω ∈ W.D := by
    intro fs; induction fs with
    | nil => exact W.Ω_mem
    | cons f fs ih => exact hCD f _ ih
  funext fs
  simp only [wfun]
  congr 1
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.foldr_cons]
    rw [show (W'.Ω : H) = W.Ω from rfl] at ih ⊢
    rw [ih]; exact hC f _ (hmem fs)

omit [CompleteSpace H] in
/-- **Extensão de `D` a `H`**: um campo definido só em `D` (como nos textos, operadores
ilimitados) estende-se a `H →ₗ H`, linearmente em `f`, sem mudar os valores em `D`. -/
theorem extensao_de_D (D : Submodule ℂ H)
    (φ₀ : SchwartzMap ET ℂ →ₗ[ℂ] D →ₗ[ℂ] H) :
    ∃ φ : SchwartzMap ET ℂ →ₗ[ℂ] H →ₗ[ℂ] H, ∀ f, ∀ ψ (hψ : ψ ∈ D), φ f ψ = φ₀ f ⟨ψ, hψ⟩ := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl D
  let P := Submodule.projectionOnto D C hC
  refine ⟨{ toFun := fun f => (φ₀ f).comp P
            map_add' := fun f g => by ext ψ; simp
            map_smul' := fun c f => by ext ψ; simp }, fun f ψ hψ => ?_⟩
  show φ₀ f (P ψ) = φ₀ f ⟨ψ, hψ⟩
  rw [Submodule.projectionOnto_apply_left hC ⟨ψ, hψ⟩]

end ForaDeD

end ATK.F1YM

#print axioms ATK.F1YM.vale_no_vacuo
#print axioms ATK.F1YM.falha_no_vazio
#print axioms ATK.F1YM.parametrica
#print axioms ATK.F1YM.wick_dois
#print axioms ATK.F1YM.wick_tres
#print axioms ATK.F1YM.wick_quatro
#print axioms ATK.F1YM.foldr_mem
#print axioms ATK.F1YM.troca_fora_de_D
#print axioms ATK.F1YM.extensao_de_D
