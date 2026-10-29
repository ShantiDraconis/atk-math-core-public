import ATK.StatusHonesto

/-!
# ATK — Análise da equação de inversão OPEN/CLOSED em `ValorBelnap`

Pergunta: o que faria `OPEN_MATH` e `CLOSED_MATH` fecharem como "`true/false` invertido um do
outro" sem nunca construir `ATK.RefutacaoTri.Tri.tf` (isto é, sem nunca exigir `P` e `¬P` ao
mesmo tempo)? Resposta mecânica, abaixo, sobre o tipo `ATK.StatusHonesto.ValorBelnap` — nenhum
teorema aqui prova ou refuta qualquer enunciado matemático do projeto; eles só caracterizam a
equação formal `aberto = neg fechado` sobre rótulos de evidência.
-/

namespace ATK.AnaliseInversao

open ATK.StatusHonesto

/-- Negação de Belnap sobre `ValorBelnap`: inverte `verdadeiro`/`falso`, fixa `ambos` e
`nenhum` (ambos já carregam sua própria "contraparte" dentro de si). -/
def neg : ValorBelnap → ValorBelnap
  | .verdadeiro => .falso
  | .falso => .verdadeiro
  | .ambos => .ambos
  | .nenhum => .nenhum

theorem neg_ambos_fixo : neg .ambos = .ambos := rfl
theorem neg_nenhum_fixo : neg .nenhum = .nenhum := rfl

/-- A equação informal "`OPEN_MATH` `true/false` = `CLOSED_MATH` `false/true`": o valor relatado
para a camada aberta é a negação de Belnap do valor relatado para a camada fechada. -/
def equacaoInversao (aberto fechado : ValorBelnap) : Prop :=
  aberto = neg fechado

theorem equacaoInversao_ambos : equacaoInversao .ambos .ambos := rfl
theorem equacaoInversao_nenhum : equacaoInversao .nenhum .nenhum := rfl

/-- Os únicos pontos fixos de `neg` — isto é, os únicos valores que podem satisfazer a equação
de inversão quando a camada aberta e a camada fechada relatam o **mesmo** valor — são `ambos` e
`nenhum`. Não existe um terceiro valor escondido: a lógica de Belnap de quatro valores já esgota
as possibilidades. -/
theorem fixo_e_ambos_ou_nenhum :
    ∀ v : ValorBelnap, neg v = v → v = .ambos ∨ v = .nenhum := by
  intro v h
  cases v with
  | verdadeiro => exact absurd h (by decide)
  | falso => exact absurd h (by decide)
  | ambos => exact Or.inl rfl
  | nenhum => exact Or.inr rfl

end ATK.AnaliseInversao

#print axioms ATK.AnaliseInversao.neg_ambos_fixo
#print axioms ATK.AnaliseInversao.neg_nenhum_fixo
#print axioms ATK.AnaliseInversao.equacaoInversao_ambos
#print axioms ATK.AnaliseInversao.equacaoInversao_nenhum
#print axioms ATK.AnaliseInversao.fixo_e_ambos_ou_nenhum
