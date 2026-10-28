# Origem de `ATK/FltRegular/`

Cópia da formalização **flt-regular** (último teorema de Fermat para primos regulares, Lean 4):

* repositório: <https://github.com/leanprover-community/flt-regular>
* commit: `faae830` (05/09/2026), o último do projeto sobre Lean `v4.34.0-rc2`, cuja Mathlib
  (`1ed178f0ec`) é ancestral da Mathlib `v4.34.1` usada pelo atk-kernel
* licença: Apache 2.0 (`LICENSE` nesta pasta, copiado do projeto)
* autores (histórico do repositório): Riccardo Brasca, Ruben Van de Velde, Chris Birkbeck,
  Eric Rodriguez, Andrew Yang, Alex J. Best, Kim Morrison e colaboradores

Mudanças feitas na cópia (nenhuma altera enunciados ou o conteúdo matemático):

1. `import FltRegular.…` / `public import FltRegular.…` → `import ATK.FltRegular.…` (o módulo raiz
   `FltRegular.lean`, só de importações, não foi copiado; `unseen.lean`, utilitário de
   documentação com IO, também não);
2. `NumberTheory/Hilbert92.lean`: a Mathlib de 10/09/2026 trocou `MulEquiv.Monoid.End` por
   `MulEquiv.monoidEnd` (com o tipo explícito); as duas ocorrências passaram a
   `MulEquiv.monoidEnd _`, e a lista de reescritas de `isTors'` foi ajustada exatamente como na
   versão posterior do próprio projeto (commit `b8a5f23`).

Verificação: as fontes não têm `sorry`, `admit`, `axiom`, `native_decide` nem comandos com IO; os
teoremas expostos em `ATK/FermatRegular.lean` (`flt_cinco`, `flt_sete`, `flt_primo_regular`, …)
dependem só de `propext`, `Classical.choice` e `Quot.sound`, conferido pelo `#print axioms` do
auditor. Os nomes das declarações originais (no espaço raiz e em `FltRegular`) foram mantidos.
