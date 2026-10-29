import ATK.FinalRoot

/-!
# ATK — Linguagem tipada de certificados terminais

Este módulo fornece uma interface formal para as obrigações restantes.
Não declara resolvidos os problemas originais. Em particular, `Raiz M`
é uma conjunção paramétrica e cinco dos seus componentes requerem
ligações independentes aos objetos matemáticos originais.

Os campos `bridges` e `producers` são provas exigidas como entrada:
definir um registro não constrói essas provas.
-/

namespace ATK.TerminalLanguage

open ATK.ClosedMath ATK.FinalRoot

/-- Evidências necessárias para obter a raiz paramétrica. A existência
deste tipo não fornece um habitante. -/
structure ConditionalCertificate (M : Models) : Prop where
  bridges : PontesRestantes M
  producers : Produtores M

/-- Aplicação formal de uma redução já estabelecida. Não é uma prova
incondicional de nenhuma das conjecturas originais. -/
theorem parameterized_root_of_certificate {M : Models}
    (h : ConditionalCertificate M) : Raiz M :=
  raiz_de_produtores h.bridges h.producers

/-- A parte fiel RH ∧ Beal é consequência do certificado condicional,
mas não é demonstrada sem a entrada `h`. -/
theorem faithful_pair_of_certificate {M : Models}
    (h : ConditionalCertificate M) : VerdeFiel :=
  raiz_implica_fiel (parameterized_root_of_certificate h)

/-- O certificado não elimina as obrigações: recupera explicitamente
as provas dos produtores e das pontes fornecidas como entrada. -/
theorem certificate_requires_producers {M : Models}
    (h : ConditionalCertificate M) : Produtores M :=
  h.producers

theorem certificate_requires_bridges {M : Models}
    (h : ConditionalCertificate M) : PontesRestantes M :=
  h.bridges

end ATK.TerminalLanguage

#print axioms ATK.TerminalLanguage.parameterized_root_of_certificate
#print axioms ATK.TerminalLanguage.faithful_pair_of_certificate
#print axioms ATK.TerminalLanguage.certificate_requires_producers
#print axioms ATK.TerminalLanguage.certificate_requires_bridges
