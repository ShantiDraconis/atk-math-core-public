import ATK.Conditional.Riemann
import ATK.Conditional.NavierStokes
import ATK.Conditional.PvsNP
import ATK.Conditional.Hodge
import ATK.Conditional.BSD
import ATK.Conditional.YangMills
import ATK.Conditional.Beal

/-!
# Os 7 lanes do M-Core em forma condicional

Cada arquivo segue o mesmo molde:

  PONTE (teoremas publicados, ainda não formalizados na Mathlib)
  → HIPÓTESE ABERTA (o que falta de matemática nova)
  → ENUNCIADO do problema

e termina com `#print axioms`. Pontes e hipóteses abertas entram como ARGUMENTOS
explícitos dos teoremas, nunca como `axiom`; por isso a auditoria só deve ver
`propext`, `Classical.choice` e `Quot.sound`.

| Problema | Teorema | Fidelidade do enunciado |
|---|---|---|
| Riemann | `ATK.Conditional.Riemann.riemann_conditional` | OFICIAL (`RiemannHypothesis` da Mathlib) |
| Beal | `ATK.Conditional.Beal.beal_conditional` | OFICIAL (enunciado elementar) |
| Navier–Stokes | `ATK.Conditional.NavierStokes.ns_conditional` | PARAMÉTRICA (`NSModel`) |
| P vs NP | `ATK.Conditional.PvsNP.pvsnp_conditional` | PARAMÉTRICA (`ComplexityModel`) |
| Hodge | `ATK.Conditional.Hodge.hodge_conditional` | PARAMÉTRICA (`HodgeModel`) |
| BSD | `ATK.Conditional.BSD.bsd_conditional` | PARAMÉTRICA (`BSDModel`) |
| Yang–Mills | `ATK.Conditional.YangMills.ym_conditional` | PARAMÉTRICA (`YMModel`) |

Nenhum destes teoremas resolve um problema: `OPEN_MATH = true` nos sete.
-/
