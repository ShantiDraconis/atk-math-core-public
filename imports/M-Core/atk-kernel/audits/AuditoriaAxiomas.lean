import Lean

/-!
# Auditoria de axiomas do `ATK` (meta-programa; não faz parte da biblioteca certificada)

`#auditoria_atk` percorre toda constante importada cujo nome começa com `ATK` e, para cada
teorema, imprime uma linha separada por tabulação

    TEOREMA <OK|PROIBIDO> <nome> <axiomas>

usando `Lean.collectAxioms` (a mesma travessia de `#print axioms`). Imprime também toda
declaração `axiom` sob `ATK` e uma linha de resumo. Permitidos: `propext`, `Classical.choice`,
`Quot.sound`. Qualquer outro (incluindo `sorryAx` e `Lean.ofReduceBool`) é PROIBIDO.

Uso: um arquivo-driver que importa os módulos a auditar, depois `import audits.AuditoriaAxiomas`
(ou este arquivo compilado à parte) e o comando `#auditoria_atk`. Ver `scripts/status_calculado.py`.
-/

open Lean Elab Command

def atkPermitidos : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#auditoria_atk" : command => do
  let env ← getEnv
  let mut tms : Array (String × List Name) := #[]
  let mut axs : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    if (`ATK).isPrefixOf n && !n.isInternal then
      match ci with
      | .thmInfo _ =>
          let a ← liftCoreM <| Lean.collectAxioms n
          tms := tms.push (n.toString, a.toList)
      | .axiomInfo _ => axs := axs.push n.toString
      | _ => pure ()
  let ord := tms.qsort (fun a b => a.1 < b.1)
  let mut ok := 0
  let mut bad := 0
  for (n, a) in ord do
    let proib := a.filter (fun x => !atkPermitidos.contains x)
    if proib.isEmpty then ok := ok + 1 else bad := bad + 1
    IO.println s!"TEOREMA\t{if proib.isEmpty then "OK" else "PROIBIDO"}\t{n}\t{a}"
  for x in axs.qsort (· < ·) do
    IO.println s!"AXIOMA_ATK\t{x}"
  IO.println s!"RESUMO\tteoremas={ord.size}\tok={ok}\tproibidos={bad}\taxiomas_atk={axs.size}"
