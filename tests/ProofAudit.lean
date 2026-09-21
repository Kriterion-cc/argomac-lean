import Proof
import Lean

run_cmd do
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    let origin := (env.getModuleIdxFor? name).bind fun index => env.header.moduleNames[index.toNat]?
    if origin.any (fun moduleName => #[`Construction, `Proof].contains moduleName.getRoot) then
      let illegal := (← Lean.collectAxioms name).filter fun axiomName =>
        !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
      unless illegal.isEmpty do
        Lean.throwError m!"The declaration {name} uses disallowed axioms: {illegal}"
