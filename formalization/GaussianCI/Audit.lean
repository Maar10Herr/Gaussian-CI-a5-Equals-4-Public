module

import GaussianCI
import Lean.Util.CollectAxioms

/-!
Check the transitive axiom dependencies of every exported project theorem.
This check rejects unproved project axioms, `sorryAx`, and native-evaluation
oracles. The three permitted dependencies are standard Lean foundations.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if name.toString.startsWith "GaussianCI." then
      -- Module imports can expose proved propositions as axiomInfo entries.
      -- collectAxioms uses their exported dependency metadata, so inspect both
      -- representations; checking thmInfo alone would miss imported proofs.
      if info matches .thmInfo _ | .axiomInfo _ then
        count := count + 1
        let dependencies ← collectAxioms name
        for dependency in dependencies do
          unless allowed.contains dependency do
            throwError "unexpected axiom {dependency} in {name}"
  if count == 0 then
    throwError "no project theorems were found"
  logInfo m!"axiom_audit_ok proof_declarations={count} allowed=propext,Classical.choice,Quot.sound"
