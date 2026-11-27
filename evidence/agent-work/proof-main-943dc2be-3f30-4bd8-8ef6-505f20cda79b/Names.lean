import Proofs.GeneralizedMackeyDecomposition
open Lean in
run_cmd do
  for (n, _) in (← getEnv).constants.toList do
    if n.toString.contains "repCofan" || n.toString.contains "inclusionAt" then
      logInfo m!"{n} {repr n}"
