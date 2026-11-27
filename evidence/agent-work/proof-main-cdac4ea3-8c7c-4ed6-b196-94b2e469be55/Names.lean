import Proofs.ParabolicExtremalOutsideRestrictionRegions
import Proofs.EvaluationForTwoProjections
import Lean
open Lean in
run_cmd do
  let env ← getEnv
  for (n, _) in env.constants do
    if ["left_project_eval", "right_project_eval", "left_mul_eval", "right_mul_eval",
        "parabolic_finite", "frame_eq", "leftParameter", "rightParameter",
        "left_shape", "right_shape", "leftAs", "rightAs"].contains (n.toString.splitOn ".").getLast! then
      logInfo m!"{n}"
