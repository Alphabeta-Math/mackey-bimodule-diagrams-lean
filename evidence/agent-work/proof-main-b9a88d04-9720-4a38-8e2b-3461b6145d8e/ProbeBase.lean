import MackeyDiagrams
import Proofs.ThreeInductionReidemeisterThree
import Proofs.ReplacementForTwoProjections
import Proofs.ReplacementForTwoMultiplications
import Proofs.FiniteParabolicJoinOfFamily

#check MackeyDiagrams.ScopedDiagram.eval
#check Equiv.Perm.ofSubtype_apply_of_not_mem
#check Finite.of_injective
#check Finite.Set.finite_image
open Lean Elab Command in
run_cmd do
  for (n, _) in (← getEnv).constants do
    if ["singleCaseTwo", "realizeLeft", "liftMultiplier", "leftCoefficients"].any (fun s => n.toString.endsWith s) then
      logInfo m!"{n}"
open private ReplacementForTwoProjectionsAux.singleCaseTwo from Proofs.ReplacementForTwoProjections
open private TwoMultiplicationsAux.realizeLeft from Proofs.ReplacementForTwoMultiplications
open private MultipliersUnderRelabellingProof.liftMultiplier from Proofs.MultipliersUnderRelabelling
#check @ReplacementForTwoProjectionsAux.singleCaseTwo
#check @TwoMultiplicationsAux.realizeLeft
#check @MultipliersUnderRelabellingProof.liftMultiplier
