import MackeyDiagrams
import Proofs.ThreeInductionReidemeisterThree
import Proofs.ReplacementForTwoProjections
import Proofs.ReplacementForTwoMultiplications
import Proofs.FiniteParabolicJoinOfFamily

set_option maxHeartbeats 2000000

private noncomputable abbrev realizedLeft := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoMultiplications `TwoMultiplicationsAux.realizeLeft)
#check @realizedLeft
