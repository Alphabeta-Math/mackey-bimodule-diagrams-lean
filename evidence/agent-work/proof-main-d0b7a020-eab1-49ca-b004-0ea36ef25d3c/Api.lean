import MackeyDiagrams
import Proofs.ReplacementForTwoProjections
import Proofs.ReplacementForTwoMultiplications
import Proofs.FiniteParabolicIntersectionBlocks
import Proofs.FiniteParabolicJoinBlocks
import Proofs.CaseOneRightProjectionConstruction
import Proofs.CaseTwoLeftProjectionConstruction
open Lean Elab Command in
run_cmd do
  for (n, _) in (← getEnv).constants.toList do
    let s := n.toString
    if ([".merged_eq_iff", ".of_pulls", ".pulls_left", ".pulls_right", ".qstar_injective",
         ".leftAs", ".rightAs", ".productLabel", ".eval_eq_iff", ".splitRightInverse",
         ".mergeLeftInverse", ".extremalPaddedBlock", ".parabolic_finite",
         ".unitLeftEval", ".leftDrawing", ".rightDrawing", ".mergedEval", ".leftDot", ".rightDot",
         ".mixedColumn", ".cancelFrame", ".terms_single"].any (fun pat : String => s.endsWith pat)) then
      logInfo m!"{n}"
open MackeyDiagrams
#check FiniteParabolicClosure
#check FiniteParabolicConjugateBlocks
#check Generator.injective_mixedMultiplicationBasis
#check Subgroup.map_subtype_le
#check Subgroup.map_subgroupOf_eq_of_le
#check Subgroup.map_comap_eq_self
#check Subgroup.map_sup
#check MulEquiv.subgroupCongr
#check Equiv.Perm.ofSubtype_subtypePerm
#check Subgroup.finiteIndex_of_finite
#check Set.Finite.of_finite
#check Biset.Hom.cancel_middle
#check _private.Proofs.EvaluationForTwoProjections.«0».EvaluationForTwoProjectionsAux.pulls_left
#check _private.Proofs.ReplacementForTwoMultiplications.«0».TwoMultiplicationsAux.leftAs
#check _private.Proofs.ReplacementForTwoProjections.«0».ReplacementForTwoProjectionsAux.merged_eq_iff
