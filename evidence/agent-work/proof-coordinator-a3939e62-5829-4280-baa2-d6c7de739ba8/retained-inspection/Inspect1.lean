import Lean
import Proofs.RightUpReidemeisterCurl
import Proofs.RightCurlAndDotSlide
import Proofs.InductionMergeDotSlide
import Proofs.InductionSplitDotSlide
import Proofs.RestrictionMergeDotSlide
import Proofs.RestrictionSplitDotSlide
import Proofs.DotBelowInsideAboveRightCurl
import Proofs.CurlWithCentralizingDot
import Proofs.MovingMergeDotBackToBranch
import Proofs.MovingSplitDotToOutputBranch
import Proofs.CurlAcrossTrivalentVertex
import Proofs.DifferentCurlIndices
import Proofs.LeftDownReidemeisterCurl
import Proofs.NormalizedIndexValuedReidemeisterCurls
import Proofs.NormalizedTrivalentCurl
import Proofs.FixedBoundaryReplacementPreorder
import Proofs.RightInputDotSlideObstruction
import Proofs.DotSlidePreorderNotSymmetric
import Proofs.InductionBimoduleOrbitSumBasis
import Proofs.FiniteOrbitSumDiagram
import Proofs.FiniteParabolicConjugateBlocks
import Proofs.FiniteParabolicIntersectionBlocks
import Proofs.FiniteParabolicJoinBlocks
import Proofs.FiniteParabolicClosure
import Proofs.ExtremalParabolicsOfFiniteGroup
import Proofs.BlockwiseGroupElementDotCriterion
import Proofs.BlockSwapOrbitSumWithoutGroupDot
open Lean Elab Command

partial def inspectDecl (env : Environment) (traverseMods : List String) (root : Name)
    (kind : String) (seen : NameSet) : CommandElabM NameSet := do
  if seen.contains root then return seen
  let some d := env.find? root | return seen
  let mut seen := seen.insert root
  let modOf := fun n => ((env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!)).getD .anonymous
  for (sectionName, expr) in #[("type", some d.type), ("value", d.value? (allowOpaque := true))] do
    if let some expr := expr then
      for c in expr.getUsedConstants do
        let m := modOf c
        let loc ← findDeclarationRanges? c
        IO.println s!"ref\t{kind}\t{root}\t{sectionName}\t{m}\t{c}\t{(loc.map (·.selectionRange.pos.line)).getD 0}"
        if traverseMods.contains m.toString then
          seen ← inspectDecl env traverseMods c kind seen
    else
      IO.println s!"novalue\t{root}\t{sectionName}"
  return seen

elab "#inspect " n:ident : command => do
  let name := n.getId
  let env ← getEnv
  let some modIndex := env.getModuleIdxFor? name | throwError "Missing {name}"
  let mod := env.header.moduleNames[modIndex.toNat]!
  let ax ← Lean.collectAxioms name
  IO.println s!"start\t{name}\t{mod}\t{ax}"
  let _ ← inspectDecl env [mod.toString] name "endpoint" {}
#inspect RightUpReidemeisterCurl
#inspect RightCurlAndDotSlide
#inspect InductionMergeDotSlide
#inspect InductionSplitDotSlide
#inspect RestrictionMergeDotSlide
#inspect RestrictionSplitDotSlide
#inspect DotBelowInsideAboveRightCurl
#inspect CurlWithCentralizingDot
#inspect MovingMergeDotBackToBranch
#inspect MovingSplitDotToOutputBranch
#inspect CurlAcrossTrivalentVertex
#inspect DifferentCurlIndices
#inspect LeftDownReidemeisterCurl
#inspect NormalizedIndexValuedReidemeisterCurls
#inspect NormalizedTrivalentCurl
#inspect FixedBoundaryReplacementPreorder
#inspect RightInputDotSlideObstruction
#inspect DotSlidePreorderNotSymmetric
#inspect InductionBimoduleOrbitSumBasis
#inspect FiniteOrbitSumDiagram
#inspect FiniteParabolicConjugateBlocks
#inspect FiniteParabolicIntersectionBlocks
#inspect FiniteParabolicJoinBlocks
#inspect FiniteParabolicClosure
#inspect ExtremalParabolicsOfFiniteGroup
#inspect BlockwiseGroupElementDotCriterion
#inspect BlockSwapOrbitSumWithoutGroupDot
