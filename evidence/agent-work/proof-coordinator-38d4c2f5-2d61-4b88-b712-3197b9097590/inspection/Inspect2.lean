import Lean
import Proofs.DotBetweenImagesInOneBlock
import Proofs.StrongerEmbeddingConditionSlideObstruction
import Proofs.SupportBoundsUnderComposition
import Proofs.SupportBoundsForInverseProduct
import Proofs.MultiplicationCapBend
import Proofs.TraceCapBend
import Proofs.OrdinaryCupBend
import Proofs.ReverseCupBend
import Proofs.TrivalentBendIdentities
import Proofs.StraightMixedTrivalentVertices
import Proofs.RightDownReidemeisterCurl
import Proofs.LeftUpReidemeisterCurl
import Proofs.ReidemeisterOne
import Proofs.TransportToMackeyRepresentative
import Proofs.MixedCrossingComposites
import Proofs.MixedReidemeisterTwoMackeyCancellation
import Proofs.MixedCrossingsThroughSmallerGroup
import Proofs.CommonMackeyIntersectionSum
import Proofs.TwoMackeySummandsWithSameInternalLabels
import Proofs.SinglePairCannotProjectOntoSeveralDoubleCosets
import Proofs.SinglePairIdentityCriterion
import Proofs.ParallelInductionProductDotAdmissibility
import Proofs.ParallelReidemeisterTwoInduction
import Proofs.ParallelReidemeisterTwoRestriction
import Proofs.StandardSymmetricGroupBraidRelation
import Proofs.ThreeInductionCrossingMultipliers
import Proofs.MultipliersUnderRelabelling
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
#inspect DotBetweenImagesInOneBlock
#inspect StrongerEmbeddingConditionSlideObstruction
#inspect SupportBoundsUnderComposition
#inspect SupportBoundsForInverseProduct
#inspect MultiplicationCapBend
#inspect TraceCapBend
#inspect OrdinaryCupBend
#inspect ReverseCupBend
#inspect TrivalentBendIdentities
#inspect StraightMixedTrivalentVertices
#inspect RightDownReidemeisterCurl
#inspect LeftUpReidemeisterCurl
#inspect ReidemeisterOne
#inspect TransportToMackeyRepresentative
#inspect MixedCrossingComposites
#inspect MixedReidemeisterTwoMackeyCancellation
#inspect MixedCrossingsThroughSmallerGroup
#inspect CommonMackeyIntersectionSum
#inspect TwoMackeySummandsWithSameInternalLabels
#inspect SinglePairCannotProjectOntoSeveralDoubleCosets
#inspect SinglePairIdentityCriterion
#inspect ParallelInductionProductDotAdmissibility
#inspect ParallelReidemeisterTwoInduction
#inspect ParallelReidemeisterTwoRestriction
#inspect StandardSymmetricGroupBraidRelation
#inspect ThreeInductionCrossingMultipliers
#inspect MultipliersUnderRelabelling
