import Lean
import Proofs.StandardTwoBlockRepresentatives
import Proofs.EqualTwoBlockSubgroups
import Proofs.MackeyConjugationExchangesFactors
import Proofs.ProductParabolicDoubleCosets
import Proofs.ProductParabolicsWithOneDoubleCoset
import Proofs.ProductParabolicsWithThreeDoubleCosets
import Proofs.TwoBlockSplitGivesFourIntersections
import Proofs.MackeyDecompositionWithParabolicRepresentatives
import Proofs.FiniteParabolicBicategoryComposition
import Proofs.FiniteParabolicBimoduleBicategory
import Proofs.FiniteParabolicJoinOfFamily
import Proofs.ParabolicCurlsFromBlockRefinements
import Proofs.ParabolicCurlFactorization
import Proofs.ParabolicCurlJoinIntersection
import Proofs.UnequalParabolicCurlProducts
import Proofs.LargestCommonMixedCrossingParabolic
import Proofs.ParabolicFullMackeyCancellation
import Proofs.ParabolicSmallerMackeyReverseComposite
import Proofs.LargestCommonParabolicDependsOnRepresentatives
import Proofs.ParabolicSharedRegionParallelInduction
import Proofs.ParabolicSharedRegionParallelRestriction
import Proofs.SharedParabolicForParallelCrossings
import Proofs.FiniteParabolicSingleDiagramReplacements
import Proofs.ParabolicExtremalThreeInductionRegions
import Proofs.ParabolicExtremalThreeInductionExample
import Proofs.ParabolicExtremalOutsideRestrictionRegions
import Proofs.ParabolicCaseTwoProjectionFiberIndices
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
#inspect StandardTwoBlockRepresentatives
#inspect EqualTwoBlockSubgroups
#inspect MackeyConjugationExchangesFactors
#inspect ProductParabolicDoubleCosets
#inspect ProductParabolicsWithOneDoubleCoset
#inspect ProductParabolicsWithThreeDoubleCosets
#inspect TwoBlockSplitGivesFourIntersections
#inspect MackeyDecompositionWithParabolicRepresentatives
#inspect FiniteParabolicBicategoryComposition
#inspect FiniteParabolicBimoduleBicategory
#inspect FiniteParabolicJoinOfFamily
#inspect ParabolicCurlsFromBlockRefinements
#inspect ParabolicCurlFactorization
#inspect ParabolicCurlJoinIntersection
#inspect UnequalParabolicCurlProducts
#inspect LargestCommonMixedCrossingParabolic
#inspect ParabolicFullMackeyCancellation
#inspect ParabolicSmallerMackeyReverseComposite
#inspect LargestCommonParabolicDependsOnRepresentatives
#inspect ParabolicSharedRegionParallelInduction
#inspect ParabolicSharedRegionParallelRestriction
#inspect SharedParabolicForParallelCrossings
#inspect FiniteParabolicSingleDiagramReplacements
#inspect ParabolicExtremalThreeInductionRegions
#inspect ParabolicExtremalThreeInductionExample
#inspect ParabolicExtremalOutsideRestrictionRegions
#inspect ParabolicCaseTwoProjectionFiberIndices
