import Lean
import Proofs.MultipliersUnderRelabelling
import Proofs.ThreeInductionReidemeisterThree
import Proofs.ThreeInductionLabelsChangeOnRoundTrip
import Proofs.AlternativeThreeInductionInternalGroups
import Proofs.MixedCrossingFiniteFiberConvention
import Proofs.EvaluationForTwoProjections
import Proofs.CaseOneRightProjectionConstruction
import Proofs.CaseTwoLeftProjectionConstruction
import Proofs.ReplacementForTwoProjections
import Proofs.CaseOneNoFiniteRightReplacement
import Proofs.CaseTwoRequiresSum
import Proofs.ReplacementForTwoMultiplications
import Proofs.MixedMultiplicationLabelsChangeOnRoundTrip
import Proofs.CaseFiveLeftShapeEvaluation
import Proofs.CaseSixRightShapeEvaluation
import Proofs.EvaluationWithOneProjection
import Proofs.RightOrbitDiagramFromProjectedStabilizer
import Proofs.ExpansionIntoRightDiagrams
import Proofs.CaseFivePointwiseFiniteDiagramIdentity
import Proofs.CaseFiveRequiresTwoTerms
import Proofs.CaseFiveRequiresInfiniteExpansion
import Proofs.CaseSixProjectionNoLeftReplacement
import Proofs.ParabolicBlockOperationExample
import Proofs.ParabolicDoubleCosetRepresentatives
import Proofs.ParabolicMackeyIntersectionBlocks
import Proofs.TableauDoubleCosetRepresentativeInS6
import Proofs.OneSidedTableauCosetRepresentatives
import Proofs.TwoBlockDoubleCosetMatrices
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
#inspect MultipliersUnderRelabelling
#inspect ThreeInductionReidemeisterThree
#inspect ThreeInductionLabelsChangeOnRoundTrip
#inspect AlternativeThreeInductionInternalGroups
#inspect MixedCrossingFiniteFiberConvention
#inspect EvaluationForTwoProjections
#inspect CaseOneRightProjectionConstruction
#inspect CaseTwoLeftProjectionConstruction
#inspect ReplacementForTwoProjections
#inspect CaseOneNoFiniteRightReplacement
#inspect CaseTwoRequiresSum
#inspect ReplacementForTwoMultiplications
#inspect MixedMultiplicationLabelsChangeOnRoundTrip
#inspect CaseFiveLeftShapeEvaluation
#inspect CaseSixRightShapeEvaluation
#inspect EvaluationWithOneProjection
#inspect RightOrbitDiagramFromProjectedStabilizer
#inspect ExpansionIntoRightDiagrams
#inspect CaseFivePointwiseFiniteDiagramIdentity
#inspect CaseFiveRequiresTwoTerms
#inspect CaseFiveRequiresInfiniteExpansion
#inspect CaseSixProjectionNoLeftReplacement
#inspect ParabolicBlockOperationExample
#inspect ParabolicDoubleCosetRepresentatives
#inspect ParabolicMackeyIntersectionBlocks
#inspect TableauDoubleCosetRepresentativeInS6
#inspect OneSidedTableauCosetRepresentatives
#inspect TwoBlockDoubleCosetMatrices
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
