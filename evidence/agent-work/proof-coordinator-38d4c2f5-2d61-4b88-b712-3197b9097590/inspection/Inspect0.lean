import Lean
import Proofs.Bimodule
import Proofs.RegularModuleRightAction
import Proofs.CanonicalWattsComparison
import Proofs.NaturalTransformationsOfTensorFunctors
import Proofs.SmallProjectiveGenerator
import Proofs.ModuleTensorUniversalProperty
import Proofs.BalancedTensorAssociativity
import Proofs.BimoduleTensorBicategoryCoherence
import Proofs.EilenbergWatts
import Proofs.ComplexEilenbergWatts
import Proofs.SmallProjectiveGeneratorCorrespondence
import Proofs.ConjugationEmbeddingCentralizerCoset
import Proofs.InductionRestrictionBimoduleStrands
import Proofs.GroupElementDotCriterion
import Proofs.InductionRestrictionAdjunction
import Proofs.FiniteIndexReverseAdjunction
import Proofs.ReverseTriangleIdentities
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.DiagrammaticFunctorCorrespondence
import Proofs.SurvivingCosetRepresentative
import Proofs.MixedCrossingFiberMaps
import Proofs.MackeyInclusionAndProjectionCrossings
import Proofs.MackeyIdentityDiagram
import Proofs.MackeySummandProjection
import Proofs.MackeyOrthogonalityDiagram
import Proofs.GeneralizedMackeyDecomposition
import Proofs.OrdinaryMackeyDecomposition
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
#inspect Bimodule
#inspect RegularModuleRightAction
#inspect CanonicalWattsComparison
#inspect NaturalTransformationsOfTensorFunctors
#inspect SmallProjectiveGenerator
#inspect ModuleTensorUniversalProperty
#inspect BalancedTensorAssociativity
#inspect BimoduleTensorBicategoryCoherence
#inspect EilenbergWatts
#inspect ComplexEilenbergWatts
#inspect SmallProjectiveGeneratorCorrespondence
#inspect ConjugationEmbeddingCentralizerCoset
#inspect InductionRestrictionBimoduleStrands
#inspect GroupElementDotCriterion
#inspect InductionRestrictionAdjunction
#inspect FiniteIndexReverseAdjunction
#inspect ReverseTriangleIdentities
#inspect InductionRestrictionMergesAndSplits
#inspect DiagrammaticFunctorCorrespondence
#inspect SurvivingCosetRepresentative
#inspect MixedCrossingFiberMaps
#inspect MackeyInclusionAndProjectionCrossings
#inspect MackeyIdentityDiagram
#inspect MackeySummandProjection
#inspect MackeyOrthogonalityDiagram
#inspect GeneralizedMackeyDecomposition
#inspect OrdinaryMackeyDecomposition
