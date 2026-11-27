import Lean
import NotesProofs.FiniteBiproductUniversalProperties
import NotesProofs.BiproductMatrixCalculus
import NotesProofs.AdditiveFunctorsAndBiproducts
import NotesProofs.CancellationAndZeroKernels
import NotesProofs.NormalMorphismsInAbelianCategories
import NotesProofs.ExactPresentationsAreCokernels
import NotesProofs.ModuleQuotientUniversalProperty
import NotesProofs.ModuleKernelsCokernelsAndImages
import NotesProofs.ModuleCategoriesAreAbelian
import NotesProofs.ModuleProductsAndCoproducts
import NotesProofs.FreeModulesAndPresentations
import NotesProofs.RegularModuleSmallProjectiveGenerator
import NotesProofs.BalancedTensorUniversalProperty
import NotesProofs.BimoduleTensorFunctoriality
import NotesProofs.RegularModuleTensorUnits
import NotesProofs.BalancedTensorAssociativity
import NotesProofs.TensorPreservesCoproducts
import NotesProofs.TensorPreservesCokernels
import NotesProofs.GroupAlgebraRingLaws
import NotesProofs.RepresentationModuleCorrespondence
import NotesProofs.GroupAlgebraInductionAdjunction
import NotesProofs.GeneratorHomExactnessAndDetection
import NotesProofs.GeneratorCokernelPresentations
import NotesProofs.GeneratorHomFullyFaithful
import NotesProofs.ReconstructionFromSmallProjectiveGenerator
import NotesProofs.RegularEvaluationRightAction
import NotesProofs.CanonicalWattsNaturalTransformation
import NotesProofs.EilenbergWatts
import NotesProofs.NaturalTransformationsByRegularEvaluation
import NotesProofs.BimoduleFunctorHomEquivalence
import NotesProofs.TensorDictionaryCompositionAndIdentities
import NotesProofs.TensorPentagonAndTriangle
import NotesProofs.HorizontalCompositionOfTransformations
import NotesProofs.AbelianEquivalencesPreserveFunctorHypotheses
import NotesProofs.CategoricalBimoduleDictionary

open Lean Elab Command

def homeModule (env : Environment) (n : Name) : Name :=
  (env.getModuleIdxFor? n).map (fun i => env.header.moduleNames[i.toNat]!) |>.getD .anonymous

partial def boundary (env : Environment) (home : Name) (todo : List Name)
    (seen : NameSet := {}) (out : NameSet := {}) (locals : NameSet := {}) :
    NameSet × NameSet :=
  match todo with
  | [] => (out, locals)
  | n :: ns =>
    if seen.contains n then boundary env home ns seen out locals
    else if homeModule env n == home then
      let next := (env.find? n).map (fun c => c.getUsedConstantsAsSet.toList) |>.getD []
      boundary env home (next ++ ns) (seen.insert n) out (locals.insert n)
    else boundary env home ns (seen.insert n) (out.insert n) locals

def row (env : Environment) (id tag : String) (n : Name) : String :=
  String.intercalate "\t" [id, tag, (homeModule env n).toString, n.toString]

run_cmd do
  let env ← getEnv
  let mut rows := #[]
  for id in ["FiniteBiproductUniversalProperties", "BiproductMatrixCalculus", "AdditiveFunctorsAndBiproducts", "CancellationAndZeroKernels", "NormalMorphismsInAbelianCategories", "ExactPresentationsAreCokernels", "ModuleQuotientUniversalProperty", "ModuleKernelsCokernelsAndImages", "ModuleCategoriesAreAbelian", "ModuleProductsAndCoproducts", "FreeModulesAndPresentations", "RegularModuleSmallProjectiveGenerator", "BalancedTensorUniversalProperty", "BimoduleTensorFunctoriality", "RegularModuleTensorUnits", "BalancedTensorAssociativity", "TensorPreservesCoproducts", "TensorPreservesCokernels", "GroupAlgebraRingLaws", "RepresentationModuleCorrespondence", "GroupAlgebraInductionAdjunction", "GeneratorHomExactnessAndDetection", "GeneratorCokernelPresentations", "GeneratorHomFullyFaithful", "ReconstructionFromSmallProjectiveGenerator", "RegularEvaluationRightAction", "CanonicalWattsNaturalTransformation", "EilenbergWatts", "NaturalTransformationsByRegularEvaluation", "BimoduleFunctorHomEquivalence", "TensorDictionaryCompositionAndIdentities", "TensorPentagonAndTriangle", "HorizontalCompositionOfTransformations", "AbelianEquivalencesPreserveFunctorHypotheses", "CategoricalBimoduleDictionary"] do
    let n := Name.mkSimple id
    let some info := env.find? n | throwError "missing {n}"
    let some val := info.value? (allowOpaque := true) | throwError "no value for {n}"
    let home := homeModule env n
    for c in info.type.getUsedConstants do
      rows := rows.push (row env id "statement" c)
    let (proof, locals) := boundary env home val.getUsedConstants.toList
    for c in proof.toList do
      rows := rows.push (row env id "proof" c)
    for c in locals.toList do
      rows := rows.push (row env id "local" c)
    let ax ← Lean.collectAxioms n
    for a in ax do
      rows := rows.push (row env id "axiom" a)
  IO.FS.writeFile "trace.tsv" (String.intercalate "\n" rows.toList ++ "\n")
