# Categorical prerequisites for bimodule string diagrams

All listed results compiled and passed the axiom audit.

[Article](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf) · [Alphabeta Math](https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf)

## Dependency overview

20 landmark definitions and results. Arrows follow dependency paths, with intermediate items omitted. [Full dependency graph](DEPENDENCIES.md) · [Exact proof graph and suppliers](proof-graph.json).

```mermaid
graph TD
  AdditiveFunctorsAndBiproducts["Addition and finite biproducts"]
  CancellationAndZeroKernels["Cancellation and zero kernels"]
  NormalMorphismsInAbelianCategories["Normal morphisms and cancellation<br/>in both directions"]
  ExactPresentationsAreCokernels["Presentations are cokernels"]
  ModuleKernelsCokernelsAndImages["Kernels, cokernels, and images"]
  FreeModulesAndPresentations["Free modules and presentations"]
  BimoduleTensorFunctoriality["Induced actions and functoriality"]
  RegularModuleTensorUnits["Tensoring with the regular module"]
  BalancedTensorAssociativity["Associativity with the correct<br/>sides"]
  TensorPreservesCokernels["Tensoring preserves cokernels"]
  GroupAlgebraInductionAdjunction["The induction bimodule"]
  GeneratorHomExactnessAndDetection["Exactness, detection, and<br/>coproducts"]
  GeneratorCokernelPresentations["Every object has a generator<br/>presentation"]
  GeneratorHomFullyFaithful["Morphisms are determined by<br/>module maps"]
  ReconstructionFromSmallProjectiveGenerator["Reconstruction from a small<br/>projective generator"]
  BimoduleFunctorHomEquivalence["The equivalence of Hom categories"]
  TensorDictionaryCompositionAndIdentities["The tensor dictionary preserves<br/>composition"]
  HorizontalCompositionOfTransformations["Composition of transformations"]
  AbelianEquivalencesPreserveFunctorHypotheses["Equivalences preserve the<br/>hypotheses on functors"]
  CategoricalBimoduleDictionary["The complete dictionary"]
  ExactPresentationsAreCokernels --> TensorPreservesCokernels
  ModuleKernelsCokernelsAndImages --> TensorPreservesCokernels
  BimoduleTensorFunctoriality --> GroupAlgebraInductionAdjunction
  CancellationAndZeroKernels --> GeneratorHomExactnessAndDetection
  NormalMorphismsInAbelianCategories --> GeneratorHomExactnessAndDetection
  NormalMorphismsInAbelianCategories --> GeneratorCokernelPresentations
  FreeModulesAndPresentations --> GeneratorHomFullyFaithful
  GeneratorHomExactnessAndDetection --> GeneratorHomFullyFaithful
  GeneratorCokernelPresentations --> GeneratorHomFullyFaithful
  GeneratorHomFullyFaithful --> ReconstructionFromSmallProjectiveGenerator
  RegularModuleTensorUnits --> TensorDictionaryCompositionAndIdentities
  TensorDictionaryCompositionAndIdentities --> HorizontalCompositionOfTransformations
  AdditiveFunctorsAndBiproducts --> AbelianEquivalencesPreserveFunctorHypotheses
  ReconstructionFromSmallProjectiveGenerator --> CategoricalBimoduleDictionary
  BimoduleFunctorHomEquivalence --> CategoricalBimoduleDictionary
  AbelianEquivalencesPreserveFunctorHypotheses --> CategoricalBimoduleDictionary
```

[Proof dependency graph](proof-graph.json) includes exact Lean suppliers and coverage.

## External proofs

The only external library used is [mathlib](https://github.com/leanprover-community/mathlib4); see the [full list of external proofs](EXTERNAL_PROOFS.md).

## Navigation and verification

- [PROJECT.md](PROJECT.md): statements, sources, translations and dependencies.
- [EXTERNAL_PROOFS.md](EXTERNAL_PROOFS.md): external proof ledger.
- NotesProofs/: Lean declarations and proofs.
- translations/: independently reviewed types and definition values.
- evidence/: reviews, compiler diagnostics and axiom audits.

Run `lake update`, `lake exe cache get`, then `lake build`. The workflow additionally checks each declaration's axioms, permitting only propext, Classical.choice and Quot.sound.
