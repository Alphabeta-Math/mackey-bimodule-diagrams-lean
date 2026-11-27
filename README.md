# Bimodule String Diagrams and the Generalized Mackey Decomposition

All listed results compiled and passed the axiom audit.

[Article](https://getcurious.cc/downloads/mackey-bimodules.pdf) · [Alphabeta Math](https://getcurious.cc/articles/math-bimodule-string-diagrams)

## Dependency graph

```mermaid
graph TD
  Bimodule["Bimodule"]
  RegularModuleRightAction["RegularModuleRightAction"]
  Bimodule --> RegularModuleRightAction
  CanonicalWattsComparison["CanonicalWattsComparison"]
  RegularModuleRightAction --> CanonicalWattsComparison
  ModuleTensorUniversalProperty --> CanonicalWattsComparison
  NaturalTransformationsOfTensorFunctors["NaturalTransformationsOfTensorFunctors"]
  Bimodule --> NaturalTransformationsOfTensorFunctors
  SmallProjectiveGenerator["SmallProjectiveGenerator"]
  ModuleTensorUniversalProperty["ModuleTensorUniversalProperty"]
  BalancedTensorAssociativity["BalancedTensorAssociativity"]
  ModuleTensorUniversalProperty --> BalancedTensorAssociativity
  BimoduleTensorBicategoryCoherence["BimoduleTensorBicategoryCoherence"]
  Bimodule --> BimoduleTensorBicategoryCoherence
  EilenbergWatts["EilenbergWatts"]
  Bimodule --> EilenbergWatts
  ComplexEilenbergWatts["ComplexEilenbergWatts"]
  EilenbergWatts --> ComplexEilenbergWatts
  SmallProjectiveGeneratorCorrespondence["SmallProjectiveGeneratorCorrespondence"]
  ConjugationEmbeddingCentralizerCoset["ConjugationEmbeddingCentralizerCoset"]
  InductionRestrictionBimoduleStrands["InductionRestrictionBimoduleStrands"]
  ConjugationEmbeddingCentralizerCoset --> InductionRestrictionBimoduleStrands
  Bimodule --> InductionRestrictionBimoduleStrands
  GroupElementDotCriterion["GroupElementDotCriterion"]
  InductionRestrictionAdjunction["InductionRestrictionAdjunction"]
  InductionRestrictionBimoduleStrands --> InductionRestrictionAdjunction
  FiniteIndexReverseAdjunction["FiniteIndexReverseAdjunction"]
  ReverseTriangleIdentities["ReverseTriangleIdentities"]
  FiniteIndexReverseAdjunction --> ReverseTriangleIdentities
  InductionRestrictionMergesAndSplits["InductionRestrictionMergesAndSplits"]
  DiagrammaticFunctorCorrespondence["DiagrammaticFunctorCorrespondence"]
  ComplexEilenbergWatts --> DiagrammaticFunctorCorrespondence
  InductionRestrictionBimoduleStrands --> DiagrammaticFunctorCorrespondence
  SurvivingCosetRepresentative["SurvivingCosetRepresentative"]
  MixedCrossingFiberMaps["MixedCrossingFiberMaps"]
  MackeyInclusionAndProjectionCrossings["MackeyInclusionAndProjectionCrossings"]
  SurvivingCosetRepresentative --> MackeyInclusionAndProjectionCrossings
  MackeyIdentityDiagram["MackeyIdentityDiagram"]
  MackeySummandProjection["MackeySummandProjection"]
  MackeyInclusionAndProjectionCrossings --> MackeySummandProjection
  SurvivingCosetRepresentative --> MackeySummandProjection
  MackeyOrthogonalityDiagram["MackeyOrthogonalityDiagram"]
  MackeyInclusionAndProjectionCrossings --> MackeyOrthogonalityDiagram
  MackeyIdentityDiagram --> MackeyOrthogonalityDiagram
  SurvivingCosetRepresentative --> MackeyOrthogonalityDiagram
  GeneralizedMackeyDecomposition["GeneralizedMackeyDecomposition"]
  MackeyIdentityDiagram --> GeneralizedMackeyDecomposition
  InductionRestrictionAdjunction --> GeneralizedMackeyDecomposition
  OrdinaryMackeyDecomposition["OrdinaryMackeyDecomposition"]
  GeneralizedMackeyDecomposition --> OrdinaryMackeyDecomposition
  RightUpReidemeisterCurl["RightUpReidemeisterCurl"]
  RightCurlAndDotSlide["RightCurlAndDotSlide"]
  RightUpReidemeisterCurl --> RightCurlAndDotSlide
  InductionMergeDotSlide --> RightCurlAndDotSlide
  InductionSplitDotSlide --> RightCurlAndDotSlide
  RestrictionMergeDotSlide --> RightCurlAndDotSlide
  RestrictionSplitDotSlide --> RightCurlAndDotSlide
  InductionMergeDotSlide["InductionMergeDotSlide"]
  InductionSplitDotSlide["InductionSplitDotSlide"]
  InductionMergeDotSlide --> InductionSplitDotSlide
  RestrictionMergeDotSlide["RestrictionMergeDotSlide"]
  RestrictionSplitDotSlide["RestrictionSplitDotSlide"]
  InductionRestrictionMergesAndSplits --> RestrictionSplitDotSlide
  RestrictionMergeDotSlide --> RestrictionSplitDotSlide
  DotBelowInsideAboveRightCurl["DotBelowInsideAboveRightCurl"]
  RightCurlAndDotSlide --> DotBelowInsideAboveRightCurl
  CurlWithCentralizingDot["CurlWithCentralizingDot"]
  FiniteIndexReverseAdjunction --> CurlWithCentralizingDot
  RightCurlAndDotSlide --> CurlWithCentralizingDot
  MovingMergeDotBackToBranch["MovingMergeDotBackToBranch"]
  InductionMergeDotSlide --> MovingMergeDotBackToBranch
  RestrictionMergeDotSlide --> MovingMergeDotBackToBranch
  MovingSplitDotToOutputBranch["MovingSplitDotToOutputBranch"]
  InductionSplitDotSlide --> MovingSplitDotToOutputBranch
  RestrictionSplitDotSlide --> MovingSplitDotToOutputBranch
  CurlAcrossTrivalentVertex["CurlAcrossTrivalentVertex"]
  RightUpReidemeisterCurl --> CurlAcrossTrivalentVertex
  DifferentCurlIndices["DifferentCurlIndices"]
  CurlAcrossTrivalentVertex --> DifferentCurlIndices
  LeftDownReidemeisterCurl["LeftDownReidemeisterCurl"]
  InductionRestrictionMergesAndSplits --> LeftDownReidemeisterCurl
  NormalizedIndexValuedReidemeisterCurls["NormalizedIndexValuedReidemeisterCurls"]
  RightUpReidemeisterCurl --> NormalizedIndexValuedReidemeisterCurls
  LeftDownReidemeisterCurl --> NormalizedIndexValuedReidemeisterCurls
  NormalizedTrivalentCurl["NormalizedTrivalentCurl"]
  NormalizedIndexValuedReidemeisterCurls --> NormalizedTrivalentCurl
  FixedBoundaryReplacementPreorder["FixedBoundaryReplacementPreorder"]
  RightInputDotSlideObstruction["RightInputDotSlideObstruction"]
  DotSlidePreorderNotSymmetric["DotSlidePreorderNotSymmetric"]
  RightInputDotSlideObstruction --> DotSlidePreorderNotSymmetric
  InductionBimoduleOrbitSumBasis["InductionBimoduleOrbitSumBasis"]
  InductionRestrictionBimoduleStrands --> InductionBimoduleOrbitSumBasis
  GroupElementDotCriterion --> InductionBimoduleOrbitSumBasis
  FiniteOrbitSumDiagram["FiniteOrbitSumDiagram"]
  FiniteIndexReverseAdjunction --> FiniteOrbitSumDiagram
  InductionBimoduleOrbitSumBasis --> FiniteOrbitSumDiagram
  FiniteParabolicConjugateBlocks["FiniteParabolicConjugateBlocks"]
  FiniteParabolicIntersectionBlocks["FiniteParabolicIntersectionBlocks"]
  FiniteParabolicJoinBlocks["FiniteParabolicJoinBlocks"]
  FiniteParabolicClosure["FiniteParabolicClosure"]
  FiniteParabolicConjugateBlocks --> FiniteParabolicClosure
  FiniteParabolicIntersectionBlocks --> FiniteParabolicClosure
  FiniteParabolicJoinBlocks --> FiniteParabolicClosure
  ExtremalParabolicsOfFiniteGroup["ExtremalParabolicsOfFiniteGroup"]
  FiniteParabolicClosure --> ExtremalParabolicsOfFiniteGroup
  BlockwiseGroupElementDotCriterion["BlockwiseGroupElementDotCriterion"]
  GroupElementDotCriterion --> BlockwiseGroupElementDotCriterion
  BlockSwapOrbitSumWithoutGroupDot["BlockSwapOrbitSumWithoutGroupDot"]
  FiniteOrbitSumDiagram --> BlockSwapOrbitSumWithoutGroupDot
  DotBetweenImagesInOneBlock["DotBetweenImagesInOneBlock"]
  StrongerEmbeddingConditionSlideObstruction["StrongerEmbeddingConditionSlideObstruction"]
  BlockwiseGroupElementDotCriterion --> StrongerEmbeddingConditionSlideObstruction
  SupportBoundsUnderComposition["SupportBoundsUnderComposition"]
  FiniteParabolicConjugateBlocks --> SupportBoundsUnderComposition
  SupportBoundsForInverseProduct["SupportBoundsForInverseProduct"]
  MultiplicationCapBend["MultiplicationCapBend"]
  TraceCapBend["TraceCapBend"]
  FiniteIndexReverseAdjunction --> TraceCapBend
  OrdinaryCupBend["OrdinaryCupBend"]
  ReverseCupBend["ReverseCupBend"]
  FiniteIndexReverseAdjunction --> ReverseCupBend
  TrivalentBendIdentities["TrivalentBendIdentities"]
  MultiplicationCapBend --> TrivalentBendIdentities
  TraceCapBend --> TrivalentBendIdentities
  OrdinaryCupBend --> TrivalentBendIdentities
  ReverseCupBend --> TrivalentBendIdentities
  StraightMixedTrivalentVertices["StraightMixedTrivalentVertices"]
  TrivalentBendIdentities --> StraightMixedTrivalentVertices
  RightDownReidemeisterCurl["RightDownReidemeisterCurl"]
  LeftUpReidemeisterCurl["LeftUpReidemeisterCurl"]
  ReidemeisterOne["ReidemeisterOne"]
  RightUpReidemeisterCurl --> ReidemeisterOne
  RightDownReidemeisterCurl --> ReidemeisterOne
  LeftUpReidemeisterCurl --> ReidemeisterOne
  LeftDownReidemeisterCurl --> ReidemeisterOne
  TransportToMackeyRepresentative["TransportToMackeyRepresentative"]
  MixedCrossingComposites["MixedCrossingComposites"]
  MixedCrossingFiberMaps --> MixedCrossingComposites
  MixedReidemeisterTwoMackeyCancellation["MixedReidemeisterTwoMackeyCancellation"]
  GeneralizedMackeyDecomposition --> MixedReidemeisterTwoMackeyCancellation
  MackeyIdentityDiagram --> MixedReidemeisterTwoMackeyCancellation
  MixedCrossingsThroughSmallerGroup["MixedCrossingsThroughSmallerGroup"]
  MixedCrossingFiberMaps --> MixedCrossingsThroughSmallerGroup
  CommonMackeyIntersectionSum["CommonMackeyIntersectionSum"]
  MixedCrossingsThroughSmallerGroup --> CommonMackeyIntersectionSum
  TwoMackeySummandsWithSameInternalLabels["TwoMackeySummandsWithSameInternalLabels"]
  CommonMackeyIntersectionSum --> TwoMackeySummandsWithSameInternalLabels
  MackeyIdentityDiagram --> TwoMackeySummandsWithSameInternalLabels
  SinglePairCannotProjectOntoSeveralDoubleCosets["SinglePairCannotProjectOntoSeveralDoubleCosets"]
  SinglePairIdentityCriterion["SinglePairIdentityCriterion"]
  MixedReidemeisterTwoMackeyCancellation --> SinglePairIdentityCriterion
  MixedCrossingFiberMaps --> SinglePairIdentityCriterion
  ParallelInductionProductDotAdmissibility["ParallelInductionProductDotAdmissibility"]
  ParallelReidemeisterTwoInduction["ParallelReidemeisterTwoInduction"]
  InductionRestrictionMergesAndSplits --> ParallelReidemeisterTwoInduction
  ParallelInductionProductDotAdmissibility --> ParallelReidemeisterTwoInduction
  ParallelReidemeisterTwoRestriction["ParallelReidemeisterTwoRestriction"]
  StandardSymmetricGroupBraidRelation["StandardSymmetricGroupBraidRelation"]
  ThreeInductionCrossingMultipliers["ThreeInductionCrossingMultipliers"]
  GroupElementDotCriterion --> ThreeInductionCrossingMultipliers
  InductionRestrictionMergesAndSplits --> ThreeInductionCrossingMultipliers
  MultipliersUnderRelabelling["MultipliersUnderRelabelling"]
  ThreeInductionCrossingMultipliers --> MultipliersUnderRelabelling
  ThreeInductionReidemeisterThree["ThreeInductionReidemeisterThree"]
  MultipliersUnderRelabelling --> ThreeInductionReidemeisterThree
  ThreeInductionCrossingMultipliers --> ThreeInductionReidemeisterThree
  ThreeInductionLabelsChangeOnRoundTrip["ThreeInductionLabelsChangeOnRoundTrip"]
  AlternativeThreeInductionInternalGroups["AlternativeThreeInductionInternalGroups"]
  ThreeInductionCrossingMultipliers --> AlternativeThreeInductionInternalGroups
  MixedCrossingFiniteFiberConvention["MixedCrossingFiniteFiberConvention"]
  MixedCrossingFiberMaps --> MixedCrossingFiniteFiberConvention
  EvaluationForTwoProjections["EvaluationForTwoProjections"]
  MixedCrossingFiniteFiberConvention --> EvaluationForTwoProjections
  MixedCrossingFiberMaps --> EvaluationForTwoProjections
  CaseOneRightProjectionConstruction["CaseOneRightProjectionConstruction"]
  EvaluationForTwoProjections --> CaseOneRightProjectionConstruction
  CaseTwoLeftProjectionConstruction["CaseTwoLeftProjectionConstruction"]
  EvaluationForTwoProjections --> CaseTwoLeftProjectionConstruction
  ReplacementForTwoProjections["ReplacementForTwoProjections"]
  CaseOneRightProjectionConstruction --> ReplacementForTwoProjections
  CaseTwoLeftProjectionConstruction --> ReplacementForTwoProjections
  CaseOneNoFiniteRightReplacement["CaseOneNoFiniteRightReplacement"]
  EvaluationForTwoProjections --> CaseOneNoFiniteRightReplacement
  CaseTwoRequiresSum["CaseTwoRequiresSum"]
  CaseTwoLeftProjectionConstruction --> CaseTwoRequiresSum
  ReplacementForTwoMultiplications["ReplacementForTwoMultiplications"]
  MixedCrossingFiniteFiberConvention --> ReplacementForTwoMultiplications
  MixedMultiplicationLabelsChangeOnRoundTrip["MixedMultiplicationLabelsChangeOnRoundTrip"]
  CaseFiveLeftShapeEvaluation["CaseFiveLeftShapeEvaluation"]
  MixedCrossingFiniteFiberConvention --> CaseFiveLeftShapeEvaluation
  CaseSixRightShapeEvaluation["CaseSixRightShapeEvaluation"]
  EvaluationWithOneProjection["EvaluationWithOneProjection"]
  CaseFiveLeftShapeEvaluation --> EvaluationWithOneProjection
  CaseSixRightShapeEvaluation --> EvaluationWithOneProjection
  RightOrbitDiagramFromProjectedStabilizer["RightOrbitDiagramFromProjectedStabilizer"]
  CaseSixRightShapeEvaluation --> RightOrbitDiagramFromProjectedStabilizer
  ExpansionIntoRightDiagrams["ExpansionIntoRightDiagrams"]
  RightOrbitDiagramFromProjectedStabilizer --> ExpansionIntoRightDiagrams
  CaseFivePointwiseFiniteDiagramIdentity["CaseFivePointwiseFiniteDiagramIdentity"]
  ExpansionIntoRightDiagrams --> CaseFivePointwiseFiniteDiagramIdentity
  RightOrbitDiagramFromProjectedStabilizer --> CaseFivePointwiseFiniteDiagramIdentity
  CaseFiveRequiresTwoTerms["CaseFiveRequiresTwoTerms"]
  EvaluationWithOneProjection --> CaseFiveRequiresTwoTerms
  CaseFiveRequiresInfiniteExpansion["CaseFiveRequiresInfiniteExpansion"]
  EvaluationWithOneProjection --> CaseFiveRequiresInfiniteExpansion
  CaseSixProjectionNoLeftReplacement["CaseSixProjectionNoLeftReplacement"]
  EvaluationWithOneProjection --> CaseSixProjectionNoLeftReplacement
  ParabolicBlockOperationExample["ParabolicBlockOperationExample"]
  FiniteParabolicConjugateBlocks --> ParabolicBlockOperationExample
  FiniteParabolicIntersectionBlocks --> ParabolicBlockOperationExample
  FiniteParabolicJoinBlocks --> ParabolicBlockOperationExample
  ParabolicDoubleCosetRepresentatives["ParabolicDoubleCosetRepresentatives"]
  ParabolicMackeyIntersectionBlocks["ParabolicMackeyIntersectionBlocks"]
  FiniteParabolicConjugateBlocks --> ParabolicMackeyIntersectionBlocks
  FiniteParabolicIntersectionBlocks --> ParabolicMackeyIntersectionBlocks
  TableauDoubleCosetRepresentativeInS6["TableauDoubleCosetRepresentativeInS6"]
  ParabolicDoubleCosetRepresentatives --> TableauDoubleCosetRepresentativeInS6
  ParabolicMackeyIntersectionBlocks --> TableauDoubleCosetRepresentativeInS6
  OneSidedTableauCosetRepresentatives["OneSidedTableauCosetRepresentatives"]
  ParabolicDoubleCosetRepresentatives --> OneSidedTableauCosetRepresentatives
  TwoBlockDoubleCosetMatrices["TwoBlockDoubleCosetMatrices"]
  ParabolicDoubleCosetRepresentatives --> TwoBlockDoubleCosetMatrices
  StandardTwoBlockRepresentatives["StandardTwoBlockRepresentatives"]
  ParabolicMackeyIntersectionBlocks --> StandardTwoBlockRepresentatives
  TwoBlockDoubleCosetMatrices --> StandardTwoBlockRepresentatives
  ParabolicDoubleCosetRepresentatives --> StandardTwoBlockRepresentatives
  EqualTwoBlockSubgroups["EqualTwoBlockSubgroups"]
  StandardTwoBlockRepresentatives --> EqualTwoBlockSubgroups
  MackeyConjugationExchangesFactors["MackeyConjugationExchangesFactors"]
  EqualTwoBlockSubgroups --> MackeyConjugationExchangesFactors
  ProductParabolicDoubleCosets["ProductParabolicDoubleCosets"]
  ParabolicDoubleCosetRepresentatives --> ProductParabolicDoubleCosets
  ProductParabolicsWithOneDoubleCoset["ProductParabolicsWithOneDoubleCoset"]
  ProductParabolicsWithThreeDoubleCosets["ProductParabolicsWithThreeDoubleCosets"]
  StandardTwoBlockRepresentatives --> ProductParabolicsWithThreeDoubleCosets
  TwoBlockSplitGivesFourIntersections["TwoBlockSplitGivesFourIntersections"]
  StandardTwoBlockRepresentatives --> TwoBlockSplitGivesFourIntersections
  MackeyDecompositionWithParabolicRepresentatives["MackeyDecompositionWithParabolicRepresentatives"]
  GeneralizedMackeyDecomposition --> MackeyDecompositionWithParabolicRepresentatives
  FiniteParabolicConjugateBlocks --> MackeyDecompositionWithParabolicRepresentatives
  ProductParabolicDoubleCosets --> MackeyDecompositionWithParabolicRepresentatives
  FiniteParabolicBicategoryComposition["FiniteParabolicBicategoryComposition"]
  MackeyDecompositionWithParabolicRepresentatives --> FiniteParabolicBicategoryComposition
  FiniteParabolicBimoduleBicategory["FiniteParabolicBimoduleBicategory"]
  FiniteParabolicBicategoryComposition --> FiniteParabolicBimoduleBicategory
  FiniteParabolicJoinOfFamily["FiniteParabolicJoinOfFamily"]
  FiniteParabolicJoinBlocks --> FiniteParabolicJoinOfFamily
  ParabolicCurlsFromBlockRefinements["ParabolicCurlsFromBlockRefinements"]
  ReidemeisterOne --> ParabolicCurlsFromBlockRefinements
  ParabolicCurlFactorization["ParabolicCurlFactorization"]
  ParabolicCurlsFromBlockRefinements --> ParabolicCurlFactorization
  ParabolicCurlJoinIntersection["ParabolicCurlJoinIntersection"]
  UnequalParabolicCurlProducts["UnequalParabolicCurlProducts"]
  ParabolicCurlJoinIntersection --> UnequalParabolicCurlProducts
  LargestCommonMixedCrossingParabolic["LargestCommonMixedCrossingParabolic"]
  CommonMackeyIntersectionSum --> LargestCommonMixedCrossingParabolic
  ExtremalParabolicsOfFiniteGroup --> LargestCommonMixedCrossingParabolic
  MackeyInclusionAndProjectionCrossings --> LargestCommonMixedCrossingParabolic
  ParabolicFullMackeyCancellation["ParabolicFullMackeyCancellation"]
  MixedReidemeisterTwoMackeyCancellation --> ParabolicFullMackeyCancellation
  ParabolicSmallerMackeyReverseComposite["ParabolicSmallerMackeyReverseComposite"]
  MixedCrossingsThroughSmallerGroup --> ParabolicSmallerMackeyReverseComposite
  LargestCommonParabolicDependsOnRepresentatives["LargestCommonParabolicDependsOnRepresentatives"]
  LargestCommonMixedCrossingParabolic --> LargestCommonParabolicDependsOnRepresentatives
  MackeyIdentityDiagram --> LargestCommonParabolicDependsOnRepresentatives
  ParabolicSharedRegionParallelInduction["ParabolicSharedRegionParallelInduction"]
  ParallelReidemeisterTwoInduction --> ParabolicSharedRegionParallelInduction
  ParabolicSharedRegionParallelRestriction["ParabolicSharedRegionParallelRestriction"]
  ParallelReidemeisterTwoRestriction --> ParabolicSharedRegionParallelRestriction
  SharedParabolicForParallelCrossings["SharedParabolicForParallelCrossings"]
  ParabolicSharedRegionParallelInduction --> SharedParabolicForParallelCrossings
  ParabolicSharedRegionParallelRestriction --> SharedParabolicForParallelCrossings
  FiniteParabolicSingleDiagramReplacements["FiniteParabolicSingleDiagramReplacements"]
  ReplacementForTwoProjections --> FiniteParabolicSingleDiagramReplacements
  ReplacementForTwoMultiplications --> FiniteParabolicSingleDiagramReplacements
  ParabolicExtremalThreeInductionRegions["ParabolicExtremalThreeInductionRegions"]
  ThreeInductionCrossingMultipliers --> ParabolicExtremalThreeInductionRegions
  FiniteParabolicIntersectionBlocks --> ParabolicExtremalThreeInductionRegions
  FiniteParabolicJoinBlocks --> ParabolicExtremalThreeInductionRegions
  ParabolicExtremalThreeInductionExample["ParabolicExtremalThreeInductionExample"]
  ParabolicExtremalThreeInductionRegions --> ParabolicExtremalThreeInductionExample
  ParabolicExtremalOutsideRestrictionRegions["ParabolicExtremalOutsideRestrictionRegions"]
  FiniteParabolicIntersectionBlocks --> ParabolicExtremalOutsideRestrictionRegions
  FiniteParabolicJoinBlocks --> ParabolicExtremalOutsideRestrictionRegions
  CaseOneRightProjectionConstruction --> ParabolicExtremalOutsideRestrictionRegions
  ParabolicCaseTwoProjectionFiberIndices["ParabolicCaseTwoProjectionFiberIndices"]
  EvaluationForTwoProjections --> ParabolicCaseTwoProjectionFiberIndices
  ParabolicExtremalOutsideRestrictionRegions --> ParabolicCaseTwoProjectionFiberIndices
  ParabolicOutsideProjectionDiagram["ParabolicOutsideProjectionDiagram"]
  ParabolicExtremalOutsideRestrictionRegions --> ParabolicOutsideProjectionDiagram
  ParabolicCaseTwoProjectionFiberIndices --> ParabolicOutsideProjectionDiagram
  ParabolicOutsideMultiplicationDiagram["ParabolicOutsideMultiplicationDiagram"]
  ParabolicExtremalOutsideRestrictionRegions --> ParabolicOutsideMultiplicationDiagram
  ReplacementForTwoMultiplications --> ParabolicOutsideMultiplicationDiagram
  SmallerParabolicReducesProjectionFiber["SmallerParabolicReducesProjectionFiber"]
  ParabolicExtremalOutsideRestrictionRegions --> SmallerParabolicReducesProjectionFiber
  ParabolicCaseTwoProjectionFiberIndices --> SmallerParabolicReducesProjectionFiber
  ParabolicCommonRightRegionForLinearLabels["ParabolicCommonRightRegionForLinearLabels"]
  ExtremalParabolicsOfFiniteGroup --> ParabolicCommonRightRegionForLinearLabels
  FiniteParabolicClosure --> ParabolicCommonRightRegionForLinearLabels
  SupportedLeftOrbitProjectedStabilizer["SupportedLeftOrbitProjectedStabilizer"]
  CaseFiveLeftShapeEvaluation --> SupportedLeftOrbitProjectedStabilizer
  RightOrbitDiagramFromProjectedStabilizer --> SupportedLeftOrbitProjectedStabilizer
  FiniteParabolicConjugateBlocks --> SupportedLeftOrbitProjectedStabilizer
  FiniteParabolicIntersectionBlocks --> SupportedLeftOrbitProjectedStabilizer
  ParabolicRightOrbitMultiplicity["ParabolicRightOrbitMultiplicity"]
  CaseSixRightShapeEvaluation --> ParabolicRightOrbitMultiplicity
  RightOrbitDiagramFromProjectedStabilizer --> ParabolicRightOrbitMultiplicity
  ExtremalParabolicsOfFiniteGroup --> ParabolicRightOrbitMultiplicity
  FiniteParabolicClosure --> ParabolicRightOrbitMultiplicity
  SupportedLeftOrbitProjectedStabilizer --> ParabolicRightOrbitMultiplicity
  ParabolicCaseFiveCoefficientOneExpansion["ParabolicCaseFiveCoefficientOneExpansion"]
  ParabolicRightOrbitMultiplicity --> ParabolicCaseFiveCoefficientOneExpansion
  ParabolicRightDiagramSpanOverCommutativeRings["ParabolicRightDiagramSpanOverCommutativeRings"]
  ParabolicCaseFiveCoefficientOneExpansion --> ParabolicRightDiagramSpanOverCommutativeRings
  ParabolicRightOrbitMultiplicity --> ParabolicRightDiagramSpanOverCommutativeRings
  ParabolicCaseFiveUnscaledDiagramIdentity["ParabolicCaseFiveUnscaledDiagramIdentity"]
  ParabolicCaseFiveCoefficientOneExpansion --> ParabolicCaseFiveUnscaledDiagramIdentity
  ParabolicCaseSixStrictStabilizerObstruction["ParabolicCaseSixStrictStabilizerObstruction"]
  SupportedLeftOrbitProjectedStabilizer --> ParabolicCaseSixStrictStabilizerObstruction
  ParabolicCaseSixReplacementThroughJoin["ParabolicCaseSixReplacementThroughJoin"]
  EvaluationWithOneProjection --> ParabolicCaseSixReplacementThroughJoin
  FiniteParabolicJoinOfFamily --> ParabolicCaseSixReplacementThroughJoin
  ParabolicCaseSixObstructionAndReplacementFamily["ParabolicCaseSixObstructionAndReplacementFamily"]
  ParabolicCaseSixStrictStabilizerObstruction --> ParabolicCaseSixObstructionAndReplacementFamily
  ParabolicCaseSixReplacementThroughJoin --> ParabolicCaseSixObstructionAndReplacementFamily
  ParabolicCaseSixOrbitCoefficientVanishesInCharacteristicThree["ParabolicCaseSixOrbitCoefficientVanishesInCharacteristicThree"]
  ParabolicRightOrbitMultiplicity --> ParabolicCaseSixOrbitCoefficientVanishesInCharacteristicThree
  CaseSixCounterexampleWithTrivialProjectedStabilizers["CaseSixCounterexampleWithTrivialProjectedStabilizers"]
  EvaluationWithOneProjection --> CaseSixCounterexampleWithTrivialProjectedStabilizers
  FiniteParabolicConjugateBlocks --> CaseSixCounterexampleWithTrivialProjectedStabilizers
  ParabolicCaseSixObstructionWithTrivialProjectedStabilizer["ParabolicCaseSixObstructionWithTrivialProjectedStabilizer"]
  CaseSixCounterexampleWithTrivialProjectedStabilizers --> ParabolicCaseSixObstructionWithTrivialProjectedStabilizer
  CaseSixReplacementThroughOverlappingBlocks["CaseSixReplacementThroughOverlappingBlocks"]
  EvaluationWithOneProjection --> CaseSixReplacementThroughOverlappingBlocks
```

[Proof dependency graph](proof-graph.json) includes exact Lean suppliers and coverage.

## External proofs

Base library: [mathlib](https://github.com/leanprover-community/mathlib4/tree/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9), commit 65d730f7150f21fdfa32f3e73a3f549c1f96a0e9 (Apache-2.0).

- **MathlibRegularCentralizer**: [Subgroup.mem_centralizer_iff](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Subgroup/Centralizer.lean#L35-L36);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct in the existing ofConjugator_eq_iff proof, converts subgroup membership into commutation with each member of H.

Import Mathlib.GroupTheory.Subgroup.Centralizer. Checked Lean signature:
Subgroup.mem_centralizer_iff.{u_1} {G : Type u_1} [Group G] {g : G} {s : Set G} :
  g ∈ Subgroup.centralizer s ↔ ∀ h ∈ s, h * g = g * h
MixedCrossingFiniteFiberConvention applies Subgroup.mem_centralizer_iff to p⁻¹ * q in the ambient group to identify the set of representatives of the given boundary embedding.
  Used by: ConjugationEmbeddingCentralizerCoset, MixedCrossingFiniteFiberConvention.
- **MathlibRepModuleEquivalence**: [Rep.equivalenceModuleMonoidAlgebra; Rep.counitIso](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/RepresentationTheory/Rep/Iso.lean#L157-L161);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Adapt the categorical adjunctions by this equivalence for group algebras. This is for a commutative coefficient ring and an arbitrary monoid, with group specialization. Prove the identification with the appropriate project bimodules on their generators.

Import Mathlib.RepresentationTheory.Rep.Iso. Checked Lean signature:
Rep.equivalenceModuleMonoidAlgebra.{w, u, v} {k : Type u} {G : Type v} [CommRing k] [Monoid G] :
  Rep.{w, u, v} k G ≌ ModuleCat (MonoidAlgebra k G)
For InductionRestrictionBimoduleStrands, use the source and target equivalences to transport Rep.indResAdjunction. Check the resulting right adjoint against restriction along the induced group-algebra map by the identity on carriers, extending the equality of actions on group generators.
Transport the representation adjunction across the equivalences for H and G. The identity on each carrier then compares transported restriction with restriction of scalars, by checking the group action on singletons.
Used in adjunction to transport restriction and reverse induction from Rep to ModuleCat for each group algebra. restrictionIso checks scalar restriction for the given conjugation embedding on group generators. unit_sum checks both resulting source comparison maps on the coefficient of each induction generator.
Carry the natural coproduct decomposition from complex representations to complex group-algebra modules by pre- and postcomposition.
The equivalence instance gives preservation of the representation coproduct under postcomposition. Its counit identifies the module of the regular representation with the reviewed regular module, acting by the identity on the carrier.
  Used by: InductionRestrictionBimoduleStrands, InductionRestrictionAdjunction, FiniteIndexReverseAdjunction, GeneralizedMackeyDecomposition, OrdinaryMackeyDecomposition.
- **MathlibIndResAdjunction**: [Rep.indResAdjunction](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/RepresentationTheory/Induced.lean#L154-L160);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct at the representation level for any group homomorphism and commutative coefficient ring. Apply to the underlying conjugation hom and identify the actual typed ordinary cup and multiplication cap with unit and counit.

Import Mathlib.RepresentationTheory.Induced. Checked Lean signature:
Rep.indResAdjunction.{w, u, v, v'} (k : Type u) {G : Type v} {H : Type v'} [CommRing k] [Group G] [Group H]
  (φ : G →* H) : Rep.indFunctor k φ ⊣ Rep.resFunctor φ
For InductionRestrictionBimoduleStrands, apply the adjunction to the underlying conjugation homomorphism and transfer it to module categories. The unit at 1 gives the natural pure tensor map, and the Hom equivalence gives the unique exterior-linear lift.
Apply the categorical adjunction at the underlying conjugation homomorphism with complex coefficients and arbitrary index. Its unit on the identity-index generator follows from the definition through Rep.indResHomEquiv. Representation.ind_mk computes the action on generators and accounts for the inverse group index in the reviewed pure tensor.
Compare representation restriction with restriction of scalars by right-adjoint uniqueness, using the project's InductionRestrictionAdjunction for the same left adjoint.
  Used by: InductionRestrictionBimoduleStrands, InductionRestrictionAdjunction, GeneralizedMackeyDecomposition.
- **MathlibResIndAdjunction**: [Rep.resIndAdjunction](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/RepresentationTheory/FiniteIndex.lean#L198-L200);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Adapt from a subgroup inclusion S.subtype along the isomorphism of the embedded source with its image S. Requires S.FiniteIndex and a decidable right-coset relation, supplied classically. Use only for standalone finite-index adjunction, with separate identification of trace and reverse cup.

Import Mathlib.RepresentationTheory.FiniteIndex. Checked Lean signature:
Rep.resIndAdjunction.{w, u, v} (k : Type u) {G : Type v} [CommRing k] [Group G] (S : Subgroup G)
  [DecidableRel ⇑(QuotientGroup.rightRel S)] [S.FiniteIndex] : Rep.resFunctor S.subtype ⊣ Rep.indFunctor k S.subtype
  Used by: FiniteIndexReverseAdjunction.
- **MathlibResIndCounit**: [Rep.resIndAdjunction_counit_app](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/RepresentationTheory/FiniteIndex.lean#L211-L214);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Adapt the representation-level formula after passing to the image subgroup. Together with the coinduced counit evaluated at 1, it provides the trace calculation on group generators under the same finite-index restriction.

Import Mathlib.RepresentationTheory.FiniteIndex. Checked Lean signature:
Rep.resIndAdjunction_counit_app.{w, u, v} {k : Type u} {G : Type v} [CommRing k] [Group G] {S : Subgroup G}
  [DecidableRel ⇑(QuotientGroup.rightRel S)] [S.FiniteIndex] (A : Rep.{max w u v, u, v} k ↥S) :
  (Rep.resIndAdjunction k S).counit.app A =
    CategoryTheory.CategoryStruct.comp ((Rep.resFunctor S.subtype).map A.indCoindIso.hom)
      ((Rep.resCoindAdjunction k S.subtype).counit.app A)
  Used by: FiniteIndexReverseAdjunction.
- **MathlibResIndUnit**: [Rep.resIndAdjunction_unit_app](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/RepresentationTheory/FiniteIndex.lean#L217-L220);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Adapt the representation-level unit by the finite-index coinduction-to-induction comparison. Match the resulting coset sum with evaluation of the typed reverse cup after passing to the image subgroup.

Import Mathlib.RepresentationTheory.FiniteIndex. Checked Lean signature:
Rep.resIndAdjunction_unit_app.{w, u, v} {k : Type u} {G : Type v} [CommRing k] [Group G] {S : Subgroup G}
  [DecidableRel ⇑(QuotientGroup.rightRel S)] [S.FiniteIndex] (B : Rep.{max w u v, u, v} k G) :
  (Rep.resIndAdjunction k S).unit.app B =
    CategoryTheory.CategoryStruct.comp ((Rep.resCoindAdjunction k S.subtype).unit.app B)
      (Rep.res S.subtype B).indCoindIso.inv
  Used by: FiniteIndexReverseAdjunction.
- **MathlibAdjLeftTriangle**: [CategoryTheory.Adjunction.left_triangle_components](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/CategoryTheory/Adjunction/Basic.lean#L114-L116);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Use for the left triangle once unit and counit are identified with the project generators and associators and unitors are inserted.

Import Mathlib.CategoryTheory.Adjunction.Basic. Checked Lean signature:
CategoryTheory.Adjunction.left_triangle_components.{v₁, v₂, u₁, u₂} {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C]
  {D : Type u₂} [CategoryTheory.Category.{v₂, u₂} D] {F : CategoryTheory.Functor C D} {G : CategoryTheory.Functor D C}
  (self : F ⊣ G) (X : C) :
  CategoryTheory.CategoryStruct.comp (F.map (self.unit.app X)) (self.counit.app (F.obj X)) =
    CategoryTheory.CategoryStruct.id (F.obj X)
Use adj.left_triangle_components for the restriction functor at each complex G-module. FiniteIndexReverseAdjunction identifies the unit and counit of this same adjunction.
  Used by: InductionRestrictionAdjunction, ReverseTriangleIdentities.
- **MathlibAdjRightTriangle**: [CategoryTheory.Adjunction.right_triangle_components](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/CategoryTheory/Adjunction/Basic.lean#L117-L118);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Use for the right triangle after the corresponding identification of units, counits and fixed boundaries.

Import Mathlib.CategoryTheory.Adjunction.Basic. Checked Lean signature:
CategoryTheory.Adjunction.right_triangle_components.{v₁, v₂, u₁, u₂} {C : Type u₁} [CategoryTheory.Category.{v₁, u₁} C]
  {D : Type u₂} [CategoryTheory.Category.{v₂, u₂} D] {F : CategoryTheory.Functor C D} {G : CategoryTheory.Functor D C}
  (self : F ⊣ G) (Y : D) :
  CategoryTheory.CategoryStruct.comp (self.unit.app (G.obj Y)) (G.map (self.counit.app Y)) =
    CategoryTheory.CategoryStruct.id (G.obj Y)
After transport, apply the right triangle component at a B-module Y and evaluate the resulting map on y. This computes the counit at the identity-index tensor in Ind(Res Y). B-linearity then gives left multiplication on general pure tensors.
Use adj.right_triangle_components for the induction functor at each complex H-module. FiniteIndexReverseAdjunction identifies the unit and counit of this same adjunction.
  Used by: InductionRestrictionAdjunction, ReverseTriangleIdentities.
- **MathlibDoubleCosetQuotient**: [DoubleCoset.Quotient; DoubleCoset.eq](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/DoubleCoset.lean#L79-L80);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct indexing type for actual group double cosets K' backslash G slash H'. No finite group assumption.

Import Mathlib.GroupTheory.DoubleCoset. Checked Lean signature:
DoubleCoset.Quotient.{u_1} {G : Type u_1} [Group G] (H K : Set G) : Type u_1
The quotient indexes the K–H double cosets of permutations of the finite carrier.
Index the actual double cosets in Theorem 2.2. DoubleCoset.eq gives the representative factorization and proves that multiplying a representative on the two sides keeps its quotient class.
In Theorem 2.1, DoubleCoset.eq identifies the class of each product kσᵢh and factors every ambient element through the chosen section. This supplies the index and surjectivity facts for the balanced multiplication map.
  Used by: SurvivingCosetRepresentative, GeneralizedMackeyDecomposition, OrdinaryMackeyDecomposition, ParabolicDoubleCosetRepresentatives.
- **MathlibDoubleCosetEq**: [DoubleCoset.eq](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/DoubleCoset.lean#L124-L127);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct equality criterion for double-coset classes of subgroup elements. Use it to reduce orbit membership to factorizations and to compare the orbit of a transported representative.

Import Mathlib.GroupTheory.DoubleCoset. Checked Lean signature:
DoubleCoset.eq.{u_1} {G : Type u_1} [Group G] {H K : Subgroup G} {a b : G} :
  DoubleCoset.mk H K a = DoubleCoset.mk H K b ↔ ∃ h ∈ H, ∃ k ∈ K, b = h * a * k
SurvivingCosetRepresentative, Lemma 2.3: applied in the ambient subgroup G to the two comapped conjugate subgroups. The supplied equality for σ j turns the quotient membership test into the factorization in (2.1), and the subgroup inclusions lift an ambient factorization back to G.
Its forward direction writes q = k * p * h for invariance. The cell matching gives the same factorization in the reverse direction for injectivity.
ProductParabolicDoubleCosets, Xiao § 7.3. The forward implication sends a double coset factorization to each coordinate. The reverse implication lifts the chosen coordinate factors through the group equivalence using the two subgroup membership equivalences. The same criterion identifies the class of 1 with every local class when either local subgroup is top. Checked at the pinned revision via the compiled Proofs.ParabolicDoubleCosetRepresentatives import.
MackeyInclusionAndProjectionCrossings, Xiao § 2.2, equation (2.1). The reverse implication identifies the class of the supplied representative σ j with that of a basis point in the range of the balanced inclusion. The two factors lie in the comapped conjugate subgroups of G. This supplies the class equality required by SurvivingCosetRepresentative to enumerate the projection fiber. Checked through the compiled project dependencies.
MixedCrossingComposites, Xiao Proposition 5.1. With the supplied double-coset section and membership of s in orbit j, the reverse implication identifies the class of s with j. This connects the registered fiber theorem at s to the requested summand projection. The pinned source matches the GitHub file and the application compiled through the shared slot.
Xiao § 2.2, equations (2.1) and (2.6). The reverse implication puts the basis input g = a(k) σ_j b(h) into the class of the actual representative σ_j, through the two comapped conjugate subgroups in G. This supplies the class hypothesis of SurvivingCosetRepresentative for the singleton calculation. The pinned GitHub source and the checked project import agree.
Xiao Proposition 5.3, SinglePairCannotProjectOntoSeveralDoubleCosets. The reverse direction proves invariance of the outer orbit coordinate under the exterior action. The two factors lie in the ranges of the two conjugation embeddings, with the right inverse accounted for by the inverse in the H coordinate. The pinned GitHub source matches the local Mathlib file. The application compiled with MackeyDiagrams and Proofs.MixedCrossingComposites through the shared slot.
MixedReidemeisterTwoMackeyCancellation uses DoubleCoset.eq at the two comapped conjugate subgroups of G. The representative section then identifies each orbit with exactly one quotient class. Checked through the pinned project imports.
SinglePairIdentityCriterion, Xiao Proposition 5.3. The reverse direction of DoubleCoset.eq proves that the outer class coordinate is invariant under the K × H action. The range/comap equalities put the two action factors in A and B, with the inverse from the right action in B. The pinned GitHub source matches the local file and the application compiled through the existing project imports.
Xiao Example 5.1. The criterion factors the ambient permutations through the two specified representatives and transports their distinctness and exhaustiveness to the supplier quotient inside the top subgroup.
Xiao Example 7.3, OneSidedTableauCosetRepresentatives. Applied in both directions to identify equality of the classes of the ordered tableau representative and a permutation with membership in its right coset. The explicit hypothesis H = ⊥ forces the right subgroup factor to be 1. The pinned GitHub file matches the local Mathlib source, and Proofs.ParabolicDoubleCosetRepresentatives supplies the import.
Xiao Example 7.6. Apply the reverse implication at the identity representative. In the two local quotients use 1 on the restricted side and the given permutation on the full side. In the product quotient factor (a, b) as (1, b) times (a, 1). Checked with the pinned project imports.
Example 8.2 uses these witnesses to classify the identity and moving double cosets and identify the classes of (13) and (13)(456).
Xiao Example 7.7. Uses the double-coset equality criterion to show the two unrestricted quotients are singletons, transport the standard two-block representatives, and project and assemble the product factorizations. Checked against the pinned GitHub source and the compiled project imports.
  Used by: SurvivingCosetRepresentative, MackeyInclusionAndProjectionCrossings, MackeyOrthogonalityDiagram, TransportToMackeyRepresentative, MixedCrossingComposites, MixedReidemeisterTwoMackeyCancellation, TwoMackeySummandsWithSameInternalLabels, SinglePairCannotProjectOntoSeveralDoubleCosets, SinglePairIdentityCriterion, ParabolicDoubleCosetRepresentatives, OneSidedTableauCosetRepresentatives, ProductParabolicDoubleCosets, ProductParabolicsWithOneDoubleCoset, ProductParabolicsWithThreeDoubleCosets, LargestCommonParabolicDependsOnRepresentatives.
- **MathlibDoubleCosetRepresentative**: [DoubleCoset.out_eq'](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/DoubleCoset.lean#L129-L130);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct verification of the built-in quotient representative. Also use the equality criterion with the article's arbitrary family of representatives. Finiteness of the double-coset type is unnecessary.

Import Mathlib.GroupTheory.DoubleCoset. Checked Lean signature:
DoubleCoset.out_eq'.{u_1} {G : Type u_1} [Group G] {H K : Subgroup G} (q : DoubleCoset.Quotient ↑H ↑K) :
  DoubleCoset.mk H K (Quotient.out q) = q
MixedCrossingFiniteFiberConvention chooses Quotient.out as the section required by the registered MixedCrossingFiberMaps theorem and verifies the section equation with DoubleCoset.out_eq'. No finite double-coset space or finite standalone cup index is required.
StandardTwoBlockRepresentatives uses DoubleCoset.out_eq' to choose a permutation in an arbitrary target double coset. The two-block matrix bounds choose the swap index for that coset, and the registered classification equates the two cosets.
In finiteCosets, use DoubleCoset.out_eq' at the two subgroups comapped to H to prove that the quotient map from H is surjective. The Mackey isomorphism uses the section equation for the caller-supplied representatives.
Xiao Example 7.6. Reduce an arbitrary class in each of the three quotients to the class of its chosen representative before applying the factorization criterion. Checked with the pinned project imports.
  Used by: SurvivingCosetRepresentative, MixedCrossingFiniteFiberConvention, StandardTwoBlockRepresentatives, ProductParabolicsWithOneDoubleCoset, FiniteParabolicBicategoryComposition.
- **MathlibFinsuppReindex**: [Finsupp.domLCongr](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/LinearAlgebra/Finsupp/LSum.lean#L181-L183);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct linearization once an equivariant equivalence of bases is proved locally. Used for Mackey orbit bijections and for tensor merge basis equivalences.

Import Mathlib.LinearAlgebra.Finsupp.LSum. Checked Lean signature:
Finsupp.domLCongr.{u_2, u_4, u_7, u_8} {M : Type u_2} {R : Type u_4} [Semiring R] [AddCommMonoid M] [Module R M]
  {α₁ : Type u_7} {α₂ : Type u_8} (e : α₁ ≃ α₂) : (α₁ →₀ M) ≃ₗ[R] α₂ →₀ M
Linearize the mixed-word basis equivalence and identify the ambient group algebra coordinates.
  Used by: InductionRestrictionMergesAndSplits, GeneralizedMackeyDecomposition.
- **MathlibFinsuppDirectSum**: [sigmaFinsuppLequivDFinsupp](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Finsupp/ToDFinsupp.lean#L337-L340);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct linear equivalence for the free module on a sigma type and the dependent direct sum of free modules. Applies with arbitrary index type to the G basis partition into double-coset fibers.

Import Mathlib.Data.Finsupp.ToDFinsupp. Checked Lean signature:
sigmaFinsuppLequivDFinsupp.{u_1, u_2, u_4, u_5} {ι : Type u_1} (R : Type u_2) {η : ι → Type u_4} {N : Type u_5}
  [Semiring R] [AddCommMonoid N] [Module R N] : ((i : ι) × η i →₀ N) ≃ₗ[R] Π₀ (i : ι), η i →₀ N
In mackeyBisetIso, transport the registered Mackey isomorphism from the dependent sum of summand coordinates to the free module on the sigma basis. sigmaCoords_action checks equivariance coordinate by coordinate. sumIso uses the same equivalence to assemble the isomorphisms for the pairs of span indices.
  Used by: MackeyIdentityDiagram, GeneralizedMackeyDecomposition, FiniteParabolicBicategoryComposition.
- **MathlibFinsuppFiniteSupport**: [Finsupp.ofSupportFinite](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Finsupp/Defs.lean#L273-L276);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct realization of a coefficient column once its support is proved finite, used for ambient orbit-sum maps and pointwise finite orbit expansions. Extend using the project free-basis API. The existing transfer constructor already supplies its own finite-fiber implementation.

Import Mathlib.Data.Finsupp.Defs. Checked Lean signature:
Finsupp.ofSupportFinite.{u_1, u_4} {α : Type u_1} {M : Type u_4} [Zero M] (f : α → M)
  (hf : (Function.support f).Finite) : α →₀ M
In InductionBimoduleOrbitSumBasis, use Finsupp.ofSupportFinite to build the orbit-indexed coordinates of the value of a bimodule map at 1. Finite support follows by pulling back the coefficient support along the injective choice of one representative per distinct finite orbit. This gives the surjectivity of the map assembling finite sums of the proposed basis vectors.
In ExpansionIntoRightDiagrams, Finsupp.ofSupportFinite collects the nonzero orbit contributions for each input basis vector. The checked finite orbit support of the coefficient column gives its support hypothesis. Linear extension and summation give the pointwise finite expansion on every input.
  Used by: InductionBimoduleOrbitSumBasis, ExpansionIntoRightDiagrams, CaseFivePointwiseFiniteDiagramIdentity.
- **MathlibCosetTower**: [Subgroup.quotientEquivProdOfLE](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Coset/Basic.lean#L386-L387);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Adapt the quotient tower equivalence to the balanced basis after identifying the diagonal stabilizers or the underlying free action. It needs subgroup inclusion and gives the product with the smaller quotient, even for infinite groups. Use the per-fiber criterion separately for finiteness.

Import Mathlib.GroupTheory.Coset.Basic. Checked Lean signature:
Subgroup.quotientEquivProdOfLE.{u_1} {α : Type u_1} [Group α] {s t : Subgroup α} (h_le : s ≤ t) :
  α ⧸ s ≃ (α ⧸ t) × ↥t ⧸ s.subgroupOf t
count_tower identifies the fiber of the coset projection with the quotient of the full stabilizer by the smaller balancing subgroup. The vertex conditions give inclusion, and the inverse on the F coordinate makes the balance classes left cosets.
  Used by: MixedCrossingFiberMaps, MixedCrossingsThroughSmallerGroup, EvaluationForTwoProjections, ParabolicCaseTwoProjectionFiberIndices, ParabolicRightOrbitMultiplicity.
- **MathlibIndexAsCard**: [Subgroup.index_eq_card](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Index.lean#L356-L357);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct conversion from a finite coset count to a natural-number subgroup index. Use only with the separately established finiteness of the fiber or relevant quotient when interpreting a scalar count.

Import Mathlib.GroupTheory.Index. Checked Lean signature:
Subgroup.index_eq_card.{u_1} {G : Type u_1} [Group G] (H : Subgroup G) : H.index = Nat.card (G ⧸ H)
In MixedCrossingFiberMaps, convert the index of the conjugate-image subgroup inside the intersection into the natural cardinality of its left-coset quotient. The checked base-fiber and orbit-transport equivalences give the required fiber cardinality, and a separate finite-quotient argument checks finiteness.
In RightUpReidemeisterCurl, used through MackeyDiagrams.Generator.capFiber_card and MackeyDiagrams.Diagram.reverseCup_multiplicationCap to identify the finite multiplication-cap fiber cardinality with the index of the image of the inner conjugation embedding. The endpoint supplies finite index of that same image. The Mathlib source at the recorded revision matches the pinned project checkout.
Used through the compiled MackeyDiagrams.Diagram.reverseCup_multiplicationCap. Its Generator.capFiber_card supplier applies Subgroup.index_eq_card to identify the cardinality of the right-coset parametrization of a multiplication fiber with the index of d.toHom.range in H. The endpoint supplies finite index for this range, as required by the finite-fiber transfer.
Used through the registered MixedCrossingFiberMaps theorem at both L and Lj. The supplier identifies the balanced fiber with the stabilizer coset quotient and uses Subgroup.index_eq_card to compute its cardinality. The specialization identifies the stabilizer with Lj and the diagonal image with the chosen subgroup. The finite-relative-index hypotheses are checked for both applications.
Used through the registered RightUpReidemeisterCurl supplier. MackeyDiagrams.Generator.capFiber_card applies Subgroup.index_eq_card to identify the quotient cardinality in the reverse-cup and multiplication-cap calculation. Both applications of the scalar curl supplier pass the finite index of the same inner embedding range.
count_tower converts the natural cardinality of the identified quotient into its relative index. Finiteness of the projected stabilizer also gives positive relative index in the minimum argument.
Used through RightCurlAndDotSlide and its RightUpReidemeisterCurl supplier. MackeyDiagrams.Generator.capFiber_card uses Subgroup.index_eq_card to count the multiplication-cap fiber by the index of the inner embedding image. The shared finite-index hypothesis of the projected conjunct supplies finiteness for the reverse-cup transfer.
In the Case 5 identity, Subgroup.index_eq_card converts the relative index of the transposition-generated subgroup in the projected stabilizer to the cardinality of its coset quotient. The projected stabilizer embeds in finite F, and its quotient is nonempty. The index is therefore nonzero and its image in Complex can be inverted.
Convert the finite index of the stabilizer of point 4 in G to the cardinality of its coset quotient before applying orbit-stabilizer.
  Used by: MixedCrossingFiberMaps, RightUpReidemeisterCurl, RightCurlAndDotSlide, DotBelowInsideAboveRightCurl, LeftDownReidemeisterCurl, MixedCrossingsThroughSmallerGroup, SmallerParabolicReducesProjectionFiber, ParabolicRightOrbitMultiplicity, ParabolicCaseFiveUnscaledDiagramIdentity.
- **MathlibIndexMulCard**: [Subgroup.index_mul_card](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Index.lean#L360-L361);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct index-cardinality identity for finite parabolics. Combine with block orders and nonzero cardinalities to obtain division over the specified coefficient ring.

Import Mathlib.GroupTheory.Index. Checked Lean signature:
Subgroup.index_mul_card.{u_1} {G : Type u_1} [Group G] (H : Subgroup G) : H.index * Nat.card ↥H = Nat.card G
Applies to the smaller group viewed as a subgroup of the larger one. The subgroupOf equivalence gives the smaller ambient group order for both index formulas.
Proposition 8.2. For each of the four subgroup inclusions, identify its range with subgroupOf and transport the order using subgroupOfEquivOfLe. Multiply the inclusion index by the smaller subgroup's order to obtain the order of H.
  Used by: ParabolicCurlsFromBlockRefinements, ParabolicCurlJoinIntersection.
- **MathlibIndexTower**: [Subgroup.relIndex_mul_relIndex](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Index.lean#L125-L128);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct multiplicativity for the two subgroup inclusions in a tower. Apply at finite index for curls and fiber indices, or for divisibility of orbit multiplicities. Index zero for infinite quotients gives no normalization.

Import Mathlib.GroupTheory.Index. Checked Lean signature:
Subgroup.relIndex_mul_relIndex.{u_1} {G : Type u_1} [Group G] (H K L : Subgroup G) (hHK : H ≤ K) (hKL : K ≤ L) :
  H.relIndex K * K.relIndex L = H.relIndex L
Apply the index tower to the image of de(E), the first crossing intersection, and a(G). The nonzero index of de(E) in G forces the lower relative index to be nonzero.
For each right singleton triple, the dot equations give a subgroup tower from (ad)(C) through its intersection with the join to its intersection with the conjugated internal group. The multiplicativity identity transfers the nonzero middle-crossing index to the smaller intersection.
Multiplies the relative indices of consecutive merges after step inclusions and the containment from the initial block group have been established.
Apply with the parabolic image K below the swap-generated subgroup L below P, as supplied by the verified parabolic extremal theorem. Positive relative index of K in L shows that the multiplicity at L is minimal.
ParabolicCurlFactorization applies this theorem to the conjugate image A ≤ B ≤ H. The comparison with the finite index of A in H shows that both link indices are nonzero and identifies the product of the two curl scalars with the direct curl scalar.
Apply the subgroup index tower to the right embedding image, the greatest parabolic subgroup, and the projected stabilizer. This gives the divisibility of each right multiplicity by the orbit index.
Apply the relative-index tower to the parabolic embedding image K ≤ L ≤ P. Its product equality gives the divisibility of the singleton multiplicity by the orbit index.
  Used by: EvaluationForTwoProjections, CaseOneRightProjectionConstruction, CaseTwoLeftProjectionConstruction, ParabolicCurlsFromBlockRefinements, ParabolicCurlFactorization, ParabolicCaseTwoProjectionFiberIndices, ParabolicRightOrbitMultiplicity, ParabolicRightDiagramSpanOverCommutativeRings.
- **MathlibIndexNonzero**: [Subgroup.index_ne_zero](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Index.lean#L694-L695);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct nonzero index with the FiniteIndex instance, then use the cast into C or the explicitly invertible coefficient assumption.

Import Mathlib.GroupTheory.Index. Checked Lean signature:
Subgroup.index_ne_zero.{u_1} {G : Type u_1} [Group G] {H : Subgroup G} [H.FiniteIndex] : H.index ≠ 0
In CommonMackeyIntersectionSum, apply Subgroup.index_ne_zero to L.subgroupOf (Lj j) using the finite relative index instance. Cast the nonzero index to Complex and cancel the reciprocal in the normalized composite.
In NormalizedIndexValuedReidemeisterCurls, apply Subgroup.index_ne_zero to the range of the inner conjugation embedding in H with the supplied FiniteIndex instance. The natural-number cast to Complex is nonzero, so the inverse index cancels the scalar from both curl evaluations. The checked project imports already provide Mathlib.GroupTheory.Index.
In LargestCommonMixedCrossingParabolic, use finite relative index of S in Lj to supply FiniteIndex for S.subgroupOf Lj. Subgroup.index_ne_zero then supplies the nonzero index needed for index monotonicity and, after casting to Complex, cancellation of the reciprocal in each drawing summand. The configured project imports supply Mathlib.GroupTheory.Index.
  Used by: NormalizedIndexValuedReidemeisterCurls, NormalizedTrivalentCurl, CommonMackeyIntersectionSum, LargestCommonMixedCrossingParabolic.
- **MathlibOrbitStabilizer**: [MulAction.orbitEquivQuotientStabilizer](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/GroupAction/Quotient.lean#L169-L173);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct for any group action after bundling the project biset action as a MulAction. Use H for dot orbits and G × F for diagonal input-output orbits. Works for arbitrary types and does not imply finitely many or finite orbits.

Import Mathlib.GroupTheory.GroupAction.Quotient. Checked Lean signature:
MulAction.orbitEquivQuotientStabilizer.{u, v} (G : Type u) {X : Type v} [Group G] [MulAction G X] (b : X) :
  ↑(MulAction.orbit G b) ≃ G ⧸ MulAction.stabilizer G b
Instantiated on the diagonal action of G × F at the chosen pair. The inverse equivalence sends a stabilizer coset to the corresponding translated pair. Its injectivity identifies equal translated pairs with equal cosets, so the checked stabilizer graph gives the exact balance relation on the projection fiber. Column support supplies the finiteness separately.
In InductionBimoduleOrbitSumBasis, use the checked orbit equivalence for the twisted H-action on G. Its inverse sends the coset of h to h acting on the chosen representative. Consequently the fiber over an orbit point is one left coset of its stabilizer. In the finite-H branch, translating that coset computes the coefficient of each group element in the reverse-cup composite, and the nonzero stabilizer order supplies the normalizing scalar.
FiniteOrbitSumDiagram, Xiao § 3.4, Proposition 3.3. In the finite-H branch, bundle h ↦ (g ↦ a(h) * g * b(h)⁻¹) as a MulAction. The inverse orbit equivalence sends the coset of h to h acting on g, so its injectivity identifies the fiber over each orbit point with the left coset of a chosen preimage. Translation to the stabilizer gives the fiber cardinality and hence the coefficient of that point. Checked via the configured project and prerequisite imports. The pinned GitHub source matches the local Mathlib file.
Identify the coset quotient of G by the stabilizer of point 4 with its orbit, the three points different from point 3.
  Used by: InductionBimoduleOrbitSumBasis, FiniteOrbitSumDiagram, ExtremalParabolicsOfFiniteGroup, RightOrbitDiagramFromProjectedStabilizer, ExpansionIntoRightDiagrams, SmallerParabolicReducesProjectionFiber, ParabolicRightOrbitMultiplicity.
- **MathlibPermSupportMul**: [Equiv.Perm.set_support_mul_subset](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Perm/Support.lean#L233-L235);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct on arbitrary carrier type. Apply to finitary permutations using separately verified finite support. Avoid the Finset-support API that requires a Fintype carrier.

Import Mathlib.GroupTheory.Perm.Support. Checked Lean signature:
Equiv.Perm.set_support_mul_subset.{u_1} {α : Type u_1} (p q : Equiv.Perm α) :
  {x | (p * q) x ≠ x} ⊆ {x | p x ≠ x} ∪ {x | q x ≠ x}
For the product (1 3)(2 4) on Nat, any moved point lies in the support of one of the two factors. Both supports are contained in the union of the three two-point blocks.
  Used by: SupportBoundsUnderComposition, SupportBoundsForInverseProduct.
- **MathlibPermInverseSupport**: [Equiv.Perm.set_support_symm_eq](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Perm/Support.lean#L221-L222);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct set-supported inverse formula on any carrier. Combine with the product support inclusion for inverse products.

Import Mathlib.GroupTheory.Perm.Support. Checked Lean signature:
Equiv.Perm.set_support_symm_eq.{u_1} {α : Type u_1} (p : Equiv.Perm α) : {x | (Equiv.symm p) x ≠ x} = {x | p x ≠ x}
  Used by: SupportBoundsForInverseProduct.
- **MathlibFinitaryPerm**: [mem_closure_isSwap'](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Perm/ClosureSwap.lean#L126-L133);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct characterization of the subgroup generated by swaps on an arbitrary decidable-equality carrier as the finitely supported permutations. Use at Nat for S_infinity.

Import Mathlib.GroupTheory.Perm.ClosureSwap. Checked Lean signature:
mem_closure_isSwap'.{u_2} {α : Type u_2} [DecidableEq α] {f : Equiv.Perm α} :
  f ∈ Subgroup.closure {σ | σ.IsSwap} ↔ (MulAction.fixedBy α f)ᶜ.Finite
The reverse implication shows the identity extension of σ belongs to the swap closure, as required by FiniteParabolicConjugateBlocks. The complement of the fixed points is contained in X.
The forward implication bounds the moved support of the relative permutation αβ⁻¹. The reverse implication certifies each identity extension from a finite block slice.
An identity extension of a permutation of a finite block has finite support in that block and so lies in the ambient swap closure.
Theorem 7.4. A representative in the ambient block subgroup fixes every point outside the common finite carrier. The finite-support direction certifies the hypothesis of FiniteParabolicConjugateBlocks. Checked through the compiled project dependency imports.
Proposition 8.2. Apply the finite-support implication to the identity extension of a permutation of a finite block. The extension fixes the complement of the block.
Identify membership in the subgroup generated by swaps with finite moved-point support. A permutation supported on the union of the finitely many finite blocks has finite moved-point support.
The fixed-point complement of a block extension is contained in its finite block. The reverse direction of the swap-closure criterion therefore puts all block permutations in the finitary ambient group.
A permutation extended from a finite block fixes its complement, so its moved set is finite. Apply mem_closure_isSwap' over Nat to lift the extension into the finitary ambient group. Checked through the existing pinned project imports.
  Used by: FiniteParabolicConjugateBlocks, FiniteParabolicIntersectionBlocks, BlockwiseGroupElementDotCriterion, SupportBoundsUnderComposition, ParabolicMackeyIntersectionBlocks, MackeyDecompositionWithParabolicRepresentatives, FiniteParabolicBicategoryComposition, ParabolicCurlsFromBlockRefinements, ParabolicCurlJoinIntersection, UnequalParabolicCurlProducts, CaseSixCounterexampleWithTrivialProjectedStabilizers.
- **MathlibSwapClosureOrbit**: [mem_closure_isSwap](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Perm/ClosureSwap.lean#L101-L123);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct characterization of membership in a subgroup generated by a set of genuine swaps by finite support and orbit preservation, on arbitrary decidable-equality carrier. Adapt to orbit blocks and their connected-component join, or to swaps contained in a finite subgroup for its largest parabolic.

Import Mathlib.GroupTheory.Perm.ClosureSwap. Checked Lean signature:
mem_closure_isSwap.{u_2} {α : Type u_2} [DecidableEq α] {S : Set (Equiv.Perm α)} (hS : ∀ f ∈ S, f.IsSwap)
  {f : Equiv.Perm α} :
  f ∈ Subgroup.closure S ↔ (MulAction.fixedBy α f)ᶜ.Finite ∧ ∀ (x : α), f x ∈ MulAction.orbit (↥(Subgroup.closure S)) x
Apply the reverse direction to genuine swaps within refinement blocks. The common finite carrier contains all moved points, and the identity or the swap of a point with its image supplies each orbit witness.
Identifies the closure of genuine block swaps with the extended symmetric group of the block. For an extended permutation, the block bounds the moved points; a moved point and its image are in the same orbit via their swap.
The finite ambient carrier supplies finite support. The identity or a single genuine in-block swap witnesses the orbit condition for every point, proving membership in the block subgroup.
Checked for ExtremalParabolicsOfFiniteGroup on leanprover/lean4:v4.36.0-rc2 with the pinned Mathlib revision and the registered Proofs.FiniteParabolicClosure import. The forward implication bounds the support of each element of P. For the reverse implication, the generators are the genuine swaps already in the target subgroup. Each moved point and its image are related by such a swap, and fixed points use the identity. This derives generation of each finite block group and proves containment of P in the orbit-block supremum.
Used in both directions on Nat. The forward implication supplies finite support for members of P from the ambient swap-closure hypothesis. For the reverse implication, use the set of genuine swaps in the target subgroup. Each moved point and its image are connected by their swap, while fixed points use the identity. This proves generation of each finite block group and containment of P in the orbit-block supremum. Checked with MackeyDiagrams and the registered Proofs.FiniteParabolicClosure import.
A block-preserving permutation fixing the complement of the common carrier has finite support. Each moved point is in the same orbit as its image under the closure of internal swaps.
Proposition 8.2. Take the generating set of genuine transpositions within the parts of one partition. The finite carrier contains all moved points. Each moved point and its image are connected by their internal transposition, and every fixed point has the identity witness.
Proposition 8.4, induction row. The finite carrier of G bounds the support of the ambient join. The swap-closure criterion puts each extended orbit-block permutation in the join, since it has finite support and preserves the orbits. Conversely, each moved point and its image admit an internal swap in the block supremum, which gives the orbit witness for the criterion applied to the swaps of that supremum.
  Used by: FiniteParabolicIntersectionBlocks, FiniteParabolicJoinBlocks, ExtremalParabolicsOfFiniteGroup, ParabolicDoubleCosetRepresentatives, ParabolicCurlsFromBlockRefinements, ParabolicCurlJoinIntersection, ParabolicSharedRegionParallelInduction.
- **MathlibSubtypePermExtension**: [Equiv.Perm.ofSubtype; Equiv.Perm.ofSubtype_subtypePerm; Equiv.Perm.ofSubtype_apply_of_mem; Equiv.Perm.ofSubtype_apply_of_not_mem; Equiv.Perm.ofSubtype_apply_mem_iff_mem](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Group/End.lean#L441-L444);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct extension of a block permutation by the identity outside a decidable predicate. Use on finite blocks in Nat and separately prove finitary membership and product decomposition.

Import Mathlib.Algebra.Group.End. Checked Lean signature:
Equiv.Perm.ofSubtype.{u_4} {α : Type u_4} {p : α → Prop} [DecidablePred p] : Equiv.Perm (Subtype p) →* Equiv.Perm α
The identity extension defines each block factor and shows that its elements preserve the block and fix its complement. For a refinement factor, apply ofSubtype_subtypePerm after proving preservation of each parent block and pointwise fixing of its complement.
The extension defines the factors. Its membership and complement evaluation lemmas show that every factor preserves all blocks of its own partition.
In SupportedLeftOrbitProjectedStabilizer, restrict each block permutation to the finite union of the blocks and extend it back by the identity. This embeds each finite parabolic group into the finite symmetric group of its block union and supplies the upper multiplication fiber finiteness in equation (6.3).
Use ofSubtype_apply_of_not_mem to show that an overgroup supported on a four-point block must contain all four moved points of the conjugated Klein four subgroup.
In Xiao §7 and §8.2, Equiv.Perm.ofSubtype_apply_of_not_mem shows that every block permutation fixes the complement of the finite union of the blocks of G. The pinned GitHub file matches the compiled project’s Mathlib checkout.
For a permutation on a block subtype, identity extension fixes the complement pointwise and preserves membership in the block. This proves that each factor of G preserves {3, 4} setwise and verifies the complement-fixing property used in conjugating H.
Xiao Example 7.7. Restricts a permutation preserving the split to each half and reconstructs it as the product of their identity extensions. The extension preserves membership in each half and fixes its complement. Checked against the pinned GitHub source and the compiled project imports.
In the Case 5 identity, embed each finite parabolic boundary group into the symmetric group on its finite block union. For each block factor, ofSubtype_apply_of_not_mem shows that its permutation fixes the complement of the union. After checking that the union is invariant, ofSubtype_subtypePerm reconstructs the permutation from its restriction. This finiteness supplies the finite basis and projection fibers used in the endpoint.
  Used by: FiniteParabolicConjugateBlocks, FiniteParabolicIntersectionBlocks, SupportBoundsUnderComposition, SupportBoundsForInverseProduct, ParabolicDoubleCosetRepresentatives, ProductParabolicsWithThreeDoubleCosets, ParabolicFullMackeyCancellation, SupportedLeftOrbitProjectedStabilizer, ParabolicCaseFiveUnscaledDiagramIdentity, CaseSixCounterexampleWithTrivialProjectedStabilizers.
- **MathlibSwapTriple**: [Equiv.swap_mul_swap_mul_swap](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Group/End.lean#L577-L580);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Direct adjacent transposition calculation for the braid by applying it in both orders with the distinctness hypotheses and swap commutativity. Use in the stated symmetric chain with separate typed crossing evaluation.

Import Mathlib.Algebra.Group.End. Checked Lean signature:
Equiv.swap_mul_swap_mul_swap.{u_4} {α : Type u_4} [DecidableEq α] {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) :
  Equiv.swap y z * Equiv.swap x y * Equiv.swap y z = Equiv.swap z x
On the three-point subtype, conjugate (12) by (23) to get (13). The three points are distinct, as required for the swap identity. Checked through the existing pinned project imports.
Example 8.3. With distinct points 1, 2 and 3, the composite (23)(12)(23) equals (13) after swap symmetry. Thus the join contains the third generator of the block on 1 through 3.
  Used by: StandardSymmetricGroupBraidRelation, UnequalParabolicCurlProducts, ParabolicExtremalThreeInductionExample.
- **MathlibSubtypePermSwap**: [Equiv.Perm.ofSubtype_swap_eq](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Perm/Support.lean#L195-L198);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. When both endpoints belong to a refinement block, the swap on the block subtype extends to the required ambient swap. This puts each generator in the corresponding factor of the subgroup supremum.
A swap inside one block extends to the ambient transposition, putting it in that factor of the supremum.
At Nat, extends the subtype swaps on the input blocks to the ambient swaps (1 2), (2 4), and (4 5), using checked block membership for each endpoint.
Realizes the ambient swap of two points in a block as the identity extension of the corresponding subtype permutation. This supplies the swaps used to recover block refinement.
Proposition 8.4. Extending a swap in a finite block subtype gives the swap of its ambient endpoints. This identifies the block generators and puts each join generator in its orbit block subgroup.
Extend the block subtype swaps to (1 2), (3 4), and (1 3) in the ambient permutations. The first two define A and the last gives an explicit element of D outside A.
Xiao Example 7.8. Both endpoints of the transposition lie in the chosen two-point refinement block U. Extending the subtype swap gives the ambient swap, so the block subgroup and the proposed refinement contain a nonidentity element. The pinned GitHub source matches the local Mathlib source, and the application checks through the project imports.
Identify the extended swaps on the two- and three-point block subtypes with the corresponding ambient transpositions. Checked through the existing pinned project imports.
Example 8.3. A swap of two elements of the symbolic finite block subtype extends to their ambient transposition. This both places the designated generators in their blocks and transports the finite-subtype swap induction.
Identify each block transposition after identity extension with the corresponding transposition in S₄.
Identify the identity extension of a subtype swap with the swap of its two ambient points in the induction step for the blocks of A.
Example 8.5. Extend a swap on the subtype of a parabolic block to the swap of the same two natural numbers, putting that ambient transposition in the subgroup.
  Used by: FiniteParabolicIntersectionBlocks, SupportBoundsUnderComposition, ParabolicBlockOperationExample, ParabolicDoubleCosetRepresentatives, TwoBlockSplitGivesFourIntersections, ParabolicCurlsFromBlockRefinements, UnequalParabolicCurlProducts, ParabolicSharedRegionParallelRestriction, ParabolicExtremalThreeInductionExample, SmallerParabolicReducesProjectionFiber, ParabolicCaseSixOrbitCoefficientVanishesInCharacteristicThree, CaseSixCounterexampleWithTrivialProjectedStabilizers, ParabolicCaseSixObstructionWithTrivialProjectedStabilizer.
- **MathlibFinsuppLiftAddHom**: [Finsupp.liftAddHom; Finsupp.liftAddHom_apply_single](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/BigOperators/Finsupp/Basic.lean#L375-L456);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. In Steps 1.1 and 2.1 the additive Finsupp equivalence extends the integer-summand maps. Its singleton formula at coefficient 1 gives the prescribed generator values.
CanonicalWattsComparison, step 3.1. Extend the generator formula for a balanced pairing to the free additive group on pairs by mapping each integer summand to the corresponding multiples. The singleton evaluation gives the formula at 1.
  Used by: CanonicalWattsComparison, ModuleTensorUniversalProperty.
- **MathlibQuotientAddGroupLift**: [QuotientAddGroup.lift; QuotientAddGroup.lift_mk](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/QuotientGroup/Defs.lean#L247-L254);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. In Step 4.1 the lift descends the free additive map through the exact subgroup of relations. The ambient group is abelian and Step 3.1 supplies the kernel containment. The quotient lift formula evaluates the descended map at each generator.
CanonicalWattsComparison, steps 3.1 and 4.1. Descend the extensions for the outer scalar action, the map on morphisms, and the comparison through the same additive quotient, after proving the three families of relations lie in their kernels.
  Used by: CanonicalWattsComparison, ModuleTensorUniversalProperty.
- **MathlibQuotientAddGroupMkSurjective**: [QuotientAddGroup.mk'_surjective](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/QuotientGroup/Defs.lean#L99-L101);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. In Step 5.1 surjectivity of the additive quotient map transfers equality on all Finsupp representatives to equality on the tensor quotient.
  Used by: ModuleTensorUniversalProperty.
- **MathlibQuotientAddGroupKerMk**: [QuotientAddGroup.ker_mk'](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/QuotientGroup/Defs.lean#L140-L144);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. The kernel formula kills all relations used to prove the balance and two additivity laws needed in Step 1.2.
  Used by: ModuleTensorUniversalProperty.
- **MathlibAddSubgroupClosureLe**: [AddSubgroup.closure_le](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Group/Subgroup/Lattice.lean#L353-L356);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. In Step 3.1 closure extends vanishing on the three relation families to containment of their generated additive subgroup in the kernel.
  Used by: ModuleTensorUniversalProperty.
- **MathlibFinsuppAddHomExtSummands**: [Finsupp.addHom_ext'](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Finsupp/Ext.lean#L51-L59);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. In Step 5.1 equality on the integer summands determines equality of the two additive homomorphisms on the free group.
  Used by: ModuleTensorUniversalProperty.
- **MathlibZmultiplesHom**: [zmultiplesHom](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Int/Cast/Lemmas.lean#L268-L276);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. In Step 2.1 this equivalence gives the additive map from integers taking 1 to the supplied value. In Step 5.1 its inverse is evaluation at 1, so equality there gives agreement on the whole summand.
  Used by: ModuleTensorUniversalProperty.
- **MathlibSubtypeSwapExtension**: [Equiv.Perm.ofSubtype_swap_eq](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Perm/Support.lean#L196-L198);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Identifies the extension of the block subtype swap with the corresponding ambient swap.
Proposition 8.4, induction row. Identity extension sends a swap of two block subtypes to the swap of their values in Nat. Apply it to the generators of the conjugated factors and to the swap of a moved point and its image inside a join orbit block.
Example 8.7. The two swaps on the three-point subtype extend to the ambient transpositions (12) and (23). This proves the inclusions of their cyclic subgroups in the middle group of the left drawing.
  Used by: FiniteParabolicJoinBlocks, ParabolicSharedRegionParallelInduction, CaseSixReplacementThroughOverlappingBlocks.
- **MathlibSwapMembershipTransitivity**: [SubmonoidClass.swap_mem_trans](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Perm/ClosureSwap.lean#L71-L79);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Composes swaps in the input join at a common point of successive blocks. The lemma includes the degenerate equalities that can occur along a walk.
Applied twice to the subgroup A ⊔ B with the three certified swap memberships along 1–2–4–5, yielding membership of (1 5).
Obtain (13) from (12) and (23) in every subgroup satisfying the two Case 1 containment bounds.
  Used by: FiniteParabolicJoinBlocks, ParabolicBlockOperationExample, SmallerParabolicReducesProjectionFiber.
- **MathlibModuleCategoryProjectivity**: [IsProjective.iff_projective](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Category/ModuleCat/Projective.lean#L42-L46);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Identifies module projectivity and categorical projectivity. The ring and the carriers of the bundled modules use the same universe, supplying Small for the ring.
  Used by: SmallProjectiveGenerator.
- **MathlibModuleEpimorphismSurjective**: [ModuleCat.epi_iff_surjective](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Category/ModuleCat/EpiMono.lean#L49-L54);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Converts the surjectivity of the direct sum free cover to an epimorphism for the projective lift.
  Used by: SmallProjectiveGenerator.
- **MathlibDependentDirectSumLinearUniversalProperty**: [DFinsupp.lsum](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/LinearAlgebra/DFinsupp.lean#L151-L190);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Constructs coproduct descents and the free cover over the possibly noncommutative ring. The auxiliary scalar ring is Nat. The single-coordinate evaluation formula checks the coproduct legs and the cover on free generators.
  Used by: SmallProjectiveGenerator.
- **MathlibModuleForgetPreservesColimits**: [ModuleCat.forget₂PreservesColimitsOfShape](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Category/ModuleCat/Colimits.lean#L123-L125);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Composes the coproduct preservation proof for endomorphism-ring-valued Hom with the additive-group forgetful functor. Discrete colimits exist in the same-universe category of abelian groups.
  Used by: SmallProjectiveGenerator.
- **MathlibModuleForgetReflectsColimits**: [ModuleCat.reflectsColimitsOfShape](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Category/ModuleCat/Colimits.lean#L117-L118);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Reflects the coproduct preserved by additive-group-valued Hom to the module category over the opposite endomorphism ring, so its direct-sum comparison is an isomorphism.
  Used by: SmallProjectiveGenerator.
- **MathlibFinsetOrderIsoOfFin**: [Finset.orderIsoOfFin](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Finset/Sort.lean#L183-L190);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Decode ranks using the inherited natural order on each block and use the inverse order isomorphism to recover the exact ranks.
Identify each cell with Fin of its computed cardinality and transport the permutation group along this equivalence, including for cardinality zero.
  Used by: ParabolicDoubleCosetRepresentatives, EqualTwoBlockSubgroups.
- **MathlibFinSigmaFinEquiv**: [finSigmaFinEquiv; finSigmaFinEquiv_apply](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/BigOperators/Fin.lean#L678-L708);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Concatenate cell-offset types into block rank types. Its application formula is converted to the specified Iio prefix sum by mapping the smaller Fin type into the block index type.
  Used by: ParabolicDoubleCosetRepresentatives.
- **MathlibFinsetEquivOfCardEq**: [Finset.equivOfCardEq](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Fintype/EquivFin.lean#L334-L336);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Match each pair of equal-cardinality cells by a bijection to build the row permutation in the injectivity proof.
  Used by: ParabolicDoubleCosetRepresentatives.
- **MathlibNormalizerConjugateSubgroup**: [Subgroup.mem_normalizer_iff_map_conj_eq](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Group/Subgroup/Basic.lean#L409-L411);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Used in Lemma 5.2 to show that conjugation by αk⁻¹α⁻¹ fixes the conjugate of K and conjugation by h fixes H. The required normalizer memberships follow from subgroup membership. These equalities identify the two factors of the transported intersection. Lean checked both applications through the existing project imports.
  Used by: TransportToMackeyRepresentative.
- **MathlibSubtypePermExtension-a368870041df**: [Equiv.Perm.ofSubtype; Equiv.Perm.ofSubtype_apply_of_mem; Equiv.Perm.ofSubtype_apply_of_not_mem; Equiv.Perm.ofSubtype_apply_coe; Equiv.Perm.ofSubtype_injective](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Group/End.lean#L437-L476);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Extend permutations of the finite carrier to Nat by the identity outside X. The evaluation lemmas identify a block factor after two extensions with the single extension of the corresponding block in Nat. Equiv.Perm.ofSubtype_apply_coe identifies the extended image of each point of X, and Equiv.Perm.ofSubtype_injective lets us reflect equality of the extended subgroups back to Sym(X).
Extend each interval permutation by the identity. The complement formula makes empty factors trivial and proves commutation and independence for the disjoint cells. Injectivity is used in the product map.
  Used by: ParabolicMackeyIntersectionBlocks, EqualTwoBlockSubgroups.
- **MathlibSubgroupMapSupInf**: [Subgroup.map_iSup; Subgroup.map_inf](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Group/Subgroup/Map.lean#L209-L217);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Move the extension through the block suprema and their intersection. Preservation of the intersection uses the checked injectivity of the extension.
  Used by: ParabolicMackeyIntersectionBlocks.
- **MathlibRegularModuleEndSelf**: [RingEquiv.moduleEndSelf](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Module/LinearMap/End.lean#L286-L294);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Supplies the opposite-ring homomorphism acting by right multiplication for the unital ring A. Its value at MulOpposite.op a is definitionally LinearMap.mulRight A a.
  Used by: RegularModuleRightAction.
- **MathlibRegularModuleConjRingEquiv**: [LinearEquiv.conjRingEquiv](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Module/Equiv/Basic.lean#L594-L600);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Conjugates the endomorphism ring along the supplied A-linear ULift equivalence and preserves the exact action formula.
  Used by: RegularModuleRightAction.
- **MathlibFunctorMapEnd**: [CategoryTheory.Functor.mapEnd](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/CategoryTheory/Endomorphism.lean#L196-L201);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Supplies the unit and multiplication laws on mapped endomorphisms. Additivity of F gives the two additional ring homomorphism fields.
  Used by: RegularModuleRightAction.
- **MathlibRegularModuleCompHom**: [Module.compHom](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Module/RingHom.lean#L54-L62);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Restricts the evaluation module over Module.End B M along the constructed homomorphism from MulOpposite A. Its scalar action is definitionally evaluation of the image endomorphism.
  Used by: RegularModuleRightAction.
- **MathlibFinSumUnivTwo**: [Fin.sum_univ_two](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/BigOperators/Fin.lean#L111);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Expands each two-term row and column sum in the Nat matrix from ParabolicDoubleCosetRepresentatives, both when extracting the margins and when certifying the matrix supplied to its representative construction. Checked from Mathlib.Algebra.BigOperators.Fin through the existing imports.
  Used by: TwoBlockDoubleCosetMatrices.
- **MathlibParabolicComponentInd**: [SimpleGraph.ConnectedComponent.ind](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean#L416);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Proves that each component block is nonempty using a representative input block.
Use a vertex representative for an arbitrary connected component. The corresponding nonempty input block lies in the common finite carrier and supplies a point in the filtered component block.
In Proposition 8.6, choose a representative vertex of a component. Its nonempty block supplies a point of the filtered join block.
  Used by: FiniteParabolicClosure, FiniteParabolicJoinOfFamily, ParabolicExtremalOutsideRestrictionRegions.
- **MathlibParabolicAdjacentComponent**: [SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean#L439);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Identifies the components of opposite-side blocks containing a common point, which establishes disjointness of distinct component blocks.
Two input blocks on opposite sides sharing a point are adjacent in the bipartite overlap graph. Equality of their connected components gives the cross-side case in pairwise disjointness of component blocks.
In Proposition 8.6, two padded blocks on opposite sides that contain the same point are adjacent. Their equal connected components establish pairwise disjointness of the join blocks.
  Used by: FiniteParabolicClosure, FiniteParabolicJoinOfFamily, ParabolicExtremalOutsideRestrictionRegions.
- **MathlibGroupAlgebraProductSupport**: [MonoidAlgebra.support_coeff_mul_subset](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/MonoidAlgebra/Support.lean#L34-L40);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Extract an ordered contributing pair from a nonzero coefficient in a product. Iteration over the two binary products supplies the termwise group-element eligibility argument in Section 6.1.
  Used by: ThreeInductionCrossingMultipliers.
- **MathlibPermFixedComplementEquiv**: [Equiv.Perm.subtypeEquivSubtypePerm](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Group/End.lean#L493-L505);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Restrict a permutation fixing the complement pointwise and extend it back by identity. Apply to the six-swap permutation on the union and to the first block containing the support of K.
In Xiao §7 and §8.2, restrict permutations of G to the finite union of the blocks. The equivalence with complement-fixing permutations makes the restriction injective. Finiteness then passes to the double-coset quotient using the given section. The pinned GitHub file matches the compiled project’s Mathlib checkout.
Example 3.3. Restrict source permutations fixing the complement of the finite carrier to permutations of that carrier. The restriction is injective, giving the finiteness required for the reverse cup.
With the decidable predicate x ∈ S for a Finset of Nat, restrict a permutation fixing the complement of S and extend it back to obtain a witness in the range defining blockSym S.
Example 8.2 uses the equivalence for finite nonempty blocks of Nat to recognize a block subgroup by fixation of its complement.
Xiao Example 7.7. Identifies the range of each half-block inclusion with the permutations fixing its complement pointwise, enabling transport of the halves under the last representative. Checked against the pinned GitHub source and the compiled project imports.
Restrict a parabolic permutation to the finite union of its blocks. The complement-fixing equivalence proves injectivity, yielding finite G for the hypotheses of Theorem 6.4(1) and (2).
  Used by: BlockSwapOrbitSumWithoutGroupDot, SupportBoundsUnderComposition, SupportBoundsForInverseProduct, ProductParabolicsWithThreeDoubleCosets, ParabolicFullMackeyCancellation, LargestCommonParabolicDependsOnRepresentatives, FiniteParabolicSingleDiagramReplacements.
- **MathlibSubgroupISupInduction**: [Subgroup.iSup_induction](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Group/Subgroup/Pointwise.lean#L195-L211);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Prove both block-membership equivalences for the subgroup supremum by checking the two factors, identity, and multiplication.
Applied to the supremum of the full block factors: each member preserves each block of a pairwise disjoint family and fixes a point that lies in no nonsingleton block.
In Xiao §7 and §8.2, prove that the subgroup generated by the blocks of G fixes the complement of their union by checking membership in a block factor, the identity, and multiplication. The pinned GitHub file matches the compiled project’s Mathlib checkout.
Example 3.3. Check preservation of each target block in the individual block factors, the identity, and products, then pass to G.
  Used by: BlockwiseGroupElementDotCriterion, BlockSwapOrbitSumWithoutGroupDot, SupportBoundsUnderComposition, ParabolicFullMackeyCancellation.
- **MathlibSwapTransportConjugation**: [Equiv.swap_apply_apply](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Group/End.lean#L538-L541);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Identify each conjugate of the witness transposition (1 2) with the swap of its transported endpoints. The allowed conjugator has both endpoints in the first block, while the composite has its endpoints in the second.
Compute the conjugate of swap 2 3 by each element of K. Since K fixes both endpoints, this proves the swap centralizes K in Example 3.2.
Proposition 8.4. Conjugation sends a genuine swap to the swap of the two transported distinct endpoints. This checks the generator hypothesis on the join of conjugate parabolic images.
Example 3.3. Conjugate (4 5) by α using the images 7 and 8 of its endpoints. These determine the transposition in the second target block.
Compute the conjugate of the source transposition (1 2) by β * α⁻¹ as the ambient transposition (3 5), using the two checked point images.
Example 8.2 applies this to conjugate (12) by (13) within the first block and obtains (23).
  Used by: RightInputDotSlideObstruction, BlockSwapOrbitSumWithoutGroupDot, SupportBoundsUnderComposition, SupportBoundsForInverseProduct, LargestCommonParabolicDependsOnRepresentatives, ParabolicSharedRegionParallelRestriction.
- **MathlibResCoindAdjunction**: [Rep.resCoindAdjunction](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/RepresentationTheory/Coinduced.lean#L297-L304);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Used in repAdj for the actual embedding homomorphism. Its counit is evaluation at 1 and its unit sends y to the function t ↦ ρ(t)y. The local finite-index natural isomorphism changes the right adjoint from coinduction to induction.
  Used by: FiniteIndexReverseAdjunction.
- **MathlibIndCoindNatIso**: [Rep.indToCoind; Rep.coindToInd; Rep.indCoindNatIso](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/RepresentationTheory/FiniteIndex.lean#L102-L200);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Adapted the finite-index inclusion comparison in local Lean declarations. The kernel pulls the image-subgroup action back by the conjugation embedding using the project trace. With the given image finite index, transversal_exists supplies the finite right transversal. The two inverse checks reduce the sums to the unique representative, and the right-coset orientation gives the inverse index in each pure tensor. The adapted maps and their connection to the exact endpoint are compiled in this proof.
  Used by: FiniteIndexReverseAdjunction.
- **MathlibRelativeIndexOneContainment**: [Subgroup.relIndex_eq_one](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Index.lean#L486-L487);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. A singleton column forces L.relIndex Lj = 1. This supplies Lj ≤ L, which combines with the given L ≤ Lj to identify the two subgroups.
  Used by: MixedCrossingsThroughSmallerGroup.
- **MathlibFiniteRelativeIndexNonzero**: [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Index.lean#L712-L713);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. The self-index of Lj is one and therefore nonzero. This supplies the finite-relative-index hypothesis for the full-subgroup instance of MixedCrossingFiberMaps.
  Used by: MixedCrossingsThroughSmallerGroup.
- **MathlibFinsetCardEqOneExistsUnique**: [Finset.card_eq_one_iff_existsUnique](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Finset/Card.lean#L698);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Import supplied by the registered dependencies. Turns the unique survivor from Lemma 2.3 into the cardinality-one coefficient in (2.5). The survivor predicate is transported to membership in the finset of surviving indices.
  Used by: MackeySummandProjection.
- **MathlibExtendSubtype**: [Equiv.extendSubtype_apply_of_mem](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Logic/Equiv/Fintype.lean#L131-L140);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Used with the equivalence from the prescribed partial domain to its injective image in a finite moved-support slice. It certifies that the resulting slice permutation agrees with the relative permutation on the prescribed domain.
  Used by: BlockwiseGroupElementDotCriterion.
- **MathlibRelativeIndexInjectiveMap**: [Subgroup.relIndex_map_map_of_injective](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Index.lean#L92-L95);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Transport the second crossing index along conjugation by p composed with b in the full-intersection construction. Use a to transport the ambient index in the common-region construction.
index_on_range applies this to the projection restricted to the full stabilizer graph. The F embedding of that graph is injective. The same theorem transports indices using a conjugation automorphism for another orbit representative.
In transportIndices, transport the first stabilizer quotient along conjugation by a(z⁻¹) and the second along b followed by conjugation by a(z⁻¹)x. The first map is an automorphism. The second is injective by ConjEmbedding.injective for b and injectivity of the conjugation automorphism. The transported subgroups are identified before applying the corresponding index formulas.
Transport the single-crossing relative index from the inclusion ranges in A to the original subgroups C and G ∩ B in S₄.
  Used by: CaseTwoLeftProjectionConstruction, ParabolicCaseTwoProjectionFiberIndices, SmallerParabolicReducesProjectionFiber, ParabolicRightOrbitMultiplicity.
- **MathlibRelativeIndexMonotoneRight**: [Subgroup.relIndex_le_of_le_right](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Index.lean#L407-L410);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Bound the first fiber size in the common-region construction by the ambient index. The transported ambient index is nonzero by the finite-index hypothesis.
  Used by: CaseTwoLeftProjectionConstruction.
- **MathlibFinsuppMapDomainComapDomain**: [Finsupp.mapDomain_comapDomain](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Finsupp/Basic.lean#L618-L622);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Recover the entire input multiplier from the finite dot label pulled back along the injective eligible-element projection, using the supplier's support condition to place every nonzero coefficient in its range.
  Used by: MultipliersUnderRelabelling, AlternativeThreeInductionInternalGroups.
- **MathlibInducedPureGeneratorExt**: [Representation.IndV.hom_ext](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/RepresentationTheory/Induced.lean#L67-L71);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Check the induction maps, their naturality and the coproduct universal property on pure tensors.
Used through the registered generalized Mackey supplier’s pure_ext wrapper to check both inverse and equivariance laws for the regular comparison, and its compatibility with right multiplication, on induction generators.
  Used by: GeneralizedMackeyDecomposition, OrdinaryMackeyDecomposition.
- **MathlibCoinvariantsLift**: [Representation.Coinvariants.lift; Representation.Coinvariants.hom_ext](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/RepresentationTheory/Coinvariants.lean#L105-L117);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Descend the complex-linear maps from the ordinary tensor product using invariance under the diagonal group action.
Use the universal property on the diagonal middle-group action on the complex tensor product. Balance over the entire middle group algebra is equivalent to invariance under this action, by evaluating a group basis element and extending linearly. Lift and extensionality on coinvariants then give the existence and uniqueness laws on pure tensors.
Descend the coset-coordinate map for induction through Mathlib's coinvariant presentation after verifying invariance under the diagonal subgroup action on pure tensors.
  Used by: DiagrammaticFunctorCorrespondence, GeneralizedMackeyDecomposition, FiniteParabolicBicategoryComposition.
- **MathlibFunctorEvaluationReflectsColimits**: [CategoryTheory.Limits.evaluationJointlyReflectsColimits](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/CategoryTheory/Limits/FunctorCategory/Basic.lean#L53-L71);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Use the pointwise coproduct universal property to construct a colimit in the functor category.
  Used by: GeneralizedMackeyDecomposition.
- **MathlibPermutationSupportSwap**: [Equiv.Perm.support_swap](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Perm/Support.lean#L437-L438);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Identifies the support of each transposition with its two distinct endpoints. The endpoint inequalities then give pairwise disjoint supports.
  Used by: StandardTwoBlockRepresentatives.
- **MathlibRelativeIndexInjectiveImage**: [Subgroup.relIndex_map_map_of_injective](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Index.lean#L93-L95);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Transfer the upper crossing index along the injective internal embedding, and identify the common-region middle crossing index by mapping through a.
Identify the relative index in the top subgroup with [G:C] and transport it under the conjugations of the arbitrary middle projection.
  Used by: CaseOneRightProjectionConstruction, CaseOneNoFiniteRightReplacement.
- **MathlibRelativeIndexSmallerUpperGroup**: [Subgroup.relIndex_le_of_le_right](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Index.lean#L408-L409);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Bound each upper fiber index using (ad)(C) ≤ a(G). The parameter’s finite-fiber witness supplies the required nonzero index of the larger upper subgroup.
  Used by: CaseOneRightProjectionConstruction.
- **MathlibCardDependentFiniteProduct**: [Nat.card_pi](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/SetTheory/Cardinal/Finite.lean#L243);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Counts choices of local permutations after the restriction and gluing equivalence.
  Used by: ParabolicCurlsFromBlockRefinements.
- **MathlibCardFiniteSymmetricGroup**: [Fintype.card_perm](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Fintype/Perm.lean#L155);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Gives the factorial for each finite block permutation group.
Example 8.2 uses the factorial cardinality of the permutations of a finite block, including the five-point and two-point blocks.
Apply Fintype.card_perm on the finite subtype of each block. The extension equivalence transfers the cardinalities to the block subgroups of the finitary ambient group. Checked through the existing pinned project imports.
  Used by: ParabolicCurlsFromBlockRefinements, UnequalParabolicCurlProducts, LargestCommonParabolicDependsOnRepresentatives.
- **MathlibChooseFactorialProduct**: [Nat.choose_mul_factorial_mul_factorial](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Nat/Choose/Basic.lean#L142);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Identifies the single merge index after the common factorial factors of the surviving blocks are cancelled.
  Used by: ParabolicCurlsFromBlockRefinements.
- **MathlibProductOverFiniteFibers**: [Finset.prod_fiberwise_of_maps_to](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean#L264);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Reassociates the finer factorial factors by the unique containing block of the coarser partition.
  Used by: ParabolicCurlsFromBlockRefinements.
- **MathlibSigmaWhiskerEquiv**: [CategoryTheory.Limits.Sigma.whiskerEquiv](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/CategoryTheory/Limits/Shapes/Products.lean#L409-L418);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Theorem 7.4. Reindex the actual functor-category coproduct from double cosets to the product of block matrix types. Each component is the same summand after composition with the classification equivalence. Checked through the compiled project dependency imports.
  Used by: MackeyDecompositionWithParabolicRepresentatives.
- **MathlibModuleCatRestrictScalarsComp**: [ModuleCat.restrictScalarsComp'](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean#L246-L272);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Theorem 7.4 inclusion case. Use the comparison isomorphism after proving that the group-algebra map of the backward embedding factors through transport by the inverse representative followed by inclusion into H. The comparison acts by the identity on the underlying module. Checked through the compiled project dependency imports.
  Used by: MackeyDecompositionWithParabolicRepresentatives.
- **MathlibQuotientMap**: [Quotient.map](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Quot.lean#L228-L236);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Descends each selected replacement to the kernel setoid of evaluation. The proof supplies evaluation preservation on both sides and checks the two round trips on quotient representatives.
  Used by: ThreeInductionReidemeisterThree, ReplacementForTwoProjections.
- **MathlibLinearCombinationMapDomain**: [Finsupp.linearCombination_mapDomain](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean#L159-L162);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Identifies evaluation of the collected lower projection label with the termwise list used by the Case 2 common-group construction. The identity accounts for coincident target parameters.
In the fixed-E Case 2 construction, identify evaluation of the coefficient function pushed forward to lower projection dots with the supplier’s weighted list, including coincident dot parameters.
  Used by: ReplacementForTwoProjections, FiniteParabolicSingleDiagramReplacements.
- **MathlibIndexMapOfInjective**: [Subgroup.index_map_of_injective](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Index.lean#L347-L348);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. With subgroup L.subgroupOf K and the injective conjugation homomorphism a.toHom : K →* H, computes the index of its image in H as its index in K times the index of a.toHom.range in H. Natural multiplication is commuted to match the article. Mathlib.GroupTheory.Index is already available from the compiled imports.
  Used by: CurlAcrossTrivalentVertex.
- **MathlibParabolicFiniteBlockExtension**: [Equiv.Perm.ofSubtype_subtypePerm](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Group/End.lean#L446-L453);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Embed a parabolic subgroup in the permutation group of the finite union of its blocks. Each block permutation preserves the union and fixes its complement, so it is the extension of its restriction. This proves finiteness used for the Case 1 middle index and the two Case 2 projection domains.
In ParabolicCommonRightRegionForLinearLabels, restrict each factor to the finite union of the blocks. It preserves the union and fixes the complement, so the extension of its restriction recovers the factor. This proves finiteness of the parabolic groups used to bound the balanced-product domains and the generated subgroup.
Each permutation fixing the complement of the proposed block preserves the block. Its restriction extends back to that permutation.
  Used by: ParabolicExtremalOutsideRestrictionRegions, SmallerParabolicReducesProjectionFiber, ParabolicCommonRightRegionForLinearLabels.
- **MathlibFinsuppMapDomainSupport**: [Finsupp.mapDomain_support](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Finsupp/Basic.lean#L366-L370);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Bound the support of the evaluated right-input label by the images of its eligible terms. Every image lies in H, so the coefficient at the outside transposition vanishes.
  Used by: RightInputDotSlideObstruction.
- **MathlibIndependentCommutingProduct**: [MonoidHom.noncommPiCoprod; MonoidHom.noncommPiCoprod_range; MonoidHom.injective_noncommPiCoprod_of_iSupIndep](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/NoncommPiCoprod.lean#L104-L247);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Multiply the four extensions and identify the image with the subgroup supremum. The proof supplies pairwise commutation, independent ranges and injectivity of every factor map, yielding the claimed multiplication-preserving equivalence.
  Used by: EqualTwoBlockSubgroups.
- **MathlibCosetProductCard**: [Subgroup.card_mul_eq_card_subgroup_mul_card_quotient](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Coset/Card.lean#L61-L67);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Proposition 8.2. Apply with subgroup B and set A to count the set of products AB as the order of B times the number of represented left cosets aB. A checked injection identifies these cosets with A modulo B.subgroupOf A, whose order relation gives |AB| |A ∩ B| = |A| |B|. Compiled through the registered project imports on Lean v4.36.0-rc2.
  Used by: ParabolicCurlJoinIntersection.
- **MathlibFinitePermSwapGeneration**: [Equiv.Perm.closure_isSwap](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Perm/Sign.lean#L121-L122);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Proposition 8.4. Generate the full permutation group of each finite block subtype by genuine swaps before extending them to permutations of Nat.
  Used by: ParabolicSharedRegionParallelRestriction.
- **MathlibSwapClosureOrbitTranspositions**: [swap_mem_closure_isSwap](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Perm/ClosureSwap.lean#L83-L99);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Proposition 8.4. Every generator of the ambient join is a genuine swap. Two points in the same orbit therefore have their swap in the join, giving the full symmetric group on each orbit block.
  Used by: ParabolicSharedRegionParallelRestriction.
- **MathlibPermutationSwapInduction**: [Equiv.Perm.swap_induction_on](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Perm/Sign.lean#L99-L112);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Proposition 8.4, induction row. Induct on permutations of each finite block subtype. After identity extension and conjugation, each nontrivial swap lies in the ambient join and is a genuine transposition of Nat. This generates each transported block factor using swaps in the join.
Example 8.2 uses finite-subtype swap induction before extending to Nat to verify that block permutations are finitary and to identify the swap closure for the section 1, (13).
Apply swap induction on a finite block subtype, then extend each factor by the identity. This reduces containment of the block to the extended genuine swaps. Checked through the existing pinned project imports.
Example 8.3. Induction on permutations of a symbolic finite block subtype reduces generation by block transpositions to the identity and a swap step. Extending those swaps verifies finitary support and the two- and three-point block identifications.
Induct on the permutations of each finite block, {1,2,3} for the least region and {1,2} for the intersection.
Induct on permutations of each two-element block subtype to show that its extended symmetric group is contained in the swap closure defining A.
  Used by: UnequalParabolicCurlProducts, LargestCommonParabolicDependsOnRepresentatives, ParabolicSharedRegionParallelInduction, ParabolicExtremalThreeInductionExample, SmallerParabolicReducesProjectionFiber, ParabolicCaseSixObstructionWithTrivialProjectedStabilizer.
- **mathlib-free-add-group-universal-map**: [FreeAddGroup.ext_hom; FreeAddGroup.lift; FreeAddGroup.lift_apply_of](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/FreeGroup/Basic.lean#L625-L681);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Extend a pairing from the generators to an additive homomorphism before descending to the balanced quotient. The generator formula computes the lift, and free-group extensionality applied to both composites with the quotient map gives tensor extensionality.
  Used by: BimoduleTensorBicategoryCoherence.
- **mathlib-free-add-group-induction**: [FreeAddGroup.induction_on](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/FreeGroup/Basic.lean#L614-L618);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Prove the finite-sum assertion on quotient representatives. Use the empty list, singleton lists, a negated first factor for the negated generator, and list concatenation for addition.
  Used by: BimoduleTensorBicategoryCoherence.
- **mathlib-add-congruence-lift**: [AddCon.lift](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Congruence/Hom.lean#L187-L194);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Descend the free additive homomorphism after verifying all four generating relations in its kernel. This constructs the balanced lift without extracting data from a proposition.
  Used by: BimoduleTensorBicategoryCoherence.
- **MathlibExtremalSubgroupIndices**: [Subgroup.index_top; Subgroup.index_bot](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Index.lean#L258-L264);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. The right loop maps onto K, whose quotient by itself has one class. The left loop has trivial image in H, so its index is the cardinality of H.
  Used by: DifferentCurlIndices.
- **MathlibNatCardZMod**: [Nat.card_zmod](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/SetTheory/Cardinal/Finite.lean#L250-L254);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Identifies the cardinality of the reviewed C₂ model via the top subgroup and the underlying type of Multiplicative (ZMod 2).
  Used by: DifferentCurlIndices.
- **MathlibFinsuppMapDomainOfNotMemRange**: [Finsupp.mapDomain_of_notMem_range](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Finsupp/Basic.lean#L285-L287);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. After applying the target merge to the unit, the right-output label is pushed along d ↦ outer.toHom d.element for induction and d ↦ outer.toHom (d.element⁻¹) for restriction. Both maps land in the subgroup image of outer.toHom. The theorem makes each coefficient outside that image zero, while the incoming singleton has coefficient one at D for induction or D⁻¹ for restriction. The inverse-closed image gives the same necessary condition in both orientations. Mathlib.Data.Finsupp.Basic is available through the configured imports.
  Used by: MovingSplitDotToOutputBranch.
- **MathlibFixingSubgroupConjugation**: [SubMulAction.fixingSubgroup_map_conj_eq](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/GroupAction/SubMulAction/OfFixingSubgroup.lean#L228-L242);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Conjugate each fixing subgroup inside the ambient finitary permutation group by transporting the complement of its block. Reindex the supremum using the induced swap of the two middle blocks.
  Used by: StrongerEmbeddingConditionSlideObstruction.
- **MathlibMulSwapTransport**: [Equiv.mul_swap_eq_swap_mul](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Group/End.lean#L535-L536);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Proves each adjacent swap commutes with the composite inclusion image because every permutation in the source subgroup fixes both swapped points.
  Used by: StandardSymmetricGroupBraidRelation.
- **MathlibSemidirectConjugationAction**: [SemidirectProduct.inl_aut](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/SemidirectProduct.lean#L138-L139);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Identify the swap conjugate of an element on the first coordinate line with the second-coordinate element.
Use conjugation by the swap to obtain the second coordinate line from the first, both in the displayed join and in the join with a conjugate of D.
  Used by: CaseOneNoFiniteRightReplacement.
- **MathlibQuotientKernelOfSurjection**: [QuotientGroup.quotientKerEquivOfSurjective](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/QuotientGroup/Basic.lean#L156-L160);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Identify the quotient of the base subgroup by the first coordinate line with the infinite second coordinate group.
Identify the quotient of G by C with the infinite image of the surjective second-coordinate homomorphism.
  Used by: CaseOneNoFiniteRightReplacement.
- **MathlibFinSumUnivFunGetElem**: [Fin.sum_univ_fun_getElem](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/BigOperators/Fin.lean#L92-L95);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Reindex the finite evaluated sum by positions in the original list, retaining repeated summands. This identifies the evaluation of the reviewed IndexedDrawing with that of the fold used in ExpansionIntoRightDiagrams.
  Used by: CaseFivePointwiseFiniteDiagramIdentity.
- **MathlibFinsetOrderIsoOfFinSymmApply**: [Finset.orderIsoOfFin_symm_apply](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Finset/Sort.lean#L203-L205);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Rewrite each rank as the index of its point in the sorted row or column.
  Used by: TableauDoubleCosetRepresentativeInS6.
- **MathlibListToFinsetSort**: [List.toFinset_sort](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Finset/Sort.lean#L91-L97);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Identify each sorted block with an explicit increasing list by checking its set of entries and that it has no duplicates.
  Used by: TableauDoubleCosetRepresentativeInS6.
- **MathlibEquivSwapApplyDef**: [Equiv.swap_apply_def](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Logic/Equiv/Basic.lean#L651-L652);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Compute the transposition on the tableau points and compare it with the rank matching.
Evaluate the two constituent transpositions on each of the four allowed point labels to prove that the representative acts by x ↦ 5 − x.
  Used by: TableauDoubleCosetRepresentativeInS6, MackeyConjugationExchangesFactors.
- **MathlibPermConjSmulRangeOfSubtype**: [Equiv.Perm.conj_smul_range_ofSubtype](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Perm/ConjAct.lean#L63-L69);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. On the finite carrier of labels 1 through 4 with decidable equality, identify the subgroup image under conjugation with the range of permutation extension from the image block. Compute that image for both intervals and use the checked involution equality for inverse conjugation.
  Used by: MackeyConjugationExchangesFactors.
- **MathlibPermSumCongrHomInjective**: [Equiv.Perm.sumCongrHom_injective](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Group/End.lean#L202-L217);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Xiao Example 7.6. The independent permutation actions on the two Fin 2 summands give an injective homomorphism. Transport through finSumFinEquiv preserves injectivity, so the split homomorphism identifies S₂ × S₂ with its range. Checked with the pinned project imports.
  Used by: ProductParabolicsWithOneDoubleCoset.
- **MathlibRelativeIndexCardinality**: [Subgroup.relIndex_mul_card](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Index.lean#L364-L365);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Example 8.2 combines the computed subgroup cardinalities with containment to obtain the relative indices 120, 60, and 2. The index of the full five-point subgroup in itself is 1.
  Used by: LargestCommonParabolicDependsOnRepresentatives.
- **MathlibFinsuppSumSingle**: [Finsupp.sum_single](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/BigOperators/Finsupp/Basic.lean#L413);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. After combining repeated eligible dots by addition of coefficients, rebuilding that Finsupp from the singleton vectors of its support gives the same coefficient vector. Used by the checked eval_collect adapter.
  Used by: CaseTwoRequiresSum.
- **MathlibDoubleCosetMem**: [DoubleCoset.mem_doubleCoset](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/DoubleCoset.lean#L44-L46);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Used in the checked canonical arithmetic. With both side sets the range line, it turns each supported first projection atom into an explicit left and right factorization. This gives the zero probe outside that double coset and uses no finite-group assumption.
  Used by: CaseTwoRequiresSum.
- **MathlibDoubleCosetMemSelf**: [DoubleCoset.mem_doubleCoset_self](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/DoubleCoset.lean#L48-L49);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Used in two_left_drawings to put τ in its own line double coset for the second CaseTwoLeftProjectionConstruction witness.
  Used by: CaseTwoRequiresSum.
- **MathlibZModIntCastKernel**: [ZMod.intCast_zmod_eq_zero_iff_dvd](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/ZMod/Basic.lean#L512-L513);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Identify the kernel of each integral orbit coordinate reduced modulo the minimum multiplicity with the principal ideal generated by that multiplicity.
Compute the kernel of reduction on each integral orbit coordinate. The ULift witnesses transport divisibility by the natural orbit index between the two integer types.
  Used by: ParabolicRightDiagramSpanOverCommutativeRings.
- **MathlibNatCardZpowers**: [Nat.card_zpowers](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/ZMod/QuotientGroup.lean#L160);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Compute the cardinality of the projected cyclic stabilizer from the kernel-checked order of the cycle.
  Used by: ParabolicCaseSixOrbitCoefficientVanishesInCharacteristicThree.
- **MathlibStabilizerSmulConjugation**: [MulAction.stabilizer_smul_eq_stabilizer_map_conj](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/GroupAction/Basic.lean#L263-L264);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Conjugate the stabilizer of the simultaneous input-output pair when changing orbit representative, then project to the right boundary.
  Used by: ParabolicCaseSixOrbitCoefficientVanishesInCharacteristicThree.
- **MathlibCharPCastEqZero**: [CharP.cast_eq_zero](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/CharP/Defs.lean#L60);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. The checked natural count of three casts to zero in the coefficient ring of characteristic three.
  Used by: ParabolicCaseSixOrbitCoefficientVanishesInCharacteristicThree.
- **MathlibIdealMemSpanSingleton**: [Ideal.mem_span_singleton](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/RingTheory/Ideal/Span.lean#L180-L181);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Express the coordinate ideal as divisibility by the cast orbit index. Use this to assemble the span from its orbit generators and to compute the integral reduction kernel.
  Used by: ParabolicRightDiagramSpanOverCommutativeRings.
- **MathlibZModIntCastSurjective**: [ZMod.intCast_surjective](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/ZMod/Basic.lean#L228-L229);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Choose an integer representative at each orbit to lift every family of residues through the orbit-coordinate equivalence.
  Used by: ParabolicRightDiagramSpanOverCommutativeRings.
- **MathlibIntCastSmulEqZsmul**: [Int.cast_smul_eq_zsmul](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Module/NatInt.lean#L169-L175);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Identify ULift Int scalar multiplication with integer multiples in the comparison between additive closure and the module span of the diagram evaluations.
  Used by: ParabolicRightDiagramSpanOverCommutativeRings.
- **MathlibAddQuotientKernelOfSurjection**: [QuotientAddGroup.quotientKerEquivOfSurjective](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/QuotientGroup/Basic.lean#L153-L160);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Identify the additive quotient by the diagram span with the codomain of the surjective coordinatewise reduction, using the checked kernel equality.
  Used by: ParabolicRightDiagramSpanOverCommutativeRings.
- **MathlibDirectSumAddEquivProd**: [DirectSum.addEquivProd](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/DirectSum/Basic.lean#L499-L505);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Convert the dependent product of residue groups to the direct sum by finiteness of the orbit type.
  Used by: ParabolicRightDiagramSpanOverCommutativeRings.
- **MathlibSwapFixesOtherPoints**: [Equiv.swap_apply_of_ne_of_ne](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Logic/Equiv/Basic.lean#L662-L664);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Example 8.7. Each generator fixes a point outside its two endpoints. This puts the cyclic subgroup in that point stabilizer and yields D ∩ E = 1 by injectivity at the common point 2.
  Used by: CaseSixReplacementThroughOverlappingBlocks.
- **MathlibFunctorLinearCriterion**: [CategoryTheory.Functor.linear_iff](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/CategoryTheory/Linear/LinearFunctor.lean#L39);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Reduce complex-linearity of the tensor functor to preservation of scaled identities in the complex-linear module categories.
  Used by: ComplexEilenbergWatts.
- **MathlibFunctorLinearIso**: [CategoryTheory.Functor.linear_of_iso](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/CategoryTheory/Linear/LinearFunctor.lean#L102);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Transport complex-linearity along the inverse of the underlying counit isomorphism to establish essential surjectivity of the restricted functor.
  Used by: ComplexEilenbergWatts.
- **MathlibFinsuppSigmaDecomposition**: [sigmaFinsuppLequivDFinsupp](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Finsupp/ToDFinsupp.lean#L293-L340);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Split the group basis by left cosets as a finitely supported family of subgroup group algebras. The worker checks the inverse on singletons and verifies right module linearity separately.
  Used by: DiagrammaticFunctorCorrespondence.
- **MathlibClosureOfColimitPreservingFunctors**: [CategoryTheory.ObjectProperty.prop_of_isColimit](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/CategoryTheory/ObjectProperty/ColimitsOfShape.lean#L225-L227);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Pointwise coproducts preserve the colimit shapes each component functor preserves. The worker separately checks complex linearity after the coproduct inclusions and constructs the lifted cocone.
  Used by: DiagrammaticFunctorCorrespondence.
- **MathlibGroupInductionFunctor**: [Rep.indFunctor](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/RepresentationTheory/Induced.lean#L111-L118);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. The induction functor in the reviewed endpoint uses coinvariants for the left regular action. The local proof works on this exact definition and its indMap.
  Used by: DiagrammaticFunctorCorrespondence.
- **MathlibCoinvariantInverseTensor**: [Representation.Coinvariants.mk_inv_tmul](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/RepresentationTheory/Coinvariants.lean#L254-L260);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Identifies a pure tensor with inverse group label (r_i * f(h))⁻¹ with the label r_i⁻¹ and vector acted on by h. The group action is the restriction of the left regular representation along f.
  Used by: DiagrammaticFunctorCorrespondence.
- **MathlibFinsuppRangeMapRange**: [Finsupp.range_mapRange](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Data/Finsupp/Defs.lean#L352-L368);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Lifts a finitely supported tuple in the kernel coordinatewise through the preceding map of an exact sequence. Only its coordinates need preimages, because the map preserves zero.
  Used by: DiagrammaticFunctorCorrespondence.
- **MathlibModuleCatFunctionExact**: [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean#L73-L78);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Reduces exactness of the original and induced short complexes of modules over the potentially noncommutative group algebras to exactness of the underlying maps.
  Used by: DiagrammaticFunctorCorrespondence.
- **MathlibAdditiveFunctorExactTFAE**: [CategoryTheory.Functor.exact_tfae](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Homology/ShortComplex/ExactFunctor.lean#L207-L222);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. The one-based pair (2, 4) converts preservation of exact sequences by the additive induction functor between abelian module categories to preservation of finite limits and finite colimits.
  Used by: DiagrammaticFunctorCorrespondence.
- **MathlibFunctorMapBiproduct**: [CategoryTheory.Functor.mapBiproduct](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/CategoryTheory/Limits/Preserves/Shapes/Biproducts.lean#L273-L282);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Supplies sumIso for the additive transport functor on the reviewed Fin-indexed biproducts. The comparison maps on inclusions and projections are CategoryTheory.Functor.biproductComparison_π and CategoryTheory.Functor.ι_biproductComparison' in the same module at lines 214–226.
  Used by: DiagrammaticFunctorCorrespondence.
- **MathlibBiproductMatrixComponents**: [CategoryTheory.Limits.biproduct.matrix_components](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/CategoryTheory/Limits/Shapes/Biproducts.lean#L968-L975);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Extracts each allowed drawing map from a matrix and computes each entry in the transported matrix.
  Used by: DiagrammaticFunctorCorrespondence.
- **MathlibBiproductComponentsMatrix**: [CategoryTheory.Limits.biproduct.components_matrix](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/CategoryTheory/Limits/Shapes/Biproducts.lean#L976-L980);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. Reconstructs a natural transformation from its matrix entries after choosing a witness in the exact allowed drawing subtype for each entry.
  Used by: DiagrammaticFunctorCorrespondence.
- **MathlibRestrictScalarsExact**: [ModuleCat.restrictScalars_map_exact](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Category/ModuleCat/ChangeOfRingsExact.lean#L33-L42);  [repository](https://github.com/leanprover-community/mathlib4); revision `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`; license: Apache-2.0. The finite-limit preservation instance from this exactness theorem applies to the reviewed restriction functor along the group-algebra map between possibly noncommutative rings.
  Used by: DiagrammaticFunctorCorrespondence.

## Upstream Lean verification

- **WattsFreePresentation**. Lean verification evidence recorded. Local integration: Import MackeyDiagrams.External.StacksEilenbergWatts from the current project build. The upstream file was compiled unchanged apart from an attribution comment against the project Lean and mathlib; source and compiled artifact hashes are recorded in evidence/verified-stacks-eilenberg-watts/receipt.json. Stacks.EilenbergWatts.iso assumes one commutative ring and a linear endofunctor: it is not the arbitrary two-ring Eilenberg–Watts theorem. The cofan lemma applies to arbitrary categories only with the stated IsColimit and IsIso hypotheses. Both depend on Classical.choice, so neither establishes a choice-free proof by its axiom audit. No original endpoint is closed without a checked adapter..
  - leanprover/lean4:v4.36.0-rc2, revision f56a316ddf7a930906d88b78d6f9a2668cffd0cf. [Stacks.EilenbergWatts.iso](https://github.com/AxiomMath/Stacks/blob/f56a316ddf7a930906d88b78d6f9a2668cffd0cf/StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/EilenbergWatts.lean#L429) · [Verification evidence](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/evidence/verified-stacks-eilenberg-watts/audit.log)
  - leanprover/lean4:v4.36.0-rc2, revision f56a316ddf7a930906d88b78d6f9a2668cffd0cf. [CategoryTheory.NatTrans.isIso_app_of_isColimit_cofan](https://github.com/AxiomMath/Stacks/blob/f56a316ddf7a930906d88b78d6f9a2668cffd0cf/StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/EilenbergWatts.lean#L84) · [Verification evidence](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/evidence/verified-stacks-eilenberg-watts/audit.log)
- **EilenbergWatts**. Lean verification evidence recorded. Local integration: Import MackeyDiagrams.External.StacksEilenbergWatts from the current project build. The upstream file was compiled unchanged apart from an attribution comment against the project Lean and mathlib; source and compiled artifact hashes are recorded in evidence/verified-stacks-eilenberg-watts/receipt.json. Stacks.EilenbergWatts.iso assumes one commutative ring and a linear endofunctor: it is not the arbitrary two-ring Eilenberg–Watts theorem. The cofan lemma applies to arbitrary categories only with the stated IsColimit and IsIso hypotheses. Both depend on Classical.choice, so neither establishes a choice-free proof by its axiom audit. No original endpoint is closed without a checked adapter. The exact original Eilenberg–Watts endpoint was subsequently proved using WattsFoundation.ReviewedOriginalWattsConnection; see evidence/EilenbergWatts-compile.json and evidence/checked-connections/EilenbergWatts-2a72adc1088d4a166c37cf51398d71eb/receipt.json. The separate choice-free auxiliary remains open..
  - leanprover/lean4:v4.36.0-rc2, revision f56a316ddf7a930906d88b78d6f9a2668cffd0cf. [Stacks.EilenbergWatts.iso](https://github.com/AxiomMath/Stacks/blob/f56a316ddf7a930906d88b78d6f9a2668cffd0cf/StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/EilenbergWatts.lean#L429) · [Verification evidence](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/evidence/verified-stacks-eilenberg-watts/audit.log)
  - leanprover/lean4:v4.36.0-rc2, revision f56a316ddf7a930906d88b78d6f9a2668cffd0cf. [CategoryTheory.NatTrans.isIso_app_of_isColimit_cofan](https://github.com/AxiomMath/Stacks/blob/f56a316ddf7a930906d88b78d6f9a2668cffd0cf/StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/EilenbergWatts.lean#L84) · [Verification evidence](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/evidence/verified-stacks-eilenberg-watts/audit.log)
- **SmallProjectiveGeneratorCorrespondence**. Lean verification evidence recorded. Local integration: The exact reviewed article statement is proved by WattsFoundation.ReviewedSmallGeneratorConnection and registered as Proofs.SmallProjectiveGeneratorCorrespondence. Its native build and axiom audit are in evidence/SmallProjectiveGeneratorCorrespondence-compile.json, and the separately checked exact connection is in /home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/evidence/checked-connections/SmallProjectiveGeneratorCorrespondence-c4ebd489805e9ea174d8622bfe4f1414/receipt.json. The locally built reconstruction, evaluation transport, naturality, bimodule-action and strict repacking helpers are documented with source and artifact hashes in evidence/small-generator-correspondence-foundations.json. This classical proof does not discharge the separately stated choice-free ProjectiveGeneratorModuleReconstruction auxiliary..
  - leanprover/lean4:v4.36.0-rc2, revision working-tree; source-sha256:723c4d0bc2439af62dc2d41a43fb6154637272f0659d2b63e4d031cc8732dc0e. [ReconstructionFromSmallProjectiveGenerator](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/WattsFoundation/ReconstructionFromSmallProjectiveGenerator.lean) · [Verification evidence](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/evidence/reconstruction-local-audit.log)
  - leanprover/lean4:v4.36.0-rc2, revision working-tree; source-sha256:ce62ef1dc565de2ec54b78ef2fb0c36b4c4623af44d80061d1f7a505be97f1a7. [SmallGeneratorBridge.equivalenceOfSmallProjectiveGenerator](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/WattsFoundation/SmallGeneratorBridge.lean) · [Verification evidence](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/evidence/small-generator-bridge-audit.log)
  - leanprover/lean4:v4.36.0-rc2, revision working-tree; source-sha256:5fe35abb01bd6f42753996f979e14e5a459234a7daa762b5873272146566de19. [SmallGeneratorBridge.regularToHom_right](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/WattsFoundation/GeneratorRegularActions.lean) · [Verification evidence](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/evidence/generator-regular-actions-audit.log)
  - leanprover/lean4:v4.36.0-rc2, revision working-tree; source-sha256:8e295b20dc09479e6ea2342f06eb317f31d674ef1161fe6db071d3f9a67f5dd3. [SmallGeneratorBridge.evaluationTransportIso_natural](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/WattsFoundation/GeneratorTransportNaturality.lean) · [Verification evidence](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/evidence/generator-transport-naturality-audit.log)
  - leanprover/lean4:v4.36.0-rc2, revision working-tree; source-sha256:c7d693f9d62e37cc7ec9d93f806af2d1cd92592fd10547f1bd5fa9e8ee6a92a7. [SmallGeneratorBridge.evaluationTransportIso_intertwines](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/WattsFoundation/GeneratorTransportAction.lean) · [Verification evidence](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/evidence/generator-transport-action-audit.log)
  - leanprover/lean4:v4.36.0-rc2, revision working-tree; source-sha256:b277f555a257e38fb7ac15ea575c0c9ba3d42312cfa0797e3244cfae59bb4d23. [ReviewedSmallGeneratorConnection](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/WattsFoundation/ReviewedSmallGeneratorConnection.lean) · [Verification evidence](file:///home/lazyinspirit/Projects/mackey-bimodule-diagrams-lean/evidence/checked-connections/SmallProjectiveGeneratorCorrespondence-c4ebd489805e9ea174d8622bfe4f1414/receipt.json)

## Navigation and verification

- [PROJECT.md](PROJECT.md): statements, sources, translations and dependencies.
- [EXTERNAL_PROOFS.md](EXTERNAL_PROOFS.md): external proof ledger.
- Proofs/: Lean declarations and proofs.
- translations/: independently reviewed types and definition values.
- evidence/: reviews, compiler diagnostics and axiom audits.

Run `lake update`, `lake exe cache get`, then `lake build`. The workflow additionally checks each declaration's axioms, permitting only propext, Classical.choice and Quot.sound.

## Included prerequisite packages

- [prerequisites](prerequisites/README.md): sources and native workflow evidence in this repository.

Run `make` from this repository root to build both the article and its prerequisite packages. See [BUILD.md](BUILD.md).

## Retired optional prerequisites

- WattsFreePresentation, ProjectiveGeneratorModuleReconstruction: unproved and excluded from the active plan. Owner directs: formalize only necessary results, not the entire lecture notes, and complete Steps 4–5. All 143 inventoried paper endpoints have registered proofs. These two stronger choice-free portal auxiliary claims are outside their dependency closure, have no retained consumers, and are not imported by the 278 local source modules checked in evidence/article-dependency-extraction/mechanical-audit.json. Ordinary Classical.choice is permitted for the article correspondences. These claims are retired as unproved, not accepted or refuted; preserve their full original state and holds in the retirement evidence. Original statements and state are preserved in evidence/retired-prerequisites-*.json.

<!-- Diagram semantics appendix -->

## How the string diagrams are formalized

The shared Lean library is [`MackeyDiagrams`](MackeyDiagrams.lean). Its ambient group is `U`; the article specializes the commutative coefficient ring to `ℂ`. Horizontal composition balances over the middle group algebra, and vertical composition is read from bottom to top. The original paper remains unchanged under `source/`.

The owner clarified on 27 November 2026 that **every dot is a finite complex linear combination of eligible group elements**, including standalone dots and marks inside crossings and curls. A group-element dot is the singleton with coefficient one. The same geometric mark supports the zero label and labels with several terms. This convention applies to the entire language and to the fresh endpoint reviews.

| Article data | Lean representation |
| --- | --- |
| Region | `Subgroup U` |
| Strand label `α C_U(H)` | `ConjEmbedding H G`, with a conjugation-induced homomorphism |
| Eligible group-element label | `Dot a b`: an element `d : G` satisfying `a(h) * d = d * b(h)` for every `h : H` |
| General dot label | `DotLabel R a b`, the finitely supported coefficient function `Dot a b →₀ R` |
| Ordered, fully labelled boundary | `Boundary K H`; `Word K H` retains a tensor expression for it |
| Typed drawing | `LabelledDrawing R bottom top` |
| Trivalent junction | `TrivalentVertex bottom top`, with twelve oriented constructors |
| Geometric shape | `PlanarShape`, with ordered bottom/top orientations and positioned wiring modulo disjoint interchange |
| Genuine shapes at one orientation boundary | `LabelledDrawing.Shapes R boundary`, requiring a typed-drawing witness |
| All admissible labellings at a fixed boundary | `LabelledDrawing.PlanarAtBoundary R bottom top shape` |
| Evaluated drawing | `Biset.Hom R bottom.basis top.basis`, an equivariant linear map |
| Shape replacement | `LabelledDrawing.ShapeReplaces`, comparing evaluated maps over the complete labelling fibers |

### Strands and eligible linear dots

[`Embedding.lean`](MackeyDiagrams/Embedding.lean) proves that two conjugators give the same strand exactly when their quotient belongs to the source subgroup's centralizer. A strand keeps its embedding label. Linear combinations of embeddings generally fail to be algebra homomorphisms. Addition of strings means a direct sum of bimodules, with matrices of maps as in §1.2; it does not mean a complex linear combination of embedding labels. Vectors in each strand's group algebra are already complex linear combinations.

[`Dot.lean`](MackeyDiagrams/Dot.lean) retains eligible group elements as atomic data. [`DotLabels.lean`](MackeyDiagrams/DotLabels.lean) supplies finite linear labels and their upward/downward drawings. Every supported term has its own eligibility proof. For a label `Σ c_d d`, upward evaluation is `x ↦ Σ c_d (x*d)`, and downward evaluation is `x ↦ Σ c_d (d⁻¹*x)`. Coefficients are not inverted or conjugated, and the whole sum need not be invertible. The basis formulas and ordered composition laws are proved. `DotLabel.upDrawing_identity` and `DotLabel.downDrawing_identity` prove that the coefficient-one identity label evaluates to the undotted induction or restriction identity map. This is an evaluation theorem, not a syntax reduction. Use the fully qualified `DotLabel.upDrawing` / `DotLabel.downDrawing` when the label is an explicit `Finsupp` expression.

The list-based `LabelledDrawing.upDot` and `.downDot` are equivalent presentations of finite labels. Their interpretation uses `ScopedDiagram.weightedUpDot` and `.weightedDownDot`. Erasure records one visible mark, regardless of coefficients or number of terms. [`LinearDots.lean`](MackeyDiagrams/LinearDots.lean) and [`LinearDotComposition.lean`](MackeyDiagrams/LinearDotComposition.lean) give the lower-level evaluated sums and prove composition by the ordered products of all pairs of terms. `Diagram.upDot` and `.downDot` remain the group-element special cases used in earlier endpoints.

An arbitrary group-algebra intertwiner is a different object. [`AlgebraDot.lean`](MackeyDiagrams/AlgebraDot.lean) retains the evaluator for a whole label that intertwines; its supported elements need not intertwine separately. Such a map is not silently admitted as an eligible dot by the owner-clarified shape grammar. The paper's special centralizing-algebra curl assertion (§3.1, p. 8) remains preserved for independent review, including this distinction; its original hypothesis must not be narrowed to termwise centralizing support. [`RightCurlLabels.lean`](MackeyDiagrams/RightCurlLabels.lean) retains that separate evaluator and its actual outer-embedding transport. The canonical `LabelledDrawing.rightCurlUp` instead uses an eligible finite linear label inside the actual trivalent cup/cap composite.

### Linear combinations and endomorphism algebra

[`DiagramVectorSpace.lean`](MackeyDiagrams/DiagramVectorSpace.lean) forms finite formal linear combinations of typed labelled drawings with termwise eligible dots and quotients by the kernel of evaluation. Two combinations have the same quotient class exactly when their evaluated bimodule maps agree; this does not identify the diagrams' geometric shapes. The quotient inherits its module structure over the coefficient ring (a complex vector space when the ring is `ℂ`). Addition of diagrams in a fixed hom-space is distinct from a direct sum of bimodules and its block maps.

[`DiagramAlgebra.lean`](MackeyDiagrams/DiagramAlgebra.lean) constructs the evaluated endomorphisms presented by diagrams as a unital associative subalgebra of linear endomorphisms. Multiplication composes maps in stacking order. It proves that the range of evaluation is exactly this subalgebra and provides the general kernel-quotient-to-image linear equivalence and explicit generic constructions transporting the ring and algebra structures onto such a quotient. Thus the quotient is canonically identified with the presented algebra. These transferred structures are not registered as global instances on the specific diagram quotient; the compiled presented image carries its algebra instance directly. For distinct source and target, one instead has hom-spaces and composition between compatible boundaries. [`DiagramComposition.lean`](MackeyDiagrams/DiagramComposition.lean) defines stacking directly on the quotient classes and proves it agrees with evaluated map composition, is bilinear and associative, has identity diagrams, and sends singleton drawings to their stacked drawing. [`IndexedQuotient.lean`](MackeyDiagrams/IndexedQuotient.lean) connects an indexed sum to its quotient class and proves equality of such classes exactly when their evaluations agree, without discarding the indexed drawing’s separate shape data.

[`BlockAlgebra.lean`](MackeyDiagrams/BlockAlgebra.lean) combines any selected family of boundary words with the same outer groups into one quotient algebra. Its generators are diagram classes from each selected source to each selected target, acting as blocks on the product of their evaluated modules. The free associative unital algebra on these generators is quotiented by equality of its evaluated block maps, and the quotient is algebra-equivalent to its image. Lean proves that each hom-space embeds injectively and linearly, that compatible blocks multiply by stacking, and that incompatible blocks multiply to zero. For a finite family, the global unit is the finite sum of the individual identity blocks. For an infinite family, this construction adjoins a global unit on the product; it is not asserted to equal the finite-support category algebra without that unit.

### Tensor products and generators

[`Biset.lean`](MackeyDiagrams/Biset.lean) models the basis of each strand and the balanced product of bases. The action of `(k,h)` is left multiplication by `k` and right multiplication by `h⁻¹`. Balancing identifies `[xh,y]` with `[x,hy]`. [`Linear.lean`](MackeyDiagrams/Linear.lean) linearizes a basis `X` to `X →₀ R` and descends horizontal composition through balancing. [`Balanced.lean`](MackeyDiagrams/Balanced.lean) proves the balanced bilinear universal property. [`HorizontalComposition.lean`](MackeyDiagrams/HorizontalComposition.lean) proves interchange, including independent operations on distinct strands and localized scalar operations.

[`Generators.lean`](MackeyDiagrams/Generators.lean) evaluates the induction merge by `[x,y] ↦ x*a(y)` and the restriction merge in the reverse factor order by `[y,x] ↦ a(y)*x`. Splits insert the appropriate unit. [`Trace.lean`](MackeyDiagrams/Trace.lean) implements the trace cap at arbitrary index, returning zero outside the embedded subgroup. [`Transfer.lean`](MackeyDiagrams/Transfer.lean) defines an equivariant finite-fiber transfer by summing preimages; the reverse cup is its multiplication-transfer instance. [`Associator.lean`](MackeyDiagrams/Associator.lean) and [`Unitors.lean`](MackeyDiagrams/Unitors.lean) rebracket or insert/remove empty factors.

[`Trivalent.lean`](MackeyDiagrams/Trivalent.lean) records the four all-parallel merges/splits and eight mixed junctions. Each has its actual ordered, oriented boundary type and a concrete cup/cap/merge/split expansion. The standalone orientations using a reverse cup require its finite-index evidence. A straight junction and its expanded presentation retain separate syntax; bend identities compare their evaluated maps with the index hypotheses in §3.5. No arbitrary map of the same boundary type stands in for a junction.

[`Mixed.lean`](MackeyDiagrams/Mixed.lean) evaluates multiplication crossings by `[k,h] ↦ a(k)*d*b(h)` and projection crossings by finite-fiber transfer. The `LabelledDrawing` crossing constructors allow finite eligible linear labels. Parallel crossings and arbitrary chains of marks are interpreted by merge, weighted dots, and split. [`ParallelDotChain.lean`](MackeyDiagrams/ParallelDotChain.lean) preserves each separate mark, and [`ParallelComposition.lean`](MackeyDiagrams/ParallelComposition.lean) / [`ParallelUnit.lean`](MackeyDiagrams/ParallelUnit.lean) check ordered products and the genuine identity case. Return labels are guaranteed for individual eligible group elements; a general linear label is not assumed invertible.

### Reverse cups and pointwise finite projection scopes

A standalone reverse cup requires finite subgroup index. The expanded Mackey projection has a prescribed cup/merge/dot/trace scope and can exist at infinite cup index when only finitely many terms survive on each basis input. These conditions are distinct.

[`ScopedCup.lean`](MackeyDiagrams/ScopedCup.lean) retains the actual typed tail and requires finite surviving support. [`ScopedCupEquivariance.lean`](MackeyDiagrams/ScopedCupEquivariance.lean) proves equivariance by reindexing. [`ScopedCupFinite.lean`](MackeyDiagrams/ScopedCupFinite.lean) connects finite-index scoped evaluation to the ordinary cup composite. An unrelated zero map cannot justify a standalone infinite-index cup in an admissible shape.

[`MixedProjectionExpansion.lean`](MackeyDiagrams/MixedProjectionExpansion.lean) gives the prescribed tail. [`ProjectionFiber.lean`](MackeyDiagrams/ProjectionFiber.lean) connects its surviving terms to the actual multiplication fiber. [`ProjectionDotChain.lean`](MackeyDiagrams/ProjectionDotChain.lean) supports any number of finite linear dot labels; every expanded group-element product must satisfy the finite-fiber condition. Coefficients are expanded termwise, not by an inverse of the whole label.

The projection's opening independently records a junction or a separate cup/merge, and its closing records a junction or a separate split/trace. `ScopedDiagram.expandedProjectionFrame` stores both choices. The same finite-fiber condition applies to all four presentations. The library proves equality of their evaluations while retaining the different drawings. [`MackeyOrthogonality.lean`](MackeyDiagrams/MackeyOrthogonality.lean) and [`MackeyDirectSum.lean`](MackeyDiagrams/MackeyDirectSum.lean) provide checked Mackey summand identities and the pointwise finite dependent direct-sum construction.

[`IndexedDrawing.lean`](MackeyDiagrams/IndexedDrawing.lean) represents a finite indexed sum as one shared typed scope containing a finite index set and a family of complete `LabelledDrawing` summands. `IndexedDrawing.shape` records that single scope and each summand’s planar shape. Its evaluator sums the typed summands’ linear maps, and `eval_apply` proves the pointwise evaluation formula. This keeps an indexed sum distinct from a zero-seeded nest of binary additions. The separate pointwise-finite infinite sums in the paper retain their own finiteness obligations.

### Shapes and fixed boundaries

[`DrawingShape.lean`](MackeyDiagrams/DrawingShape.lean) is the intermediate drawing erasure, not the final domain for the paper's preorder. Raw expressions can describe incompatible stacks. The canonical shape APIs are in [`PlanarShape.lean`](MackeyDiagrams/PlanarShape.lean):

- Erase all region labels, embedding values and dot coefficients while retaining ordered wire orientations, marked vertices, junction orientations and arithmetic expression scopes.
- Encode geometry as a sequence of positioned operations. Tensor association and subdivisions of identity wires contribute no vertices.
- Identify different height orders of disjoint operations. Their offsets change according to their actual input/output arities. This includes an operation independent of a scalar or sum box, while retaining the box's scope.
- Require a typed-drawing witness for each member of `LabelledDrawing.Shapes R boundary`. Both shapes in `ShapeReplaces` have the same specified bottom and top orientation sequences. Malformed raw stacks are excluded.
- At fully fixed boundary groups and strand cosets, use the entire fiber `PlanarAtBoundary`. Its interpretation transports the actual typed diagram to canonical boundary words; no arbitrary evaluator or restricted family can be substituted.

[`Boundary.lean`](MackeyDiagrams/Boundary.lean) keeps the ordered region/strand list. [`BoundaryEvaluation.lean`](MackeyDiagrams/BoundaryEvaluation.lean) proves the inverse transports. [`Replacement.lean`](MackeyDiagrams/Replacement.lean) proves that boundary transport preserves and reflects equality of evaluated maps. The concrete `ShapeReplaces` relation is proved equivalent to inclusion of attainable-map sets, and is reflexive and transitive.

Shape equality and equality of evaluated maps remain separate. In particular, an identity-labelled dot still has a visible mark, two successive marks remain two, a dot slide can change shape, and the different projection presentations can have equal evaluation. Reidemeister and bend identities are not inserted as shape-equality axioms.

[`IndexedDrawing.lean`](MackeyDiagrams/IndexedDrawing.lean) retains one finite indexed-sum scope and every summand's shape. [`PointwiseIndexedDrawing.lean`](MackeyDiagrams/PointwiseIndexedDrawing.lean) also permits an arbitrary index type when only finitely many summands act nontrivially on each input. Its `shape` retains the full indexed family independently of the input and of coefficients, while `evalAt` and `eval` give its pointwise sum and resulting linear map. [`PointwiseIndexedBimodule.lean`](MackeyDiagrams/PointwiseIndexedBimodule.lean) proves that this map commutes with the boundary actions and packages it as `evalHom`. A pointwise-finite infinite sum is not automatically a finite formal combination or an element of the finite-combination quotient algebra. The scope-preserving Mackey cancellation and Mackey identity statements have passed independent review and Lean checks.

### Verification and remaining work

The article's published PDF was revised after `source/mackey-bimodules.pdf` was archived. The current published revision has SHA-256 `e7712567f611d36713fb4dbf45f8b1aeefea022ea2e403462529850ebe290cc8`; the archive has SHA-256 `bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2`. Some historical translation notes say the published PDF matched the project copy byte for byte; that is not a current-file identity claim. The affected notes and correction are recorded in [`source-provenance-correction-20261128.json`](evidence/source-provenance-correction-20261128.json). Archive and published page references must be checked against the copy named.

A sentence in the earlier revised section 1.2 incorrectly described horizontal tensor product as bilinear on maps over the common group algebra. The current article instead states complex-bilinearity on maps and tensoring of bimodules over that algebra. The reason and scope are recorded in [`horizontal-bilinearity-defect-20261128.json`](evidence/horizontal-bilinearity-defect-20261128.json).

[`LanguageChecks.lean`](MackeyDiagrams/LanguageChecks.lean) checks all twelve trivalent boundary orientations, uniform linear labels, zero labels, termwise downward inverses, the two-dot parallel frame, disjoint-height interchange and its evaluation, identity-dot shape distinction, explicit curl junctions, and distinct projection presentations with equal evaluation. The new language modules build against the pinned Lean and Mathlib. The focused axiom audit is retained under `.lake/lean-workflow-supervision/language-audit-20261127/`.

These library checks do not grant registered proof credit to the 153 article endpoints. The initial translation recheck after the owner clarification has completed, with suppliers checked before consumers; subsequent reviews found additional indexed-scope issues, and the affected corrections are being reviewed and re-proved. That initial recheck is not a guarantee that no other translation needs repair. Statements that describe arbitrary algebra intertwiners, explicitly restrict to group-element dots, or quantify over diagram shapes require particular attention. The source inventory and previous evidence remain preserved. The project remains a draft until the workflow's compilation, allowed-axiom checks, dependency audit and full closeout succeed.
