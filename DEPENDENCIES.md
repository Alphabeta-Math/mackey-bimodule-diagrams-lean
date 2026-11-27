# Full dependency graph

Every active planned endpoint and its immediate dependencies. [Exact proof suppliers and verification](proof-graph.json).

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

Included prerequisite packages:

- [prerequisites](prerequisites/DEPENDENCIES.md) · [Exact proof graph](prerequisites/proof-graph.json)
