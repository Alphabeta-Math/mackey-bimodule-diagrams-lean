import Proofs.EvaluationWithOneProjection
import Proofs.ExpansionIntoRightDiagrams
import MackeyDiagrams.PlanarShape
import MackeyDiagrams.BoundaryEvaluation
import MackeyDiagrams.PointwiseIndexedDrawing
import MackeyDiagrams.MixedIdentities
import Mathlib.GroupTheory.Index

#check MackeyDiagrams.PlanarCode.Equivalent.exchange
#check MackeyDiagrams.PlanarCode.Equivalent.context
#check MackeyDiagrams.PlanarCode.length_eq
#check Quotient.exact
#check MackeyDiagrams.LabelledDrawing.PlanarAtBoundary
#check MackeyDiagrams.LabelledDrawing.PlanarAtBoundary.interpret
#check MackeyDiagrams.Word.eval_reorderToFrom
#check MackeyDiagrams.Word.eval_reorderFromTo
#check MackeyDiagrams.Biset.Hom.transferBasis_sum
#check MackeyDiagrams.Biset.associateBasisEquiv
#check MackeyDiagrams.Generator.mixedEquiv
#check MackeyDiagrams.ScopedDiagram.eval_linearCombination_apply
#check MackeyDiagrams.PointwiseIndexedDrawing.evalAt_def
#check MackeyDiagrams.PointwiseIndexedDrawing.eval_apply
#print axioms MackeyDiagrams.PointwiseIndexedDrawing.eval
#print axioms EvaluationWithOneProjection
#print axioms ExpansionIntoRightDiagrams
#check Finsupp.induction_linear
#check Subgroup.index_top

open MackeyDiagrams in
#eval PlanarCode.encode <|
  .vertical (.horizontal (.straight [true]) (.vertex .mixedProjection))
    (.vertical (.horizontal (.vertex .parallelUp) (.straight [false]))
      (.horizontal (.straight [true]) (.vertex .mixedMultiplication)))
