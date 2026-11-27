import ShapePart
import Proofs.DotSlidePreorderNotSymmetric

open MackeyDiagrams
open CaseTwoAudit

#check DotSlidePreorderProof.factor_rightCode
#check DotSlidePreorderProof.empty_geometry_atBoundary
#print axioms DotSlidePreorderProof.empty_geometry_atBoundary

theorem structure_connection {p q : Word G F}
    (x : MackeyDiagrams.LabelledDrawing Complex p q)
    (h : MackeyDiagrams.PlanarCode.encode x.erase.geometry = []) :
    ∃ he : p.boundary = q.boundary,
      x.interpret.atBoundary.eval =
        DotSlideStructuralCoherence.transport he
          (MackeyDiagrams.Biset.Hom.id (R := Complex) p.boundary.word.basis) :=
  DotSlidePreorderProof.empty_geometry_atBoundary x h

#print axioms structure_connection
