import FirstStage
import FactorPart

namespace CaseTwoAudit

open MackeyDiagrams

/-- Normalize stage one of the exact left Case 2 drawing. -/
theorem first_stage_at_boundary {p q : Word G F} (drawing : LabelledDrawing Complex p q)
    (h : PlanarCode.encode drawing.erase.geometry = [.vertex 0 .mixedProjection])
    (hp : p.boundary = bottom.boundary) :
    ∃ (B : Subgroup U) (r : ConjEmbedding B G) (s : ConjEmbedding B D)
      (xs : List (Complex × ProjectionDot.Mixed a b r s))
      (hq : q.boundary = (tensor (tensor (up r) (down s)) (up c)).boundary),
      CaseTwoFirstStage.castBoundary hp hq drawing.interpret.atBoundary.eval =
        (((LabelledDrawing.compactProjection a b r s xs).horizontal
          (drawId (up c))).interpret.atBoundary).eval :=
  CaseTwoFirstStage.normalizeFirst a b c drawing h hp

end CaseTwoAudit

#check CaseTwoFactor.factor_left
#print axioms CaseTwoAudit.first_stage_at_boundary
#print axioms CaseTwoFirstStage.eval_collectProjection
