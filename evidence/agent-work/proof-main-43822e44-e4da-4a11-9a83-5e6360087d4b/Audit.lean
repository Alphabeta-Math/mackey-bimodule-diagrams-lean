import MackeyDiagrams
import Proofs.GroupElementDotCriterion
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 2000000

theorem FixedBoundaryReplacementPreorder : (∀ {U : Type*} [Group U], ∀ boundary : List Bool × List Bool,
  (∀ s t : MackeyDiagrams.LabelledDrawing.Shapes (U := U) Complex boundary,
    MackeyDiagrams.LabelledDrawing.ShapeReplaces s t ↔
      ∀ (A B : Subgroup U) (p q : MackeyDiagrams.Boundary A B),
        MackeyDiagrams.ScopedDiagram.attainable
          (fun v (label : MackeyDiagrams.LabelledDrawing.PlanarAtBoundary Complex p q v) => MackeyDiagrams.LabelledDrawing.PlanarAtBoundary.interpret label) (Subtype.val s) ⊆
        MackeyDiagrams.ScopedDiagram.attainable
          (fun v (label : MackeyDiagrams.LabelledDrawing.PlanarAtBoundary Complex p q v) => MackeyDiagrams.LabelledDrawing.PlanarAtBoundary.interpret label) (Subtype.val t)) ∧
  (∀ s : MackeyDiagrams.LabelledDrawing.Shapes (U := U) Complex boundary,
    MackeyDiagrams.LabelledDrawing.ShapeReplaces s s) ∧
  (∀ s t z : MackeyDiagrams.LabelledDrawing.Shapes (U := U) Complex boundary,
    MackeyDiagrams.LabelledDrawing.ShapeReplaces s t →
    MackeyDiagrams.LabelledDrawing.ShapeReplaces t z →
    MackeyDiagrams.LabelledDrawing.ShapeReplaces s z)) :=
(by
  -- Xiao states the replacement criterion in §3.3 on p. 10 of the archived
  -- original PDF and p. 12 of the revised published PDF. The two PDFs have
  -- different hashes and give the same criterion in this passage. No numbered
  -- Alphabeta Math steps are available for this endpoint.
  intro U _ boundary
  refine ⟨?_, ?_, ?_⟩
  · -- At each fixed choice of boundary groups and strand cosets, the fiber
    -- contains every typed labelling of the given shape. Matching their
    -- evaluations is range inclusion.
    intro s t
    exact MackeyDiagrams.LabelledDrawing.shapeReplaces_iff_attainable_subset s t
  · -- The existing labelling witnesses its own replacement.
    intro s
    exact MackeyDiagrams.LabelledDrawing.shapeReplaces_refl s
  · -- Compose the two matching labelling witnesses at the same boundary.
    -- Identity-dot evaluation applies to particular drawings. Here the
    -- PlanarAtBoundary fibers already handle all allowed dot labels.
    intro s t z hst htz
    exact MackeyDiagrams.LabelledDrawing.shapeReplaces_trans hst htz)

#print axioms FixedBoundaryReplacementPreorder
