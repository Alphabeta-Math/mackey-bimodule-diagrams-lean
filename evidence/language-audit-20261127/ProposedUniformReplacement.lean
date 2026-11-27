import MackeyDiagrams.PlanarShape
import Mathlib.Basic.Complex.Basic

theorem ProposedUniformReplacement :
∀ {U : Type*} [Group U], ∀ boundary : List Bool × List Bool,
  (∀ s t : MackeyDiagrams.LabelledDrawing.Shapes (U := U) Complex boundary,
    MackeyDiagrams.LabelledDrawing.ShapeReplaces s t ↔
      ∀ (A B : Subgroup U) (p q : MackeyDiagrams.Boundary A B),
        MackeyDiagrams.ScopedDiagram.attainable
          (fun v (label : MackeyDiagrams.LabelledDrawing.PlanarAtBoundary Complex p q v) => label.interpret) s.val ⊆
        MackeyDiagrams.ScopedDiagram.attainable
          (fun v (label : MackeyDiagrams.LabelledDrawing.PlanarAtBoundary Complex p q v) => label.interpret) t.val) ∧
  (∀ s : MackeyDiagrams.LabelledDrawing.Shapes (U := U) Complex boundary,
    MackeyDiagrams.LabelledDrawing.ShapeReplaces s s) ∧
  (∀ s t z : MackeyDiagrams.LabelledDrawing.Shapes (U := U) Complex boundary,
    MackeyDiagrams.LabelledDrawing.ShapeReplaces s t →
    MackeyDiagrams.LabelledDrawing.ShapeReplaces t z →
    MackeyDiagrams.LabelledDrawing.ShapeReplaces s z) := by
  intro U inst boundary
  exact ⟨MackeyDiagrams.LabelledDrawing.shapeReplaces_iff_attainable_subset,
    MackeyDiagrams.LabelledDrawing.shapeReplaces_refl,
    fun _ _ _ => MackeyDiagrams.LabelledDrawing.shapeReplaces_trans⟩

#print axioms ProposedUniformReplacement
