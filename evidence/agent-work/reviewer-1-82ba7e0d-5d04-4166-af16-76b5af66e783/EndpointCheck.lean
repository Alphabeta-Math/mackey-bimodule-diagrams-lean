import MackeyDiagrams.DotLabels
import Mathlib.Basic.Complex.Basic

universe u

#check (∀ {U : Type*} [Group U] (H G : Subgroup U) (α β : U)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G)
    (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G),
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  ∀ z : MackeyDiagrams.DotLabel Complex a b,
    let zDual : MackeyDiagrams.DotLabel Complex b a :=
      Finsupp.mapDomain MackeyDiagrams.Dot.inverse z
    let rightZ := MackeyDiagrams.DotLabel.upDrawing z
    let leftZ := MackeyDiagrams.DotLabel.downDrawing zDual
    let rightDual := MackeyDiagrams.DotLabel.upDrawing zDual
    let leftDual := MackeyDiagrams.DotLabel.downDrawing z
    let idUpA := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up a))
    let idUpB := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up b))
    let idDownA := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.down a))
    let idDownB := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.down b))
    let multiplicationLeft := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal rightZ idDownB)
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.multiplicationCap b))
    let multiplicationRight := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal idUpA leftZ)
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.multiplicationCap a))
    let traceLeft := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal leftDual idUpB)
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.traceCap b))
    let traceRight := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal idDownA rightDual)
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.traceCap a))
    let ordinaryLeft := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.ordinaryCup a))
      (MackeyDiagrams.LabelledDrawing.horizontal leftDual idUpA)
    let ordinaryRight := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.ordinaryCup b))
      (MackeyDiagrams.LabelledDrawing.horizontal idDownB rightDual)
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret multiplicationLeft) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret multiplicationRight) ∧
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret traceLeft) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret traceRight) ∧
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret ordinaryLeft) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret ordinaryRight) ∧
    (∀ (finiteA : Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a)))
       (finiteB : Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom b))),
      let reverseLeft := MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.reverseCup a finiteA))
        (MackeyDiagrams.LabelledDrawing.horizontal rightZ idDownA)
      let reverseRight := MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.reverseCup b finiteB))
        (MackeyDiagrams.LabelledDrawing.horizontal idUpB leftZ)
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret reverseLeft) =
        MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret reverseRight)) : Prop)
