import Mathlib.Basic.Complex.Basic
import MackeyDiagrams.Diagram

set_option autoImplicit false
universe u

def translatedEndpoint : Prop :=
  ∀ {U : Type u} [Group U] (H G : Subgroup U) (α β : U)
      (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G)
      (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G),
    let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
    let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
    let upA := MackeyDiagrams.Word.up a
    let downA := MackeyDiagrams.Word.down a
    let upB := MackeyDiagrams.Word.up b
    let downB := MackeyDiagrams.Word.down b
    let idUp := MackeyDiagrams.Diagram.id (R := Complex) upA
    let idDown := MackeyDiagrams.Diagram.id (R := Complex) downB
    let ordinaryUp :=
      MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.insertRightUnit upA)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal idUp (MackeyDiagrams.Diagram.ordinaryCup a))
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.unassociate upA downA upA)
            (MackeyDiagrams.Diagram.vertical
              (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.multiplicationCap a) idUp)
              (MackeyDiagrams.Diagram.leftUnit upA))))
    let ordinaryDown :=
      MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.insertLeftUnit downB)
        (MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.ordinaryCup b) idDown)
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.associate downB upB downB)
            (MackeyDiagrams.Diagram.vertical
              (MackeyDiagrams.Diagram.horizontal idDown (MackeyDiagrams.Diagram.multiplicationCap b))
              (MackeyDiagrams.Diagram.rightUnit downB))))
    MackeyDiagrams.Diagram.eval ordinaryUp = MackeyDiagrams.Diagram.eval idUp ∧
    MackeyDiagrams.Diagram.eval ordinaryDown = MackeyDiagrams.Diagram.eval idDown ∧
    (∀ finiteA : Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom a)),
      let reverseUp :=
        MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.insertLeftUnit upA)
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.reverseCup a finiteA) idUp)
            (MackeyDiagrams.Diagram.vertical
              (MackeyDiagrams.Diagram.associate upA downA upA)
              (MackeyDiagrams.Diagram.vertical
                (MackeyDiagrams.Diagram.horizontal idUp (MackeyDiagrams.Diagram.traceCap a))
                (MackeyDiagrams.Diagram.rightUnit upA))))
      MackeyDiagrams.Diagram.eval reverseUp = MackeyDiagrams.Diagram.eval idUp) ∧
    (∀ finiteB : Subgroup.FiniteIndex (MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom b)),
      let reverseDown :=
        MackeyDiagrams.Diagram.vertical
          (MackeyDiagrams.Diagram.insertRightUnit downB)
          (MackeyDiagrams.Diagram.vertical
            (MackeyDiagrams.Diagram.horizontal idDown (MackeyDiagrams.Diagram.reverseCup b finiteB))
            (MackeyDiagrams.Diagram.vertical
              (MackeyDiagrams.Diagram.unassociate downB upB downB)
              (MackeyDiagrams.Diagram.vertical
                (MackeyDiagrams.Diagram.horizontal (MackeyDiagrams.Diagram.traceCap b) idDown)
                (MackeyDiagrams.Diagram.leftUnit downB))))
      MackeyDiagrams.Diagram.eval reverseDown = MackeyDiagrams.Diagram.eval idDown)
