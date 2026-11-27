import MackeyDiagrams
import Proofs.RightUpReidemeisterCurl
import Proofs.RightDownReidemeisterCurl
import Proofs.LeftUpReidemeisterCurl
import Proofs.LeftDownReidemeisterCurl

universe u

theorem ReidemeisterOne : (
∀ {U : Type u} [Group U] (K H G : Subgroup U) (δ α : U)
    (hδ : ∀ k : K, δ * (k : U) * δ⁻¹ ∈ H)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G),
  let d := MackeyDiagrams.ConjEmbedding.ofConjugator δ hδ
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let S := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom d)
  (∀ finite : Subgroup.FiniteIndex S,
    let curl := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
        (MackeyDiagrams.TrivalentVertex.upToUpDown a d finite))
      (MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.upDownToUp a d))
    let straight := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up a))
    let scaled := MackeyDiagrams.LabelledDrawing.scale (Subgroup.index S : Complex) straight
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret curl) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret scaled)) ∧
  (let curl := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
        (MackeyDiagrams.TrivalentVertex.downToDownUp a d))
      (MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.downUpToDown a d))
   let straight := MackeyDiagrams.LabelledDrawing.ordinary
     (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.down d))
   MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret curl) =
     MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret straight)) ∧
  (let curl := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
        (MackeyDiagrams.TrivalentVertex.upToDownUp a d))
      (MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.downUpToUp a d))
   let straight := MackeyDiagrams.LabelledDrawing.ordinary
     (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up d))
   MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret curl) =
     MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret straight)) ∧
  (∀ finite : Subgroup.FiniteIndex S,
    let curl := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
        (MackeyDiagrams.TrivalentVertex.downToUpDown a d finite))
      (MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.upDownToDown a d))
    let straight := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.down a))
    let scaled := MackeyDiagrams.LabelledDrawing.scale (Subgroup.index S : Complex) straight
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret curl) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret scaled))
) :=
by
  intro U inst K H G δ α hδ hα
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact RightUpReidemeisterCurl K H G δ α hδ hα
  · exact RightDownReidemeisterCurl K H G δ α hδ hα
  · let d := MackeyDiagrams.ConjEmbedding.ofConjugator δ hδ
    let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
    have hInterchange :
        (MackeyDiagrams.Biset.Hom.id (R := Complex) (MackeyDiagrams.Word.down a).basis).horizontal ((MackeyDiagrams.Generator.mergeUp Complex a d).vertical
              (MackeyDiagrams.Generator.splitUp Complex a d))
        = ((MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Word.down a).basis).horizontal
            (MackeyDiagrams.Generator.mergeUp Complex a d)).vertical
          ((MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Word.down a).basis).horizontal
            (MackeyDiagrams.Generator.splitUp Complex a d)) := by
      rw [MackeyDiagrams.Biset.Hom.horizontal_vertical, MackeyDiagrams.Biset.Hom.id_vertical]
    have h := LeftUpReidemeisterCurl K H G δ α hδ hα
    simpa only [MackeyDiagrams.LabelledDrawing.interpret, MackeyDiagrams.ScopedDiagram.eval,
      MackeyDiagrams.TrivalentVertex.expand, MackeyDiagrams.BentVertex.expand,
      MackeyDiagrams.Diagram.traceCapOnLeft, MackeyDiagrams.Diagram.eval, hInterchange,
      MackeyDiagrams.Biset.Hom.vertical_assoc] using h
  · exact LeftDownReidemeisterCurl K H G δ α hδ hα

#print axioms ReidemeisterOne
