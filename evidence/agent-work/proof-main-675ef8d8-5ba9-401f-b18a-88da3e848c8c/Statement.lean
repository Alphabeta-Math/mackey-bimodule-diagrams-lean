import MackeyDiagrams
import Proofs.InductionMergeDotSlide
import Proofs.RestrictionMergeDotSlide

def movingMergeStatement : Prop :=
∀ {U : Type*} [Group U] (K H G : Subgroup U)
    (γ : MackeyDiagrams.ConjEmbedding H G)
    (α : MackeyDiagrams.ConjEmbedding K H)
    (target : MackeyDiagrams.ConjEmbedding K G)
    (D : MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp γ α) target),
  let singleton := fun {A B : Subgroup U} {a b : MackeyDiagrams.ConjEmbedding A B}
      (d : MackeyDiagrams.Dot a b) =>
    (Finsupp.single d (1 : Complex) : MackeyDiagrams.DotLabel Complex a b)
  let upInput := MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up γ)
    (MackeyDiagrams.Word.up α)
  let downInput := MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.down α)
    (MackeyDiagrams.Word.down γ)
  let mergedUp := MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
      (MackeyDiagrams.TrivalentVertex.mergeUp γ α))
    (MackeyDiagrams.DotLabel.upDrawing (singleton D))
  let mergedDown := MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
      (MackeyDiagrams.TrivalentVertex.mergeDown γ α))
    (MackeyDiagrams.DotLabel.downDrawing (singleton D))
  let matchesUp := fun {out : MackeyDiagrams.ConjEmbedding K G} (h : out = target)
      (branch : MackeyDiagrams.LabelledDrawing Complex upInput (MackeyDiagrams.Word.up out)) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret
        (show MackeyDiagrams.LabelledDrawing Complex upInput (MackeyDiagrams.Word.up target)
          from h ▸ branch)) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret mergedUp)
  let matchesDown := fun {out : MackeyDiagrams.ConjEmbedding K G} (h : out = target)
      (branch : MackeyDiagrams.LabelledDrawing Complex downInput (MackeyDiagrams.Word.down out)) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret
        (show MackeyDiagrams.LabelledDrawing Complex downInput (MackeyDiagrams.Word.down target)
          from h ▸ branch)) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret mergedDown)
  let inImage := MackeyDiagrams.Dot.element D ∈
    MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom γ)
  ((∃ (β : MackeyDiagrams.ConjEmbedding K H) (e : MackeyDiagrams.Dot α β)
        (h : MackeyDiagrams.ConjEmbedding.comp γ β = target),
      matchesUp h (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.ordinary
            (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up γ)))
          (MackeyDiagrams.DotLabel.upDrawing (singleton e)))
        (MackeyDiagrams.LabelledDrawing.trivalent
          (MackeyDiagrams.TrivalentVertex.mergeUp γ β)))) ↔ inImage) ∧
  ((∃ (β : MackeyDiagrams.ConjEmbedding K H) (e : MackeyDiagrams.Dot α β)
        (h : MackeyDiagrams.ConjEmbedding.comp γ β = target),
      matchesDown h (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.DotLabel.downDrawing (singleton e))
          (MackeyDiagrams.LabelledDrawing.ordinary
            (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.down γ))))
        (MackeyDiagrams.LabelledDrawing.trivalent
          (MackeyDiagrams.TrivalentVertex.mergeDown γ β)))) ↔ inImage) ∧
  (∃ (γ' : MackeyDiagrams.ConjEmbedding H G) (d : MackeyDiagrams.Dot γ γ')
      (h : MackeyDiagrams.ConjEmbedding.comp γ' α = target),
    matchesUp h (MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.DotLabel.upDrawing (singleton d))
        (MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up α))))
      (MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.mergeUp γ' α))) ∧
    matchesDown h (MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.down α)))
        (MackeyDiagrams.DotLabel.downDrawing (singleton d)))
      (MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.mergeDown γ' α))))
