import MackeyDiagrams
import Proofs.RightUpReidemeisterCurl
import Proofs.RightDownReidemeisterCurl
import Proofs.LeftUpReidemeisterCurl
import Proofs.LeftDownReidemeisterCurl

universe u

open MackeyDiagrams in
private theorem reidemeisterOne_leftUpExpansion {U : Type u} [Group U]
    {K H G : Subgroup U} (a : ConjEmbedding H G) (d : ConjEmbedding K H) :
  let up := Word.up d
  let loopDown := Word.down a
  let loopUp := Word.up a
  let straight := Diagram.id (R := Complex) up
  let cup := Diagram.horizontal
    (Diagram.ordinaryCup a) straight
  let middle := Diagram.horizontal
    (Diagram.id loopDown)
    (Diagram.vertical
      (Diagram.mergeUp a d)
      (Diagram.splitUp a d))
  let cap := Diagram.horizontal
    (Diagram.traceCap a) straight
  let expanded :=
    Diagram.vertical
      (Diagram.insertLeftUnit up)
      (Diagram.vertical cup
        (Diagram.vertical
          (Diagram.associate loopDown loopUp up)
          (Diagram.vertical middle
            (Diagram.vertical
              (Diagram.unassociate loopDown loopUp up)
              (Diagram.vertical cap
                (Diagram.leftUnit up))))))
  let lower := LabelledDrawing.trivalent (R := Complex) (TrivalentVertex.upToDownUp a d)
  let upper := LabelledDrawing.trivalent (R := Complex) (TrivalentVertex.downUpToUp a d)
  (lower.vertical upper).interpret.eval = expanded.eval := by
  intro up loopDown loopUp straight cup middle cap expanded lower upper
  -- Alphabeta Math's tensor product proof uses balance in Step 2.1,
  -- quotient descent in Step 3.1, and generation by elementary tensors
  -- in Step 4.1. Here the middle algebra is a complex group algebra.
  -- The project linearizes the balanced biset, and horizontal_vertical
  -- establishes interchange by evaluating the two composites on the
  -- classes of elementary pairs. The left tensor factor is an identity.
  -- https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products
  have interchange :
      (Biset.Hom.id (R := Complex) (Biset.restriction a)).horizontal
          ((Generator.mergeUp Complex a d).vertical (Generator.splitUp Complex a d)) =
        ((Biset.Hom.id (Biset.restriction a)).horizontal (Generator.mergeUp Complex a d)).vertical
          ((Biset.Hom.id (Biset.restriction a)).horizontal (Generator.splitUp Complex a d)) := by
    rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  simp only [lower, upper, expanded, middle, cap, cup, straight, up, loopDown, loopUp,
    LabelledDrawing.interpret, ScopedDiagram.eval, TrivalentVertex.expand, BentVertex.expand,
    Diagram.traceCapOnLeft, Diagram.eval, Word.basis, interchange, Biset.Hom.vertical_assoc]

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
  -- Xiao, Theorem 4.1, (4.1)–(4.4), appears on p. 14 of the
  -- archived original PDF and p. 16 of the revised published PDF.
  -- The proof is on pp. 15 and 17 respectively. The PDF hashes differ.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  intro U inst K H G δ α hδ hα d a S
  refine ⟨?_, ?_, ?_, ?_⟩
  -- The K-loops use the finite index of the image of δ in H.
  -- Each reverse cup summand contributes the identity, giving the index.
  -- The G-loops use the ordinary cup and trace, with coefficient one
  -- and arbitrary index of the image of α in G.
  · exact RightUpReidemeisterCurl K H G δ α hδ hα
  · exact RightDownReidemeisterCurl K H G δ α hδ hα
  · -- The lower junction expands to ordinary cup and merge, and the
    -- upper to split and trace cap. The supplier groups the middle maps
    -- into one horizontal composite. Interchange and vertical associativity
    -- identify the evaluations at the same H–K boundary.
    intro curl straight
    exact (reidemeisterOne_leftUpExpansion a d).trans (LeftUpReidemeisterCurl K H G δ α hδ hα)
  · exact LeftDownReidemeisterCurl K H G δ α hδ hα

#print axioms ReidemeisterOne
