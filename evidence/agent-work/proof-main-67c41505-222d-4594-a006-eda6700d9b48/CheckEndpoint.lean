import MackeyDiagrams
import Proofs.RightCurlAndDotSlide

universe u

theorem DotBelowInsideAboveRightCurl : (
∀ {U : Type u} [Group U] (K H G : Subgroup U),
  let liftOuterDot :=
    fun {a b : MackeyDiagrams.ConjEmbedding H G}
      (inner : MackeyDiagrams.ConjEmbedding K H) (d : MackeyDiagrams.Dot a b) =>
      (⟨MackeyDiagrams.Dot.element d,
        fun k => MackeyDiagrams.Dot.intertwines d
          (MackeyDiagrams.ConjEmbedding.toHom inner k)⟩ :
        MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a inner)
          (MackeyDiagrams.ConjEmbedding.comp b inner))
  (∀ (δ α : U)
      (hδ : ∀ k : K, δ * (k : U) * δ⁻¹ ∈ H)
      (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G),
    let loop := MackeyDiagrams.ConjEmbedding.ofConjugator δ hδ
    let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
    let S := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom loop)
    ∀ finite : Subgroup.FiniteIndex S,
      let lower := fun p : MackeyDiagrams.ConjEmbedding H G =>
        MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
          (MackeyDiagrams.TrivalentVertex.upToUpDown p loop finite)
      let upper := fun p : MackeyDiagrams.ConjEmbedding H G =>
        MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
          (MackeyDiagrams.TrivalentVertex.upDownToUp p loop)
      let curl := fun p : MackeyDiagrams.ConjEmbedding H G =>
        MackeyDiagrams.LabelledDrawing.vertical (lower p) (upper p)
      let straight := MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up a))
      let scaledStraight :=
        MackeyDiagrams.LabelledDrawing.scale (Subgroup.index S : Complex) straight
      ((∀ k : K, (MackeyDiagrams.ConjEmbedding.toHom loop k : U) = (k : U)) →
        Subgroup.index S = Subgroup.index (Subgroup.comap (Subgroup.subtype H) K)) ∧
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret (curl a)) =
        MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret scaledStraight) ∧
      (∀ (β : U)
          (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G)
          (hd : α * β⁻¹ ∈ G),
        let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
        let d : MackeyDiagrams.Dot a b :=
          MackeyDiagrams.Dot.ofRepresentatives α β (fun _ => rfl) (fun _ => rfl) hd
        let dot := MackeyDiagrams.DotLabel.upDrawing (Finsupp.single d (1 : Complex))
        let loopIdentity := MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.down loop))
        let insideDot := MackeyDiagrams.DotLabel.upDrawing
          (Finsupp.single (liftOuterDot loop d) (1 : Complex))
        let below := MackeyDiagrams.LabelledDrawing.vertical dot (curl b)
        let inside := MackeyDiagrams.LabelledDrawing.vertical (lower a)
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.horizontal insideDot loopIdentity) (upper b))
        let above := MackeyDiagrams.LabelledDrawing.vertical (curl a) dot
        let scaledDot := MackeyDiagrams.LabelledDrawing.scale (Subgroup.index S : Complex) dot
        MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret below) =
          MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret scaledDot) ∧
        MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret inside) =
          MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret scaledDot) ∧
        MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret above) =
          MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret scaledDot)))
) :=
(
by
  -- Xiao, Proposition 3.1 and its unnumbered curl proof, archived PDF
  -- pp. 7–8 and published 28 November revision p. 10.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- The paper evaluates the two junctions using a coset sum and moves
  -- right multiplication past the inner factors by intertwining.
  -- Project the registered supplier's first conjunct to reuse that
  -- calculation. It uses the same finite-index image, coefficient-one
  -- dot restricted along the same inner embedding, and three typed
  -- placements. Each equality compares evaluations at a fixed boundary.
  intro U inst K H G
  exact (RightCurlAndDotSlide K H G).1
)

#print axioms DotBelowInsideAboveRightCurl
