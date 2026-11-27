import MackeyDiagrams
import Proofs.FiniteIndexReverseAdjunction
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 2000000
universe u

theorem LeftDownReidemeisterCurl : (∀ {U : Type u} [Group U] (K H G : Subgroup U) (δ α : U)
  (hδ : ∀ k : K, δ * (k : U) * δ⁻¹ ∈ H)
  (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G),
let d := MackeyDiagrams.ConjEmbedding.ofConjugator δ hδ
let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
let S := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom d)
∀ finite : Subgroup.FiniteIndex S,
  let curl := MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
      (MackeyDiagrams.TrivalentVertex.downToUpDown a d finite))
    (MackeyDiagrams.LabelledDrawing.trivalent
      (MackeyDiagrams.TrivalentVertex.upDownToDown a d))
  let straight := MackeyDiagrams.LabelledDrawing.ordinary
    (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.down a))
  let scaled := MackeyDiagrams.LabelledDrawing.scale (Subgroup.index S : Complex) straight
  MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret curl) =
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret scaled)) :=
(by
  intro U inst K H G δ α hδ hα d a S finite curl straight scaled
  -- Ian Xiao, Theorem 4.1, (4.4). The archived project PDF has the
  -- figure on p. 14 and its proof on p. 15. The revised published PDF
  -- has the figure on p. 16 and its proof on p. 17.
  -- The plan supplies no Alphabeta Math item for this endpoint.
  -- Steps 1–3 follow the calculation in the paper's §4.
  -- Step 1 (expand the two junctions): expose the reverse cup and the
  -- multiplication cap. The given finite index is for d.toHom.range in H.
  -- The earlier ReviewedLeftDownCurl calculation uses the expanded Diagram.
  -- Here interpret the actual trivalent drawings and reassociate only their
  -- evaluated vertical maps to recover that calculation.
  simp only [curl, scaled, straight, MackeyDiagrams.LabelledDrawing.interpret,
    MackeyDiagrams.ScopedDiagram.eval, MackeyDiagrams.TrivalentVertex.expand,
    MackeyDiagrams.Diagram.eval, MackeyDiagrams.Word.basis,
    MackeyDiagrams.Biset.Hom.vertical_assoc]
  -- Step 2 (compose the restriction maps): cancel the merge and split
  -- between the two tensor rebracketings using the down merge–split
  -- identity from InductionRestrictionMergesAndSplits.
  have hmid :
      (MackeyDiagrams.Generator.mergeDown Complex a d).vertical
        (MackeyDiagrams.Generator.splitDown Complex a d) =
      MackeyDiagrams.Biset.Hom.id ((MackeyDiagrams.Biset.restriction d).tensor
        (MackeyDiagrams.Biset.restriction a)) :=
    (InductionRestrictionMergesAndSplits K H G α δ hα hδ).2.2.2.2.2.1
  rw [← MackeyDiagrams.Biset.Hom.vertical_assoc
      ((MackeyDiagrams.Biset.Hom.id _).horizontal
        (MackeyDiagrams.Generator.mergeDown Complex a d)),
    MackeyDiagrams.Biset.Hom.horizontal_vertical,
    MackeyDiagrams.Biset.Hom.id_vertical, hmid, MackeyDiagrams.Biset.Hom.horizontal_id,
    MackeyDiagrams.Biset.Hom.id_vertical]
  rw [← MackeyDiagrams.Biset.Hom.vertical_assoc
      (MackeyDiagrams.Biset.associate (MackeyDiagrams.Biset.induction d)
        (MackeyDiagrams.Biset.restriction d) (MackeyDiagrams.Biset.restriction a) Complex),
    MackeyDiagrams.Biset.associate_unassociate, MackeyDiagrams.Biset.Hom.id_vertical]
  -- Step 3 (evaluate the finite coset sum): count the fibers of multiplication
  -- in H before acting on the down-strand. The transfer theorem counts the
  -- same right cosets as the paper's transversal and sends each term to the
  -- same generator. This replaces the explicit transversal calculation in
  -- FiniteIndexReverseAdjunction. The resulting scalar acts on the outer
  -- strand by horizontal interchange and the left unitor.
  have hcup :
      (MackeyDiagrams.Generator.reverseCup Complex d finite).vertical
        (MackeyDiagrams.Generator.multiplicationCap Complex d) =
      (MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Biset.regular H)).scale
        (S.index : Complex) :=
    MackeyDiagrams.Diagram.reverseCup_multiplicationCap d finite
  rw [← MackeyDiagrams.Biset.Hom.vertical_assoc
      ((MackeyDiagrams.Generator.reverseCup Complex d finite).horizontal
        (MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Biset.restriction a))),
    MackeyDiagrams.Biset.Hom.horizontal_vertical, MackeyDiagrams.Biset.Hom.id_vertical,
    hcup, MackeyDiagrams.Biset.Hom.horizontal_scale_left,
    MackeyDiagrams.Biset.Hom.horizontal_id, MackeyDiagrams.Biset.Hom.vertical_scale_left,
    MackeyDiagrams.Biset.Hom.id_vertical, MackeyDiagrams.Biset.Hom.vertical_scale_right,
    MackeyDiagrams.Biset.insertLeftUnit_leftUnit])

#print axioms LeftDownReidemeisterCurl
