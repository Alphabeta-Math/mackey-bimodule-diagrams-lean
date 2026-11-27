import MackeyDiagrams
import Proofs.InductionRestrictionAdjunction
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 2000000

universe u

theorem RightDownReidemeisterCurl : (∀ {U : Type u} [Group U] (K H G : Subgroup U) (δ α : U)
    (hδ : ∀ k : K, δ * (k : U) * δ⁻¹ ∈ H)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G),
  let d := MackeyDiagrams.ConjEmbedding.ofConjugator δ hδ
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let curl := MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
      (MackeyDiagrams.TrivalentVertex.downToDownUp a d))
    (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
      (MackeyDiagrams.TrivalentVertex.downUpToDown a d))
  let straight := MackeyDiagrams.LabelledDrawing.ordinary
    (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.down d))
  MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret curl) =
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret straight)) :=
(by
  intro U inst K H G δ α hδ hα d a curl straight
  -- Theorem 4.1, (4.2), is on p. 14 of the archived source PDF
  -- (bc57d13777e7df145b6dfd84029e0e9539fedb33d22b2823e14c096e4c3c12f2)
  -- and p. 16 of the revised published PDF
  -- (6d7e885955f23ae6d10d8e8394d3fe9252dfc2fa7ce7ec149ec190de766c978e).
  -- Both give the right-hand G-loop on the K–H down-strand.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- The retained ReviewedRightDownCurl uses a pre-expanded Diagram. Here we
  -- unfold both typed junctions via LabelledDrawing.interpret and the
  -- TrivalentVertex and BentVertex expansions. Interchange identifies the
  -- two separately whiskered generators with the retained middle map.
  -- Alphabeta Math's module tensor universal property, Steps 3.1, 4.1 and
  -- 5.1, motivate balance, descent and determination on elementary tensors.
  -- The project implements those steps by linearizing the balanced biset:
  -- mergeDown_splitDown uses the balance of [x,y] and [1,a(x)*y].
  -- https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products
  have hmerge :
      ((MackeyDiagrams.Generator.mergeDown Complex a d).horizontal
          (MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Biset.induction a))).vertical
        ((MackeyDiagrams.Generator.splitDown Complex a d).horizontal
          (MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Biset.induction a))) =
        MackeyDiagrams.Biset.Hom.id
          (((MackeyDiagrams.Biset.restriction d).tensor
            (MackeyDiagrams.Biset.restriction a)).tensor
            (MackeyDiagrams.Biset.induction a)) := by
    have hmid :
        (MackeyDiagrams.Generator.mergeDown Complex a d).vertical
          (MackeyDiagrams.Generator.splitDown Complex a d) =
          MackeyDiagrams.Biset.Hom.id ((MackeyDiagrams.Biset.restriction d).tensor
            (MackeyDiagrams.Biset.restriction a)) :=
      MackeyDiagrams.Diagram.mergeDown_splitDown a d
    rw [MackeyDiagrams.Biset.Hom.horizontal_vertical, hmid,
      MackeyDiagrams.Biset.Hom.vertical_id, MackeyDiagrams.Biset.Hom.horizontal_id]
  -- The ordinary cup and trace act with coefficient one at arbitrary index.
  -- The routed InductionRestrictionAdjunction and
  -- InductionRestrictionMergesAndSplits describe the individual generators.
  -- The cancellation lemmas below and above give the needed identities
  -- directly on the corresponding evaluated composites.
  have hcup :
      (MackeyDiagrams.Generator.ordinaryCup Complex a).vertical
        (MackeyDiagrams.Generator.traceCap Complex a) =
        MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Biset.regular H) :=
    MackeyDiagrams.Diagram.ordinaryCup_traceCap a
  simp only [curl, straight, MackeyDiagrams.LabelledDrawing.interpret,
    MackeyDiagrams.ScopedDiagram.eval, MackeyDiagrams.TrivalentVertex.expand,
    MackeyDiagrams.BentVertex.expand, MackeyDiagrams.Diagram.eval,
    MackeyDiagrams.Word.basis, MackeyDiagrams.Biset.Hom.vertical_assoc]
  -- The opening junction uses unassociate and the closing uses associate,
  -- so the inverse lemma has the order unassociate_associate.
  rw [← MackeyDiagrams.Biset.Hom.vertical_assoc
      ((MackeyDiagrams.Generator.mergeDown Complex a d).horizontal
        (MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Biset.induction a))),
    hmerge, MackeyDiagrams.Biset.Hom.id_vertical,
    ← MackeyDiagrams.Biset.Hom.vertical_assoc
      (MackeyDiagrams.Biset.unassociate (MackeyDiagrams.Biset.restriction d)
        (MackeyDiagrams.Biset.restriction a) (MackeyDiagrams.Biset.induction a) Complex),
    MackeyDiagrams.Biset.unassociate_associate, MackeyDiagrams.Biset.Hom.id_vertical]
  rw [← MackeyDiagrams.Biset.Hom.vertical_assoc
      ((MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Biset.restriction d)).horizontal
        (MackeyDiagrams.Generator.ordinaryCup Complex a)),
    MackeyDiagrams.Biset.Hom.horizontal_vertical,
    MackeyDiagrams.Biset.Hom.id_vertical, hcup,
    MackeyDiagrams.Biset.Hom.horizontal_id, MackeyDiagrams.Biset.Hom.id_vertical]
  exact MackeyDiagrams.Biset.insertRightUnit_rightUnit)

#print axioms RightDownReidemeisterCurl
