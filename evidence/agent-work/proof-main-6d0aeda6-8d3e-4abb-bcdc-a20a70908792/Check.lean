import MackeyDiagrams
import Proofs.FiniteIndexReverseAdjunction
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 2000000

universe u

open MackeyDiagrams in
private theorem rightUpCurl_assemble {L M : Type u} [Group L] [Group M]
    {W X Y A B : Biset L M}
    (insert : Biset.Hom Complex W X) (cup : Biset.Hom Complex X Y)
    (reassoc : Biset.Hom Complex Y A) (merge : Biset.Hom Complex A B)
    (split : Biset.Hom Complex B A) (assoc : Biset.Hom Complex A Y)
    (cap : Biset.Hom Complex Y X) (remove : Biset.Hom Complex X W) (n : Complex)
    (hMiddle : (reassoc.vertical merge).vertical (split.vertical assoc) = Biset.Hom.id Y)
    (hLoop : cup.vertical cap = (Biset.Hom.id X).scale n)
    (hUnits : insert.vertical remove = Biset.Hom.id W) :
    (insert.vertical (cup.vertical (reassoc.vertical merge))).vertical
        (split.vertical (assoc.vertical (cap.vertical remove))) =
      (Biset.Hom.id W).scale n := by
  calc
    _ = insert.vertical (Biset.Hom.vertical
          (cup.vertical ((reassoc.vertical merge).vertical (split.vertical assoc)))
          (cap.vertical remove)) := by
        simp only [Biset.Hom.vertical_assoc]
    _ = insert.vertical ((cup.vertical cap).vertical remove) := by
        rw [hMiddle, Biset.Hom.vertical_id, Biset.Hom.vertical_assoc]
    _ = (Biset.Hom.id W).scale n := by
        rw [hLoop, Biset.Hom.vertical_scale_left, Biset.Hom.id_vertical,
          Biset.Hom.vertical_scale_right, hUnits]

open MackeyDiagrams in
private theorem rightUpCurl_tensorInverse {L M N : Type u} [Group L] [Group M] [Group N]
    {X Y : Biset L M} (f : Biset.Hom Complex X Y) (g : Biset.Hom Complex Y X)
    (Z : Biset M N) (h : f.vertical g = Biset.Hom.id X) :
    (f.horizontal (Biset.Hom.id Z)).vertical (g.horizontal (Biset.Hom.id Z)) =
      Biset.Hom.id (X.tensor Z) := by
  rw [Biset.Hom.horizontal_vertical, h, Biset.Hom.id_vertical, Biset.Hom.horizontal_id]

open MackeyDiagrams in
private theorem rightUpCurl_tensorScalar {L M : Type u} [Group L] [Group M]
    (X : Biset L M) {Y Z : Biset M M} (cup : Biset.Hom Complex Y Z)
    (cap : Biset.Hom Complex Z Y) (n : Complex)
    (h : cup.vertical cap = (Biset.Hom.id Y).scale n) :
    ((Biset.Hom.id X).horizontal cup).vertical ((Biset.Hom.id X).horizontal cap) =
      (Biset.Hom.id (X.tensor Y)).scale n := by
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical, h,
    Biset.Hom.horizontal_scale_right, Biset.Hom.horizontal_id]

theorem RightUpReidemeisterCurl : (∀ {U : Type u} [Group U] (K H G : Subgroup U) (δ α : U)
    (hδ : ∀ k : K, δ * (k : U) * δ⁻¹ ∈ H)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G),
  let d := MackeyDiagrams.ConjEmbedding.ofConjugator δ hδ
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let S := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom d)
  ∀ finite : Subgroup.FiniteIndex S,
    let curl := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
        (MackeyDiagrams.TrivalentVertex.upToUpDown a d finite))
      (MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.upDownToUp a d))
    let straight := MackeyDiagrams.LabelledDrawing.ordinary
      (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up a))
    let scaled := MackeyDiagrams.LabelledDrawing.scale (Subgroup.index S : Complex) straight
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret curl) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret scaled)) :=
(by
  intro U inst K H G δ α hδ hα d a S finite curl straight scaled
  -- Xiao's (4.1) and its unnumbered proof appear on pp. 14–15 of the
  -- project PDF and pp. 16–17 of the current published PDF. Both show
  -- the same junctions and identify the scalar using the same finite index.
  -- The typed trivalent expansion checks the connection to the explicit
  -- composite in the retained ReviewedRightUpCurl calculation. Its merge
  -- and split appear as separate maps before their evaluated cancellation.
  simp only [curl, straight, scaled, MackeyDiagrams.LabelledDrawing.interpret,
    MackeyDiagrams.ScopedDiagram.eval, MackeyDiagrams.TrivalentVertex.expand,
    MackeyDiagrams.BentVertex.expand, MackeyDiagrams.Diagram.eval, MackeyDiagrams.Word.basis]
  refine rightUpCurl_assemble _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
  · -- Merge and split cancel on the upward pair, with identity on the
    -- downward leg. The two rebracketings then cancel.
    exact MackeyDiagrams.Biset.Hom.cancel_middle _ _ _ _
      (rightUpCurl_tensorInverse _ _ _ (MackeyDiagrams.Diagram.mergeUp_splitUp a d))
      MackeyDiagrams.Biset.unassociate_associate
  · -- The finite multiplication-cap fiber realizes Xiao's transversal sum.
    -- Generator.capFiber_card uses Subgroup.index_eq_card on the inner image,
    -- which is exactly the subgroup S with finite-index evidence finite.
    exact rightUpCurl_tensorScalar _ _ _ _
      (MackeyDiagrams.Diagram.reverseCup_multiplicationCap d finite)
  · exact MackeyDiagrams.Biset.insertRightUnit_rightUnit)

#print axioms RightUpReidemeisterCurl
