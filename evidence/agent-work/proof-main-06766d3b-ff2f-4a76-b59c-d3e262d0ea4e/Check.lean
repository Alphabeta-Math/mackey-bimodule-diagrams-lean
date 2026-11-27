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

namespace RightUpCurlSupport

open MackeyDiagrams

variable {U : Type u} [Group U] {K H G : Subgroup U}
  (a : ConjEmbedding H G) (d : ConjEmbedding K H)

local notation "UpBasis" => Biset.induction a
local notation "LoopUpBasis" => Biset.induction d
local notation "LoopDownBasis" => Biset.restriction d
local notation "StraightMap" => Biset.Hom.id (R := Complex) UpBasis
local notation "InsertUnit" => Biset.insertRightUnit UpBasis Complex
local notation "RemoveUnit" => Biset.rightUnit UpBasis Complex
local notation "Reassociate" => Biset.unassociate UpBasis LoopUpBasis LoopDownBasis Complex
local notation "Associate" => Biset.associate UpBasis LoopUpBasis LoopDownBasis Complex
local notation "Merge" => Biset.Hom.horizontal (Generator.mergeUp Complex a d) (Biset.Hom.id LoopDownBasis)
local notation "Split" => Biset.Hom.horizontal (Generator.splitUp Complex a d) (Biset.Hom.id LoopDownBasis)
local notation "Cup[" f "]" => Biset.Hom.horizontal StraightMap (Generator.reverseCup Complex d f)
local notation "Cap" => Biset.Hom.horizontal StraightMap (Generator.multiplicationCap Complex d)
local notation "IndexScalar" => (d.toHom.range.index : Complex)

-- The merge and split are inverse on the upward pair. Carry the
-- downward identity through both and cancel the two rebracketings.
private theorem middle :
    ((Reassociate).vertical Merge).vertical ((Split).vertical Associate) =
      Biset.Hom.id ((UpBasis).tensor ((LoopUpBasis).tensor LoopDownBasis)) := by
  have h :
      (Generator.mergeUp Complex a d).vertical (Generator.splitUp Complex a d) =
        Biset.Hom.id ((UpBasis).tensor LoopUpBasis) :=
    Diagram.mergeUp_splitUp (R := Complex) a d
  exact Biset.Hom.cancel_middle Reassociate Merge Split Associate
    (rightUpCurl_tensorInverse _ _ LoopDownBasis h)
    (Biset.unassociate_associate (R := Complex))

-- The finite cap fiber gives the same terms as the article's right
-- transversal sum. Generator.capFiber_card counts these terms via
-- Subgroup.index_eq_card and the right-to-left quotient equivalence.
-- The reverse cup's finiteness evidence is precisely for d.toHom.range.
private theorem loop (finite : d.toHom.range.FiniteIndex) :
    (Cup[finite]).vertical Cap = (Biset.Hom.id ((UpBasis).tensor (Biset.regular H))).scale IndexScalar := by
  have h : (Generator.reverseCup Complex d finite).vertical (Generator.multiplicationCap Complex d) =
      (Biset.Hom.id (Biset.regular H)).scale IndexScalar :=
    Diagram.reverseCup_multiplicationCap (R := Complex) d finite
  exact rightUpCurl_tensorScalar UpBasis _ _ IndexScalar h

private theorem calculation (finite : d.toHom.range.FiniteIndex) :
    ((InsertUnit).vertical ((Cup[finite]).vertical ((Reassociate).vertical Merge))).vertical
        ((Split).vertical ((Associate).vertical ((Cap).vertical RemoveUnit))) = (StraightMap).scale IndexScalar :=
  rightUpCurl_assemble InsertUnit (Cup[finite]) Reassociate Merge Split Associate Cap RemoveUnit IndexScalar
    (middle a d) (loop a d finite) (Biset.insertRightUnit_rightUnit (R := Complex))

end RightUpCurlSupport

-- By definitional equality, interpret then eval expands exactly the
-- two junctions via TrivalentVertex.expand and BentVertex.expand.
open MackeyDiagrams in
private theorem RightUpCurlSupport.eval_trivalent {U : Type u} [Group U] {K H G : Subgroup U}
    (a : ConjEmbedding H G) (d : ConjEmbedding K H) (finite : d.toHom.range.FiniteIndex) :
    let lower := LabelledDrawing.trivalent (R := Complex) (TrivalentVertex.upToUpDown a d finite)
    let upper := LabelledDrawing.trivalent (R := Complex) (TrivalentVertex.upDownToUp a d)
    let straight := LabelledDrawing.ordinary (Diagram.id (R := Complex) (Word.up a))
    (lower.vertical upper).interpret.eval =
      (straight.scale (d.toHom.range.index : Complex)).interpret.eval :=
  RightUpCurlSupport.calculation a d finite

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
  -- Xiao's Theorem 4.1, equation (4.1), is on p. 14 of the archived
  -- original PDF and p. 16 of the revised published PDF. The unnumbered
  -- proof is on pp. 15 and 17, respectively. Both drawings have the
  -- same two mixed junctions and require finite index of δKδ⁻¹ in H.
  -- The undotted part of Proposition 3.1 gives the same cup and cap
  -- calculation. The cap-fiber proof uses the representative
  -- (z * t⁻¹, t) for a right coset of the inner image over z in H.
  -- The earlier ReviewedRightUpCurl uses an explicit cup, cap, merge
  -- and split. Here the two trivalent vertices stay in the statement.
  -- Their interpretations give those same maps at the fixed boundary.
  exact RightUpCurlSupport.eval_trivalent a d finite)

#print axioms RightUpReidemeisterCurl
