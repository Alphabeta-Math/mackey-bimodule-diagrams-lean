import MackeyDiagrams.Boundary
import MackeyDiagrams.HorizontalComposition

/-! The structural maps used to put a diagram at canonical boundaries are inverse. -/

namespace MackeyDiagrams.Biset

universe u v

variable {K H J F : Type u} [Group K] [Group H] [Group J] [Group F]
variable {R : Type v} [CommSemiring R]
variable {X W : Biset K H} {Y : Biset H J} {Z : Biset J F}

theorem associate_unassociate :
    (associate X Y Z R).vertical (unassociate X Y Z R) = Hom.id _ := by
  apply Hom.ext
  apply Finsupp.lhom_ext
  intro z r
  change (unassociate X Y Z R).toLinearMap
    ((associate X Y Z R).toLinearMap (Finsupp.single z r)) = Finsupp.single z r
  rw [associate, Hom.ofFunction_single, unassociate, Hom.ofFunction_single]
  exact congrArg (fun x => Finsupp.single x r) ((associateBasisEquiv X Y Z).left_inv z)

theorem unassociate_associate :
    (unassociate X Y Z R).vertical (associate X Y Z R) = Hom.id _ := by
  apply Hom.ext
  apply Finsupp.lhom_ext
  intro z r
  change (associate X Y Z R).toLinearMap
    ((unassociate X Y Z R).toLinearMap (Finsupp.single z r)) = Finsupp.single z r
  rw [unassociate, Hom.ofFunction_single, associate, Hom.ofFunction_single]
  exact congrArg (fun x => Finsupp.single x r) ((associateBasisEquiv X Y Z).right_inv z)

theorem insertLeftUnit_leftUnit :
    (insertLeftUnit X R).vertical (leftUnit X R) = Hom.id X := by
  apply Hom.ext
  apply Finsupp.lhom_ext
  intro x r
  change (leftUnit X R).toLinearMap
    ((insertLeftUnit X R).toLinearMap (Finsupp.single x r)) = Finsupp.single x r
  rw [insertLeftUnit, Hom.ofFunction_single, leftUnit, Hom.ofFunction_single]
  change Finsupp.single (X.act 1 x) r = Finsupp.single x r
  rw [X.one_act]

theorem leftUnit_insertLeftUnit :
    (leftUnit X R).vertical (insertLeftUnit X R) = Hom.id _ := by
  apply Hom.ext
  apply Finsupp.lhom_ext
  intro x r
  refine Quotient.inductionOn x (fun z => ?_)
  rcases z with ⟨k,x⟩
  change (insertLeftUnit X R).toLinearMap ((leftUnit X R).toLinearMap
      (Finsupp.single ((regular K).pair X k x) r)) =
    Finsupp.single ((regular K).pair X k x) r
  rw [leftUnit, Hom.ofFunction_single, insertLeftUnit, Hom.ofFunction_single]
  change Finsupp.single ((regular K).pair X 1 (X.act (k,1) x)) r = _
  apply congrArg (fun z => Finsupp.single z r)
  simpa [regular] using ((regular K).pair_balance X k 1 x).symm

theorem insertRightUnit_rightUnit :
    (insertRightUnit X R).vertical (rightUnit X R) = Hom.id X := by
  apply Hom.ext
  apply Finsupp.lhom_ext
  intro x r
  change (rightUnit X R).toLinearMap
    ((insertRightUnit X R).toLinearMap (Finsupp.single x r)) = Finsupp.single x r
  rw [insertRightUnit, Hom.ofFunction_single, rightUnit, Hom.ofFunction_single]
  change Finsupp.single (X.act (1,(1 : H)⁻¹) x) r = Finsupp.single x r
  rw [inv_one]
  change Finsupp.single (X.act 1 x) r = Finsupp.single x r
  rw [X.one_act]

theorem rightUnit_insertRightUnit :
    (rightUnit X R).vertical (insertRightUnit X R) = Hom.id _ := by
  apply Hom.ext
  apply Finsupp.lhom_ext
  intro x r
  refine Quotient.inductionOn x (fun z => ?_)
  rcases z with ⟨x,h⟩
  change (insertRightUnit X R).toLinearMap ((rightUnit X R).toLinearMap
      (Finsupp.single (X.pair (regular H) x h) r)) =
    Finsupp.single (X.pair (regular H) x h) r
  rw [rightUnit, Hom.ofFunction_single, insertRightUnit, Hom.ofFunction_single]
  change Finsupp.single (X.pair (regular H) (X.act (1,h⁻¹) x) 1) r = _
  apply congrArg (fun z => Finsupp.single z r)
  simpa [regular] using X.pair_balance (regular H) h x 1

end MackeyDiagrams.Biset

namespace MackeyDiagrams.Biset.Hom

universe u v

variable {K H : Type u} [Group K] [Group H] {R : Type v} [CommSemiring R]
variable {A B C : Biset K H}

theorem cancel_middle (start : Hom R A B) (inside : Hom R B C)
    (outside : Hom R C B) (finish : Hom R B A)
    (hInside : inside.vertical outside = id B)
    (hOutside : start.vertical finish = id A) :
    (start.vertical inside).vertical (outside.vertical finish) = id A := by
  rw [vertical_assoc, ← vertical_assoc inside, hInside, id_vertical, hOutside]

end MackeyDiagrams.Biset.Hom

namespace MackeyDiagrams

universe u v

variable {U : Type u} [Group U] {K H J : Subgroup U}
variable {R : Type v} [CommSemiring R]

namespace Boundary

theorem eval_append_split (a : Boundary K H) (b : Boundary H J) :
    ((a.appendDiagram (R := R) b).vertical (a.splitDiagram b)).eval =
      (Diagram.id (a.word.tensor b.word)).eval := by
  induction a with
  | empty => exact Biset.leftUnit_insertLeftUnit
  | cons s rest ih =>
    change ((Biset.associate s.word.basis rest.word.basis b.word.basis R).vertical
      ((Biset.Hom.id s.word.basis).horizontal (rest.appendDiagram b).eval)).vertical
      (((Biset.Hom.id s.word.basis).horizontal (rest.splitDiagram b).eval).vertical
        (Biset.unassociate s.word.basis rest.word.basis b.word.basis R)) = Biset.Hom.id _
    refine Biset.Hom.cancel_middle _ _ _ _ ?_ Biset.associate_unassociate
    rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
    change (Biset.Hom.id s.word.basis).horizontal
      (((rest.appendDiagram (R := R) b).vertical (rest.splitDiagram b)).eval) = _
    rw [ih b]
    exact Biset.Hom.horizontal_id _ _

theorem eval_split_append (a : Boundary K H) (b : Boundary H J) :
    ((a.splitDiagram (R := R) b).vertical (a.appendDiagram b)).eval =
      (Diagram.id (a.append b).word).eval := by
  induction a with
  | empty => exact Biset.insertLeftUnit_leftUnit
  | cons s rest ih =>
    change (((Biset.Hom.id s.word.basis).horizontal (rest.splitDiagram b).eval).vertical
      (Biset.unassociate s.word.basis rest.word.basis b.word.basis R)).vertical
      ((Biset.associate s.word.basis rest.word.basis b.word.basis R).vertical
        ((Biset.Hom.id s.word.basis).horizontal (rest.appendDiagram b).eval)) = Biset.Hom.id _
    refine Biset.Hom.cancel_middle _ _ _ _ Biset.unassociate_associate ?_
    rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
    change (Biset.Hom.id s.word.basis).horizontal
      (((rest.splitDiagram (R := R) b).vertical (rest.appendDiagram b)).eval) = _
    rw [ih b]
    exact Biset.Hom.horizontal_id _ _

end Boundary

namespace Word

theorem eval_reorderToFrom (p : Word K H) :
    ((p.reorderToBoundary (R := R)).vertical p.reorderFromBoundary).eval =
      (Diagram.id p).eval := by
  induction p with
  | empty => rfl
  | up => exact Biset.insertRightUnit_rightUnit
  | down => exact Biset.insertRightUnit_rightUnit
  | tensor p q ihp ihq =>
    change (((p.reorderToBoundary (R := R)).eval.horizontal q.reorderToBoundary.eval).vertical
      ((p.boundary.appendDiagram q.boundary).eval)).vertical
      ((p.boundary.splitDiagram q.boundary).eval.vertical
        ((p.reorderFromBoundary (R := R)).eval.horizontal q.reorderFromBoundary.eval)) = Biset.Hom.id _
    refine Biset.Hom.cancel_middle _ _ _ _ (Boundary.eval_append_split (R := R) p.boundary q.boundary) ?_
    rw [Biset.Hom.horizontal_vertical]
    change (((p.reorderToBoundary (R := R)).vertical p.reorderFromBoundary).eval).horizontal
      (((q.reorderToBoundary (R := R)).vertical q.reorderFromBoundary).eval) = _
    rw [ihp, ihq]
    exact Biset.Hom.horizontal_id _ _

theorem eval_reorderFromTo (p : Word K H) :
    ((p.reorderFromBoundary (R := R)).vertical p.reorderToBoundary).eval =
      (Diagram.id p.boundary.word).eval := by
  induction p with
  | empty => rfl
  | up => exact Biset.rightUnit_insertRightUnit
  | down => exact Biset.rightUnit_insertRightUnit
  | tensor p q ihp ihq =>
    change ((p.boundary.splitDiagram q.boundary).eval.vertical
      (((p.reorderFromBoundary (R := R)).eval.horizontal q.reorderFromBoundary.eval))).vertical
      ((((p.reorderToBoundary (R := R)).eval.horizontal q.reorderToBoundary.eval)).vertical
        (p.boundary.appendDiagram q.boundary).eval) = Biset.Hom.id _
    refine Biset.Hom.cancel_middle _ _ _ _ ?_ (Boundary.eval_split_append (R := R) p.boundary q.boundary)
    rw [Biset.Hom.horizontal_vertical]
    change (((p.reorderFromBoundary (R := R)).vertical p.reorderToBoundary).eval).horizontal
      (((q.reorderFromBoundary (R := R)).vertical q.reorderToBoundary).eval) = _
    rw [ihp, ihq]
    exact Biset.Hom.horizontal_id _ _

end Word
end MackeyDiagrams
