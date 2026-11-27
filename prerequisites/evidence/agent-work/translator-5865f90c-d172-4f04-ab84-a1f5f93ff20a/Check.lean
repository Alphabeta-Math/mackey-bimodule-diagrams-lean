import Mathlib.Algebra.Category.ModuleCat.Basic
import NotesProofs.WattsActions

universe u v z w

theorem RegularEvaluationRightAction :
∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
  (F : CategoryTheory.Functor (ModuleCat.{max u z} R) (ModuleCat.{w} S))
  [CategoryTheory.Functor.Additive F],
  let A := ModuleCat.of R (ULift.{z} R)
  let B := CategoryTheory.Functor.obj F A
  let rho : R → Quiver.Hom A A := fun r =>
    ModuleCat.ofHom
      (LinearEquiv.conjRingEquiv
        (LinearEquiv.symm (ULift.moduleEquiv : LinearEquiv (RingHom.id R) (ULift.{z} R) R))
        (LinearMap.mulRight R r))
  ∃ right : Module (MulOpposite R) ↥B,
    letI : Module (MulOpposite R) ↥B := right
    SMulCommClass (MulOpposite R) S ↥B ∧
      ∀ (r : R) (b : ↥B),
        SMul.smul (MulOpposite.op r) b =
          ModuleCat.Hom.hom (CategoryTheory.Functor.map F (rho r)) b := by
  intro R S _ _ F _
  exact ⟨NotesProofs.wattsRightModule F, NotesProofs.wattsRight_commutes F,
    NotesProofs.wattsRight_apply F⟩

private theorem lifted_right_multiplication_apply (R : Type u) [Ring R]
    (r : R) (x : ULift.{z} R) :
    let A := ModuleCat.of R (ULift.{z} R)
    let rho : R → Quiver.Hom A A := fun r =>
      ModuleCat.ofHom
        (LinearEquiv.conjRingEquiv
          (LinearEquiv.symm (ULift.moduleEquiv : LinearEquiv (RingHom.id R) (ULift.{z} R) R))
          (LinearMap.mulRight R r))
    ModuleCat.Hom.hom (rho r) x = ULift.up (ULift.down x * r) := rfl

#print axioms RegularEvaluationRightAction
