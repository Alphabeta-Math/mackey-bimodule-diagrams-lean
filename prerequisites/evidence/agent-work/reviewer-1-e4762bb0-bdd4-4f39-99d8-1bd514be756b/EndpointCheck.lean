import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Module.Equiv.Basic

universe u v z w

def translatedEndpoint : Prop :=
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
          ModuleCat.Hom.hom (CategoryTheory.Functor.map F (rho r)) b

example (R : Type u) [Ring R] (r : R) (x : ULift.{z} R) :
    ModuleCat.Hom.hom
      (ModuleCat.ofHom
        (LinearEquiv.conjRingEquiv
          (LinearEquiv.symm (ULift.moduleEquiv : LinearEquiv (RingHom.id R) (ULift.{z} R) R))
          (LinearMap.mulRight R r))) x =
      ULift.up (x.down * r) :=
  rfl
