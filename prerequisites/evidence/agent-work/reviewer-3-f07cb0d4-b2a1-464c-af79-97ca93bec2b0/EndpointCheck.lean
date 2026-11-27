import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.Grp.Basic

universe u v w z

def endpoint : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
    (F : CategoryTheory.Functor (ModuleCat.{max u z} R) (ModuleCat.{w} S))
    [CategoryTheory.Functor.Additive F],
    let A := ModuleCat.of R (ULift.{z} R)
    let B := CategoryTheory.Functor.obj F A
    let down : LinearEquiv (RingHom.id R) (ULift.{z} R) R := ULift.moduleEquiv
    let right : R → B → B := fun r b =>
      ModuleCat.Hom.hom (CategoryTheory.Functor.map F
        (ModuleCat.ofHom (LinearEquiv.conjRingEquiv (LinearEquiv.symm down)
          (LinearMap.mulRight R r)))) b
    let lambda : ∀ M : ModuleCat.{max u z} R, M → Quiver.Hom A M :=
      fun _ m => ModuleCat.ofHom (LinearMap.smulRight (LinearEquiv.toLinearMap down) m)
    let Balanced := fun (M : ModuleCat.{max u z} R)
        (G : AddCommGrpCat.{max u z w}) (p : B → M → G) =>
      (∀ (b b' : B) (m : M), p (b + b') m = p b m + p b' m) ∧
      (∀ (b : B) (m m' : M), p b (m + m') = p b m + p b m') ∧
      (∀ (r : R) (b : B) (m : M), p (right r b) m = p b (r • m))
    ∀ (T : CategoryTheory.Functor (ModuleCat.{max u z} R) (ModuleCat.{max u z w} S))
      (pure : ∀ M : ModuleCat.{max u z} R, B → M → ModuleCat.carrier (CategoryTheory.Functor.obj T M)),
      (∀ M : ModuleCat.{max u z} R,
        Balanced M (AddCommGrpCat.of (ModuleCat.carrier (CategoryTheory.Functor.obj T M))) (pure M) ∧
        (∀ (G : AddCommGrpCat.{max u z w}) (p : B → M → G),
          Balanced M G p →
            ∃! h : AddMonoidHom (ModuleCat.carrier (CategoryTheory.Functor.obj T M)) G,
              ∀ (b : B) (m : M), h (pure M b m) = p b m) ∧
        (∀ (s : S) (b : B) (m : M), s • pure M b m = pure M (s • b) m)) →
      (∀ {M N : ModuleCat.{max u z} R} (f : Quiver.Hom M N) (b : B) (m : M),
        ModuleCat.Hom.hom (CategoryTheory.Functor.map T f) (pure M b m) =
          pure N b (ModuleCat.Hom.hom f m)) →
      ∃ τ : CategoryTheory.NatTrans T
          (CategoryTheory.Functor.comp F (ModuleCat.uliftFunctor.{max u z, w} S)),
        ∀ (M : ModuleCat.{max u z} R) (b : B) (m : M),
          ModuleCat.Hom.hom (CategoryTheory.NatTrans.app τ M) (pure M b m) =
            ULift.up (ModuleCat.Hom.hom (CategoryTheory.Functor.map F (lambda M m)) b)
