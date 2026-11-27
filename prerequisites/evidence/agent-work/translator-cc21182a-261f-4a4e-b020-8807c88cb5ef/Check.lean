import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.ULift
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

universe u v w

def RegularModuleSmallProjectiveGenerator : Prop :=
  ∀ (R : Type u) [Ring R],
    let A := ModuleCat.of R (ULift.{max v w} R)
    (∃ e : ∀ M : ModuleCat.{max u v w} R, AddEquiv (Quiver.Hom A M) ↥M,
      (∀ (M : ModuleCat.{max u v w} R) (f : Quiver.Hom A M),
        e M f = ModuleCat.Hom.hom f (ULift.up (1 : R))) ∧
      (∀ {M N : ModuleCat.{max u v w} R} (g : Quiver.Hom M N) (f : Quiver.Hom A M),
        e N (CategoryTheory.CategoryStruct.comp f g) = ModuleCat.Hom.hom g (e M f))) ∧
    CategoryTheory.Projective A ∧
    CategoryTheory.IsSeparator A ∧
    (∀ (I : Type v) (M : I → ModuleCat.{max u v w} R),
      letI : DecidableEq I := Classical.decEq I
      let D := ModuleCat.of R (DirectSum I (fun i => ↥(M i)))
      Function.Bijective
        (DirectSum.toAddMonoid (β := fun i => Quiver.Hom A (M i)) (γ := Quiver.Hom A D)
          (fun i => CategoryTheory.Preadditive.rightComp A
            (ModuleCat.ofHom (DirectSum.lof R I (fun j => ↥(M j)) i))))) ∧
    (∃ e : RingEquiv (CategoryTheory.End A) (MulOpposite R),
      ∀ f : CategoryTheory.End A,
        e f = MulOpposite.op
          (ULift.down (ModuleCat.Hom.hom (CategoryTheory.End.asHom f) (ULift.up (1 : R)))))

#check RegularModuleSmallProjectiveGenerator.{u, v, w}
#check LinearMap.ringLmapEquivSelf
#check RingEquiv.moduleEndSelf
#check ModuleCat.endRingEquiv
#check CategoryTheory.End.mul_asHom
#check DirectSum.toAddMonoid_of
