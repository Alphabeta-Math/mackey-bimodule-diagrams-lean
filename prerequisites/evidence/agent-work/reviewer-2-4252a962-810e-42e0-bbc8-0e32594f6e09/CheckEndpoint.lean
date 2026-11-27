import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products

universe u v w

def translatedEndpoint : Prop :=
  ∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.LocallySmall.{w} C]
      [CategoryTheory.Abelian C] [CategoryTheory.Limits.HasCoproducts.{w} C]
      (P : C) [CategoryTheory.Projective P],
    CategoryTheory.IsSeparator P →
    (∀ (I : Type w) (A : I → C),
      letI : DecidableEq I := Classical.decEq I
      Function.Bijective
        (DirectSum.toAddMonoid
          (β := fun i => Quiver.Hom P (A i))
          (γ := Quiver.Hom P (CategoryTheory.Limits.sigmaObj A))
          (fun i => CategoryTheory.Preadditive.rightComp P
            (CategoryTheory.Limits.Sigma.ι A i)))) →
    let H : CategoryTheory.Functor C (ModuleCat.{v} (MulOpposite (CategoryTheory.End P))) :=
      CategoryTheory.preadditiveCoyonedaObj P
    ∀ (X Y : C),
      Function.Bijective (CategoryTheory.Functor.map H (X := X) (Y := Y))
