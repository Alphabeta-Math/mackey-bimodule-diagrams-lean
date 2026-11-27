import Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

universe u v w

def ReviewedEndpoint : Prop :=
  ∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    [CategoryTheory.Limits.HasCoproducts.{w} C] (P : C) [CategoryTheory.Projective P],
    CategoryTheory.IsSeparator P →
    (∀ (I : Type w) (X : I → C),
      letI : DecidableEq I := Classical.decEq I
      Function.Bijective
        (DirectSum.toAddMonoid (β := fun i => Quiver.Hom P (X i))
          (fun i => CategoryTheory.Preadditive.rightComp P
            (CategoryTheory.Limits.Sigma.ι X i)))) →
    let H := CategoryTheory.preadditiveCoyonedaObj P
    (∀ {X Y : C} (f : Quiver.Hom X Y),
      CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair f 0) H) ∧
    (∀ {X Y : C} (f : Quiver.Hom X Y),
      CategoryTheory.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair f 0) H) ∧
    (∀ (I : Type w), CategoryTheory.Limits.PreservesColimitsOfShape
      (CategoryTheory.Discrete I) H) ∧
    CategoryTheory.Functor.Faithful H ∧
    CategoryTheory.Functor.ReflectsIsomorphisms H
