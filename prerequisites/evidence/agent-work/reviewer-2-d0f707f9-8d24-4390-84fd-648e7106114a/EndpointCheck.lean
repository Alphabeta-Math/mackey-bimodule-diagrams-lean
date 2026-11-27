import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.DirectSum.Basic

universe u v

def TranslatedEndpoint : Prop :=
∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.LocallySmall.{v} C]
    [CategoryTheory.Abelian C] [CategoryTheory.Limits.HasCoproducts.{v} C]
    (P : C) [CategoryTheory.Projective P],
  CategoryTheory.IsSeparator P →
  (∀ (I : Type v) (X : I → C),
    letI : DecidableEq I := Classical.decEq I
    Function.Bijective
      (DirectSum.toAddMonoid
        (β := fun i => Quiver.Hom P (X i))
        (γ := Quiver.Hom P (CategoryTheory.Limits.sigmaObj X))
        (fun i => CategoryTheory.Preadditive.rightComp P
          (CategoryTheory.Limits.Sigma.ι X i)))) →
  let R := MulOpposite (CategoryTheory.End P)
  let H : CategoryTheory.Functor C (ModuleCat.{v} R) :=
    CategoryTheory.preadditiveCoyonedaObj P
  ∃ L : CategoryTheory.Functor (ModuleCat.{v} R) C,
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp L H)
      (CategoryTheory.Functor.id (ModuleCat.{v} R))) ∧
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp H L)
      (CategoryTheory.Functor.id C))
