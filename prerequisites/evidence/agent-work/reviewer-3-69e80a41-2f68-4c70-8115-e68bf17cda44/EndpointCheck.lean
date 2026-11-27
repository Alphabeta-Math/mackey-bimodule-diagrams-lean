import Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

universe u v w

def generatorCokernelPresentationsEndpoint : Prop :=
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
  ∀ X : C,
    ∃ (I J : Type w),
      let copower := fun K : Type w => CategoryTheory.Limits.sigmaObj (fun _ : K => P)
      ∃ (d : Quiver.Hom (copower J) (copower I)) (q : Quiver.Hom (copower I) X)
        (h : CategoryTheory.CategoryStruct.comp d q = 0),
        Nonempty (CategoryTheory.Limits.IsColimit
          (CategoryTheory.Limits.CokernelCofork.ofπ q h))
