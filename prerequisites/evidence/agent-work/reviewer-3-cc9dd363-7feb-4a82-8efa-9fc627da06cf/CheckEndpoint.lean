import Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

open CategoryTheory CategoryTheory.Limits
universe u v w

def checkedEndpoint : Prop :=
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

section
variable {C : Type u} [Category.{v} C] [Abelian C] (P : C)

example : IsSeparator P ↔
    ∀ ⦃X Y : C⦄ (f g : X ⟶ Y), (∀ h : P ⟶ X, h ≫ f = h ≫ g) → f = g :=
  isSeparator_def P

example (a b : End P) : (a * b).asHom = b.asHom ≫ a.asHom := rfl

example (X : C) : ((preadditiveCoyonedaObj P).obj X : Type v) = (P ⟶ X) := rfl

example (X : C) (a : End P) (f : P ⟶ X) :
    (MulOpposite.op a : (End P)ᵐᵒᵖ) • f = a.asHom ≫ f := rfl

example {X Y : C} (u : X ⟶ Y) (f : P ⟶ X) :
    (preadditiveCoyonedaObj P).map u f = f ≫ u := rfl

example [HasCoproducts.{w} C] {I : Type w} [DecidableEq I]
    (A : I → C) (i : I) (f : P ⟶ A i) :
    (DirectSum.toAddMonoid (fun j => Preadditive.rightComp P (Sigma.ι A j)))
        (DirectSum.of (fun j => P ⟶ A j) i f) = f ≫ Sigma.ι A i :=
  DirectSum.toAddMonoid_of _ _ _
end
