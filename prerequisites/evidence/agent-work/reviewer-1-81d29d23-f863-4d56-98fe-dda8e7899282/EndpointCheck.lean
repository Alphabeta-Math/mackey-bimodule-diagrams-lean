import Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

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

open CategoryTheory CategoryTheory.Limits

section Definitions
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {P X Y : C}

example (a : End P) (f : P ⟶ X) :
    (MulOpposite.op a) • f = a.asHom ≫ f := rfl

example (f : P ⟶ X) (u : X ⟶ Y) :
    ((preadditiveCoyonedaObj P).map u) f = f ≫ u := rfl

example (a b : End P) :
    (a * b).asHom = b.asHom ≫ a.asHom := rfl

example [HasCoproducts.{w} C] {I : Type w} [DecidableEq I] (A : I → C)
    (i : I) (f : P ⟶ A i) :
    (DirectSum.toAddMonoid (β := fun i => P ⟶ A i) (γ := P ⟶ sigmaObj A)
      (fun i => Preadditive.rightComp P (Sigma.ι A i)))
      (DirectSum.of (fun i => P ⟶ A i) i f) = f ≫ Sigma.ι A i :=
  DirectSum.toAddMonoid_of _ _ _
end Definitions
