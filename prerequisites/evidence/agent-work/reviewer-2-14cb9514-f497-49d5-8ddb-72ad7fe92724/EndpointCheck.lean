import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.Algebra.DirectSum.Basic

universe u₁ u₂ v₁ v₂ w

def endpoint : Prop :=
∀ {C : Type u₁} {D : Type u₂}
  [CategoryTheory.Category.{v₁} C] [CategoryTheory.Category.{v₂} D]
  [CategoryTheory.Abelian C] [CategoryTheory.Abelian D]
  (e : CategoryTheory.Equivalence C D),
  let F := CategoryTheory.Equivalence.functor e
  CategoryTheory.Functor.Additive F ∧
  (∀ {X Y : C} (f : Quiver.Hom X Y),
    CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair f 0) F ∧
    CategoryTheory.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair f 0) F) ∧
  (∀ (I : Type w),
    CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete I) F) ∧
  (∀ [CategoryTheory.Functor.Additive F] (S : CategoryTheory.ShortComplex C),
    CategoryTheory.ShortComplex.Exact S →
      CategoryTheory.ShortComplex.Exact (CategoryTheory.ShortComplex.map S F)) ∧
  (∀ [CategoryTheory.Limits.HasCoproducts.{w} C],
    ∃ hD : CategoryTheory.Limits.HasCoproducts.{w} D,
    letI : CategoryTheory.Limits.HasCoproducts.{w} D := hD
    ∀ (P : C),
      CategoryTheory.Projective P →
      CategoryTheory.IsSeparator P →
      (∀ (I : Type w) (X : I → C),
        letI : DecidableEq I := Classical.decEq I
        Function.Bijective
          (DirectSum.toAddMonoid (β := fun i => Quiver.Hom P (X i))
            (fun i => CategoryTheory.Preadditive.rightComp P
              (CategoryTheory.Limits.Sigma.ι X i)))) →
      CategoryTheory.Projective (CategoryTheory.Functor.obj F P) ∧
      CategoryTheory.IsSeparator (CategoryTheory.Functor.obj F P) ∧
      (∀ (I : Type w) (Y : I → D),
        letI : DecidableEq I := Classical.decEq I
        Function.Bijective
          (DirectSum.toAddMonoid
            (β := fun i => Quiver.Hom (CategoryTheory.Functor.obj F P) (Y i))
            (fun i => CategoryTheory.Preadditive.rightComp (CategoryTheory.Functor.obj F P)
              (CategoryTheory.Limits.Sigma.ι Y i)))))

set_option pp.universes true in
#check endpoint
