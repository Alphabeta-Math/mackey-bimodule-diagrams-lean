import NotesProofs.General.BimoduleTensorCategory
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Generator.Preadditive
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.Algebra.DirectSum.Basic

universe uA uD v

def endpointUnderReview : Prop :=
∀ (A : Type uA) (D : Type uD)
    [CategoryTheory.Category.{v} A] [CategoryTheory.Category.{v} D]
    [CategoryTheory.LocallySmall.{v} A] [CategoryTheory.LocallySmall.{v} D]
    [CategoryTheory.Abelian A] [CategoryTheory.Abelian D]
    [CategoryTheory.Limits.HasCoproducts.{v} A] [CategoryTheory.Limits.HasCoproducts.{v} D]
    (P : A) (Q : D) [CategoryTheory.Projective P] [CategoryTheory.Projective Q],
  CategoryTheory.IsSeparator P →
  CategoryTheory.IsSeparator Q →
  (∀ (I : Type v) (X : I → A),
    letI : DecidableEq I := Classical.decEq I
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => Quiver.Hom P (X i))
        (fun i => CategoryTheory.Preadditive.rightComp P (CategoryTheory.Limits.Sigma.ι X i)))) →
  (∀ (I : Type v) (Y : I → D),
    letI : DecidableEq I := Classical.decEq I
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => Quiver.Hom Q (Y i))
        (fun i => CategoryTheory.Preadditive.rightComp Q (CategoryTheory.Limits.Sigma.ι Y i)))) →
  let R := MulOpposite (CategoryTheory.End P)
  let S := MulOpposite (CategoryTheory.End Q)
  let HA : CategoryTheory.Functor A (ModuleCat.{v} R) :=
    CategoryTheory.preadditiveCoyonedaObj P
  let HD : CategoryTheory.Functor D (ModuleCat.{v} S) :=
    CategoryTheory.preadditiveCoyonedaObj Q
  let Good := CategoryTheory.ObjectProperty.FullSubcategory
    (fun F : CategoryTheory.Functor A D =>
      CategoryTheory.Functor.Additive F ∧
      (∀ {X Y : A} (f : Quiver.Hom X Y),
        CategoryTheory.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair f 0) F) ∧
      (∀ I : Type v, CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete I) F))
  let Bimod := NotesProofs.General.ConcreteBimodule.{v,0} R S
  Nonempty (CategoryTheory.Equivalence Good Bimod) ∧
  ∀ (LA : CategoryTheory.Functor (ModuleCat.{v} R) A)
    (LD : CategoryTheory.Functor (ModuleCat.{v} S) D),
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp LA HA)
      (CategoryTheory.Functor.id (ModuleCat.{v} R))) →
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp HA LA)
      (CategoryTheory.Functor.id A)) →
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp LD HD)
      (CategoryTheory.Functor.id (ModuleCat.{v} S))) →
    Nonempty (CategoryTheory.Iso (CategoryTheory.Functor.comp HD LD)
      (CategoryTheory.Functor.id D)) →
    ∃ E : CategoryTheory.Equivalence Good Bimod,
      (∀ F : Good,
        let W := CategoryTheory.Functor.comp LA
          (CategoryTheory.Functor.comp (CategoryTheory.ObjectProperty.FullSubcategory.obj F) HD)
        let BF := CategoryTheory.Functor.obj (CategoryTheory.Equivalence.functor E) F
        let M := NotesProofs.General.ConcreteBimodule.carrier BF
        ModuleCat.of S M = CategoryTheory.Functor.obj W (ChoiceFreeWatts.regular.{v,0} R) ∧
        ∀ r : R,
          HEq (fun m : M => SMul.smul (MulOpposite.op r) m)
            (fun x => ChoiceFreeWatts.right W r x)) ∧
      (∀ B : Bimod,
        CategoryTheory.ObjectProperty.FullSubcategory.obj
          (CategoryTheory.Functor.obj (CategoryTheory.Equivalence.inverse E) B) =
          CategoryTheory.Functor.comp HA
            (CategoryTheory.Functor.comp
              (NotesProofs.General.concreteTensorFunctor.{v,0} (R := R) (S := S)
                (NotesProofs.General.ConcreteBimodule.carrier B)) LD))

#print axioms endpointUnderReview
