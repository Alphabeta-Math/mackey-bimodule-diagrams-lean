import Proofs.EilenbergWatts
import Mathlib.CategoryTheory.Linear.LinearFunctor

open scoped ModuleCat.Algebra
universe u v

noncomputable def reviewedComplexType : Prop :=
∀ (S R : RingCat.{u}) [Algebra Complex S] [Algebra Complex R],
  let ew := Classical.choose _root_.EilenbergWatts S R
  let Bimod := Sigma (fun M : ModuleCat.{max u v} S =>
    { a : _root_.Bimodule.1 S R M // a.1 = ModuleCat.isModule M })
  let Good := fun F : CategoryTheory.Functor (ModuleCat.{max u v} R) (ModuleCat.{max u v} S) =>
    CategoryTheory.Functor.Additive F ∧
    CategoryTheory.Limits.PreservesFiniteColimits F ∧
    ∀ I : Type (max u v),
      CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete I) F
  let GoodFunctors := CategoryTheory.ObjectProperty.FullSubcategory Good
  letI : CategoryTheory.Category.{max u v} Bimod :=
    (fun (c : CategoryTheory.Category.{max u v} Bimod)
      (_ : @CategoryTheory.Equivalence Bimod GoodFunctors c inferInstance) => c) _ ew
  let EqualScalars : CategoryTheory.ObjectProperty Bimod := fun B =>
    letI : Module (MulOpposite R) B.1 := B.2.1.2.1
    ∀ (z : Complex) (b : B.1),
      algebraMap Complex S z • b = MulOpposite.op (algebraMap Complex R z) • b
  let ComplexLinear : CategoryTheory.ObjectProperty GoodFunctors := fun F =>
    CategoryTheory.Functor.Linear Complex F.obj
  (∀ B : Bimod, EqualScalars B ↔ ComplexLinear (ew.functor.obj B)) ∧
  ∃ restricted : CategoryTheory.Equivalence
      (CategoryTheory.ObjectProperty.FullSubcategory EqualScalars)
      (CategoryTheory.ObjectProperty.FullSubcategory ComplexLinear),
    CategoryTheory.Functor.comp restricted.functor (CategoryTheory.ObjectProperty.ι ComplexLinear) =
      CategoryTheory.Functor.comp (CategoryTheory.ObjectProperty.ι EqualScalars) ew.functor
