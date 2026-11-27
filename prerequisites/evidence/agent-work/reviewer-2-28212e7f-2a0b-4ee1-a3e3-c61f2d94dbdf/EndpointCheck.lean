import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

axiom reviewedEndpoint :
  ∀ {C : Type*} {D : Type*}
    [CategoryTheory.Category.{_} C] [CategoryTheory.Category.{_} D]
    [CategoryTheory.Preadditive C] [CategoryTheory.Preadditive D]
    [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.Limits.HasZeroObject D]
    [CategoryTheory.Limits.HasFiniteBiproducts C]
    [CategoryTheory.Limits.HasFiniteBiproducts D]
    (F : CategoryTheory.Functor C D),
    (∀ [CategoryTheory.Functor.Additive F],
      CategoryTheory.Limits.PreservesFiniteBiproducts F) ∧
    ((∀ X : C, CategoryTheory.Limits.IsZero X →
        CategoryTheory.Limits.IsZero (CategoryTheory.Functor.obj F X)) →
      CategoryTheory.Limits.PreservesFiniteProducts F →
      CategoryTheory.Limits.PreservesFiniteCoproducts F →
      CategoryTheory.Functor.Additive F)

set_option pp.universes true in
#check reviewedEndpoint
