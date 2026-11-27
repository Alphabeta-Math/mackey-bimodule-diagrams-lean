import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero


theorem AdditiveFunctorsAndBiproducts :
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
:= by
  intro C D _ _ _ _ _ _ _ _ F
  constructor
  · intro _
    exact CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive F
  · intro preservesZero _ _
    let : CategoryTheory.Functor.PreservesZeroMorphisms F :=
      CategoryTheory.Functor.preservesZeroMorphisms_of_map_zero_object
        (preservesZero _ (CategoryTheory.Limits.isZero_zero C)).isoZero
    exact CategoryTheory.Functor.additive_of_preserves_binary_products F

#print axioms AdditiveFunctorsAndBiproducts
