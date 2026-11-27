import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.FiniteBiproductUniversalProperties

set_option maxHeartbeats 2000000

theorem AdditiveFunctorsAndBiproducts : (
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
) :=
(by
  intro C D _ _ _ _ _ _ _ _ F
  -- Combine the implications as in Alphabeta Math step 3.1.
  constructor
  · -- For Alphabeta Math step 1.1, Mathlib maps the finite identity-sum
    -- equation using additivity and applies the bilimit criterion.
    intro hAdditive
    exact CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive F
  · -- Alphabeta Math steps 1.2 and 2.1 start with preservation of biproducts.
    -- Proposition 3.9 supplies preservation of zero objects and finite products
    -- and coproducts. The chosen zero object supplies preservation of zero
    -- morphisms. Source finite biproducts give binary products, and
    -- finite-product preservation supplies preservation of the binary shape.
    -- Mathlib's binary-product criterion then preserves the binary biproduct
    -- pairing and codiagonal that express addition, so the finite-coproduct
    -- premise and the separate finite-biproduct theorem can remain unused.
    intro hZero hProducts _hCoproducts
    let : CategoryTheory.Functor.PreservesZeroMorphisms F :=
      CategoryTheory.Functor.preservesZeroMorphisms_of_map_zero_object
        (hZero _ (CategoryTheory.Limits.isZero_zero C)).isoZero
    exact CategoryTheory.Functor.additive_of_preserves_binary_products F)
