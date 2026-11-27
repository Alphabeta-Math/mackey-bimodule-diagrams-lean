import Mathlib.RepresentationTheory.Rep.Iso

universe u v w

set_option autoImplicit false

def endpoint : Prop :=
  ∀ (k : Type u) [Field k] (G : Type v) [Group G],
    let U := CategoryTheory.Functor.comp
      (CategoryTheory.forget₂ (Rep.{w} k G) (ModuleCat.{w} k))
      (CategoryTheory.forget₂ (ModuleCat.{w} k) AddCommGrpCat.{w})
    let V := CategoryTheory.forget₂ (ModuleCat.{w} (MonoidAlgebra k G)) AddCommGrpCat.{w}
    ∃ (F : CategoryTheory.Functor (Rep.{w} k G) (ModuleCat.{w} (MonoidAlgebra k G)))
      (H : CategoryTheory.Functor (ModuleCat.{w} (MonoidAlgebra k G)) (Rep.{w} k G)),
      CategoryTheory.Functor.comp F H = CategoryTheory.Functor.id (Rep.{w} k G) ∧
      CategoryTheory.Functor.comp H F =
        CategoryTheory.Functor.id (ModuleCat.{w} (MonoidAlgebra k G)) ∧
      CategoryTheory.Functor.comp F V = U ∧
      CategoryTheory.Functor.comp H U = V

#check endpoint
