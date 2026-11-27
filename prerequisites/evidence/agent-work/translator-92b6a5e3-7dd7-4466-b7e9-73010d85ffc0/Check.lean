import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.EssentiallySmall

theorem ModuleCategoriesAreAbelian :
    ∀ (R : Type u) [Ring R],
      CategoryTheory.LocallySmall.{v} (ModuleCat.{v} R) ∧
        Nonempty (CategoryTheory.Abelian (ModuleCat.{v} R)) := by
  intro R _
  exact ⟨CategoryTheory.locallySmall_self (ModuleCat.{v} R), ⟨ModuleCat.abelian⟩⟩

set_option pp.universes true in
#check ModuleCategoriesAreAbelian
#print axioms ModuleCategoriesAreAbelian
