import Mathlib.Algebra.Category.ModuleCat.Abelian

universe u v

theorem ReviewedModuleCategoriesConnection : (∀ (R : Type u) [Ring R], CategoryTheory.LocallySmall.{v} (ModuleCat.{v} R) ∧ Nonempty (CategoryTheory.Abelian (ModuleCat.{v} R))) := by
  intro R _
  exact ⟨inferInstance, ⟨inferInstance⟩⟩

#print axioms ReviewedModuleCategoriesConnection
