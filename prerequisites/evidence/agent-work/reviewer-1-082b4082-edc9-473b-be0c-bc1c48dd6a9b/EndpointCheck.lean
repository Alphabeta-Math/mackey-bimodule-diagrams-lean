import Mathlib.Algebra.Category.ModuleCat.Abelian

universe u v

theorem endpointCheck :
    ∀ (R : Type u) [Ring R],
      CategoryTheory.LocallySmall.{v} (ModuleCat.{v} R) ∧
        Nonempty (CategoryTheory.Abelian (ModuleCat.{v} R)) :=
  fun R _ => ⟨(CategoryTheory.locallySmall_self (ModuleCat.{v} R)), ⟨ModuleCat.abelian⟩⟩

#print axioms endpointCheck
