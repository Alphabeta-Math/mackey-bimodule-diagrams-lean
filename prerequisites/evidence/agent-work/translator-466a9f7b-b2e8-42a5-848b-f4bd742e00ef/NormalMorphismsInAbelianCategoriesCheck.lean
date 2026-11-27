import Mathlib.CategoryTheory.Abelian.Basic

theorem NormalMorphismsInAbelianCategories :
    ∀ (C : Type _) [CategoryTheory.Category.{_} C] [CategoryTheory.Abelian C]
      {X Y : C} (f : Quiver.Hom X Y),
      (∀ [CategoryTheory.Mono f] (s : CategoryTheory.Limits.CokernelCofork f),
        CategoryTheory.Limits.IsColimit s →
          Nonempty (CategoryTheory.Limits.IsLimit
            (CategoryTheory.Limits.KernelFork.ofι f
              (CategoryTheory.Limits.CokernelCofork.condition s)))) ∧
      (∀ [CategoryTheory.Epi f] (s : CategoryTheory.Limits.KernelFork f),
        CategoryTheory.Limits.IsLimit s →
          Nonempty (CategoryTheory.Limits.IsColimit
            (CategoryTheory.Limits.CokernelCofork.ofπ f
              (CategoryTheory.Limits.KernelFork.condition s)))) ∧
      (∀ [CategoryTheory.Mono f] [CategoryTheory.Epi f], CategoryTheory.IsIso f) := by
  intro C _ _ X Y f
  exact ⟨fun [_] s h => ⟨CategoryTheory.Abelian.monoIsKernelOfCokernel s h⟩,
    fun [_] s h => ⟨CategoryTheory.Abelian.epiIsCokernelOfKernel s h⟩,
    fun [_] [_] => CategoryTheory.isIso_of_mono_of_epi f⟩

set_option pp.universes true in
#check NormalMorphismsInAbelianCategories
#print axioms NormalMorphismsInAbelianCategories
