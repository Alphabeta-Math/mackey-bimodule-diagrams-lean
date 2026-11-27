import Mathlib.CategoryTheory.Abelian.Basic

#check (
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
  (∀ [CategoryTheory.Mono f] [CategoryTheory.Epi f], CategoryTheory.IsIso f)
  : Prop)

#check @CategoryTheory.Abelian.monoIsKernelOfCokernel
#check @CategoryTheory.Abelian.epiIsCokernelOfKernel
#check @CategoryTheory.isIso_of_mono_of_epi

#check @CategoryTheory.Abelian.ofCoimageImageComparisonIsIso

section
variable (C : Type*) [CategoryTheory.Category C] [CategoryTheory.Abelian C]
#synth CategoryTheory.Balanced C
#synth CategoryTheory.Limits.HasKernels C
#synth CategoryTheory.Limits.HasCokernels C
end
