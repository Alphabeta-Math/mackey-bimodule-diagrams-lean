import Mathlib.CategoryTheory.Abelian.Basic

set_option pp.universes true in
#check (∀ (C : Type _) [CategoryTheory.Category.{_} C] [CategoryTheory.Abelian C]
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
  (∀ [CategoryTheory.Mono f] [CategoryTheory.Epi f], CategoryTheory.IsIso f))

#check CategoryTheory.Abelian.monoIsKernelOfCokernel
#check CategoryTheory.Abelian.epiIsCokernelOfKernel
#check CategoryTheory.isIso_of_mono_of_epi
#check CategoryTheory.Abelian.ofCoimageImageComparisonIsIso
#check CategoryTheory.Abelian.coimageImageComparison

section
universe u v
variable (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
variable {X Y : C} (f : Quiver.Hom X Y)
#synth CategoryTheory.Limits.HasKernel f
#synth CategoryTheory.Limits.HasCokernel f
#synth CategoryTheory.Balanced C
end
