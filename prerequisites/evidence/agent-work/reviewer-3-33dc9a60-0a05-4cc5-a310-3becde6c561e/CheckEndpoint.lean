import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

universe u v

def reviewedEndpoint : Prop :=
  ∀ (C : Type u) [CategoryTheory.Category.{v} C] [CategoryTheory.Preadditive C]
    [CategoryTheory.Limits.HasZeroObject C] [CategoryTheory.Limits.HasFiniteBiproducts C]
    [CategoryTheory.Limits.HasKernels C] [CategoryTheory.Limits.HasCokernels C]
    {X Y : C} (f g : Quiver.Hom X Y),
  (CategoryTheory.Mono f ↔ CategoryTheory.Limits.IsZero (CategoryTheory.Limits.kernel f)) ∧
  (CategoryTheory.Epi f ↔ CategoryTheory.Limits.IsZero (CategoryTheory.Limits.cokernel f)) ∧
  (∀ {W : C} (i : Quiver.Hom W X),
    (∃ h : CategoryTheory.CategoryStruct.comp i f = CategoryTheory.CategoryStruct.comp i g,
      Nonempty (CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.Fork.ofι i h))) ↔
    (∃ h : CategoryTheory.CategoryStruct.comp i (f - g) = 0,
      Nonempty (CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.KernelFork.ofι i h)))) ∧
  (∀ {W : C} (p : Quiver.Hom Y W),
    (∃ h : CategoryTheory.CategoryStruct.comp f p = CategoryTheory.CategoryStruct.comp g p,
      Nonempty (CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.Cofork.ofπ p h))) ↔
    (∃ h : CategoryTheory.CategoryStruct.comp (f - g) p = 0,
      Nonempty (CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.CokernelCofork.ofπ p h))))

#print reviewedEndpoint
