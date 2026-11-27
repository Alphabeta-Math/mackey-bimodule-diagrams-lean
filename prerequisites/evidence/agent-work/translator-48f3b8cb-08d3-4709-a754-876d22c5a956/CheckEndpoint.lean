import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

theorem CancellationAndZeroKernels :
(
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
) := by
  intro C _ _ _ _ _ _ X Y f g
  refine ⟨CategoryTheory.Preadditive.mono_iff_isZero_kernel f,
    CategoryTheory.Preadditive.epi_iff_isZero_cokernel f, ?_, ?_⟩
  · intro W i
    constructor
    · rintro ⟨h, ⟨hi⟩⟩
      refine ⟨?_, ⟨CategoryTheory.Preadditive.isLimitKernelForkOfFork hi⟩⟩
      rw [CategoryTheory.Preadditive.comp_sub, h, sub_self]
    · rintro ⟨h, ⟨hi⟩⟩
      refine ⟨?_, ⟨CategoryTheory.Preadditive.isLimitForkOfKernelFork hi⟩⟩
      exact sub_eq_zero.mp (CategoryTheory.Preadditive.comp_sub i f g ▸ h)
  · intro W p
    constructor
    · rintro ⟨h, ⟨hp⟩⟩
      refine ⟨?_, ⟨CategoryTheory.Preadditive.isColimitCokernelCoforkOfCofork hp⟩⟩
      rw [CategoryTheory.Preadditive.sub_comp, h, sub_self]
    · rintro ⟨h, ⟨hp⟩⟩
      refine ⟨?_, ⟨CategoryTheory.Preadditive.isColimitCoforkOfCokernelCofork hp⟩⟩
      exact sub_eq_zero.mp (CategoryTheory.Preadditive.sub_comp f g p ▸ h)

#print axioms CancellationAndZeroKernels
