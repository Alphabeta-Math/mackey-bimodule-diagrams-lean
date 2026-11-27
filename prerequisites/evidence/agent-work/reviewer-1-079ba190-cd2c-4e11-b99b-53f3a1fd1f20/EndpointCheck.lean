import Mathlib.Algebra.Homology.ShortComplex.Exact

#check (∀ {𝒜 : Type*} [CategoryTheory.Category.{_} 𝒜] [CategoryTheory.Abelian 𝒜]
  {A B C : 𝒜} (f : Quiver.Hom A B) (q : Quiver.Hom B C),
  (∃ h : CategoryTheory.CategoryStruct.comp f q = 0,
    CategoryTheory.ShortComplex.Exact (CategoryTheory.ShortComplex.mk f q h) ∧ CategoryTheory.Epi q) ↔
  (∃ h : CategoryTheory.CategoryStruct.comp f q = 0,
    Nonempty (CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.CokernelCofork.ofπ q h))))

#check CategoryTheory.ShortComplex.exact_iff_epi
#check CategoryTheory.ShortComplex.exact_iff_epi_kernel_lift
#check CategoryTheory.ShortComplex.exact_and_epi_g_iff_g_is_cokernel
#check CategoryTheory.Limits.CokernelCofork.ofπ
#print axioms CategoryTheory.ShortComplex.exact_and_epi_g_iff_g_is_cokernel
