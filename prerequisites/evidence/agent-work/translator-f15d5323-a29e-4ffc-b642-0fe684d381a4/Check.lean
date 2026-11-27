import Mathlib.Algebra.Homology.ShortComplex.Exact

theorem ExactPresentationsAreCokernels :
    ∀ {𝒜 : Type*} [CategoryTheory.Category.{_} 𝒜] [CategoryTheory.Abelian 𝒜]
      {A B C : 𝒜} (f : Quiver.Hom A B)
      (q : Quiver.Hom B C),
      (∃ h : CategoryTheory.CategoryStruct.comp f q = 0,
        CategoryTheory.ShortComplex.Exact (CategoryTheory.ShortComplex.mk f q h) ∧
          CategoryTheory.Epi q) ↔
      (∃ h : CategoryTheory.CategoryStruct.comp f q = 0,
        Nonempty (CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.CokernelCofork.ofπ q h))) := by
  intro 𝒜 _ _ A B C f q
  constructor
  · rintro ⟨h, hexact⟩
    exact ⟨h, (CategoryTheory.ShortComplex.exact_and_epi_g_iff_g_is_cokernel
      (CategoryTheory.ShortComplex.mk f q h)).mp hexact⟩
  · rintro ⟨h, hcokernel⟩
    exact ⟨h, (CategoryTheory.ShortComplex.exact_and_epi_g_iff_g_is_cokernel
      (CategoryTheory.ShortComplex.mk f q h)).mpr hcokernel⟩

#check ExactPresentationsAreCokernels
#print axioms ExactPresentationsAreCokernels
