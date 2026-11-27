import Mathlib.CategoryTheory.Abelian.Exact

axiom reviewedEndpoint :
  ∀ {𝒜 : Type*} [CategoryTheory.Category.{_} 𝒜] [CategoryTheory.Abelian 𝒜]
    {A B C : 𝒜} (f : Quiver.Hom A B) (q : Quiver.Hom B C),
    (∃ h : CategoryTheory.CategoryStruct.comp f q = 0,
      CategoryTheory.ShortComplex.Exact (CategoryTheory.ShortComplex.mk f q h) ∧ CategoryTheory.Epi q) ↔
    (∃ h : CategoryTheory.CategoryStruct.comp f q = 0,
      Nonempty (CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.CokernelCofork.ofπ q h)))

set_option pp.universes true in
#check reviewedEndpoint
#check CategoryTheory.ShortComplex.exact_iff_image_eq_kernel
#check CategoryTheory.ShortComplex.exact_iff_epi
#check CategoryTheory.Limits.CokernelCofork.ofπ
