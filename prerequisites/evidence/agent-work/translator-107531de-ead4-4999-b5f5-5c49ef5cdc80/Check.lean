import Mathlib.Algebra.Category.ModuleCat.Kernels

theorem ModuleKernelsCokernelsAndImages :
  ∀ (R : Type _) [Ring R] {M N : ModuleCat.{_} R} (f : Quiver.Hom M N),
    let g := ModuleCat.Hom.hom f
    let ker := LinearMap.ker g
    let im := LinearMap.range g
    (∀ m : M, m ∈ ker ↔ g m = 0) ∧
    (∀ n : N, n ∈ im ↔ ∃ m : M, g m = n) ∧
    (∃ h : CategoryTheory.CategoryStruct.comp
        (ModuleCat.ofHom (Submodule.subtype ker)) f = 0,
      Nonempty (CategoryTheory.Limits.IsLimit
        (CategoryTheory.Limits.KernelFork.ofι (ModuleCat.ofHom (Submodule.subtype ker)) h))) ∧
    (∃ h : CategoryTheory.CategoryStruct.comp f (ModuleCat.ofHom (Submodule.mkQ im)) = 0,
      Nonempty (CategoryTheory.Limits.IsColimit
        (CategoryTheory.Limits.CokernelCofork.ofπ (ModuleCat.ofHom (Submodule.mkQ im)) h))) ∧
    (∃ e : LinearEquiv (RingHom.id R) (HasQuotient.Quotient M ker) ↥im,
      ∀ m : M, (e (Submodule.mkQ ker m) : N) = g m) ∧
    (CategoryTheory.Mono f ↔ Function.Injective ⇑g) ∧
    (CategoryTheory.Epi f ↔ Function.Surjective ⇑g)
  := by
  intro R _ M N f
  dsimp only
  refine ⟨fun _ => LinearMap.mem_ker, fun _ => LinearMap.mem_range, ?_, ?_, ?_,
    ModuleCat.mono_iff_injective f, ModuleCat.epi_iff_surjective f⟩
  · exact ⟨CategoryTheory.Limits.KernelFork.condition (ModuleCat.kernelCone f),
      ⟨ModuleCat.kernelIsLimit f⟩⟩
  · exact ⟨CategoryTheory.Limits.CokernelCofork.condition (ModuleCat.cokernelCocone f),
      ⟨ModuleCat.cokernelIsColimit f⟩⟩
  · exact ⟨LinearMap.quotKerEquivRange (ModuleCat.Hom.hom f),
      LinearMap.quotKerEquivRange_apply_mk (ModuleCat.Hom.hom f)⟩

#print axioms ModuleKernelsCokernelsAndImages
