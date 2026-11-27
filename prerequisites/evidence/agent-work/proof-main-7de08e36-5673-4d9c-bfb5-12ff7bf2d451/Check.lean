import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.ModuleQuotientUniversalProperty

#check ModuleCat.kernelIsLimit
#check ModuleCat.cokernelIsColimit
#check LinearMap.quotKerEquivRange
#check ModuleCat.mono_iff_injective
#check ModuleCat.epi_iff_surjective
#check LinearMap.quotKerEquivRange_apply_mk

theorem ModuleKernelsCokernelsAndImages : (
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
) :=
(by
  intro R _ M N f
  dsimp only
  -- Proposition 5.5 describes the kernel and image of the underlying linear map.
  refine ⟨fun _ => LinearMap.mem_ker, fun _ => LinearMap.mem_range, ?_, ?_, ?_,
    ModuleCat.mono_iff_injective f, ModuleCat.epi_iff_surjective f⟩
  -- The notes prove the kernel by corestricting maps with zero composite.
  -- The pinned limit has exactly the submodule inclusion as its leg.
  · exact ⟨CategoryTheory.Limits.KernelFork.condition (ModuleCat.kernelCone f),
      ⟨ModuleCat.kernelIsLimit f⟩⟩
  -- The pinned colimit packages the notes' quotient argument (Proposition 5.4):
  -- a map with zero composite kills the range and descends uniquely along mkQ.
  · exact ⟨CategoryTheory.Limits.CokernelCofork.condition (ModuleCat.cokernelCocone f),
      ⟨ModuleCat.cokernelIsColimit f⟩⟩
  -- Alphabeta Math, thm-first-isomorphism-theorem-modules, steps 1.1–4.1.
  -- The pinned equivalence combines descent (1.1) with injectivity of the lift,
  -- since the submodule being quotiented out is exactly its original kernel
  -- (2.2 and 3.1). It constructs an equivalence onto the range of that lift
  -- and identifies that range with the original image (2.1 and 4.1).
  -- The representative computation checks the map specified in the notes.
  · exact ⟨LinearMap.quotKerEquivRange (ModuleCat.Hom.hom f),
      LinearMap.quotKerEquivRange_apply_mk (ModuleCat.Hom.hom f)⟩
)

#print axioms ModuleKernelsCokernelsAndImages
