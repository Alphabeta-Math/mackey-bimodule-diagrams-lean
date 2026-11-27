import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction

set_option maxHeartbeats 2000000

theorem NormalMorphismsInAbelianCategories : (
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
) :=
(by
  intro C _ _ X Y f
  refine ⟨?_, ?_, ?_⟩
  · -- Alphabeta Math steps 1.1–2.1 obtain the kernel property through the
    -- coimage–image comparison. Mathlib uses normality in its abelian
    -- class and gives the property directly for the supplied cokernel.
    intro _ s hs
    exact ⟨CategoryTheory.Abelian.monoIsKernelOfCokernel s hs⟩
  · -- Step 3.1 argues in the opposite category. The dual Mathlib result
    -- gives the cokernel property directly for the supplied kernel.
    intro _ s hs
    exact ⟨CategoryTheory.Abelian.epiIsCokernelOfKernel s hs⟩
  · -- For the last clause of lecture notes Proposition 4.5, use the
    -- Balanced instance inferred from Abelian and both hypotheses on f.
    intro _ _
    exact CategoryTheory.isIso_of_mono_of_epi f)
