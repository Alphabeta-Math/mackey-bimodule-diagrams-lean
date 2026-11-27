import Mathlib
import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.CanonicalWattsNaturalTransformation
import NotesProofs.RegularModuleTensorUnits
import NotesProofs.FreeModulesAndPresentations
import NotesProofs.TensorPreservesCoproducts
import NotesProofs.TensorPreservesCokernels

set_option maxHeartbeats 2000000

theorem EilenbergWatts : (
∀ (R S : Type u) [Ring R] [Ring S],
  (∀ (F : CategoryTheory.Functor (ModuleCat.{u} R) (ModuleCat.{u} S))
    [CategoryTheory.Functor.Additive F],
    NotesProofs.WattsPreservesCokernels F →
    NotesProofs.WattsPreservesCoproducts F →
    CategoryTheory.IsIso (NotesProofs.wattsComparisonNatTrans F)) ∧
  (∀ (B : Type u) [AddCommGroup B] [Module S B] [Module (MulOpposite R) B]
    [SMulCommClass (MulOpposite R) S B],
    let T := NotesProofs.concreteTensorFunctor (R := R) (S := S) B
    CategoryTheory.Functor.Additive T ∧
      NotesProofs.WattsPreservesCokernels T ∧
      NotesProofs.WattsPreservesCoproducts T)
) :=
(by
  intro R S _ _
  constructor
  · intro F _ hc hp
    exact (NotesProofs.wattsNaturalIso F hc hp).isIso_hom
  · intro B _ _ _ _
    exact ⟨inferInstance, NotesProofs.concreteTensorFunctor_preservesCokernels B,
      NotesProofs.concreteTensorFunctor_preservesCoproducts B⟩
)
