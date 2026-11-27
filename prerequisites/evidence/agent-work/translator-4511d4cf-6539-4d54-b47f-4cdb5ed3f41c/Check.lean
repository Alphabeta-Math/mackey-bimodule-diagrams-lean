import NotesProofs.ConcreteTensorPreservation
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

universe u

private theorem comparison_isIso
    {R S : Type u} [Ring R] [Ring S]
    (F : CategoryTheory.Functor (ModuleCat.{u} R) (ModuleCat.{u} S))
    [CategoryTheory.Functor.Additive F]
    (hcok : NotesProofs.WattsPreservesCokernels F)
    (hcop : NotesProofs.WattsPreservesCoproducts F) :
    CategoryTheory.IsIso (NotesProofs.wattsComparisonNatTrans F) := by
  let (X : ModuleCat.{u} R) :
      CategoryTheory.IsIso (CategoryTheory.NatTrans.app (NotesProofs.wattsComparisonNatTrans F) X) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).2
      (NotesProofs.watts_comparison_bijective F hcok hcop X)
  exact CategoryTheory.NatIso.isIso_of_isIso_app _

theorem EilenbergWatts :
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
          NotesProofs.WattsPreservesCoproducts T) := by
  intro R S _ _
  refine ⟨fun F _ hcok hcop => comparison_isIso F hcok hcop, ?_⟩
  intro B _ _ _ _
  exact ⟨NotesProofs.concreteTensorFunctor_additive B,
    NotesProofs.concreteTensorFunctor_preservesCokernels B,
    NotesProofs.concreteTensorFunctor_preservesCoproducts B⟩

#print axioms EilenbergWatts
