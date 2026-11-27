import Mathlib.CategoryTheory.NatIso
import NotesProofs.ConcreteTensorPreservation

universe u

def ReviewedEndpoint : Prop :=
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

#print ReviewedEndpoint
#print axioms ReviewedEndpoint
