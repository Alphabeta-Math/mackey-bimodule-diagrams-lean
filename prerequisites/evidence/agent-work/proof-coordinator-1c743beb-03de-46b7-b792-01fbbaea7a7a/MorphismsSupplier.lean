import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.EilenbergWatts
import NotesProofs.RegularModuleTensorUnits
import NotesProofs.ReviewedWattsMorphismsConnection

universe u

#check (ReviewedWattsMorphismsConnection.{u} :
∀ (R S : Type u) [Ring R] [Ring S],
  (∀ (F G : CategoryTheory.Functor (ModuleCat.{u} R) (ModuleCat.{u} S))
      [CategoryTheory.Functor.Additive F] [CategoryTheory.Functor.Additive G],
    NotesProofs.WattsPreservesCokernels F →
    NotesProofs.WattsPreservesCoproducts F →
    NotesProofs.WattsPreservesCokernels G →
    NotesProofs.WattsPreservesCoproducts G →
    let A := ChoiceFreeWatts.regular.{u, u} R
    let B₀ := CategoryTheory.Functor.obj F A
    let D₀ := CategoryTheory.Functor.obj G A
    letI _rightF : Module (MulOpposite R) (ModuleCat.carrier B₀) :=
      NotesProofs.wattsRightModule F
    letI _rightG : Module (MulOpposite R) (ModuleCat.carrier D₀) :=
      NotesProofs.wattsRightModule G
    ∃ e : Equiv (CategoryTheory.NatTrans F G)
        (NotesProofs.BimoduleMap (R := R) (S := S)
          (M := ModuleCat.carrier B₀) (N := ModuleCat.carrier D₀)),
      ∀ η : CategoryTheory.NatTrans F G,
        Subtype.val (Equiv.toFun e η) = ModuleCat.Hom.hom (CategoryTheory.NatTrans.app η A)) ∧
  (∀ (B D : Type u) [AddCommGroup B] [AddCommGroup D]
      [Module S B] [Module S D] [Module (MulOpposite R) B] [Module (MulOpposite R) D]
      [SMulCommClass (MulOpposite R) S B] [SMulCommClass (MulOpposite R) S D],
    let TB := NotesProofs.concreteTensorFunctor (R := R) (S := S) B
    let TD := NotesProofs.concreteTensorFunctor (R := R) (S := S) D
    ∀ η : CategoryTheory.NatTrans TB TD,
      ∃! β : NotesProofs.BimoduleMap (R := R) (S := S) (M := B) (N := D),
        η = NotesProofs.tensorBimoduleMapNatTrans β))
#print axioms ReviewedWattsMorphismsConnection
