import Mathlib
import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.EilenbergWatts
import NotesProofs.RegularModuleTensorUnits

set_option maxHeartbeats 2000000

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

theorem NaturalTransformationsByRegularEvaluation : (
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
        η = NotesProofs.tensorBimoduleMapNatTrans β)
) :=
(by
  intro R S _ _
  constructor
  · intro F G _ _ hFc hFp hGc hGp
    letI : PreservesFiniteColimits F := NotesProofs.mathlibFiniteColimits_of_watts F hFc
    letI : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) F := NotesProofs.mathlibCoproducts_of_watts F hFp
    letI : PreservesFiniteColimits G := NotesProofs.mathlibFiniteColimits_of_watts G hGc
    letI : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) G := NotesProofs.mathlibCoproducts_of_watts G hGp
    let FF : NotesProofs.General.ConcreteBimodule.GoodFunctors.{u,u} R S := ⟨F, ⟨inferInstance, inferInstance, inferInstance⟩⟩
    let GG : NotesProofs.General.ConcreteBimodule.GoodFunctors.{u,u} R S := ⟨G, ⟨inferInstance, inferInstance, inferInstance⟩⟩
    let E := NotesProofs.General.ConcreteBimodule.eilenbergWattsCanonical.{u,u} R S
    let lift : (F ⟶ G) ≃ (FF ⟶ GG) :=
      ⟨fun η => (ObjectProperty.homMk η : FF ⟶ GG), fun η => η.hom, fun _ => rfl, fun η => by apply ObjectProperty.hom_ext; rfl⟩
    let e := lift.trans (E.fullyFaithfulInverse.homEquiv (X := FF) (Y := GG))
    refine ⟨e, ?_⟩
    intro η
    rfl
  · intro B D _ _ _ _ _ _ _ _ TB TD η
    refine ⟨NotesProofs.tensorNatEvaluationMap η, ?_, ?_⟩
    · exact (NotesProofs.tensorNatEvaluation_complete η).symm
    · intro β hβ
      have h := congrArg NotesProofs.tensorNatEvaluationMap hβ.symm
      simpa only [NotesProofs.tensorNatEvaluation_induced] using h
)
