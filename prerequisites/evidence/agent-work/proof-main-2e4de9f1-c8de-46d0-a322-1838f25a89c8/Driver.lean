import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.RegularModuleSmallProjectiveGenerator

set_option maxHeartbeats 2000000

theorem RegularEvaluationRightAction : (
∀ (R : Type u) (S : Type v) [Ring R] [Ring S]
  (F : CategoryTheory.Functor (ModuleCat.{max u z} R) (ModuleCat.{w} S))
  [CategoryTheory.Functor.Additive F],
  let A := ModuleCat.of R (ULift.{z} R)
  let B := CategoryTheory.Functor.obj F A
  let rho : R → Quiver.Hom A A := fun r =>
    ModuleCat.ofHom
      (LinearEquiv.conjRingEquiv
        (LinearEquiv.symm (ULift.moduleEquiv : LinearEquiv (RingHom.id R) (ULift.{z} R) R))
        (LinearMap.mulRight R r))
  ∃ right : Module (MulOpposite R) ↥B,
    letI : Module (MulOpposite R) ↥B := right
    SMulCommClass (MulOpposite R) S ↥B ∧
      ∀ (r : R) (b : ↥B),
        SMul.smul (MulOpposite.op r) b =
          ModuleCat.Hom.hom (CategoryTheory.Functor.map F (rho r)) b
) :=
(by
  intro R S _ _ F _
  -- Ian X, Lemma 9.2 (p. 29), and Alphabeta Math steps 1.1–1.4.
  -- NotesProofs.WattsActions (source SHA-256
  -- aff94142f5443ca41e7f7f0f384740b4acfd1484f13b5f34afe83d5aa760c9f3)
  -- packages the pointwise laws by composing RingEquiv.moduleEndSelf with
  -- ULift conjugation and F's map on endomorphisms. Functoriality preserves
  -- unit and composition, and additivity preserves sums and zero.
  -- Step 2.1 is wattsRight_commutes, by S-linearity of the images.
  -- Step 3.1 pairs these witnesses on the given left S-module.
  refine ⟨NotesProofs.wattsRightModule F, NotesProofs.wattsRight_commutes F, ?_⟩
  intro r b
  -- Both lifted endomorphisms apply x ↦ ULift.up (x.down * r).
  -- The supplier and reviewed formula use the same conjugated map, so
  -- reduction identifies their images under F.
  calc
    _ = ChoiceFreeWatts.right F r b := NotesProofs.wattsRight_apply F r b
    _ = _ := rfl)
