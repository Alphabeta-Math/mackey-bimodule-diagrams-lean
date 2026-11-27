import Mathlib.Algebra.Category.ModuleCat.Basic
import MackeyDiagrams
import Proofs.Bimodule

set_option maxHeartbeats 2000000

theorem RegularModuleRightAction : (∀ (A : Type u) (B : Type v) [Ring A] [Ring B]
  (F : CategoryTheory.Functor (ModuleCat.{max u z} A) (ModuleCat.{w} B))
  [CategoryTheory.Functor.Additive F],
  let regular := ModuleCat.of A (ULift.{z} A)
  let lift := LinearEquiv.symm (ULift.moduleEquiv : ULift.{z} A ≃ₗ[A] A)
  let M := CategoryTheory.Functor.obj F regular
  ∃ N : Bimodule.1 B A M,
    N.1 = ModuleCat.isModule M ∧
    ∀ (a : A) (m : M),
      @SMul.smul (MulOpposite A) M
        N.2.1.toDistribMulAction.toMulAction.toSemigroupAction.toSMul (MulOpposite.op a) m =
      ModuleCat.Hom.hom
        (CategoryTheory.Functor.map F
          (ModuleCat.ofHom (LinearEquiv.conjRingEquiv lift (LinearMap.mulRight A a)))) m) :=
(by
  intro A B _ _ F _ regular lift M
  -- Xiao, Theorem 1.1, gives the action formula on the regular module.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf#page=2
  -- Alphabeta Math 1.1–1.4. Right multiplication represents Aᵐᵒᵖ in
  -- the endomorphism ring of the regular left A-module. Multiplication
  -- in Aᵐᵒᵖ accounts for the reversal in step 1.3.
  -- Conjugate by the ULift equivalence to use the specified source universe.
  let regularAction : MulOpposite A →+* CategoryTheory.End regular :=
    (ModuleCat.endRingEquiv regular).symm.toRingHom.comp
      ((LinearEquiv.conjRingEquiv lift).toRingHom.comp
        (RingEquiv.moduleEndSelf A).toRingHom)
  -- Functoriality handles the unit and multiplication. Additivity handles
  -- sums and zero, so the induced map on endomorphisms is a ring homomorphism.
  let mapEnd : CategoryTheory.End regular →+* CategoryTheory.End M :=
    { F.mapEnd regular with
      map_zero' := by
        apply CategoryTheory.End.ext
        exact F.map_zero _ _
      map_add' := by
        intro f g
        apply CategoryTheory.End.ext
        exact F.map_add }
  let action : MulOpposite A →+* Module.End B M :=
    (ModuleCat.endRingEquiv M).toRingHom.comp (mapEnd.comp regularAction)
  -- Pull back the evaluation action to package the right-module laws of
  -- steps 1.1–1.4, including additivity in the module argument and both zero laws.
  let right : Module (MulOpposite A) M := Module.compHom M action
  -- Step 2.1. The images of the right multiplications are B-linear.
  -- Step 3.1. The witness retains the original B-module structure.
  refine ⟨⟨ModuleCat.isModule M, ⟨right, ⟨?_⟩⟩⟩, rfl, ?_⟩
  · intro a b m
    show action a (b • m) = b • action a m
    exact (action a).map_smul b m
  · intro a m
    -- At op a the regular-module equivalence reduces to LinearMap.mulRight A a.
    rfl)
