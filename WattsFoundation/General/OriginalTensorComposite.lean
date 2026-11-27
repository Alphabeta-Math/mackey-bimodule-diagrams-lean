import WattsFoundation.General.OriginalTensorUnit

/-! Composition of paper-style bimodules: the outer right action on the
balanced tensor is induced by functoriality. -/

set_option backward.isDefEq.respectTransparency false

namespace WattsFoundation.General

universe u v
open CategoryTheory

variable (R S T : Type u) [Ring R] [Ring S] [Ring T]
variable (C : OriginalBimodule.{u,v} S T) (B : OriginalBimodule.{u,v} R S)

/-- The action of the opposite ring on the balanced tensor of two bimodules. -/
noncomputable def originalCompositeRightAction :
    MulOpposite R →+* Module.End T ((originalTensor S T C).obj B.1) := by
  let MB := originalToConcreteObj R S B
  letI : Module (MulOpposite R) B.1 := MB.rightModule
  letI : SMulCommClass (MulOpposite R) S B.1 := MB.commuting
  let F := originalTensor S T C
  letI : F.Additive := ((originalWattsWithEvaluation.{u,v} S T).functor.obj C).property.1
  let actionB : MulOpposite R →+* CategoryTheory.End B.1 :=
    (ModuleCat.endRingEquiv B.1).symm.toRingHom.comp (Module.toModuleEnd S B.1)
  let mapEnd : CategoryTheory.End B.1 →+* CategoryTheory.End (F.obj B.1) :=
    { F.mapEnd B.1 with
      map_zero' := by apply CategoryTheory.End.ext; exact F.map_zero _ _
      map_add' := by intro f g; apply CategoryTheory.End.ext; exact F.map_add }
  exact (ModuleCat.endRingEquiv (F.obj B.1)).toRingHom.comp (mapEnd.comp actionB)

/-- The balanced tensor has the induced right module structure. -/
@[instance_reducible] noncomputable def originalCompositeRightModule :
    Module (MulOpposite R) ((originalTensor S T C).obj B.1) :=
  Module.compHom ((originalTensor S T C).obj B.1) (originalCompositeRightAction R S T C B)

noncomputable local instance OriginalTensorComposite_right :
    Module (MulOpposite R) ((originalTensor S T C).obj B.1) := originalCompositeRightModule R S T C B

/-- The induced right action commutes with the outer left action. -/
theorem originalCompositeRightCommutes :
    SMulCommClass (MulOpposite R) T ((originalTensor S T C).obj B.1) :=
  ⟨fun a t x => (originalCompositeRightAction R S T C B a).map_smul t x⟩

/-- The composed bimodule in the original workflow's encoding. -/
noncomputable def originalCompositeBimodule : OriginalBimodule.{u,v} R T :=
  ⟨(originalTensor S T C).obj B.1,
    ⟨⟨inferInstance, ⟨originalCompositeRightModule R S T C B, originalCompositeRightCommutes R S T C B⟩⟩, rfl⟩⟩

/-- On elementary tensors, the induced right action acts on the second factor. -/
theorem originalCompositeBimodule_right (c : C.1) (b : B.1) (r : R) :
    originalRight R T (originalCompositeBimodule R S T C B)
      (originalTensorPure S T C B.1 c b) r =
        originalTensorPure S T C B.1 c (originalRight R S B b r) := by
  let MB := originalToConcreteObj R S B
  letI : Module (MulOpposite R) B.1 := MB.rightModule
  letI : SMulCommClass (MulOpposite R) S B.1 := MB.commuting
  change ((originalTensor S T C).map (ModuleCat.ofHom
    (Module.toModuleEnd S B.1 (MulOpposite.op r)))).hom
      (originalTensorPure S T C B.1 c b) = _
  rw [originalTensorPure_map]
  rfl

#print axioms originalCompositeBimodule
#print axioms originalCompositeBimodule_right

end WattsFoundation.General
