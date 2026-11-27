import NotesProofs.ConcreteTensorCoproduct

/-! The canonical right action on the value of an additive functor at the
regular module, constructed directly from Mathlib endomorphism-ring maps. -/

namespace NotesProofs

universe u v z w

open CategoryTheory

variable {A : Type u} {B : Type v} [Ring A] [Ring B]
variable (F : ModuleCat.{max u z} A ⥤ ModuleCat.{w} B) [F.Additive]

/-- The action of the opposite ring on `F(A)` by images of right multiplication. -/
def wattsRightAction : MulOpposite A →+* Module.End B (ChoiceFreeWatts.M F) :=
  let regular := ChoiceFreeWatts.regular.{u,z} A
  let lift := (ULift.moduleEquiv : ULift.{z} A ≃ₗ[A] A).symm
  let regularAction : MulOpposite A →+* CategoryTheory.End regular :=
    (ModuleCat.endRingEquiv regular).symm.toRingHom.comp
      ((LinearEquiv.conjRingEquiv lift).toRingHom.comp
        (RingEquiv.moduleEndSelf A).toRingHom)
  let mapEnd : CategoryTheory.End regular →+* CategoryTheory.End (F.obj regular) :=
    { F.mapEnd regular with
      map_zero' := by apply CategoryTheory.End.ext; exact F.map_zero _ _
      map_add' := by intro f g; apply CategoryTheory.End.ext; exact F.map_add }
  (ModuleCat.endRingEquiv (F.obj regular)).toRingHom.comp (mapEnd.comp regularAction)

/-- The regular-module value, equipped with the induced right module structure. -/
@[instance_reducible] def wattsRightModule : Module (MulOpposite A) (ChoiceFreeWatts.M F) :=
  Module.compHom (ChoiceFreeWatts.M F) (wattsRightAction F)

local instance WattsActions_local1 : Module (MulOpposite A) (ChoiceFreeWatts.M F) := wattsRightModule F

/-- The induced right action commutes with the target-ring action. -/
theorem wattsRight_commutes : SMulCommClass (MulOpposite A) B (ChoiceFreeWatts.M F) :=
  ⟨fun a b m => (wattsRightAction F a).map_smul b m⟩

/-- It agrees on each ring element with the established comparison action. -/
theorem wattsRight_apply (a : A) (m : ChoiceFreeWatts.M F) :
    MulOpposite.op a • m = ChoiceFreeWatts.right F a m := rfl

#print axioms wattsRight_commutes
#print axioms wattsRight_apply

end NotesProofs
