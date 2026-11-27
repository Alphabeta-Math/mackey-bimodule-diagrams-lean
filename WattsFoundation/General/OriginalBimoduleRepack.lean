import WattsFoundation.General.OriginalBimoduleAdapter

set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace WattsFoundation.General
universe u v
variable (R S : Type u) [Ring R] [Ring S]
variable (M : OriginalBimodule.{u,v} R S) (N : ModuleCat.{max u v} S) (e : M.1 ≅ N)

noncomputable def repackRightAction : MulOpposite R →+* Module.End S N := by
  let MB := originalToConcreteObj R S M
  letI : Module (MulOpposite R) M.1 := MB.rightModule
  letI : SMulCommClass (MulOpposite R) S M.1 := MB.commuting
  exact (LinearEquiv.conjRingEquiv e.toLinearEquiv).toRingHom.comp (Module.toModuleEnd S M.1)

@[instance_reducible] noncomputable def repackRightModule : Module (MulOpposite R) N :=
  Module.compHom N (repackRightAction R S M N e)

theorem repackRightCommutes :
    letI : Module (MulOpposite R) N := repackRightModule R S M N e
    SMulCommClass (MulOpposite R) S N := by
  letI : Module (MulOpposite R) N := repackRightModule R S M N e
  exact ⟨fun a s n => (repackRightAction R S M N e a).map_smul s n⟩

noncomputable def repackBimodule : OriginalBimodule.{u,v} R S :=
  ⟨N, ⟨⟨inferInstance, ⟨repackRightModule R S M N e, repackRightCommutes R S M N e⟩⟩, rfl⟩⟩

theorem repackRight_hom (m : M.1) (r : R) :
    originalRight R S (repackBimodule R S M N e) (e.hom m) r =
      e.hom (originalRight R S M m r) := by
  let MB := originalToConcreteObj R S M
  letI : Module (MulOpposite R) M.1 := MB.rightModule
  letI : SMulCommClass (MulOpposite R) S M.1 := MB.commuting
  change ((LinearEquiv.conjRingEquiv e.toLinearEquiv)
    (Module.toModuleEnd S M.1 (MulOpposite.op r))) (e.hom m) =
      e.hom (MulOpposite.op r • m)
  simp

end WattsFoundation.General
