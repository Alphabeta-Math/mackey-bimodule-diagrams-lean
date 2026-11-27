import WattsFoundation.SmallGeneratorBridge
import Mathlib.Algebra.Module.ULift

open CategoryTheory CategoryTheory.Limits
universe u v

namespace SmallGeneratorBridge

noncomputable def regularToHom {C : Type u} [Category.{v} C] [Preadditive C] (P : C) :
    ModuleCat.of (End P)ᵐᵒᵖ (ULift.{0} (End P)ᵐᵒᵖ) ≅ (preadditiveCoyonedaObj P).obj P := by
  let R := (End P)ᵐᵒᵖ
  let unopAdd : R ≃+ (preadditiveCoyonedaObj P).obj P := MulOpposite.opAddEquiv.symm.trans End.addEquiv
  let regular : R ≃ₗ[R] (preadditiveCoyonedaObj P).obj P :=
    { unopAdd with map_smul' := fun _ _ => rfl }
  exact ((ULift.moduleEquiv : ULift.{0} R ≃ₗ[R] R).trans regular).toModuleIso

end SmallGeneratorBridge
