import WattsFoundation.GeneratorRegularActions
open CategoryTheory
universe u v
namespace SmallGeneratorBridge

noncomputable def regularRight {C : Type u} [Category.{v} C] [Preadditive C]
    (P : C) (r : (End P)ᵐᵒᵖ) :
    ModuleCat.of (End P)ᵐᵒᵖ (ULift.{0} (End P)ᵐᵒᵖ) ⟶
      ModuleCat.of (End P)ᵐᵒᵖ (ULift.{0} (End P)ᵐᵒᵖ) := by
  let R := (End P)ᵐᵒᵖ
  let down : ULift.{0} R ≃ₗ[R] R := ULift.moduleEquiv
  exact ModuleCat.ofHom ((LinearEquiv.conjRingEquiv down.symm) (LinearMap.mulRight R r))

theorem regularToHom_intertwines {C : Type u} [Category.{v} C] [Preadditive C]
    (P : C) (r : (End P)ᵐᵒᵖ) :
    regularRight P r ≫ (regularToHom P).hom =
      (regularToHom P).hom ≫ (preadditiveCoyonedaObj P).map (End.asHom (MulOpposite.unop r)) := by
  apply ModuleCat.hom_ext
  ext x
  rcases x with ⟨x⟩
  change (regularToHom P).hom (ULift.up (x * r)) =
    (regularToHom P).hom (ULift.up x) ≫ End.asHom (MulOpposite.unop r)
  simpa only [MulOpposite.op_unop] using regularToHom_right P x (MulOpposite.unop r)

end SmallGeneratorBridge
