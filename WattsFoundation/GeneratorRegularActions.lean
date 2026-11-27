import WattsFoundation.GeneratorRegularUnit

open CategoryTheory
universe u v
namespace SmallGeneratorBridge

@[simp] theorem regularToHom_up {C : Type u} [Category.{v} C] [Preadditive C]
    (P : C) (r : (End P)ᵐᵒᵖ) :
    (regularToHom P).hom (ULift.up r) = End.asHom (MulOpposite.unop r) := by
  rfl

theorem regularToHom_right {C : Type u} [Category.{v} C] [Preadditive C]
    (P : C) (r : (End P)ᵐᵒᵖ) (p : End P) :
    (regularToHom P).hom (ULift.up (r * MulOpposite.op p)) =
      (regularToHom P).hom (ULift.up r) ≫ End.asHom p := by
  simp only [regularToHom_up]
  rfl

end SmallGeneratorBridge
