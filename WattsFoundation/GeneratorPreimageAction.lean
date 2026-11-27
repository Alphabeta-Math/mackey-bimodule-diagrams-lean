import WattsFoundation.GeneratorTransport
import WattsFoundation.GeneratorRegularIntertwining
open CategoryTheory
universe u v
namespace SmallGeneratorBridge

theorem regularPreimageIso_intertwines {C : Type u} [Category.{v} C] [Preadditive C]
    (P : C) [(preadditiveCoyonedaObj P).IsEquivalence] (r : (End P)ᵐᵒᵖ) :
    (preadditiveCoyonedaObj P).asEquivalence.inverse.map (regularRight P r) ≫
        (regularPreimageIso P).hom =
      (regularPreimageIso P).hom ≫ End.asHom (MulOpposite.unop r) := by
  let E := (preadditiveCoyonedaObj P).asEquivalence
  let f : P ⟶ P := End.asHom (MulOpposite.unop r)
  have hunit := E.unitIso.inv.naturality f
  change E.inverse.map ((preadditiveCoyonedaObj P).map f) ≫ (E.unitIso.app P).inv =
    (E.unitIso.app P).inv ≫ f at hunit
  change E.inverse.map (regularRight P r) ≫
      (E.inverse.map (regularToHom P).hom ≫ (E.unitIso.app P).inv) =
    (E.inverse.map (regularToHom P).hom ≫ (E.unitIso.app P).inv) ≫ f
  calc
    _ = E.inverse.map (regularRight P r ≫ (regularToHom P).hom) ≫ (E.unitIso.app P).inv := by
      simp only [Functor.map_comp, Category.assoc]
    _ = E.inverse.map ((regularToHom P).hom ≫ (preadditiveCoyonedaObj P).map f) ≫
        (E.unitIso.app P).inv := by rw [regularToHom_intertwines]
    _ = E.inverse.map (regularToHom P).hom ≫
        (E.inverse.map ((preadditiveCoyonedaObj P).map f) ≫ (E.unitIso.app P).inv) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = E.inverse.map (regularToHom P).hom ≫ ((E.unitIso.app P).inv ≫ f) := by rw [hunit]
    _ = _ := by simp only [Category.assoc]

end SmallGeneratorBridge
