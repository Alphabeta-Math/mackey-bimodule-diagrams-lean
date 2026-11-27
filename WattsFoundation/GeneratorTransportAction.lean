import WattsFoundation.GeneratorTransport
import WattsFoundation.GeneratorPreimageAction
open CategoryTheory
universe u v w
namespace SmallGeneratorBridge

theorem evaluationTransportIso_intertwines {C : Type u} {D : Type w}
    [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]
    (P : C) (Q : D) [(preadditiveCoyonedaObj P).IsEquivalence]
    (F : C ⥤ D) (r : (End P)ᵐᵒᵖ) :
    (preadditiveCoyonedaObj Q).map
      (F.map ((preadditiveCoyonedaObj P).asEquivalence.inverse.map (regularRight P r))) ≫
        (evaluationTransportIso P Q F).hom =
      (evaluationTransportIso P Q F).hom ≫
        (preadditiveCoyonedaObj Q).map (F.map (End.asHom (MulOpposite.unop r))) := by
  simp only [evaluationTransportIso, Functor.mapIso_hom, ← Functor.map_comp,
    regularPreimageIso_intertwines]

end SmallGeneratorBridge
