import WattsFoundation.GeneratorTransport
open CategoryTheory
universe u v w
namespace SmallGeneratorBridge

theorem evaluationTransportIso_natural {C : Type u} {D : Type w}
    [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]
    (P : C) (Q : D) [(preadditiveCoyonedaObj P).IsEquivalence]
    {F G : C ⥤ D} (η : F ⟶ G) :
    (preadditiveCoyonedaObj Q).map
        (η.app ((preadditiveCoyonedaObj P).asEquivalence.inverse.obj
          (ModuleCat.of (End P)ᵐᵒᵖ (ULift.{0} (End P)ᵐᵒᵖ)))) ≫
      (evaluationTransportIso P Q G).hom =
    (evaluationTransportIso P Q F).hom ≫
      (preadditiveCoyonedaObj Q).map (η.app P) := by
  simp only [evaluationTransportIso, Functor.mapIso_hom, ← Functor.map_comp, η.naturality]

end SmallGeneratorBridge
