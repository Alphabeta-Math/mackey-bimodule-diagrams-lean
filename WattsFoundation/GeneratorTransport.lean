import WattsFoundation.GeneratorRegularActions

open CategoryTheory
universe u v w
namespace SmallGeneratorBridge

noncomputable def regularPreimageIso {C : Type u} [Category.{v} C] [Preadditive C]
    (P : C) [(preadditiveCoyonedaObj P).IsEquivalence] :
    (preadditiveCoyonedaObj P).asEquivalence.inverse.obj
      (ModuleCat.of (End P)ᵐᵒᵖ (ULift.{0} (End P)ᵐᵒᵖ)) ≅ P := by
  let E := (preadditiveCoyonedaObj P).asEquivalence
  exact E.inverse.mapIso (regularToHom P) ≪≫ (E.unitIso.app P).symm

noncomputable def evaluationTransportIso {C : Type u} {D : Type w}
    [Category.{v} C] [Category.{v} D] [Preadditive C] [Preadditive D]
    (P : C) (Q : D) [(preadditiveCoyonedaObj P).IsEquivalence] (F : C ⥤ D) :
    (preadditiveCoyonedaObj Q).obj
      (F.obj ((preadditiveCoyonedaObj P).asEquivalence.inverse.obj
        (ModuleCat.of (End P)ᵐᵒᵖ (ULift.{0} (End P)ᵐᵒᵖ)))) ≅
      (preadditiveCoyonedaObj Q).obj (F.obj P) :=
  (preadditiveCoyonedaObj Q).mapIso (F.mapIso (regularPreimageIso P))

end SmallGeneratorBridge
