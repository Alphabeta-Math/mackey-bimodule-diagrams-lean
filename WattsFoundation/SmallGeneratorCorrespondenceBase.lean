import WattsFoundation.SmallGeneratorBridge
import WattsFoundation.GeneratorFunctorTransport
import WattsFoundation.GeneratorTransportNaturality
import WattsFoundation.GeneratorTransportAction
import WattsFoundation.General.OriginalBimoduleRepackFunctor

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Limits
namespace SmallGeneratorBridge
universe uA uD v

variable {A : Type uA} {D : Type uD} [Category.{v} A] [Category.{v} D]
variable [Abelian A] [Abelian D] [HasCoproducts.{v} A] [HasCoproducts.{v} D]
variable (P : A) (Q : D) [Projective P] [Projective Q]
variable (hP : IsSeparator P) (hQ : IsSeparator Q)
variable (hsP : ∀ I : Type v, PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (Opposite.op P)))
variable (hsQ : ∀ I : Type v, PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (Opposite.op Q)))

noncomputable def generatorEquivalence {C : Type uA} [Category.{v} C] [Abelian C] [HasCoproducts.{v} C]
    (X : C) [Projective X] (h : IsSeparator X)
    (hs : ∀ I : Type v, PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (Opposite.op X))) :
    C ≌ ModuleCat.{v} (End X)ᵐᵒᵖ := by
  letI : (preadditiveCoyonedaObj X).IsEquivalence := equivalenceOfSmallProjectiveGenerator X h hs
  exact (preadditiveCoyonedaObj X).asEquivalence

noncomputable def abstractEquivalence :
    (Good (C := A) (D := D)).FullSubcategory ≌
      WattsFoundation.General.OriginalBimodule.{v,0} (End P)ᵐᵒᵖ (End Q)ᵐᵒᵖ :=
  (functorTransport (generatorEquivalence P hP hsP) (generatorEquivalence Q hQ hsQ)).trans
    (WattsFoundation.General.originalWattsWithEvaluation.{v,0} (End P)ᵐᵒᵖ (End Q)ᵐᵒᵖ).symm

noncomputable def actualEvaluation :
    (Good (C := A) (D := D)).FullSubcategory ⥤ ModuleCat.{v} (End Q)ᵐᵒᵖ :=
  (Good (C := A) (D := D)).ι ⋙ ((evaluation A D).obj P ⋙ preadditiveCoyonedaObj Q)

noncomputable def abstractEvaluationIso :
    (abstractEquivalence P Q hP hQ hsP hsQ).functor ⋙
      WattsFoundation.General.originalForget (End P)ᵐᵒᵖ (End Q)ᵐᵒᵖ ≅ actualEvaluation P Q := by
  letI : (preadditiveCoyonedaObj P).IsEquivalence := equivalenceOfSmallProjectiveGenerator P hP hsP
  letI : (preadditiveCoyonedaObj Q).IsEquivalence := equivalenceOfSmallProjectiveGenerator Q hQ hsQ
  refine NatIso.ofComponents (fun F => evaluationTransportIso P Q F.obj) ?_
  intro F G η
  exact evaluationTransportIso_natural P Q η.hom


noncomputable def exactEvaluationEquivalence :
    (Good (C := A) (D := D)).FullSubcategory ≌
      WattsFoundation.General.OriginalBimodule.{v,0} (End P)ᵐᵒᵖ (End Q)ᵐᵒᵖ :=
  WattsFoundation.General.repackedEquivalence (End P)ᵐᵒᵖ (End Q)ᵐᵒᵖ (actualEvaluation P Q)
    (abstractEquivalence P Q hP hQ hsP hsQ) (abstractEvaluationIso P Q hP hQ hsP hsQ)

theorem exactEvaluationEquivalence_forget :
    (exactEvaluationEquivalence P Q hP hQ hsP hsQ).functor ⋙
      WattsFoundation.General.originalForget (End P)ᵐᵒᵖ (End Q)ᵐᵒᵖ = actualEvaluation P Q :=
  WattsFoundation.General.repackedEquivalence_forget (End P)ᵐᵒᵖ (End Q)ᵐᵒᵖ (actualEvaluation P Q)
    (abstractEquivalence P Q hP hQ hsP hsQ) (abstractEvaluationIso P Q hP hQ hsP hsQ)

end SmallGeneratorBridge
