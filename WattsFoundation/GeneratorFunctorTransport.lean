import WattsFoundation.AbelianEquivalencesPreserveFunctorHypotheses
import WattsFoundation.General.OriginalBimoduleAdapter
import Mathlib.CategoryTheory.Adjunction.Limits

set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace SmallGeneratorBridge
universe u₁ u₂ u₃ u₄ v v₁ v₂

def Good {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] : ObjectProperty (C ⥤ D) := fun F =>
  F.Additive ∧ PreservesFiniteColimits F ∧ ∀ I : Type v, PreservesColimitsOfShape (Discrete I) F

noncomputable def restrictEquivalence
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    (e : C ≌ D) (P : ObjectProperty C) (Q : ObjectProperty D)
    (hF : ∀ X, P X → Q (e.functor.obj X))
    (hG : ∀ Y, Q Y → P (e.inverse.obj Y)) : P.FullSubcategory ≌ Q.FullSubcategory := by
  let F := Q.lift (P.ι ⋙ e.functor) (fun X => hF X.obj X.property)
  let G := P.lift (Q.ι ⋙ e.inverse) (fun Y => hG Y.obj Y.property)
  let η : 𝟭 P.FullSubcategory ≅ F ⋙ G :=
    NatIso.ofComponents (fun X => P.isoMk (e.unitIso.app X.obj)) (by
      intro X Y f
      apply ObjectProperty.hom_ext
      exact e.unitIso.hom.naturality f.hom)
  let ε : G ⋙ F ≅ 𝟭 Q.FullSubcategory :=
    NatIso.ofComponents (fun Y => Q.isoMk (e.counitIso.app Y.obj)) (by
      intro X Y f
      apply ObjectProperty.hom_ext
      exact e.counitIso.hom.naturality f.hom)
  exact CategoryTheory.Equivalence.mk F G η ε

theorem whiskerGood
    {A : Type u₁} {D : Type u₂} {C : Type u₃} {E : Type u₄}
    [Category.{v} A] [Category.{v} D] [Category.{v} C] [Category.{v} E]
    [Abelian A] [Abelian D] [Abelian C] [Abelian E]
    (left : C ≌ A) (right : D ≌ E) (F : A ⥤ D) (hF : Good F) :
    Good (left.functor ⋙ F ⋙ right.functor) := by
  have hL := AbelianEquivalencesPreserveFunctorHypotheses.{u₃,u₁,v,v,v} left
  have hR := AbelianEquivalencesPreserveFunctorHypotheses.{u₂,u₄,v,v,v} right
  letI : left.functor.Additive := hL.1
  letI : right.functor.Additive := hR.1
  letI : F.Additive := hF.1
  letI : PreservesFiniteColimits F := hF.2.1
  letI : PreservesColimitsOfSize.{0,0} left.functor := Adjunction.isEquivalence_preservesColimits left.functor
  letI : PreservesColimitsOfSize.{0,0} right.functor := Adjunction.isEquivalence_preservesColimits right.functor
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I
  letI := hL.2.2.1 I
  letI := hF.2.2 I
  letI := hR.2.2.1 I
  infer_instance

noncomputable def functorTransport
    {A : Type u₁} {D : Type u₂} [Category.{v} A] [Category.{v} D]
    [Abelian A] [Abelian D] {R S : Type v} [Ring R] [Ring S]
    (eA : A ≌ ModuleCat.{v} R) (eD : D ≌ ModuleCat.{v} S) :
    (Good (C := A) (D := D)).FullSubcategory ≌
      WattsFoundation.General.ConcreteBimodule.GoodFunctors.{v,0} R S := by
  let e := (eA.congrLeft (E := D)).trans (eD.congrRight (E := ModuleCat.{v} R))
  apply restrictEquivalence e
  · intro F hF
    exact whiskerGood eA.symm eD F hF
  · intro T hT
    exact whiskerGood eA eD.symm T hT

end SmallGeneratorBridge
