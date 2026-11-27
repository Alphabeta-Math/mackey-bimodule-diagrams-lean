import WattsFoundation.SmallGeneratorCorrespondenceBase

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

theorem exactEvaluation_right (F : (Good (C := A) (D := D)).FullSubcategory)
    (b : ((exactEvaluationEquivalence P Q hP hQ hsP hsQ).functor.obj F).1) (p : End P) :
    WattsFoundation.General.originalRight (End P)ᵐᵒᵖ (End Q)ᵐᵒᵖ
      ((exactEvaluationEquivalence P Q hP hQ hsP hsQ).functor.obj F) b (MulOpposite.op p) =
      b ≫ F.obj.map (End.asHom p) := by
  letI : (preadditiveCoyonedaObj P).IsEquivalence := equivalenceOfSmallProjectiveGenerator P hP hsP
  letI : (preadditiveCoyonedaObj Q).IsEquivalence := equivalenceOfSmallProjectiveGenerator Q hQ hsQ
  let E := abstractEquivalence P Q hP hQ hsP hsQ
  let α := abstractEvaluationIso P Q hP hQ hsP hsQ
  let m : (E.functor.obj F).1 := (α.app F).inv b
  have hrep := WattsFoundation.General.repackedEquivalence_right (End P)ᵐᵒᵖ (End Q)ᵐᵒᵖ
    (actualEvaluation P Q) E α F m (MulOpposite.op p)
  have hint := evaluationTransportIso_intertwines P Q F.obj (MulOpposite.op p)
  have hpoint := congrArg (fun f => f m) hint
  have action0 : WattsFoundation.General.originalRight (End P)ᵐᵒᵖ (End Q)ᵐᵒᵖ
      (E.functor.obj F) m (MulOpposite.op p) =
      ((preadditiveCoyonedaObj Q).map
        (F.obj.map ((preadditiveCoyonedaObj P).asEquivalence.inverse.map
          (regularRight P (MulOpposite.op p))))) m := by
    rfl
  rw [action0] at hrep
  have hm : (α.app F).hom m = b := (α.app F).toLinearEquiv.right_inv b
  rw [hm] at hrep
  change (α.app F).hom (((preadditiveCoyonedaObj Q).map
      (F.obj.map ((preadditiveCoyonedaObj P).asEquivalence.inverse.map
        (regularRight P (MulOpposite.op p))))) m) =
      (α.app F).hom m ≫ F.obj.map (End.asHom p) at hpoint
  rw [hm] at hpoint
  exact hrep.trans hpoint


theorem exactEvaluation_left_right (F : (Good (C := A) (D := D)).FullSubcategory)
    (b : ((exactEvaluationEquivalence P Q hP hQ hsP hsQ).functor.obj F).1)
    (q : End Q) (p : End P) :
    MulOpposite.op q • WattsFoundation.General.originalRight (End P)ᵐᵒᵖ (End Q)ᵐᵒᵖ
      ((exactEvaluationEquivalence P Q hP hQ hsP hsQ).functor.obj F) b (MulOpposite.op p) =
      (End.asHom q ≫ b) ≫ F.obj.map (End.asHom p) := by
  rw [exactEvaluation_right P Q hP hQ hsP hsQ F b p]
  change End.asHom q ≫ (b ≫ F.obj.map (End.asHom p)) = (End.asHom q ≫ b) ≫ F.obj.map (End.asHom p)
  exact (Category.assoc _ _ _).symm


theorem exactEvaluation_map (F G : (Good (C := A) (D := D)).FullSubcategory) (θ : F ⟶ G)
    (b : ((exactEvaluationEquivalence P Q hP hQ hsP hsQ).functor.obj F).1) :
    ((exactEvaluationEquivalence P Q hP hQ hsP hsQ).functor.map θ).val b =
      b ≫ θ.hom.app P := by
  have h := CategoryTheory.Functor.congr_hom (exactEvaluationEquivalence_forget P Q hP hQ hsP hsQ) θ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  exact ConcreteCategory.congr_hom h b

end SmallGeneratorBridge
