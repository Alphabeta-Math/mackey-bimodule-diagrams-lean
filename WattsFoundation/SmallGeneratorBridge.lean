import WattsFoundation.ReconstructionFromSmallProjectiveGenerator
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
universe u v

namespace SmallGeneratorBridge

noncomputable def directSumCofan {I : Type v} (M : I → AddCommGrpCat.{v}) : Cofan M := by
  classical
  exact Cofan.mk (AddCommGrpCat.of (DirectSum I (fun i => M i)))
    (fun i => AddCommGrpCat.ofHom (DirectSum.of (fun i => M i) i))

noncomputable def directSumIsColimit {I : Type v} (M : I → AddCommGrpCat.{v}) :
    IsColimit (directSumCofan M) := by
  classical
  refine Cofan.IsColimit.mk (directSumCofan M)
    (fun s => AddCommGrpCat.ofHom (DirectSum.toAddMonoid (fun i => (s.inj i).hom))) ?_ ?_
  · intro s i
    apply AddCommGrpCat.hom_ext
    ext x
    simpa [directSumCofan] using (DirectSum.toAddMonoid_of (fun j => (s.inj j).hom) i x)
  · intro s f hf
    apply AddCommGrpCat.hom_ext
    apply DirectSum.addHom_ext
    intro i x
    have h := congrArg (fun g : M i ⟶ s.pt => g.hom x) (hf i)
    change f.hom ((DirectSum.of (fun i => M i) i) x) = (s.inj i).hom x at h
    change f.hom ((DirectSum.of (fun i => M i) i) x) =
      DirectSum.toAddMonoid (fun j => (s.inj j).hom) ((DirectSum.of (fun i => M i) i) x)
    rw [DirectSum.toAddMonoid_of]
    exact h

theorem smallOfPreserves {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{v} C]
    (P : C) (hsmall : ∀ I : Type v,
      PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (Opposite.op P)))
    (I : Type v) (X : I → C) :
    letI : DecidableEq I := Classical.decEq I
    Function.Bijective (DirectSum.toAddMonoid (β := fun i => P ⟶ X i)
      (γ := P ⟶ sigmaObj X) (fun i => Preadditive.rightComp P (Sigma.ι X i))) := by
  classical
  let F : C ⥤ AddCommGrpCat.{v} := preadditiveCoyoneda.obj (Opposite.op P)
  letI : PreservesColimitsOfShape (Discrete I) F := hsmall I
  let D : I → AddCommGrpCat.{v} := fun i => F.obj (X i)
  let h1 := directSumIsColimit D
  let c2 : Cofan D := Cofan.mk (F.obj (sigmaObj X)) (fun i => F.map (Sigma.ι X i))
  let h2 : IsColimit c2 := isColimitCofanMkObjOfIsColimit F X (Sigma.ι X) (coproductIsCoproduct X)
  let e := h1.coconePointUniqueUpToIso h2
  have comp : e.hom.hom = DirectSum.toAddMonoid
      (fun i => Preadditive.rightComp P (Sigma.ι X i)) := by
    apply DirectSum.addHom_ext
    intro i x
    have h := h1.fac c2 ⟨i⟩
    have hx := congrArg (fun g : F.obj (X i) ⟶ F.obj (sigmaObj X) => g.hom x) h
    change e.hom.hom ((DirectSum.of (fun i => D i) i) x) = (F.map (Sigma.ι X i)).hom x at hx
    change e.hom.hom ((DirectSum.of (fun i => P ⟶ X i) i) x) =
      (DirectSum.toAddMonoid (fun j => Preadditive.rightComp P (Sigma.ι X j)))
        ((DirectSum.of (fun i => P ⟶ X i) i) x)
    rw [DirectSum.toAddMonoid_of]
    exact hx
  rw [← comp]
  exact ConcreteCategory.bijective_of_isIso e.hom


theorem equivalenceOfSmallProjectiveGenerator {C : Type u} [Category.{v} C]
    [Abelian C] [HasCoproducts.{v} C] (P : C) [Projective P]
    (hsep : IsSeparator P)
    (hsmall : ∀ I : Type v,
      PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (Opposite.op P))) :
    (preadditiveCoyonedaObj P).IsEquivalence := by
  classical
  obtain ⟨L, ⟨c⟩, ⟨unit⟩⟩ := ReconstructionFromSmallProjectiveGenerator C P hsep
    (fun I X => smallOfPreserves P hsmall I X)
  let E : C ≌ ModuleCat.{v} (End P)ᵐᵒᵖ :=
    CategoryTheory.Equivalence.mk (preadditiveCoyonedaObj P) L unit.symm c
  exact E.isEquivalence_functor

end SmallGeneratorBridge

