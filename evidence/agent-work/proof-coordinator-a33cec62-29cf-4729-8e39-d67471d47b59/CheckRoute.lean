import WattsFoundation.ReconstructionFromSmallProjectiveGenerator
import Proofs.EilenbergWatts

universe u v w
#check ReconstructionFromSmallProjectiveGenerator
#print axioms ReconstructionFromSmallProjectiveGenerator

noncomputable def ReviewedCorrespondenceType : Prop :=
∀ (A : Type u) (E : Type w)
    [CategoryTheory.Category.{v} A] [CategoryTheory.Category.{v} E]
    [CategoryTheory.Abelian A] [CategoryTheory.Abelian E]
    [CategoryTheory.Limits.HasCoproducts.{v} A]
    [CategoryTheory.Limits.HasCoproducts.{v} E]
    (P : A) (Q : E),
  CategoryTheory.Projective P →
  CategoryTheory.IsSeparator P →
  (∀ I : Type v, CategoryTheory.Limits.PreservesColimitsOfShape
    (CategoryTheory.Discrete I)
    (CategoryTheory.Functor.obj CategoryTheory.preadditiveCoyoneda (Opposite.op P))) →
  CategoryTheory.Projective Q →
  CategoryTheory.IsSeparator Q →
  (∀ I : Type v, CategoryTheory.Limits.PreservesColimitsOfShape
    (CategoryTheory.Discrete I)
    (CategoryTheory.Functor.obj CategoryTheory.preadditiveCoyoneda (Opposite.op Q))) →
  let R := MulOpposite (CategoryTheory.End P)
  let S := MulOpposite (CategoryTheory.End Q)
  let HP : CategoryTheory.Functor A (ModuleCat.{v} R) :=
    CategoryTheory.preadditiveCoyonedaObj P
  let HQ : CategoryTheory.Functor E (ModuleCat.{v} S) :=
    CategoryTheory.preadditiveCoyonedaObj Q
  let Good := fun F : CategoryTheory.Functor A E =>
    CategoryTheory.Functor.Additive F ∧
      CategoryTheory.Limits.PreservesFiniteColimits F ∧
      ∀ I : Type v, CategoryTheory.Limits.PreservesColimitsOfShape
        (CategoryTheory.Discrete I) F
  let Functors := CategoryTheory.ObjectProperty.FullSubcategory Good
  let incl := CategoryTheory.ObjectProperty.ι Good
  let eval := CategoryTheory.Functor.comp incl
    (CategoryTheory.Functor.comp
      (CategoryTheory.Functor.obj (CategoryTheory.evaluation A E) P) HQ)
  let Actions := fun (M : ModuleCat.{v} S) =>
    { d : Sigma (fun left : Module S M =>
        Subtype (fun right : Module (MulOpposite R) M =>
          letI : SMul S M := left.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
          letI : SMul (MulOpposite R) M :=
            right.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
          SMulCommClass (MulOpposite R) S M)) //
      d.1 = ModuleCat.isModule M }
  let Bimod := Sigma Actions
  let right := fun (M : Bimod) (b : M.1) (r : R) =>
    letI : Module (MulOpposite R) M.1 := M.2.1.2.1
    MulOpposite.op r • b
  let Hom := fun (M N : Bimod) =>
    { f : LinearMap (RingHom.id S) M.1 N.1 //
      ∀ (b : M.1) (r : R), f (right M b r) = right N (f b) r }
  letI : CategoryTheory.Category Bimod :=
    { Hom := Hom
      id := fun _ => ⟨LinearMap.id, fun _ _ => rfl⟩
      comp := fun f g =>
        ⟨LinearMap.comp g.val f.val, fun b r =>
          Eq.trans (congrArg (fun x => g.val x) (f.property b r))
            (g.property (f.val b) r)⟩
      id_comp := fun _ => Subtype.ext (LinearMap.id_comp _)
      comp_id := fun _ => Subtype.ext (LinearMap.comp_id _)
      assoc := fun _ _ _ => Subtype.ext (LinearMap.comp_assoc _ _ _) }
  let forgetBimod : CategoryTheory.Functor Bimod (ModuleCat.{v} S) :=
    { obj := fun M => M.1
      map := fun f => ModuleCat.ofHom f.val
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
  CategoryTheory.Functor.IsEquivalence HP ∧
    CategoryTheory.Functor.IsEquivalence HQ ∧
    ∃ Φ : CategoryTheory.Equivalence Functors Bimod,
      ∃ h : CategoryTheory.Functor.comp Φ.functor forgetBimod = eval,
        let toHom := fun (F : Functors) =>
          cast (congrArg ModuleCat.carrier (CategoryTheory.Functor.congr_obj h F))
        (∀ (F : Functors) (b : (Φ.functor.obj F).1)
            (q : CategoryTheory.End Q) (p : CategoryTheory.End P),
          toHom F (MulOpposite.op q • right (Φ.functor.obj F) b (MulOpposite.op p)) =
            CategoryTheory.CategoryStruct.comp
              (CategoryTheory.CategoryStruct.comp
                (CategoryTheory.End.asHom q) (toHom F b))
              (F.obj.map (CategoryTheory.End.asHom p))) ∧
        (∀ (F G : Functors) (θ : Quiver.Hom F G) (b : (Φ.functor.obj F).1),
          toHom G ((Φ.functor.map θ).val b) =
            CategoryTheory.CategoryStruct.comp (toHom F b)
              (CategoryTheory.NatTrans.app (incl.map θ) P))
