import NotesProofs.General.OriginalTensorAssociator
import Mathlib.Algebra.Category.Ring.Basic

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

universe u v
open CategoryTheory

theorem ReviewedOriginalWattsConnection : (let Mod := fun A : RingCat.{u} => ModuleCat.{max u v} A
let Actions := fun (S R : RingCat.{u}) (M : Mod S) =>
  { d : Bimodule.1 S R M // d.1 = ModuleCat.isModule M }
let Bimod := fun (S R : RingCat.{u}) => Sigma (Actions S R)
let right := fun (S R : RingCat.{u}) (M : Bimod S R) (m : M.1) (r : R) =>
  letI : Module (MulOpposite R) M.1 := M.2.1.2.1
  MulOpposite.op r • m
let Hom := fun (S R : RingCat.{u}) (M N : Bimod S R) =>
  { f : LinearMap (RingHom.id S) M.1 N.1 //
    ∀ (m : M.1) (r : R), f (right S R M m r) = right S R N (f m) r }
letI : ∀ S R : RingCat.{u}, CategoryTheory.Category (Bimod S R) := fun S R =>
  { Hom := Hom S R
    id := fun _ => ⟨LinearMap.id, fun _ _ => rfl⟩
    comp := fun f g =>
      ⟨LinearMap.comp g.val f.val, fun m r =>
        Eq.trans (congrArg (fun x => g.val x) (f.property m r))
          (g.property (f.val m) r)⟩
    id_comp := fun _ => Subtype.ext (LinearMap.id_comp _)
    comp_id := fun _ => Subtype.ext (LinearMap.comp_id _)
    assoc := fun _ _ _ => Subtype.ext (LinearMap.comp_assoc _ _ _) }
let forgetBimod : ∀ S R : RingCat.{u}, CategoryTheory.Functor (Bimod S R) (Mod S) :=
  fun _ _ =>
    { obj := fun M => M.1
      map := fun f => ModuleCat.ofHom f.val
      map_id := fun _ => rfl
      map_comp := fun _ _ => rfl }
let Good := fun (S R : RingCat.{u}) (F : CategoryTheory.Functor (Mod R) (Mod S)) =>
  CategoryTheory.Functor.Additive F ∧
  CategoryTheory.Limits.PreservesFiniteColimits F ∧
  ∀ I : Type (max u v), CategoryTheory.Limits.PreservesColimitsOfShape
    (CategoryTheory.Discrete I) F
let PreservingFunctors := fun (S R : RingCat.{u}) => CategoryTheory.ObjectProperty.FullSubcategory (Good S R)
let incl := fun (S R : RingCat.{u}) => CategoryTheory.ObjectProperty.ι (Good S R)
let regular := fun (R : RingCat.{u}) => ModuleCat.of R (ULift.{v} R)
let rho : ∀ (R : RingCat.{u}), R → ModuleCat.Hom (regular R) (regular R) :=
  fun R r =>
    ModuleCat.ofHom (LinearEquiv.conjRingEquiv
      (LinearEquiv.symm (ULift.moduleEquiv : ULift.{v} R ≃ₗ[R] R)) (LinearMap.mulRight R r))
let eval := fun (S R : RingCat.{u}) =>
  CategoryTheory.Functor.comp (incl S R)
    (CategoryTheory.Functor.obj (CategoryTheory.evaluation (Mod R) (Mod S)) (regular R))
let Balanced := fun (S R : RingCat.{u}) (B : Bimod S R) (X : Mod R) (Y : Mod S)
    (p : B.1 → X → Y) =>
  (∀ (b b' : B.1) (x : X), p (b + b') x = p b x + p b' x) ∧
  (∀ (b : B.1) (x x' : X), p b (x + x') = p b x + p b x') ∧
  (∀ (s : S) (b : B.1) (x : X), p (s • b) x = s • p b x) ∧
  (∀ (r : R) (b : B.1) (x : X), p (right S R B b r) x = p b (r • x))
∃ EW : ∀ S R : RingCat.{u}, CategoryTheory.Equivalence (Bimod S R) (PreservingFunctors S R),
  let tensor := fun (S R : RingCat.{u}) (B : Bimod S R) =>
    CategoryTheory.Functor.obj (incl S R) ((EW S R).functor.obj B)
  ∃ pure : ∀ (S R : RingCat.{u}) (B : Bimod S R) (X : Mod R), B.1 → X → (tensor S R B).obj X,
    (∀ (S R : RingCat.{u}) (B : Bimod S R) (X : Mod R),
      Balanced S R B X ((tensor S R B).obj X) (pure S R B X) ∧
      ∀ (Y : Mod S) (p : B.1 → X → Y), Balanced S R B X Y p →
        ∃! f : LinearMap (RingHom.id S) ((tensor S R B).obj X) Y,
          ∀ (b : B.1) (x : X), f (pure S R B X b x) = p b x) ∧
    (∀ (S R : RingCat.{u}) (B : Bimod S R) (X Y : Mod R)
      (f : ModuleCat.Hom X Y) (b : B.1) (x : X),
      ModuleCat.Hom.hom ((tensor S R B).map f) (pure S R B X b x) =
        pure S R B Y b (ModuleCat.Hom.hom f x)) ∧
    (∀ (S R : RingCat.{u}) (B B' : Bimod S R) (f : Hom S R B B')
      (X : Mod R) (b : B.1) (x : X),
      ModuleCat.Hom.hom
        (CategoryTheory.NatTrans.app ((incl S R).map ((EW S R).functor.map f)) X)
        (pure S R B X b x) = pure S R B' X (f.val b) x) ∧
    (∀ S R : RingCat.{u},
      ∃ h : CategoryTheory.Functor.comp (EW S R).inverse (forgetBimod S R) = eval S R,
        ∀ (F : PreservingFunctors S R),
          let toEval := cast (congrArg ModuleCat.carrier (CategoryTheory.Functor.congr_obj h F))
          ∀ (m : ((EW S R).inverse.obj F).1) (r : R),
            toEval (right S R ((EW S R).inverse.obj F) m r) =
              ModuleCat.Hom.hom (F.obj.map (rho R r)) (toEval m)) ∧
    (∀ (T S R : RingCat.{u}) (C : Bimod T S) (B : Bimod S R),
      ∃ a : Actions T R ((tensor T S C).obj B.1),
        let CB : Bimod T R := ⟨(tensor T S C).obj B.1, a⟩
        (∀ (c : C.1) (b : B.1) (r : R),
          right T R CB (pure T S C B.1 c b) r = pure T S C B.1 c (right S R B b r)) ∧
        ∃ i : CategoryTheory.Iso (tensor T R CB)
            (CategoryTheory.Functor.comp (tensor S R B) (tensor T S C)),
          ∀ (X : Mod R) (c : C.1) (b : B.1) (x : X),
            ModuleCat.Hom.hom (i.hom.app X) (pure T R CB X (pure T S C B.1 c b) x) =
              pure T S C ((tensor S R B).obj X) c (pure S R B X b x)) ∧
    (∀ R : RingCat.{u}, ∃ a : Actions R R (regular R),
      let RR : Bimod R R := ⟨regular R, a⟩
      (∀ (x : ULift.{v} R) (r : R), right R R RR x r = ULift.up (x.down * r)) ∧
      ∃ i : CategoryTheory.Iso (tensor R R RR) (CategoryTheory.Functor.id (Mod R)),
        ∀ (X : Mod R) (r : ULift.{v} R) (x : X),
          ModuleCat.Hom.hom (i.hom.app X) (pure R R RR X r x) = r.down • x)) := by
  intro Mod Actions Bimod right Hom forgetBimod Good PreservingFunctors incl regular rho eval Balanced
  refine ⟨fun S R => NotesProofs.General.originalWattsWithEvaluation.{u,v} R S, ?_⟩
  refine ⟨fun S R B X => NotesProofs.General.originalTensorPure R S B X, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S R B X
    exact NotesProofs.General.originalTensorPure_universal R S B X
  · intro S R B X Y f b x
    exact NotesProofs.General.originalTensorPure_map R S B f b x
  · intro S R B B' f X b x
    exact NotesProofs.General.originalTensorPure_bimoduleMap R S B B' f X b x
  · intro S R
    refine ⟨NotesProofs.General.originalWatts_inverse_forget R S, ?_⟩
    intro F toEval m r
    exact NotesProofs.General.originalWatts_inverse_right R S F m r
  · intro T S R C B
    refine ⟨(NotesProofs.General.originalCompositeBimodule R S T C B).2, ?_, ?_⟩
    · intro c b r
      exact NotesProofs.General.originalCompositeBimodule_right R S T C B c b r
    · refine ⟨NotesProofs.General.originalAssocNatIso R S T C B, ?_⟩
      intro X c b x
      exact NotesProofs.General.originalAssocNatIso_pure R S T C B X c b x
  · intro R
    refine ⟨(NotesProofs.General.originalRegularBimodule R).2, ?_, ?_⟩
    · intro x r
      exact NotesProofs.General.originalRegularBimodule_right R x r
    · refine ⟨NotesProofs.General.originalRegularTensorNatIso R, ?_⟩
      intro X r x
      exact NotesProofs.General.originalRegularTensorNatIso_pure R X r x

#print axioms ReviewedOriginalWattsConnection
