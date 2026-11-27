import NotesProofs.General.RegularEvaluationEquivalence
import Proofs.Bimodule

/-! A bridge between the Sigma/subtype bimodule presentation in the paper
workflow and the structure-based bimodule category used in the checked
Eilenberg–Watts equivalence. -/

set_option backward.isDefEq.respectTransparency false

namespace NotesProofs.General

universe u v
open CategoryTheory

variable (R S : Type u) [Ring R] [Ring S]

/-- The paper workflow's bimodule objects. -/
def OriginalBimodule := Sigma (fun M : ModuleCat.{max u v} S =>
  { d : Bimodule.1 S R M // d.1 = ModuleCat.isModule M })

/-- Right multiplication in the paper workflow's presentation. -/
def originalRight (M : OriginalBimodule.{u,v} R S) (m : M.1) (r : R) : M.1 :=
  letI : Module (MulOpposite R) M.1 := M.2.1.2.1
  MulOpposite.op r • m

/-- Morphisms in the paper workflow's bimodule presentation. -/
def OriginalBimoduleHom (M N : OriginalBimodule.{u,v} R S) :=
  { f : M.1 →ₗ[S] N.1 // ∀ m r, f (originalRight R S M m r) = originalRight R S N (f m) r }

instance originalBimoduleCategory : Category (OriginalBimodule.{u,v} R S) where
  Hom := OriginalBimoduleHom R S
  id M := ⟨LinearMap.id, fun _ _ => rfl⟩
  comp f g := ⟨g.1.comp f.1, fun m r => (congrArg (fun x => g.1 x) (f.2 m r)).trans (g.2 (f.1 m) r)⟩
  id_comp f := by apply Subtype.ext; ext; rfl
  comp_id f := by apply Subtype.ext; ext; rfl
  assoc f g h := by apply Subtype.ext; ext; rfl

/-- Convert a workflow bimodule to the structure-based presentation. -/
def originalToConcreteObj (M : OriginalBimodule.{u,v} R S) : ConcreteBimodule.{u,v} R S := by
  letI : Module (MulOpposite R) M.1 := M.2.1.2.1
  have hcomm : SMulCommClass (MulOpposite R) S M.1 := by
    rcases M with ⟨M, ⟨⟨left, ⟨right, comm⟩⟩, hleft⟩⟩
    cases hleft
    exact comm
  exact { carrier := M.1, rightModule := inferInstance, commuting := hcomm }

/-- Convert a structure-based bimodule to the paper workflow's presentation. -/
def concreteToOriginalObj (M : ConcreteBimodule.{u,v} R S) : OriginalBimodule.{u,v} R S :=
  ⟨ModuleCat.of S M.carrier, ⟨⟨inferInstance, ⟨inferInstance, inferInstance⟩⟩, rfl⟩⟩

/-- The two encodings give the same maps. -/
def originalToConcrete : OriginalBimodule.{u,v} R S ⥤ ConcreteBimodule.{u,v} R S where
  obj := originalToConcreteObj R S
  map f := ⟨f.1, fun r m => f.2 m r⟩
  map_id M := by apply Subtype.ext; rfl
  map_comp f g := by apply Subtype.ext; rfl

/-- Convert structure-based bimodules and their maps to the workflow encoding. -/
def concreteToOriginal : ConcreteBimodule.{u,v} R S ⥤ OriginalBimodule.{u,v} R S where
  obj := concreteToOriginalObj R S
  map f := ⟨f.1, fun m r => f.2 r m⟩
  map_id M := by apply Subtype.ext; rfl
  map_comp f g := by apply Subtype.ext; rfl

/-- Unpackaging after packaging is naturally isomorphic to the identity. -/
def concreteRepackCounit :
    concreteToOriginal.{u,v} R S ⋙ originalToConcrete.{u,v} R S ≅ 𝟭 (ConcreteBimodule.{u,v} R S) := by
  refine NatIso.ofComponents (fun M => ?_) ?_
  · cases M
    exact Iso.refl _
  · intro M N f
    cases M
    cases N
    apply Subtype.ext
    rfl

instance originalToConcrete_full : (originalToConcrete.{u,v} R S).Full where
  map_surjective {M N} f := ⟨⟨f.1, fun m r => f.2 r m⟩, by apply Subtype.ext; rfl⟩

instance originalToConcrete_faithful : (originalToConcrete.{u,v} R S).Faithful where
  map_injective {M N} f g h := by
    apply Subtype.ext
    have hh := congrArg (fun (k : (originalToConcrete R S).obj M ⟶ (originalToConcrete R S).obj N) => k.1) h
    exact hh

instance originalToConcrete_essSurj : (originalToConcrete.{u,v} R S).EssSurj where
  mem_essImage M := by
    refine ⟨concreteToOriginalObj R S M, ⟨?_⟩⟩
    cases M
    exact Iso.refl _

instance originalToConcrete_isEquivalence : (originalToConcrete.{u,v} R S).IsEquivalence where

/-- The paper's Sigma bimodules are equivalent to the structure-based
bimodule category. -/
noncomputable def originalBimoduleEquivalence :
    OriginalBimodule.{u,v} R S ≌ ConcreteBimodule.{u,v} R S :=
  (originalToConcrete.{u,v} R S).asEquivalence

/-- The encoding equivalence with the explicit packaging functor as inverse. -/
noncomputable def originalBimoduleEquivalenceWithInverse :
    OriginalBimodule.{u,v} R S ≌ ConcreteBimodule.{u,v} R S := by
  let E := originalBimoduleEquivalence.{u,v} R S
  let G := concreteToOriginal.{u,v} R S
  let F := originalToConcrete.{u,v} R S
  have h : G ≅ E.inverse :=
    (Functor.rightUnitor G).symm ≪≫
      Functor.isoWhiskerLeft G E.unitIso ≪≫
      (Functor.associator G F E.inverse).symm ≪≫
      Functor.isoWhiskerRight (concreteRepackCounit R S) E.inverse ≪≫
      Functor.leftUnitor E.inverse
  exact E.changeInverse h.symm

/-- The paper's bimodule category is equivalent to the category of good
module functors. -/
noncomputable def originalBimoduleWattsEquivalence :
    OriginalBimodule.{u,v} R S ≌ ConcreteBimodule.GoodFunctors.{u,v} R S :=
  (originalBimoduleEquivalence.{u,v} R S).trans
    (ConcreteBimodule.eilenbergWattsEquivalence.{u,v} R S)

/-- Forget the right action and retain the left module. -/
def originalForget : OriginalBimodule.{u,v} R S ⥤ ModuleCat.{max u v} S where
  obj M := M.1
  map f := ModuleCat.ofHom f.1
  map_id M := rfl
  map_comp f g := rfl

/-- The original workflow's bimodule category with the explicit
regular-evaluation inverse. -/
noncomputable def originalWattsWithEvaluation :
    OriginalBimodule.{u,v} R S ≌ ConcreteBimodule.GoodFunctors.{u,v} R S :=
  (originalBimoduleEquivalenceWithInverse.{u,v} R S).trans
    (ConcreteBimodule.eilenbergWattsEquivalenceWithEvaluation.{u,v} R S)

/-- After forgetting the right action, the inverse is exactly evaluation at
the lifted regular module. -/
theorem originalWatts_inverse_forget :
    (originalWattsWithEvaluation.{u,v} R S).inverse ⋙ originalForget.{u,v} R S =
      (ObjectProperty.ι (ConcreteBimodule.Good.{u,v} R S)) ⋙
        ((CategoryTheory.evaluation (ModuleCat.{max u v} R) (ModuleCat.{max u v} S)).obj
          (ChoiceFreeWatts.regular.{u,v} R)) := by
  rfl

/-- The right action of the explicit inverse is induced by the image of
right multiplication on the regular module. -/
theorem originalWatts_inverse_right (F : ConcreteBimodule.GoodFunctors.{u,v} R S)
    (m : ((originalWattsWithEvaluation.{u,v} R S).inverse.obj F).1) (r : R) :
    originalRight R S ((originalWattsWithEvaluation.{u,v} R S).inverse.obj F) m r =
      (F.obj.map (ModuleCat.ofHom (LinearEquiv.conjRingEquiv
        ((ULift.moduleEquiv : ULift.{v} R ≃ₗ[R] R).symm) (LinearMap.mulRight R r)))).hom m := by
  rfl

#print axioms originalWatts_inverse_right
#print axioms originalWattsWithEvaluation
#print axioms originalWatts_inverse_forget
#print axioms concreteRepackCounit
#print axioms originalBimoduleEquivalenceWithInverse
#print axioms originalToConcrete
#print axioms originalBimoduleEquivalence
#print axioms originalBimoduleWattsEquivalence

end NotesProofs.General
