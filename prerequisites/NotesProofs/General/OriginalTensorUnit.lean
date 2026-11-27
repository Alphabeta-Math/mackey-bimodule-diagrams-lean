import NotesProofs.General.OriginalTensorFormulas

/-! The regular bimodule and the tensor unit for the paper-style encoding. -/

set_option backward.isDefEq.respectTransparency false

namespace NotesProofs.General

universe u v
open CategoryTheory

variable (R : Type u) [Ring R]

/-- Right multiplication on the lifted regular left module. -/
def regularRightAction : MulOpposite R →+* Module.End R (ULift.{v} R) :=
  (LinearEquiv.conjRingEquiv ((ULift.moduleEquiv : ULift.{v} R ≃ₗ[R] R).symm)).toRingHom.comp
    (RingEquiv.moduleEndSelf R).toRingHom

@[instance_reducible] def regularRightModule : Module (MulOpposite R) (ULift.{v} R) :=
  Module.compHom (ULift.{v} R) (regularRightAction R)

local instance OriginalTensorUnit_right : Module (MulOpposite R) (ULift.{v} R) := regularRightModule R

/-- Left and right multiplication on the regular module commute. -/
theorem regularRightCommutes : SMulCommClass (MulOpposite R) R (ULift.{v} R) :=
  ⟨fun a s m => (regularRightAction R a).map_smul s m⟩

local instance OriginalTensorUnit_commute : SMulCommClass (MulOpposite R) R (ULift.{v} R) := regularRightCommutes R

@[simp] theorem regularRight_apply (x : ULift.{v} R) (r : R) :
    MulOpposite.op r • x = ULift.up (x.down * r) := rfl

/-- The regular bimodule in the paper workflow's encoding. -/
def originalRegularBimodule : OriginalBimodule.{u,v} R R :=
  ⟨ChoiceFreeWatts.regular.{u,v} R, ⟨⟨inferInstance, ⟨regularRightModule R, regularRightCommutes R⟩⟩, rfl⟩⟩

/-- Its right action is multiplication on the right. -/
theorem originalRegularBimodule_right (x : ULift.{v} R) (r : R) :
    originalRight R R (originalRegularBimodule R) x r = ULift.up (x.down * r) := rfl

/-- Left multiplication evaluates the regular tensor. -/
noncomputable def originalRegularTensorMap (X : ModuleCat.{max u v} R) :
    (originalTensor R R (originalRegularBimodule R)).obj X →ₗ[R] X := by
  let B := originalRegularBimodule.{u,v} R
  let p : ULift.{v} R → X → X := fun a x => a.down • x
  have hb : originalBalanced R R B X X p := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b x
      change (a.down + b.down) • x = a.down • x + b.down • x
      exact add_smul _ _ _
    · intro a x y
      exact smul_add a.down x y
    · intro s a x
      change (s * a.down) • x = s • (a.down • x)
      exact mul_smul s a.down x
    · intro r a x
      change (a.down * r) • x = a.down • (r • x)
      exact mul_smul a.down r x
  exact Classical.choose ((originalTensorPure_universal R R B X).2 X p hb)

@[simp] theorem originalRegularTensorMap_pure (X : ModuleCat.{max u v} R) (a : ULift.{v} R) (x : X) :
    originalRegularTensorMap R X (originalTensorPure R R (originalRegularBimodule R) X a x) = a.down • x :=
  (Classical.choose_spec ((originalTensorPure_universal R R (originalRegularBimodule R) X).2 X
    (fun a x => a.down • x) (by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro a b x; exact add_smul _ _ _
      · intro a x y; exact smul_add _ _ _
      · intro s a x; exact mul_smul _ _ _
      · intro r a x; exact mul_smul _ _ _))).1 a x

/-- Inserting the regular unit gives the inverse tensor map. -/
noncomputable def originalRegularTensorInv (X : ModuleCat.{max u v} R) :
    X →ₗ[R] (originalTensor R R (originalRegularBimodule R)).obj X where
  toFun x := originalTensorPure R R (originalRegularBimodule R) X (⟨1⟩ : ULift.{v} R) x
  map_add' x y := (originalTensorPure_universal R R (originalRegularBimodule R) X).1.2.1 _ x y
  map_smul' r x := by
    let p := originalTensorPure R R (originalRegularBimodule R) X
    have hb := (originalTensorPure_universal R R (originalRegularBimodule R) X).1
    change p (⟨1⟩ : ULift.{v} R) (r • x) = r • p (⟨1⟩ : ULift.{v} R) x
    calc
      p (⟨1⟩ : ULift.{v} R) (r • x) =
          p (originalRight R R (originalRegularBimodule R) (⟨1⟩ : ULift.{v} R) r) x :=
        (hb.2.2.2 r (⟨1⟩ : ULift.{v} R) x).symm
      _ = p (r • (⟨1⟩ : ULift.{v} R)) x := by
        congr 1
        apply ULift.ext
        simp [originalRegularBimodule_right]
      _ = r • p (⟨1⟩ : ULift.{v} R) x := hb.2.2.1 r _ x

/-- The regular tensor map is an isomorphism on every module. -/
noncomputable def originalRegularTensorIso (X : ModuleCat.{max u v} R) :
    (originalTensor R R (originalRegularBimodule R)).obj X ≃ₗ[R] X := by
  apply LinearEquiv.ofLinearMap (originalRegularTensorMap R X) (originalRegularTensorInv R X)
  · ext x
    change originalRegularTensorMap R X
      (originalTensorPure R R (originalRegularBimodule R) X (⟨1⟩ : ULift.{v} R) x) = x
    rw [originalRegularTensorMap_pure, one_smul]
  · let p := originalTensorPure R R (originalRegularBimodule R) X
    have hp := (originalTensorPure_universal R R (originalRegularBimodule R) X).1
    obtain ⟨g, hg, unique⟩ := (originalTensorPure_universal R R (originalRegularBimodule R) X).2
      ((originalTensor R R (originalRegularBimodule R)).obj X) p hp
    have hcomp : ∀ a x, ((originalRegularTensorInv R X).comp (originalRegularTensorMap R X)) (p a x) = p a x := by
      intro a x
      change p (⟨1⟩ : ULift.{v} R) (originalRegularTensorMap R X (p a x)) = p a x
      rw [originalRegularTensorMap_pure]
      calc
        p (⟨1⟩ : ULift.{v} R) (a.down • x) =
            p (originalRight R R (originalRegularBimodule R) (⟨1⟩ : ULift.{v} R) a.down) x :=
          (hp.2.2.2 a.down (⟨1⟩ : ULift.{v} R) x).symm
        _ = p a x := by
          congr 1
          apply ULift.ext
          simp [originalRegularBimodule_right]
    have hid : ∀ a x, (LinearMap.id : (originalTensor R R (originalRegularBimodule R)).obj X →ₗ[R] _) (p a x) = p a x := by intros; rfl
    exact (unique _ hcomp).trans (unique _ hid).symm

/-- The regular tensor isomorphisms are natural in the module. -/
noncomputable def originalRegularTensorNatIso :
    originalTensor R R (originalRegularBimodule R) ≅ 𝟭 (ModuleCat.{max u v} R) := by
  refine NatIso.ofComponents (fun X => (originalRegularTensorIso R X).toModuleIso) ?_
  intro X Y f
  apply ModuleCat.hom_ext
  let p := originalTensorPure R R (originalRegularBimodule R) X
  let h : ULift.{v} R → X → Y := fun a x => a.down • f.hom x
  have hb : originalBalanced R R (originalRegularBimodule R) X Y h := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b x; exact add_smul _ _ _
    · intro a x y; change a.down • f.hom (x + y) = _; rw [map_add, smul_add]
    · intro s a x; exact mul_smul _ _ _
    · intro r a x; change (a.down * r) • f.hom x = a.down • f.hom (r • x); rw [map_smul, mul_smul]
  obtain ⟨g, hg, unique⟩ := (originalTensorPure_universal R R (originalRegularBimodule R) X).2 Y h hb
  have left : ∀ a x,
      ((originalRegularTensorMap R Y).comp ((originalTensor R R (originalRegularBimodule R)).map f).hom) (p a x) = h a x := by
    intro a x
    change originalRegularTensorMap R Y (((originalTensor R R (originalRegularBimodule R)).map f).hom (p a x)) = _
    rw [originalTensorPure_map, originalRegularTensorMap_pure]
  have right : ∀ a x,
      (f.hom.comp (originalRegularTensorMap R X)) (p a x) = h a x := by
    intro a x
    change f.hom (originalRegularTensorMap R X (p a x)) = _
    rw [originalRegularTensorMap_pure, map_smul]
  exact (unique _ left).trans (unique _ right).symm

/-- The natural unit isomorphism has the paper's formula on pure tensors. -/
theorem originalRegularTensorNatIso_pure (X : ModuleCat.{max u v} R)
    (a : ULift.{v} R) (x : X) :
    ((originalRegularTensorNatIso R).hom.app X).hom
      (originalTensorPure R R (originalRegularBimodule R) X a x) = a.down • x :=
  originalRegularTensorMap_pure R X a x

#print axioms originalRegularTensorNatIso
#print axioms originalRegularTensorNatIso_pure
#print axioms originalRegularTensorIso
#print axioms originalRegularTensorMap_pure

end NotesProofs.General
