import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.BalancedTensorAssociativity
import NotesProofs.RegularModuleTensorUnits
open CategoryTheory NotesProofs

namespace NotesTensorDictionary

universe u

set_option backward.isDefEq.respectTransparency false

section Tensor

variable {R S : Type u} [Ring R] [Ring S]
variable (B : Type u) [AddCommGroup B] [Module S B] [Module (MulOpposite R) B]
  [SMulCommClass (MulOpposite R) S B]

private abbrev tensor := concreteTensorFunctor (R := R) (S := S) B

private abbrev pure {X : ModuleCat.{u} R} (b : B) (x : X) :
    (tensor (S := S) B).obj X :=
  concretePure (R := R) (M := B) b x

private theorem pure_add_left {X : ModuleCat.{u} R} (b b' : B) (x : X) :
    pure (S := S) B (b + b') x = pure B b x + pure B b' x :=
  (ChoiceFreeWatts.pureBalanced rightAction).1 b b' x

private theorem pure_add_right {X : ModuleCat.{u} R} (b : B) (x x' : X) :
    pure (S := S) B b (x + x') = pure B b x + pure B b x' :=
  (ChoiceFreeWatts.pureBalanced rightAction).2.1 b x x'

private theorem pure_balance {X : ModuleCat.{u} R} (r : R) (b : B) (x : X) :
    pure (S := S) B (MulOpposite.op r • b) x = pure B b (r • x) :=
  (ChoiceFreeWatts.pureBalanced rightAction).2.2 r b x

private theorem smul_pure {X : ModuleCat.{u} R} (s : S) (b : B) (x : X) :
    s • pure (S := S) B b x = pure B (s • b) x :=
  ChoiceFreeWatts.scale_pure rightAction right_commute s b x

private theorem map_pure {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (b : B) (x : X) :
    ((tensor (S := S) B).map f) (pure B b x) = pure B b (f x) :=
  concreteTensorMap_pure (S := S) f.hom b x

private theorem tensor_ext {X : ModuleCat.{u} R} {Y : Type u} [AddCommGroup Y]
    (f g : (tensor (S := S) B).obj X →+ Y)
    (h : ∀ b x, f (pure B b x) = g (pure B b x)) : f = g :=
  ChoiceFreeWatts.tensorExt rightAction f g h

private def pureLeft {X : ModuleCat.{u} R} (x : X) : B →+ (tensor (S := S) B).obj X :=
  AddMonoidHom.mk' (fun b => pure B b x) (fun b b' => pure_add_left B b b' x)

private def pureRight {X : ModuleCat.{u} R} (b : B) : X →+ (tensor (S := S) B).obj X :=
  concretePure (R := R) (M := B) b

end Tensor

section Regular

variable (R : Type u) [Ring R]

-- Alphabeta Math, lem-tensoring-defines-a-pseudofunctor-with-interchange,
-- step 1.3. The article's comparison is the unitor itself. The left clause
-- of RegularModuleTensorUnits has definitionally the same quotient and action:
-- op r acts on a by a * r. Its naturality witness is existential, so check
-- naturality for the actual functor map by testing on pure tensors.
theorem regular :
    ∃ unit : tensor (R := R) (S := R) R ≅ Functor.id (ModuleCat.{u} R),
      ∀ (M : ModuleCat.{u} R) (r : R) (m : M),
        (unit.hom.app M) (pure R r m) = r • m := by
  obtain ⟨unit, hp, _⟩ := (RegularModuleTensorUnits.{u,u,u,u} R).1
  let F := tensor (R := R) (S := R) R
  let component (M : ModuleCat.{u} R) : F.obj M ≅ M := (unit M).toModuleIso
  have h (M : ModuleCat.{u} R) (r : R) (m : M) :
      (component M).hom (pure R r m) = r • m := hp M r m
  refine ⟨NatIso.ofComponents component ?_, h⟩
  intro M N f
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply tensor_ext (S := R) R
  intro r m
  change (component N).hom (F.map f (pure R r m)) =
    f ((component M).hom (pure R r m))
  rw [map_pure, h, h]
  exact (f.hom.map_smul r m).symm

end Regular

section Composition

variable {R S T : Type u} [Ring R] [Ring S] [Ring T]
variable (B C : Type u) [AddCommGroup B] [AddCommGroup C]
  [Module S B] [Module (MulOpposite R) B] [SMulCommClass (MulOpposite R) S B]
  [Module T C] [Module (MulOpposite S) C] [SMulCommClass (MulOpposite S) T C]

abbrev composite (S T : Type u) [Ring S] [Ring T]
    (B C : Type u) [AddCommGroup B] [AddCommGroup C]
    [Module S B] [Module T C] [Module (MulOpposite S) C]
    [SMulCommClass (MulOpposite S) T C] := (tensor (R := S) (S := T) C).obj (ModuleCat.of S B)

-- Descend right multiplication by applying the additive tensor functor to
-- the S-linear scalar endomorphisms of B. This proves all module laws at once.
private def rightActionHom : MulOpposite R →+* Module.End T (composite S T B C) := by
  let X := ModuleCat.of S B
  let F := tensor (R := S) (S := T) C
  let mapEnd : End X →+* End (F.obj X) :=
    { F.mapEnd X with
      map_zero' := by apply End.ext; exact F.map_zero _ _
      map_add' := by intro f g; apply End.ext; exact F.map_add }
  exact (ModuleCat.endRingEquiv (F.obj X)).toRingHom.comp
    (mapEnd.comp ((ModuleCat.endRingEquiv X).symm.toRingHom.comp (Module.toModuleEnd S B)))

@[instance_reducible] def rightModule : Module (MulOpposite R) (composite S T B C) :=
  Module.compHom _ (rightActionHom (S := S) (T := T) B C)

local instance : Module (MulOpposite R) (composite S T B C) := rightModule B C

theorem rightCommutes : SMulCommClass (MulOpposite R) T (composite S T B C) :=
  ⟨fun a t z => (rightActionHom (S := S) (T := T) B C a).map_smul t z⟩

local instance : SMulCommClass (MulOpposite R) T (composite S T B C) := rightCommutes B C

theorem right_pure (r : R) (c : C) (b : B) :
    MulOpposite.op r • pure (S := T) C (X := ModuleCat.of S B) c b =
      pure (S := T) C (X := ModuleCat.of S B) c (MulOpposite.op r • b) := by
  change ((tensor (R := S) (S := T) C).map
    (ModuleCat.ofHom (Module.toModuleEnd S B (MulOpposite.op r)))) (pure (S := T) C (X := ModuleCat.of S B) c b) = _
  rw [map_pure]
  rfl

theorem left_pure (t : T) (c : C) (b : B) :
    t • pure (S := T) C (X := ModuleCat.of S B) c b =
      pure (S := T) C (X := ModuleCat.of S B) (t • c) b :=
  smul_pure C (X := ModuleCat.of S B) t c b

variable (R S T) in
private abbrev src : ModuleCat.{u} R ⥤ ModuleCat.{u} T :=
  tensor (R := R) (S := S) B ⋙ tensor (R := S) (S := T) C

variable (R S T) in
private abbrev dst : ModuleCat.{u} R ⥤ ModuleCat.{u} T :=
  tensor (R := R) (S := T) (composite S T B C : Type u)

variable {B C}
variable (X : ModuleCat.{u} R)

private abbrev srcPure (c : C) (b : B) (x : X) : (src R S T B C).obj X :=
  pure (S := T) C (X := (tensor (S := S) B).obj X) c (pure (S := S) B b x)

private abbrev dstPure (c : C) (b : B) (x : X) : (dst R S T B C).obj X :=
  pure (S := T) (composite S T B C : Type u) (pure (S := T) C (X := ModuleCat.of S B) c b) x

private theorem src_ext {Y : Type u} [AddCommGroup Y] (f g : (src R S T B C).obj X →+ Y)
    (h : ∀ c b x, f (srcPure X c b x) = g (srcPure X c b x)) : f = g := by
  apply tensor_ext (S := T) C
  intro c z
  exact DFunLike.congr_fun
    (tensor_ext (S := S) B (f.comp (pureRight (S := T) C c)) (g.comp (pureRight (S := T) C c)) (h c)) z

private theorem dst_ext {Y : Type u} [AddCommGroup Y] (f g : (dst R S T B C).obj X →+ Y)
    (h : ∀ c b x, f (dstPure X c b x) = g (dstPure X c b x)) : f = g := by
  apply tensor_ext (S := T) (composite S T B C : Type u)
  intro z x
  exact DFunLike.congr_fun
    (tensor_ext (S := T) C (f.comp (pureLeft (composite S T B C : Type u) x))
      (g.comp (pureLeft (composite S T B C : Type u) x)) (fun c b => h c b x)) z

-- Ian X, Theorem 10.1 (env-10-1, p. 32), and Alphabeta Math step 1.2.
-- The registered BalancedTensorAssociativity and NotesBalancedAssoc.assoc
-- use a Finsupp quotient, whereas the reviewed functors use a FreeAddGroup
-- quotient. Use the coordinator's two balanced descents on the actual
-- quotient, including its fixed T-action and the right action above.
-- The portal takes the inverse of its associator in step 1.2. Here the
-- comparison already points from C ⊗ (B ⊗ X) to (C ⊗ B) ⊗ X.
private theorem toCompositeInner_balanced (c : C) :
    ChoiceFreeWatts.Balanced (rightAction (R := R) (M := B))
      (fun b x => dstPure (S := S) (T := T) (B := B) (C := C) X c b x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b b' x
    change pure (S := T) (composite S T B C : Type u) (pure (S := T) C (X := ModuleCat.of S B) c (b + b')) x = _
    rw [pure_add_right, pure_add_left]
  · intro b x x'
    exact pure_add_right (composite S T B C : Type u) _ x x'
  · intro r b x
    change dstPure (S := S) (T := T) (B := B) (C := C) X c (MulOpposite.op r • b) x = dstPure (S := S) (T := T) (B := B) (C := C) X c b (r • x)
    change pure (S := T) (composite S T B C : Type u) (pure (S := T) C (X := ModuleCat.of S B) c (MulOpposite.op r • b)) x = _
    rw [← right_pure (B := B) (C := C) (T := T), pure_balance]

private def toCompositeInner (c : C) : (tensor (S := S) B).obj X →+ (dst R S T B C).obj X :=
  ChoiceFreeWatts.tensorLift rightAction _ (toCompositeInner_balanced (S := S) (T := T) (B := B) (C := C) X c)

private theorem toCompositeInner_pure (c : C) (b : B) (x : X) :
    toCompositeInner (S := S) (T := T) (B := B) (C := C) X c (pure (S := S) B b x) = dstPure (S := S) (T := T) (B := B) (C := C) X c b x :=
  ChoiceFreeWatts.tensorLift_pure rightAction _ (toCompositeInner_balanced (S := S) (T := T) (B := B) (C := C) X c) b x

private theorem toComposite_balanced :
    ChoiceFreeWatts.Balanced (rightAction (R := S) (M := C))
      (toCompositeInner (S := S) (T := T) (B := B) (C := C) X · ·) := by
  refine ⟨?_, fun c => map_add (toCompositeInner (S := S) (T := T) (B := B) (C := C) X c), ?_⟩
  · intro c c' z
    have h : toCompositeInner (S := S) (T := T) (B := B) (C := C) X (c + c') = toCompositeInner (S := S) (T := T) (B := B) (C := C) X c + toCompositeInner (S := S) (T := T) (B := B) (C := C) X c' := by
      apply tensor_ext (S := S) B
      intro b x
      simp only [AddMonoidHom.add_apply, toCompositeInner_pure, dstPure, pure_add_left]
    exact DFunLike.congr_fun h z
  · intro s c z
    let scale := DistribSMul.toAddMonoidHom ((tensor (S := S) B).obj X) s
    have h : toCompositeInner (S := S) (T := T) (B := B) (C := C) X (MulOpposite.op s • c) = (toCompositeInner (S := S) (T := T) (B := B) (C := C) X c).comp scale := by
      apply tensor_ext (S := S) B
      intro b x
      change toCompositeInner (S := S) (T := T) (B := B) (C := C) X (MulOpposite.op s • c) (pure (S := S) B b x) =
        toCompositeInner (S := S) (T := T) (B := B) (C := C) X c (s • pure (S := S) B b x)
      simp only [smul_pure, toCompositeInner_pure, dstPure, pure_balance]
    exact DFunLike.congr_fun h z

private theorem toComposite_outer (t : T) (c : C) (z : (tensor (S := S) B).obj X) :
    toCompositeInner (S := S) (T := T) (B := B) (C := C) X (t • c) z = t • toCompositeInner (S := S) (T := T) (B := B) (C := C) X c z := by
  let scale := DistribSMul.toAddMonoidHom ((dst R S T B C).obj X) t
  have h : toCompositeInner (S := S) (T := T) (B := B) (C := C) X (t • c) = scale.comp (toCompositeInner (S := S) (T := T) (B := B) (C := C) X c) := by
    apply tensor_ext (S := S) B
    intro b x
    change toCompositeInner (S := S) (T := T) (B := B) (C := C) X (t • c) (pure (S := S) B b x) =
      t • toCompositeInner (S := S) (T := T) (B := B) (C := C) X c (pure (S := S) B b x)
    simp only [toCompositeInner_pure, dstPure, smul_pure]
  exact DFunLike.congr_fun h z

private def toComposite : (src R S T B C).obj X →ₗ[T] (dst R S T B C).obj X :=
  ChoiceFreeWatts.tensorLinearLift rightAction right_commute
    (toCompositeInner (S := S) (T := T) (B := B) (C := C) X · ·) (toComposite_balanced (S := S) (T := T) (B := B) (C := C) X) (toComposite_outer (S := S) (T := T) (B := B) (C := C) X)

private theorem toComposite_pure (c : C) (b : B) (x : X) :
    toComposite (S := S) (T := T) (B := B) (C := C) X (srcPure (S := S) (T := T) (B := B) (C := C) X c b x) = dstPure (S := S) (T := T) (B := B) (C := C) X c b x :=
  (ChoiceFreeWatts.tensorLinearLift_pure rightAction right_commute
    (toCompositeInner (S := S) (T := T) (B := B) (C := C) X · ·) (toComposite_balanced (S := S) (T := T) (B := B) (C := C) X) (toComposite_outer (S := S) (T := T) (B := B) (C := C) X) c _).trans
    (toCompositeInner_pure (S := S) (T := T) (B := B) (C := C) X c b x)

private theorem fromCompositeInner_balanced (x : X) :
    ChoiceFreeWatts.Balanced (rightAction (R := S) (M := C))
      (fun c b => srcPure (S := S) (T := T) (B := B) (C := C) X c b x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c c' b
    exact pure_add_left C c c' (pure (S := S) B b x)
  · intro c b b'
    simp only [srcPure, pure_add_left, pure_add_right]
  · intro s c b
    change srcPure (S := S) (T := T) (B := B) (C := C) X (MulOpposite.op s • c) b x = srcPure (S := S) (T := T) (B := B) (C := C) X c (s • b) x
    simp only [srcPure, pure_balance, smul_pure]

private def fromCompositeInner (x : X) : composite S T B C →ₗ[T] (src R S T B C).obj X :=
  ChoiceFreeWatts.tensorLinearLift rightAction right_commute _
    (fromCompositeInner_balanced (S := S) (T := T) (B := B) (C := C) X x) (fun t c b => (smul_pure C t c (pure (S := S) B b x)).symm)

private theorem fromCompositeInner_pure (c : C) (b : B) (x : X) :
    fromCompositeInner (S := S) (T := T) (B := B) (C := C) X x (pure (S := T) C (X := ModuleCat.of S B) c b) = srcPure (S := S) (T := T) (B := B) (C := C) X c b x :=
  ChoiceFreeWatts.tensorLinearLift_pure rightAction right_commute _
    (fromCompositeInner_balanced (S := S) (T := T) (B := B) (C := C) X x) _ c b

private theorem fromComposite_balanced :
    ChoiceFreeWatts.Balanced (rightAction (R := R) (M := (composite S T B C : Type u)))
      (fun z x => fromCompositeInner (S := S) (T := T) (B := B) (C := C) X x z) := by
  refine ⟨fun z z' x => map_add (fromCompositeInner (S := S) (T := T) (B := B) (C := C) X x) z z', ?_, ?_⟩
  · intro z x x'
    have h : (fromCompositeInner (S := S) (T := T) (B := B) (C := C) X (x + x')).toAddMonoidHom =
        (fromCompositeInner (S := S) (T := T) (B := B) (C := C) X x).toAddMonoidHom + (fromCompositeInner (S := S) (T := T) (B := B) (C := C) X x').toAddMonoidHom := by
      apply tensor_ext (S := T) C
      intro c b
      simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.add_apply,
        fromCompositeInner_pure, srcPure, pure_add_right]
    exact DFunLike.congr_fun h z
  · intro r z x
    let scale := (rightActionHom (S := S) (T := T) B C (MulOpposite.op r)).toAddMonoidHom
    have h : (fromCompositeInner (S := S) (T := T) (B := B) (C := C) X x).toAddMonoidHom.comp scale =
        (fromCompositeInner (S := S) (T := T) (B := B) (C := C) X (r • x)).toAddMonoidHom := by
      apply tensor_ext (S := T) C
      intro c b
      change fromCompositeInner (S := S) (T := T) (B := B) (C := C) X x (MulOpposite.op r • pure (S := T) C (X := ModuleCat.of S B) c b) =
        fromCompositeInner (S := S) (T := T) (B := B) (C := C) X (r • x) (pure (S := T) C (X := ModuleCat.of S B) c b)
      simp only [right_pure, fromCompositeInner_pure, srcPure, pure_balance]
    exact DFunLike.congr_fun h z

private def fromComposite : (dst R S T B C).obj X →ₗ[T] (src R S T B C).obj X :=
  ChoiceFreeWatts.tensorLinearLift rightAction right_commute
    (fun z x => fromCompositeInner (S := S) (T := T) (B := B) (C := C) X x z) (fromComposite_balanced (S := S) (T := T) (B := B) (C := C) X)
    (fun t z x => (fromCompositeInner (S := S) (T := T) (B := B) (C := C) X x).map_smul t z)

private theorem fromComposite_pure (c : C) (b : B) (x : X) :
    fromComposite (S := S) (T := T) (B := B) (C := C) X (dstPure (S := S) (T := T) (B := B) (C := C) X c b x) = srcPure (S := S) (T := T) (B := B) (C := C) X c b x :=
  (ChoiceFreeWatts.tensorLinearLift_pure rightAction right_commute
    (fun z x => fromCompositeInner (S := S) (T := T) (B := B) (C := C) X x z) (fromComposite_balanced (S := S) (T := T) (B := B) (C := C) X) _ _ x).trans
    (fromCompositeInner_pure (S := S) (T := T) (B := B) (C := C) X c b x)

private def component : (src R S T B C).obj X ≅ (dst R S T B C).obj X := by
  let forward := toComposite (S := S) (T := T) (B := B) (C := C) X
  let backward := fromComposite (S := S) (T := T) (B := B) (C := C) X
  refine (LinearEquiv.ofLinearMap forward backward ?_ ?_).toModuleIso
  · apply LinearMap.toAddMonoidHom_injective
    apply dst_ext (S := S) (T := T) X
    intro c b x
    change forward (backward (dstPure (S := S) (T := T) X c b x)) =
      dstPure (S := S) (T := T) X c b x
    simp only [forward, backward, fromComposite_pure, toComposite_pure]
  · apply LinearMap.toAddMonoidHom_injective
    apply src_ext (S := S) (T := T) X
    intro c b x
    change backward (forward (srcPure (S := S) (T := T) X c b x)) =
      srcPure (S := S) (T := T) X c b x
    simp only [forward, backward, toComposite_pure, fromComposite_pure]

private theorem component_pure (c : C) (b : B) (x : X) :
    (component (S := S) (T := T) X).hom (srcPure (S := S) (T := T) X c b x) =
      dstPure (S := S) (T := T) X c b x :=
  toComposite_pure (S := S) (T := T) X c b x

private theorem src_map_pure {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (c : C) (b : B) (x : X) :
    ((src R S T B C).map f) (srcPure (S := S) (T := T) X c b x) =
      srcPure (S := S) (T := T) Y c b (f x) := by
  change ((tensor (R := S) (S := T) C).map ((tensor (R := R) (S := S) B).map f))
    (pure (S := T) C c (pure (S := S) B b x)) = _
  rw [map_pure, map_pure]
  rfl

private theorem dst_map_pure {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (c : C) (b : B) (x : X) :
    ((dst R S T B C).map f) (dstPure (S := S) (T := T) X c b x) =
      dstPure (S := S) (T := T) Y c b (f x) :=
  map_pure (composite S T B C : Type u) f _ x

-- The generator test in portal step 2.1 is used here for naturality in X,
-- which is the variable of the two functors in Theorem 10.1.
variable (R S T B C) in
def composition : src R S T B C ≅ dst R S T B C := by
  refine NatIso.ofComponents (component (S := S) (T := T) (B := B) (C := C)) ?_
  intro X Y f
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply src_ext (S := S) (T := T) X
  intro c b x
  change (component (S := S) (T := T) Y).hom
      ((src R S T B C).map f (srcPure (S := S) (T := T) X c b x)) =
    (dst R S T B C).map f ((component (S := S) (T := T) X).hom
      (srcPure (S := S) (T := T) X c b x))
  rw [src_map_pure, component_pure, component_pure, dst_map_pure]

variable (R S T B C) in
theorem composition_pure (c : C) (b : B) (x : X) :
    ((composition R S T B C).hom.app X) (srcPure (S := S) (T := T) X c b x) =
      dstPure (S := S) (T := T) X c b x :=
  component_pure (S := S) (T := T) X c b x

end Composition
end NotesTensorDictionary
