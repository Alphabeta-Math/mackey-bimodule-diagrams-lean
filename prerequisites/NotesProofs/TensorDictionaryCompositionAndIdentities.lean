import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.BalancedTensorAssociativity
import NotesProofs.RegularModuleTensorUnits

set_option maxHeartbeats 2000000

universe u

namespace NotesTensorDictionary

open CategoryTheory NotesProofs

-- Ian X, Abelian Categories and Bimodules, Theorem 10.1 (env-10-1).
-- https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=32
-- https://alphabetamath.cc/item/lem-tensoring-defines-a-pseudofunctor-with-interchange
-- The article needs the two natural comparisons from portal steps 1.2–1.3.
-- The later portal coherence and interchange clauses concern the larger
-- pseudofunctor statement.

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
-- Theorem 10.1 links Chapter 6 through env-6-5, whose statement is the
-- associator. The unitor is Theorem 6.4 (env-6-4), which is the unit
-- clause formalized by RegularModuleTensorUnits.
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
    (ModuleCat.ofHom (Module.toModuleEnd S B (MulOpposite.op r))))
      (pure (S := T) C (X := ModuleCat.of S B) c b) = _
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

variable (S T) in
private abbrev srcPure (c : C) (b : B) (x : X) : (src R S T B C).obj X :=
  pure (S := T) C (X := (tensor (S := S) B).obj X) c (pure (S := S) B b x)

variable (S T) in
private abbrev dstPure (c : C) (b : B) (x : X) : (dst R S T B C).obj X :=
  pure (S := T) (composite S T B C : Type u) (pure (S := T) C (X := ModuleCat.of S B) c b) x

private theorem src_ext {Y : Type u} [AddCommGroup Y] (f g : (src R S T B C).obj X →+ Y)
    (h : ∀ c b x, f (srcPure S T X c b x) = g (srcPure S T X c b x)) : f = g := by
  apply tensor_ext (S := T) C
  intro c z
  exact DFunLike.congr_fun
    (tensor_ext (S := S) B (f.comp (pureRight (S := T) C c)) (g.comp (pureRight (S := T) C c)) (h c)) z

private theorem dst_ext {Y : Type u} [AddCommGroup Y] (f g : (dst R S T B C).obj X →+ Y)
    (h : ∀ c b x, f (dstPure S T X c b x) = g (dstPure S T X c b x)) : f = g := by
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
-- ChoiceFreeWatts.tensorLift, tensorLinearLift, their pure formulas, and
-- tensorExt supply descent and uniqueness on this quotient (WattsSupport.lean,
-- SHA-256 853d1dd0016bf0735f7a84559e2f1cbbb701fc3cb0e00395a0e138ffecb1f967).
-- The pinned Mathlib TensorProduct.assoc requires a commutative base semiring.
-- The commuting outer actions used here leave all three rings arbitrary.
variable (S T B C) in
private theorem toCompositeInner_balanced (c : C) :
    ChoiceFreeWatts.Balanced (rightAction (R := R) (M := B))
      (fun b x => dstPure S T X c b x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b b' x
    change pure (S := T) (composite S T B C : Type u)
      (pure (S := T) C (X := ModuleCat.of S B) c (b + b')) x = _
    rw [pure_add_right, pure_add_left]
  · intro b x x'
    exact pure_add_right (composite S T B C : Type u) _ x x'
  · intro r b x
    change pure (S := T) (composite S T B C : Type u)
      (pure (S := T) C (X := ModuleCat.of S B) c (MulOpposite.op r • b)) x = _
    rw [← right_pure (B := B) (C := C) (T := T), pure_balance]

variable (S T B C) in
private def toCompositeInner (c : C) : (tensor (S := S) B).obj X →+ (dst R S T B C).obj X :=
  ChoiceFreeWatts.tensorLift rightAction _ (toCompositeInner_balanced S T B C X c)

variable (S T B C) in
private theorem toCompositeInner_pure (c : C) (b : B) (x : X) :
    toCompositeInner S T B C X c (pure (S := S) B b x) = dstPure S T X c b x :=
  ChoiceFreeWatts.tensorLift_pure rightAction _ (toCompositeInner_balanced S T B C X c) b x

variable (S T B C) in
private theorem toComposite_balanced :
    ChoiceFreeWatts.Balanced (rightAction (R := S) (M := C))
      (toCompositeInner S T B C X · ·) := by
  refine ⟨?_, fun c => map_add (toCompositeInner S T B C X c), ?_⟩
  · intro c c' z
    have h : toCompositeInner S T B C X (c + c') = toCompositeInner S T B C X c + toCompositeInner S T B C X c' := by
      apply tensor_ext (S := S) B
      intro b x
      simp only [AddMonoidHom.add_apply, toCompositeInner_pure, dstPure, pure_add_left]
    exact DFunLike.congr_fun h z
  · intro s c z
    let scale := DistribSMul.toAddMonoidHom ((tensor (S := S) B).obj X) s
    have h : toCompositeInner S T B C X (MulOpposite.op s • c) = (toCompositeInner S T B C X c).comp scale := by
      apply tensor_ext (S := S) B
      intro b x
      change toCompositeInner S T B C X (MulOpposite.op s • c) (pure (S := S) B b x) =
        toCompositeInner S T B C X c (s • pure (S := S) B b x)
      simp only [smul_pure, toCompositeInner_pure, dstPure, pure_balance]
    exact DFunLike.congr_fun h z

variable (S T B C) in
private theorem toComposite_outer (t : T) (c : C) (z : (tensor (S := S) B).obj X) :
    toCompositeInner S T B C X (t • c) z = t • toCompositeInner S T B C X c z := by
  let scale := DistribSMul.toAddMonoidHom ((dst R S T B C).obj X) t
  have h : toCompositeInner S T B C X (t • c) = scale.comp (toCompositeInner S T B C X c) := by
    apply tensor_ext (S := S) B
    intro b x
    change toCompositeInner S T B C X (t • c) (pure (S := S) B b x) =
      t • toCompositeInner S T B C X c (pure (S := S) B b x)
    simp only [toCompositeInner_pure, dstPure, smul_pure]
  exact DFunLike.congr_fun h z

variable (S T B C) in
private def toComposite : (src R S T B C).obj X →ₗ[T] (dst R S T B C).obj X :=
  ChoiceFreeWatts.tensorLinearLift rightAction right_commute
    (toCompositeInner S T B C X · ·) (toComposite_balanced S T B C X) (toComposite_outer S T B C X)

variable (S T B C) in
private theorem toComposite_pure (c : C) (b : B) (x : X) :
    toComposite S T B C X (srcPure S T X c b x) = dstPure S T X c b x :=
  (ChoiceFreeWatts.tensorLinearLift_pure rightAction right_commute
    (toCompositeInner S T B C X · ·) (toComposite_balanced S T B C X) (toComposite_outer S T B C X) c _).trans
    (toCompositeInner_pure S T B C X c b x)

variable (S T B C) in
private theorem fromCompositeInner_balanced (x : X) :
    ChoiceFreeWatts.Balanced (rightAction (R := S) (M := C))
      (fun c (b : B) => srcPure S T X c b x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c c' b
    exact pure_add_left C c c' (pure (S := S) B b x)
  · intro c b b'
    simp only [srcPure, pure_add_left, pure_add_right]
  · intro s c b
    change srcPure S T X (MulOpposite.op s • c) b x = srcPure S T X c (s • b) x
    simp only [srcPure, pure_balance, smul_pure]

variable (S T B C) in
private def fromCompositeInner (x : X) : composite S T B C →ₗ[T] (src R S T B C).obj X :=
  ChoiceFreeWatts.tensorLinearLift rightAction right_commute _
    (fromCompositeInner_balanced S T B C X x) (fun t c b => (smul_pure C t c (pure (S := S) B b x)).symm)

variable (S T B C) in
private theorem fromCompositeInner_pure (c : C) (b : B) (x : X) :
    fromCompositeInner S T B C X x (pure (S := T) C (X := ModuleCat.of S B) c b) = srcPure S T X c b x :=
  ChoiceFreeWatts.tensorLinearLift_pure rightAction right_commute _
    (fromCompositeInner_balanced S T B C X x) _ c b

variable (S T B C) in
private theorem fromComposite_balanced :
    ChoiceFreeWatts.Balanced (rightAction (R := R) (M := (composite S T B C : Type u)))
      (fun z x => fromCompositeInner S T B C X x z) := by
  refine ⟨fun z z' x => map_add (fromCompositeInner S T B C X x) z z', ?_, ?_⟩
  · intro z x x'
    have h : (fromCompositeInner S T B C X (x + x')).toAddMonoidHom =
        (fromCompositeInner S T B C X x).toAddMonoidHom + (fromCompositeInner S T B C X x').toAddMonoidHom := by
      apply tensor_ext (S := T) C
      intro c b
      simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.add_apply,
        fromCompositeInner_pure, srcPure, pure_add_right]
    exact DFunLike.congr_fun h z
  · intro r z x
    let scale := (rightActionHom (S := S) (T := T) B C (MulOpposite.op r)).toAddMonoidHom
    have h : (fromCompositeInner S T B C X x).toAddMonoidHom.comp scale =
        (fromCompositeInner S T B C X (r • x)).toAddMonoidHom := by
      apply tensor_ext (S := T) C
      intro c b
      change fromCompositeInner S T B C X x (MulOpposite.op r • pure (S := T) C (X := ModuleCat.of S B) c b) =
        fromCompositeInner S T B C X (r • x) (pure (S := T) C (X := ModuleCat.of S B) c b)
      simp only [right_pure, fromCompositeInner_pure, srcPure, pure_balance]
    exact DFunLike.congr_fun h z

variable (S T B C) in
private def fromComposite : (dst R S T B C).obj X →ₗ[T] (src R S T B C).obj X :=
  ChoiceFreeWatts.tensorLinearLift rightAction right_commute
    (fun z x => fromCompositeInner S T B C X x z) (fromComposite_balanced S T B C X)
    (fun t z x => (fromCompositeInner S T B C X x).map_smul t z)

variable (S T B C) in
private theorem fromComposite_pure (c : C) (b : B) (x : X) :
    fromComposite S T B C X (dstPure S T X c b x) = srcPure S T X c b x :=
  (ChoiceFreeWatts.tensorLinearLift_pure rightAction right_commute
    (fun z x => fromCompositeInner S T B C X x z) (fromComposite_balanced S T B C X) _ _ x).trans
    (fromCompositeInner_pure S T B C X c b x)

private def component : (src R S T B C).obj X ≅ (dst R S T B C).obj X := by
  let forward := toComposite S T B C X
  let backward := fromComposite S T B C X
  refine (LinearEquiv.ofLinearMap forward backward ?_ ?_).toModuleIso
  · apply LinearMap.toAddMonoidHom_injective
    apply dst_ext (S := S) (T := T) X
    intro c b x
    change forward (backward (dstPure S T X c b x)) =
      dstPure S T X c b x
    simp only [forward, backward, fromComposite_pure, toComposite_pure]
  · apply LinearMap.toAddMonoidHom_injective
    apply src_ext (S := S) (T := T) X
    intro c b x
    change backward (forward (srcPure S T X c b x)) =
      srcPure S T X c b x
    simp only [forward, backward, toComposite_pure, fromComposite_pure]

private theorem component_pure (c : C) (b : B) (x : X) :
    (component (S := S) (T := T) X).hom (srcPure S T X c b x) =
      dstPure S T X c b x :=
  toComposite_pure S T B C X c b x

private theorem src_map_pure {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (c : C) (b : B) (x : X) :
    ((src R S T B C).map f) (srcPure S T X c b x) =
      srcPure S T Y c b (f x) := by
  change ((tensor (R := S) (S := T) C).map ((tensor (R := R) (S := S) B).map f))
    (pure (S := T) C c (pure (S := S) B b x)) = _
  rw [map_pure, map_pure]

private theorem dst_map_pure {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (c : C) (b : B) (x : X) :
    ((dst R S T B C).map f) (dstPure S T X c b x) =
      dstPure S T Y c b (f x) :=
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
      ((src R S T B C).map f (srcPure S T X c b x)) =
    (dst R S T B C).map f ((component (S := S) (T := T) X).hom
      (srcPure S T X c b x))
  rw [src_map_pure, component_pure, component_pure, dst_map_pure]

variable (R S T B C) in
theorem composition_pure (c : C) (b : B) (x : X) :
    ((composition R S T B C).hom.app X) (srcPure S T X c b x) =
      dstPure S T X c b x :=
  component_pure (S := S) (T := T) X c b x

end Composition
end NotesTensorDictionary

theorem TensorDictionaryCompositionAndIdentities : (
∀ (R : Type u) [Ring R],
  (let F := NotesProofs.concreteTensorFunctor (R := R) (S := R) R
   ∃ unit : CategoryTheory.Iso F (CategoryTheory.Functor.id (ModuleCat.{u} R)),
     ∀ (M : ModuleCat.{u} R) (r : R) (m : M),
       (unit.hom.app M) (NotesProofs.concretePure (R := R) (M := R) r m) = r • m) ∧
  (∀ (S T : Type u) [Ring S] [Ring T]
      (B C : Type u) [AddCommGroup B] [AddCommGroup C]
      [Module S B] [Module (MulOpposite R) B] [SMulCommClass (MulOpposite R) S B]
      [Module T C] [Module (MulOpposite S) C] [SMulCommClass (MulOpposite S) T C],
    let TB := NotesProofs.concreteTensorFunctor (R := R) (S := S) B
    let TC := NotesProofs.concreteTensorFunctor (R := S) (S := T) C
    let CB := TC.obj (ModuleCat.of S B)
    let pureCB := fun (c : C) (b : B) =>
      (NotesProofs.concretePure (R := S) (M := C) c b : CB)
    (∀ (t : T) (c : C) (b : B), (ModuleCat.isModule CB).smul t (pureCB c b) = pureCB (t • c) b) ∧
    (∃ rightCB : Module (MulOpposite R) CB,
      letI := rightCB
      (∀ (r : R) (c : C) (b : B),
        rightCB.smul (MulOpposite.op r) (pureCB c b) = pureCB c (MulOpposite.op r • b)) ∧
      (∃ commute : SMulCommClass (MulOpposite R) T CB,
        letI := commute
        let TCB := NotesProofs.concreteTensorFunctor (R := R) (S := T) (CB : Type u)
        ∃ assoc : CategoryTheory.Iso (CategoryTheory.Functor.comp TB TC) TCB,
          ∀ (M : ModuleCat.{u} R) (c : C) (b : B) (m : M),
            (assoc.hom.app M) (NotesProofs.concretePure (R := S) (M := C) c
              (NotesProofs.concretePure (R := R) (M := B) b m)) =
              NotesProofs.concretePure (R := R) (M := (CB : Type u)) (pureCB c b) m)))
) :=
(by
  -- Theorem 10.1, p. 32. Portal steps 1.2 and 1.3 supply the comparison
  -- directions after using the article's evaluation direction for the unit.
  intro R _
  refine ⟨NotesTensorDictionary.regular R, ?_⟩
  intro S T _ _ B C _ _ _ _ _ _ _ _ TB TC CB pureCB
  refine ⟨NotesTensorDictionary.left_pure B C, ?_⟩
  refine ⟨NotesTensorDictionary.rightModule B C, NotesTensorDictionary.right_pure B C, ?_⟩
  exact ⟨NotesTensorDictionary.rightCommutes B C, NotesTensorDictionary.composition R S T B C,
    NotesTensorDictionary.composition_pure R S T B C⟩)
