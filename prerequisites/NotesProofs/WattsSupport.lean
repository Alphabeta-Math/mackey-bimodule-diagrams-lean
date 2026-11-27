import MackeyDiagrams
import Proofs.RegularModuleRightAction
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.GroupTheory.FreeGroup.Basic

open CategoryTheory

namespace ChoiceFreeWatts

universe u v z w j

-- Alphabeta Math, lem-canonical-free-presentation-controls-eilenberg-watts-comparison,
-- Steps 1.1–2.2. Build the comparison on the reviewed balanced additive
-- quotient. CanonicalWattsComparison uses a Finsupp quotient, and its audit
-- and the ModuleTensorUniversalProperty audit include Classical.choice.
-- The descent uses FreeAddGroup.lift and AddCon.lift, with generator
-- uniqueness from the inverse of FreeAddGroup.lift. Both are in the pinned
-- mathlib revision 65d730f7150f21fdfa32f3e73a3f549c1f96a0e9 (Apache-2.0).
-- https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/FreeGroup/Basic.lean#L666
-- https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/Congruence/Hom.lean#L190
def Word {S : Type*} (r : FreeAddGroup S → FreeAddGroup S → Prop) :=
  (addConGen r).Quotient

instance {S : Type*} (r : FreeAddGroup S → FreeAddGroup S → Prop) :
    AddGroup (Word r) := AddCon.addGroup (addConGen r)

def wordMk {S : Type*} (r : FreeAddGroup S → FreeAddGroup S → Prop) :
    FreeAddGroup S →+ Word r := (addConGen r).mk'

def wordGen {S : Type*} (r : FreeAddGroup S → FreeAddGroup S → Prop) (s : S) :
    Word r := wordMk r (FreeAddGroup.of s)

theorem wordEq {S : Type*} {r : FreeAddGroup S → FreeAddGroup S → Prop}
    {p q : FreeAddGroup S} (h : r p q) : wordMk r p = wordMk r q :=
  (AddCon.eq (addConGen r)).2 (AddConGen.Rel.of p q h)

def wordLift {S Y : Type*} [AddGroup Y] {r : FreeAddGroup S → FreeAddGroup S → Prop}
    (f : S → Y) (hf : ∀ p q, r p q → FreeAddGroup.lift f p = FreeAddGroup.lift f q) :
    Word r →+ Y :=
  (addConGen r).lift (FreeAddGroup.lift f)
    (AddCon.addConGen_le.mpr fun p q hpq => (AddCon.ker_rel _).2 (hf p q hpq))

theorem wordLift_gen {S Y : Type*} [AddGroup Y]
    {r : FreeAddGroup S → FreeAddGroup S → Prop} (f : S → Y) (hf) (s : S) :
    wordLift (r := r) f hf (wordGen r s) = f s :=
  FreeAddGroup.lift_apply_of

theorem wordExt {S Y : Type*} [AddGroup Y] {r : FreeAddGroup S → FreeAddGroup S → Prop}
    (f g : Word r →+ Y) (h : ∀ s, f (wordGen r s) = g (wordGen r s)) : f = g := by
  have hfg : f.comp (wordMk r) = g.comp (wordMk r) := by
    apply FreeAddGroup.lift.symm.injective
    exact funext h
  ext x
  exact AddCon.induction_on x (fun p => DFunLike.congr_fun hfg p)

section Tensor

variable {A : Type u} [Ring A]
variable {M : Type w} [AddCommGroup M]
variable {X : Type j} [AddCommGroup X] [Module A X]

def tensorRel (right : A → M → M) (X : Type j) [AddCommGroup X] [Module A X]
    (p q : FreeAddGroup (M × X)) : Prop :=
  let gen := fun m x => FreeAddGroup.of (m, x)
  (∃ a b : FreeAddGroup (M × X), p = a + b ∧ q = b + a) ∨
  (∃ (m m' : M) (x : X), p = gen (m + m') x ∧ q = gen m x + gen m' x) ∨
  (∃ (m : M) (x x' : X), p = gen m (x + x') ∧ q = gen m x + gen m x') ∨
  (∃ (a : A) (m : M) (x : X), p = gen (right a m) x ∧ q = gen m (a • x))

abbrev Tensor (right : A → M → M) (X : Type j) [AddCommGroup X] [Module A X] :=
  Word (tensorRel right X)

variable (right : A → M → M)

@[instance_reducible] def tensorAddCommGroup : AddCommGroup (Tensor right X) :=
  { AddCon.addGroup (addConGen (tensorRel right X)) with
    add_comm := fun p q =>
      AddCon.induction_on₂ p q fun a b =>
        (AddCon.eq (addConGen (tensorRel right X))).2
          (AddConGen.Rel.of (a + b) (b + a) (Or.inl ⟨a, b, rfl, rfl⟩)) }

attribute [local instance] tensorAddCommGroup

abbrev pure (m : M) (x : X) : Tensor right X := wordGen (tensorRel right X) (m, x)

def Balanced {Y : Type*} [AddCommGroup Y] (f : M → X → Y) : Prop :=
  (∀ m m' x, f (m + m') x = f m x + f m' x) ∧
  (∀ m x x', f m (x + x') = f m x + f m x') ∧
  (∀ a m x, f (right a m) x = f m (a • x))

theorem pureBalanced : Balanced right (pure (X := X) right) :=
  ⟨fun m m' x => wordEq (Or.inr (Or.inl ⟨m, m', x, rfl, rfl⟩)),
   fun m x x' => wordEq (Or.inr (Or.inr (Or.inl ⟨m, x, x', rfl, rfl⟩))),
   fun a m x => wordEq (Or.inr (Or.inr (Or.inr ⟨a, m, x, rfl, rfl⟩)))⟩

def tensorLift {Y : Type*} [AddCommGroup Y] (f : M → X → Y) (hf : Balanced right f) :
    Tensor right X →+ Y :=
  wordLift (fun p => f p.1 p.2) fun p q h => by
    rcases h with ⟨a, b, rfl, rfl⟩ | ⟨m, m', x, rfl, rfl⟩ |
      ⟨m, x, x', rfl, rfl⟩ | ⟨a, m, x, rfl, rfl⟩
    · simp only [map_add, add_comm]
    · simpa only [map_add, FreeAddGroup.lift_apply_of] using hf.1 m m' x
    · simpa only [map_add, FreeAddGroup.lift_apply_of] using hf.2.1 m x x'
    · simpa only [FreeAddGroup.lift_apply_of] using hf.2.2 a m x

theorem tensorLift_pure {Y : Type*} [AddCommGroup Y] (f : M → X → Y)
    (hf : Balanced right f) (m : M) (x : X) :
    tensorLift right f hf (pure right m x) = f m x :=
  wordLift_gen _ _ _

theorem tensorExt {Y : Type*} [AddCommGroup Y] (f g : Tensor right X →+ Y)
    (h : ∀ m x, f (pure right m x) = g (pure right m x)) : f = g :=
  wordExt f g (fun p => h p.1 p.2)

variable {B : Type v} [Ring B] [Module B M]

def scale (commute : ∀ (a : A) (b : B) (m : M), right a (b • m) = b • right a m)
    (b : B) : Tensor right X →+ Tensor right X :=
  tensorLift right (fun m x => pure right (b • m) x)
    ⟨fun m m' x => by
       change pure right (b • (m + m')) x = pure right (b • m) x + pure right (b • m') x
       rw [smul_add, (pureBalanced right).1],
     fun m x x' => (pureBalanced right).2.1 (b • m) x x',
     fun a m x => by
       change pure right (b • right a m) x = pure right (b • m) (a • x)
       rw [← commute, (pureBalanced right).2.2]⟩

theorem scale_pure (commute : ∀ (a : A) (b : B) (m : M), right a (b • m) = b • right a m)
    (b : B) (m : M) (x : X) :
    scale right commute b (pure right m x) = pure right (b • m) x :=
  tensorLift_pure _ _ _ _ _

@[instance_reducible] def outerModule
    (commute : ∀ (a : A) (b : B) (m : M), right a (b • m) = b • right a m) :
    Module B (Tensor right X) where
  smul b t := scale right commute b t
  one_smul t :=
    DFunLike.congr_fun (tensorExt right (scale right commute 1) (AddMonoidHom.id _) (fun m x => by
      simp only [scale_pure, one_smul, AddMonoidHom.id_apply])) t
  mul_smul b c t :=
    DFunLike.congr_fun (tensorExt right (scale right commute (b * c)) ((scale right commute b).comp (scale right commute c))
      (fun m x => by simp only [scale_pure, AddMonoidHom.comp_apply, mul_smul])) t
  smul_zero b := map_zero (scale right commute b)
  smul_add b t t' := map_add (scale right commute b) t t'
  add_smul b c t :=
    DFunLike.congr_fun (tensorExt right (scale right commute (b + c)) (scale right commute b + scale right commute c)
      (fun m x => by
        simp only [scale_pure, AddMonoidHom.add_apply, add_smul, (pureBalanced right).1])) t
  zero_smul t :=
    DFunLike.congr_fun (tensorExt right (scale right commute 0) 0 (fun m x => by
      simp only [scale_pure, zero_smul, AddMonoidHom.zero_apply]
      have hzero := (pureBalanced right).1 (0 : M) 0 x
      rw [zero_add] at hzero
      apply add_left_cancel (a := pure right (0 : M) x)
      rw [add_zero, ← hzero])) t

variable (commute : ∀ (a : A) (b : B) (m : M), right a (b • m) = b • right a m)


def tensorLinearLift {Y : Type*} [AddCommGroup Y] [Module B Y] (f : M → X → Y)
    (hf : Balanced right f) (hB : ∀ (b : B) m x, f (b • m) x = b • f m x) :
    @LinearMap B B _ _ (RingHom.id B) (Tensor right X) Y _ _ (outerModule right commute) _ :=
  letI := outerModule (X := X) right commute
  { tensorLift right f hf with
    map_smul' := fun b t => by
      change tensorLift right f hf (scale right commute b t) = b • tensorLift right f hf t
      exact DFunLike.congr_fun (tensorExt right
        ((tensorLift right f hf).comp (scale right commute b))
        ((DistribSMul.toAddMonoidHom Y b).comp (tensorLift right f hf))
        (fun m x => by
          simp only [AddMonoidHom.comp_apply, scale_pure, tensorLift_pure,
            DistribSMul.toAddMonoidHom_apply]
          exact hB b m x)) t }

theorem tensorLinearLift_pure {Y : Type*} [AddCommGroup Y] [Module B Y] (f : M → X → Y)
    (hf : Balanced right f) (hB : ∀ (b : B) m x, f (b • m) x = b • f m x)
    (m : M) (x : X) :
    tensorLinearLift right commute f hf hB (pure right m x) = f m x :=
  tensorLift_pure right f hf m x

end Tensor


section Comparison

variable {A : Type u} {B : Type v} [Ring A] [Ring B]

abbrev regular (A : Type u) [Ring A] := ModuleCat.of A (ULift.{z} A)

variable (F : ModuleCat.{max u z} A ⥤ ModuleCat.{w} B) [F.Additive]

abbrev M := F.obj (regular.{u,z} A)

def right (a : A) : M F →ₗ[B] M F :=
  (F.map (ModuleCat.ofHom (LinearEquiv.conjRingEquiv
    ((ULift.moduleEquiv : ULift.{z} A ≃ₗ[A] A).symm) (LinearMap.mulRight A a)))).hom

-- Use the registered supplier with the identical lifted regular module and
-- right multiplication. Its existential bimodule is eliminated into Prop.
theorem rightCommute (a : A) (b : B) (m : M F) :
    right F a (b • m) = b • right F a m := by
  obtain ⟨⟨left, rightModule, comm⟩, hleft, hright⟩ := RegularModuleRightAction.{u,v,z,w} A B F
  dsimp only at hleft
  subst left
  have h := comm.smul_comm (MulOpposite.op a) b m
  exact (hright a (b • m)).symm.trans (h.trans (congrArg (fun x : M F => b • x) (hright a m)))

def ell (X : ModuleCat.{max u z} A) (x : X) : regular.{u,z} A ⟶ X :=
  ModuleCat.ofHom (LinearMap.smulRight (ULift.moduleEquiv : ULift.{z} A ≃ₗ[A] A).toLinearMap x)

theorem ell_apply (X : ModuleCat.{max u z} A) (x : X) (r : ULift.{z} A) :
    (ell X x).hom r = r.down • x := rfl

def beta (X : ModuleCat.{max u z} A) (m : M F) (x : X) : F.obj X :=
  (F.map (ell X x)).hom m

theorem ell_add (X : ModuleCat.{max u z} A) (x y : X) :
    ell X (x + y) = ell X x + ell X y := by
  apply ModuleCat.hom_ext
  ext r
  exact smul_add r.down x y

theorem ell_balance (X : ModuleCat.{max u z} A) (a : A) (x : X) :
    (ModuleCat.ofHom (LinearEquiv.conjRingEquiv
      ((ULift.moduleEquiv : ULift.{z} A ≃ₗ[A] A).symm) (LinearMap.mulRight A a))) ≫ ell X x =
      ell X (a • x) := by
  apply ModuleCat.hom_ext
  ext r
  exact mul_smul r.down a x

theorem ell_comp {X Y : ModuleCat.{max u z} A} (f : X ⟶ Y) (x : X) :
    ell X x ≫ f = ell Y (f.hom x) := by
  apply ModuleCat.hom_ext
  ext r
  exact f.hom.map_smul r.down x

theorem beta_balanced (X : ModuleCat.{max u z} A) :
    Balanced (fun a m => right F a m) (beta F X) := by
  refine ⟨fun m n x => (F.map (ell X x)).hom.map_add m n, ?_, ?_⟩
  · intro m x y
    unfold beta
    rw [ell_add, F.map_add]
    rfl
  · intro a m x
    unfold beta right
    rw [← ell_balance X a x, F.map_comp]
    rfl

def tensorObj (X : ModuleCat.{max u z} A) : ModuleCat.{max u z w} B :=
  let rightAction := fun a m => right F a m
  @ModuleCat.of B _ (Tensor rightAction X) (tensorAddCommGroup rightAction)
    (outerModule rightAction (rightCommute F))

def comparison (X : ModuleCat.{max u z} A) : tensorObj F X →ₗ[B] F.obj X :=
  tensorLinearLift _ (rightCommute F) (beta F X) (beta_balanced F X)
    (fun b m x => (F.map (ell X x)).hom.map_smul b m)

theorem comparison_pure (X : ModuleCat.{max u z} A) (m : M F) (x : X) :
    comparison F X (pure (fun a m => right F a m) m x) = beta F X m x :=
  tensorLinearLift_pure _ _ _ _ _ _ _

def regularInverse : M F →ₗ[B] tensorObj F (regular.{u,z} A) where
  toFun m := pure (fun a m => right F a m) m ⟨1⟩
  map_add' m n := (pureBalanced (fun a m => right F a m)).1 m n (⟨1⟩ : ULift.{z} A)
  map_smul' b m := by
    change pure _ (b • m) (⟨1⟩ : ULift.{z} A) =
      scale _ (rightCommute F) b (pure _ m (⟨1⟩ : ULift.{z} A))
    exact (scale_pure _ (rightCommute F) b m (⟨1⟩ : ULift.{z} A)).symm

theorem comparison_regular_right :
    (comparison F (regular.{u,z} A)).comp (regularInverse F) = LinearMap.id := by
  suffices h : ell (regular.{u,z} A) (⟨1⟩ : ULift.{z} A) = 𝟙 _ by
    apply LinearMap.ext
    intro m
    change comparison F _ (pure _ m (⟨1⟩ : ULift.{z} A)) = m
    rw [comparison_pure, beta, h, F.map_id, ModuleCat.hom_id, LinearMap.id_apply]
  apply ModuleCat.hom_ext
  ext r
  change (r.down • (⟨1⟩ : ULift.{z} A)).down = r.down
  exact mul_one r.down

theorem comparison_regular_left :
    (regularInverse F).comp (comparison F (regular.{u,z} A)) = LinearMap.id := by
  apply LinearMap.toAddMonoidHom_injective
  apply tensorExt (fun a m => right F a m)
  intro m (x : ULift.{z} A)
  have h : ell (regular.{u,z} A) x =
      ModuleCat.ofHom (LinearEquiv.conjRingEquiv
        ((ULift.moduleEquiv : ULift.{z} A ≃ₗ[A] A).symm) (LinearMap.mulRight A x.down)) := by
    apply ModuleCat.hom_ext
    rfl
  change regularInverse F (comparison F _ (pure _ m x)) = pure _ m x
  rw [comparison_pure, beta, h]
  change pure (fun a m => right F a m) (right F x.down m) (⟨1⟩ : ULift.{z} A) = pure _ m x
  rw [(pureBalanced (X := ULift.{z} A) (fun a m => right F a m)).2.2]
  congr 1
  apply ULift.ext
  exact mul_one x.down

-- Steps 1.2 and 2.2 use the canonical comparison on the specified
-- generators. Generator extensionality proves the identities in this model.
def tensorMap {X Y : ModuleCat.{max u z} A} (f : X ⟶ Y) : tensorObj F X ⟶ tensorObj F Y :=
  @ModuleCat.ofHom B _ (tensorObj F X) (tensorObj F Y) _ _ _ _ (tensorLinearLift _ (rightCommute F)
    (fun m x => pure (fun a m => right F a m) m (f.hom x))
    ⟨fun m n x => (pureBalanced _).1 m n (f.hom x),
     fun m x x' => by
       change pure (fun a m => right F a m) m (f.hom (x + x')) = _
       rw [map_add, (pureBalanced (fun a m => right F a m)).2.1]
       rfl,
     fun a m x => by
       change pure (fun a m => right F a m) (right F a m) (f.hom x) =
         pure (fun a m => right F a m) m (f.hom (a • x))
       rw [(pureBalanced (fun a m => right F a m)).2.2, f.hom.map_smul]⟩
    (fun b m x => (scale_pure _ (rightCommute F) b m (f.hom x)).symm))

theorem tensorMap_pure {X Y : ModuleCat.{max u z} A} (f : X ⟶ Y) (m : M F) (x : X) :
    (tensorMap F f).hom (pure (fun a m => right F a m) m x) =
      pure (fun a m => right F a m) m (f.hom x) :=
  tensorLinearLift_pure _ _ _ _ (fun b m x => (scale_pure _ (rightCommute F) b m (f.hom x)).symm) _ _

theorem tensorMap_id (X : ModuleCat.{max u z} A) :
    tensorMap F (𝟙 X) = 𝟙 (tensorObj F X) := by
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply tensorExt (fun a m => right F a m)
  intro m x
  exact tensorMap_pure F (𝟙 X) m x

theorem tensorMap_comp {X Y Z : ModuleCat.{max u z} A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    tensorMap F (f ≫ g) = tensorMap F f ≫ tensorMap F g := by
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply tensorExt (fun a m => right F a m)
  intro m x
  change (tensorMap F (f ≫ g)).hom (pure _ m x) =
    (tensorMap F g).hom ((tensorMap F f).hom (pure _ m x))
  rw [tensorMap_pure, tensorMap_pure, tensorMap_pure]
  rfl

def tensorFunctor : ModuleCat.{max u z} A ⥤ ModuleCat.{max u z w} B where
  obj := tensorObj F
  map := tensorMap F
  map_id := tensorMap_id F
  map_comp := tensorMap_comp F

theorem comparison_naturality {X Y : ModuleCat.{max u z} A} (f : X ⟶ Y) :
    (comparison F Y).comp (tensorMap F f).hom = (F.map f).hom.comp (comparison F X) := by
  apply LinearMap.toAddMonoidHom_injective
  apply tensorExt (fun a m => right F a m)
  intro m x
  change comparison F Y ((tensorMap F f).hom (pure _ m x)) =
    (F.map f).hom (comparison F X (pure _ m x))
  rw [tensorMap_pure, comparison_pure, comparison_pure, beta, beta,
    ← ell_comp f x, F.map_comp]
  rfl

def liftedF : ModuleCat.{max u z} A ⥤ ModuleCat.{max u z w} B where
  obj X := (ModuleCat.uliftFunctor.{max u z, w} B).obj (F.obj X)
  map f := (ModuleCat.uliftFunctor.{max u z, w} B).map (F.map f)
  map_id X :=
    (congrArg (fun f => (ModuleCat.uliftFunctor.{max u z, w} B).map f) (F.map_id X)).trans
      ((ModuleCat.uliftFunctor.{max u z, w} B).map_id (F.obj X))
  map_comp f g :=
    (congrArg (fun f => (ModuleCat.uliftFunctor.{max u z, w} B).map f) (F.map_comp f g)).trans
      ((ModuleCat.uliftFunctor.{max u z, w} B).map_comp (F.map f) (F.map g))

def tau : NatTrans (tensorFunctor F) (liftedF F) where
  app X := @ModuleCat.ofHom B _ (tensorObj F X) (ULift.{max u z} (F.obj X)) _ _ _ _
    ((ULift.moduleEquiv : ULift.{max u z} (F.obj X) ≃ₗ[B] F.obj X).symm.toLinearMap.comp
      (comparison F X))
  naturality {X Y} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    apply ULift.ext
    exact DFunLike.congr_fun (comparison_naturality F f) t


end Comparison
section Coproduct

variable {R : Type u} [Ring R] {I : Type j} (D : I → ModuleCat.{z} R)

def sumRel (p q : FreeAddGroup (Sigma fun i => (D i : Type z))) : Prop :=
  let gen := fun (i : I) (x : D i) => FreeAddGroup.of (⟨i, x⟩ : Sigma fun i => (D i : Type z))
  (∃ a b, p = a + b ∧ q = b + a) ∨
  (∃ (i : I) (x y : D i), p = gen i (x + y) ∧ q = gen i x + gen i y)

abbrev Sum := Word (sumRel D)

@[instance_reducible] def sumAddCommGroup : AddCommGroup (Sum D) :=
  { AddCon.addGroup (addConGen (sumRel D)) with
    add_comm := fun p q =>
      AddCon.induction_on₂ p q fun a b =>
        (AddCon.eq (addConGen (sumRel D))).2
          (AddConGen.Rel.of (a + b) (b + a) (Or.inl ⟨a, b, rfl, rfl⟩)) }

attribute [local instance] sumAddCommGroup

abbrev summand (i : I) (x : D i) : Sum D := wordGen (sumRel D) ⟨i, x⟩

theorem summand_add (i : I) (x y : D i) :
    summand D i (x + y) = summand D i x + summand D i y :=
  wordEq (Or.inr ⟨i, x, y, rfl, rfl⟩)

def sumAddLift {Y : Type*} [AddCommGroup Y] (f : ∀ i, D i →+ Y) : Sum D →+ Y :=
  wordLift (fun p => f p.1 p.2) fun _ _ h => by
    rcases h with ⟨a, b, rfl, rfl⟩ | ⟨i, x, y, rfl, rfl⟩
    · simp only [map_add, add_comm]
    · simp only [map_add, FreeAddGroup.lift_apply_of]

theorem sumAddLift_summand {Y : Type*} [AddCommGroup Y] (f : ∀ i, D i →+ Y)
    (i : I) (x : D i) : sumAddLift D f (summand D i x) = f i x :=
  wordLift_gen _ _ _

def sumScale (r : R) : Sum D →+ Sum D :=
  sumAddLift D fun i =>
    { toFun := fun x => summand D i (r • x)
      map_add' := fun x y => by
        change summand D i (r • (x + y)) = summand D i (r • x) + summand D i (r • y)
        rw [smul_add, summand_add]
      map_zero' := by
        change summand D i (r • 0) = 0
        rw [smul_zero]
        have h := summand_add D i 0 0
        rw [zero_add] at h
        apply add_left_cancel (a := summand D i 0)
        rw [add_zero, ← h] }

theorem sumScale_summand (r : R) (i : I) (x : D i) :
    sumScale D r (summand D i x) = summand D i (r • x) :=
  sumAddLift_summand D _ i x

theorem sumExt {Y : Type*} [AddCommGroup Y] (f g : Sum D →+ Y)
    (h : ∀ i x, f (summand D i x) = g (summand D i x)) : f = g :=
  wordExt f g fun p => h p.1 p.2

@[instance_reducible] def sumModule : Module R (Sum D) where
  smul r x := sumScale D r x
  one_smul x :=
    DFunLike.congr_fun (sumExt D (sumScale D 1) (AddMonoidHom.id _) (fun i t => by
      simp only [sumScale_summand, one_smul, AddMonoidHom.id_apply])) x
  mul_smul r s x :=
    DFunLike.congr_fun (sumExt D (sumScale D (r * s)) ((sumScale D r).comp (sumScale D s))
      (fun i t => by simp only [sumScale_summand, AddMonoidHom.comp_apply, mul_smul])) x
  smul_zero r := map_zero (sumScale D r)
  smul_add r x y := map_add (sumScale D r) x y
  add_smul r s x :=
    DFunLike.congr_fun (sumExt D (sumScale D (r + s)) (sumScale D r + sumScale D s)
      (fun i t => by
        simp only [sumScale_summand, AddMonoidHom.add_apply, add_smul, summand_add])) x
  zero_smul x :=
    DFunLike.congr_fun (sumExt D (sumScale D 0) 0 (fun i x => by
      simp only [sumScale_summand, zero_smul, AddMonoidHom.zero_apply]
      have h := summand_add D i 0 0
      rw [zero_add] at h
      apply add_left_cancel (a := summand D i 0)
      rw [add_zero, ← h])) x

def sumObj : ModuleCat.{max j z} R := @ModuleCat.of R _ (Sum D) (sumAddCommGroup D) (sumModule D)

def sumIncl (i : I) : D i →ₗ[R] sumObj D where
  toFun := summand D i
  map_add' := summand_add D i
  map_smul' r x := (sumScale_summand D r i x).symm

def sumLift {Y : Type*} [AddCommGroup Y] [Module R Y] (f : ∀ i, D i →ₗ[R] Y) :
    sumObj D →ₗ[R] Y :=
  { sumAddLift D (fun i => (f i).toAddMonoidHom) with
    map_smul' := fun r t => by
      change sumAddLift D (fun i => (f i).toAddMonoidHom) (sumScale D r t) =
        r • sumAddLift D (fun i => (f i).toAddMonoidHom) t
      exact DFunLike.congr_fun
        (sumExt D ((sumAddLift D fun i => (f i).toAddMonoidHom).comp (sumScale D r))
          ((DistribSMul.toAddMonoidHom Y r).comp (sumAddLift D fun i => (f i).toAddMonoidHom))
          (fun i x => by
            simp only [AddMonoidHom.comp_apply, sumScale_summand, sumAddLift_summand,
              DistribSMul.toAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe, LinearMap.map_smul]))
        t }

theorem sumLift_summand {Y : Type*} [AddCommGroup Y] [Module R Y] (f : ∀ i, D i →ₗ[R] Y)
    (i : I) (x : D i) : sumLift D f (summand D i x) = f i x :=
  sumAddLift_summand D (fun i => (f i).toAddMonoidHom) i x

end Coproduct

section Presentation

variable {A : Type u} [Ring A]

def freeObj (I : Type (max u z)) : ModuleCat.{max u z} A :=
  sumObj (fun _ : I => regular.{u,z} A)

def freeIncl (I : Type (max u z)) (i : I) : regular.{u,z} A ⟶ freeObj (A := A) I :=
  @ModuleCat.ofHom A _ (regular.{u,z} A) (freeObj (A := A) I) _ _ _ _
    (sumIncl (fun _ : I => regular.{u,z} A) i)

def freeDesc {I : Type (max u z)} {X : ModuleCat.{max u z} A} (f : I → X) :
    freeObj I ⟶ X :=
  @ModuleCat.ofHom A _ (freeObj (A := A) I) X _ _ _ _
    (sumLift (fun _ : I => regular.{u,z} A) fun i => (ell X (f i)).hom)

theorem freeDesc_gen {I : Type (max u z)} {X : ModuleCat.{max u z} A} (f : I → X)
    (i : I) : (freeDesc f).hom ((freeIncl I i).hom (⟨1⟩ : ULift.{z} A)) = f i := by
  change sumLift (fun _ : I => regular.{u,z} A) (fun i => (ell X (f i)).hom)
    (summand (fun _ : I => regular.{u,z} A) i ⟨1⟩) = f i
  rw [sumLift_summand, ell_apply]
  exact one_smul A (f i)

theorem freeCoproduct (I : Type (max u z)) (Q : ModuleCat.{max u z} A)
    (legs : I → (regular.{u,z} A ⟶ Q)) :
    ∃! d : freeObj I ⟶ Q, ∀ i, freeIncl I i ≫ d = legs i := by
  let L := fun i => (legs i).hom
  let d : freeObj I ⟶ Q := @ModuleCat.ofHom A _ (freeObj (A := A) I) Q _ _ _ _
    (sumLift (fun _ : I => regular.{u,z} A) L)
  have hd (i : I) : freeIncl I i ≫ d = legs i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact fun a => sumLift_summand (fun _ : I => regular.{u,z} A) L i a
  refine ⟨d, hd, ?_⟩
  intro e he
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply sumExt (fun _ : I => regular.{u,z} A)
  intro i (a : ULift.{z} A)
  exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ((he i).trans (hd i).symm)) a

-- Step 1.3 uses the whole carrier of X and then the whole carrier of
-- the kernel. The word presentation avoids the choice dependency in
-- ModuleCat.freeDesc, including for an index type without decidable equality.
def cover (X : ModuleCat.{max u z} A) : freeObj (A := A) X ⟶ X := freeDesc id

def Relations (X : ModuleCat.{max u z} A) : Type (max u z) :=
  {p : freeObj (A := A) X // (cover X).hom p = 0}

def relationsMap (X : ModuleCat.{max u z} A) : freeObj (A := A) (Relations X) ⟶ freeObj X :=
  freeDesc (fun i : Relations X => (i : {p : freeObj (A := A) X // (cover X).hom p = 0}).val)

def sectionOnGenerators (X : ModuleCat.{max u z} A) (x : X) : freeObj (A := A) X :=
  (freeIncl X x).hom (⟨1⟩ : ULift.{z} A)

theorem cover_section (X : ModuleCat.{max u z} A) (x : X) :
    (cover X).hom (sectionOnGenerators X x) = x := freeDesc_gen id x

theorem relations_zero (X : ModuleCat.{max u z} A) :
    relationsMap X ≫ cover X = @ModuleCat.ofHom A _ (freeObj (A := A) (Relations X)) X _ _ _ _ 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply sumExt (fun _ : Relations X => regular.{u,z} A)
  intro i (a : ULift.{z} A)
  change (cover X).hom ((relationsMap X).hom (summand (fun _ : Relations X => regular.{u,z} A) i a)) = 0
  have hi : (cover X).hom i.val = 0 := i.property
  change (cover X).hom
    (sumLift (fun _ : Relations X => regular.{u,z} A) (fun i => (ell (freeObj X) i.val).hom)
      (summand (fun _ : Relations X => regular.{u,z} A) i a)) = 0
  rw [sumLift_summand, ell_apply, LinearMap.map_smul, hi, smul_zero]

theorem cover_cokernel (X Z : ModuleCat.{max u z} A) (g : freeObj (A := A) X ⟶ Z)
    (hg : relationsMap X ≫ g = @ModuleCat.ofHom A _ (freeObj (A := A) (Relations X)) Z _ _ _ _ 0) :
    ∃! d : X ⟶ Z, cover X ≫ d = g := by
  let s := sectionOnGenerators X
  have equal (p p' : freeObj (A := A) X) (h : (cover X).hom p = (cover X).hom p') :
      g.hom p = g.hom p' := by
    let k : Relations X := ⟨p - p', by
      apply add_right_cancel (b := (cover X).hom p')
      rw [← map_add, sub_add_cancel, zero_add, h]⟩
    have hk := freeDesc_gen (X := freeObj X) (fun i : Relations X => i.val) k
    change (relationsMap X).hom ((freeIncl (Relations X) k).hom (⟨1⟩ : ULift.{z} A)) =
      p - p' at hk
    have kill : g.hom (p - p') = 0 :=
      (congrArg g.hom hk).symm.trans
        (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hg)
          ((freeIncl (Relations X) k).hom (⟨1⟩ : ULift.{z} A)))
    calc
      g.hom p = g.hom (p - p' + p') := congrArg g.hom (sub_add_cancel p p').symm
      _ = g.hom p' := by rw [map_add, kill, zero_add]
  let d : X ⟶ Z := ModuleCat.ofHom
    { toFun := fun x => g.hom (s x)
      map_add' := fun x y => by
        change g.hom (s (x + y)) = g.hom (s x) + g.hom (s y)
        rw [← map_add]
        apply equal
        rw [cover_section, map_add, cover_section, cover_section]
      map_smul' := fun a x => by
        change g.hom (s (a • x)) = a • g.hom (s x)
        rw [← LinearMap.map_smul]
        apply equal
        rw [cover_section, LinearMap.map_smul, cover_section] }
  have hd : cover X ≫ d = g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    change g.hom (s ((cover X).hom p)) = g.hom p
    exact equal _ _ (cover_section X _)
  refine ⟨d, hd, ?_⟩
  intro e he
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (he.trans hd.symm)) (s x)
  change e.hom ((cover X).hom (s x)) = d.hom ((cover X).hom (s x)) at h
  rwa [cover_section] at h

end Presentation

def explicitRange {B S T : Type*} [Ring B] [AddCommGroup S] [Module B S]
    [AddCommGroup T] [Module B T] (f : S →ₗ[B] T) : Submodule B T where
  carrier := { t | ∃ s, f s = t }
  zero_mem' := ⟨0, map_zero f⟩
  add_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, map_add f s t⟩
  smul_mem' := by
    rintro b _ ⟨s, rfl⟩
    exact ⟨b • s, f.map_smul b s⟩

section

variable {B : Type v} [Ring B]
variable {I : Type j} {D : I → ModuleCat.{w} B} {P : ModuleCat.{w} B}

/-- Step 2.1 with the target universe from the reviewed hypothesis. Applying
its uniqueness to the image detects joint surjectivity, without using an
inverse or resizing the full tensor carrier into the target universe. -/
theorem surjectiveOfPreservedCoproduct (ι : ∀ i, D i ⟶ P)
    (coprod : ∀ (Q : ModuleCat.{w} B) (legs : ∀ i, D i ⟶ Q),
      ∃! d : P ⟶ Q, ∀ i, ι i ≫ d = legs i)
    {T : Type*} [AddCommGroup T] [Module B T] (τ : T →ₗ[B] P)
    (legs : ∀ i, D i →ₗ[B] T) (hlegs : ∀ i, τ.comp (legs i) = (ι i).hom) :
    Function.Surjective τ := by
  let Q := ModuleCat.of B (explicitRange τ)
  let inc : Q ⟶ P := ModuleCat.ofHom (explicitRange τ).subtype
  let lifts (i : I) : D i ⟶ Q :=
    ModuleCat.ofHom ((ι i).hom.codRestrict (explicitRange τ) fun d =>
      ⟨legs i d, DFunLike.congr_fun (hlegs i) d⟩)
  have lifts_inc (i : I) : lifts i ≫ inc = ι i := by
    apply ModuleCat.hom_ext
    rfl
  obtain ⟨k, hk, _⟩ := coprod Q lifts
  obtain ⟨l, _, hl⟩ := coprod P ι
  have equal : k ≫ inc = 𝟙 P := by
    apply (hl (k ≫ inc) ?_).trans (hl (𝟙 P) ?_).symm
    · intro i
      rw [← Category.assoc, hk i, lifts_inc]
    · intro i
      exact Category.comp_id (ι i)
  intro p
  have hp : ((k.hom p : Q) : P) = p := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom equal) p
  exact hp ▸ (k.hom p).property

end

section

variable {B : Type v} [Ring B]
variable {L P X : ModuleCat.{w} B}

/-- The range of the preserved cokernel map lies in the tested target
universe. Cokernel uniqueness in Step 2.2 implies surjectivity by
factorization through this range. -/
theorem cokernelSurjective (f : L ⟶ P) (q : P ⟶ X)
    (zero : f ≫ q = ModuleCat.ofHom 0)
    (cokern : ∀ (Z : ModuleCat.{w} B) (g : P ⟶ Z),
      f ≫ g = ModuleCat.ofHom 0 → ∃! d : X ⟶ Z, q ≫ d = g) :
    Function.Surjective q.hom := by
  let Q := ModuleCat.of B (explicitRange q.hom)
  let inc : Q ⟶ X := ModuleCat.ofHom (explicitRange q.hom).subtype
  let π : P ⟶ Q := ModuleCat.ofHom (q.hom.codRestrict (explicitRange q.hom) fun x => ⟨x, rfl⟩)
  have hinc : π ≫ inc = q := by
    apply ModuleCat.hom_ext
    rfl
  have hπ : f ≫ π = ModuleCat.ofHom 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom zero) p
  obtain ⟨back, hback, _⟩ := cokern Q π hπ
  obtain ⟨d, _, hd⟩ := cokern X q zero
  have hinv : back ≫ inc = 𝟙 X := by
    apply (hd (back ≫ inc) ?_).trans (hd (𝟙 X) (Category.comp_id q)).symm
    rw [← Category.assoc, hback, hinc]
  intro x
  have hx : ((back.hom x : Q) : X) = x :=
    DFunLike.congr_fun (congrArg ModuleCat.Hom.hom hinv) x
  exact hx ▸ (back.hom x).property

end

section Integrate

variable {A : Type u} {B : Type v} [Ring A] [Ring B]
variable (F : ModuleCat.{max u z} A ⥤ ModuleCat.{w} B) [F.Additive]

-- Steps 1.2 and 2.1 apply the actual small-target preservation
-- hypothesis to the canonical free module. The image detects
-- surjectivity in Type w, even though the full tensor is larger.
theorem comparison_free_surjective (I : Type (max u z))
    (hcoprod : ∀ (Q : ModuleCat.{w} B) (legs : ∀ _ : I, M F ⟶ Q),
      ∃! d : F.obj (freeObj (A := A) I) ⟶ Q,
        ∀ i, F.map (freeIncl I i) ≫ d = legs i) :
    Function.Surjective (comparison F (freeObj (A := A) I)) := by
  let leg (i : I) : M F →ₗ[B] tensorObj F (freeObj (A := A) I) :=
    (tensorMap F (freeIncl I i)).hom.comp (regularInverse F)
  apply surjectiveOfPreservedCoproduct (D := fun _ : I => M F)
    (fun i => F.map (freeIncl I i)) hcoprod _ leg
  intro i
  change (comparison F _).comp
    ((tensorMap F (freeIncl I i)).hom.comp (regularInverse F)) =
      (F.map (freeIncl I i)).hom
  rw [← LinearMap.comp_assoc, comparison_naturality, LinearMap.comp_assoc,
    comparison_regular_right, LinearMap.comp_id]

-- Steps 2.2–3.1. The source presentation is an actual cokernel. The
-- small-target image argument can be applied to F of that presentation.
-- This yields a preimage in Prop. Step 4.1 still needs one inverse family
-- as data for the NatTrans, and these eliminations do not supply it.
theorem comparison_surjective
    (hcokern :
      ∀ (L P X : ModuleCat.{max u z} A) (f : L ⟶ P) (q : P ⟶ X),
      f ≫ q = ModuleCat.ofHom 0 →
      (∀ (Z : ModuleCat.{max u z} A) (g : P ⟶ Z),
        f ≫ g = ModuleCat.ofHom 0 → ∃! d : X ⟶ Z, q ≫ d = g) →
      F.map f ≫ F.map q = ModuleCat.ofHom 0 ∧
      ∀ (Z : ModuleCat.{w} B) (g : F.obj P ⟶ Z),
        F.map f ≫ g = ModuleCat.ofHom 0 → ∃! d : F.obj X ⟶ Z, F.map q ≫ d = g)
    (hcoprod :
      ∀ (I : Type (max u z)) (D : I → ModuleCat.{max u z} A) (P : ModuleCat.{max u z} A)
        (ι : ∀ i, D i ⟶ P),
      (∀ (Q : ModuleCat.{max u z} A) (legs : ∀ i, D i ⟶ Q),
        ∃! d : P ⟶ Q, ∀ i, ι i ≫ d = legs i) →
      ∀ (Q : ModuleCat.{w} B) (legs : ∀ i, F.obj (D i) ⟶ Q),
        ∃! d : F.obj P ⟶ Q, ∀ i, F.map (ι i) ≫ d = legs i)
    (X : ModuleCat.{max u z} A) : Function.Surjective (comparison F X) := by
  have hk := hcokern _ _ _ (relationsMap X) (cover X) (relations_zero X) (cover_cokernel X)
  have hq := cokernelSurjective _ _ hk.1 hk.2
  have hp := comparison_free_surjective F X
    (hcoprod X (fun _ => regular.{u,z} A) (freeObj X) (freeIncl X) (freeCoproduct X))
  intro y
  obtain ⟨x, rfl⟩ := hq y
  obtain ⟨t, rfl⟩ := hp x
  exact ⟨(tensorMap F (cover X)).hom t, DFunLike.congr_fun (comparison_naturality F (cover X)) t⟩

end Integrate

-- The portal's Step 4.1 concludes a natural isomorphism from componentwise
-- isomorphisms and states that no choice is needed. The analogous direct
-- Lean construction from a pointwise ExistsUnique of inverses is rejected:
-- Exists.casesOn can only eliminate into Prop, and app X must be a morphism.
-- This is a gap in this Lean route. The kernel diagnostic does not refute
-- the set-theoretic claim. The supplied lecture notes assume ordinary
-- choice and do not resolve the gap under the reviewed Prop hypotheses.
-- https://alphabetamath.cc/item/lem-canonical-free-presentation-controls-eilenberg-watts-comparison
--
-- The checked Stacks cofan lemma requires both mapped IsColimit witnesses
-- and IsIso on each summand. Its audit includes Classical.choice. The
-- checked Stacks.EilenbergWatts.iso also uses that axiom and works over one
-- commutative ring for an R-linear endofunctor. Neither is used here.

end ChoiceFreeWatts

#print axioms ChoiceFreeWatts.comparison
#print axioms ChoiceFreeWatts.comparison_regular_left
#print axioms ChoiceFreeWatts.comparison_regular_right

#print axioms ChoiceFreeWatts.tau

#print axioms ChoiceFreeWatts.tensorFunctor
#print axioms ChoiceFreeWatts.comparison_naturality
#print axioms ChoiceFreeWatts.liftedF

#print axioms ChoiceFreeWatts.sumLift

#print axioms ChoiceFreeWatts.freeCoproduct
#print axioms ChoiceFreeWatts.cover_cokernel
#print axioms ChoiceFreeWatts.relations_zero

#print axioms ChoiceFreeWatts.rightCommute

#print axioms ChoiceFreeWatts.comparison_surjective
