import Mathlib.Algebra.Category.ModuleCat.Ulift
import MackeyDiagrams
import Proofs.RegularModuleRightAction
import Proofs.ModuleTensorUniversalProperty

set_option maxHeartbeats 2000000

open CategoryTheory

namespace CanonicalWattsComparisonSupport

universe u v w z y

noncomputable section Tensor

variable {A : Type u} {M : Type w} {X : Type z} [Ring A] [AddCommGroup M]
  [AddCommGroup X] [Module A X]

private abbrev gen (m : M) (x : X) : (M × X) →₀ ℤ :=
  Finsupp.single (m, x) 1

private abbrev relations (right : A → M → M) (X : Type z)
    [AddCommGroup X] [Module A X] : AddSubgroup ((M × X) →₀ ℤ) :=
  AddSubgroup.closure
    {p | (∃ (m m' : M) (x : X), p = gen (m + m') x - gen m x - gen m' x) ∨
      (∃ (m : M) (x x' : X), p = gen m (x + x') - gen m x - gen m x') ∨
      (∃ (a : A) (m : M) (x : X), p = gen (right a m) x - gen m (a • x))}

private abbrev Tensor (right : A → M → M) (X : Type z) [AddCommGroup X] [Module A X] :=
  ((M × X) →₀ ℤ) ⧸ relations right X

private abbrev pure (right : A → M → M) (m : M) (x : X) : Tensor right X :=
  QuotientAddGroup.mk' (relations right X) (gen m x)

private def Balanced {Y : Type y} [AddCommGroup Y] (right : A → M → M)
    (f : M → X → Y) : Prop :=
  (∀ m m' x, f (m + m') x = f m x + f m' x) ∧
  (∀ m x x', f m (x + x') = f m x + f m x') ∧
  (∀ a m x, f (right a m) x = f m (a • x))

variable {right : A → M → M}

private theorem pure_balanced [Module (MulOpposite A) M]
    (hright : ∀ a m, MulOpposite.op a • m = right a m) :
    Balanced right (pure (X := X) right) := by
  have h : right = fun a m => MulOpposite.op a • m :=
    funext fun a => funext fun m => (hright a m).symm
  subst right
  exact (ModuleTensorUniversalProperty.{u,w,z,0} A M X).1

private theorem tensor_ext [Module (MulOpposite A) M]
    (hright : ∀ a m, MulOpposite.op a • m = right a m) {Y : Type y} [AddCommGroup Y]
    (f g : Tensor right X →+ Y) (heq : ∀ m x, f (pure right m x) = g (pure right m x)) :
    f = g := by
  have h : right = fun a m => MulOpposite.op a • m :=
    funext fun a => funext fun m => (hright a m).symm
  subst right
  have ⟨⟨addLeft, addRight, balance⟩, univ⟩ := ModuleTensorUniversalProperty A M X
  obtain ⟨k, _, unique⟩ := (univ Y).1
    ⟨fun p => f (pure _ p.1 p.2),
      fun m m' x => (congrArg f (addLeft m m' x)).trans (map_add f _ _),
      fun m x x' => (congrArg f (addRight m x x')).trans (map_add f _ _),
      fun a m x => congrArg f (balance a m x)⟩
  exact (unique f (fun _ _ => rfl)).trans (unique g (fun m x => (heq m x).symm)).symm

-- Step 3.1 uses the universal property. Use the supplier for uniqueness
-- and implement its extension formula directly, so the map is defined by
-- the specified generators and relations.
private noncomputable def extend {Y : Type y} [AddCommGroup Y] (f : M → X → Y) :
    ((M × X) →₀ ℤ) →+ Y :=
  Finsupp.liftAddHom (fun p => zmultiplesHom Y (f p.1 p.2))

omit [AddCommGroup M] [AddCommGroup X] in
private theorem extend_gen {Y : Type y} [AddCommGroup Y] (f : M → X → Y) (m : M) (x : X) :
    extend f (gen m x) = f m x := by
  unfold extend
  rw [Finsupp.liftAddHom_apply_single]
  exact one_zsmul _

private noncomputable def lift {Y : Type y} [AddCommGroup Y] (f : M → X → Y)
    (hf : Balanced right f) : Tensor right X →+ Y :=
  QuotientAddGroup.lift (relations right X) (extend f) (by
    apply (AddSubgroup.closure_le _).2
    intro p hp
    apply AddMonoidHom.mem_ker.mpr
    rcases hp with ⟨m, m', x, rfl⟩ | ⟨m, x, x', rfl⟩ | ⟨a, m, x, rfl⟩
    · rw [map_sub, map_sub, sub_sub, extend_gen, extend_gen, extend_gen, hf.1, sub_self]
    · rw [map_sub, map_sub, sub_sub, extend_gen, extend_gen, extend_gen, hf.2.1, sub_self]
    · rw [map_sub, extend_gen, extend_gen, hf.2.2, sub_self])

private theorem lift_pure {Y : Type y} [AddCommGroup Y] (f : M → X → Y)
    (hf : Balanced right f) (m : M) (x : X) :
    lift f hf (pure right m x) = f m x :=
  extend_gen f m x

variable {B : Type v} [Ring B] [Module B M] [Module (MulOpposite A) M]
variable (hright : ∀ a m, MulOpposite.op a • m = right a m)
variable [SMulCommClass (MulOpposite A) B M]

-- Step 3.1 invokes the induced outer action. Build that action for this
-- quotient by descending m ↦ b • m for fixed b, using the commuting actions.
include hright in
private theorem scaleBalanced (b : B) :
    Balanced right (fun m (x : X) => pure right (b • m) x) := by
  have hp := pure_balanced (X := X) hright
  refine ⟨fun m m' x => ?_, fun m x x' => hp.2.1 _ x x', fun a m x => ?_⟩
  · change pure right (b • (m + m')) x = pure right (b • m) x + pure right (b • m') x
    rw [smul_add, hp.1]
  · change pure right (b • right a m) x = pure right (b • m) (a • x)
    rw [← hright, ← smul_comm (MulOpposite.op a) b m, hright, hp.2.2]

private def scale (b : B) : Tensor right X →+ Tensor right X :=
  lift _ (scaleBalanced hright b)

private theorem scale_pure (b : B) (m : M) (x : X) :
    scale hright b (pure right m x) = pure right (b • m) x :=
  lift_pure _ _ _ _

@[instance_reducible] private def outerModule : Module B (Tensor right X) where
  smul b t := scale hright b t
  one_smul t := by
    have h : scale hright (1 : B) = AddMonoidHom.id (Tensor right X) :=
      tensor_ext hright _ _ (fun m x => by simp only [scale_pure, one_smul, AddMonoidHom.id_apply])
    exact DFunLike.congr_fun h t
  mul_smul b c t := by
    have h : scale (X := X) hright (b * c) = (scale hright b).comp (scale hright c) :=
      tensor_ext hright _ _ (fun m x => by
        simp only [scale_pure, AddMonoidHom.comp_apply, mul_smul])
    exact DFunLike.congr_fun h t
  smul_zero b := map_zero (scale hright b)
  smul_add b t t' := map_add (scale hright b) t t'
  add_smul b c t := by
    have h : scale (X := X) hright (b + c) = scale hright b + scale hright c :=
      tensor_ext hright _ _ (fun m x => by
        simp only [scale_pure, AddMonoidHom.add_apply, add_smul, (pure_balanced (X := X) hright).1])
    exact DFunLike.congr_fun h t
  zero_smul t := by
    have h : scale hright (0 : B) = (0 : Tensor right X →+ Tensor right X) :=
      tensor_ext hright _ _ (fun _ x => by
        simp only [scale_pure, zero_smul, AddMonoidHom.zero_apply]
        have hzero := (pure_balanced hright).1 (0 : M) 0 x
        rw [zero_add] at hzero
        apply add_left_cancel (a := pure right (0 : M) x)
        rw [add_zero, ← hzero])
    exact DFunLike.congr_fun h t

private theorem outer_smul_pure (b : B) (m : M) (x : X) :
    letI : Module B (Tensor right X) := outerModule hright
    b • pure right m x = pure right (b • m) x :=
  scale_pure hright b m x

private def linearLift {Y : Type y} [AddCommGroup Y] [Module B Y]
    (f : M → X → Y) (hf : Balanced right f)
    (hB : ∀ (b : B) m x, f (b • m) x = b • f m x) :
    @LinearMap B B _ _ (RingHom.id B) (Tensor right X) Y _ _
      (outerModule hright) _ :=
  letI : Module B (Tensor right X) := outerModule hright
  { lift f hf with
    map_smul' := by
      intro b t
      let bY := DistribSMul.toAddMonoidHom Y b
      have h : (lift f hf).comp (scale hright b) = bY.comp (lift f hf) :=
        tensor_ext hright _ _ (fun m x => by
          simp only [AddMonoidHom.comp_apply, scale_pure, lift_pure]
          exact hB b m x)
      exact DFunLike.congr_fun h t }

private theorem linearLift_pure {Y : Type y} [AddCommGroup Y] [Module B Y]
    (f : M → X → Y) (hf : Balanced right f)
    (hB : ∀ (b : B) m x, f (b • m) x = b • f m x) (m : M) (x : X) :
    linearLift hright f hf hB (pure right m x) = f m x :=
  lift_pure f hf m x

end Tensor
end CanonicalWattsComparisonSupport


theorem CanonicalWattsComparison : (∀ (A : Type u) (B : Type v) [Ring A] [Ring B]
  (F : CategoryTheory.Functor (ModuleCat.{max u z} A) (ModuleCat.{w} B))
  [CategoryTheory.Functor.Additive F],
  let regular := ModuleCat.of A (ULift.{z} A)
  let down : LinearEquiv (RingHom.id A) (ULift.{z} A) A := ULift.moduleEquiv
  let FX : ModuleCat.{max u z} A → ModuleCat.{w} B := CategoryTheory.Functor.obj F
  let M := FX regular
  let right : A → M → M := fun a m =>
    ModuleCat.Hom.hom (CategoryTheory.Functor.map F
      (ModuleCat.ofHom (LinearEquiv.conjRingEquiv (LinearEquiv.symm down)
        (LinearMap.mulRight A a)))) m
  let ell : ∀ (X : ModuleCat.{max u z} A), X → ModuleCat.Hom regular X :=
    fun _X x => ModuleCat.ofHom (LinearMap.smulRight (LinearEquiv.toLinearMap down) x)
  let beta : ∀ (X : ModuleCat.{max u z} A), M → X → ModuleCat.carrier (FX X) :=
    fun X m x => ModuleCat.Hom.hom (CategoryTheory.Functor.map F (ell X x)) m
  let Free := fun (X : ModuleCat.{max u z} A) => Finsupp (Prod M X) Int
  let gen : ∀ (X : ModuleCat.{max u z} A), M → X → Free X :=
    fun _X m x => Finsupp.single (m, x) 1
  let relations : ∀ (X : ModuleCat.{max u z} A), AddSubgroup (Free X) := fun X =>
    AddSubgroup.closure
      { p | (∃ (m m' : M) (x : X), p = gen X (m + m') x - gen X m x - gen X m' x) ∨
        (∃ (m : M) (x x' : X), p = gen X m (x + x') - gen X m x - gen X m x') ∨
        (∃ (a : A) (m : M) (x : X), p = gen X (right a m) x - gen X m (a • x)) }
  let Tensor := fun X => HasQuotient.Quotient (Free X) (relations X)
  let pure : ∀ (X : ModuleCat.{max u z} A), M → X → Tensor X :=
    fun X m x => QuotientAddGroup.mk' (relations X) (gen X m x)
  (∀ (X : ModuleCat.{max u z} A),
    (∀ (m m' : M) (x : X), beta X (m + m') x = beta X m x + beta X m' x) ∧
    (∀ (m : M) (x x' : X), beta X m (x + x') = beta X m x + beta X m x') ∧
    (∀ (a : A) (m : M) (x : X), beta X (right a m) x = beta X m (a • x)) ∧
    (∀ (b : B) (m : M) (x : X), beta X (b • m) x = b • beta X m x)) ∧
  (∃ (tensorModule : ∀ (X : ModuleCat.{max u z} A), Module B (Tensor X)),
    let obj : ModuleCat.{max u z} A → ModuleCat.{max u z w} B := fun X =>
      @ModuleCat.of B _ (Tensor X) (QuotientAddGroup.Quotient.addCommGroup (relations X))
        (tensorModule X)
    ∃ (map : ∀ {X Y : ModuleCat.{max u z} A}, ModuleCat.Hom X Y → ModuleCat.Hom (obj X) (obj Y))
      (mapId : ∀ X, @map X X (CategoryTheory.CategoryStruct.id X) =
        CategoryTheory.CategoryStruct.id (obj X))
      (mapComp : ∀ {X Y Z : ModuleCat.{max u z} A} (f : ModuleCat.Hom X Y) (g : ModuleCat.Hom Y Z),
        @map X Z (@CategoryTheory.CategoryStruct.comp _ _ X Y Z f g) =
          @CategoryTheory.CategoryStruct.comp _ _ (obj X) (obj Y) (obj Z)
            (@map X Y f) (@map Y Z g)),
      let T : CategoryTheory.Functor (ModuleCat.{max u z} A) (ModuleCat.{max u z w} B) :=
        CategoryTheory.Functor.mk obj (@map) mapId (@mapComp)
      let liftedF := CategoryTheory.Functor.comp F (ModuleCat.uliftFunctor.{max u z, w} B)
      ∃ tau : CategoryTheory.NatTrans T liftedF,
        (∀ (X : ModuleCat.{max u z} A) (b : B) (m : M) (x : X),
          letI : Module B (Tensor X) := tensorModule X
          b • pure X m x = pure X (b • m) x) ∧
        (∀ (X Y : ModuleCat.{max u z} A) (f : ModuleCat.Hom X Y) (m : M) (x : X),
          ModuleCat.Hom.hom (CategoryTheory.Functor.map T f) (pure X m x) =
            pure Y m (ModuleCat.Hom.hom f x)) ∧
        (∀ (X : ModuleCat.{max u z} A),
          letI : Module B (Tensor X) := tensorModule X
          let tauX : LinearMap (RingHom.id B) (Tensor X) (FX X) := LinearMap.comp
            (LinearEquiv.toLinearMap (ULift.moduleEquiv :
              LinearEquiv (RingHom.id B) (ULift.{max u z} (FX X)) (FX X)))
            (ModuleCat.Hom.hom (CategoryTheory.NatTrans.app tau X))
          (∀ (m : M) (x : X), tauX (pure X m x) = beta X m x) ∧
          (∀ h : AddMonoidHom (Tensor X) (FX X),
            (∀ (m : M) (x : X), h (pure X m x) = beta X m x) →
              h = LinearMap.toAddMonoidHom tauX)))) :=
(by
  intro A B _ _ F _ regular down FX M right ell beta Free gen relations Tensor pure
  -- Alphabeta Math 1.1. The map x ↦ ℓₓ is additive and is compatible
  -- with right multiplication on the lifted regular module.
  let mulR (a : A) : regular ⟶ regular :=
    ModuleCat.ofHom (LinearEquiv.conjRingEquiv down.symm (LinearMap.mulRight A a))
  have ell_add (X : ModuleCat.{max u z} A) (x x' : X) :
      ell X (x + x') = @Add.add (regular ⟶ X) inferInstance (ell X x) (ell X x') := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change down t • (x + x') = down t • x + down t • x'
    exact smul_add _ _ _
  have ell_smul (X : ModuleCat.{max u z} A) (a : A) (x : X) :
      mulR a ≫ ell X x = ell X (a • x) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change (down t * a) • x = down t • (a • x)
    exact mul_smul _ _ _
  -- Step 2.1 uses the regular-module action with its original B-module
  -- structure. The supplier's pointwise formula identifies the exact
  -- balance relations in the endpoint with those of the quotient supplier.
  obtain ⟨⟨leftModule, ⟨rightModule, commute⟩⟩, hLeft, hAction⟩ :=
    RegularModuleRightAction A B F
  change leftModule = ModuleCat.isModule M at hLeft
  subst leftModule
  let : Module (MulOpposite A) M := rightModule
  have hRight (a : A) (m : M) : MulOpposite.op a • m = right a m := hAction a m
  have : SMulCommClass (MulOpposite A) B M := commute
  have betaBalanced (X : ModuleCat.{max u z} A) :
      CanonicalWattsComparisonSupport.Balanced right (beta X) := by
    refine ⟨?_, ?_, ?_⟩
    · intro m m' x
      exact map_add (F.map (ell X x)).hom m m'
    · intro m x x'
      change (F.map (ell X (x + x'))).hom m =
        (F.map (ell X x)).hom m + (F.map (ell X x')).hom m
      have hmap := F.map_add (X := regular) (Y := X) (f := ell X x) (g := ell X x')
      exact congrArg (fun k : FX regular ⟶ FX X => k.hom m)
        ((congrArg (fun k : regular ⟶ X => F.map k) (ell_add X x x')).trans hmap)
    · intro a m x
      change (F.map (ell X x)).hom ((F.map (mulR a)).hom m) =
        (F.map (ell X (a • x))).hom m
      rw [← ell_smul, F.map_comp]
      rfl
  have beta_smul (X : ModuleCat.{max u z} A) (b : B) (m : M) (x : X) :
      beta X (b • m) x = b • beta X m x :=
    (F.map (ell X x)).hom.map_smul b m
  refine ⟨fun X => ⟨(betaBalanced X).1, (betaBalanced X).2.1,
    (betaBalanced X).2.2, beta_smul X⟩, ?_⟩
  -- Step 3.1. Construct the outer action on the quotient, then descend
  -- the two generator formulas for the tensor functor and the comparison.
  let tensorModule (X : ModuleCat.{max u z} A) : Module B (Tensor X) :=
    CanonicalWattsComparisonSupport.outerModule hRight
  refine ⟨tensorModule, ?_⟩
  let obj (X : ModuleCat.{max u z} A) : ModuleCat.{max u z w} B :=
    @ModuleCat.of B _ (Tensor X) (QuotientAddGroup.Quotient.addCommGroup (relations X))
      (tensorModule X)
  have outer_pure (X : ModuleCat.{max u z} A) (b : B) (m : M) (x : X) :
      letI : Module B (Tensor X) := tensorModule X
      b • pure X m x = pure X (b • m) x :=
    CanonicalWattsComparisonSupport.outer_smul_pure hRight b m x
  have morphismBalanced {X Y : ModuleCat.{max u z} A} (f : X ⟶ Y) :
      CanonicalWattsComparisonSupport.Balanced right (fun m x => pure Y m (f.hom x)) := by
    have hp := CanonicalWattsComparisonSupport.pure_balanced (X := Y) hRight
    refine ⟨fun m m' x => hp.1 m m' (f.hom x), ?_, ?_⟩
    · intro m x x'
      simpa only [map_add] using hp.2.1 m (f.hom x) (f.hom x')
    · intro a m x
      simpa only [map_smul] using hp.2.2 a m (f.hom x)
  have morphism_smul {X Y : ModuleCat.{max u z} A} (f : X ⟶ Y)
      (b : B) (m : M) (x : X) :
      let : Module B (Tensor Y) := tensorModule Y
      pure Y (b • m) (f.hom x) = b • pure Y m (f.hom x) :=
    (outer_pure Y b m (f.hom x)).symm
  let map {X Y : ModuleCat.{max u z} A} (f : X ⟶ Y) : obj X ⟶ obj Y :=
    ModuleCat.ofHom (CanonicalWattsComparisonSupport.linearLift (X := X) hRight
      (fun m x => pure Y m (f.hom x)) (morphismBalanced f)
      (morphism_smul f))
  have map_pure (X Y : ModuleCat.{max u z} A) (f : X ⟶ Y) (m : M) (x : X) :
      (map f).hom (pure X m x) = pure Y m (f.hom x) :=
    CanonicalWattsComparisonSupport.linearLift_pure hRight
      (fun n t => pure Y n (f.hom t)) (morphismBalanced f) (morphism_smul f) m x
  have hom_ext {X : ModuleCat.{max u z} A} {Z : ModuleCat.{max u z w} B}
      {f g : obj X ⟶ Z}
      (h : ∀ (m : M) (x : X), f.hom (pure X m x) = g.hom (pure X m x)) : f = g :=
    ModuleCat.hom_ext (LinearMap.toAddMonoidHom_injective
      (CanonicalWattsComparisonSupport.tensor_ext hRight _ _ h))
  have mapId (X : ModuleCat.{max u z} A) : map (𝟙 X) = 𝟙 (obj X) := by
    apply hom_ext
    intro m x
    rw [map_pure]
    rfl
  have mapComp {X Y Z : ModuleCat.{max u z} A} (f : X ⟶ Y) (g : Y ⟶ Z) :
      map (f ≫ g) = map f ≫ map g := by
    apply hom_ext
    intro m x
    change (map (f ≫ g)).hom (pure X m x) = (map g).hom ((map f).hom (pure X m x))
    rw [map_pure, map_pure, map_pure]
    rfl
  let T : ModuleCat.{max u z} A ⥤ ModuleCat.{max u z w} B :=
    ⟨obj, @map, mapId, @mapComp⟩
  let liftedF := F ⋙ ModuleCat.uliftFunctor.{max u z, w} B
  let compare (X : ModuleCat.{max u z} A) : (obj X) →ₗ[B] FX X :=
    CanonicalWattsComparisonSupport.linearLift hRight (beta X) (betaBalanced X) (beta_smul X)
  have compare_pure (X : ModuleCat.{max u z} A) (m : M) (x : X) :
      compare X (pure X m x) = beta X m x :=
    CanonicalWattsComparisonSupport.linearLift_pure hRight
      (beta X) (betaBalanced X) (beta_smul X) m x
  -- Step 4.1. Linearity of f gives ℓₓ ≫ f = ℓ_{f(x)}; the
  -- naturality square follows on generators after applying F.
  have beta_natural {X Y : ModuleCat.{max u z} A} (f : X ⟶ Y) (m : M) (x : X) :
      (F.map f).hom (beta X m x) = beta Y m (f.hom x) := by
    have hell : ell X x ≫ f = ell Y (f.hom x) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      change f.hom (down t • x) = down t • f.hom x
      exact f.hom.map_smul _ _
    change (F.map f).hom ((F.map (ell X x)).hom m) =
      (F.map (ell Y (f.hom x))).hom m
    rw [← hell, F.map_comp]
    rfl
  -- Step 5.1. The target universe lift accommodates the carriers of
  -- the quotients. Its inverse recovers the comparison on each object.
  -- The construction uses the quotient relations and the given variables.
  let component (X : ModuleCat.{max u z} A) : T.obj X ⟶ liftedF.obj X :=
    ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp (compare X))
  let tau : T ⟶ liftedF :=
    { app := component
      naturality := by
        intro X Y f
        apply hom_ext
        intro m x
        change ULift.up (compare Y ((map f).hom (pure X m x))) =
          ULift.up ((F.map f).hom (compare X (pure X m x)))
        rw [map_pure, compare_pure, compare_pure, beta_natural] }
  refine ⟨@map, mapId, @mapComp, tau, outer_pure, map_pure, ?_⟩
  intro X
  change (∀ (m : M) (x : X), compare X (pure X m x) = beta X m x) ∧
    (∀ h : Tensor X →+ FX X, (∀ (m : M) (x : X), h (pure X m x) = beta X m x) →
      h = (compare X).toAddMonoidHom)
  refine ⟨compare_pure X, fun h hh => ?_⟩
  exact CanonicalWattsComparisonSupport.tensor_ext hRight _ _
    (fun m x => (hh m x).trans (compare_pure X m x).symm))

#print axioms CanonicalWattsComparison
