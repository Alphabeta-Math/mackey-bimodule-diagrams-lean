import Mathlib.Algebra.Category.ModuleCat.Ulift
import MackeyDiagrams
import Proofs.RegularModuleRightAction
import Proofs.ModuleTensorUniversalProperty

open CategoryTheory

universe u v w z

#check (∀ (A : Type u) (B : Type v) [Ring A] [Ring B]
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
              h = LinearMap.toAddMonoidHom tauX))))
