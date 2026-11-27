import MackeyDiagrams
import Mathlib.GroupTheory.FreeGroup.Basic
import Proofs.CanonicalWattsComparison

universe u v w z

def WattsFreePresentationCorrectedType : Prop :=
  (∀ (A : Type u) (B : Type v) [Ring A] [Ring B]
  (F : CategoryTheory.Functor (ModuleCat.{max u z} A) (ModuleCat.{w} B))
  [CategoryTheory.Functor.Additive F],
  let FX := CategoryTheory.Functor.obj F
  let Fmap := fun (X Y : ModuleCat.{max u z} A) (f : ModuleCat.Hom X Y) =>
    CategoryTheory.Functor.map F f
  let compA : ∀ {X Y Z : ModuleCat.{max u z} A},
      ModuleCat.Hom X Y → ModuleCat.Hom Y Z → ModuleCat.Hom X Z :=
    fun {X Y Z} f g => @CategoryTheory.CategoryStruct.comp (ModuleCat.{max u z} A) _ X Y Z f g
  let compB : ∀ {X Y Z : ModuleCat.{w} B},
      ModuleCat.Hom X Y → ModuleCat.Hom Y Z → ModuleCat.Hom X Z :=
    fun {X Y Z} f g => @CategoryTheory.CategoryStruct.comp (ModuleCat.{w} B) _ X Y Z f g
  Nonempty (∀ (X Y Q : ModuleCat.{max u z} A)
      (f : ModuleCat.Hom X Y) (q : ModuleCat.Hom Y Q),
    compA f q = ModuleCat.ofHom 0 →
    Nonempty (∀ (Z : ModuleCat.{max u z} A) (g : ModuleCat.Hom Y Z),
      compA f g = ModuleCat.ofHom 0 →
      Unique {d : ModuleCat.Hom Q Z // compA q d = g}) →
    PProd (compB (Fmap X Y f) (Fmap Y Q q) = ModuleCat.ofHom 0)
      (∀ (Z : ModuleCat.{w} B) (g : ModuleCat.Hom (FX Y) Z),
        compB (Fmap X Y f) g = ModuleCat.ofHom 0 →
        Unique {d : ModuleCat.Hom (FX Q) Z //
          compB (Fmap Y Q q) d = g})) →
  Nonempty (∀ (I : Type (max u z)) (D : I → ModuleCat.{max u z} A) (P : ModuleCat.{max u z} A)
    (ι : ∀ i, ModuleCat.Hom (D i) P),
    Nonempty (∀ (Q : ModuleCat.{max u z} A) (legs : ∀ i, ModuleCat.Hom (D i) Q),
      Unique {d : ModuleCat.Hom P Q //
        ∀ i : I, compA (ι i) d = legs i}) →
    ∀ (Q : ModuleCat.{w} B) (legs : ∀ i, ModuleCat.Hom (FX (D i)) Q),
      Unique {d : ModuleCat.Hom (FX P) Q //
        ∀ i : I, compB (Fmap (D i) P (ι i)) d = legs i}) →
  let regular := ModuleCat.of A (ULift.{z} A)
  let down : LinearEquiv (RingHom.id A) (ULift.{z} A) A := ULift.moduleEquiv
  let M := FX regular
  let right : A → M → M := fun a m =>
    ModuleCat.Hom.hom (CategoryTheory.Functor.map F
      (ModuleCat.ofHom (LinearEquiv.conjRingEquiv (LinearEquiv.symm down)
        (LinearMap.mulRight A a)))) m
  let ell : ∀ (X : ModuleCat.{max u z} A), X → ModuleCat.Hom regular X :=
    fun _X x => ModuleCat.ofHom (LinearMap.smulRight (LinearEquiv.toLinearMap down) x)
  let beta : ∀ (X : ModuleCat.{max u z} A), M → X → ModuleCat.carrier (FX X) :=
    fun X m x => ModuleCat.Hom.hom (CategoryTheory.Functor.map F (ell X x)) m
  let Free := fun (X : ModuleCat.{max u z} A) => FreeAddGroup (Prod M X)
  let gen : ∀ (X : ModuleCat.{max u z} A), M → X → Free X :=
    fun _X m x => FreeAddGroup.of (m, x)
  let rel : ∀ (X : ModuleCat.{max u z} A), Free X → Free X → Prop := fun X p q =>
    (∃ a b : Free X, p = a + b ∧ q = b + a) ∨
    (∃ (m m' : M) (x : X), p = gen X (m + m') x ∧ q = gen X m x + gen X m' x) ∨
    (∃ (m : M) (x x' : X), p = gen X m (x + x') ∧ q = gen X m x + gen X m x') ∨
    (∃ (a : A) (m : M) (x : X), p = gen X (right a m) x ∧ q = gen X m (a • x))
  let relations : ∀ (X : ModuleCat.{max u z} A), AddCon (Free X) :=
    fun X => addConGen (rel X)
  let Tensor := fun X => AddCon.Quotient (relations X)
  let tensorAddCommGroup : ∀ (X : ModuleCat.{max u z} A), AddCommGroup (Tensor X) := fun X =>
    { AddCon.addGroup (relations X) with
      add_comm := fun p q =>
        AddCon.induction_on₂ p q fun a b =>
          (AddCon.eq (relations X)).2
            (AddConGen.Rel.of (a + b) (b + a) (Or.inl ⟨a, b, rfl, rfl⟩)) }
  let pure : ∀ (X : ModuleCat.{max u z} A), M → X → Tensor X :=
    fun X m x => @AddCon.toQuotient _ _ (relations X) (gen X m x)
  letI : ∀ X, AddCommGroup (Tensor X) := tensorAddCommGroup
  ∃ (tensorModule : ∀ (X : ModuleCat.{max u z} A), Module B (Tensor X)),
  let obj : ModuleCat.{max u z} A → ModuleCat.{max u z w} B := fun X =>
    @ModuleCat.of B _ (Tensor X) (tensorAddCommGroup X)
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
    let liftTarget := ModuleCat.uliftFunctor.{max u z, w} B
    let liftedF : CategoryTheory.Functor (ModuleCat.{max u z} A) (ModuleCat.{max u z w} B) :=
      { obj := fun X => CategoryTheory.Functor.obj liftTarget (FX X)
        map := fun f => CategoryTheory.Functor.map liftTarget (CategoryTheory.Functor.map F f)
        map_id := fun X =>
          Eq.trans
            (congrArg (fun f => CategoryTheory.Functor.map liftTarget f)
              (CategoryTheory.Functor.map_id F X))
            (CategoryTheory.Functor.map_id liftTarget (FX X))
        map_comp := fun {_ _ _} f g =>
          Eq.trans
            (congrArg (fun h => CategoryTheory.Functor.map liftTarget h)
              (CategoryTheory.Functor.map_comp F f g))
            (CategoryTheory.Functor.map_comp liftTarget
              (CategoryTheory.Functor.map F f) (CategoryTheory.Functor.map F g)) }
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
            h = LinearMap.toAddMonoidHom tauX)) ∧
      (∃ inverse : CategoryTheory.NatTrans liftedF T,
        ∀ X : ModuleCat.{max u z} A,
          let tauX := CategoryTheory.NatTrans.app tau X
          let invX := CategoryTheory.NatTrans.app inverse X
          CategoryTheory.CategoryStruct.comp tauX invX =
            CategoryTheory.CategoryStruct.id (CategoryTheory.Functor.obj T X) ∧
          CategoryTheory.CategoryStruct.comp invX tauX =
            CategoryTheory.CategoryStruct.id (CategoryTheory.Functor.obj liftedF X)))

#print axioms WattsFreePresentationCorrectedType

-- Test the witness across the same Prop-to-Type boundary as the inverse.
theorem packagedFactors {I : Type u} {L : I → Type v} [∀ i, Subsingleton (L i)]
    (h : Nonempty (∀ i, Unique (L i))) : Nonempty (∀ i, L i) := by
  obtain ⟨f⟩ := h
  exact ⟨fun i => (f i).default⟩

#print axioms packagedFactors
