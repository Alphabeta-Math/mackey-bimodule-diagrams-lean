import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Rep.Iso
import Proofs.ConjugationEmbeddingCentralizerCoset
import Proofs.Bimodule
import Proofs.ModuleTensorUniversalProperty
import MackeyDiagrams

private abbrev strandTensorsOnRight.{u, v} := fun (S R : Type u) [Ring S] [Ring R]
  (N : Type u) [AddCommGroup N]
  (left : S → N → N) (right : R → N → N)
  (F : CategoryTheory.Functor (ModuleCat.{max u v} R) (ModuleCat.{max u v} S)) =>
let Balanced := fun (X : ModuleCat.{max u v} R) (Y : ModuleCat.{max u v} S)
    (p : N → X → Y) =>
  (∀ n n' : N, ∀ x : X, p (n + n') x = p n x + p n' x) ∧
  (∀ n : N, ∀ x x' : X, p n (x + x') = p n x + p n x') ∧
  (∀ (s : S) (n : N) (x : X), p (left s n) x = s • p n x) ∧
  (∀ (r : R) (n : N) (x : X), p (right r n) x = p n (r • x))
∃ τ : ∀ X : ModuleCat.{max u v} R, N → X → F.obj X,
  (∀ X, Balanced X (F.obj X) (τ X)) ∧
  (∀ (X : ModuleCat.{max u v} R) (Y : ModuleCat.{max u v} S)
      (p : N → X → Y), Balanced X Y p →
    ∃! f : LinearMap (RingHom.id S) (F.obj X) Y,
      ∀ (n : N) (x : X), f (τ X n x) = p n x) ∧
  (∀ (X Y : ModuleCat.{max u v} R) (f : Quiver.Hom X Y) (n : N) (x : X),
    ModuleCat.Hom.hom (F.map f) (τ X n x) = τ Y n (ModuleCat.Hom.hom f x))

section
open CategoryTheory
universe i u v

-- Alphabeta Math, Universal property of M⊗_RN, Steps 1.2, 4.1 and 5.1.
-- For this realization the adjunction unit provides the generator at 1. The
-- Hom equivalence descends a balanced map with its exterior linearity, and
-- injectivity gives uniqueness. ModuleTensorUniversalProperty constructs the
-- additive quotient; the Hom equivalence here works in the required module
-- category and supplies naturality in the tensor argument.
private theorem strandInductionTensor {A B : Type u} [Ring A] [Ring B]
    (φ : A →+* B) {F : ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} B}
    (adj : F ⊣ ModuleCat.restrictScalars φ) :
    strandTensorsOnRight B A B (fun s n => s * n) (fun r n => n * φ r) F := by
  let η (X : ModuleCat A) (x : X) : F.obj X := (adj.unit.app X).hom x
  have ηadd (X : ModuleCat A) (x y : X) : η X (x + y) = η X x + η X y :=
    (adj.unit.app X).hom.map_add x y
  have ηsmul (X : ModuleCat A) (r : A) (x : X) : η X (r • x) = φ r • η X x :=
    (adj.unit.app X).hom.map_smul r x
  have homEquiv_apply (X : ModuleCat A) (Y : ModuleCat B) (f : F.obj X ⟶ Y) (x : X) :
      ((adj.homEquiv X Y) f).hom x = f.hom (η X x) := by
    rw [Adjunction.homEquiv_unit]
    rfl
  refine ⟨fun X n x => n • η X x, ?_, ?_, ?_⟩
  · intro X
    refine ⟨fun n m x => add_smul n m _, ?_, fun s n x => mul_smul s n _, ?_⟩
    · intro n x y
      change n • η X (x + y) = n • η X x + n • η X y
      rw [ηadd, smul_add]
    · intro r n x
      change (n * φ r) • η X x = n • η X (r • x)
      rw [ηsmul, mul_smul]
  · intro X Y p hp
    rcases hp with ⟨_, hadd, hleft, hbal⟩
    have at_one (n : B) (x : X) : p n x = n • p 1 x := by
      simpa only [mul_one] using hleft n 1 x
    let base : X ⟶ (ModuleCat.restrictScalars φ).obj Y :=
      ModuleCat.ofHom (X := X) (Y := (ModuleCat.restrictScalars φ).obj Y)
        { toFun := p 1
          map_add' := hadd 1
          map_smul' := fun r x => by
            change p 1 (r • x) = φ r • p 1 x
            have hb : p (1 * φ r) x = p 1 (r • x) := hbal r 1 x
            exact (by simpa only [one_mul] using hb.symm : p 1 (r • x) = p (φ r) x) |>.trans
              (at_one (φ r) x) }
    let lift := (adj.homEquiv X Y).symm base
    have on_unit : ∀ x : X, lift.hom (η X x) = p 1 x := by
      intro x
      rw [← homEquiv_apply, Equiv.apply_symm_apply]
      rfl
    refine ⟨lift.hom, ?_, ?_⟩
    · intro n x
      change lift.hom (n • η X x) = p n x
      rw [map_smul, on_unit]
      exact (at_one n x).symm
    · intro candidate hcandidate
      have heq : ModuleCat.ofHom candidate = lift := by
        apply (adj.homEquiv X Y).injective
        apply ModuleCat.hom_ext
        ext x
        rw [homEquiv_apply, homEquiv_apply, on_unit]
        change candidate (η X x) = p 1 x
        simpa only [one_smul] using hcandidate 1 x
      exact congrArg ModuleCat.Hom.hom heq
  · intro X Y f n x
    have hf : (F.map f).hom (η X x) = η Y (f.hom x) := by
      exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (adj.unit_naturality f)) x
    change (F.map f).hom (n • η X x) = n • η Y (f.hom x)
    rw [map_smul, hf]

-- Steps 1.2 and 5.1 specialize here to multiplication on the regular tensor
-- factor. Balancing expresses p(n,x) as p(1,n • x).
private theorem strandRestrictionTensor {A B : Type u} [Ring A] [Ring B]
    (φ : A →+* B) :
    strandTensorsOnRight A B B (fun r n => φ r * n) (fun s n => n * s)
      (ModuleCat.restrictScalars.{max u v} φ) := by
  refine ⟨fun X n x => n • x, ?_, ?_, ?_⟩
  · intro X
    exact ⟨fun n m x => add_smul n m x, fun n x y => smul_add n x y,
      fun r n x => mul_smul (φ r) n x, fun s n x => mul_smul n s x⟩
  · intro X Y p hp
    rcases hp with ⟨_, hadd, hleft, hbal⟩
    have at_one (n : B) (x : X) : p n x = p 1 (n • x) := by
      simpa only [one_mul] using hbal n 1 x
    let lift : ((ModuleCat.restrictScalars φ).obj X) →ₗ[A] Y :=
      { toFun := p 1
        map_add' := hadd 1
        map_smul' := fun r x => by
          let y : X := x
          change p 1 (φ r • y) = r • p 1 y
          rw [← at_one]
          simpa only [mul_one] using hleft r 1 y }
    refine ⟨lift, fun n x => (at_one n x).symm, ?_⟩
    intro candidate hcandidate
    apply LinearMap.ext
    intro x
    let y : X := x
    change candidate (show (ModuleCat.restrictScalars φ).obj X from y) = p 1 y
    have hc : candidate (show (ModuleCat.restrictScalars φ).obj X from (1 : B) • y) = p 1 y :=
      hcandidate 1 y
    simpa only [one_smul] using hc
  · intro X Y f n x
    exact f.hom.map_smul n x

-- The two restriction functors agree on the action of the middle group
-- algebra. Check the identity on carriers first on group elements and then
-- extend it by the group algebra's universal property.
private noncomputable def strandRestrictionIso
    {k : Type i} {G H : Type u} [CommRing k] [Group G] [Group H] (f : H →* G) :
    (Rep.ofModuleMonoidAlgebra ⋙ (Rep.resFunctor f ⋙ Rep.toModuleMonoidAlgebra)) ≅
      ModuleCat.restrictScalars.{max i u v} (MonoidAlgebra.mapDomainAlgHom k k f).toRingHom := by
  let A := MonoidAlgebra k H
  let B := MonoidAlgebra k G
  let φ := MonoidAlgebra.mapDomainAlgHom k k f
  let F : ModuleCat.{max i u v} B ⥤ ModuleCat.{max i u v} A :=
    Rep.ofModuleMonoidAlgebra ⋙ (Rep.resFunctor f ⋙ Rep.toModuleMonoidAlgebra)
  let R := ModuleCat.restrictScalars.{max i u v} φ.toRingHom
  change F ≅ R
  have action (X : ModuleCat B) (r : A) (x : F.obj X) : r • x = φ r • (show X from x) := by
    let ρ := Representation.ofModule (k := k) (G := G) X
    let σ : Representation k H (RestrictScalars k B X) := ρ.comp f
    have hf : σ.asAlgebraHom = ρ.asAlgebraHom.comp φ := by
      apply (MonoidAlgebra.lift k _ H).symm.injective
      apply MonoidHom.ext
      intro h
      change σ.asAlgebraHom (MonoidAlgebra.single h 1) =
        ρ.asAlgebraHom (MonoidAlgebra.mapDomain f (MonoidAlgebra.single h 1))
      rw [MonoidAlgebra.mapDomain_single, Representation.asAlgebraHom_single_one,
        Representation.asAlgebraHom_single_one]
      rfl
    change σ.asAlgebraHom r x = _
    rw [hf]
    exact Representation.ofModule_asAlgebraHom_apply_apply X (φ r) x
  refine NatIso.ofComponents (fun X => ?_) (fun g => ?_)
  · let e : (F.obj X) ≃ₗ[A] (R.obj X) :=
      { toEquiv := Equiv.refl X
        map_add' := fun _ _ => rfl
        map_smul' := fun r x => action X r x }
    exact e.toModuleIso
  · apply ModuleCat.hom_ext
    ext x
    rfl

private noncomputable def strandInductionAdjunction
    {k : Type i} {G H : Type u} [CommRing k] [Group G] [Group H] (f : H →* G) :
    ((Rep.ofModuleMonoidAlgebra ⋙ Rep.indFunctor.{max i u v} k f) ⋙ Rep.toModuleMonoidAlgebra) ⊣
      ModuleCat.restrictScalars.{max i u v} (MonoidAlgebra.mapDomainAlgHom k k f).toRingHom :=
  (((Rep.equivalenceModuleMonoidAlgebra (k := k) (G := H)).symm.toAdjunction.comp
    (Rep.indResAdjunction k f)).comp
      (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)).toAdjunction).ofNatIsoRight
        (strandRestrictionIso.{i, u, v} f)

end

section
open MackeyDiagrams
universe u w

-- Alphabeta Math, Steps 3.1, 4.1 and 5.1. For two linearized bisets the
-- additive relations already hold by bilinearity. The orbit quotient enforces
-- diagonal group balance. Extend this to the middle group algebra by linearity.
private theorem strandBalancedProduct {K H J : Type u} [Group K] [Group H] [Group J]
    (X : Biset K H) (Y : Biset H J) :
    let right := fun (r : MonoidAlgebra Complex H) (x : X.carrier →₀ Complex) =>
      freeLift Complex (fun h : H => X.actLinear Complex (1, h⁻¹) x) r.coeff
    let left := fun (r : MonoidAlgebra Complex H) (y : Y.carrier →₀ Complex) =>
      freeLift Complex (fun h : H => Y.actLinear Complex (h, 1) y) r.coeff
    let pair := Biset.pairLinear Complex X Y
    (∀ r x y, pair (right r x) y = pair x (left r y)) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module Complex M]
        (f : (X.carrier →₀ Complex) →ₗ[Complex] (Y.carrier →₀ Complex) →ₗ[Complex] M),
      (∀ r x y, f (right r x) y = f x (left r y)) →
      ∃! lift : ((X.tensor Y).carrier →₀ Complex) →ₗ[Complex] M,
        ∀ x y, lift (pair x y) = f x y) := by
  intro right left pair
  have undo (h : H) (x : X.carrier →₀ Complex) :
      X.actLinear Complex (1, h⁻¹) (X.actLinear Complex (1, h) x) = x := by
    have comp_eq :
        (X.actLinear Complex (1, h⁻¹)).comp (X.actLinear Complex (1, h)) =
          LinearMap.id := by
      apply Finsupp.lhom_ext
      intro a c
      simp only [LinearMap.comp_apply, LinearMap.id_apply, Biset.actLinear_single, ← X.mul_act,
        Prod.mk_mul_mk, one_mul, inv_mul_cancel, ← Prod.one_eq_mk, X.one_act]
    exact LinearMap.congr_fun comp_eq x
  have right_single (h : H) (x : X.carrier →₀ Complex) :
      right (MonoidAlgebra.single h 1) x = X.actLinear Complex (1, h⁻¹) x := by
    simp [right]
  have left_single (h : H) (y : Y.carrier →₀ Complex) :
      left (MonoidAlgebra.single h 1) y = Y.actLinear Complex (h, 1) y := by
    simp [left]
  constructor
  · intro r x y
    let l := (pair.flip y).comp
      (freeLift Complex (fun h : H => X.actLinear Complex (1, h⁻¹) x))
    let m := (pair x).comp
      (freeLift Complex (fun h : H => Y.actLinear Complex (h, 1) y))
    have hlm : l = m := by
      apply Finsupp.lhom_ext
      intro h c
      change pair (freeLift Complex _ (Finsupp.single h c)) y =
        pair x (freeLift Complex _ (Finsupp.single h c))
      simp only [freeLift_single, map_smul, LinearMap.smul_apply]
      -- Reindex the inverse in the first slot of diagonal balance.
      have heq := Biset.pairLinear_balance Complex X Y h
        (X.actLinear Complex (1, h⁻¹) x) y
      have hinv := undo h⁻¹ x
      simp only [inv_inv] at hinv
      rw [hinv] at heq
      exact congrArg (fun z => c • z) heq.symm
    exact LinearMap.congr_fun hlm r.coeff
  · intro M _ _ f hf
    have diagonal : Biset.IsBalanced f := by
      intro h x y
      have heq := hf (MonoidAlgebra.single h 1) (X.actLinear Complex (1, h) x) y
      rw [right_single, left_single, undo] at heq
      exact heq.symm
    exact ⟨Biset.liftBalanced f diagonal, Biset.liftBalanced_pairLinear f diagonal,
      fun g hg => Biset.liftBalanced_unique f diagonal g hg⟩

-- A pair of group elements acts by left and right multiplication on basis
-- vectors. Both expressions extend to the whole group algebra by linearity.
private theorem strandBasisMultiplication {G : Type u} [Group G] (a b : G)
    (x : MonoidAlgebra Complex G) :
    MonoidAlgebra.ofCoeff
      (Finsupp.lmapDomain Complex Complex (fun z : G => a * z * b) x.coeff) =
      MonoidAlgebra.single a 1 * (x * MonoidAlgebra.single b 1) := by
  induction x using MonoidAlgebra.induction_on with
  | of z =>
    simp [MonoidAlgebra.of_apply, Finsupp.lmapDomain_apply, MonoidAlgebra.single_mul_single,
      mul_assoc]
  | add x y hx hy =>
    simp only [MonoidAlgebra.coeff_add, map_add, MonoidAlgebra.ofCoeff_add, add_mul,
      mul_add, hx, hy]
  | smul r x hx =>
    simp only [MonoidAlgebra.coeff_smul, map_smul, MonoidAlgebra.ofCoeff_smul,
      smul_mul_assoc, mul_smul_comm, hx]

-- Pull back each regular action along the prescribed ring homomorphism.
private noncomputable def strandBimodule {S R B : Type u} [Ring S] [Ring R] [Ring B]
    (leftHom : S →+* B) (rightHom : R →+* B) : Bimodule.1 S R B :=
  let left : Module S B := Module.compHom B leftHom
  let right : Module (MulOpposite R) B := Module.compHom B (RingHom.op rightHom)
  letI : SMul S B := left.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
  letI : SMul (MulOpposite R) B := right.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
  ⟨left, ⟨right, show SMulCommClass (MulOpposite R) S B from
    ⟨fun r s x => show (leftHom s * x) * rightHom (MulOpposite.unop r) =
      leftHom s * (x * rightHom (MulOpposite.unop r)) from mul_assoc _ _ _⟩⟩⟩

end

universe u v w

theorem InductionRestrictionBimoduleStrands : (∀ {U : Type u} [Group U],
  (∀ (H G : Subgroup U) (α : U) (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G),
    let A := MonoidAlgebra Complex H
    let B := MonoidAlgebra Complex G
    let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
    let φ := MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom
    let up := MackeyDiagrams.Word.up a
    let down := MackeyDiagrams.Word.down a
    let Ind : CategoryTheory.Functor (ModuleCat.{max u v} A) (ModuleCat.{max u v} B) :=
      CategoryTheory.Functor.comp
        (CategoryTheory.Functor.comp
          (Rep.ofModuleMonoidAlgebra (k := Complex) (G := H))
          (Rep.indFunctor Complex a.toHom))
        (Rep.toModuleMonoidAlgebra (k := Complex) (G := G))
    let Res : CategoryTheory.Functor (ModuleCat.{max u v} B) (ModuleCat.{max u v} A) :=
      ModuleCat.restrictScalars φ.toRingHom
    let TensorsOnRight := fun (S R : Type u) [Ring S] [Ring R]
        (N : Type u) [AddCommGroup N]
        (left : S → N → N) (right : R → N → N)
        (F : CategoryTheory.Functor (ModuleCat.{max u v} R) (ModuleCat.{max u v} S)) =>
      let Balanced := fun (X : ModuleCat.{max u v} R) (Y : ModuleCat.{max u v} S)
          (p : N → X → Y) =>
        (∀ n n' : N, ∀ x : X, p (n + n') x = p n x + p n' x) ∧
        (∀ n : N, ∀ x x' : X, p n (x + x') = p n x + p n x') ∧
        (∀ (s : S) (n : N) (x : X), p (left s n) x = s • p n x) ∧
        (∀ (r : R) (n : N) (x : X), p (right r n) x = p n (r • x))
      ∃ τ : ∀ X : ModuleCat.{max u v} R, N → X → F.obj X,
        (∀ X, Balanced X (F.obj X) (τ X)) ∧
        (∀ (X : ModuleCat.{max u v} R) (Y : ModuleCat.{max u v} S)
            (p : N → X → Y), Balanced X Y p →
          ∃! f : LinearMap (RingHom.id S) (F.obj X) Y,
            ∀ (n : N) (x : X), f (τ X n x) = p n x) ∧
        (∀ (X Y : ModuleCat.{max u v} R) (f : Quiver.Hom X Y) (n : N) (x : X),
          ModuleCat.Hom.hom (F.map f) (τ X n x) = τ Y n (ModuleCat.Hom.hom f x))
    (∀ (h : H) (c : Complex),
      φ (MonoidAlgebra.single h c) = MonoidAlgebra.single (a.toHom h) c) ∧
    (∀ (β : U) (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G),
      φ = MonoidAlgebra.mapDomainAlgHom Complex Complex
        (MackeyDiagrams.ConjEmbedding.ofConjugator β hβ).toHom ↔
      LeftCosetEquivalence (Subgroup.centralizer (H : Set U) : Set U) α β) ∧
    ∃ (I : Bimodule.1 B A (MonoidAlgebra Complex up.basis.carrier))
      (D : Bimodule.1 A B (MonoidAlgebra Complex down.basis.carrier)),
      let leftI := @SMul.smul B B I.1.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
      let rightI := fun (r : A) (x : B) =>
        @SMul.smul (MulOpposite A) B
          I.2.1.toDistribMulAction.toMulAction.toSemigroupAction.toSMul (MulOpposite.op r) x
      let leftD := @SMul.smul A B D.1.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
      let rightD := fun (r : B) (x : B) =>
        @SMul.smul (MulOpposite B) B
          D.2.1.toDistribMulAction.toMulAction.toSemigroupAction.toSMul (MulOpposite.op r) x
      (∀ (s x : B), leftI s x = s * x) ∧
      (∀ (r : A) (x : B), rightI r x = x * φ r) ∧
      (∀ (r : A) (x : B), leftD r x = φ r * x) ∧
      (∀ (s x : B), rightD s x = x * s) ∧
      (∀ (g : G) (h : H) (x : B),
        MonoidAlgebra.ofCoeff
          (MackeyDiagrams.Biset.actLinear Complex up.basis (g, h⁻¹) (MonoidAlgebra.coeff x)) =
        leftI (MonoidAlgebra.single g 1) (rightI (MonoidAlgebra.single h 1) x)) ∧
      (∀ (h : H) (g : G) (x : B),
        MonoidAlgebra.ofCoeff
          (MackeyDiagrams.Biset.actLinear Complex down.basis (h, g⁻¹) (MonoidAlgebra.coeff x)) =
        leftD (MonoidAlgebra.single h 1) (rightD (MonoidAlgebra.single g 1) x)) ∧
      TensorsOnRight B A B leftI rightI Ind ∧
      TensorsOnRight A B B leftD rightD Res) ∧
  (∀ (K L J : Subgroup U) (p : MackeyDiagrams.Word K L) (q : MackeyDiagrams.Word L J),
    let X := Finsupp p.basis.carrier Complex
    let Y := Finsupp q.basis.carrier Complex
    let Z := Finsupp (MackeyDiagrams.Word.tensor p q).basis.carrier Complex
    let right := fun (r : MonoidAlgebra Complex L) (x : X) =>
      MackeyDiagrams.freeLift Complex
        (fun h : L => MackeyDiagrams.Biset.actLinear Complex p.basis (1, h⁻¹) x)
        (MonoidAlgebra.coeff r)
    let left := fun (r : MonoidAlgebra Complex L) (y : Y) =>
      MackeyDiagrams.freeLift Complex
        (fun h : L => MackeyDiagrams.Biset.actLinear Complex q.basis (h, 1) y)
        (MonoidAlgebra.coeff r)
    let pair := MackeyDiagrams.Biset.pairLinear Complex p.basis q.basis
    (∀ (r : MonoidAlgebra Complex L) (x : X) (y : Y),
      pair (right r x) y = pair x (left r y)) ∧
    (∀ (M : Type w) [AddCommGroup M] [Module Complex M]
        (f : LinearMap (RingHom.id Complex) X (LinearMap (RingHom.id Complex) Y M)),
      (∀ (r : MonoidAlgebra Complex L) (x : X) (y : Y),
        f (right r x) y = f x (left r y)) →
      ∃! lift : LinearMap (RingHom.id Complex) Z M,
        ∀ (x : X) (y : Y), lift (pair x y) = f x y)) ∧
  (∀ (K L J : Subgroup U)
      (p p' : MackeyDiagrams.Word K L) (q q' : MackeyDiagrams.Word L J)
      (d : MackeyDiagrams.LabelledDrawing Complex p p')
      (e : MackeyDiagrams.LabelledDrawing Complex q q')
      (x : Finsupp p.basis.carrier Complex) (y : Finsupp q.basis.carrier Complex),
    (MackeyDiagrams.LabelledDrawing.interpret
      (MackeyDiagrams.LabelledDrawing.horizontal d e)).eval.toLinearMap
      (MackeyDiagrams.Biset.pairLinear Complex p.basis q.basis x y) =
    MackeyDiagrams.Biset.pairLinear Complex p'.basis q'.basis
      ((MackeyDiagrams.LabelledDrawing.interpret d).eval.toLinearMap x)
      ((MackeyDiagrams.LabelledDrawing.interpret e).eval.toLinearMap y)) ∧
  (∀ (K H : Subgroup U) (p q r : MackeyDiagrams.Word K H)
      (bottom : MackeyDiagrams.LabelledDrawing Complex p q)
      (top : MackeyDiagrams.LabelledDrawing Complex q r),
    (MackeyDiagrams.LabelledDrawing.interpret
      (MackeyDiagrams.LabelledDrawing.vertical bottom top)).eval.toLinearMap =
      LinearMap.comp (MackeyDiagrams.LabelledDrawing.interpret top).eval.toLinearMap
        (MackeyDiagrams.LabelledDrawing.interpret bottom).eval.toLinearMap)) :=
by
  classical
  intro U _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro H G α hα A B a φ up down Ind Res TensorsOnRight
    have single (h : H) (c : Complex) :
        φ (MonoidAlgebra.single h c) = MonoidAlgebra.single (a.toHom h) c :=
      MonoidAlgebra.mapDomain_single
    refine ⟨single, ?_, ?_⟩
    · intro β hβ
      exact ConjugationEmbeddingCentralizerCoset H G α β hα hβ
    -- The two arrows in § 1.2 use the same carrier. Pull back the right
    -- regular action for the up-strand and the left regular action for the
    -- down-strand. The right action is a module over the opposite ring.
    let I : Bimodule.1 B A B := strandBimodule (RingHom.id B) φ.toRingHom
    let D : Bimodule.1 A B B := strandBimodule φ.toRingHom (RingHom.id B)
    refine ⟨I, D, (fun _ _ => rfl), (fun _ _ => rfl), (fun _ _ => rfl),
      (fun _ _ => rfl), ?_, ?_, ?_, ?_⟩
    · intro g h x
      -- The second coordinate of the biset action acts by an inverse.
      change MonoidAlgebra.ofCoeff
          (Finsupp.lmapDomain Complex Complex (fun z : G => g * z * (a.toHom h⁻¹)⁻¹) x.coeff) =
        MonoidAlgebra.single g 1 * (x * φ (MonoidAlgebra.single h 1))
      rw [single]
      simpa only [map_inv, inv_inv] using strandBasisMultiplication g (a.toHom h) x
    · intro h g x
      change MonoidAlgebra.ofCoeff
          (Finsupp.lmapDomain Complex Complex (fun z : G => a.toHom h * z * (g⁻¹)⁻¹) x.coeff) =
        φ (MonoidAlgebra.single h 1) * (x * MonoidAlgebra.single g 1)
      rw [single]
      simpa only [inv_inv] using strandBasisMultiplication (a.toHom h) g x
    · exact strandInductionTensor φ.toRingHom (F := Ind)
        (strandInductionAdjunction.{0, u, v} (k := Complex) a.toHom)
    · exact strandRestrictionTensor φ.toRingHom
  · intro K L J p q
    exact strandBalancedProduct p.basis q.basis
  · intro K L J p p' q q' d e x y
    exact MackeyDiagrams.Biset.Hom.horizontal_pairLinear d.interpret.eval e.interpret.eval x y
  · intro K H p q r bottom top
    -- Evaluate the typed stack from bottom to top.
    rfl

#print axioms InductionRestrictionBimoduleStrands
