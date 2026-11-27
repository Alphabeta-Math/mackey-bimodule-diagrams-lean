import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Basic.Complex.Basic
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
universe u v

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
    exact ⟨fun n m x => add_smul n m _, fun n x y => by rw [ηadd, smul_add],
      fun s n x => mul_smul s n _, fun r n x => by rw [ηsmul, mul_smul]⟩
  · intro X Y p hp
    rcases hp with ⟨_, hadd, hleft, hbal⟩
    have at_one (n : B) (x : X) : p n x = n • p 1 x := by
      simpa only [mul_one] using hleft n 1 x
    let base : X ⟶ (ModuleCat.restrictScalars φ).obj Y :=
      ModuleCat.ofHom
        { toFun := p 1
          map_add' := hadd 1
          map_smul' := fun r x => by
            change p 1 (r • x) = φ r • p 1 x
            rw [← hbal, one_mul, at_one] }
    let lift := (adj.homEquiv X Y).symm base
    have on_unit : ∀ x : X, lift.hom (η X x) = p 1 x := by
      intro x
      rw [← homEquiv_apply, Equiv.apply_symm_apply]
      rfl
    refine ⟨lift.hom, ?_, ?_⟩
    · intro n x
      change lift.hom (n • η X x) = p n x
      rw [map_smul, on_unit, at_one]
    · intro candidate hcandidate
      have heq : ModuleCat.ofHom candidate = lift := by
        apply (adj.homEquiv X Y).injective
        apply ModuleCat.hom_ext
        ext x
        rw [homEquiv_apply, homEquiv_apply, on_unit]
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
          change p 1 (φ r • x) = r • p 1 x
          rw [← at_one]
          simpa only [mul_one] using hleft r 1 x }
    refine ⟨lift, fun n x => (at_one n x).symm, ?_⟩
    intro candidate hcandidate
    ext x
    simpa only [one_smul] using hcandidate 1 x
  · intro X Y f n x
    exact f.hom.map_smul n x

-- The two restriction functors agree on the action of the middle group
-- algebra. Check the identity on carriers first on group elements and then
-- extend it by the group algebra's universal property.
private noncomputable def strandRestrictionIso
    {k G H : Type u} [CommRing k] [Group G] [Group H] (f : H →* G) :
    (Rep.ofModuleMonoidAlgebra ⋙ (Rep.resFunctor f ⋙ Rep.toModuleMonoidAlgebra)) ≅
      ModuleCat.restrictScalars.{max u v} (MonoidAlgebra.mapDomainAlgHom k k f).toRingHom := by
  let A := MonoidAlgebra k H
  let B := MonoidAlgebra k G
  let φ := MonoidAlgebra.mapDomainAlgHom k k f
  let F : ModuleCat.{max u v} B ⥤ ModuleCat.{max u v} A :=
    Rep.ofModuleMonoidAlgebra ⋙ (Rep.resFunctor f ⋙ Rep.toModuleMonoidAlgebra)
  let R := ModuleCat.restrictScalars.{max u v} φ.toRingHom
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
    {k G H : Type u} [CommRing k] [Group G] [Group H] (f : H →* G) :
    ((Rep.ofModuleMonoidAlgebra ⋙ Rep.indFunctor.{max u v} k f) ⋙ Rep.toModuleMonoidAlgebra) ⊣
      ModuleCat.restrictScalars.{max u v} (MonoidAlgebra.mapDomainAlgHom k k f).toRingHom :=
  (((Rep.equivalenceModuleMonoidAlgebra (k := k) (G := H)).symm.toAdjunction.comp
    (Rep.indResAdjunction k f)).comp
      (Rep.equivalenceModuleMonoidAlgebra (k := k) (G := G)).toAdjunction).ofNatIsoRight
        (strandRestrictionIso f)

end
