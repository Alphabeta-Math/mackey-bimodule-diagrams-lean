import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RepresentationTheory.Rep.Iso
import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.RepresentationModuleCorrespondence
import NotesProofs.BimoduleTensorFunctoriality
namespace GroupAlgebraInductionAux

open CategoryTheory

universe r s l u v w

section Rings

variable {R : Type r} [Ring R] {S : Type s} [Ring S]

private abbrev Balanced (i : R →+* S) (V : ModuleCat.{l} R)
    (A : Type l) [AddCommGroup A] (p : S → V → A) : Prop :=
  (∀ x y z, p (x + y) z = p x z + p y z) ∧
  (∀ x z z', p x (z + z') = p x z + p x z') ∧
  (∀ (a : R) (x : S) (z : V), p (x * i a) z = p x (a • z))

-- The single-object functor encodes right multiplication by i(a).
-- Associativity gives S-linearity and reverses the order of the endomorphisms.
private def regularBimodule (i : R →+* S) :
    AdditiveFunctor (SingleObj (MulOpposite R)) (ModuleCat.{s} S) := by
  let F : SingleObj (MulOpposite R) ⥤ ModuleCat.{s} S :=
    { obj := fun _ => ModuleCat.of S S
      map := fun a => ModuleCat.ofHom (LinearMap.mulRight S (i (MulOpposite.unop a)))
      map_id := by
        intro X
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change x * i 1 = x
        rw [map_one, mul_one]
      map_comp := by
        intro X Y Z a b
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change x * i (MulOpposite.unop ((show MulOpposite R from b) * (show MulOpposite R from a))) =
          (x * i (MulOpposite.unop a)) * i (MulOpposite.unop b)
        rw [MulOpposite.unop_mul, map_mul, mul_assoc] }
  refine ⟨F, ⟨?_⟩⟩
  intro X Y a b
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change x * i (MulOpposite.unop (a + b)) =
    x * i (MulOpposite.unop a) + x * i (MulOpposite.unop b)
  rw [MulOpposite.unop_add, map_add, mul_add]

-- Use the registered tensor functor and its universal property with this
-- fixed bimodule. The tensor supplier permits arbitrary noncommutative rings
-- and an output universe enlarged to the common module-carrier universe.
private theorem tensorForRingMap (i : R →+* S) :
    ∃ (L : ModuleCat.{max s l} R ⥤ ModuleCat.{max s l} S)
      (p : ∀ V : ModuleCat.{max s l} R, S → V → L.obj V),
      (∀ V, Balanced i V (L.obj V) (p V)) ∧
      (∀ (V : ModuleCat.{max s l} R) (A : Type (max s l)) [AddCommGroup A]
        (q : S → V → A), Balanced i V A q →
          ∃! f : L.obj V →+ A, ∀ x z, f (p V x z) = q x z) ∧
      (∀ (V : ModuleCat.{max s l} R) (a x : S) (z : V), a • p V x z = p V (a * x) z) ∧
      (∀ {V V' : ModuleCat.{max s l} R} (f : V ⟶ V') (x : S) (z : V),
        (L.map f).hom (p V x z) = p V' x (f.hom z)) := by
  let B := regularBimodule i
  obtain ⟨F, pure, hObj, hMap, _, _⟩ :=
    BimoduleTensorFunctoriality.{r, s, s, max s l, 0} R S
  refine ⟨Prod.sectR B _ ⋙ F, pure B, ?_, ?_, ?_, ?_⟩
  · intro V
    exact (hObj B V).1
  · intro V A _ q hq
    exact (hObj B V).2.1 (AddCommGrpCat.of A) q hq
  · intro V a x z
    exact (hObj B V).2.2 a x z
  · intro V V' f x z
    exact hMap (𝟙 B) f x z

variable (i : R →+* S) {L : ModuleCat.{l} R ⥤ ModuleCat.{l} S}
  {p : ∀ V : ModuleCat.{l} R, S → V → L.obj V}
  (hp : ∀ V, Balanced i V (L.obj V) (p V))
  (liftUnique : ∀ (V : ModuleCat.{l} R) (A : Type l) [AddCommGroup A]
    (q : S → V → A), Balanced i V A q →
      ∃! f : L.obj V →+ A, ∀ x z, f (p V x z) = q x z)
  (hpSmul : ∀ (V : ModuleCat.{l} R) (a x : S) (z : V), a • p V x z = p V (a * x) z)

include hp liftUnique in
private theorem addHom_ext {V : ModuleCat.{l} R} {A : Type l} [AddCommGroup A]
    (f g : L.obj V →+ A) (h : ∀ x z, f (p V x z) = g (p V x z)) : f = g := by
  have hq : Balanced i V A (fun x z => g (p V x z)) :=
    ⟨fun x y z => by rw [(hp V).1, map_add],
      fun x z z' => by rw [(hp V).2.1, map_add],
      fun a x z => by rw [(hp V).2.2]⟩
  obtain ⟨k, _, hk⟩ := liftUnique V A _ hq
  exact (hk f h).trans (hk g (fun _ _ => rfl)).symm

-- Proposition 7.6 and Alphabeta Math step 1.1. The same formulas work
-- over k in place of ℤ: restriction acts by i(a), so the R-linearity of f
-- and associativity give balance for every a, not only for group generators.
-- https://alphabetamath.cc/item/thm-induction-is-left-adjoint-and-coinduction-right-adjoint-to-restriction
include hp liftUnique hpSmul in
private theorem extension_exists {V : ModuleCat.{l} R} {W : ModuleCat.{l} S}
    (f : V ⟶ (ModuleCat.restrictScalars i).obj W) :
    ∃ g : L.obj V ⟶ W, ∀ x z, g.hom (p V x z) = x • (show W from f.hom z) := by
  let q := fun (x : S) (z : V) => x • (show W from f.hom z)
  have hq : Balanced i V W q := by
    refine ⟨?_, ?_, ?_⟩
    · intro x y z
      exact add_smul x y _
    · intro x z z'
      dsimp [q]
      rw [f.hom.map_add]
      exact smul_add x (show W from f.hom z) (show W from f.hom z')
    · intro a x z
      dsimp [q]
      rw [f.hom.map_smul]
      exact mul_smul x (i a) _
  obtain ⟨g, hg, _⟩ := liftUnique V W q hq
  refine ⟨ModuleCat.ofHom { __ := g, map_smul' := ?_ }, hg⟩
  intro a z
  let lhs := g.comp (DistribSMul.toAddMonoidHom (L.obj V) a)
  let rhs := (DistribSMul.toAddMonoidHom W a).comp g
  have h : lhs = rhs := addHom_ext i hp liftUnique lhs rhs (by
    intro x y
    change g (a • p V x y) = a • g (p V x y)
    rw [hpSmul, hg, hg]
    exact mul_smul a x _)
  exact DFunLike.congr_fun h z

private def evaluateAtOne {V : ModuleCat.{l} R} {W : ModuleCat.{l} S}
    (g : L.obj V ⟶ W) : V ⟶ (ModuleCat.restrictScalars i).obj W := by
  let f : V →ₗ[R] ((ModuleCat.restrictScalars i).obj W : Type l) :=
    { toFun := fun z => g.hom (p V 1 z)
      map_add' := by intro x y; rw [(hp V).2.1, map_add]
      map_smul' := by
        intro a z
        change g.hom (p V 1 (a • z)) = i a • g.hom (p V 1 z)
        rw [← (hp V).2.2, one_mul, ← g.hom.map_smul, hpSmul, mul_one] }
  exact ModuleCat.ofHom f

-- The article needs the induction half of the portal result. We package the
-- two formulas of step 1.1 with naturality on both variables using the
-- balanced tensor from Proposition 6.3. Mathlib's representation adjunction
-- uses coinvariants, and its module extension adjunction assumes commutative
-- rings, so we construct the adjunction for this tensor directly.
include hp liftUnique hpSmul in
private theorem tensorRestrictAdjunction
    (hpMap : ∀ {V V' : ModuleCat.{l} R} (f : V ⟶ V') (x : S) (z : V),
      (L.map f).hom (p V x z) = p V' x (f.hom z)) :
    Nonempty (L ⊣ ModuleCat.restrictScalars i) := by
  classical
  let extend {V : ModuleCat.{l} R} {W : ModuleCat.{l} S}
      (f : V ⟶ (ModuleCat.restrictScalars i).obj W) : L.obj V ⟶ W :=
    Classical.choose (extension_exists i hp liftUnique hpSmul f)
  have extend_pure {V : ModuleCat.{l} R} {W : ModuleCat.{l} S}
      (f : V ⟶ (ModuleCat.restrictScalars i).obj W) (x : S) (z : V) :
      (extend f).hom (p V x z) = x • (show W from f.hom z) :=
    Classical.choose_spec (extension_exists i hp liftUnique hpSmul f) x z
  let e (V : ModuleCat.{l} R) (W : ModuleCat.{l} S) :
      (L.obj V ⟶ W) ≃ (V ⟶ (ModuleCat.restrictScalars i).obj W) :=
    { toFun := evaluateAtOne i hp hpSmul
      invFun := extend
      left_inv := by
        intro g
        apply ModuleCat.hom_ext
        apply LinearMap.toAddMonoidHom_injective
        apply addHom_ext i hp liftUnique
        intro x z
        change (extend (evaluateAtOne i hp hpSmul g)).hom (p V x z) = g.hom (p V x z)
        rw [extend_pure]
        change x • g.hom (p V 1 z) = g.hom (p V x z)
        rw [← g.hom.map_smul, hpSmul, mul_one]
      right_inv := by
        intro f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro z
        change (extend f).hom (p V 1 z) = (show W from f.hom z)
        rw [extend_pure, one_smul] }
  refine ⟨Adjunction.mkOfHomEquiv ⟨e, ?_, ?_⟩⟩
  · intro V V' W f g
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply addHom_ext i hp liftUnique
    intro x z
    change (extend (f ≫ g)).hom (p V x z) =
      (extend g).hom ((L.map f).hom (p V x z))
    rw [hpMap, extend_pure, extend_pure]
    rfl
  · intro V W W' g f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl

end Rings

end GroupAlgebraInductionAux
