import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.RepresentationModuleCorrespondence
import NotesProofs.BimoduleTensorFunctoriality

set_option maxHeartbeats 2000000

namespace GroupAlgebraInductionAux

open CategoryTheory

universe r s l

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
-- NotesProofs/BimoduleTensorFunctoriality.lean, checked source SHA-256
-- 02b714b60c6b88656a0155503911d08df6285283088a22566e92b3331e3dd39f.
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
    ⟨fun x y z => by dsimp only; rw [(hp V).1, map_add],
      fun x z z' => by dsimp only; rw [(hp V).2.1, map_add],
      fun a x z => congrArg g ((hp V).2.2 a x z)⟩
  obtain ⟨k, _, hk⟩ := liftUnique V A _ hq
  exact (hk f h).trans (hk g (fun _ _ => rfl)).symm

-- Proposition 7.6 and Alphabeta Math step 1.1. Use the two formulas over
-- the article’s coefficient field. Since restriction acts by i(a), the
-- R-linearity of f and associativity give balance for every a in R.
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

private noncomputable def evaluateAtOne {V : ModuleCat.{l} R} {W : ModuleCat.{l} S}
    (g : L.obj V ⟶ W) : V ⟶ (ModuleCat.restrictScalars i).obj W := by
  let f : V →ₗ[R] ((ModuleCat.restrictScalars i).obj W : Type l) :=
    { toFun := fun z => g.hom (p V 1 z)
      map_add' := by
        intro x y
        exact (congrArg g.hom ((hp V).2.1 1 x y)).trans (g.hom.map_add _ _)
      map_smul' := by
        intro a z
        change g.hom (p V 1 (a • z)) = i a • g.hom (p V 1 z)
        rw [← (hp V).2.2, one_mul, ← g.hom.map_smul, hpSmul, mul_one] }
  exact ModuleCat.ofHom (R := R) (X := V) (Y := ↑((ModuleCat.restrictScalars i).obj W)) f

-- The article needs the induction half of the portal result. We package the
-- two formulas of step 1.1 with naturality on both variables using the
-- balanced tensor from Proposition 6.3. A direct adjunction here keeps the
-- chosen pure-tensor operations. Rep.indResAdjunction uses coinvariants.
-- ModuleCat.extendRestrictScalarsAdj requires commutative rings, whereas
-- subgroup group algebras can be noncommutative.
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

theorem GroupAlgebraInductionAdjunction : (
∀ (k : Type u) [Field k] (G : Type v) [Group G] (H : Subgroup G),
  let R := MonoidAlgebra k (↥H)
  let S := MonoidAlgebra k G
  let i : RingHom R S := MonoidAlgebra.mapDomainRingHom k (Subgroup.subtype H)
  letI : Module (MulOpposite R) S := Module.compHom S (RingHom.op i)
  let Res := ModuleCat.restrictScalars.{max u v w} i
  let ToRepH : CategoryTheory.Functor (ModuleCat.{max u v w} R) (Rep.{max u v w} k (↥H)) :=
    Rep.ofModuleMonoidAlgebra
  let ToRepG : CategoryTheory.Functor (ModuleCat.{max u v w} S) (Rep.{max u v w} k G) :=
    Rep.ofModuleMonoidAlgebra
  let Balanced := fun (V : ModuleCat.{max u v w} R)
      (A : Type (max u v w)) [AddCommGroup A] (p : AddMonoidHom S (AddMonoidHom V A)) =>
    ∀ (a : R) (x : S) (z : V), p (x * i a) z = p x (a • z)
  Function.Injective i ∧
  (∀ (a : R) (h : ↥H), MonoidAlgebra.coeff (i a) (h : G) = MonoidAlgebra.coeff a h) ∧
  (∀ (a : R) (g : G), g ∉ H → MonoidAlgebra.coeff (i a) g = 0) ∧
  (∀ (a : R) (x : S), MulOpposite.op a • x = x * i a) ∧
  SMulCommClass (MulOpposite R) S S ∧
  (∀ (W : ModuleCat.{max u v w} S) (a : k) (z : W),
    (show W from a • (show ToRepH.obj (Res.obj W) from z)) =
      (show W from a • (show ToRepG.obj W from z))) ∧
  (∀ (W : ModuleCat.{max u v w} S) (h : ↥H) (z : W),
    (show W from Rep.ρ (ToRepH.obj (Res.obj W)) h z) =
      (show W from Rep.ρ (ToRepG.obj W) (h : G) z)) ∧
  ∃ (Ind : CategoryTheory.Functor (ModuleCat.{max u v w} R) (ModuleCat.{max u v w} S))
    (pure : ∀ V : ModuleCat.{max u v w} R, AddMonoidHom S (AddMonoidHom V (Ind.obj V))),
    (∀ V : ModuleCat.{max u v w} R,
      Balanced V (Ind.obj V) (pure V) ∧
      (∀ (A : Type (max u v w)) [AddCommGroup A] (p : AddMonoidHom S (AddMonoidHom V A)),
        Balanced V A p → ∃! f : AddMonoidHom (Ind.obj V) A, ∀ x z, f (pure V x z) = p x z) ∧
      (∀ (s x : S) (z : V), s • pure V x z = pure V (s * x) z) ∧
      (∀ (g : G) (x : S) (z : V),
        (show Ind.obj V from Rep.ρ (ToRepG.obj (Ind.obj V)) g (pure V x z)) =
          pure V (MonoidAlgebra.single g (1 : k) * x) z)) ∧
    (∀ {V V' : ModuleCat.{max u v w} R} (f : Quiver.Hom V V') (x : S) (z : V),
      ModuleCat.Hom.hom (Ind.map f) (pure V x z) = pure V' x (ModuleCat.Hom.hom f z)) ∧
    Nonempty (CategoryTheory.Adjunction Ind Res)
) :=
(by
  intro k _ G _ H
  dsimp only
  let R := MonoidAlgebra k (↥H)
  let S := MonoidAlgebra k G
  let i : R →+* S := MonoidAlgebra.mapDomainRingHom k H.subtype
  have hsub : Function.Injective (H.subtype : ↥H → G) := Subtype.val_injective
  have hsingle (h : ↥H) (a : k) :
      i (MonoidAlgebra.single h a) = MonoidAlgebra.single (h : G) a :=
    MonoidAlgebra.mapDomain_single
  -- Ian X, Abelian Categories and Bimodules, Proposition 7.6, p. 24.
  -- https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=24
  -- The subgroup inclusion has singleton fibers
  -- on the image and empty off it. Associativity gives commuting actions.
  refine ⟨MonoidAlgebra.mapDomain_injective hsub, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a h
    exact Finsupp.mapDomain_apply_of_injective hsub (MonoidAlgebra.coeff a) h
  · intro a g hg
    exact Finsupp.mapDomain_of_notMem_range (MonoidAlgebra.coeff a) g
      (fun ⟨h, hh⟩ => hg (hh ▸ h.property))
  · intro a x
    rfl
  · let rightModule : Module (MulOpposite R) S := Module.compHom S (RingHom.op i)
    exact ⟨fun (a : MulOpposite R) (b x : S) =>
      (show (b * x) * i a.unop = b * (x * i a.unop) from mul_assoc _ _ _)⟩
  · intro W a z
    -- Theorem 7.4’s canonical conversion restricts along a ↦ a[1].
    -- The reviewed RepresentationModuleCorrespondence supplies existential
    -- witnesses. To identify the action of the endpoint’s specified functor,
    -- compute directly from Rep.ofModuleMonoidAlgebra.
    change i (MonoidAlgebra.single (1 : ↥H) a) • z =
      (MonoidAlgebra.single (1 : G) a : S) • z
    rw [hsingle]
    rfl
  · intro W h z
    change i (MonoidAlgebra.single h (1 : k)) • z =
      (MonoidAlgebra.single (h : G) (1 : k) : S) • z
    rw [hsingle]
  · obtain ⟨Ind, p, hp, hLift, hSmul, hMap⟩ :=
      GroupAlgebraInductionAux.tensorForRingMap.{max u v, max u v, w} i
    let pure (V : ModuleCat.{max u v w} R) : S →+ (V →+ Ind.obj V) :=
      AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (p V x) ((hp V).2.1 x))
        (fun x y => AddMonoidHom.ext ((hp V).1 x y))
    refine ⟨Ind, pure, ?_, hMap, GroupAlgebraInductionAux.tensorRestrictAdjunction i hp
      hLift hSmul hMap⟩
    intro V
    refine ⟨(hp V).2.2, ?_, hSmul V, ?_⟩
    · intro A _ q hq
      exact hLift V A (fun x z => q x z)
        ⟨fun x y z => by dsimp only; rw [map_add, AddMonoidHom.add_apply],
        fun x z z' => (q x).map_add z z', hq⟩
    · intro g x z
      exact hSmul V (MonoidAlgebra.single g (1 : k)) x z)
