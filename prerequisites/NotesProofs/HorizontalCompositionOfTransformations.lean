import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.TensorDictionaryCompositionAndIdentities
import NotesProofs.NaturalTransformationsByRegularEvaluation
import NotesProofs.BimoduleTensorFunctoriality

set_option maxHeartbeats 2000000

universe u

namespace NotesHorizontalComposition

open CategoryTheory NotesProofs

variable {R S : Type u} [Ring R] [Ring S]
variable {P Q : Type u}
  [AddCommGroup P] [Module S P] [Module (MulOpposite R) P]
  [SMulCommClass (MulOpposite R) S P]
  [AddCommGroup Q] [Module S Q] [Module (MulOpposite R) Q]
  [SMulCommClass (MulOpposite R) S Q]

private abbrev tensor (P : Type u) [AddCommGroup P] [Module S P]
    [Module (MulOpposite R) P] [SMulCommClass (MulOpposite R) S P] :=
  concreteTensorFunctor (R := R) (S := S) P

private abbrev pure {X : ModuleCat.{u} R} (p : P) (x : X) :
    (tensor (S := S) P).obj X :=
  concretePure (R := R) (M := P) p x

private theorem map_pure {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (p : P) (x : X) :
    (tensor (S := S) P).map f (pure (S := S) p x) = pure (S := S) p (f x) :=
  concreteTensorMap_pure (S := S) f.hom p x

private theorem app_pure (f : BimoduleMap (R := R) (S := S) (M := P) (N := Q))
    (X : ModuleCat.{u} R) (p : P) (x : X) :
    (tensorBimoduleMapNatTrans f).app X (pure (S := S) p x) =
      pure (S := S) (f.val p) x :=
  tensorBimoduleMapComponent_pure f X p x

private theorem tensor_ext {X : ModuleCat.{u} R} {Y : Type u} [AddCommGroup Y]
    (f g : (tensor (S := S) P).obj X →+ Y)
    (h : ∀ p x, f (pure (S := S) p x) = g (pure (S := S) p x)) : f = g :=
  ChoiceFreeWatts.tensorExt rightAction f g h

end NotesHorizontalComposition

theorem HorizontalCompositionOfTransformations : (
∀ (R S T : Type u) [Ring R] [Ring S] [Ring T]
    (B B' C C' : Type u)
    [AddCommGroup B] [Module S B] [Module (MulOpposite R) B]
    [SMulCommClass (MulOpposite R) S B]
    [AddCommGroup B'] [Module S B'] [Module (MulOpposite R) B']
    [SMulCommClass (MulOpposite R) S B']
    [AddCommGroup C] [Module T C] [Module (MulOpposite S) C]
    [SMulCommClass (MulOpposite S) T C]
    [AddCommGroup C'] [Module T C'] [Module (MulOpposite S) C']
    [SMulCommClass (MulOpposite S) T C'],
  let TB := NotesProofs.concreteTensorFunctor (R := R) (S := S) B
  let TB' := NotesProofs.concreteTensorFunctor (R := R) (S := S) B'
  let TC := NotesProofs.concreteTensorFunctor (R := S) (S := T) C
  let TC' := NotesProofs.concreteTensorFunctor (R := S) (S := T) C'
  let CB := CategoryTheory.Functor.obj TC (ModuleCat.of S B)
  let CB' := CategoryTheory.Functor.obj TC' (ModuleCat.of S B')
  let pureCB := fun (c : C) (b : B) =>
    (NotesProofs.concretePure (R := S) (M := C) c b : ModuleCat.carrier CB)
  let pureCB' := fun (c' : C') (b' : B') =>
    (NotesProofs.concretePure (R := S) (M := C') c' b' : ModuleCat.carrier CB')
  ∃ (rightCB : Module (MulOpposite R) (ModuleCat.carrier CB))
    (rightCB' : Module (MulOpposite R) (ModuleCat.carrier CB')),
    letI : Module (MulOpposite R) (ModuleCat.carrier CB) := rightCB
    letI : Module (MulOpposite R) (ModuleCat.carrier CB') := rightCB'
    (∀ (r : R) (c : C) (b : B),
      rightCB.smul (MulOpposite.op r) (pureCB c b) = pureCB c (MulOpposite.op r • b)) ∧
    (∀ (r : R) (c' : C') (b' : B'),
      rightCB'.smul (MulOpposite.op r) (pureCB' c' b') = pureCB' c' (MulOpposite.op r • b')) ∧
    (∃ (commuteCB : SMulCommClass (MulOpposite R) T (ModuleCat.carrier CB))
      (commuteCB' : SMulCommClass (MulOpposite R) T (ModuleCat.carrier CB')),
      letI : SMulCommClass (MulOpposite R) T (ModuleCat.carrier CB) := commuteCB
      letI : SMulCommClass (MulOpposite R) T (ModuleCat.carrier CB') := commuteCB'
      let TCB := NotesProofs.concreteTensorFunctor (R := R) (S := T) (ModuleCat.carrier CB)
      let TCB' := NotesProofs.concreteTensorFunctor (R := R) (S := T) (ModuleCat.carrier CB')
      ∃ (assoc : CategoryTheory.Iso (CategoryTheory.Functor.comp TB TC) TCB)
        (assoc' : CategoryTheory.Iso (CategoryTheory.Functor.comp TB' TC') TCB'),
        (∀ (M : ModuleCat.{u} R) (c : C) (b : B) (m : M),
          (CategoryTheory.NatTrans.app assoc.hom M)
            (NotesProofs.concretePure (R := S) (M := C) c
              (NotesProofs.concretePure (R := R) (M := B) b m)) =
            NotesProofs.concretePure (R := R) (M := ModuleCat.carrier CB) (pureCB c b) m) ∧
        (∀ (M : ModuleCat.{u} R) (c' : C') (b' : B') (m : M),
          (CategoryTheory.NatTrans.app assoc'.hom M)
            (NotesProofs.concretePure (R := S) (M := C') c'
              (NotesProofs.concretePure (R := R) (M := B') b' m)) =
            NotesProofs.concretePure (R := R) (M := ModuleCat.carrier CB') (pureCB' c' b') m) ∧
        (∀ (β : NotesProofs.BimoduleMap (R := R) (S := S) (M := B) (N := B'))
           (γ : NotesProofs.BimoduleMap (R := S) (S := T) (M := C) (N := C')),
          ∃ δ : NotesProofs.BimoduleMap (R := R) (S := T)
              (M := ModuleCat.carrier CB) (N := ModuleCat.carrier CB'),
            (∀ (c : C) (b : B),
              (Subtype.val δ) (pureCB c b) = pureCB' ((Subtype.val γ) c) ((Subtype.val β) b)) ∧
            CategoryTheory.CategoryStruct.comp
                (CategoryTheory.NatTrans.hcomp
                  (NotesProofs.tensorBimoduleMapNatTrans β)
                  (NotesProofs.tensorBimoduleMapNatTrans γ)) assoc'.hom =
              CategoryTheory.CategoryStruct.comp assoc.hom
                (NotesProofs.tensorBimoduleMapNatTrans δ)))
) :=
(by
  -- Ian X, Proposition 10.2 (env-10-2, p. 32).
  -- https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=32
  -- Alphabeta Math, steps 1.1, 1.2 and 2.1.
  -- https://alphabetamath.cc/item/lem-tensoring-defines-a-pseudofunctor-with-interchange
  -- TensorDictionaryCompositionAndIdentities supplies the right actions,
  -- commuting instances, and pure formulas for both comparisons in step 1.2.
  -- Its comparison maps already point from nested to reassociated tensors.
  intro R S T _ _ _ B B' C C' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    TB TB' TC TC' CB CB' pureCB pureCB'
  open CategoryTheory NotesProofs NotesHorizontalComposition in
  obtain ⟨_, rightCB, hr, commute, assoc, ha⟩ :=
    (TensorDictionaryCompositionAndIdentities R).2 S T B C
  obtain ⟨_, rightCB', hr', commute', assoc', ha'⟩ :=
    (TensorDictionaryCompositionAndIdentities R).2 S T B' C'
  let _ : Module (MulOpposite R) CB := rightCB
  let _ : Module (MulOpposite R) CB' := rightCB'
  let _ : SMulCommClass (MulOpposite R) T CB := commute
  let _ : SMulCommClass (MulOpposite R) T CB' := commute'
  refine ⟨rightCB, rightCB', hr, hr', commute, commute', assoc, assoc', ha, ha', ?_⟩
  intro β γ
  -- Use the already descended tensor transformation from step 1.1 and the
  -- concrete functor map. Their composite implements the balanced lift of
  -- (c, b) ↦ γ(c) ⊗ β(b) with its T-linearity built in. The registered
  -- BimoduleTensorFunctoriality gives an existential functor in an additive
  -- functor encoding, so its witnesses do not fix these concrete carriers.
  -- NaturalTransformationsByRegularEvaluation classifies arbitrary tensor
  -- transformations. Here β and γ already specify both transformations.
  let f : CB ⟶ CB' :=
    (tensorBimoduleMapNatTrans γ).app (ModuleCat.of S B) ≫
      TC'.map (ModuleCat.ofHom β.val)
  have hf (c : C) (b : B) : f (pureCB c b) = pureCB' (γ.val c) (β.val b) := by
    change (tensor (R := S) (S := T) C').map (ModuleCat.ofHom β.val)
      ((tensorBimoduleMapNatTrans γ).app (ModuleCat.of S B)
        (NotesHorizontalComposition.pure (S := T) c b)) = _
    rw [app_pure, NotesHorizontalComposition.map_pure]
    rfl
  have hright (r : R) (z : CB) :
      f (MulOpposite.op r • z) = MulOpposite.op r • f z := by
    let sourceAction : CB →+ CB := AddMonoidHom.mk' (MulOpposite.op r • ·) (smul_add _)
    let targetAction : CB' →+ CB' := AddMonoidHom.mk' (MulOpposite.op r • ·) (smul_add _)
    have h : f.hom.toAddMonoidHom.comp sourceAction =
        targetAction.comp f.hom.toAddMonoidHom := by
      apply tensor_ext (S := T) (P := C) (X := ModuleCat.of S B)
      intro c b
      change f (rightCB.smul (MulOpposite.op r) (pureCB c b)) =
        rightCB'.smul (MulOpposite.op r) (f (pureCB c b))
      rw [hr, hf, hf, hr', β.property]
    exact DFunLike.congr_fun h z
  let δ : BimoduleMap (R := R) (S := T) (M := CB.carrier) (N := CB'.carrier) :=
    ⟨f.hom, hright⟩
  refine ⟨δ, hf, ?_⟩
  -- Step 2.1 uses the generator computation in each variable of the
  -- iterated tensor. Mathlib's horizontal component applies γ first and
  -- then the image of β under TC'. The article uses the other order,
  -- which yields the same pure tensor by the two component formulas.
  apply NatTrans.ext
  funext M
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply tensor_ext (S := T) (P := C) (X := TB.obj M)
  intro c z
  let left := ((tensorBimoduleMapNatTrans β ◫ tensorBimoduleMapNatTrans γ) ≫ assoc'.hom).app M
  let right := (assoc.hom ≫ tensorBimoduleMapNatTrans δ).app M
  let pc : TB.obj M →+ (TB ⋙ TC).obj M := concretePure (R := S) (M := C) c
  have h : left.hom.toAddMonoidHom.comp pc = right.hom.toAddMonoidHom.comp pc := by
    apply tensor_ext (S := S) (P := B) (X := M)
    intro b m
    change left (pc (NotesHorizontalComposition.pure (S := S) b m)) =
      right (pc (NotesHorizontalComposition.pure (S := S) b m))
    dsimp only [left, right, NatTrans.comp_app]
    rw [NatTrans.hcomp_app]
    change (assoc'.hom.app M)
        (TC'.map ((tensorBimoduleMapNatTrans β).app M)
          ((tensorBimoduleMapNatTrans γ).app (TB.obj M)
            (NotesHorizontalComposition.pure (S := T) c
              (NotesHorizontalComposition.pure (S := S) b m)))) =
      (tensorBimoduleMapNatTrans δ).app M
        ((assoc.hom.app M)
          (NotesHorizontalComposition.pure (S := T) c (NotesHorizontalComposition.pure (S := S) b m)))
    rw [app_pure, NotesHorizontalComposition.map_pure, app_pure, ha', ha]
    exact (congrArg (fun p : CB'.carrier => concretePure (R := R) (M := CB'.carrier) p m)
      (hf c b).symm).trans (app_pure δ M (pureCB c b) m).symm
  exact DFunLike.congr_fun h z)
