import MackeyDiagrams
import NotesProofs.ConcreteTensorBimoduleMap
import NotesProofs.WattsMathlibReverse
import NotesProofs.General.OriginalBimoduleAdapter
import NotesProofs.ClassicalReconstruction
import NotesProofs.BimoduleTensorFunctoriality

set_option maxHeartbeats 2000000

theorem RegularModuleTensorUnits : (
∀ (R : Type u) [Ring R],
  let regularRight := fun (r x : R) => x * r
  let LeftTensor := fun (M : ModuleCat.{v} R) => ChoiceFreeWatts.Tensor regularRight M
  letI _leftAdd (M : ModuleCat.{v} R) : AddCommGroup (LeftTensor M) :=
    ChoiceFreeWatts.tensorAddCommGroup (X := M) regularRight
  letI _leftModule (M : ModuleCat.{v} R) : Module R (LeftTensor M) :=
    ChoiceFreeWatts.outerModule (X := M) regularRight (fun (r a x : R) => mul_assoc a x r)
  let leftPure := fun (M : ModuleCat.{v} R) (r : R) (m : M) =>
    (ChoiceFreeWatts.pure regularRight r m : LeftTensor M)
  let RightMod := ModuleCat.{w} (MulOpposite R)
  let right := fun (B : RightMod) (r : R) (b : B) => MulOpposite.op r • b
  let RightTensor := fun (B : RightMod) => ChoiceFreeWatts.Tensor (right B) R
  letI _rightAdd (B : RightMod) : AddCommGroup (RightTensor B) :=
    ChoiceFreeWatts.tensorAddCommGroup (X := R) (right B)
  let rightPure := fun (B : RightMod) (b : B) (r : R) =>
    (ChoiceFreeWatts.pure (right B) b r : RightTensor B)
  (∃ leftUnit : ∀ M : ModuleCat.{v} R, LinearEquiv (RingHom.id R) (LeftTensor M) M,
    (∀ (M : ModuleCat.{v} R) (r : R) (m : M),
      leftUnit M (leftPure M r m) = r • m) ∧
    (∀ {M N : ModuleCat.{v} R} (f : Quiver.Hom M N),
      ∃ tf : LinearMap (RingHom.id R) (LeftTensor M) (LeftTensor N),
        (∀ (r : R) (m : M), tf (leftPure M r m) = leftPure N r (f m)) ∧
        (∀ z : LeftTensor M, leftUnit N (tf z) = f (leftUnit M z)))) ∧
  (∃ rightModule : ∀ B : RightMod, Module (MulOpposite R) (RightTensor B),
    letI _rightModuleInstance (B : RightMod) : Module (MulOpposite R) (RightTensor B) :=
      rightModule B
    ∃ rightUnit : ∀ B : RightMod, LinearEquiv (RingHom.id (MulOpposite R)) (RightTensor B) B,
      (∀ (B : RightMod) (b : B) (r : R), rightUnit B (rightPure B b r) = right B r b) ∧
      (∀ (B : RightMod) (a r : R) (b : B),
        MulOpposite.op a • rightPure B b r = rightPure B b (r * a)) ∧
      (∀ {B C : RightMod} (g : Quiver.Hom B C),
        ∃ tg : LinearMap (RingHom.id (MulOpposite R)) (RightTensor B) (RightTensor C),
          (∀ (b : B) (r : R), tg (rightPure B b r) = rightPure C (g b) r) ∧
          (∀ z : RightTensor B, rightUnit C (tg z) = g (rightUnit B z))) ∧
      (∀ (S : Type s) [Ring S] (B : RightMod) [Module S B]
          [SMulCommClass (MulOpposite R) S B],
        letI : Module S (RightTensor B) :=
          ChoiceFreeWatts.outerModule (X := R) (right B)
            (fun (r : R) (a : S) (b : B) => smul_comm (MulOpposite.op r) a b)
        SMulCommClass (MulOpposite R) S (RightTensor B) ∧
        (∀ (a : S) (z : RightTensor B), rightUnit B (a • z) = a • rightUnit B z)))
) :=
(by
  intro R _ regularRight LeftTensor leftPure RightMod right RightTensor rightPure
  let leftAdd (M : ModuleCat.{v} R) : AddCommGroup (LeftTensor M) :=
    ChoiceFreeWatts.tensorAddCommGroup (X := M) regularRight
  let leftModule (M : ModuleCat.{v} R) : Module R (LeftTensor M) :=
    ChoiceFreeWatts.outerModule (X := M) regularRight (fun (r a x : R) => mul_assoc a x r)
  let rightAdd (B : RightMod) : AddCommGroup (RightTensor B) :=
    ChoiceFreeWatts.tensorAddCommGroup (X := R) (right B)
  -- Ian X, Theorem 6.4, p. 19.
  -- https://getcurious.cc/downloads/abelian-categories-and-bimodules-lecture-notes.pdf#page=19
  -- Alphabeta Math, steps 1.1–4.1.
  -- https://alphabetamath.cc/item/thm-unit-isomorphisms-for-module-tensor-products
  -- BimoduleTensorFunctoriality supplies a categorical existence theorem with
  -- lifted carriers. Here the endpoint fixes the unlifted quotient and independent
  -- universes. Use its underlying WattsSupport lifts and pure-tensor extensionality
  -- directly on that quotient. The checked NotesProofs/WattsSupport.lean
  -- (SHA-256 853d1dd0016bf0735f7a84559e2f1cbbb701fc3cb0e00395a0e138ffecb1f967)
  -- supplies pureBalanced, tensorLift, tensorLift_pure, tensorLinearLift,
  -- tensorLinearLift_pure, tensorExt, tensorAddCommGroup, and outerModule.
  -- The common-universe ConcreteTensorUnitor uses ULift on the regular factor.
  -- The balance calculations below use literal R in that factor.
  constructor
  · -- Steps 1.1 and 3.1: balance uses mul_smul, which also gives outer linearity.
    have comm (r a x : R) : regularRight r (a • x) = a • regularRight r x :=
      mul_assoc a x r
    have balanced (M : ModuleCat.{v} R) :
        ChoiceFreeWatts.Balanced regularRight (fun (r : R) (m : M) => r • m) :=
      ⟨fun r s m => add_smul r s m, fun r m n => smul_add r m n,
        fun a r m => mul_smul r a m⟩
    let eval (M : ModuleCat.{v} R) : LeftTensor M →ₗ[R] M :=
      ChoiceFreeWatts.tensorLinearLift regularRight comm (fun r m => r • m)
        (balanced M) (fun a r m => mul_smul a r m)
    have eval_pure (M : ModuleCat.{v} R) (r : R) (m : M) :
        eval M (leftPure M r m) = r • m :=
      ChoiceFreeWatts.tensorLinearLift_pure regularRight comm _ (balanced M) _ r m
    -- Step 2.1: insertion of one is additive and its composite with evaluation
    -- is tested on the pure generators by tensorExt.
    let insert (M : ModuleCat.{v} R) : M →+ LeftTensor M :=
      AddMonoidHom.mk' (leftPure M 1) ((ChoiceFreeWatts.pureBalanced regularRight).2.1 1)
    have insert_eval (M : ModuleCat.{v} R) (z : LeftTensor M) :
        insert M (eval M z) = z := by
      have h : (insert M).comp (eval M).toAddMonoidHom = AddMonoidHom.id _ := by
        apply ChoiceFreeWatts.tensorExt regularRight
        intro r m
        change leftPure M 1 (eval M (leftPure M r m)) = leftPure M r m
        rw [eval_pure]
        simpa only [regularRight, one_mul] using
          ((ChoiceFreeWatts.pureBalanced (X := M) regularRight).2.2 r 1 m).symm
      exact DFunLike.congr_fun h z
    let unit (M : ModuleCat.{v} R) : LeftTensor M ≃ₗ[R] M :=
      { eval M with
        invFun := insert M
        left_inv := insert_eval M
        right_inv := fun m => (eval_pure M 1 m).trans (one_smul R m) }
    refine ⟨unit, eval_pure, ?_⟩
    -- The article's naturality square is witnessed by conjugating each module
    -- morphism by the unit. Its pure formula follows from linearity and evaluation.
    intro M N f
    let tf := (unit N).symm.toLinearMap.comp (f.hom.comp (unit M).toLinearMap)
    refine ⟨tf, ?_, ?_⟩
    · intro r m
      apply (unit N).injective
      change unit N ((unit N).symm (f (unit M (leftPure M r m)))) =
        unit N (leftPure N r (f m))
      rw [LinearEquiv.apply_symm_apply]
      change f (eval M (leftPure M r m)) = eval N (leftPure N r (f m))
      rw [eval_pure, eval_pure]
      exact f.hom.map_smul r m
    · intro z
      exact (unit N).apply_symm_apply (f (unit M z))
  · -- Step 1.2: op a acts as right multiplication by a. Hence evaluation
    -- on ((b a), r) uses op r * op a = op (a * r).
    have balanced (B : RightMod) : ChoiceFreeWatts.Balanced (right B)
        (fun (b : B) (r : R) => right B r b) := by
      refine ⟨fun b c r => smul_add (MulOpposite.op r) b c, ?_, ?_⟩
      · intro b r t
        exact add_smul (MulOpposite.op r) (MulOpposite.op t) b
      · intro a b r
        exact (mul_smul (MulOpposite.op r) (MulOpposite.op a) b).symm
    let eval (B : RightMod) : RightTensor B →+ B :=
      ChoiceFreeWatts.tensorLift (right B) (fun b r => right B r b) (balanced B)
    have eval_pure (B : RightMod) (b : B) (r : R) :
        eval B (rightPure B b r) = right B r b :=
      ChoiceFreeWatts.tensorLift_pure (right B) _ (balanced B) b r
    let insert (B : RightMod) : B →+ RightTensor B :=
      AddMonoidHom.mk' (fun b => rightPure B b 1)
        (fun b c => (ChoiceFreeWatts.pureBalanced (X := R) (right B)).1 b c 1)
    have insert_eval (B : RightMod) (z : RightTensor B) :
        insert B (eval B z) = z := by
      have h : (insert B).comp (eval B) = AddMonoidHom.id _ := by
        apply ChoiceFreeWatts.tensorExt (right B)
        intro b r
        change rightPure B (eval B (rightPure B b r)) 1 = rightPure B b r
        rw [eval_pure]
        simpa only [smul_eq_mul, mul_one] using
          (ChoiceFreeWatts.pureBalanced (X := R) (right B)).2.2 r b (1 : R)
      exact DFunLike.congr_fun h z
    let equiv (B : RightMod) : RightTensor B ≃+ B :=
      { eval B with
        invFun := insert B
        left_inv := insert_eval B
        right_inv := fun b => (eval_pure B b 1).trans (one_smul (MulOpposite R) b) }
    -- Step 3.1: transfer the right action across the additive isomorphism.
    -- Its pure formula identifies it with right multiplication on the second
    -- factor. This implements the action on the particular reviewed quotient.
    let rightModule (B : RightMod) : Module (MulOpposite R) (RightTensor B) :=
      (equiv B).module (MulOpposite R)
    let unit (B : RightMod) : RightTensor B ≃ₗ[MulOpposite R] B :=
      (equiv B).linearEquiv (MulOpposite R)
    refine ⟨rightModule, unit, eval_pure, ?_, ?_, ?_⟩
    · intro B a r b
      apply (unit B).injective
      rw [(unit B).map_smul]
      change MulOpposite.op a • eval B (rightPure B b r) =
        eval B (rightPure B b (r * a))
      rw [eval_pure, eval_pure]
      exact (mul_smul (MulOpposite.op a) (MulOpposite.op r) b).symm
    · -- As on the left, conjugation proves the naturality square at every tensor.
      intro B C g
      let tg := (unit C).symm.toLinearMap.comp (g.hom.comp (unit B).toLinearMap)
      refine ⟨tg, ?_, ?_⟩
      · intro b r
        apply (unit C).injective
        change unit C ((unit C).symm (g (unit B (rightPure B b r)))) =
          unit C (rightPure C (g b) r)
        rw [LinearEquiv.apply_symm_apply, show unit B (rightPure B b r) = right B r b
          from eval_pure B b r, show unit C (rightPure C (g b) r) = right C r (g b)
          from eval_pure C (g b) r]
        exact g.hom.map_smul (MulOpposite.op r) b
      · intro z
        exact (unit C).apply_symm_apply (g (unit B z))
    · -- Steps 3.1 and 4.1: the bimodule hypothesis makes the pairing S-linear.
      -- Compare its S-linear lift with evaluation on generators. Injectivity of
      -- the right unit then carries commutation of the two actions back to tensors.
      intro S _ B _ _
      let commute (r : R) (a : S) (b : B) :
          right B r (a • b) = a • right B r b :=
        smul_comm (MulOpposite.op r) a b
      let : Module S (RightTensor B) :=
        ChoiceFreeWatts.outerModule (X := R) (right B) commute
      let outerEval : RightTensor B →ₗ[S] B :=
        ChoiceFreeWatts.tensorLinearLift (right B) commute
          (fun b r => right B r b) (balanced B) (fun a b r => commute r a b)
      have eval_eq : outerEval.toAddMonoidHom = eval B :=
        ChoiceFreeWatts.tensorExt (right B) _ _ (fun b r =>
          (ChoiceFreeWatts.tensorLinearLift_pure (right B) commute _
            (balanced B) (fun a b r => commute r a b) b r).trans (eval_pure B b r).symm)
      have outer_smul (a : S) (z : RightTensor B) : unit B (a • z) = a • unit B z := by
        change eval B (a • z) = a • eval B z
        rw [← eval_eq]
        exact outerEval.map_smul a z
      refine ⟨⟨?_⟩, outer_smul⟩
      intro a c z
      apply (unit B).injective
      rw [(unit B).map_smul, outer_smul, outer_smul, (unit B).map_smul]
      exact smul_comm a c (unit B z)
)

#print axioms RegularModuleTensorUnits
