import MackeyDiagrams
import Proofs.ModuleTensorUniversalProperty

set_option maxHeartbeats 2000000

namespace BalancedTensorAssoc

noncomputable section

variable {R S C M N P A M' N' P' : Type*}
variable [Ring R] [Ring S]
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup A]

private abbrev generator (m : M) (n : N) : (M × N) →₀ ℤ :=
  Finsupp.single (m, n) 1

private abbrev relations (R : Type*) [Ring R] (M N : Type*)
    [AddCommGroup M] [AddCommGroup N] [Module (Rᵐᵒᵖ) M] [Module R N] :
    AddSubgroup ((M × N) →₀ ℤ) :=
  AddSubgroup.closure
    { z | (∃ (m m' : M) (n : N),
          z = generator (m + m') n - generator m n - generator m' n) ∨
        (∃ (m : M) (n n' : N),
          z = generator m (n + n') - generator m n - generator m n') ∨
        (∃ (r : R) (m : M) (n : N),
          z = generator (MulOpposite.op r • m) n - generator m (r • n)) }

private abbrev Tensor (R : Type*) [Ring R] (M N : Type*)
    [AddCommGroup M] [AddCommGroup N] [Module (Rᵐᵒᵖ) M] [Module R N] :=
  HasQuotient.Quotient ((M × N) →₀ ℤ) (relations R M N)

variable [Module (Rᵐᵒᵖ) M] [Module R N] [Module (Sᵐᵒᵖ) N] [Module S P]

private abbrev pure (R : Type*) [Ring R] {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module (Rᵐᵒᵖ) M] [Module R N]
    (m : M) (n : N) : Tensor R M N :=
  QuotientAddGroup.mk' (relations R M N) (generator m n)

private theorem pure_add_left (m m' : M) (n : N) :
    pure R (m + m') n = pure R m n + pure R m' n :=
  (ModuleTensorUniversalProperty.{_, _, _, 0} R M N).1.1 m m' n

private theorem pure_add_right (m : M) (n n' : N) :
    pure R m (n + n') = pure R m n + pure R m n' :=
  (ModuleTensorUniversalProperty.{_, _, _, 0} R M N).1.2.1 m n n'

private theorem pure_balance (r : R) (m : M) (n : N) :
    pure R (MulOpposite.op r • m) n = pure R m (r • n) :=
  (ModuleTensorUniversalProperty.{_, _, _, 0} R M N).1.2.2 r m n

private abbrev additive {B : Type*} [AddZeroClass B] (f : B → A)
    (hf : ∀ x y, f (x + y) = f x + f y) : B →+ A where
  toFun := f
  map_add' := hf
  map_zero' := by
    have h := hf 0 0
    rw [zero_add] at h
    exact (add_left_cancel (show f 0 + 0 = f 0 + f 0 by rw [add_zero]; exact h)).symm

private def pureLeft (n : N) : M →+ Tensor R M N :=
  additive (fun m => pure R m n) (fun m m' => pure_add_left m m' n)

private def pureRight (m : M) : N →+ Tensor R M N :=
  additive (pure R m) (pure_add_right m)

private theorem liftExists (f : M × N → A)
    (hl : ∀ m m' n, f (m + m', n) = f (m, n) + f (m', n))
    (hr : ∀ m n n', f (m, n + n') = f (m, n) + f (m, n'))
    (hb : ∀ (r : R) m n, f (MulOpposite.op r • m, n) = f (m, r • n)) :
    ∃! F : Tensor R M N →+ A, ∀ m n, F (pure R m n) = f (m, n) :=
  ((ModuleTensorUniversalProperty R M N).2 A).1 ⟨f, hl, hr, hb⟩

-- Alphabeta Math, thm-associativity-of-balanced-tensor-products.
-- https://alphabetamath.cc/item/thm-associativity-of-balanced-tensor-products
-- The coordinator's quotient adapters are definitional: the curried generator
-- here has the same pair of indices and the same three subgroup generators.
-- The registered universal property already performs the free additive extension
-- and quotient descent in Proofs.ModuleTensorUniversalProperty. This
-- endpoint allows classical choice, which extracts the unique lifts below.
private def descend (f : M →+ N →+ A)
    (hb : ∀ (r : R) m n, f (MulOpposite.op r • m) n = f m (r • n)) :
    Tensor R M N →+ A :=
  Classical.choose (liftExists (fun p => f p.1 p.2)
    (fun m m' n => DFunLike.congr_fun (map_add f m m') n)
    (fun m n n' => map_add (f m) n n') hb)

private theorem descend_pure (f : M →+ N →+ A)
    (hb : ∀ (r : R) m n, f (MulOpposite.op r • m) n = f m (r • n)) (m : M) (n : N) :
    descend f hb (pure R m n) = f m n :=
  (Classical.choose_spec (liftExists (fun p => f p.1 p.2)
    (fun m m' n => DFunLike.congr_fun (map_add f m m') n)
    (fun m n n' => map_add (f m) n n') hb)).1 m n

private theorem hom_ext (f g : Tensor R M N →+ A)
    (h : ∀ m n, f (pure R m n) = g (pure R m n)) : f = g := by
  obtain ⟨F, _, unique⟩ := liftExists (fun p => g (pure R p.1 p.2))
    (fun m m' n => by rw [pure_add_left, map_add])
    (fun m n n' => by rw [pure_add_right, map_add])
    (fun r m n => by rw [pure_balance])
  exact (unique f h).trans (unique g (fun _ _ => rfl)).symm

variable [AddCommGroup M'] [AddCommGroup N'] [Module (Rᵐᵒᵖ) M'] [Module R N']

private def tensorMap (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') :
    Tensor R M N →+ Tensor R M' N' :=
  descend
    (additive (fun m => (pureRight (R := R) (f m)).comp g.toAddMonoidHom)
      (fun m m' => AddMonoidHom.ext fun n => by
        change pure R (f (m + m')) (g n) = pure R (f m) (g n) + pure R (f m') (g n)
        rw [map_add, pure_add_left]))
    (fun r m n => by
      change pure R (f (MulOpposite.op r • m)) (g n) = pure R (f m) (g (r • n))
      rw [map_smul, map_smul, pure_balance])

private theorem tensorMap_pure (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N')
    (m : M) (n : N) :
    tensorMap f g (pure R m n) = pure R (f m) (g n) := by
  rw [tensorMap, descend_pure]
  rfl

section OuterAction

variable [Ring C]

private def scalarMap (T B : Type*) [Ring T] [AddCommGroup B] [Module T B] [Module C B]
    [SMulCommClass C T B] (c : C) : B →ₗ[T] B where
  toFun b := c • b
  map_add' := smul_add c
  map_smul' t b := smul_comm c t b

@[instance_reducible] private def moduleFromMaps {B : Type*} [AddCommGroup B] (f : C → B →+ B)
    (one : f 1 = AddMonoidHom.id B)
    (mul : ∀ c d, f (c * d) = (f c).comp (f d))
    (add : ∀ c d, f (c + d) = f c + f d)
    (zero : f 0 = 0) : Module C B where
  smul c b := f c b
  one_smul b := DFunLike.congr_fun one b
  mul_smul c d b := DFunLike.congr_fun (mul c d) b
  smul_zero c := map_zero (f c)
  smul_add c := map_add (f c)
  add_smul c d b := DFunLike.congr_fun (add c d) b
  zero_smul b := DFunLike.congr_fun zero b

-- The portal assumes the two inner actions in L1. We construct them, including
-- the module laws, by descending the commuting scalar maps and testing on pairs.
@[instance_reducible] private def leftModule [Module C M] [SMulCommClass C (Rᵐᵒᵖ) M] :
    Module C (Tensor R M N) :=
  moduleFromMaps (fun c => tensorMap (scalarMap (Rᵐᵒᵖ) M c) (LinearMap.id (R := R)))
    (hom_ext _ _ fun m n => by
      rw [tensorMap_pure]
      change pure R ((1 : C) • m) n = pure R m n
      rw [one_smul])
    (fun c d => hom_ext _ _ fun m n => by
      rw [tensorMap_pure, AddMonoidHom.comp_apply, tensorMap_pure, tensorMap_pure]
      change pure R ((c * d) • m) n = pure R (c • d • m) n
      rw [mul_smul])
    (fun c d => hom_ext _ _ fun m n => by
      rw [tensorMap_pure, AddMonoidHom.add_apply, tensorMap_pure, tensorMap_pure]
      change pure R ((c + d) • m) n = pure R (c • m) n + pure R (d • m) n
      rw [add_smul, pure_add_left])
    (hom_ext _ _ fun m n => by
      rw [tensorMap_pure]
      change pure R ((0 : C) • m) n = 0
      rw [zero_smul]
      exact map_zero (pureLeft n))

private theorem leftModule_pure [Module C M] [SMulCommClass C (Rᵐᵒᵖ) M]
    (c : C) (m : M) (n : N) :
    (leftModule (C := C) (R := R) (M := M) (N := N)).smul c (pure R m n) =
      pure R (c • m) n :=
  tensorMap_pure _ _ m n

@[instance_reducible] private def rightModule [Module C N] [SMulCommClass C R N] :
    Module C (Tensor R M N) :=
  moduleFromMaps (fun c => tensorMap (LinearMap.id (R := Rᵐᵒᵖ)) (scalarMap R N c))
    (hom_ext _ _ fun m n => by
      rw [tensorMap_pure]
      change pure R m ((1 : C) • n) = pure R m n
      rw [one_smul])
    (fun c d => hom_ext _ _ fun m n => by
      rw [tensorMap_pure, AddMonoidHom.comp_apply, tensorMap_pure, tensorMap_pure]
      change pure R m ((c * d) • n) = pure R m (c • d • n)
      rw [mul_smul])
    (fun c d => hom_ext _ _ fun m n => by
      rw [tensorMap_pure, AddMonoidHom.add_apply, tensorMap_pure, tensorMap_pure]
      change pure R m ((c + d) • n) = pure R m (c • n) + pure R m (d • n)
      rw [add_smul, pure_add_right])
    (hom_ext _ _ fun m n => by
      rw [tensorMap_pure]
      change pure R m ((0 : C) • n) = 0
      rw [zero_smul]
      exact map_zero (pureRight m))

private theorem rightModule_pure [Module C N] [SMulCommClass C R N]
    (c : C) (m : M) (n : N) :
    (rightModule (C := C) (R := R) (M := M) (N := N)).smul c (pure R m n) =
      pure R m (c • n) :=
  tensorMap_pure _ _ m n

end OuterAction

section Triple

variable [Module (Sᵐᵒᵖ) (Tensor R M N)] [Module R (Tensor S N P)]

private abbrev LeftTensor (R S : Type*) [Ring R] [Ring S] (M N P : Type*)
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module (Rᵐᵒᵖ) M] [Module R N] [Module (Sᵐᵒᵖ) (Tensor R M N)] [Module S P] :=
  Tensor S (Tensor R M N) P

private abbrev RightTensor (R S : Type*) [Ring R] [Ring S] (M N P : Type*)
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module (Rᵐᵒᵖ) M] [Module (Sᵐᵒᵖ) N] [Module S P] [Module R (Tensor S N P)] :=
  Tensor R M (Tensor S N P)

private abbrev leftPure (m : M) (n : N) (p : P) : LeftTensor R S M N P :=
  pure S (pure R m n) p

private abbrev rightPure (m : M) (n : N) (p : P) : RightTensor R S M N P :=
  pure R m (pure S n p)

private abbrev LeftActionLaw (R S M N : Type*) [Ring R] [Ring S]
    [AddCommGroup M] [AddCommGroup N] [Module (Rᵐᵒᵖ) M] [Module R N]
    [Module (Sᵐᵒᵖ) N] [Module (Sᵐᵒᵖ) (Tensor R M N)] :=
  ∀ (s : S) (m : M) (n : N), MulOpposite.op s • pure R m n =
    pure R m (MulOpposite.op s • n)

private abbrev RightActionLaw (R S N P : Type*) [Ring R] [Ring S]
    [AddCommGroup N] [AddCommGroup P] [Module (Sᵐᵒᵖ) N] [Module S P]
    [Module R N] [Module R (Tensor S N P)] :=
  ∀ (r : R) (n : N) (p : P), r • pure S n p = pure S (r • n) p

private structure TriplePairing (R S M N P A : Type*) [Ring R] [Ring S]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup A]
    [Module (Rᵐᵒᵖ) M] [Module R N] [Module (Sᵐᵒᵖ) N] [Module S P] where
  run : M → N → P → A
  add_first : ∀ m m' n p, run (m + m') n p = run m n p + run m' n p
  add_middle : ∀ m n n' p, run m (n + n') p = run m n p + run m n' p
  add_last : ∀ m n p p', run m n (p + p') = run m n p + run m n p'
  balance_R : ∀ (r : R) m n p, run (MulOpposite.op r • m) n p = run m (r • n) p
  balance_S : ∀ (s : S) m n p, run m (MulOpposite.op s • n) p = run m n (s • p)

variable {f : TriplePairing R S M N P A}

-- Step 1.1 first descends the R-balanced pairing, with P →+ A as
-- target. This keeps additivity in p bundled before the second descent.
private def leftInner (f : TriplePairing R S M N P A) : Tensor R M N →+ (P →+ A) :=
  descend
    (additive (fun m => additive (fun n => additive (f.run m n) (f.add_last m n))
      (fun n n' => AddMonoidHom.ext fun p => f.add_middle m n n' p))
      (fun m m' => AddMonoidHom.ext fun n => AddMonoidHom.ext fun p => f.add_first m m' n p))
    (fun r m n => AddMonoidHom.ext fun p => f.balance_R r m n p)

omit [Module (Sᵐᵒᵖ) (Tensor R M N)] [Module R (Tensor S N P)] in
private theorem leftInner_pure (m : M) (n : N) (p : P) :
    leftInner f (pure R m n) p = f.run m n p := by
  rw [leftInner, descend_pure]
  rfl

-- Step 2.1 compares two additive maps on MN to verify S-balance.
private def leftLift (hL : LeftActionLaw R S M N) (f : TriplePairing R S M N P A) :
    LeftTensor R S M N P →+ A :=
  descend (leftInner f) (fun s x p => by
    let e : Tensor R M N →+ A :=
      ((AddMonoidHom.eval p).comp (leftInner f)).comp
        (DistribSMul.toAddMonoidHom _ (MulOpposite.op s))
    let g : Tensor R M N →+ A := (AddMonoidHom.eval (s • p)).comp (leftInner f)
    have eq : e = g := hom_ext _ _ fun m n => by
      change leftInner f (MulOpposite.op s • pure R m n) p = leftInner f (pure R m n) (s • p)
      rw [hL, leftInner_pure, leftInner_pure]
      exact f.balance_S s m n p
    exact DFunLike.congr_fun eq x)

private theorem leftLift_pure (hL : LeftActionLaw R S M N)
    (m : M) (n : N) (p : P) :
    leftLift hL f (leftPure m n p) = f.run m n p := by
  unfold leftLift
  exact (descend_pure _ _ (pure R m n) p).trans (leftInner_pure m n p)

-- Steps 1.2 and 2.2 first descend the S-balanced pairing for each m.
-- Extensionality on N ⊗ P proves additivity in m and R-balance.
private def rightInner (f : TriplePairing R S M N P A) (m : M) : Tensor S N P →+ A :=
  descend (additive (fun n => additive (f.run m n) (f.add_last m n))
    (fun n n' => AddMonoidHom.ext fun p => f.add_middle m n n' p))
    (f.balance_S · m)

omit [Module (Sᵐᵒᵖ) (Tensor R M N)] [Module R (Tensor S N P)] in
private theorem rightInner_pure (m : M) (n : N) (p : P) :
    rightInner f m (pure S n p) = f.run m n p := by
  unfold rightInner
  exact descend_pure _ _ n p

private def rightLift (hT : RightActionLaw R S N P) (f : TriplePairing R S M N P A) :
    RightTensor R S M N P →+ A :=
  descend (additive (rightInner f) (fun m m' => hom_ext _ _ fun n p => by
    rw [AddMonoidHom.add_apply, rightInner_pure, rightInner_pure, rightInner_pure]
    exact f.add_first m m' n p)) (fun r m y => by
    let g := (rightInner f m).comp (DistribSMul.toAddMonoidHom _ r)
    have eq : rightInner f (MulOpposite.op r • m) = g := hom_ext _ _ fun n p => by
      change rightInner f (MulOpposite.op r • m) (pure S n p) = rightInner f m (r • pure S n p)
      rw [hT, rightInner_pure, rightInner_pure]
      exact f.balance_R r m n p
    exact DFunLike.congr_fun eq y)

private theorem rightLift_pure (hT : RightActionLaw R S N P)
    (m : M) (n : N) (p : P) :
    rightLift hT f (rightPure m n p) = f.run m n p := by
  unfold rightLift
  exact (descend_pure _ _ m (pure S n p)).trans (rightInner_pure m n p)

omit [Module (Sᵐᵒᵖ) N] [Module R (Tensor S N P)] in
private theorem left_ext (f g : LeftTensor R S M N P →+ A)
    (h : ∀ m n p, f (leftPure m n p) = g (leftPure m n p)) : f = g := by
  apply hom_ext
  intro x p
  exact DFunLike.congr_fun (hom_ext (f.comp (pureLeft p)) (g.comp (pureLeft p))
    (fun m n => h m n p)) x

omit [Module R N] [Module (Sᵐᵒᵖ) (Tensor R M N)] in
private theorem right_ext (f g : RightTensor R S M N P →+ A)
    (h : ∀ m n p, f (rightPure m n p) = g (rightPure m n p)) : f = g := by
  apply hom_ext
  intro m y
  exact DFunLike.congr_fun (hom_ext (f.comp (pureRight m)) (g.comp (pureRight m))
    (fun n p => h m n p)) y

private def leftPairing (hL : LeftActionLaw R S M N) :
    TriplePairing R S M N P (LeftTensor R S M N P) where
  run := leftPure
  add_first m m' n p := by rw [leftPure, leftPure, leftPure, pure_add_left, pure_add_left]
  add_middle m n n' p := by rw [leftPure, leftPure, leftPure, pure_add_right, pure_add_left]
  add_last m n p p' := pure_add_right (pure R m n) p p'
  balance_R r m n p := congrArg (fun x => pure S x p) (pure_balance r m n)
  balance_S s m n p := by rw [leftPure, leftPure, ← hL, pure_balance]

private def rightPairing (hT : RightActionLaw R S N P) :
    TriplePairing R S M N P (RightTensor R S M N P) where
  run := rightPure
  add_first m m' n p := pure_add_left m m' (pure S n p)
  add_middle m n n' p := by rw [rightPure, rightPure, rightPure, pure_add_left, pure_add_right]
  add_last m n p p' := by rw [rightPure, rightPure, rightPure, pure_add_right, pure_add_right]
  balance_R r m n p := by rw [rightPure, rightPure, ← hT, pure_balance]
  balance_S s m n p := congrArg (pure R m) (pure_balance s n p)

-- Step 3.1 uses the two descents twice for extensionality on pure triples.
private def reassoc (hL : LeftActionLaw R S M N) (hT : RightActionLaw R S N P) :
    LeftTensor R S M N P ≃+ RightTensor R S M N P :=
  let f := leftLift hL (rightPairing hT)
  let g := rightLift hT (leftPairing hL)
  have fg : f.comp g = AddMonoidHom.id _ := right_ext _ _ fun m n p => by
    change f (g (rightPure m n p)) = rightPure m n p
    rw [show g (rightPure m n p) = leftPure m n p from rightLift_pure hT m n p]
    exact leftLift_pure hL m n p
  have gf : g.comp f = AddMonoidHom.id _ := left_ext _ _ fun m n p => by
    change g (f (leftPure m n p)) = leftPure m n p
    rw [show f (leftPure m n p) = rightPure m n p from leftLift_pure hL m n p]
    exact rightLift_pure hT m n p
  { toFun := f
    invFun := g
    left_inv := DFunLike.congr_fun gf
    right_inv := DFunLike.congr_fun fg
    map_add' := map_add f }

private theorem reassoc_pure (hL : LeftActionLaw R S M N) (hT : RightActionLaw R S N P)
    (m : M) (n : N) (p : P) :
    reassoc hL hT (leftPure m n p) = rightPure m n p :=
  leftLift_pure hL m n p

private theorem reassoc_unique (hL : LeftActionLaw R S M N) (hT : RightActionLaw R S N P)
    (e : LeftTensor R S M N P ≃+ RightTensor R S M N P) :
    (∀ m n p, e (leftPure m n p) = rightPure m n p) ↔ e = reassoc hL hT := by
  constructor
  · intro h
    have eq : e.toAddMonoidHom = (reassoc hL hT).toAddMonoidHom :=
      left_ext _ _ fun m n p => (h m n p).trans (reassoc_pure hL hT m n p).symm
    apply AddEquiv.ext
    intro q
    exact congrArg (fun k : LeftTensor R S M N P →+ RightTensor R S M N P => k q) eq
  · rintro rfl
    exact reassoc_pure hL hT

-- Step 3.2. Descend the C-action on the right nesting, where it acts on
-- the first factor. Transfer it through the additive equivalence to obtain
-- the action on the left nesting and check its required pure-tensor formula.
private theorem left_compatibility [Ring C] [Module C M] [SMulCommClass C (Rᵐᵒᵖ) M]
    (hL : LeftActionLaw R S M N) (hT : RightActionLaw R S N P) :
    ∃ (aL : Module C (LeftTensor R S M N P)) (aT : Module C (RightTensor R S M N P)),
      (∀ (c : C) (m : M) (n : N) (p : P),
        aL.smul c (leftPure m n p) = leftPure (c • m) n p ∧
        aT.smul c (rightPure m n p) = rightPure (c • m) n p) ∧
      ∀ c q, reassoc hL hT (aL.smul c q) = aT.smul c (reassoc hL hT q) := by
  let aT : Module C (RightTensor R S M N P) := leftModule
  let e := reassoc hL hT
  let aL := e.module C
  refine ⟨aL, aT, ?_, ?_⟩
  · intro c m n p
    have hp : aT.smul c (rightPure m n p) = rightPure (c • m) n p :=
      leftModule_pure c m (pure S n p)
    refine ⟨?_, hp⟩
    change e.symm (aT.smul c (e (leftPure m n p))) = leftPure (c • m) n p
    rw [show e (leftPure m n p) = rightPure m n p from reassoc_pure hL hT m n p, hp]
    exact e.symm_apply_eq.mpr (reassoc_pure hL hT (c • m) n p).symm
  · intro c q
    exact e.apply_symm_apply (aT.smul c (e q))

-- The right exterior action is a left action of the opposite ring. Descend it
-- on the left nesting, where it acts on the last factor.
private theorem right_compatibility [Ring C] [Module (Cᵐᵒᵖ) P] [SMulCommClass S (Cᵐᵒᵖ) P]
    (hL : LeftActionLaw R S M N) (hT : RightActionLaw R S N P) :
    ∃ (aL : Module (Cᵐᵒᵖ) (LeftTensor R S M N P))
      (aT : Module (Cᵐᵒᵖ) (RightTensor R S M N P)),
      (∀ (c : C) (m : M) (n : N) (p : P),
        aL.smul (MulOpposite.op c) (leftPure m n p) = leftPure m n (MulOpposite.op c • p) ∧
        aT.smul (MulOpposite.op c) (rightPure m n p) = rightPure m n (MulOpposite.op c • p)) ∧
      ∀ (c : C) q, reassoc hL hT (aL.smul (MulOpposite.op c) q) =
        aT.smul (MulOpposite.op c) (reassoc hL hT q) := by
  let _ := SMulCommClass.symm S (Cᵐᵒᵖ) P
  let aL : Module (Cᵐᵒᵖ) (LeftTensor R S M N P) := rightModule
  let e := reassoc hL hT
  let aT := e.symm.module (Cᵐᵒᵖ)
  refine ⟨aL, aT, ?_, ?_⟩
  · intro c m n p
    have hp : aL.smul (MulOpposite.op c) (leftPure m n p) =
        leftPure m n (MulOpposite.op c • p) := rightModule_pure (MulOpposite.op c) (pure R m n) p
    refine ⟨hp, ?_⟩
    change e (aL.smul (MulOpposite.op c) (e.symm (rightPure m n p))) =
      rightPure m n (MulOpposite.op c • p)
    rw [show e.symm (rightPure m n p) = leftPure m n p from
      e.symm_apply_eq.mpr (reassoc_pure hL hT m n p).symm, hp]
    exact reassoc_pure hL hT m n (MulOpposite.op c • p)
  · intro c q
    change e (aL.smul (MulOpposite.op c) q) =
      e (aL.smul (MulOpposite.op c) (e.symm (e q)))
    rw [e.symm_apply_apply]

section Naturality

variable [AddCommGroup P'] [Module (Sᵐᵒᵖ) N'] [Module S P']
variable [Module (Sᵐᵒᵖ) (Tensor R M' N')] [Module R (Tensor S N' P')]

private def pullPairing (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') (h : P →ₗ[S] P')
    (hg : ∀ (s : S) n, g (MulOpposite.op s • n) = MulOpposite.op s • g n)
    (b : TriplePairing R S M' N' P' A) : TriplePairing R S M N P A where
  run m n p := b.run (f m) (g n) (h p)
  add_first m m' n p := by rw [map_add, b.add_first]
  add_middle m n n' p := by rw [map_add, b.add_middle]
  add_last m n p p' := by rw [map_add, b.add_last]
  balance_R r m n p := by rw [map_smul, map_smul, b.balance_R]
  balance_S s m n p := by rw [hg, map_smul, b.balance_S]

-- Step 3.2 also supplies the two induced maps by descent and proves the
-- naturality square for any pair of maps with the stated generator formulas.
private theorem reassoc_natural
    (hL : LeftActionLaw R S M N) (hT : RightActionLaw R S N P)
    (hL' : LeftActionLaw R S M' N') (hT' : RightActionLaw R S N' P')
    (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N') (h : P →ₗ[S] P')
    (hg : ∀ (s : S) n, g (MulOpposite.op s • n) = MulOpposite.op s • g n) :
    let Maps := (LeftTensor R S M N P →+ LeftTensor R S M' N' P') ×
      (RightTensor R S M N P →+ RightTensor R S M' N' P')
    let induced := fun (maps : Maps) => ∀ m n p,
      maps.1 (leftPure m n p) = leftPure (f m) (g n) (h p) ∧
      maps.2 (rightPure m n p) = rightPure (f m) (g n) (h p)
    (∃ maps : Maps, induced maps) ∧
      (∀ maps : Maps, induced maps → ∀ q,
        reassoc hL' hT' (maps.1 q) = maps.2 (reassoc hL hT q)) := by
  intro Maps induced
  refine ⟨?_, ?_⟩
  · exact ⟨⟨leftLift hL (pullPairing f g h hg (leftPairing hL')),
      rightLift hT (pullPairing f g h hg (rightPairing hT'))⟩,
      fun m n p => ⟨leftLift_pure hL m n p, rightLift_pure hT m n p⟩⟩
  · intro maps hm q
    have eq : (reassoc hL' hT').toAddMonoidHom.comp maps.1 =
        maps.2.comp (reassoc hL hT).toAddMonoidHom := by
      apply left_ext
      intro m n p
      change reassoc hL' hT' (maps.1 (leftPure m n p)) =
        maps.2 (reassoc hL hT (leftPure m n p))
      rw [(hm m n p).1, reassoc_pure, reassoc_pure, (hm m n p).2]
    exact DFunLike.congr_fun eq q

end Naturality

end Triple

end

end BalancedTensorAssoc

theorem BalancedTensorAssociativity : (∀ (R : Type u) (S : Type v) [Ring R] [Ring S],
  let Middle := Sigma (fun N : ModuleCat.{x} R =>
    { right : Module (MulOpposite S) N //
      letI := right
      SMulCommClass (MulOpposite S) R N })
  let Triple := Prod (ModuleCat.{w} (MulOpposite R)) (Prod Middle (ModuleCat.{y} S))
  let first := fun (X : Triple) => X.1
  let middle := fun (X : Triple) => X.2.1.1
  let last := fun (X : Triple) => X.2.2
  let rightMiddle := fun (X : Triple) => X.2.1.2.val
  let innerLeft := fun (X : Triple) =>
    let M := first X
    let N := middle X
    let F := Finsupp (Prod M N) Int
    let gen : M → N → F := fun a b => Finsupp.single (a, b) 1
    let H : AddSubgroup F := AddSubgroup.closure
      { z | (∃ (a a' : M) (b : N),
              z = gen (a + a') b - gen a b - gen a' b) ∨
            (∃ (a : M) (b b' : N),
              z = gen a (b + b') - gen a b - gen a b') ∨
            (∃ (r : R) (a : M) (b : N),
              z = gen (MulOpposite.op r • a) b - gen a (r • b)) }
    (⟨H, fun m n => QuotientAddGroup.mk' H (gen m n)⟩ :
      Sigma (fun K : AddSubgroup F => M → N → HasQuotient.Quotient F K))
  let innerRight := fun (X : Triple) =>
    let N := middle X
    let P := last X
    letI := rightMiddle X
    let F := Finsupp (Prod N P) Int
    let gen : N → P → F := fun a b => Finsupp.single (a, b) 1
    let H : AddSubgroup F := AddSubgroup.closure
      { z | (∃ (a a' : N) (b : P),
              z = gen (a + a') b - gen a b - gen a' b) ∨
            (∃ (a : N) (b b' : P),
              z = gen a (b + b') - gen a b - gen a b') ∨
            (∃ (r : S) (a : N) (b : P),
              z = gen (MulOpposite.op r • a) b - gen a (r • b)) }
    (⟨H, fun n p => QuotientAddGroup.mk' H (gen n p)⟩ :
      Sigma (fun K : AddSubgroup F => N → P → HasQuotient.Quotient F K))
  let MN := fun (X : Triple) =>
    HasQuotient.Quotient (Finsupp (Prod (first X) (middle X)) Int) (innerLeft X).1
  let NP := fun (X : Triple) =>
    HasQuotient.Quotient (Finsupp (Prod (middle X) (last X)) Int) (innerRight X).1
  let InnerActions := fun (X : Triple) =>
    { a : Prod (Module (MulOpposite S) (MN X)) (Module R (NP X)) //
      (∀ (s : S) (m : first X) (n : middle X),
        a.1.smul (MulOpposite.op s) ((innerLeft X).2 m n) =
          (innerLeft X).2 m ((rightMiddle X).smul (MulOpposite.op s) n)) ∧
      (∀ (r : R) (n : middle X) (p : last X),
        a.2.smul r ((innerRight X).2 n p) = (innerRight X).2 (r • n) p) }
  let Parenthesized := Sigma InnerActions
  let left := fun (X : Parenthesized) =>
    let M := first X.1
    let N := middle X.1
    let P := last X.1
    let A := MN X.1
    letI := X.2.val.1
    let F := Finsupp (Prod A P) Int
    let gen : A → P → F := fun a b => Finsupp.single (a, b) 1
    let H : AddSubgroup F := AddSubgroup.closure
      { z | (∃ (a a' : A) (b : P),
              z = gen (a + a') b - gen a b - gen a' b) ∨
            (∃ (a : A) (b b' : P),
              z = gen a (b + b') - gen a b - gen a b') ∨
            (∃ (r : S) (a : A) (b : P),
              z = gen (MulOpposite.op r • a) b - gen a (r • b)) }
    (⟨H, fun m n p => QuotientAddGroup.mk' H (gen ((innerLeft X.1).2 m n) p)⟩ :
      Sigma (fun K : AddSubgroup F => M → N → P → HasQuotient.Quotient F K))
  let right := fun (X : Parenthesized) =>
    let M := first X.1
    let N := middle X.1
    let P := last X.1
    let B := NP X.1
    letI := X.2.val.2
    let F := Finsupp (Prod M B) Int
    let gen : M → B → F := fun a b => Finsupp.single (a, b) 1
    let H : AddSubgroup F := AddSubgroup.closure
      { z | (∃ (a a' : M) (b : B),
              z = gen (a + a') b - gen a b - gen a' b) ∨
            (∃ (a : M) (b b' : B),
              z = gen a (b + b') - gen a b - gen a b') ∨
            (∃ (r : R) (a : M) (b : B),
              z = gen (MulOpposite.op r • a) b - gen a (r • b)) }
    (⟨H, fun m n p => QuotientAddGroup.mk' H (gen m ((innerRight X.1).2 n p))⟩ :
      Sigma (fun K : AddSubgroup F => M → N → P → HasQuotient.Quotient F K))
  let L := fun (X : Parenthesized) =>
    HasQuotient.Quotient (Finsupp (Prod (MN X.1) (last X.1)) Int) (left X).1
  let T := fun (X : Parenthesized) =>
    HasQuotient.Quotient (Finsupp (Prod (first X.1) (NP X.1)) Int) (right X).1
  let tL := fun (X : Parenthesized) => (left X).2
  let tT := fun (X : Parenthesized) => (right X).2
  (∀ X : Triple, Nonempty (InnerActions X)) ∧
  (∃ α : ∀ X : Parenthesized, AddEquiv (L X) (T X),
    (∀ (X : Parenthesized) (e : AddEquiv (L X) (T X)),
      (∀ (m : first X.1) (n : middle X.1) (p : last X.1),
        e (tL X m n p) = tT X m n p) ↔ e = α X) ∧
    (∀ (X : Parenthesized) (C : Type z) [Ring C] [Module C (first X.1)]
        [SMulCommClass C (MulOpposite R) (first X.1)],
      ∃ (aL : Module C (L X)) (aT : Module C (T X)),
        (∀ (c : C) (m : first X.1) (n : middle X.1) (p : last X.1),
          aL.smul c (tL X m n p) = tL X (c • m) n p ∧
          aT.smul c (tT X m n p) = tT X (c • m) n p) ∧
        (∀ (c : C) (q : L X), α X (aL.smul c q) = aT.smul c (α X q))) ∧
    (∀ (X : Parenthesized) (D : Type t) [Ring D] [Module (MulOpposite D) (last X.1)]
        [SMulCommClass S (MulOpposite D) (last X.1)],
      ∃ (aL : Module (MulOpposite D) (L X)) (aT : Module (MulOpposite D) (T X)),
        (∀ (d : D) (m : first X.1) (n : middle X.1) (p : last X.1),
          aL.smul (MulOpposite.op d) (tL X m n p) = tL X m n (MulOpposite.op d • p) ∧
          aT.smul (MulOpposite.op d) (tT X m n p) = tT X m n (MulOpposite.op d • p)) ∧
        (∀ (d : D) (q : L X),
          α X (aL.smul (MulOpposite.op d) q) = aT.smul (MulOpposite.op d) (α X q))) ∧
    (∀ (X Y : Parenthesized)
        (f : LinearMap (RingHom.id (MulOpposite R)) (first X.1) (first Y.1))
        (g : LinearMap (RingHom.id R) (middle X.1) (middle Y.1))
        (h : LinearMap (RingHom.id S) (last X.1) (last Y.1)),
      (∀ (s : S) (n : middle X.1),
        g ((rightMiddle X.1).smul (MulOpposite.op s) n) =
          (rightMiddle Y.1).smul (MulOpposite.op s) (g n)) →
      let TensorMaps := Prod (AddMonoidHom (L X) (L Y)) (AddMonoidHom (T X) (T Y))
      let induced := fun (maps : TensorMaps) =>
        ∀ (m : first X.1) (n : middle X.1) (p : last X.1),
          maps.1 (tL X m n p) = tL Y (f m) (g n) (h p) ∧
          maps.2 (tT X m n p) = tT Y (f m) (g n) (h p)
      (∃ maps : TensorMaps, induced maps) ∧
      (∀ maps : TensorMaps, induced maps → ∀ q : L X, α Y (maps.1 q) = maps.2 (α X q))))) :=
(
by
  intro R S _ _ Middle Triple first middle last rightMiddle innerLeft innerRight MN NP
    InnerActions Parenthesized left right L T tL tT
  refine ⟨?_, ?_⟩
  · intro X
    letI := rightMiddle X
    letI : SMulCommClass (Sᵐᵒᵖ) R (middle X) := X.2.1.2.property
    letI := SMulCommClass.symm (Sᵐᵒᵖ) R (middle X)
    exact ⟨⟨⟨BalancedTensorAssoc.rightModule (C := Sᵐᵒᵖ) (R := R) (M := first X) (N := middle X),
      BalancedTensorAssoc.leftModule (C := R) (R := S) (M := middle X) (N := last X)⟩,
      ⟨fun s m n => BalancedTensorAssoc.rightModule_pure (MulOpposite.op s) m n, BalancedTensorAssoc.leftModule_pure⟩⟩⟩
  · let α (X : Parenthesized) : L X ≃+ T X := by
      letI := rightMiddle X.1
      letI := X.2.val.1
      letI := X.2.val.2
      exact BalancedTensorAssoc.reassoc X.2.property.1 X.2.property.2
    -- Step 4.1 packages the canonical isomorphism and its three properties.
    refine ⟨α, ?_, ?_, ?_, ?_⟩
    · intro X e
      letI := rightMiddle X.1
      letI := X.2.val.1
      letI := X.2.val.2
      exact BalancedTensorAssoc.reassoc_unique X.2.property.1 X.2.property.2 e
    · intro X C _ _ _
      letI := rightMiddle X.1
      letI := X.2.val.1
      letI := X.2.val.2
      exact BalancedTensorAssoc.left_compatibility X.2.property.1 X.2.property.2
    · intro X D _ _ _
      letI := rightMiddle X.1
      letI := X.2.val.1
      letI := X.2.val.2
      exact BalancedTensorAssoc.right_compatibility X.2.property.1 X.2.property.2
    · intro X Y f g h hg
      letI := rightMiddle X.1
      letI := X.2.val.1
      letI := X.2.val.2
      letI := rightMiddle Y.1
      letI := Y.2.val.1
      letI := Y.2.val.2
      exact BalancedTensorAssoc.reassoc_natural X.2.property.1 X.2.property.2 Y.2.property.1 Y.2.property.2 f g h hg
)

#print axioms BalancedTensorAssociativity
