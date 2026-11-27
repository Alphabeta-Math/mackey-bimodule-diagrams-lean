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

-- The coordinator's quotient adapters are definitional: the curried generator
-- here has the same pair of indices and the same three subgroup generators.
-- The registered universal property already performs the free additive extension
-- and quotient descent. Only its existence and uniqueness are needed here.
private def descend (f : M →+ N →+ A)
    (hb : ∀ (r : R) m n, f (MulOpposite.op r • m) n = f m (r • n)) :
    Tensor R M N →+ A :=
  Classical.choose (liftExists (fun p => f p.1 p.2)
    (fun m m' n => DFunLike.congr_fun (map_add f m m') n)
    (fun m n n' => map_add (f m) n n') hb)

@[simp] private theorem descend_pure (f : M →+ N →+ A)
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

@[simp] private theorem tensorMap_pure (f : M →ₗ[Rᵐᵒᵖ] M') (g : N →ₗ[R] N')
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

@[simp] private theorem leftInner_pure (m : M) (n : N) (p : P) :
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

@[simp] private theorem leftLift_pure (hL : LeftActionLaw R S M N)
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

@[simp] private theorem rightInner_pure (m : M) (n : N) (p : P) :
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

@[simp] private theorem rightLift_pure (hT : RightActionLaw R S N P)
    (m : M) (n : N) (p : P) :
    rightLift hT f (rightPure m n p) = f.run m n p := by
  unfold rightLift
  exact (descend_pure _ _ m (pure S n p)).trans (rightInner_pure m n p)

private theorem left_ext (f g : LeftTensor R S M N P →+ A)
    (h : ∀ m n p, f (leftPure m n p) = g (leftPure m n p)) : f = g := by
  apply hom_ext
  intro x p
  exact DFunLike.congr_fun (hom_ext (f.comp (pureLeft p)) (g.comp (pureLeft p))
    (fun m n => h m n p)) x

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

@[simp] private theorem reassoc_pure (hL : LeftActionLaw R S M N) (hT : RightActionLaw R S N P)
    (m : M) (n : N) (p : P) :
    reassoc hL hT (leftPure m n p) = rightPure m n p :=
  leftLift_pure hL m n p

end Triple

end

end BalancedTensorAssoc
