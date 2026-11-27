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
  rw [leftPure, leftLift, descend_pure, leftInner_pure]

-- Steps 1.2 and 2.2 first descend the S-balanced pairing for each m.
-- Extensionality on N ⊗ P proves additivity in m and R-balance.
private def rightInner (f : TriplePairing R S M N P A) (m : M) : Tensor S N P →+ A :=
  descend (additive (fun n => additive (f.run m n) (f.add_last m n))
    (fun n n' => AddMonoidHom.ext fun p => f.add_middle m n n' p))
    (f.balance_S · m)

@[simp] private theorem rightInner_pure (m : M) (n : N) (p : P) :
    rightInner f m (pure S n p) = f.run m n p := by
  rw [rightInner, descend_pure]
  rfl

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
  rw [rightPure, rightLift, descend_pure]
  exact rightInner_pure m n p

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
  AddEquiv.ofAddMonoidHom f g
    (right_ext _ _ fun m n p => by
      change f (g (rightPure m n p)) = rightPure m n p
      rw [show g (rightPure m n p) = leftPure m n p from rightLift_pure hT m n p]
      exact leftLift_pure hL m n p)
    (left_ext _ _ fun m n p => by
      change g (f (leftPure m n p)) = leftPure m n p
      rw [show f (leftPure m n p) = rightPure m n p from leftLift_pure hL m n p]
      exact rightLift_pure hT m n p)

@[simp] private theorem reassoc_pure (hL : LeftActionLaw R S M N) (hT : RightActionLaw R S N P)
    (m : M) (n : N) (p : P) :
    reassoc hL hT (leftPure m n p) = rightPure m n p :=
  leftLift_pure hL m n p

end Triple
