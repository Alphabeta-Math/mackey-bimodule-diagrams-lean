
private theorem reassoc_unique (hL : LeftActionLaw R S M N) (hT : RightActionLaw R S N P)
    (e : LeftTensor R S M N P ≃+ RightTensor R S M N P) :
    (∀ m n p, e (leftPure m n p) = rightPure m n p) ↔ e = reassoc hL hT := by
  constructor
  · intro h
    have eq : e.toAddMonoidHom = (reassoc hL hT).toAddMonoidHom :=
      left_ext _ _ fun m n p => (h m n p).trans (reassoc_pure hL hT m n p).symm
    exact AddEquiv.ext (DFunLike.congr_fun eq)
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
  letI aT : Module C (RightTensor R S M N P) := leftModule
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
  letI := SMulCommClass.symm S (Cᵐᵒᵖ) P
  letI aL : Module (Cᵐᵒᵖ) (LeftTensor R S M N P) := rightModule
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
