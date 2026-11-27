import Proofs.Bimodule
import MackeyDiagrams

set_option maxHeartbeats 2000000

universe u v w z

theorem ModuleTensorUniversalProperty : ∀ (R : Type u) (M : Type v) (N : Type w) [Ring R]
  [AddCommGroup M] [AddCommGroup N] [Module (MulOpposite R) M] [Module R N],
  let F := Finsupp (Prod M N) Int
  let gen : Prod M N → F := fun p => Finsupp.single p 1
  let H : AddSubgroup F := AddSubgroup.closure
    { x | (∃ (m m' : M) (n : N),
        x = gen (m + m', n) - gen (m, n) - gen (m', n)) ∨
      (∃ (m : M) (n n' : N),
        x = gen (m, n + n') - gen (m, n) - gen (m, n')) ∨
      (∃ (r : R) (m : M) (n : N),
        x = gen (MulOpposite.op r • m, n) - gen (m, r • n)) }
  let T := HasQuotient.Quotient F H
  let τ : Prod M N → T := fun p => QuotientAddGroup.mk' H (gen p)
  ((∀ (m m' : M) (n : N), τ (m + m', n) = τ (m, n) + τ (m', n)) ∧
    (∀ (m : M) (n n' : N), τ (m, n + n') = τ (m, n) + τ (m, n')) ∧
    (∀ (r : R) (m : M) (n : N), τ (MulOpposite.op r • m, n) = τ (m, r • n))) ∧
  (∀ (A : Type z) [AddCommGroup A],
    let Bal := { b : Prod M N → A //
      (∀ (m m' : M) (n : N), b (m + m', n) = b (m, n) + b (m', n)) ∧
      (∀ (m : M) (n n' : N), b (m, n + n') = b (m, n) + b (m, n')) ∧
      (∀ (r : R) (m : M) (n : N), b (MulOpposite.op r • m, n) = b (m, r • n)) }
    (∀ b : Bal, ∃! lift : AddMonoidHom T A, ∀ m n, lift (τ (m, n)) = b.val (m, n)) ∧
    (∃ e : Equiv (AddMonoidHom T A) Bal, ∀ f p, (e f).val p = f (τ p))) :=
by
  intro R M N _ _ _ _ _
  intro F gen H T τ
  let q : F →+ T := QuotientAddGroup.mk' H
  have killRelation (x : F) (hx : x ∈ H) : q x = 0 := by
    apply AddMonoidHom.mem_ker.mp
    rwa [QuotientAddGroup.ker_mk']
  -- Alphabeta Math 1.2 uses balance of elementary tensors from its presentation
  -- hypothesis L1. Here we first prove that balance in the specified quotient.
  have addLeft (m m' : M) (n : N) :
      τ (m + m', n) = τ (m, n) + τ (m', n) := by
    have h := killRelation (gen (m + m', n) - gen (m, n) - gen (m', n))
      (AddSubgroup.subset_closure (Or.inl ⟨m, m', n, rfl⟩))
    rw [map_sub, map_sub, sub_sub] at h
    exact sub_eq_zero.mp h
  have addRight (m : M) (n n' : N) :
      τ (m, n + n') = τ (m, n) + τ (m, n') := by
    have h := killRelation (gen (m, n + n') - gen (m, n) - gen (m, n'))
      (AddSubgroup.subset_closure (Or.inr (Or.inl ⟨m, n, n', rfl⟩)))
    rw [map_sub, map_sub, sub_sub] at h
    exact sub_eq_zero.mp h
  have balance (r : R) (m : M) (n : N) :
      τ (MulOpposite.op r • m, n) = τ (m, r • n) := by
    have h := killRelation (gen (MulOpposite.op r • m, n) - gen (m, r • n))
      (AddSubgroup.subset_closure (Or.inr (Or.inr ⟨r, m, n, rfl⟩)))
    rw [map_sub] at h
    exact sub_eq_zero.mp h
  refine ⟨⟨addLeft, addRight, balance⟩, ?_⟩
  intro A _ Bal
  -- Step 1.2 now restricts each additive homomorphism to elementary tensors.
  let restrict (f : T →+ A) : Bal :=
    ⟨fun p => f (τ p),
      fun m m' n => (congrArg f (addLeft m m' n)).trans (map_add f _ _),
      fun m n n' => (congrArg f (addRight m n n')).trans (map_add f _ _),
      fun r m n => congrArg f (balance r m n)⟩
  -- Steps 1.1 and 2.1 use the integer scalar action on A. The additive
  -- Finsupp equivalence extends the maps k ↦ k • b(p) on the basis summands.
  let extend (b : Bal) : F →+ A :=
    Finsupp.liftAddHom (fun p => zmultiplesHom A (b.val p))
  have extendGen (b : Bal) (p : M × N) : extend b (gen p) = b.val p := by
    change Finsupp.liftAddHom (fun p => zmultiplesHom A (b.val p))
      (Finsupp.single p (1 : ℤ)) = b.val p
    rw [Finsupp.liftAddHom_apply_single]
    change (1 : ℤ) • b.val p = b.val p
    exact one_zsmul _
  -- Step 3.1 kills all generators using the three balanced-map laws,
  -- and closure then gives the kernel containment for the full subgroup.
  have relationKernel (b : Bal) : H ≤ (extend b).ker := by
    apply (AddSubgroup.closure_le _).2
    intro x hx
    apply AddMonoidHom.mem_ker.mpr
    rcases hx with ⟨m, m', n, rfl⟩ | ⟨m, n, n', rfl⟩ | ⟨r, m, n, rfl⟩
    · rw [map_sub, map_sub, sub_sub, extendGen, extendGen, extendGen, b.property.1, sub_self]
    · rw [map_sub, map_sub, sub_sub, extendGen, extendGen, extendGen, b.property.2.1, sub_self]
    · rw [map_sub, extendGen, extendGen, b.property.2.2, sub_self]
  -- Step 4.1 descends explicitly. Normality follows from commutativity of F.
  let descend (b : Bal) : T →+ A :=
    QuotientAddGroup.lift H (extend b) (relationKernel b)
  have descendGen (b : Bal) (p : M × N) : descend b (τ p) = b.val p := by
    exact (QuotientAddGroup.lift_mk H (relationKernel b) (gen p)).trans (extendGen b p)
  -- Step 5.1 uses quotient surjectivity and extensionality on the integer
  -- summands. An additive homomorphism out of ℤ is determined by its value at 1.
  have tensorExt (f g : T →+ A) (h : ∀ p, f (τ p) = g (τ p)) : f = g := by
    have hfree : f.comp q = g.comp q := by
      apply Finsupp.addHom_ext'
      intro p
      apply (zmultiplesHom A).symm.injective
      change f (τ p) = g (τ p)
      exact h p
    apply AddMonoidHom.ext
    intro t
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective H t
    exact DFunLike.congr_fun hfree x
  -- These inverse laws give both conclusions. Step 6.1 covers zero modules
  -- and the zero ring through the same construction, so no case split is needed.
  refine ⟨?_, ?_⟩
  · intro b
    refine ⟨descend b, fun m n => descendGen b (m, n), ?_⟩
    intro f hf
    exact tensorExt f (descend b) (fun p => (hf p.1 p.2).trans (descendGen b p).symm)
  · refine ⟨⟨restrict, descend, ?_, ?_⟩, fun _ _ => rfl⟩
    · intro f
      exact tensorExt (descend (restrict f)) f (descendGen (restrict f))
    · intro b
      exact Subtype.ext (funext (descendGen b))

#print axioms ModuleTensorUniversalProperty
