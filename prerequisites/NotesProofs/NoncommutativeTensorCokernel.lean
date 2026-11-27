import NotesProofs.BalancedCokernelDescent

/-! Universal-property proof that tensoring over a noncommutative ring
preserves a presented cokernel. The tensor objects are supplied through their
balanced-map universal properties. -/

namespace NotesProofs

universe u v

variable {R S : Type u} [Ring R] [Ring S]
variable {M L N Q TL TN TQ : Type v}
variable [AddCommGroup M] [Module (MulOpposite R) M] [Module S M]
variable [AddCommGroup L] [Module R L] [AddCommGroup N] [Module R N]
variable [AddCommGroup Q] [Module R Q]
variable [AddCommGroup TL] [Module S TL] [AddCommGroup TN] [Module S TN]
variable [AddCommGroup TQ] [Module S TQ]

/-- The balanced tensor universal property in a fixed module universe. -/
def IsBalancedTensor {X T : Type v} [AddCommGroup X] [Module R X]
    [AddCommGroup T] [Module S T] (p : M →+ (X →+ T)) : Prop :=
  (∀ (r : R) (m : M) (x : X), p (MulOpposite.op r • m) x = p m (r • x)) ∧
  (∀ (s : S) (m : M) (x : X), p (s • m) x = s • p m x) ∧
  ∀ (D : Type v) [AddCommGroup D] [Module S D] (b : M →+ (X →+ D)),
    (∀ (r : R) (m : M) (x : X), b (MulOpposite.op r • m) x = b m (r • x)) →
    (∀ (s : S) (m : M) (x : X), b (s • m) x = s • b m x) →
    ∃! h : T →ₗ[S] D, ∀ m x, h (p m x) = b m x

/-- The induced map on balanced tensors has the cokernel factorization
property. This applies to arbitrary (possibly noncommutative) `R` and `S`. -/
theorem balanced_tensor_cokernel_factorization
    (f : L →ₗ[R] N) (q : N →ₗ[R] Q)
    (q_surj : Function.Surjective q)
    (exact : ∀ n, q n = 0 → ∃ l, f l = n)
    (pL : M →+ (L →+ TL)) (pN : M →+ (N →+ TN)) (pQ : M →+ (Q →+ TQ))
    (tensorN : IsBalancedTensor (R := R) (S := S) pN)
    (tensorQ : IsBalancedTensor (R := R) (S := S) pQ)
    (tf : TL →ₗ[S] TN) (tq : TN →ₗ[S] TQ)
    (tf_pure : ∀ m l, tf (pL m l) = pN m (f l))
    (tq_pure : ∀ m n, tq (pN m n) = pQ m (q n)) :
    ∀ (D : Type v) [AddCommGroup D] [Module S D] (h : TN →ₗ[S] D),
      (∀ z, h (tf z) = 0) → ∃! k : TQ →ₗ[S] D, ∀ z, k (tq z) = h z := by
  intro D _ _ h hk
  let b : M →+ (N →+ D) :=
    { toFun := fun m => h.toAddMonoidHom.comp (pN m)
      map_zero' := by ext n; simp
      map_add' := by intro a b; ext n; simp }
  have b_balance : ∀ (r : R) (m : M) (n : N),
      b (MulOpposite.op r • m) n = b m (r • n) := by
    intro r m n
    change h (pN (MulOpposite.op r • m) n) = h (pN m (r • n))
    rw [tensorN.1]
  have b_outer : ∀ (s : S) (m : M) (n : N), b (s • m) n = s • b m n := by
    intro s m n
    change h (pN (s • m) n) = s • h (pN m n)
    rw [tensorN.2.1, map_smul]
  have b_kill : ∀ m l, b m (f l) = 0 := by
    intro m l
    change h (pN m (f l)) = 0
    rw [← tf_pure]
    exact hk _
  obtain ⟨c, ⟨c_factor, c_balance⟩, _⟩ :=
    balanced_cokernel_descent f q q_surj exact b b_balance b_kill
  have c_outer := balanced_cokernel_descent_outer_linear q q_surj b c c_factor b_outer
  obtain ⟨k, k_pure, k_unique⟩ := tensorQ.2.2 D c c_balance c_outer
  refine ⟨k, ?_, ?_⟩
  · have kq_pure : ∀ m n, (k.comp tq) (pN m n) = b m n := by
      intro m n
      change k (tq (pN m n)) = b m n
      rw [tq_pure, k_pure, c_factor]
    have h_pure : ∀ m n, h (pN m n) = b m n := by intro m n; rfl
    obtain ⟨g, hg, g_unique⟩ := tensorN.2.2 D b b_balance b_outer
    have eqmaps : k.comp tq = h := (g_unique _ kq_pure).trans (g_unique _ h_pure).symm
    exact fun z => DFunLike.congr_fun eqmaps z
  · intro j hj
    apply k_unique
    intro m x
    obtain ⟨n, rfl⟩ := q_surj x
    rw [← tq_pure, hj, c_factor]
    rfl

/-- Tensoring carries the given exact presentation to a cokernel, under
the displayed universal properties and generator formulas. -/
theorem balanced_tensor_preserves_cokernel
    (f : L →ₗ[R] N) (q : N →ₗ[R] Q)
    (q_surj : Function.Surjective q)
    (exact : ∀ n, q n = 0 → ∃ l, f l = n)
    (qf_zero : ∀ l, q (f l) = 0)
    (pL : M →+ (L →+ TL)) (pN : M →+ (N →+ TN)) (pQ : M →+ (Q →+ TQ))
    (tensorL : IsBalancedTensor (R := R) (S := S) pL)
    (tensorN : IsBalancedTensor (R := R) (S := S) pN)
    (tensorQ : IsBalancedTensor (R := R) (S := S) pQ)
    (tf : TL →ₗ[S] TN) (tq : TN →ₗ[S] TQ)
    (tf_pure : ∀ m l, tf (pL m l) = pN m (f l))
    (tq_pure : ∀ m n, tq (pN m n) = pQ m (q n)) :
    (∀ z, tq (tf z) = 0) ∧
    (∀ (D : Type v) [AddCommGroup D] [Module S D] (h : TN →ₗ[S] D),
      (∀ z, h (tf z) = 0) → ∃! k : TQ →ₗ[S] D, ∀ z, k (tq z) = h z) := by
  constructor
  · let b : M →+ (L →+ TQ) := 0
    have hb_balance : ∀ (r : R) (m : M) (l : L),
        b (MulOpposite.op r • m) l = b m (r • l) := by simp [b]
    have hb_outer : ∀ (s : S) (m : M) (l : L), b (s • m) l = s • b m l := by simp [b]
    obtain ⟨g, hg, g_unique⟩ := tensorL.2.2 TQ b hb_balance hb_outer
    have htq : ∀ m l, (tq.comp tf) (pL m l) = b m l := by
      intro m l
      change tq (tf (pL m l)) = 0
      rw [tf_pure, tq_pure, qf_zero, map_zero]
    have hzero : ∀ m l, (0 : TL →ₗ[S] TQ) (pL m l) = b m l := by simp [b]
    have eqmaps : tq.comp tf = 0 := (g_unique _ htq).trans (g_unique _ hzero).symm
    intro z
    exact DFunLike.congr_fun eqmaps z
  · exact balanced_tensor_cokernel_factorization f q q_surj exact pL pN pQ
      tensorN tensorQ tf tq tf_pure tq_pure

#print axioms balanced_tensor_cokernel_factorization
#print axioms balanced_tensor_preserves_cokernel

end NotesProofs
