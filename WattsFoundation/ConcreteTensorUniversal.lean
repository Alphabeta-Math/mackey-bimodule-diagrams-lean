import WattsFoundation.WattsSupport
import WattsFoundation.NoncommutativeTensorCokernel

/-! The general free-additive-group balanced tensor construction from the
original project satisfies the S-linear universal property used by the
noncommutative cokernel theorem. -/

namespace WattsFoundation

universe u v

variable {R S : Type u} [Ring R] [Ring S]
variable {M X : Type v} [AddCommGroup M] [Module (MulOpposite R) M] [Module S M]
variable [AddCommGroup X] [Module R X]

def rightAction (a : R) (m : M) : M := MulOpposite.op a • m

variable [SMulCommClass (MulOpposite R) S M]

theorem right_commute (r : R) (s : S) (m : M) :
    rightAction r (s • m) = s • rightAction r m := smul_comm (MulOpposite.op r) s m

local instance ConcreteTensorUniversal_local1 : AddCommGroup (ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) X) :=
  ChoiceFreeWatts.tensorAddCommGroup (X := X) (rightAction (R := R) (M := M))
local instance ConcreteTensorUniversal_local2 : Module S (ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) X) :=
  ChoiceFreeWatts.outerModule (X := X) (rightAction (R := R) (M := M)) right_commute

/-- The generator is biadditive, bundled as an additive hom in each variable. -/
def concretePure : M →+ (X →+ ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) X) :=
  AddMonoidHom.mk'
    (fun m => AddMonoidHom.mk' (fun x => ChoiceFreeWatts.pure rightAction m x)
      (fun x y => (ChoiceFreeWatts.pureBalanced rightAction).2.1 m x y))
    (by
      intro m m'
      ext x
      exact (ChoiceFreeWatts.pureBalanced rightAction).1 m m' x)

/-- The concrete tensor satisfies the universal property used by the
cokernel theorem, including outer S-linearity. -/
theorem concretePure_isBalancedTensor :
    IsBalancedTensor (R := R) (S := S) (concretePure (R := R) (M := M) (X := X)) := by
  constructor
  · intro r m x
    exact (ChoiceFreeWatts.pureBalanced rightAction).2.2 r m x
  constructor
  · intro s m x
    exact (ChoiceFreeWatts.scale_pure rightAction right_commute s m x).symm
  · intro D _ _ b hbalance houter
    let f : M → X → D := fun m x => b m x
    have hbalanced : ChoiceFreeWatts.Balanced rightAction f :=
      ⟨fun m m' x => DFunLike.congr_fun (map_add b m m') x,
       fun m x x' => map_add (b m) x x', hbalance⟩
    let lift := ChoiceFreeWatts.tensorLinearLift rightAction right_commute f hbalanced houter
    refine ⟨lift, ?_, ?_⟩
    · intro m x
      exact ChoiceFreeWatts.tensorLinearLift_pure rightAction right_commute f hbalanced houter m x
    · intro h hh
      apply LinearMap.toAddMonoidHom_injective
      apply ChoiceFreeWatts.tensorExt rightAction
      intro m x
      exact (hh m x).trans
        (ChoiceFreeWatts.tensorLinearLift_pure rightAction right_commute f hbalanced houter m x).symm

variable {Y : Type v} [AddCommGroup Y] [Module R Y]

/-- The tensor map induced by a left R-linear map. -/
def concreteTensorMap (f : X →ₗ[R] Y) :
    ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) X →ₗ[S]
      ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) Y :=
  ChoiceFreeWatts.tensorLinearLift rightAction right_commute
    (fun m x => ChoiceFreeWatts.pure rightAction m (f x))
    ⟨fun m m' x => (ChoiceFreeWatts.pureBalanced rightAction).1 m m' (f x),
     fun m x x' => by dsimp only; rw [map_add, (ChoiceFreeWatts.pureBalanced rightAction).2.1],
     fun r m x => by dsimp only; rw [(ChoiceFreeWatts.pureBalanced rightAction).2.2, map_smul]⟩
    (fun s m x => (ChoiceFreeWatts.scale_pure rightAction right_commute s m (f x)).symm)

@[simp] theorem concreteTensorMap_pure (f : X →ₗ[R] Y) (m : M) (x : X) :
    concreteTensorMap (M := M) (S := S) f (concretePure (R := R) (M := M) m x) =
      concretePure (R := R) (M := M) m (f x) := by
  apply ChoiceFreeWatts.tensorLinearLift_pure

variable {L N Q : Type v} [AddCommGroup L] [Module R L] [AddCommGroup N] [Module R N]
  [AddCommGroup Q] [Module R Q]

/-- Concrete noncommutative tensoring preserves a module cokernel presentation. -/
theorem concrete_tensor_preserves_cokernel (f : L →ₗ[R] N) (q : N →ₗ[R] Q)
    (q_surj : Function.Surjective q)
    (exact : ∀ n, q n = 0 → ∃ l, f l = n)
    (qf_zero : ∀ l, q (f l) = 0) :
    (∀ z, concreteTensorMap (M := M) (S := S) q
      (concreteTensorMap (M := M) (S := S) f z) = 0) ∧
    (∀ (D : Type v) [AddCommGroup D] [Module S D]
      (h : ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) N →ₗ[S] D),
      (∀ z, h (concreteTensorMap (M := M) (S := S) f z) = 0) →
      ∃! k : ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) Q →ₗ[S] D,
        ∀ z, k (concreteTensorMap (M := M) (S := S) q z) = h z) := by
  exact balanced_tensor_preserves_cokernel f q q_surj exact qf_zero
    (concretePure (R := R) (M := M) (X := L))
    (concretePure (R := R) (M := M) (X := N))
    (concretePure (R := R) (M := M) (X := Q))
    (concretePure_isBalancedTensor (R := R) (S := S) (M := M) (X := L))
    (concretePure_isBalancedTensor (R := R) (S := S) (M := M) (X := N))
    (concretePure_isBalancedTensor (R := R) (S := S) (M := M) (X := Q))
    (concreteTensorMap (M := M) (S := S) f) (concreteTensorMap (M := M) (S := S) q)
    (concreteTensorMap_pure (M := M) (S := S) f)
    (concreteTensorMap_pure (M := M) (S := S) q)

#print axioms concretePure_isBalancedTensor
#print axioms concrete_tensor_preserves_cokernel

end WattsFoundation
