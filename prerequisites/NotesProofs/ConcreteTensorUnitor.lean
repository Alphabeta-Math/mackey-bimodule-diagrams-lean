import NotesProofs.ConcreteTensorFunctor

/-! The unit isomorphism for tensoring an arbitrary bimodule with the
regular left module. -/

set_option backward.isDefEq.respectTransparency false

namespace NotesProofs

universe u
open CategoryTheory

variable {R S : Type u} [Ring R] [Ring S]
variable (M : Type u) [AddCommGroup M] [Module (MulOpposite R) M] [Module S M]
variable [SMulCommClass (MulOpposite R) S M]

local instance ConcreteTensorUnitor_local1 {X : Type u} [AddCommGroup X] [Module R X] :
    AddCommGroup (ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) X) :=
  ChoiceFreeWatts.tensorAddCommGroup _
local instance ConcreteTensorUnitor_local2 {X : Type u} [AddCommGroup X] [Module R X] :
    Module S (ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) X) :=
  ChoiceFreeWatts.outerModule _ right_commute

/-- Multiplication of a tensor with the regular module. -/
def concreteTensorUnitor :
    ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) (ChoiceFreeWatts.regular R) →ₗ[S] M :=
  ChoiceFreeWatts.tensorLinearLift rightAction right_commute (fun m (a : ULift.{u} R) =>
    MulOpposite.op a.down • m)
    ⟨fun m n a => smul_add (MulOpposite.op a.down) m n,
     fun m a b => by simp [add_smul],
     fun r m a => by
       change MulOpposite.op a.down • (MulOpposite.op r • m) = MulOpposite.op (r * a.down) • m
       rw [← mul_smul]
       rfl⟩
    (fun s m a => right_commute a.down s m)

/-- Insertion of the unit gives the inverse of the tensor unitor. -/
def concreteTensorUnitorInv : M →ₗ[S]
    ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) (ChoiceFreeWatts.regular R) where
  toFun m := concretePure (R := R) (M := M) m (⟨1⟩ : ULift.{u} R)
  map_add' m n := DFunLike.congr_fun (map_add (concretePure (R := R) (M := M)) m n) _
  map_smul' s m := by
    exact (ChoiceFreeWatts.scale_pure rightAction right_commute s m (⟨1⟩ : ULift.{u} R)).symm

@[simp] theorem concreteTensorUnitor_pure (m : M) (a : ULift.{u} R) :
    concreteTensorUnitor (R := R) (S := S) M (concretePure (R := R) (M := M) m a) = MulOpposite.op a.down • m := by
  apply ChoiceFreeWatts.tensorLinearLift_pure

/-- The two unitor maps are inverse S-linear maps. -/
noncomputable def concreteTensorRegularIso :
    ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) (ChoiceFreeWatts.regular R) ≃ₗ[S] M := by
  apply LinearEquiv.ofLinearMap (concreteTensorUnitor (R := R) (S := S) M) (concreteTensorUnitorInv (R := R) (S := S) M)
  · ext m
    change concreteTensorUnitor (R := R) (S := S) M (concretePure (R := R) (M := M) m (⟨1⟩ : ULift.{u} R)) = m
    rw [concreteTensorUnitor_pure]
    simp
  · apply LinearMap.toAddMonoidHom_injective
    apply ChoiceFreeWatts.tensorExt (rightAction (R := R) (M := M))
    intro m a
    change concretePure (R := R) (M := M) (concreteTensorUnitor (R := R) (S := S) M (concretePure (R := R) (M := M) m a))
      (⟨1⟩ : ULift.{u} R) = concretePure (R := R) (M := M) m a
    rw [concreteTensorUnitor_pure]
    change ChoiceFreeWatts.pure rightAction (rightAction a.down m) (⟨1⟩ : ULift.{u} R) = _
    rw [(ChoiceFreeWatts.pureBalanced rightAction).2.2]
    congr 1
    apply ULift.ext
    exact mul_one a.down

#print axioms concreteTensorRegularIso

end NotesProofs
