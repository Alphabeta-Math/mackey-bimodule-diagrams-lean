import NotesProofs.ConcreteTensorUnitor

/-! A bimodule map induces a natural transformation between tensor functors. -/

set_option backward.isDefEq.respectTransparency false

namespace NotesProofs

universe u
open CategoryTheory

variable {R S : Type u} [Ring R] [Ring S]
variable {M N : Type u} [AddCommGroup M] [Module (MulOpposite R) M] [Module S M]
  [SMulCommClass (MulOpposite R) S M]
  [AddCommGroup N] [Module (MulOpposite R) N] [Module S N]
  [SMulCommClass (MulOpposite R) S N]

local instance ConcreteTensorBimoduleMap_local1 {P X : Type u} [AddCommGroup P] [Module (MulOpposite R) P]
    [AddCommGroup X] [Module R X] :
    AddCommGroup (ChoiceFreeWatts.Tensor (rightAction (R := R) (M := P)) X) :=
  ChoiceFreeWatts.tensorAddCommGroup _
local instance ConcreteTensorBimoduleMap_local2 {P X : Type u} [AddCommGroup P] [Module (MulOpposite R) P] [Module S P]
    [SMulCommClass (MulOpposite R) S P] [AddCommGroup X] [Module R X] :
    Module S (ChoiceFreeWatts.Tensor (rightAction (R := R) (M := P)) X) :=
  ChoiceFreeWatts.outerModule _ right_commute

/-- An S-linear map that also respects the right R-action. -/
def BimoduleMap := { f : M →ₗ[S] N // ∀ (r : R) (m : M),
  f (MulOpposite.op r • m) = MulOpposite.op r • f m }

/-- The induced map on one tensor product. -/
def tensorBimoduleMapComponent (f : BimoduleMap (R := R) (S := S) (M := M) (N := N))
    (X : ModuleCat.{u} R) :
    ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) X →ₗ[S]
      ChoiceFreeWatts.Tensor (rightAction (R := R) (M := N)) X :=
  ChoiceFreeWatts.tensorLinearLift rightAction right_commute
    (fun m x => ChoiceFreeWatts.pure (rightAction (R := R) (M := N)) (f.1 m) x)
    ⟨fun m n x => by dsimp only; rw [map_add, (ChoiceFreeWatts.pureBalanced _).1],
     fun m x y => (ChoiceFreeWatts.pureBalanced _).2.1 (f.1 m) x y,
     fun r m x => by
       change ChoiceFreeWatts.pure (rightAction (R := R) (M := N)) (f.1 (MulOpposite.op r • m)) x = _
       rw [f.2]
       exact (ChoiceFreeWatts.pureBalanced (rightAction (R := R) (M := N))).2.2 r (f.1 m) x⟩
    (fun s m x => by
      rw [map_smul]
      exact (ChoiceFreeWatts.scale_pure _ right_commute s (f.1 m) x).symm)

@[simp] theorem tensorBimoduleMapComponent_pure
    (f : BimoduleMap (R := R) (S := S) (M := M) (N := N)) (X : ModuleCat.{u} R) (m : M) (x : X) :
    tensorBimoduleMapComponent f X (concretePure (R := R) (M := M) m x) =
      concretePure (R := R) (M := N) (f.1 m) x := by
  apply ChoiceFreeWatts.tensorLinearLift_pure

/-- Naturality of the induced tensor maps. -/
def tensorBimoduleMapNatTrans (f : BimoduleMap (R := R) (S := S) (M := M) (N := N)) :
    concreteTensorFunctor (R := R) (S := S) M ⟶ concreteTensorFunctor (R := R) (S := S) N where
  app X := @ModuleCat.ofHom S _ ((concreteTensorFunctor (R := R) (S := S) M).obj X)
    ((concreteTensorFunctor (R := R) (S := S) N).obj X) _ _ _ _ (tensorBimoduleMapComponent f X)
  naturality {X Y} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply ChoiceFreeWatts.tensorExt (rightAction (R := R) (M := M))
    intro m x
    change tensorBimoduleMapComponent f Y
        (concreteTensorMap (M := M) (S := S) g.hom (concretePure (R := R) (M := M) m x)) =
      concreteTensorMap (M := N) (S := S) g.hom
        (tensorBimoduleMapComponent f X (concretePure (R := R) (M := M) m x))
    rw [concreteTensorMap_pure, tensorBimoduleMapComponent_pure,
      tensorBimoduleMapComponent_pure, concreteTensorMap_pure]

/-- Evaluation of a tensor map out of the regular module, on all tensors. -/
theorem concreteTensor_fromRegular (X : ModuleCat.{u} R) (x : X)
    (t : ChoiceFreeWatts.Tensor (rightAction (R := R) (M := N)) (ChoiceFreeWatts.regular R)) :
    concreteTensorMap (M := N) (S := S) (ChoiceFreeWatts.ell X x).hom t =
      concretePure (R := R) (M := N) (concreteTensorUnitor (R := R) (S := S) N t) x := by
  let p : N →+ ChoiceFreeWatts.Tensor (rightAction (R := R) (M := N)) X :=
    AddMonoidHom.mk' (fun n => concretePure (R := R) (M := N) n x)
      (fun n n' => (ChoiceFreeWatts.pureBalanced (rightAction (R := R) (M := N))).1 n n' x)
  let left := (concreteTensorMap (M := N) (S := S) (ChoiceFreeWatts.ell X x).hom).toAddMonoidHom
  let right := p.comp (concreteTensorUnitor (R := R) (S := S) N).toAddMonoidHom
  have eq : left = right := by
    apply ChoiceFreeWatts.tensorExt (rightAction (R := R) (M := N))
    intro n a
    change concreteTensorMap (M := N) (S := S) (ChoiceFreeWatts.ell X x).hom
        (concretePure (R := R) (M := N) n a) =
      concretePure (R := R) (M := N)
        (concreteTensorUnitor (R := R) (S := S) N (concretePure (R := R) (M := N) n a)) x
    rw [concreteTensorMap_pure, concreteTensorUnitor_pure, ChoiceFreeWatts.ell_apply]
    exact ((ChoiceFreeWatts.pureBalanced (rightAction (R := R) (M := N))).2.2 a.down n x).symm
  exact DFunLike.congr_fun eq t

/-- Evaluation of a natural transformation at the regular module, transported
through the tensor unitors. -/
def tensorNatEvaluation
    (τ : concreteTensorFunctor (R := R) (S := S) M ⟶ concreteTensorFunctor (R := R) (S := S) N) :
    M →ₗ[S] N :=
  (concreteTensorUnitor (R := R) (S := S) N).comp
    ((τ.app (ChoiceFreeWatts.regular R)).hom.comp (concreteTensorUnitorInv (R := R) (S := S) M))

/-- Naturality at maps from the regular module determines every component
on pure tensors. -/
theorem tensorNatTrans_pure
    (τ : concreteTensorFunctor (R := R) (S := S) M ⟶ concreteTensorFunctor (R := R) (S := S) N)
    (X : ModuleCat.{u} R) (m : M) (x : X) :
    (τ.app X).hom (concretePure (R := R) (M := M) m x) =
      concretePure (R := R) (M := N) (tensorNatEvaluation τ m) x := by
  have hn := DFunLike.congr_fun
    (congrArg ModuleCat.Hom.hom (τ.naturality (ChoiceFreeWatts.ell X x)))
      (concretePure (R := R) (M := M) m (⟨1⟩ : ULift.{u} R))
  change (τ.app X).hom (concreteTensorMap (M := M) (S := S) (ChoiceFreeWatts.ell X x).hom
      (concretePure (R := R) (M := M) m (⟨1⟩ : ULift.{u} R))) =
    concreteTensorMap (M := N) (S := S) (ChoiceFreeWatts.ell X x).hom
      ((τ.app (ChoiceFreeWatts.regular R)).hom
        (concretePure (R := R) (M := M) m (⟨1⟩ : ULift.{u} R))) at hn
  rw [concreteTensorMap_pure, ChoiceFreeWatts.ell_apply, one_smul, concreteTensor_fromRegular] at hn
  exact hn

/-- The evaluated map respects the right R-action. -/
theorem tensorNatEvaluation_right
    (τ : concreteTensorFunctor (R := R) (S := S) M ⟶ concreteTensorFunctor (R := R) (S := S) N)
    (r : R) (m : M) :
    tensorNatEvaluation τ (MulOpposite.op r • m) = MulOpposite.op r • tensorNatEvaluation τ m := by
  have balance : concretePure (R := R) (M := M) (MulOpposite.op r • m) (⟨1⟩ : ULift.{u} R) =
      concretePure (R := R) (M := M) m (⟨r⟩ : ULift.{u} R) := by
    change ChoiceFreeWatts.pure (rightAction (R := R) (M := M)) (rightAction r m) (⟨1⟩ : ULift.{u} R) = _
    rw [(ChoiceFreeWatts.pureBalanced (rightAction (R := R) (M := M))).2.2]
    congr 1
    apply ULift.ext
    exact mul_one r
  change concreteTensorUnitor (R := R) (S := S) N
      ((τ.app (ChoiceFreeWatts.regular R)).hom
        (concretePure (R := R) (M := M) (MulOpposite.op r • m) (⟨1⟩ : ULift.{u} R))) = _
  rw [balance, tensorNatTrans_pure, concreteTensorUnitor_pure]

/-- Evaluation therefore defines a bimodule map. -/
def tensorNatEvaluationMap
    (τ : concreteTensorFunctor (R := R) (S := S) M ⟶ concreteTensorFunctor (R := R) (S := S) N) :
    BimoduleMap (R := R) (S := S) (M := M) (N := N) :=
  ⟨tensorNatEvaluation τ, tensorNatEvaluation_right τ⟩

/-- Evaluation recovers a bimodule map from its induced tensor transformation. -/
theorem tensorNatEvaluation_induced
    (f : BimoduleMap (R := R) (S := S) (M := M) (N := N)) :
    tensorNatEvaluationMap (tensorBimoduleMapNatTrans f) = f := by
  apply Subtype.ext
  ext m
  change concreteTensorUnitor (R := R) (S := S) N
    (tensorBimoduleMapComponent f (ChoiceFreeWatts.regular R)
      (concretePure (R := R) (M := M) m (⟨1⟩ : ULift.{u} R))) = f.1 m
  rw [tensorBimoduleMapComponent_pure, concreteTensorUnitor_pure]
  simp

/-- A natural transformation is recovered from its regular-module value. -/
theorem tensorNatEvaluation_complete
    (τ : concreteTensorFunctor (R := R) (S := S) M ⟶ concreteTensorFunctor (R := R) (S := S) N) :
    tensorBimoduleMapNatTrans (tensorNatEvaluationMap τ) = τ := by
  apply NatTrans.ext
  funext X
  apply ModuleCat.hom_ext
  apply LinearMap.toAddMonoidHom_injective
  apply ChoiceFreeWatts.tensorExt (rightAction (R := R) (M := M))
  intro m x
  change tensorBimoduleMapComponent (tensorNatEvaluationMap τ) X
      (concretePure (R := R) (M := M) m x) =
    (τ.app X).hom (concretePure (R := R) (M := M) m x)
  rw [tensorBimoduleMapComponent_pure, tensorNatTrans_pure]
  rfl

/-- Bimodule maps are in bijection with natural transformations of their
tensor functors. -/
def bimoduleMapEquivNatTrans :
    BimoduleMap (R := R) (S := S) (M := M) (N := N) ≃
      (concreteTensorFunctor (R := R) (S := S) M ⟶ concreteTensorFunctor (R := R) (S := S) N) where
  toFun := tensorBimoduleMapNatTrans
  invFun := tensorNatEvaluationMap
  left_inv := tensorNatEvaluation_induced
  right_inv := tensorNatEvaluation_complete

#print axioms bimoduleMapEquivNatTrans
#print axioms tensorBimoduleMapNatTrans
#print axioms tensorNatEvaluationMap
#print axioms concreteTensor_fromRegular

end NotesProofs
