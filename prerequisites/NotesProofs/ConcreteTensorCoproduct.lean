import NotesProofs.ConcreteTensorUniversal
import NotesProofs.NoncommutativeTensorCoproduct

/-! Concrete tensoring preserves set-indexed direct sums for arbitrary rings. -/

namespace NotesProofs

universe u v

variable {R S : Type u} [Ring R] [Ring S]
variable {M : Type v} [AddCommGroup M] [Module (MulOpposite R) M] [Module S M]
variable [SMulCommClass (MulOpposite R) S M]
variable {I : Type v} (D : I → ModuleCat.{v} R)

local instance ConcreteTensorCoproduct_local1 {X : Type v} [AddCommGroup X] [Module R X] :
    AddCommGroup (ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) X) :=
  ChoiceFreeWatts.tensorAddCommGroup (X := X) (rightAction (R := R) (M := M))
local instance ConcreteTensorCoproduct_local2 {X : Type v} [AddCommGroup X] [Module R X] :
    Module S (ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) X) :=
  ChoiceFreeWatts.outerModule (X := X) (rightAction (R := R) (M := M)) right_commute

/-- The concrete direct sum has its expected additive universal property. -/
theorem concrete_sum_additive_coproduct :
    ∀ (E : Type v) [AddCommGroup E] (legs : ∀ i, D i →+ E),
      ∃! d : (ChoiceFreeWatts.sumObj D) →+ E,
        ∀ i x, d (ChoiceFreeWatts.sumIncl D i x) = legs i x := by
  intro E _ legs
  refine ⟨ChoiceFreeWatts.sumAddLift D legs, ?_, ?_⟩
  · intro i x
    exact ChoiceFreeWatts.sumAddLift_summand D legs i x
  · intro d hd
    apply ChoiceFreeWatts.sumExt D
    intro i x
    exact (hd i x).trans (ChoiceFreeWatts.sumAddLift_summand D legs i x).symm

/-- The induced tensor maps form a coproduct cocone, including the empty
index set. All rings may be noncommutative. -/
theorem concrete_tensor_preserves_coproduct :
    ∀ (E : Type v) [AddCommGroup E] [Module S E]
      (legs : ∀ i, ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) (D i) →ₗ[S] E),
      ∃! h : ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M))
          (ChoiceFreeWatts.sumObj D) →ₗ[S] E,
        ∀ i t, h (concreteTensorMap (M := M) (S := S) (ChoiceFreeWatts.sumIncl D i) t) = legs i t := by
  exact balanced_tensor_preserves_coproduct
    (fun i => (D i : Type v))
    (fun i => ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) (D i))
    (fun i => ChoiceFreeWatts.sumIncl D i)
    (concrete_sum_additive_coproduct D)
    (fun i => concretePure (R := R) (M := M) (X := D i))
    (concretePure (R := R) (M := M) (X := ChoiceFreeWatts.sumObj D))
    (fun i => concretePure_isBalancedTensor (R := R) (S := S) (M := M) (X := D i))
    (concretePure_isBalancedTensor (R := R) (S := S) (M := M) (X := ChoiceFreeWatts.sumObj D))
    (fun i => concreteTensorMap (M := M) (S := S) (ChoiceFreeWatts.sumIncl D i))
    (fun i => concreteTensorMap_pure (M := M) (S := S) (ChoiceFreeWatts.sumIncl D i))

/-- The family of concrete tensor modules. -/
def concreteTensorFamily (i : I) : ModuleCat.{v} S :=
  ModuleCat.of S (ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) (D i))

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map from the direct sum of the tensors to the tensor of
the direct sum is an isomorphism, including for an empty index set. -/
theorem concrete_tensor_direct_sum_iso :
    ∃ e : (ChoiceFreeWatts.sumObj (concreteTensorFamily (S := S) (M := M) D)) ≃ₗ[S]
          ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) (ChoiceFreeWatts.sumObj D),
      ∀ i m x, e (ChoiceFreeWatts.summand (concreteTensorFamily (S := S) (M := M) D) i
        (concretePure (R := R) (M := M) m x)) =
        concretePure (R := R) (M := M) m (ChoiceFreeWatts.sumIncl D i x) := by
  let family := concreteTensorFamily (S := S) (M := M) D
  let ti : ∀ i, family i →ₗ[S]
      ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) (ChoiceFreeWatts.sumObj D) :=
    fun i => concreteTensorMap (M := M) (S := S) (ChoiceFreeWatts.sumIncl D i)
  let f := ChoiceFreeWatts.sumLift family ti
  obtain ⟨g, hg, gunique⟩ := concrete_tensor_preserves_coproduct (M := M) (S := S) D
    (ChoiceFreeWatts.sumObj family) (fun i => ChoiceFreeWatts.sumIncl family i)
  have fg : f.comp g = LinearMap.id := by
    obtain ⟨a, ha, unique⟩ := concrete_tensor_preserves_coproduct (M := M) (S := S) D
      (ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) (ChoiceFreeWatts.sumObj D)) ti
    have hfg : ∀ i t, (f.comp g) (ti i t) = ti i t := by
      intro i t
      change f (g (concreteTensorMap (M := M) (S := S) (ChoiceFreeWatts.sumIncl D i) t)) = ti i t
      rw [hg]
      exact ChoiceFreeWatts.sumLift_summand family ti i t
    have hid : ∀ i t, (LinearMap.id : ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) (ChoiceFreeWatts.sumObj D) →ₗ[S] _) (ti i t) = ti i t := by intros; rfl
    exact (unique _ hfg).trans (unique _ hid).symm
  have gf : g.comp f = LinearMap.id := by
    apply LinearMap.toAddMonoidHom_injective
    apply ChoiceFreeWatts.sumExt family
    intro i t
    change g (f (ChoiceFreeWatts.summand family i t)) = ChoiceFreeWatts.summand family i t
    rw [ChoiceFreeWatts.sumLift_summand]
    change g (concreteTensorMap (M := M) (S := S) (ChoiceFreeWatts.sumIncl D i) t) = _
    exact hg i t
  refine ⟨LinearEquiv.ofLinearMap f g fg gf, ?_⟩
  intro i m x
  change ChoiceFreeWatts.sumLift family ti (ChoiceFreeWatts.summand family i _) = _
  rw [ChoiceFreeWatts.sumLift_summand]
  exact concreteTensorMap_pure (M := M) (S := S) (ChoiceFreeWatts.sumIncl D i) m x

#print axioms concrete_tensor_direct_sum_iso
#print axioms concrete_sum_additive_coproduct
#print axioms concrete_tensor_preserves_coproduct

end NotesProofs
