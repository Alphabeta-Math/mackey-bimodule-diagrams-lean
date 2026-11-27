import WattsFoundation.ConcreteTensorCoproduct
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Tensoring by an arbitrary bimodule is an additive functor. -/

set_option backward.isDefEq.respectTransparency false

namespace WattsFoundation

universe u
open CategoryTheory

variable {R S : Type u} [Ring R] [Ring S]
variable (M : Type u) [AddCommGroup M] [Module (MulOpposite R) M] [Module S M]
variable [SMulCommClass (MulOpposite R) S M]

local instance ConcreteTensorFunctor_local1 {X : Type u} [AddCommGroup X] [Module R X] :
    AddCommGroup (ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) X) :=
  ChoiceFreeWatts.tensorAddCommGroup _
local instance ConcreteTensorFunctor_local2 {X : Type u} [AddCommGroup X] [Module R X] :
    Module S (ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) X) :=
  ChoiceFreeWatts.outerModule _ right_commute

/-- Tensoring with an arbitrary S-R bimodule. -/
def concreteTensorFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} S where
  obj X := ModuleCat.of S (ChoiceFreeWatts.Tensor (rightAction (R := R) (M := M)) X)
  map f := ModuleCat.ofHom (concreteTensorMap (M := M) (S := S) f.hom)
  map_id X := by
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply ChoiceFreeWatts.tensorExt (rightAction (R := R) (M := M))
    intro m x
    change concreteTensorMap (M := M) (S := S) (LinearMap.id)
      (concretePure (R := R) (M := M) m x) = concretePure (R := R) (M := M) m x
    rw [concreteTensorMap_pure]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply ChoiceFreeWatts.tensorExt (rightAction (R := R) (M := M))
    intro m x
    change concreteTensorMap (M := M) (S := S) (g.hom.comp f.hom)
      (concretePure (R := R) (M := M) m x) =
      concreteTensorMap (M := M) (S := S) g.hom
        (concreteTensorMap (M := M) (S := S) f.hom (concretePure (R := R) (M := M) m x))
    rw [concreteTensorMap_pure, concreteTensorMap_pure, concreteTensorMap_pure]
    rfl

/-- Tensoring is additive on maps. -/
instance concreteTensorFunctor_additive : (concreteTensorFunctor (R := R) (S := S) M).Additive where
  map_add {X Y} {f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.toAddMonoidHom_injective
    apply ChoiceFreeWatts.tensorExt (rightAction (R := R) (M := M))
    intro m x
    change concreteTensorMap (M := M) (S := S) (f.hom + g.hom)
        (concretePure (R := R) (M := M) m x) =
      concreteTensorMap (M := M) (S := S) f.hom (concretePure (R := R) (M := M) m x) +
      concreteTensorMap (M := M) (S := S) g.hom (concretePure (R := R) (M := M) m x)
    rw [concreteTensorMap_pure, concreteTensorMap_pure, concreteTensorMap_pure]
    exact (ChoiceFreeWatts.pureBalanced (rightAction (R := R) (M := M))).2.1 m (f.hom x) (g.hom x)

#print axioms concreteTensorFunctor
#print axioms concreteTensorFunctor_additive

end WattsFoundation
