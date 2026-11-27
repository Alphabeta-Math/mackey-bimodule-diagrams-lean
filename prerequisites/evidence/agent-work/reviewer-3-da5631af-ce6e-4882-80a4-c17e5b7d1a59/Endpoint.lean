import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.EssentiallySmall

universe u v

def endpoint : Prop :=
  ∀ (R : Type u) [Ring R], CategoryTheory.LocallySmall.{v} (ModuleCat.{v} R) ∧ Nonempty (CategoryTheory.Abelian (ModuleCat.{v} R))

set_option pp.universes true in
#print endpoint

#check CategoryTheory.Abelian.ofCoimageImageComparisonIsIso
