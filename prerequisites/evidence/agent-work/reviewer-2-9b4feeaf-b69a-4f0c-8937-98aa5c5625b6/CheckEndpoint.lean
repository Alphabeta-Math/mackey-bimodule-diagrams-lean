import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.EssentiallySmall

universe u v

def TranslatedEndpoint : Prop :=
  ∀ (R : Type u) [Ring R], CategoryTheory.LocallySmall.{v} (ModuleCat.{v} R) ∧ Nonempty (CategoryTheory.Abelian (ModuleCat.{v} R))

#check CategoryTheory.Abelian.ofCoimageImageComparisonIsIso
#check CategoryTheory.Abelian.coimageIsoImage

section
variable (R : Type u) [Ring R]
#synth CategoryTheory.LocallySmall.{v} (ModuleCat.{v} R)
#synth CategoryTheory.Abelian (ModuleCat.{v} R)
end
