import Mathlib.CategoryTheory.NatIso
import Mathlib.Logic.Function.Basic

open CategoryTheory

#print axioms NatIso.isIso_of_isIso_app
#print axioms Function.bijective_iff_has_inverse

universe u v
variable {I : Type u} {F : I → Type v} {valid : (i : I) → F i → Prop}

-- Diagnostic for turning pointwise unique witnesses into component data.
def assemble (h : ∀ i, ∃! f : F i, valid i f) : (i : I) → F i :=
  fun i => match h i with
    | ⟨f, _⟩ => f
