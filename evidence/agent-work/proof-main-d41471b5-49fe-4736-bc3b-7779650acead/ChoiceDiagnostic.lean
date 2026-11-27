import Mathlib.Algebra.Category.ModuleCat.Ulift

private def extractComponents {ι : Type} {K : ι → Type} {P : ∀ i, K i → Prop}
    (h : ∀ i, ∃! k, P i k) : ∀ i, K i :=
  fun i => (h i).elim fun k _ => k
