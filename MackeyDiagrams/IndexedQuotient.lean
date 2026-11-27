import MackeyDiagrams.DiagramVectorSpace
import MackeyDiagrams.IndexedDrawing

namespace MackeyDiagrams.DiagramVectorSpace
universe u v w z
variable {U : Type u} [Group U] {K H : Subgroup U}
variable (R : Type v) [CommRing R] (p q : Word K H) {ι : Type w}

/-- Forget only the indexed-scope geometry, retaining every evaluated summand. -/
noncomputable def indexedExpressions (d : IndexedDrawing R p q ι) : Expressions R p q := by
  classical
  exact ∑ i ∈ d.indices, Finsupp.single (d.summand i) 1

theorem indexedExpressions_eval (d : IndexedDrawing R p q ι) :
    evaluate R p q (indexedExpressions R p q d) = d.eval := by
  classical
  simp [indexedExpressions, IndexedDrawing.eval, singleton_eval]

/-- Indexed sums have equal classes exactly when their maps agree, while their
    separate `IndexedDrawing.shape` values remain available. -/
theorem indexedClasses_eq_iff {κ : Type z} (d : IndexedDrawing R p q ι)
    (e : IndexedDrawing R p q κ) :
    (Submodule.Quotient.mk (indexedExpressions R p q d) : MapClasses R p q) =
      Submodule.Quotient.mk (indexedExpressions R p q e) ↔ d.eval = e.eval := by
  rw [quotient_eq_iff, indexedExpressions_eval, indexedExpressions_eval]

end MackeyDiagrams.DiagramVectorSpace
