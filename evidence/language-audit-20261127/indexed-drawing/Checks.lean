import MackeyDiagrams.IndexedDrawing

namespace MackeyDiagrams.IndexedDrawing
universe u v w
variable {U : Type u} [Group U] {K H : Subgroup U}
variable {R : Type v} [CommSemiring R] {p q : Word K H}
variable {ι : Type w} [DecidableEq ι]

example (i : ι) (f : ι → LabelledDrawing R p q) (x : p.basis.carrier →₀ R) :
    (IndexedDrawing.mk {i} f).eval x = (f i).interpret.eval.toLinearMap x := by
  simp [eval_apply]

example (s : Finset ι) (f : ι → LabelledDrawing R p q) :
    (IndexedDrawing.mk s f).shape.indices = s ∧
    ∀ i, (IndexedDrawing.mk s f).shape.summand i = (f i).planarShape := by
  exact ⟨rfl, fun _ => rfl⟩

#print axioms MackeyDiagrams.IndexedDrawing.eval_apply
#print axioms MackeyDiagrams.IndexedDrawing.shape
end MackeyDiagrams.IndexedDrawing
