import MackeyDiagrams.PlanarShape

/-! A finite indexed sum is one arithmetic scope containing complete typed
summands. The representation preserves the actual index type and set, not a
zero-seeded nest of binary drawing additions. -/

namespace MackeyDiagrams

universe u v w
variable {U : Type u} [Group U] {K H : Subgroup U}
variable {R : Type v} [CommSemiring R]

structure IndexedDrawing (R : Type v) [CommSemiring R] {K H : Subgroup U}
    (p q : Word K H) (ι : Type w) where
  indices : Finset ι
  summand : ι → LabelledDrawing R p q

namespace IndexedDrawing

variable {p q : Word K H} {ι : Type w}

/-- The single outer sum scope, retaining every indexed summand's geometry. -/
structure Shape (ι : Type w) where
  indices : Finset ι
  summand : ι → PlanarShape

def shape (d : IndexedDrawing R p q ι) : Shape ι :=
  ⟨d.indices, fun i => (d.summand i).planarShape⟩

/-- Evaluate the whole sum only after retaining its diagram scope. -/
noncomputable def eval (d : IndexedDrawing R p q ι) :
    (p.basis.carrier →₀ R) →ₗ[R] (q.basis.carrier →₀ R) :=
  ∑ i ∈ d.indices, (d.summand i).interpret.eval.toLinearMap

@[simp] theorem eval_apply (d : IndexedDrawing R p q ι) (x : p.basis.carrier →₀ R) :
    d.eval x = ∑ i ∈ d.indices, (d.summand i).interpret.eval.toLinearMap x := by
  simp [eval]

end IndexedDrawing
end MackeyDiagrams
