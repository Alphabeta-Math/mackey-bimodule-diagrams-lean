import MackeyDiagrams.PlanarShape
import Mathlib.Algebra.BigOperators.Finprod

/-! A pointwise finite indexed drawing keeps one sum scope, even for an
infinite index type. Its evaluation is defined at each input using the finite
set of summands which are nonzero there. This is a separate operation from a
finite formal linear combination: no membership in the finite diagram algebra
is asserted merely from pointwise finiteness. -/

namespace MackeyDiagrams

universe u v w
variable {U : Type u} [Group U] {K H : Subgroup U}
variable {R : Type v} [CommSemiring R]

structure PointwiseIndexedDrawing (R : Type v) [CommSemiring R]
    {K H : Subgroup U} (p q : Word K H) (ι : Type w) where
  summand : ι → LabelledDrawing R p q
  finiteSupport : ∀ x : p.basis.carrier →₀ R,
    Set.Finite (Function.support fun i =>
      (summand i).interpret.eval.toLinearMap x)

namespace PointwiseIndexedDrawing

variable {p q : Word K H} {ι : Type w}

/-- One indexed sum scope whose entries retain their own geometric shapes. -/
structure Shape (ι : Type w) where
  summand : ι → PlanarShape

def shape (d : PointwiseIndexedDrawing R p q ι) : Shape ι :=
  ⟨fun i => (d.summand i).planarShape⟩

/-- Evaluate the sum on one input, without changing its stored shape. -/
noncomputable def evalAt (d : PointwiseIndexedDrawing R p q ι)
    (x : p.basis.carrier →₀ R) : q.basis.carrier →₀ R :=
  ∑ i ∈ (d.finiteSupport x).toFinset,
    (d.summand i).interpret.eval.toLinearMap x

@[simp] theorem evalAt_def (d : PointwiseIndexedDrawing R p q ι)
    (x : p.basis.carrier →₀ R) :
    d.evalAt x = ∑ i ∈ (d.finiteSupport x).toFinset,
      (d.summand i).interpret.eval.toLinearMap x := rfl

theorem evalAt_eq_finsum (d : PointwiseIndexedDrawing R p q ι)
    (x : p.basis.carrier →₀ R) :
    d.evalAt x = ∑ᶠ i, (d.summand i).interpret.eval.toLinearMap x := by
  exact (finsum_eq_sum _ (d.finiteSupport x)).symm

/-- The pointwise sum is a linear map, despite possibly infinitely many
    summands being needed across different inputs. -/
noncomputable def eval (d : PointwiseIndexedDrawing R p q ι) :
    (p.basis.carrier →₀ R) →ₗ[R] (q.basis.carrier →₀ R) where
  toFun := d.evalAt
  map_add' x y := by
    rw [evalAt_eq_finsum, evalAt_eq_finsum, evalAt_eq_finsum,
      ← finsum_add_distrib (d.finiteSupport x) (d.finiteSupport y)]
    apply finsum_congr
    intro i
    exact map_add (d.summand i).interpret.eval.toLinearMap x y
  map_smul' c x := by
    change d.evalAt (c • x) = c • d.evalAt x
    rw [evalAt_eq_finsum, evalAt_eq_finsum, smul_finsum' c (d.finiteSupport x)]
    apply finsum_congr
    intro i
    exact map_smul (d.summand i).interpret.eval.toLinearMap c x

@[simp] theorem eval_apply (d : PointwiseIndexedDrawing R p q ι)
    (x : p.basis.carrier →₀ R) : d.eval x = d.evalAt x := rfl

end PointwiseIndexedDrawing
end MackeyDiagrams
