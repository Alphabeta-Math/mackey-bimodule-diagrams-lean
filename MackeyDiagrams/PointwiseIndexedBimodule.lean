import MackeyDiagrams.PointwiseIndexedDrawing

namespace MackeyDiagrams
universe u v w
variable {U : Type u} [Group U] {K H : Subgroup U}
variable {R : Type v} [CommSemiring R]
variable {p q : Word K H} {ι : Type w}

namespace PointwiseIndexedDrawing

/-- Evaluation of a pointwise-finite drawing sum is a bimodule map. -/
noncomputable def evalHom (d : PointwiseIndexedDrawing R p q ι) :
    Biset.Hom R p.basis q.basis where
  toLinearMap := d.eval
  commutes := by
    intro g x
    change d.evalAt (p.basis.actLinear R g x) = q.basis.actLinear R g (d.evalAt x)
    rw [d.evalAt_eq_finsum, d.evalAt_eq_finsum]
    rw [map_finsum (q.basis.actLinear R g) (d.finiteSupport x)]
    apply finsum_congr
    intro i
    exact (d.summand i).interpret.eval.commutes g x

@[simp] theorem evalHom_apply (d : PointwiseIndexedDrawing R p q ι)
    (x : p.basis.carrier →₀ R) : d.evalHom.toLinearMap x = d.evalAt x := rfl

end PointwiseIndexedDrawing
end MackeyDiagrams
