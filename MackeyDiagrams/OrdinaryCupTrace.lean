import MackeyDiagrams.StructuralBasis

/-! An ordinary cup closes under the subgroup trace with coefficient one. -/

namespace MackeyDiagrams.Diagram

universe u v

variable {U : Type u} [Group U] {A B : Subgroup U}
variable {R : Type v} [CommSemiring R]

theorem eval_ordinaryCup_single (a : ConjEmbedding A B) (x : A) (r : R) :
    (ordinaryCup (R := R) a).eval.toLinearMap (Finsupp.single x r) =
      Finsupp.single ((Biset.restriction a).pair (Biset.induction a) (a.toHom x) 1) r := by
  change (Generator.ordinaryCup R a).toLinearMap _ = _
  rw [Generator.ordinaryCup, Biset.Hom.ofFunction_single]

theorem ordinaryCup_traceCap (a : ConjEmbedding A B) :
    ((ordinaryCup (R := R) a).vertical (traceCap a)).eval = (id (.empty A)).eval := by
  apply eval_ext
  intro x r
  change A at x
  change (traceCap a).eval.toLinearMap ((ordinaryCup a).eval.toLinearMap (Finsupp.single x r)) =
    Finsupp.single x r
  rw [eval_ordinaryCup_single (R := R) a x r, eval_traceCap_single, mul_one,
    Generator.traceBasis_image, Finsupp.smul_single, smul_eq_mul, mul_one]

end MackeyDiagrams.Diagram
