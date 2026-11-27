namespace MackeyDiagrams

private theorem parallelRIIRestriction_evalCrossing {U : Type*} [Group U]
    {K H H' G : Subgroup U} {R : Type*} [CommSemiring R]
    (a : ConjEmbedding H G) (b : ConjEmbedding K H)
    (a' : ConjEmbedding H' G) (b' : ConjEmbedding K H')
    (label : DotLabel R (a.comp b) (a'.comp b')) :
    (LabelledDrawing.parallelDown a b a' b' label.terms).interpret.eval =
      (Diagram.mergeDown (R := R) a b).eval.vertical
        (label.downDrawing.interpret.eval.vertical (Diagram.splitDown a' b').eval) := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  change (ScopedDiagram.linearCombination (label.terms.map fun (r, d) =>
      (r, ScopedDiagram.ordinary (Diagram.parallelDown a b a' b' d)))).eval.toLinearMap x =
    (Diagram.splitDown (R := R) a' b').eval.toLinearMap
      ((Diagram.finiteSum (label.terms.map fun (r, d) =>
        Diagram.scale r (Diagram.downDot d))).eval.toLinearMap
          ((Diagram.mergeDown (R := R) a b).eval.toLinearMap x))
  rw [ScopedDiagram.eval_linearCombination_apply, Diagram.eval_finiteSum]
  generalize label.terms = terms
  induction terms with
  | nil => simp
  | cons term terms ih =>
    rcases term with ⟨r, d⟩
    simp only [List.map_cons, List.sum_cons, map_add, ih]
    congr 1
    change r • (Diagram.splitDown (R := R) a' b').eval.toLinearMap
      ((Diagram.downDot d).eval.toLinearMap ((Diagram.mergeDown a b).eval.toLinearMap x)) =
      (Diagram.splitDown (R := R) a' b').eval.toLinearMap
        (r • (Diagram.downDot d).eval.toLinearMap ((Diagram.mergeDown a b).eval.toLinearMap x))
    rw [map_smul]

private theorem parallelRIIRestriction_evalSingleton {U : Type*} [Group U]
    {K G : Subgroup U} {p q : ConjEmbedding K G} (d : Dot p q) :
    (DotLabel.downDrawing (Finsupp.single d (1 : Complex))).interpret.eval =
      (Diagram.downDot (R := Complex) d).eval := by
  rw [DotLabel.eval_downDrawing]
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  exact (Diagram.eval_linearDownDot_apply (Finsupp.single d (1 : Complex)) x).trans (by
    rw [freeLift_single, one_smul])

end MackeyDiagrams
