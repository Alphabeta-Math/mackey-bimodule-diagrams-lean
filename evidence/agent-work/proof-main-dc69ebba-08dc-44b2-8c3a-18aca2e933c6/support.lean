namespace ParallelReidemeisterTwoInductionProof

open MackeyDiagrams

variable {U : Type*} [Group U] {G K H B : Subgroup U}
variable {R : Type*} [CommSemiring R]

-- The crossing constructor interprets a sum of complete crossings. Move the
-- fixed merge and split through that sum at the level of linear maps.
private theorem eval_parallelUp_terms
    (a : ConjEmbedding H G) (b : ConjEmbedding K H)
    (c : ConjEmbedding B G) (d : ConjEmbedding K B)
    (terms : List (R × Dot (a.comp b) (c.comp d))) :
    (LabelledDrawing.parallelUp a b c d terms).interpret.eval =
      ((Diagram.mergeUp (R := R) a b).eval.vertical
        (LabelledDrawing.upDot terms).interpret.eval).vertical (Diagram.splitUp c d).eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  change (ScopedDiagram.linearCombination
      (terms.map fun (r, t) => (r, ScopedDiagram.ordinary (Diagram.parallelUp a b c d t)))).eval.toLinearMap z =
    (Diagram.splitUp c d).eval.toLinearMap
      ((Diagram.finiteSum (terms.map fun (r,t) => Diagram.scale r (Diagram.upDot t))).eval.toLinearMap
        ((Diagram.mergeUp a b).eval.toLinearMap z))
  rw [ScopedDiagram.eval_linearCombination_apply, Diagram.eval_finiteSum]
  induction terms with
  | nil => simp
  | cons term rest ih =>
    rcases term with ⟨r, t⟩
    simp only [List.map_cons, List.sum_cons, map_add]
    have scaled :
        (Diagram.scale r (Diagram.upDot t)).eval.toLinearMap
            ((Diagram.mergeUp a b).eval.toLinearMap z) =
          r • (Diagram.upDot (R := R) t).eval.toLinearMap
            ((Diagram.mergeUp a b).eval.toLinearMap z) := rfl
    rw [ih, scaled, map_smul]
    rfl

private theorem eval_parallelUp_single [Nontrivial R]
    (a : ConjEmbedding H G) (b : ConjEmbedding K H)
    (c : ConjEmbedding B G) (d : ConjEmbedding K B)
    (t : Dot (a.comp b) (c.comp d)) :
    (LabelledDrawing.parallelUp a b c d
        (DotLabel.terms (Finsupp.single t (1 : R)))).interpret.eval =
      (Diagram.parallelUp a b c d t (R := R)).eval := by
  classical
  have h : DotLabel.terms (Finsupp.single t (1 : R)) =
      (Finsupp.single t (1 : R)).support.toList.map
        (fun p => ((Finsupp.single t (1 : R)) p, p)) := rfl
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  change (ScopedDiagram.linearCombination
      ((DotLabel.terms (Finsupp.single t (1 : R))).map
        fun (r, p) => (r, ScopedDiagram.ordinary (Diagram.parallelUp a b c d p)))).eval.toLinearMap z = _
  rw [ScopedDiagram.eval_linearCombination_apply, h, Finsupp.support_single _ one_ne_zero]
  simp [ScopedDiagram.eval]

private theorem compose_singletons
    {a b c : ConjEmbedding K G} (x : Dot a b) (y : Dot b c) :
    DotLabel.compose (Finsupp.single x (1 : R)) (Finsupp.single y 1) =
      Finsupp.single (x.vertical y) 1 := by
  unfold DotLabel.compose Dot.linearProduct
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
  · rw [mul_one]
  · simp
  · simp

private theorem eval_transported_up_id {a b : ConjEmbedding K G} (same : a = b) :
    (LabelledDrawing.interpret
      (Eq.ndrec (motive := fun e => LabelledDrawing R (.up a) (.up e))
        (.ordinary (Diagram.id (.up a))) same)).eval = (Diagram.transportUpId same).eval := by
  cases same
  rfl

private theorem eval_transported_word_id {p q : Word G K} (same : p = q) :
    (LabelledDrawing.interpret
      (Eq.ndrec (motive := fun w => LabelledDrawing R p w)
        (.ordinary (Diagram.id p)) same)).eval =
    (Eq.ndrec (motive := fun w => Diagram R p w) (Diagram.id p) same).eval := by
  cases same
  rfl

end ParallelReidemeisterTwoInductionProof

open MackeyDiagrams ParallelReidemeisterTwoInductionProof
