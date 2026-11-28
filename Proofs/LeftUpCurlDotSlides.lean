import MackeyDiagrams

/-! The dot on an upward strand slides across a left curl without an index
factor. The lower junction uses an ordinary cup; the upper junction uses
the subgroup trace. -/

universe u v

namespace MackeyDiagrams.Diagram

variable {U : Type u} [Group U] {K H G : Subgroup U}
variable {R : Type v} [CommSemiring R]

/-- The left curl on an upward strand, built from the two typed trivalent junctions. -/
def leftUpCurl (a : ConjEmbedding H G) (b : ConjEmbedding K H) :
    Diagram R (.up b) (.up b) :=
  (TrivalentVertex.upToDownUp a b).expand.vertical (TrivalentVertex.downUpToUp a b).expand

/-- Put the whiskered dot on the composite upward strand inside the left curl. -/
def leftUpCurlInside (a : ConjEmbedding H G) {b c : ConjEmbedding K H} (e : Dot b c) :
    Diagram R (.up b) (.up c) :=
  (TrivalentVertex.upToDownUp a b).expand.vertical
    (((id (.down a)).horizontal (upDot (e.whisker a))).vertical
      (TrivalentVertex.downUpToUp a c).expand)

private theorem eval_leftUpCurlLower_single (a : ConjEmbedding H G)
    (b : ConjEmbedding K H) (x : H) (r : R) :
    ((TrivalentVertex.upToDownUp a b).expand (R := R)).eval.toLinearMap (Finsupp.single x r) =
      Finsupp.single ((Biset.restriction a).pair (Biset.induction (a.comp b))
        1 (a.toHom x)) r := by
  change ((id (R := R) (.down a)).horizontal (mergeUp a b)).eval.toLinearMap
    ((associate (.down a) (.up a) (.up b)).eval.toLinearMap
      (((ordinaryCup a).horizontal (id (.up b))).eval.toLinearMap
        ((insertLeftUnit (.up b)).eval.toLinearMap (Finsupp.single x r)))) = _
  rw [eval_insertLeftUnit_single, eval_horizontal_single, eval_ordinaryCup_single,
    eval_id_apply, map_one, Biset.pairLinear_single, one_mul]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [eval_associate_single, eval_horizontal_single, eval_id_apply, eval_mergeUp_single,
    one_mul, Biset.pairLinear_single, one_mul]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]

private theorem eval_leftUpCurlUpper_single (a : ConjEmbedding H G)
    (b : ConjEmbedding K H) (x : H) (r : R) :
    ((TrivalentVertex.downUpToUp a b).expand (R := R)).eval.toLinearMap
        (Finsupp.single ((Biset.restriction a).pair (Biset.induction (a.comp b))
          1 (a.toHom x)) r) = Finsupp.single x r := by
  have h := eval_traceCapOnLeft_image (R := R) a b 1 (a.toHom x) x (one_mul _)
  change (traceCapOnLeft a b).eval.toLinearMap _ = _
  rw [show Finsupp.single
      ((Biset.restriction a).pair (Biset.induction (a.comp b)) 1 (a.toHom x)) r =
      r • Finsupp.single
      ((Biset.restriction a).pair (Biset.induction (a.comp b)) 1 (a.toHom x)) (1 : R) by
        simp, map_smul, h]
  simp

private theorem eval_leftUpCurl_single (a : ConjEmbedding H G)
    (b : ConjEmbedding K H) (x : H) (r : R) :
    (leftUpCurl (R := R) a b).eval.toLinearMap (Finsupp.single x r) = Finsupp.single x r := by
  rw [leftUpCurl, eval_vertical_apply, eval_leftUpCurlLower_single, eval_leftUpCurlUpper_single]

/-- The three typed placements of an eligible dot at a left curl on an up-strand
all evaluate to that dot. The inside label is the image under the fixed outer
embedding, and no finite-index hypothesis is needed. -/
theorem leftUpCurl_dotSlides (a : ConjEmbedding H G) {b c : ConjEmbedding K H}
    (e : Dot b c) :
    ((upDot (R := R) e).vertical (leftUpCurl a c)).eval = (upDot e).eval ∧
    (leftUpCurlInside (R := R) a e).eval = (upDot e).eval ∧
    ((leftUpCurl (R := R) a b).vertical (upDot e)).eval = (upDot e).eval := by
  refine ⟨?_, ?_, ?_⟩
  · apply eval_ext
    intro x r
    rw [eval_vertical_apply, eval_upDot_single, eval_leftUpCurl_single]
  · apply eval_ext
    intro x r
    change H at x
    rw [leftUpCurlInside, eval_vertical_apply, eval_vertical_apply,
      eval_leftUpCurlLower_single, eval_horizontal_single, eval_id_apply,
      eval_upDot_single (R := R) (e.whisker a), Biset.pairLinear_single, one_mul]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [show a.toHom x * (e.whisker a).element = a.toHom (x * e.element) by
      exact (map_mul a.toHom x e.element).symm]
    rw [eval_leftUpCurlUpper_single, eval_upDot_single]
  · apply eval_ext
    intro x r
    rw [eval_vertical_apply, eval_leftUpCurl_single]

end MackeyDiagrams.Diagram
