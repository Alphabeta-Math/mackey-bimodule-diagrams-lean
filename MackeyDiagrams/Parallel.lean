import MackeyDiagrams.Identities

/-!
# Parallel Reidemeister II for upward strands

All three two-strand words may have different intermediate groups.
-/

namespace MackeyDiagrams.Diagram

universe u v
variable {U : Type u} [Group U] {G K H : Subgroup U}
variable {R : Type v} [CommSemiring R]

@[simp] theorem eval_splitUp_single (b : ConjEmbedding H G) (a : ConjEmbedding K H)
    (x : G) (r : R) :
    (splitUp (R := R) b a).eval.toLinearMap (Finsupp.single x r) =
      Finsupp.single ((Biset.induction b).pair (Biset.induction a) x 1) r := by
  change (Generator.splitUp R b a).toLinearMap _ = _
  unfold Generator.splitUp
  rw [Biset.Hom.ofFunction_single]

theorem mergeUp_splitUp (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
    ((mergeUp (R := R) b a).vertical (splitUp b a)).eval =
      (id ((Word.up b).tensor (.up a))).eval := by
  apply eval_ext
  intro z r
  refine Quotient.inductionOn z (fun xy => ?_)
  rcases xy with ⟨x,y⟩
  change (splitUp b a).eval.toLinearMap
      ((mergeUp b a).eval.toLinearMap
        (Finsupp.single ((Biset.induction b).pair (Biset.induction a) x y) r)) = _
  rw [eval_mergeUp_single (R := R) b a x y r, eval_splitUp_single]
  change Finsupp.single ((Biset.induction b).pair (Biset.induction a) (x * b.toHom y) 1) r =
    Finsupp.single ((Biset.induction b).pair (Biset.induction a) x y) r
  apply congrArg (fun z => Finsupp.single z r)
  simpa [Biset.induction] using (Biset.induction b).pair_balance (Biset.induction a) y x 1

theorem splitUp_mergeUp (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
    ((splitUp (R := R) b a).vertical (mergeUp b a)).eval = (id (.up (b.comp a))).eval := by
  apply eval_ext
  intro x r
  change G at x
  change (mergeUp b a).eval.toLinearMap
      ((splitUp b a).eval.toLinearMap (Finsupp.single x r)) = _
  rw [eval_splitUp_single (R := R) b a x r, eval_mergeUp_single (R := R) b a x 1 r]
  rw [eval_id_apply]
  simp

theorem eval_upDot_id (a : ConjEmbedding K G) :
    (upDot (R := R) (Dot.id a)).eval = (id (.up a)).eval := by
  apply eval_ext
  intro x r
  change G at x
  rw [eval_upDot_single (R := R) (Dot.id a) x r]
  rw [eval_id_apply]
  simp [Dot.id]

def parallelUp {H' : Subgroup U}
    (b : ConjEmbedding H G) (a : ConjEmbedding K H)
    (b' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
    (d : Dot (b.comp a) (b'.comp a')) :
    Diagram R ((Word.up b).tensor (.up a)) ((Word.up b').tensor (.up a')) :=
  ((mergeUp b a).vertical (upDot d)).vertical (splitUp b' a')

/-- Two labelled crossings reduce to a single merge–dot–split. -/
theorem parallelUp_comp {H' H'' : Subgroup U}
    (b : ConjEmbedding H G) (a : ConjEmbedding K H)
    (b' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
    (b'' : ConjEmbedding H'' G) (a'' : ConjEmbedding K H'')
    (d : Dot (b.comp a) (b'.comp a')) (e : Dot (b'.comp a') (b''.comp a'')) :
    ((parallelUp (R := R) b a b' a' d).vertical (parallelUp b' a' b'' a'' e)).eval =
      (parallelUp b a b'' a'' (d.vertical e)).eval := by
  apply eval_ext
  intro z r
  refine Quotient.inductionOn z (fun xy => ?_)
  rcases xy with ⟨x,y⟩
  change G at x
  change H at y
  change ((parallelUp (R := R) b a b' a' d).vertical (parallelUp b' a' b'' a'' e)).eval.toLinearMap
      (Finsupp.single ((Biset.induction b).pair (Biset.induction a) x y) r) =
    (parallelUp b a b'' a'' (d.vertical e)).eval.toLinearMap
      (Finsupp.single ((Biset.induction b).pair (Biset.induction a) x y) r)
  let input := Finsupp.single ((Biset.induction b).pair (Biset.induction a) x y) r
  change (splitUp b'' a'').eval.toLinearMap
      ((upDot e).eval.toLinearMap
        ((mergeUp b' a').eval.toLinearMap
          ((splitUp b' a').eval.toLinearMap
            ((upDot d).eval.toLinearMap ((mergeUp b a).eval.toLinearMap input))))) =
    (splitUp b'' a'').eval.toLinearMap
      ((upDot (d.vertical e)).eval.toLinearMap ((mergeUp b a).eval.toLinearMap input))
  dsimp only [input]
  rw [eval_mergeUp_single (R := R) b a x y r, eval_upDot_single (R := R) d (x * b.toHom y) r,
    eval_splitUp_single (R := R) b' a' (x * b.toHom y * d.element) r,
    eval_mergeUp_single (R := R) b' a' (x * b.toHom y * d.element) 1 r]
  simp only [map_one, mul_one]
  rw [eval_upDot_single (R := R) e (x * b.toHom y * d.element) r,
    eval_upDot_single (R := R) (d.vertical e) (x * b.toHom y) r]
  simp only [Dot.vertical, mul_assoc]

theorem parallelUp_return {H' : Subgroup U}
    (b : ConjEmbedding H G) (a : ConjEmbedding K H)
    (b' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
    (d : Dot (b.comp a) (b'.comp a')) :
    ((parallelUp (R := R) b a b' a' d).vertical (parallelUp b' a' b a d.inverse)).eval =
      (id ((Word.up b).tensor (.up a))).eval := by
  rw [parallelUp_comp, Dot.then_inverse]
  apply eval_ext
  intro z r
  change (splitUp b a).eval.toLinearMap
      ((upDot (Dot.id (b.comp a))).eval.toLinearMap
        ((mergeUp b a).eval.toLinearMap (Finsupp.single z r))) = _
  rw [eval_upDot_id (R := R) (b.comp a), eval_id_apply]
  exact LinearMap.congr_fun
    (congrArg Biset.Hom.toLinearMap (mergeUp_splitUp (R := R) b a)) _

end MackeyDiagrams.Diagram

