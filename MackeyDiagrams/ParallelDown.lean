import MackeyDiagrams.Parallel

/-! The parallel Reidemeister II calculation for two restriction strands. -/

namespace MackeyDiagrams.Diagram

universe u v
variable {U : Type u} [Group U] {G K H : Subgroup U}
variable {R : Type v} [CommSemiring R]

@[simp] theorem eval_mergeDown_single (b : ConjEmbedding H G) (a : ConjEmbedding K H)
    (x : H) (y : G) (r : R) :
    (mergeDown (R := R) b a).eval.toLinearMap
        (Finsupp.single ((Biset.restriction a).pair (Biset.restriction b) x y) r) =
      Finsupp.single (b.toHom x * y) r := by
  change (Generator.mergeDown R b a).toLinearMap _ = _
  unfold Generator.mergeDown
  rw [Biset.Hom.ofFunction_single]
  rfl

@[simp] theorem eval_splitDown_single (b : ConjEmbedding H G) (a : ConjEmbedding K H)
    (x : G) (r : R) :
    (splitDown (R := R) b a).eval.toLinearMap (Finsupp.single x r) =
      Finsupp.single ((Biset.restriction a).pair (Biset.restriction b) 1 x) r := by
  change (Generator.splitDown R b a).toLinearMap _ = _
  unfold Generator.splitDown
  rw [Biset.Hom.ofFunction_single]

theorem mergeDown_splitDown (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
    ((mergeDown (R := R) b a).vertical (splitDown b a)).eval =
      (id ((Word.down a).tensor (.down b))).eval := by
  apply eval_ext
  intro z r
  refine Quotient.inductionOn z (fun xy => ?_)
  rcases xy with ⟨x,y⟩
  change (splitDown b a).eval.toLinearMap
      ((mergeDown b a).eval.toLinearMap
        (Finsupp.single ((Biset.restriction a).pair (Biset.restriction b) x y) r)) = _
  rw [eval_mergeDown_single, eval_splitDown_single, eval_id_apply]
  change Finsupp.single ((Biset.restriction a).pair (Biset.restriction b) 1 (b.toHom x * y)) r =
    Finsupp.single ((Biset.restriction a).pair (Biset.restriction b) x y) r
  apply congrArg (fun z => Finsupp.single z r)
  simpa [Biset.restriction] using
    ((Biset.restriction a).pair_balance (Biset.restriction b) x 1 y).symm

theorem splitDown_mergeDown (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
    ((splitDown (R := R) b a).vertical (mergeDown b a)).eval = (id (.down (b.comp a))).eval := by
  apply eval_ext
  intro x r
  change G at x
  rw [eval_vertical_apply, eval_splitDown_single, eval_mergeDown_single, eval_id_apply,
    map_one, one_mul]

def parallelDown {H' : Subgroup U}
    (b : ConjEmbedding H G) (a : ConjEmbedding K H)
    (b' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
    (d : Dot (b.comp a) (b'.comp a')) :
    Diagram R ((Word.down a).tensor (.down b)) ((Word.down a').tensor (.down b')) :=
  ((mergeDown b a).vertical (downDot d)).vertical (splitDown b' a')

theorem parallelDown_comp {H' H'' : Subgroup U}
    (b : ConjEmbedding H G) (a : ConjEmbedding K H)
    (b' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
    (b'' : ConjEmbedding H'' G) (a'' : ConjEmbedding K H'')
    (d : Dot (b.comp a) (b'.comp a')) (e : Dot (b'.comp a') (b''.comp a'')) :
    ((parallelDown (R := R) b a b' a' d).vertical (parallelDown b' a' b'' a'' e)).eval =
      (parallelDown b a b'' a'' (d.vertical e)).eval := by
  apply eval_ext
  intro z r
  refine Quotient.inductionOn z (fun xy => ?_)
  rcases xy with ⟨x,y⟩
  change H at x
  change G at y
  change ((parallelDown (R := R) b a b' a' d).vertical (parallelDown b' a' b'' a'' e)).eval.toLinearMap
      (Finsupp.single ((Biset.restriction a).pair (Biset.restriction b) x y) r) =
    (parallelDown b a b'' a'' (d.vertical e)).eval.toLinearMap
      (Finsupp.single ((Biset.restriction a).pair (Biset.restriction b) x y) r)
  let input := Finsupp.single ((Biset.restriction a).pair (Biset.restriction b) x y) r
  change (splitDown b'' a'').eval.toLinearMap
      ((downDot e).eval.toLinearMap
        ((mergeDown b' a').eval.toLinearMap
          ((splitDown b' a').eval.toLinearMap
            ((downDot d).eval.toLinearMap ((mergeDown b a).eval.toLinearMap input))))) =
    (splitDown b'' a'').eval.toLinearMap
      ((downDot (d.vertical e)).eval.toLinearMap ((mergeDown b a).eval.toLinearMap input))
  dsimp only [input]
  rw [eval_mergeDown_single (R := R) b a x y r,
    eval_downDot_single (R := R) d (b.toHom x * y) r,
    eval_splitDown_single (R := R) b' a' (d.element⁻¹ * (b.toHom x * y)) r,
    eval_mergeDown_single (R := R) b' a' 1 (d.element⁻¹ * (b.toHom x * y)) r]
  simp only [map_one, one_mul]
  rw [eval_downDot_single (R := R) e (d.element⁻¹ * (b.toHom x * y)) r,
    eval_downDot_single (R := R) (d.vertical e) (b.toHom x * y) r]
  simp only [Dot.vertical, mul_inv_rev, mul_assoc]

theorem parallelDown_return {H' : Subgroup U}
    (b : ConjEmbedding H G) (a : ConjEmbedding K H)
    (b' : ConjEmbedding H' G) (a' : ConjEmbedding K H')
    (d : Dot (b.comp a) (b'.comp a')) :
    ((parallelDown (R := R) b a b' a' d).vertical (parallelDown b' a' b a d.inverse)).eval =
      (id ((Word.down a).tensor (.down b))).eval := by
  rw [parallelDown_comp, Dot.then_inverse]
  have hd : (downDot (R := R) (Dot.id (b.comp a))).eval = (id (.down (b.comp a))).eval := by
    apply eval_ext
    intro x r
    change G at x
    rw [eval_downDot_single (R := R) (Dot.id (b.comp a)) x r, eval_id_apply]
    simp [Dot.id]
  apply eval_ext
  intro z r
  change (splitDown b a).eval.toLinearMap
      ((downDot (Dot.id (b.comp a))).eval.toLinearMap
        ((mergeDown b a).eval.toLinearMap (Finsupp.single z r))) = _
  rw [hd, eval_id_apply]
  exact LinearMap.congr_fun
    (congrArg Biset.Hom.toLinearMap (mergeDown_splitDown (R := R) b a)) _

end MackeyDiagrams.Diagram
