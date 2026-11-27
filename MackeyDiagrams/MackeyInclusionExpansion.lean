import MackeyDiagrams.OrdinaryCupTrace
import MackeyDiagrams.CupCapIdentities
import MackeyDiagrams.MackeyOrthogonality

/-! The drawn Mackey inclusion expands using an ordinary cup, one dot,
and a multiplication cap. -/

namespace MackeyDiagrams.Diagram

universe u v

variable {U : Type u} [Group U] {K H G L : Subgroup U}
variable {R : Type v} [CommSemiring R]

def expandedMackeyInclusion (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H) (d : Dot (a.comp l) (b.comp r)) :
    Diagram R ((Word.up l).tensor (.down r)) ((Word.down a).tensor (.up b)) :=
  let kg := Word.down a
  let gk := Word.up a
  let gh := Word.up b
  let kl := Word.up l
  let lh := Word.down r
  let hl := Word.up r
  let Mj := kl.tensor lh
  .vertical (.insertLeftUnit Mj)
    (.vertical (.horizontal (.ordinaryCup a) (.id Mj))
      (.vertical (.associate kg gk Mj)
        (.vertical (.horizontal (.id kg) (.unassociate gk kl lh))
          (.vertical (.horizontal (.id kg) (.horizontal
              (.vertical (.mergeUp a l) (.vertical (.upDot d) (.splitUp b r))) (.id lh)))
            (.vertical (.horizontal (.id kg) (.associate gh hl lh))
              (.vertical (.horizontal (.id kg) (.horizontal (.id gh) (.multiplicationCap r)))
                (.horizontal (.id kg) (.rightUnit gh))))))))

theorem eval_expandedMackeyInclusion (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H) (d : Dot (a.comp l) (b.comp r)) :
    (expandedMackeyInclusion (R := R) a b l r d).eval = (mixedMultiplication a b l r d).eval := by
  apply eval_ext_on_generators
  intro z
  refine Quotient.inductionOn z (fun xy => ?_)
  rcases xy with ⟨k,h⟩
  change K at k
  change H at h
  let kg := Word.down a
  let gk := Word.up a
  let gh := Word.up b
  let kl := Word.up l
  let lh := Word.down r
  let hl := Word.up r
  let Mj := kl.tensor lh
  let v := kl.basis.pair lh.basis k h
  let dot := (mergeUp (R := R) a l).vertical ((upDot d).vertical (splitUp b r))
  let x := a.toHom k * d.element
  have hdot : dot.eval.toLinearMap (Finsupp.single (gk.basis.pair kl.basis 1 k) 1) =
      Finsupp.single (gh.basis.pair hl.basis x 1) 1 := by
    change (splitUp (R := R) b r).eval.toLinearMap
      ((upDot d).eval.toLinearMap ((mergeUp a l).eval.toLinearMap
        (Finsupp.single (gk.basis.pair kl.basis 1 k) 1))) = _
    rw [eval_mergeUp_single (R := R) a l 1 k 1, one_mul,
      eval_upDot_single (R := R) d (a.toHom k) 1, eval_splitUp_single (R := R) b r x 1]
  change (horizontal (id kg) (rightUnit gh)).eval.toLinearMap
    ((horizontal (id kg) (horizontal (id gh) (multiplicationCap r))).eval.toLinearMap
      ((horizontal (id kg) (associate gh hl lh)).eval.toLinearMap
        ((horizontal (id kg) (horizontal dot (id lh))).eval.toLinearMap
          ((horizontal (id kg) (unassociate gk kl lh)).eval.toLinearMap
            ((associate kg gk Mj).eval.toLinearMap
              ((horizontal (ordinaryCup a) (id Mj)).eval.toLinearMap
                ((insertLeftUnit Mj).eval.toLinearMap (Finsupp.single v 1)))))))) =
    (mixedMultiplication a b l r d).eval.toLinearMap (Finsupp.single v 1)
  rw [eval_insertLeftUnit_single Mj, eval_horizontal_single (ordinaryCup a) (id Mj),
    one_smul, eval_ordinaryCup_single (R := R) a 1 1, map_one, eval_id_apply,
    Biset.pairLinear_single, one_mul, eval_associate_single kg gk Mj]
  rw [eval_horizontal_single (id kg) (unassociate gk kl lh), one_smul, eval_id_apply]
  dsimp only [v]
  rw [eval_unassociate_single gk kl lh, Biset.pairLinear_single, one_mul]
  rw [eval_horizontal_single (id kg) (horizontal dot (id lh)), one_smul, eval_id_apply,
    eval_horizontal_single dot (id lh), one_smul, eval_id_apply, hdot,
    Biset.pairLinear_single, one_mul, Biset.pairLinear_single, one_mul]
  rw [eval_horizontal_single (id kg) (associate gh hl lh), one_smul, eval_id_apply,
    eval_associate_single gh hl lh, Biset.pairLinear_single, one_mul]
  rw [eval_horizontal_single (id kg) (horizontal (id gh) (multiplicationCap r)),
    one_smul, eval_id_apply, eval_horizontal_single (id gh) (multiplicationCap r),
    one_smul, eval_id_apply, eval_multiplicationCap_single (R := R) r 1 h 1,
    one_mul, Biset.pairLinear_single, one_mul, Biset.pairLinear_single, one_mul]
  rw [eval_horizontal_single (id kg) (rightUnit gh), one_smul, eval_id_apply,
    eval_rightUnit_single gh, Biset.pairLinear_single, one_mul]
  change Finsupp.single (kg.basis.pair gh.basis 1 (1*x*(b.toHom h⁻¹)⁻¹)) 1 =
    (Generator.mixedMultiplication a b l r d R).toLinearMap
      (Finsupp.single ((Biset.induction l).pair (Biset.restriction r) k h) 1)
  simp only [one_mul, map_inv, inv_inv, Generator.mixedMultiplication, Biset.Hom.ofFunction_single]
  apply congrArg (fun y => Finsupp.single y 1)
  have he := Generator.mixedPair_mixedProduct a b (kg.basis.pair gh.basis 1 (x * b.toHom h))
  change Generator.mixedPair a b (1 * (x * b.toHom h)) =
    kg.basis.pair gh.basis 1 (x * b.toHom h) at he
  rw [one_mul] at he
  exact he.symm

end MackeyDiagrams.Diagram
