import MackeyDiagrams.MixedProjectionExpansion
import MackeyDiagrams.Parallel

/-! Basis evaluation rules for the structural maps and subgroup trace. -/

namespace MackeyDiagrams.Diagram

universe u v

variable {U : Type u} [Group U] {K H J F G : Subgroup U}
variable {R : Type v} [CommSemiring R]

theorem eval_associate_single (p : Word K H) (q : Word H J) (t : Word J F)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : t.basis.carrier) (c : R) :
    (associate (R := R) p q t).eval.toLinearMap
      (Finsupp.single ((p.basis.tensor q.basis).pair t.basis (p.basis.pair q.basis x y) z) c) =
    Finsupp.single (p.basis.pair (q.basis.tensor t.basis) x (q.basis.pair t.basis y z)) c := by
  change (Biset.associate p.basis q.basis t.basis R).toLinearMap _ = _
  rw [Biset.associate, Biset.Hom.ofFunction_single]
  rfl

theorem eval_unassociate_single (p : Word K H) (q : Word H J) (t : Word J F)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : t.basis.carrier) (c : R) :
    (unassociate (R := R) p q t).eval.toLinearMap
      (Finsupp.single (p.basis.pair (q.basis.tensor t.basis) x (q.basis.pair t.basis y z)) c) =
    Finsupp.single ((p.basis.tensor q.basis).pair t.basis (p.basis.pair q.basis x y) z) c := by
  change (Biset.unassociate p.basis q.basis t.basis R).toLinearMap _ = _
  rw [Biset.unassociate, Biset.Hom.ofFunction_single]
  rfl

theorem eval_leftUnit_single (p : Word K H) (x : K) (y : p.basis.carrier) (c : R) :
    (leftUnit (R := R) p).eval.toLinearMap
      (Finsupp.single ((Biset.regular K).pair p.basis x y) c) =
    Finsupp.single (p.basis.act (x,1) y) c := by
  change (Biset.leftUnit p.basis R).toLinearMap _ = _
  rw [Biset.leftUnit, Biset.Hom.ofFunction_single]
  rfl

theorem eval_traceCap_single (a : ConjEmbedding K G) (x y : G) (c : R) :
    (traceCap (R := R) a).eval.toLinearMap
      (Finsupp.single ((Biset.restriction a).pair (Biset.induction a) x y) c) =
    c • Generator.traceBasis R a (x * y) := by
  change (Generator.traceCap R a).toLinearMap _ = _
  rw [Generator.traceCap, Biset.Hom.ofBasis_single]
  rfl

theorem eval_traceCapOnLeft_image (a : ConjEmbedding K G) (l : ConjEmbedding H K)
    (x y : G) (k : K) (h : x * y = a.toHom k) :
    (traceCapOnLeft (R := R) a l).eval.toLinearMap
      (Finsupp.single ((Biset.restriction a).pair (Biset.induction (a.comp l)) x y) 1) =
    Finsupp.single k 1 := by
  let upL := Word.up l
  change (leftUnit (R := R) upL).eval.toLinearMap
    ((horizontal (traceCap a) (id upL)).eval.toLinearMap
      ((unassociate (.down a) (.up a) upL).eval.toLinearMap
        ((horizontal (id (.down a)) (splitUp a l)).eval.toLinearMap
          (Finsupp.single ((Biset.restriction a).pair (Biset.induction (a.comp l)) x y) 1)))) = _
  rw [eval_horizontal_single (id (.down a)) (splitUp a l) x y 1, one_smul, eval_id_apply,
    eval_splitUp_single (R := R) a l y 1, Biset.pairLinear_single, one_mul]
  rw [eval_unassociate_single (R := R) (.down a) (.up a) upL x y 1 1]
  rw [eval_horizontal_single (traceCap a) (id upL) ((Biset.restriction a).pair (Biset.induction a) x y) 1 1,
    one_smul, eval_id_apply, eval_traceCap_single, one_smul, h, Generator.traceBasis_image,
    Biset.pairLinear_single, one_mul, eval_leftUnit_single]
  change Finsupp.single (k * 1 * (l.toHom 1)⁻¹) 1 = _
  simp

theorem eval_traceCapOnLeft_outside (a : ConjEmbedding K G) (l : ConjEmbedding H K)
    (x y : G) (h : ¬ ∃ k, a.toHom k = x * y) :
    (traceCapOnLeft (R := R) a l).eval.toLinearMap
      (Finsupp.single ((Biset.restriction a).pair (Biset.induction (a.comp l)) x y) 1) = 0 := by
  let upL := Word.up l
  change (leftUnit (R := R) upL).eval.toLinearMap
    ((horizontal (traceCap a) (id upL)).eval.toLinearMap
      ((unassociate (.down a) (.up a) upL).eval.toLinearMap
        ((horizontal (id (.down a)) (splitUp a l)).eval.toLinearMap
          (Finsupp.single ((Biset.restriction a).pair (Biset.induction (a.comp l)) x y) 1)))) = _
  rw [eval_horizontal_single (id (.down a)) (splitUp a l) x y 1, one_smul, eval_id_apply,
    eval_splitUp_single (R := R) a l y 1, Biset.pairLinear_single, one_mul]
  rw [eval_unassociate_single (R := R) (.down a) (.up a) upL x y 1 1]
  rw [eval_horizontal_single (traceCap a) (id upL) ((Biset.restriction a).pair (Biset.induction a) x y) 1 1,
    one_smul, eval_traceCap_single, Generator.traceBasis_outside R a _ h, smul_zero,
    map_zero, LinearMap.zero_apply, map_zero]

end MackeyDiagrams.Diagram

namespace MackeyDiagrams.Diagram

universe u v

variable {U : Type u} [Group U] {K H G L : Subgroup U}
variable {R : Type v} [CommSemiring R]

theorem eval_mixedProjectionTail_single (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H) (d : Dot (a.comp l) (b.comp r))
    (x y : G) (h₁ h₂ : H) :
    (mixedProjectionTail (R := R) a b l r d).eval.toLinearMap
      (Finsupp.single
        (((Word.down a).tensor (.up b)).basis.pair (reverseCupWord r).basis
          ((Biset.restriction a).pair (Biset.induction b) x y)
          ((Biset.induction r).pair (Biset.restriction r) h₁ h₂)) 1) =
    (horizontal (traceCapOnLeft a l) (id (.down r))).eval.toLinearMap
      (Finsupp.single
        (((Word.down a).tensor (.up (a.comp l))).basis.pair (Word.down r).basis
          ((Biset.restriction a).pair (Biset.induction (a.comp l))
            x (y * b.toHom h₁ * d.element⁻¹)) h₂) 1) := by
  let kg := Word.down a
  let gh := Word.up b
  let hl := Word.up r
  let lh := Word.down r
  let gl := Word.up (a.comp l)
  let dot := (mergeUp (R := R) b r).vertical (upDot d.inverse)
  let trace := horizontal (traceCapOnLeft (R := R) a l) (id lh)
  let cup := hl.basis.pair lh.basis h₁ h₂
  let input := Finsupp.single ((kg.basis.tensor gh.basis).pair
    (hl.basis.tensor lh.basis) (kg.basis.pair gh.basis x y) cup) (1 : R)
  change trace.eval.toLinearMap
    ((unassociate kg gl lh).eval.toLinearMap
      ((horizontal (id kg) (horizontal dot (id lh))).eval.toLinearMap
        ((horizontal (id kg) (unassociate gh hl lh)).eval.toLinearMap
          ((associate kg gh (reverseCupWord r)).eval.toLinearMap input)))) = _
  dsimp only [input, cup]
  rw [eval_associate_single kg gh (reverseCupWord r)]
  rw [eval_horizontal_single (id kg) (unassociate gh hl lh),
    one_smul, eval_id_apply, eval_unassociate_single gh hl lh, Biset.pairLinear_single, one_mul]
  rw [eval_horizontal_single (id kg) (horizontal dot (id lh)), one_smul, eval_id_apply,
    eval_horizontal_single dot (id lh), one_smul, eval_id_apply]
  have he : dot.eval.toLinearMap
      (Finsupp.single (gh.basis.pair hl.basis y h₁) 1) =
      Finsupp.single (y * b.toHom h₁ * d.element⁻¹) 1 := by
    change (upDot (R := R) d.inverse).eval.toLinearMap
      ((mergeUp b r).eval.toLinearMap (Finsupp.single (gh.basis.pair hl.basis y h₁) 1)) = _
    rw [eval_mergeUp_single (R := R) b r y h₁ 1,
      eval_upDot_single (R := R) d.inverse (y * b.toHom h₁) 1]
    rfl
  rw [he, Biset.pairLinear_single, one_mul, Biset.pairLinear_single, one_mul,
    eval_unassociate_single kg gl lh]

end MackeyDiagrams.Diagram

namespace MackeyDiagrams.Diagram

universe u v

variable {U : Type u} [Group U] {K H : Subgroup U}
variable {R : Type v} [CommSemiring R]

theorem eval_rightUnit_single (p : Word K H) (x : p.basis.carrier) (y : H) (c : R) :
    (rightUnit (R := R) p).eval.toLinearMap
      (Finsupp.single (p.basis.pair (Biset.regular H) x y) c) =
    Finsupp.single (p.basis.act (1,y⁻¹) x) c := by
  change (Biset.rightUnit p.basis R).toLinearMap _ = _
  rw [Biset.rightUnit, Biset.Hom.ofFunction_single]
  rfl

theorem eval_insertLeftUnit_single (p : Word K H) (x : p.basis.carrier) (c : R) :
    (insertLeftUnit (R := R) p).eval.toLinearMap (Finsupp.single x c) =
      Finsupp.single ((Biset.regular K).pair p.basis 1 x) c := by
  change (Biset.insertLeftUnit p.basis R).toLinearMap _ = _
  rw [Biset.insertLeftUnit, Biset.Hom.ofFunction_single]

theorem eval_multiplicationCap_single (a : ConjEmbedding K H) (x y : H) (c : R) :
    (multiplicationCap (R := R) a).eval.toLinearMap
      (Finsupp.single ((Biset.induction a).pair (Biset.restriction a) x y) c) =
    Finsupp.single (x*y) c := by
  change (Generator.multiplicationCap R a).toLinearMap _ = _
  rw [Generator.multiplicationCap, Biset.Hom.ofFunction_single]
  rfl

end MackeyDiagrams.Diagram
