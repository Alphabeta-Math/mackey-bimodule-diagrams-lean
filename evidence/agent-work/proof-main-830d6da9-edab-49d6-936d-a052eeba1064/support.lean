namespace StandardSymmetricBraidProof

open MackeyDiagrams

noncomputable section

variable {U : Type*} [Group U] {G H J F : Subgroup U}
variable (a : ConjEmbedding H G) (b : ConjEmbedding J H) (c : ConjEmbedding F J)

private abbrev cross (d : Dot (a.comp b) (a.comp b)) :
    Diagram Complex ((Word.up a).tensor (.up b)) ((Word.up a).tensor (.up b)) :=
  (Diagram.mergeUp a b).vertical ((Diagram.upDot d).vertical (Diagram.splitUp a b))

private abbrev left (d : Dot (a.comp b) (a.comp b)) :=
  (cross a b d).horizontal (Diagram.id (.up c))

private abbrev right (e : Dot (b.comp c) (b.comp c)) :=
  (Diagram.associate (.up a) (.up b) (.up c)).vertical
    (((Diagram.id (.up a)).horizontal (cross b c e)).vertical
      (Diagram.unassociate (.up a) (.up b) (.up c)))

private abbrev triple (x : G) (y : H) (z : J) :
    (((Word.up a).tensor (.up b)).tensor (.up c)).basis.carrier :=
  ((Word.up a).basis.tensor (Word.up b).basis).pair (Word.up c).basis
    ((Word.up a).basis.pair (Word.up b).basis x y) z

private theorem pair_normal (x : G) (y : H) :
    (Word.up a).basis.pair (Word.up b).basis x y =
      (Word.up a).basis.pair (Word.up b).basis (x * a.toHom y) 1 := by
  symm
  simpa [Word.basis, Biset.induction] using
    (Word.up a).basis.pair_balance (Word.up b).basis y x 1

-- Balance the third coordinate into the second, then the second into
-- the first. This is the three-strand merge and split on representatives.
private theorem triple_normal (x : G) (y : H) (z : J) :
    triple a b c x y z = triple a b c (x * a.toHom (y * b.toHom z)) 1 1 := by
  have moveRight : triple a b c x (y * b.toHom z) 1 = triple a b c x y z := by
    simpa [Biset.act_pair, Word.basis, Biset.induction] using
      ((Word.up a).basis.tensor (Word.up b).basis).pair_balance (Word.up c).basis
        z ((Word.up a).basis.pair (Word.up b).basis x y) 1
  rw [← moveRight]
  exact congrArg (fun xy => ((Word.up a).basis.tensor (Word.up b).basis).pair
    (Word.up c).basis xy 1) (pair_normal a b x (y * b.toHom z))

-- The parallel-crossing composition supplier composes two crossings on
-- the same pair. Here the active pair alternates and the right crossing
-- changes parentheses. Compute each crossing using the checked merge,
-- dot, split and associator basis equations, then compose the resulting
-- right multiplications in stacking order.
private theorem cross_single (d : Dot (a.comp b) (a.comp b)) (x : G) (y : H)
    (r : Complex) :
    (cross a b d).eval.toLinearMap
      (Finsupp.single ((Word.up a).basis.pair (Word.up b).basis x y) r) =
    Finsupp.single ((Word.up a).basis.pair (Word.up b).basis
      (x * a.toHom y * d.element) 1) r := by
  unfold cross
  rw [Diagram.eval_vertical_apply, Diagram.eval_vertical_apply]
  rw [Diagram.eval_mergeUp_single a b x y r,
    Diagram.eval_upDot_single, Diagram.eval_splitUp_single]

private theorem left_single (d : Dot (a.comp b) (a.comp b)) (x : G) (r : Complex) :
    (left a b c d).eval.toLinearMap (Finsupp.single (triple a b c x 1 1) r) =
      Finsupp.single (triple a b c (x * d.element) 1 1) r := by
  rw [Diagram.eval_horizontal_single (cross a b d) (Diagram.id (.up c)),
    cross_single a b, Diagram.eval_id_apply, Biset.pairLinear_single]
  simp only [map_one, mul_one, Finsupp.smul_single, smul_eq_mul]

private theorem right_single (e : Dot (b.comp c) (b.comp c)) (x : G) (r : Complex) :
    (right a b c e).eval.toLinearMap (Finsupp.single (triple a b c x 1 1) r) =
      Finsupp.single (triple a b c (x * a.toHom e.element) 1 1) r := by
  unfold right
  rw [Diagram.eval_vertical_apply, Diagram.eval_vertical_apply]
  rw [Diagram.eval_associate_single (.up a) (.up b) (.up c),
    Diagram.eval_horizontal_single (Diagram.id (.up a)) (cross b c e),
    Diagram.eval_id_apply, cross_single b c, Biset.pairLinear_single]
  simp only [map_one, one_mul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [Diagram.eval_unassociate_single (.up a) (.up b) (.up c)]
  exact congrArg (fun xy => Finsupp.single
    (((Word.up a).basis.tensor (Word.up b).basis).pair (Word.up c).basis xy 1) r)
    (pair_normal a b x e.element)

private theorem braid (d : Dot (a.comp b) (a.comp b)) (e : Dot (b.comp c) (b.comp c))
    (h : a.toHom e.element * d.element * a.toHom e.element =
      d.element * a.toHom e.element * d.element) :
    ((right a b c e).vertical ((left a b c d).vertical (right a b c e))).eval =
      ((left a b c d).vertical ((right a b c e).vertical (left a b c d))).eval := by
  apply Diagram.eval_ext
  intro v r
  refine Quotient.inductionOn v (fun pair => ?_)
  rcases pair with ⟨xy, z⟩
  refine Quotient.inductionOn xy (fun pair => ?_)
  rcases pair with ⟨x, y⟩
  change
    (((right a b c e).vertical ((left a b c d).vertical (right a b c e))).eval.toLinearMap
      (Finsupp.single (triple a b c x y z) r)) =
    (((left a b c d).vertical ((right a b c e).vertical (left a b c d))).eval.toLinearMap
      (Finsupp.single (triple a b c x y z) r))
  rw [triple_normal a b c]
  rw [Diagram.eval_vertical_apply (right a b c e) ((left a b c d).vertical (right a b c e)),
    Diagram.eval_vertical_apply (left a b c d) (right a b c e),
    Diagram.eval_vertical_apply (left a b c d) ((right a b c e).vertical (left a b c d)),
    Diagram.eval_vertical_apply (right a b c e) (left a b c d),
    right_single, left_single, right_single, left_single, right_single, left_single]
  simpa only [mul_assoc] using congrArg
    (fun t => Finsupp.single (triple a b c ((x * a.toHom (y * b.toHom z)) * t) 1 1) r) h

end

end StandardSymmetricBraidProof
