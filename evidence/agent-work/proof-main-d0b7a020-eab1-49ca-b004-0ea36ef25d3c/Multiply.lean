namespace OutsideRegionsAux
open MackeyDiagrams
noncomputable section

variable {U : Type*} [Group U] {K H J L M G A D F C E B : Subgroup U}

private abbrev col {X : Type*} (x : X) : Vec X :=
  Finsupp.single x 1

private theorem push_before {p q r : Word K H}
    (D : LabelledDrawing Complex p q) (E : LabelledDrawing Complex q r)
    (x : p.basis.carrier) (y : q.basis.carrier) (z : r.basis.carrier)
    (hd : ev D (col x) = col y) (he : ev E (col y) = col z) :
    ev (before D E) (col x) = col z := by
  change ev E (ev D (col x)) = _
  rw [hd, he]

private theorem push_atLeft {p p' : Word K H} {q : Word H J}
    (D : LabelledDrawing Complex p p') (x : p.basis.carrier) (y : q.basis.carrier)
    (x' : p'.basis.carrier) (hd : ev D (col x) = col x') :
    ev (atLeft D q) (col (pair p q x y)) = col (pair p' q x' y) := by
  change (D.interpret.eval.horizontal (Diagram.id q).eval).toLinearMap _ = _
  rw [Biset.Hom.horizontal_single, one_smul, Diagram.eval_id_apply, hd,
    Biset.pairLinear_single, one_mul]

private theorem push_atRight {p : Word K H} {q : Word H J} {s : Word J L}
    {q' : Word H M} {s' : Word M L}
    (D : LabelledDrawing Complex (q.tensor s) (q'.tensor s'))
    (x : p.basis.carrier) (y : q.basis.carrier) (z : s.basis.carrier)
    (y' : q'.basis.carrier) (z' : s'.basis.carrier)
    (hd : ev D (col (pair q s y z)) = col (pair q' s' y' z')) :
    ev (atRight p D) (col (triple p q s x y z)) = col (triple p q' s' x y' z') := by
  change (Diagram.unassociate (R := Complex) p q' s').eval.toLinearMap
    (((Diagram.id p).eval.horizontal D.interpret.eval).toLinearMap
      ((Diagram.associate (R := Complex) p q s).eval.toLinearMap (col (triple p q s x y z)))) = _
  rw [Diagram.eval_associate_single, Biset.Hom.horizontal_single, one_smul,
    Diagram.eval_id_apply, hd, Biset.pairLinear_single, one_mul, Diagram.eval_unassociate_single]

private theorem push_mixed (a : ConjEmbedding K A) (b : ConjEmbedding H A)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (x : Dot (a.comp l) (b.comp r)) (g : K) (h : H) :
    ev (.mixedMultiplication a b l r [(1,x)]) (col (pair (.up l) (.down r) g h)) =
      col (pair (.down a) (.up b) (a.toHom g * x.element * b.toHom h) 1) := by
  let label : DotLabel Complex (a.comp l) (b.comp r) := Finsupp.single x 1
  have hterms : label.terms = [(1,x)] := by
    classical
    simp [label, DotLabel.terms]
  rw [← hterms]
  have hcol := ((MixedCrossingFiniteFiberConvention (U := U)).2.2.1 a b l r label).1
    (pair (.up l) (.down r) g h)
  rw [hterms] at hcol
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_smul] at hcol
  exact hcol

private theorem push_parallel (a : ConjEmbedding H A) (b : ConjEmbedding L H)
    (j : ConjEmbedding J A) (w : ConjEmbedding L J)
    (x : Dot (a.comp b) (j.comp w)) (g : A) (h : H) :
    ev (.parallelUp a b j w [(1,x)]) (col (pair (.up a) (.up b) g h)) =
      col (pair (.up j) (.up w) (g * a.toHom h * x.element) 1) := by
  rw [singleton_parallel]
  change (Diagram.splitUp (R := Complex) j w).eval.toLinearMap
    ((Diagram.upDot x).eval.toLinearMap ((Diagram.mergeUp a b).eval.toLinearMap
      (col (pair (.up a) (.up b) g h)))) = _
  rw [Diagram.eval_mergeUp_single, Diagram.eval_upDot_single, Diagram.eval_splitUp_single]

variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev framedMul (drawing : LabelledDrawing Complex (top d e f) (bottom a b c)) :=
  before (splitTop d e f) (before drawing (mergeBottom a b c))

private theorem push_splitTop (g : G) (h : F) :
    ev (splitTop d e f) (col (pair (.up (d.comp e)) (.down f) g h)) =
      col (triple (.up d) (.up e) (.down f) g 1 h) := by
  change (Diagram.horizontal (R := Complex) (Diagram.splitUp d e) (Diagram.id (.down f))).eval.toLinearMap _ = _
  rw [Diagram.eval_horizontal_single, one_smul, Diagram.eval_splitUp_single,
    Diagram.eval_id_apply, Biset.pairLinear_single, one_mul]

private theorem push_mergeBottom (x y : A) (z : D) :
    ev (mergeBottom a b c) (col (triple (.down a) (.up b) (.up c) x y z)) =
      col (Generator.mixedPair a (b.comp c) (x * (y * b.toHom z))) := by
  change (Diagram.horizontal (R := Complex) (Diagram.id (.down a)) (Diagram.mergeUp b c)).eval.toLinearMap
    ((Diagram.associate (.down a) (.up b) (.up c)).eval.toLinearMap
      (col (triple (.down a) (.up b) (.up c) x y z))) = _
  rw [Diagram.eval_associate_single, Diagram.eval_horizontal_single, one_smul,
    Diagram.eval_id_apply, Diagram.eval_mergeUp_single, Biset.pairLinear_single, one_mul]
  exact congrArg col (mixedPair_coord a (b.comp c) x (y * b.toHom z))

private abbrev leftMulDrawing (r : ConjEmbedding B G) (s : ConjEmbedding B D)
    (t : ConjEmbedding E B) (x : Dot (a.comp r) (b.comp s))
    (y : Dot (s.comp t) (c.comp f)) (z : Dot (r.comp t) (d.comp e)) :=
  before (atLeft (.parallelUp d e r t [(1,z.inverse)]) (.down f))
    (before (atRight (.up r) (.mixedMultiplication s c t f [(1,y)]))
      (atLeft (.mixedMultiplication a b r s [(1,x)]) (.up c)))

private abbrev rightMulDrawing (j : ConjEmbedding B A) (v : ConjEmbedding C B)
    (w : ConjEmbedding F B) (ell : Dot (b.comp c) (j.comp w))
    (m : Dot (a.comp d) (j.comp v)) (n : Dot (v.comp e) (w.comp f)) :=
  before (atRight (.up d) (.mixedMultiplication v w e f [(1,n)]))
    (before (atLeft (.mixedMultiplication a j d v [(1,m)]) (.up w))
      (atRight (.down a) (.parallelUp j w b c [(1,ell.inverse)])))

-- The forward columns of Xiao's Theorem 6.5 specialize to the same
-- parameter products as the backward coefficient calculation of Lemma 6.3.
private theorem push_left {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : Dot (a.comp r) (b.comp s))
    (y : Dot (s.comp t) (c.comp f)) (z : Dot (r.comp t) (d.comp e)) (g : G) (h : F) :
    ev (framedMul a b c d e f (leftMulDrawing a b c d e f r s t x y z))
      (col (pair (.up (d.comp e)) (.down f) g h)) =
      col (Generator.mixedPair a (b.comp c)
        (a.toHom g * leftParameter a b c d e f x y z * (b.comp c).toHom h)) := by
  let g' := g * z.element⁻¹
  let t' := y.element * c.toHom h
  let q := a.toHom g' * x.element * b.toHom t'
  have h₁ := push_atLeft (.parallelUp d e r t [(1,z.inverse)])
    (q := .down f) (pair (.up d) (.up e) g 1) h (pair (.up r) (.up t) g' 1) (by
      simpa only [g', map_one, mul_one, Dot.inverse] using push_parallel d e r t z.inverse g 1)
  have h₂ := push_atRight (p := Word.up r) (.mixedMultiplication s c t f [(1,y)])
    g' 1 h t' 1 (by simpa only [t', map_one, one_mul] using push_mixed s c t f y 1 h)
  have h₃ := push_atLeft (.mixedMultiplication a b r s [(1,x)])
    (q := .up c) (pair (.up r) (.down s) g' t') 1
    (pair (.down a) (.up b) q 1) (push_mixed a b r s x g' t')
  have h₄ := push_mergeBottom a b c q 1 1
  have hEval := push_before _ _ _ _ _ (push_splitTop d e f g h)
    (push_before _ _ _ _ _ (push_before _ _ _ _ _ h₁ (push_before _ _ _ _ _ h₂ h₃)) h₄)
  simpa only [q, g', t', leftParameter, map_one, one_mul, mul_one, map_mul,
    ConjEmbedding.comp_apply, mul_assoc] using hEval

private theorem push_right {j : ConjEmbedding B A} {v : ConjEmbedding C B}
    {w : ConjEmbedding F B} (ell : Dot (b.comp c) (j.comp w))
    (m : Dot (a.comp d) (j.comp v)) (n : Dot (v.comp e) (w.comp f)) (g : G) (h : F) :
    ev (framedMul a b c d e f (rightMulDrawing a b c d e f j v w ell m n))
      (col (pair (.up (d.comp e)) (.down f) g h)) =
      col (Generator.mixedPair a (b.comp c)
        (a.toHom g * rightParameter a b c d e f ell m n * (b.comp c).toHom h)) := by
  let n' := n.element * w.toHom h
  let q := a.toHom g * m.element * j.toHom n'
  have h₁ := push_atRight (p := Word.up d) (.mixedMultiplication v w e f [(1,n)])
    g 1 h n' 1 (by simpa only [n', map_one, one_mul] using push_mixed v w e f n 1 h)
  have h₂ := push_atLeft (.mixedMultiplication a j d v [(1,m)])
    (q := .up w) (pair (.up d) (.down v) g n') 1
    (pair (.down a) (.up j) q 1) (push_mixed a j d v m g n')
  have h₃ := push_atRight (p := Word.down a) (.parallelUp j w b c [(1,ell.inverse)])
    q 1 1 ell.element⁻¹ 1 (by
      simpa only [map_one, mul_one, one_mul, Dot.inverse] using push_parallel j w b c ell.inverse 1 1)
  have h₄ := push_mergeBottom a b c q ell.element⁻¹ 1
  have hEval := push_before _ _ _ _ _ (push_splitTop d e f g h)
    (push_before _ _ _ _ _ (push_before _ _ _ _ _ h₁ (push_before _ _ _ _ _ h₂ h₃)) h₄)
  have he := ell.inverse.intertwines h
  simp only [Dot.inverse, ConjEmbedding.comp_apply] at he
  simpa only [q, n', rightParameter, map_one, mul_one, map_mul,
    ConjEmbedding.comp_apply, mul_assoc, he] using hEval

private theorem multiplication_comparison
    (p : ProjectionDot.Mixed a (b.comp c) (d.comp e) f)
    (drawing : LabelledDrawing Complex (top d e f) (bottom a b c)) (q : A)
    (h : ∀ (g : G) (k : F), ev (framedMul a b c d e f drawing)
      (col (pair (.up (d.comp e)) (.down f) g k)) =
      col (Generator.mixedPair a (b.comp c) (a.toHom g * q * (b.comp c).toHom k))) :
    drawing.interpret.eval = (targetMultiplication a b c d e f p).interpret.eval ↔ q = p.dot.element := by
  classical
  have htarget : ev (framedMul a b c d e f (targetMultiplication a b c d e f p)) =
      ev (.mixedMultiplication a (b.comp c) (d.comp e) f [(1,p.dot)]) :=
    framed_target (splitTop d e f) (mergeBottom a b c) (mergeTop d e f) (splitBottom a b c)
      (cancel_splitTop_mergeTop d e f) (cancel_splitBottom_mergeBottom a b c) _
  have col_target (g : G) (k : F) :
      ev (.mixedMultiplication a (b.comp c) (d.comp e) f [(1,p.dot)])
        (col (pair (.up (d.comp e)) (.down f) g k)) =
        col (Generator.mixedPair a (b.comp c) (a.toHom g * p.dot.element * (b.comp c).toHom k)) := by
    refine (push_mixed a (b.comp c) (d.comp e) f p.dot g k).trans ?_
    apply congrArg col
    exact (mixedPair_coord a (b.comp c) _ 1).trans (congrArg _ (mul_one _))
  rw [← frame_eq (splitTop d e f) (mergeBottom a b c) (mergeTop d e f) (splitBottom a b c)
    (cancel_mergeTop_splitTop d e f) (cancel_mergeBottom_splitBottom a b c)]
  change (ev (framedMul a b c d e f drawing) =
    ev (framedMul a b c d e f (targetMultiplication a b c d e f p))) ↔ _
  rw [htarget]
  constructor
  · intro he
    have eq := h 1 1
    rw [he, col_target] at eq
    simp only [map_one, one_mul, mul_one] at eq
    apply (Generator.mixedEquiv a (b.comp c)).symm.injective
    exact Finsupp.single_left_injective one_ne_zero eq.symm
  · rintro rfl
    apply Finsupp.lhom_ext
    intro z k
    have hc (z : (mergedTop d e f).basis.carrier) :
        ev (framedMul a b c d e f drawing) (col z) =
        ev (.mixedMultiplication a (b.comp c) (d.comp e) f [(1,p.dot)]) (col z) :=
      Quotient.inductionOn z fun ⟨g,h'⟩ => (h g h').trans (col_target g h').symm
    rw [show Finsupp.single z k = k • col z by simp [col, Finsupp.smul_single],
      map_smul, map_smul, hc]

private theorem left_mul_eval {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (p : ProjectionDot.Mixed a (b.comp c) (d.comp e) f)
    (x : Dot (a.comp r) (b.comp s)) (y : Dot (s.comp t) (c.comp f)) (z : Dot (r.comp t) (d.comp e)) :
    (leftMulDrawing a b c d e f r s t x y z).interpret.eval =
      (targetMultiplication a b c d e f p).interpret.eval ↔ leftParameter a b c d e f x y z = p.dot.element :=
  multiplication_comparison a b c d e f p _ _ (push_left a b c d e f x y z)

private theorem right_mul_eval {j : ConjEmbedding B A} {v : ConjEmbedding C B}
    {w : ConjEmbedding F B} (p : ProjectionDot.Mixed a (b.comp c) (d.comp e) f)
    (ell : Dot (b.comp c) (j.comp w)) (m : Dot (a.comp d) (j.comp v)) (n : Dot (v.comp e) (w.comp f)) :
    (rightMulDrawing a b c d e f j v w ell m n).interpret.eval =
      (targetMultiplication a b c d e f p).interpret.eval ↔ rightParameter a b c d e f ell m n = p.dot.element :=
  multiplication_comparison a b c d e f p _ _ (push_right a b c d e f ell m n)

end
end OutsideRegionsAux
