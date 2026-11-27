namespace OutsideRegionsAux
open MackeyDiagrams

noncomputable section
variable {U : Type*} [Group U] {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)
variable (p : ProjectionDot.Mixed a (b.comp c) (d.comp e) f)

private abbrev mergeBottom : LabelledDrawing Complex (bottom a b c) (mergedBottom a b c) :=
  before (.ordinary (.associate (.down a) (.up b) (.up c)))
    (.horizontal (drawId (.down a)) (.trivalent (.mergeUp b c)))

private abbrev splitTop : LabelledDrawing Complex (mergedTop d e f) (top d e f) :=
  .horizontal (.trivalent (.splitUp d e)) (drawId (.down f))

private abbrev targetProjection :=
  before (mergeBottom a b c)
    (before (.compactProjection a (b.comp c) (d.comp e) f [(1,p)]) (splitTop d e f))

private abbrev targetMultiplication :=
  before (mergeTop d e f)
    (before (.mixedMultiplication a (b.comp c) (d.comp e) f [(1,p.dot)]) (splitBottom a b c))

-- The boundary frames come in inverse pairs, by the typed trivalent
-- and reassociation identities. This bridges merged coordinates and the
-- full three-strand equality used in the endpoint.
private theorem cancel_splitBottom_mergeBottom :
    (splitBottom a b c).interpret.eval.vertical (mergeBottom a b c).interpret.eval =
      Biset.Hom.id (mergedBottom a b c).basis := by
  let X := (Word.down a).basis
  let Y := (Word.up b).basis
  let Z := (Word.up c).basis
  let S := (Diagram.id (R := Complex) (.down a)).eval.horizontal (Diagram.splitUp b c).eval
  let M := (Diagram.id (R := Complex) (.down a)).eval.horizontal (Diagram.mergeUp b c).eval
  change (S.vertical (Biset.unassociate X Y Z Complex)).vertical
    ((Biset.associate X Y Z Complex).vertical M) = _
  refine Biset.Hom.cancel_middle _ _ _ _ Biset.unassociate_associate ?_
  change ((Biset.Hom.id (R := Complex) X).horizontal (Diagram.splitUp b c).eval).vertical
    ((Biset.Hom.id X).horizontal (Diagram.mergeUp b c).eval) = _
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change (Biset.Hom.id X).horizontal
    (((Diagram.splitUp (R := Complex) b c).vertical (Diagram.mergeUp b c)).eval) = _
  rw [Diagram.splitUp_mergeUp]
  exact Biset.Hom.horizontal_id _ _

private theorem cancel_mergeBottom_splitBottom :
    (mergeBottom a b c).interpret.eval.vertical (splitBottom a b c).interpret.eval =
      Biset.Hom.id (bottom a b c).basis := by
  change ((Biset.associate (Word.down a).basis (Word.up b).basis (Word.up c).basis
      Complex).vertical
      ((Biset.Hom.id (Word.down a).basis).horizontal (Diagram.mergeUp b c).eval)).vertical
    (((Biset.Hom.id (Word.down a).basis).horizontal (Diagram.splitUp b c).eval).vertical
      (Biset.unassociate (Word.down a).basis (Word.up b).basis (Word.up c).basis Complex)) = _
  refine Biset.Hom.cancel_middle _ _ _ _ ?_ Biset.associate_unassociate
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change (Biset.Hom.id (Word.down a).basis).horizontal
    ((Diagram.mergeUp (R := Complex) b c).vertical (Diagram.splitUp b c)).eval = _
  rw [Diagram.mergeUp_splitUp]
  exact Biset.Hom.horizontal_id _ _

private theorem cancel_splitTop_mergeTop :
    (splitTop d e f).interpret.eval.vertical (mergeTop d e f).interpret.eval =
      Biset.Hom.id (mergedTop d e f).basis := by
  change ((Diagram.splitUp d e).eval.horizontal (Biset.Hom.id (Word.down f).basis)).vertical
      ((Diagram.mergeUp d e).eval.horizontal (Biset.Hom.id (Word.down f).basis)) = _
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change ((Diagram.splitUp (R := Complex) d e).vertical (Diagram.mergeUp d e)).eval.horizontal
    (Biset.Hom.id (Word.down f).basis) = _
  rw [Diagram.splitUp_mergeUp]
  exact Biset.Hom.horizontal_id _ _

private theorem cancel_mergeTop_splitTop :
    (mergeTop d e f).interpret.eval.vertical (splitTop d e f).interpret.eval =
      Biset.Hom.id (top d e f).basis := by
  change ((Diagram.mergeUp d e).eval.horizontal (Biset.Hom.id (Word.down f).basis)).vertical
      ((Diagram.splitUp d e).eval.horizontal (Biset.Hom.id (Word.down f).basis)) = _
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.id_vertical]
  change ((Diagram.mergeUp (R := Complex) d e).vertical (Diagram.splitUp d e)).eval.horizontal
    (Biset.Hom.id (Word.down f).basis) = _
  rw [Diagram.mergeUp_splitUp]
  exact Biset.Hom.horizontal_id _ _

private theorem frame_eq {U : Type*} [Group U] {K H : Subgroup U}
    {p₀ p q q₀ : Word K H}
    (pre : LabelledDrawing Complex p₀ p) (post : LabelledDrawing Complex q q₀)
    (preInv : LabelledDrawing Complex p p₀) (postInv : LabelledDrawing Complex q₀ q)
    (hp : preInv.interpret.eval.vertical pre.interpret.eval = Biset.Hom.id p.basis)
    (hq : post.interpret.eval.vertical postInv.interpret.eval = Biset.Hom.id q.basis)
    (x y : LabelledDrawing Complex p q) :
    ev (before pre (before x post)) = ev (before pre (before y post)) ↔
      x.interpret.eval = y.interpret.eval := by
  constructor
  · intro h
    have he : pre.interpret.eval.vertical (x.interpret.eval.vertical post.interpret.eval) =
        pre.interpret.eval.vertical (y.interpret.eval.vertical post.interpret.eval) :=
      Biset.Hom.ext h
    have undo (z : LabelledDrawing Complex p q) :
        (preInv.interpret.eval.vertical (pre.interpret.eval.vertical
          (z.interpret.eval.vertical post.interpret.eval))).vertical postInv.interpret.eval =
        z.interpret.eval := by
      rw [← Biset.Hom.vertical_assoc preInv.interpret.eval, hp, Biset.Hom.id_vertical,
        Biset.Hom.vertical_assoc, hq, Biset.Hom.vertical_id]
    have h' := congrArg (fun z => (preInv.interpret.eval.vertical z).vertical postInv.interpret.eval) he
    exact (undo x).symm.trans (h'.trans (undo y))
  · intro h
    exact congrArg (fun z : Biset.Hom Complex p.basis q.basis =>
      (pre.interpret.eval.vertical (z.vertical post.interpret.eval)).toLinearMap) h

private theorem framed_target {U : Type*} [Group U] {K H : Subgroup U}
    {p₀ p q q₀ : Word K H}
    (pre : LabelledDrawing Complex p₀ p) (post : LabelledDrawing Complex q q₀)
    (preInv : LabelledDrawing Complex p p₀) (postInv : LabelledDrawing Complex q₀ q)
    (hp : pre.interpret.eval.vertical preInv.interpret.eval = Biset.Hom.id p₀.basis)
    (hq : postInv.interpret.eval.vertical post.interpret.eval = Biset.Hom.id q₀.basis)
    (target : LabelledDrawing Complex p₀ q₀) :
    ev (before pre (before (before preInv (before target postInv)) post)) = ev target := by
  change (pre.interpret.eval.vertical
    ((preInv.interpret.eval.vertical (target.interpret.eval.vertical postInv.interpret.eval)).vertical
      post.interpret.eval)).toLinearMap = _
  rw [Biset.Hom.vertical_assoc preInv.interpret.eval,
    ← Biset.Hom.vertical_assoc pre.interpret.eval, hp, Biset.Hom.id_vertical,
    Biset.Hom.vertical_assoc, hq, Biset.Hom.vertical_id]

private theorem projection_comparison
    (drawing : LabelledDrawing Complex (bottom a b c) (top d e f)) (q : A)
    (h : ∀ (g : G) (k : F), Pulls (mergedEval a b c d e f drawing)
      (pair (.up (d.comp e)) (.down f) g k)
      (Generator.mixedPair a (b.comp c) (a.toHom g * q * (b.comp c).toHom k))) :
    drawing.interpret.eval = (targetProjection a b c d e f p).interpret.eval ↔ q = p.dot.element := by
  classical
  have htarget : mergedEval a b c d e f (targetProjection a b c d e f p) =
      ev (.compactProjection a (b.comp c) (d.comp e) f [(1, p)]) :=
    framed_target (splitBottom a b c) (mergeTop d e f) (mergeBottom a b c) (splitTop d e f)
      (cancel_splitBottom_mergeBottom a b c) (cancel_splitTop_mergeTop d e f) _
  rw [← frame_eq (splitBottom a b c) (mergeTop d e f) (mergeBottom a b c) (splitTop d e f)
    (cancel_mergeBottom_splitBottom a b c) (cancel_mergeTop_splitTop d e f)]
  change (mergedEval a b c d e f drawing =
    mergedEval a b c d e f (targetProjection a b c d e f p)) ↔ _
  rw [htarget]
  constructor
  · intro he
    have hq := h 1 1 (Finsupp.single (Generator.mixedPair a (b.comp c) q) 1)
    rw [he] at hq
    rw [pulls_compact a (b.comp c) (d.comp e) f p 1 1 _] at hq
    simp only [map_one, one_mul, mul_one, Finsupp.single_eq_same] at hq
    by_contra hne
    have hne' : Generator.mixedPair a (b.comp c) (p.dot.element) ≠
        Generator.mixedPair a (b.comp c) q :=
      fun h => hne ((Generator.mixedEquiv a (b.comp c)).symm.injective h.symm)
    rw [Finsupp.single_eq_of_ne hne'] at hq
    exact zero_ne_one hq
  · rintro rfl
    apply LinearMap.ext
    intro input
    apply Finsupp.ext
    intro output
    refine Quotient.inductionOn output (fun ⟨g,k⟩ => ?_)
    exact (h g k input).trans (pulls_compact a (b.comp c) (d.comp e) f p g k input).symm

private theorem left_project_eval {r : ConjEmbedding B G} {s : ConjEmbedding B D}
    {t : ConjEmbedding E B} (x : ProjectionDot.Mixed a b r s) (y : ProjectionDot.Mixed s c t f)
    (z : Dot (r.comp t) (d.comp e)) :
    (leftDrawing a b c d e f r s t [(1,x)] [(1,y)] [(1,z)]).interpret.eval =
      (targetProjection a b c d e f p).interpret.eval ↔ leftParameter a b c d e f x.dot y.dot z = p.dot.element :=
  projection_comparison a b c d e f p _ _ (pulls_left a b c d e f x y z)

private theorem right_project_eval {j : ConjEmbedding B A} {v : ConjEmbedding C B}
    {w : ConjEmbedding F B} (ell : Dot (b.comp c) (j.comp w))
    (m : ProjectionDot.Mixed a j d v) (n : ProjectionDot.Mixed v w e f) :
    (rightDrawing a b c d e f j v w [(1,ell)] [(1,m)] [(1,n)]).interpret.eval =
      (targetProjection a b c d e f p).interpret.eval ↔ rightParameter a b c d e f ell m.dot n.dot = p.dot.element :=
  projection_comparison a b c d e f p _ _ (pulls_right a b c d e f ell m n)

end
end OutsideRegionsAux
