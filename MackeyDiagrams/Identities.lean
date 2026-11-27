import MackeyDiagrams.Diagram

/-! Diagram identities proved by evaluation on the balanced basis. -/

namespace MackeyDiagrams

universe u v

variable {U : Type u} [Group U]
variable {R : Type v} [CommSemiring R]

namespace Dot

variable {A B C : Subgroup U} {a a' : ConjEmbedding A B}

def whisker (b : ConjEmbedding B C) (d : Dot a a') : Dot (b.comp a) (b.comp a') where
  element := b.toHom d.element
  intertwines := fun h => by
    simp only [ConjEmbedding.comp_apply, ← map_mul]
    rw [d.intertwines]

end Dot

namespace Diagram

variable {A B C : Subgroup U}

theorem eval_ext {p q : Word A B} {x y : Diagram R p q}
    (h : ∀ (z : p.basis.carrier) (r : R),
      x.eval.toLinearMap (Finsupp.single z r) = y.eval.toLinearMap (Finsupp.single z r)) :
    x.eval = y.eval :=
  Biset.Hom.ext (Finsupp.lhom_ext h)

@[simp] theorem eval_upDot_single {a b : ConjEmbedding A B} (d : Dot a b)
    (z : B) (r : R) :
    (upDot (R := R) d).eval.toLinearMap (Finsupp.single z r) =
      Finsupp.single (z * d.element) r := by
  change (Generator.upDot R d).toLinearMap _ = _
  unfold Generator.upDot
  rw [Biset.Hom.ofFunction_single]

@[simp] theorem eval_downDot_single {a b : ConjEmbedding A B} (d : Dot a b)
    (z : B) (r : R) :
    (downDot (R := R) d).eval.toLinearMap (Finsupp.single z r) =
      Finsupp.single (d.element⁻¹ * z) r := by
  change (Generator.downDot R d).toLinearMap _ = _
  unfold Generator.downDot
  rw [Biset.Hom.ofFunction_single]

theorem upDot_vertical {a b c : ConjEmbedding A B} (d : Dot a b) (e : Dot b c) :
    ((upDot (R := R) d).vertical (upDot e)).eval = (upDot (d.vertical e)).eval := by
  apply eval_ext
  intro x r
  change B at x
  change (upDot e).eval.toLinearMap ((upDot d).eval.toLinearMap (Finsupp.single x r)) = _
  rw [eval_upDot_single (R := R) d x r, eval_upDot_single (R := R) e (x * d.element) r,
    eval_upDot_single (R := R) (d.vertical e) x r]
  rw [show (d.vertical e).element = d.element * e.element from rfl, mul_assoc]

theorem downDot_vertical {a b c : ConjEmbedding A B} (d : Dot a b) (e : Dot b c) :
    ((downDot (R := R) d).vertical (downDot e)).eval = (downDot (d.vertical e)).eval := by
  apply eval_ext
  intro x r
  change B at x
  change (downDot e).eval.toLinearMap ((downDot d).eval.toLinearMap (Finsupp.single x r)) = _
  rw [eval_downDot_single (R := R) d x r, eval_downDot_single (R := R) e (d.element⁻¹ * x) r,
    eval_downDot_single (R := R) (d.vertical e) x r]
  simp [Dot.vertical, mul_assoc]

@[simp] theorem eval_mergeUp_single (b : ConjEmbedding B C) (a : ConjEmbedding A B)
    (x : C) (y : B) (r : R) :
    (mergeUp (R := R) b a).eval.toLinearMap
        (Finsupp.single ((Biset.induction b).pair (Biset.induction a) x y) r) =
      Finsupp.single (x * b.toHom y) r := by
  change (Generator.mergeUp R b a).toLinearMap _ = _
  unfold Generator.mergeUp
  rw [Biset.Hom.ofFunction_single]
  rfl

@[simp] theorem eval_vertical_apply {K H : Subgroup U} {p q t : Word K H}
    (d : Diagram R p q) (e : Diagram R q t) (z : p.basis.carrier →₀ R) :
    (d.vertical e).eval.toLinearMap z = e.eval.toLinearMap (d.eval.toLinearMap z) := rfl

@[simp] theorem eval_id_apply {K H : Subgroup U} (p : Word K H)
    (z : p.basis.carrier →₀ R) : (id (R := R) p).eval.toLinearMap z = z := rfl

@[simp] theorem eval_horizontal_single {K H J : Subgroup U}
    {p p' : Word K H} {q q' : Word H J}
    (d : Diagram R p p') (e : Diagram R q q')
    (x : p.basis.carrier) (y : q.basis.carrier) (r : R) :
    (d.horizontal e).eval.toLinearMap (Finsupp.single (p.basis.pair q.basis x y) r) =
      r • Biset.pairLinear R p'.basis q'.basis
        (d.eval.toLinearMap (Finsupp.single x 1)) (e.eval.toLinearMap (Finsupp.single y 1)) :=
  Biset.Hom.horizontal_single _ _ _ _ _

/-- Moving a dot on the incoming right leg onto the merged induction strand. -/
theorem mergeUp_slide_right (b : ConjEmbedding B C) {a a' : ConjEmbedding A B}
    (d : Dot a a') :
    (((id (R := R) (.up b)).horizontal (.upDot d)).vertical (.mergeUp b a')).eval =
      ((mergeUp b a).vertical (.upDot (d.whisker b))).eval := by
  apply eval_ext
  intro z r
  refine Quotient.inductionOn z (fun xy => ?_)
  rcases xy with ⟨x,y⟩
  change C at x
  change B at y
  change (vertical (horizontal (id (.up b)) (upDot d)) (mergeUp b a')).eval.toLinearMap
      (Finsupp.single ((Word.up b).basis.pair (Word.up a).basis x y) r) =
    (vertical (mergeUp b a) (upDot (d.whisker b))).eval.toLinearMap
      (Finsupp.single ((Word.up b).basis.pair (Word.up a).basis x y) r)
  rw [eval_vertical_apply, eval_vertical_apply,
    eval_horizontal_single (id (R := R) (.up b)) (upDot d) x y r]
  rw [eval_id_apply, eval_upDot_single (R := R) d y 1,
    Biset.pairLinear_single, one_mul]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [eval_mergeUp_single (R := R) b a' x (y * d.element) r,
    eval_mergeUp_single (R := R) b a x y r,
    eval_upDot_single (R := R) (d.whisker b) (x * b.toHom y) r]
  simp [Dot.whisker, mul_assoc]

end Diagram

end MackeyDiagrams

