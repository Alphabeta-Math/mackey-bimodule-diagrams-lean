import MackeyDiagrams.DrawingShape
import MackeyDiagrams.LinearDotComposition

/-! A dot label is a finitely supported coefficient function on eligible
group elements. The coefficient ring is generalized; specialize to `Complex`
for the article. Eligibility is checked term by term by the type `Dot a b`.
Neither the support nor its coefficients contribute vertices to the shape. -/

namespace MackeyDiagrams

universe u v
variable {U : Type u} [Group U] {H G : Subgroup U}

abbrev DotLabel (R : Type v) [Zero R] (a b : ConjEmbedding H G) := Dot a b →₀ R

namespace DotLabel

variable {R : Type v} [CommSemiring R] {a b c : ConjEmbedding H G}

noncomputable def identity (a : ConjEmbedding H G) : DotLabel R a a :=
  Finsupp.single (Dot.id a) 1

noncomputable def terms (label : DotLabel R a b) : List (R × Dot a b) :=
  label.support.toList.map fun d => (label d, d)

noncomputable def upDrawing (label : DotLabel R a b) :
    LabelledDrawing R (.up a) (.up b) := .upDot label.terms

noncomputable def downDrawing (label : DotLabel R a b) :
    LabelledDrawing R (.down a) (.down b) := .downDot label.terms

theorem eligible (label : DotLabel R a b) (d : Dot a b) (_ : label d ≠ 0) (h : H) :
    a.toHom h * d.element = d.element * b.toHom h := d.intertwines h

theorem upDrawing_shape (label : DotLabel R a b) :
    label.upDrawing.erase = .vertex .upDot := rfl

theorem downDrawing_shape (label : DotLabel R a b) :
    label.downDrawing.erase = .vertex .downDot := rfl

theorem eval_upDrawing (label : DotLabel R a b) :
    label.upDrawing.interpret.eval = (Diagram.linearUpDot label).eval := by
  simp only [upDrawing, terms, LabelledDrawing.interpret, ScopedDiagram.eval,
    Diagram.linearUpDot, List.map_map]
  rfl

theorem eval_downDrawing (label : DotLabel R a b) :
    label.downDrawing.interpret.eval = (Diagram.linearDownDot label).eval := by
  simp only [downDrawing, terms, LabelledDrawing.interpret, ScopedDiagram.eval,
    Diagram.linearDownDot, List.map_map]
  rfl

/-- Inserting an identity-labelled dot does not change the induction map. -/
theorem upDrawing_identity (a : ConjEmbedding H G) :
    (upDrawing (identity (R := R) a)).interpret.eval = Biset.Hom.id (Word.up a).basis := by
  rw [eval_upDrawing]
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x r
  rw [Diagram.eval_linearUpDot_apply, identity, freeLift_single, one_smul,
    Diagram.eval_upDot_single]
  simp [Dot.id, Biset.Hom.id]

/-- The restriction orientation has the same identity-dot theorem. -/
theorem downDrawing_identity (a : ConjEmbedding H G) :
    (downDrawing (identity (R := R) a)).interpret.eval = Biset.Hom.id (Word.down a).basis := by
  rw [eval_downDrawing]
  apply Biset.Hom.ext
  apply Finsupp.lhom_ext
  intro x r
  rw [Diagram.eval_linearDownDot_apply, identity, freeLift_single, one_smul,
    Diagram.eval_downDot_single]
  simp [Dot.id, Biset.Hom.id]

theorem upDrawing_basis (label : DotLabel R a b) (x : G) :
    label.upDrawing.interpret.eval.toLinearMap (Finsupp.single x 1) =
      (label.support.toList.map fun d => label d • Finsupp.single (x * d.element) 1).sum := by
  rw [eval_upDrawing]
  exact Diagram.eval_linearUpDot_single label x

/-- Inverting the group element is termwise. Coefficients are neither
inverted nor conjugated, and the whole linear label need not be a unit. -/
theorem downDrawing_basis (label : DotLabel R a b) (x : G) :
    label.downDrawing.interpret.eval.toLinearMap (Finsupp.single x 1) =
      (label.support.toList.map fun d => label d • Finsupp.single (d.element⁻¹ * x) 1).sum := by
  rw [eval_downDrawing]
  exact Diagram.eval_linearDownDot_single label x

noncomputable def compose (first : DotLabel R a b) (second : DotLabel R b c) :
    DotLabel R a c := Dot.linearProduct first second

theorem upDrawing_compose (first : DotLabel R a b) (second : DotLabel R b c) :
    (first.upDrawing.vertical second.upDrawing).interpret.eval =
      (compose first second).upDrawing.interpret.eval := by
  change first.upDrawing.interpret.eval.vertical second.upDrawing.interpret.eval = _
  rw [eval_upDrawing, eval_upDrawing, eval_upDrawing]
  exact Diagram.linearUpDot_vertical first second

theorem downDrawing_compose (first : DotLabel R a b) (second : DotLabel R b c) :
    (first.downDrawing.vertical second.downDrawing).interpret.eval =
      (compose first second).downDrawing.interpret.eval := by
  change first.downDrawing.interpret.eval.vertical second.downDrawing.interpret.eval = _
  rw [eval_downDrawing, eval_downDrawing, eval_downDrawing]
  exact Diagram.linearDownDot_vertical first second

end DotLabel
end MackeyDiagrams
