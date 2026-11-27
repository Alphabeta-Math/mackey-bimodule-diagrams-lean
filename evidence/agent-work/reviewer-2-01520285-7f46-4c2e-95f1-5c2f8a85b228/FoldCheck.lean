import MackeyDiagrams.DrawingShape
import Mathlib.Basic.Complex.Basic

open MackeyDiagrams

universe u
variable {U : Type u} [Group U] {K H : Subgroup U} {p q : Word K H}

private def foldDrawing (terms : List (Complex × LabelledDrawing Complex p q)) :
    LabelledDrawing Complex p q :=
  terms.foldr (fun term rest => .add (.scale term.1 term.2) rest)
    (.ordinary (.zero p q))

example (x : Finsupp p.basis.carrier Complex) :
    (foldDrawing (p := p) (q := q) []).interpret.eval.toLinearMap x = 0 := rfl

example (c : Complex) (d : LabelledDrawing Complex p q)
    (x : Finsupp p.basis.carrier Complex) :
    (foldDrawing [(c, d)]).interpret.eval.toLinearMap x =
      c • d.interpret.eval.toLinearMap x := by
  change c • d.interpret.eval.toLinearMap x + 0 = _
  exact add_zero _
