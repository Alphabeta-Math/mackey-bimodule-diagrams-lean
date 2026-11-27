
section Drawing
variable {U : Type u} [Group U] {H G : Subgroup U}
variable {R : Type v} [CommSemiring R] {a b : ConjEmbedding H G}

private theorem up_eval (z : DotLabel R a b) (x : G →₀ R) :
    z.upDrawing.interpret.eval.toLinearMap x =
      freeLift R (fun d => (Diagram.upDot d).eval.toLinearMap x) z := by
  rw [DotLabel.eval_upDrawing, Diagram.eval_linearUpDot_apply]

private theorem down_eval (z : DotLabel R a b) (x : G →₀ R) :
    z.downDrawing.interpret.eval.toLinearMap x =
      freeLift R (fun d => (Diagram.downDot d).eval.toLinearMap x) z := by
  rw [DotLabel.eval_downDrawing, Diagram.eval_linearDownDot_apply]

private theorem up_dual (z : DotLabel R a b) (x : G →₀ R) :
    (DotLabel.upDrawing (Finsupp.mapDomain Dot.inverse z)).interpret.eval.toLinearMap x =
      freeLift R (fun d => (Diagram.upDot d.inverse).eval.toLinearMap x) z := by
  rw [up_eval, lift_dual]

private theorem down_dual (z : DotLabel R a b) (x : G →₀ R) :
    (DotLabel.downDrawing (Finsupp.mapDomain Dot.inverse z)).interpret.eval.toLinearMap x =
      freeLift R (fun d => (Diagram.downDot d.inverse).eval.toLinearMap x) z := by
  rw [down_eval, lift_dual]

/- In the draft, the first proof step reduces each comparison to group-element
   dots by linearity. Here freeLift implements that reduction, keeping the
   empty sum and arbitrary coefficients. The drawing interpretation reduces
   horizontal and vertical syntax to composition of the evaluated maps. -/
theorem multiplication_label (z : DotLabel R a b) :
    (z.upDrawing.interpret.eval.horizontal (Diagram.id (.down b)).eval).vertical
      (Diagram.multiplicationCap b).eval =
    ((Diagram.id (.up a)).eval.horizontal
      (DotLabel.downDrawing (Finsupp.mapDomain Dot.inverse z)).interpret.eval).vertical
      (Diagram.multiplicationCap a).eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro w
  simp only [Biset.Hom.vertical, LinearMap.comp_apply]
  rw [lift_horizontal_left z _ _ (up_eval z), lift_horizontal_right z _ _ _ (down_dual z),
    lift_map, lift_map]
  apply congrArg (fun basis => freeLift R basis z)
  funext d
  exact congrArg (fun m => Biset.Hom.toLinearMap m w) (multiplication (R := R) d)

theorem trace_label (z : DotLabel R a b) :
    (z.downDrawing.interpret.eval.horizontal (Diagram.id (.up b)).eval).vertical
      (Diagram.traceCap b).eval =
    ((Diagram.id (.down a)).eval.horizontal
      (DotLabel.upDrawing (Finsupp.mapDomain Dot.inverse z)).interpret.eval).vertical
      (Diagram.traceCap a).eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro w
  simp only [Biset.Hom.vertical, LinearMap.comp_apply]
  rw [lift_horizontal_left z _ _ (down_eval z), lift_horizontal_right z _ _ _ (up_dual z),
    lift_map, lift_map]
  apply congrArg (fun basis => freeLift R basis z)
  funext d
  exact congrArg (fun m => Biset.Hom.toLinearMap m w) (trace (R := R) d)

theorem ordinary_label (z : DotLabel R a b) :
    (Diagram.ordinaryCup a).eval.vertical
      (z.downDrawing.interpret.eval.horizontal (Diagram.id (.up a)).eval) =
    (Diagram.ordinaryCup b).eval.vertical ((Diagram.id (.down b)).eval.horizontal
      (DotLabel.upDrawing (Finsupp.mapDomain Dot.inverse z)).interpret.eval) := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro w
  simp only [Biset.Hom.vertical, LinearMap.comp_apply]
  rw [lift_horizontal_left z _ _ (down_eval z), lift_horizontal_right z _ _ _ (up_dual z)]
  apply congrArg (fun basis => freeLift R basis z)
  funext d
  exact congrArg (fun m => Biset.Hom.toLinearMap m w) (ordinary (R := R) d)

theorem reverse_label (z : DotLabel R a b) (ha : a.toHom.range.FiniteIndex)
    (hb : b.toHom.range.FiniteIndex) :
    (Diagram.reverseCup a ha).eval.vertical
      (z.upDrawing.interpret.eval.horizontal (Diagram.id (.down a)).eval) =
    (Diagram.reverseCup b hb).eval.vertical ((Diagram.id (.up b)).eval.horizontal
      (DotLabel.downDrawing (Finsupp.mapDomain Dot.inverse z)).interpret.eval) := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro w
  simp only [Biset.Hom.vertical, LinearMap.comp_apply]
  rw [lift_horizontal_left z _ _ (up_eval z), lift_horizontal_right z _ _ _ (down_dual z)]
  apply congrArg (fun basis => freeLift R basis z)
  funext d
  exact congrArg (fun m => Biset.Hom.toLinearMap m w) (reverse (R := R) d ha hb)

end Drawing
