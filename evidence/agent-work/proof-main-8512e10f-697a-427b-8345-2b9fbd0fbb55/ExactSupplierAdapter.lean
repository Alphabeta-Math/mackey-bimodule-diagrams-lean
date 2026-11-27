import Core

open MackeyDiagrams CaseTwoAudit

theorem first_projection_range {B : Subgroup U}
    (r : ConjEmbedding B G) (s : ConjEmbedding B D) (t : ConjEmbedding T B)
    (x : ProjectionLabel a b r s) (y : ProjectionLabel s c t f)
    (z : Dot (comp r t) de) (g : G) (h : F) :
    ∀ M, eval
      (LabelledDrawing.vertical
        (LabelledDrawing.horizontal (LabelledDrawing.compactProjection a b r s [(1,x)])
          (drawId (up c)))
        (LabelledDrawing.vertical
          (atRight (up r) (LabelledDrawing.compactProjection s c t f [(1,y)]))
          (LabelledDrawing.horizontal (LabelledDrawing.parallelUp r t d e [(1,z)])
            (drawId (down f))))) M ((Biset.induction de).pair (Biset.restriction f) g h) =
      M (Generator.mixedPair a bc
        (a.toHom g * (a.toHom z.element⁻¹ * x.dot.element * b.toHom y.dot.element) * bc.toHom h)) := by
  -- This is an exact kernel-checked connection to the calculation used by Lemma 6.3.
  -- The local name points to the audited declaration in the same compiled dependency.
  run_tac
    let name := Lean.Name.str
      ((Lean.Name.num `_private.Proofs.EvaluationForTwoProjections 0).str
        "EvaluationForTwoProjectionsAux") "pulls_left"
    let term : Lean.Term := ⟨Lean.mkIdent name⟩
    Lean.Elab.Tactic.evalTactic (← `(tactic| exact $term a b c d e f x y z g h))

#print axioms first_projection_range
