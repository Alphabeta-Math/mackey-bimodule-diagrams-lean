import MackeyDiagrams.PlanarShape

/-! Checks of the source-to-syntax connection, including the regressions that
blocked Section 3.3. These are library checks, not registered article proofs. -/

namespace MackeyDiagrams.LanguageChecks

universe u v
variable {U : Type u} [Group U]
variable {R : Type v} [CommSemiring R]

theorem trivalent_inputs {K H : Subgroup U} {p q : Word K H}
    (vertex : TrivalentVertex p q) : vertex.kind.inputs = p.directions := by
  cases vertex <;> rfl

theorem trivalent_outputs {K H : Subgroup U} {p q : Word K H}
    (vertex : TrivalentVertex p q) : vertex.kind.outputs = q.directions := by
  cases vertex <;> rfl

theorem dot_coefficients_preserve_shape {H G : Subgroup U} {a b : ConjEmbedding H G}
    (x y : DotLabel R a b) : x.upDrawing.planarShape = y.upDrawing.planarShape := rfl

theorem zero_dot_keeps_mark {H G : Subgroup U} {a b : ConjEmbedding H G}
    (x : DotLabel R a b) : x.downDrawing.planarShape = (0 : DotLabel R a b).downDrawing.planarShape := rfl

theorem singleton_dot_basis {H G : Subgroup U} {a b : ConjEmbedding H G}
    (d : Dot a b) (c : R) (x : G) :
    (DotLabel.upDrawing (Finsupp.single d c)).interpret.eval.toLinearMap
      (Finsupp.single x (1 : R)) = c • Finsupp.single (x * d.element) (1 : R) := by
  rw [DotLabel.eval_upDrawing, Diagram.eval_linearUpDot_apply, freeLift_single,
    Diagram.eval_upDot_single]

theorem singleton_down_dot_basis {H G : Subgroup U} {a b : ConjEmbedding H G}
    (d : Dot a b) (c : R) (x : G) :
    (DotLabel.downDrawing (Finsupp.single d c)).interpret.eval.toLinearMap
      (Finsupp.single x (1 : R)) = c • Finsupp.single (d.element⁻¹ * x) (1 : R) := by
  rw [DotLabel.eval_downDrawing, Diagram.eval_linearDownDot_apply, freeLift_single,
    Diagram.eval_downDot_single]

theorem group_dot_and_linear_dot_same_shape {H G : Subgroup U}
    {a b : ConjEmbedding H G} (d : Dot a b) (labels : List (R × Dot a b)) :
    (LabelledDrawing.ordinary (Diagram.upDot (R := R) d)).planarShape =
      (LabelledDrawing.upDot labels).planarShape := rfl

theorem merge_is_one_trivalent_vertex {K H G : Subgroup U}
    (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
    (LabelledDrawing.ordinary (Diagram.mergeUp (R := R) b a)).planarShape =
      (LabelledDrawing.trivalent (R := R) (.mergeUp b a)).planarShape := rfl

theorem bent_junction_same_shape {K H G : Subgroup U}
    (b : ConjEmbedding H G) (a : ConjEmbedding K H) :
    (LabelledDrawing.bentVertex (R := R) (.multiplicationCap b a)).planarShape =
      (LabelledDrawing.trivalent (R := R) (.upDownToUp b a)).planarShape := rfl

theorem two_mark_parallel_frame {K H G : Subgroup U}
    (b : ConjEmbedding H G) (a : ConjEmbedding K H)
    (d e : Dot (b.comp a) (b.comp a))
    (x y : List (R × Dot (b.comp a) (b.comp a))) :
    (LabelledDrawing.ordinary ((Diagram.mergeUp (R := R) b a).vertical
      ((Diagram.upDot d).vertical ((Diagram.upDot e).vertical (Diagram.splitUp b a))))).planarShape =
    (LabelledDrawing.parallelUpChain b a b a (.cons x (.cons y (.empty (b.comp a))))).planarShape := rfl

theorem disjoint_dot_heights_preserve_shape {A B C : Subgroup U}
    {a a' : ConjEmbedding B A} {b b' : ConjEmbedding C B}
    (x : List (R × Dot a a')) (y : List (R × Dot b b')) :
    (((LabelledDrawing.upDot x).horizontal (.ordinary (Diagram.id (.up b)))).vertical
        ((LabelledDrawing.ordinary (Diagram.id (.up a'))).horizontal (.upDot y))).planarShape =
    (((LabelledDrawing.ordinary (Diagram.id (.up a))).horizontal (.upDot y)).vertical
        ((LabelledDrawing.upDot x).horizontal (.ordinary (Diagram.id (.up b'))))).planarShape := by
  exact congrArg (PlanarShape.mk [true, true] [true, true])
    (Quotient.sound (PlanarCode.Equivalent.exchange [] [] 0 0
      (.vertex 0 .upDot) (.vertex 0 .upDot)))

theorem disjoint_dot_heights_preserve_evaluation {A B C : Subgroup U}
    {a a' : ConjEmbedding B A} {b b' : ConjEmbedding C B}
    (x : List (R × Dot a a')) (y : List (R × Dot b b')) :
    (((LabelledDrawing.upDot x).horizontal (.ordinary (Diagram.id (.up b)))).vertical
        ((LabelledDrawing.ordinary (Diagram.id (.up a'))).horizontal (.upDot y))).interpret.eval =
    (((LabelledDrawing.ordinary (Diagram.id (.up a))).horizontal (.upDot y)).vertical
        ((LabelledDrawing.upDot x).horizontal (.ordinary (Diagram.id (.up b'))))).interpret.eval :=
  Biset.Hom.horizontal_disjoint (ScopedDiagram.weightedUpDot x).eval (ScopedDiagram.weightedUpDot y).eval

theorem tensor_parentheses_preserve_shape {A B C D : Subgroup U}
    {a a' : ConjEmbedding B A} {b b' : ConjEmbedding C B} {c c' : ConjEmbedding D C}
    (x : List (R × Dot a a')) (y : List (R × Dot b b')) (z : List (R × Dot c c')) :
    (((LabelledDrawing.upDot x).horizontal (.upDot y)).horizontal (.upDot z)).planarShape =
      ((LabelledDrawing.upDot x).horizontal ((LabelledDrawing.upDot y).horizontal (.upDot z))).planarShape := rfl

theorem vertical_parentheses_preserve_shape {H G : Subgroup U}
    {a b c d : ConjEmbedding H G}
    (x : List (R × Dot a b)) (y : List (R × Dot b c)) (z : List (R × Dot c d)) :
    (((LabelledDrawing.upDot x).vertical (.upDot y)).vertical (.upDot z)).planarShape =
      ((LabelledDrawing.upDot x).vertical ((LabelledDrawing.upDot y).vertical (.upDot z))).planarShape := rfl

theorem identity_dot_is_still_a_different_shape {H G : Subgroup U}
    (a : ConjEmbedding H G) :
    (LabelledDrawing.upDot (R := R) [(1, Dot.id a)]).planarShape ≠
      (LabelledDrawing.ordinary (Diagram.id (R := R) (.up a))).planarShape := by
  intro h
  have counts := PlanarCode.length_eq (Quotient.exact (congrArg PlanarShape.wiring h))
  change 1 = 0 at counts
  cases counts

theorem right_curl_keeps_actual_junctions_and_mark {K H G : Subgroup U}
    (inner : ConjEmbedding K H) {a b : ConjEmbedding H G}
    (labels : List (R × Dot (a.comp inner) (b.comp inner)))
    (finite : inner.toHom.range.FiniteIndex) :
    (LabelledDrawing.rightCurlUp inner labels finite).planarShape =
      ((LabelledDrawing.bentVertex (R := R) (.reverseCup a inner finite)).vertical
        (((LabelledDrawing.upDot labels).horizontal (.ordinary (Diagram.id (.down inner)))).vertical
          (.bentVertex (.multiplicationCap b inner)))).planarShape := rfl

theorem projection_presentations_keep_distinct_shapes {K H G L : Subgroup U}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (labels : List (R × ProjectionDot.Mixed a b l r)) :
    (LabelledDrawing.expandedProjection a b l r labels .junction .junction).planarShape ≠
      (LabelledDrawing.expandedProjection a b l r labels .cupAndMerge .junction).planarShape := by
  intro h
  have counts := PlanarCode.length_eq (Quotient.exact (congrArg PlanarShape.wiring h))
  change 3 = 4 at counts
  cases counts

theorem projection_presentations_preserve_evaluation {K H G L : Subgroup U}
    (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding L K) (r : ConjEmbedding L H)
    (labels : List (R × ProjectionDot.Mixed a b l r)) :
    (LabelledDrawing.expandedProjection a b l r labels .junction .junction).interpret.eval =
      (LabelledDrawing.expandedProjection a b l r labels .cupAndMerge .junction).interpret.eval :=
  LabelledDrawing.eval_expandedProjection_opening a b l r labels .junction

end MackeyDiagrams.LanguageChecks
