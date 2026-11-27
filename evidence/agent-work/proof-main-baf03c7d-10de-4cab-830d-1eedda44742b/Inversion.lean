
namespace CaseTwoAudit

open MackeyDiagrams

private theorem collect_terms {X : Type*} (xs : X →₀ Complex) :
    CaseTwoFirstStage.collectProjection (terms xs) = xs := by
  unfold CaseTwoFirstStage.collectProjection terms
  rw [List.map_map, Finset.sum_map_toList]
  exact Finsupp.sum_single xs

private theorem projection_eval_collect {V : Type*} [Group V]
    {K H P L : Subgroup V} (α : ConjEmbedding K P) (β : ConjEmbedding H P)
    (η : ConjEmbedding L K) (θ : ConjEmbedding L H)
    (xs : List (Complex × ProjectionDot.Mixed α β η θ)) :
    (LabelledDrawing.compactProjection α β η θ xs).interpret.eval =
      (LabelledDrawing.compactProjection α β η θ
        (terms (CaseTwoFirstStage.collectProjection xs))).interpret.eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  rw [CaseTwoFirstStage.eval_collectProjection, CaseTwoFirstStage.eval_collectProjection,
    collect_terms]

private theorem castBoundary_eq_reindex {V : Type*} [Group V] {K H : Subgroup V}
    {p q p' q' : Boundary K H} (hp : p = p') (hq : q = q')
    (m : Biset.Hom Complex p.word.basis q.word.basis) :
    CaseTwoFirstStage.castBoundary hp hq m = reindexBoundaryHom hp hq m := by
  cases hp
  cases hq
  rfl

private theorem cast_eq_reindex {V : Type*} [Group V] {K H : Subgroup V}
    {p q p' q' : Boundary K H} (hp : p = p') (hq : q = q')
    (m : Biset.Hom Complex p.word.basis q.word.basis) :
    cast (congrArg₂ (fun X Y : Boundary K H => Biset.Hom Complex X.word.basis Y.word.basis)
      hp hq) m = reindexBoundaryHom hp hq m := by
  cases hp
  cases hq
  rfl

private theorem reindex_stage_two {V : Type*} [Group V] {K H : Subgroup V}
    {p q p' q' : Word K H} (stage : LabelledDrawing Complex p q)
    (normal : LabelledDrawing Complex p' q')
    (hp : p.boundary = p'.boundary) (hq : q'.boundary = q.boundary)
    (h : CaseTwoStage.evalAt stage hp rfl = CaseTwoStage.evalAt normal rfl hq) :
    reindexBoundaryHom hp hq.symm stage.interpret.atBoundary.eval =
      normal.interpret.atBoundary.eval := by
  have hf {P Q P' Q' : Boundary K H} (h₁ : P = P') (h₂ : Q' = Q)
      (m : Biset.Hom Complex P.word.basis Q.word.basis)
      (n : Biset.Hom Complex P'.word.basis Q'.word.basis)
      (he : reindexBoundaryHom h₁ rfl m = reindexBoundaryHom rfl h₂ n) :
      reindexBoundaryHom h₁ h₂.symm m = n := by
    cases h₁
    cases h₂
    exact he
  apply hf hp hq
  have same {x y : Word K H} (d : LabelledDrawing Complex x y)
      {P Q : Boundary K H} (a : x.boundary = P) (b : y.boundary = Q) :
      CaseTwoStage.evalAt d a b = reindexBoundaryHom a b d.interpret.atBoundary.eval := by
    cases a
    cases b
    rfl
  simpa only [same] using h

private theorem first_collected {B : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (xs : List (Complex × ProjectionLabel a b r s)) :
    let lhs := (LabelledDrawing.compactProjection a b r s xs).horizontal (drawId (up c))
    let rhs := (LabelledDrawing.compactProjection a b r s
      (terms (CaseTwoFirstStage.collectProjection xs))).horizontal (drawId (up c))
    lhs.interpret.atBoundary.eval = rhs.interpret.atBoundary.eval := by
  dsimp only
  apply (ScopedDiagram.eval_atBoundary_eq_iff _ _).2
  exact congrArg (fun m => m.horizontal (drawId (up c)).interpret.eval)
    (projection_eval_collect a b r s xs)

private theorem second_collected {B : Subgroup U} (r : ConjEmbedding B G)
    (s : ConjEmbedding B D) (t : ConjEmbedding T B)
    (ys : List (Complex × ProjectionLabel s c t f)) :
    (CaseTwoStage.rightProjection r s c t f ys).interpret.atBoundary.eval =
      (atRight (up r) (LabelledDrawing.compactProjection s c t f
        (terms (CaseTwoFirstStage.collectProjection ys)))).interpret.atBoundary.eval := by
  apply (ScopedDiagram.eval_atBoundary_eq_iff _ _).2
  exact congrArg (fun m =>
    (Diagram.associate (R := Complex) (up r) (down s) (up c)).eval.vertical
      (((drawId (up r)).interpret.eval.horizontal m).vertical
        (Diagram.unassociate (R := Complex) (up r) (up t) (down f)).eval))
    (projection_eval_collect s c t f ys)

/-- Normalize the three actual singleton stages at their common ordered boundaries. -/
theorem checked_left_inversion : CaseTwoLeftInversion := by
  intro replacement
  obtain ⟨m, n, stage₁, stage₂, stage₃, hc₁, hc₂, hc₃, hcut⟩ :=
    CaseTwoFactor.factor_left replacement.diagram
      (checked_leftCode replacement.diagram replacement.shape_eq)
  obtain ⟨B, r, s, xs, hm, h₁⟩ :=
    first_stage_at_boundary stage₁ hc₁ replacement.bottom_eq
  obtain ⟨t, ys, hn, h₂⟩ :=
    CaseTwoStage.secondStage_fixedSuffix r s c d e f stage₂ stage₃ hc₂ hc₃ hm replacement.top_eq
  obtain ⟨zs, h₃⟩ := normalize_case_two_third stage₃ hc₃ r t hn.symm replacement.top_eq
  refine ⟨B, r, s, t, CaseTwoFirstStage.collectProjection xs,
    CaseTwoFirstStage.collectProjection ys, zs, ?_⟩
  have he₁ := ((castBoundary_eq_reindex _ _ _).symm.trans h₁).trans (first_collected r s xs)
  have he₂ := (reindex_stage_two _ _ hm hn h₂).trans (second_collected r s t ys)
  have he₃ := (cast_eq_reindex hn.symm replacement.top_eq
    stage₃.interpret.atBoundary.eval).symm.trans h₃
  exact (eval_planarAtBoundary replacement).trans
    (combine_cut_stage_equalities replacement.bottom_eq hm hn.symm replacement.top_eq
      hcut he₁ he₂ he₃)

end CaseTwoAudit
