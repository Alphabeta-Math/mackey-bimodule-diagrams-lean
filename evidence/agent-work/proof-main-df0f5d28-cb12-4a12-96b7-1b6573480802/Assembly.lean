namespace DotSlidePreorderProof

open MackeyDiagrams

universe u
variable {U : Type u} [Group U]

private theorem transport_id_eq_boundaryId {G K : Subgroup U}
    {P Q : Boundary G K} (h : P = Q) :
    DotSlideStructuralCoherence.transport h
      (Biset.Hom.id (R := Complex) P.word.basis) = boundaryId h := by
  subst Q
  rfl

private theorem cast_boundaryId {G K : Subgroup U} {P Q : Boundary G K} (h : P = Q) :
    cast (congrArg (fun b => BoundaryMap P b) h.symm) (boundaryId h) =
      Biset.Hom.id (R := Complex) P.word.basis := by
  subst Q
  rfl

private theorem dot_empty_coherence : EmptyCodeCoherence U := by
  intro G K p q d h
  obtain ⟨he, hev⟩ := empty_geometry_atBoundary d h
  exact ⟨he, hev.trans (transport_id_eq_boundaryId he)⟩

private theorem merge_empty_coherence : EmptyCodeStraight U := by
  intro G K p q d h
  obtain ⟨he, hev⟩ := dot_empty_coherence (U := U) d h
  apply straightAt_of_eq he
  change cast _ (canon d.interpret.eval) = _
  rw [hev]
  exact cast_boundaryId he

end DotSlidePreorderProof

namespace DotSlidePreorderBridge

open MackeyDiagrams DotSlidePreorderProof

universe u
variable {U : Type u} [Group U] {G K : Subgroup U}

private abbrev BoundaryHom (p q : Boundary G K) :=
  Biset.Hom Complex p.word.basis q.word.basis

private theorem heq_of_hom_cast {p q p' q' : Boundary G K}
    (hp : p = p') (hq : q = q') {f : BoundaryHom p q} {g : BoundaryHom p' q'}
    (h : cast (congrArg₂ (fun b c : Boundary G K => BoundaryHom b c) hp hq) f = g) :
    HEq f g := by
  subst p'
  subst q'
  exact heq_of_eq h

private theorem vertical_heq {p m q p' m' q' : Boundary G K}
    (hp : p = p') (hm : m = m') (hq : q = q')
    {f : BoundaryHom p m} {f' : BoundaryHom p' m'}
    {g : BoundaryHom m q} {g' : BoundaryHom m' q'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (f.vertical g) (f'.vertical g') := by
  subst p'
  subst m'
  subst q'
  rw [eq_of_heq hf, eq_of_heq hg]

/- Proposition 3.2 uses (3.1) on the displayed right-input drawing.
   For the full planar fiber, first cut its rigid event list and normalize the
   two typed stages. The source shape provides the width-two hypothesis.
   On the shared middle word the two normalized ordered boundaries agree,
   including both embedding labels. Transport both evaluations through that
   common boundary before composing. -/
private theorem stagedNormalForm : StagedNormalForm U := by
  intro G K p m q below above hw hb ha
  let v : LabelledDrawing.PlanarAtBoundary Complex p.boundary m.boundary below.planarShape :=
    ⟨p, m, below, rfl, rfl, rfl⟩
  obtain ⟨H, l, a, b, label, hp, hm, hd⟩ :=
    normalizeRightDot (dot_empty_coherence (U := U)) v hb hw
  have hmw : m.directions.length ≤ 2 := by
    have h := congrArg boundaryDirections hm
    rw [boundaryDirections_word, boundaryDirections_word] at h
    rw [← h]
    change 2 ≤ 2
    exact le_rfl
  obtain ⟨J, l', b', hm', hq, he⟩ :=
    singleton_merge_normal_form (merge_empty_coherence (U := U)) above ha hmw
  obtain ⟨hJ, hl, hb'⟩ := branchBoundary_inj l b l' b' (hm'.symm.trans hm.symm)
  subst J
  have hl' := eq_of_heq hl
  have hb'' := eq_of_heq hb'
  subst l'
  subst b'
  let dotStage : LabelledDrawing Complex (pair l a) (pair l b) :=
    (LabelledDrawing.ordinary (Diagram.id (.up l))).horizontal label.upDrawing
  let mergeStage : LabelledDrawing Complex (pair l b) (.up (l.comp b)) :=
    .trivalent (.mergeUp l b)
  let dotRep : LabelledDrawing.PlanarAtBoundary Complex p.boundary m.boundary singletonRightShape :=
    ⟨_, _, dotStage, hp, hm, rfl⟩
  have hd' : HEq below.interpret.atBoundary.eval dotStage.interpret.atBoundary.eval :=
    (heq_of_eq (show below.interpret.atBoundary.eval = dotRep.interpret.eval from hd)).trans
      (atBoundary_eval_heq dotRep)
  have he' : HEq above.interpret.atBoundary.eval mergeStage.interpret.atBoundary.eval :=
    heq_of_hom_cast hm' hq he
  let rep : LabelledDrawing.PlanarAtBoundary Complex p.boundary q.boundary rightShape :=
    ⟨_, _, branch l label, hp, hq.symm, branch_shape l label⟩
  refine ⟨H, l, a, b, label, hp, hq.symm, ?_⟩
  have hv := vertical_heq hp.symm hm.symm hq hd' he'
  rw [← normalize_vertical below.interpret above.interpret,
    ← normalize_vertical dotStage.interpret mergeStage.interpret] at hv
  exact eq_of_heq (hv.trans (atBoundary_eval_heq rep).symm)

private theorem wholeFiber : NormalForm U := normalForm_of_staged stagedNormalForm

end DotSlidePreorderBridge
