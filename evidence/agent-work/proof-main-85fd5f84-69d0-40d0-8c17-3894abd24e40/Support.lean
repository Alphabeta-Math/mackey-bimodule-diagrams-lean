namespace RightInputDotSlideProof

open MackeyDiagrams

variable {U : Type*} [Group U] {K H G : Subgroup U}

/-- Evaluate the merged-strand mark on the balanced tensor of the two units. -/
private theorem trunkUnit (γ : ConjEmbedding H G) (α : ConjEmbedding K H)
    (d : Dot (γ.comp α) (γ.comp α)) :
    ((LabelledDrawing.trivalent (TrivalentVertex.mergeUp γ α)).vertical
      (DotLabel.upDrawing (Finsupp.single d (1 : Complex)))).interpret.eval.toLinearMap
      (Finsupp.single ((Biset.induction γ).pair (Biset.induction α) 1 1) 1) =
      Finsupp.single d.element 1 := by
  change (DotLabel.upDrawing (Finsupp.single d (1 : Complex))).interpret.eval.toLinearMap
    ((Diagram.mergeUp γ α).eval.toLinearMap
      (Finsupp.single ((Biset.induction γ).pair (Biset.induction α) 1 1) 1)) = _
  rw [Diagram.eval_mergeUp_single, map_one, one_mul, DotLabel.eval_upDrawing,
    Diagram.eval_linearUpDot_apply, freeLift_single, one_smul,
    Diagram.eval_upDot_single, one_mul]

/-- The right-input drawing pushes each eligible term through the outer embedding. -/
private theorem branchUnit (γ : ConjEmbedding H G) (α β : ConjEmbedding K H)
    (label : DotLabel Complex α β) :
    (((LabelledDrawing.ordinary (Diagram.id (Word.up γ))).horizontal
      (DotLabel.upDrawing label)).vertical
      (LabelledDrawing.trivalent (TrivalentVertex.mergeUp γ β))).interpret.eval.toLinearMap
      (Finsupp.single ((Biset.induction γ).pair (Biset.induction α) 1 1) 1) =
      Finsupp.mapDomain (fun term => γ.toHom term.element) label := by
  classical
  let outer := Biset.induction γ
  let inner := Biset.induction β
  let merge := (Diagram.mergeUp (R := Complex) γ β).eval.toLinearMap
  let dot := (DotLabel.upDrawing label).interpret.eval
  let straight := (Diagram.id (R := Complex) (Word.up γ)).eval
  let pairAtOne := Biset.pairLinear Complex outer inner (Finsupp.single 1 1)
  change merge ((straight.horizontal dot).toLinearMap
    (Finsupp.single (outer.pair (Biset.induction α) 1 1) 1)) = _
  rw [Biset.Hom.horizontal_single, one_smul]
  change merge (pairAtOne (dot.toLinearMap (Finsupp.single 1 1))) = _
  rw [show dot.toLinearMap (Finsupp.single 1 1) =
      (label.support.toList.map (fun d => label d • Finsupp.single d.element 1)).sum by
    simpa only [dot, one_mul] using DotLabel.upDrawing_basis label (1 : H)]
  change (merge.comp pairAtOne)
      ((label.support.toList.map (fun d => label d • Finsupp.single d.element 1)).sum) = _
  rw [map_list_sum, List.map_map, ← List.sum_toFinset _ label.support.nodup_toList,
    Finset.toList_toFinset, Finsupp.mapDomain, Finsupp.sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  change merge (pairAtOne (label d • Finsupp.single d.element 1)) = _
  rw [map_smul, map_smul]
  dsimp only [pairAtOne, merge, outer, inner]
  rw [Biset.pairLinear_single, mul_one, Diagram.eval_mergeUp_single, one_mul,
    Finsupp.smul_single, smul_eq_mul, mul_one]

end RightInputDotSlideProof
