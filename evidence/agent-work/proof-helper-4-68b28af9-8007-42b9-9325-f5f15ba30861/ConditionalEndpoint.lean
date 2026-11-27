import CaseTwoDriverCheck

set_option maxHeartbeats 2000000

namespace CaseTwoAudit
open MackeyDiagrams

private def GroupObstruction : Prop :=
  (∀ {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D)
      (x : MackeyDiagrams.Dot (comp a r) (comp b s)),
      MackeyDiagrams.Dot.element x ∈ swapCoset →
      B = ⊥ ∧ ∀ y : MackeyDiagrams.Dot (comp a r) (comp b s),
        MackeyDiagrams.Dot.element y ∈ line →
        ¬ Set.Finite {j | MackeyDiagrams.Generator.mixedMultiplicationBasis a b r s y j =
          MackeyDiagrams.Generator.mixedPair a b (MackeyDiagrams.Dot.element y)})

private theorem group_obstruction : GroupObstruction := by
  intro B r s x hx
  have hB := forced_bot r s x hx
  refine ⟨hB, ?_⟩
  subst B
  exact unbounded_line_fiber r s

private theorem rhs_one_nonzero : eval rhs (basisVector 1) ≠ 0 := by
  intro h
  have hu := congrArg (fun x => x unitOut) h
  rw [rhs_probe_one] at hu
  exact one_ne_zero hu

private theorem rhs_swap_nonzero : eval rhs (basisVector τ) ≠ 0 := by
  intro h
  have hu := congrArg (fun x => x unitOut) h
  rw [rhs_probe_swap] at hu
  exact one_ne_zero hu

set_option diagnostics true in
theorem endpoint_of_checked_inversion (normal : CaseTwoLeftInversion) :
    CaseTwoReviewedType := by
  unfold CaseTwoReviewedType
  refine ⟨?_, ?_, ?_, ?_, first, mid 1, mid τ, last, overall 1, overall τ,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cup_indices.1
  · exact cup_indices.2
  · exact intersect_calc
  · exact group_obstruction
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact right_sum
  · exact rhs_one_nonzero
  · exact rhs_swap_nonzero
  · intro allowed drawings hd he
    refine allowed_crossings allowed drawings hd ?_
    cases drawings with
    | nil => exact he
    | cons drawing rest => exact he
  · exact two_left_drawings
  · exact no_replacement_of_canonical normal

end CaseTwoAudit

#print axioms CaseTwoAudit.endpoint_of_checked_inversion
