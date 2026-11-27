import Drawing
import Concrete

namespace CaseFiveInfiniteAux
open MackeyDiagrams PlanarCode

theorem right_named_support (lower : Lower) (middle : Middle) (upper : Upper) (g x : P)
    (hx : x ∉ Finset.image Dot.element (Finsupp.support lower)) :
    eval (LabelledDrawing.PlanarAtBoundary.diagram (rightAt lower middle upper)) (input g x) = 0 := by
  classical
  let ss := List.map (fun (t : Complex × Dot (comp a i) (comp a i)) =>
      (t.1, (⟨t.2, rightFinite t.2⟩ : ProjectionDot.Mixed a a i i))) (DotLabel.terms lower)
  let prj := (LabelledDrawing.compactProjection (R := Complex) a a i i ss).interpret.eval
  let xx : Raw (tensor ad df) := (x,1)
  have hz : prj.toLinearMap (basisVector (tensor ad df) xx) = 0 := by
    apply projections_zero a a i i ss xx (x : U)
    · exact ⟨P,P,(x : U),1,rfl,rfl,mul_one _⟩
    · intro t ht he
      obtain ⟨term, hterm, rfl⟩ := List.mem_map.mp ht
      obtain ⟨d, hd, hd'⟩ := List.mem_map.mp hterm
      apply hx
      refine Finset.mem_image.mpr ⟨d, by simpa using hd, ?_⟩
      apply Subtype.ext
      exact (congrArg (fun u : Complex × Dot (comp a i) (comp a i) => u.2.element.val) hd').trans he.symm
  suffices h : ((Diagram.id (R := Complex) ga).eval.horizontal prj).toLinearMap (input g x) = 0 by
    let second := LabelledDrawing.parallelUp a i p a (DotLabel.terms middle)
    let third := LabelledDrawing.mixedMultiplication p a a i (DotLabel.terms upper)
    let tail := stack (plain (Diagram.unassociate ga ai fj))
      (stack (beside second (drawId fj))
        (stack (plain (Diagram.associate gc ck fj)) (beside (drawId gc) third)))
    change tail.interpret.eval.toLinearMap (((Diagram.id (R := Complex) ga).eval.horizontal prj).toLinearMap
      (input g x)) = 0
    rw [h, map_zero]
  change ((Diagram.id (R := Complex) ga).eval.horizontal prj).toLinearMap
    (basisVector bottom (g,xx)) = 0
  rw [basis_horizontal, hz, map_zero]

theorem fixed_right_code (d : RightDrawing) : (geoInfo d.diagram.erase).events = rightCode := by
  have hs := congrArg PlanarShape.wiring d.shape_eq
  change Quotient.mk PlanarCode.setoid (geoInfo d.diagram.erase).events =
    Quotient.mk PlanarCode.setoid rightCode at hs
  exact (rigid_eq (Quotient.exact hs)).2 rigid_rightCode

-- The shape fiber in the statement is wider than the explicit family in
-- ExpansionIntoRightDiagrams. Its finite-orbit iff applies only to that
-- family. Rigidity and the support induction retain arbitrary typed syntax.
theorem right_all_support (d : RightDrawing) :
    ∃ S : Finset P, ∀ g x : P, x ∉ S → evalAt (interpretRight d) (input g x) = 0 := by
  classical
  have h := support_atBoundary d
  rw [fixed_right_code d] at h
  have he := support_seq (.structural (preserve_reorder_to bottom))
    (support_seq h (.structural (preserve_reorder_from top)))
  change SupportRule
    (Biset.Hom.vertical (Word.reorderToBoundary (R := Complex) bottom).eval
      ((interpretRight d).eval.vertical (Word.reorderFromBoundary (R := Complex) top).eval))
    rightCode at he
  obtain ⟨_, S, hS⟩ := he.2 1 rfl
  let lift : U → P := fun u => ⟨u, Subgroup.mem_top u⟩
  refine ⟨S.image lift, ?_⟩
  intro g x hx
  let inp : Raw bottom := (g,x,1)
  have hx' : (x : U) ∉ S := fun hh =>
    hx (Finset.mem_image.mpr ⟨x.val, hh, Subtype.ext rfl⟩)
  have hp : Selected (slots bottom inp) 1 (x : U) :=
    ⟨P,P,(x : U),1,rfl,rfl,mul_one _⟩
  exact hS inp (x : U) hp hx'

theorem evalAt_sum (terms : List (Complex × RightDrawing)) (v : X.carrier →₀ Complex) :
    evalAt (rightSum terms) v = (terms.map (fun t => t.1 • evalAt (interpretRight t.2) v)).sum := by
  let start := (Word.reorderToBoundary (R := Complex) bottom).eval.toLinearMap
  let finish := (Word.reorderFromBoundary (R := Complex) top).eval.toLinearMap
  induction terms with
  | nil =>
    change finish 0 = 0
    exact map_zero finish
  | cons t ts ih =>
    have split : rightSum (t::ts) = .add (.scale t.1 (interpretRight t.2)) (rightSum ts) := rfl
    rw [split, List.map_cons, List.sum_cons, ← ih]
    change finish (t.1 • (interpretRight t.2).eval.toLinearMap (start v) +
      (rightSum ts).eval.toLinearMap (start v)) =
      t.1 • finish ((interpretRight t.2).eval.toLinearMap (start v)) +
        finish ((rightSum ts).eval.toLinearMap (start v))
    rw [map_add, map_smul]

theorem finite_right_sum (terms : List (Complex × RightDrawing)) :
    (∃ S : Finset P, ∀ g x : P, x ∉ S → evalAt (rightSum terms) (input g x) = 0) ∧
    evalAt (rightSum terms) ≠ eval left := by
  classical
  have support : ∃ S : Finset P, ∀ g x : P, x ∉ S → evalAt (rightSum terms) (input g x) = 0 := by
    induction terms with
    | nil => exact ⟨∅, fun _ _ _ => by rw [evalAt_sum]; rfl⟩
    | cons t ts ih =>
      obtain ⟨S, hs⟩ := right_all_support t.2
      obtain ⟨T, ht⟩ := ih
      refine ⟨S ∪ T, ?_⟩
      intro g x hx
      have hS : x ∉ S := fun h => hx (Finset.mem_union.mpr (Or.inl h))
      have hT : x ∉ T := fun h => hx (Finset.mem_union.mpr (Or.inr h))
      rw [evalAt_sum, List.map_cons, List.sum_cons, ← evalAt_sum, hs g x hS, ht g x hT, smul_zero, add_zero]
  refine ⟨support, ?_⟩
  intro he
  obtain ⟨S, hS⟩ := support
  have : Infinite U := by
    change Infinite Int
    infer_instance
  have : Infinite P := Infinite.of_injective (fun u : U => (⟨u,Subgroup.mem_top u⟩ : P))
    (fun _ _ h => congrArg Subtype.val h)
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset S
  have hz := hS 1 x hx
  rw [he, left_column, one_mul] at hz
  exact Finsupp.single_ne_zero.mpr one_ne_zero hz

theorem pointwise_finiteness (v : X.carrier →₀ Complex) :
    Set.Finite {r : P | eval (rightTerm r) v ≠ 0} := by
  induction v using Finsupp.induction_linear with
  | zero => simpa only [map_zero, ne_eq, not_true_eq_false, Set.ofPred_false] using
      (Set.finite_empty : (∅ : Set P).Finite)
  | add v w hv hw =>
    refine (hv.union hw).subset ?_
    intro r hr
    change eval (rightTerm r) (v+w) ≠ 0 at hr
    rw [map_add] at hr
    by_cases h : eval (rightTerm r) v = 0
    · exact Or.inr (fun hw => hr (by rw [h, hw, add_zero]))
    · exact Or.inl h
  | single v c =>
    obtain ⟨g,x,rfl⟩ := input_surj v
    refine (Set.finite_singleton x).subset ?_
    intro r hr
    change eval (rightTerm r) (Finsupp.single (inputPair g x) c) ≠ 0 at hr
    rw [← Finsupp.smul_single_one, map_smul] at hr
    change c • eval (rightTerm r) (input g x) ≠ 0 at hr
    rw [right_column] at hr
    by_contra h
    have hx : x ≠ r := fun he => h (Set.mem_singleton_iff.mpr he.symm)
    exact hr (by rw [ite_eq_right hx, smul_zero])

-- Use the full cyclic index in the single indexed drawing. On a basis column
-- all terms away from the named index are zero. The checked linear evaluation
-- of PointwiseIndexedDrawing extends this calculation to every input.
theorem pointwise_column_sum :
    ∃ finite : ∀ v : X.carrier →₀ Complex,
      Set.Finite {x : P | eval (rightTerm x) v ≠ 0},
    let drawing : PointwiseIndexedDrawing Complex bottom top P := ⟨rightTerm, finite⟩
    ∀ v : X.carrier →₀ Complex, eval left v = drawing.evalAt v := by
  classical
  refine ⟨pointwise_finiteness, ?_⟩
  let drawing : PointwiseIndexedDrawing Complex bottom top P := ⟨rightTerm, pointwise_finiteness⟩
  change ∀ v : X.carrier →₀ Complex, eval left v = drawing.evalAt v
  suffices h : eval left = drawing.eval by
    intro v
    exact (LinearMap.congr_fun h v).trans (drawing.eval_apply v)
  apply Finsupp.lhom_ext
  intro v c
  rw [← Finsupp.smul_single_one, map_smul, map_smul]
  congr 1
  obtain ⟨g,x,rfl⟩ := input_surj v
  change eval left (input g x) = drawing.eval (input g x)
  rw [left_column, PointwiseIndexedDrawing.eval_apply, PointwiseIndexedDrawing.evalAt_def]
  let indices := (pointwise_finiteness (input g x)).toFinset
  change output (g*x) = ∑ r ∈ indices, eval (rightTerm r) (input g x)
  rw [Finset.sum_eq_single x]
  · rw [right_column, ite_eq_left rfl]
  · intro r _ hr
    rw [right_column, ite_eq_right (Ne.symm hr)]
  · intro hn
    have hz : eval (rightTerm x) (input g x) = 0 := by
      by_contra h
      exact hn ((Set.Finite.mem_toFinset _).2 h)
    rw [right_column, ite_eq_left rfl] at hz
    exact False.elim (Finsupp.single_ne_zero.mpr one_ne_zero hz)

end CaseFiveInfiniteAux
