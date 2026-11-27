import MackeyDiagrams
import Proofs.GroupElementDotCriterion
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 2000000

namespace MackeyDiagrams

private theorem parallelRIIRestriction_evalCrossing {U : Type*} [Group U]
    {K H H' G : Subgroup U} {R : Type*} [CommSemiring R]
    (a : ConjEmbedding H G) (b : ConjEmbedding K H)
    (a' : ConjEmbedding H' G) (b' : ConjEmbedding K H')
    (label : DotLabel R (a.comp b) (a'.comp b')) :
    (LabelledDrawing.parallelDown a b a' b' label.terms).interpret.eval =
      (Diagram.mergeDown (R := R) a b).eval.vertical
        (label.downDrawing.interpret.eval.vertical (Diagram.splitDown a' b').eval) := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  change (ScopedDiagram.linearCombination (label.terms.map fun (r, d) =>
      (r, ScopedDiagram.ordinary (Diagram.parallelDown a b a' b' d)))).eval.toLinearMap x =
    (Diagram.splitDown (R := R) a' b').eval.toLinearMap
      ((Diagram.finiteSum (label.terms.map fun (r, d) =>
        Diagram.scale r (Diagram.downDot d))).eval.toLinearMap
          ((Diagram.mergeDown (R := R) a b).eval.toLinearMap x))
  rw [ScopedDiagram.eval_linearCombination_apply, Diagram.eval_finiteSum]
  generalize label.terms = terms
  induction terms with
  | nil => simp
  | cons term terms ih =>
    rcases term with ⟨r, d⟩
    simp only [List.map_cons, List.sum_cons, map_add, ih]
    congr 1
    change r • (Diagram.splitDown (R := R) a' b').eval.toLinearMap
      ((Diagram.downDot d).eval.toLinearMap ((Diagram.mergeDown a b).eval.toLinearMap x)) =
      (Diagram.splitDown (R := R) a' b').eval.toLinearMap
        (r • (Diagram.downDot d).eval.toLinearMap ((Diagram.mergeDown a b).eval.toLinearMap x))
    rw [map_smul]

private theorem parallelRIIRestriction_evalSingleton {U : Type*} [Group U]
    {K G : Subgroup U} {p q : ConjEmbedding K G} (d : Dot p q) :
    (DotLabel.downDrawing (Finsupp.single d (1 : Complex))).interpret.eval =
      (Diagram.downDot (R := Complex) d).eval := by
  rw [DotLabel.eval_downDrawing]
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro x
  exact (Diagram.eval_linearDownDot_apply (Finsupp.single d (1 : Complex)) x).trans (by
    rw [freeLift_single, one_smul])

end MackeyDiagrams

theorem ParallelReidemeisterTwoRestriction : (
∀ {U : Type*} [Group U] (K H B H' G : Subgroup U)
    (α β γ δ α' β' : U)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G)
    (hβ : ∀ k : K, β * (k : U) * β⁻¹ ∈ H)
    (hγ : ∀ b : B, γ * (b : U) * γ⁻¹ ∈ G)
    (hδ : ∀ k : K, δ * (k : U) * δ⁻¹ ∈ B)
    (hα' : ∀ h : H', α' * (h : U) * (α')⁻¹ ∈ G)
    (hβ' : ∀ k : K, β' * (k : U) * (β')⁻¹ ∈ H'),
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  let c := MackeyDiagrams.ConjEmbedding.ofConjugator γ hγ
  let f := MackeyDiagrams.ConjEmbedding.ofConjugator δ hδ
  let a' := MackeyDiagrams.ConjEmbedding.ofConjugator α' hα'
  let b' := MackeyDiagrams.ConjEmbedding.ofConjugator β' hβ'
  let u := MackeyDiagrams.ConjEmbedding.comp a b
  let v := MackeyDiagrams.ConjEmbedding.comp c f
  let w := MackeyDiagrams.ConjEmbedding.comp a' b'
  let evalDrawing {p q : MackeyDiagrams.Word K G}
      (drawing : MackeyDiagrams.LabelledDrawing Complex p q) :=
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
  let singleton {p q : MackeyDiagrams.ConjEmbedding K G} (d : MackeyDiagrams.Dot p q) :
      MackeyDiagrams.DotLabel Complex p q :=
    Finsupp.single d 1
  let twoCrossings (D : MackeyDiagrams.DotLabel Complex u v)
      (E : MackeyDiagrams.DotLabel Complex v w) :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.parallelDown a b c f (MackeyDiagrams.DotLabel.terms D))
      (MackeyDiagrams.LabelledDrawing.parallelDown c f a' b' (MackeyDiagrams.DotLabel.terms E))
  let mergeDotSplit (label : MackeyDiagrams.DotLabel Complex u w) :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
        (MackeyDiagrams.TrivalentVertex.mergeDown a b))
      (MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.DotLabel.downDrawing label)
        (MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
          (MackeyDiagrams.TrivalentVertex.splitDown a' b')))
  (∀ (d : MackeyDiagrams.Dot u v) (e : MackeyDiagrams.Dot v w),
    let dNode := MackeyDiagrams.DotLabel.downDrawing (singleton d)
    let eNode := MackeyDiagrams.DotLabel.downDrawing (singleton e)
    let product := singleton (MackeyDiagrams.Dot.vertical d e)
    evalDrawing (twoCrossings (singleton d) (singleton e)) = evalDrawing (mergeDotSplit product) ∧
    (∀ x : MonoidAlgebra Complex G,
      let first := MackeyDiagrams.Biset.Hom.toLinearMap (evalDrawing dNode) (MonoidAlgebra.coeff x)
      let second := MackeyDiagrams.Biset.Hom.toLinearMap (evalDrawing eNode) first
      let dInv : MonoidAlgebra Complex G := MonoidAlgebra.single (MackeyDiagrams.Dot.element d)⁻¹ 1
      let eInv : MonoidAlgebra Complex G := MonoidAlgebra.single (MackeyDiagrams.Dot.element e)⁻¹ 1
      first = MonoidAlgebra.coeff (dInv * x) ∧
      second = MonoidAlgebra.coeff (eInv * (dInv * x)) ∧
      second = MonoidAlgebra.coeff
        (MonoidAlgebra.single ((MackeyDiagrams.Dot.element d) * (MackeyDiagrams.Dot.element e))⁻¹ 1 * x))) ∧
  (∀ (D : MackeyDiagrams.DotLabel Complex u v) (E : MackeyDiagrams.DotLabel Complex v w),
    evalDrawing (twoCrossings D E) =
      evalDrawing (mergeDotSplit (MackeyDiagrams.DotLabel.compose D E)))
) :=
(by
  intro U inst K H B H' G α β γ δ α' β' hα hβ hγ hδ hα' hβ' a b c f a' b' u v w
    evalDrawing singleton twoCrossings mergeDotSplit
  -- Xiao, § 5.2, gives this restriction case immediately after Theorem 5.4's proof.
  -- The archived original has it on p. 18. The revised published PDF has it on p. 20.
  -- The two PDF files have different hashes. Their restriction paragraphs agree.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- No numbered Alphabeta Math proof is supplied for this endpoint. The steps below
  -- follow Xiao's calculation.
  -- Step 1: expand the two marked crossings at their typed boundaries. The drawing
  -- evaluator sums whole crossings, so first pass the fixed split through the finite sum.
  -- Step 2: cancel the split and merge on the middle chain through B, then compose
  -- the eligible finite labels termwise in stacking order. The middle cancellation
  -- specializes splitDown_mergeDown to c and f. Each ordered product in
  -- downDrawing_compose uses Dot.vertical at the shared embedding v.
  have merged (D : MackeyDiagrams.DotLabel Complex u v)
      (E : MackeyDiagrams.DotLabel Complex v w) :
      evalDrawing (twoCrossings D E) =
        evalDrawing (mergeDotSplit (MackeyDiagrams.DotLabel.compose D E)) := by
    let lower := (MackeyDiagrams.DotLabel.downDrawing D).interpret.eval
    let upper := (MackeyDiagrams.DotLabel.downDrawing E).interpret.eval
    let product := (MackeyDiagrams.DotLabel.downDrawing
      (MackeyDiagrams.DotLabel.compose D E)).interpret.eval
    let bottomMerge := (MackeyDiagrams.Diagram.mergeDown (R := Complex) a b).eval
    let middleSplit := (MackeyDiagrams.Diagram.splitDown (R := Complex) c f).eval
    let middleMerge := (MackeyDiagrams.Diagram.mergeDown (R := Complex) c f).eval
    let topSplit := (MackeyDiagrams.Diagram.splitDown (R := Complex) a' b').eval
    change ((MackeyDiagrams.LabelledDrawing.parallelDown a b c f
      (MackeyDiagrams.DotLabel.terms D)).interpret.eval).vertical
      (MackeyDiagrams.LabelledDrawing.parallelDown c f a' b'
        (MackeyDiagrams.DotLabel.terms E)).interpret.eval =
      bottomMerge.vertical (product.vertical topSplit)
    rw [MackeyDiagrams.parallelRIIRestriction_evalCrossing,
      MackeyDiagrams.parallelRIIRestriction_evalCrossing]
    have middle : middleSplit.vertical middleMerge =
        MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Word.down v).basis :=
      MackeyDiagrams.Diagram.splitDown_mergeDown c f
    have dots : lower.vertical upper = product :=
      MackeyDiagrams.DotLabel.downDrawing_compose D E
    simpa only [MackeyDiagrams.Biset.Hom.vertical_assoc] using
      MackeyDiagrams.Biset.Hom.merge_dot_split_comp
        bottomMerge lower middleSplit middleMerge upper topSplit product middle dots
  refine ⟨?_, merged⟩
  intro d e dNode eNode product
  constructor
  · have product_eq : MackeyDiagrams.DotLabel.compose (singleton d) (singleton e) =
        product := by
      change MackeyDiagrams.Dot.linearProduct (Finsupp.single d (1 : Complex))
        (Finsupp.single e 1) = Finsupp.single (d.vertical e) 1
      simp [MackeyDiagrams.Dot.linearProduct, Finsupp.sum_single_index]
    simpa only [product_eq] using merged (singleton d) (singleton e)
  -- Step 3: transport the inverse left multiplication calculation from the historical
  -- Diagram connection to the marked singleton drawings. The root build has changed
  -- since that receipt. The singleton adapter checks the connection in the current
  -- imports, using eval_downDot_groupAlgebra directly. The law (de)⁻¹ = e⁻¹d⁻¹
  -- supplies the stacking order.
  · intro x first second dInv eInv
    have hd : evalDrawing dNode = (MackeyDiagrams.Diagram.downDot (R := Complex) d).eval :=
      MackeyDiagrams.parallelRIIRestriction_evalSingleton d
    have he : evalDrawing eNode = (MackeyDiagrams.Diagram.downDot (R := Complex) e).eval :=
      MackeyDiagrams.parallelRIIRestriction_evalSingleton e
    have h₁ : first = (dInv * x).coeff := by
      change (evalDrawing dNode).toLinearMap x.coeff = _
      rw [hd]
      exact MackeyDiagrams.Diagram.eval_downDot_groupAlgebra d x
    have h₂ : second = (eInv * (dInv * x)).coeff := by
      change (evalDrawing eNode).toLinearMap first = _
      rw [he, h₁]
      exact MackeyDiagrams.Diagram.eval_downDot_groupAlgebra e (dInv * x)
    refine ⟨h₁, h₂, ?_⟩
    rw [h₂, ← mul_assoc]
    change (MonoidAlgebra.single e.element⁻¹ (1 : Complex) *
      MonoidAlgebra.single d.element⁻¹ 1 * x).coeff = _
    rw [MonoidAlgebra.single_mul_single, one_mul, mul_inv_rev])
