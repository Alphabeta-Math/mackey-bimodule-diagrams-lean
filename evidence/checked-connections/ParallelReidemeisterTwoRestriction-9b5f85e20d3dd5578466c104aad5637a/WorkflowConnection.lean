import MackeyDiagrams
import Mathlib.Basic.Complex.Basic

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem LeanWorkflowCheckedConnection : (∀ {U : Type*} [Group U] (K H B H' G : Subgroup U)
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
  let bottomMerge := MackeyDiagrams.Diagram.mergeDown (R := Complex) a b
  let middleSplit := MackeyDiagrams.Diagram.splitDown (R := Complex) c f
  let middleMerge := MackeyDiagrams.Diagram.mergeDown (R := Complex) c f
  let topSplit := MackeyDiagrams.Diagram.splitDown (R := Complex) a' b'
  let lowerCrossing := fun node : MackeyDiagrams.Diagram Complex
      (MackeyDiagrams.Word.down u) (MackeyDiagrams.Word.down v) =>
    MackeyDiagrams.Diagram.vertical bottomMerge
      (MackeyDiagrams.Diagram.vertical node middleSplit)
  let upperCrossing := fun node : MackeyDiagrams.Diagram Complex
      (MackeyDiagrams.Word.down v) (MackeyDiagrams.Word.down w) =>
    MackeyDiagrams.Diagram.vertical middleMerge
      (MackeyDiagrams.Diagram.vertical node topSplit)
  let mergedCrossing := fun node : MackeyDiagrams.Diagram Complex
      (MackeyDiagrams.Word.down u) (MackeyDiagrams.Word.down w) =>
    MackeyDiagrams.Diagram.vertical bottomMerge
      (MackeyDiagrams.Diagram.vertical node topSplit)
  (∀ (d : MackeyDiagrams.Dot u v) (e : MackeyDiagrams.Dot v w),
    let dNode := MackeyDiagrams.Diagram.downDot (R := Complex) d
    let eNode := MackeyDiagrams.Diagram.downDot (R := Complex) e
    let productNode := MackeyDiagrams.Diagram.downDot (R := Complex) (MackeyDiagrams.Dot.vertical d e)
    MackeyDiagrams.Diagram.eval
        (MackeyDiagrams.Diagram.vertical (lowerCrossing dNode) (upperCrossing eNode)) =
      MackeyDiagrams.Diagram.eval (mergedCrossing productNode) ∧
    (∀ x : MonoidAlgebra Complex G,
      let first := MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval dNode)
        (MonoidAlgebra.coeff x)
      let second := MackeyDiagrams.Biset.Hom.toLinearMap (MackeyDiagrams.Diagram.eval eNode) first
      let dInv : MonoidAlgebra Complex G := MonoidAlgebra.single (MackeyDiagrams.Dot.element d)⁻¹ 1
      let eInv : MonoidAlgebra Complex G := MonoidAlgebra.single (MackeyDiagrams.Dot.element e)⁻¹ 1
      first = MonoidAlgebra.coeff (dInv * x) ∧
      second = MonoidAlgebra.coeff (eInv * (dInv * x)) ∧
      second = MonoidAlgebra.coeff
        (MonoidAlgebra.single ((MackeyDiagrams.Dot.element d) * (MackeyDiagrams.Dot.element e))⁻¹ 1 * x))) ∧
  (∀ (D : MackeyDiagrams.Dot u v →₀ Complex) (E : MackeyDiagrams.Dot v w →₀ Complex),
    let product : MackeyDiagrams.Dot u w →₀ Complex :=
      Finsupp.sum D (fun d rd =>
        Finsupp.sum E (fun e re => Finsupp.single (MackeyDiagrams.Dot.vertical d e) (rd * re)))
    MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.vertical
        (lowerCrossing (MackeyDiagrams.Diagram.linearDownDot D))
        (upperCrossing (MackeyDiagrams.Diagram.linearDownDot E))) =
      MackeyDiagrams.Diagram.eval (mergedCrossing (MackeyDiagrams.Diagram.linearDownDot product)))) :=
(by
  intro U inst K H B H' G α β γ δ α' β' hα hβ hγ hδ hα' hβ' a b c f a' b' u v w
    bottomMerge middleSplit middleMerge topSplit lowerCrossing upperCrossing mergedCrossing
  have hc : middleSplit.eval.vertical middleMerge.eval =
      MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Word.down v).basis :=
    MackeyDiagrams.Diagram.splitDown_mergeDown c f
  constructor
  · intro d e dNode eNode productNode
    constructor
    · have hdots : dNode.eval.vertical eNode.eval = productNode.eval :=
        MackeyDiagrams.Diagram.downDot_vertical d e
      change (bottomMerge.eval.vertical (dNode.eval.vertical middleSplit.eval)).vertical
          (middleMerge.eval.vertical (eNode.eval.vertical topSplit.eval)) =
        bottomMerge.eval.vertical (productNode.eval.vertical topSplit.eval)
      simpa only [MackeyDiagrams.Biset.Hom.vertical_assoc] using
        MackeyDiagrams.Biset.Hom.merge_dot_split_comp
          bottomMerge.eval dNode.eval middleSplit.eval middleMerge.eval eNode.eval topSplit.eval
          productNode.eval hc hdots
    · intro x first second dInv eInv
      have h₁ : first = (dInv * x).coeff :=
        MackeyDiagrams.Diagram.eval_downDot_groupAlgebra d x
      have h₂ : second = (eInv * (dInv * x)).coeff := by
        change eNode.eval.toLinearMap first = _
        rw [h₁]
        exact MackeyDiagrams.Diagram.eval_downDot_groupAlgebra e (dInv * x)
      refine ⟨h₁, h₂, ?_⟩
      rw [h₂, ← mul_assoc]
      change (MonoidAlgebra.single e.element⁻¹ (1 : Complex) *
        MonoidAlgebra.single d.element⁻¹ 1 * x).coeff = _
      rw [MonoidAlgebra.single_mul_single, one_mul, mul_inv_rev]
  · intro D E product
    have hdots : (MackeyDiagrams.Diagram.linearDownDot D).eval.vertical
        (MackeyDiagrams.Diagram.linearDownDot E).eval =
        (MackeyDiagrams.Diagram.linearDownDot product).eval :=
      MackeyDiagrams.Diagram.linearDownDot_vertical D E
    change (bottomMerge.eval.vertical ((MackeyDiagrams.Diagram.linearDownDot D).eval.vertical
        middleSplit.eval)).vertical
      (middleMerge.eval.vertical ((MackeyDiagrams.Diagram.linearDownDot E).eval.vertical
        topSplit.eval)) =
      bottomMerge.eval.vertical ((MackeyDiagrams.Diagram.linearDownDot product).eval.vertical
        topSplit.eval)
    simpa only [MackeyDiagrams.Biset.Hom.vertical_assoc] using
      MackeyDiagrams.Biset.Hom.merge_dot_split_comp
        bottomMerge.eval (MackeyDiagrams.Diagram.linearDownDot D).eval
        middleSplit.eval middleMerge.eval (MackeyDiagrams.Diagram.linearDownDot E).eval
        topSplit.eval (MackeyDiagrams.Diagram.linearDownDot product).eval hc hdots)
