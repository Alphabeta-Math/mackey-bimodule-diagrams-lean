import MackeyDiagrams
import Mathlib.Basic.Complex.Basic

set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem LeanWorkflowCheckedConnection : (∀ {U : Type*} [Group U] (G K H B H' : Subgroup U)
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
  let d := MackeyDiagrams.ConjEmbedding.ofConjugator δ hδ
  let a' := MackeyDiagrams.ConjEmbedding.ofConjugator α' hα'
  let b' := MackeyDiagrams.ConjEmbedding.ofConjugator β' hβ'
  let bottom := MackeyDiagrams.ConjEmbedding.comp a b
  let middle := MackeyDiagrams.ConjEmbedding.comp c d
  let top := MackeyDiagrams.ConjEmbedding.comp a' b'
  let bottomWord := MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up a) (MackeyDiagrams.Word.up b)
  let middleWord := MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up c) (MackeyDiagrams.Word.up d)
  let topWord := MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up a') (MackeyDiagrams.Word.up b')
  let bottomMerge := MackeyDiagrams.Diagram.mergeUp (R := Complex) a b
  let middleMerge := MackeyDiagrams.Diagram.mergeUp (R := Complex) c d
  let middleSplit := MackeyDiagrams.Diagram.splitUp (R := Complex) c d
  let topSplit := MackeyDiagrams.Diagram.splitUp (R := Complex) a' b'
  let lowerCrossing (dot : MackeyDiagrams.Diagram Complex
      (MackeyDiagrams.Word.up bottom) (MackeyDiagrams.Word.up middle)) :=
    MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.vertical bottomMerge dot) middleSplit
  let upperCrossing (dot : MackeyDiagrams.Diagram Complex
      (MackeyDiagrams.Word.up middle) (MackeyDiagrams.Word.up top)) :=
    MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.vertical middleMerge dot) topSplit
  let mergeDotSplit (dot : MackeyDiagrams.Diagram Complex
      (MackeyDiagrams.Word.up bottom) (MackeyDiagrams.Word.up top)) :=
    MackeyDiagrams.Diagram.vertical (MackeyDiagrams.Diagram.vertical bottomMerge dot) topSplit
  let unitCancellation (dot : MackeyDiagrams.Diagram Complex
      (MackeyDiagrams.Word.up bottom) (MackeyDiagrams.Word.up top)) : Prop :=
    ∃ sameLabel : bottom = top,
      let straightStrand := Eq.ndrec (motive := fun label => MackeyDiagrams.Diagram Complex
          (MackeyDiagrams.Word.up bottom) (MackeyDiagrams.Word.up label))
        (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up bottom)) sameLabel
      let dotFree := mergeDotSplit straightStrand
      MackeyDiagrams.Diagram.eval (mergeDotSplit dot) = MackeyDiagrams.Diagram.eval dotFree ∧
      ∀ sameBoundary : bottomWord = topWord,
        let identity := Eq.ndrec
          (motive := fun word => MackeyDiagrams.Diagram Complex bottomWord word)
          (MackeyDiagrams.Diagram.id bottomWord) sameBoundary
        MackeyDiagrams.Diagram.eval dotFree = MackeyDiagrams.Diagram.eval identity
  (∀ (x : MackeyDiagrams.Dot bottom middle) (y : MackeyDiagrams.Dot middle top),
    let productDot := MackeyDiagrams.Diagram.upDot (R := Complex) (MackeyDiagrams.Dot.vertical x y)
    let twoCrossings := MackeyDiagrams.Diagram.vertical
      (lowerCrossing (MackeyDiagrams.Diagram.upDot x)) (upperCrossing (MackeyDiagrams.Diagram.upDot y))
    MackeyDiagrams.Diagram.eval twoCrossings = MackeyDiagrams.Diagram.eval (mergeDotSplit productDot) ∧
    (MackeyDiagrams.Dot.element x * MackeyDiagrams.Dot.element y = 1 → unitCancellation productDot)) ∧
  (∀ (x : Finsupp (MackeyDiagrams.Dot bottom middle) Complex)
      (y : Finsupp (MackeyDiagrams.Dot middle top) Complex),
    let product := Finsupp.sum x (fun p r => Finsupp.sum y (fun q s =>
      Finsupp.single (MackeyDiagrams.Dot.vertical p q) (r * s)))
    let productDot := MackeyDiagrams.Diagram.linearUpDot product
    let twoCrossings := MackeyDiagrams.Diagram.vertical
      (lowerCrossing (MackeyDiagrams.Diagram.linearUpDot x))
      (upperCrossing (MackeyDiagrams.Diagram.linearUpDot y))
    MackeyDiagrams.Diagram.eval twoCrossings = MackeyDiagrams.Diagram.eval (mergeDotSplit productDot) ∧
    (Finsupp.mapDomain (MackeyDiagrams.Dot.element (a := bottom) (b := top)) product =
      Finsupp.single (1 : G) (1 : Complex) → unitCancellation productDot)) ∧
  (∀ x : MackeyDiagrams.Dot bottom middle,
    ∃ y : MackeyDiagrams.Dot middle bottom,
      let forward := lowerCrossing (MackeyDiagrams.Diagram.upDot x)
      let backward := MackeyDiagrams.Diagram.vertical
        (MackeyDiagrams.Diagram.vertical middleMerge (MackeyDiagrams.Diagram.upDot y))
        (MackeyDiagrams.Diagram.splitUp a b)
      MackeyDiagrams.Dot.element y = (MackeyDiagrams.Dot.element x)⁻¹ ∧
      MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.vertical forward backward) =
        MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.id bottomWord) ∧
      MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.vertical backward forward) =
        MackeyDiagrams.Diagram.eval (MackeyDiagrams.Diagram.id middleWord))) :=
(by
  intro U inst G K H B H' α β γ δ α' β' hα hβ hγ hδ hα' hβ'
    a b c d a' b' bottom middle top bottomWord middleWord topWord
    bottomMerge middleMerge middleSplit topSplit lowerCrossing upperCrossing mergeDotSplit unitCancellation
  have cancelUnit (node : MackeyDiagrams.Diagram Complex
        (MackeyDiagrams.Word.up bottom) (MackeyDiagrams.Word.up top))
      (same : bottom = top)
      (he : node.eval = (MackeyDiagrams.Diagram.transportUpId same).eval) :
      unitCancellation node := by
    refine ⟨same, ?_, ?_⟩
    · change (bottomMerge.eval.vertical node.eval).vertical topSplit.eval =
        (bottomMerge.eval.vertical (MackeyDiagrams.Diagram.transportUpId same).eval).vertical topSplit.eval
      rw [he]
    · intro boundary
      exact MackeyDiagrams.Diagram.eval_unitCrossing_sameBoundary a b a' b' same boundary
  have hc : middleSplit.eval.vertical middleMerge.eval =
      MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Word.up middle).basis :=
    MackeyDiagrams.Diagram.splitUp_mergeUp c d
  refine ⟨?_, ?_, ?_⟩
  · intro x y productDot twoCrossings
    refine ⟨MackeyDiagrams.Diagram.parallelUp_comp a b c d a' b' x y, ?_⟩
    intro h
    obtain ⟨same, he⟩ := MackeyDiagrams.Diagram.eval_upDot_unit (R := Complex) (x.vertical y) h
    exact cancelUnit productDot same he
  · intro x y product productDot twoCrossings
    constructor
    · have he : (MackeyDiagrams.Diagram.linearUpDot x).eval.vertical
          (MackeyDiagrams.Diagram.linearUpDot y).eval = productDot.eval :=
        MackeyDiagrams.Diagram.linearUpDot_vertical x y
      exact MackeyDiagrams.Biset.Hom.merge_dot_split_comp
        bottomMerge.eval (MackeyDiagrams.Diagram.linearUpDot x).eval
        middleSplit.eval middleMerge.eval (MackeyDiagrams.Diagram.linearUpDot y).eval
        topSplit.eval productDot.eval hc he
    · intro h
      obtain ⟨same, he⟩ := MackeyDiagrams.Diagram.eval_linearUpDot_unit product h
      exact cancelUnit productDot same he
  · intro x
    refine ⟨x.inverse, rfl, MackeyDiagrams.Diagram.parallelUp_return a b c d x, ?_⟩
    have hx : x.inverse.inverse = x := MackeyDiagrams.Dot.ext (inv_inv x.element)
    have hh := MackeyDiagrams.Diagram.parallelUp_return (R := Complex) c d a b x.inverse
    rw [hx] at hh
    exact hh)
