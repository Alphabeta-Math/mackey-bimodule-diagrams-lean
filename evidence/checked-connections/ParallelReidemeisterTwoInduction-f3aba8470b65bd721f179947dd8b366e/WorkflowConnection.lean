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
    bottomMerge middleMerge middleSplit topSplit lowerCrossing upperCrossing mergeDotSplit
    unitCancellation
  have sameEmbedding {l r : MackeyDiagrams.ConjEmbedding K G}
      (t : MackeyDiagrams.Dot l r) (unit : t.element = 1) : l = r := by
    apply MackeyDiagrams.ConjEmbedding.ext
    apply MonoidHom.ext
    intro k
    simpa only [unit, mul_one, one_mul] using t.intertwines k
  have straightIdentity : ∀ {L L' : Subgroup U}
      (l : MackeyDiagrams.ConjEmbedding L G) (r : MackeyDiagrams.ConjEmbedding K L)
      (l' : MackeyDiagrams.ConjEmbedding L' G) (r' : MackeyDiagrams.ConjEmbedding K L')
      (hw : (MackeyDiagrams.Word.up l).tensor (.up r) = (MackeyDiagrams.Word.up l').tensor (.up r'))
      (he : l.comp r = l'.comp r'),
      (((MackeyDiagrams.Diagram.mergeUp (R := Complex) l r).vertical
        (he ▸ MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up (l.comp r)) :
          MackeyDiagrams.Diagram Complex (MackeyDiagrams.Word.up (l.comp r))
            (MackeyDiagrams.Word.up (l'.comp r')))).vertical
          (MackeyDiagrams.Diagram.splitUp l' r')).eval =
        (show MackeyDiagrams.Diagram Complex ((MackeyDiagrams.Word.up l).tensor (.up r))
          ((MackeyDiagrams.Word.up l').tensor (.up r')) from
            hw ▸ MackeyDiagrams.Diagram.id ((MackeyDiagrams.Word.up l).tensor (.up r))).eval := by
    intro L L' l r l' r' hw he
    injection hw with hG hL hK hl hr
    subst L'
    have hl' : l = l' := by
      have := eq_of_heq hl
      injection this
    have hr' : r = r' := by
      have := eq_of_heq hr
      injection this
    subst l'
    subst r'
    change ((MackeyDiagrams.Diagram.mergeUp (R := Complex) l r).eval.vertical
        (MackeyDiagrams.Biset.Hom.id _)).vertical (MackeyDiagrams.Diagram.splitUp l r).eval =
      (MackeyDiagrams.Diagram.id ((MackeyDiagrams.Word.up l).tensor (.up r))).eval
    rw [MackeyDiagrams.Biset.Hom.vertical_id]
    exact MackeyDiagrams.Diagram.mergeUp_splitUp l r
  have evalUnit (t : MackeyDiagrams.Dot bottom top) (unit : t.element = 1) :
      unitCancellation (MackeyDiagrams.Diagram.upDot t) := by
    let same := sameEmbedding t unit
    refine ⟨same, ?_, ?_⟩
    · have hd : (MackeyDiagrams.Diagram.upDot (R := Complex) t).eval =
          (show MackeyDiagrams.Diagram Complex (MackeyDiagrams.Word.up bottom)
            (MackeyDiagrams.Word.up top) from
              same ▸ MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up bottom)).eval := by
        generalize htop : top = target at t unit same ⊢
        cases same
        have ht : t = MackeyDiagrams.Dot.id bottom := MackeyDiagrams.Dot.ext unit
        rw [ht]
        exact MackeyDiagrams.Diagram.eval_upDot_id bottom
      change (bottomMerge.eval.vertical (MackeyDiagrams.Diagram.upDot t).eval).vertical
          topSplit.eval = _
      rw [hd]
      rfl
    · intro hw
      exact straightIdentity a b a' b' hw same
  have hc : middleSplit.eval.vertical middleMerge.eval =
      MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Word.up middle).basis :=
    MackeyDiagrams.Diagram.splitUp_mergeUp c d
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    exact ⟨MackeyDiagrams.Diagram.parallelUp_comp a b c d a' b' x y,
      evalUnit (x.vertical y)⟩
  · intro x y product productDot twoCrossings
    constructor
    · exact MackeyDiagrams.Biset.Hom.merge_dot_split_comp
        bottomMerge.eval (MackeyDiagrams.Diagram.linearUpDot x).eval
        middleSplit.eval middleMerge.eval (MackeyDiagrams.Diagram.linearUpDot y).eval
        topSplit.eval productDot.eval hc (MackeyDiagrams.Diagram.linearUpDot_vertical x y)
    · intro unit
      let element := MackeyDiagrams.Dot.element (a := bottom) (b := top)
      have nonzero : Finsupp.mapDomain element product 1 ≠ 0 := by
        rw [unit, Finsupp.single_eq_same]
        exact one_ne_zero
      obtain ⟨t, ht⟩ := Finsupp.mem_range_of_mapDomain_ne_zero nonzero
      have single : product = Finsupp.single t 1 := by
        apply Finsupp.mapDomain_injective (f := element) (fun _ _ => MackeyDiagrams.Dot.ext)
        rw [unit, Finsupp.mapDomain_single, ht]
      have heval : productDot.eval = (MackeyDiagrams.Diagram.upDot (R := Complex) t).eval := by
        apply MackeyDiagrams.Diagram.eval_ext
        intro z r
        change (MackeyDiagrams.Diagram.linearUpDot product).eval.toLinearMap (Finsupp.single z r) = _
        rw [single, MackeyDiagrams.Diagram.eval_linearUpDot_apply, MackeyDiagrams.freeLift_single, one_smul]
      obtain ⟨same, hdots, hidentity⟩ := evalUnit t ht
      refine ⟨same, ?_, hidentity⟩
      change (bottomMerge.eval.vertical productDot.eval).vertical topSplit.eval = _
      rw [heval]
      exact hdots
  · intro x
    have inverseInverse : x.inverse.inverse = x := by
      apply MackeyDiagrams.Dot.ext
      exact inv_inv x.element
    refine ⟨x.inverse, rfl, MackeyDiagrams.Diagram.parallelUp_return a b c d x, ?_⟩
    change ((MackeyDiagrams.Diagram.parallelUp c d a b x.inverse).vertical
      (MackeyDiagrams.Diagram.parallelUp a b c d x)).eval = _
    simpa only [inverseInverse] using MackeyDiagrams.Diagram.parallelUp_return c d a b x.inverse)
