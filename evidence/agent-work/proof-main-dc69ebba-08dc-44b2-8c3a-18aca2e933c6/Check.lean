import MackeyDiagrams
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.ParallelInductionProductDotAdmissibility

set_option maxHeartbeats 2000000

namespace ParallelReidemeisterTwoInductionProof

open MackeyDiagrams

variable {U : Type*} [Group U] {G K H B : Subgroup U}
variable {R : Type*} [CommSemiring R]

-- The crossing constructor interprets a sum of complete crossings. Move the
-- fixed merge and split through that sum at the level of linear maps.
private theorem eval_parallelUp_terms
    (a : ConjEmbedding H G) (b : ConjEmbedding K H)
    (c : ConjEmbedding B G) (d : ConjEmbedding K B)
    (terms : List (R × Dot (a.comp b) (c.comp d))) :
    (LabelledDrawing.parallelUp a b c d terms).interpret.eval =
      ((Diagram.mergeUp (R := R) a b).eval.vertical
        (LabelledDrawing.upDot terms).interpret.eval).vertical (Diagram.splitUp c d).eval := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  change (ScopedDiagram.linearCombination
      (terms.map fun (r, t) => (r, ScopedDiagram.ordinary (Diagram.parallelUp a b c d t)))).eval.toLinearMap z =
    (Diagram.splitUp c d).eval.toLinearMap
      ((Diagram.finiteSum (terms.map fun (r,t) => Diagram.scale r (Diagram.upDot t))).eval.toLinearMap
        ((Diagram.mergeUp a b).eval.toLinearMap z))
  rw [ScopedDiagram.eval_linearCombination_apply, Diagram.eval_finiteSum]
  induction terms with
  | nil => simp
  | cons term rest ih =>
    rcases term with ⟨r, t⟩
    simp only [List.map_cons, List.sum_cons, map_add]
    have scaled :
        (Diagram.scale r (Diagram.upDot t)).eval.toLinearMap
            ((Diagram.mergeUp a b).eval.toLinearMap z) =
          r • (Diagram.upDot (R := R) t).eval.toLinearMap
            ((Diagram.mergeUp a b).eval.toLinearMap z) := rfl
    rw [ih, scaled, map_smul]
    rfl

private theorem eval_parallelUp_single [Nontrivial R]
    (a : ConjEmbedding H G) (b : ConjEmbedding K H)
    (c : ConjEmbedding B G) (d : ConjEmbedding K B)
    (t : Dot (a.comp b) (c.comp d)) :
    (LabelledDrawing.parallelUp a b c d
        (DotLabel.terms (Finsupp.single t (1 : R)))).interpret.eval =
      (Diagram.parallelUp a b c d t (R := R)).eval := by
  classical
  have h : DotLabel.terms (Finsupp.single t (1 : R)) =
      (Finsupp.single t (1 : R)).support.toList.map
        (fun p => ((Finsupp.single t (1 : R)) p, p)) := rfl
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  change (ScopedDiagram.linearCombination
      ((DotLabel.terms (Finsupp.single t (1 : R))).map
        fun (r, p) => (r, ScopedDiagram.ordinary (Diagram.parallelUp a b c d p)))).eval.toLinearMap z = _
  rw [ScopedDiagram.eval_linearCombination_apply, h, Finsupp.support_single _ one_ne_zero]
  simp [ScopedDiagram.eval]

private theorem compose_singletons
    {a b c : ConjEmbedding K G} (x : Dot a b) (y : Dot b c) :
    DotLabel.compose (Finsupp.single x (1 : R)) (Finsupp.single y 1) =
      Finsupp.single (x.vertical y) 1 := by
  unfold DotLabel.compose Dot.linearProduct
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index]
  · rw [mul_one]
  · simp
  · simp

private theorem eval_transported_up_id {a b : ConjEmbedding K G} (same : a = b) :
    (LabelledDrawing.interpret
      (Eq.ndrec (motive := fun e => LabelledDrawing R (.up a) (.up e))
        (.ordinary (Diagram.id (.up a))) same)).eval = (Diagram.transportUpId same).eval := by
  cases same
  rfl

private theorem eval_transported_word_id {p q : Word G K} (same : p = q) :
    (LabelledDrawing.interpret
      (Eq.ndrec (motive := fun w => LabelledDrawing R p w)
        (.ordinary (Diagram.id p)) same)).eval =
    (Eq.ndrec (motive := fun w => Diagram R p w) (Diagram.id p) same).eval := by
  cases same
  rfl

end ParallelReidemeisterTwoInductionProof

open MackeyDiagrams ParallelReidemeisterTwoInductionProof

theorem ParallelReidemeisterTwoInduction : (∀ {U : Type*} [Group U] (G K H B H' : Subgroup U)
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
  let evalDrawing {p q : MackeyDiagrams.Word G K}
      (drawing : MackeyDiagrams.LabelledDrawing Complex p q) :=
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
  let singleton {p q : MackeyDiagrams.ConjEmbedding K G} (dot : MackeyDiagrams.Dot p q) :
      MackeyDiagrams.DotLabel Complex p q :=
    Finsupp.single dot (1 : Complex)
  let lowerCrossing (label : MackeyDiagrams.DotLabel Complex bottom middle) :=
    MackeyDiagrams.LabelledDrawing.parallelUp a b c d (MackeyDiagrams.DotLabel.terms label)
  let upperCrossing (label : MackeyDiagrams.DotLabel Complex middle top) :=
    MackeyDiagrams.LabelledDrawing.parallelUp c d a' b' (MackeyDiagrams.DotLabel.terms label)
  let bottomMerge :=
    MackeyDiagrams.LabelledDrawing.trivalent (R := Complex) (MackeyDiagrams.TrivalentVertex.mergeUp a b)
  let topSplit :=
    MackeyDiagrams.LabelledDrawing.trivalent (R := Complex) (MackeyDiagrams.TrivalentVertex.splitUp a' b')
  let mergeSplit (strand : MackeyDiagrams.LabelledDrawing Complex
      (MackeyDiagrams.Word.up bottom) (MackeyDiagrams.Word.up top)) :=
    MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.vertical bottomMerge strand) topSplit
  let unitCancellation (product : MackeyDiagrams.DotLabel Complex bottom top) : Prop :=
    ∃ sameLabel : bottom = top,
      let straight := Eq.ndrec
        (motive := fun label => MackeyDiagrams.LabelledDrawing Complex
          (MackeyDiagrams.Word.up bottom) (MackeyDiagrams.Word.up label))
        (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up bottom)))
        sameLabel
      let dotFree := mergeSplit straight
      evalDrawing (mergeSplit (MackeyDiagrams.DotLabel.upDrawing product)) = evalDrawing dotFree ∧
      ∀ sameBoundary : bottomWord = topWord,
        let identity := Eq.ndrec
          (motive := fun word => MackeyDiagrams.LabelledDrawing Complex bottomWord word)
          (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id bottomWord)) sameBoundary
        evalDrawing dotFree = evalDrawing identity
  (∀ (x : MackeyDiagrams.Dot bottom middle) (y : MackeyDiagrams.Dot middle top),
    let product := singleton (MackeyDiagrams.Dot.vertical x y)
    let twoCrossings := MackeyDiagrams.LabelledDrawing.vertical
      (lowerCrossing (singleton x)) (upperCrossing (singleton y))
    evalDrawing twoCrossings = evalDrawing (mergeSplit (MackeyDiagrams.DotLabel.upDrawing product)) ∧
    (MackeyDiagrams.Dot.element x * MackeyDiagrams.Dot.element y = 1 → unitCancellation product)) ∧
  (∀ (x : MackeyDiagrams.DotLabel Complex bottom middle)
      (y : MackeyDiagrams.DotLabel Complex middle top),
    let product := MackeyDiagrams.DotLabel.compose x y
    let twoCrossings := MackeyDiagrams.LabelledDrawing.vertical (lowerCrossing x) (upperCrossing y)
    evalDrawing twoCrossings = evalDrawing (mergeSplit (MackeyDiagrams.DotLabel.upDrawing product)) ∧
    (Finsupp.mapDomain (MackeyDiagrams.Dot.element (a := bottom) (b := top)) product =
      Finsupp.single (1 : G) (1 : Complex) → unitCancellation product)) ∧
  (∀ x : MackeyDiagrams.Dot bottom middle,
    ∃ y : MackeyDiagrams.Dot middle bottom,
      let forward := lowerCrossing (singleton x)
      let backward : MackeyDiagrams.LabelledDrawing Complex middleWord bottomWord :=
        MackeyDiagrams.LabelledDrawing.parallelUp c d a b
          (MackeyDiagrams.DotLabel.terms (singleton y))
      MackeyDiagrams.Dot.element y = (MackeyDiagrams.Dot.element x)⁻¹ ∧
      evalDrawing (MackeyDiagrams.LabelledDrawing.vertical forward backward) =
        evalDrawing (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id bottomWord)) ∧
      evalDrawing (MackeyDiagrams.LabelledDrawing.vertical backward forward) =
        evalDrawing (MackeyDiagrams.LabelledDrawing.ordinary (MackeyDiagrams.Diagram.id middleWord)))) :=
(by
  intro U inst G K H B H' α β γ δ α' β' hα hβ hγ hδ hα' hβ'
    a b c d a' b' bottom middle top bottomWord middleWord topWord
    evalDrawing singleton lowerCrossing upperCrossing bottomMerge topSplit mergeSplit unitCancellation
  -- Xiao, §5.2, Theorem 5.4 and its preceding drawing. The archived
  -- source/mackey-bimodules.pdf has them on p. 18. The revised PDF served at
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf has them on p. 20.
  -- The four steps below follow the order of the article proof.
  -- Theorem 5.4, step 1: split then merge on the middle word. The
  -- registered split/merge result is specialized to (γ, δ) and their inclusions.
  have middleInverse :
      (Diagram.splitUp (R := Complex) c d).eval.vertical (Diagram.mergeUp c d).eval =
        Biset.Hom.id (Word.up middle).basis :=
    (InductionRestrictionMergesAndSplits K B G γ δ hγ hδ).2.2.2.2.1
  -- Theorem 5.4, step 2: compose right multiplications in bottom-to-top order.
  -- The historical checked connection used Diagram with an earlier root
  -- artifact. Here the current merge, dot and split equations are joined
  -- by distributing each trivalent map through the finite sum while
  -- keeping each marked crossing and the single product mark as syntax.
  -- Dot.vertical provides the termwise intertwining proof for each ordered
  -- pair of supported terms used by DotLabel.compose.
  have composeCrossings (x : DotLabel Complex bottom middle)
      (y : DotLabel Complex middle top) :
      evalDrawing (.vertical (lowerCrossing x) (upperCrossing y)) =
        evalDrawing (mergeSplit (DotLabel.upDrawing (DotLabel.compose x y))) := by
    change ((LabelledDrawing.parallelUp a b c d x.terms).interpret.eval).vertical
        (LabelledDrawing.parallelUp c d a' b' y.terms).interpret.eval =
      ((Diagram.mergeUp (R := Complex) a b).eval.vertical
        (DotLabel.upDrawing (DotLabel.compose x y)).interpret.eval).vertical (Diagram.splitUp a' b').eval
    rw [eval_parallelUp_terms, eval_parallelUp_terms]
    exact Biset.Hom.merge_dot_split_comp _ _ _ _ _ _ _ middleInverse
      (DotLabel.upDrawing_compose x y)
  -- Theorem 5.4, step 3: a unit group-algebra product forces equal
  -- embeddings. Transport the straight strand, then use the full word
  -- equality to cancel the outside trivalent vertices.
  have cancelUnit (product : DotLabel Complex bottom top)
      (unit : Finsupp.mapDomain Dot.element product = Finsupp.single (1 : G) (1 : Complex)) :
      unitCancellation product := by
    obtain ⟨same, hunit⟩ := Diagram.eval_linearUpDot_unit product unit
    refine ⟨same, ?_, ?_⟩
    · change ((Diagram.mergeUp (R := Complex) a b).eval.vertical
          (DotLabel.upDrawing product).interpret.eval).vertical (Diagram.splitUp a' b').eval =
        ((Diagram.mergeUp (R := Complex) a b).eval.vertical
          (LabelledDrawing.interpret
            (Eq.ndrec (motive := fun e => LabelledDrawing Complex (.up bottom) (.up e))
              (.ordinary (Diagram.id (.up bottom))) same)).eval).vertical (Diagram.splitUp a' b').eval
      rw [DotLabel.eval_upDrawing, hunit, eval_transported_up_id]
    · intro sameBoundary
      change ((Diagram.mergeUp (R := Complex) a b).eval.vertical
          (LabelledDrawing.interpret
            (Eq.ndrec (motive := fun e => LabelledDrawing Complex (.up bottom) (.up e))
              (.ordinary (Diagram.id (.up bottom))) same)).eval).vertical (Diagram.splitUp a' b').eval =
        (LabelledDrawing.interpret
          (Eq.ndrec (motive := fun w => LabelledDrawing Complex bottomWord w)
            (.ordinary (Diagram.id bottomWord)) sameBoundary)).eval
      rw [eval_transported_up_id, eval_transported_word_id]
      exact Diagram.eval_unitCrossing_sameBoundary a b a' b' same sameBoundary
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    refine ⟨?_, ?_⟩
    · exact (composeCrossings (singleton x) (singleton y)).trans
        (congrArg (fun z => evalDrawing (mergeSplit (DotLabel.upDrawing z))) (compose_singletons x y))
    · intro unit
      apply cancelUnit
      change Finsupp.mapDomain Dot.element (Finsupp.single (x.vertical y) 1) = _
      rw [Finsupp.mapDomain_single]
      exact congrArg (fun g : G => Finsupp.single g (1 : Complex)) unit
  · intro x y
    exact ⟨composeCrossings x y, cancelUnit (DotLabel.compose x y)⟩
  · intro x
    -- Theorem 5.4, step 4: the admissibility supplier gives a typed
    -- return element. Identify it with Dot.inverse using its element
    -- equation, and apply the checked single-crossing law in both orders.
    obtain ⟨y, hy, _, _, _⟩ :=
      (ParallelInductionProductDotAdmissibility G K H B H' α β γ δ α' β'
        hα hβ hγ hδ hα' hβ').2 x
    have hy' : y = x.inverse := Dot.ext hy
    refine ⟨y, hy, ?_, ?_⟩
    · change (LabelledDrawing.parallelUp a b c d (DotLabel.terms (singleton x))).interpret.eval.vertical
        (LabelledDrawing.parallelUp c d a b (DotLabel.terms (singleton y))).interpret.eval =
          (Diagram.id bottomWord).eval
      dsimp only [singleton]
      rw [eval_parallelUp_single, eval_parallelUp_single, hy']
      exact Diagram.parallelUp_return a b c d x
    · change (LabelledDrawing.parallelUp c d a b (DotLabel.terms (singleton y))).interpret.eval.vertical
        (LabelledDrawing.parallelUp a b c d (DotLabel.terms (singleton x))).interpret.eval =
          (Diagram.id middleWord).eval
      dsimp only [singleton]
      have hinv : y.inverse = x := by
        apply Dot.ext
        change y.element⁻¹ = x.element
        rw [hy, inv_inv]
      rw [eval_parallelUp_single, eval_parallelUp_single, ← hinv]
      exact Diagram.parallelUp_return c d a b y)

#print axioms ParallelReidemeisterTwoInduction
