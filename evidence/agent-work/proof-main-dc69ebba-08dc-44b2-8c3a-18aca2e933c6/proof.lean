by
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
      exact Diagram.parallelUp_return c d a b y
