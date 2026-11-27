by
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
    rw [MonoidAlgebra.single_mul_single, one_mul, mul_inv_rev]
