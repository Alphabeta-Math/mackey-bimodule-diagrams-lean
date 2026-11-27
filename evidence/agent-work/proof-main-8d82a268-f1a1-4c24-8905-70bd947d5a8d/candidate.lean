by
  -- Xiao, Example 3.1 (archived original p. 9, 28 November revision p. 12).
  -- Section 3.2 immediately before the example specifies an undotted right
  -- curl on each input, with right regions K and H respectively.
  intro U G H K L leftStrand rightStrand rightLoop leftLoop rightCurl
  open MackeyDiagrams in
  have eval_expansion {A B M : Subgroup U} (strand : ConjEmbedding A B)
      (loop : ConjEmbedding M A) (finite : loop.toHom.range.FiniteIndex) :
      (rightCurl strand loop finite).eval =
        ((LabelledDrawing.trivalent (R := Complex)
            (TrivalentVertex.upToUpDown strand loop finite)).vertical
          (LabelledDrawing.trivalent (TrivalentVertex.upDownToUp strand loop))).interpret.eval := by
    -- Expand the two bent vertices. Interchange combines merge and split
    -- beside the downward identity, and associativity matches the explicit curl.
    let down := Biset.Hom.id (R := Complex) (Word.down loop).basis
    have hMiddle := Biset.Hom.horizontal_vertical
      (Generator.mergeUp Complex strand loop) down (Generator.splitUp Complex strand loop) down
    dsimp only [down] at hMiddle
    rw [Biset.Hom.id_vertical] at hMiddle
    simp only [rightCurl, LabelledDrawing.interpret, ScopedDiagram.eval,
      TrivalentVertex.expand, BentVertex.expand, Diagram.eval,
      ← hMiddle, Biset.Hom.vertical_assoc]
  -- Use the reviewed Multiplicative (ZMod 2) model and compute the
  -- two extremal subgroup indices directly in that model.
  -- Alphabeta Math, steps 1.1 and 1.2, count the quotient of a group
  -- by itself and by its trivial subgroup, respectively.
  -- https://alphabetamath.cc/item/ex-index-of-the-trivial-subgroups
  have hRightIndex : rightLoop.toHom.range.index = 1 := by
    change (MonoidHom.id K).range.index = 1
    have hRange : (MonoidHom.id K).range = ⊤ :=
      MonoidHom.range_eq_top.mpr fun x => ⟨x, rfl⟩
    rw [hRange, Subgroup.index_top]
  have hLeftRange : leftLoop.toHom.range = (⊥ : Subgroup H) := by
    apply le_antisymm _ bot_le
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    have hx : (x : U) = 1 := Subgroup.mem_bot.mp x.property
    simp [leftLoop, hx]
  -- H is the top subgroup of a finite group of order two, as required
  -- for the cardinality argument in step 1.2. Mathlib computes the index
  -- via the quotient equivalence with H.
  have hLeftIndex : leftLoop.toHom.range.index = 2 := by
    rw [hLeftRange, Subgroup.index_bot]
    change Nat.card (⊤ : Subgroup U) = 2
    rw [Subgroup.card_top]
    change Nat.card (ZMod 2) = 2
    exact Nat.card_zmod 2
  have hγ : ∀ x : H, (1 : U) * (x : U) * (1 : U)⁻¹ ∈ G := by
    intro x
    simp [G]
  have hα : ∀ x : K, (1 : U) * (x : U) * (1 : U)⁻¹ ∈ H := by
    intro x
    simp [H, G]
  -- Both loop images have finite index because their ambient groups
  -- are finite. The right loop also supplies the supplier's merged-loop
  -- parameter, since the merged strand has right region K.
  have finiteRight : rightLoop.toHom.range.FiniteIndex := inferInstance
  have finiteLeft : leftLoop.toHom.range.FiniteIndex := inferInstance
  have hCurls :=
    (CurlAcrossTrivalentVertex K H G (1 : U) (1 : U) hγ hα).2 L rightLoop finiteRight
  -- Select the two full scalar evaluations at their respective boundaries.
  -- The supplier uses equality of indices only for the subsequent slide.
  have hRight := (hCurls.2.1 L rightLoop finiteRight).1
  have hLeft := (hCurls.2.2 L leftLoop finiteLeft).1
  constructor
  · rw [eval_expansion]
    simpa only [hRightIndex, Nat.cast_one] using! hRight
  · rw [eval_expansion]
    simpa only [hLeftIndex, Nat.cast_ofNat] using! hLeft
