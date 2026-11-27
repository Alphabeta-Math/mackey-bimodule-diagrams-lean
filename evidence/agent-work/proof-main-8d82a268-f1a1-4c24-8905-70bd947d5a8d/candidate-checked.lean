by
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
  have hCurls := (CurlAcrossTrivalentVertex K H G (1 : U) (1 : U) hγ hα).2
    L rightLoop (inferInstance : rightLoop.toHom.range.FiniteIndex)
  have hRight := (hCurls.2.1 L rightLoop
    (inferInstance : rightLoop.toHom.range.FiniteIndex)).1
  have hLeft := (hCurls.2.2 L leftLoop
    (inferInstance : leftLoop.toHom.range.FiniteIndex)).1
  constructor
  · rw [eval_expansion]
    simpa only [hRightIndex, Nat.cast_one, MackeyDiagrams.LabelledDrawing.interpret,
      MackeyDiagrams.ScopedDiagram.eval, MackeyDiagrams.Diagram.eval] using hRight
  · rw [eval_expansion]
    simpa only [hLeftIndex, Nat.cast_ofNat, MackeyDiagrams.LabelledDrawing.interpret,
      MackeyDiagrams.ScopedDiagram.eval, MackeyDiagrams.Diagram.eval] using hLeft
