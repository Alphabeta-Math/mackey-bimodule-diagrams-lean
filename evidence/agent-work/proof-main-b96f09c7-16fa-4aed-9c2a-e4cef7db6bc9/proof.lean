by
  intro U inst K H G α γ b hα hγ hb hD D outer inner input merged inputDot singleton
    upTop downTop dotThenSplitUp dotThenSplitDown evalUpAtInput evalDownAtInput
  -- Xiao, § 3.2, “Moving a dot back to a branch,” archived original p. 9
  -- and published 28 November revision p. 11. No numbered Alphabeta proof
  -- steps are registered for this endpoint. The construction uses (3.2) and (3.4).
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf#page=11
  have hInputDot : inputDot.element = D := rfl
  constructor
  · intro newInner sameInput rightLabel splitThenRightUp splitThenRightDown matchEq
    -- Apply the target merge to both split evaluations at the unit.
    -- This uses splitUp_mergeUp and splitDown_mergeDown, the inverse laws
    -- on the single strand. The other inverse laws act on two strands.
    -- For a finite right label the resulting coefficients are pushed through
    -- the outer embedding term by term. Downward, the indices use inverses.
    rcases matchEq with hu | hd
    · have h := congrArg Biset.Hom.toLinearMap hu
      change dotThenSplitUp.interpret.eval.toLinearMap =
        (show LabelledDrawing Complex (.up input) upTop from
          sameInput ▸ splitThenRightUp).interpret.eval.toLinearMap at h
      rw [castUp] at h
      exact hInputDot ▸ rightUpNecessary outer newInner inner inputDot rightLabel h
    · have h := congrArg Biset.Hom.toLinearMap hd
      change dotThenSplitDown.interpret.eval.toLinearMap =
        (show LabelledDrawing Complex (.down input) downTop from
          sameInput ▸ splitThenRightDown).interpret.eval.toLinearMap at h
      rw [castDown] at h
      exact hInputDot ▸ rightDownNecessary outer newInner inner inputDot rightLabel h
  · intro leftRepresentative
    -- Factor the given input representative, keeping the inner label fixed.
    have hFactor : b = leftRepresentative * γ := by
      change b = (b * γ⁻¹) * γ
      group
    have hLeftRep : leftRepresentative = (D : U) * α := by
      change b * γ⁻¹ = (b * (α * γ)⁻¹) * α
      group
    refine ⟨hFactor, hLeftRep, ?_⟩
    have hLeft (h : H) : leftRepresentative * (h : U) * leftRepresentative⁻¹ ∈ G := by
      have hm := (D * outer.toHom h * D⁻¹).property
      change (D : U) * (α * (h : U) * α⁻¹) * (D : U)⁻¹ ∈ G at hm
      rw [hLeftRep]
      convert hm using 1
      group
    refine ⟨hLeft, ?_⟩
    intro newOuter
    have sameInput : newOuter.comp inner = input := by
      apply ConjEmbedding.ext
      apply MonoidHom.ext
      intro k
      apply Subtype.ext
      change leftRepresentative * (γ * (k : U) * γ⁻¹) * leftRepresentative⁻¹ =
        b * (k : U) * b⁻¹
      rw [hFactor]
      group
    have hRel : leftRepresentative * α⁻¹ = (D : U) := by rw [hLeftRep, mul_assoc, mul_inv_cancel, mul_one]
    have hRelMem : leftRepresentative * α⁻¹ ∈ G := by rw [hRel]; exact D.property
    let leftDot : Dot newOuter outer :=
      Dot.ofRepresentatives leftRepresentative α (fun _ => rfl) (fun _ => rfl) hRelMem
    have hDot : leftDot.element = D := Subtype.ext hRel
    refine ⟨sameInput, leftDot, hDot, ?_⟩
    intro splitThenLeftUp splitThenLeftDown
    let stem : Dot (newOuter.comp inner) merged :=
      ⟨leftDot.element, fun k => leftDot.intertwines (inner.toHom k)⟩
    have ⟨hu, hd⟩ := leftSlide leftRepresentative α γ hLeft hα hγ hRelMem
    -- The replacement has the same input embedding. On the underlying
    -- free modules, the lifted dot and the original dot have multiplier D.
    have sameUp : (up inputDot).interpret.eval.toLinearMap =
        (up stem).interpret.eval.toLinearMap := by
      apply Finsupp.lhom_ext
      intro x r
      rw [upSingle, upSingle, hInputDot, show stem.element = D from hDot]
    have sameDown : (down inputDot).interpret.eval.toLinearMap =
        (down stem).interpret.eval.toLinearMap := by
      apply Finsupp.lhom_ext
      intro x r
      rw [downSingle, downSingle, hInputDot, show stem.element = D from hDot]
    constructor
    · apply Biset.Hom.ext
      change dotThenSplitUp.interpret.eval.toLinearMap =
        (show LabelledDrawing Complex (.up input) upTop from
          sameInput ▸ splitThenLeftUp).interpret.eval.toLinearMap
      rw [castUp]
      have h := congrArg Biset.Hom.toLinearMap hu.symm
      change (Diagram.splitUp (R := Complex) outer inner).eval.toLinearMap.comp
        (up inputDot).interpret.eval.toLinearMap = _
      rw [sameUp]
      exact h
    · apply Biset.Hom.ext
      change dotThenSplitDown.interpret.eval.toLinearMap =
        (show LabelledDrawing Complex (.down input) downTop from
          sameInput ▸ splitThenLeftDown).interpret.eval.toLinearMap
      rw [castDown]
      have h := congrArg Biset.Hom.toLinearMap hd.symm
      change (Diagram.splitDown (R := Complex) outer inner).eval.toLinearMap.comp
        (down inputDot).interpret.eval.toLinearMap = _
      rw [sameDown]
      exact h
