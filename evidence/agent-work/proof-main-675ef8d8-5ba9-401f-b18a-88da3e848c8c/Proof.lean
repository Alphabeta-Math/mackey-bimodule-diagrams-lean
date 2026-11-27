by
  open MackeyDiagrams MovingMergeDotProof in
  intro U inst K H G γ α target D singleton upInput downInput mergedUp mergedDown
    matchesUp matchesDown inImage
  -- Xiao § 3.2, “Moving a dot back to a branch,” archived original p. 9
  -- and revised published PDF p. 11. The two copies have distinct hashes.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf#page=11
  -- The rendered restriction merge reverses the horizontal order and uses
  -- the inverse multiplier. No numbered Alphabeta counterpart is registered.
  -- Apply (3.1) and (3.3) at d = 1 for the right branch or e = 1 for the left.
  -- The shared identity-dot laws remove the unused mark at evaluation only.
  have transferUp {out : ConjEmbedding K G} (E : Dot (γ.comp α) out)
      (h : out = target) (p : LabelledDrawing Complex upInput (Word.up out))
      (hp : p.interpret.eval = ((mergeUp γ α).vertical (up E)).interpret.eval) :
      matchesUp h p ↔ E.element = D.element := by
    subst out
    change p.interpret.eval = ((mergeUp γ α).vertical (up D)).interpret.eval ↔ _
    rw [hp]
    exact ⟨detectUp, fun he => by rw [show E = D from Dot.ext he]⟩
  have transferDown {out : ConjEmbedding K G} (E : Dot (γ.comp α) out)
      (h : out = target) (p : LabelledDrawing Complex downInput (Word.down out))
      (hp : p.interpret.eval = ((mergeDown γ α).vertical (down E)).interpret.eval) :
      matchesDown h p ↔ E.element = D.element := by
    subst out
    change p.interpret.eval = ((mergeDown γ α).vertical (down D)).interpret.eval ↔ _
    rw [hp]
    exact ⟨detectDown, fun he => by rw [show E = D from Dot.ext he]⟩
  -- Evaluation on the unit tensor justifies cancellation in the necessity
  -- argument. The merge and singleton-label formulas give the coefficients
  -- in both orientations. A nonzero singleton coefficient detects its index.
  -- The range witness supplies e directly. Conjugation by e⁻¹ preserves H
  -- and determines β; the common effective multiplier fixes the output label.
  have rightWitness (hi : inImage) :
      ∃ (β : ConjEmbedding K H) (e : Dot α β),
        (e.whisker γ).element = D.element := by
    obtain ⟨s, hs⟩ := hi
    obtain ⟨β, e, he⟩ := retarget α s
    exact ⟨β, e, (congrArg γ.toHom he).trans hs⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨β, e, h, hp⟩
    exact ⟨e.element, (transferUp (e.whisker γ) h (rightUp γ e) (rightSlide γ e).1).mp hp⟩
  · intro hi
    obtain ⟨β, e, he⟩ := rightWitness hi
    have h := sameTarget he
    exact ⟨β, e, h,
      (transferUp (e.whisker γ) h (rightUp γ e) (rightSlide γ e).1).mpr he⟩
  · rintro ⟨β, e, h, hp⟩
    exact ⟨e.element, (transferDown (e.whisker γ) h (rightDown γ e) (rightSlide γ e).2).mp hp⟩
  · intro hi
    obtain ⟨β, e, he⟩ := rightWitness hi
    have h := sameTarget he
    exact ⟨β, e, h,
      (transferDown (e.whisker γ) h (rightDown γ e) (rightSlide γ e).2).mpr he⟩
  · -- The new outer representative is D⁻¹γ. Its lifted dot has element D.
    obtain ⟨γ', d, hd⟩ := retarget γ D.element
    have h := sameTarget (e := liftOuter d α) hd
    have ⟨hu, hdown⟩ := leftSlide d α
    exact ⟨γ', d, h, (transferUp (liftOuter d α) h (leftUp d α) hu).mpr hd,
      (transferDown (liftOuter d α) h (leftDown d α) hdown).mpr hd⟩
