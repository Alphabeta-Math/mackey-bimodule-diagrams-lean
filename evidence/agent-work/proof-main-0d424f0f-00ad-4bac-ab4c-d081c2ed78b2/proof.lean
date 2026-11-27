by
  classical
  intro finitary U blockSym parabolic G A D F C E hG hA hD hF hC hE
    a b d c e f up down tensor comp ga ad df gc ce ef bottom top X Y Pair input output
    project projectedPair projectedSource projectedTarget MatrixMap
    coefficient evaluate ordinary stack juxtapose ProjectionLabel LeftData leftDrawing rightDrawing
    B₀ hB₀ i₀ j₀ k₀ r₀ t₀ s₀ z orbit orbitCoefficient hstrict N terms weights hterms leftSum
  -- Xiao, Proposition 8.8, first assertion and first diagram
  -- (archived original p. 41 and revised published PDF p. 43).
  -- The online proof has one paragraph for this assertion, without numbered steps.
  -- Step 1 follows its invocation of Proposition 8.7 through the registered
  -- SupportedLeftOrbitProjectedStabilizer theorem. All seven groups are
  -- parabolic. Its upper projection certificate agrees by proof irrelevance
  -- with the one carried by each eligible projection term.
  have vanishes (n : Fin N) :
      coefficient (evaluate (leftDrawing (terms n))) z = 0 := by
    have hB := hterms n
    revert hB
    generalize terms n = term
    rcases term with ⟨B, u, v, w, rs, ts, ss⟩
    intro hB
    -- Step 2 follows the linear-label paragraph after Proposition 8.7
    -- and expands all three marks in the shared evaluator. This handles the supplied projection list directly,
    -- including repeated terms and their individual finite-fiber witnesses.
    -- EvaluationWithOneProjection gives a fiber formula on left-associated
    -- columns, with its weighted projection list built from a Finsupp.
    -- The local expansion instead preserves the actual list and outer
    -- associators. The singleton coefficient calculation is already proved
    -- in SupportedLeftOrbitProjectedStabilizer.
    apply CaseSixStrictAux.left_apply_zero a b d c e f u v w
      (DotLabel.terms rs) (DotLabel.terms ts) ss (Finsupp.single z.1 1) z.2
    intro r t s
    rcases SupportedLeftOrbitProjectedStabilizer hG hA hD hF hC hE hB
      a b d c e f u v w r t s.dot with
      ⟨finite, source, target, hsource, htarget, hsourceAct, htargetAct, hsupport, hstabilizer, _⟩
    by_contra hnonzero
    have heq : projectedPair z = projectedSource z.1 ⊓ projectedTarget z.2 :=
      (hstabilizer z hnonzero).1
    exact (ne_of_lt hstrict) heq
  -- Step 3 uses the actual indexed drawing evaluation. The right
  -- orbit indicator has coefficient one at its representative. For an
  -- arbitrary right drawing the nonzero coefficient is a hypothesis.
  -- ParabolicRightOrbitMultiplicity computes and normalizes singleton
  -- right terms separately.
  have hsum : coefficient (IndexedDrawing.eval leftSum) z = 0 := by
    change (IndexedDrawing.eval leftSum (Finsupp.single z.1 1)) z.2 = 0
    rw [IndexedDrawing.eval_apply, Finset.sum_apply']
    apply Finset.sum_eq_zero
    intro n hn
    change (weights n • evaluate (leftDrawing (terms n)) (Finsupp.single z.1 1)) z.2 = 0
    rw [Finsupp.smul_apply]
    change weights n • coefficient (evaluate (leftDrawing (terms n))) z = 0
    rw [vanishes, smul_zero]
  constructor
  · intro hall
    have hz : z ∈ orbit := ⟨1, Prod.ext (Biset.one_act X z.1) (Biset.one_act Y z.2)⟩
    have hone : orbitCoefficient z = 1 := ite_eq_left hz
    have h := hall z
    rw [hsum, hone] at h
    exact zero_ne_one h
  · intro B' hB' i j k r t s rightMap hnonzero heq
    apply hnonzero
    rw [heq, hsum]
