by
  intro U blockSym parabolic K H G α β hα hβ hK hH hG
    eα eβ A B J σ hσ j s orbit a b Lj left right dot
    L hL hParabolicL hIndex leftL rightL leftJ rightJ dL dJ M ML MJ qBasis qBasisJ q fiber n
  -- Xiao, §8.2, the fiber-sum diagram following Proposition 8.3
  -- (archived PDF pp. 35–36, published 28 November revision pp. 37–38),
  -- invokes the smaller-group formula of §5.1.
  -- The reviewed plan supplies no numbered Alphabeta Math proof for this
  -- endpoint. Steps 1–3 of the registered MixedCrossingComposites proof
  -- use the balanced push and its finite-fiber transfer. Steps 4–5 compare
  -- the two composite columns and detect identity by singleton support.
  -- MixedCrossingsThroughSmallerGroup packages these computations with the
  -- range and cardinality for the chosen j. The prescribed section hσ and
  -- finite relative index hIndex meet its hypotheses directly. The route’s
  -- mixedMultiplicationBasis, transferBasis_sum and
  -- inclusion_then_projection_single calculations are already packaged
  -- in this supplier. The parabolic representative theorem builds a
  -- particular tableau section
  -- and a functor decomposition. Here the section is already given and
  -- can be arbitrary, so no additional representative choice is needed.
  obtain ⟨hfL, hfJ, h⟩ :=
    MixedCrossingsThroughSmallerGroup K H G α β hα hβ σ hσ j L hL hIndex
  refine ⟨hfL, hfJ, ?_⟩
  intro hf fiberSum iotaL pL iotaJ pJ outerL outerJ innerL straight
  rcases h with ⟨hOuter, hRange, hPair, hPush, hProject, hInner, hIdentity⟩
  refine ⟨hOuter, hRange, hPair, hPush, hProject, hInner, ?_⟩
  -- The two straight strands have the same evaluation as the identity of
  -- their tensor boundary. Keep the horizontal node in the diagram syntax.
  have hStraight : straight.eval = (MackeyDiagrams.Diagram.id (R := Complex) ML).eval :=
    MackeyDiagrams.Biset.Hom.horizontal_id
      (MackeyDiagrams.Biset.induction leftL) (MackeyDiagrams.Biset.restriction rightL)
  rw [hStraight]
  exact hIdentity
