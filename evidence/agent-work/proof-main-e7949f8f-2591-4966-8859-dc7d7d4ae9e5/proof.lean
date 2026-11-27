by
  open ReverseTriangleIdentitiesSupport in
  intro U _ H G α hα A B a S φ up down traceCap cap pairDI pairID basisG E
  -- Xiao, § 1.2, Cups and caps, p. 3 in the archived original and p. 4
  -- in the published 28 November revision (SHA-256 813c82da512e992a11a53aa044c3a79d199b2bef5295639084c1f6b789d27e61).
  -- The dual-basis formulas agree in both copies. The reverse cup starts
  -- at the empty G boundary and the trace cap ends at the empty H boundary.
  obtain ⟨hTraceIn, hTraceOut, hBimodule, hCap, hFinite⟩ :=
    FiniteIndexReverseAdjunction.{u, v} H G α hα
  refine ⟨hTraceIn, hTraceOut, hBimodule, hCap, ?_⟩
  intro finite reverseCup cup IsT toRep Ind Res pure
  obtain ⟨⟨T, hT⟩, adj, hCounit, hCupUnit⟩ := hFinite finite
  have hCup : CupFormula a finite T := by
    calc
      _ = _ := ((hCupUnit T hT).1 1).1
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t _
        change MackeyDiagrams.Biset.pairLinear Complex up.basis down.basis
          (Finsupp.single ((1 : G) * t⁻¹) 1) (Finsupp.single t 1) = _
        rw [MackeyDiagrams.Biset.pairLinear_single, one_mul, mul_one]
  -- The right transversal selects the term for the down strand. Applying
  -- it to g⁻¹ selects the term for the up strand by subgroup inversion.
  -- Alphabeta Math's module tensor universal property, Steps 3.1 and 4.1,
  -- motivates balance and checking on elementary tensors. The shared
  -- balanced biset supplies descent, and linearity extends the basis checks.
  -- The categorical triangle laws apply to the supplied module adjunction.
  -- The diagram triangles are evaluated separately on the strand bases,
  -- with the supplied cup expansion and the trace-basis formula.
  exact ⟨⟨T, hT⟩, fun T' hT' => dual_basis a T' hT',
    ⟨triangle_down a finite T hT hCup, triangle_up a finite T hT hCup⟩,
    adj, adj.left_triangle_components, adj.right_triangle_components, hCounit, hCupUnit⟩
