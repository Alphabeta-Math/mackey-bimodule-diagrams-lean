by
  open MackeyDiagrams CurlWithCentralizingDotSupport in
  intro U _ K H G δ α hδ hα inner outer S lift basis finite
  -- Xiao §3.1, the paragraph after Proposition 3.1's curl calculation:
  -- archived original PDF p. 8, published 28 November revision pp. 10–11
  -- (SHA-256 813c82da512e992a11a53aa044c3a79d199b2bef5295639084c1f6b789d27e61).
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- The revision permits commutation after addition for the endomorphism
  -- in this calculation. The middle mark uses the separate AlgebraUpDot
  -- evaluator with that whole-algebra hypothesis. The comparison uses
  -- equality of evaluations, and the sliding mark uses the finite
  -- termwise eligible DotLabel.
  -- RightCurlAndDotSlide supplies only the inclusion-index clause.
  refine ⟨((RightCurlAndDotSlide K H G).1 δ α hδ hα finite).1, ?_⟩
  intro a ha middle curl transversal term T hT trace
  have hcentral : ∀ y : MonoidAlgebra Complex H, Commute y trace :=
    CurlWithCentralizingDotSupport.trace_central inner a ha T hT
  refine ⟨hcentral, ?_⟩
  intro traceLabel straight
  -- Alphabeta Math, Module tensor universal property, Steps 3.1, 4.1
  -- and 5.1, motivates descent through balancing and checking generators.
  -- https://alphabetamath.cc/item/thm-universal-property-of-module-tensor-products
  -- Here the shared Biset.pairLinear has already descended. The
  -- finite-index witness and unique right transversal are passed to
  -- FiniteIndexReverseAdjunction at the inner embedding; its first cup
  -- formula at 1 already packages Generator.rightCosetEquivCapFiber's
  -- reindexing of the multiplication-cap fiber.
  have cup :
      (Diagram.reverseCup (R := Complex) inner finite).eval.toLinearMap (Finsupp.single 1 1) =
        ∑ t ∈ T, Biset.pairLinear Complex (Word.up inner).basis (Word.down inner).basis
          (Finsupp.single t⁻¹ 1) (Finsupp.single t 1) := by
    -- The spare module universe can be 0 in this diagram calculation.
    obtain ⟨_, _, _, hCup⟩ := (FiniteIndexReverseAdjunction.{_, 0} K H δ hδ).2.2.2.2 finite
    simpa only [inner, MonoidAlgebra.coeff_single, one_mul] using ((hCup T hT).1 1).1
  have hEval : curl.eval = (straight outer).eval := by
    apply Biset.Hom.ext
    apply Finsupp.lhom_ext
    intro g c
    change G at g
    have hc : Finsupp.single g c = c • Finsupp.single g (1 : Complex) := by
      simp [Finsupp.smul_single, smul_eq_mul]
    rw [hc, map_smul, map_smul]
    apply congrArg (c • ·)
    exact CurlWithCentralizingDotSupport.curl_basis outer inner middle finite T cup g
  refine ⟨hEval, ?_, CurlWithCentralizingDotSupport.summand_invariant inner a ha, ?_⟩
  · intro x
    rw [hEval]
    change (MonoidAlgebra.ofCoeff (MonoidAlgebra.coeff x) * lift outer trace).coeff = _
    rw [MonoidAlgebra.ofCoeff_coeff]
  · intro β hβ outer' d dot slideBelow slideAbove
    exact CurlWithCentralizingDotSupport.trace_slide traceLabel d
