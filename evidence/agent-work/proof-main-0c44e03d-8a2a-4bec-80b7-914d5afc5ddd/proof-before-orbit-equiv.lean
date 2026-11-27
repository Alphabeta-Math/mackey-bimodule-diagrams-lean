by
  classical
  intro U inst G A D F C E a b d c e f up down tensor comp ga ad df gc ce ef bottom top
    X Y Pair input output orbit stabilizer projected coefficient LowerLabel MiddleLabel
    UpperLabel Fiber lowerMap finiteFibers ProjectionTerm projectionTerm drawId rightDrawing
    singletonDrawing eval IsRightTerm
  -- Ian Xiao, § 6.3.1, Theorem 6.7, archived p. 26 and revised published
  -- p. 28. Equation (6.4) is on archived p. 25 and revised p. 27.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- The endpoint has no linked numbered Alphabeta proof in the coordinator
  -- context. The numbered comments follow the construction in the paper.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Step 1. Equivariance transports the entire finitely supported column.
    rintro M z z' ⟨q, rfl⟩
    exact ProjectedRightOrbitAux.coefficient_smul a b d c e f M q z
  · -- Step 2. Normalize the first G-coordinate by a simultaneous left action.
    exact ProjectedRightOrbitAux.normalize a b d c e f
  · -- Step 3. Recover the conjugation embeddings and three vertex conditions
    -- from the full stabilizer, using the inverse on the action's F-coordinate.
    intro r t s z₀ P O
    refine ⟨ProjectedRightOrbitAux.projected_equations a b d c e f r t s,
      ProjectedRightOrbitAux.orbit_range a b d c e f r t s, ?_, ?_⟩
    · intro g g' x h
      simpa only [mul_assoc] using ProjectedRightOrbitAux.point_eq a b d g' g (r * d.toHom h) x
    · obtain ⟨i, j, k, rDot, tDot, sDot, hj, hr, ht, hs, graph⟩ :=
        ProjectedRightOrbitAux.graph_and_dots a b d c e f r t s
      -- Step 4. The graph yields the exact balance relation on representatives.
      -- The orbit-stabilizer equivalence gives an abstract orbit quotient.
      -- Here the explicit relation also identifies the specified projection fiber.
      have bij (g : G) (x : D) :
          Set.BijOn (ProjectedRightOrbitAux.fiberOutput a c e f i j t s g)
            {w | lowerMap P i j rDot w = MackeyDiagrams.Generator.mixedPair b d x}
            {y | (input g x, y) ∈ O} :=
        ProjectedRightOrbitAux.fiber_bij a b d c e f r t s g x i j rDot hr graph
      refine ⟨i, j, k, rDot, tDot, sDot, hj, hr, ht, hs, graph, bij, ?_⟩
      -- Step 5. Column support proves finite fibers. Apply the registered
      -- CaseSixRightShapeEvaluation singleton clause and count the unique preimage.
      intro M hM
      have hf := ProjectedRightOrbitAux.finite_supported_orbit a b d c e f M z₀ hM
      refine ⟨hf, ?_⟩
      have fin : finiteFibers P i j rDot := by
        intro z
        let x := MackeyDiagrams.Generator.mixedProduct b d z
        have hx : MackeyDiagrams.Generator.mixedPair b d x = z :=
          MackeyDiagrams.Generator.mixedPair_mixedProduct b d z
        have h := (bij 1 x).finite_iff_finite.mpr (hf (input 1 x))
        rw [hx] at h
        exact h
      refine ⟨fin, fun z => ?_⟩
      have hbij (g : G) (x : D) :
          Set.BijOn (ProjectedRightOrbitAux.fiberOutput a c e f i j tDot.element sDot.element g)
            {w | lowerMap P i j rDot w = MackeyDiagrams.Generator.mixedPair b d x}
            {y | (input g x, y) ∈ ProjectedRightOrbitAux.orbit a b d c e f
              rDot.element tDot.element sDot.element} := by
        simpa only [hr, ht, hs] using bij g x
      have hc := ProjectedRightOrbitAux.column_indicator a b d c e f i j k
        rDot tDot sDot fin hbij z
      simpa only [hr, ht, hs] using hc
  · -- Step 6. Every allowed singleton triple is confined to the orbit of its labels.
    intro P
    exact ProjectedRightOrbitAux.singleton_nonzero a b d c e f
  · -- Step 7. The three finite labels and the outer finite sum give finitely
    -- many possible orbits, without requiring that any of the orbits be finite.
    intro terms hterms drawing
    apply ProjectedRightOrbitAux.activeOrbits_fold a b d c e f terms
    intro term hterm
    obtain ⟨P, i, j, k, lower, middle, upper, h⟩ := hterms term hterm
    rw [h]
    exact ProjectedRightOrbitAux.activeOrbits_drawing a b d c e f i j k lower middle upper
  · -- Step 8. At a fixed input, project the column's finite support to orbits.
    intro M p
    apply ((M.toLinearMap (Finsupp.single p 1)).support.finite_toSet.image
      (fun y => orbit (p, y))).subset
    rintro O ⟨y, hy, rfl⟩
    exact ⟨y, Finsupp.mem_support_iff.mpr hy, rfl⟩
