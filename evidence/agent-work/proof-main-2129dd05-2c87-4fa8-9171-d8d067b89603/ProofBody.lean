by
  intro U inst G A D F C E repGA repAD repDF repGC repCE repEF
    hGA hAD hDF hGC hCE hEF ga ad df gc ce ef bottomPair topPair
    word bottom top straight merge split splitBottom mergeTop mergedEvaluation multiplier
    crossing crossLeft crossRight LeftLabels RightLabels leftDiagram rightDiagram
    leftMultiplier rightMultiplier
  -- Lemma 6.1, archived PDF pp. 19–20 and revised published PDF pp. 21–22.
  -- The source locator uses the archived pagination. The PDFs have different
  -- checksums. The online proof has named sections, with no numbered
  -- Alphabeta proof steps supplied for this endpoint.
  -- The registered supplier gives both ordered multiplier formulas and their
  -- termwise support condition on exactly the merge-dot-split drawings above.
  have supplier :=
    ThreeInductionCrossingMultipliers G A D F C E repGA repAD repDF repGC repCE repEF
      hGA hAD hDF hGC hCE hEF
  let allowed := fun p : G =>
    (repGA * repAD * repDF)⁻¹ * (p : U) * (repGC * repCE * repEF) ∈ Subgroup.centralizer (F : Set U)
  refine relabel ga ad df gc ce ef leftMultiplier rightMultiplier allowed ?_ ?_ ?_
  · intro p hp
    exact eligibleOfCentralizer (fun f => (supplier.1 f).1) (fun f => (supplier.1 f).2)
      p ((supplier.2.2.2.2.1 p).2.mpr hp)
  · exact supplier.2.2.2.2.2.1
  · exact supplier.2.2.2.2.2.2
