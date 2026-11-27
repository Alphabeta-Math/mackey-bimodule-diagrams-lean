by
  classical
  intro U inst G A D F C E a b c d e f up down tensor comp hom bc ad de ade bcf
    bottom top mergedBottom mergedTop Drawing drawId splitBottom mergeTop eval mergedEval
    atRight ProjectionLabel Parameter Q Qstar intersection lower terms finiteFibers left right
    Left Right leftDrawing rightDrawing sumDrawings conjugatedImage join middleFinite expansion
    leftEval rightEval leftClasses rightClasses
  -- Xiao, §6.2.1, Lemma 6.3 and Theorem 6.4, archived original pp. 22–23
  -- (bc57d137…) and revised published PDF pp. 24–25 (6d7e8859…).
  -- Alphabeta Math numbers the replacement directions as Theorem 6.4(1)
  -- and (2), with the constructions and the quotient argument in prose.
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#thm:three-projections
  obtain ⟨hindex, hfibers, hleft, hright⟩ := EvaluationForTwoProjections a b c d e f
  have sum_eq (ds : List Drawing) : sumDrawings ds = ReplacementForTwoProjectionsAux.drawSum ds := by
    cases ds <;> rfl
  refine ⟨hindex, hfibers, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro B r s t x y z
    exact (hleft r s t).1 x y z
  · intro B' j v w ell m n
    exact (hright j v w).1 ell m n
  -- Step 1 (Theorem 6.4(1)). The join construction and finite-sum
  -- criterion use their original middle-index hypothesis. The merge
  -- and split inverses transport equality to the fixed boundary.
  · intro l
    obtain ⟨coeff, hc, hu⟩ := ReplacementForTwoProjectionsAux.leftCoefficients a b c d e f l
    refine ⟨coeff, hc, hu, ?_⟩
    refine Iff.trans ?_ (ReplacementForTwoProjectionsAux.caseOne a b c d e f l coeff hc)
    constructor
    · rintro ⟨ds, he⟩
      exact ⟨ds, (congrArg eval (sum_eq (ds.map rightDrawing))).symm.trans he⟩
    · rintro ⟨ds, he⟩
      exact ⟨ds, (congrArg eval (sum_eq (ds.map rightDrawing))).trans he⟩
  · exact ReplacementForTwoProjectionsAux.rightCoefficients a b c d e f
  · exact ReplacementForTwoProjectionsAux.singleRight a b c d e f
  · exact ReplacementForTwoProjectionsAux.singleCaseOne a b c d e f
  -- Step 2 (Theorem 6.4(2)). The full intersection gives one left term
  -- per supported parameter. The common group under finite index lets
  -- those coefficients share one lower mark.
  · intro r
    obtain ⟨ds, he⟩ := ReplacementForTwoProjectionsAux.caseTwo a b c d e f r
    exact ⟨ds, (congrArg eval (sum_eq (ds.map leftDrawing))).trans he⟩
  · exact ReplacementForTwoProjectionsAux.singleCaseTwo a b c d e f
  -- Step 3 (Theorem 6.4, final paragraph). Apply both single replacements
  -- and descend them to the quotient by evaluation. The index of the
  -- image of de supplies finite index for the larger image of d.
  · exact ReplacementForTwoProjectionsAux.evaluationClasses a b c d e f
