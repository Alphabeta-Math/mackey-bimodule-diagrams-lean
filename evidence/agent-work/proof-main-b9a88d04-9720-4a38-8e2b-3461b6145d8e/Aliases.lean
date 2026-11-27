namespace FiniteParabolicReplacementProof
open MackeyDiagrams

-- These aliases refer to the already compiled construction lemmas in the
-- registered suppliers. The elaborator resolves the exact private name,
-- and the kernel checks each alias against the imported declaration.
private noncomputable abbrev projLeftLabels := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoProjections `ReplacementForTwoProjectionsAux.LeftLabels)

private noncomputable abbrev projRightLabels := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoProjections `ReplacementForTwoProjectionsAux.RightLabels)

private noncomputable abbrev projEvalLeft := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoProjections `ReplacementForTwoProjectionsAux.evalLeft)

private noncomputable abbrev projEvalRight := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoProjections `ReplacementForTwoProjectionsAux.evalRight)

private noncomputable abbrev projMergedEqIff := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoProjections `ReplacementForTwoProjectionsAux.merged_eq_iff)

private noncomputable abbrev projMerged := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoProjections `ReplacementForTwoProjectionsAux.merged)

private noncomputable abbrev projLeftTerm := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoProjections `ReplacementForTwoProjectionsAux.leftTerm)

private noncomputable abbrev projLeftDraw := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoProjections `ReplacementForTwoProjectionsAux.leftDraw)

private noncomputable abbrev projLabelTerms := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoProjections `ReplacementForTwoProjectionsAux.labelTerms)

private noncomputable abbrev projTermsSingle := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoProjections `ReplacementForTwoProjectionsAux.terms_single)

private noncomputable abbrev projWeighted := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoProjections `ReplacementForTwoProjectionsAux.weighted)

private noncomputable abbrev projWeightedLabelTerms := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoProjections `ReplacementForTwoProjectionsAux.weighted_labelTerms)

private noncomputable abbrev projLeftWeighted := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoProjections `ReplacementForTwoProjectionsAux.leftWeighted)

private noncomputable abbrev multRealizeLeft := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoMultiplications `TwoMultiplicationsAux.realizeLeft)

private noncomputable abbrev multRealizeRight := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoMultiplications `TwoMultiplicationsAux.realizeRight)

private noncomputable abbrev multEvalEqIff := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.ReplacementForTwoMultiplications `TwoMultiplicationsAux.eval_eq_iff)

private noncomputable abbrev indLiftMultiplier := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.MultipliersUnderRelabelling `MultipliersUnderRelabellingProof.liftMultiplier)

private noncomputable abbrev indLiftMultiplierValue := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.MultipliersUnderRelabelling `MultipliersUnderRelabellingProof.liftMultiplier_value)

private noncomputable abbrev indDotValueIdentity := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.MultipliersUnderRelabelling `MultipliersUnderRelabellingProof.dotValue_identity)

private noncomputable abbrev indEligibleOfCentralizer := by_elab
  Lean.Meta.mkConstWithFreshMVarLevels
    (Lean.mkPrivateNameCore `Proofs.MultipliersUnderRelabelling `MultipliersUnderRelabellingProof.eligibleOfCentralizer)

