import MackeyDiagrams
import Proofs.ThreeInductionReidemeisterThree
import Proofs.ReplacementForTwoProjections
import Proofs.ReplacementForTwoMultiplications
import Proofs.FiniteParabolicJoinOfFamily

set_option maxHeartbeats 2000000

namespace FiniteParabolicReplacementProof
open MackeyDiagrams

private theorem finiteOfBlocks {S : Subgroup (Equiv.Perm Nat)} {G : Subgroup S}
    {n : Nat} (blocks : Fin n → Finset Nat)
    (hG : G.map S.subtype =
      ⨆ i, (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ blocks i)).range) :
    Finite G := by
  classical
  let X := Finset.univ.biUnion blocks
  have fixes (g : G) : ∀ x : Nat, x ∉ X → ((g.val : Equiv.Perm Nat)) x = x := by
    have hg : (g.val : Equiv.Perm Nat) ∈
        ⨆ i, (Equiv.Perm.ofSubtype (p := fun x : Nat => x ∈ blocks i)).range := by
      rw [← hG]
      exact ⟨g.val, g.property, rfl⟩
    refine Subgroup.iSup_induction _ (C := fun σ : Equiv.Perm Nat =>
      ∀ x : Nat, x ∉ X → σ x = x) hg ?_ ?_ ?_
    · rintro i _ ⟨σ, rfl⟩ x hx
      exact Equiv.Perm.ofSubtype_apply_of_not_mem σ
        (fun hxi => hx (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hxi⟩))
    · exact fun _ _ => rfl
    · intro s t hs ht x hx
      change s (t x) = x
      rw [ht x hx, hs x hx]
  let restrict := (Equiv.Perm.subtypeEquivSubtypePerm (fun x : Nat => x ∈ X)).symm
  refine Finite.of_injective (fun g : G => restrict ⟨g.val.val, fixes g⟩) ?_
  intro g h eq
  exact Subtype.ext (Subtype.ext (congrArg Subtype.val (restrict.injective eq)))

private theorem quotientOfReplacements {L R M S : Type}
    (leftEval : L → M) (rightEval : R → M) (leftRegion : L → S) (rightRegion : R → S)
    (B B' : S)
    (forward : ∀ l, ∃ r, rightRegion r = B' ∧ rightEval r = leftEval l)
    (backward : ∀ r, ∃ l, leftRegion l = B ∧ leftEval l = rightEval r) :
    ∃ (toRight : L → R) (toLeft : R → L)
      (classes : Quotient (Setoid.ker leftEval) ≃ Quotient (Setoid.ker rightEval)),
      (∀ l, rightRegion (toRight l) = B' ∧ rightEval (toRight l) = leftEval l ∧
        classes (Quotient.mk _ l) = Quotient.mk _ (toRight l)) ∧
      (∀ r, leftRegion (toLeft r) = B ∧ leftEval (toLeft r) = rightEval r ∧
        classes.symm (Quotient.mk _ r) = Quotient.mk _ (toLeft r)) := by
  choose toRight hR using forward
  choose toLeft hL using backward
  let classes : Quotient (Setoid.ker leftEval) ≃ Quotient (Setoid.ker rightEval) :=
    { toFun := Quotient.map toRight (fun {_ _} h => (hR _).2.trans (h.trans (hR _).2.symm))
      invFun := Quotient.map toLeft (fun {_ _} h => (hL _).2.trans (h.trans (hL _).2.symm))
      left_inv := fun q => Quotient.inductionOn q
        (fun l => Quotient.sound ((hL (toRight l)).2.trans (hR l).2))
      right_inv := fun q => Quotient.inductionOn q
        (fun r => Quotient.sound ((hR (toLeft r)).2.trans (hL r).2)) }
  exact ⟨toRight, toLeft, classes, fun l => ⟨(hR l).1, (hR l).2, rfl⟩,
    fun r => ⟨(hL r).1, (hL r).2, rfl⟩⟩

section InductionCrossing

variable {U : Type} [Group U] {P Q Q' S : Subgroup U}

private abbrev drawingEval {K H : Subgroup U} {p q : Word K H}
    (x : LabelledDrawing Complex p q) :=
  x.interpret.eval

private abbrev expandedParallel
    (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (a' : ConjEmbedding Q' P) (b' : ConjEmbedding S Q')
    (x : DotLabel Complex (a.comp b) (a'.comp b')) :
    LabelledDrawing Complex ((Word.up a).tensor (.up b)) ((Word.up a').tensor (.up b')) :=
  .vertical (.trivalent (.mergeUp a b)) (.vertical x.upDrawing (.trivalent (.splitUp a' b')))

private theorem parallelEval
    (a : ConjEmbedding Q P) (b : ConjEmbedding S Q)
    (a' : ConjEmbedding Q' P) (b' : ConjEmbedding S Q')
    (x : DotLabel Complex (a.comp b) (a'.comp b')) :
    drawingEval (LabelledDrawing.parallelUp a b a' b' x.terms) =
      drawingEval (expandedParallel a b a' b' x) := by
  apply Biset.Hom.ext
  apply LinearMap.ext
  intro z
  change (ScopedDiagram.linearCombination (x.terms.map fun (c, d) =>
    (c, ScopedDiagram.ordinary (Diagram.parallelUp a b a' b' d)))).eval.toLinearMap z =
    (Diagram.splitUp (R := Complex) a' b').eval.toLinearMap
      ((Diagram.finiteSum (x.terms.map fun (c, d) => Diagram.scale c (Diagram.upDot d))).eval.toLinearMap
        ((Diagram.mergeUp (R := Complex) a b).eval.toLinearMap z))
  rw [ScopedDiagram.eval_linearCombination_apply, Diagram.eval_finiteSum]
  simp only [List.map_map, Function.comp_def, map_list_sum, List.map_map, Prod.map,
    Diagram.eval, Biset.Hom.scale, LinearMap.smul_apply, map_smul]
  rfl

private theorem verticalEval {K H : Subgroup U} {p q r : Word K H}
    {a a' : LabelledDrawing Complex p q} {b b' : LabelledDrawing Complex q r}
    (ha : drawingEval a = drawingEval a') (hb : drawingEval b = drawingEval b') :
    drawingEval (a.vertical b) = drawingEval (a'.vertical b') :=
  congrArg₂ Biset.Hom.vertical ha hb

private theorem horizontalEval {K H J : Subgroup U}
    {p q : Word K H} {r s : Word H J}
    {a a' : LabelledDrawing Complex p q} {b b' : LabelledDrawing Complex r s}
    (ha : drawingEval a = drawingEval a') (hb : drawingEval b = drawingEval b') :
    drawingEval (a.horizontal b) = drawingEval (a'.horizontal b') :=
  congrArg₂ Biset.Hom.horizontal ha hb

private theorem represented {H K : Subgroup U} (a : ConjEmbedding H K) :
    ∃ s : U, ∃ h : ∀ x : H, s * (x : U) * s⁻¹ ∈ K,
      a = ConjEmbedding.ofConjugator s h := by
  obtain ⟨s, hs⟩ := a.hasRepresentative
  let h (x : H) := hs x ▸ (a.toHom x).property
  exact ⟨s, h, ConjEmbedding.ext (MonoidHom.ext fun x => Subtype.ext (hs x))⟩

end InductionCrossing

end FiniteParabolicReplacementProof
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

section Projection
variable {U : Type} [Group U] {G A D F C E : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
  (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

-- Theorem 6.4(1). Use the supplier's common right group for the whole
-- coefficient function. Its public existential has forgotten the group.
private theorem projectionForward (hd : d.toHom.range.FiniteIndex)
    (l : projLeftLabels a b c d e f) :
    ∃ r : projRightLabels a b c d e f, r.1 = A ∧
      projEvalRight a b c d e f r = projEvalLeft a b c d e f l := by
  obtain ⟨ell, m, n, _, _, _, _, he⟩ := (CaseOneRightProjectionConstruction a b c d e f).2.1 hd
  obtain ⟨coeff, hc, _, _⟩ := (ReplacementForTwoProjections a b c d e f).2.2.2.2.1 l
  let r : projRightLabels a b c d e f :=
    ⟨A, ConjEmbedding.id A, a.comp d, b.comp c,
      Finsupp.single ell 1, Finsupp.single m 1, Finsupp.mapDomain n coeff⟩
  exact ⟨r, rfl, (projMergedEqIff a b c d e f _ _).1 ((he coeff).trans hc.symm)⟩

-- Theorem 6.4(2). The common left group is E. Collect the lower projection
-- terms in one coefficient label using the supplier's linearity lemma.
private theorem projectionBackward (hd : (d.comp e).toHom.range.FiniteIndex)
    (r : projRightLabels a b c d e f) :
    ∃ l : projLeftLabels a b c d e f, l.1 = E ∧
      projEvalLeft a b c d e f l = projEvalRight a b c d e f r := by
  obtain ⟨coeff, hc, _⟩ := (ReplacementForTwoProjections a b c d e f).2.2.2.2.2.1 r
  obtain ⟨drawing, hshape, he⟩ := (CaseTwoLeftProjectionConstruction a b c d e f).2.1 hd coeff
  obtain ⟨x, y, z, _, _, _, _, rfl⟩ := hshape
  let de := d.comp e
  let cf := c.comp f
  let t := ConjEmbedding.id E
  let l : projLeftLabels a b c d e f :=
    ⟨E, de, cf, t, Finsupp.mapDomain x coeff, Finsupp.single y 1, Finsupp.single z 1⟩
  let value := fun xs => projMerged a b c d e f (projLeftTerm a b c d e f de cf t xs [(1, y)] [(1, z)])
  let unitValue := fun p => value [(1, p)]
  have heval : projMerged a b c d e f (projLeftDraw a b c d e f l) =
      value (projLabelTerms (Finsupp.mapDomain x coeff)) := by
    change projMerged a b c d e f (projLeftTerm a b c d e f de cf t _
      (projLabelTerms (Finsupp.single y 1)) (DotLabel.terms (Finsupp.single z 1))) = _
    rw [show projLabelTerms (Finsupp.single y (1 : Complex)) = [(1, y)] from
      projTermsSingle y one_ne_zero,
      show DotLabel.terms (Finsupp.single z (1 : Complex)) = [(1, z)] from
      projTermsSingle z one_ne_zero]
  have hcollect : value (projLabelTerms (Finsupp.mapDomain x coeff)) =
      value ((projLabelTerms coeff).map fun term => (term.1, x term.2)) := by
    calc
      _ = projWeighted unitValue (projLabelTerms (Finsupp.mapDomain x coeff)) :=
        projLeftWeighted a b c d e f de cf t _ _ _
      _ = Finsupp.linearCombination Complex (unitValue ∘ x) coeff := by
        rw [projWeightedLabelTerms, Finsupp.linearCombination_mapDomain]
      _ = projWeighted (unitValue ∘ x) (projLabelTerms coeff) :=
        (projWeightedLabelTerms _ _).symm
      _ = projWeighted unitValue ((projLabelTerms coeff).map fun term => (term.1, x term.2)) := by
        simp only [projWeighted, List.map_map, Function.comp_def]
      _ = _ := (projLeftWeighted a b c d e f de cf t _ _ _).symm
  exact ⟨l, rfl, (projMergedEqIff a b c d e f _ _).1
    (heval.trans (hcollect.trans (he.trans hc.symm)))⟩

end Projection

end FiniteParabolicReplacementProof
