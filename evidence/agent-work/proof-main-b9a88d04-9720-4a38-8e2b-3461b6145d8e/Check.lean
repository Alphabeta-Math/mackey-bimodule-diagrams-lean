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
  have hh := restrict.injective eq
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun s => s.val) hh

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

private noncomputable abbrev drawingEval {K H : Subgroup U} {p q : Word K H}
    (x : LabelledDrawing Complex p q) :=
  x.interpret.eval

private noncomputable abbrev expandedParallel
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
  simp only [List.map_map, Function.comp_def, map_list_sum, List.map_map,
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
        refine (projWeightedLabelTerms unitValue (Finsupp.mapDomain x coeff)).trans ?_
        rw [Finsupp.linearCombination_mapDomain]
      _ = projWeighted (unitValue ∘ x) (projLabelTerms coeff) :=
        (projWeightedLabelTerms _ _).symm
      _ = projWeighted unitValue ((projLabelTerms coeff).map fun term => (term.1, x term.2)) := by
        change ((projLabelTerms coeff).map (fun term => term.1 • unitValue (x term.2))).sum =
          (((projLabelTerms coeff).map (fun term => (term.1, x term.2))).map
            (fun term => term.1 • unitValue term.2)).sum
        simp only [List.map_map, Function.comp_def]
      _ = _ := (projLeftWeighted a b c d e f de cf t _ _ _).symm
  exact ⟨l, rfl, (projMergedEqIff a b c d e f _ _).1
    (heval.trans (hcollect.trans (he.trans hc.symm)))⟩

end Projection

end FiniteParabolicReplacementProof

open MackeyDiagrams FiniteParabolicReplacementProof

theorem FiniteParabolicSingleDiagramReplacements : (
let finitary := Subgroup.closure {σ : Equiv.Perm Nat | Equiv.Perm.IsSwap σ}
let U := ↥finitary
let blockSym := fun (S : Finset Nat) =>
  MonoidHom.range (Equiv.Perm.ofSubtype (p := fun n : Nat => n ∈ S))
let parabolic := fun (H : Subgroup U) =>
  ∃ (n : Nat) (blocks : Fin n → Finset Nat),
    (∀ i, Finset.Nonempty (blocks i)) ∧
    Pairwise (fun i j => Disjoint (blocks i) (blocks j)) ∧
    Subgroup.map (Subgroup.subtype finitary) H = iSup (fun i => blockSym (blocks i))
let Region := {H : Subgroup U // parabolic H}
let Embedding := MackeyDiagrams.ConjEmbedding (U := U)
let comp := @MackeyDiagrams.ConjEmbedding.comp U _
let up := @MackeyDiagrams.Word.up U _
let down := @MackeyDiagrams.Word.down U _
let tensor := @MackeyDiagrams.Word.tensor U _
let Drawing := fun {K H : Subgroup U} (p q : MackeyDiagrams.Word K H) =>
  MackeyDiagrams.LabelledDrawing Complex p q
let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
let vertical := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
let horizontal := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
let straight := fun {K H : Subgroup U} (p : MackeyDiagrams.Word K H) =>
  ordinary (MackeyDiagrams.Diagram.id p)
let evaluate := fun {K H : Subgroup U} {p q : MackeyDiagrams.Word K H} (drawing : Drawing p q) =>
  MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret drawing)
let onFirstTwo := fun {K H J J' L : Subgroup U}
    {p : MackeyDiagrams.Word K J} {q : MackeyDiagrams.Word J H}
    {p' : MackeyDiagrams.Word K J'} {q' : MackeyDiagrams.Word J' H}
    (crossing : Drawing (tensor p q) (tensor p' q')) (r : MackeyDiagrams.Word H L) =>
  horizontal crossing (straight r)
let onLastTwo := fun {K H J J' L : Subgroup U}
    (p : MackeyDiagrams.Word K H)
    {q : MackeyDiagrams.Word H J} {r : MackeyDiagrams.Word J L}
    {q' : MackeyDiagrams.Word H J'} {r' : MackeyDiagrams.Word J' L}
    (crossing : Drawing (tensor q r) (tensor q' r')) =>
  vertical (ordinary (MackeyDiagrams.Diagram.associate p q r))
    (vertical (horizontal (straight p) crossing)
      (ordinary (MackeyDiagrams.Diagram.unassociate p q' r')))
let stack := fun {K H : Subgroup U} {p q r s : MackeyDiagrams.Word K H}
    (first : Drawing p q) (second : Drawing q r) (third : Drawing r s) =>
  vertical first (vertical second third)
let DotWeights := fun {H K : Subgroup U} (a b : Embedding H K) =>
  MackeyDiagrams.DotLabel Complex a b
let parallel := fun {P Q Q' S : Subgroup U}
    (a : Embedding Q P) (b : Embedding S Q) (a' : Embedding Q' P) (b' : Embedding S Q')
    (label : DotWeights (comp a b) (comp a' b')) =>
  MackeyDiagrams.LabelledDrawing.parallelUp a b a' b' (MackeyDiagrams.DotLabel.terms label)
let ProjectionWeights := fun {K H P L : Subgroup U}
    (α : Embedding K P) (β : Embedding H P) (η : Embedding L K) (θ : Embedding L H) =>
  Finsupp (MackeyDiagrams.ProjectionDot.Mixed α β η θ) Complex
let project := fun {K H P L : Subgroup U}
    (α : Embedding K P) (β : Embedding H P) (η : Embedding L K) (θ : Embedding L H)
    (label : ProjectionWeights α β η θ) =>
  MackeyDiagrams.LabelledDrawing.compactProjection α β η θ
    (List.map (fun term => (label term, term)) (Finset.toList (Finsupp.support label)))
let multiply := fun {K H P L : Subgroup U}
    (α : Embedding K P) (β : Embedding H P) (η : Embedding L K) (θ : Embedding L H)
    (label : DotWeights (comp α η) (comp β θ)) =>
  MackeyDiagrams.LabelledDrawing.mixedMultiplication α β η θ (MackeyDiagrams.DotLabel.terms label)
let Replacements := fun {K H : Subgroup U} {bottom top : MackeyDiagrams.Word K H}
    {Left Right : Type} (leftDiagram : Left → Drawing bottom top)
    (rightDiagram : Right → Drawing bottom top)
    (leftRegion : Left → Subgroup U) (rightRegion : Right → Subgroup U)
    (B B' : Subgroup U) =>
  let leftEval := fun l => evaluate (leftDiagram l)
  let rightEval := fun r => evaluate (rightDiagram r)
  let leftClasses := Setoid.ker leftEval
  let rightClasses := Setoid.ker rightEval
  ∃ (toRight : Left → Right) (toLeft : Right → Left)
    (classes : Equiv (Quotient leftClasses) (Quotient rightClasses)),
    (∀ l : Left, rightRegion (toRight l) = B' ∧
      rightEval (toRight l) = leftEval l ∧
      classes (Quotient.mk leftClasses l) = Quotient.mk rightClasses (toRight l)) ∧
    (∀ r : Right, leftRegion (toLeft r) = B ∧
      leftEval (toLeft r) = rightEval r ∧
      Equiv.symm classes (Quotient.mk rightClasses r) = Quotient.mk leftClasses (toLeft r))
∀ (G A D F C E : Subgroup U),
  parabolic G → parabolic A → parabolic D → parabolic F → parabolic C → parabolic E →
  (∀ (ga : Embedding A G) (ad : Embedding D A) (df : Embedding F D)
      (gc : Embedding C G) (ce : Embedding E C) (ef : Embedding F E),
    let bottom := tensor (tensor (up ga) (up ad)) (up df)
    let top := tensor (tensor (up gc) (up ce)) (up ef)
    let Left := Σ B : Region,
      Σ gb : Embedding B.val G, Σ bd : Embedding D B.val, Σ be : Embedding E B.val,
        DotWeights (comp ga ad) (comp gb bd) ×
        DotWeights (comp bd df) (comp be ef) ×
        DotWeights (comp gb be) (comp gc ce)
    let Right := Σ B' : Region,
      Σ ab' : Embedding B'.val A, Σ cb' : Embedding B'.val C, Σ b'f : Embedding F B'.val,
        DotWeights (comp ad df) (comp ab' b'f) ×
        DotWeights (comp ga ab') (comp gc cb') ×
        DotWeights (comp cb' b'f) (comp ce ef)
    let leftDiagram : Left → Drawing bottom top :=
      fun ⟨_, gb, bd, be, x₁, x₂, x₃⟩ =>
        stack
          (onFirstTwo (parallel ga ad gb bd x₁) (up df))
          (onLastTwo (up gb) (parallel bd df be ef x₂))
          (onFirstTwo (parallel gb be gc ce x₃) (up ef))
    let rightDiagram : Right → Drawing bottom top :=
      fun ⟨_, ab', cb', b'f, y₁, y₂, y₃⟩ =>
        stack
          (onLastTwo (up ga) (parallel ad df ab' b'f y₁))
          (onFirstTwo (parallel ga ab' gc cb' y₂) (up b'f))
          (onLastTwo (up gc) (parallel cb' b'f ce ef y₃))
    Replacements leftDiagram rightDiagram
      (fun l => l.1.val) (fun r => r.1.val) G F) ∧
  (∀ (a : Embedding G A) (b : Embedding D A) (c : Embedding F D)
      (d : Embedding C G) (e : Embedding E C) (f : Embedding E F),
    let bc := comp b c
    let de := comp d e
    let lower := tensor (tensor (down a) (up b)) (up c)
    let upper := tensor (tensor (up d) (up e)) (down f)
    let LeftProjection := Σ B : Region,
      Σ r : Embedding B.val G, Σ s : Embedding B.val D, Σ t : Embedding E B.val,
        ProjectionWeights a b r s × ProjectionWeights s c t f ×
        DotWeights (comp r t) de
    let RightProjection := Σ B' : Region,
      Σ j : Embedding B'.val A, Σ v : Embedding C B'.val, Σ w : Embedding F B'.val,
        DotWeights bc (comp j w) ×
        ProjectionWeights a j d v × ProjectionWeights v w e f
    let leftProjection : LeftProjection → Drawing lower upper :=
      fun ⟨_, r, s, t, x, y, z⟩ =>
        stack
          (onFirstTwo (project a b r s x) (up c))
          (onLastTwo (up r) (project s c t f y))
          (onFirstTwo (parallel r t d e z) (down f))
    let rightProjection : RightProjection → Drawing lower upper :=
      fun ⟨_, j, v, w, ℓ, m, n⟩ =>
        stack
          (onLastTwo (down a) (parallel b c j w ℓ))
          (onFirstTwo (project a j d v m) (up w))
          (onLastTwo (up d) (project v w e f n))
    let LeftMultiplication := Σ B : Region,
      Σ r : Embedding B.val G, Σ s : Embedding B.val D, Σ t : Embedding E B.val,
        DotWeights de (comp r t) ×
        DotWeights (comp s t) (comp c f) ×
        DotWeights (comp a r) (comp b s)
    let RightMultiplication := Σ B' : Region,
      Σ j : Embedding B'.val A, Σ v : Embedding C B'.val, Σ w : Embedding F B'.val,
        DotWeights (comp v e) (comp w f) ×
        DotWeights (comp a d) (comp j v) ×
        DotWeights (comp j w) bc
    let leftMultiplication : LeftMultiplication → Drawing upper lower :=
      fun ⟨_, r, s, t, x, y, z⟩ =>
        stack
          (onFirstTwo (parallel d e r t x) (down f))
          (onLastTwo (up r) (multiply s c t f y))
          (onFirstTwo (multiply a b r s z) (up c))
    let rightMultiplication : RightMultiplication → Drawing upper lower :=
      fun ⟨_, j, v, w, x, y, z⟩ =>
        stack
          (onLastTwo (up d) (multiply v w e f x))
          (onFirstTwo (multiply a j d v y) (up w))
          (onLastTwo (down a) (parallel j w b c z))
    Replacements leftProjection rightProjection
      (fun l => l.1.val) (fun r => r.1.val) E A ∧
    Replacements leftMultiplication rightMultiplication
      (fun l => l.1.val) (fun r => r.1.val) E A)
) :=
(by
  classical
  intro finitary U blockSym parabolic Region Embedding comp up down tensor Drawing ordinary
    vertical horizontal straight evaluate onFirstTwo onLastTwo stack DotWeights parallel
    ProjectionWeights project multiply Replacements G A D F C E hG hA hD hF hC hE
  -- Xiao, § 8.3, archived p. 37 and published 28 November revision p. 39.
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#parabolic-reidemeister-three
  -- Each named replacement preserves the evaluated map. The inverse laws
  -- follow by quotient induction, using both certified evaluation equalities.
  constructor
  · intro ga ad df gc ce ef bottom top Left Right leftDiagram rightDiagram
    -- Lemma 6.1 and Theorem 6.2. The public quotient bijection forgets its
    -- middle groups. Use its multiplier supplier and choose the canonical
    -- G and F witnesses before forming the evaluation quotients.
    obtain ⟨sga, hga, rfl⟩ := represented ga
    obtain ⟨sad, had, rfl⟩ := represented ad
    obtain ⟨sdf, hdf, rfl⟩ := represented df
    obtain ⟨sgc, hgc, rfl⟩ := represented gc
    obtain ⟨sce, hce, rfl⟩ := represented ce
    obtain ⟨sef, hef, rfl⟩ := represented ef
    let ga := ConjEmbedding.ofConjugator sga hga
    let ad := ConjEmbedding.ofConjugator sad had
    let df := ConjEmbedding.ofConjugator sdf hdf
    let gc := ConjEmbedding.ofConjugator sgc hgc
    let ce := ConjEmbedding.ofConjugator sce hce
    let ef := ConjEmbedding.ofConjugator sef hef
    let bottomPair := ga.comp ad
    let topPair := gc.comp ce
    let deBottom := bottomPair.comp df
    let deTop := topPair.comp ef
    let splitBottom : Drawing (up deBottom) bottom :=
      vertical (.trivalent (.splitUp bottomPair df))
        (horizontal (.trivalent (.splitUp ga ad)) (straight (up df)))
    let mergeTop : Drawing top (up deTop) :=
      vertical (horizontal (.trivalent (.mergeUp gc ce)) (straight (up ef)))
        (.trivalent (.mergeUp topPair ef))
    let multiplier (x : Drawing bottom top) : MonoidAlgebra Complex G :=
      MonoidAlgebra.ofCoeff ((evaluate (vertical splitBottom (vertical x mergeTop))).toLinearMap
        (MonoidAlgebra.coeff (1 : MonoidAlgebra Complex G)))
    let leftExpanded : Left → Drawing bottom top :=
      fun ⟨_, gb, bd, be, x, y, z⟩ =>
        stack (onFirstTwo (expandedParallel ga ad gb bd x) (up df))
          (onLastTwo (up gb) (expandedParallel bd df be ef y))
          (onFirstTwo (expandedParallel gb be gc ce z) (up ef))
    let rightExpanded : Right → Drawing bottom top :=
      fun ⟨_, ab, cb, bf, x, y, z⟩ =>
        stack (onLastTwo (up ga) (expandedParallel ad df ab bf x))
          (onFirstTwo (expandedParallel ga ab gc cb y) (up bf))
          (onLastTwo (up gc) (expandedParallel cb bf ce ef z))
    -- The reviewed statement uses the compact crossing. Distribution of
    -- vertical evaluation over the weighted list proves the bridge above.
    have firstEval {K H J J' L : Subgroup U} {p : Word K J} {q : Word J H}
        {p' : Word K J'} {q' : Word J' H}
        {x y : Drawing (tensor p q) (tensor p' q')} (r : Word H L)
        (h : evaluate x = evaluate y) :
        evaluate (onFirstTwo x r) = evaluate (onFirstTwo y r) :=
      horizontalEval h rfl
    have lastEval {K H J J' L : Subgroup U} (p : Word K H)
        {q : Word H J} {r : Word J L} {q' : Word H J'} {r' : Word J' L}
        {x y : Drawing (tensor q r) (tensor q' r')} (h : evaluate x = evaluate y) :
        evaluate (onLastTwo p x) = evaluate (onLastTwo p y) :=
      verticalEval rfl (verticalEval (horizontalEval rfl h) rfl)
    have hLeftEval (l : Left) : evaluate (leftDiagram l) = evaluate (leftExpanded l) := by
      rcases l with ⟨B, gb, bd, be, x, y, z⟩
      exact verticalEval (firstEval (up df) (parallelEval ga ad gb bd x))
        (verticalEval (lastEval (up gb) (parallelEval bd df be ef y))
          (firstEval (up ef) (parallelEval gb be gc ce z)))
    have hRightEval (r : Right) : evaluate (rightDiagram r) = evaluate (rightExpanded r) := by
      rcases r with ⟨B, ab, cb, bf, x, y, z⟩
      exact verticalEval (lastEval (up ga) (parallelEval ad df ab bf x))
        (verticalEval (firstEval (up bf) (parallelEval ga ab gc cb y))
          (lastEval (up gc) (parallelEval cb bf ce ef z)))
    have supplier := ThreeInductionCrossingMultipliers G A D F C E sga sad sdf sgc sce sef
      hga had hdf hgc hce hef
    have evalIff (x y : Drawing bottom top) :
        evaluate x = evaluate y ↔ multiplier x = multiplier y :=
      supplier.2.2.2.1 x y
    let allowed (p : G) :=
      (sga * sad * sdf)⁻¹ * (p : U) * (sgc * sce * sef) ∈ Subgroup.centralizer (F : Set U)
    let along {H K : Subgroup U} (a : Embedding H K) :=
      MonoidAlgebra.mapDomainAlgHom Complex Complex a.toHom
    let dotValue {H K : Subgroup U} {a b : Embedding H K} (x : DotWeights a b) :=
      MonoidAlgebra.ofCoeff (Finsupp.mapDomain Dot.element x)
    let middle (m : MonoidAlgebra Complex G) : DotWeights deBottom deTop :=
      indLiftMultiplier m
    have middleValue (m : MonoidAlgebra Complex G)
        (hm : ∀ p ∈ m.coeff.support, allowed p) : dotValue (middle m) = m := by
      apply indLiftMultiplierValue m
      intro p hp
      exact indEligibleOfCentralizer (fun f => (supplier.1 f).1) (fun f => (supplier.1 f).2)
        p ((supplier.2.2.2.2.1 p).2.mpr (hm p hp))
    have dotIdentity {H K : Subgroup U} (a : Embedding H K) :
        dotValue (DotLabel.identity a) = 1 := indDotValueIdentity a
    let ab := ad.comp df
    let cb := ce.comp ef
    let idF := ConjEmbedding.id F
    let idG := ConjEmbedding.id G
    let buildRight (m : MonoidAlgebra Complex G) : Right :=
      ⟨⟨F, hF⟩, ab, cb, idF, DotLabel.identity ab, middle m, DotLabel.identity cb⟩
    let buildLeft (m : MonoidAlgebra Complex G) : Left :=
      ⟨⟨G, hG⟩, idG, bottomPair, topPair, DotLabel.identity bottomPair, middle m,
        DotLabel.identity topPair⟩
    have hRight (m : MonoidAlgebra Complex G) (hm : ∀ p ∈ m.coeff.support, allowed p) :
        multiplier (rightExpanded (buildRight m)) = m := by
      calc
        _ = along ga (dotValue (DotLabel.identity ab)) * dotValue (middle m) *
              along gc (dotValue (DotLabel.identity cb)) :=
          (supplier.2.2.2.2.2.2 F ab cb idF (DotLabel.identity ab) (middle m) (DotLabel.identity cb)).1
        _ = m := by
          rw [dotIdentity ab, dotIdentity cb, map_one, map_one, one_mul, mul_one,
            middleValue m hm]
    have hLeft (m : MonoidAlgebra Complex G) (hm : ∀ p ∈ m.coeff.support, allowed p) :
        multiplier (leftExpanded (buildLeft m)) = m := by
      calc
        _ = dotValue (DotLabel.identity bottomPair) * along idG (dotValue (middle m)) *
              dotValue (DotLabel.identity topPair) :=
          (supplier.2.2.2.2.2.1 G idG bottomPair topPair (DotLabel.identity bottomPair) (middle m)
            (DotLabel.identity topPair)).1
        _ = m := by
          rw [dotIdentity bottomPair, dotIdentity topPair, one_mul, mul_one, middleValue m hm]
          change MonoidAlgebra.mapDomainAlgHom Complex Complex (MonoidHom.id G) m = m
          simp only [MonoidAlgebra.mapDomainAlgHom_id, AlgHom.id_apply]
    apply quotientOfReplacements (fun l => evaluate (leftDiagram l))
      (fun r => evaluate (rightDiagram r)) (fun l => l.1.val) (fun r => r.1.val) G F
    · intro l
      let m := multiplier (leftExpanded l)
      have hm : ∀ p ∈ m.coeff.support, allowed p := by
        rcases l with ⟨B, gb, bd, be, x, y, z⟩
        exact (supplier.2.2.2.2.2.1 B.val gb bd be x y z).2
      have h := (evalIff (rightExpanded (buildRight m)) (leftExpanded l)).2 (hRight m hm)
      exact ⟨buildRight m, rfl, (hRightEval (buildRight m)).trans (h.trans (hLeftEval l).symm)⟩
    · intro r
      let m := multiplier (rightExpanded r)
      have hm : ∀ p ∈ m.coeff.support, allowed p := by
        rcases r with ⟨B, ab, cb, bf, x, y, z⟩
        exact (supplier.2.2.2.2.2.2 B.val ab cb bf x y z).2
      have h := (evalIff (leftExpanded (buildLeft m)) (rightExpanded r)).2 (hLeft m hm)
      exact ⟨buildLeft m, rfl, (hLeftEval (buildLeft m)).trans (h.trans (hRightEval r).symm)⟩
  · intro a b c d e f bc de lower upper LeftProjection RightProjection leftProjection rightProjection
      LeftMultiplication RightMultiplication leftMultiplication rightMultiplication
    constructor
    · -- The numbered directions of Theorem 6.4 ask for the finite indices
      -- of d(C) and (de)(E) in G. Both follow from the finite block model.
      -- The p-dependent parabolic join is for the fallback single-term
      -- construction. At finite G the supplier gives the common group A.
      have finiteG : Finite G := by
        obtain ⟨n, blocks, _, _, hblocks⟩ := hG
        exact finiteOfBlocks blocks hblocks
      have hd : d.toHom.range.FiniteIndex := Subgroup.finiteIndex_of_finite
      have hde : (d.comp e).toHom.range.FiniteIndex := Subgroup.finiteIndex_of_finite
      apply quotientOfReplacements (fun l => evaluate (leftProjection l))
        (fun r => evaluate (rightProjection r)) (fun l => l.1.val) (fun r => r.1.val) E A
      · rintro ⟨B, r, s, t, x, y, z⟩
        obtain ⟨⟨P, j, v, w, l, m, n⟩, hP, h⟩ :=
          projectionForward a b c d e f hd ⟨B.val, r, s, t, x, y, z⟩
        change P = A at hP
        subst P
        exact ⟨⟨⟨A, hA⟩, j, v, w, l, m, n⟩, rfl, h⟩
      · rintro ⟨B, j, v, w, l, m, n⟩
        obtain ⟨⟨P, r, s, t, x, y, z⟩, hP, h⟩ :=
          projectionBackward a b c d e f hde ⟨B.val, j, v, w, l, m, n⟩
        change P = E at hP
        subst P
        exact ⟨⟨⟨E, hE⟩, r, s, t, x, y, z⟩, rfl, h⟩
    · -- Cases 3 and 4 of Theorem 6.5. Use the public normalization
      -- statements and the checked fixed-region realizers. Equality of the
      -- multipliers is converted to equality before the boundary merges.
      have supplier := ReplacementForTwoMultiplications a b c d e f
      apply quotientOfReplacements (fun l => evaluate (leftMultiplication l))
        (fun r => evaluate (rightMultiplication r)) (fun l => l.1.val) (fun r => r.1.val) E A
      · rintro ⟨B, r, s, t, x, y, z⟩
        obtain ⟨M, hM, hleft⟩ := supplier.1 ⟨B.val, r, s, t, x, y, z⟩
        obtain ⟨X, Y, Z, hright⟩ := multRealizeRight a b c d e f M hM
        exact ⟨⟨⟨A, hA⟩, ConjEmbedding.id A, a.comp d, b.comp c, X, Y, Z⟩,
          rfl, (multEvalEqIff a b c d e f hright hleft).2 rfl⟩
      · rintro ⟨B, j, v, w, x, y, z⟩
        obtain ⟨M, hM, hright⟩ := supplier.2.1 ⟨B.val, j, v, w, x, y, z⟩
        obtain ⟨X, Y, Z, hleft⟩ := multRealizeLeft a b c d e f M hM
        exact ⟨⟨⟨E, hE⟩, d.comp e, c.comp f, ConjEmbedding.id E, X, Y, Z⟩,
          rfl, (multEvalEqIff a b c d e f hleft hright).2 rfl⟩
)

#print axioms FiniteParabolicSingleDiagramReplacements
