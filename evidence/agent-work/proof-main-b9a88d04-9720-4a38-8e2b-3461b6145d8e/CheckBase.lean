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
