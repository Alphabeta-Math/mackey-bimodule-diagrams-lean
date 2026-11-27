import MackeyDiagrams
import Proofs.MovingMergeDotBackToBranch

set_option maxHeartbeats 2000000

namespace RightInputDotSlideProof

open MackeyDiagrams

variable {U : Type*} [Group U] {K H G : Subgroup U}

/-- Evaluate the merged-strand mark on the balanced tensor of the two units. -/
private theorem trunkUnit (γ : ConjEmbedding H G) (α : ConjEmbedding K H)
    (d : Dot (γ.comp α) (γ.comp α)) :
    ((LabelledDrawing.trivalent (TrivalentVertex.mergeUp γ α)).vertical
      (DotLabel.upDrawing (Finsupp.single d (1 : Complex)))).interpret.eval.toLinearMap
      (Finsupp.single ((Biset.induction γ).pair (Biset.induction α) 1 1) 1) =
      Finsupp.single d.element 1 := by
  change (DotLabel.upDrawing (Finsupp.single d (1 : Complex))).interpret.eval.toLinearMap
    ((Diagram.mergeUp γ α).eval.toLinearMap
      (Finsupp.single ((Biset.induction γ).pair (Biset.induction α) 1 1) 1)) = _
  rw [Diagram.eval_mergeUp_single, map_one, one_mul, DotLabel.eval_upDrawing,
    Diagram.eval_linearUpDot_apply, freeLift_single, one_smul,
    Diagram.eval_upDot_single, one_mul]

/-- The right-input drawing pushes each eligible term through the outer embedding. -/
private theorem branchUnit (γ : ConjEmbedding H G) (α β : ConjEmbedding K H)
    (label : DotLabel Complex α β) :
    (((LabelledDrawing.ordinary (Diagram.id (Word.up γ))).horizontal
      (DotLabel.upDrawing label)).vertical
      (LabelledDrawing.trivalent (TrivalentVertex.mergeUp γ β))).interpret.eval.toLinearMap
      (Finsupp.single ((Biset.induction γ).pair (Biset.induction α) 1 1) 1) =
      Finsupp.mapDomain (fun term => γ.toHom term.element) label := by
  classical
  let outer := Biset.induction γ
  let inner := Biset.induction β
  let merge := (Diagram.mergeUp (R := Complex) γ β).eval.toLinearMap
  let dot := (DotLabel.upDrawing label).interpret.eval
  let straight := (Diagram.id (R := Complex) (Word.up γ)).eval
  let pairAtOne := Biset.pairLinear Complex outer inner (Finsupp.single 1 1)
  change merge ((straight.horizontal dot).toLinearMap
    (Finsupp.single (outer.pair (Biset.induction α) 1 1) 1)) = _
  rw [Biset.Hom.horizontal_single, one_smul]
  change merge (pairAtOne (dot.toLinearMap (Finsupp.single 1 1))) = _
  rw [show dot.toLinearMap (Finsupp.single 1 1) =
      (label.support.toList.map (fun d => label d • Finsupp.single d.element 1)).sum by
    simpa only [dot, one_mul] using DotLabel.upDrawing_basis label (1 : H)]
  change (merge.comp pairAtOne)
      ((label.support.toList.map (fun d => label d • Finsupp.single d.element 1)).sum) = _
  rw [map_list_sum, List.map_map, ← List.sum_toFinset _ label.support.nodup_toList,
    Finset.toList_toFinset, Finsupp.mapDomain, Finsupp.sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  change merge (pairAtOne (label d • Finsupp.single d.element 1)) = _
  rw [map_smul, map_smul]
  dsimp only [pairAtOne, merge, outer, inner]
  rw [Biset.pairLinear_single, mul_one, Diagram.eval_mergeUp_single, one_mul,
    Finsupp.smul_single, smul_eq_mul, mul_one]

end RightInputDotSlideProof

theorem RightInputDotSlideObstruction : (
let U := Equiv.Perm (Fin 4)
let G : Subgroup U := ⊤
let H := MulAction.stabilizer U (3 : Fin 4)
let K := H ⊓ MulAction.stabilizer U (2 : Fin 4)
let inG : ∀ x : U, x ∈ G := fun _ => Subgroup.mem_top _
let α : MackeyDiagrams.ConjEmbedding K H :=
  MackeyDiagrams.ConjEmbedding.ofConjugator 1 (by
    intro k
    simpa only [one_mul, inv_one, mul_one] using (inf_le_left : K ≤ H) k.property)
let γ : MackeyDiagrams.ConjEmbedding H G :=
  MackeyDiagrams.ConjEmbedding.ofConjugator 1 (fun _ => inG _)
let target := MackeyDiagrams.ConjEmbedding.comp γ α
let g : G := ⟨Equiv.swap (2 : Fin 4) 3, inG _⟩
let gLabel : MackeyDiagrams.ConjEmbedding K G :=
  MackeyDiagrams.ConjEmbedding.ofConjugator (g : U) (fun _ => inG _)
let input := MackeyDiagrams.Word.tensor (MackeyDiagrams.Word.up γ)
  (MackeyDiagrams.Word.up α)
let output := MackeyDiagrams.Word.up target
let unitTensor := Finsupp.single
  (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction γ)
    (MackeyDiagrams.Biset.induction α) 1 1) (1 : Complex)
(g : U) ∈ Subgroup.centralizer (K : Set U) ∧ gLabel = target ∧ (g : U) ∉ H ∧
  ∃ d : MackeyDiagrams.Dot target target, MackeyDiagrams.Dot.element d = g ∧
    let B : MackeyDiagrams.LabelledDrawing Complex input output :=
      MackeyDiagrams.LabelledDrawing.vertical
        (MackeyDiagrams.LabelledDrawing.trivalent
          (MackeyDiagrams.TrivalentVertex.mergeUp γ α))
        (MackeyDiagrams.DotLabel.upDrawing
          (Finsupp.single d (1 : Complex) : MackeyDiagrams.DotLabel Complex target target))
    let evalB := MackeyDiagrams.ScopedDiagram.eval
      (MackeyDiagrams.LabelledDrawing.interpret B)
    MackeyDiagrams.Biset.Hom.toLinearMap evalB unitTensor = Finsupp.single g 1 ∧
      ∀ (β : MackeyDiagrams.ConjEmbedding K H) (label : MackeyDiagrams.DotLabel Complex α β)
        (h : MackeyDiagrams.ConjEmbedding.comp γ β = target),
        let A : MackeyDiagrams.LabelledDrawing Complex input
            (MackeyDiagrams.Word.up (MackeyDiagrams.ConjEmbedding.comp γ β)) :=
          MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.horizontal
              (MackeyDiagrams.LabelledDrawing.ordinary
                (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up γ)))
              (MackeyDiagrams.DotLabel.upDrawing label))
            (MackeyDiagrams.LabelledDrawing.trivalent
              (MackeyDiagrams.TrivalentVertex.mergeUp γ β))
        let evalA := MackeyDiagrams.ScopedDiagram.eval
          (MackeyDiagrams.LabelledDrawing.interpret
            (Eq.ndrec (motive := fun out =>
              MackeyDiagrams.LabelledDrawing Complex input (MackeyDiagrams.Word.up out)) A h))
        let imageA := MackeyDiagrams.Biset.Hom.toLinearMap evalA unitTensor
        imageA = Finsupp.mapDomain
          (fun term => MackeyDiagrams.ConjEmbedding.toHom γ (MackeyDiagrams.Dot.element term))
          label ∧
        (∀ x : G, x ∈ Finsupp.support imageA → (x : U) ∈ H) ∧
        evalA ≠ evalB
) :=
(by
  intro U G H K inG α γ target g gLabel input output unitTensor
  -- Ian Xiao, §3.3, Example 3.2 (ex:dot-slide-obstruction), archived source PDF
  -- p. 10 and revised published PDF p. 12.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf#page=12
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#ex:dot-slide-obstruction
  -- The saved citation's byte-for-byte comparison predates the revision.
  -- The two pages agree on the example. The article page provides the example
  -- without a separate numbered proof, so the proof follows its claims in order.
  -- Lean uses zero-based points, so (3 4) is the swap of 2 and 3.
  -- The historical checked connection proves the same centralizer and boundary
  -- facts for Diagram. Recheck them here and use the current LabelledDrawing
  -- interpretation for both evaluations.
  have hcomm (k : K) : (k : U) * (g : U) = (g : U) * (k : U) := by
    have h3 : (k : U) (3 : Fin 4) = 3 := MulAction.mem_stabilizer_iff.mp k.property.1
    have h2 : (k : U) (2 : Fin 4) = 2 := MulAction.mem_stabilizer_iff.mp k.property.2
    change (k : U) * Equiv.swap 2 3 = Equiv.swap 2 3 * (k : U)
    calc
      (k : U) * Equiv.swap 2 3 = ((k : U) * Equiv.swap 2 3 * (k : U)⁻¹) * (k : U) :=
        (mul_inv_cancel_right _ _).symm
      _ = Equiv.swap 2 3 * (k : U) := by
        rw [← Equiv.swap_apply_apply, h2, h3]
  have hcentr : (g : U) ∈ Subgroup.centralizer (K : Set U) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => hcomm ⟨k, hk⟩
  have hOutside : (g : U) ∉ H := by
    intro hg
    have hfix : Equiv.swap (2 : Fin 4) 3 3 = 3 := MulAction.mem_stabilizer_iff.mp hg
    rw [Equiv.swap_apply_right] at hfix
    exact (by decide : (2 : Fin 4) ≠ 3) hfix
  have hγ (x : H) : (γ.toHom x : U) = (x : U) := by
    dsimp only [γ]
    simp only [MackeyDiagrams.ConjEmbedding.ofConjugator_apply, one_mul, inv_one, mul_one]
  have htarget (k : K) : (target.toHom k : U) = (k : U) := by
    change (γ.toHom (α.toHom k) : U) = (k : U)
    rw [hγ]
    dsimp only [α]
    simp only [MackeyDiagrams.ConjEmbedding.ofConjugator_apply, one_mul, inv_one, mul_one]
  let d : MackeyDiagrams.Dot target target :=
    ⟨g, fun k => Subtype.ext (by
      change (target.toHom k : U) * (g : U) = (g : U) * (target.toHom k : U)
      rw [htarget]
      exact hcomm k)⟩
  refine ⟨hcentr, ?_, hOutside, d, rfl, ?_⟩
  · let incl : MackeyDiagrams.ConjEmbedding K G :=
      MackeyDiagrams.ConjEmbedding.ofConjugator 1 (fun _ => inG _)
    have hsame : incl = gLabel :=
      (MackeyDiagrams.ConjEmbedding.ofConjugator_eq_iff _ _ _ _).mpr
        (by simpa only [inv_one, one_mul] using hcentr)
    rw [← hsame]
    apply MackeyDiagrams.ConjEmbedding.ext
    apply MonoidHom.ext
    intro k
    apply Subtype.ext
    rw [htarget]
    dsimp only [incl]
    simp only [MackeyDiagrams.ConjEmbedding.ofConjugator_apply, one_mul, inv_one, mul_one]
  · dsimp only
    have hB := RightInputDotSlideProof.trunkUnit γ α d
    refine ⟨hB, ?_⟩
    intro β label h
    -- The induction merge pictured in §3.2 for (3.1) gives the two shapes
    -- in Proposition 3.2. Example 3.2 fixes the outer embedding. Cancel it
    -- before reducing the dependent transport of the labelled drawing.
    have hβ : β = α := MackeyDiagrams.Diagram.mergeUp_rightEmbedding_eq γ h
    subst β
    -- The paper places the right-input value in H for a group-element dot.
    -- For the owner's finite linear labels its image is supported in H.
    -- MovingMergeDotBackToBranch and the historical connection treat singleton
    -- marks. The retained weightedS4DotSlide proves inequality for weighted lists.
    -- Compute the exact Finsupp image here before comparing coefficients.
    have hA := RightInputDotSlideProof.branchUnit γ α α label
    have hSupport (x : G)
        (hx : x ∈ (Finsupp.mapDomain (fun term => γ.toHom term.element) label).support) :
        (x : U) ∈ H := by
      classical
      obtain ⟨term, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hx)
      rw [hγ]
      exact term.element.property
    refine ⟨hA, ?_, ?_⟩
    · rw [hA]
      exact hSupport
    · intro heq
      have hAtUnits := congrArg
        (fun f => MackeyDiagrams.Biset.Hom.toLinearMap f unitTensor) heq
      rw [hA, hB] at hAtUnits
      have hzero : Finsupp.mapDomain (fun term => γ.toHom term.element) label g = 0 := by
        by_contra h
        exact hOutside (hSupport g (Finsupp.mem_support_iff.mpr h))
      have hCoeff := DFunLike.congr_fun hAtUnits g
      change _ = Finsupp.single g (1 : Complex) g at hCoeff
      rw [hzero, Finsupp.single_eq_same] at hCoeff
      exact zero_ne_one hCoeff)
