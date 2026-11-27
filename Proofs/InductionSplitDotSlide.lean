import MackeyDiagrams
import Proofs.GroupElementDotCriterion
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.InductionMergeDotSlide

set_option maxHeartbeats 2000000

theorem InductionSplitDotSlide : (
∀ {U : Type*} [Group U] (K H G : Subgroup U) (γ α β : U)
    (hγ : ∀ h : H, γ * (h : U) * γ⁻¹ ∈ G)
    (hα : ∀ k : K, α * (k : U) * α⁻¹ ∈ H)
    (hβ : ∀ k : K, β * (k : U) * β⁻¹ ∈ H)
    (he : α * β⁻¹ ∈ H),
  let g := MackeyDiagrams.ConjEmbedding.ofConjugator γ hγ
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  let e : MackeyDiagrams.Dot a b :=
    MackeyDiagrams.Dot.ofRepresentatives α β (fun _ => rfl) (fun _ => rfl) he
  let rightDot := MackeyDiagrams.DotLabel.upDrawing (Finsupp.single e (1 : Complex))
  let split := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
    (MackeyDiagrams.TrivalentVertex.splitUp g a)
  (∀ (γ' : U)
      (hγ' : ∀ h : H, γ' * (h : U) * (γ')⁻¹ ∈ G)
      (hd : γ * (γ')⁻¹ ∈ G),
    let g' := MackeyDiagrams.ConjEmbedding.ofConjugator γ' hγ'
    let d : MackeyDiagrams.Dot g g' :=
      MackeyDiagrams.Dot.ofRepresentatives γ γ' (fun _ => rfl) (fun _ => rfl) hd
    let lifted : MackeyDiagrams.Dot
        (MackeyDiagrams.ConjEmbedding.comp g a)
        (MackeyDiagrams.ConjEmbedding.comp g' a) :=
      ⟨MackeyDiagrams.Dot.element d,
        fun k => MackeyDiagrams.Dot.intertwines d
          (MackeyDiagrams.ConjEmbedding.toHom a k)⟩
    let merged := MackeyDiagrams.Dot.vertical lifted (MackeyDiagrams.Dot.whisker g' e)
    let left := MackeyDiagrams.LabelledDrawing.vertical split
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.DotLabel.upDrawing (Finsupp.single d (1 : Complex))) rightDot)
    let right := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.DotLabel.upDrawing (Finsupp.single merged (1 : Complex)))
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp g' b))
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret left) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret right)) ∧
  (let left := MackeyDiagrams.LabelledDrawing.vertical split
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up g))) rightDot)
    let right := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.DotLabel.upDrawing
        (Finsupp.single (MackeyDiagrams.Dot.whisker g e) (1 : Complex)))
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp g b))
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret left) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret right))
) :=
(by
  intro U group K H G γ α β hγ hα hβ he g a b e rightDot split
  -- Xiao, Proposition 3.1, (3.2), and the induction-split drawing in § 3.2.
  -- The archived source/mackey-bimodules.pdf has (3.2) on p. 8 and the drawing
  -- on p. 9. The revised published PDF has them on pp. 10 and 11, respectively.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- The source proves (3.1) by the multiplication formula and the intertwining
  -- identity. Apply the compiled InductionMergeDotSlide to the same conjugators
  -- and membership hypotheses. For (3.2), compose with the source and target
  -- splits using the two inverse equations in MackeyDiagrams.Parallel.
  -- These equations apply at the given bracketed words over Complex.
  have cancelMerge
      (sourceOuter targetOuter : MackeyDiagrams.ConjEmbedding H G)
      (sourceInner targetInner : MackeyDiagrams.ConjEmbedding K H)
      (legs : MackeyDiagrams.Biset.Hom Complex
        ((MackeyDiagrams.Word.up sourceOuter).tensor (.up sourceInner)).basis
        ((MackeyDiagrams.Word.up targetOuter).tensor (.up targetInner)).basis)
      (stem : MackeyDiagrams.Biset.Hom Complex
        (MackeyDiagrams.Word.up (sourceOuter.comp sourceInner)).basis
        (MackeyDiagrams.Word.up (targetOuter.comp targetInner)).basis)
      (square : legs.vertical (MackeyDiagrams.Diagram.mergeUp targetOuter targetInner).eval =
        (MackeyDiagrams.Diagram.mergeUp sourceOuter sourceInner).eval.vertical stem) :
      (MackeyDiagrams.Diagram.splitUp sourceOuter sourceInner).eval.vertical legs =
        stem.vertical (MackeyDiagrams.Diagram.splitUp targetOuter targetInner).eval := by
    let splitSource := (MackeyDiagrams.Diagram.splitUp (R := Complex) sourceOuter sourceInner).eval
    let mergeSource := (MackeyDiagrams.Diagram.mergeUp (R := Complex) sourceOuter sourceInner).eval
    let mergeTarget := (MackeyDiagrams.Diagram.mergeUp (R := Complex) targetOuter targetInner).eval
    let splitTarget := (MackeyDiagrams.Diagram.splitUp (R := Complex) targetOuter targetInner).eval
    have sourceInverse : splitSource.vertical mergeSource = MackeyDiagrams.Biset.Hom.id _ :=
      MackeyDiagrams.Diagram.splitUp_mergeUp sourceOuter sourceInner
    have targetInverse : mergeTarget.vertical splitTarget = MackeyDiagrams.Biset.Hom.id _ :=
      MackeyDiagrams.Diagram.mergeUp_splitUp targetOuter targetInner
    change splitSource.vertical legs = stem.vertical splitTarget
    calc
      splitSource.vertical legs =
          ((splitSource.vertical legs).vertical mergeTarget).vertical splitTarget := by
        rw [MackeyDiagrams.Biset.Hom.vertical_assoc, targetInverse,
          MackeyDiagrams.Biset.Hom.vertical_id]
      _ = (splitSource.vertical (mergeSource.vertical stem)).vertical splitTarget := by
        rw [MackeyDiagrams.Biset.Hom.vertical_assoc splitSource legs, square]
      _ = stem.vertical splitTarget := by
        rw [← MackeyDiagrams.Biset.Hom.vertical_assoc splitSource mergeSource,
          sourceInverse, MackeyDiagrams.Biset.Hom.id_vertical]
  obtain ⟨mergeBoth, mergeRight⟩ := InductionMergeDotSlide K H G γ α β hγ hα hβ he
  constructor
  · intro γ' hγ' hd g' d lifted merged left right
    exact cancelMerge g g' a b
      ((MackeyDiagrams.DotLabel.upDrawing (Finsupp.single d (1 : Complex))).interpret.eval.horizontal
        rightDot.interpret.eval)
      (MackeyDiagrams.DotLabel.upDrawing (Finsupp.single merged (1 : Complex))).interpret.eval
      (mergeBoth γ' hγ' hd)
  · intro left right
    -- In the second slide of § 3.2, the outer leg is unmarked. Use the
    -- separate right-leg merge square and its ordinary identity strand.
    exact cancelMerge g g a b
      ((MackeyDiagrams.Diagram.id (R := Complex) (.up g)).eval.horizontal rightDot.interpret.eval)
      (MackeyDiagrams.DotLabel.upDrawing
        (Finsupp.single (MackeyDiagrams.Dot.whisker g e) (1 : Complex))).interpret.eval
      mergeRight)
