import MackeyDiagrams
import Proofs.GroupElementDotCriterion
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.RestrictionMergeDotSlide

set_option maxHeartbeats 2000000

theorem RestrictionSplitDotSlide : (
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
  let legDot := MackeyDiagrams.DotLabel.downDrawing (Finsupp.single e (1 : Complex))
  let split := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
    (MackeyDiagrams.TrivalentVertex.splitDown g a)
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
      (MackeyDiagrams.LabelledDrawing.horizontal legDot
        (MackeyDiagrams.DotLabel.downDrawing (Finsupp.single d (1 : Complex))))
    let right := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.DotLabel.downDrawing (Finsupp.single merged (1 : Complex)))
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitDown g' b))
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret left) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret right)) ∧
  (let left := MackeyDiagrams.LabelledDrawing.vertical split
      (MackeyDiagrams.LabelledDrawing.horizontal legDot
        (MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.down g))))
    let right := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.DotLabel.downDrawing
        (Finsupp.single (MackeyDiagrams.Dot.whisker g e) (1 : Complex)))
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitDown g b))
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret left) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret right))
) :=
(by
  intro U inst K H G γ α β hγ hα hβ he
  -- Proposition 3.1, (3.3) and (3.4), and the fourth drawing of §3.2.
  -- The archived original PDF (source/) has (3.4) on p. 8 and the
  -- fourth drawing on p. 9. The revised published PDF (article-revision/)
  -- has them on pp. 10 and 11 respectively. The two editions agree here.
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#prop:curl
  -- The proof of (3.1) computes on simple tensors. Here the checked
  -- restriction merge square supplies its downward counterpart (3.3).
  -- The dots satisfy their intertwining conditions by Dot.ofRepresentatives
  -- using he and hd for the two subgroup memberships. This is the representative
  -- case of GroupElementDotCriterion, with intertwining carried by the Dot type.
  -- RestrictionMergeDotSlide supplies both evaluated squares in tensor order
  -- H then G, with merged multiplier γ'(e⁻¹)d⁻¹, where γ' acts by conjugation.
  have mergeSquares := RestrictionMergeDotSlide K H G γ α β hγ hα hβ he
  -- Derive (3.4) by composing (3.3) with the source and target splits.
  -- The source split followed by merge is identity on the composite strand.
  -- The target merge followed by split is identity on the two-strand word.
  -- These are the last two clauses of InductionRestrictionMergesAndSplits,
  -- which uses Diagram.mergeDown_splitDown and Diagram.splitDown_mergeDown.
  -- The drawing interpreter reduces the trivalent vertices to these maps
  -- and vertical stacking to Biset.Hom.vertical.
  have splitSquare {X Y W Z : MackeyDiagrams.Biset K G}
      (merge : MackeyDiagrams.Biset.Hom Complex X Y)
      (split : MackeyDiagrams.Biset.Hom Complex Y X)
      (merge' : MackeyDiagrams.Biset.Hom Complex W Z)
      (split' : MackeyDiagrams.Biset.Hom Complex Z W)
      (legs : MackeyDiagrams.Biset.Hom Complex X W)
      (merged : MackeyDiagrams.Biset.Hom Complex Y Z)
      (sourceInverse : split.vertical merge = MackeyDiagrams.Biset.Hom.id Y)
      (targetInverse : merge'.vertical split' = MackeyDiagrams.Biset.Hom.id W)
      (mergeSquare : legs.vertical merge' = merge.vertical merged) :
      split.vertical legs = merged.vertical split' := by
    calc
      split.vertical legs = split.vertical ((legs.vertical merge').vertical split') := by
        rw [MackeyDiagrams.Biset.Hom.vertical_assoc legs merge' split', targetInverse,
          MackeyDiagrams.Biset.Hom.vertical_id]
      _ = split.vertical ((merge.vertical merged).vertical split') := by rw [mergeSquare]
      _ = (split.vertical merge).vertical (merged.vertical split') := by
        simp only [MackeyDiagrams.Biset.Hom.vertical_assoc]
      _ = merged.vertical split' := by
        rw [sourceInverse, MackeyDiagrams.Biset.Hom.id_vertical]
  let g := MackeyDiagrams.ConjEmbedding.ofConjugator γ hγ
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  obtain ⟨_, _, _, _, _, _, sourceInverse⟩ :=
    InductionRestrictionMergesAndSplits K H G γ α hγ hα
  change (∀ (γ' : U) (hγ' : ∀ h : H, γ' * (h : U) * (γ')⁻¹ ∈ G)
      (hd : γ * (γ')⁻¹ ∈ G), _) ∧ _
  constructor
  · intro γ' hγ' hd
    let g' := MackeyDiagrams.ConjEmbedding.ofConjugator γ' hγ'
    obtain ⟨_, _, _, _, _, targetInverse, _⟩ :=
      InductionRestrictionMergesAndSplits K H G γ' β hγ' hβ
    exact splitSquare (MackeyDiagrams.Diagram.mergeDown g a).eval
      (MackeyDiagrams.Diagram.splitDown g a).eval
      (MackeyDiagrams.Diagram.mergeDown g' b).eval
      (MackeyDiagrams.Diagram.splitDown g' b).eval
      _ _ sourceInverse targetInverse (mergeSquares.1 γ' hγ' hd)
  · -- The fourth drawing in §3.2 has an unmarked γ leg (d = 1).
    -- Use the corresponding merge square with that leg already undotted.
    obtain ⟨_, _, _, _, _, targetInverse, _⟩ :=
      InductionRestrictionMergesAndSplits K H G γ β hγ hβ
    exact splitSquare (MackeyDiagrams.Diagram.mergeDown g a).eval
      (MackeyDiagrams.Diagram.splitDown g a).eval
      (MackeyDiagrams.Diagram.mergeDown g b).eval
      (MackeyDiagrams.Diagram.splitDown g b).eval
      _ _ sourceInverse targetInverse mergeSquares.2)
