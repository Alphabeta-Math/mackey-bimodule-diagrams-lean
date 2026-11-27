import MackeyDiagrams
import Proofs.GroupElementDotCriterion
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 2000000

theorem InductionMergeDotSlide : (∀ {U : Type*} [Group U] (K H G : Subgroup U) (γ α β : U)
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
  let merge := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
    (MackeyDiagrams.TrivalentVertex.mergeUp g a)
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
    let left := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.DotLabel.upDrawing (Finsupp.single d (1 : Complex))) rightDot)
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp g' b))
    let right := MackeyDiagrams.LabelledDrawing.vertical merge
      (MackeyDiagrams.DotLabel.upDrawing (Finsupp.single merged (1 : Complex)))
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret left) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret right)) ∧
  (let left := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up g))) rightDot)
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp g b))
    let right := MackeyDiagrams.LabelledDrawing.vertical merge
      (MackeyDiagrams.DotLabel.upDrawing
        (Finsupp.single (MackeyDiagrams.Dot.whisker g e) (1 : Complex)))
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret left) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret right))) :=
(by
  intro U group K H G γ α β hγ hα hβ he g a b e rightDot merge
  -- Xiao, Proposition 3.1, eq. (3.1), and the first slide diagram in § 3.2.
  -- The current published PDF matches article-revision/mackey-bimodules.pdf.
  -- The equation, calculation and TikZ diagram agree with the original source/.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- The historical checked connection (InductionMergeDotSlide-35669a6fda70c55531a695d34dfb2ab3)
  -- uses ordinary Diagram syntax. Recheck its basis argument here with the current
  -- imports, then identify only the evaluations of the coefficient-one labels.
  -- No numbered Alphabeta proof is recorded for this endpoint.
  -- GroupElementDotCriterion and InductionRestrictionMergesAndSplits give
  -- the corresponding group-algebra formulas. The route's eval_upDot_single
  -- and eval_mergeUp_single give their basis versions directly at these words.
  have singletonEval {L M : Subgroup U} {p q : MackeyDiagrams.ConjEmbedding L M}
      (t : MackeyDiagrams.Dot p q) :
      (MackeyDiagrams.DotLabel.upDrawing (Finsupp.single t (1 : Complex))).interpret.eval =
        (MackeyDiagrams.Diagram.upDot (R := Complex) t).eval := by
    rw [MackeyDiagrams.DotLabel.eval_upDrawing]
    apply MackeyDiagrams.Diagram.eval_ext
    intro z r
    rw [MackeyDiagrams.Diagram.eval_linearUpDot_apply,
      MackeyDiagrams.freeLift_single, one_smul]
  constructor
  · intro γ' hγ' hd g' d lifted merged left right
    have both :
        (((MackeyDiagrams.Diagram.upDot (R := Complex) d).horizontal
          (.upDot e)).vertical (.mergeUp g' b)).eval =
          ((MackeyDiagrams.Diagram.mergeUp (R := Complex) g a).vertical
            (.upDot merged)).eval := by
      apply MackeyDiagrams.Diagram.eval_ext
      intro z r
      refine Quotient.inductionOn z (fun xy => ?_)
      rcases xy with ⟨x, y⟩
      change G at x
      change H at y
      change (((MackeyDiagrams.Diagram.upDot (R := Complex) d).horizontal
          (.upDot e)).vertical (.mergeUp g' b)).eval.toLinearMap
          (Finsupp.single ((MackeyDiagrams.Word.up g).basis.pair
            (MackeyDiagrams.Word.up a).basis x y) r) =
        ((MackeyDiagrams.Diagram.mergeUp (R := Complex) g a).vertical
          (.upDot merged)).eval.toLinearMap
          (Finsupp.single ((MackeyDiagrams.Word.up g).basis.pair
            (MackeyDiagrams.Word.up a).basis x y) r)
      -- First equality in the paper's proof of (3.1): right multiplication
      -- on the two inputs followed by multiplication through the outer embedding.
      rw [MackeyDiagrams.Diagram.eval_vertical_apply,
        MackeyDiagrams.Diagram.eval_vertical_apply,
        MackeyDiagrams.Diagram.eval_horizontal_single,
        MackeyDiagrams.Diagram.eval_upDot_single,
        MackeyDiagrams.Diagram.eval_upDot_single,
        MackeyDiagrams.Biset.pairLinear_single, one_mul]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [MackeyDiagrams.Diagram.eval_mergeUp_single,
        MackeyDiagrams.Diagram.eval_mergeUp_single,
        MackeyDiagrams.Diagram.eval_upDot_single]
      congr 1
      -- Second equality: the dot eligibility equation moves d across g'(y).
      change (x * d.element) * g'.toHom (y * e.element) =
        (x * g.toHom y) * (d.element * g'.toHom e.element)
      rw [map_mul, ← mul_assoc (x * d.element), mul_assoc x d.element,
        ← d.intertwines y]
      simp only [mul_assoc]
    change
      ((MackeyDiagrams.DotLabel.upDrawing (Finsupp.single d (1 : Complex))).interpret.eval.horizontal
        rightDot.interpret.eval).vertical
        (MackeyDiagrams.Diagram.mergeUp (R := Complex) g' b).eval =
      (MackeyDiagrams.Diagram.mergeUp (R := Complex) g a).eval.vertical
        (MackeyDiagrams.DotLabel.upDrawing (Finsupp.single merged (1 : Complex))).interpret.eval
    rw [show rightDot = MackeyDiagrams.DotLabel.upDrawing (Finsupp.single e (1 : Complex)) from rfl,
      singletonEval d, singletonEval e, singletonEval merged]
    exact both
  · -- The rendered slide in § 3.2 has a genuinely unmarked left input.
    have inner := MackeyDiagrams.Diagram.mergeUp_slide_right (R := Complex) g e
    intro left right
    change
      ((MackeyDiagrams.Diagram.id (R := Complex) (.up g)).eval.horizontal
        rightDot.interpret.eval).vertical
        (MackeyDiagrams.Diagram.mergeUp (R := Complex) g b).eval =
      (MackeyDiagrams.Diagram.mergeUp (R := Complex) g a).eval.vertical
        (MackeyDiagrams.DotLabel.upDrawing
          (Finsupp.single (MackeyDiagrams.Dot.whisker g e) (1 : Complex))).interpret.eval
    rw [show rightDot = MackeyDiagrams.DotLabel.upDrawing (Finsupp.single e (1 : Complex)) from rfl,
      singletonEval e, singletonEval (MackeyDiagrams.Dot.whisker g e)]
    exact inner)
