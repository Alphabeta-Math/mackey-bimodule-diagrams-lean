import MackeyDiagrams
import Proofs.GroupElementDotCriterion
import Proofs.InductionRestrictionMergesAndSplits

set_option maxHeartbeats 2000000

theorem RestrictionMergeDotSlide : (∀ {U : Type*} [Group U] (K H G : Subgroup U) (γ α β : U)
    (hγ : ∀ h : H, γ * (h : U) * γ⁻¹ ∈ G)
    (hα : ∀ k : K, α * (k : U) * α⁻¹ ∈ H)
    (hβ : ∀ k : K, β * (k : U) * β⁻¹ ∈ H)
    (he : α * β⁻¹ ∈ H),
  let g := MackeyDiagrams.ConjEmbedding.ofConjugator γ hγ
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  let e : MackeyDiagrams.Dot a b :=
    MackeyDiagrams.Dot.ofRepresentatives α β (fun _ => rfl) (fun _ => rfl) he
  let innerDot := MackeyDiagrams.DotLabel.downDrawing (Finsupp.single e (1 : Complex))
  let merge := MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
    (MackeyDiagrams.TrivalentVertex.mergeDown g a)
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
      (MackeyDiagrams.LabelledDrawing.horizontal innerDot
        (MackeyDiagrams.DotLabel.downDrawing (Finsupp.single d (1 : Complex))))
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeDown g' b))
    let right := MackeyDiagrams.LabelledDrawing.vertical merge
      (MackeyDiagrams.DotLabel.downDrawing (Finsupp.single merged (1 : Complex)))
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret left) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret right)) ∧
  (let left := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.horizontal innerDot
        (MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.down g))))
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeDown g b))
    let right := MackeyDiagrams.LabelledDrawing.vertical merge
      (MackeyDiagrams.DotLabel.downDrawing
        (Finsupp.single (MackeyDiagrams.Dot.whisker g e) (1 : Complex)))
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret left) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret right))) :=
(by
  classical
  intro U inst K H G γ α β hγ hα hβ he
  -- Proposition 3.1, equation (3.3), and the third drawing in §3.2.
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#prop:curl
  -- The published PDF matches the local article-revision copy. The local
  -- source copy is a different PDF revision with the same equation and TikZ.
  -- Dot.ofRepresentatives uses he and hd to put the relative conjugators
  -- in the target subgroups and verifies the required intertwining.
  let g := MackeyDiagrams.ConjEmbedding.ofConjugator γ hγ
  let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
  let e : MackeyDiagrams.Dot a b :=
    MackeyDiagrams.Dot.ofRepresentatives α β (fun _ => rfl) (fun _ => rfl) he
  let down := fun {A B : Subgroup U} {p q : MackeyDiagrams.ConjEmbedding A B}
      (t : MackeyDiagrams.Dot p q) =>
    MackeyDiagrams.DotLabel.downDrawing (Finsupp.single t (1 : Complex))
  let merge := fun (outer : MackeyDiagrams.ConjEmbedding H G)
      (inner : MackeyDiagrams.ConjEmbedding K H) =>
    MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
      (MackeyDiagrams.TrivalentVertex.mergeDown outer inner)
  -- The route's downDrawing_basis computes on coefficient 1. Its companion
  -- eval_downDrawing and eval_linearDownDot_apply give the singleton formula
  -- at arbitrary coefficient, including after the merge.
  have dotBasis {A B : Subgroup U} {p q : MackeyDiagrams.ConjEmbedding A B}
      (t : MackeyDiagrams.Dot p q) (x : B) (r : Complex) :
      (down t).interpret.eval.toLinearMap (Finsupp.single x r) =
        Finsupp.single (t.element⁻¹ * x) r := by
    dsimp only [down]
    rw [MackeyDiagrams.DotLabel.eval_downDrawing,
      MackeyDiagrams.Diagram.eval_linearDownDot_apply,
      MackeyDiagrams.freeLift_single, one_smul, MackeyDiagrams.Diagram.eval_downDot_single]
  have slide (g' : MackeyDiagrams.ConjEmbedding H G) (d : MackeyDiagrams.Dot g g') :
      let lifted : MackeyDiagrams.Dot (g.comp a) (g'.comp a) :=
        ⟨d.element, fun k => d.intertwines (a.toHom k)⟩
      let merged := lifted.vertical (MackeyDiagrams.Dot.whisker g' e)
      (((down e).horizontal (down d)).vertical (merge g' b)).interpret.eval =
        ((merge g a).vertical (down merged)).interpret.eval := by
    dsimp only
    apply MackeyDiagrams.Biset.Hom.ext
    apply Finsupp.lhom_ext
    intro z r
    refine Quotient.inductionOn z (fun xy => ?_)
    rcases xy with ⟨x, y⟩
    change H at x
    change G at y
    let lifted : MackeyDiagrams.Dot (g.comp a) (g'.comp a) :=
      ⟨d.element, fun k => d.intertwines (a.toHom k)⟩
    let merged := lifted.vertical (MackeyDiagrams.Dot.whisker g' e)
    let input := Finsupp.single ((MackeyDiagrams.Biset.restriction a).pair
      (MackeyDiagrams.Biset.restriction g) x y) r
    -- Follow the simple-tensor calculation for (3.1) in Proposition 3.1.
    -- For (3.3), represent simple tensors by balanced pairs in the reversed
    -- restriction order and use Diagram.eval_mergeDown_single. The registered
    -- dot and merge endpoints give the corresponding group-algebra formulas.
    -- The shared drawing interpreter composes evaluated maps, so use
    -- Biset.Hom.horizontal_single, the map formula underlying eval_horizontal_single.
    change (MackeyDiagrams.Diagram.mergeDown g' b).eval.toLinearMap
        (((down e).interpret.eval.horizontal (down d).interpret.eval).toLinearMap input) =
      (down merged).interpret.eval.toLinearMap
        ((MackeyDiagrams.Diagram.mergeDown g a).eval.toLinearMap input)
    dsimp only [input]
    rw [MackeyDiagrams.Biset.Hom.horizontal_single, dotBasis, dotBasis,
      MackeyDiagrams.Biset.pairLinear_single, one_mul, Finsupp.smul_single, smul_eq_mul,
      mul_one, MackeyDiagrams.Diagram.eval_mergeDown_single,
      MackeyDiagrams.Diagram.eval_mergeDown_single, dotBasis]
    -- The downward dots invert the group elements termwise. The outer dot's
    -- inverse intertwiner moves d⁻¹ past g'(x) in that order.
    -- Inverting the composite dot gives g'(e⁻¹) * d⁻¹, the multiplier of (3.3).
    have commute : g'.toHom x * d.element⁻¹ = d.element⁻¹ * g.toHom x :=
      d.inverse.intertwines x
    congr 1
    change g'.toHom (e.element⁻¹ * x) * (d.element⁻¹ * y) =
      (d.element * g'.toHom e.element)⁻¹ * (g.toHom x * y)
    simp only [map_mul, mul_inv_rev, map_inv, mul_assoc]
    rw [← mul_assoc (g'.toHom x) d.element⁻¹ y, commute, mul_assoc]
  change (∀ (γ' : U) (hγ' : ∀ h : H, γ' * (h : U) * (γ')⁻¹ ∈ G)
      (hd : γ * (γ')⁻¹ ∈ G), _) ∧ _
  constructor
  · intro γ' hγ' hd
    exact slide (MackeyDiagrams.ConjEmbedding.ofConjugator γ' hγ')
      (MackeyDiagrams.Dot.ofRepresentatives γ γ' (fun _ => rfl) (fun _ => rfl) hd)
  · -- In the third drawing of §3.2 the outer leg is unmarked. Specialize to
    -- d = 1 and use the downward identity-dot evaluation theorem on that leg.
    have hs := slide g (MackeyDiagrams.Dot.id g)
    dsimp only at hs
    have hmerged :
        MackeyDiagrams.Dot.vertical
          (⟨(MackeyDiagrams.Dot.id g).element,
            fun k => (MackeyDiagrams.Dot.id g).intertwines (a.toHom k)⟩ :
            MackeyDiagrams.Dot (g.comp a) (g.comp a))
          (MackeyDiagrams.Dot.whisker g e) = MackeyDiagrams.Dot.whisker g e := by
      apply MackeyDiagrams.Dot.ext
      exact one_mul _
    rw [hmerged] at hs
    change ((down e).interpret.eval.horizontal
        ((down (MackeyDiagrams.Dot.id g)).interpret.eval)).vertical
          (merge g b).interpret.eval =
      (merge g a).interpret.eval.vertical
        (down (MackeyDiagrams.Dot.whisker g e)).interpret.eval at hs
    rw [show (down (MackeyDiagrams.Dot.id g)).interpret.eval =
        MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Word.down g).basis from
      MackeyDiagrams.DotLabel.downDrawing_identity g] at hs
    exact hs)
