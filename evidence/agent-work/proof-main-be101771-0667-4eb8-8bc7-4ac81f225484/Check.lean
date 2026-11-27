import MackeyDiagrams
import Proofs.GroupElementDotCriterion
import Proofs.FiniteIndexReverseAdjunction
import Proofs.RightUpReidemeisterCurl
import Proofs.InductionMergeDotSlide
import Proofs.InductionSplitDotSlide
import Proofs.RestrictionMergeDotSlide
import Proofs.RestrictionSplitDotSlide

set_option maxHeartbeats 2000000

universe u

namespace RightCurlAndDotSlideSupport

open MackeyDiagrams

variable {U : Type u} [Group U] {K H G : Subgroup U}

private def liftDot {a b : ConjEmbedding H G} (loop : ConjEmbedding K H) (d : Dot a b) :
    Dot (a.comp loop) (b.comp loop) :=
  ⟨d.element, fun k => d.intertwines (loop.toHom k)⟩

private theorem singleton_eval {a b : ConjEmbedding H G} (d : Dot a b) :
    (DotLabel.upDrawing (Finsupp.single d (1 : Complex))).interpret.eval =
      (Diagram.upDot (R := Complex) d).eval := by
  rw [DotLabel.eval_upDrawing]
  apply Diagram.eval_ext
  intro x r
  rw [Diagram.eval_linearUpDot_apply, freeLift_single, one_smul]

private theorem insert_slide {a b : ConjEmbedding H G} (d : Dot a b) :
    ((Diagram.insertRightUnit (R := Complex) (.up a)).vertical
      ((Diagram.upDot d).horizontal (.id (.empty H)))).eval =
      ((Diagram.upDot (R := Complex) d).vertical (.insertRightUnit (.up b))).eval := by
  apply Diagram.eval_ext
  intro x r
  change G at x
  change ((Diagram.upDot (R := Complex) d).horizontal (.id (.empty H))).eval.toLinearMap
      ((Diagram.insertRightUnit (R := Complex) (.up a)).eval.toLinearMap (Finsupp.single x r)) =
    (Diagram.insertRightUnit (R := Complex) (.up b)).eval.toLinearMap
      ((Diagram.upDot (R := Complex) d).eval.toLinearMap (Finsupp.single x r))
  have insert (p : ConjEmbedding H G) (z : G) :
      (Diagram.insertRightUnit (R := Complex) (.up p)).eval.toLinearMap (Finsupp.single z r) =
        Finsupp.single ((Word.up p).basis.pair (Word.empty H).basis z 1) r :=
    by
      change (Biset.insertRightUnit (Word.up p).basis Complex).toLinearMap _ = _
      rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single]
  rw [insert a x, Diagram.eval_horizontal_single, Diagram.eval_upDot_single,
    Diagram.eval_id_apply, Biset.pairLinear_single, one_mul,
    Diagram.eval_upDot_single (R := Complex) d x r, insert]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]

private theorem unassociate_slide {a b : ConjEmbedding H G} (d : Dot a b)
    (loop : ConjEmbedding K H) :
    let p := Word.up a
    let p' := Word.up b
    let q := Word.up loop
    let t := Word.down loop
    let dot := Diagram.upDot (R := Complex) d
    (((dot.horizontal (.id (q.tensor t))).vertical (.unassociate p' q t))).eval =
      ((Diagram.unassociate p q t).vertical ((dot.horizontal (.id q)).horizontal (.id t))).eval := by
  intro p p' q t dot
  apply Diagram.eval_ext
  intro w r
  refine Quotient.inductionOn w (fun ⟨x, yz⟩ => ?_)
  refine Quotient.inductionOn yz (fun ⟨y, z⟩ => ?_)
  change G at x
  change H at y z
  change (Diagram.unassociate (R := Complex) p' q t).eval.toLinearMap
      ((dot.horizontal (.id (q.tensor t))).eval.toLinearMap
        (Finsupp.single (p.basis.pair (q.basis.tensor t.basis) x (q.basis.pair t.basis y z)) r)) =
    ((dot.horizontal (.id q)).horizontal (.id t)).eval.toLinearMap
      ((Diagram.unassociate (R := Complex) p q t).eval.toLinearMap
        (Finsupp.single (p.basis.pair (q.basis.tensor t.basis) x (q.basis.pair t.basis y z)) r))
  rw [Diagram.eval_horizontal_single, Diagram.eval_unassociate_single,
    Diagram.eval_horizontal_single, Diagram.eval_horizontal_single]
  rw [show dot = Diagram.upDot (R := Complex) d from rfl,
    Diagram.eval_upDot_single (R := Complex) d x 1,
    Diagram.eval_id_apply (q.tensor t), Diagram.eval_id_apply q, Diagram.eval_id_apply t]
  rw [Biset.pairLinear_single, one_mul, Biset.pairLinear_single, one_mul, one_smul,
    Biset.pairLinear_single, one_mul]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  exact Diagram.eval_unassociate_single p' q t (x * d.element) y z r

-- This is the basis identity in Xiao's proof of (3.1), with the loop leg
-- unchanged. The intertwining equation holds for every element of H.
private theorem merge_slide {a b : ConjEmbedding H G} (d : Dot a b)
    (loop : ConjEmbedding K H) :
    (((Diagram.upDot (R := Complex) d).horizontal (.id (.up loop))).vertical
      (.mergeUp b loop)).eval =
      ((Diagram.mergeUp (R := Complex) a loop).vertical (.upDot (liftDot loop d))).eval := by
  apply Diagram.eval_ext
  intro w r
  refine Quotient.inductionOn w (fun ⟨x, y⟩ => ?_)
  change G at x
  change H at y
  change (Diagram.mergeUp (R := Complex) b loop).eval.toLinearMap
      (((Diagram.upDot d).horizontal (.id (.up loop))).eval.toLinearMap
        (Finsupp.single ((Word.up a).basis.pair (Word.up loop).basis x y) r)) =
    (Diagram.upDot (R := Complex) (liftDot loop d)).eval.toLinearMap
      ((Diagram.mergeUp a loop).eval.toLinearMap
        (Finsupp.single ((Word.up a).basis.pair (Word.up loop).basis x y) r))
  rw [Diagram.eval_horizontal_single, Diagram.eval_upDot_single, Diagram.eval_id_apply,
    Biset.pairLinear_single, one_mul]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [Diagram.eval_mergeUp_single, Diagram.eval_mergeUp_single, Diagram.eval_upDot_single]
  change Finsupp.single ((x * d.element) * b.toHom y) r =
    Finsupp.single ((x * a.toHom y) * d.element) r
  rw [mul_assoc, ← d.intertwines y, ← mul_assoc]

private theorem paste {L M : Type u} [Group L] [Group M]
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Biset L M}
    {f₁ : Biset.Hom Complex X₀ X₁} {f₂ : Biset.Hom Complex X₁ X₂}
    {g₁ : Biset.Hom Complex Y₀ Y₁} {g₂ : Biset.Hom Complex Y₁ Y₂}
    {d₀ : Biset.Hom Complex X₀ Y₀} {d₁ : Biset.Hom Complex X₁ Y₁}
    {d₂ : Biset.Hom Complex X₂ Y₂}
    (h₁ : d₀.vertical g₁ = f₁.vertical d₁) (h₂ : d₁.vertical g₂ = f₂.vertical d₂) :
    d₀.vertical (g₁.vertical g₂) = (f₁.vertical f₂).vertical d₂ := by
  rw [← Biset.Hom.vertical_assoc d₀, h₁, Biset.Hom.vertical_assoc f₁, h₂,
    ← Biset.Hom.vertical_assoc f₁]

private theorem tensor_square {L M N : Type u} [Group L] [Group M] [Group N]
    {X₀ X₁ X₂ X₃ : Biset L M} (Z : Biset M N)
    {f₁ : Biset.Hom Complex X₀ X₁} {f₂ : Biset.Hom Complex X₁ X₃}
    {g₁ : Biset.Hom Complex X₀ X₂} {g₂ : Biset.Hom Complex X₂ X₃}
    (h : f₁.vertical f₂ = g₁.vertical g₂) :
    (f₁.horizontal (Biset.Hom.id Z)).vertical (f₂.horizontal (Biset.Hom.id Z)) =
      (g₁.horizontal (Biset.Hom.id Z)).vertical (g₂.horizontal (Biset.Hom.id Z)) := by
  rw [Biset.Hom.horizontal_vertical, Biset.Hom.horizontal_vertical, h]

-- Expand the lower junction into unit, cup, reassociation and merge. The
-- cup stays on the same loop and its finite-fiber sum is carried by interchange.
private theorem lower_slide {a b : ConjEmbedding H G} (d : Dot a b)
    (loop : ConjEmbedding K H) (finite : loop.toHom.range.FiniteIndex) :
    let lower := fun p : ConjEmbedding H G =>
      LabelledDrawing.trivalent (R := Complex) (TrivalentVertex.upToUpDown p loop finite)
    let mark := fun {L M : Subgroup U} {p q : ConjEmbedding L M} (e : Dot p q) =>
      DotLabel.upDrawing (Finsupp.single e (1 : Complex))
    let loopIdentity := LabelledDrawing.ordinary (Diagram.id (R := Complex) (Word.down loop))
    (mark d).interpret.eval.vertical (lower b).interpret.eval =
      (lower a).interpret.eval.vertical
        ((mark (liftDot loop d)).horizontal loopIdentity).interpret.eval := by
  intro lower mark loopIdentity
  change (DotLabel.upDrawing (Finsupp.single d (1 : Complex))).interpret.eval.vertical
      (lower b).interpret.eval =
    (lower a).interpret.eval.vertical
      ((DotLabel.upDrawing (Finsupp.single (liftDot loop d) (1 : Complex))).interpret.eval.horizontal
        (Biset.Hom.id (Word.down loop).basis))
  rw [singleton_eval d, singleton_eval (liftDot loop d)]
  let t := (Word.down loop).basis
  let cup := Diagram.reverseCup (R := Complex) loop finite
  have cup_slide := Biset.Hom.horizontal_disjoint (Diagram.upDot (R := Complex) d).eval cup.eval
  have merge_square :
      ((Diagram.upDot (R := Complex) d).horizontal (.id (.up loop))).eval.vertical
        (Diagram.mergeUp (R := Complex) b loop).eval =
      (Diagram.mergeUp (R := Complex) a loop).eval.vertical
        (Diagram.upDot (R := Complex) (liftDot loop d)).eval :=
    merge_slide d loop
  have squares := paste (insert_slide d).symm (paste cup_slide
    (paste (unassociate_slide d loop) (tensor_square t merge_square)))
  exact squares

end RightCurlAndDotSlideSupport


theorem RightCurlAndDotSlide : (
∀ {U : Type u} [Group U] (K H G : Subgroup U),
  let liftOuterDot :=
    fun {a b : MackeyDiagrams.ConjEmbedding H G}
      (inner : MackeyDiagrams.ConjEmbedding K H) (d : MackeyDiagrams.Dot a b) =>
      (⟨MackeyDiagrams.Dot.element d,
        fun k => MackeyDiagrams.Dot.intertwines d
          (MackeyDiagrams.ConjEmbedding.toHom inner k)⟩ :
        MackeyDiagrams.Dot (MackeyDiagrams.ConjEmbedding.comp a inner)
          (MackeyDiagrams.ConjEmbedding.comp b inner))
  (∀ (δ α : U)
      (hδ : ∀ k : K, δ * (k : U) * δ⁻¹ ∈ H)
      (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G),
    let loop := MackeyDiagrams.ConjEmbedding.ofConjugator δ hδ
    let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
    let S := MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom loop)
    ∀ finite : Subgroup.FiniteIndex S,
      let lower := fun p : MackeyDiagrams.ConjEmbedding H G =>
        MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
          (MackeyDiagrams.TrivalentVertex.upToUpDown p loop finite)
      let upper := fun p : MackeyDiagrams.ConjEmbedding H G =>
        MackeyDiagrams.LabelledDrawing.trivalent (R := Complex)
          (MackeyDiagrams.TrivalentVertex.upDownToUp p loop)
      let curl := fun p : MackeyDiagrams.ConjEmbedding H G =>
        MackeyDiagrams.LabelledDrawing.vertical (lower p) (upper p)
      let straight := MackeyDiagrams.LabelledDrawing.ordinary
        (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.up a))
      let scaledStraight :=
        MackeyDiagrams.LabelledDrawing.scale (Subgroup.index S : Complex) straight
      ((∀ k : K, (MackeyDiagrams.ConjEmbedding.toHom loop k : U) = (k : U)) →
        Subgroup.index S = Subgroup.index (Subgroup.comap (Subgroup.subtype H) K)) ∧
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret (curl a)) =
        MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret scaledStraight) ∧
      (∀ (β : U)
          (hβ : ∀ h : H, β * (h : U) * β⁻¹ ∈ G)
          (hd : α * β⁻¹ ∈ G),
        let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
        let d : MackeyDiagrams.Dot a b :=
          MackeyDiagrams.Dot.ofRepresentatives α β (fun _ => rfl) (fun _ => rfl) hd
        let dot := MackeyDiagrams.DotLabel.upDrawing (Finsupp.single d (1 : Complex))
        let loopIdentity := MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.id (R := Complex) (MackeyDiagrams.Word.down loop))
        let insideDot := MackeyDiagrams.DotLabel.upDrawing
          (Finsupp.single (liftOuterDot loop d) (1 : Complex))
        let below := MackeyDiagrams.LabelledDrawing.vertical dot (curl b)
        let inside := MackeyDiagrams.LabelledDrawing.vertical (lower a)
          (MackeyDiagrams.LabelledDrawing.vertical
            (MackeyDiagrams.LabelledDrawing.horizontal insideDot loopIdentity) (upper b))
        let above := MackeyDiagrams.LabelledDrawing.vertical (curl a) dot
        let scaledDot := MackeyDiagrams.LabelledDrawing.scale (Subgroup.index S : Complex) dot
        MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret below) =
          MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret scaledDot) ∧
        MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret inside) =
          MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret scaledDot) ∧
        MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret above) =
          MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret scaledDot))) ∧
  (∀ (γ γ' α β : U)
      (hγ : ∀ h : H, γ * (h : U) * γ⁻¹ ∈ G)
      (hγ' : ∀ h : H, γ' * (h : U) * (γ')⁻¹ ∈ G)
      (hα : ∀ k : K, α * (k : U) * α⁻¹ ∈ H)
      (hβ : ∀ k : K, β * (k : U) * β⁻¹ ∈ H)
      (hd : γ * (γ')⁻¹ ∈ G) (he : α * β⁻¹ ∈ H),
    let g := MackeyDiagrams.ConjEmbedding.ofConjugator γ hγ
    let g' := MackeyDiagrams.ConjEmbedding.ofConjugator γ' hγ'
    let a := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
    let b := MackeyDiagrams.ConjEmbedding.ofConjugator β hβ
    let d : MackeyDiagrams.Dot g g' :=
      MackeyDiagrams.Dot.ofRepresentatives γ γ' (fun _ => rfl) (fun _ => rfl) hd
    let e : MackeyDiagrams.Dot a b :=
      MackeyDiagrams.Dot.ofRepresentatives α β (fun _ => rfl) (fun _ => rfl) he
    let merged := MackeyDiagrams.Dot.vertical (liftOuterDot a d)
      (MackeyDiagrams.Dot.whisker g' e)
    let dLabel := Finsupp.single d (1 : Complex)
    let eLabel := Finsupp.single e (1 : Complex)
    let mergedLabel := Finsupp.single merged (1 : Complex)
    let legDotsUp := MackeyDiagrams.LabelledDrawing.horizontal
      (MackeyDiagrams.DotLabel.upDrawing dLabel) (MackeyDiagrams.DotLabel.upDrawing eLabel)
    let legDotsDown := MackeyDiagrams.LabelledDrawing.horizontal
      (MackeyDiagrams.DotLabel.downDrawing eLabel) (MackeyDiagrams.DotLabel.downDrawing dLabel)
    let mergedUp := MackeyDiagrams.DotLabel.upDrawing mergedLabel
    let mergedDown := MackeyDiagrams.DotLabel.downDrawing mergedLabel
    let upMergeL := MackeyDiagrams.LabelledDrawing.vertical legDotsUp
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp g' b))
    let upMergeR := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeUp g a)) mergedUp
    let upSplitL := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp g a)) legDotsUp
    let upSplitR := MackeyDiagrams.LabelledDrawing.vertical mergedUp
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitUp g' b))
    let downMergeL := MackeyDiagrams.LabelledDrawing.vertical legDotsDown
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeDown g' b))
    let downMergeR := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.mergeDown g a)) mergedDown
    let downSplitL := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitDown g a)) legDotsDown
    let downSplitR := MackeyDiagrams.LabelledDrawing.vertical mergedDown
      (MackeyDiagrams.LabelledDrawing.trivalent (MackeyDiagrams.TrivalentVertex.splitDown g' b))
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret upMergeL) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret upMergeR) ∧
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret upSplitL) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret upSplitR) ∧
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret downMergeL) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret downMergeR) ∧
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret downSplitL) =
      MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret downSplitR))
) :=
(by
  intro U group K H G liftOuterDot
  constructor
  · intro δ α hδ hα loop a S finite lower upper curl straight scaledStraight
    -- Xiao, Proposition 3.1 and its unnumbered curl proof, archived
    -- original source/mackey-bimodules.pdf, pp. 7–8, and the revised
    -- published PDF, pp. 9–10, matching article-revision/mackey-bimodules.pdf.
    -- https://getcurious.cc/downloads/mackey-bimodules.pdf
    -- The Alphabeta Math portal presents the same unnumbered curl proof.
    -- The registered scalar supplier counts the cap fiber by the subgroup
    -- index and evaluates the two trivalent junctions at this boundary.
    -- The reverse cup uses the same finite-index image in every curl.
    have undotted := RightUpReidemeisterCurl K H G δ α hδ hα finite
    refine ⟨?_, undotted, ?_⟩
    · intro hInclusion
      have hRange : S = Subgroup.comap (Subgroup.subtype H) K := by
        ext h
        change (∃ k : K, loop.toHom k = h) ↔ (h : U) ∈ K
        constructor
        · rintro ⟨k, rfl⟩
          simpa only [hInclusion k] using k.property
        · intro hk
          exact ⟨⟨h, hk⟩, Subtype.ext (hInclusion ⟨h, hk⟩)⟩
      exact congrArg Subgroup.index hRange
    · intro β hβ hd b d dot loopIdentity insideDot below inside above scaledDot
      -- The typed dot supplies α*(t⁻¹) d = d β*(t⁻¹) for the paper's
      -- coset calculation. Use this equality at the merge, then use
      -- interchange to carry the full reverse cup with its fixed loop.
      -- This gives the same map without choosing a transversal again.
      -- The three marks are coefficient-one singleton labels as specified
      -- by the proposition. The proof compares their maps at fixed endpoints.
      have undottedB := RightUpReidemeisterCurl K H G δ β hδ hβ finite
      have hBelow :
          (MackeyDiagrams.LabelledDrawing.interpret below).eval =
            (MackeyDiagrams.LabelledDrawing.interpret scaledDot).eval := by
        change dot.interpret.eval.vertical (curl b).interpret.eval =
          dot.interpret.eval.scale (S.index : Complex)
        rw [show (curl b).interpret.eval =
          (MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Word.up b).basis).scale
            (S.index : Complex) from undottedB,
          MackeyDiagrams.Biset.Hom.vertical_scale_right, MackeyDiagrams.Biset.Hom.vertical_id]
      refine ⟨hBelow, ?_, ?_⟩
      · have slide := RightCurlAndDotSlideSupport.lower_slide d loop finite
        change dot.interpret.eval.vertical (lower b).interpret.eval =
          (lower a).interpret.eval.vertical
            (insideDot.horizontal loopIdentity).interpret.eval at slide
        change (lower a).interpret.eval.vertical
            ((insideDot.horizontal loopIdentity).interpret.eval.vertical (upper b).interpret.eval) = _
        rw [← MackeyDiagrams.Biset.Hom.vertical_assoc, ← slide,
          MackeyDiagrams.Biset.Hom.vertical_assoc]
        exact hBelow
      · change (curl a).interpret.eval.vertical dot.interpret.eval =
          dot.interpret.eval.scale (S.index : Complex)
        rw [show (curl a).interpret.eval =
          (MackeyDiagrams.Biset.Hom.id (MackeyDiagrams.Word.up a).basis).scale
            (S.index : Complex) from undotted,
          MackeyDiagrams.Biset.Hom.vertical_scale_left, MackeyDiagrams.Biset.Hom.id_vertical]
  · intro γ γ' α β hγ hγ' hα hβ hd he g g' a b d e merged dLabel eLabel mergedLabel
      legDotsUp legDotsDown mergedUp mergedDown upMergeL upMergeR upSplitL upSplitR
      downMergeL downMergeR downSplitL downSplitR
    -- Xiao (3.1)–(3.4). Each supplier's first conjunct is the two-leg
    -- equality with the same conjugators, admissible singleton labels and
    -- merged element d · γ'(e). No finite-index condition enters these slides.
    exact ⟨(InductionMergeDotSlide K H G γ α β hγ hα hβ he).1 γ' hγ' hd,
      (InductionSplitDotSlide K H G γ α β hγ hα hβ he).1 γ' hγ' hd,
      (RestrictionMergeDotSlide K H G γ α β hγ hα hβ he).1 γ' hγ' hd,
      (RestrictionSplitDotSlide K H G γ α β hγ hα hβ he).1 γ' hγ' hd⟩
)

#print axioms RightCurlAndDotSlide
