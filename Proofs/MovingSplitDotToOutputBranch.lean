import MackeyDiagrams
import Proofs.InductionSplitDotSlide
import Proofs.RestrictionSplitDotSlide

set_option maxHeartbeats 2000000

namespace MovingSplitDotProof

open MackeyDiagrams

variable {U : Type*} [Group U] {K H G : Subgroup U}

private noncomputable abbrev up {A B : Subgroup U} {a b : ConjEmbedding A B} (d : Dot a b) :=
  DotLabel.upDrawing (Finsupp.single d (1 : Complex))

private noncomputable abbrev down {A B : Subgroup U} {a b : ConjEmbedding A B} (d : Dot a b) :=
  DotLabel.downDrawing (Finsupp.single d (1 : Complex))

private theorem upSingle {a b : ConjEmbedding K G} (d : Dot a b) (x : G) (r : Complex) :
    (up d).interpret.eval.toLinearMap (Finsupp.single x r) =
      Finsupp.single (x * d.element) r := by
  dsimp only [up]
  rw [DotLabel.eval_upDrawing, Diagram.eval_linearUpDot_apply, freeLift_single, one_smul,
    Diagram.eval_upDot_single]

private theorem downSingle {a b : ConjEmbedding K G} (d : Dot a b) (x : G) (r : Complex) :
    (down d).interpret.eval.toLinearMap (Finsupp.single x r) =
      Finsupp.single (d.element⁻¹ * x) r := by
  dsimp only [down]
  rw [DotLabel.eval_downDrawing, Diagram.eval_linearDownDot_apply, freeLift_single, one_smul,
    Diagram.eval_downDot_single]

-- An embedding changes the biset action. Its up and down carriers are both G.
private theorem castUp {p q : ConjEmbedding K G} (h : p = q) {w : Word G K}
    (d : LabelledDrawing Complex (.up p) w) :
    (show LabelledDrawing Complex (.up q) w from h ▸ d).interpret.eval.toLinearMap =
      d.interpret.eval.toLinearMap := by
  cases h
  rfl

private theorem castDown {p q : ConjEmbedding K G} (h : p = q) {w : Word K G}
    (d : LabelledDrawing Complex (.down p) w) :
    (show LabelledDrawing Complex (.down q) w from h ▸ d).interpret.eval.toLinearMap =
      d.interpret.eval.toLinearMap := by
  cases h
  rfl

private theorem imageCoeff {ι : Type*} (outer : ConjEmbedding H G) (index : ι → H)
    (label : ι →₀ Complex) (q : G) (outside : q ∉ outer.toHom.range) :
    (Finsupp.mapDomain (fun i => outer.toHom (index i)) label) q = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨i, hi⟩
  exact outside ⟨index i, hi⟩

private theorem mapLabel {ι : Type*} (label : ι →₀ Complex) (index : ι → H)
    (target : H → G) (f : (H →₀ Complex) →ₗ[Complex] G →₀ Complex)
    (basis : ∀ y, f (Finsupp.single y 1) = Finsupp.single (target y) 1) :
    f ((label.support.toList.map fun i => label i • Finsupp.single (index i) 1).sum) =
      Finsupp.mapDomain (fun i => target (index i)) label := by
  classical
  rw [map_list_sum, List.map_map, ← List.sum_toFinset _ label.support.nodup_toList,
    Finset.toList_toFinset, Finsupp.mapDomain, Finsupp.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  change f (label i • Finsupp.single (index i) 1) = _
  rw [map_smul, basis, Finsupp.smul_single, smul_eq_mul, mul_one]

private theorem rightUpUnit (outer : ConjEmbedding H G) (a b : ConjEmbedding K H)
    (label : DotLabel Complex a b) :
    (Diagram.mergeUp (R := Complex) outer b).eval.toLinearMap
      (((Diagram.id (R := Complex) (.up outer)).eval.horizontal
          (DotLabel.upDrawing label).interpret.eval).toLinearMap
        ((Diagram.splitUp (R := Complex) outer a).eval.toLinearMap (Finsupp.single 1 1))) =
      Finsupp.mapDomain (fun d => outer.toHom d.element) label := by
  rw [Diagram.eval_splitUp_single, Biset.Hom.horizontal_single, one_smul]
  let pairAtOne := Biset.pairLinear Complex (Biset.induction outer) (Biset.induction b)
    (Finsupp.single 1 1)
  let merge := (Diagram.mergeUp (R := Complex) outer b).eval.toLinearMap
  change merge (pairAtOne ((DotLabel.upDrawing label).interpret.eval.toLinearMap
    (Finsupp.single 1 1))) = _
  rw [DotLabel.upDrawing_basis]
  simp only [one_mul]
  change (merge.comp pairAtOne) _ = _
  apply mapLabel label (fun d => d.element) outer.toHom
  intro y
  change merge (pairAtOne (Finsupp.single y 1)) = _
  dsimp only [merge, pairAtOne]
  rw [Biset.pairLinear_single, one_mul, Diagram.eval_mergeUp_single, one_mul]

private theorem rightDownUnit (outer : ConjEmbedding H G) (a b : ConjEmbedding K H)
    (label : DotLabel Complex a b) :
    (Diagram.mergeDown (R := Complex) outer b).eval.toLinearMap
      (((DotLabel.downDrawing label).interpret.eval.horizontal
          (Diagram.id (R := Complex) (.down outer)).eval).toLinearMap
        ((Diagram.splitDown (R := Complex) outer a).eval.toLinearMap (Finsupp.single 1 1))) =
      Finsupp.mapDomain (fun d => outer.toHom d.element⁻¹) label := by
  rw [Diagram.eval_splitDown_single, Biset.Hom.horizontal_single, one_smul]
  let pairAtOne := (Biset.pairLinear Complex (Biset.restriction b) (Biset.restriction outer)).flip
    (Finsupp.single 1 1)
  let merge := (Diagram.mergeDown (R := Complex) outer b).eval.toLinearMap
  change merge (pairAtOne ((DotLabel.downDrawing label).interpret.eval.toLinearMap
    (Finsupp.single 1 1))) = _
  rw [DotLabel.downDrawing_basis]
  simp only [mul_one]
  change (merge.comp pairAtOne) _ = _
  apply mapLabel label (fun d => d.element⁻¹) outer.toHom
  intro y
  change merge (pairAtOne (Finsupp.single y 1)) = _
  dsimp only [merge, pairAtOne, LinearMap.flip_apply]
  rw [Biset.pairLinear_single, one_mul, Diagram.eval_mergeDown_single, mul_one]

private theorem rightUpNecessary (outer : ConjEmbedding H G) (a b : ConjEmbedding K H)
    {p : ConjEmbedding K G} (d : Dot p (outer.comp b)) (label : DotLabel Complex a b)
    (eq : ((up d).interpret.eval.vertical (Diagram.splitUp outer b).eval).toLinearMap =
      ((Diagram.splitUp outer a).eval.vertical
        ((Diagram.id (.up outer)).eval.horizontal (DotLabel.upDrawing label).interpret.eval)
        ).toLinearMap) :
    d.element ∈ outer.toHom.range := by
  let merge := (Diagram.mergeUp (R := Complex) outer b).eval.toLinearMap
  have h := congrArg (fun f => merge (f (Finsupp.single 1 1))) eq
  change merge ((Diagram.splitUp (R := Complex) outer b).eval.toLinearMap
      ((up d).interpret.eval.toLinearMap (Finsupp.single 1 1))) =
    merge (((Diagram.id (.up outer)).eval.horizontal (DotLabel.upDrawing label).interpret.eval).toLinearMap
      ((Diagram.splitUp (R := Complex) outer a).eval.toLinearMap (Finsupp.single 1 1))) at h
  rw [upSingle, one_mul, rightUpUnit outer a b label] at h
  have cancel := congrArg (fun f => f.toLinearMap (Finsupp.single d.element 1))
    (Diagram.splitUp_mergeUp (R := Complex) outer b)
  change merge ((Diagram.splitUp (R := Complex) outer b).eval.toLinearMap
      (Finsupp.single d.element 1)) = Finsupp.single d.element 1 at cancel
  rw [cancel] at h
  by_contra outside
  have coefficient := congrArg (fun f : G →₀ Complex => f d.element) h
  change (Finsupp.single d.element (1 : Complex)) d.element =
    (Finsupp.mapDomain (fun t => outer.toHom t.element) label) d.element at coefficient
  rw [Finsupp.single_eq_same, imageCoeff outer (fun t => t.element) label _ outside] at coefficient
  exact one_ne_zero coefficient

private theorem rightDownNecessary (outer : ConjEmbedding H G) (a b : ConjEmbedding K H)
    {p : ConjEmbedding K G} (d : Dot p (outer.comp b)) (label : DotLabel Complex a b)
    (eq : ((down d).interpret.eval.vertical (Diagram.splitDown outer b).eval).toLinearMap =
      ((Diagram.splitDown outer a).eval.vertical
        ((DotLabel.downDrawing label).interpret.eval.horizontal (Diagram.id (.down outer)).eval)
        ).toLinearMap) :
    d.element ∈ outer.toHom.range := by
  let merge := (Diagram.mergeDown (R := Complex) outer b).eval.toLinearMap
  have h := congrArg (fun f => merge (f (Finsupp.single 1 1))) eq
  change merge ((Diagram.splitDown (R := Complex) outer b).eval.toLinearMap
      ((down d).interpret.eval.toLinearMap (Finsupp.single 1 1))) =
    merge (((DotLabel.downDrawing label).interpret.eval.horizontal (Diagram.id (.down outer)).eval).toLinearMap
      ((Diagram.splitDown (R := Complex) outer a).eval.toLinearMap (Finsupp.single 1 1))) at h
  rw [downSingle, mul_one, rightDownUnit outer a b label] at h
  have cancel := congrArg (fun f => f.toLinearMap (Finsupp.single d.element⁻¹ 1))
    (Diagram.splitDown_mergeDown (R := Complex) outer b)
  change merge ((Diagram.splitDown (R := Complex) outer b).eval.toLinearMap
      (Finsupp.single d.element⁻¹ 1)) = Finsupp.single d.element⁻¹ 1 at cancel
  rw [cancel] at h
  by_contra outside
  have invOutside : d.element⁻¹ ∉ outer.toHom.range := by
    intro hin
    exact outside (by simpa only [inv_inv] using outer.toHom.range.inv_mem hin)
  have coefficient := congrArg (fun f : G →₀ Complex => f d.element⁻¹) h
  change (Finsupp.single d.element⁻¹ (1 : Complex)) d.element⁻¹ =
    (Finsupp.mapDomain (fun t => outer.toHom t.element⁻¹) label) d.element⁻¹ at coefficient
  rw [Finsupp.single_eq_same, imageCoeff outer (fun t => t.element⁻¹) label _ invOutside] at coefficient
  exact one_ne_zero coefficient

private theorem leftSlide (x y z : U)
    (hx : ∀ h : H, x * (h : U) * x⁻¹ ∈ G)
    (hy : ∀ h : H, y * (h : U) * y⁻¹ ∈ G)
    (hz : ∀ k : K, z * (k : U) * z⁻¹ ∈ H)
    (hxy : x * y⁻¹ ∈ G) :
    let a := ConjEmbedding.ofConjugator x hx
    let b := ConjEmbedding.ofConjugator y hy
    let c := ConjEmbedding.ofConjugator z hz
    let d : Dot a b := Dot.ofRepresentatives x y (fun _ => rfl) (fun _ => rfl) hxy
    let stem : Dot (a.comp c) (b.comp c) := ⟨d.element, fun k => d.intertwines (c.toHom k)⟩
    ((Diagram.splitUp (R := Complex) a c).eval.vertical
        ((up d).interpret.eval.horizontal (Diagram.id (.up c)).eval) =
      (up stem).interpret.eval.vertical (Diagram.splitUp b c).eval) ∧
    ((Diagram.splitDown (R := Complex) a c).eval.vertical
        ((Diagram.id (.down c)).eval.horizontal (down d).interpret.eval) =
      (down stem).interpret.eval.vertical (Diagram.splitDown b c).eval) := by
  intro a b c d stem
  -- InductionSplitDotSlide and RestrictionSplitDotSlide give (3.2) and
  -- (3.4) with the same inner representative z on both sides and e = 1.
  -- Remove that mark at evaluation only, using the shared identity-dot laws.
  have hzz : z * z⁻¹ ∈ H := by simp
  let e : Dot c c := Dot.ofRepresentatives z z (fun _ => rfl) (fun _ => rfl) hzz
  have he : e = Dot.id c := by
    apply Dot.ext
    apply Subtype.ext
    change z * z⁻¹ = 1
    exact mul_inv_cancel z
  have hu := (InductionSplitDotSlide K H G x z z hx hz hz hzz).1 y hy hxy
  have hd := (RestrictionSplitDotSlide K H G x z z hx hz hz hzz).1 y hy hxy
  change (Diagram.splitUp (R := Complex) a c).eval.vertical
      ((up d).interpret.eval.horizontal (up e).interpret.eval) =
    (up (stem.vertical (e.whisker b))).interpret.eval.vertical (Diagram.splitUp b c).eval at hu
  change (Diagram.splitDown (R := Complex) a c).eval.vertical
      ((down e).interpret.eval.horizontal (down d).interpret.eval) =
    (down (stem.vertical (e.whisker b))).interpret.eval.vertical (Diagram.splitDown b c).eval at hd
  have hstem : stem.vertical ((Dot.id c).whisker b) = stem := by
    apply Dot.ext
    change stem.element * b.toHom 1 = stem.element
    rw [map_one, mul_one]
  rw [he, hstem, show (up (Dot.id c)).interpret.eval = Biset.Hom.id (Word.up c).basis
    from DotLabel.upDrawing_identity c] at hu
  rw [he, hstem, show (down (Dot.id c)).interpret.eval = Biset.Hom.id (Word.down c).basis
    from DotLabel.downDrawing_identity c] at hd
  exact ⟨hu, hd⟩

end MovingSplitDotProof

open MackeyDiagrams MovingSplitDotProof

theorem MovingSplitDotToOutputBranch : (
∀ {U : Type*} [Group U] (K H G : Subgroup U) (α γ b : U)
    (hα : ∀ h : H, α * (h : U) * α⁻¹ ∈ G)
    (hγ : ∀ k : K, γ * (k : U) * γ⁻¹ ∈ H)
    (hb : ∀ k : K, b * (k : U) * b⁻¹ ∈ G)
    (hD : b * (α * γ)⁻¹ ∈ G),
  let D : G := ⟨b * (α * γ)⁻¹, hD⟩
  let outer := MackeyDiagrams.ConjEmbedding.ofConjugator α hα
  let inner := MackeyDiagrams.ConjEmbedding.ofConjugator γ hγ
  let input := MackeyDiagrams.ConjEmbedding.ofConjugator b hb
  let merged := MackeyDiagrams.ConjEmbedding.comp outer inner
  let inputDot : MackeyDiagrams.Dot input merged :=
    MackeyDiagrams.Dot.ofRepresentatives b (α * γ) (fun _ => rfl)
      (fun k => congrArg (fun c : MulAut U => c (k : U))
        (Eq.symm (map_mul (MulAut.conj (G := U)) α γ))) hD
  let singleton := fun {A B : Subgroup U} {a c : MackeyDiagrams.ConjEmbedding A B}
      (d : MackeyDiagrams.Dot a c) =>
    (Finsupp.single d (1 : Complex) : MackeyDiagrams.DotLabel Complex a c)
  let upTop := MackeyDiagrams.Word.tensor
    (MackeyDiagrams.Word.up outer) (MackeyDiagrams.Word.up inner)
  let downTop := MackeyDiagrams.Word.tensor
    (MackeyDiagrams.Word.down inner) (MackeyDiagrams.Word.down outer)
  let dotThenSplitUp := MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.DotLabel.upDrawing (singleton inputDot))
    (MackeyDiagrams.LabelledDrawing.trivalent
      (MackeyDiagrams.TrivalentVertex.splitUp outer inner))
  let dotThenSplitDown := MackeyDiagrams.LabelledDrawing.vertical
    (MackeyDiagrams.DotLabel.downDrawing (singleton inputDot))
    (MackeyDiagrams.LabelledDrawing.trivalent
      (MackeyDiagrams.TrivalentVertex.splitDown outer inner))
  let evalUpAtInput := fun {p : MackeyDiagrams.ConjEmbedding K G} (hp : p = input)
      (d : MackeyDiagrams.LabelledDrawing Complex (MackeyDiagrams.Word.up p) upTop) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret
      (show MackeyDiagrams.LabelledDrawing Complex (MackeyDiagrams.Word.up input) upTop
        from hp ▸ d))
  let evalDownAtInput := fun {p : MackeyDiagrams.ConjEmbedding K G} (hp : p = input)
      (d : MackeyDiagrams.LabelledDrawing Complex (MackeyDiagrams.Word.down p) downTop) =>
    MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret
      (show MackeyDiagrams.LabelledDrawing Complex (MackeyDiagrams.Word.down input) downTop
        from hp ▸ d))
  (∀ (newInner : MackeyDiagrams.ConjEmbedding K H)
      (sameInput : MackeyDiagrams.ConjEmbedding.comp outer newInner = input)
      (rightLabel : MackeyDiagrams.DotLabel Complex newInner inner),
    let splitThenRightUp := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.splitUp outer newInner))
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up outer)))
        (MackeyDiagrams.DotLabel.upDrawing rightLabel))
    let splitThenRightDown := MackeyDiagrams.LabelledDrawing.vertical
      (MackeyDiagrams.LabelledDrawing.trivalent
        (MackeyDiagrams.TrivalentVertex.splitDown outer newInner))
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.DotLabel.downDrawing rightLabel)
        (MackeyDiagrams.LabelledDrawing.ordinary
          (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.down outer))))
    (evalUpAtInput (Eq.refl input) dotThenSplitUp =
        evalUpAtInput sameInput splitThenRightUp ∨
      evalDownAtInput (Eq.refl input) dotThenSplitDown =
        evalDownAtInput sameInput splitThenRightDown) →
      D ∈ MonoidHom.range (MackeyDiagrams.ConjEmbedding.toHom outer)) ∧
  (let leftRepresentative := b * γ⁻¹
   b = leftRepresentative * γ ∧
   leftRepresentative = (D : U) * α ∧
   ∃ hLeft : ∀ h : H, leftRepresentative * (h : U) * leftRepresentative⁻¹ ∈ G,
     let newOuter := MackeyDiagrams.ConjEmbedding.ofConjugator leftRepresentative hLeft
     ∃ (sameInput : MackeyDiagrams.ConjEmbedding.comp newOuter inner = input)
       (leftDot : MackeyDiagrams.Dot newOuter outer),
       MackeyDiagrams.Dot.element leftDot = D ∧
       (let splitThenLeftUp := MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.trivalent
            (MackeyDiagrams.TrivalentVertex.splitUp newOuter inner))
          (MackeyDiagrams.LabelledDrawing.horizontal
            (MackeyDiagrams.DotLabel.upDrawing (singleton leftDot))
            (MackeyDiagrams.LabelledDrawing.ordinary
              (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.up inner))))
        let splitThenLeftDown := MackeyDiagrams.LabelledDrawing.vertical
          (MackeyDiagrams.LabelledDrawing.trivalent
            (MackeyDiagrams.TrivalentVertex.splitDown newOuter inner))
          (MackeyDiagrams.LabelledDrawing.horizontal
            (MackeyDiagrams.LabelledDrawing.ordinary
              (MackeyDiagrams.Diagram.id (MackeyDiagrams.Word.down inner)))
            (MackeyDiagrams.DotLabel.downDrawing (singleton leftDot)))
        evalUpAtInput (Eq.refl input) dotThenSplitUp =
          evalUpAtInput sameInput splitThenLeftUp ∧
        evalDownAtInput (Eq.refl input) dotThenSplitDown =
          evalDownAtInput sameInput splitThenLeftDown))
) :=
(by
  intro U inst K H G α γ b hα hγ hb hD D outer inner input merged inputDot singleton
    upTop downTop dotThenSplitUp dotThenSplitDown evalUpAtInput evalDownAtInput
  -- Xiao, § 3.2, “Moving a dot back to a branch,” archived original p. 9
  -- and published 28 November revision p. 11. No numbered Alphabeta proof
  -- steps are registered for this endpoint. The construction uses (3.2) and (3.4).
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf#page=11
  have hInputDot : inputDot.element = D := rfl
  constructor
  · intro newInner sameInput rightLabel splitThenRightUp splitThenRightDown matchEq
    -- Apply the target merge to both split evaluations at the unit.
    -- This uses splitUp_mergeUp and splitDown_mergeDown, the inverse laws
    -- on the single strand. The other inverse laws act on two strands.
    -- For a finite right label the resulting coefficients are pushed through
    -- the outer embedding term by term. Downward, the indices use inverses.
    rcases matchEq with hu | hd
    · have h := congrArg Biset.Hom.toLinearMap hu
      change dotThenSplitUp.interpret.eval.toLinearMap =
        (show LabelledDrawing Complex (.up input) upTop from
          sameInput ▸ splitThenRightUp).interpret.eval.toLinearMap at h
      rw [castUp] at h
      exact hInputDot ▸ rightUpNecessary outer newInner inner inputDot rightLabel h
    · have h := congrArg Biset.Hom.toLinearMap hd
      change dotThenSplitDown.interpret.eval.toLinearMap =
        (show LabelledDrawing Complex (.down input) downTop from
          sameInput ▸ splitThenRightDown).interpret.eval.toLinearMap at h
      rw [castDown] at h
      exact hInputDot ▸ rightDownNecessary outer newInner inner inputDot rightLabel h
  · intro leftRepresentative
    -- Factor the given input representative, keeping the inner label fixed.
    have hFactor : b = leftRepresentative * γ := by
      change b = (b * γ⁻¹) * γ
      group
    have hLeftRep : leftRepresentative = (D : U) * α := by
      change b * γ⁻¹ = (b * (α * γ)⁻¹) * α
      group
    refine ⟨hFactor, hLeftRep, ?_⟩
    have hLeft (h : H) : leftRepresentative * (h : U) * leftRepresentative⁻¹ ∈ G := by
      have hm := (D * outer.toHom h * D⁻¹).property
      change (D : U) * (α * (h : U) * α⁻¹) * (D : U)⁻¹ ∈ G at hm
      rw [hLeftRep]
      convert hm using 1
      group
    refine ⟨hLeft, ?_⟩
    intro newOuter
    have sameInput : newOuter.comp inner = input := by
      apply ConjEmbedding.ext
      apply MonoidHom.ext
      intro k
      apply Subtype.ext
      change leftRepresentative * (γ * (k : U) * γ⁻¹) * leftRepresentative⁻¹ =
        b * (k : U) * b⁻¹
      rw [hFactor]
      group
    have hRel : leftRepresentative * α⁻¹ = (D : U) := by rw [hLeftRep, mul_assoc, mul_inv_cancel, mul_one]
    have hRelMem : leftRepresentative * α⁻¹ ∈ G := by rw [hRel]; exact D.property
    let leftDot : Dot newOuter outer :=
      Dot.ofRepresentatives leftRepresentative α (fun _ => rfl) (fun _ => rfl) hRelMem
    have hDot : leftDot.element = D := Subtype.ext hRel
    refine ⟨sameInput, leftDot, hDot, ?_⟩
    intro splitThenLeftUp splitThenLeftDown
    let stem : Dot (newOuter.comp inner) merged :=
      ⟨leftDot.element, fun k => leftDot.intertwines (inner.toHom k)⟩
    have ⟨hu, hd⟩ := leftSlide leftRepresentative α γ hLeft hα hγ hRelMem
    -- The replacement has the same input embedding. On the underlying
    -- free modules, the lifted dot and the original dot have multiplier D.
    have sameUp : (up inputDot).interpret.eval.toLinearMap =
        (up stem).interpret.eval.toLinearMap := by
      apply Finsupp.lhom_ext
      intro x r
      rw [upSingle, upSingle, hInputDot, show stem.element = D from hDot]
    have sameDown : (down inputDot).interpret.eval.toLinearMap =
        (down stem).interpret.eval.toLinearMap := by
      apply Finsupp.lhom_ext
      intro x r
      rw [downSingle, downSingle, hInputDot, show stem.element = D from hDot]
    constructor
    · apply Biset.Hom.ext
      change dotThenSplitUp.interpret.eval.toLinearMap =
        (show LabelledDrawing Complex (.up input) upTop from
          sameInput ▸ splitThenLeftUp).interpret.eval.toLinearMap
      rw [castUp]
      have h := congrArg Biset.Hom.toLinearMap hu.symm
      change (Diagram.splitUp (R := Complex) outer inner).eval.toLinearMap.comp
        (up inputDot).interpret.eval.toLinearMap = _
      rw [sameUp]
      exact h
    · apply Biset.Hom.ext
      change dotThenSplitDown.interpret.eval.toLinearMap =
        (show LabelledDrawing Complex (.down input) downTop from
          sameInput ▸ splitThenLeftDown).interpret.eval.toLinearMap
      rw [castDown]
      have h := congrArg Biset.Hom.toLinearMap hd.symm
      change (Diagram.splitDown (R := Complex) outer inner).eval.toLinearMap.comp
        (down inputDot).interpret.eval.toLinearMap = _
      rw [sameDown]
      exact h)
