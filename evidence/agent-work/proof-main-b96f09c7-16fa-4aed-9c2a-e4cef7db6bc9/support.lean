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
