namespace CommonMackeyIntersectionSumAux

open MackeyDiagrams

noncomputable section

variable {U : Type*} [Group U] {K H G S : Subgroup U}

private def cupProjection (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding S K) (r : ConjEmbedding S H)
    (d : Dot (a.comp l) (b.comp r)) (hc : r.toHom.range.FiniteIndex) :
    Diagram Complex ((Word.down a).tensor (.up b)) ((Word.up l).tensor (.down r)) :=
  let kg := Word.down a
  let gk := Word.up a
  let gh := Word.up b
  let kl := Word.up l
  let hl := Word.up r
  let lh := Word.down r
  let target := kl.tensor lh
  let insertCup := (Diagram.horizontal (.id kg) (.insertRightUnit gh)).vertical
    (Diagram.horizontal (.id kg) (Diagram.horizontal (.id gh) (.reverseCup r hc)))
  let rebracket := Diagram.horizontal (.id kg) (.unassociate gh hl lh)
  let insertDot := Diagram.horizontal (.id kg)
    (Diagram.horizontal ((Diagram.mergeUp b r).vertical
      ((Diagram.upDot d.inverse).vertical (Diagram.splitUp a l))) (.id lh))
  let prepareTrace := (Diagram.horizontal (.id kg) (.associate gk kl lh)).vertical
    (.unassociate kg gk target)
  let trace := (Diagram.horizontal (.traceCap a) (.id target)).vertical (.leftUnit target)
  insertCup.vertical (rebracket.vertical (insertDot.vertical (prepareTrace.vertical trace)))

private theorem insertRightUnit_single {A B : Subgroup U} (p : Word A B) (x : p.basis.carrier) :
    (Diagram.insertRightUnit (R := Complex) p).eval.toLinearMap (Finsupp.single x 1) =
      Finsupp.single (p.basis.pair (Biset.regular B) x 1) 1 := by
  change (Biset.insertRightUnit p.basis Complex).toLinearMap _ = _
  rw [Biset.insertRightUnit, Biset.Hom.ofFunction_single]

private theorem cupProjection_eval (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding S K) (r : ConjEmbedding S H)
    (d : Dot (a.comp l) (b.comp r)) (hc : r.toHom.range.FiniteIndex)
    (hf : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = z}) :
    (cupProjection a b l r d hc).eval = (Diagram.mixedProjection a b l r d hf).eval := by
  classical
  let kg := Word.down a
  let gk := Word.up a
  let gh := Word.up b
  let kl := Word.up l
  let hl := Word.up r
  let lh := Word.down r
  let M := kg.tensor gh
  let target := kl.tensor lh
  let C := reverseCupWord r
  let cup : Diagram Complex (.empty H) C := .reverseCup r hc
  let prep : Diagram Complex M (kg.tensor (gh.tensor C)) :=
    (Diagram.horizontal (.id kg) (.insertRightUnit gh)).vertical
      (Diagram.horizontal (.id kg) (Diagram.horizontal (.id gh) cup))
  let middle : Diagram Complex (gh.tensor hl) (gk.tensor kl) :=
    (Diagram.mergeUp b r).vertical ((Diagram.upDot d.inverse).vertical (Diagram.splitUp a l))
  let tail' : Diagram Complex (kg.tensor (gh.tensor C)) target :=
    (Diagram.horizontal (.id kg) (.unassociate gh hl lh)).vertical
      ((Diagram.horizontal (.id kg) (Diagram.horizontal middle (.id lh))).vertical
        (((Diagram.horizontal (.id kg) (.associate gk kl lh)).vertical
          (.unassociate kg gk target)).vertical
          ((Diagram.horizontal (.traceCap a) (.id target)).vertical (.leftUnit target))))
  let tail := Diagram.mixedProjectionTail (R := Complex) a b l r d
  let scope := RightCupTrace.ofFiniteAfter tail
    (RightCupTrace.mixedProjectionTail_finiteAfter (R := Complex) a b l r d hf)
  -- Proposition 5.1 uses the transfer through the surviving fiber. At
  -- finite right index the checked cup agrees with the scoped transfer.
  -- Compare the article's placement of the split and trace on each cup term.
  have hscope : scope.eval = (Diagram.mixedProjection a b l r d hf).eval :=
    ScopedDiagram.eval_expandedMixedProjection a b l r d hf
  rw [← hscope, RightCupTrace.eval_eq_reverseCup scope hc]
  apply Diagram.eval_ext_on_generators
  intro z
  refine Quotient.inductionOn z fun ⟨x, y⟩ => ?_
  let fiber := Generator.multiplicationCap_finiteFiber r hc (1 : H)
  have hcup : cup.eval.toLinearMap (Finsupp.single (1 : H) 1) =
      ∑ s ∈ fiber.toFinset, Finsupp.single s (1 : Complex) := by
    change (Generator.reverseCup Complex r hc).toLinearMap (Finsupp.single (1 : H) 1) = _
    rw [Generator.reverseCup, Biset.Hom.transfer_single, one_smul, Biset.Hom.transferBasis_sum]
  have hprep (x y : G) :
      prep.eval.toLinearMap (Finsupp.single (kg.basis.pair gh.basis x y) 1) =
        ∑ s ∈ fiber.toFinset,
          Finsupp.single (kg.basis.pair (gh.tensor C).basis x (gh.basis.pair C.basis y s)) 1 := by
    dsimp only [prep]
    rw [Diagram.eval_vertical_apply, Diagram.eval_horizontal_single, one_smul,
      Diagram.eval_id_apply, insertRightUnit_single, Biset.pairLinear_single, one_mul,
      Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply,
      Diagram.eval_horizontal_single, one_smul, Diagram.eval_id_apply,
      hcup, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [Biset.pairLinear_single, one_mul, Biset.pairLinear_single, one_mul]
  change tail'.eval.toLinearMap (prep.eval.toLinearMap
      (Finsupp.single (kg.basis.pair gh.basis x y) 1)) =
    tail.eval.toLinearMap ((Diagram.horizontal (.id M) cup).eval.toLinearMap
      ((Diagram.insertRightUnit M).eval.toLinearMap
        (Finsupp.single (kg.basis.pair gh.basis x y) 1)))
  rw [hprep, map_sum, insertRightUnit_single, Diagram.eval_horizontal_single, one_smul,
    Diagram.eval_id_apply, hcup, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [Biset.pairLinear_single, one_mul]
  refine Quotient.inductionOn s fun ⟨h₁, h₂⟩ => ?_
  change tail'.eval.toLinearMap
      (Finsupp.single (kg.basis.pair (gh.tensor C).basis x
        (gh.basis.pair C.basis y (hl.basis.pair lh.basis h₁ h₂))) 1) =
    tail.eval.toLinearMap (Finsupp.single (M.basis.pair C.basis
      (kg.basis.pair gh.basis x y) (hl.basis.pair lh.basis h₁ h₂)) 1)
  let v := y * b.toHom h₁ * d.element⁻¹
  have hmiddle : middle.eval.toLinearMap (Finsupp.single (gh.basis.pair hl.basis y h₁) 1) =
      Finsupp.single (gk.basis.pair kl.basis v 1) 1 := by
    dsimp only [middle]
    rw [Diagram.eval_vertical_apply, Diagram.eval_mergeUp_single, Diagram.eval_vertical_apply,
      Diagram.eval_upDot_single, Diagram.eval_splitUp_single]
    rfl
  rw [show tail.eval.toLinearMap (Finsupp.single (M.basis.pair C.basis
      (kg.basis.pair gh.basis x y) (hl.basis.pair lh.basis h₁ h₂)) 1) = _ from
    Diagram.eval_mixedProjectionTail_single a b l r d x y h₁ h₂]
  dsimp only [tail']
  rw [Diagram.eval_vertical_apply, Diagram.eval_vertical_apply, Diagram.eval_vertical_apply,
    Diagram.eval_vertical_apply, Diagram.eval_vertical_apply]
  rw [Diagram.eval_horizontal_single (Diagram.id kg) (Diagram.unassociate gh hl lh),
    one_smul, Diagram.eval_id_apply, Diagram.eval_unassociate_single,
    Biset.pairLinear_single, one_mul]
  rw [Diagram.eval_horizontal_single (Diagram.id kg) (Diagram.horizontal middle (Diagram.id lh)),
    one_smul, Diagram.eval_id_apply,
    Diagram.eval_horizontal_single middle (Diagram.id lh), one_smul, hmiddle,
    Diagram.eval_id_apply, Biset.pairLinear_single, one_mul, Biset.pairLinear_single, one_mul]
  rw [Diagram.eval_horizontal_single (Diagram.id kg) (Diagram.associate gk kl lh),
    one_smul, Diagram.eval_id_apply, Diagram.eval_associate_single,
    Biset.pairLinear_single, one_mul, Diagram.eval_unassociate_single]
  rw [Diagram.eval_horizontal_single (Diagram.traceCap a) (Diagram.id target),
    one_smul, Diagram.eval_traceCap_single, one_smul, Diagram.eval_id_apply,
    Diagram.eval_horizontal_single (Diagram.traceCapOnLeft a l) (Diagram.id lh),
    one_smul, Diagram.eval_id_apply]
  by_cases himage : ∃ k, a.toHom k = x * v
  · obtain ⟨k, hk⟩ := himage
    rw [← hk, Generator.traceBasis_image, Diagram.eval_traceCapOnLeft_image a l x v k hk.symm,
      Biset.pairLinear_single, one_mul, Biset.pairLinear_single, one_mul,
      Diagram.eval_leftUnit_single]
    change Finsupp.single ((target.basis.act (k, 1)) (kl.basis.pair lh.basis 1 h₂)) 1 =
      Finsupp.single (kl.basis.pair lh.basis k h₂) 1
    congr 1
    change ((kl.basis.tensor lh.basis).act (k, 1)) (kl.basis.pair lh.basis 1 h₂) = _
    rw [Biset.act_pair, show lh.basis.act (1, 1) h₂ = h₂ from
      lh.basis.one_act h₂]
    change kl.basis.pair lh.basis (k * 1 * (l.toHom 1)⁻¹) h₂ = _
    simp
  · rw [Generator.traceBasis_outside Complex a _ himage,
      Diagram.eval_traceCapOnLeft_outside a l x v himage]
    simp only [map_zero, LinearMap.zero_apply]

private theorem cupOuter_eval (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding S K) (r : ConjEmbedding S H) (d : Dot (a.comp l) (b.comp r))
    (hc : r.toHom.range.FiniteIndex)
    (hf : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = z}) :
    ((cupProjection a b l r d hc).vertical (Diagram.mixedMultiplication a b l r d)).eval =
      ((Diagram.mixedProjection (R := Complex) a b l r d hf).vertical
        (Diagram.mixedMultiplication a b l r d)).eval :=
  congrArg (fun p => p.vertical (Diagram.mixedMultiplication a b l r d).eval)
    (cupProjection_eval a b l r d hc hf)

private theorem scaledCupOuter_eval (a : ConjEmbedding K G) (b : ConjEmbedding H G)
    (l : ConjEmbedding S K) (r : ConjEmbedding S H) (d : Dot (a.comp l) (b.comp r))
    (hc : r.toHom.range.FiniteIndex)
    (hf : ∀ z, Set.Finite {w | Generator.mixedMultiplicationBasis a b l r d w = z}) (c : Complex) :
    (Diagram.scale c ((cupProjection a b l r d hc).vertical
      (Diagram.mixedMultiplication a b l r d))).eval =
      (Diagram.scale c ((Diagram.mixedProjection a b l r d hf).vertical
        (Diagram.mixedMultiplication a b l r d))).eval :=
  congrArg (Biset.Hom.scale c) (cupOuter_eval a b l r d hc hf)

private theorem sumDiagram_eval_eq {I : Type*} {M : Word K H}
    (left right : I → Diagram Complex M M) (h : ∀ j, (left j).eval = (right j).eval)
    (indices : List I) :
    (indices.foldr (fun j acc => Diagram.add (left j) acc) (Diagram.zero M M)).eval =
      (indices.foldr (fun j acc => Diagram.add (right j) acc) (Diagram.zero M M)).eval := by
  induction indices with
  | nil => rfl
  | cons j js ih =>
    change (left j).eval.add _ = (right j).eval.add _
    rw [h j, ih]

private theorem cardFiber {X : Type*} (s : Set X) (hs : s.Finite) :
    hs.toFinset.card = Nat.card s :=
  (Set.ncard_eq_toFinset_card s hs).symm

end

end CommonMackeyIntersectionSumAux

open MackeyDiagrams
