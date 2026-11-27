by
  classical
  intro U inst G A D F C E a b c d e f up down tensor comp hom bc ad de ade bcf
    bottom top mergedBottom mergedTop Drawing drawId splitBottom mergeTop eval mergedEval
    atRight ProjectionLabel Parameter Q Qstar intersection lower terms finiteFibers left right
    Left Right leftDrawing rightDrawing sumDrawings conjugatedImage join middleFinite expansion
    leftEval rightEval leftClasses rightClasses
  -- Xiao, §6.2.1, Lemma 6.3 and Theorem 6.4, archived original pp. 22–23
  -- (bc57d137…) and revised published PDF pp. 24–25 (6d7e8859…).
  -- The Alphabeta Math rendering numbers the replacement directions as
  -- Theorem 6.4(1) and (2) and gives the constructions in prose.
  -- https://getcurious.cc/articles/math-bimodule-string-diagrams#thm:three-projections
  have hboundary (x y : Drawing) :
      mergedEval x = mergedEval y ↔ eval x = eval y :=
    ReplacementForTwoProjectionsAux.merged_eq_iff a b c d e f x y
  have hsum (ds : List Drawing) : mergedEval (sumDrawings ds) = (ds.map mergedEval).sum :=
    ReplacementForTwoProjectionsAux.framed_sum splitBottom mergeTop ds
  obtain ⟨hindex, hfibers, hleft, hright⟩ := EvaluationForTwoProjections a b c d e f
  have hleftCoeffs (l : Left) : ∃! coeff : Finsupp Parameter Complex,
      mergedEval (leftDrawing l) = expansion coeff := by
    rcases l with ⟨B, r, s, t, xs, ys, zs⟩
    exact (hleft r s t).2 xs ys zs
  have hrightCoeffs (r : Right) : ∃! coeff : Finsupp Parameter Complex,
      mergedEval (rightDrawing r) = expansion coeff := by
    rcases r with ⟨B', j, v, w, ells, ms, ns⟩
    exact (hright j v w).2 ells ms ns

  -- Step 1 (Theorem 6.4(1)). Use the join construction and its middle
  -- index test. The registered result compares merged maps on lists of
  -- drawings; lift each drawing back to a list of actual right labels.
  obtain ⟨hjoin, hrightCommon, hcriterion⟩ := CaseOneRightProjectionConstruction a b c d e f
  have hsingleRight (p : Parameter) (hp : middleFinite p) :
      ∃ r : Right, mergedEval (rightDrawing r) = Qstar p := by
    obtain ⟨j, v, w, ell, m, n, _, _, _, _, _, _, _, he⟩ := hjoin p hp
    exact ⟨⟨_, j, v, w, Finsupp.single ell 1, Finsupp.single m 1, Finsupp.single n 1⟩, he⟩
  have hcaseOne (l : Left) (coeff : Finsupp Parameter Complex)
      (hc : mergedEval (leftDrawing l) = expansion coeff) :
      (∃ ds : List Right, eval (sumDrawings (ds.map rightDrawing)) = leftEval l) ↔
        ∀ p ∈ coeff.support, middleFinite p := by
    have h : (∃ ds : List Drawing,
        (∀ x ∈ ds, ∃ r : Right, x = rightDrawing r) ∧
        mergedEval (sumDrawings ds) = mergedEval (leftDrawing l)) ↔
        ∀ p ∈ coeff.support, middleFinite p := by
      rcases l with ⟨B, r, s, t, xs, ys, zs⟩
      exact (hcriterion r s t xs ys zs coeff hc).congr (by
        constructor
        · rintro ⟨ds, hds, he⟩
          refine ⟨ds, ?_, he⟩
          intro x hx
          obtain ⟨B', j, v, w, ells, ms, ns, hdraw⟩ := hds x hx
          exact ⟨⟨B', j, v, w, ells, ms, ns⟩, hdraw⟩
        · rintro ⟨ds, hds, he⟩
          refine ⟨ds, ?_, he⟩
          intro x hx
          obtain ⟨⟨B', j, v, w, ells, ms, ns⟩, hdraw⟩ := hds x hx
          exact ⟨B', j, v, w, ells, ms, ns, hdraw⟩) Iff.rfl
    rw [← h]
    constructor
    · rintro ⟨ds, he⟩
      refine ⟨ds.map rightDrawing, ?_, (hboundary _ _).2 he⟩
      intro x hx
      obtain ⟨r, _, hr⟩ := List.mem_map.mp hx
      exact ⟨r, hr.symm⟩
    · rintro ⟨ds, hds, he⟩
      have lift (xs : List Drawing) (hs : ∀ x ∈ xs, ∃ r : Right, x = rightDrawing r) :
          ∃ rs : List Right, rs.map rightDrawing = xs := by
        induction xs with
        | nil => exact ⟨[], rfl⟩
        | cons x xs ih =>
          obtain ⟨r, hr⟩ := hs x (List.mem_cons_self ..)
          obtain ⟨rs, hrs⟩ := ih (fun z hz => hs z (List.mem_cons_of_mem x hz))
          exact ⟨r :: rs, by rw [List.map_cons, ← hr, hrs]⟩
      obtain ⟨rs, rfl⟩ := lift ds hds
      exact ⟨rs, (hboundary _ _).1 he⟩
  have hsingleCaseOne (hd : Subgroup.FiniteIndex (MonoidHom.range (hom d))) :
      ∀ l : Left, ∃ r : Right, rightEval r = leftEval l := by
    obtain ⟨ell, m, n, _, _, _, _, he⟩ := hrightCommon hd
    intro l
    obtain ⟨coeff, hc, _⟩ := hleftCoeffs l
    let r : Right := ⟨A, MackeyDiagrams.ConjEmbedding.id A, ad, bc,
      Finsupp.single ell 1, Finsupp.single m 1, Finsupp.mapDomain n coeff⟩
    exact ⟨r, (hboundary _ _).1 ((he coeff).trans hc.symm)⟩

  -- Step 2 (Theorem 6.4(2)). Use the full-intersection and common-group
  -- constructions with their finite-fiber witnesses. Put each coefficient
  -- in the lower mark rather than adding a scalar box around a summand.
  -- For the common group, mapDomain collects coefficients at equal lower
  -- parameters. Linearity in this marked crossing checks both presentations.
  obtain ⟨hfull, hleftCommon, _⟩ := CaseTwoLeftProjectionConstruction a b c d e f
  have hweighted {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
      (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
      (xs : List (Complex × ProjectionLabel a b r s))
      (ys : List (Complex × ProjectionLabel s c t f))
      (zs : List (Complex × MackeyDiagrams.Dot (comp r t) de)) :
      mergedEval (left r s t xs ys zs) =
        ReplacementForTwoProjectionsAux.weighted
          (fun x => mergedEval (left r s t [(1, x)] ys zs)) xs :=
    ReplacementForTwoProjectionsAux.firstProjectionWeighted a b r s (drawId (up c)) splitBottom
      (MackeyDiagrams.LabelledDrawing.vertical
        (atRight (up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f ys))
        (MackeyDiagrams.LabelledDrawing.horizontal
          (MackeyDiagrams.LabelledDrawing.parallelUp r t d e zs) (drawId (down f))))
      mergeTop xs
  have hleftWeight (p : Parameter) (weight : Complex) (hw : weight ≠ 0) :
      ∃ l : Left, mergedEval (leftDrawing l) = weight • Qstar p := by
    obtain ⟨drawing, hshape, he⟩ := hfull p
    obtain ⟨r, s, t, _, _, _, _, x, y, z, _, _, _, _, _, rfl⟩ := hshape
    refine ⟨⟨_, r, s, t, Finsupp.single x weight, Finsupp.single y 1, Finsupp.single z 1⟩, ?_⟩
    change mergedEval (left r s t (terms (Finsupp.single x weight)) (terms (Finsupp.single y 1))
      (MackeyDiagrams.DotLabel.terms (Finsupp.single z 1))) = _
    rw [show terms (Finsupp.single x weight) = [(weight, x)] from
      ReplacementForTwoProjectionsAux.terms_single x hw,
      show terms (Finsupp.single y (1 : Complex)) = [(1, y)] from
        ReplacementForTwoProjectionsAux.terms_single y one_ne_zero,
      show MackeyDiagrams.DotLabel.terms (Finsupp.single z (1 : Complex)) = [(1, z)] from
        ReplacementForTwoProjectionsAux.terms_single z one_ne_zero,
      hweighted]
    change weight • mergedEval (left r s t [(1, x)] [(1, y)] [(1, z)]) + 0 = _
    rw [add_zero]
    exact congrArg (weight • ·) he
  have hcaseTwo (r : Right) :
      ∃ ds : List Left, eval (sumDrawings (ds.map leftDrawing)) = rightEval r := by
    obtain ⟨coeff, hc, _⟩ := hrightCoeffs r
    have hex (p : {p // p ∈ coeff.support}) :
        ∃ l : Left, mergedEval (leftDrawing l) = coeff p.1 • Qstar p.1 :=
      hleftWeight p.1 (coeff p.1) (Finsupp.mem_support_iff.mp p.2)
    choose build hbuild using hex
    refine ⟨coeff.support.attach.toList.map build, (hboundary _ _).1 ?_⟩
    rw [hsum, hc, List.map_map, List.map_map]
    have hmap : coeff.support.attach.toList.map (mergedEval ∘ leftDrawing ∘ build) =
        coeff.support.attach.toList.map (fun p => coeff p.1 • Qstar p.1) :=
      List.map_congr_left (fun p _ => hbuild p)
    change (coeff.support.attach.toList.map (mergedEval ∘ leftDrawing ∘ build)).sum = _
    rw [hmap, Finset.sum_map_toList]
    exact Finset.sum_attach coeff.support (fun p => coeff p • Qstar p)
  have hsingleCaseTwo (hd : Subgroup.FiniteIndex (MonoidHom.range (hom de))) :
      ∀ r : Right, ∃ l : Left, leftEval l = rightEval r := by
    intro r
    obtain ⟨coeff, hc, _⟩ := hrightCoeffs r
    obtain ⟨drawing, hshape, he⟩ := hleftCommon hd coeff
    obtain ⟨x, y, z, _, _, _, _, rfl⟩ := hshape
    let cf := comp c f
    let t := MackeyDiagrams.ConjEmbedding.id E
    let l : Left := ⟨E, de, cf, t, Finsupp.mapDomain x coeff, Finsupp.single y 1, Finsupp.single z 1⟩
    let value := fun xs => mergedEval (left de cf t xs [(1, y)] [(1, z)])
    let unitValue := fun p => value [(1, p)]
    have heval : mergedEval (leftDrawing l) = value (terms (Finsupp.mapDomain x coeff)) := by
      change mergedEval (left de cf t _ (terms (Finsupp.single y 1))
        (MackeyDiagrams.DotLabel.terms (Finsupp.single z 1))) = _
      rw [show terms (Finsupp.single y (1 : Complex)) = [(1, y)] from
        ReplacementForTwoProjectionsAux.terms_single y one_ne_zero,
        show MackeyDiagrams.DotLabel.terms (Finsupp.single z (1 : Complex)) = [(1, z)] from
          ReplacementForTwoProjectionsAux.terms_single z one_ne_zero]
    have hcollect : value (terms (Finsupp.mapDomain x coeff)) =
        value ((terms coeff).map (fun term => (term.1, x term.2))) := by
      calc
        _ = ReplacementForTwoProjectionsAux.weighted unitValue (terms (Finsupp.mapDomain x coeff)) :=
          hweighted de cf t _ _ _
        _ = Finsupp.linearCombination Complex (unitValue ∘ x) coeff := by
          rw [ReplacementForTwoProjectionsAux.weighted_labelTerms, Finsupp.linearCombination_mapDomain]
        _ = ReplacementForTwoProjectionsAux.weighted (unitValue ∘ x) (terms coeff) :=
          (ReplacementForTwoProjectionsAux.weighted_labelTerms _ _).symm
        _ = _ := by
          rw [hweighted de cf t]
          simp only [ReplacementForTwoProjectionsAux.weighted, List.map_map, Function.comp_def]
    exact ⟨l, (hboundary _ _).1 (heval.trans (hcollect.trans (he.trans hc.symm)))⟩

  refine ⟨hindex, hfibers, fun r s t x y z => (hleft r s t).1 x y z,
    fun j v w ell m n => (hright j v w).1 ell m n, ?_,
    hrightCoeffs, hsingleRight, hsingleCaseOne, hcaseTwo, hsingleCaseTwo, ?_⟩
  · intro l
    obtain ⟨coeff, hc, hu⟩ := hleftCoeffs l
    exact ⟨coeff, hc, hu, hcaseOne l coeff hc⟩
  -- Step 3 (Theorem 6.4, final paragraph). The image of de lies in the
  -- image of d. Finite index of the smaller subgroup supplies the Case 1
  -- hypothesis, and equality of evaluations gives the quotient round trips.
  · intro h
    have hh : Subgroup.FiniteIndex (MonoidHom.range (hom de)) := by
      rcases h with h | h
      · exact h
      · letI : Finite G := h
        infer_instance
    have hle : MonoidHom.range (hom de) ≤ MonoidHom.range (hom d) := by
      rintro g ⟨v, hv⟩
      exact ⟨hom e v, hv⟩
    letI : Subgroup.FiniteIndex (MonoidHom.range (hom de)) := hh
    exact ReplacementForTwoProjectionsAux.quotientReplacement leftEval rightEval
      (hsingleCaseOne (Subgroup.finiteIndex_of_le hle)) (hsingleCaseTwo hh)
