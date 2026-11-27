by
  classical
  intro U inst G A D F C E a b d c e f up down tensor comp ga ad df gc ce ef bottom top
    X Y Pair orbit coefficient MiddleLabel UpperLabel ProjectionTerm drawId rightDrawing eval
    IsRightTerm M
  -- Ian Xiao, Theorem 6.7, archived PDF p. 26 and revised published PDF p. 28.
  -- https://getcurious.cc/downloads/mackey-bimodules.pdf
  -- The downloaded revision matches article-revision/mackey-bimodules.pdf.
  -- The archived original has a distinct SHA-256 digest. Both pages contain
  -- the same theorem, so the reviewed Lean type is used verbatim.
  -- Alphabeta Math presents the proof in paragraphs. Steps 1–4 here follow
  -- its coefficient invariance, stabilizer construction, and two finiteness arguments.
  let supplier := RightOrbitDiagramFromProjectedStabilizer G A D F C E a b d c e f
  -- Step 1. The supplier checks equivariance for this very action, including
  -- the inverse on the exterior right coordinate.
  have constant (z w : Pair) (hw : w ∈ orbit z) : coefficient M w = coefficient M z :=
    supplier.1 M z w hw
  let action : MulAction (G × F) Pair :=
    { smul := fun q z => (MackeyDiagrams.Biset.act X q z.1, MackeyDiagrams.Biset.act Y q z.2)
      one_smul := fun z => Prod.ext (MackeyDiagrams.Biset.one_act X z.1)
        (MackeyDiagrams.Biset.one_act Y z.2)
      mul_smul := fun q q' z => Prod.ext (MackeyDiagrams.Biset.mul_act X q q' z.1)
        (MackeyDiagrams.Biset.mul_act Y q q' z.2) }
  have orbit_eq (z w : Pair) : orbit z = orbit w ↔ z ∈ orbit w :=
    @MulAction.orbit_eq_iff _ _ _ action z w
  let supported : Set (Set Pair) := {O | ∃ z : Pair, O = orbit z ∧ coefficient M z ≠ 0}
  -- Step 2. Use the normalized pair and the projected stabilizer. The
  -- nonzero coefficient at that pair supplies the finite-fiber hypothesis.
  -- The supplier connects the typed compact projection, parallel induction
  -- crossing, and multiplication to (6.4) via CaseSixRightShapeEvaluation.
  -- EvaluationWithOneProjection gives the underlying basis formula in coordinates
  -- in D. The orbit supplier already checks the needed indicator for the exact
  -- list-labelled syntax and the finite-label converse.
  have realize (O : supported) :
      ∃ drawing : MackeyDiagrams.LabelledDrawing Complex bottom top,
        IsRightTerm drawing ∧ ∀ w : Pair,
          coefficient (eval drawing) w = if w ∈ O.val then 1 else 0 := by
    obtain ⟨z, he, hz⟩ := O.property
    obtain ⟨r, t, s, hz'⟩ := supplier.2.1 z
    let z₀ : Pair :=
      (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
        (MackeyDiagrams.Word.basis (tensor ad df)) 1 (MackeyDiagrams.Generator.mixedPair b d r),
       MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction c)
        (MackeyDiagrams.Word.basis (tensor ce ef)) t (MackeyDiagrams.Generator.mixedPair e f s))
    have h₀ : coefficient M z₀ ≠ 0 := (constant z₀ z hz') ▸ hz
    obtain ⟨i, j, k, rDot, tDot, sDot, _, _, _, _, _, _, realizeAt⟩ :=
      (supplier.2.2.1 r t s).2.2.2
    obtain ⟨_, finite, indicator⟩ := realizeAt M h₀
    let lower := [((1 : Complex), (⟨rDot, finite⟩ : ProjectionTerm _ i j))]
    let drawing := rightDrawing _ i j k lower [(1, tDot)] [(1, sDot)]
    refine ⟨drawing, ⟨_, i, j, k, lower, [(1, tDot)], [(1, sDot)], rfl⟩, fun w => ?_⟩
    have he' : O.val = orbit z₀ := he.trans ((orbit_eq z z₀).mpr hz')
    rw [he']
    exact indicator w
  let diagram (O : supported) := Classical.choose (realize O)
  have right (O : supported) : IsRightTerm (diagram O) := (Classical.choose_spec (realize O)).1
  let weight (O : supported) := coefficient M (Classical.choose O.property)
  have weight_eq (O : supported) (x : X.carrier) (y : Y.carrier) (h : orbit (x, y) = O.val) :
      weight O = coefficient M (x, y) := by
    have he := (Classical.choose_spec O.property).1
    exact (constant _ _ ((orbit_eq _ _).mp (h.trans he))).symm
  let L (O : supported) := weight O • (eval (diagram O)).toLinearMap
  have matrix (O : supported) (x : X.carrier) (y : Y.carrier) :
      L O (Finsupp.single x 1) y =
        if orbit (x, y) = O.val then weight O else 0 := by
    obtain ⟨z, he, _⟩ := O.property
    have hm : ((x, y) : Pair) ∈ O.val ↔ orbit (x, y) = O.val := by
      rw [he]
      exact (orbit_eq (x, y) z).symm
    have indicator := (Classical.choose_spec (realize O)).2 (x, y)
    change (weight O • (eval (diagram O)).toLinearMap (Finsupp.single x 1)) y = _
    rw [Finsupp.smul_apply]
    change weight O * coefficient (eval (diagram O)) (x, y) = _
    rw [indicator]
    by_cases h : orbit (x, y) = O.val
    · rw [ite_eq_left h, ite_eq_left (hm.mpr h), mul_one]
    · rw [ite_eq_right h, ite_eq_right (fun hw => h (hm.mp hw)), mul_zero]
  -- Step 3. Finiteness for every input is obtained by a linear extension of
  -- the assembled basis columns. Each coordinate of the sum has at most
  -- one contributing orbit, though a column may involve several orbits.
  have pointwise := ExpansionIntoRightDiagramsAux.orbit_columns orbit M.toLinearMap
    supported weight L (fun x y h => ⟨(x, y), rfl, h⟩) weight_eq (supplier.2.2.2.2.2 M) matrix
  refine ⟨⟨supported, weight, diagram, right, pointwise⟩, ?_⟩
  -- Step 4. The checked converse covers the three independent finite vertex
  -- labels and the outer finite sum. For the reverse implication, realize
  -- the finite orbit family by the specified list fold of typed drawings.
  constructor
  · rintro ⟨terms, hterms, hM⟩
    rw [hM]
    exact supplier.2.2.2.2.1 terms hterms
  · intro h
    let all : Finset supported := @Finset.univ supported h.fintype
    obtain ⟨terms, hterms, hsum⟩ :=
      ExpansionIntoRightDiagramsAux.fold_finset weight diagram all
    refine ⟨terms, ?_, ?_⟩
    · intro term ht
      obtain ⟨O, rfl⟩ := hterms term ht
      exact right O
    · apply MackeyDiagrams.Biset.Hom.ext
      apply LinearMap.ext
      intro v
      obtain ⟨finite, sum⟩ := pointwise
      calc
        M.toLinearMap v = (finite v).toFinset.sum (fun O => L O v) := sum v
        _ = all.sum (fun O => L O v) := by
          apply Finset.sum_subset (@Finset.subset_univ supported h.fintype _)
          intro O _ hO
          rw [Set.Finite.mem_toFinset] at hO
          exact not_ne_iff.mp hO
        _ = _ := (hsum v).symm
