namespace ReplacementForTwoProjectionsAux

open MackeyDiagrams

universe u
noncomputable section

variable {U : Type u} [Group U] {G A D F C E B B' : Subgroup U}
variable (a : ConjEmbedding G A) (b : ConjEmbedding D A) (c : ConjEmbedding F D)
variable (d : ConjEmbedding C G) (e : ConjEmbedding E C) (f : ConjEmbedding E F)

private abbrev atRight {K H J L J' : Subgroup U} (p : Word K H)
    {q : Word H J} {r : Word J L} {q' : Word H J'} {r' : Word J' L}
    (x : LabelledDrawing Complex (q.tensor r) (q'.tensor r')) :=
  LabelledDrawing.vertical (.ordinary (.associate p q r))
    (.vertical (.horizontal (drawId p) x) (.ordinary (.unassociate p q' r')))

local notation "bc'" => b.comp c
local notation "ad'" => a.comp d
local notation "de'" => d.comp e

private abbrev Parameter := ProjectionDot.Mixed a bc' de' f

private abbrev transfer (p : Parameter a b c d e f) :=
  (Diagram.mixedProjection (R := Complex) a bc' de' f p.dot p.finite).eval.toLinearMap

private abbrev expansion (coeff : Parameter a b c d e f →₀ Complex) :=
  coeff.sum (fun p weight => weight • transfer a b c d e f p)

private abbrev Drawing := LabelledDrawing Complex (bottom a b c) (top d e f)

private abbrev merged (x : Drawing a b c d e f) :=
  ev (.vertical (splitBottom a b c) (.vertical x (mergeTop d e f)))

private abbrev leftTerm (r : ConjEmbedding B G) (s : ConjEmbedding B D)
    (t : ConjEmbedding E B) (xs : List (Complex × ProjectionDot.Mixed a b r s))
    (ys : List (Complex × ProjectionDot.Mixed s c t f))
    (zs : List (Complex × Dot (r.comp t) de')) : Drawing a b c d e f :=
  .vertical (.horizontal (.compactProjection a b r s xs) (drawId (.up c)))
    (.vertical (atRight (.up r) (.compactProjection s c t f ys))
      (.horizontal (.parallelUp r t d e zs) (drawId (.down f))))

private abbrev rightTerm (j : ConjEmbedding B' A) (v : ConjEmbedding C B')
    (w : ConjEmbedding F B') (ells : List (Complex × Dot bc' (j.comp w)))
    (ms : List (Complex × ProjectionDot.Mixed a j d v))
    (ns : List (Complex × ProjectionDot.Mixed v w e f)) : Drawing a b c d e f :=
  .vertical (atRight (.down a) (.parallelUp b c j w ells))
    (.vertical (.horizontal (.compactProjection a j d v ms) (drawId (.up w)))
      (atRight (.up d) (.compactProjection v w e f ns)))

private abbrev LeftLabels :=
  Σ B : Subgroup U, Σ r : ConjEmbedding B G, Σ s : ConjEmbedding B D, Σ t : ConjEmbedding E B,
    Finsupp (ProjectionDot.Mixed a b r s) Complex × Finsupp (ProjectionDot.Mixed s c t f) Complex ×
      DotLabel Complex (r.comp t) de'

private abbrev RightLabels :=
  Σ B' : Subgroup U, Σ j : ConjEmbedding B' A, Σ v : ConjEmbedding C B', Σ w : ConjEmbedding F B',
    DotLabel Complex bc' (j.comp w) × Finsupp (ProjectionDot.Mixed a j d v) Complex ×
      Finsupp (ProjectionDot.Mixed v w e f) Complex

private abbrev leftDraw : LeftLabels a b c d e f → Drawing a b c d e f :=
  fun ⟨_, r, s, t, xs, ys, zs⟩ => leftTerm a b c d e f r s t (labelTerms xs) (labelTerms ys) zs.terms

private abbrev rightDraw : RightLabels a b c d e f → Drawing a b c d e f :=
  fun ⟨_, j, v, w, ells, ms, ns⟩ => rightTerm a b c d e f j v w ells.terms (labelTerms ms) (labelTerms ns)

private abbrev middleFinite (p : Parameter a b c d e f) :=
  let conjugated := (bc').toHom.range.map (MulAut.conj p.dot.element).toMonoidHom
  ((ad').toHom.range.subgroupOf (a.toHom.range ⊓ ((ad').toHom.range ⊔ conjugated))).FiniteIndex

private abbrev evalLeft (l : LeftLabels a b c d e f) := (leftDraw a b c d e f l).interpret.eval
private abbrev evalRight (r : RightLabels a b c d e f) := (rightDraw a b c d e f r).interpret.eval

local notation "LD" => LeftLabels a b c d e f
local notation "RD" => RightLabels a b c d e f
local notation "Draw" => Drawing a b c d e f
local notation "Param" => Parameter a b c d e f
local notation "qstar" => transfer a b c d e f
local notation "expand" => expansion a b c d e f
local notation "mergedEval'" => merged a b c d e f
local notation "leftTerm'" => leftTerm a b c d e f
local notation "leftDraw'" => leftDraw a b c d e f
local notation "rightDraw'" => rightDraw a b c d e f
local notation "leftEval'" => evalLeft a b c d e f
local notation "rightEval'" => evalRight a b c d e f
local notation "middleOK" => middleFinite a b c d e f

-- Lemma 6.3 supplies uniqueness of the transfer expansion for these exact
-- coefficient labels, with finite fibers carried by ProjectionDot.Mixed.
private theorem leftCoefficients (l : LD) :
    ∃! coeff : Param →₀ Complex, mergedEval' (leftDraw' l) = expand coeff := by
  rcases l with ⟨B, r, s, t, xs, ys, zs⟩
  exact ((EvaluationForTwoProjections a b c d e f).2.2.1 r s t).2 xs ys zs

private theorem rightCoefficients (r : RD) :
    ∃! coeff : Param →₀ Complex, mergedEval' (rightDraw' r) = expand coeff := by
  rcases r with ⟨B', j, v, w, ells, ms, ns⟩
  exact ((EvaluationForTwoProjections a b c d e f).2.2.2 j v w).2 ells ms ns

-- Theorem 6.4(1). Apply the registered join construction and middle-index test.
private theorem singleRight (p : Param) (hp : middleOK p) :
    ∃ r : RD, mergedEval' (rightDraw' r) = qstar p := by
  obtain ⟨j, v, w, ell, m, n, _, _, _, _, _, _, _, he⟩ :=
    (CaseOneRightProjectionConstruction a b c d e f).1 p hp
  exact ⟨⟨_, j, v, w, Finsupp.single ell 1, Finsupp.single m 1, Finsupp.single n 1⟩, he⟩


private theorem caseOneMerged (l : LD) (coeff : Param →₀ Complex)
    (hc : mergedEval' (leftDraw' l) = expand coeff) :
    (∃ ds : List Draw,
      (∀ x ∈ ds, ∃ r : RD, x = rightDraw' r) ∧
      mergedEval' (drawSum ds) = mergedEval' (leftDraw' l)) ↔
    ∀ p ∈ coeff.support, middleOK p := by
  rcases l with ⟨B, r, s, t, xs, ys, zs⟩
  have criterion := (CaseOneRightProjectionConstruction a b c d e f).2.2 r s t xs ys zs coeff hc
  constructor
  · rintro ⟨ds, hds, he⟩
    apply criterion.mp
    refine ⟨ds, ?_, ?_⟩
    · intro x hx
      obtain ⟨⟨B', j, v, w, ells, ms, ns⟩, hdraw⟩ := hds x hx
      exact ⟨B', j, v, w, ells, ms, ns, hdraw⟩
    · cases ds <;> exact he
  · intro hs
    obtain ⟨ds, hds, he⟩ := criterion.mpr hs
    refine ⟨ds, ?_, ?_⟩
    · intro x hx
      obtain ⟨B', j, v, w, ells, ms, ns, hdraw⟩ := hds x hx
      exact ⟨⟨B', j, v, w, ells, ms, ns⟩, hdraw⟩
    · cases ds <;> exact he

private theorem caseOne (l : LD) (coeff : Param →₀ Complex)
    (hc : mergedEval' (leftDraw' l) = expand coeff) :
    (∃ ds : List RD, (drawSum (ds.map rightDraw')).interpret.eval = leftEval' l) ↔
      ∀ p ∈ coeff.support, middleOK p := by
  refine Iff.trans ?_ (caseOneMerged a b c d e f l coeff hc)
  constructor
  · rintro ⟨ds, he⟩
    refine ⟨ds.map rightDraw', ?_, (merged_eq_iff a b c d e f _ _).2 he⟩
    intro x hx
    obtain ⟨r, _, hr⟩ := List.mem_map.mp hx
    exact ⟨r, hr.symm⟩
  · rintro ⟨ds, hds, he⟩
    have lift (xs : List Draw) (hs : ∀ x ∈ xs, ∃ r : RD, x = rightDraw' r) :
        ∃ rs : List RD, rs.map rightDraw' = xs := by
      induction xs with
      | nil => exact ⟨[], rfl⟩
      | cons x xs ih =>
        obtain ⟨r, hr⟩ := hs x (List.mem_cons_self ..)
        obtain ⟨rs, hrs⟩ := ih (fun z hz => hs z (List.mem_cons_of_mem x hz))
        exact ⟨r :: rs, by rw [List.map_cons, ← hr, hrs]⟩
    obtain ⟨rs, rfl⟩ := lift ds hds
    exact ⟨rs, (merged_eq_iff a b c d e f _ _).1 he⟩

private theorem singleCaseOne (hd : Subgroup.FiniteIndex d.toHom.range) :
    ∀ l : LD, ∃ r : RD, rightEval' r = leftEval' l := by
  obtain ⟨ell, m, n, _, _, _, _, he⟩ := (CaseOneRightProjectionConstruction a b c d e f).2.1 hd
  intro l
  obtain ⟨coeff, hc, _⟩ := leftCoefficients a b c d e f l
  let r : RD := ⟨A, MackeyDiagrams.ConjEmbedding.id A, ad', bc',
    Finsupp.single ell 1, Finsupp.single m 1, Finsupp.mapDomain n coeff⟩
  exact ⟨r, (merged_eq_iff a b c d e f _ _).1 ((he coeff).trans hc.symm)⟩

-- Theorem 6.4(2). Put each coefficient in the marked lower projection.
-- Balanced horizontal evaluation and stacking are linear in that mark.
private theorem leftWeighted {B : Subgroup U} (r : MackeyDiagrams.ConjEmbedding B G)
    (s : MackeyDiagrams.ConjEmbedding B D) (t : MackeyDiagrams.ConjEmbedding E B)
    (xs : List (Complex × ProjectionDot.Mixed a b r s))
    (ys : List (Complex × ProjectionDot.Mixed s c t f))
    (zs : List (Complex × MackeyDiagrams.Dot (r.comp t) de')) :
    mergedEval' (leftTerm' r s t xs ys zs) =
      weighted
        (fun x => mergedEval' (leftTerm' r s t [(1, x)] ys zs)) xs :=
  firstProjectionWeighted a b r s (drawId (.up c)) (splitBottom a b c)
    (MackeyDiagrams.LabelledDrawing.vertical
      (atRight (.up r) (MackeyDiagrams.LabelledDrawing.compactProjection s c t f ys))
      (MackeyDiagrams.LabelledDrawing.horizontal
        (MackeyDiagrams.LabelledDrawing.parallelUp r t d e zs) (drawId (.down f))))
    (mergeTop d e f) xs

private theorem leftWeight (p : Param) (weight : Complex) (hw : weight ≠ 0) :
    ∃ l : LD, mergedEval' (leftDraw' l) = weight • qstar p := by
  obtain ⟨drawing, hshape, he⟩ := (CaseTwoLeftProjectionConstruction a b c d e f).1 p
  obtain ⟨r, s, t, _, _, _, _, x, y, z, _, _, _, _, _, rfl⟩ := hshape
  refine ⟨⟨_, r, s, t, Finsupp.single x weight, Finsupp.single y 1, Finsupp.single z 1⟩, ?_⟩
  change mergedEval' (leftTerm' r s t (labelTerms (Finsupp.single x weight)) (labelTerms (Finsupp.single y 1))
    (MackeyDiagrams.DotLabel.terms (Finsupp.single z 1))) = _
  rw [show labelTerms (Finsupp.single x weight) = [(weight, x)] from
    terms_single x hw,
    show labelTerms (Finsupp.single y (1 : Complex)) = [(1, y)] from
      terms_single y one_ne_zero,
    show MackeyDiagrams.DotLabel.terms (Finsupp.single z (1 : Complex)) = [(1, z)] from
      terms_single z one_ne_zero,
    leftWeighted a b c d e f]
  change weight • mergedEval' (leftTerm' r s t [(1, x)] [(1, y)] [(1, z)]) + 0 = _
  rw [add_zero]
  exact congrArg (weight • ·) he

-- The endpoint presents its finite sum as a list of whole drawings.
-- Evaluate its additive fold and match it with the coefficient support.
private theorem caseTwo (r : RD) :
    ∃ ds : List LD, (drawSum (ds.map leftDraw')).interpret.eval = rightEval' r := by
  obtain ⟨coeff, hc, _⟩ := rightCoefficients a b c d e f r
  have hex (p : {p // p ∈ coeff.support}) :
      ∃ l : LD, mergedEval' (leftDraw' l) = coeff p.1 • qstar p.1 :=
    leftWeight a b c d e f p.1 (coeff p.1) (Finsupp.mem_support_iff.mp p.2)
  choose build hbuild using hex
  refine ⟨coeff.support.attach.toList.map build, (merged_eq_iff a b c d e f _ _).1 ?_⟩
  change mergedEval' (drawSum ((coeff.support.attach.toList.map build).map leftDraw')) =
    mergedEval' (rightDraw' r)
  refine Eq.trans ?_ hc.symm
  refine (framed_sum (splitBottom a b c) (mergeTop d e f) _).trans ?_
  rw [List.map_map, List.map_map]
  have hmap : coeff.support.attach.toList.map (mergedEval' ∘ leftDraw' ∘ build) =
      coeff.support.attach.toList.map (fun p => coeff p.1 • qstar p.1) :=
    List.map_congr_left (fun p _ => hbuild p)
  change (coeff.support.attach.toList.map (mergedEval' ∘ leftDraw' ∘ build)).sum = _
  rw [hmap, Finset.sum_map_toList]
  exact Finset.sum_attach coeff.support (fun p => coeff p • qstar p)

-- Collect coincident lower parameters inside the one marked projection.
-- Linearity identifies the collected label with the supplier's termwise list.
private theorem singleCaseTwo (hd : Subgroup.FiniteIndex ((de').toHom.range)) :
    ∀ r : RD, ∃ l : LD, leftEval' l = rightEval' r := by
  intro r
  obtain ⟨coeff, hc, _⟩ := rightCoefficients a b c d e f r
  obtain ⟨drawing, hshape, he⟩ := (CaseTwoLeftProjectionConstruction a b c d e f).2.1 hd coeff
  obtain ⟨x, y, z, _, _, _, _, rfl⟩ := hshape
  let cf := c.comp f
  let t := MackeyDiagrams.ConjEmbedding.id E
  let l : LD := ⟨E, de', cf, t, Finsupp.mapDomain x coeff, Finsupp.single y 1, Finsupp.single z 1⟩
  let value := fun xs => mergedEval' (leftTerm' de' cf t xs [(1, y)] [(1, z)])
  let unitValue := fun p => value [(1, p)]
  have heval : mergedEval' (leftDraw' l) = value (labelTerms (Finsupp.mapDomain x coeff)) := by
    change mergedEval' (leftTerm' de' cf t _ (labelTerms (Finsupp.single y 1))
      (MackeyDiagrams.DotLabel.terms (Finsupp.single z 1))) = _
    rw [show labelTerms (Finsupp.single y (1 : Complex)) = [(1, y)] from
      terms_single y one_ne_zero,
      show MackeyDiagrams.DotLabel.terms (Finsupp.single z (1 : Complex)) = [(1, z)] from
        terms_single z one_ne_zero]
  have hcollect : value (labelTerms (Finsupp.mapDomain x coeff)) =
      value ((labelTerms coeff).map (fun term => (term.1, x term.2))) := by
    calc
      _ = weighted unitValue (labelTerms (Finsupp.mapDomain x coeff)) :=
        leftWeighted a b c d e f de' cf t _ _ _
      _ = Finsupp.linearCombination Complex (unitValue ∘ x) coeff := by
        rw [weighted_labelTerms, Finsupp.linearCombination_mapDomain]
      _ = weighted (unitValue ∘ x) (labelTerms coeff) :=
        (weighted_labelTerms _ _).symm
      _ = weighted unitValue ((labelTerms coeff).map (fun term => (term.1, x term.2))) := by
        simp only [weighted, List.map_map, Function.comp_def]
      _ = _ := (leftWeighted a b c d e f de' cf t _ _ _).symm
  exact ⟨l, (merged_eq_iff a b c d e f _ _).1 (heval.trans (hcollect.trans (he.trans hc.symm)))⟩
private theorem evaluationClasses (h : ((de').toHom.range).FiniteIndex ∨ Finite G) :
    ∃ (lr : LD → RD) (rl : RD → LD)
      (q : Quotient (Setoid.ker leftEval') ≃ Quotient (Setoid.ker rightEval')),
      (∀ l, rightEval' (lr l) = leftEval' l ∧ q (Quotient.mk _ l) = Quotient.mk _ (lr l)) ∧
      (∀ r, leftEval' (rl r) = rightEval' r ∧ q.symm (Quotient.mk _ r) = Quotient.mk _ (rl r)) := by
  have hd : ((de').toHom.range).FiniteIndex := by
    rcases h with h | h
    · exact h
    · exact @Subgroup.finiteIndex_of_finite G _ _ h
  have hle : (de').toHom.range ≤ d.toHom.range := by
    rintro g ⟨v, hv⟩
    exact ⟨e.toHom v, hv⟩
  exact quotientReplacement leftEval' rightEval'
    (singleCaseOne a b c d e f (@Subgroup.finiteIndex_of_le G _ _ _ hd hle))
    (singleCaseTwo a b c d e f hd)

end
end ReplacementForTwoProjectionsAux
