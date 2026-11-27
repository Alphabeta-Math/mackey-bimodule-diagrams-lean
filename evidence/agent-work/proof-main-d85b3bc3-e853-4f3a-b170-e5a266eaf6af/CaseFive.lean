import MackeyDiagrams
import Proofs.InductionRestrictionMergesAndSplits
import Proofs.MixedCrossingFiniteFiberConvention

universe u
namespace CaseFiveLeftShapeEvaluationAux

open MackeyDiagrams

variable {U : Type u} [Group U] {G A D F C E B : Subgroup U}
variable (a : ConjEmbedding A G) (b : ConjEmbedding A D) (d : ConjEmbedding F D)
variable (c : ConjEmbedding C G) (e : ConjEmbedding C E) (f : ConjEmbedding F E)
variable (α : ConjEmbedding G B) (β : ConjEmbedding D B) (γ : ConjEmbedding E B)

private abbrev RDot := Dot (α.comp a) (β.comp b)
private abbrev TDot := Dot (β.comp d) (γ.comp f)
private abbrev SDot := Dot (α.comp c) (γ.comp e)

private noncomputable abbrev ev {K H : Subgroup U} {p q : Word K H} (drawing : LabelledDrawing Complex p q) :=
  drawing.interpret.eval.toLinearMap

private abbrev input (g : G) (x : D) :=
  ((Word.up a).tensor (.down b)).basis.pair (Word.up d).basis
    ((Biset.induction a).pair (Biset.restriction b) g x) 1

private abbrev middleBasis {J : Subgroup U} (η : ConjEmbedding J B) (j : ConjEmbedding F J) (z : B) :=
  ((Word.down α).tensor (.up η)).basis.pair (Word.up j).basis (Generator.mixedPair α η z) 1

private abbrev targetBasis := ((Word.up c).tensor (.down e)).basis

private abbrev output (p : (targetBasis c e).carrier) :=
  (targetBasis c e).pair (Word.up f).basis p 1

private abbrev finiteFibers (s : SDot c e α γ) :=
  ∀ z : B, Set.Finite {p | Generator.mixedProduct α γ
    (Generator.mixedMultiplicationBasis α γ c e s p) = z}

private abbrev projectionDot (s : SDot c e α γ) (hs : finiteFibers c e α γ s) :
    ProjectionDot.Mixed α γ c e :=
  ⟨s, fun z => Set.Finite.subset (hs (Generator.mixedProduct α γ z))
    (fun _ hz => congrArg (Generator.mixedProduct α γ) hz)⟩

private noncomputable abbrev column (s : SDot c e α γ) (hs : finiteFibers c e α γ s) (z : B) :=
  (hs z).toFinset.sum fun p => Finsupp.single (output c e f p) (1 : Complex)

private abbrev first (rs : List (Complex × RDot a b α β)) : LabelledDrawing Complex
    (((Word.up a).tensor (.down b)).tensor (.up d))
    (((Word.down α).tensor (.up β)).tensor (.up d)) :=
  .horizontal (.mixedMultiplication α β a b rs) (.ordinary (.id (.up d)))

private abbrev second (ts : List (Complex × TDot d f β γ)) : LabelledDrawing Complex
    (((Word.down α).tensor (.up β)).tensor (.up d))
    (((Word.down α).tensor (.up γ)).tensor (.up f)) :=
  .vertical (.ordinary (.associate (.down α) (.up β) (.up d)))
    (.vertical (.horizontal (.ordinary (.id (.down α))) (.parallelUp β d γ f ts))
      (.ordinary (.unassociate (.down α) (.up γ) (.up f))))

private abbrev third (ss : List (Complex × ProjectionDot.Mixed α γ c e)) : LabelledDrawing Complex
    (((Word.down α).tensor (.up γ)).tensor (.up f))
    (((Word.up c).tensor (.down e)).tensor (.up f)) :=
  .horizontal (.compactProjection α γ c e ss) (.ordinary (.id (.up f)))

/- Xiao, Lemma 6.6, equation (6.3) and its proof, first operation: the lower
   multiplication gives u(g) r v(x). The typed spectator contributes its
   unit. The Dot type supplies the first vertex condition, as required by
   the registered finite-fiber convention's multiplication formulas. -/
private theorem firstColumn (rs : List (Complex × RDot a b α β)) (g : G) (x : D) :
    ev (first a b d α β rs) (Finsupp.single (input a b d g x) 1) =
      (rs.map fun (k, r) => k • Finsupp.single
        (middleBasis α β d (α.toHom g * r.element * β.toHom x)) 1).sum := by
  let w := (Biset.induction a).pair (Biset.restriction b) g x
  let X := ((Word.down α).tensor (.up β)).basis
  let Y := (Word.up d).basis
  let frame := (Biset.pairLinear Complex X Y).flip (Finsupp.single 1 1)
  let terms := rs.map fun (k,r) => (k, ScopedDiagram.ordinary
    (Diagram.mixedMultiplication (R := Complex) α β a b r))
  change ((ScopedDiagram.linearCombination terms).eval.horizontal
    (Diagram.id (.up d)).eval).toLinearMap (Finsupp.single (input a b d g x) 1) = _
  rw [show Finsupp.single (input a b d g x) (1 : Complex) =
    Biset.pairLinear Complex ((Word.up a).tensor (.down b)).basis Y
      (Finsupp.single w 1) (Finsupp.single 1 1) by
        rw [Biset.pairLinear_single, one_mul]]
  rw [Biset.Hom.horizontal_pairLinear, Diagram.eval_id_apply]
  change frame ((ScopedDiagram.linearCombination terms).eval.toLinearMap (Finsupp.single w 1)) = _
  rw [ScopedDiagram.eval_linearCombination_apply, map_list_sum]
  simp only [terms, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨k,r⟩ _
  simp only [Function.comp_apply, map_smul]
  obtain ⟨hprod, hpush, _⟩ := (MixedCrossingFiniteFiberConvention (U := U)).2.1 α β a b r
  change k • frame ((Diagram.mixedMultiplication α β a b r).eval.toLinearMap
    (Finsupp.single w 1)) = _
  rw [hpush w, hprod g x]
  change k • Biset.pairLinear Complex X Y
    (Finsupp.single (Generator.mixedPair α β _) 1) (Finsupp.single 1 1) = _
  rw [Biset.pairLinear_single, one_mul]

/- Lemma 6.6, second operation: the induction dot right-multiplies by t.
   The paper suppresses reassociation and the split's unit factor. After
   merging, multiplying and splitting, rebracket and use the inverse law
   of mixedEquiv (which is proved by balancing) to normalize (z,t) to
   (z*t,1). The induction merge and split are the basis rules underlying
   InductionRestrictionMergesAndSplits, valid for the given embeddings
   without choosing representatives. -/
private theorem secondColumn (ts : List (Complex × TDot d f β γ)) (z : B) :
    ev (second d f α β γ ts) (Finsupp.single (middleBasis α β d z) 1) =
      (ts.map fun (k, t) => k • Finsupp.single (middleBasis α γ f (z * t.element)) 1).sum := by
  let P := Word.down α
  let Q := (Word.up β).tensor (.up d)
  let S := (Word.up γ).tensor (.up f)
  let frame := (Biset.pairLinear Complex P.basis S.basis) (Finsupp.single z 1)
  let unassoc := (Diagram.unassociate (R := Complex) P (.up γ) (.up f)).eval.toLinearMap
  let terms := ts.map fun (k,t) => (k, ScopedDiagram.ordinary
    (Diagram.parallelUp (R := Complex) β d γ f t))
  change unassoc (((Diagram.id P).eval.horizontal
    (ScopedDiagram.linearCombination terms).eval).toLinearMap
    ((Diagram.associate (R := Complex) P (.up β) (.up d)).eval.toLinearMap
      (Finsupp.single (middleBasis α β d z) 1))) = _
  rw [show Finsupp.single (middleBasis α β d z) (1 : Complex) =
    Finsupp.single ((P.basis.tensor (Word.up β).basis).pair (Word.up d).basis
      (P.basis.pair (Word.up β).basis z 1) 1) 1 from rfl,
    Diagram.eval_associate_single P (.up β) (.up d) z 1 1 1]
  rw [show Finsupp.single (P.basis.pair Q.basis z ((Word.up β).basis.pair (Word.up d).basis 1 1)) (1 : Complex) =
    Biset.pairLinear Complex P.basis Q.basis (Finsupp.single z 1)
      (Finsupp.single ((Word.up β).basis.pair (Word.up d).basis 1 1) 1) by rw [Biset.pairLinear_single, one_mul]]
  rw [Biset.Hom.horizontal_pairLinear, Diagram.eval_id_apply]
  change unassoc (frame ((ScopedDiagram.linearCombination terms).eval.toLinearMap
    (Finsupp.single ((Word.up β).basis.pair (Word.up d).basis 1 1) 1))) = _
  rw [ScopedDiagram.eval_linearCombination_apply, map_list_sum, map_list_sum]
  simp only [terms, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨k,t⟩ _
  simp only [Function.comp_apply, map_smul]
  have hpar :
      (Diagram.parallelUp (R := Complex) β d γ f t).eval.toLinearMap
        (Finsupp.single ((Word.up β).basis.pair (Word.up d).basis 1 1) 1) =
      Finsupp.single ((Word.up γ).basis.pair (Word.up f).basis t.element 1) 1 := by
    change (Diagram.splitUp (R := Complex) γ f).eval.toLinearMap
      ((Diagram.upDot t).eval.toLinearMap
        ((Diagram.mergeUp β d).eval.toLinearMap
          (Finsupp.single ((Word.up β).basis.pair (Word.up d).basis 1 1) 1))) = _
    rw [Diagram.eval_mergeUp_single β d, map_one, mul_one,
      Diagram.eval_upDot_single, one_mul, Diagram.eval_splitUp_single]
  change k • unassoc (frame ((Diagram.parallelUp β d γ f t).eval.toLinearMap _)) = _
  rw [hpar]
  change k • unassoc (Biset.pairLinear Complex P.basis S.basis
    (Finsupp.single z 1) (Finsupp.single ((Word.up γ).basis.pair (Word.up f).basis t.element 1) 1)) = _
  rw [Biset.pairLinear_single, one_mul]
  unfold unassoc
  rw [Diagram.eval_unassociate_single P (.up γ) (.up f) z t.element 1 1]
  let w := (Biset.restriction α).pair (Biset.induction γ) z t.element
  have hw : w = Generator.mixedPair α γ (z * t.element) :=
    (Generator.mixedPair_mixedProduct α γ w).symm
  change k • Finsupp.single (((Word.down α).tensor (.up γ)).basis.pair
    (Word.up f).basis w 1) 1 = _
  rw [hw]

/- Lemma 6.6, third operation: take the fiber of the upper multiplication
   over the value computed by the lower two crossings. The registered
   finite-fiber convention supplies the projection column with exactly the
   termwise group-fiber hypothesis here. Framing pairs each output with
   the spectator unit and preserves its coefficient. -/
private theorem thirdColumn (ss : List (Complex × {s : SDot c e α γ // finiteFibers c e α γ s}))
    (z : B) :
    ev (third c e f α γ (ss.map fun (k,s) => (k, projectionDot c e α γ s.1 s.2)))
      (Finsupp.single (middleBasis α γ f z) 1) =
      (ss.map fun (k,s) => k • column c e f α γ s.1 s.2 z).sum := by
  let X := ((Word.down α).tensor (.up γ)).basis
  let Y := (Word.up f).basis
  let frame := (Biset.pairLinear Complex (targetBasis c e) Y).flip (Finsupp.single 1 1)
  let labels := ss.map fun (k,s) => (k, projectionDot c e α γ s.1 s.2)
  let terms := labels.map fun (k,s) => (k, ScopedDiagram.ordinary
    (Diagram.mixedProjection (R := Complex) α γ c e s.dot s.finite))
  change ((ScopedDiagram.linearCombination terms).eval.horizontal
    (Diagram.id (.up f)).eval).toLinearMap (Finsupp.single (middleBasis α γ f z) 1) = _
  rw [show Finsupp.single (middleBasis α γ f z) (1 : Complex) =
    Biset.pairLinear Complex X Y (Finsupp.single (Generator.mixedPair α γ z) 1)
      (Finsupp.single 1 1) by
        rw [Biset.pairLinear_single, one_mul]]
  rw [Biset.Hom.horizontal_pairLinear, Diagram.eval_id_apply]
  change frame ((ScopedDiagram.linearCombination terms).eval.toLinearMap
    (Finsupp.single (Generator.mixedPair α γ z) 1)) = _
  rw [ScopedDiagram.eval_linearCombination_apply, map_list_sum]
  simp only [terms, List.map_map]
  simp only [labels, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨k,s⟩ _
  simp only [Function.comp_apply, map_smul]
  obtain ⟨_, _, _, hproj⟩ := (MixedCrossingFiniteFiberConvention (U := U)).2.1 α γ c e s.1
  change k • frame ((Diagram.mixedProjection α γ c e s.1
    (projectionDot c e α γ s.1 s.2).finite).eval.toLinearMap
      (Finsupp.single (Generator.mixedPair α γ z) 1)) = _
  have hcolumn :
      (Diagram.mixedProjection (R := Complex) α γ c e s.1
        (projectionDot c e α γ s.1 s.2).finite).eval.toLinearMap
        (Finsupp.single (Generator.mixedPair α γ z) 1) =
      (s.2 z).toFinset.sum (fun p => Finsupp.single p 1) := (hproj s.2).1 z
  rw [hcolumn, map_sum]
  simp only [frame, LinearMap.flip_apply, column, output, Y]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [Biset.pairLinear_single, one_mul]

/- Lemma 6.6, linear labels: expand the three marked stages in evaluation.
   Linearity at the two composition interfaces gives one product of
   coefficients for each ordered triple. Each projection term keeps
   its own finite-fiber certificate, including when no terms are present. -/
private theorem stackedColumn (rs : List (Complex × RDot a b α β))
    (ts : List (Complex × TDot d f β γ))
    (ss : List (Complex × {s : SDot c e α γ // finiteFibers c e α γ s}))
    (g : G) (x : D) :
    ev (.vertical (first a b d α β rs) (.vertical (second d f α β γ ts)
      (third c e f α γ (ss.map fun (k,s) => (k, projectionDot c e α γ s.1 s.2)))))
      (Finsupp.single (input a b d g x) 1) =
    (rs.map fun (cr,r) =>
      (ts.map fun (ct,t) =>
        (ss.map fun (cs,s) => (cr * ct * cs) •
          column c e f α γ s.1 s.2 (α.toHom g * r.element * β.toHom x * t.element)).sum).sum).sum := by
  let next := ev (second d f α β γ ts)
  let last := ev (third c e f α γ (ss.map fun (k,s) => (k, projectionDot c e α γ s.1 s.2)))
  change last (next (ev (first a b d α β rs) (Finsupp.single (input a b d g x) 1))) = _
  rw [firstColumn, map_list_sum, map_list_sum]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨cr,r⟩ _
  simp only [Function.comp_apply, map_smul]
  let z := α.toHom g * r.element * β.toHom x
  change cr • last (ev (second d f α β γ ts) (Finsupp.single (middleBasis α β d z) 1)) = _
  rw [secondColumn, map_list_sum, List.map_map]
  rw [show cr • (List.map _ ts).sum = _ from map_list_sum (DistribSMul.toAddMonoidHom _ cr) _]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨ct,t⟩ _
  change cr • last (ct • Finsupp.single (middleBasis α γ f (z * t.element)) 1) = _
  rw [map_smul, smul_smul]
  change (cr * ct) • ev (third c e f α γ _) (Finsupp.single (middleBasis α γ f (z * t.element)) 1) = _
  rw [thirdColumn]
  rw [show (cr * ct) • (List.map _ ss).sum = _ from map_list_sum (DistribSMul.toAddMonoidHom _ (cr * ct)) _]
  simp only [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ⟨cs,s⟩ _
  exact smul_smul (cr * ct) cs _

end CaseFiveLeftShapeEvaluationAux
theorem CaseFiveLeftShapeEvaluation :
∀ {U : Type u} [Group U] {G A D F C E B : Subgroup U}
    (a : MackeyDiagrams.ConjEmbedding A G) (b : MackeyDiagrams.ConjEmbedding A D)
    (d : MackeyDiagrams.ConjEmbedding F D) (c : MackeyDiagrams.ConjEmbedding C G)
    (e : MackeyDiagrams.ConjEmbedding C E) (f : MackeyDiagrams.ConjEmbedding F E)
    (α : MackeyDiagrams.ConjEmbedding G B) (β : MackeyDiagrams.ConjEmbedding D B)
    (γ : MackeyDiagrams.ConjEmbedding E B),
  let up := @MackeyDiagrams.Word.up U _
  let down := @MackeyDiagrams.Word.down U _
  let tensor := @MackeyDiagrams.Word.tensor U _
  let comp := @MackeyDiagrams.ConjEmbedding.comp U _
  let sourcePair := tensor (up a) (down b)
  let targetPair := tensor (up c) (down e)
  let targetBasis := MackeyDiagrams.Word.basis targetPair
  let bottom := tensor sourcePair (up d)
  let top := tensor targetPair (up f)
  let RDot := MackeyDiagrams.Dot (comp α a) (comp β b)
  let TDot := MackeyDiagrams.Dot (comp β d) (comp γ f)
  let SDot := MackeyDiagrams.Dot (comp α c) (comp γ e)
  let q := fun (s : SDot) (p : targetBasis.carrier) =>
    MackeyDiagrams.Generator.mixedProduct α γ
      (MackeyDiagrams.Generator.mixedMultiplicationBasis α γ c e s p)
  let finiteFibers := fun (s : SDot) => ∀ z : B, Set.Finite {p | q s p = z}
  let projectionDot := fun (s : SDot) (hs : finiteFibers s) =>
    (⟨s, fun z => Set.Finite.subset (hs (MackeyDiagrams.Generator.mixedProduct α γ z))
      (fun _ hz => congrArg (MackeyDiagrams.Generator.mixedProduct α γ) hz)⟩ :
        MackeyDiagrams.ProjectionDot.Mixed α γ c e)
  let stack := @MackeyDiagrams.LabelledDrawing.vertical U _ Complex _
  let juxtapose := @MackeyDiagrams.LabelledDrawing.horizontal U _ Complex _
  let ordinary := @MackeyDiagrams.LabelledDrawing.ordinary U _ Complex _
  let drawing := fun (rs : List (Complex × RDot)) (ts : List (Complex × TDot))
      (ss : List (Complex × MackeyDiagrams.ProjectionDot.Mixed α γ c e)) =>
    (stack
      (juxtapose (MackeyDiagrams.LabelledDrawing.mixedMultiplication α β a b rs)
        (ordinary (MackeyDiagrams.Diagram.id (up d))))
      (stack
        (ordinary (MackeyDiagrams.Diagram.associate (down α) (up β) (up d)))
        (stack
          (juxtapose (ordinary (MackeyDiagrams.Diagram.id (down α)))
            (MackeyDiagrams.LabelledDrawing.parallelUp β d γ f ts))
          (stack
            (ordinary (MackeyDiagrams.Diagram.unassociate (down α) (up γ) (up f)))
            (juxtapose (MackeyDiagrams.LabelledDrawing.compactProjection α γ c e ss)
              (ordinary (MackeyDiagrams.Diagram.id (up f))))))) :
      MackeyDiagrams.LabelledDrawing Complex bottom top)
  let input := fun (g : G) (x : D) =>
    MackeyDiagrams.Biset.pair (MackeyDiagrams.Word.basis sourcePair)
      (MackeyDiagrams.Biset.induction d)
      (MackeyDiagrams.Biset.pair (MackeyDiagrams.Biset.induction a)
        (MackeyDiagrams.Biset.restriction b) g x) 1
  let output := fun (p : targetBasis.carrier) =>
    MackeyDiagrams.Biset.pair targetBasis (MackeyDiagrams.Biset.induction f) p 1
  let evaluates := fun (diagram : MackeyDiagrams.LabelledDrawing Complex bottom top)
      (g : G) (x : D) =>
    MackeyDiagrams.Biset.Hom.toLinearMap
      (MackeyDiagrams.ScopedDiagram.eval (MackeyDiagrams.LabelledDrawing.interpret diagram))
      (Finsupp.single (input g x) 1)
  let fiberSum := fun (r : RDot) (t : TDot) (s : SDot) (hs : finiteFibers s) (g : G) (x : D) =>
    Finset.sum (Set.Finite.toFinset (hs
      (MackeyDiagrams.ConjEmbedding.toHom α g * MackeyDiagrams.Dot.element r *
        MackeyDiagrams.ConjEmbedding.toHom β x * MackeyDiagrams.Dot.element t)))
      (fun p => Finsupp.single (output p) (1 : Complex))
  (∀ (r : RDot) (t : TDot) (s : SDot) (hs : finiteFibers s) (g : G) (x : D),
    evaluates (drawing [(1, r)] [(1, t)] [(1, projectionDot s hs)]) g x =
      fiberSum r t s hs g x) ∧
  (∀ (rs : MackeyDiagrams.DotLabel Complex (comp α a) (comp β b))
      (ts : MackeyDiagrams.DotLabel Complex (comp β d) (comp γ f))
      (ss : MackeyDiagrams.DotLabel Complex (comp α c) (comp γ e))
      (hs : ∀ s ∈ Finsupp.support ss, finiteFibers s) (g : G) (x : D),
    let supported := Finset.attach (Finsupp.support ss)
    let terms := List.map (fun s =>
      (ss (Subtype.val s), projectionDot (Subtype.val s) (hs (Subtype.val s) (Subtype.property s))))
      (Finset.toList supported)
    evaluates (drawing (MackeyDiagrams.DotLabel.terms rs) (MackeyDiagrams.DotLabel.terms ts) terms) g x =
      Finsupp.sum rs (fun r cr =>
        Finsupp.sum ts (fun t ct =>
          Finset.sum supported (fun s =>
            (cr * ct * ss (Subtype.val s)) •
              fiberSum r t (Subtype.val s) (hs (Subtype.val s) (Subtype.property s)) g x)))) :=
by
  classical
  intro U inst G A D F C E B a b d c e f α β γ
  intro up down tensor comp sourcePair targetPair targetBasis bottom top
    RDot TDot SDot q finiteFibers projectionDot stack juxtapose ordinary drawing input output
    evaluates fiberSum
  constructor
  · intro r t s hs g x
    have h := CaseFiveLeftShapeEvaluationAux.stackedColumn a b d c e f α β γ
      [(1, r)] [(1, t)] [(1, ⟨s, hs⟩)] g x
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, one_smul,
      add_zero] at h
    exact h
  · intro rs ts ss hs g x supported terms
    let projectionLabels :
        List (Complex × {s : SDot // finiteFibers s}) :=
      supported.toList.map fun s => (ss s.1, ⟨s.1, hs s.1 s.2⟩)
    have h := CaseFiveLeftShapeEvaluationAux.stackedColumn a b d c e f α β γ
      (MackeyDiagrams.DotLabel.terms rs) (MackeyDiagrams.DotLabel.terms ts) projectionLabels g x
    have hlabels :
        (projectionLabels.map fun (k,s) => (k, projectionDot s.1 s.2)) = terms := by
      rw [show projectionLabels = _ from rfl, List.map_map]
      rfl
    change evaluates (drawing (MackeyDiagrams.DotLabel.terms rs) (MackeyDiagrams.DotLabel.terms ts)
        (projectionLabels.map fun (k,s) => (k, projectionDot s.1 s.2))) g x = _ at h
    rw [hlabels] at h
    rw [h]
    -- The finite lists enumerate the two coefficient supports and the attached
    -- projection support. The index retains the evidence needed for each fiber.
    simp only [MackeyDiagrams.DotLabel.terms, projectionLabels, List.map_map, Function.comp_def,
      Finset.sum_map_toList, Finsupp.sum]
    rfl
#print axioms CaseFiveLeftShapeEvaluation
